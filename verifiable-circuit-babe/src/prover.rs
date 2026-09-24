use ark_bn254::{Bn254, G1Affine, G1Projective, G2Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec::pairing::Pairing;
use ark_ff::{One, Zero};
use ark_groth16::Proof as Groth16Proof;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use garbled_snark_verifier::bag::{Circuit, S};
use ark_groth16::VerifyingKey as Groth16VerifyingKey;
use garbled_snark_verifier::dv_bn254::fq::Fq as DvFq;
use garbled_snark_verifier::dv_bn254::fr::Fr as DvFr;
use crate::babe::{WitnessEncProveCt, WitnessEncSetupCt};
use crate::cac::{CACSetupPackage, FinalizedInstanceData};
use crate::dre::matrices::u_bar_vec;
use crate::dre::N_PADDED;
use crate::gc::{SparseAdaptorTable, SGC_PART1_CONSTANT_SIZE};
use crate::instance::{b_value_bits, set_gc_const_labels, set_sgc2_rq_eval_labels};
use crate::soldering::{SolderedLabelsData, SolderingData};
use crate::utils::{derive_hashlock, h_160, h_256, ro_from_pairing_bytes};

pub const GROTH_16_SEED: u64 = 42;

pub struct BABEProver {
    groth16_proof: Groth16Proof<Bn254>,
    dyn_pubin: ark_bn254::Fr,
    pub vk: Groth16VerifyingKey<ark_bn254::Bn254>,
    pub valid_msg: Option<[u8; 32]>,
    pub valid_ct_prove: Option<WitnessEncProveCt>,
    pub valid_finalized_id: Option<usize>,
}

impl BABEProver {
    pub fn new(
        vk: Groth16VerifyingKey<Bn254>,
        groth16_proof: Groth16Proof<Bn254>,
        dyn_pubin: ark_bn254::Fr
    ) -> Self {
        Self {
            groth16_proof,
            dyn_pubin,
            vk,
            valid_msg: None,
            valid_ct_prove: None,
            valid_finalized_id: None,
        }
    }

    /// Verify that the soldering guest output's commitments match the `CACSetupPackage`.
    pub fn verify_soldering_output_match_commitment(
        output: &SolderedLabelsData,
        package: &CACSetupPackage,
        finalized_indices: &[usize],
    ) -> Result<(), String> {
        let base_idx = finalized_indices[0];
        for (j, (h0, h1)) in output.base_commitment.iter().enumerate() {
            let committed = &package.commits[base_idx].epk[j];
            if &h_160(h0) != &committed[0] {
                return Err(format!("base commitment mismatch at wire {j} label 0"));
            }
            if &h_160(h1) != &committed[1] {
                return Err(format!("base commitment mismatch at wire {j} label 1"));
            }
        }
        for (i, &idx) in finalized_indices[1..].iter().enumerate() {
            for (j, (h0, h1)) in output.commitments[i].iter().enumerate() {
                let committed = &package.commits[idx].epk[j];
                if &h_160(h0) != &committed[0] {
                    return Err(format!("instance {idx} commitment mismatch at wire {j} label 0"));
                }
                if &h_160(h1) != &committed[1] {
                    return Err(format!("instance {idx} commitment mismatch at wire {j} label 1"));
                }
            }
        }
        Ok(())
    }

    /// Called when Prover receives `SolderingData` from Verifier (off-chain).
    ///
    /// Verifies:
    /// The ZK soldering proof output is consistent with the CAC commitments.
    pub fn verify_soldering_output(
        package: &CACSetupPackage,
        soldering: &SolderingData,
        client: &zkm_sdk::ProverClient,
        verifying_key: &zkm_sdk::ZKMVerifyingKey,
    ) -> Result<(), String> {
        client
            .verify(&soldering.soldering_proof.proof, verifying_key)
            .map_err(|e| format!("failed to verify soldering proof: {e:?}"))?;

        let sld_output = soldering.soldering_proof.output()?;
        Self::verify_soldering_output_match_commitment(
            &sld_output,
            package,
            &soldering.finalized_indices,
        )?;

        Ok(())
    }

    /// Called upon seeing ChallengeAssert Tx on-chain and extracting the input label L from it.
    /// This function checks if Prover can compute the valid msg for WronglyChallenged Txn.
    pub fn check_compute_msg(
        &mut self,
        finalized: &[FinalizedInstanceData],
        pi1_labels: &[S],
        x_d_labels: &[S],
        soldering: &SolderingData,
        h_msgs_onchain: &[[u8; 20]],
    ) -> bool {
        let sld = match soldering.soldering_proof.output() {
            Ok(output) => output,
            Err(error) => {
                tracing::error!("failed to decode soldering public values: {error}");
                return false;
            }
        };

        self.check_compute_msg_with_soldered_output(
            finalized,
            pi1_labels,
            x_d_labels,
            &sld,
            h_msgs_onchain,
        )
    }

    pub fn check_compute_msg_with_soldered_output(
        &mut self,
        finalized: &[FinalizedInstanceData],
        pi1_labels: &[S],
        x_d_labels: &[S],
        sld: &SolderedLabelsData,
        h_msgs_onchain: &[[u8; 20]],
    ) -> bool {
        let (mut fgc, fgc_indices, mut sgc, sgc_indices) = crate::gc::read_flat_original_gc();

        tracing::info!("Trying base instance...");
        let base_res = self.try_evaluate_instance(
            &finalized[0],
            &pi1_labels,
            &x_d_labels,
            h_msgs_onchain[0],
            &mut fgc, &fgc_indices, &mut sgc, &sgc_indices,
        );
        match base_res {
            Ok(true) => return true,
            Ok(false) => tracing::warn!("base instance did not yield valid msg"),
            Err(e) => tracing::error!("evaluating base instance: {e}"),
        }

        // If cant get valid msg from base instance, try non-base instances using per-wire deltas.
        tracing::info!("Trying non-base instance...");
        for i in 1..finalized.len() {
            let deltas_i = &sld.deltas[i - 1];
            let instance_pi1_labels: Vec<S> = pi1_labels
                .iter()
                .enumerate()
                .map(|(j, &lbl)| {
                    let (d0, d1) = deltas_i[j];
                    if h_256(&lbl.0) == sld.base_commitment[j].0 {
                        lbl ^ S(d0)
                    } else {
                        lbl ^ S(d1)
                    }
                })
                .collect();

            let instance_x_d_labels: Vec<S> = x_d_labels
                .iter()
                .enumerate()
                .map(|(j, &lbl)| {
                    let idx = 2 * N_PADDED + j;
                    let (d0, d1) = deltas_i[idx];
                    if h_256(&lbl.0) == sld.base_commitment[idx].0 {
                        lbl ^ S(d0)
                    } else {
                        lbl ^ S(d1)
                    }
                })
                .collect();

            fgc.reset_circuit_except_01_constants();
            sgc.reset_circuit_except_01_constants();
            let temp = self.try_evaluate_instance(
                &finalized[i],
                &instance_pi1_labels,
                &instance_x_d_labels,
                h_msgs_onchain[i],
                &mut fgc, &fgc_indices, &mut sgc, &sgc_indices,
            );
            match temp {
                Ok(true) => return true,
                Ok(false) => tracing::warn!("non-base instance {i} did not yield valid msg"),
                Err(e) => tracing::error!("evaluating non-base instance: {e}"),
            }
        }

        false
    }

    /// Evaluate the garbled circuit for one instance, decrypt the message, and check it
    /// against `h_msg_onchain`. On success, stores the result fields and returns `Ok(true)`.
    fn try_evaluate_instance(
        &mut self,
        data: &FinalizedInstanceData,
        pi1_labels: &[S],
        x_d_labels: &[S],
        h_msg_onchain: [u8; 20],
        fgc: &mut Circuit,
        fgc_indices: &[usize],
        sgc: &mut Circuit,
        sgc_indices: &[usize],
    ) -> Result<bool, String> {
        let ct_prove = self.compute_ct_prove_for_instance(
            fgc, fgc_indices, sgc, sgc_indices, data, pi1_labels, x_d_labels,
        );
        tracing::info!("compute ct_prove done");

        let msg = Self::compute_msg(&self.groth16_proof, &ct_prove, &data.ct_setup, &self.vk)?;
        // found the valid one.
        if derive_hashlock(&msg) == h_msg_onchain {
            self.valid_msg = Some(msg);
            self.valid_ct_prove = Some(ct_prove);
            self.valid_finalized_id = Some(data.index);
            return Ok(true);
        }

        Ok(false)
    }

    /// Garble-evaluate the circuit and return the resulting `ct1 = r·π₁`.
    pub fn compute_ct_prove(
        &self,
        fgc: &mut Circuit,
        fgc_indices: &[usize],
        sgc: &mut Circuit,
        sgc_indices: &[usize],
        const_labels: &[Vec<S>; 2],
        pi1_labels: &[S],
        x_d_labels: &[S],
        ciphertext_sets: &[Vec<S>; 3],
        adaptor_tables: &[SparseAdaptorTable; 2],
        b: &ark_bn254::G1Affine,
        aes_salt: S,
    ) -> WitnessEncProveCt {
        assert_eq!(
            const_labels[1].len(), SGC_PART1_CONSTANT_SIZE,
            "const_labels[1] (SGC constant labels) must have length SGC_PART1_CONSTANT_SIZE"
        );

        let pi1 = self.groth16_proof.a;
        let x_d = self.dyn_pubin;

        // --------Compute ct1--------------
        set_gc_const_labels(fgc, &const_labels[0]);
        for (i, &lbl) in pi1_labels.iter().enumerate() {
            fgc.0[i + 2].borrow_mut().label = Some(lbl);
        }
        let fgc_witness: Vec<bool> = DvFq::to_bits(pi1.x).into_iter().chain([false, false])
            .chain(DvFq::to_bits(pi1.y)).chain([false, false])
            .collect();
        let fgc_output_labels = BABEProver::eval_circuit_with_ciphertext(
            fgc,
            fgc_indices,
            &fgc_witness,
            &ciphertext_sets[0],
            2,
            Some(aes_salt)
        );
        let ct1 = BABEProver::eval_adaptor_table(
            &fgc_output_labels, pi1, &adaptor_tables[0]
        );

        // --------Compute ct1'--------------
        // Part1: compute Q = x_d * L2 + B.
        set_gc_const_labels(sgc, &const_labels[1]);
        for (i, &lbl) in x_d_labels.iter().enumerate() {
            sgc.0[i + SGC_PART1_CONSTANT_SIZE].borrow_mut().label = Some(lbl);
        }
        // Compute B bit representation (Montgomery form) for use as constant wires.
        let (b_x_bits, b_y_bits) = b_value_bits(b);
        for (i, bit) in b_x_bits.iter().enumerate() {
            sgc.0[2 + i].borrow_mut().value = Some(*bit);
        }
        for (i, bit) in b_y_bits.iter().enumerate() {
            sgc.0[2 + 254 + i].borrow_mut().value = Some(*bit);
        }
        let sgc_part1_witness: Vec<bool> = DvFr::to_bits(x_d).into_iter().chain([false, false]).collect();
        let sgc_output_labels_1 = BABEProver::eval_circuit_with_ciphertext(
            sgc,
            sgc_indices,
            &sgc_part1_witness,
            &ciphertext_sets[1],
            SGC_PART1_CONSTANT_SIZE,
            Some(aes_salt)
        );

        // Part2: compute rQ
        let q = self.vk.gamma_abc_g1[2] * self.dyn_pubin + b;
        let q_affine = q.into_affine();
        fgc.reset_circuit_except_01_constants();
        set_gc_const_labels(fgc, &const_labels[1][0..2]);
        set_sgc2_rq_eval_labels(fgc, &sgc_output_labels_1, const_labels[1][0]);
        let sgc_witness: Vec<bool> = DvFq::to_bits(q_affine.x).into_iter().chain([false, false])
            .chain(DvFq::to_bits(q_affine.y)).chain([false, false])
            .collect();
        let sgc_output_labels_2 = BABEProver::eval_circuit_with_ciphertext(
            fgc,
            fgc_indices,
            &sgc_witness,
            &ciphertext_sets[2],
            2,
            Some(aes_salt)
        );
        let ct1_prime = BABEProver::eval_adaptor_table(
            &sgc_output_labels_2, q_affine, &adaptor_tables[1]
        );

        WitnessEncProveCt { ct1_r_pi1: ct1, ct1_prime }
    }

    pub fn compute_ct_prove_for_instance(
        &self,
        fgc: &mut Circuit,
        fgc_indices: &[usize],
        sgc: &mut Circuit,
        sgc_indices: &[usize],
        data: &FinalizedInstanceData,
        pi1_labels: &[S],
        x_d_labels: &[S],
    ) -> WitnessEncProveCt {
        self.compute_ct_prove(
            fgc,
            fgc_indices,
            sgc,
            sgc_indices,
            &[data.constant_labels_0.to_vec(), data.constant_labels_1.to_vec()],
            pi1_labels,
            x_d_labels,
            &data.ciphertext_sets,
            &data.adaptor_tables,
            &data.b,
            data.aes_salt,
        )
    }

    pub(crate) fn eval_circuit_with_ciphertext(
        circuit: &mut Circuit,
        output_indices: &[usize],
        witness: &[bool],
        ciphertext: &[S],
        const_skip: usize,
        salt: Option<S>,
    ) -> Vec<[u8; 16]> {
        circuit.set_witness_value(&witness, const_skip);
        for gate in &mut circuit.1 {
            gate.evaluate();
        }
        circuit.garbled_evaluate_without_delta(ciphertext, salt);

        let output_labels: Vec<[u8; 16]> = output_indices
            .iter()
            .map(|i| circuit.0[*i].borrow().get_label().0)
            .collect();
        output_labels
    }

    pub(crate) fn eval_adaptor_table(
        u_bar_labels: &[[u8; 16]],
        u: G1Affine,
        adaptor_table: &SparseAdaptorTable,
    ) -> Vec<u8> {
        let u_bar = u_bar_vec(&u);
        let decrypted_encodings = adaptor_table.eval(u_bar_labels, &u_bar);

        let mut sum = G1Projective::zero();
        let mut weight = ark_bn254::Fr::one();
        for decoding in decrypted_encodings {
            let (x, y, z) = decoding.f_i;
            sum += G1Projective::new(x, y, z) * weight;
            weight += weight;
        }

        let result = sum.into_affine();
        assert!(
            result.is_on_curve() && result.is_in_correct_subgroup_assuming_on_curve(),
            "adaptor eval: result is not a valid G1 point"
        );
        let mut ct = Vec::new();
        result.serialize_compressed(&mut ct).expect("serialize r·G1P");
        ct

    }

    /// Decrypt the message from `ct_prove` and `ct_setup` using the Groth16 proof.
    pub fn compute_msg(
        proof: &Groth16Proof<Bn254>,
        ct_prove: &WitnessEncProveCt,
        ct_setup: &WitnessEncSetupCt,
        vk: &ark_groth16::VerifyingKey<Bn254>,
    ) -> Result<[u8; 32], String> {
        let ct1 = G1Affine::deserialize_compressed(ct_prove.ct1_r_pi1.as_slice())
            .map_err(|e| format!("deserialize ct1: {e}"))?
            .into_group();
        let ct1_prime = G1Affine::deserialize_compressed(ct_prove.ct1_prime.as_slice())
            .map_err(|e| format!("deserialize ct1_prime: {e}"))?;
        let ct2 = G2Affine::deserialize_compressed(ct_setup.ct2_r_delta_g2.as_slice())
            .map_err(|e| format!("deserialize ct2: {e}"))?
            .into_group();

        let r_y = Bn254::pairing(ct1, proof.b) - Bn254::pairing(proof.c, ct2);
        let q_blind = Bn254::pairing(ct1_prime, vk.gamma_g2);
        let mask_gt = r_y - q_blind;

        let mut mask_bytes = Vec::new();
        mask_gt.serialize_compressed(&mut mask_bytes).map_err(|e| format!("serialize mask_gt: {e}"))?;
        let mask = ro_from_pairing_bytes(&mask_bytes, 32);

        let ct3 = &ct_setup.ct3_masked_msg;
        if ct3.len() != 32 {
            return Err(format!("ct3 unexpected length {}", ct3.len()));
        }
        let mut msg = [0u8; 32];
        for i in 0..32 {
            msg[i] = ct3[i] ^ mask[i];
        }
        Ok(msg)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Bn254, Fr};
    use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
    use rand::SeedableRng;
    use garbled_snark_verifier::core::utils::reset_gid;
    use crate::babe::DummyMulCircuit;
    use crate::cac::cac_finalize_indices;
    use crate::instance::CACInstance;
    use crate::soldering::{build_soldered_wires_input, soldering_guest_compute};
    use crate::verifier::BABEVerifier;

    const TEST_N_CC: usize = 4;
    const TEST_M_CC: usize = 2;

    #[test]
    #[ignore = "requires artifacts match the dummy vk"]
    fn test_prover_ct_prove_decrypts_message() {
        reset_gid();
        let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(GROTH_16_SEED);

        // 1. Groth16 setup and prove: a * b = c.
        let a = Fr::from(3u64);
        let b = Fr::from(7u64);
        let (pk, vk) = ark_groth16::Groth16::<Bn254>::setup(
            DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) },
            &mut rng,
        ).unwrap();
        let proof = ark_groth16::Groth16::<Bn254>::prove(
            &pk,
            DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) },
            &mut rng,
        ).unwrap();
        let static_public_inputs = a * b;
        let dynamic_public_inputs = a * a; // x_d

        // 2. Verifier enc_setup.
        let verifier = CACInstance::new_from_seed(
            rand::random(),
            &vk,
            static_public_inputs,
        ).unwrap();

        // 3. Input labels: [pi1_xbits, pi1_ybits, x_dbits...].
        let pi1_labels = verifier.compute_pi1_labels_based_on_value(proof.a);
        let x_d_labels = verifier.compute_x_d_labels_based_on_value(dynamic_public_inputs);
        let constant_labels = verifier.get_2_circuit_constant_labels();

        // 4. Prover evaluates the garbled circuit.
        // Prover has: 2 circuits, input labels, constants labels & value
        let prover = BABEProver::new(
            vk.clone(),
            proof.clone(),
            dynamic_public_inputs
        );
        let (mut fgc, fgc_indices, mut sgc, sgc_indices) = crate::gc::read_flat_original_gc();

        let ct_prove = prover.compute_ct_prove(
            &mut fgc,
            &fgc_indices,
            &mut sgc,
            &sgc_indices,
            &constant_labels,
            &pi1_labels,
            &x_d_labels,
            &verifier.ciphertexts_sets,
            &verifier.adaptor_tables,
            &verifier.secrets.b,
            verifier.secrets.aes_salt,
        );
        drop(fgc);
        drop(sgc);

        // 5. Decrypt and verify.
        let msg = BABEProver::compute_msg(&proof, &ct_prove, &verifier.ct_setup, &vk).unwrap();
        assert_eq!(msg, verifier.secrets.msg);
    }

    /// Build the common C&C + soldering scaffolding used by both tests below.
    /// Returns `(verifier, package, finalized_indices, finalized, soldering, h_msgs_onchain)`.
    fn setup_cac_soldering(
    ) -> (BABEVerifier, CACSetupPackage, Vec<usize>, Vec<FinalizedInstanceData>, SolderedLabelsData)
    {
        let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(GROTH_16_SEED);
        let a = Fr::from(3u64);
        let b = Fr::from(7u64);
        let (_, vk) = ark_groth16::Groth16::<Bn254>::setup(
            DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) }, &mut rng,
        ).unwrap();
        let static_public_inputs = a * b;
        let _dynamic_public_inputs = a * a;

        let verifier = BABEVerifier::new(TEST_N_CC, &vk, static_public_inputs).unwrap();
        let package = verifier.commit();
        let finalized_indices = cac_finalize_indices(TEST_N_CC, TEST_M_CC);
        let (_temp, finalized) = verifier.open(&finalized_indices).expect("verifier open failed");

        let soldered_input = build_soldered_wires_input(&verifier, &finalized_indices);
        let soldered_output = soldering_guest_compute(&soldered_input);

        (verifier, package, finalized_indices, finalized, soldered_output)
    }

    // ── verify_soldering_output ───────────────────────────────────────────────

    #[test]
    fn test_verify_soldering_output_ok() {
        let (_, package, finalized_indices, _, soldered_output) = setup_cac_soldering();
        BABEProver::verify_soldering_output_match_commitment(
            &soldered_output,
            &package,
            &finalized_indices,
        )
        .expect("soldering commitments should match");
    }

    // ── check_compute_msg ─────────────────────────────────────────────────────

    #[test]
    #[ignore = "requires artifacts match the dummy vk"]
    fn test_check_compute_msg_finds_valid_msg() {
        let (verifier, package, finalized_indices, finalized, soldered_output) =
            setup_cac_soldering();

        // Prove with the same dummy circuit.
        let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(GROTH_16_SEED);
        let a = Fr::from(3u64);
        let b = Fr::from(7u64);
        let (pk, vk) = ark_groth16::Groth16::<Bn254>::setup(
            DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) },
            &mut rng,
        )
        .unwrap();
        let proof = ark_groth16::Groth16::<Bn254>::prove(
            &pk,
            DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) },
            &mut rng,
        )
        .unwrap();
        let _static_public_inputs = a * b;
        let dynamic_public_inputs = a * a;


        // base_input_labels: active labels for the 508 π₁ input wires of the base instance.
        let base_idx = finalized_indices[0];
        let pi1_labels = verifier.compute_pi1_labels(base_idx, proof.a);
        let x_d_labels = verifier.compute_x_d_labels(base_idx, dynamic_public_inputs);
        let mut prover = BABEProver::new(vk.clone(), proof.clone(), dynamic_public_inputs);

        // Extract h_msgs from bitcoin script of WronglyChallenged Txn
        // But in this test, we just get from package
        let mut h_msgs_onchain: Vec<[u8; 20]> = finalized_indices.iter().map(|&idx| package.commits[idx].h_msg).collect();
        let found = prover.check_compute_msg_with_soldered_output(
            &finalized, &pi1_labels, &x_d_labels, &soldered_output, &h_msgs_onchain,
        );

        assert!(found, "expected a valid msg to be found");
        assert!(prover.valid_msg.is_some());
        assert!(prover.valid_ct_prove.is_some());
        assert!(prover.valid_finalized_id.is_some());

        // change the base msg to access non-base instance
        println!("change the base msg to access non-base instance");
        let mut prover = BABEProver::new(vk, proof, dynamic_public_inputs);
        h_msgs_onchain[0] = [0u8; 20];
        let found = prover.check_compute_msg_with_soldered_output(
            &finalized, &pi1_labels, &x_d_labels, &soldered_output, &h_msgs_onchain,
        );
        assert!(found, "expected a valid msg to be found");
        assert!(prover.valid_msg.is_some());
        assert!(prover.valid_ct_prove.is_some());
        assert!(prover.valid_finalized_id.is_some());
        assert_ne!(prover.valid_finalized_id.unwrap(), finalized_indices[0]);
    }

    // Soundness: a Prover claiming an x_d that its proof does not actually attest to must not
    // be able to decrypt, in any finalized instance (base or soldered).
    #[test]
    #[ignore = "requires artifacts match the dummy vk"]
    fn test_check_compute_msg_rejects_wrong_x_d() {
        let (verifier, package, finalized_indices, finalized, soldered_output) =
            setup_cac_soldering();

        let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(GROTH_16_SEED);
        let a = Fr::from(3u64);
        let b = Fr::from(7u64);
        let (pk, vk) = ark_groth16::Groth16::<Bn254>::setup(
            DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) },
            &mut rng,
        )
        .unwrap();
        // Proof genuinely attests d = a*a = 9; claim a different x_d.
        let proof = ark_groth16::Groth16::<Bn254>::prove(
            &pk,
            DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) },
            &mut rng,
        )
        .unwrap();
        let wrong_dynamic_public_inputs = a * a + Fr::from(1u64);

        let base_idx = finalized_indices[0];
        let pi1_labels = verifier.compute_pi1_labels(base_idx, proof.a);
        let x_d_labels = verifier.compute_x_d_labels(base_idx, wrong_dynamic_public_inputs);
        let mut prover = BABEProver::new(vk, proof, wrong_dynamic_public_inputs);

        let h_msgs_onchain: Vec<[u8; 20]> =
            finalized_indices.iter().map(|&idx| package.commits[idx].h_msg).collect();
        let found = prover.check_compute_msg_with_soldered_output(
            &finalized, &pi1_labels, &x_d_labels, &soldered_output, &h_msgs_onchain,
        );

        assert!(!found, "a mismatched x_d must not decrypt the message");
        assert!(prover.valid_msg.is_none());
        assert!(prover.valid_ct_prove.is_none());
        assert!(prover.valid_finalized_id.is_none());
    }
}
