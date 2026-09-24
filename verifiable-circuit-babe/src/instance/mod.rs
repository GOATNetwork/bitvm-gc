use ark_bn254::Fr;
use ark_ec::AffineRepr;
use ark_ec::pairing::Pairing;
use garbled_snark_verifier::bag::{Circuit, S};
use crate::babe::WitnessEncSetupCt;
use crate::gc::{FlatEvalBuffer, read_compact_gc, SparseAdaptorTable, SGC_PART1_CONSTANT_SIZE};
use crate::instance::secret::{InstanceSecrets, Seed};
use ark_groth16::VerifyingKey as Groth16VerifyingKey;
use ark_serialize::CanonicalSerialize;
use garbled_snark_verifier::dv_bn254::fq::Fq as DvFq;
use garbled_snark_verifier::dv_bn254::fr::Fr as DvFr;
use crate::dre::{N, Q_SIZE, U_BAR_SIZE};
use crate::instance::commit::CACInstanceCommit;
use crate::utils::{derive_hashlock, g2_project_to_ser, h_256, ro_from_pairing_bytes};

pub mod secret;
pub mod commit;

/// Decompose `b`'s x/y coordinates (Montgomery form) into bits, as used for the
/// SGC Part 1 constant wires `2..2+N` (x) and `2+N..2+2N` (y).
pub fn b_value_bits(b: &ark_bn254::G1Affine) -> (Vec<bool>, Vec<bool>) {
    let b_x_bits: Vec<bool> = DvFq::to_bits(DvFq::as_montgomery(b.x));
    let b_y_bits: Vec<bool> = DvFq::to_bits(DvFq::as_montgomery(b.y));
    (b_x_bits, b_y_bits)
}

pub struct CACInstance {
    pub seed: Seed,
    pub secrets: InstanceSecrets,
    pub ct_setup: WitnessEncSetupCt,
    pub adaptor_tables: [SparseAdaptorTable; 2],
    /// for fgc, sgc part 1, sgc part 2 — dense, one entry per non-free gate only.
    pub ciphertexts_sets: [Vec<S>; 3]
}

impl CACInstance {
    /// Construct a instance fully determined by `seed`.
    /// W/O ct_setup.
    pub fn new_from_seed(
        seed: Seed,
        vk: &Groth16VerifyingKey<ark_bn254::Bn254>,
        static_inputs: Fr,
    ) -> Result<Self, String> {
        if vk.gamma_abc_g1.len() != 3 {
            return Err("static/dynamic split does not match vk".to_string());
        }

        let secrets = InstanceSecrets::new_from_seed(seed);
        let (fgc_flat, fgc_indices, sgc_flat, sgc_indices) = read_compact_gc();

        // FGC
        let (fgc_ciphertext, fgc_output_labels) = {
            let mut buf = FlatEvalBuffer::new(fgc_flat.num_wires);
            for (i, l) in secrets.constant_0labels[0].iter().enumerate() {
                buf.set_label(i, l.0);
            }
            for (i, &key) in secrets.input_0labels[0].iter().enumerate() {
                buf.set_label(2 + i, key.0);
            }
            buf.garble_and_collect(fgc_flat, fgc_indices, secrets.delta[0].0, Some(secrets.aes_salt))
        };
        assert_eq!(fgc_output_labels.len(), 2 * U_BAR_SIZE);

        // SGC Part 1
        let (sgc_ciphertext_1, sgc_output_labels_1) = {
            let mut buf = FlatEvalBuffer::new(sgc_flat.num_wires);
            for (i, l) in secrets.constant_0labels[1].iter().enumerate() {
                buf.set_label(i, l.0);
            }
            for (i, &key) in secrets.input_0labels[1].iter().enumerate() {
                buf.set_label(SGC_PART1_CONSTANT_SIZE + i, key.0);
            }
            buf.garble_and_collect(sgc_flat, sgc_indices, secrets.delta[1].0, Some(secrets.aes_salt))
        };
        assert_eq!(sgc_output_labels_1.len(), 2 * Q_SIZE);

        // SGC Part 2: same topology as FGC, SGC delta, input 0-labels from Part 1 outputs.
        let (sgc_ciphertext_2, sgc_output_labels_2) = {
            let mut buf = FlatEvalBuffer::new(fgc_flat.num_wires);
            buf.set_label(0, secrets.constant_0labels[1][0].0);
            buf.set_label(1, secrets.constant_0labels[1][1].0);
            set_sgc2_rq_labels(&mut buf, &sgc_output_labels_1, secrets.constant_0labels[1][0].0);
            buf.garble_and_collect(fgc_flat, fgc_indices, secrets.delta[1].0, Some(secrets.aes_salt))
        };
        assert_eq!(sgc_output_labels_2.len(), 2 * U_BAR_SIZE);

        let fgc_adaptor_table = SparseAdaptorTable::build_from_r_and_u_bar_labels(
            secrets.r, &fgc_output_labels, &secrets.rhos[0], &secrets.fq_deltas[0],
        );
        let sgc_adaptor_table = SparseAdaptorTable::build_from_r_and_u_bar_labels(
            secrets.r, &sgc_output_labels_2, &secrets.rhos[1], &secrets.fq_deltas[1],
        );

        let ct_setup = Self::enc_setup(&secrets, vk, static_inputs)?;

        Ok(Self {
            seed,
            secrets,
            ct_setup,
            adaptor_tables: [fgc_adaptor_table, sgc_adaptor_table],
            ciphertexts_sets: [fgc_ciphertext, sgc_ciphertext_1, sgc_ciphertext_2],
        })
    }

    /// Commitment-only path: same circuit setup as `new_from_seed` but ciphertexts and
    /// adaptor tables are stream-hashed without being stored.
    pub fn commit_from_seed(
        seed: Seed,
        vk: &Groth16VerifyingKey<ark_bn254::Bn254>,
        static_inputs: Fr,
    ) -> Result<CACInstanceCommit, String> {
        if vk.gamma_abc_g1.len() != 3 {
            return Err("static/dynamic split does not match vk".to_string());
        }

        let secrets = InstanceSecrets::new_from_seed(seed);
        let (fgc_flat, fgc_indices, sgc_flat, sgc_indices) = read_compact_gc();

        // FGC: flat garble — no Rc/RefCell, no evaluate pass, cache-friendly.
        let (com_fgc, fgc_output_labels) = {
            let mut buf = FlatEvalBuffer::new(fgc_flat.num_wires);
            for (i, l) in secrets.constant_0labels[0].iter().enumerate() {
                buf.set_label(i, l.0);
            }
            for (i, &key) in secrets.input_0labels[0].iter().enumerate() {
                buf.set_label(2 + i, key.0);
            }
            buf.garble_and_hash(fgc_flat, fgc_indices, secrets.delta[0].0, Some(secrets.aes_salt))
        };
        assert_eq!(fgc_output_labels.len(), 2 * U_BAR_SIZE);

        // SGC Part 1: constant labels include wire-0, wire-1, and B-coordinate bits.
        let (com_sgc_1, sgc_output_labels_1) = {
            let mut buf = FlatEvalBuffer::new(sgc_flat.num_wires);
            for (i, l) in secrets.constant_0labels[1].iter().enumerate() {
                buf.set_label(i, l.0);
            }
            for (i, &key) in secrets.input_0labels[1].iter().enumerate() {
                buf.set_label(SGC_PART1_CONSTANT_SIZE + i, key.0);
            }
            buf.garble_and_hash(sgc_flat, sgc_indices, secrets.delta[1].0, Some(secrets.aes_salt))
        };
        assert_eq!(sgc_output_labels_1.len(), 2 * Q_SIZE);

        // SGC Part 2: same topology as FGC, SGC delta, input 0-labels from Part 1 outputs.
        let (com_sgc_2, sgc_output_labels_2) = {
            let mut buf = FlatEvalBuffer::new(fgc_flat.num_wires);
            buf.set_label(0, secrets.constant_0labels[1][0].0);
            buf.set_label(1, secrets.constant_0labels[1][1].0);
            set_sgc2_rq_labels(&mut buf, &sgc_output_labels_1, secrets.constant_0labels[1][0].0);
            buf.garble_and_hash(fgc_flat, fgc_indices, secrets.delta[1].0, Some(secrets.aes_salt))
        };
        assert_eq!(sgc_output_labels_2.len(), 2 * U_BAR_SIZE);

        // Adaptor tables: build and hash on-the-fly, never materialized.
        let com_adaptor_0 = SparseAdaptorTable::build_and_hash(
            secrets.r, &fgc_output_labels, &secrets.rhos[0], &secrets.fq_deltas[0],
        );
        let com_adaptor_1 = SparseAdaptorTable::build_and_hash(
            secrets.r, &sgc_output_labels_2, &secrets.rhos[1], &secrets.fq_deltas[1],
        );

        // ct_setup (small).
        let ct_setup = Self::enc_setup(&secrets, vk, static_inputs)?;
        let mut ct_setup_bytes = Vec::new();
        ct_setup_bytes.extend_from_slice(&ct_setup.ct2_r_delta_g2);
        ct_setup_bytes.extend_from_slice(&ct_setup.ct3_masked_msg);

        // Build the commit from hashes and small secret data — no GC data retained.
        let delta = secrets.delta;
        let epk: Vec<[[u8; 20]; 2]> = secrets.input_0labels[0]
            .iter()
            .map(|&key| [derive_hashlock(&key.0), derive_hashlock(&(key ^ delta[0]).0)])
            .chain(secrets.input_0labels[1].iter().map(|&key| {
                [derive_hashlock(&key.0), derive_hashlock(&(key ^ delta[1]).0)]
            }))
            .collect();

        let constant_commits_0: [[[u8; 32]; 2]; 2] = std::array::from_fn(|w| {
            let l0 = secrets.constant_0labels[0][w];
            [h_256(&l0.0), h_256(&(l0 ^ delta[0]).0)]
        });
        assert_eq!(secrets.constant_0labels[1].len(), SGC_PART1_CONSTANT_SIZE);
        let constant_commits_1: Vec<[[u8; 32]; 2]> = secrets.constant_0labels[1]
            .iter()
            .map(|&l0| [h_256(&l0.0), h_256(&(l0 ^ delta[1]).0)])
            .collect();

        let mut b_blind_bytes = Vec::new();
        secrets.b.serialize_compressed(&mut b_blind_bytes).expect("serialize b");

        let commit = CACInstanceCommit {
            epk,
            constant_commits_fgc: constant_commits_0,
            constant_commits_sgc: constant_commits_1,
            b_blind_commit: h_256(&b_blind_bytes),
            h_msg: derive_hashlock(&secrets.msg),
            h_ct_setup: h_256(&ct_setup_bytes),
            com_adaptor: [com_adaptor_0, com_adaptor_1],
            com_gc: [com_fgc, com_sgc_1, com_sgc_2],
        };

        Ok(commit)
    }

    /// Enc*(crs, x_S, |D|, msg; r, B):
    ///   P_S = gamma_abc[0] + Σ_{k} x_S[k]·gamma_abc[k+1]
    ///   mask = Y_S^r - e(r·B, γ) where Y_S^r = e(α, r·β) + e(P_S, r·γ)
    fn enc_setup(
        secrets: &InstanceSecrets,
        vk: &Groth16VerifyingKey<ark_bn254::Bn254>,
        static_inputs: Fr,
    ) -> Result<WitnessEncSetupCt, String> {
        let r = secrets.r;
        let p_s = vk.gamma_abc_g1[0].into_group() + vk.gamma_abc_g1[1].into_group() * static_inputs;

        let r_b = secrets.b * r;
        let r_delta = vk.delta_g2.into_group() * r;

        let t1 = ark_bn254::Bn254::pairing(vk.alpha_g1, vk.beta_g2.into_group() * r);
        let t2 = ark_bn254::Bn254::pairing(p_s, vk.gamma_g2.into_group() * r);
        let y_s_r = t1 + t2;

        let q_b = ark_bn254::Bn254::pairing(r_b, vk.gamma_g2);
        let mask_gt = y_s_r - q_b;

        let mut mask_bytes = Vec::new();
        mask_gt.serialize_compressed(&mut mask_bytes).or(Err("Failed to serialize mask_bytes"))?;
        let mask = ro_from_pairing_bytes(&mask_bytes, secrets.msg.len());
        let ct3 = secrets.msg.iter().zip(mask.iter()).map(|(a, b)| a ^ b).collect::<Vec<_>>();

        Ok(WitnessEncSetupCt {
            ct2_r_delta_g2: g2_project_to_ser(r_delta),
            ct3_masked_msg: ct3,
        })
    }

    /// Returns the input labels given the bits of pi1.
    /// Use for testing.
    pub fn compute_pi1_labels_based_on_value(&self, pi1: ark_bn254::G1Affine) -> Vec<S> {
        let witness: Vec<bool> = DvFq::to_bits(pi1.x).into_iter().chain([false, false])
            .chain(DvFq::to_bits(pi1.y)).chain([false, false])
            .collect();
        let delta = self.secrets.delta[0];
        witness.iter().enumerate().map(|(i, &b)| {
            let key = self.secrets.input_0labels[0][i];
            if b { key ^ delta } else { key }
        }).collect()
    }

    /// Returns the input labels given the bits of pi1.
    /// Use for testing.
    pub fn compute_x_d_labels_based_on_value(&self, x_d: Fr) -> Vec<S> {
        let witness: Vec<bool> = DvFr::to_bits(x_d).into_iter().chain([false, false]).collect();
        let delta = self.secrets.delta[1];
        witness.iter().enumerate().map(|(i, &b)| {
            let key = self.secrets.input_0labels[1][i];
            if b { key ^ delta } else { key }
        }).collect()
    }

    pub fn get_b_value_labels(&self) -> Vec<S> {
        let (b_x_bits, b_y_bits) = b_value_bits(&self.secrets.b);
        let mut labels = Vec::new();
        for (i, bit) in b_x_bits.iter().enumerate() {
            if *bit {
                labels.push(self.secrets.constant_0labels[1][i + 2] ^ self.secrets.delta[1]);
            } else {
                labels.push(self.secrets.constant_0labels[1][i + 2]);
            }
        }

        for (i, bit) in b_y_bits.iter().enumerate() {
            if *bit {
                labels.push(self.secrets.constant_0labels[1][i + 2 + 254] ^ self.secrets.delta[1]);
            } else {
                labels.push(self.secrets.constant_0labels[1][i + 2 + 254]);
            }
        }

        labels
    }

    // Labels of constants in both circuits
    pub fn get_2_circuit_constant_labels(&self) -> [Vec<S>; 2] {
        let f_01_labels = [
            self.secrets.constant_0labels[0][0], self.secrets.constant_0labels[0][1] ^ self.secrets.delta[0]
        ];

        let s_01_labels = [
            self.secrets.constant_0labels[1][0], self.secrets.constant_0labels[1][1] ^ self.secrets.delta[1]
        ];
        let s_b_labels = self.get_b_value_labels();
        let s_constant_labels: Vec<S> = s_01_labels
            .to_vec().into_iter().chain(s_b_labels).collect();
        [f_01_labels.to_vec(), s_constant_labels]
    }

    pub fn commit(&self) -> CACInstanceCommit {
        CACInstanceCommit::from_instance(self)
    }
}

/// Set SGC Part 2 input 0-labels
/// Wire layout: Q.x bits (0..N) | Q.x MSB slots | Q.y bits (0..N) | Q.y MSB slots.
/// `q_pairs` is the interleaved [l0, l1, l0, l1, ...] output from SGC Part 1 (2*Q_SIZE entries).
/// `msb_l0` is the 0-label for the 4 MSB-slot wires/
fn set_sgc2_rq_labels(buf: &mut FlatEvalBuffer, q_pairs: &[[u8; 16]], msb_l0: [u8; 16]) {
    for (i, key) in q_pairs[..2 * N].iter().step_by(2).enumerate() {
        buf.set_label(2 + i, *key);
    }
    buf.set_label(2 + N, msb_l0);
    buf.set_label(2 + N + 1, msb_l0);
    for (i, key) in q_pairs[2 * N..].iter().step_by(2).enumerate() {
        buf.set_label(2 + N + 2 + i, *key);
    }
    buf.set_label(2 + N + 2 + N, msb_l0);
    buf.set_label(2 + N + 2 + N + 1, msb_l0);
}

pub fn set_gc_const_labels(
    circuit: &mut Circuit,
    constant_labels: &[S],
) {
    assert!(
        constant_labels.len() <= circuit.0.len(),
        "constant_labels ({}) exceeds circuit wire count ({})",
        constant_labels.len(), circuit.0.len()
    );
    for i in 0..constant_labels.len() {
        circuit.0[i].borrow_mut().label = Some(constant_labels[i]);
    }
}

/// Set SGC Part 2 input labels on a Circuit for evaluation.
/// same layout as set_sgc2_q_labels
pub fn set_sgc2_rq_eval_labels(circuit: &mut Circuit, q_labels: &[[u8; 16]], msb_label: S) {
    for (i, &key) in q_labels[..N].iter().enumerate() {
        circuit.0[2 + i].borrow_mut().label = Some(S(key));
    }
    circuit.0[2 + N].borrow_mut().label = Some(msb_label);
    circuit.0[2 + N + 1].borrow_mut().label = Some(msb_label);
    for (i, &key) in q_labels[N..].iter().enumerate() {
        circuit.0[2 + N + 2 + i].borrow_mut().label = Some(S(key));
    }
    circuit.0[2 + N + 2 + N].borrow_mut().label = Some(msb_label);
    circuit.0[2 + N + 2 + N + 1].borrow_mut().label = Some(msb_label);
}


#[cfg(test)]
mod tests {
    use super::*;
    use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
    use ark_ec::CurveGroup;
    use rand::SeedableRng;
    use garbled_snark_verifier::circuits::bn254::g1::G1Affine;
    use crate::babe::DummyMulCircuit;
    use crate::prover::{BABEProver, GROTH_16_SEED};

    #[test]
    #[ignore = "requires artifacts match the dummy vk"]
    fn enc_setup_prove_dec_roundtrip() {
        use crate::babe::{witness_enc_decrypt, WitnessEncProveCt};

        let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(GROTH_16_SEED);

        let a = Fr::from(3u64);
        let b = Fr::from(7u64);
        let circuit = DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) };
        let (pk, vk) = ark_groth16::Groth16::<ark_bn254::Bn254>::setup(circuit, &mut rng)
            .expect("groth16 setup");
        let proof = ark_groth16::Groth16::<ark_bn254::Bn254>::prove(
            &pk,
            DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) },
            &mut rng,
        ).expect("groth16 prove");

        // |S|=1 (a*b static), |D|=1 (a*a dynamic)
        let static_inputs = a * b;
        let dynamic_inputs = a * a;

        let instance = CACInstance::new_from_seed([2u8; 32], &vk, static_inputs)
            .expect("new_from_seed");
        println!("generate instance done");

        let r = instance.secrets.r;
        let b_blind = instance.secrets.b;
        let pi1 = proof.a;
        let constant_labels = instance.get_2_circuit_constant_labels();
        let pi1_labels = instance.compute_pi1_labels_based_on_value(proof.a);
        let x_d_labels = instance.compute_x_d_labels_based_on_value(dynamic_inputs);
        let (mut fgc, fgc_indices, mut sgc, sgc_indices) = crate::gc::read_flat_original_gc();

        // evaluate the fgc to get the r * pi_1
        set_gc_const_labels(&mut fgc, &constant_labels[0]);
        for (i, &lbl) in pi1_labels.iter().enumerate() {
            fgc.0[i + 2].borrow_mut().label = Some(lbl);
        }
        let fgc_witness: Vec<bool> = DvFq::to_bits(pi1.x).into_iter().chain([false, false])
            .chain(DvFq::to_bits(pi1.y)).chain([false, false])
            .collect();
        let fgc_output_labels = BABEProver::eval_circuit_with_ciphertext(
            &mut fgc,
            &fgc_indices,
            &fgc_witness,
            &instance.ciphertexts_sets[0],
            2,
            Some(instance.secrets.aes_salt)
        );
        let ct1_bytes = BABEProver::eval_adaptor_table(
            &fgc_output_labels, pi1, &instance.adaptor_tables[0]
        );
        let mut expected_ct1_bytes = Vec::new();
        (pi1 * r).into_affine().serialize_compressed(&mut expected_ct1_bytes).expect("serialize r·G1P");
        assert_eq!(ct1_bytes, expected_ct1_bytes, "fgc is wrong");
        println!("fgc test done");

        // evaluate the sgc part 1 to get the Q
        set_gc_const_labels(&mut sgc, &constant_labels[1]);
        for (i, &lbl) in x_d_labels.iter().enumerate() {
            sgc.0[i + SGC_PART1_CONSTANT_SIZE].borrow_mut().label = Some(lbl);
        }
        let (b_x_bits, b_y_bits) = b_value_bits(&b_blind);
        for (i, bit) in b_x_bits.iter().enumerate() {
            sgc.0[2 + i].borrow_mut().value = Some(*bit);
        }
        for (i, bit) in b_y_bits.iter().enumerate() {
            sgc.0[2 + 254 + i].borrow_mut().value = Some(*bit);
        }
        let sgc_part1_witness: Vec<bool> = DvFr::to_bits(dynamic_inputs).into_iter().chain([false, false]).collect();
        let sgc_output_labels_1 = BABEProver::eval_circuit_with_ciphertext(
            &mut sgc,
            &sgc_indices,
            &sgc_part1_witness,
            &instance.ciphertexts_sets[1],
            SGC_PART1_CONSTANT_SIZE,
            Some(instance.secrets.aes_salt)
        );
        // check that sgc computed correctly
        let q_proj = vk.gamma_abc_g1[2].into_group() * dynamic_inputs + b_blind;
        let q_affine = q_proj.into_affine();
        let q_value_bits = G1Affine::to_bits(q_affine);
        for (k, &idx) in sgc_indices.iter().enumerate() {
            let w_val = sgc.0[idx].borrow().get_value();
            let q_val = q_value_bits[k];
            assert_eq!(w_val, q_val, "sgc part 1: mismatch at k={k}: wire={w_val}, q_val={q_val}");
        }
        println!("sgc part 1 test done");

        // evaluate the sgc part2 to get the r * Q
        fgc.reset_circuit_except_01_constants();
        set_gc_const_labels(&mut fgc, &constant_labels[1][0..2]);
        set_sgc2_rq_eval_labels(&mut fgc, &sgc_output_labels_1, constant_labels[1][0]);
        let sgc_witness: Vec<bool> = DvFq::to_bits(q_affine.x).into_iter().chain([false, false])
            .chain(DvFq::to_bits(q_affine.y)).chain([false, false])
            .collect();
        let sgc_output_labels_2 = BABEProver::eval_circuit_with_ciphertext(
            &mut fgc,
            &fgc_indices,
            &sgc_witness,
            &instance.ciphertexts_sets[2],
            2,
            Some(instance.secrets.aes_salt)
        );
        let ct1_prime = BABEProver::eval_adaptor_table(
            &sgc_output_labels_2, q_affine, &instance.adaptor_tables[1]
        );

        let mut expected_ct1_prime_bytes = Vec::new();
        (q_affine * r).into_affine().serialize_compressed(&mut expected_ct1_prime_bytes).expect("serialize r·G1P");
        assert_eq!(ct1_prime, expected_ct1_prime_bytes, "sgc part2 is wrong");
        println!("sgc part 2 test done");

        let ctprove = WitnessEncProveCt {
            ct1_r_pi1: ct1_bytes,
            ct1_prime,
        };
        let decrypted = witness_enc_decrypt(
            &vk, &instance.ct_setup, &ctprove,
            proof.b.into_group(), proof.c.into_group(),
        ).unwrap();

        println!("decrypted done");
        assert_eq!(decrypted.as_slice(), &instance.secrets.msg);
    }
}
