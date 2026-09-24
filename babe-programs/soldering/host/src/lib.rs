use ark_bn254::{Bn254, Fr};
use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_groth16::VerifyingKey as Groth16VerifyingKey;
use bitvm::signatures::Wots;
use rand::SeedableRng;
use verifiable_circuit_babe::babe::{babe_build_deposit_lock, babe_prover_assert, babe_prover_presign, babe_prover_wrongly_challenged_cac, babe_verifier_cac_setup, babe_verifier_challenge_assert_cac, babe_verifier_presign, babe_verify_prover_presigs, babe_verify_verifier_presigs, build_ca_outlock, BtcPk, DummyMulCircuit, ProverSetupState, VerifierSetupState, M_CC, N_CC};
use verifiable_circuit_babe::cac::{
    cac_finalize_indices, verify_finalized_indices_in_bundle, verify_finalized_instances,
    verify_opened_instances, CACSetupPackage, FinalizedInstanceData,
};
use verifiable_circuit_babe::prover::{BABEProver, GROTH_16_SEED};
use verifiable_circuit_babe::soldering::{
    build_soldered_wires_input, SolderingData, SolderingProof,
};
use verifiable_circuit_babe::transactions::{
    OnchainSize, TxAssertWitness, TxChallengeAssertWitness, TxDepositLock,
    TxWronglyChallengedWitness,
};
use verifiable_circuit_babe::instance::secret::Seed;
use verifiable_circuit_babe::utils::derive_hashlock;
use verifiable_circuit_babe::verifier::BABEVerifier;
use zkm_sdk::{include_elf, ProverClient, ZKMProvingKey, ZKMStdin, ZKMVerifyingKey};
use verifiable_circuit_babe::wots::Wots96;

const SOLDERING_GUEST: &[u8] = include_elf!("soldering-guest");

pub struct BabeBundleBuilder {
    client: ProverClient,
    proving_key: ZKMProvingKey,
    verifying_key: ZKMVerifyingKey,
}

pub struct BabeBundle {
    pub opened: Vec<(usize, Seed)>,
    pub finalized: Vec<FinalizedInstanceData>,
    pub soldering: SolderingData,
}

pub struct BabeCACE2ERun {
    pub deposit_lock: TxDepositLock,
    pub assert_witness: TxAssertWitness,
    pub challenge_assert_witness: TxChallengeAssertWitness,
    pub wrongly_challenged_witness: TxWronglyChallengedWitness,
}

impl BabeBundleBuilder {
    pub fn new() -> Self {
        let client = ProverClient::new();
        let (proving_key, verifying_key) = client.setup(SOLDERING_GUEST);
        Self { client, proving_key, verifying_key }
    }

    pub fn babe_verifier_open_and_solder(
        &self,
        verifier: &BABEVerifier,
        finalized_indices: &[usize],
    ) -> Result<BabeBundle, String> {
        let (opened, finalized) = verifier.open(finalized_indices)
            .expect("verifier open failed");
        let soldered_input = build_soldered_wires_input(verifier, finalized_indices);
        let mut stdin = ZKMStdin::new();
        stdin.write(&soldered_input);
        let proof = self
            .client
            .prove(&self.proving_key, stdin)
            .compressed()
            .run()
            .map_err(|e| format!("failed to prove soldering program: {e:?}"))?;

        Ok(BabeBundle {
            opened,
            finalized,
            soldering: SolderingData {
                finalized_indices: finalized_indices.to_vec(),
                soldering_proof: SolderingProof { proof },
            },
        })
    }

    pub fn babe_prover_verify_setup(
        &self,
        package: &CACSetupPackage,
        bundle: &BabeBundle,
        vk: &Groth16VerifyingKey<Bn254>,
        static_public_inputs: Fr,
        finalized_indices: &[usize],
    ) -> Result<(), String> {
        verify_finalized_indices_in_bundle(
            package,
            &bundle.opened,
            &bundle.finalized,
            finalized_indices,
            &bundle.soldering.finalized_indices,
        )?;
        verify_opened_instances(package, &bundle.opened, vk, static_public_inputs)?;
        verify_finalized_instances(package, &bundle.finalized)?;

        BABEProver::verify_soldering_output(
            package,
            &bundle.soldering,
            &self.client,
            &self.verifying_key,
        )
    }

    pub fn run_babe_e2e_cac(&self) -> Result<BabeCACE2ERun, String> {
        let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(GROTH_16_SEED);
        let a = Fr::from(7u64);
        let b = Fr::from(9u64);
        let (groth16_pk, vk) = ark_groth16::Groth16::<Bn254>::setup(
            DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) },
            &mut rng,
        )
        .map_err(|e| format!("failed to setup Groth16 fixture: {e:?}"))?;
        let proof = ark_groth16::Groth16::<Bn254>::prove(
            &groth16_pk,
            DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) },
            &mut rng,
        )
        .map_err(|e| format!("failed to prove Groth16 fixture: {e:?}"))?;
        let static_public_inputs = a * b;
        let dynamic_public_inputs = a * a;

        // ── Setup phase ───────────────────────────────────────────────────────────

        // Prover sends pk_p to Verifier.
        let pk_p = BtcPk([0u8; 33]);
        println!("Prover: generating BTC keys and sending pk_p to Verifier");

        // Verifier creates N_CC instances and sends CACSetupPackage.
        println!("Verifier generating BTC keys");
        let pk_v = BtcPk([1u8; 33]);
        println!("Verifier: building {} instances...", N_CC);
        let (verifier, package) = babe_verifier_cac_setup(&vk, static_public_inputs);
        // Verifier sends vk and package to Prover
        println!("Verifier: sending pk_v and {} instance commitment to Prover", N_CC);

        // Prover check the size of package and samples M_CC finalized indices
        assert_eq!(package.commits.len(), N_CC);
        let finalized_indices = cac_finalize_indices(N_CC, M_CC);
        println!("Prover: finalized indices = {:?}", &finalized_indices);

        // Verifier opens non-finalized instances and generates soldering proof.
        println!("Verifier: opening and soldering...");
        let bundle = self.babe_verifier_open_and_solder(&verifier, &finalized_indices)?;

        println!("Prover: verifying opening and soldering proof...");
        // Prover verifies everything.
        self.babe_prover_verify_setup(&package, &bundle, &vk, static_public_inputs, &finalized_indices)?;

        println!("Prover: generating Wots96 signing key...");
        let wots_sk_p = Wots96::generate_secret_key();
        let wots_pk_p = Wots96::generate_public_key(&wots_sk_p);

        // ── Create Txn Set and Presign ──────────────────────────────────────────────────
        println!("Prover: creating Tx Set and pre sign...");
        let h_msgs = finalized_indices.iter().map(|&idx| package.commits[idx].h_msg).collect();
        let tx_challenge_assert_outlock_p = build_ca_outlock(&pk_p, &pk_v, h_msgs);
        let prover_presigs = babe_prover_presign();
        println!("Prover: sending lpk_p, presigs_p to Verifier");
        println!("Verifier: verifying presigs_p...");
        if !babe_verify_prover_presigs(
            &prover_presigs,
            &tx_challenge_assert_outlock_p,
            &pk_p,
            &pk_v,
            &package,
            &finalized_indices,
        ) {
            return Err("invalid prover presignatures".to_string());
        }

        println!("Verifier: creating Tx Set and pre sign...");
        // same as above, no need to implement
        let verifier_presigs = babe_verifier_presign();
        println!("Verifier: sending presigs_v to Verifier...");

        println!("Prover: verifying presigs_p...");
        if !babe_verify_verifier_presigs(&verifier_presigs) {
            return Err("invalid verifier presignatures".to_string());
        }

        // ── Deposit ───────────────────────────────────────────────────────────────

        println!("Prover: submitting Deposit Txn...");
        let deposit_lock = babe_build_deposit_lock(pk_p, pk_v, 100_000);
        // Both parties persist their setup state.
        let prover_state = ProverSetupState {
            wots_sk_p,
            finalized: bundle.finalized,
            soldering: bundle.soldering,
            h_msgs: tx_challenge_assert_outlock_p.h_msgs,
            presigs_v: verifier_presigs,
        };
        let verifier_state = VerifierSetupState {
            verifier,
            finalized_indices,
            wots_pk_p,
            presigs_p: prover_presigs,
        };

        // ── Proving phase ─────────────────────────────────────────────────────────

        // Assert: Prover posts π₁ + x_d and Wots96 sig on-chain.
        let assert_witness = babe_prover_assert(&proof, &prover_state.wots_sk_p, dynamic_public_inputs);
        println!("Prover: posting tx_Assert...");
        println!("tx_Assert witness:            {} bytes", assert_witness.size_bytes());

        // Script: validate tx_Assert (simulates Bitcoin script checks).
        // 1. Check Wots96 sig length.
        let arr_sig: [[u8; 21]; Wots96::TOTAL_DIGIT_LEN as usize] = assert_witness
            .wots_sig
            .clone()
            .try_into()
            .map_err(|_| "tx_Assert: wrong Wots96 signature length".to_string())?;
        // 2. Verify Wots96 sig against the operator public key.
        let msg = Wots96::signature_to_message(&arr_sig);
        if !verifiable_circuit_babe::wots::wots96_verify(&verifier_state.wots_pk_p, &msg, &arr_sig) {
            return Err("tx_Assert: Wots96 signature verification failed".to_string());
        }

        // Verifier: reconstruct the Groth16 proof from tx_Assert and verify it.
        // If valid, no challenge is necessary — the Prover wins the honest path directly.
        // This E2E continues to the challenge path to exercise it end-to-end regardless.
        println!("Verifier: recovering and verifying Groth16 proof from tx_Assert...");
        match assert_witness.try_recover_pi1_xd() {
            None => return Err("tx_Assert: witness is not in correct format (π₁ or x_d malformed)".to_string()),
            Some(_) => {
                if assert_witness.verify_groth16_proof(&vk, &[static_public_inputs]) {
                    println!("Verifier: Groth16 proof is valid — no challenge needed in production.");
                } else {
                    return Err("tx_Assert: Groth16 proof failed to verify".to_string());
                }
            }
        }

        // ChallengeAssert: Verifier verifies Wots sig and reveals base-instance labels.
        let challenge_assert_witness = babe_verifier_challenge_assert_cac(
            &assert_witness,
            &verifier_state,
        )
        .ok_or_else(|| "invalid Wots96 signature in assert witness".to_string())?;
        println!("Verifier: posting tx_ChallengeAssert...");
        println!("tx_ChallengeAssert witness:   {} bytes", challenge_assert_witness.size_bytes());

        println!("Script: checking the valid of Verifier labels...");
        // WronglyChallenged: Prover evaluates GC (base first, then non-base if needed).
        println!("Prover: Finding msg...");
        let (wrongly_challenged_witness, instance_id) =
            babe_prover_wrongly_challenged_cac(
                &vk,
                dynamic_public_inputs,
                &challenge_assert_witness,
                &proof,
                &prover_state,
            )
                .ok_or_else(|| {
                    "failed to recover a valid wrongly-challenged message".to_string()
                })?;
        println!("Prover: posting tx_WronglyChallenged...");
        println!("tx_WronglyChallenged witness: {} bytes", wrongly_challenged_witness.size_bytes());

        // Sanity: msg must satisfy the on-chain hashlock.
        let finalized_id = prover_state
            .finalized
            .iter()
            .position(|data| data.index == instance_id)
            .ok_or_else(|| "recovered instance is not finalized".to_string())?;
        if derive_hashlock(&wrongly_challenged_witness.msg) != prover_state.h_msgs[finalized_id] {
            return Err("recovered message does not match the finalized hashlock".to_string());
        }

        Ok(BabeCACE2ERun {
            deposit_lock,
            assert_witness,
            challenge_assert_witness,
            wrongly_challenged_witness,
        })
    }
}

impl Default for BabeBundleBuilder {
    fn default() -> Self {
        Self::new()
    }
}
