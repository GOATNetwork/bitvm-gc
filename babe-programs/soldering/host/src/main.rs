use std::time::Instant;

use ark_bn254::{Bn254, Fr};
use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK};
use soldering_host::BabeBundleBuilder;
use tracing::info;
use rand::SeedableRng;
use zkm_sdk::{utils as sdk_utils, ZKMStdin};
use verifiable_circuit_babe::babe::DummyMulCircuit;
use verifiable_circuit_babe::prover::GROTH_16_SEED;
use verifiable_circuit_babe::soldering::{
    build_soldered_wires_input, SolderedWiresInput,
};
use verifiable_circuit_babe::verifier::BABEVerifier;

const M_CC: usize = 4; // Number of finalized C&C instances.


fn main() {
    sdk_utils::setup_logger();

    // Prove with the same dummy circuit.
    let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(GROTH_16_SEED);
    let a = Fr::from(3u64);
    let b = Fr::from(7u64);
    let (_pk, vk) = ark_groth16::Groth16::<Bn254>::setup(
        DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) }, &mut rng,
    ).unwrap();
    let static_public_inputs = a * b;

    //  1. Create N_CC instances
    let start = Instant::now();
    let verifier = BABEVerifier::new(M_CC, &vk, static_public_inputs).expect("verifier setup failed");
    info!(elapsed = ?start.elapsed(), n_cc = M_CC, "BABEVerifier created");

    //  2. C&C commit and derive finalized indices
    let package = verifier.commit();
    let finalized_indices = vec![0, 1, 2, 3];

    //  3. Build SolderedWiresInput from finalized instances
    let start = Instant::now();
    let soldering_input = build_soldered_wires_input(&verifier, &finalized_indices);
    info!(elapsed = ?start.elapsed(), "SolderedWiresInput built");

    //  4. Feed input to zkVM guest
    let mut stdin = ZKMStdin::new();
    stdin.write::<SolderedWiresInput>(&soldering_input);

    //  3. Generate and verify soldering proof through the reusable host API.
    let start = Instant::now();
    let builder = BabeBundleBuilder::new();
    let bundle = builder
        .babe_verifier_open_and_solder(&verifier, &finalized_indices)
        .expect("open and solder failed");
    builder
        .babe_prover_verify_setup(&package, &bundle, &vk, static_public_inputs, &finalized_indices)
        .expect("setup verification failed");
    info!(elapsed = ?start.elapsed(), "soldering proof generated and verified");
}
