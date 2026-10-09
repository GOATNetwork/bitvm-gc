/// Test-only binary: writes the 8 garbled circuit artifacts for the `DummyMulCircuit` VK
/// instead of Ziren's. Tests marked "requires artifacts match the dummy vk" need these.
///
/// The Groth16 VK depends only on the RNG seed and the circuit shape, so every test that
/// sets up `DummyMulCircuit` with `GROTH_16_SEED` shares the same L_2.
///
/// Output paths are the same as `generate_artifacts` (same env vars and defaults), so this
/// overwrites the Ziren artifacts. Re-run `generate_artifacts` before using real Ziren proofs.
///
/// Run with:
///   cargo run --release --bin generate_dummy_artifacts
use ark_bn254::{Bn254, Fr};
use ark_crypto_primitives::snark::CircuitSpecificSetupSNARK;
use ark_groth16::Groth16;
use rand::SeedableRng;
use verifiable_circuit_babe::babe::DummyMulCircuit;
use verifiable_circuit_babe::gc::generate_compact_artifacts;
use verifiable_circuit_babe::prover::GROTH_16_SEED;
use verifiable_circuit_babe::utils::dynamic_base;

fn main() {
    let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(GROTH_16_SEED);
    let circuit = DummyMulCircuit::<Fr> { a: Some(Fr::from(3u64)), b: Some(Fr::from(7u64)) };
    let (_, vk) = Groth16::<Bn254>::setup(circuit, &mut rng).expect("failed to set up DummyMulCircuit");
    let l2_point = dynamic_base(&vk).expect("dummy VK does not match the public-input layout");
    println!("Dummy VK L_2 = {l2_point}");
    generate_compact_artifacts(l2_point);
}
