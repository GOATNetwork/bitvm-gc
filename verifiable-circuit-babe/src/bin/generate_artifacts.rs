/// One-time binary to compile, compact, and write the garbled circuit artifacts.
///
/// Produces 8 artifact files:
///   fgc_gates.bin + fgc_out_indices.bin             (FGC original — for read_flat_original_gc)
///   fgc_compact_gates.bin + fgc_compact_out_indices.bin  (FGC compact — for read_compact_gc)
///   sgc_gates.bin + sgc_out_indices.bin             (SGC original — for read_flat_original_gc)
///   sgc_compact_gates.bin + sgc_compact_out_indices.bin  (SGC compact — for read_compact_gc)
///
/// Output paths are controlled by env vars (defaults shown):
///   FGC_GATES_PATH=./fgc_gates.bin
///   FGC_OUT_INDICES_PATH=./fgc_out_indices.bin
///   FGC_COMPACT_GATES_PATH=./fgc_compact_gates.bin
///   FGC_COMPACT_OUT_INDICES_PATH=./fgc_compact_out_indices.bin
///   SGC_GATES_PATH=./sgc_gates.bin
///   SGC_OUT_INDICES_PATH=./sgc_out_indices.bin
///   SGC_COMPACT_GATES_PATH=./sgc_compact_gates.bin
///   SGC_COMPACT_OUT_INDICES_PATH=./sgc_compact_out_indices.bin
///
/// Run with:
///   cargo run --release --bin generate_artifacts
use ark_bn254::G1Affine;
use verifiable_circuit_babe::gc::generate_compact_artifacts;
use zkm_verifier::{IMM_GROTH16_VK_BYTES, load_ark_groth16_verifying_key_from_bytes};

/// Load the dynamic-input coefficient from Ziren's bundled immutable Groth16 VK.
fn load_immutable_l2_point() -> G1Affine {
    let vk = load_ark_groth16_verifying_key_from_bytes(*IMM_GROTH16_VK_BYTES)
        .expect("failed to parse Ziren immutable Groth16 VK");
    assert_eq!(
        vk.gamma_abc_g1.len(),
        3,
        "Ziren immutable Groth16 VK must contain coefficients for two public inputs",
    );

    vk.gamma_abc_g1[2]
}

fn main() {
    println!("Loading Ziren immutable Groth16 VK...");
    generate_compact_artifacts(load_immutable_l2_point());
}
