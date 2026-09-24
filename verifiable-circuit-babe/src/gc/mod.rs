mod adaptor;
pub mod artifact;
pub mod utils;
pub mod circuit;

use std::cell::RefCell;
use std::fs;
use std::rc::Rc;
use std::sync::OnceLock;
pub use artifact::*;
pub use circuit::*;
pub use adaptor::*;
use garbled_snark_verifier::bag::{Circuit, Gate, S, Wire};
use garbled_snark_verifier::core::gate::{gate_garbled_with_delta, GateType};
use garbled_snark_verifier::core::utils::SerializableGate;
pub use utils::*;

/// Increment this whenever the circuit compilation or artifact serialization format changes.
/// Both readers (`flat_from_bytes`, `deserialize_circuit`) assert this value matches what
/// is stored on disk; a mismatch means stale artifacts — re-run `generate_artifacts`.
pub const ARTIFACT_VERSION: u32 = 1;

/// Hard upper bound on `num_wires` read from an artifact file.
/// Prevents a crafted or corrupted file from triggering a multi-GB allocation.
const MAX_CIRCUIT_WIRES: u32 = 1_000_000_000;

// ── Flat artifact paths (unique wire IDs, used by read_flat_original_gc) ──────────────
// garbled_evaluate_without_delta requires each Wire to be the output of exactly
// one gate. These are the pre-compaction artifacts that preserve that invariant.
fn fgc_gates_path() -> String {
    std::env::var("FGC_GATES_PATH").unwrap_or_else(|_| "./fgc_gates.bin".to_string())
}

fn fgc_indices_path() -> String {
    std::env::var("FGC_OUT_INDICES_PATH").unwrap_or_else(|_| "./fgc_out_indices.bin".to_string())
}

fn sgc_gates_path() -> String {
    std::env::var("SGC_GATES_PATH").unwrap_or_else(|_| "./sgc_gates.bin".to_string())
}

fn sgc_indices_path() -> String {
    std::env::var("SGC_OUT_INDICES_PATH").unwrap_or_else(|_| "./sgc_out_indices.bin".to_string())
}

// ── Compact artifact paths (slot-reused wire IDs, used by read_compact_gc) ───
// Wire IDs are remapped to minimise FlatEvalBuffer size. Each slot may be reused
// across gate steps (safe for Vec<[u8;16]> reads-before-write, not for RefCell).
fn fgc_compact_gates_path() -> String {
    std::env::var("FGC_COMPACT_GATES_PATH").unwrap_or_else(|_| "./fgc_compact_gates.bin".to_string())
}

fn fgc_compact_indices_path() -> String {
    std::env::var("FGC_COMPACT_OUT_INDICES_PATH").unwrap_or_else(|_| "./fgc_compact_out_indices.bin".to_string())
}

fn sgc_compact_gates_path() -> String {
    std::env::var("SGC_COMPACT_GATES_PATH").unwrap_or_else(|_| "./sgc_compact_gates.bin".to_string())
}

fn sgc_compact_indices_path() -> String {
    std::env::var("SGC_COMPACT_OUT_INDICES_PATH").unwrap_or_else(|_| "./sgc_compact_out_indices.bin".to_string())
}

// ── Flat circuit ──────────────────────────────────────────────────────────────

/// Gate topology stored as a flat Vec of tuples — used by both compact and original paths.
pub struct FlatGates {
    pub num_wires: usize,
    /// (wire_a_id, wire_b_id, wire_c_id, gate_type_u8, gid) — 20 bytes/gate,
    /// contiguous in memory so the hardware prefetcher can work effectively.
    pub gates: Vec<(u32, u32, u32, u8, u32)>,
}

/// Per-instance mutable label state for the flat garble path.
pub struct FlatEvalBuffer {
    pub labels: Vec<[u8; 16]>,
}

impl FlatEvalBuffer {
    pub fn new(num_wires: usize) -> Self {
        assert!(
            num_wires <= MAX_CIRCUIT_WIRES as usize,
            "num_wires={num_wires} exceeds safety limit — artifact may be corrupted"
        );
        Self { labels: vec![[0u8; 16]; num_wires] }
    }

    #[inline]
    pub fn set_label(&mut self, wire_id: usize, label: [u8; 16]) {
        self.labels[wire_id] = label;
    }

    /// Garble every gate, stream-hash all ciphertexts, and return
    /// `(com_gc, output_label_pairs)` where each pair is `[l0, l1]`
    /// with `l1 = l0 ^ delta`.
    pub fn garble_and_hash(
        &mut self,
        flat: &FlatGates,
        output_indices: &[usize],
        delta: [u8; 16],
        salt: Option<S>,
    ) -> ([u8; 32], Vec<[u8; 16]>) {
        use sha2::{Digest, Sha256};

        let delta_s = S(delta);
        let mut hasher = Sha256::new();

        for &(a, b, c, gt, gid) in &flat.gates {
            let a0 = S(self.labels[a as usize]);
            let b0 = S(self.labels[b as usize]);
            let gate_type = GateType::try_from(gt).expect("unknown gate type");
            let (c0, ct) = gate_garbled_with_delta(a0, b0, gid, gate_type, delta_s, salt);
            self.labels[c as usize] = c0.0;
            if let Some(s) = ct {
                hasher.update(s.0);
            }
        }

        let hash: [u8; 32] = hasher.finalize().into();
        let output_labels: Vec<[u8; 16]> = output_indices
            .iter()
            .flat_map(|&idx| {
                let l0 = S(self.labels[idx]);
                [l0.0, (l0 ^ delta_s).0]
            })
            .collect();
        (hash, output_labels)
    }

    /// Like `garble_and_hash` but materializes ciphertexts for the evaluator path.
    /// Returns only the ciphertexts of gates that actually need one 
    pub fn garble_and_collect(
        &mut self,
        flat: &FlatGates,
        output_indices: &[usize],
        delta: [u8; 16],
        salt: Option<S>,
    ) -> (Vec<S>, Vec<[u8; 16]>) {
        let delta_s = S(delta);
        let non_free_gates_count = count_non_free_gates(flat);
        let mut ciphertexts = Vec::with_capacity(non_free_gates_count);

        for &(a, b, c, gt, gid) in &flat.gates {
            let a0 = S(self.labels[a as usize]);
            let b0 = S(self.labels[b as usize]);
            let gate_type = GateType::try_from(gt).expect("unknown gate type");
            let (c0, ct) = gate_garbled_with_delta(a0, b0, gid, gate_type, delta_s, salt);
            self.labels[c as usize] = c0.0;
            if let Some(s) = ct {
                ciphertexts.push(s);
            }
        }

        let output_labels: Vec<[u8; 16]> = output_indices
            .iter()
            .flat_map(|&idx| {
                let l0 = S(self.labels[idx]);
                [l0.0, (l0 ^ delta_s).0]
            })
            .collect();
        (ciphertexts, output_labels)
    }
}

static COMPACT_FGC: OnceLock<(FlatGates, Vec<usize>)> = OnceLock::new();
static COMPACT_SGC: OnceLock<(FlatGates, Vec<usize>)> = OnceLock::new();

/// Load compact FGC and SGC gate data into `FlatGates`, cached on first call.
/// Wire IDs are slot-remapped to minimise `FlatEvalBuffer` size.
/// Raw bytes are read once then dropped — not retained in static memory.
pub fn read_compact_gc() -> (
    &'static FlatGates, &'static Vec<usize>,
    &'static FlatGates, &'static Vec<usize>,
) {
    let (fgc_flat, fgc_idx) = COMPACT_FGC.get_or_init(|| {
        let gates_path = fgc_compact_gates_path();
        let indices_path = fgc_compact_indices_path();
        let gates_bytes = fs::read(&gates_path)
            .unwrap_or_else(|_| panic!("'{}' not found — run: cargo run -r --bin generate_artifacts", gates_path));
        let idx_bytes = fs::read(&indices_path)
            .unwrap_or_else(|_| panic!("'{}' not found — run: cargo run -r --bin generate_artifacts", indices_path));
        flat_from_bytes(&gates_bytes, &idx_bytes)
    });
    let (sgc_flat, sgc_idx) = COMPACT_SGC.get_or_init(|| {
        let gates_path = sgc_compact_gates_path();
        let indices_path = sgc_compact_indices_path();
        let gates_bytes = fs::read(&gates_path)
            .unwrap_or_else(|_| panic!("'{}' not found — run: cargo run -r --bin generate_artifacts", gates_path));
        let idx_bytes = fs::read(&indices_path)
            .unwrap_or_else(|_| panic!("'{}' not found — run: cargo run -r --bin generate_artifacts", indices_path));
        flat_from_bytes(&gates_bytes, &idx_bytes)
    });
    // derive and cache the non-free-gate counts
    NON_FREE_GATES_COUNTS.get_or_init(|| [count_non_free_gates(fgc_flat), count_non_free_gates(sgc_flat)]);
    (fgc_flat, fgc_idx, sgc_flat, sgc_idx)
}

static NON_FREE_GATES_COUNTS: OnceLock<[usize; 2]> = OnceLock::new();

pub fn non_free_gates_counts() -> [usize; 2] {
    if let Some(counts) = NON_FREE_GATES_COUNTS.get() {
        return *counts;
    }
    read_compact_gc();
    *NON_FREE_GATES_COUNTS.get().expect("read_compact_gc() must populate NON_FREE_GATES_COUNTS")
}

fn flat_from_bytes(gates_bytes: &[u8], output_indices_bytes: &[u8]) -> (FlatGates, Vec<usize>) {
    let (version, num_wires, gates_read): (u32, u32, Vec<SerializableGate>) =
        bincode::deserialize(gates_bytes).expect("deserialize gates");
    assert!(
        version == ARTIFACT_VERSION,
        "artifact version {version} != expected {ARTIFACT_VERSION} — re-run: cargo run -r --bin generate_artifacts"
    );
    let output_indices: Vec<usize> =
        bincode::deserialize(output_indices_bytes).expect("deserialize indices");
    let flat = FlatGates {
        num_wires: num_wires as usize,
        gates: gates_read
            .iter()
            .map(|g| (g.wire_a_id, g.wire_b_id, g.wire_c_id, g.gate_type, g.gid))
            .collect(),
    };
    (flat, output_indices)
}

/// Load both circuits as Rc/RefCell-based `Circuit` for evaluation.
pub fn read_flat_original_gc() -> (Circuit, Vec<usize>, Circuit, Vec<usize>) {
    let fgc_gates_bytes = fs::read(fgc_gates_path())
        .unwrap_or_else(|_| panic!("'{}' not found — run: cargo run -r --bin generate_artifacts", fgc_gates_path()));
    let fgc_idx_bytes = fs::read(fgc_indices_path())
        .unwrap_or_else(|_| panic!("'{}' not found — run: cargo run -r --bin generate_artifacts", fgc_indices_path()));
    let (fgc, fgc_indices) = deserialize_circuit(&fgc_gates_bytes, &fgc_idx_bytes);

    let sgc_gates_bytes = fs::read(sgc_gates_path())
        .unwrap_or_else(|_| panic!("'{}' not found — run: cargo run -r --bin generate_artifacts", sgc_gates_path()));
    let sgc_idx_bytes = fs::read(sgc_indices_path())
        .unwrap_or_else(|_| panic!("'{}' not found — run: cargo run -r --bin generate_artifacts", sgc_indices_path()));
    let (sgc, sgc_indices) = deserialize_circuit(&sgc_gates_bytes, &sgc_idx_bytes);

    (fgc, fgc_indices, sgc, sgc_indices)
}

fn deserialize_circuit(gates_bytes: &[u8], output_indices_bytes: &[u8]) -> (Circuit, Vec<usize>) {
    let (version, num_wires, gates_read): (u32, u32, Vec<SerializableGate>) =
        bincode::deserialize(gates_bytes).expect("deserialize gates");
    assert!(
        version == ARTIFACT_VERSION,
        "artifact version {version} != expected {ARTIFACT_VERSION} — re-run: cargo run -r --bin generate_artifacts"
    );
    let output_indices: Vec<usize> =
        bincode::deserialize(output_indices_bytes).expect("deserialize indices");

    let wires: Vec<_> = (0..num_wires)
        .map(|id| Rc::new(RefCell::new(Wire { label: None, value: None, id: Some(id) })))
        .collect();
    wires[0].borrow_mut().value = Some(false);
    wires[1].borrow_mut().value = Some(true);

    let gates: Vec<Gate> = gates_read.iter().map(|sg| {
        Gate::new_with_gid(
            wires[sg.wire_a_id as usize].clone(),
            wires[sg.wire_b_id as usize].clone(),
            wires[sg.wire_c_id as usize].clone(),
            GateType::try_from(sg.gate_type).expect("unknown gate type"),
            sg.gid,
        )
    }).collect();

    (Circuit(wires, gates), output_indices)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Verify that compact artifacts produce identical ciphertexts and output labels
    /// to the original (non-compacted) artifacts given the same pre-initialized labels.
    /// Requires artifacts on disk — run `cargo run --release --bin generate_artifacts` first.
    #[test]
    #[ignore]
    fn test_compact_garbling_matches_original() {
        let delta = [0xAAu8; 16];
        // Non-C&C default salt
        let salt = Some(garbled_snark_verifier::core::utils::NON_CAC_SALT);

        // ── FGC ──────────────────────────────────────────────────────────────
        let (fgc_compact, fgc_compact_idx, sgc_compact, sgc_compact_idx) = read_compact_gc();

        let fgc_bytes = std::fs::read(fgc_gates_path())
            .expect("fgc_gates.bin missing — run generate_compact_artifacts first");
        let fgc_idx = std::fs::read(fgc_indices_path())
            .expect("fgc_out_indices.bin missing");
        let (fgc_orig, fgc_orig_idx) = flat_from_bytes(&fgc_bytes, &fgc_idx);

        let mut buf_compact = FlatEvalBuffer::new(fgc_compact.num_wires);
        let mut buf_orig    = FlatEvalBuffer::new(fgc_orig.num_wires);
        for i in 0..FGC_NUM_PRE_INITIALIZED {
            // Deterministic distinct label per pre-initialized wire
            let label = [i as u8, (i >> 8) as u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
            buf_compact.set_label(i, label);
            buf_orig.set_label(i, label);
        }

        let (ct_compact, out_compact) = buf_compact.garble_and_collect(fgc_compact, fgc_compact_idx, delta, salt);
        let (ct_orig,    out_orig)    = buf_orig.garble_and_collect(&fgc_orig, &fgc_orig_idx, delta, salt);

        assert_eq!(ct_compact, ct_orig,    "FGC: ciphertexts differ (compact vs original)");
        assert_eq!(out_compact, out_orig,  "FGC: output labels differ");
        println!("FGC: compact garbling matches original ✓");

        // ── SGC ──────────────────────────────────────────────────────────────
        let sgc_bytes = std::fs::read(sgc_gates_path())
            .expect("sgc_gates.bin missing");
        let sgc_idx = std::fs::read(sgc_indices_path())
            .expect("sgc_out_indices.bin missing");
        let (sgc_orig, sgc_orig_idx) = flat_from_bytes(&sgc_bytes, &sgc_idx);

        let mut buf_compact = FlatEvalBuffer::new(sgc_compact.num_wires);
        let mut buf_orig    = FlatEvalBuffer::new(sgc_orig.num_wires);
        for i in 0..SGC_NUM_PRE_INITIALIZED {
            let label = [i as u8, (i >> 8) as u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
            buf_compact.set_label(i, label);
            buf_orig.set_label(i, label);
        }

        let (ct_compact, out_compact) = buf_compact.garble_and_collect(sgc_compact, sgc_compact_idx, delta, salt);
        let (ct_orig,    out_orig)    = buf_orig.garble_and_collect(&sgc_orig, &sgc_orig_idx, delta, salt);

        assert_eq!(ct_compact, ct_orig,    "SGC: ciphertexts differ (compact vs original)");
        assert_eq!(out_compact, out_orig,  "SGC: output labels differ");
        println!("SGC: compact garbling matches original ✓");
    }
}
