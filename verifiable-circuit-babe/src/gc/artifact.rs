use std::fs;
use ark_bn254::G1Affine;
use garbled_snark_verifier::core::gate::GateType;
use garbled_snark_verifier::core::utils::{reset_gid, SerializableGate};

use super::circuit::{
    compile_fgc, compile_sgc_part1, FGC_NUM_PRE_INITIALIZED, SGC_NUM_PRE_INITIALIZED,
};

/// Count gates needing a ciphertext
fn count_non_free(gates: &[(u32, u32, u32, u8, u32)]) -> usize {
    gates.iter()
        .filter(|&&(_, _, _, gt, _)| GateType::try_from(gt).expect("unknown gate type").needs_ciphertext())
        .count()
}

pub struct CircuitStats {
    pub name: &'static str,
    pub num_gates: usize,
    pub non_free_gates: usize,
    pub num_wires_original: usize,
    pub num_pre_initialized: usize,
    pub max_live_wires: usize,
    pub flat_buf_original_mb: f64,
    pub flat_buf_compacted_mb: f64,
    pub compression_ratio: f64,
}

/// Convert a compiled Circuit into a flat (num_wires, gates, output_indices) triple,
/// consuming the circuit so it is dropped immediately after.
fn compile_to_flat(
    circuit: garbled_snark_verifier::bag::Circuit,
    output_indices: Vec<usize>,
) -> (u32, Vec<(u32, u32, u32, u8, u32)>, Vec<usize>) {
    let num_wires = circuit.0.len() as u32;
    let gates = circuit.1.iter().map(|g| (
        g.wire_a.borrow().id.unwrap(),
        g.wire_b.borrow().id.unwrap(),
        g.wire_c.borrow().id.unwrap(),
        g.gate_type as u8,
        g.gid,
    )).collect();
    (num_wires, gates, output_indices)
}

fn compute_last_read(
    gates: &[(u32, u32, u32, u8, u32)],
    num_wires: usize,
    output_indices: &[usize],
    num_pre_initialized: usize,
) -> Vec<u32> {
    let mut last_read = vec![u32::MAX; num_wires];
    for (step, &(a, b, _c, _gt, _gid)) in gates.iter().enumerate() {
        last_read[a as usize] = step as u32;
        last_read[b as usize] = step as u32;
    }
    // Pre-initialized wires (constants 0/1 + inputs) must never be freed.
    for i in 0..num_pre_initialized {
        last_read[i] = u32::MAX;
    }
    // Output wire labels must survive past the garbling loop.
    for &idx in output_indices {
        last_read[idx] = u32::MAX;
    }
    last_read
}

/// Linear-scan register allocator: reassign wire IDs to virtual slot IDs so that
/// dead slots are reused. Rewrites gate tuples and output_indices in-place.
/// Returns max_live_wires (= new num_wires).
fn remap_wire_ids(
    gates: &mut Vec<(u32, u32, u32, u8, u32)>,
    num_wires: &mut u32,
    output_indices: &mut Vec<usize>,
    last_read: &[u32],
    num_pre_initialized: usize,
) -> usize {
    let original_num_wires = *num_wires as usize;
    let mut slot_of = vec![u32::MAX; original_num_wires];
    let mut free_list: Vec<u32> = Vec::new();
    let mut next_fresh: u32 = 0;
    let mut max_slot: u32 = 0;

    for wire_id in 0..num_pre_initialized {
        slot_of[wire_id] = next_fresh;
        max_slot = max_slot.max(next_fresh);
        next_fresh += 1;
    }

    for (step, gate) in gates.iter_mut().enumerate() {
        let (a, b, c, _gt, _gid) = *gate;
        let step_u32 = step as u32;

        let sa = slot_of[a as usize];
        let sb = slot_of[b as usize];

        // Allocate output slot BEFORE freeing inputs. This guarantees c's slot never
        // equals a's or b's slot within the same gate.
        let slot = free_list.pop().unwrap_or_else(|| {
            let s = next_fresh;
            next_fresh += 1;
            s
        });
        slot_of[c as usize] = slot;
        max_slot = max_slot.max(slot);

        gate.0 = sa;
        gate.1 = sb;
        gate.2 = slot;

        // Free dying input slots after c is assigned — slots become available for
        // subsequent gates.
        if last_read[a as usize] == step_u32 {
            free_list.push(sa);
        }
        if b != a && last_read[b as usize] == step_u32 {
            free_list.push(sb);
        }
    }

    for idx in output_indices.iter_mut() {
        *idx = slot_of[*idx] as usize;
    }

    let max_live_wires = max_slot as usize + 1;
    *num_wires = max_live_wires as u32;
    max_live_wires
}

fn write_circuit(
    num_wires: u32,
    gates: &[(u32, u32, u32, u8, u32)],
    output_indices: &[usize],
    gates_path: &str,
    indices_path: &str,
) {
    let serializable: Vec<SerializableGate> = gates.iter().map(|&(a, b, c, gt, gid)| {
        SerializableGate { wire_a_id: a, wire_b_id: b, wire_c_id: c, gate_type: gt, gid }
    }).collect();
    let gates_bytes = bincode::serialize(&(super::ARTIFACT_VERSION, num_wires, &serializable)).expect("serialize gates");
    fs::write(gates_path, &gates_bytes).expect("write gates");
    let idx_bytes = bincode::serialize(&output_indices).expect("serialize indices");
    fs::write(indices_path, &idx_bytes).expect("write indices");
}

fn print_report(stats: &[CircuitStats; 2]) {
    println!("\n=== Circuit Artifact Report ===");
    let mut total_before = 0.0f64;
    let mut total_after = 0.0f64;
    for s in stats {
        println!("\n[{}]", s.name);
        println!("  Gates:              {:>15}", s.num_gates);
        println!("  Non-free gates:     {:>15}", s.non_free_gates);
        println!("  Wires (original):   {:>15}", s.num_wires_original);
        println!("  Pre-initialized:    {:>15}", s.num_pre_initialized);
        println!("  Max live wires:     {:>15}", s.max_live_wires);
        println!("  FlatEvalBuffer:     {:>10.2} MB  →  {:>8.2} MB",
                 s.flat_buf_original_mb, s.flat_buf_compacted_mb);
        println!("  Compression:        {:.1}×", s.compression_ratio);
        total_before += s.flat_buf_original_mb;
        total_after  += s.flat_buf_compacted_mb;
    }
    println!("\n[Verifier RAM per instance (FlatEvalBuffer)]");
    println!("  Before: {:.2} MB", total_before);
    println!("  After:  {:.2} MB  ({:.1}× reduction)",
             total_after, total_before / total_after);

    println!("\n[Non-free gate counts]");
    println!("  FGC: {}", stats[0].non_free_gates);
    println!("  SGC: {}", stats[1].non_free_gates);
}

/// Generate, compact, and write all circuit artifacts from scratch.
pub fn generate_compact_artifacts(l2_point: G1Affine) -> [CircuitStats; 2] {
    reset_gid();

    // ── FGC ──────────────────────────────────────────────────────────────────
    println!("[1/6] Compiling FGC...");
    let (bld, fgc_out_idx) = compile_fgc();
    let (mut fgc_num_wires, mut fgc_gates, mut fgc_out_idx) =
        compile_to_flat(bld.build(&[]), fgc_out_idx);
    let fgc_wires_orig = fgc_num_wires as usize;

    // Write original (non-compacted) artifacts for read_flat_original_gc() BEFORE remapping.
    write_circuit(fgc_num_wires, &fgc_gates, &fgc_out_idx,
                  &super::fgc_gates_path(), &super::fgc_indices_path());

    println!("[2/6] Analyzing FGC liveness ({} gates, {} wires)...", fgc_gates.len(), fgc_wires_orig);
    let fgc_last_read = compute_last_read(&fgc_gates, fgc_wires_orig, &fgc_out_idx, FGC_NUM_PRE_INITIALIZED);
    let fgc_max_live = remap_wire_ids(
        &mut fgc_gates, &mut fgc_num_wires, &mut fgc_out_idx,
        &fgc_last_read, FGC_NUM_PRE_INITIALIZED,
    );

    println!("[3/6] Writing FGC compact artifacts (max_live_wires = {})...", fgc_max_live);
    write_circuit(fgc_num_wires, &fgc_gates, &fgc_out_idx,
                  &super::fgc_compact_gates_path(), &super::fgc_compact_indices_path());

    let fgc_stats = CircuitStats {
        name: "FGC",
        num_gates: fgc_gates.len(),
        non_free_gates: count_non_free(&fgc_gates),
        num_wires_original: fgc_wires_orig,
        num_pre_initialized: FGC_NUM_PRE_INITIALIZED,
        max_live_wires: fgc_max_live,
        flat_buf_original_mb:  (fgc_wires_orig * 16) as f64 / (1 << 20) as f64,
        flat_buf_compacted_mb: (fgc_max_live  * 16) as f64 / (1 << 20) as f64,
        compression_ratio: fgc_wires_orig as f64 / fgc_max_live as f64,
    };

    // ── SGC Part 1 ───────────────────────────────────────────────────────────
    println!("[4/6] Compiling SGC Part 1...");
    let (bld, sgc_out_idx) = compile_sgc_part1(l2_point);
    let (mut sgc_num_wires, mut sgc_gates, mut sgc_out_idx) =
        compile_to_flat(bld.build(&[]), sgc_out_idx);
    let sgc_wires_orig = sgc_num_wires as usize;

    write_circuit(sgc_num_wires, &sgc_gates, &sgc_out_idx,
                  &super::sgc_gates_path(), &super::sgc_indices_path());

    println!("[5/6] Analyzing SGC liveness ({} gates, {} wires)...", sgc_gates.len(), sgc_wires_orig);
    let sgc_last_read = compute_last_read(&sgc_gates, sgc_wires_orig, &sgc_out_idx, SGC_NUM_PRE_INITIALIZED);
    let sgc_max_live = remap_wire_ids(
        &mut sgc_gates, &mut sgc_num_wires, &mut sgc_out_idx,
        &sgc_last_read, SGC_NUM_PRE_INITIALIZED,
    );

    println!("[6/6] Writing SGC compact artifacts (max_live_wires = {})...", sgc_max_live);
    write_circuit(sgc_num_wires, &sgc_gates, &sgc_out_idx,
                  &super::sgc_compact_gates_path(), &super::sgc_compact_indices_path());

    let sgc_stats = CircuitStats {
        name: "SGC Part 1",
        num_gates: sgc_gates.len(),
        non_free_gates: count_non_free(&sgc_gates),
        num_wires_original: sgc_wires_orig,
        num_pre_initialized: SGC_NUM_PRE_INITIALIZED,
        max_live_wires: sgc_max_live,
        flat_buf_original_mb:  (sgc_wires_orig * 16) as f64 / (1 << 20) as f64,
        flat_buf_compacted_mb: (sgc_max_live  * 16) as f64 / (1 << 20) as f64,
        compression_ratio: sgc_wires_orig as f64 / sgc_max_live as f64,
    };

    let stats = [fgc_stats, sgc_stats];
    print_report(&stats);
    stats
}

#[cfg(test)]
mod tests {
    use ark_ec::AffineRepr;
    use super::*;

    #[test]
    #[ignore]
    fn test_generate_compact_artifacts() {
        let stats = generate_compact_artifacts(G1Affine::generator());
        println!("FGC  compression: {:.1}x", stats[0].compression_ratio);
        println!("SGC  compression: {:.1}x", stats[1].compression_ratio);
        assert!(stats[0].max_live_wires < stats[0].num_wires_original,
                "FGC: expected some compaction");
        assert!(stats[1].max_live_wires < stats[1].num_wires_original,
                "SGC: expected some compaction");
    }
}
