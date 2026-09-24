use ark_bn254::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup, Zero};
use sha2::{Digest, Sha256};
use garbled_snark_verifier::circuits::sect233k1::builder::{CircuitAdapter, CircuitTrait};
use garbled_snark_verifier::dv_bn254::basic::{not, selector};
use garbled_snark_verifier::dv_bn254::fp254impl::Fp254Impl;
use garbled_snark_verifier::dv_bn254::{fq::Fq, fr::Fr};
use garbled_snark_verifier::dv_bn254::g1::{projective_to_affine_montgomery, G1Projective as GcG1Projective, G1Projective};
use garbled_snark_verifier::core::gate::GateType;

use crate::dre::{N, N_PADDED, Q_SIZE, U_BAR_SIZE};
use crate::gc::FlatGates;

// Unsigned 8-bit windowed scalar-mul parameters. Must match the `SCALAR_WINDOW_*`
// constants in garbled-snark-verifier's dv_bn254::g1. With w=8 we do 32 mixed-adds
// over a full 256-entry precomputed table. x_d is supplied as plain Fr bits (LSB-first).
pub const WINDOW_BITS: usize = 8;
pub const WINDOW_COUNT: usize = (Fr::N_BITS + WINDOW_BITS - 1) / WINDOW_BITS; // 32
pub const WINDOW_ENTRIES: usize = 1 << WINDOW_BITS; // 256
pub const PRECOMP_TABLE_BITS: usize = WINDOW_COUNT * WINDOW_ENTRIES * 2 * N;
pub const SGC_PART1_CONSTANT_SIZE: usize = 2 + 2 * N; // 0/1 + B.

/// Number of wires initialized before the garbling loop in each circuit.
/// These are assigned slots 0..N-1 by the liveness allocator and must match
/// the `set_label` indices used in `CACInstance::new_from_seed` / `commit_from_seed`.
pub const FGC_NUM_PRE_INITIALIZED: usize = 2 + 2 * N_PADDED;   // wire0, wire1, π_x(N_PADDED), π_y(N_PADDED)
pub const SGC_NUM_PRE_INITIALIZED: usize = SGC_PART1_CONSTANT_SIZE + N_PADDED; // wire0,1 + B + x_d


// ── Circuit 1 / FGC ────────────────────────────────────────────────────────

/// Compile the FGC: evaluates the ū(π) subcircuit.
///
/// Input wire layout:
///   [0..N)    π_x — x-coordinate of π (evaluator input)
///   [N..2·N)  π_y — y-coordinate of π (evaluator input)
///
/// `g` is the fallback point, embedded as constant wires.
///
/// Output: U_BAR_SIZE bits — ū(π) when π is on the curve, ū(g) otherwise.
pub fn compile_fgc() -> (CircuitAdapter, Vec<usize>) {
    let mut bld = CircuitAdapter::default();

    let pi_x_all: Vec<usize> = (0..N_PADDED).map(|_| bld.fresh_one()).collect();
    let pi_y_all: Vec<usize> = (0..N_PADDED).map(|_| bld.fresh_one()).collect();

    let output_indices = emit_fgc(&mut bld, &pi_x_all, &pi_y_all);
    (bld, output_indices)
}

fn emit_fgc(
    bld: &mut CircuitAdapter,
    pi_x_all: &[usize],
    pi_y_all: &[usize],
) -> Vec<usize> {
    let pi_x = &pi_x_all[..N];
    let pi_y = &pi_y_all[..N];

    // R² mod p — converts normal → Montgomery form
    let r_sq = Fq::as_montgomery(Fq::as_montgomery(ark_bn254::Fq::from(1u64)));

    let x_m = Fq::mul_by_constant_montgomery(bld, pi_x, r_sq);
    let y_m = Fq::mul_by_constant_montgomery(bld, pi_y, r_sq);

    let x_sq_m = Fq::square_montgomery(bld, &x_m);
    let y_sq_m = Fq::square_montgomery(bld, &y_m);
    let xy_m   = Fq::mul_montgomery(bld, &x_m, &y_m);
    let x_cu_m = Fq::mul_montgomery(bld, &x_sq_m, &x_m);

    let three_mont = Fq::as_montgomery(ark_bn254::Fq::from(3u64));
    let rhs_m    = Fq::add_constant(bld, &x_cu_m, three_mont);
    let on_curve = Fq::equal(bld, &y_sq_m, &rhs_m);

    // MSB slots (bits N and N+1 of each coordinate) must be zero for a valid field element.
    let any_msb_x = bld.or_wire(pi_x_all[N], pi_x_all[N + 1]);
    let any_msb_y = bld.or_wire(pi_y_all[N], pi_y_all[N + 1]);
    let any_msb   = bld.or_wire(any_msb_x, any_msb_y);
    let msb_ok    = not(bld, any_msb);
    let valid     = bld.and_wire(on_curve, msb_ok);

    // montgomery_reduce(A·R ‖ 0) = A — converts back to standard form
    let x_sq = Fq::mul_by_constant_montgomery(bld, &x_sq_m, ark_bn254::Fq::from(1u64));
    let y_sq = Fq::mul_by_constant_montgomery(bld, &y_sq_m, ark_bn254::Fq::from(1u64));
    let xy   = Fq::mul_by_constant_montgomery(bld, &xy_m,   ark_bn254::Fq::from(1u64));

    let mut pi_u_bar: Vec<usize> = Vec::with_capacity(U_BAR_SIZE);
    pi_u_bar.push(bld.one());
    pi_u_bar.extend_from_slice(pi_x);
    pi_u_bar.extend_from_slice(pi_y);
    pi_u_bar.extend(x_sq);
    pi_u_bar.extend(y_sq);
    pi_u_bar.extend(xy);
    assert_eq!(pi_u_bar.len(), U_BAR_SIZE);

    let g_u_bar = g_u_bar_indices(bld);

    (0..U_BAR_SIZE)
        .map(|k| selector(bld, pi_u_bar[k], g_u_bar[k], valid))
        .collect()
}

// ── Circuit 2 Part 1 / SGC Part 1 ──────────────────────────────────────────

/// Compile SGC Part 1: computes Q = x_d · L_2 + B.
///
/// `l2` is fixed and is embedded as constant wires.
/// B is garbler-private and supplied as input wires.
///
/// Input wire layout:
///   [0..N)            B_x — x-coordinate of B, Montgomery form (garbler-private)
///   [N..2·N)          B_y — y-coordinate of B, Montgomery form (garbler-private)
///   [2·N..2·N+N_PADDED) x_d — scalar bits LSB-first + 2 MSB slots (evaluator input)
///
/// Output: Q_SIZE = 2·N bits — (x, y) of Q in standard affine form,
///         or G1 generator if any MSB slot is non-zero.
pub fn compile_sgc_part1(l2: G1Affine) -> (CircuitAdapter, Vec<usize>) {
    let mut bld = CircuitAdapter::default();

    // B — garbler-private affine point, Montgomery form
    let b_x = Fq::wires(&mut bld);
    let b_y = Fq::wires(&mut bld);

    let x_d: Vec<usize> = (0..N_PADDED).map(|_| bld.fresh_one()).collect();

    // MSB slots must be zero for a valid Fr scalar.
    let any_msb = bld.or_wire(x_d[N], x_d[N + 1]);
    let msb_ok  = not(&mut bld, any_msb);

    // L_2 table — embedded as constant wires
    let table_wires: Vec<usize> = build_l2_table_bits(&l2)
        .into_iter()
        .map(|bit| if bit { bld.one() } else { bld.zero() })
        .collect();
    assert_eq!(table_wires.len(), PRECOMP_TABLE_BITS);

    let q_output = emit_scalar_mul_then_add(&mut bld, &x_d[..N], &b_x.0, &b_y.0, &table_wires);

    // Fallback to G1 generator when MSBs are non-zero.
    let generator = G1Affine::generator();
    let gen_output: Vec<usize> = Fq::to_bits(generator.x).into_iter()
        .chain(Fq::to_bits(generator.y))
        .map(|b| if b { bld.one() } else { bld.zero() })
        .collect();
    assert_eq!(gen_output.len(), Q_SIZE);

    let output_indices: Vec<usize> = q_output.iter().zip(gen_output.iter())
        .map(|(&real, &fallback)| selector(&mut bld, real, fallback, msb_ok))
        .collect();
    (bld, output_indices)
}


/// Emit: scalar_point = x_d · L_2 (windowed private table) then add affine point P.
///
/// Wire indices for the affine point and table may be input or constant wires.
/// Output: Q_SIZE bits — (x, y) in standard affine form.
fn emit_scalar_mul_then_add(
    bld: &mut CircuitAdapter,
    x_d: &[usize],
    p_x_wires: &[usize],
    p_y_wires: &[usize],
    table_wires: &[usize],
) -> Vec<usize> {
    assert_eq!(table_wires.len(), PRECOMP_TABLE_BITS);

    let prod_proj_m = GcG1Projective::scalar_mul_private_table_circuit(bld, x_d, table_wires);

    let mut p_affine_m: Vec<usize> = p_x_wires.to_vec();
    p_affine_m.extend_from_slice(p_y_wires);
    let result_proj_m =
        GcG1Projective::add_mixed_montgomery_no_inf(bld, &prod_proj_m, &p_affine_m);

    // Convert projective Montgomery (X·R, Y·R, Z·R) → standard affine (x, y)
    // x = X/Z, y = Y/Z via Fermat inversion of Z in the Montgomery domain
    let x_m: [usize; N] = result_proj_m[..N].try_into().unwrap();
    let y_m: [usize; N] = result_proj_m[N..2 * N].try_into().unwrap();
    let z_m: [usize; N] = result_proj_m[2 * N..].try_into().unwrap();
    let mont_res_proj = G1Projective {
        x: Fq(x_m),
        y: Fq(y_m),
        z: Fq(z_m),
    };
    let (mont_res_affine, _is_valid) = projective_to_affine_montgomery(bld, &mont_res_proj);
    // convert back to standard form
    let x_q = Fq::mul_by_constant_montgomery(bld, &mont_res_affine.x.0, ark_bn254::Fq::from(1u64));
    let y_q = Fq::mul_by_constant_montgomery(bld, &mont_res_affine.y.0, ark_bn254::Fq::from(1u64));

    let mut output = Vec::with_capacity(Q_SIZE);
    output.extend_from_slice(&x_q);
    output.extend_from_slice(&y_q);
    assert_eq!(output.len(), Q_SIZE);
    output
}

/// Build constant wire indices for ū(G1 generator) — the fallback output.
fn g_u_bar_indices(bld: &mut CircuitAdapter) -> Vec<usize> {
    let g    = G1Affine::generator();
    let x    = g.x;
    let y    = g.y;
    let x_sq = x * x;
    let y_sq = y * y;
    let xy   = x * y;

    let mut indices: Vec<usize> = Vec::with_capacity(U_BAR_SIZE);
    indices.push(bld.one());

    for val in [x, y, x_sq, y_sq, xy] {
        let bits = Fq::to_bits(val);
        for &b in bits.iter().take(N) {
            indices.push(if b { bld.one() } else { bld.zero() });
        }
    }

    assert_eq!(indices.len(), U_BAR_SIZE);
    indices
}

/// SHA256 commitment to a dense GC ciphertext list (only entries from gates where
/// `GateType::needs_ciphertext()` is true — free-XOR gates don't get a slot).
pub fn gc_ciphertexts_commit(ciphertexts: &[garbled_snark_verifier::bag::S], non_free_gates_count: usize) -> [u8; 32] {
    assert_eq!(ciphertexts.len(), non_free_gates_count, "non-free gate count does not match circuit topology");
    let mut hasher = Sha256::new();
    for ct in ciphertexts {
        hasher.update(ct.0);
    }
    hasher.finalize().into()
}

/// Count non-free gates in a compact `FlatGates` topology.
pub fn count_non_free_gates(flat: &FlatGates) -> usize {
    flat.gates.iter()
        .filter(|&&(_, _, _, gt, _)| GateType::try_from(gt).expect("unknown gate type").needs_ciphertext())
        .count()
}

/// Build the unsigned w=8 Base table.
///
/// Layout: window `i` (i = 0..WINDOW_COUNT), entry `j` (j = 0..WINDOW_ENTRIES) stores
/// `j · 256^i · Base` in affine Montgomery form. Entry j=0 is the point at infinity.
pub fn build_l2_table_bits(base: &G1Affine) -> Vec<bool> {
    let mut bits = Vec::with_capacity(PRECOMP_TABLE_BITS);
    let mut window_base = ark_bn254::G1Projective::from(base.clone());

    for _ in 0..WINDOW_COUNT {
        let mut multiple = ark_bn254::G1Projective::zero(); // j=0: infinity
        for _ in 0..WINDOW_ENTRIES {
            let aff = multiple.into_affine();
            bits.extend(Fq::to_bits(Fq::as_montgomery(aff.x)));
            bits.extend(Fq::to_bits(Fq::as_montgomery(aff.y)));
            multiple += window_base;
        }

        for _ in 0..WINDOW_BITS {
            window_base.double_in_place();
        }
    }
    bits
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::CurveGroup;
    use ark_ff::UniformRand;
    use garbled_snark_verifier::core::utils::reset_gid;
    use crate::dre::Q_SIZE;

    fn random_g1_affine() -> G1Affine {
        let mut rng = rand::thread_rng();
        ark_bn254::G1Projective::rand(&mut rng).into_affine()
    }

    // ── FGC witness / tests ─────────────────────────────────────────────────

    /// Witness for compile_fgc: π_x (N bits) + 2 MSB zeros, π_y (N bits) + 2 MSB zeros.
    fn fgc_witness(pi: &G1Affine) -> Vec<bool> {
        Fq::to_bits(pi.x).into_iter()
            .chain([false, false])
            .chain(Fq::to_bits(pi.y))
            .chain([false, false])
            .collect()
    }

    fn eval_fgc(pi: &G1Affine) -> Vec<bool> {
        let witness = fgc_witness(pi);
        reset_gid();
        let (bld, output_indices) = compile_fgc();
        assert_eq!(output_indices.len(), U_BAR_SIZE);
        let mut circuit = bld.build(&witness);
        for gate in &mut circuit.1 { gate.evaluate(); }
        output_indices.iter().map(|&i| circuit.0[i].borrow().get_value()).collect()
    }

    #[test]
    fn test_fgc_on_curve() {
        let pi = random_g1_affine();
        let output = eval_fgc(&pi);

        assert_eq!(output.len(), U_BAR_SIZE);
        assert!(output[0], "u₀ must be 1");

        for (k, (chunk, expected_bits)) in output[1..].chunks(N).zip([
            Fq::to_bits(pi.x),
            Fq::to_bits(pi.y),
            Fq::to_bits(pi.x * pi.x),
            Fq::to_bits(pi.y * pi.y),
            Fq::to_bits(pi.x * pi.y),
        ]).enumerate() {
            for (j, (&got, &exp)) in chunk.iter().zip(expected_bits.iter()).enumerate() {
                assert_eq!(got, exp, "field element {k} bit {j} mismatch");
            }
        }
    }

    #[test]
    fn test_fgc_off_curve_falls_back_to_g() {
        let pi = random_g1_affine();

        let mut off_pi = pi;
        off_pi.y += ark_bn254::Fq::from(1u64);
        let output = eval_fgc(&off_pi);

        assert_eq!(output.len(), U_BAR_SIZE);
        assert!(output[0], "u₀ must be 1");

        let g = G1Affine::generator();
        let gx_bits = Fq::to_bits(g.x);
        for k in 0..N {
            assert_eq!(output[1 + k], gx_bits[k], "generator.x bit {k} mismatch");
        }
        let gy_bits = Fq::to_bits(g.y);
        for k in 0..N {
            assert_eq!(output[1 + N + k], gy_bits[k], "generator.y bit {k} mismatch");
        }
    }

    #[test]
    fn test_fgc_msb_nonzero_falls_back_to_generator() {
        let pi = random_g1_affine(); // valid on-curve point
        let mut witness = fgc_witness(&pi);
        witness[N] = true; // pi_x MSB slot 0 = 1

        reset_gid();
        let (bld, output_indices) = compile_fgc();
        let mut circuit = bld.build(&witness);
        for gate in &mut circuit.1 { gate.evaluate(); }
        let output: Vec<bool> = output_indices.iter()
            .map(|&i| circuit.0[i].borrow().get_value()).collect();

        assert_eq!(output.len(), U_BAR_SIZE);
        assert!(output[0], "u₀ must be 1");
        let g = G1Affine::generator();
        let gx_bits = Fq::to_bits(g.x);
        for k in 0..N {
            assert_eq!(output[1 + k], gx_bits[k], "generator.x bit {k} mismatch");
        }
        let gy_bits = Fq::to_bits(g.y);
        for k in 0..N {
            assert_eq!(output[1 + N + k], gy_bits[k], "generator.y bit {k} mismatch");
        }
    }

    // ── SGC Part 1 witness / tests ──────────────────────────────────────────

    /// Witness for compile_sgc_part1: B_x (Montgomery) | B_y (Montgomery) | x_d (N bits) + 2 MSB zeros.
    /// L_2 table is baked into the circuit as constants, so it is not part of the witness.
    fn sgc_part1_witness(x_d: ark_bn254::Fr, b: &G1Affine) -> Vec<bool> {
        Fq::to_bits(Fq::as_montgomery(b.x))
            .into_iter()
            .chain(Fq::to_bits(Fq::as_montgomery(b.y)))
            .chain(Fr::to_bits(x_d))
            .chain([false, false])
            .collect()
    }

    fn eval_sgc_part1(l2: G1Affine, b: G1Affine, x_d: ark_bn254::Fr) -> ark_bn254::G1Affine {
        let witness = sgc_part1_witness(x_d, &b);
        reset_gid();
        let (bld, output_indices) = compile_sgc_part1(l2);
        assert_eq!(output_indices.len(), Q_SIZE);

        let mut circuit = bld.build(&witness);
        circuit.gate_counts().print();
        for gate in &mut circuit.1 { gate.evaluate(); }

        let bits: Vec<bool> = output_indices
            .iter()
            .map(|&i| circuit.0[i].borrow().get_value())
            .collect();

        let x = Fq::from_bits(bits[..N].to_vec());
        let y = Fq::from_bits(bits[N..2 * N].to_vec());
        ark_bn254::G1Affine::new_unchecked(x, y)
    }

    #[test]
    fn test_sgc_part1_random_xd() {
        let mut rng = rand::thread_rng();
        let l2 = random_g1_affine();
        let b  = random_g1_affine();
        let x_d = ark_bn254::Fr::rand(&mut rng);

        let got      = eval_sgc_part1(l2, b, x_d);
        let expected = (ark_bn254::G1Projective::from(l2) * x_d
            + ark_bn254::G1Projective::from(b))
            .into_affine();

        assert_eq!(got, expected, "Q = x_d · L₂ + B affine mismatch");
    }

    #[test]
    fn test_sgc_part1_xd_one() {
        let l2 = random_g1_affine();
        let b  = random_g1_affine();

        let got      = eval_sgc_part1(l2, b, ark_bn254::Fr::from(1u64));
        let expected = (ark_bn254::G1Projective::from(l2)
            + ark_bn254::G1Projective::from(b))
            .into_affine();

        assert_eq!(got, expected, "Q = 1·L₂ + B should equal L₂ + B");
    }

    #[test]
    fn test_sgc_part1_xd_msb_nonzero_falls_back_to_generator() {
        let mut rng = rand::thread_rng();
        let l2 = random_g1_affine();
        let b  = random_g1_affine();
        let x_d = ark_bn254::Fr::rand(&mut rng);

        let mut witness = sgc_part1_witness(x_d, &b);
        // sgc_part1_witness layout: B_x (N) | B_y (N) | x_d (N) | false, false
        // x_d MSB slot 0 is at index 2*N + N = 762
        witness[2 * N + N] = true;

        reset_gid();
        let (bld, output_indices) = compile_sgc_part1(l2);
        let mut circuit = bld.build(&witness);
        for gate in &mut circuit.1 { gate.evaluate(); }

        let bits: Vec<bool> = output_indices.iter()
            .map(|&i| circuit.0[i].borrow().get_value()).collect();
        let x = Fq::from_bits(bits[..N].to_vec());
        let y = Fq::from_bits(bits[N..2 * N].to_vec());
        let result = ark_bn254::G1Affine::new_unchecked(x, y);

        assert_eq!(result, ark_bn254::G1Affine::generator(),
                   "SGC Part 1 should fall back to G1 generator when x_d MSB is set");
    }
}
