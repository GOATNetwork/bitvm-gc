//! Binary circuit implementation of DV Verifier Program
//!

use ark_ff::AdditiveGroup;
use crate::circuits::sect233k1::builder::{CircuitAdapter, CircuitTrait};
use crate::circuits::sect233k1::blake3_ckt;
use crate::dv_bn254::bigint::U254;
use crate::dv_bn254::fp254impl::Fp254Impl;
use super::{
    fr::{
        FR_LEN, Fr,
    },
};
use crate::dv_bn254::fq::{Fq, FQ_LEN};
use crate::dv_bn254::g1::G1Projective;
use crate::dv_bn254::hinted_double_sm::hinted_double_scalar_mul::emit_hinted_double_scalar_mul;

const PROOF_BIT_LEN: usize = FQ_LEN * 3 * 2 + FR_LEN * 2;
const PUBINP_BIT_LEN: usize = 2 * FR_LEN;
const TRAPDOOR_BIT_LEN: usize = FR_LEN * 3;

pub(crate) const WITNESS_BIT_LEN: usize = PROOF_BIT_LEN + PUBINP_BIT_LEN + TRAPDOOR_BIT_LEN;

pub fn get_input_indexes<T: CircuitTrait>(bld: &mut T) -> (Proof, PublicInputs, Trapdoor) {
    let secrets = Trapdoor {
        tau: Fr(bld.fresh()),
        delta: Fr(bld.fresh()),
        epsilon: Fr(bld.fresh())
    };
    let rpin = PublicInputs {
        public_inputs: [Fr(bld.fresh()), Fr(bld.fresh())]
    };

    let commit_p = G1Projective::wires(bld);
    let kzg_k = G1Projective::wires(bld);

    let proof = Proof {
        mont_commit_p: commit_p,
        mont_kzg_k: kzg_k,
        mont_a0: Fr(bld.fresh()),
        mont_b0: Fr(bld.fresh()),
        x1: (Fr(bld.fresh()), bld.fresh_one()),
        x2: (Fr(bld.fresh()), bld.fresh_one()),
        z: (Fr(bld.fresh()), bld.fresh_one()),

    };
    (proof, rpin, secrets)
}

/// Proof wires
#[derive(Debug, Clone)]
pub struct Proof {
    /// commit_p
    pub mont_commit_p: G1Projective, // commitment to witness folding & quotient
    /// kzg_k
    pub mont_kzg_k: G1Projective, // combined KZG evaluation proof
    /// a0
    pub mont_a0: Fr,
    /// b0
    pub mont_b0: Fr,
    /// x1
    pub x1: (Fr, usize),
    /// x2
    pub x2: (Fr, usize),
    /// z
    pub z: (Fr, usize),
}

/// RawPublicInputs
#[derive(Debug)]
pub struct PublicInputs {
    pub public_inputs: [Fr; 2],
}

/// Trapdoor
#[derive(Debug)]
pub struct Trapdoor {
    /// tau
    pub tau: Fr, // trapdoor (only known to verifier)
    /// delta
    pub delta: Fr,
    /// epsilon
    pub epsilon: Fr,
}

#[derive(Debug)]
pub struct IndexInfo {
    /// input wire inclusive range
    pub input_wire_range: (usize, usize),
    /// const zero wire label
    pub const_zero: usize,
    /// const one wire label
    pub const_one: usize,
    /// output index
    pub output_index: usize,
}

fn u8_arr_to_labels_le<T: CircuitTrait>(bld: &mut T, ns: &[u8]) -> Vec<[usize; 8]> {
    let zero = bld.zero();
    let one = bld.one();
    let mut vs: Vec<[usize; 8]> = Vec::new();
    for n in ns {
        let v: Vec<usize> = (0..8)
            .map(|i| {
                let r = (n >> i) & 1_u8 != 0_u8;
                if r { one } else { zero }
            })
            .collect();
        let v: [usize; 8] = v.try_into().unwrap();
        vs.push(v);
    }
    vs
}

fn get_fs_challenge<T: CircuitTrait>(
    bld: &mut T,
    commit_p: &G1Projective,
    public_inputs: [Fr; 2],
    srs_bytes: Vec<u8>,
    circuit_info_bytes: Vec<u8>,
) -> Fr {
    // convert into byte-aligned representation
    let zero = bld.zero();
    let mut commit_bits = commit_p.x.0.to_vec();
    commit_bits.resize(256, zero);
    commit_bits.extend_from_slice(&commit_p.y.0.to_vec());
    commit_bits.resize(512, zero);
    commit_bits.extend_from_slice(&commit_p.z.0.to_vec());
    commit_bits.resize(768, zero);

    let commit_p_u8 = commit_bits.chunks(8).map(|chunk| chunk.try_into().unwrap()).collect();

    let witness_commitment_hash = blake3_ckt::hash(bld, commit_p_u8);

    let public_inputs_hash = {
        let mut buf = Vec::new();
        for pubin in public_inputs {
            let mut pubin_256 = [bld.zero(); 256];
            pubin_256[0..FR_LEN].copy_from_slice(&pubin.0);
            let mut r: Vec<[usize; 8]> = pubin_256
                .chunks(8)
                .map(|x| {
                    let y: [usize; 8] = x.try_into().unwrap();
                    y
                })
                .collect();
            buf.append(&mut r);
        }

        blake3_ckt::hash(bld, buf)
    };

    let compile_time_hash = {
        let srs_bytes = u8_arr_to_labels_le(bld, &srs_bytes);
        let srs_hash = blake3_ckt::hash(bld, srs_bytes);
        let circuit_info_bytes = u8_arr_to_labels_le(bld, &circuit_info_bytes);
        let circuit_info_hash = blake3_ckt::hash(bld, circuit_info_bytes);
        let mut compile_time_bytes: Vec<[usize; 8]> = Vec::new();
        compile_time_bytes.extend_from_slice(&srs_hash);
        compile_time_bytes.extend_from_slice(&circuit_info_hash);
        blake3_ckt::hash(bld, compile_time_bytes)
    };

    let runtime_hash = {
        let mut runtime_bytes: Vec<[usize; 8]> = Vec::new();
        runtime_bytes.extend_from_slice(&witness_commitment_hash);
        runtime_bytes.extend_from_slice(&public_inputs_hash);

        blake3_ckt::hash(bld, runtime_bytes)
    };

    let mut root_hash = {
        let mut root_bytes: Vec<[usize; 8]> = Vec::new();
        root_bytes.extend_from_slice(&compile_time_hash);
        root_bytes.extend_from_slice(&runtime_hash);

        blake3_ckt::hash(bld, root_bytes)
    };

    let zero_byte = [bld.zero(); 8];
    // convert to Fr
    root_hash[31..].copy_from_slice(&[zero_byte; 1]); // mask top 1 bytes, 256-8=248 bits

    let root_hash_flat: Vec<usize> = root_hash.into_iter().flatten().collect();
    let root_fr_inner: [usize; FR_LEN] = root_hash_flat[0..FR_LEN].try_into().unwrap();

    Fr(root_fr_inner)
}

// /// Convert raw public inputs into scalar field element as done by Ziren
// fn get_pub_hash_from_raw_pub_inputs<T: CircuitTrait>(bld: &mut T, raw_pub_in: &PublicInputs) -> Fr {
//     let inps: Vec<[usize; 8]> = raw_pub_in
//         .deposit_index
//         .chunks(8)
//         .map(|x| {
//             let y: [usize; 8] = x.try_into().unwrap();
//             y
//         })
//         .collect();
//     let mut out_hash = blake3_ckt::hash(bld, inps);
//     let zero_byte = [bld.zero(); 8];
//     out_hash[0..4].copy_from_slice(&[zero_byte; 4]); // MSB masked assuming BE
//     out_hash.reverse();
//
//     let out_hash_flat: Vec<usize> = out_hash.into_iter().flatten().collect();
//     let out_fr: Fr = out_hash_flat[0..FR_LEN].try_into().unwrap();
//     out_fr
// }

/// Function to compile dvsnark verifier circuit
pub fn compile_verifier() -> (CircuitAdapter, IndexInfo) {
    let mut bld = CircuitAdapter::default();
    let index_info = compile_verifier_with(&mut bld, |_, _| {});
    (bld, index_info)
}

/// The verifier circuit on any builder. `inputs` is called with the input
/// wires' inclusive range as soon as they are allocated, before any gate reads
/// them: a builder that evaluates as it goes (`sect233k1::stream`) sets their
/// values there.
pub fn compile_verifier_with<T: CircuitTrait>(bld: &mut T, inputs: impl FnOnce(&mut T, (usize, usize))) -> IndexInfo {
    let input_wire_start = bld.next_wire();
    let (proof, rpin, secrets) = get_input_indexes(bld);
    let input_wire_end = bld.next_wire();
    let input_wire_range = (input_wire_start, input_wire_end - 1); // -1 because inclusive range
    inputs(bld, input_wire_range);

    // Prepare
    let passed_index = verify(bld, proof, rpin, secrets);
    IndexInfo {
        input_wire_range,
        const_zero: bld.zero(),
        const_one: bld.one(),
        output_index: passed_index,
    }
}

/// evaluate verifier
pub fn evaluate_verifier(
    bld: &mut CircuitAdapter,
    witness: [bool; WITNESS_BIT_LEN],
    output_wire_index: usize,
) -> bool {
    let wires = bld.eval_gates(&witness);
    wires[output_wire_index]
}

/// verify
pub(crate) fn verify<T: CircuitTrait>(
    bld: &mut T,
    proof: Proof,
    public_inputs: PublicInputs,
    secrets: Trapdoor,
) -> usize {
    let one_wire = bld.one();
    let fr_modulus = U254::wires_set_from_number(bld, &Fr::modulus_as_biguint());
    let proof_a0_invalid = Fr::ge_unsigned(bld, &proof.mont_a0.0, &fr_modulus); // a0 > R
    let proof_b0_invalid = Fr::ge_unsigned(bld, &proof.mont_b0.0, &fr_modulus); // b0 > R
    let a0_b0_invalid = bld.or_wire(proof_a0_invalid, proof_b0_invalid); // either a0 or b0 invalid
    // public inputs
    let mut proof_pubinp_invalid = Fr::ge_unsigned(bld, &public_inputs.public_inputs[0].0, &fr_modulus);
    for i in 1..public_inputs.public_inputs.len() {
        let pubinp_invalid = Fr::ge_unsigned(bld, &public_inputs.public_inputs[i].0, &fr_modulus);
        proof_pubinp_invalid = bld.or_wire(proof_pubinp_invalid, pubinp_invalid);
    }
    // trapdoor
    let proof_tau_invalid = Fr::ge_unsigned(bld, &secrets.tau.0, &fr_modulus);
    let proof_delta_invalid = Fr::ge_unsigned(bld, &secrets.delta.0, &fr_modulus);
    let proof_epsilon_invalid = Fr::ge_unsigned(bld, &secrets.epsilon.0, &fr_modulus);
    let tau_delta_invalid = bld.or_wire(proof_tau_invalid, proof_delta_invalid);
    let trapdoor_invalid = bld.or_wire(tau_delta_invalid, proof_epsilon_invalid);
    let a0_b0_trapdoor_invalid = bld.or_wire(a0_b0_invalid, trapdoor_invalid); // either a0, b0, or trapdoor invalid

    // point scalars
    let commit_p_scalar_valid = G1Projective::emit_point_scalar_valid(bld, &proof.mont_commit_p);
    let kzg_k_scalar_valid = G1Projective::emit_point_scalar_valid(bld, &proof.mont_kzg_k);
    let point_scalars_valid = bld.and_wire(commit_p_scalar_valid, kzg_k_scalar_valid); // both point scalars valid

    let proof_scalars_invalid = bld.or_wire(proof_pubinp_invalid, a0_b0_trapdoor_invalid); // either invalid
    let scalars_valid = bld.xor_wire(proof_scalars_invalid, one_wire); // both scalars valid
    let proof_scalars_valid = bld.and_wire(scalars_valid, point_scalars_valid);

    let is_proof_commit_p_on_curve =
        G1Projective::emit_projective_montgomery_point_is_on_curve(bld, &proof.mont_commit_p);
    let is_proof_kzg_k_on_curve =
        G1Projective::emit_projective_montgomery_point_is_on_curve(bld, &proof.mont_kzg_k);
    let decoded_points_valid = bld.and_wire(is_proof_commit_p_on_curve, is_proof_kzg_k_on_curve); // both points valid

    // decompose
    let two_to_170 = Fr::two_to_170(bld);
    let proof_x1_invalid = Fr::ge_unsigned(bld, &proof.x1.0.0, &two_to_170);
    let proof_x2_invalid = Fr::ge_unsigned(bld, &proof.x2.0.0, &two_to_170);
    let proof_z_invalid = Fr::ge_unsigned(bld, &proof.z.0.0, &two_to_170);

    let x1x2_invalid = bld.or_wire(proof_x1_invalid, proof_x2_invalid); // either x1, x2 invalid
    let decompose_invalid = bld.or_wire(x1x2_invalid, proof_z_invalid); // either x1, x2, z invalid
    let decompose_valid = bld.xor_wire(decompose_invalid, one_wire); // all valid

    let point_and_decode_valid_stats = bld.gate_counts();
    println!("point_and_decode_decompose_valid_stats: {:?}", point_and_decode_valid_stats);

    let fs_challenge_alpha =
        get_fs_challenge(bld, &proof.mont_commit_p, public_inputs.public_inputs.clone(), vec![], vec![]);
    let i0 = {
        let t0 = Fr::mul_montgomery(bld, &public_inputs.public_inputs[1].0, &fs_challenge_alpha.0);
        Fr::add(bld, &t0, &public_inputs.public_inputs[0].0)
    };

    let r0 = {
        //&proof.a0 * &proof.b0 - &proof.i0
        let t0 = Fr::mul_montgomery(bld, &proof.mont_a0.0, &proof.mont_b0.0);
        Fr::sub(bld, &t0, &i0)
    };

    // Step 3. Compute u₀ and v₀
    let u0 = {
        //(proof.a0 + secrets.delta * (proof.b0 + secrets.delta * r0)) * secrets.epsilon
        let delta_r0 = Fr::mul_montgomery(bld, &secrets.delta.0, &r0);
        let b0_plus = Fr::add(bld, &proof.mont_b0.0, &delta_r0);
        let inner = Fr::mul_montgomery(bld, &secrets.delta.0, &b0_plus);
        let sum = Fr::add(bld, &proof.mont_a0.0, &inner);

        Fr::mul_montgomery(bld, &sum, &secrets.epsilon.0)
    };

    let tmp0 = Fr::sub(bld, &secrets.tau.0, &fs_challenge_alpha.0);
    let v0 = Fr::mul_montgomery(bld, &tmp0, &secrets.epsilon.0);

    let u0_v0_stats = bld.gate_counts();
    println!("u0_v0_stats: {:?}", u0_v0_stats);


    // Step 4. Check: x_1 G + x_2Q - zP = 0, using multi_scalar_mul_with_precompute
    let mont_generator_wires = G1Projective::wires_set_montgomery_generator(bld);
    let neg_ws_gen = G1Projective::negate_with_neg_selector(
        bld,
        &mont_generator_wires,
        proof.x1.1,
    );

    let neg_ws_k = G1Projective::negate_with_neg_selector(
        bld,
        &proof.mont_kzg_k.to_vec_wires(),
        proof.x2.1,
    );

    let neg_ws_p = G1Projective::negate_with_pos_selector(
        bld,
        &proof.mont_commit_p.to_vec_wires(),
        proof.z.1,
    );

    let lhs = emit_hinted_double_scalar_mul(
        bld,
        &vec![proof.x1.0.0.to_vec(), proof.x2.0.0.to_vec(), proof.z.0.0.to_vec()],
        &vec![neg_ws_gen, neg_ws_k, neg_ws_p],
    );
    let rhs = G1Projective::wires_set_montgomery(bld, ark_bn254::G1Projective::ZERO);
    let step4_valid = G1Projective::equal(bld, &lhs, &rhs.to_vec_wires());

    let step4_stats = bld.gate_counts();
    println!("step4_stats: {:?}", step4_stats);

    // Step 5. Check u0 * z - x1 = 0 && v0 * z - x2 = 0
    // to montgomery
    let mont_x1 = Fr::to_montgomery_circuit(bld, &proof.x1.0.0);
    let mont_x2 = Fr::to_montgomery_circuit(bld, &proof.x2.0.0);
    let mont_z = Fr::to_montgomery_circuit(bld, &proof.z.0.0);

    let neg_ws_x1 = Fr::negate_with_selector(bld, &mont_x1, proof.x1.1);
    let neg_ws_x2 = Fr::negate_with_selector(bld, &mont_x2, proof.x2.1);
    let neg_ws_z = Fr::negate_with_selector(bld, &mont_z, proof.z.1);

    let u0_z = Fr::mul_montgomery(bld, &u0, &neg_ws_z);
    let u0_z_sub_x1 = Fr::sub(bld, &u0_z, &neg_ws_x1);
    let check1 = Fr::equal_zero(bld, &u0_z_sub_x1);
    let v0_z = Fr::mul_montgomery(bld, &v0, &neg_ws_z);
    let v0_z_sub_x2 = Fr::sub(bld, &v0_z, &neg_ws_x2);
    let check2 = Fr::equal_zero(bld, &v0_z_sub_x2);
    let step5_valid = bld.and_wire(check1, check2);

    let step5_stats = bld.gate_counts();
    println!("step5_stats: {:?}", step5_stats);

    let decode_decompose_valid = bld.and_wire(decompose_valid, decoded_points_valid);
    let proof_elements_valid = bld.and_wire(decode_decompose_valid, proof_scalars_valid);
    let step45_valid = bld.and_wire(step4_valid, step5_valid);
    bld.and_wire(proof_elements_valid, step45_valid)
}

#[cfg(test)]
mod test {
    use std::str::FromStr;
    use ark_ff::AdditiveGroup;
    use crate::circuits::sect233k1::builder::{CircuitAdapter, CircuitTrait};
    use crate::dv_bn254::bigint::U254;
    use crate::dv_bn254::dv_ckt::{get_fs_challenge, get_input_indexes};
    use crate::dv_bn254::dv_ref::{FrRef, ProofRef, PublicInputsRef, TrapdoorRef, VerifierPayloadRef};
    use crate::dv_bn254::fp254impl::Fp254Impl;
    use crate::dv_bn254::fr::Fr;
    use crate::dv_bn254::g1::G1Projective;
    use crate::dv_bn254::hinted_double_sm::hinted_double_scalar_mul::emit_hinted_double_scalar_mul;

    fn initialize_witness() -> VerifierPayloadRef{
        // Prepare VerifierPayloadRef
        let tau = FrRef::from_str(
            "11862927736293505976827355338938040996519579475528107310941684119781757391039",
        )
            .unwrap();
        let delta = FrRef::from_str(
            "19144933261297331633080959100481380589633074304003794613695593869462980578759",
        )
            .unwrap();
        let epsilon = FrRef::from_str(
            "313961560996054992893313828582054121800731311457442837960229611969948337040",
        )
            .unwrap();
        let mont_commit_p = ark_bn254::G1Projective::new_unchecked(
            ark_bn254::Fq::from_str("7945797433559704849311923614598929259737771858793098395236612582183144719173").unwrap(),
            ark_bn254::Fq::from_str("17012034996486701113694275047646644230671894233797105837810220927620239598653").unwrap(),
            ark_bn254::Fq::from_str("1904029105985936155224998850934598237583320194268951485119152920799350410912").unwrap(),
        );
        let mont_kzg_k = ark_bn254::G1Projective::new_unchecked(
            ark_bn254::Fq::from_str("218840416271392248134913265936769272628298608502613289864227836162651470083").unwrap(),
            ark_bn254::Fq::from_str("12507096977197660920086344758001040257535547413335347824125243167552228396643").unwrap(),
            ark_bn254::Fq::from_str("7718594443256972252891810807829015169125545629599067047189461244308075009980").unwrap(),
        );

        let mont_a0 = FrRef::from_str(
            "2379383345977345328483769109781010318500935685616923216261946203557840245156",
        )
            .unwrap();
        let mont_b0 = FrRef::from_str(
            "10710067834367256827276997192305278081193710391606660405083208486036847880486",
        )
            .unwrap();

        let x1_val = FrRef::from_str(
            "117254209170240570118468483301402360720011190156626"
        ).unwrap();
        let x1 = (x1_val, false);
        let x2_val = FrRef::from_str(
            "428956628384832546334058967498472364665310775024525"
        ).unwrap();
        let x2 = (x2_val, false);
        let z_val = FrRef::from_str(
            "382966261084432891439040614202494776072682302885809"
        ).unwrap();
        let z = (z_val, true);

        let public_inputs = [
            FrRef::from_str("16217006396879640651787331949151919374620611580946319582101174263628714475489")
                .unwrap(),
            FrRef::from_str("4224161200009956348416803608862024017805255356259249285367676853928926904303")
                .unwrap(),
        ];

        let witness = VerifierPayloadRef {
            proof: ProofRef { mont_commit_p, mont_kzg_k, mont_a0, mont_b0, x1, x2, z },
            public_input: PublicInputsRef { public_inputs },
            trapdoor: TrapdoorRef { tau, delta, epsilon },
        };
        witness
    }

    #[test]
    fn test_decompose_dvbn254() {
        let mut bld = CircuitAdapter::default();

        let u0 = ark_bn254::Fr::from_str("21457562058599027886128781723011550118341889803802259009197664792048723713284").unwrap();
        let v0 = ark_bn254::Fr::from_str("18773909891129115237742565942774855385236068205643017366808288723990672538934").unwrap();
        let x1 = ark_bn254::Fr::from_str("117254209170240570118468483301402360720011190156626").unwrap();
        let x2 = ark_bn254::Fr::from_str("428956628384832546334058967498472364665310775024525").unwrap();
        let z = ark_bn254::Fr::from_str("382966261084432891439040614202494776072682302885809").unwrap();

        let neg_x1 = false;
        let neg_x2 = false;
        let neg_z = true;

        let u0_wires = Fr::wires(&mut bld);
        let v0_wires = Fr::wires(&mut bld);
        let x1_wires = Fr::wires(&mut bld);
        let x2_wires = Fr::wires(&mut bld);
        let z_wires = Fr::wires(&mut bld);
        let neg_x1_wire = bld.fresh_one();
        let neg_x2_wire = bld.fresh_one();
        let neg_z_wire = bld.fresh_one();

        let neg_ws_x1 = Fr::negate_with_selector(&mut bld, &x1_wires.0, neg_x1_wire);
        let neg_ws_x2 = Fr::negate_with_selector(&mut bld, &x2_wires.0, neg_x2_wire);
        let neg_ws_z = Fr::negate_with_selector(&mut bld, &z_wires.0, neg_z_wire);

        let u0_z = Fr::mul_montgomery(&mut bld, &u0_wires.0, &neg_ws_z);
        let u0_z_sub_x1 = Fr::sub(&mut bld, &u0_z, &neg_ws_x1);

        let v0_z = Fr::mul_montgomery(&mut bld, &v0_wires.0, &neg_ws_z);
        let v0_z_sub_x2 = Fr::sub(&mut bld, &v0_z, &neg_ws_x2);

        let witness = Fr::to_bits(Fr::as_montgomery(u0)).iter()
            .chain(Fr::to_bits(Fr::as_montgomery(v0)).iter())
            .chain(Fr::to_bits(Fr::as_montgomery(x1)).iter())
            .chain(Fr::to_bits(Fr::as_montgomery(x2)).iter())
            .chain(Fr::to_bits(Fr::as_montgomery(z)).iter())
            .chain(&[neg_x1, neg_x2, neg_z])
            .copied()
            .collect::<Vec<_>>();

        let wires_bits = bld.eval_gates(&witness);
        let u0_z_sub_x1_bits = u0_z_sub_x1.iter().map(|w| wires_bits[*w]).collect::<Vec<bool>>();
        let v0_z_sub_x2_bits = v0_z_sub_x2.iter().map(|w| wires_bits[*w]).collect::<Vec<bool>>();
        let u0_z_sub_x1_val = Fr::from_bits(u0_z_sub_x1_bits);
        let v0_z_sub_x2_val = Fr::from_bits(v0_z_sub_x2_bits);

        assert_eq!(u0_z_sub_x1_val, Fr::as_montgomery(ark_bn254::Fr::ZERO));
        assert_eq!(v0_z_sub_x2_val, Fr::as_montgomery(ark_bn254::Fr::ZERO));
    }

    #[test]
    fn test_proof_valid() {
        let witness = initialize_witness();
        let mut bld = CircuitAdapter::default();
        let (proof, _, _) = get_input_indexes(&mut bld);

        let is_proof_commit_p_on_curve =
            G1Projective::emit_projective_montgomery_point_is_on_curve(&mut bld, &proof.mont_commit_p);
        let is_proof_kzg_k_on_curve =
            G1Projective::emit_projective_montgomery_point_is_on_curve(&mut bld, &proof.mont_kzg_k);

        let one_wire = bld.one();
        let fr_modulus = U254::wires_set_from_number(&mut bld, &Fr::modulus_as_biguint());
        let proof_a0_invalid = Fr::ge_unsigned(&mut bld, &proof.mont_a0.0, &fr_modulus); // a0 should be less than modulus
        let proof_b0_invalid = Fr::ge_unsigned(&mut bld, &proof.mont_b0.0, &fr_modulus);
        let proof_scalars_invalid = bld.or_wire(proof_a0_invalid, proof_b0_invalid); // either invalid
        let proof_scalars_valid = bld.xor_wire(proof_scalars_invalid, one_wire); // both scalars valid
        let decoded_points_valid = bld.and_wire(is_proof_commit_p_on_curve, is_proof_kzg_k_on_curve); // both points valid

        // decompose
        let two_to_170 = Fr::two_to_170(&mut bld);
        let proof_x1_invalid = Fr::ge_unsigned(&mut bld, &proof.x1.0.0, &two_to_170);
        let proof_x2_invalid = Fr::ge_unsigned(&mut bld, &proof.x2.0.0, &two_to_170);
        let proof_z_invalid = Fr::ge_unsigned(&mut bld, &proof.z.0.0, &two_to_170);

        let x1x2_invalid = bld.or_wire(proof_x1_invalid, proof_x2_invalid); // either x1, x2 invalid
        let decompose_invalid = bld.or_wire(x1x2_invalid, proof_z_invalid); // either x1, x2, z invalid
        let decompose_valid = bld.xor_wire(decompose_invalid, one_wire); // all valid


        let valid1 = bld.and_wire(proof_scalars_valid, decoded_points_valid);
        let valid = bld.and_wire(valid1, decompose_valid);
        // eval
        let wires_bits = bld.eval_gates(&witness.to_bits());
        let valid_val = wires_bits[valid];
        assert!(valid_val);
        let stats = bld.gate_counts();
        println!("{stats}");
    }


    #[test]
    fn test_compute_u0_v0() {
        let witness = initialize_witness();

        let mut bld = CircuitAdapter::default();
        let (proof, rpin, secrets) = get_input_indexes(&mut bld);

        let fs_challenge_alpha =
            get_fs_challenge(&mut bld, &proof.mont_commit_p, rpin.public_inputs.clone(), vec![], vec![]);
        let i0 = {
            let t0 = Fr::mul_montgomery(&mut bld, &rpin.public_inputs[1].0, &fs_challenge_alpha.0);
            Fr::add(&mut bld, &t0, &rpin.public_inputs[0].0)
        };

        let r0 = {
            //&proof.a0 * &proof.b0 - &proof.i0
            let t0 = Fr::mul_montgomery(&mut bld, &proof.mont_a0.0, &proof.mont_b0.0);
            Fr::sub(&mut bld, &t0, &i0)
        };

        // Step 3. Compute u₀ and v₀
        let u0 = {
            //(proof.a0 + secrets.delta * (proof.b0 + secrets.delta * r0)) * secrets.epsilon
            let delta_r0 = Fr::mul_montgomery(&mut bld, &secrets.delta.0, &r0);
            let b0_plus = Fr::add(&mut bld, &proof.mont_b0.0, &delta_r0);
            let inner = Fr::mul_montgomery(&mut bld, &secrets.delta.0, &b0_plus);
            let sum = Fr::add(&mut bld, &proof.mont_a0.0, &inner);

            Fr::mul_montgomery(&mut bld, &sum, &secrets.epsilon.0)
        };

        let tmp0 = Fr::sub(&mut bld, &secrets.tau.0, &fs_challenge_alpha.0);
        let v0 = Fr::mul_montgomery(&mut bld, &tmp0, &secrets.epsilon.0);

        // eval:
        let wires_bits = bld.eval_gates(&witness.to_bits());

        let u0_bits = u0.iter().map(|w| wires_bits[*w]).collect::<Vec<bool>>();
        let v0_bits = v0.iter().map(|w| wires_bits[*w]).collect::<Vec<bool>>();
        let u0_val = Fr::from_bits(u0_bits);
        let v0_val = Fr::from_bits(v0_bits);

        let expected_u0 = ark_bn254::Fr::from_str(
            "21457562058599027886128781723011550118341889803802259009197664792048723713284",
        )
            .unwrap();
        let expected_v0 = ark_bn254::Fr::from_str(
            "18773909891129115237742565942774855385236068205643017366808288723990672538934",
        )
            .unwrap();

        let mont_u0 = Fr::as_montgomery(expected_u0);
        let mont_v0 = Fr::as_montgomery(expected_v0);
        assert_eq!(u0_val, mont_u0);
        assert_eq!(v0_val, mont_v0);

        let stats = bld.gate_counts();
        println!("{stats}");
    }

    #[test]
    #[ignore]
    fn test_point_computation_hinted_msm() {
        let mont_commit_p = ark_bn254::G1Projective::new_unchecked(
            ark_bn254::Fq::from_str("7945797433559704849311923614598929259737771858793098395236612582183144719173").unwrap(),
            ark_bn254::Fq::from_str("17012034996486701113694275047646644230671894233797105837810220927620239598653").unwrap(),
            ark_bn254::Fq::from_str("1904029105985936155224998850934598237583320194268951485119152920799350410912").unwrap(),
        );
        let mont_kzg_k = ark_bn254::G1Projective::new_unchecked(
            ark_bn254::Fq::from_str("218840416271392248134913265936769272628298608502613289864227836162651470083").unwrap(),
            ark_bn254::Fq::from_str("12507096977197660920086344758001040257535547413335347824125243167552228396643").unwrap(),
            ark_bn254::Fq::from_str("7718594443256972252891810807829015169125545629599067047189461244308075009980").unwrap(),
        );

        let x1_val = ark_bn254::Fr::from_str(
            "117254209170240570118468483301402360720011190156626"
        ).unwrap();
        let x1 = (x1_val, false);
        let x2_val = ark_bn254::Fr::from_str(
            "428956628384832546334058967498472364665310775024525"
        ).unwrap();
        let x2 = (x2_val, false);
        let z_val = ark_bn254::Fr::from_str(
            "382966261084432891439040614202494776072682302885809"
        ).unwrap();
        let z = (z_val, true);

        let mut bld = CircuitAdapter::default();
        let x1_wires = (Fr::wires(&mut bld), bld.fresh_one());
        let x2_wires = (Fr::wires(&mut bld), bld.fresh_one());
        let z_wires = (Fr::wires(&mut bld), bld.fresh_one());
        let mont_p_wires = G1Projective::wires(&mut bld);
        let mont_k_wires = G1Projective::wires(&mut bld);
        let mont_generator_wires = G1Projective::wires_set_montgomery_generator(&mut bld);

        let neg_ws_gen = G1Projective::negate_with_neg_selector(
            &mut bld,
            &mont_generator_wires,
            x1_wires.1,
        );

        let neg_ws_k = G1Projective::negate_with_neg_selector(
            &mut bld,
            &mont_k_wires.to_vec_wires(),
            x2_wires.1,
        );

        let neg_ws_p = G1Projective::negate_with_pos_selector(
            &mut bld,
            &mont_p_wires.to_vec_wires(),
            z_wires.1,
        );

        let out_wires = emit_hinted_double_scalar_mul(
            &mut bld,
            &vec![x1_wires.0.0.to_vec(), x2_wires.0.0.to_vec(), z_wires.0.0.to_vec()],
            &vec![neg_ws_gen, neg_ws_k, neg_ws_p],
        );

        let witness = Fr::to_bits(x1.0).into_iter()
            .chain([x1.1])
            .chain(Fr::to_bits(x2.0).into_iter())
            .chain([x2.1])
            .chain(Fr::to_bits(z.0).into_iter())
            .chain([z.1])
            .chain(G1Projective::to_bits(mont_commit_p).into_iter())
            .chain(G1Projective::to_bits(mont_kzg_k).into_iter())
            .collect::<Vec<bool>>();

        let wires_bits = bld.eval_gates(&witness);
        let out_bits = out_wires.iter().map(|w| wires_bits[*w]).collect::<Vec<bool>>();
        let out_point = G1Projective::from_bits(out_bits);
        assert_eq!(out_point, G1Projective::as_montgomery(ark_bn254::G1Projective::ZERO));
        let stats = bld.gate_counts();
        println!("{stats}");
    }
}
