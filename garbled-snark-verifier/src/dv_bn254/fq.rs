use crate::dv_bn254::bigint::U254;
use crate::circuits::bn254::utils::create_rng;
use crate::{dv_bn254::fp254impl::Fp254Impl};
use ark_ff::{AdditiveGroup, Field, UniformRand};
use core::str::FromStr;
use num_bigint::BigUint;
use crate::circuits::sect233k1::builder::CircuitTrait;
use crate::dv_bn254::basic::not;

pub const FQ_LEN: usize = 254;
#[derive(Debug, Clone)]
pub struct Fq(pub [usize; FQ_LEN]);

impl Fp254Impl for Fq {
    const MODULUS: &'static str =
        "21888242871839275222246405745257275088696311157297823662689037894645226208583";
    const MONTGOMERY_M_INVERSE: &'static str =
        "4759646384140481320982610724935209484903937857060724391493050186936685796471";
    const MONTGOMERY_R_INVERSE: &'static str =
        "18289368484950178621272022062020525048389989670507786348948026221581485535495";
    const N_BITS: usize = 254;

    fn half_modulus() -> BigUint {
        BigUint::from(ark_bn254::Fq::from(1) / ark_bn254::Fq::from(2))
    }

    fn one_third_modulus() -> BigUint {
        BigUint::from(ark_bn254::Fq::from(1) / ark_bn254::Fq::from(3))
    }

    fn two_third_modulus() -> BigUint {
        BigUint::from(ark_bn254::Fq::from(2) / ark_bn254::Fq::from(3))
    }

    fn neg<T: CircuitTrait>(bld: &mut T, a: &[usize]) -> Vec<usize> {
        assert_eq!(a.len(), Self::N_BITS);
        let mut not_a =  Vec::new();
        for i in 0..Self::N_BITS {
            not_a.push(not(bld, a[i]));
        }

        let wires = Self::add_constant(
            bld,
            &not_a,
            ark_bn254::Fq::from(1) - ark_bn254::Fq::from(Self::not_modulus_as_biguint()),
        );
        wires
    }
}

impl Fq {
    const B_MUL: &'static str =
        "11601089733084985762858650344571909944996040564978406380258545510642996494113";

    pub fn b_mul_as_biguint() -> BigUint {
        BigUint::from_str(Self::B_MUL).unwrap()
    }

    pub fn as_montgomery(a: ark_bn254::Fq) -> ark_bn254::Fq {
        a * ark_bn254::Fq::from(Self::montgomery_r_as_biguint())
    }

    pub fn from_montgomery(a: ark_bn254::Fq) -> ark_bn254::Fq {
        a / ark_bn254::Fq::from(Self::montgomery_r_as_biguint())
    }

    pub fn random() -> ark_bn254::Fq {
        let mut prng = create_rng();
        ark_bn254::Fq::rand(&mut prng)
    }

    pub fn to_bits(u: ark_bn254::Fq) -> Vec<bool> {
        let mut bytes = BigUint::from(u).to_bytes_le();
        bytes.extend(vec![0_u8; 32 - bytes.len()]);
        let mut bits = Vec::new();
        for byte in bytes {
            for i in 0..8 {
                bits.push(((byte >> i) & 1) == 1)
            }
        }
        bits.pop();
        bits.pop();
        bits
    }

    pub fn from_bits(bits: Vec<bool>) -> ark_bn254::Fq {
        let zero = BigUint::ZERO;
        let one = BigUint::from(1_u8);
        let mut u = zero.clone();
        for bit in bits.iter().rev() {
            u = u.clone() + u.clone() + if *bit { one.clone() } else { zero.clone() };
        }
        ark_bn254::Fq::from(u)
    }

    pub fn wires<T: CircuitTrait> (bld: &mut T) -> Self {
        let inner: [usize; FQ_LEN] = bld.fresh();
        Self(inner)
    }

    pub fn wires_set<T: CircuitTrait>(bld: &mut T, u: ark_bn254::Fq) -> Self {
        let inner = Self::to_bits(u)[0..Self::N_BITS]
            .iter()
            .map(|bit| {
                if *bit {
                    bld.one()
                } else {
                    bld.zero()
                }
            })
            .collect::<Vec<usize>>();
        Self(inner.try_into().unwrap())
    }

    pub fn wires_set_montgomery<T: CircuitTrait>(bld: &mut T, u: ark_bn254::Fq) -> Self {
        Self::wires_set(bld, Self::as_montgomery(u))
    }

    pub fn from_wires<T: CircuitTrait>(bld: &mut T, fq: Fq) -> ark_bn254::Fq {
        Self::from_bits(fq.0.iter().map(|wire| {
            if *wire != bld.one() || *wire != bld.zero() {
                panic!("wire value is not set properly");
            }
            *wire == bld.one()
        }).collect())
    }

    fn equal_constant<T: CircuitTrait> (bld: &mut T, a: &[usize], b: ark_bn254::Fq) -> usize {
        U254::equal_constant(bld, a, &BigUint::from(b))
    }

    pub fn from_montgomery_wires<T: CircuitTrait>(bld: &mut T, fq: Fq) -> ark_bn254::Fq {
        Self::from_montgomery(Self::from_wires(bld, fq))
    }

    pub fn add_constant<T: CircuitTrait>(bld: &mut T, a: &[usize], b: ark_bn254::Fq) -> Vec<usize> {
        assert_eq!(a.len(), Self::N_BITS);
        if b == ark_bn254::Fq::ZERO {
            return a.to_vec();
        }

        let mut wires_1 = U254::add_constant(bld, a, &BigUint::from(b));
        let u = wires_1.pop().unwrap();
        let c = Self::not_modulus_as_biguint();
        let mut wires_2 = U254::add_constant(bld, &wires_1, &c);
        wires_2.pop();
        let v = U254::less_than_constant(bld, &wires_1, &Self::modulus_as_biguint());

        // Ncimp
        let not_a = not(bld, u);
        let s = bld.and_wire(not_a, v);
        U254::select(bld, &wires_1, &wires_2, s)
    }

    pub fn mul_by_constant_montgomery<T: CircuitTrait>(bld: &mut T, a: &[usize], b: ark_bn254::Fq) -> Vec<usize> {
        assert_eq!(a.len(), Self::N_BITS);

        if b == ark_bn254::Fq::ZERO {
            return Fq::wires_set(bld, ark_bn254::Fq::ZERO).0.to_vec();
        }

        if b == Fq::as_montgomery(ark_bn254::Fq::ONE) {
            return a.to_vec();
        }

        // b == 1 (standard form) means: convert a from Montgomery → standard.
        // montgomery_reduce(a ‖ 0) = a * R⁻¹ mod p, skipping the Karatsuba mul entirely.
        if b == ark_bn254::Fq::ONE {
            let mut padded = a.to_vec();
            padded.extend((0..Self::N_BITS).map(|_| bld.zero()));
            return Self::montgomery_reduce(bld, &padded);
        }

        let mul_circuit = U254::mul_by_constant(bld, a, b.into());
        let reduction_circuit = Self::montgomery_reduce(bld, &mul_circuit);
        reduction_circuit
    }

    pub fn inverse<T: CircuitTrait>(bld: &mut T, a: &[usize]) -> (Vec<usize>, usize) {
        assert_eq!(a.len(), Self::N_BITS);
        // check if a is zero
        let is_zero = Self::equal_zero(bld, a);
        let input_valid = not(bld, is_zero);

        let wires_1 = U254::odd_part(bld, a);
        let odd_part = wires_1.0;
        let mut even_part = wires_1.1;

        // initialize value for wires
        let neg_odd_part = Self::neg(bld, &odd_part);
        let mut u = U254::half(bld, &neg_odd_part);
        let mut v = odd_part;
        let mut k = Fq::wires_set(bld, ark_bn254::Fq::ONE).0.to_vec();
        let mut r = Fq::wires_set(bld, ark_bn254::Fq::ONE).0.to_vec();
        let mut s = Fq::wires_set(bld, ark_bn254::Fq::from(2)).0.to_vec();

        for _ in 0..2 * Self::N_BITS {
            let not_x1 = u[0];
            let not_x2 = v[0];
            let x3 = U254::greater_than(bld, &u, &v);

            // Nimp
            let not_b = not(bld, not_x2);
            let p2 = bld.and_wire(not_x1, not_b);
            let wires_2 = bld.and_wire(not_x1, not_x2);
            let p3 = bld.and_wire(wires_2, x3);
            let not_x3 = not(bld, x3);
            let p4 = bld.and_wire(wires_2, not_x3);

            //part1
            let u1 = U254::half(bld, &u);
            let v1 = v.clone();
            let r1 = r.clone();
            let s1 = U254::double_without_overflow(bld, &s);
            let k1 = U254::add_constant_without_carry(
                bld,
                &k,
                &BigUint::from_str("1").unwrap(),
            );

            // part2
            let u2 = u.clone();
            let v2 = U254::half(bld, &v);
            let r2 = U254::double_without_overflow(bld, &r);
            let s2 = s.clone();
            let k2 = U254::add_constant_without_carry(
                bld,
                &k,
                &BigUint::from_str("1").unwrap(),
            );

            // part3
            let u3 = U254::sub_without_borrow(bld, &u1, &v2);
            let v3 = v.clone();
            let r3 = U254::add_without_carry(bld, &r, &s);
            let s3 = U254::double_without_overflow(bld, &s);
            let k3 = U254::add_constant_without_carry(
                bld,
                &k,
                &BigUint::from_str("1").unwrap(),
            );

            // part4
            let u4 = u.clone();
            let v4 = U254::sub_without_borrow(bld, &v2, &u1);
            let r4 = U254::double_without_overflow(bld, &r);
            let s4 = U254::add_without_carry(bld, &r, &s);
            let k4 = U254::add_constant_without_carry(
                bld,
                &k,
                &BigUint::from_str("1").unwrap(),
            );

            // calculate new u
            let wire_u_1 = U254::self_or_zero_inv(bld, &u1, not_x1);
            let wire_u_2 = U254::self_or_zero(bld, &u2, p2);
            let wire_u_3 = U254::self_or_zero(bld, &u3, p3);
            let wire_u_4 = U254::self_or_zero(bld, &u4, p4);

            let add_u_1 = U254::add_without_carry(bld, &wire_u_1, &wire_u_2);
            let add_u_2 = U254::add_without_carry(bld, &add_u_1, &wire_u_3);
            let new_u = U254::add_without_carry(bld, &add_u_2, &wire_u_4);

            // calculate new v
            let wire_v_1 = U254::self_or_zero_inv(bld, &v1, not_x1);
            let wire_v_2 = U254::self_or_zero(bld, &v2, p2);
            let wire_v_3 = U254::self_or_zero(bld, &v3, p3);
            let wire_v_4 = U254::self_or_zero(bld, &v4, p4);

            let add_v_1 = U254::add_without_carry(bld, &wire_v_1, &wire_v_2);
            let add_v_2 = U254::add_without_carry(bld, &add_v_1, &wire_v_3);
            let new_v = U254::add_without_carry(bld, &add_v_2, &wire_v_4);

            // calculate new r
            let wire_r_1 = U254::self_or_zero_inv(bld, &r1, not_x1);
            let wire_r_2 = U254::self_or_zero(bld, &r2, p2);
            let wire_r_3 = U254::self_or_zero(bld, &r3, p3);
            let wire_r_4 = U254::self_or_zero(bld, &r4, p4);

            let add_r_1 = U254::add_without_carry(bld, &wire_r_1, &wire_r_2);
            let add_r_2 = U254::add_without_carry(bld, &add_r_1, &wire_r_3);
            let new_r = U254::add_without_carry(bld, &add_r_2, &wire_r_4);

            // calculate new s
            let wire_s_1 = U254::self_or_zero_inv(bld, &s1, not_x1);
            let wire_s_2 = U254::self_or_zero(bld, &s2, p2);
            let wire_s_3 = U254::self_or_zero(bld, &s3, p3);
            let wire_s_4 = U254::self_or_zero(bld, &s4, p4);

            let add_s_1 = U254::add_without_carry(bld, &wire_s_1, &wire_s_2);
            let add_s_2 = U254::add_without_carry(bld, &add_s_1, &wire_s_3);
            let new_s = U254::add_without_carry(bld, &add_s_2, &wire_s_4);

            // calculate new k
            let wire_k_1 = U254::self_or_zero_inv(bld, &k1, not_x1);
            let wire_k_2 = U254::self_or_zero(bld, &k2, p2);
            let wire_k_3 = U254::self_or_zero(bld, &k3, p3);
            let wire_k_4 = U254::self_or_zero(bld, &k4, p4);

            let add_k_1 = U254::add_without_carry(bld, &wire_k_1,& wire_k_2);
            let add_k_2 = U254::add_without_carry(bld, &add_k_1, &wire_k_3);
            let new_k = U254::add_without_carry(bld, &add_k_2, &wire_k_4);

            // set new values

            let v_equals_one = U254::equal_constant(
                bld,
                &v,
                &BigUint::from_str("1").unwrap()
            );
            u = U254::select(bld, &u, &new_u, v_equals_one);
            v = U254::select(bld, &v, &new_v, v_equals_one);
            r = U254::select(bld, &r, &new_r, v_equals_one);
            s = U254::select(bld, &s, &new_s, v_equals_one);
            k = U254::select(bld, &k, &new_k, v_equals_one);
        }

        // divide result by even part
        for _ in 0..Self::N_BITS {
            let updated_s = Self::half(bld, &s);
            let updated_even_part = Self::half(bld, &even_part);
            let selector = Self::equal_constant(bld, &even_part, ark_bn254::Fq::ONE);
            s = U254::select(bld, &s, &updated_s, selector);
            even_part = U254::select(bld, &even_part, &updated_even_part, selector);
        }

        // divide result by 2^k
        for _ in 0..2 * Self::N_BITS {
            let updated_s = Self::half(bld, &s);
            let updated_k = Fq::add_constant(bld, &k, ark_bn254::Fq::from(-1));
            let selector = Self::equal_constant(bld, &k, ark_bn254::Fq::ZERO);
            s = U254::select(bld, &s, &updated_s, selector);
            k = U254::select(bld, &k, &updated_k, selector);
        }
        (s, input_valid)
    }

    pub fn inverse_montgomery<T: CircuitTrait>(bld: &mut T, a: &[usize]) -> (Vec<usize>, usize) {
        let (b, is_valid_input) = Self::inverse(bld, a);
        let result = Self::mul_by_constant_montgomery(
            bld,
            &b,
            ark_bn254::Fq::from(Fq::montgomery_r_as_biguint()).square()
                * ark_bn254::Fq::from(Fq::montgomery_r_as_biguint()),
        );

        (result, is_valid_input)
    }
}


#[cfg(test)]
mod tests {
    use ark_ff::Field;
    use crate::circuits::sect233k1::builder::CircuitAdapter;
    use crate::dv_bn254::fp254impl::Fp254Impl;
    use crate::dv_bn254::fq::Fq;

    #[test]
    fn test_fq_mul_montgomery_dvbn254() {
        let a = Fq::random();
        let b = Fq::random();

        let mut bld = CircuitAdapter::default();
        let a_mont = Fq::as_montgomery(a);
        let b_mont = Fq::as_montgomery(b);

        let a_wires = Fq::wires(&mut bld);
        let b_wires = Fq::wires(&mut bld);

        let a_witness = Fq::to_bits(a_mont);
        let b_witness = Fq::to_bits(b_mont);
        let witness = a_witness.iter().chain(b_witness.iter()).cloned().collect::<Vec<bool>>();

        let out_wires = Fq::mul_montgomery(&mut bld, &a_wires.0, &b_wires.0);
        let wires = bld.eval_gates(&witness);
        let output_bits = out_wires.iter().map(|w| wires[*w]).collect::<Vec<bool>>();
        let c = Fq::from_bits(output_bits);
        assert_eq!(c, Fq::as_montgomery(a * b));
    }

    #[test]
    fn test_fq_inverse_montgomery_dvbn254() {
        let a = ark_bn254::Fq::from(10);

        let mut bld = CircuitAdapter::default();
        let mont_a = Fq::as_montgomery(a);

        let a_ref = Fq::wires(&mut bld);

        let (out, is_valid) = Fq::inverse_montgomery(&mut bld, &a_ref.0);
        let witness = Fq::to_bits(mont_a);
        let wires = bld.eval_gates(&witness);

        let inv_a_bits: Vec<bool> = out.iter().map(|id| wires[*id]).collect();
        let c = Fq::from_bits(inv_a_bits);
        let is_valid_bit = wires[is_valid];
        assert_eq!(c, Fq::as_montgomery(a.inverse().unwrap()));
        assert!(is_valid_bit);
    }
}
