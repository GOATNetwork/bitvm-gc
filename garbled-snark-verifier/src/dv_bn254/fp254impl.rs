use crate::{
    dv_bn254::{
        bigint::U254,
        fq::Fq,
    },
};
use ark_ff::{AdditiveGroup, Field};
use core::str::FromStr;
use num_bigint::BigUint;
use crate::circuits::sect233k1::builder::CircuitTrait;
use crate::dv_bn254::basic::not;
use crate::dv_bn254::fr::Fr;

pub trait Fp254Impl: Sized {
    const MODULUS: &'static str;
    const MONTGOMERY_R: &'static str =
        "28948022309329048855892746252171976963317496166410141009864396001978282409984"; //2^254

    const MONTGOMERY_M_INVERSE: &'static str; // MODULUS^-1 modulo R
    const MONTGOMERY_R_INVERSE: &'static str; // R^-1 modulo MODULUS
    const N_BITS: usize;
    const MODULUS_ADD_1_DIV_4: &'static str =
        "5472060717959818805561601436314318772174077789324455915672259473661306552146"; // (MODULUS+1)/4

    fn modulus_as_biguint() -> BigUint {
        BigUint::from_str(Self::MODULUS).unwrap()
    }

    fn montgomery_r_as_biguint() -> BigUint {
        BigUint::from_str(Self::MONTGOMERY_R).unwrap()
    }

    fn montgomery_m_inverse_as_biguint() -> BigUint {
        BigUint::from_str(Self::MONTGOMERY_M_INVERSE).unwrap()
    }

    fn montgomery_r_inverse_as_biguint() -> BigUint {
        BigUint::from_str(Self::MONTGOMERY_R_INVERSE).unwrap()
    }

    fn not_modulus_as_biguint() -> BigUint {
        let p = Self::modulus_as_biguint();
        let a = BigUint::from_str("2").unwrap().pow(Self::N_BITS.try_into().unwrap());
        a - p
    }

    fn half_modulus() -> BigUint;

    fn one_third_modulus() -> BigUint;

    fn two_third_modulus() -> BigUint;

    fn multiplexer<T: CircuitTrait> (bld: &mut T, a: &Vec<Vec<usize>>, s: &[usize], w: usize) -> Vec<usize> {
        U254::multiplexer(bld, a, s, w)
    }

    fn equal<T: CircuitTrait> (bld: &mut T, a: &[usize], b: &[usize]) -> usize {
        U254::equal(bld, a, b)
    }

    fn equal_zero<T: CircuitTrait> (bld: &mut T, a: &[usize]) -> usize {
        U254::equal_constant(bld, a, &BigUint::ZERO)
    }

    fn add<T: CircuitTrait> (bld: &mut T, a: &[usize], b: &[usize]) -> Vec<usize> {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut wires_1 = U254::add(bld, a, b);
        let u = wires_1.pop().unwrap();
        let c = Self::not_modulus_as_biguint();
        let mut wires_2 = U254::add_constant(bld, &wires_1, &c);
        wires_2.pop();
        let v = U254::less_than_constant(bld, &wires_1, &Self::modulus_as_biguint());
        let not_u = not(bld, u);
        let s = bld.and_wire(not_u, v);
        let wires_3 = U254::select(bld, &wires_1, &wires_2, s);
        wires_3
    }

    fn neg<T: CircuitTrait>(bld: &mut T, a: &[usize]) -> Vec<usize>;

    fn sub<T: CircuitTrait>(bld: &mut T, a: &[usize], b: &[usize]) -> Vec<usize> {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let neg_b = Self::neg(bld, b);
        let result = Self::add(bld, a, &neg_b);
        result
    }

    fn double<T: CircuitTrait>(bld: &mut T, a: &[usize]) -> Vec<usize> {
        assert_eq!(a.len(), Self::N_BITS);
        let mut aa = a.to_vec();
        let u = aa.pop().unwrap();
        let mut shifted_wires = vec![bld.zero()];
        shifted_wires.extend(aa);
        let c = Self::not_modulus_as_biguint();
        let mut wires_2 = U254::add_constant(bld, &shifted_wires, &c);
        wires_2.pop();
        let v = U254::less_than_constant(bld, &shifted_wires, &Self::modulus_as_biguint());

        // Ncimp
        let not_a = not(bld, u);
        let s = bld.and_wire(not_a, v);
        let result = U254::select(bld, &shifted_wires, &wires_2, s);
        result
    }

    fn half<T: CircuitTrait>(bld: &mut T, a: &[usize]) -> Vec<usize> {
        assert_eq!(a.len(), Self::N_BITS);
        let selector = a[0];
        let wires_1 = U254::half(bld, a);
        let wires_2 = U254::add_constant_without_carry(bld, &wires_1, &Self::half_modulus());
        let result = U254::select(bld, &wires_2, &wires_1, selector);
        result
    }

    fn triple<T: CircuitTrait>(bld: &mut T, a: &[usize]) -> Vec<usize> {
        assert_eq!(a.len(), Self::N_BITS);
        let a_2 = Self::double(bld, a);
        let a_3 = Self::add(bld, &a_2, a);
        a_3
    }

    // ───────────────────  a ≥ c   (one wire, MSB first)  ─────────────────────
    //  Gate cost: 4·W XOR + 3·W AND
    fn ge_unsigned<T: CircuitTrait>(bld: &mut T, a: &[usize], c: &[usize]) -> usize {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(c.len(), Self::N_BITS);
        let w = a.len();
        let mut gt = bld.zero();
        let mut eq = bld.one();
        for i in (0..w).rev() {
            let ai = a[i];
            let bi = c[i];
            let m0 = not(bld, bi);
            let ai_gt_bi = bld.and_wire(ai, m0);
            //let _m1 = not(b, ai);
            //let ai_lt_bi = b.and_wire(m1, bi);
            let m2 = bld.and_wire(eq, ai_gt_bi);
            gt = bld.or_wire(gt, m2);
            let m3 = bld.xor_wire(ai, bi);
            let m4 = not(bld, m3);
            eq = bld.and_wire(eq, m4); // keep eq flag
        }
        bld.or_wire(gt, eq) // ge = gt ∨ eq
    }


    fn montgomery_reduce<T: CircuitTrait>(bld: &mut T, x: &[usize]) -> Vec<usize> {
        let x_low = x[..254].to_vec();
        let x_high = x[254..].to_vec();
        let q = U254::mul_by_constant_modulo_power_two(
            bld,
            &x_low,
            Self::montgomery_m_inverse_as_biguint(),
            254,
        );
        let sub = U254::mul_by_constant(bld, &q, Self::modulus_as_biguint())[254..508].to_vec();
        let bound_check = U254::greater_than(bld, &sub, &x_high);
        let subtract_if_too_much = U254::self_or_zero_constant(
            bld,
            &Self::modulus_as_biguint(),
            bound_check,
        );
        let new_sub = U254::sub_without_borrow(bld, &sub, &subtract_if_too_much);
        let result = U254::sub_without_borrow(bld, &x_high, &new_sub);
        result
    }

    fn mul_montgomery<T: CircuitTrait>(bld: &mut T, a: &[usize], b: &[usize]) -> Vec<usize> {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mul_circuit = U254::mul_karatsuba(bld, a, b);
        let reduction_circuit = Self::montgomery_reduce(bld, &mul_circuit);
        reduction_circuit
    }

    fn square_montgomery<T: CircuitTrait>(bld: &mut T, a: &[usize]) -> Vec<usize> {
        assert_eq!(a.len(), Self::N_BITS);
        let sq_circuit = U254::square_karatsuba(bld, a);
        Self::montgomery_reduce(bld, &sq_circuit)
    }

    // ──────────────────────────  2-way mux  (sel ? a : b)  ────────────────────
    #[inline]
    fn mux<T: CircuitTrait>(b: &mut T, sel: usize, a: usize, d: usize) -> usize {
        let m0 = b.xor_wire(a, d);
        let m1 = b.and_wire(sel, m0);
        b.xor_wire(d, m1)
    }
    fn mux_vec<T: CircuitTrait>(b: &mut T, sel: usize, a: &[usize], d: &[usize]) -> Vec<usize> {
        a.iter().zip(d).map(|(&x, &y)| Self::mux(b, sel, x, y)).collect()
    }

    fn negate_with_selector<T: CircuitTrait>(bld: &mut T, a: &[usize], neg: usize) -> Vec<usize> {
        let neg_a = Self::neg(bld, a);
        Self::mux_vec(bld, neg, &neg_a, a)
    }
}
