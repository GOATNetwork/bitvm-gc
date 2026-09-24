use crate::{
    dv_bn254::bigint::{
        add::{add_generic, sub_generic_without_borrow},
        cmp::self_or_zero_generic,
        utils::{bits_from_biguint},
    },
};
use num_bigint::BigUint;

use once_cell::sync::Lazy;
use std::sync::Mutex;
use crate::circuits::sect233k1::builder::CircuitTrait;
use crate::dv_bn254::bigint::U254;

// static KARATSUBA_DECISIONS: Lazy<Mutex<[Option<bool>; 256]>> =
//     Lazy::new(|| Mutex::new([None; 256]));

fn extend_with_false<T: CircuitTrait>(bld: &mut T, wires: &mut Vec<usize>) {
    wires.push(bld.zero())
}

// fn set_karatsuba_decision_flag(index: usize, value: bool) {
//     let mut flags = KARATSUBA_DECISIONS.lock().unwrap();
//     flags[index] = Some(value);
// }
//
// fn get_karatsuba_decision_flag(index: usize) -> Option<bool> {
//     let flags = KARATSUBA_DECISIONS.lock().unwrap();
//     flags[index]
// }

/// Squaring base case: exploits a[i]*a[i]=a[i] (no AND) and symmetry a[i]*a[j]=a[j]*a[i]
/// (reuse the same wire), halving AND gates vs mul_generic.
fn square_base<T: CircuitTrait>(bld: &mut T, a: &[usize], n: usize) -> Vec<usize> {
    // Precompute AND pairs: diagonal is free, symmetric pairs share one gate.
    let mut products = vec![vec![0usize; n]; n];
    for i in 0..n {
        for j in i..n {
            if i == j {
                products[i][j] = a[i]; // a[i] AND a[i] = a[i]
            } else {
                let p = bld.and_wire(a[i], a[j]);
                products[i][j] = p;
                products[j][i] = p; // fan-out, no extra gate
            }
        }
    }
    let mut res = vec![bld.zero(); n * 2];
    for j in 0..n {
        let partial: Vec<usize> = (0..n).map(|i| products[i][j]).collect();
        let segment = res[j..j + n].to_vec();
        let new_bits = add_generic(bld, &segment, &partial, n);
        res[j..j + n + 1].clone_from_slice(&new_bits);
    }
    res
}

/// Karatsuba squaring: all three recursive sub-problems are squarings,
/// and the base case uses square_base (≈ half the AND gates of mul_generic).
pub fn square_karatsuba_generic<T: CircuitTrait>(bld: &mut T, a_wires: &[usize], len: usize) -> Vec<usize> {
    if len < 5 {
        return square_base(bld, a_wires, len);
    }
    let len_0 = len / 2;
    let len_1 = len.div_ceil(2);

    let a_0 = a_wires[0..len_0].to_vec();
    let a_1 = a_wires[len_0..].to_vec();

    let sq_0 = square_karatsuba_generic(bld, &a_0, len_0);
    let sq_1 = square_karatsuba_generic(bld, &a_1, len_1);

    let mut extended_sq_0 = sq_0.clone();
    let mut extended_a_0 = a_0.clone();
    if len_0 < len_1 {
        extend_with_false(bld, &mut extended_a_0);
        extend_with_false(bld, &mut extended_sq_0);
        extend_with_false(bld, &mut extended_sq_0);
    }

    // (a_0 + a_1)^2 provides the Karatsuba cross-term
    let sum_a = add_generic(bld, &extended_a_0, &a_1, len_1);
    let mut sq_sum = add_generic(bld, &extended_sq_0, &sq_1, len_1 * 2);
    extend_with_false(bld, &mut sq_sum);

    let sum_sq = square_karatsuba_generic(bld, &sum_a, len_1 + 1);
    let cross_term =
        sub_generic_without_borrow(bld, &sum_sq, &sq_sum, (len_1 + 1) * 2)
            [..(len + 1)]
            .to_vec();

    let mut res = vec![bld.zero(); len * 2];
    res[..(len_0 * 2)].clone_from_slice(&sq_0);

    {
        let segment = res[len_0..(len_0 + len + 1)].to_vec();
        let new_segment = add_generic(bld, &segment, &cross_term, len + 1);
        res[len_0..(len_0 + len + 2)].clone_from_slice(&new_segment);
    }

    {
        let segment = res[(2 * len_0)..].to_vec();
        let new_segment = add_generic(bld, &segment, &sq_1, len_1 * 2);
        res[(2 * len_0)..].clone_from_slice(&new_segment[..(2 * len_1)]);
    }

    res
}

pub fn mul_generic<T: CircuitTrait>(bld: &mut T, a_wires: &[usize], b_wires: &[usize], len: usize) -> Vec<usize> {
    assert_eq!(a_wires.len(), len);
    assert_eq!(b_wires.len(), len);

    let mut res = vec![bld.zero(); len * 2];

    for (i, current_bit) in b_wires.iter().enumerate().take(len) {
        let mut addition_wires_0 = vec![];
        for j in i..(i + len) {
            addition_wires_0.push(res[j].clone());
        }
        let addition_wires_1 =
            self_or_zero_generic(bld, &a_wires, *current_bit, len);
        let new_bits = add_generic(bld, &addition_wires_0, &addition_wires_1, len);
        res[i..(i + len + 1)].clone_from_slice(&new_bits);
    }
    res
}

// decider[i] = 0, not calculated, 1 = karatsuba, 0 = brute force
// this is a version of karatsuba I've just made up without any specific reference, there's probably a lot of room for improvement
pub fn mul_karatsuba_generic<T: CircuitTrait>(
    bld: &mut T,
    a_wires: &[usize],
    b_wires: &[usize],
    len: usize
) -> Vec<usize> {
    assert_eq!(a_wires.len(), len);
    assert_eq!(b_wires.len(), len);
    if len < 5 {
        return mul_generic(bld, a_wires, b_wires, len);
    }
    // let mut min_circuit = Vec::new();
    // let karatsuba_flag = get_karatsuba_decision_flag(len);
    // if karatsuba_flag.is_none() || !karatsuba_flag.unwrap() {
    //     min_circuit = mul_generic(bld, &a_wires, &b_wires, len);
    // }
    //
    // if karatsuba_flag.is_none() || karatsuba_flag.unwrap() {
    let mut res = vec![bld.zero(); len * 2];
    let len_0 = len / 2;
    let len_1 = len.div_ceil(2);

    let a_0 = a_wires[0..len_0].to_vec();
    let a_1 = a_wires[len_0..].to_vec();

    let b_0 = b_wires[0..len_0].to_vec();
    let b_1 = b_wires[len_0..].to_vec();

    let sq_0 = mul_karatsuba_generic(bld, &a_0, &b_0, len_0);
    let sq_1 = mul_karatsuba_generic(bld, &a_1, &b_1, len_1);
    let mut extended_sq_0 = sq_0.clone();
    let mut extended_a_0 = a_0.clone();
    let mut extended_b_0 = b_0.clone();
    if len_0 < len_1 {
        extend_with_false(bld, &mut extended_a_0);
        extend_with_false(bld, &mut extended_b_0);
        extend_with_false(bld, &mut extended_sq_0);
        extend_with_false(bld, &mut extended_sq_0);
    }

    let sum_a = add_generic(bld, &extended_a_0, &a_1, len_1);
    let sum_b = add_generic(bld, &extended_b_0, &b_1, len_1);
    let mut sq_sum = add_generic(bld, &extended_sq_0, &sq_1, len_1 * 2);
    extend_with_false(bld, &mut sq_sum);

    let sum_mul = mul_karatsuba_generic(bld, &sum_a, &sum_b, len_1 + 1);
    let cross_term =
        sub_generic_without_borrow(bld, &sum_mul, &sq_sum, (len_1 + 1) * 2)
            [..(len + 1)]
            .to_vec(); //len_0 + len_1 = len

    res[..(len_0 * 2)].clone_from_slice(&sq_0);

    {
        let segment = res[len_0..(len_0 + len + 1)].to_vec();
        let new_segment = add_generic(bld, &segment, &cross_term, len + 1);
        res[len_0..(len_0 + len + 2)].clone_from_slice(&new_segment);
    }

    {
        let segment = res[(2 * len_0)..].to_vec();
        let new_segment = add_generic(bld, &segment, &sq_1, len_1 * 2);
        res[(2 * len_0)..].clone_from_slice(&new_segment[..(2 * len_1)]);
    }
    res

    //     if circuit.gate_count() < min_circuit.gate_count() || min_circuit.gate_count() == 0 {
    //         set_karatsuba_decision_flag(len, true);
    //         min_circuit = circuit;
    //     }
    // }
    //
    // if get_karatsuba_decision_flag(len).is_none() {
    //     set_karatsuba_decision_flag(len, false);
    // }
    //
    // min_circuit
}

impl U254 {
    pub fn mul<T: CircuitTrait>(bld: &mut T, a_wires: &[usize], b_wires: &[usize]) -> Vec<usize> {
        mul_generic(bld, a_wires, b_wires, Self::N_BITS)
    }

    pub fn mul_karatsuba<T: CircuitTrait>(bld: &mut T, a_wires: &[usize], b_wires: &[usize]) -> Vec<usize> {
        mul_karatsuba_generic(bld, a_wires, b_wires, Self::N_BITS)
    }

    pub fn square_karatsuba<T: CircuitTrait>(bld: &mut T, a_wires: &[usize]) -> Vec<usize> {
        square_karatsuba_generic(bld, a_wires, Self::N_BITS)
    }

    pub fn mul_by_constant<T: CircuitTrait>(bld: &mut T, a_wires: &[usize], c: BigUint) -> Vec<usize> {
        assert_eq!(a_wires.len(), Self::N_BITS);
        let mut c_bits = bits_from_biguint(&c);
        c_bits.truncate(Self::N_BITS);

        let mut res = vec![bld.zero(); Self::N_BITS * 2];
        for (i, bit) in c_bits.iter().enumerate() {
            if *bit {
                let mut addition_wires = vec![];
                for j in i..(i + Self::N_BITS) {
                    addition_wires.push(res[j]);
                }
                let new_bits = Self::add(bld, a_wires, &addition_wires);
                res[i..(i + Self::N_BITS + 1)]
                    .clone_from_slice(&new_bits[..((i + Self::N_BITS - i) + 1)]);
            }
        }
        res

        //this is buggy at the moment because of borrowing, an optimization for later maybe?
        /*
        let d = change_to_neg_pos_decomposition(c_bits);
        for (i, coeff) in d.iter().enumerate().rev() {
            if *coeff == 0 {
                continue;
            }
             let mut operation_wires = vec![];
            for j in i..(i + N_BITS) {
                operation_wires.push(circuit.0[j].clone());
            }
            let new_bits;
            if *coeff == 1 {
                new_bits = Self::add(a_wires.clone(), operation_wires));
            } else {
                new_bits = Self::optimized_sub(a_wires.clone(), operation_wires, false));
            }
            for j in i..=(i + N_BITS - (*coeff == -1) as usize) {
                circuit.0[j] = new_bits[j - i].clone();
            }
        }
        */

    }

    pub fn mul_by_constant_modulo_power_two<T: CircuitTrait>(
        bld: &mut T,
        a_wires: &[usize],
        c: BigUint,
        power: usize
    ) -> Vec<usize> {
        assert_eq!(a_wires.len(), Self::N_BITS);
        assert!(power < 2 * Self::N_BITS);
        let mut c_bits = bits_from_biguint(&c);
        c_bits.truncate(Self::N_BITS);

        let mut res = vec![bld.zero(); power];
        for (i, bit) in c_bits.iter().enumerate() {
            if i == power {
                break;
            }
            if *bit {
                let mut addition_wires = vec![];
                let number_of_bits = (power - i).min(Self::N_BITS);
                for j in i..(i + number_of_bits) {
                    addition_wires.push(res[j]);
                }
                let new_bits = add_generic(
                    bld,
                    &a_wires[0..number_of_bits].to_vec(),
                    &addition_wires,
                    number_of_bits,
                );
                if i + number_of_bits < power {
                    res[i..(i + number_of_bits + 1)].clone_from_slice(&new_bits);
                } else {
                    res[i..(i + number_of_bits)]
                        .clone_from_slice(&new_bits[..number_of_bits]);
                }
            }
        }
        res
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use num_bigint::BigUint;
    use crate::circuits::sect233k1::builder::CircuitAdapter;
    use crate::dv_bn254::bigint::{
        U254,
        utils::{biguint_from_bits, random_biguint_n_bits},
    };

    //tests are currently only for 254 bits

    #[test]
    fn test_mul_dvbn254() {
        for _ in 0..10 {
            let a = random_biguint_n_bits(254);
            let b = random_biguint_n_bits(254);
            let mut bld = CircuitAdapter::default();
            let a_wires = U254::wires_set_from_number(&mut bld, &a);
            let b_wires = U254::wires_set_from_number(&mut bld, &b);
            let circuit =
                U254::mul(&mut bld, &a_wires, &b_wires);
            let c = &a * &b;
            let wires = bld.eval_gates(&vec![]);

            let result = biguint_from_bits(
                circuit.iter().map(|output_wire| wires[*output_wire]).collect(),
            );
            assert_eq!(result, c);
        }
    }

    #[test]
    fn test_karatsuba_dvbn254() {
        for _ in 0..10 {
            let mut bld = CircuitAdapter::default();
            let a = random_biguint_n_bits(254);
            let b = random_biguint_n_bits(254);
            let a_wires = U254::wires_set_from_number(&mut bld, &a);
            let b_wires = U254::wires_set_from_number(&mut bld, &b);
            let out_wires = U254::mul_karatsuba(
                &mut bld,
                &a_wires,
                &b_wires,
            );
            let c = &a * &b;
            let wires = bld.eval_gates(&vec![]);
            let result = biguint_from_bits(
                out_wires.iter().map(|output_wire| wires[*output_wire]).collect(),
            );
            assert_eq!(result, c);
        }
    }
}
