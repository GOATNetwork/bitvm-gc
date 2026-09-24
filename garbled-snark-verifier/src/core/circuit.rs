use crate::{bag::*, core::{gate::GateCount, s::S, utils::{NON_CAC_DELTA, NON_CAC_SALT}}};

// wires, gates
#[derive(Debug)]
pub struct Circuit(pub Wires, pub Vec<Gate>);

impl Circuit {
    pub fn empty() -> Self {
        Self(Vec::new(), Vec::new())
    }

    pub fn new(wires: Wires, gates: Vec<Gate>) -> Self {
        Self(wires, gates)
    }

    // calculate all ciphertext, and send to evaluator
    pub fn garbled_gates(&self) -> Vec<Option<S>> {
        self.garbled_gates_with_delta(NON_CAC_DELTA, Some(NON_CAC_SALT))
    }

    pub fn garbled_gates_with_delta(&self, delta: S, salt: Option<S>) -> Vec<Option<S>> {
        self.1
            .iter()
            .enumerate()
            .map(|(i, gate)| {
                gate.garbled_with_delta(delta, salt)
            })
            .collect()
    }

    pub fn extend(&mut self, circuit: Self) -> Wires {
        self.1.extend(circuit.1);
        circuit.0
    }

    pub fn add(&mut self, gate: Gate) {
        self.1.push(gate);
    }

    pub fn add_wire(&mut self, wire: Wirex) {
        self.0.push(wire);
    }

    pub fn add_wires(&mut self, wires: Wires) {
        self.0.extend(wires);
    }

    pub fn gate_count(&self) -> usize {
        self.1.len()
    }

    pub fn gate_counts(&self) -> GateCount {
        let mut gc = GateCount::default();
        for gate in self.1.iter() {
            gc.0[gate.gate_type as usize] += 1;
        }
        gc
    }

    pub fn garbled_evaluate(&self, garblings: &[Option<S>]) -> S {
        self.garbled_evaluate_with_delta(garblings, NON_CAC_DELTA, Some(NON_CAC_SALT))
    }

    pub fn garbled_evaluate_with_delta(&self, garblings: &[Option<S>], delta: S, salt: Option<S>) -> S {
        let mut garbled_evaluations = vec![];
        for (i, gate) in self.1.iter().enumerate() {
            let (output, output_label) = gate.e()(
                gate.wire_a.borrow().get_value(),
                gate.wire_b.borrow().get_value(),
                gate.wire_a.borrow().select_with_delta(gate.wire_a.borrow().get_value(), delta),
                gate.wire_b.borrow().select_with_delta(gate.wire_b.borrow().get_value(), delta),
                garblings[i],
                gate.gid,
                salt,
            );
            assert_eq!(output, gate.wire_c.borrow().get_value());
            garbled_evaluations.push((output, output_label));
        }

        for (i, gate) in self.1.iter().enumerate() {
            let check = gate.check_garbled_circuit_with_delta(garbled_evaluations[i].1, delta);
            assert!(check);
        }

        garbled_evaluations.last().unwrap().1
    }

    /// `ciphertexts` holds only the entries produced by gates where
    /// `GateType::needs_ciphertext()` is true, in gate order — free-XOR gates
    pub fn garbled_evaluate_without_delta(&self, ciphertexts: &[S], salt: Option<S>) {
        let mut ct_idx = 0usize;
        for gate in self.1.iter() {
            let ct = if gate.gate_type.needs_ciphertext() {
                let c = ciphertexts[ct_idx];
                ct_idx += 1;
                Some(c)
            } else {
                None
            };
            let (output, output_label) = gate.e()(
                gate.wire_a.borrow().get_value(),
                gate.wire_b.borrow().get_value(),
                gate.wire_a.borrow().get_label(),
                gate.wire_b.borrow().get_label(),
                ct,
                gate.gid,
                salt,
            );
            // check the output is correct
            assert_eq!(output, gate.wire_c.borrow().get_value());
            // add new label to output wire
            if gate.wire_c.borrow().label.is_some() {
                assert_eq!(gate.wire_c.borrow().get_label(), output_label);
            }
            else {
                gate.wire_c.borrow_mut().set_label(output_label);
            }
        }
    }

    pub fn set_witness_value(&mut self, witness: &[bool], skip: usize) {
        // Gate wires are Rc<RefCell<Wire>> sharing the same data as self.0, so this covers all.
        witness.iter()
            .zip(self.0.iter().skip(skip))
            .for_each(|(bit, wirex)| wirex.borrow_mut().set_value_for_uninitialized(*bit));
    }

    pub fn reset_circuit_except_01_constants(&mut self) {
        for wirex in self.0.iter().skip(2) {
            wirex.borrow_mut().value = None;
        }
        for wirex in self.0.iter() {
            wirex.borrow_mut().label = None;
        }
    }

    pub fn is_fresh(&self) -> bool {
        let fresh_val = self.0.iter().skip(2).all(|wirex| wirex.borrow().value.is_none());
        let fresh_label = self.0.iter().all(|wirex| wirex.borrow().label.is_none());
        fresh_val && fresh_label
    }

    pub fn size_in_bytes(&self) -> usize {
        // Wires: each Wirex is Rc<RefCell<Wire>>, Wire lives on heap
        let wire_data_size = self.0.len() * (
            std::mem::size_of::<Wire>()   // actual Wire struct
                + std::mem::size_of::<usize>() * 2  // Rc strong + weak count
        );
        // Gates: Vec<Gate> is contiguous, but each gate holds 3 Rc pointers
        // Gate itself is stack-allocated in the Vec
        let gate_data_size = self.1.len() * std::mem::size_of::<Gate>();

        // Vec metadata (ptr + len + capacity) for both Wires and Gates
        let vec_overhead = std::mem::size_of::<Vec<Wirex>>()
            + std::mem::size_of::<Vec<Gate>>();

        wire_data_size + gate_data_size + vec_overhead
    }
}

#[cfg(feature = "garbled")]
#[cfg(test)]
mod tests {
    use crate::bag::new_wirex;
    use crate::circuits::basic::selector;
    use crate::circuits::bn254::fq6::Fq6;
    use crate::circuits::bn254::g1::{G1Projective, projective_to_affine_montgomery};
    use crate::core::utils::{NON_CAC_DELTA, NON_CAC_SALT};
    use ark_ec::CurveGroup;
    use ark_ff::{AdditiveGroup, Field};

    #[test]
    fn test_selector_circuit_garbled_evaluation() {
        let mut wire_a = new_wirex();
        wire_a.borrow_mut().set(false);

        let mut wire_b = new_wirex();
        wire_b.borrow_mut().set(true);

        let mut wire_c = new_wirex();
        wire_c.borrow_mut().set(false);

        let mut circuit = selector(wire_a, wire_b, wire_c);

        for gate in &mut circuit.1 {
            gate.evaluate();
        }
        let garblings = circuit.garbled_gates();
        let output_label = circuit.garbled_evaluate(&garblings);

        // hand-computing output label
        let g1_output_label = circuit.1[0].wire_a.borrow().select(false).hash_ext(circuit.1[0].gid, Some(NON_CAC_SALT));
        let g2_output_label = circuit.1[1].wire_a.borrow().select(false).hash_ext(circuit.1[1].gid, Some(NON_CAC_SALT))
            ^ garblings[1].unwrap()
            ^ circuit.1[1].wire_b.borrow().select(true);
        let computed_output_label = (g1_output_label).hash_ext(circuit.1[2].gid, Some(NON_CAC_SALT))
            ^ garblings[2].unwrap()
            ^ (g2_output_label ^ NON_CAC_DELTA);

        assert_eq!(output_label, computed_output_label);
    }

    #[test]
    fn test_fq6_mul_montgomery_circuit_garbled_evaluation() {
        let a = Fq6::random();
        let b = Fq6::random();
        let mut circuit = Fq6::mul_montgomery(
            Fq6::wires_set(Fq6::as_montgomery(a)),
            Fq6::wires_set(Fq6::as_montgomery(b)),
        );
        circuit.gate_counts().print();
        for gate in &mut circuit.1 {
            gate.evaluate();
        }
        let garblings = circuit.garbled_gates();
        let _ = circuit.garbled_evaluate(&garblings);
    }

    #[test]
    fn test_g1_projective_to_affine_montgomery_circuit_garbled_evaluation() {
        let p_projective = G1Projective::random().double();
        assert_ne!(p_projective.z, ark_bn254::Fq::ONE);
        let p_affine = p_projective.into_affine();
        let mut circuit =
            projective_to_affine_montgomery(G1Projective::wires_set_montgomery(p_projective));
        circuit.gate_counts().print();
        for gate in &mut circuit.1 {
            gate.evaluate();
        }
        let garblings = circuit.garbled_gates();
        let _ = circuit.garbled_evaluate(&garblings);
    }
}
