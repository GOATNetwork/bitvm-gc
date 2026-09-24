use garbled_snark_verifier::bag::*;
use garbled_snark_verifier::core::gate::GateType;
use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::rc::Rc;

pub fn parser(filename: &str) -> (Circuit, Vec<Wires>, Vec<Wires>) {
    let data = fs::read_to_string(filename).expect("error");
    let mut lines = data.lines();

    let mut words = lines.next().unwrap().split_whitespace();
    let nog: usize = words.next().unwrap().parse().unwrap();
    let now: usize = words.next().unwrap().parse().unwrap();
    let mut wires = Vec::new();
    for _ in 0..now {
        wires.push(new_wirex());
    }

    let mut input_sizes = Vec::<usize>::new();
    let mut words = lines.next().unwrap().split_whitespace();
    for _ in 0..words.next().unwrap().parse().unwrap() {
        let x: usize = words.next().unwrap().parse().unwrap();
        input_sizes.push(x);
    }

    let mut output_sizes = Vec::<usize>::new();
    let mut words = lines.next().unwrap().split_whitespace();
    for _ in 0..words.next().unwrap().parse().unwrap() {
        let x: usize = words.next().unwrap().parse().unwrap();
        output_sizes.push(x);
    }

    let mut i = 0;
    let mut gates = Vec::new();
    while i < nog {
        let line = lines.next().unwrap();
        if line.is_empty() {
            continue;
        }
        let mut words = line.split_whitespace();
        let gate_id: usize = words.next().unwrap().parse().unwrap();
        let number_of_inputs: usize = words.next().unwrap().parse().unwrap();
        let number_of_outputs: usize = words.next().unwrap().parse().unwrap();
        let mut input_wires: Vec<usize> = Vec::new();
        for _ in 0..number_of_inputs {
            input_wires.push(words.next().unwrap().parse().unwrap());
        }
        let mut output_wires: Vec<usize> = Vec::new();
        for _ in 0..number_of_outputs {
            output_wires.push(words.next().unwrap().parse().unwrap());
        }
        let gate_type_str = words.next().unwrap().to_lowercase();
        let gate_type = match gate_type_str.as_str() {
            "and" => GateType::And,
            "or" => GateType::Or,
            "xor" => GateType::Xor,
            "nor" => GateType::Nor,
            "nand" => GateType::Nand,
            "inv" | "not" => GateType::Not,
            "xnor" => GateType::Xnor,
            "nimp" => GateType::Nimp,
            "ncimp" => GateType::Ncimp,
            "cimp" => GateType::Cimp,
            "imp" => GateType::Imp,
            _ => panic!("Unknown gate type: {}", gate_type_str),
        };
        let gate = Gate::new_with_gid(
            wires[input_wires[0]].clone(),
            if number_of_inputs == 1 {
                wires[input_wires[0]].clone()
            } else {
                wires[input_wires[1]].clone()
            },
            wires[output_wires[0]].clone(),
            gate_type,
            gate_id as u32,
        );
        gates.push(gate);
        i += 1;
    }
    let c = Circuit::new(wires.clone(), gates);

    let mut inputs = Vec::new();
    let wires_copy = wires.clone();
    let mut wires_iter = wires_copy.iter();
    for input_size in input_sizes {
        let mut input = Vec::new();
        for _ in 0..input_size {
            input.push(wires_iter.next().unwrap().clone());
        }
        inputs.push(input);
    }

    let mut outputs = Vec::new();
    let mut wires_reversed = wires.clone();
    wires_reversed.reverse();
    let mut wires_iter = wires_reversed.iter();
    for output_size in output_sizes.iter().rev() {
        let mut output = Vec::new();
        for _ in 0..*output_size {
            output.push(wires_iter.next().unwrap().clone());
        }
        output.reverse();
        outputs.push(output);
    }
    outputs.reverse();

    (c, inputs, outputs)
}

pub fn wire_id(w: &Wirex) -> usize {
    Rc::as_ptr(w) as usize
}

pub fn write_bristol(
    circuit: &Circuit,
    input_sizes: &[usize],
    output_sizes: &[usize],
    filename: &str,
) -> Result<(), std::io::Error> {
    let mut file = fs::File::create(filename)?;
    writeln!(file, "{} {}", circuit.gate_count(), circuit.0.len())?;
    let mut wire_map = HashMap::new();
    for (i, wire) in circuit.0.iter().enumerate() {
        wire_map.insert(wire_id(&wire), i);
    }

    write!(file, "{}", input_sizes.len())?;
    for size in input_sizes {
        write!(file, " {}", size)?;
    }
    writeln!(file)?;

    write!(file, "{}", output_sizes.len())?;
    for size in output_sizes {
        write!(file, " {}", size)?;
    }
    writeln!(file)?;
    writeln!(file)?;

    for gate in &circuit.1 {
        writeln!(
            file,
            "{} {} {} {} {} {} {}",
            gate.gid,
            2,
            1,
            wire_map[&wire_id(&gate.wire_a)],
            wire_map[&wire_id(&gate.wire_b)],
            wire_map[&wire_id(&gate.wire_c)],
            gate.gate_type.to_string().to_uppercase(),
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use garbled_snark_verifier::core::utils::NON_CAC_DELTA;
    use rand::Rng;

    pub fn evaluator(
        circuit_file: &str,
        garblings: &[Option<S>],
        input_tuples: &[Vec<(S, bool)>],
        expected_output_label: S,
    ) {
        let (mut circuit, input_wires, _output_wires) = parser(circuit_file);

        for (i, input_wires) in input_wires.iter().enumerate() {
            for (j, wire) in input_wires.iter().enumerate() {
                let (label, bit) = input_tuples[i][j];
                if !bit {
                    wire.borrow_mut().set_label(label);
                } else {
                    wire.borrow_mut().set_label(label ^ NON_CAC_DELTA);
                }

                wire.borrow_mut().set(bit);
            }
        }

        for gate in &mut circuit.1 {
            gate.evaluate();
        }

        let computed_garblings = circuit.garbled_gates();
        assert_eq!(computed_garblings, garblings);

        let computed_output_label = circuit.garbled_evaluate(garblings);
        assert_eq!(computed_output_label, expected_output_label);
    }

    #[test]
    fn test_bristol_adder() {
        let (circuit, inputs, outputs) = parser("src/bristol-examples/adder64.txt");
        let mut rng = rand::thread_rng();
        let a: u64 = rng.r#gen();
        let b: u64 = rng.r#gen();
        for (i, wire) in inputs[0].iter().enumerate() {
            wire.borrow_mut().set((a >> i) & 1 == 1);
        }
        for (i, wire) in inputs[1].iter().enumerate() {
            wire.borrow_mut().set((b >> i) & 1 == 1);
        }
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let mut result_bits = Vec::new();
        for wire in outputs[0].clone() {
            result_bits.push(wire.borrow().get_value());
        }
        let mut c: u64 = 0;
        for bit in result_bits.iter().rev() {
            c = 2 * c + if *bit { 1 } else { 0 };
        }
        assert_eq!(c, a.wrapping_add(b));
    }

    #[test]
    fn test_bristol_multiplier() {
        let (circuit, inputs, outputs) = parser("src/bristol-examples/multiplier64.txt");
        let mut rng = rand::thread_rng();
        let a: u64 = rng.r#gen();
        let b: u64 = rng.r#gen();
        for (i, wire) in inputs[0].iter().enumerate() {
            wire.borrow_mut().set((a >> i) & 1 == 1);
        }
        for (i, wire) in inputs[1].iter().enumerate() {
            wire.borrow_mut().set((b >> i) & 1 == 1);
        }
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let mut result_bits = Vec::new();
        for wire in outputs[0].clone() {
            result_bits.push(wire.borrow().get_value());
        }
        let mut c: u64 = 0;
        for bit in result_bits.iter().rev() {
            c = 2 * c + if *bit { 1 } else { 0 };
        }
        assert_eq!(c, a.wrapping_mul(b));
    }

    #[test]
    fn test_bristol_subtracter() {
        let (circuit, inputs, outputs) = parser("src/bristol-examples/subtracter64.txt");
        let mut rng = rand::thread_rng();
        let a: u64 = rng.r#gen();
        let b: u64 = rng.r#gen();
        for (i, wire) in inputs[0].iter().enumerate() {
            wire.borrow_mut().set((a >> i) & 1 == 1);
        }
        for (i, wire) in inputs[1].iter().enumerate() {
            wire.borrow_mut().set((b >> i) & 1 == 1);
        }
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let mut result_bits = Vec::new();
        for wire in outputs[0].clone() {
            result_bits.push(wire.borrow().get_value());
        }
        let mut c: u64 = 0;
        for bit in result_bits.iter().rev() {
            c = 2 * c + if *bit { 1 } else { 0 };
        }
        assert_eq!(c, a.wrapping_sub(b));
    }

    #[test]
    fn test_bristol_writer() {
        let a = new_wirex();
        let b = new_wirex();
        let c = new_wirex();
        let d = new_wirex();
        let f = new_wirex();
        let g = new_wirex();
        let gate_1 = Gate::nand(a.clone(), c.clone(), d.clone());
        let gate_2 = Gate::and_variant(c.clone(), b.clone(), f.clone(), [1, 0, 1]);
        let gate_3 = Gate::nand(d.clone(), f.clone(), g.clone());
        let circuit = Circuit::new(vec![a, b, c, d, f, g], vec![gate_1, gate_2, gate_3]);
        write_bristol(&circuit, &[1, 1, 1], &[1], "test_bristol_writer.txt").unwrap();
    }

    #[test]
    fn test_selector_circuit_evaluator() {
        let (mut circuit, inputs, _outputs) = parser("src/bristol-examples/selector.txt");
        inputs[0][0].borrow_mut().set(false);
        inputs[1][0].borrow_mut().set(true);
        inputs[2][0].borrow_mut().set(false);
        for gate in &mut circuit.1 {
            gate.evaluate();
        }
        let garblings = circuit.garbled_gates();
        let expected_output_label = circuit.garbled_evaluate(&garblings);

        let input_tuples = vec![
            vec![(inputs[0][0].borrow().select(false), false)],
            vec![(inputs[1][0].borrow().select(true), true)],
            vec![(inputs[2][0].borrow().select(false), false)],
        ];

        evaluator(
            "src/bristol-examples/selector.txt",
            &garblings,
            &input_tuples,
            expected_output_label,
        );
    }

    #[test]
    fn test_adder64_circuit_evaluator() {
        let (mut circuit, inputs, _outputs) = parser("src/bristol-examples/adder64.txt");
        let mut rng = rand::thread_rng();
        let a: u64 = rng.r#gen();
        let b: u64 = rng.r#gen();
        for (i, wire) in inputs[0].iter().enumerate() {
            wire.borrow_mut().set((a >> i) & 1 == 1);
        }
        for (i, wire) in inputs[1].iter().enumerate() {
            wire.borrow_mut().set((b >> i) & 1 == 1);
        }
        for gate in &mut circuit.1 {
            gate.evaluate();
        }
        let garblings = circuit.garbled_gates();
        let expected_output_label = circuit.garbled_evaluate(&garblings);

        let input_tuples: Vec<Vec<(S, bool)>> = inputs
            .iter()
            .map(|input_wires| {
                input_wires
                    .iter()
                    .map(|wire| {
                        (wire.borrow().select(wire.borrow().get_value()), wire.borrow().get_value())
                    })
                    .collect()
            })
            .collect();

        evaluator(
            "src/bristol-examples/adder64.txt",
            &garblings,
            &input_tuples,
            expected_output_label,
        );
    }
}
