use crate::bag::Circuit;
use std::time::Instant;
use crate::dv_bn254::dv_ckt::compile_verifier;
use crate::dv_bn254::dv_ref::VerifierPayloadRef;

pub fn dv_snark_verifier_circuit(
    witness: &VerifierPayloadRef
) -> Circuit {
    let start = Instant::now();
    let (builder, _) = compile_verifier();
    println!("Compile time: {:?}", start.elapsed());
    let start = Instant::now();
    let circuit = builder.build(&witness.to_bits());
    println!("build circuit time:{:?}", start.elapsed());

    circuit
}

pub fn dv_snark_verifier_bench_circuit(
    witness: &VerifierPayloadRef
) -> Circuit {
    let start = Instant::now();
    let (builder, _) = compile_verifier();
    println!("Compile time: {:?}", start.elapsed());
    let start = Instant::now();
    let circuit = builder.build_benchmark(&witness.to_bits());
    println!("build circuit time:{:?}", start.elapsed());

    circuit
}

#[cfg(test)]
mod test {
    use std::str::FromStr;
    use crate::circuits::sect233k1::builder::CircuitTrait;
    use crate::dv_bn254::dv_ckt::compile_verifier;
    use crate::dv_bn254::dv_ref::{FrRef, ProofRef, PublicInputsRef, TrapdoorRef, VerifierPayloadRef};


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
    fn test_dv_snark_verifier_circuit_dvbn254() {
        // Prepare VerifierPayloadRef
        let witness = initialize_witness();

        let (bld, info) = compile_verifier();
        let wires_bits = bld.eval_gates(&witness.to_bits());
        println!("number of wires: {}", wires_bits.len());

        let output_value = wires_bits[info.output_index];
        println!("output_value: {}", output_value);
        assert_eq!(output_value, true);

        let stats = bld.gate_counts();
        println!("Gate counts: {:?}", stats);
    }

    /// The same verifier, garbled and evaluated gate by gate as it is built
    /// (`sect233k1::stream`), holding only the live wires: the stored build
    /// above needs more memory than a small machine has. It accepts the valid
    /// witness and rejects it with one bit flipped.
    #[test]
    fn test_dv_snark_verifier_circuit_dvbn254_streamed() {
        use crate::circuits::sect233k1::stream::{Plan, Streaming, ValuedBuilder};
        use crate::dv_bn254::dv_ckt::compile_verifier_with;

        fn run(bits: &[bool]) -> bool {
            let mut plan = Plan::new();
            let planned = compile_verifier_with(&mut plan, |_, _| {});
            plan.keep(planned.output_index);
            let wires = plan.wires();
            let mut s = Streaming::planned(plan, false);
            let info = compile_verifier_with(&mut s, |s, (lo, hi)| {
                assert_eq!(hi + 1 - lo, bits.len());
                for (wire, &bit) in (lo..=hi).zip(bits.iter()) {
                    s.set_input(wire, bit);
                }
            });
            assert_eq!(s.wires(), wires);
            println!(
                "{} non-free gates, {} wires, {} live at peak; {:?}",
                s.non_free_gates(),
                s.wires(),
                s.peak_live(),
                s.gate_counts()
            );
            s.value(info.output_index)
        }

        let bits = initialize_witness().to_bits();
        assert!(run(&bits), "the verifier accepts the valid proof");
        let mut bad = bits;
        bad[bits.len() / 2] ^= true;
        assert!(!run(&bad), "the verifier rejects a changed witness");
    }
}
