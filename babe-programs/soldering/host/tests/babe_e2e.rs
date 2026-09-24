use soldering_host::BabeBundleBuilder;
use verifiable_circuit_babe::transactions::OnchainSize;

#[test]
#[ignore = "requires artifacts match the dummy vk/program"]
fn e2e_babe_cac() {
    let run = BabeBundleBuilder::new().run_babe_e2e_cac().expect("BABE/CAC e2e flow");

    assert_eq!(run.assert_witness.size_bytes(), 2154); 
    assert_eq!(run.challenge_assert_witness.size_bytes(), 14312);
    assert_eq!(run.wrongly_challenged_witness.size_bytes(), 64);
}
