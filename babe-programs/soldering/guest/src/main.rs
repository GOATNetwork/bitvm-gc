#![no_std]
#![no_main]
extern crate alloc;

zkm_zkvm::entrypoint!(main);

use verifiable_circuit_babe::soldering::{soldering_guest_compute, SolderedLabelsData, SolderedWiresInput};

fn main() {
    let input = zkm_zkvm::io::read::<SolderedWiresInput>();
    let output = soldering_guest_compute(&input);
    zkm_zkvm::io::commit::<SolderedLabelsData>(&output);
}
