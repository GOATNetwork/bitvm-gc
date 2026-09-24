//! This mod mainly ported from alpenlabs/dv-pari-circuit.
//!
//! Circuit (_ckt) and Reference (_ref) Implementation for DV Verifier.
//! Reference implementation primarily serves to verify the correctness of respective circuit based implementations
//!
pub mod blake3_ckt;

pub mod builder;
pub mod stream;

pub mod curve_ckt;
#[cfg(test)]
pub mod curve_ref;
pub mod curve_scalar_mul_ckt;

pub mod dv_ckt;

#[cfg(test)]
pub mod dv_ref;

pub mod gf_ckt;
pub mod gf_interpolate_ckt;
pub mod gf_mul_ckt;
pub mod gf_ref;

pub mod gf9_ckt;
pub mod gf9_eval_ckt;
pub mod gf9_ref;

pub mod fr_ckt;
pub mod fr_ref;
pub mod types;
