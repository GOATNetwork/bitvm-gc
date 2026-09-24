use ark_bn254::Fq;

pub mod utils;
pub mod matrices;
pub const N: usize = 254;
/// Padded input width per field element: 254 real bits + 2 MSB slots checked by the GC.
pub const N_PADDED: usize = 256;
pub const U_BAR_SIZE: usize = 1 + 5 * N; // 1271 — ū(π) binary decomposition
pub const Q_SIZE: usize = 2 * N;       // 508  — standard affine (x,y) of x_d·L_2 + B

/// Decoding: f_i = r_i·π + ρ_i  (Jacobian coords)
pub struct DREDecoding {
    pub f_i: (Fq, Fq, Fq),
}