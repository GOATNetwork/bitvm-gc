use ark_bn254::{Fq, Fr, G1Affine};
use ark_ff::{UniformRand, Zero};
use garbled_snark_verifier::bag::S;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use rand_chacha::rand_core::RngCore;
use crate::dre::{N, N_PADDED, utils::sample_rhos};

pub type Seed = [u8; 32];

pub struct InstanceSecrets {
    /// 2 deltas for 2 garbled circuits
    pub delta:         [S; 2],
    pub r:             Fr,
    pub msg:           [u8; 32],
    /// label0 per input wire, for 2 circuits
    /// fgc input size = 2 * N_PADDED // pi_1
    /// sgc input size = N_PADDED // x_d
    pub input_0labels: [Vec<S>; 2],
    /// Constant 0labels.
    /// fgc size = 2 (0/1)
    /// sgc size = 2 + 2 * N (for B)
    pub constant_0labels: [Vec<S>; 2],
    pub rhos:          [Vec<G1Affine>; 2],
    pub fq_deltas:     [Vec<Fq>; 2],
    pub b: G1Affine,
    /// Public per-instance salt for the `_aes` garbling-hash backend (Guo-Katz-Wang-Yu,
    /// ePrint 2019/074). Unused by other hash backends.
    pub aes_salt: S,
}

/// Cheaply derive only the two fields needed for label encoding
pub fn derive_light_from_seed(seed: Seed) -> ([S; 2], [Vec<S>; 2]) {
    let mut rng = ChaCha20Rng::from_seed(seed);
    let delta = [gen_s(&mut rng, 1)[0], gen_s(&mut rng, 1)[0]];
    let _ = Fr::rand(&mut rng);          // advance past r
    rng.fill_bytes(&mut [0u8; 32]);      // advance past msg
    let input_0labels = [gen_s(&mut rng, 2 * N_PADDED), gen_s(&mut rng, N_PADDED)];
    (delta, input_0labels)
}

impl InstanceSecrets {
    pub fn new_from_seed(seed: Seed) -> Self {
        let mut rng = ChaCha20Rng::from_seed(seed);

        let delta = [gen_s(&mut rng, 1)[0], gen_s(&mut rng, 1)[0]];

        let r = Fr::rand(&mut rng);

        let mut msg = [0u8; 32];
        rng.fill_bytes(&mut msg);

        let input_0labels = [gen_s(&mut rng, 2 * N_PADDED), gen_s(&mut rng, N_PADDED)];

        let constant_val_labels = [gen_s(&mut rng, 2), gen_s(&mut rng, 2 + 2 * N)];

        let rhos = [sample_rhos(&mut rng), sample_rhos(&mut rng)];

        let fq_deltas = [gen_fq_deltas(&mut rng, N), gen_fq_deltas(&mut rng, N)];

        let b = G1Affine::rand(&mut rng);

        let aes_salt = gen_s(&mut rng, 1)[0];

        Self {
            delta,
            r,
            msg,
            input_0labels,
            constant_0labels: constant_val_labels,
            rhos,
            fq_deltas,
            b,
            aes_salt,
        }
    }
}

fn gen_s<R: RngCore>(rng: &mut R, n: usize) -> Vec<S> {
    (0..n)
        .map(|_| {
            let mut b = [0u8; 16];
            rng.fill_bytes(&mut b);
            S(b)
        })
        .collect()
}

fn gen_fq_deltas<R: RngCore>(rng: &mut R, n: usize) -> Vec<Fq> {
    (0..n)
        .map(|_| loop {
            let v = Fq::rand(rng);
            if !v.is_zero() {
                break v;
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_seed(b: u8) -> Seed {
        let mut s = [0u8; 32];
        s[0] = b;
        s
    }

    // `derive_light_from_seed` replays the same RNG draw sequence as the prefix of
    // `InstanceSecrets::new_from_seed` (delta, then r, then msg, then input_0labels).
    // If the two ever drift out of sync, `BABEVerifier` would silently compute wrong
    // GC labels with nothing else catching it — so pin the equivalence directly.
    #[test]
    fn test_derive_light_matches_full_secrets() {
        for b in [0u8, 1, 42, u8::MAX] {
            let seed = test_seed(b);
            let (light_delta, light_labels) = derive_light_from_seed(seed);
            let full = InstanceSecrets::new_from_seed(seed);

            assert_eq!(light_delta, full.delta, "delta mismatch for seed {b}");
            assert_eq!(light_labels, full.input_0labels, "input_0labels mismatch for seed {b}");
        }
    }

    #[test]
    fn test_derive_light_differs_across_seeds() {
        let (delta_a, labels_a) = derive_light_from_seed(test_seed(1));
        let (delta_b, labels_b) = derive_light_from_seed(test_seed(2));

        assert_ne!(delta_a, delta_b);
        assert_ne!(labels_a, labels_b);
    }
}
