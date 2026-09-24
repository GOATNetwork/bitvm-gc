use ark_bn254::{Fr, G1Affine};
use ark_groth16::VerifyingKey as Groth16VerifyingKey;
use garbled_snark_verifier::bag::S;
use garbled_snark_verifier::dv_bn254::fq::Fq as DvFq;
use garbled_snark_verifier::dv_bn254::fr::Fr as DvFr;
use serde::{Deserialize, Serialize};
use crate::cac::CACSetupPackage;
use crate::dre::N_PADDED;
use crate::gc::SGC_PART1_CONSTANT_SIZE;
use crate::instance::CACInstance;
use crate::instance::commit::CACInstanceCommit;
use crate::instance::secret::Seed;

/// Instances processed in parallel per batch (RAM gate).
/// Override via CAC_BATCH_SIZE env var at runtime.
pub const BATCH_SIZE: usize = 8;

/// Per-instance encoding secrets needed for label computation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct InstanceLightSecrets {
    pub delta: [S; 2],
    pub input_0labels: [Vec<S>; 2],
}

impl InstanceLightSecrets {
    pub fn from_seed(seed: Seed) -> Self {
        let (delta, input_0labels) = crate::instance::secret::derive_light_from_seed(seed);
        Self { delta, input_0labels }
    }

    pub fn compute_pi1_labels(&self, pi1: G1Affine) -> Vec<S> {
        let delta = self.delta[0];
        DvFq::to_bits(pi1.x).into_iter().chain([false, false])
            .chain(DvFq::to_bits(pi1.y)).chain([false, false])
            .enumerate()
            .map(|(i, b)| {
                let key = self.input_0labels[0][i];
                if b { key ^ delta } else { key }
            })
            .collect()
    }

    pub fn compute_x_d_labels(&self, x_d: Fr) -> Vec<S> {
        let delta = self.delta[1];
        DvFr::to_bits(x_d).into_iter().chain([false, false])
            .enumerate()
            .map(|(i, b)| {
                let key = self.input_0labels[1][i];
                if b { key ^ delta } else { key }
            })
            .collect()
    }

    /// Build labels for all 3*N_PADDED input bits from the raw 96-byte Wots message.
    /// Layout: pi1.x | pi1.y | x_d (each contains N_PADDED bits).
    /// Same as serialize_uncompressed byte
    pub fn compute_labels_from_bytes(&self, raw: &[u8; 96]) -> Vec<S> {
        let delta_fgc = self.delta[0];
        let delta_sgc = self.delta[1];
        let mut labels = Vec::with_capacity(3 * N_PADDED);
        for i in 0..2 * N_PADDED {
            let bit = (raw[i / 8] >> (i % 8)) & 1;
            let key = self.input_0labels[0][i];
            labels.push(if bit == 1 { key ^ delta_fgc } else { key });
        }
        for i in 0..N_PADDED {
            let bit = (raw[64 + i / 8] >> (i % 8)) & 1;
            let key = self.input_0labels[1][i];
            labels.push(if bit == 1 { key ^ delta_sgc } else { key });
        }
        labels
    }
}

/// The C&C Verifier: manages N_CC garbled-circuit instances for Cut-and-Choose.
pub struct BABEVerifier {
    seeds: Vec<Seed>,
    commits: CACSetupPackage,
    vk: Groth16VerifyingKey<ark_bn254::Bn254>,
    static_public_inputs: Fr,
}

impl BABEVerifier {
    /// Create `n_cc` fresh instances processed in batches of BATCH_SIZE.
    pub fn new(
        n_cc: usize,
        vk: &Groth16VerifyingKey<ark_bn254::Bn254>,
        static_public_inputs: Fr,
    ) -> Result<Self, String> {
        use p3_maybe_rayon::prelude::*;

        let seeds: Vec<Seed> = (0..n_cc).map(|_| rand::random()).collect();

        let n_cores = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8);
        let batch_size = std::env::var("CAC_BATCH_SIZE")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(BATCH_SIZE)
            .min(n_cores)
            .min(n_cc);

        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(batch_size)
            .build()
            .map_err(|e| e.to_string())?;

        let mut commits = Vec::with_capacity(n_cc);

        for batch_seeds in seeds.chunks(batch_size) {
            // Generate up to BATCH_SIZE instances in parallel. For each instance,
            // stream-hash the ciphertexts and adaptor table without materializing them.
            let batch_results: Vec<Result<CACInstanceCommit, String>> =
                pool.install(|| {
                    batch_seeds
                        .par_iter()
                        .map(|&seed| {
                            let commit =
                                CACInstance::commit_from_seed(seed, vk, static_public_inputs)?;
                            Ok(commit)
                        })
                        .collect()
                });

            for result in batch_results {
                commits.push(result?);
            }
        }
        let commits = CACSetupPackage { commits };
        Ok(Self {
            seeds,
            commits,
            vk: vk.clone(),
            static_public_inputs,
        })
    }

    /// Restore a `BABEVerifier` from previously persisted state.
    pub fn from_state(
        seeds: &[Seed],
        commits: &CACSetupPackage,
        vk: &Groth16VerifyingKey<ark_bn254::Bn254>,
        static_public_inputs: Fr,
    ) -> Option<Self> {
        if seeds.len() != commits.commits.len() {
            return None;
        }
        Some(Self {
            seeds: seeds.to_vec(),
            commits: commits.clone(),
            vk: vk.clone(),
            static_public_inputs
        })

    }

    /// Return the C&C commit package from pre-computed commitments.
    pub fn commit(&self) -> CACSetupPackage {
        self.commits.clone()
    }

    /// After receiving the finalized indices, reveal:
    /// - seeds for the non-finalized instances (N_CC - M_CC)
    /// - full GC data for the M_CC finalized instances, regenerated one-by-one
    pub fn open(
        &self,
        finalized_indices: &[usize],
    ) -> Result<(Vec<(usize, Seed)>, Vec<crate::cac::FinalizedInstanceData>), String> {
        let finalized_set: std::collections::HashSet<usize> =
            finalized_indices.iter().copied().collect();

        let opened: Vec<(usize, Seed)> = (0..self.seeds.len())
            .filter(|i| !finalized_set.contains(i))
            .map(|i| (i, self.seeds[i]))
            .collect();

        // Regenerate all M_CC finalized instances in parallel
        use p3_maybe_rayon::prelude::*;
        let finalized: Vec<Result<crate::cac::FinalizedInstanceData, String>> = finalized_indices
            .par_iter()
            .map(|&i| {
                let seed = self.seeds.get(i).ok_or_else(|| {
                    format!(
                        "instance {i}: index out of range ({} seeds)",
                        self.seeds.len()
                    )
                })?;
                let inst = CACInstance::new_from_seed(
                    *seed,
                    &self.vk,
                    self.static_public_inputs,
                )?;

                let constant_labels_0 = [
                    inst.secrets.constant_0labels[0][0],
                    inst.secrets.constant_0labels[0][1] ^ inst.secrets.delta[0],
                ];
                let mut constant_labels_1 = vec![
                    inst.secrets.constant_0labels[1][0],
                    inst.secrets.constant_0labels[1][1] ^ inst.secrets.delta[1],
                ];
                constant_labels_1.extend(inst.get_b_value_labels());
                assert_eq!(constant_labels_1.len(), SGC_PART1_CONSTANT_SIZE);

                Ok(crate::cac::FinalizedInstanceData {
                    index: i,
                    ciphertext_sets: inst.ciphertexts_sets,
                    adaptor_tables: inst.adaptor_tables,
                    ct_setup: inst.ct_setup,
                    constant_labels_0,
                    constant_labels_1,
                    b: inst.secrets.b,
                    aes_salt: inst.secrets.aes_salt,
                })
                // inst is dropped here
            })
            .collect();
        let finalized = finalized.into_iter().collect::<Result<Vec<_>, _>>()?;

        Ok((opened, finalized))
    }

    /// Compute the active π₁ input labels for instance `idx` given a concrete π₁.
    pub fn compute_pi1_labels(&self, idx: usize, pi1: G1Affine) -> Vec<S> {
        let ls = InstanceLightSecrets::from_seed(self.seeds[idx]);
        ls.compute_pi1_labels(pi1)
    }

    /// Compute the active x_d input labels for instance `idx` given a concrete x_d.
    pub fn compute_x_d_labels(&self, idx: usize, x_d: Fr) -> Vec<S> {
        let ls = InstanceLightSecrets::from_seed(self.seeds[idx]);
        ls.compute_x_d_labels(x_d)
    }

    /// Compute all input labels for instance `idx` from the raw 96-byte Wots message.
    pub fn compute_labels_from_bytes(&self, idx: usize, raw: &[u8; 96]) -> Vec<S> {
        let ls = InstanceLightSecrets::from_seed(self.seeds[idx]);
        ls.compute_labels_from_bytes(raw)
    }

    pub fn get_seeds(&self) -> Vec<Seed> {
        self.seeds.clone()
    }

    pub fn light_secrets_for(&self, idx: usize) -> InstanceLightSecrets {
        InstanceLightSecrets::from_seed(self.seeds[idx])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;
    use ark_crypto_primitives::snark::CircuitSpecificSetupSNARK;
    use rand::SeedableRng;
    use crate::babe::DummyMulCircuit;
    use crate::cac::CACSetupPackage;
    use crate::instance::commit::CACInstanceCommit;
    use crate::prover::GROTH_16_SEED;
    use crate::utils::pi1_xd_to_wots96_msg;

    fn test_seed(b: u8) -> Seed {
        let mut s = [0u8; 32];
        s[0] = b;
        s
    }

    fn dummy_vk() -> Groth16VerifyingKey<ark_bn254::Bn254> {
        let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(GROTH_16_SEED);
        let a = Fr::from(3u64);
        let b = Fr::from(7u64);
        let (_, vk) = ark_groth16::Groth16::<ark_bn254::Bn254>::setup(
            DummyMulCircuit::<Fr> { a: Some(a), b: Some(b) }, &mut rng,
        ).expect("groth16 setup");
        vk
    }

    fn dummy_commit() -> CACInstanceCommit {
        CACInstanceCommit {
            epk: vec![],
            constant_commits_fgc: [[[0u8; 32]; 2]; 2],
            constant_commits_sgc: vec![],
            b_blind_commit: [0u8; 32],
            h_msg: [0u8; 20],
            h_ct_setup: [0u8; 32],
            com_adaptor: [[0u8; 32]; 2],
            com_gc: [[0u8; 32]; 3],
        }
    }

    // Two independent bit-extraction paths (raw bytes vs. DvFq/DvFr::to_bits) must agree.
    #[test]
    fn test_compute_labels_from_bytes_matches_split_computation() {
        let ls = InstanceLightSecrets::from_seed(test_seed(7));

        let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(1);
        let pi1 = G1Affine::from(ark_bn254::G1Projective::rand(&mut rng));
        let x_d = Fr::rand(&mut rng);

        let pi1_labels = ls.compute_pi1_labels(pi1);
        let xd_labels = ls.compute_x_d_labels(x_d);
        assert_eq!(pi1_labels.len(), 2 * N_PADDED);
        assert_eq!(xd_labels.len(), N_PADDED);

        let split: Vec<S> = pi1_labels.into_iter().chain(xd_labels).collect();

        let raw = pi1_xd_to_wots96_msg(&pi1, x_d);
        let from_bytes = ls.compute_labels_from_bytes(&raw);
        assert_eq!(from_bytes.len(), 3 * N_PADDED);

        assert_eq!(from_bytes, split);
    }

    #[test]
    fn test_from_state_rejects_length_mismatch() {
        let vk = dummy_vk();
        let commits = CACSetupPackage { commits: vec![dummy_commit(), dummy_commit()] };

        let seeds3 = [test_seed(1), test_seed(2), test_seed(3)];
        let seeds2 = [test_seed(1), test_seed(2)];
        assert!(BABEVerifier::from_state(&seeds3, &commits, &vk, Fr::from(0u64)).is_none());
        assert!(BABEVerifier::from_state(&seeds2, &commits, &vk, Fr::from(0u64)).is_some());
    }

    #[test]
    fn test_open_rejects_out_of_range_index() {
        let vk = dummy_vk();
        let commits = CACSetupPackage { commits: vec![dummy_commit()] };
        let verifier = BABEVerifier::from_state(&[test_seed(1)], &commits, &vk, Fr::from(0u64)).unwrap();

        let err = verifier.open(&[5]).expect_err("index 5 is out of range for 1 seed");
        assert!(err.contains('5'), "error should reference the bad index: {err}");
    }
}
