use ark_serialize::CanonicalSerialize;
use serde::{Deserialize, Serialize};
use crate::gc::{gc_ciphertexts_commit, non_free_gates_counts, SGC_PART1_CONSTANT_SIZE};
use crate::instance::CACInstance;
use crate::utils::{derive_hashlock, h_256};

/// Per-instance commitment sent from Verifier to Prover during C&C commit phase.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CACInstanceCommit {
    /// RIPEMD(SHA256)(label0) and RIPEMD(SHA256)(label1) for each input wire.
    pub epk: Vec<[[u8; 20]; 2]>,
    /// SHA256(label0) and SHA256(label1) for each of the 2 constant wires in fgc.
    pub constant_commits_fgc: [[[u8; 32]; 2]; 2],
    /// constant commit for sgc. Length must be `SGC_PART1_CONSTANT_SIZE` (510, = 2 + 2*N).
    pub constant_commits_sgc: Vec<[[u8; 32]; 2]>,
    /// commitment of b_blind in this instance.
    pub b_blind_commit: [u8; 32],
    pub h_msg: [u8; 20],
    /// RO(ct_setup) = SHA256(ct2_r_delta_g2 || ct3_masked_msg).
    pub h_ct_setup: [u8; 32],
    /// SHA256 commitment to the adaptor table.
    pub com_adaptor: [[u8; 32]; 2],
    /// SHA256 commitment to the GC gate ciphertexts.
    pub com_gc: [[u8; 32]; 3],
}

impl CACInstanceCommit {
    pub fn from_instance(instance: &CACInstance) -> Self {
        let delta = instance.secrets.delta;

        let input_commits = {
            let fgc_pairs: Vec<[[u8; 20]; 2]> = instance.secrets.input_0labels[0]
                .iter()
                .map(|&key| [derive_hashlock(&key.0), derive_hashlock(&(key ^ delta[0]).0)])
                .collect();
            let sgc_pairs: Vec<[[u8; 20]; 2]> = instance.secrets.input_0labels[1]
                .iter()
                .map(|&key| [derive_hashlock(&key.0), derive_hashlock(&(key ^ delta[1]).0)])
                .collect();
            let pairs: Vec<[[u8; 20]; 2]> = fgc_pairs.into_iter().chain(sgc_pairs).collect();
            pairs
        };

        let constant_commits_0 = std::array::from_fn(|w| {
            let l0 = instance.secrets.constant_0labels[0][w];
            [h_256(&l0.0), h_256(&(l0 ^ delta[0]).0)]
        });
        assert_eq!(instance.secrets.constant_0labels[1].len(), SGC_PART1_CONSTANT_SIZE);
        let constant_commits_1: Vec<[[u8; 32]; 2]> = instance.secrets.constant_0labels[1]
            .iter()
            .map(|&l0| [h_256(&l0.0), h_256(&(l0 ^ delta[1]).0)])
            .collect();

        let mut ct_setup_bytes = Vec::new();
        ct_setup_bytes.extend_from_slice(&instance.ct_setup.ct2_r_delta_g2);
        ct_setup_bytes.extend_from_slice(&instance.ct_setup.ct3_masked_msg);

        let mut b_blind_bytes = Vec::new();
        instance.secrets.b.serialize_compressed(&mut b_blind_bytes).expect("serialize r·G1P");

        let b_blind_commit = h_256(&b_blind_bytes);

        CACInstanceCommit {
            epk: input_commits,
            constant_commits_fgc: constant_commits_0,
            constant_commits_sgc: constant_commits_1,
            b_blind_commit,
            h_msg: derive_hashlock(&instance.secrets.msg),
            h_ct_setup: h_256(&ct_setup_bytes),
            com_adaptor: [instance.adaptor_tables[0].commit(), instance.adaptor_tables[1].commit()],
            com_gc: {
                let [fgc_count, sgc_count] = non_free_gates_counts();
                [
                    gc_ciphertexts_commit(&instance.ciphertexts_sets[0], fgc_count),
                    gc_ciphertexts_commit(&instance.ciphertexts_sets[1], sgc_count),
                    gc_ciphertexts_commit(&instance.ciphertexts_sets[2], fgc_count),
                ]
            }
        }
    }
}
