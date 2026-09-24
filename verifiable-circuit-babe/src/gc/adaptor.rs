use ark_bn254::{Fq, Fr, G1Affine};
use ark_ff::Zero;
use ark_serialize::CanonicalSerialize;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use crate::dre::{DREDecoding, N, U_BAR_SIZE};
use crate::dre::matrices::{build_d_i_sparse, nonzero_col_indices};
use crate::gc::utils::{aes_dec, aes_enc, prf_fq};
use crate::utils::{deserialize_fq, serialize_fq};

/// Ciphertext of one Fq element (32 bytes = 2 AES-128 blocks)
pub type Ct = [u8; 32];

/// Ciphertexts for ubar=0.
/// `offset` = Σ_k s_k = Σ_k (prf_fq(label_1_k) - D_k).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SparseAdaptorRow {
    pub cts: Vec<Ct>,
    #[serde(serialize_with = "serialize_fq", deserialize_with = "deserialize_fq")]
    pub offset: Fq,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SparseAdaptorEntry {
    pub x: SparseAdaptorRow,
    pub y: SparseAdaptorRow,
    pub z: SparseAdaptorRow,
}

/// Adaptor table storing ciphertexts only for structurally nonzero D entries.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SparseAdaptorTable {
    pub entries: Vec<SparseAdaptorEntry>,
}

impl SparseAdaptorTable {
    pub fn build_from_r_and_u_bar_labels(
        r: Fr,
        labels: &[[u8; 16]],
        rhos: &[G1Affine],
        fq_deltas: &[Fq],
    ) -> Self {
        assert_eq!(labels.len(), 2 * U_BAR_SIZE);
        assert_eq!(rhos.len(), N);
        assert_eq!(fq_deltas.len(), N);

        #[cfg(debug_assertions)]
        {
            use ark_bn254::G1Projective;
            let mut sum = G1Projective::zero();
            let mut pw = Fr::from(1u64);
            for rho in rhos {
                sum += G1Projective::from(*rho) * pw;
                pw += pw;
            }
            debug_assert!(sum.is_zero(), "ρ constraint ∑ 2^i·ρ_i = O violated");
        }

        let r_bits = garbled_snark_verifier::dv_bn254::fr::Fr::to_bits(r);
        let col_indices = nonzero_col_indices();
        let prf_cache: Vec<Fq> = (0..U_BAR_SIZE).map(|k| prf_fq(&labels[2 * k + 1])).collect();

        let entries = (0..N)
            .map(|i| {
                let r_i = Fq::from(r_bits[i] as u8);
                let d = build_d_i_sparse(fq_deltas[i], r_i, &rhos[i]);

                let build_row = |j: usize| -> SparseAdaptorRow {
                    let mut offset = Fq::zero();
                    let cts = col_indices[j]
                        .iter()
                        .zip(d[j].iter())
                        .map(|(&k, &d_val)| {
                            let s_k = prf_cache[k] - d_val;
                            offset += s_k;
                            aes_enc(&s_k, &labels[2 * k])
                        })
                        .collect();
                    SparseAdaptorRow { cts, offset }
                };

                SparseAdaptorEntry {
                    x: build_row(0),
                    y: build_row(1),
                    z: build_row(2),
                }
            })
            .collect();

        SparseAdaptorTable { entries }
    }

    /// Build the adaptor table entry-by-entry, hashing each row on-the-fly without
    /// materializing the full `Vec<SparseAdaptorEntry>`. Produces the same hash as
    /// `SparseAdaptorTable::build_from_r_and_u_bar_labels(...).commit()`.
    pub fn build_and_hash(
        r: Fr,
        labels: &[[u8; 16]],
        rhos: &[G1Affine],
        fq_deltas: &[Fq],
    ) -> [u8; 32] {
        assert_eq!(labels.len(), 2 * U_BAR_SIZE);
        assert_eq!(rhos.len(), N);
        assert_eq!(fq_deltas.len(), N);

        let r_bits = garbled_snark_verifier::dv_bn254::fr::Fr::to_bits(r);
        let col_indices = nonzero_col_indices();
        let prf_cache: Vec<Fq> = (0..U_BAR_SIZE).map(|k| prf_fq(&labels[2 * k + 1])).collect();

        let mut hasher = Sha256::new();
        let mut buf = Vec::new();

        for i in 0..N {
            let r_i = Fq::from(r_bits[i] as u8);
            let d = build_d_i_sparse(fq_deltas[i], r_i, &rhos[i]);

            for j in 0..3 {
                let mut offset = Fq::zero();
                for (&k, &d_val) in col_indices[j].iter().zip(d[j].iter()) {
                    let s_k = prf_cache[k] - d_val;
                    offset += s_k;
                    let ct = aes_enc(&s_k, &labels[2 * k]);
                    hasher.update(ct.as_slice());
                }
                buf.clear();
                offset.serialize_compressed(&mut buf).expect("serialize Fq offset");
                hasher.update(&buf);
                // row data is never stored — dropped here
            }
        }

        hasher.finalize().into()
    }

    /// SHA256 over all ciphertexts and Fq offsets in entry/row order.
    pub fn commit(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for entry in &self.entries {
            for row in [&entry.x, &entry.y, &entry.z] {
                for ct in &row.cts {
                    hasher.update(ct.as_slice());
                }
                let mut buf = Vec::new();
                row.offset.serialize_compressed(&mut buf).expect("serialize Fq offset");
                hasher.update(&buf);
            }
        }
        hasher.finalize().into()
    }

    /// Decrypt the adaptor table and sum each row to recover Jacobian coords of r_i·π + ρ_i.
    pub fn eval(&self, labels: &[[u8; 16]], u_bar: &[Fq]) -> Vec<DREDecoding> {
        assert_eq!(labels.len(), U_BAR_SIZE);
        assert_eq!(u_bar.len(), U_BAR_SIZE);

        let col_indices = nonzero_col_indices();

        self.entries
            .iter()
            .map(|entry| {
                let dec_row = |row: &SparseAdaptorRow, j: usize| -> Fq {
                    let raw: Fq = col_indices[j]
                        .iter()
                        .zip(row.cts.iter())
                        .map(|(&k, ct)| {
                            if u_bar[k].is_zero() {
                                aes_dec(ct, &labels[k])
                            } else {
                                prf_fq(&labels[k])
                            }
                        })
                        .sum();
                    raw - row.offset
                };

                DREDecoding {
                    f_i: (dec_row(&entry.x, 0), dec_row(&entry.y, 1), dec_row(&entry.z, 2)),
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Fr, G1Projective};
    use ark_ec::CurveGroup;
    use ark_ff::{UniformRand, Zero, One};
    use garbled_snark_verifier::core::s::S;
    use garbled_snark_verifier::core::utils::NON_CAC_DELTA;
    use crate::dre::matrices::u_bar_vec;

    #[test]
    fn test_sparse_adaptor_table() {
        let mut rng = rand::thread_rng();
        let pi = G1Projective::rand(&mut rng).into_affine();
        let r = Fr::rand(&mut rng);

        let u_bar_pi = u_bar_vec(&pi);

        let labels: Vec<[u8; 16]> = (0..U_BAR_SIZE)
            .flat_map(|_| {
                let l0 = S::random();
                let l1 = l0 ^ NON_CAC_DELTA;
                [l0.0, l1.0]
            })
            .collect();

        let rhos = crate::dre::utils::sample_rhos(&mut rng);
        let fq_deltas: Vec<Fq> = (0..N)
            .map(|_| loop {
                let v = UniformRand::rand(&mut rng);
                if !Zero::is_zero(&v) { break v; }
            })
            .collect();
        let table = SparseAdaptorTable::build_from_r_and_u_bar_labels(r, &labels, &rhos, &fq_deltas);

        let eval_labels: Vec<[u8; 16]> = (0..U_BAR_SIZE)
            .map(|k| if u_bar_pi[k].is_zero() { labels[2 * k] } else { labels[2 * k + 1] })
            .collect();

        let decodings = table.eval(&eval_labels, &u_bar_pi);

        let mut sum = G1Projective::zero();
        let mut weight = Fr::one();
        for decoding in decodings {
            let (x, y, z) = decoding.f_i;
            sum += G1Projective::new(x, y, z) * weight;
            weight += weight;
        }

        let expected = (G1Projective::from(pi) * r).into_affine();
        assert_eq!(sum.into_affine(), expected, "Sparse: ∑ 2^i·f_i should equal r·π");
    }
}