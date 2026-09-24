// ─── Transaction skeletons. This will be replaced by real Txn in Bitvm2-node ─────────

use ark_bn254::{Bn254, Fq, Fr, G1Affine, G2Affine};
use ark_ec::CurveGroup;
use ark_groth16::{Proof as Groth16Proof, VerifyingKey as Groth16VerifyingKey};
use ark_serialize::CanonicalDeserialize;
use serde::{Deserialize, Serialize};
use crate::babe::{BabeBtcSig, BtcPk, BTC_SIG_BYTES, MSG_BYTES};
use crate::utils::{g1_from_ser_checked, g2_from_ser_checked};
use crate::wots::Wots96;
use bitvm::signatures::Wots;

/// Constants embedded in the locking script of tx_Deposit output 0.
/// Script: CheckSig(pk_P) ∧ CheckSig(pk_V)
#[derive(Debug, Clone)]
pub struct TxDepositLock {
    pub pk_p: BtcPk,
    pub pk_v: BtcPk,
    pub amount: u64,
}

#[derive(Debug, Clone)]
pub struct TxChallengeAssertOutputLock {
    pub pk_p: BtcPk,
    pub pk_v: BtcPk,
    pub h_msgs: Vec<[u8; 20]>,
}

// ─── Transaction witnesses (on-chain data) ────────────────────────────────────

/// tx_Assert — witness for input 0.
/// Input spends a UTXO with: CheckWotsSig(wots_pk_P)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TxAssertWitness {
    /// Wots96 signature over the 96-byte message (π₁.x LE-32 ∥ π₁.y LE-32 ∥ x_d LE-32).
    pub wots_sig: Vec<[u8; 21]>,
    /// π₂ (G2Affine) from the Groth16 proof, compressed-serialized.
    pub pi2: Vec<u8>,
    /// π₃ (G1Affine) from the Groth16 proof, compressed-serialized.
    pub pi3: Vec<u8>,
}

impl TxAssertWitness {
    /// Check that the Assert witness is in the correct format and recover (π₁, x_d).
    /// Returns None if the 96-byte message does not decode to a valid (G1Affine, Fr) pair
    pub fn try_recover_pi1_xd(&self) -> Option<(G1Affine, Fr)> {
        // wrong length
        if self.wots_sig.len() != Wots96::TOTAL_DIGIT_LEN as usize {
            return None;
        }

        let arr_sig: [[u8; 21]; Wots96::TOTAL_DIGIT_LEN as usize] =
            self.wots_sig.clone().try_into().ok()?;
        let msg = Wots96::signature_to_message(&arr_sig);
        let x = Fq::deserialize_uncompressed(&msg[0..32]).ok()?;
        let y = Fq::deserialize_uncompressed(&msg[32..64]).ok()?;
        let pi1 = G1Affine::new_unchecked(x, y);
        if !pi1.is_on_curve() {
            return None;
        }
        let x_d = Fr::deserialize_uncompressed(&msg[64..96]).ok()?;
        Some((pi1, x_d))
    }

    /// Recover (π₂: G2Affine, π₃: G1Affine) from the compressed-serialized bytes.
    /// Returns None if either is malformed, at infinity, off-curve, or in the wrong subgroup.
    pub fn recover_pi2_pi3(&self) -> Option<(G2Affine, G1Affine)> {
        let pi2 = g2_from_ser_checked(&self.pi2)?.into_affine();
        let pi3 = g1_from_ser_checked(&self.pi3)?.into_affine();
        Some((pi2, pi3))
    }

    /// Reconstruct the full Groth16 proof (π₁, π₂, π₃) and verify it.
    /// π₁ and x_d are recovered from `wots_sig`; π₂ and π₃ from `pi2`/`pi3`.
    /// `static_public_inputs` are prepended to `[x_d]` to form the complete public input vector.
    /// Returns false if any field is malformed or the proof does not verify.
    pub fn verify_groth16_proof(
        &self,
        vk: &Groth16VerifyingKey<Bn254>,
        static_public_inputs: &[Fr],
    ) -> bool {
        let (pi1, x_d) = match self.try_recover_pi1_xd() {
            Some(v) => v,
            None => return false,
        };
        let (pi2, pi3) = match self.recover_pi2_pi3() {
            Some(v) => v,
            None => return false,
        };
        let mut public_inputs = static_public_inputs.to_vec();
        public_inputs.push(x_d);
        verify_groth16_proof_components(pi1, pi2, pi3, &public_inputs, vk)
    }
}

/// Reconstruct a Groth16 proof from its components and verify it against `vk`.
/// `public_inputs` must be the complete ordered vector expected by the circuit.
fn verify_groth16_proof_components(
    pi1: G1Affine,
    pi2: G2Affine,
    pi3: G1Affine,
    public_inputs: &[Fr],
    vk: &Groth16VerifyingKey<Bn254>,
) -> bool {
    let proof = Groth16Proof { a: pi1, b: pi2, c: pi3 };
    let pvk = ark_groth16::prepare_verifying_key(vk);
    ark_groth16::Groth16::<Bn254>::verify_proof(&pvk, &proof, public_inputs).unwrap_or(false)
}

/// tx_ChallengeAssert — witness for input 0.
/// Input spends tx_Assert output 1: CheckSigsConsistent(wots_pk_P, epk_V) ∧ CheckSig(pk_V) ∧ CheckSig(pk_P)
/// Script verifies:
///   (a) Wots96 sig is valid for some 96-byte message m — binds π₁ and x_d to the prover
///   (b) SHA256(L[i]) == epk_V[i][bit_i(m)]  — L[i] is the correct GC label for bit_i under epk
///   (c) Wots96 sig and epk labels are consistent over the same message m — both sign/encode the same bits

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChallengeAssertWitnessRaw {
    /// L₁…L_M — one GC input label per bit of π₁ and x_d, LAMPORT_N × 16 bytes.
    pub input_labels: Vec<[u8; 16]>,
    /// Wots96 sig re-posted from TxAssertWitness to bind the labels to π₁ and x_d.
    pub wots_sig: Vec<[u8; 21]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TxChallengeAssertWitness {
    pub witness: ChallengeAssertWitnessRaw,
    /// VerifierLiveSig
    pub sig_v: BabeBtcSig,
    /// ProverPresigChallengeAssert
    pub sig_p: BabeBtcSig,
}

/// tx_WronglyChallenged — witness for input 0.
/// Input spends tx_ChallengeAssert output 0: HashLock(h_msg) ∧ CheckSig(pk_P)
/// Script verifies: SHA256(msg) == h_msg.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TxWronglyChallengedWitness {
    /// ProverLiveSig
    pub sig_p: BabeBtcSig,
    /// Decrypted secret — preimage of h_msg = SHA256(msg).
    pub msg: [u8; 32],
}

/// tx_NoWithdraw — witnesses for inputs 0 and 1.
/// Input 0 spends tx_Assert output 0:          CheckSig(pk_P) ∧ CheckSig(pk_V)
/// Input 1 spends tx_ChallengeAssert output 0: RelTimelock(Δ₁) ∧ CheckSig(pk_V)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TxNoWithdrawWitness {
    /// ProverPresigNoWithdraw — for input 0
    pub input0_sig_p: BabeBtcSig,
    /// VerifierLiveSig — for input 0
    pub input0_sig_v: BabeBtcSig,
    /// VerifierLiveSig — for input 1, after RelTimelock(Δ₁)
    pub input1_sig_v: BabeBtcSig,
}

/// tx_Withdraw — witnesses for inputs 0 and 1.
/// Input 0 spends tx_Deposit output 0: CheckSig(pk_P) ∧ CheckSig(pk_V)
/// Input 1 spends tx_Assert output 0:  RelTimelock(Δ₂) ∧ CheckSig(pk_P) ∧ CheckSig(pk_V)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TxWithdrawWitness {
    /// ProverLiveSig — for input 0
    pub input0_sig_p: BabeBtcSig,
    /// VerifierPresigWithdraw — for input 0
    pub input0_sig_v: BabeBtcSig,
    /// ProverLiveSig — for input 1, after RelTimelock(Δ₂)
    pub input1_sig_p: BabeBtcSig,
    /// VerifierPresigWithdraw — for input 1
    pub input1_sig_v: BabeBtcSig,
}

// ─── OnchainSize trait ────────────────────────────────────────────────────────

pub trait OnchainSize {
    fn size_bytes(&self) -> usize;
}

impl OnchainSize for TxAssertWitness {
    fn size_bytes(&self) -> usize {
        Wots96::TOTAL_DIGIT_LEN as usize * 21
            + 64  // π₂: G2Affine compressed
            + 32  // π₃: G1Affine compressed
    }
}

impl OnchainSize for TxChallengeAssertWitness {
    fn size_bytes(&self) -> usize {
        self.witness.input_labels.len() * 16                 // LAMPORT_N × 16 bytes
            + Wots96::TOTAL_DIGIT_LEN as usize * 20  // wots_sig preimages
            + BTC_SIG_BYTES                          // sig_v: 32 bytes
            + BTC_SIG_BYTES                          // sig_p: 32 bytes
    }
}

impl OnchainSize for TxWronglyChallengedWitness {
    fn size_bytes(&self) -> usize {
        BTC_SIG_BYTES // sig_p: 32 bytes
            + MSG_BYTES   // msg:   32 bytes
    }
}

impl OnchainSize for TxNoWithdrawWitness {
    fn size_bytes(&self) -> usize {
        BTC_SIG_BYTES * 3 // 3 sigs × 32 bytes = 96 bytes
    }
}

impl OnchainSize for TxWithdrawWitness {
    fn size_bytes(&self) -> usize {
        BTC_SIG_BYTES * 4 // 4 sigs × 32 bytes = 128 bytes
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Fq, Fr, G1Affine};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;
    use ark_serialize::CanonicalSerialize;
    use bitvm::signatures::Wots;
    use crate::babe::DummyMulCircuit;
    use crate::utils::pi1_xd_to_wots96_msg;
    use crate::wots::Wots96;

    fn make_witness_from_raw_msg(msg: &[u8; 96]) -> TxAssertWitness {
        let sk = Wots96::generate_secret_key();
        TxAssertWitness { wots_sig: Wots96::sign(&sk, msg).to_vec(), pi2: vec![], pi3: vec![] }
    }

    // ── try_recover_pi1_xd ─────────────────────────────────────────

    #[test]
    fn test_recover_valid_generator_and_fr() {
        let pi1 = G1Affine::generator();
        let x_d = Fr::from(42u64);
        let msg = pi1_xd_to_wots96_msg(&pi1, x_d);
        let witness = make_witness_from_raw_msg(&msg);

        let (recovered_pi1, recovered_xd) = witness.try_recover_pi1_xd().unwrap();
        assert_eq!(recovered_pi1, pi1);
        assert_eq!(recovered_xd, x_d);
    }

    #[test]
    fn test_recover_wrong_length() {
        let witness = TxAssertWitness {
            wots_sig: vec![[0u8; 21]; Wots96::TOTAL_DIGIT_LEN as usize - 1],
            pi2: vec![], pi3: vec![],
        };
        assert!(witness.try_recover_pi1_xd().is_none());

        let witness = TxAssertWitness {
            wots_sig: vec![[0u8; 21]; Wots96::TOTAL_DIGIT_LEN as usize + 1],
            pi2: vec![], pi3: vec![],
        };
        assert!(witness.try_recover_pi1_xd().is_none());
    }

    #[test]
    fn test_recover_empty_sig() {
        let witness = TxAssertWitness { wots_sig: vec![], pi2: vec![], pi3: vec![] };
        assert!(witness.try_recover_pi1_xd().is_none());
    }

    #[test]
    fn test_recover_off_curve_point() {
        // (1, 1) is not on BN254 G1
        let mut msg = [0u8; 96];
        let mut buf = Vec::new();
        Fq::from(1u64).serialize_uncompressed(&mut buf).unwrap();
        msg[0..32].copy_from_slice(&buf);
        buf.clear();
        Fq::from(1u64).serialize_uncompressed(&mut buf).unwrap();
        msg[32..64].copy_from_slice(&buf);
        let witness = make_witness_from_raw_msg(&msg);
        assert!(witness.try_recover_pi1_xd().is_none());
    }

    #[test]
    fn test_recover_x_coordinate_out_of_field() {
        // 0xFF..FF > Fq modulus → Fq::deserialize_uncompressed returns Err
        let mut msg = [0u8; 96];
        msg[0..32].fill(0xFF);
        let witness = make_witness_from_raw_msg(&msg);
        assert!(witness.try_recover_pi1_xd().is_none());
    }

    #[test]
    fn test_recover_y_coordinate_out_of_field() {
        let pi1 = G1Affine::generator();
        let mut buf = Vec::new();
        pi1.x.serialize_uncompressed(&mut buf).unwrap();
        let mut msg = [0u8; 96];
        msg[0..32].copy_from_slice(&buf);
        msg[32..64].fill(0xFF); // y > Fq modulus
        let witness = make_witness_from_raw_msg(&msg);
        assert!(witness.try_recover_pi1_xd().is_none());
    }

    #[test]
    fn test_recover_xd_out_of_field() {
        let pi1 = G1Affine::generator();
        let mut msg = pi1_xd_to_wots96_msg(&pi1, Fr::from(0u64));
        msg[64..96].fill(0xFF); // x_d > Fr modulus
        let witness = make_witness_from_raw_msg(&msg);
        assert!(witness.try_recover_pi1_xd().is_none());
    }

    // ── recover_pi2_pi3 ───────────────────────────────────────────────────────

    #[test]
    fn test_recover_pi2_pi3_valid() {
        let mut rng = rand::thread_rng();
        let pi2 = ark_bn254::G2Projective::rand(&mut rng).into_affine();
        let pi3 = ark_bn254::G1Projective::rand(&mut rng).into_affine();

        let mut pi2_bytes = Vec::new();
        pi2.serialize_compressed(&mut pi2_bytes).unwrap();
        let mut pi3_bytes = Vec::new();
        pi3.serialize_compressed(&mut pi3_bytes).unwrap();

        let witness = TxAssertWitness {
            wots_sig: vec![[0u8; 21]; Wots96::TOTAL_DIGIT_LEN as usize],
            pi2: pi2_bytes,
            pi3: pi3_bytes,
        };
        let (r2, r3) = witness.recover_pi2_pi3().unwrap();
        assert_eq!(r2, pi2);
        assert_eq!(r3, pi3);
    }

    #[test]
    fn test_recover_pi2_pi3_invalid_pi2() {
        let mut rng = rand::thread_rng();
        let pi3 = ark_bn254::G1Projective::rand(&mut rng).into_affine();
        let mut pi3_bytes = Vec::new();
        pi3.serialize_compressed(&mut pi3_bytes).unwrap();

        let witness = TxAssertWitness {
            wots_sig: vec![],
            pi2: vec![0u8; 64], // invalid G2 bytes
            pi3: pi3_bytes,
        };
        assert!(witness.recover_pi2_pi3().is_none());
    }

    // ── verify_groth16_proof ──────────────────────────────────────────────────

    #[test]
    fn test_verify_groth16_proof_valid() {
        use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
        use ark_groth16::Groth16;
        use rand::SeedableRng;

        let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(42);
        let a = Fr::from(3u64);
        let b = Fr::from(4u64);

        let circuit = DummyMulCircuit { a: Some(a), b: Some(b) };
        let (pk, vk) = Groth16::<Bn254>::setup(circuit, &mut rng).unwrap();

        let circuit = DummyMulCircuit { a: Some(a), b: Some(b) };
        let proof = Groth16::<Bn254>::prove(&pk, circuit, &mut rng).unwrap();

        let static_pi = a * b;
        let x_d = a * a;

        let msg = pi1_xd_to_wots96_msg(&proof.a, x_d);
        let sk = Wots96::generate_secret_key();
        let mut pi2_bytes = Vec::new();
        proof.b.serialize_compressed(&mut pi2_bytes).unwrap();
        let mut pi3_bytes = Vec::new();
        proof.c.serialize_compressed(&mut pi3_bytes).unwrap();

        let witness = TxAssertWitness {
            wots_sig: Wots96::sign(&sk, &msg).to_vec(),
            pi2: pi2_bytes,
            pi3: pi3_bytes,
        };

        assert!(witness.verify_groth16_proof(&vk, &[static_pi]));
    }

    #[test]
    fn test_verify_groth16_proof_bad_pi2_pi3() {
        use ark_crypto_primitives::snark::CircuitSpecificSetupSNARK;
        use ark_groth16::Groth16;
        use rand::SeedableRng;

        let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(99);
        let a = Fr::from(3u64);
        let b = Fr::from(4u64);
        let circuit = DummyMulCircuit { a: Some(a), b: Some(b) };
        let (_, vk) = Groth16::<Bn254>::setup(circuit, &mut rng).unwrap();

        let x_d = a * a;
        let msg = pi1_xd_to_wots96_msg(&G1Affine::generator(), x_d);
        let sk = Wots96::generate_secret_key();

        // Zero bytes → recover_pi2_pi3 returns None → verify returns false
        let witness = TxAssertWitness {
            wots_sig: Wots96::sign(&sk, &msg).to_vec(),
            pi2: vec![0u8; 64],
            pi3: vec![0u8; 32],
        };
        assert!(!witness.verify_groth16_proof(&vk, &[a * b]));
    }
}
