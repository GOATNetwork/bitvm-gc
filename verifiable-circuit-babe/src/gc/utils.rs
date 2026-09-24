use aes::Aes128;
use aes::cipher::generic_array::GenericArray;
use aes::cipher::{BlockDecrypt, BlockEncrypt, KeyInit};
use ark_bn254::Fq;
use ark_ff::{BigInteger, PrimeField};
use crate::gc::adaptor::Ct;

// These are PUBLICLY KNOWN fixed constants used as AES keys for the adaptor-table PRF.
// Security relies on the correlation-robustness assumption: AES with a fixed public key
// is indistinguishable from a random function when inputs are uniformly random GC labels.
// This is the standard assumption in garbled-circuit literature (half-gates, free-XOR).
//
// WARNING: You MUST replace these constants with independently sampled random values
// before deploying in any production protocol. Using the defaults in production
// breaks the correlation-robustness assumption across independent deployments.
//
// Current values are the first two SHA-256 initial hash constants (H₀, H₁ from
// FIPS 180-4, derived from fractional parts of √2 and √3).
const PRF_KEY_0: [u8; 16] = [0x6a, 0x09, 0xe6, 0x67, 0xf3, 0xbc, 0xc9, 0x08,
                              0xb2, 0xfb, 0x13, 0x6c, 0xe3, 0x7e, 0x94, 0x11];
const PRF_KEY_1: [u8; 16] = [0xbb, 0x67, 0xae, 0x85, 0x84, 0xca, 0xa7, 0x3b,
                              0x9c, 0xa2, 0xfc, 0xe9, 0xd7, 0x8a, 0x58, 0x6a];

/// This is the "random oracle on label", using AES
#[inline(always)]
pub fn prf_fq(label: &[u8; 16]) -> Fq {
    let c0 = Aes128::new(GenericArray::from_slice(&PRF_KEY_0));
    let mut b0 = *GenericArray::from_slice(label);
    c0.encrypt_block(&mut b0);

    let c1 = Aes128::new(GenericArray::from_slice(&PRF_KEY_1));
    let mut b1 = *GenericArray::from_slice(label);
    c1.encrypt_block(&mut b1);

    let mut out = [0u8; 32];
    out[..16].copy_from_slice(&b0);
    out[16..].copy_from_slice(&b1);
    Fq::from_le_bytes_mod_order(&out)
}

fn fq_to_bytes(fq: &Fq) -> [u8; 32] {
    fq.into_bigint().to_bytes_le().try_into().expect("Fq serializes to exactly 32 bytes")
}

fn bytes_to_fq(bytes: &[u8; 32]) -> Fq {
    Fq::from_le_bytes_mod_order(bytes)
}


// --- AES-128 encrypt/decrypt for Fq (32 bytes = 2 blocks) ---
//
// Block 0 uses the key directly.
// Block 1 tweaks the key (XOR last byte with 0x01) to avoid encrypting
// two plaintext blocks under the identical key (standard ECB weakness).
#[inline(always)]
pub fn aes_enc(fq: &Fq, key: &[u8; 16]) -> Ct {
    let plain = fq_to_bytes(fq);

    let mut ct = [0u8; 32];
    let cipher0 = Aes128::new(GenericArray::from_slice(key));
    let mut block0 = *GenericArray::from_slice(&plain[..16]);
    cipher0.encrypt_block(&mut block0);
    ct[..16].copy_from_slice(&block0);

    let mut key1 = *key;
    key1[15] ^= 0x01; // tweak for second block to avoid ECB weakness
    let cipher1 = Aes128::new(GenericArray::from_slice(&key1));
    let mut block1 = *GenericArray::from_slice(&plain[16..]);
    cipher1.encrypt_block(&mut block1);
    ct[16..].copy_from_slice(&block1);

    ct
}

pub fn aes_dec(ct: &Ct, key: &[u8; 16]) -> Fq {
    let cipher0 = Aes128::new(GenericArray::from_slice(key));
    let mut block0 = *GenericArray::from_slice(&ct[..16]);
    cipher0.decrypt_block(&mut block0);

    let mut key1 = *key;
    key1[15] ^= 0x01; // tweak for second block to avoid ECB weakness
    let cipher1 = Aes128::new(GenericArray::from_slice(&key1));
    let mut block1 = *GenericArray::from_slice(&ct[16..]);
    cipher1.decrypt_block(&mut block1);

    let mut plain = [0u8; 32];
    plain[..16].copy_from_slice(&block0);
    plain[16..].copy_from_slice(&block1);

    bytes_to_fq(&plain)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_aes_enc_dec() {
        let key = [0u8; 16];
        let fq = Fq::from(123456789u64);
        let ct = aes_enc(&fq, &key);
        let decrypted = aes_dec(&ct, &key);
        assert_eq!(fq, decrypted, "AES encryption/decryption failed");
    }
}