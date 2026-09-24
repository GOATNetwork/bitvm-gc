/// This is copied from:
/// https://github.com/KSlashh/BitVM/blob/f46dbbee24e5b54cff771b155b45f6f98ea1a2bb/goat/src/wots.rs

use bitcoin::script::read_scriptint;
use bitcoin::Witness;
use bitvm::signatures::utils::bitcoin_representation;
pub use bitvm::signatures::winternitz::{Parameters, VoidConverter};
pub use bitvm::signatures::{CompactWots, WinternitzSecret, Wots};

pub const WOTS96_LOG2_BASE: u32 = 8;
pub const WOTS96_BASE: u32 = 1 << WOTS96_LOG2_BASE;

pub struct Wots96;

impl Wots for Wots96 {
    type Converter = VoidConverter;
    type PublicKey = [[u8; 20]; Self::TOTAL_DIGIT_LEN as usize];
    type Message = [u8; Self::MSG_BYTE_LEN as usize];
    type Signature = [[u8; 21]; Self::TOTAL_DIGIT_LEN as usize];

    const MSG_BYTE_LEN: u32 = 96;
    const PARAMETERS: Parameters =
        Parameters::new_by_bit_length(Self::MSG_BYTE_LEN * 8, WOTS96_LOG2_BASE);

    fn raw_witness_to_signature(witness: &Witness) -> Self::Signature {
        assert_eq!(witness.len(), 2 * Self::TOTAL_DIGIT_LEN as usize);

        let mut digit_signatures = Vec::with_capacity(Self::TOTAL_DIGIT_LEN as usize);
        for i in (0..witness.len()).step_by(2) {
            assert_eq!(
                witness[i].len(),
                20,
                "the digit signature should be constant 20 bytes"
            );
            assert!(
                witness[i + 1].len() <= 2,
                "the base256 digit should fit in minimally encoded script bytes"
            );

            let digit_value = read_scriptint(&witness[i + 1]).unwrap();
            assert!(
                (0..WOTS96_BASE as i64).contains(&digit_value),
                "the digit should be in the valid Wots96 base range"
            );

            let mut digit_signature = [0u8; 21];
            digit_signature[..20].copy_from_slice(&witness[i]);
            digit_signature[20] = digit_value as u8;
            digit_signatures.push(digit_signature);
        }

        Self::Signature::try_from(digit_signatures).unwrap()
    }

    fn signature_to_raw_witness(signature: &Self::Signature) -> Witness {
        let mut witness = Witness::new();
        for digit_signature in signature.as_ref() {
            witness.push(&digit_signature[..20]);
            witness.push(bitcoin_representation(i32::from(digit_signature[20])));
        }
        witness
    }

    fn signature_to_message(signature: &Self::Signature) -> Self::Message {
        if WOTS96_LOG2_BASE == 8 {
            let bytes = signature
                .as_ref()
                .iter()
                .map(|digit_sig| digit_sig[20])
                .take(Self::MSG_BYTE_LEN as usize)
                .rev()
                .collect::<Vec<_>>();
            return Self::Message::try_from(bytes).unwrap();
        }

        let digits = signature
            .as_ref()
            .iter()
            .map(|digit_sig| digit_sig[20])
            .take((Self::MSG_BYTE_LEN * 8).div_ceil(WOTS96_LOG2_BASE) as usize)
            .rev()
            .collect::<Vec<_>>();

        let mut bytes = Vec::with_capacity(Self::MSG_BYTE_LEN as usize);
        let mut byte = 0u8;
        let mut used_bits = 0u32;
        for digit in digits {
            byte |= digit << used_bits;
            used_bits += WOTS96_LOG2_BASE;
            if used_bits >= 8 {
                bytes.push(byte);
                byte = digit >> (8 - (used_bits - WOTS96_LOG2_BASE));
                used_bits -= 8;
            }
        }
        bytes.truncate(Self::MSG_BYTE_LEN as usize);

        Self::Message::try_from(bytes).unwrap()
    }
}

impl CompactWots for Wots96 {
    type CompactSignature = [[u8; 20]; Self::TOTAL_DIGIT_LEN as usize];
}

pub type Wots96Secret = WinternitzSecret;
pub type Wots96PublicKey = <Wots96 as Wots>::PublicKey;
pub type Wots96Sig = <Wots96 as Wots>::Signature;

/// Verify a Wots96 signature against a public key and message.
///
/// Mirrors `lamport_verify`: for each digit position i, hash `sig[i][..20]`
/// exactly `(max_digit - d_i)` more times and compare against `pk[i]`.
/// Digits are derived from `msg` directly (not trusted from sig[i][20]).
pub fn wots96_verify(pk: &Wots96PublicKey, msg: &[u8; 96], sig: &Wots96Sig) -> bool {
    use bitcoin::hashes::{hash160, Hash};

    let base = WOTS96_BASE as usize;                          // 256
    let max_digit = base - 1;                                  // 255
    let msg_digit_len = Wots96::MSG_BYTE_LEN as usize;        // 96 (one byte = one digit)
    let total_digit_len = Wots96::TOTAL_DIGIT_LEN as usize;   // 98
    let chk_digit_len = total_digit_len - msg_digit_len;       // 2

    // Step 1: message digits — each byte is one digit, reversed (matches message_to_digits internals)
    let mut digits: Vec<usize> = msg.iter().rev().map(|&b| b as usize).collect();

    // Step 2: checksum = max_digit * msg_digit_len - sum(message_digits)
    let checksum: usize = max_digit * msg_digit_len - digits.iter().sum::<usize>();

    // Step 3: encode checksum as big-endian base-256 digits and append
    let mut chk = checksum;
    let mut chk_digits = vec![0usize; chk_digit_len];
    for d in chk_digits.iter_mut().rev() {
        *d = chk % base;
        chk /= base;
    }
    digits.extend(chk_digits);

    // Step 4: for each digit position i, verify the hash chain against pk[i]
    for i in 0..total_digit_len {
        let d_i = digits[i];
        let mut h = hash160::Hash::from_byte_array(sig[i][..20].try_into().unwrap());
        for _ in 0..(max_digit - d_i) {
            h = hash160::Hash::hash(h.as_byte_array());
        }
        if h.as_byte_array() != &pk[i] {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wots_witness_and_message_roundtrip() {
        let sk = Wots96::generate_secret_key();
        let msg = [7u8; 96];
        let sig = Wots96::sign(&sk, &msg);

        assert_eq!(Wots96::signature_to_message(&sig), msg);

        let witness = Wots96::signature_to_raw_witness(&sig);
        let recovered = Wots96::raw_witness_to_signature(&witness);
        assert_eq!(recovered, sig);
    }

    #[test]
    #[should_panic]
    fn test_raw_witness_to_signature_rejects_wrong_length() {
        Wots96::raw_witness_to_signature(&Witness::new());
    }
}