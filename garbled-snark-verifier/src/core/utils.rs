use std::{cell::RefCell, rc::Rc, slice, sync::atomic::AtomicU32};

use serde::{Deserialize, Serialize};

use crate::{
    bag::{Circuit, Gate, S, Wire},
    core::gate::{GateType, gate_garbled},
};

use std::sync::atomic::Ordering;

pub const SUB_CIRCUIT_MAX_GATES: usize = 2_000_000;
pub const SUB_INPUT_GATES_PART_SIZE: usize = 200_000;
pub const SUB_INPUT_GATES_PARTS: usize = 10;
pub const LABEL_SIZE: usize = 16;
/// Default global DELTA for non-C&C garbling. C&C uses per-instance delta passed explicitly.
pub static NON_CAC_DELTA: S = S::one();
/// Default global salt for non-C&C garbling (`_aes` backend only). C&C uses a fresh
/// per-instance random salt passed explicitly.
pub static NON_CAC_SALT: S = S([0xA5u8; LABEL_SIZE]);

#[cfg(feature = "_aes")]
static AES128_CIPHER: std::sync::OnceLock<aes::Aes128> = std::sync::OnceLock::new();

/// Fixed-key AES-128 cipher, expanded once and reused.
#[cfg(feature = "_aes")]
fn aes128_static_cipher() -> &'static aes::Aes128 {
    use aes::cipher::KeyInit;
    AES128_CIPHER.get_or_init(|| aes::Aes128::new(&[0x42; 16].into()))
}

// u32 is not enough for current gates scale.
pub static GID: AtomicU32 = AtomicU32::new(0);

#[inline(always)]
pub fn inc_gid() -> u32 {
    GID.fetch_add(1, Ordering::SeqCst) + 1
}

#[inline(always)]
pub fn reset_gid() {
    GID.store(0, Ordering::SeqCst);
}

pub fn bit_to_usize(bit: bool) -> usize {
    if bit { 1 } else { 0 }
}

#[allow(unused_variables)]
pub fn hash(input: &[u8], salt: Option<[u8; LABEL_SIZE]>) -> [u8; LABEL_SIZE] {
    #[allow(unused_assignments, unused_mut)]
    let mut output = [0u8; 32];

    #[cfg(feature = "_blake3")]
    {
        use blake3::hash;
        output = *hash(input).as_bytes();
    }

    #[cfg(feature = "_sha2")]
    {
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        hasher.update(input);
        let result = hasher.finalize();
        output.copy_from_slice(&result[..32]);
    }

    #[cfg(feature = "_poseidon2")]
    {
        use poseidon2::poseidon2;
        output = poseidon2(input);
    }
    #[cfg(feature = "_aes")]
    {
        use aes::cipher::{BlockEncrypt, generic_array::GenericArray};

        // Guo-Katz-Wang-Yu (ePrint 2019/074, Thm 5): H_S(x,i) = pi(sigma(S^x)) ^ sigma(S^x),
        // sigma(x_L||x_R) = (x_L^x_R)||x_L. `input` is `label || tweak_bytes`; tweak is
        // zero-extended to LABEL_SIZE since only `hash_ext`'s 20-byte shape is live today.
        // This follows the implementation:
        // https://github.com/BitVM/garbled-snark-verifier/blob/52b49127dc426f0c88ce7fc418116e67173c2f22/src/hashers/mod.rs#L124
        assert!(input.len() >= LABEL_SIZE, "_aes hash requires at least a 16-byte label");
        let salt = salt.expect("_aes hash requires an explicit random salt");
        let mut x0 = [0u8; LABEL_SIZE];
        for i in 0..LABEL_SIZE {
            let tweak_byte = input.get(LABEL_SIZE + i).copied().unwrap_or(0);
            x0[i] = input[i] ^ tweak_byte ^ salt[i];
        }
        let mut p = [0u8; LABEL_SIZE];
        for i in 0..8 {
            p[i] = x0[i] ^ x0[8 + i];
        }
        p[8..16].copy_from_slice(&x0[0..8]);

        let cipher = aes128_static_cipher();
        let mut block = GenericArray::clone_from_slice(&p);
        cipher.encrypt_block(&mut block);

        for i in 0..LABEL_SIZE {
            output[i] = block[i] ^ p[i];
        }
    }
    unsafe { *(output.as_ptr() as *const [u8; LABEL_SIZE]) }
}

#[repr(C)]
#[derive(Default, Debug, Clone, Copy, Serialize, Deserialize)]
pub struct SerializableGate {
    pub gate_type: u8,
    pub wire_a_id: u32,
    pub wire_b_id: u32,
    pub wire_c_id: u32,
    pub gid: u32,
}

#[repr(C)]
#[derive(Clone, Debug)]
pub struct SerializableSubCircuitGates<const N: usize> {
    pub gates: [SerializableGate; N],
}

pub fn serialize_to_bytes<const N: usize>(s: &SerializableSubCircuitGates<N>) -> Vec<u8> {
    unsafe {
        let ptr = s as *const SerializableSubCircuitGates<N> as *const u8;
        let bytes = slice::from_raw_parts(ptr, size_of::<SerializableSubCircuitGates<N>>());
        bytes.to_vec()
    }
}

pub fn deserialize_from_bytes<const N: usize>(buf: &[u8]) -> SerializableSubCircuitGates<N> {
    assert!(buf.len() >= std::mem::size_of::<SerializableSubCircuitGates<N>>());
    unsafe {
        let ptr = buf.as_ptr() as *const SerializableSubCircuitGates<N>;
        ptr.read_unaligned()
    }
}


#[repr(C)]
#[derive(Default, Clone, Debug, Serialize, Deserialize)]
pub struct SerializableWire {
    pub label: S,
    pub value: Option<bool>,
}

#[repr(C)]
#[derive(Default, Clone, Debug, Serialize, Deserialize)]
pub struct SerializableSubWires {
    pub labels: Vec<S>,
    pub value: Vec<Option<bool>>,
}

impl SerializableSubWires {
    pub fn from_serialzable_wires(wires: &[SerializableWire]) -> Self {
        let mut labels = Vec::with_capacity(wires.len());
        let mut value = Vec::with_capacity(wires.len());
        for wire in wires {
            labels.push(wire.label);
            value.push(wire.value);
        }
        SerializableSubWires { labels, value }
    }
}

pub fn check_guest(
    sub_gates_parts: &[Vec<u8>; SUB_INPUT_GATES_PARTS],
    sub_wires: &[u8],
    sub_ciphertexts: &[u8],
) -> Vec<u8>  {
    check_guest_with_delta(sub_gates_parts, sub_wires, sub_ciphertexts, NON_CAC_DELTA, Some(NON_CAC_SALT))
}

pub fn check_guest_with_delta(
    sub_gates_parts: &[Vec<u8>; SUB_INPUT_GATES_PARTS],
    sub_wires: &[u8],
    sub_ciphertexts: &[u8],
    delta: S,
    salt: Option<S>,
) -> Vec<u8>  {
    // read sub_ciphertexts:
    let mut c_start = 0;
    let num_ciphertexts = u64::from_le_bytes(sub_ciphertexts[c_start..c_start + 8].try_into().unwrap());
    c_start += 8;

    // create input for ciphertext check syscall
    let input_size = 16 + num_ciphertexts * 68;
    let mut input = vec![0u8; input_size as usize];
    let mut offset = 0;
    let mut index = 0;
    input[offset..offset + LABEL_SIZE].copy_from_slice(&delta.0);
    offset += LABEL_SIZE;
    for part in 0..SUB_INPUT_GATES_PARTS {
        let sub_gates: SerializableSubCircuitGates<SUB_INPUT_GATES_PART_SIZE> = deserialize_from_bytes(&sub_gates_parts[part]);
        for i in 0..sub_gates.gates.len() {
            if sub_gates.gates[i].gate_type < 8 { // and | or gate
                let gate = &sub_gates.gates[i];
                let base = 8usize;
                let start_a0 = base + (gate.wire_a_id as usize) * LABEL_SIZE;
                let start_b0 = base + (gate.wire_b_id as usize) * LABEL_SIZE;

                let a0 = S::from_slice(&sub_wires[start_a0..start_a0 + LABEL_SIZE]);
                let a1 = a0 ^ delta;

                let h0 = a0.hash_ext(gate.gid, salt);
                let h1 = a1.hash_ext(gate.gid, salt);

                // align memory
                input[offset..offset + 4].copy_from_slice(&(sub_gates.gates[i].gate_type as u32).to_le_bytes().to_vec());
                input[offset + 4..offset + 20].copy_from_slice(&h0.0);
                input[offset + 20..offset + 36].copy_from_slice(&h1.0);
                input[offset + 36..offset + 52].copy_from_slice(&sub_wires[start_b0..start_b0 + LABEL_SIZE]);
                input[offset + 52..offset + 68].copy_from_slice(&sub_ciphertexts[c_start..c_start + LABEL_SIZE]);
                index += 1;
                c_start += LABEL_SIZE;
                offset += 68;
            }
        }
    }
    assert_eq!(index, num_ciphertexts);
    input
}

