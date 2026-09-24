//! Binary Circuit Representation of Blake3 Hasher
//! Implementation directly referenced from official BLAKE3 reference implementation rust code,
//! including its tree mode, so inputs of any length are supported.
//!
//! Wire layout: a byte is eight wires, bit 0 first (`U8`); a word is 32 wires, bit 0 first (`U32`).
//!
//! Cost: 10,281 AND gates per compression (one per adder bit below the top, see
//! `wrapping_add_u32`); a 64-byte input is one compression, a 256-byte input four.

use core::cmp::min;

use super::builder::CircuitTrait;

const OUT_LEN: usize = 32;
const BLOCK_LEN: usize = 64;
const CHUNK_LEN: usize = 1024;

const CHUNK_START: u32 = 1 << 0;
const CHUNK_END: u32 = 1 << 1;
const PARENT: u32 = 1 << 2;
const ROOT: u32 = 1 << 3;

pub type U32 = [usize; 32];
pub type U8 = [usize; 8];

fn const_u32_to_bits_le<T: CircuitTrait>(bld: &mut T, n: u32) -> U32 {
    let vs: Vec<bool> = (0..32).map(|i| (n >> i) & 1 != 0).collect();
    let vs: Vec<usize> = vs.iter().map(|v| bool_const_to_wire_label(bld, *v)).collect();
    vs.try_into().unwrap()
}

fn bool_const_to_wire_label<T: CircuitTrait>(bld: &mut T, v: bool) -> usize {
    if !v { bld.zero() } else { bld.one() }
}

fn get_iv<T: CircuitTrait>(bld: &mut T) -> [U32; 8] {
    let iv2: [U32; 8] = [
        const_u32_to_bits_le(bld, 0x6A09E667),
        const_u32_to_bits_le(bld, 0xBB67AE85),
        const_u32_to_bits_le(bld, 0x3C6EF372),
        const_u32_to_bits_le(bld, 0xA54FF53A),
        const_u32_to_bits_le(bld, 0x510E527F),
        const_u32_to_bits_le(bld, 0x9B05688C),
        const_u32_to_bits_le(bld, 0x1F83D9AB),
        const_u32_to_bits_le(bld, 0x5BE0CD19),
    ];
    iv2
}

const MSG_PERMUTATION: [u8; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

/// `a + b mod 2^32` at one AND gate per bit.
///
/// The original computed the carry as `(a·b) ⊕ (p·c)`, two ANDs per bit. Under
/// free-XOR the majority function is one: `maj(a, b, c) = c ⊕ ((a⊕c)·(b⊕c))`.
/// The carry out of bit 31 is discarded, so it is not computed.
fn wrapping_add_u32<T: CircuitTrait>(bld: &mut T, a: U32, b: U32) -> U32 {
    let mut result = [0; 32];
    let mut carry = bld.zero();

    for i in 0..32 {
        let p = bld.xor_wire(a[i], b[i]);
        result[i] = bld.xor_wire(p, carry);
        if i < 31 {
            let ac = bld.xor_wire(a[i], carry);
            let bc = bld.xor_wire(b[i], carry);
            let t = bld.and_wire(ac, bc);
            carry = bld.xor_wire(carry, t);
        }
    }

    result
}

fn xor_u32<T: CircuitTrait>(bld: &mut T, a: U32, b: U32) -> U32 {
    let c: Vec<usize> = (0..32).map(|i| bld.xor_wire(a[i], b[i])).collect();
    c.try_into().unwrap()
}

fn and_u32<T: CircuitTrait>(bld: &mut T, a: U32, b: U32) -> U32 {
    let c: Vec<usize> = (0..32).map(|i| bld.and_wire(a[i], b[i])).collect();
    c.try_into().unwrap()
}

fn or_u32<T: CircuitTrait>(bld: &mut T, x: U32, y: U32) -> U32 {
    let xpy = xor_u32(bld, x, y);
    let xmy = and_u32(bld, x, y);

    xor_u32(bld, xpy, xmy)
}

fn rotate_right_u32(value: U32, n: u32) -> U32 {
    let mut result = [0; 32];
    let shift = (n % 32) as usize;

    for (i, result_i) in result.iter_mut().enumerate() {
        // Compute the new position using modular arithmetic
        let from_index = (i + shift) % 32;
        *result_i = value[from_index];
    }

    result
}

// The mixing function, G, which mixes either a column or a diagonal.
#[allow(clippy::too_many_arguments)]
fn g<T: CircuitTrait>(
    bld: &mut T,
    state: &mut [U32; 16],
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    mx: U32,
    my: U32,
) {
    let tmp0 = wrapping_add_u32(bld, state[a], state[b]);
    state[a] = wrapping_add_u32(bld, tmp0, mx);
    state[d] = rotate_right_u32(xor_u32(bld, state[d], state[a]), 16);
    state[c] = wrapping_add_u32(bld, state[c], state[d]);
    state[b] = rotate_right_u32(xor_u32(bld, state[b], state[c]), 12);

    let tmp0 = wrapping_add_u32(bld, state[a], state[b]);
    state[a] = wrapping_add_u32(bld, tmp0, my);
    state[d] = rotate_right_u32(xor_u32(bld, state[d], state[a]), 8);
    state[c] = wrapping_add_u32(bld, state[c], state[d]);
    state[b] = rotate_right_u32(xor_u32(bld, state[b], state[c]), 7);
}

fn round<T: CircuitTrait>(bld: &mut T, state: &mut [U32; 16], m: &[U32; 16]) {
    // Mix the columns.
    g(bld, state, 0, 4, 8, 12, m[0], m[1]);
    g(bld, state, 1, 5, 9, 13, m[2], m[3]);
    g(bld, state, 2, 6, 10, 14, m[4], m[5]);
    g(bld, state, 3, 7, 11, 15, m[6], m[7]);
    // Mix the diagonals.
    g(bld, state, 0, 5, 10, 15, m[8], m[9]);
    g(bld, state, 1, 6, 11, 12, m[10], m[11]);
    g(bld, state, 2, 7, 8, 13, m[12], m[13]);
    g(bld, state, 3, 4, 9, 14, m[14], m[15]);
}

fn permute(m: &mut [U32; 16]) {
    let mut permuted = [[0; 32]; 16];
    for i in 0..16 {
        permuted[i] = m[MSG_PERMUTATION[i] as usize];
    }
    *m = permuted;
}

fn compress<T: CircuitTrait>(
    bld: &mut T,
    chaining_value: &[U32; 8],
    block_words: &[U32; 16],
    counter: u64,
    block_len: U32,
    flags: U32,
) -> [U32; 16] {
    let counter_low = const_u32_to_bits_le(bld, counter as u32);
    let counter_high = const_u32_to_bits_le(bld, (counter >> 32) as u32);
    #[rustfmt::skip]
    let iv: [U32; 8] = get_iv(bld);
    let mut state = [
        chaining_value[0],
        chaining_value[1],
        chaining_value[2],
        chaining_value[3],
        chaining_value[4],
        chaining_value[5],
        chaining_value[6],
        chaining_value[7],
        iv[0],
        iv[1],
        iv[2],
        iv[3],
        counter_low,
        counter_high,
        block_len,
        flags,
    ];

    let mut block = *block_words;

    round(bld, &mut state, &block); // round 1
    permute(&mut block);
    round(bld, &mut state, &block); // round 2
    permute(&mut block);
    round(bld, &mut state, &block); // round 3
    permute(&mut block);
    round(bld, &mut state, &block); // round 4
    permute(&mut block);
    round(bld, &mut state, &block); // round 5
    permute(&mut block);
    round(bld, &mut state, &block); // round 6
    permute(&mut block);
    round(bld, &mut state, &block); // round 7

    for i in 0..8 {
        state[i] = xor_u32(bld, state[i], state[i + 8]);
        state[i + 8] = xor_u32(bld, state[i + 8], chaining_value[i]);
    }
    state
}

fn first_8_words(compression_output: [U32; 16]) -> [U32; 8] {
    compression_output[0..8].try_into().unwrap()
}

fn words_from_little_endian_bytes(bytes: &[U8], words: &mut [U32]) {
    debug_assert_eq!(bytes.len(), 4 * words.len());
    for (four_bytes, word) in bytes.chunks_exact(4).zip(words) {
        let app_four_bytes: U32 = four_bytes.concat().try_into().unwrap();
        *word = app_four_bytes;
    }
}

struct Output {
    input_chaining_value: [U32; 8],
    block_words: [U32; 16],
    /// The chunk's counter; 0 for a parent node. The root's output blocks
    /// are numbered instead.
    counter: u64,
    block_len: U32,
    flags: U32,
}

impl Output {
    /// The chaining value: the first eight words of the compression, for a
    /// chunk or parent node that is not the root.
    fn chaining_value<T: CircuitTrait>(&self, bld: &mut T) -> [U32; 8] {
        first_8_words(compress(bld, &self.input_chaining_value, &self.block_words, self.counter, self.block_len, self.flags))
    }

    fn root_output_bytes<T: CircuitTrait>(&self, bld: &mut T, out_slice: &mut [U8]) {
        let root = const_u32_to_bits_le(bld, ROOT);
        for (output_block_counter, out_block) in out_slice.chunks_mut(2 * OUT_LEN).enumerate() {
            let flags = or_u32(bld, self.flags, root);
            let words = compress(
                bld,
                &self.input_chaining_value,
                &self.block_words,
                output_block_counter as u64,
                self.block_len,
                flags,
            );
            for (word_bits, out_word_bits) in words.iter().zip(out_block.chunks_mut(4)) {
                for (i, byte_bits) in out_word_bits.iter_mut().enumerate() {
                    let arr: U8 = word_bits[8 * i..(i + 1) * 8].try_into().unwrap();
                    *byte_bits = arr;
                }
            }
        }
    }
}

struct ChunkState {
    chaining_value: [U32; 8],
    chunk_counter: u64,
    block: [U8; BLOCK_LEN],
    block_len: u8,
    blocks_compressed: u8,
    flags: U32,
}

impl ChunkState {
    fn new<T: CircuitTrait>(
        bld: &mut T,
        key_words: [U32; 8],
        chunk_counter: u64,
        flags: U32,
    ) -> Self {
        let zero_gate = bld.zero();
        Self {
            chaining_value: key_words,
            chunk_counter,
            block: [[zero_gate; 8]; BLOCK_LEN],
            block_len: 0,
            blocks_compressed: 0,
            flags,
        }
    }

    fn len(&self) -> usize {
        BLOCK_LEN * self.blocks_compressed as usize + self.block_len as usize
    }

    fn start_flag<T: CircuitTrait>(&self, bld: &mut T) -> U32 {
        let r = if self.blocks_compressed == 0 { CHUNK_START } else { 0 };
        const_u32_to_bits_le(bld, r)
    }

    fn update<T: CircuitTrait>(&mut self, bld: &mut T, mut input: &[U8]) {
        let zero_gate = bld.zero();
        let block_len = const_u32_to_bits_le(bld, BLOCK_LEN as u32);
        while !input.is_empty() {
            // If the block buffer is full, compress it and clear it. More
            // input is coming, so this compression is not CHUNK_END.
            if self.block_len as usize == BLOCK_LEN {
                let mut block_words = [[zero_gate; 32]; 16];
                words_from_little_endian_bytes(&self.block, &mut block_words);
                let start_flag = self.start_flag(bld);
                let flags = or_u32(bld, self.flags, start_flag);
                let cmp = compress(
                    bld,
                    &self.chaining_value,
                    &block_words,
                    self.chunk_counter,
                    block_len,
                    flags,
                );
                self.chaining_value = first_8_words(cmp);
                self.blocks_compressed += 1;
                self.block = [[zero_gate; 8]; BLOCK_LEN];
                self.block_len = 0;
            }

            // Copy input bytes into the block buffer.
            let want = BLOCK_LEN - self.block_len as usize;
            let take = min(want, input.len());
            self.block[self.block_len as usize..][..take].copy_from_slice(&input[..take]);
            self.block_len += take as u8;
            input = &input[take..];
        }
    }

    fn output<T: CircuitTrait>(&self, bld: &mut T) -> Output {
        let zero_gate = bld.zero();
        let mut block_words = [[zero_gate; 32]; 16];
        words_from_little_endian_bytes(&self.block, &mut block_words);
        let start_flag = self.start_flag(bld);
        let flags = or_u32(bld, self.flags, start_flag);
        let chunk_end = const_u32_to_bits_le(bld, CHUNK_END);
        let flags = or_u32(bld, flags, chunk_end);

        Output {
            input_chaining_value: self.chaining_value,
            block_words,
            counter: self.chunk_counter,
            block_len: const_u32_to_bits_le(bld, self.block_len as u32),
            flags,
        }
    }
}

/// A parent node: the two children's chaining values as one block.
fn parent_output<T: CircuitTrait>(
    bld: &mut T,
    left_child_cv: [U32; 8],
    right_child_cv: [U32; 8],
    key_words: [U32; 8],
    flags: U32,
) -> Output {
    let zero_gate = bld.zero();
    let mut block_words = [[zero_gate; 32]; 16];
    block_words[..8].copy_from_slice(&left_child_cv);
    block_words[8..].copy_from_slice(&right_child_cv);
    let parent = const_u32_to_bits_le(bld, PARENT);
    Output {
        input_chaining_value: key_words,
        block_words,
        counter: 0,
        block_len: const_u32_to_bits_le(bld, BLOCK_LEN as u32),
        flags: or_u32(bld, flags, parent),
    }
}

fn parent_cv<T: CircuitTrait>(
    bld: &mut T,
    left_child_cv: [U32; 8],
    right_child_cv: [U32; 8],
    key_words: [U32; 8],
    flags: U32,
) -> [U32; 8] {
    parent_output(bld, left_child_cv, right_child_cv, key_words, flags).chaining_value(bld)
}

/// An incremental hasher that can accept any number of writes, in the tree
/// mode of the reference implementation: a stack of subtree chaining values,
/// merged as chunks complete and at the end.
pub struct Hasher {
    chunk_state: ChunkState,
    key_words: [U32; 8],
    cv_stack: Vec<[U32; 8]>,
    flags: U32,
}

impl Hasher {
    fn new_internal<T: CircuitTrait>(bld: &mut T, key_words: [U32; 8], flags: U32) -> Self {
        Self { chunk_state: ChunkState::new(bld, key_words, 0, flags), key_words, cv_stack: Vec::new(), flags }
    }

    /// A completed chunk's chaining value joins the stack, merging with every
    /// completed subtree of its size (the trailing zeros of the chunk count).
    fn add_chunk_chaining_value<T: CircuitTrait>(&mut self, bld: &mut T, mut new_cv: [U32; 8], mut total_chunks: u64) {
        while total_chunks & 1 == 0 {
            let left = self.cv_stack.pop().expect("a subtree to merge with");
            new_cv = parent_cv(bld, left, new_cv, self.key_words, self.flags);
            total_chunks >>= 1;
        }
        self.cv_stack.push(new_cv);
    }

    /// Construct a new `Hasher` for the regular hash function.
    pub fn new<T: CircuitTrait>(bld: &mut T) -> Self {
        let zero_gate = bld.zero();
        let iv = get_iv(bld);
        let zero = [zero_gate; 32];
        Self::new_internal(bld, iv, zero)
    }

    /// Add input to the hash state. This can be called any number of times.
    pub fn update<T: CircuitTrait>(&mut self, bld: &mut T, mut input: &[U8]) {
        while !input.is_empty() {
            // A full chunk with more input coming is complete: its chaining
            // value goes to the tree, and a new chunk starts.
            if self.chunk_state.len() == CHUNK_LEN {
                let chunk_cv = self.chunk_state.output(bld).chaining_value(bld);
                let total_chunks = self.chunk_state.chunk_counter + 1;
                self.add_chunk_chaining_value(bld, chunk_cv, total_chunks);
                self.chunk_state = ChunkState::new(bld, self.key_words, total_chunks, self.flags);
            }

            // Compress input bytes into the current chunk state.
            let want = CHUNK_LEN - self.chunk_state.len();
            let take = min(want, input.len());
            self.chunk_state.update(bld, &input[..take]);
            input = &input[take..];
        }
    }

    /// Finalize the hash and write any number of output bytes.
    pub fn finalize<T: CircuitTrait>(&self, bld: &mut T, out_slice: &mut [U8]) {
        // The last chunk, then every subtree on the stack, right to left,
        // becomes the right child of a parent; the topmost parent is the root.
        let mut output = self.chunk_state.output(bld);
        let mut parent_nodes_remaining = self.cv_stack.len();
        while parent_nodes_remaining > 0 {
            parent_nodes_remaining -= 1;
            let right = output.chaining_value(bld);
            output = parent_output(bld, self.cv_stack[parent_nodes_remaining], right, self.key_words, self.flags);
        }
        output.root_output_bytes(bld, out_slice);
    }
}

pub fn hash<T: CircuitTrait>(bld: &mut T, input_bits: Vec<U8>) -> [U8; 32] {
    let mut hasher = Hasher::new(bld);
    hasher.update(bld, &input_bits);

    let mut hash = [[0; 8]; 32];
    hasher.finalize(bld, &mut hash);
    hash
}

/// `blake3(input)` for an input of `n` bytes: `n` fresh byte inputs in, 32 bytes out.
pub fn hash_bytes<T: CircuitTrait>(bld: &mut T, input: &[U8]) -> [U8; 32] {
    let mut hasher = Hasher::new(bld);
    hasher.update(bld, input);
    let mut out = [[0usize; 8]; 32];
    hasher.finalize(bld, &mut out);
    out
}

#[cfg(test)]
mod test {
    use super::super::{
        blake3_ckt::{Hasher, U8, hash_bytes},
        builder::{CircuitAdapter, CircuitTrait},
    };

    use blake3::Hasher as RefHasher;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    fn str_to_bits_le(ns: &[u8]) -> Vec<[bool; 8]> {
        let mut vs: Vec<[bool; 8]> = Vec::new();
        for n in ns {
            let v: Vec<bool> = (0..8).map(|i| (n >> i) & 1 != 0).collect();
            let v: [bool; 8] = v.try_into().unwrap();
            vs.push(v);
        }
        vs
    }

    fn read_bytes(wires: &[bool], out: &[U8]) -> Vec<u8> {
        out.iter().map(|w| (0..8).fold(0u8, |acc, i| acc | (u8::from(wires[w[i]]) << i))).collect()
    }

    #[test]
    fn test_emit_blake3_hash() {
        // Circuit verified for different inputs of known length

        let mut bld = CircuitAdapter::default();

        let input1 = b"fbcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd"; // 64 byte input
        let input2 = b"ef02ef02ef03ef02ef02ef02ef04ef02ef02ef02ef02ef0aef02ef02ef02ef02";
        assert_eq!(input1.len(), input2.len(), "both reference inputs should be of same size");

        // Compile blake3 circuit for fixed input length
        let input_labels: Vec<U8> = (0..input1.len()).map(|_| bld.fresh()).collect();
        let mut hasher = Hasher::new(&mut bld);
        hasher.update(&mut bld, &input_labels);
        let mut out_slice = [[0; 8]; 32];
        hasher.finalize(&mut bld, &mut out_slice);

        let stats = bld.gate_counts();
        println!("{stats}");
        // One compression, one AND per adder bit below the top.
        assert_eq!(stats.direct_and, 10_281);

        // Evaluate the same circuit on both inputs against the blake3 crate.
        for input in [input1, input2] {
            let mut hasher = RefHasher::new();
            hasher.update(input);
            let wires = bld.eval_gates(&str_to_bits_le(input).concat());
            assert_eq!(read_bytes(&wires, &out_slice), hasher.finalize().as_bytes().to_vec());
        }
    }

    /// Against the blake3 crate at one-chunk lengths and in tree mode: two
    /// chunks, four (a two-level tree), five (an unbalanced one).
    #[test]
    fn test_blake3_tree_mode() {
        let mut rng = ChaCha20Rng::seed_from_u64(3);
        for n in [0usize, 1, 64, 65, 256, 1024, 1025, 1072, 2048, 4096, 4097] {
            let msg: Vec<u8> = (0..n).map(|_| rng.r#gen()).collect();
            let mut bld = CircuitAdapter::default();
            let input: Vec<U8> = (0..n).map(|_| bld.fresh::<8>()).collect();
            let out = hash_bytes(&mut bld, &input);
            let wires = bld.eval_gates(&str_to_bits_le(&msg).concat());
            assert_eq!(read_bytes(&wires, &out), blake3::hash(&msg).as_bytes().to_vec(), "{n} bytes");
            println!("blake3 of {n} bytes: {} AND", bld.gate_counts().direct_and);
        }
    }
}
