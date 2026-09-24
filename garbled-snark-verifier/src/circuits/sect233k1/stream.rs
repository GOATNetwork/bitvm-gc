//! A circuit backend that garbles and evaluates each gate as it is emitted.
//!
//! `CircuitAdapter` keeps every gate in memory and garbles afterwards, which
//! caps the circuit at what fits: ~10^8 gates on a small machine. Nothing in
//! garbling needs the gate list -- a gate's ciphertext depends only on its
//! input wires' labels -- so this backend implements [`CircuitTrait`] by
//! processing each gate on arrival and keeping, per *live* wire, one 16-byte
//! label and one bit. The circuit is built once and is garbled, evaluated and
//! checked by the time the builder returns; no gate is stored.
//!
//! The evaluation is the garbler's own check: for each non-free gate the
//! evaluator's formula is run on the input labels of the wires' values and
//! must reproduce the output label of the output's value. That is the
//! correctness of the garbling, gate by gate, on the proof it is built with.
//!
//! [`ValuedBuilder`] is the one extension: an input wire's value is handed to
//! the backend as the wire is allocated, so that no gate list or second pass
//! is needed to evaluate. `CircuitAdapter` implements it by ignoring the value
//! (it evaluates from a witness afterwards).
//!
//! The gate folding is `CircuitAdapter`'s, rule for rule (`x ⊕ x = 0`,
//! `x ⊕ 0 = x`, `x ∧ x = x`, `x ∧ 0 = 0`, `x ∧ 1 = x`, `x ∨ x = x`,
//! `x ∨ 1 = 1`, `x ∨ 0 = x`), so that the two backends emit the same circuit
//! and the same counts.
//!
//! **Live wires only.** A 2^18 verifier has ~10^9 wires, 17 GB of labels if
//! every wire keeps its own; but at any moment only the wires still to be
//! read are needed. [`Plan`] is a first pass of the same builder that records
//! each wire's number of uses (one byte per wire; the build is deterministic,
//! so the k-th wire of the second pass is the k-th of the first). The garbling
//! pass then hands out *slots*: a wire's slot is released after its last use
//! and taken by a later wire. Wire ids are slots, which `CircuitTrait` permits
//! (nothing asks that ids be increasing); the two constants keep slots 0 and
//! 1 forever, and a wire used 255 or more times is never released.
//!
//! **A secret random `Δ`.** Each `Streaming` draws its own `Δ` (and label
//! seed): with the fixed public `NON_CAC_DELTA` every label yields its
//! complement, so the true label of the output wire would be free to compute.
//! Gates are garbled with `gate_garbled_with_delta` and checked with
//! `gate_evaluate`, with no salt: under `_blake3`, `H(l) = Blake3(l ‖ gid)`,
//! `gid` counting the non-free gates.
//!
//! Labels: input wires get `Blake3(seed ‖ k)` under a random 32-byte seed,
//! with `k` the wire's creation index; every other wire's label is what its
//! gate yields. Per-slot storage is in fixed chunks, since a `Vec` of 10^8
//! labels doubles into twice its size when it grows.

use super::builder::{
    CircuitAdapter, CircuitTrait, CustomGateParams, CustomGateType, GateCounts, GateOperation, Template,
};
use crate::circuits::bn254::utils::random_seed;
use crate::core::gate::{GateType, gate_evaluate, gate_garbled_with_delta};
use crate::core::s::S;

/// A builder that learns each input wire's value as the wire is allocated.
pub trait ValuedBuilder: CircuitTrait {
    fn set_input(&mut self, wire: usize, value: bool);
}

impl ValuedBuilder for CircuitAdapter {
    fn set_input(&mut self, _wire: usize, _value: bool) {}
}

/// A growable array that never moves what it holds: fixed-size chunks.
pub struct Chunked<T> {
    chunks: Vec<Vec<T>>,
    len: usize,
}

const CHUNK_BITS: usize = 22;
const CHUNK: usize = 1 << CHUNK_BITS;

impl<T: Copy> Chunked<T> {
    fn new() -> Self {
        Self { chunks: Vec::new(), len: 0 }
    }

    fn push(&mut self, x: T) {
        if self.len % CHUNK == 0 {
            self.chunks.push(Vec::with_capacity(CHUNK));
        }
        self.chunks.last_mut().expect("a chunk was just ensured").push(x);
        self.len += 1;
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T: Copy> core::ops::Index<usize> for Chunked<T> {
    type Output = T;
    fn index(&self, i: usize) -> &T {
        &self.chunks[i >> CHUNK_BITS][i & (CHUNK - 1)]
    }
}

impl<T: Copy> core::ops::IndexMut<usize> for Chunked<T> {
    fn index_mut(&mut self, i: usize) -> &mut T {
        &mut self.chunks[i >> CHUNK_BITS][i & (CHUNK - 1)]
    }
}

fn zero_counts() -> GateCounts {
    GateCounts { direct_and: 0, direct_xor: 0, direct_or: 0, custom: 0, custom_and: 0, custom_xor: 0, custom_or: 0 }
}

fn copy_counts(c: &GateCounts) -> GateCounts {
    GateCounts {
        direct_and: c.direct_and,
        direct_xor: c.direct_xor,
        direct_or: c.direct_or,
        custom: 0,
        custom_and: 0,
        custom_xor: 0,
        custom_or: 0,
    }
}

/// A wire used this often is never released.
const PINNED: u8 = u8::MAX;

/// The first pass: the number of uses of each wire, by creation index, with
/// the same folding as the garbling pass so that the two see the same wires.
pub struct Plan {
    uses: Chunked<u8>,
    counts: GateCounts,
    empty: Vec<GateOperation>,
}

impl Plan {
    pub fn new() -> Self {
        let mut me = Self { uses: Chunked::new(), counts: zero_counts(), empty: Vec::new() };
        me.uses.push(PINNED);
        me.uses.push(PINNED);
        me
    }

    fn alloc(&mut self) -> usize {
        self.uses.push(0);
        self.uses.len() - 1
    }

    fn used(&mut self, x: usize) {
        let u = &mut self.uses[x];
        *u = u.saturating_add(1);
    }

    pub fn wires(&self) -> usize {
        self.uses.len()
    }

    /// A wire read after the build, such as an output, is never released:
    /// otherwise its slot goes to a later wire once the last gate has read it.
    pub fn keep(&mut self, wire: usize) {
        self.uses[wire] = PINNED;
    }
}

impl Default for Plan {
    fn default() -> Self {
        Self::new()
    }
}

impl CircuitTrait for Plan {
    fn fresh_one(&mut self) -> usize {
        self.alloc()
    }

    fn fresh<const N: usize>(&mut self) -> [usize; N] {
        core::array::from_fn(|_| self.fresh_one())
    }

    fn zero(&mut self) -> usize {
        0
    }

    fn one(&mut self) -> usize {
        1
    }

    fn xor_wire(&mut self, x: usize, y: usize) -> usize {
        if x == y {
            return 0;
        }
        if x == 0 {
            return y;
        }
        if y == 0 {
            return x;
        }
        self.used(x);
        self.used(y);
        self.counts.direct_xor += 1;
        self.alloc()
    }

    fn or_wire(&mut self, x: usize, y: usize) -> usize {
        if x == y {
            return x;
        }
        if x == 1 || y == 1 {
            return 1;
        }
        if x == 0 {
            return y;
        }
        if y == 0 {
            return x;
        }
        self.used(x);
        self.used(y);
        self.counts.direct_or += 1;
        self.alloc()
    }

    fn and_wire(&mut self, x: usize, y: usize) -> usize {
        if x == y {
            return x;
        }
        if x == 0 || y == 0 {
            return 0;
        }
        if x == 1 {
            return y;
        }
        if y == 1 {
            return x;
        }
        self.used(x);
        self.used(y);
        self.counts.direct_and += 1;
        self.alloc()
    }

    fn push_custom_gate(&mut self, _params: CustomGateParams, _new_wire_idx: usize) {
        unimplemented!("custom gates are not used")
    }

    fn get_gates(&self) -> &Vec<GateOperation> {
        &self.empty
    }

    fn gate_counts(&self) -> GateCounts {
        copy_counts(&self.counts)
    }

    fn next_wire(&self) -> usize {
        self.uses.len()
    }

    fn init_circuit_config_for_custom_gate(&mut self, _templ_type: CustomGateType) -> &Template {
        unimplemented!("custom gates are not used")
    }

    fn get_template(&self, _templ_type: CustomGateType) -> Option<&Template> {
        None
    }
}

impl ValuedBuilder for Plan {
    fn set_input(&mut self, _wire: usize, _value: bool) {}
}

/// Garble and evaluate on the fly. See the module documentation.
pub struct Streaming {
    delta: S,
    seed: [u8; 32],
    /// Per slot.
    label0: Chunked<S>,
    value: Chunked<bool>,
    remaining: Chunked<u8>,
    free: Vec<usize>,
    /// Uses per wire by creation index, from a [`Plan`]; without one every
    /// wire is pinned and slots are never reused.
    plan: Option<Chunked<u8>>,
    created: usize,
    peak_live: usize,
    counts: GateCounts,
    /// Ciphertexts, kept only when asked for; the count is always kept.
    ciphertexts: Vec<S>,
    keep_ciphertexts: bool,
    non_free: usize,
    empty: Vec<GateOperation>,
}

impl Streaming {
    /// Without a plan: one slot per wire, nothing released.
    pub fn new(keep_ciphertexts: bool) -> Self {
        Self::with(None, keep_ciphertexts)
    }

    /// With the use counts of a first pass of the same build.
    pub fn planned(plan: Plan, keep_ciphertexts: bool) -> Self {
        Self::with(Some(plan.uses), keep_ciphertexts)
    }

    fn with(plan: Option<Chunked<u8>>, keep_ciphertexts: bool) -> Self {
        let mut me = Self {
            delta: S::random(),
            seed: random_seed::<32>(),
            label0: Chunked::new(),
            value: Chunked::new(),
            remaining: Chunked::new(),
            free: Vec::new(),
            plan,
            created: 0,
            peak_live: 0,
            counts: zero_counts(),
            ciphertexts: Vec::new(),
            keep_ciphertexts,
            non_free: 0,
            empty: Vec::new(),
        };
        // Wires 0 and 1 are the constants, as `CircuitAdapter` numbers them.
        let zero = me.alloc(false);
        let one = me.alloc(true);
        assert_eq!((zero, one), (0, 1));
        me
    }

    /// The label of an input wire, from its creation index.
    fn input_label(&self, k: usize) -> S {
        let mut h = blake3::Hasher::new_keyed(&self.seed);
        h.update(&(k as u64).to_le_bytes());
        let mut label = [0u8; 16];
        h.finalize_xof().fill(&mut label);
        S::from_slice(&label)
    }

    /// A wire with a fresh input label.
    fn alloc(&mut self, value: bool) -> usize {
        let label = self.input_label(self.created);
        self.alloc_with(value, label)
    }

    /// A wire whose label a gate sets: the next creation index, in a released
    /// slot when there is one.
    fn alloc_with(&mut self, value: bool, label: S) -> usize {
        let k = self.created;
        self.created += 1;
        let uses = match &self.plan {
            Some(p) => p[k],
            None => PINNED,
        };
        if let Some(slot) = self.free.pop() {
            self.label0[slot] = label;
            self.value[slot] = value;
            self.remaining[slot] = uses;
            slot
        } else {
            self.label0.push(label);
            self.value.push(value);
            self.remaining.push(uses);
            self.peak_live = self.peak_live.max(self.label0.len());
            self.label0.len() - 1
        }
    }

    /// One use of `x`: release its slot after the last.
    fn consume(&mut self, x: usize) {
        let r = &mut self.remaining[x];
        if *r == PINNED {
            return;
        }
        assert!(*r > 0, "a wire is read more often than its plan says");
        *r -= 1;
        if *r == 0 {
            self.free.push(x);
        }
    }

    /// The evaluator's label of `wire`: its false label offset by its value.
    fn held(&self, wire: usize) -> S {
        if self.value[wire] { self.label0[wire] ^ self.delta } else { self.label0[wire] }
    }

    /// One non-free gate: garble it, then run the evaluator's formula on the
    /// held input labels and require the held output label.
    fn non_free(&mut self, x: usize, y: usize, is_or: bool) -> usize {
        let gid = u32::try_from(self.non_free).expect("gate ids fit in u32");
        // The garbling of the gate, under this garbler's delta and no salt.
        let gate_type = if is_or { GateType::Or } else { GateType::And };
        let (c0, ct) = gate_garbled_with_delta(self.label0[x], self.label0[y], gid, gate_type, self.delta, None);
        let v = if is_or { self.value[x] | self.value[y] } else { self.value[x] & self.value[y] };
        // The evaluator, holding the labels of the values.
        let evaluated = gate_evaluate(gate_type, self.value[x], self.held(x), self.held(y), ct, gid, None);
        let ct = ct.expect("AND and OR gates carry a ciphertext");
        self.consume(x);
        self.consume(y);
        let d = self.alloc_with(v, c0);
        assert_eq!(evaluated, self.held(d), "the evaluator's label is the output's label");
        if self.keep_ciphertexts {
            self.ciphertexts.push(ct);
        }
        self.non_free += 1;
        d
    }

    pub fn value(&self, wire: usize) -> bool {
        self.value[wire]
    }

    pub fn label0(&self, wire: usize) -> S {
        self.label0[wire]
    }

    pub fn delta(&self) -> S {
        self.delta
    }

    pub fn non_free_gates(&self) -> usize {
        self.non_free
    }

    pub fn ciphertexts(&self) -> &[S] {
        &self.ciphertexts
    }

    /// Wires created.
    pub fn wires(&self) -> usize {
        self.created
    }

    /// The most slots ever held at once.
    pub fn peak_live(&self) -> usize {
        self.peak_live
    }
}

impl CircuitTrait for Streaming {
    fn fresh_one(&mut self) -> usize {
        self.alloc(false)
    }

    fn fresh<const N: usize>(&mut self) -> [usize; N] {
        core::array::from_fn(|_| self.fresh_one())
    }

    fn zero(&mut self) -> usize {
        0
    }

    fn one(&mut self) -> usize {
        1
    }

    fn xor_wire(&mut self, x: usize, y: usize) -> usize {
        if x == y {
            return 0;
        }
        if x == 0 {
            return y;
        }
        if y == 0 {
            return x;
        }
        let v = self.value[x] ^ self.value[y];
        let l = self.label0[x] ^ self.label0[y];
        self.consume(x);
        self.consume(y);
        self.counts.direct_xor += 1;
        self.alloc_with(v, l)
    }

    fn or_wire(&mut self, x: usize, y: usize) -> usize {
        if x == y {
            return x;
        }
        if x == 1 || y == 1 {
            return 1;
        }
        if x == 0 {
            return y;
        }
        if y == 0 {
            return x;
        }
        self.counts.direct_or += 1;
        self.non_free(x, y, true)
    }

    fn and_wire(&mut self, x: usize, y: usize) -> usize {
        if x == y {
            return x;
        }
        if x == 0 || y == 0 {
            return 0;
        }
        if x == 1 {
            return y;
        }
        if y == 1 {
            return x;
        }
        self.counts.direct_and += 1;
        self.non_free(x, y, false)
    }

    fn push_custom_gate(&mut self, _params: CustomGateParams, _new_wire_idx: usize) {
        unimplemented!("custom gates are not used")
    }

    fn get_gates(&self) -> &Vec<GateOperation> {
        &self.empty
    }

    fn gate_counts(&self) -> GateCounts {
        copy_counts(&self.counts)
    }

    fn next_wire(&self) -> usize {
        self.label0.len()
    }

    fn init_circuit_config_for_custom_gate(&mut self, _templ_type: CustomGateType) -> &Template {
        unimplemented!("custom gates are not used")
    }

    fn get_template(&self, _templ_type: CustomGateType) -> Option<&Template> {
        None
    }
}

impl ValuedBuilder for Streaming {
    fn set_input(&mut self, wire: usize, value: bool) {
        self.value[wire] = value;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small circuit through a plan and then the planned garbler: the
    /// output's value and label follow the inputs, and the slot count is the
    /// live-wire bound rather than the wire count.
    #[test]
    fn planned_slots_are_released_and_reused() {
        fn build<T: ValuedBuilder>(b: &mut T, bits: [bool; 3]) -> usize {
            let x = b.fresh_one();
            b.set_input(x, bits[0]);
            let y = b.fresh_one();
            b.set_input(y, bits[1]);
            let z = b.fresh_one();
            b.set_input(z, bits[2]);
            let mut acc = b.and_wire(x, y);
            for _ in 0..100 {
                let t = b.xor_wire(acc, z);
                acc = b.or_wire(t, x);
                acc = b.and_wire(acc, y);
            }
            acc
        }
        for bits in 0..8u8 {
            let w = [bits & 1 == 1, bits & 2 == 2, bits & 4 == 4];
            let mut p = Plan::new();
            let _ = build(&mut p, w);
            let wires = p.wires();
            let mut s = Streaming::planned(p, true);
            let out = build(&mut s, w);
            let mut expect = w[0] & w[1];
            for _ in 0..100 {
                expect = ((expect ^ w[2]) | w[0]) & w[1];
            }
            assert_eq!(s.value(out), expect);
            assert_eq!(s.non_free_gates(), 201);
            assert_eq!(s.ciphertexts().len(), 201);
            assert_eq!(s.wires(), wires);
            assert!(s.peak_live() < 12, "{} slots for {} wires", s.peak_live(), wires);
        }
    }
}
