use ark_bn254::{Fq, Fr, G1Affine, G2Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_groth16::VerifyingKey as Groth16VerifyingKey;
use ripemd::{Ripemd160, Digest as RipemdDigest};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use sha2::{Digest, Sha256};

// ── Groth16 public-input layout ───────────────────────────────────────────────
// Layout: [vkey_hash, committed_values_digest, vk_root].
// L_i = gamma_abc_g1[i]; public-input slot i (0-based) is multiplied by L_{i+1}, and L_0 is the constant term.

pub const STATIC_SLOTS: [usize; 2] = [0, 2];
pub const DYNAMIC_SLOTS: [usize; 1] = [1];
pub const NUM_PUBLIC_INPUTS: usize = STATIC_SLOTS.len() + DYNAMIC_SLOTS.len();

pub type StaticInputs = [Fr; STATIC_SLOTS.len()];
pub type DynamicInputs = [Fr; DYNAMIC_SLOTS.len()];

/// Static inputs of the Ziren wrap circuit.
pub fn ziren_static_inputs(vkey_hash: &[u8; 32], vk_root: &[u8; 32]) -> StaticInputs {
    [Fr::from_be_bytes_mod_order(vkey_hash), Fr::from_be_bytes_mod_order(vk_root)]
}

/// Checks that `vk` has exactly `NUM_PUBLIC_INPUTS` public inputs.
pub fn check_vk_layout(vk: &Groth16VerifyingKey<ark_bn254::Bn254>) -> Result<(), String> {
    if vk.gamma_abc_g1.len() != NUM_PUBLIC_INPUTS + 1 {
        return Err(format!(
            "vk has {} public inputs, expected {NUM_PUBLIC_INPUTS} (static slots {STATIC_SLOTS:?}, dynamic slots {DYNAMIC_SLOTS:?})",
            vk.gamma_abc_g1.len().saturating_sub(1),
        ));
    }
    Ok(())
}

/// P_S = L_0 + Σ_k static[k]·L_{STATIC_SLOTS[k]+1}
pub fn static_vk_x(
    vk: &Groth16VerifyingKey<ark_bn254::Bn254>,
    static_inputs: &StaticInputs,
) -> Result<ark_bn254::G1Projective, String> {
    check_vk_layout(vk)?;
    Ok(STATIC_SLOTS.iter().zip(static_inputs).fold(
        vk.gamma_abc_g1[0].into_group(),
        |acc, (&slot, x)| acc + vk.gamma_abc_g1[slot + 1] * x,
    ))
}

/// L_i: the base point of the dynamic input, baked into SGC part 1 as the l2 point.
pub fn dynamic_base(vk: &Groth16VerifyingKey<ark_bn254::Bn254>) -> Result<G1Affine, String> {
    check_vk_layout(vk)?;
    Ok(vk.gamma_abc_g1[DYNAMIC_SLOTS[0] + 1])
}

/// Full ordered public-input vector, with each value placed at its slot.
pub fn full_public_inputs(static_inputs: &StaticInputs, dynamic_inputs: &DynamicInputs) -> Vec<Fr> {
    let mut out = vec![Fr::from(0u64); NUM_PUBLIC_INPUTS];
    for (&slot, &x) in STATIC_SLOTS.iter().zip(static_inputs) {
        out[slot] = x;
    }
    for (&slot, &x) in DYNAMIC_SLOTS.iter().zip(dynamic_inputs) {
        out[slot] = x;
    }
    out
}

pub fn groth16_vk_x(
    vk: &Groth16VerifyingKey<ark_bn254::Bn254>,
    public_inputs: &[Fr],
) -> Option<ark_bn254::G1Projective> {
    if vk.gamma_abc_g1.len() != public_inputs.len() + 1 {
        return None;
    }
    let mut acc = vk.gamma_abc_g1[0].into_group();
    for (i, x) in public_inputs.iter().enumerate() {
        acc += vk.gamma_abc_g1[i + 1].into_group() * *x;
    }
    Some(acc)
}

pub fn g2_project_to_ser(p: ark_bn254::G2Projective) -> Vec<u8> {
    let mut out = Vec::new();
    p.into_affine().serialize_compressed(&mut out).expect("serialize g2");
    out
}

pub fn g1_project_to_ser(p: ark_bn254::G1Projective) -> Vec<u8> {
    let mut out = Vec::new();
    p.into_affine().serialize_compressed(&mut out).expect("serialize g1");
    out
}

/// Non-identity, on-curve, correct-subgroup check for an already-parsed G1 point.
pub fn g1affine_is_valid(a: &G1Affine) -> bool {
    !a.is_zero() && a.is_on_curve() && a.is_in_correct_subgroup_assuming_on_curve()
}

pub fn g1_from_ser_checked(v: &[u8]) -> Option<ark_bn254::G1Projective> {
    let a = G1Affine::deserialize_compressed(v).ok()?;
    if !g1affine_is_valid(&a) {
        return None;
    }
    Some(a.into_group())
}

pub fn g2_from_ser_checked(v: &[u8]) -> Option<ark_bn254::G2Projective> {
    let a = G2Affine::deserialize_compressed(v).ok()?;
    if a.is_zero() || !a.is_on_curve() || !a.is_in_correct_subgroup_assuming_on_curve() {
        return None;
    }
    Some(a.into_group())
}

/// Encode pi1 and x_d into a 96-byte Wots96 message.
/// Layout: pi1.x LE-32 || pi1.y LE-32 || x_d LE-32.
/// Bit packing: bits[i] = (msg[i/8] >> (i%8)) & 1  (LSB-first within each byte).
/// Bits 254-255 of each 32-byte chunk are always 0 (BN254 fields are < 2^254).
pub fn pi1_xd_to_wots96_msg(pi1: &G1Affine, x_d: Fr) -> [u8; 96] {
    let mut msg = [0u8; 96];
    let mut tmp = Vec::new();

    pi1.x.serialize_uncompressed(&mut tmp).expect("serialize pi1.x");
    msg[..32].copy_from_slice(&tmp);

    tmp.clear();
    pi1.y.serialize_uncompressed(&mut tmp).expect("serialize pi1.y");
    msg[32..64].copy_from_slice(&tmp);

    tmp.clear();
    x_d.serialize_uncompressed(&mut tmp).expect("serialize x_d");
    msg[64..96].copy_from_slice(&tmp);

    msg
}

pub fn ro_from_pairing_bytes(seed: &[u8], msg_len: usize) -> Vec<u8> {
    let key = h_256(seed);
    let mut nonce = [0u8; 12];
    nonce.copy_from_slice(&h_256(&[b"babe-we-known-pi1-ro-nonce".as_slice(), seed].concat())[..12]);
    derive_stream_xor_keyed(key, nonce, msg_len)
}

fn derive_stream_xor_keyed(key: [u8; 32], nonce: [u8; 12], msg_len: usize) -> Vec<u8> {
    let mut out = vec![0u8; msg_len];
    let mut ctr: u32 = 0;
    let mut off = 0usize;
    while off < msg_len {
        let mut blk = b"babe-we-stream".to_vec();
        blk.extend_from_slice(&key);
        blk.extend_from_slice(&nonce);
        blk.extend_from_slice(&ctr.to_le_bytes());
        let hblk = h_256(&blk);
        let take = core::cmp::min(32, msg_len - off);
        out[off..off + take].copy_from_slice(&hblk[..take]);
        ctr += 1;
        off += take;
    }
    out
}

#[inline(always)]
/// SHA256
pub fn h_256(data: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}

/// RIPEMD160
pub fn h_160(data: &[u8]) -> [u8; 20] {
    let mut hasher = Ripemd160::new();
    hasher.update(data);
    hasher.finalize().into()
}

/// h_msg = RIPEMD160(SHA256(data)) — the hashlock value.
pub fn derive_hashlock(secret: &[u8]) -> [u8; 20] {
    h_160(&h_256(&secret))
}

/// `serde` shim for `Fq` via its compressed `ark-serialize` byte form.
/// Use with `#[serde(serialize_with = "crate::utils::serialize_fq", deserialize_with = "crate::utils::deserialize_fq")]`.
pub fn serialize_fq<S: Serializer>(val: &Fq, serializer: S) -> Result<S::Ok, S::Error> {
    let mut bytes = Vec::new();
    val.serialize_compressed(&mut bytes).map_err(serde::ser::Error::custom)?;
    bytes.serialize(serializer)
}

pub fn deserialize_fq<'de, D: Deserializer<'de>>(deserializer: D) -> Result<Fq, D::Error> {
    let bytes = Vec::<u8>::deserialize(deserializer)?;
    Fq::deserialize_compressed(bytes.as_slice()).map_err(serde::de::Error::custom)
}

pub fn serialize_g1affine<S: Serializer>(val: &G1Affine, serializer: S) -> Result<S::Ok, S::Error> {
    let mut bytes = Vec::new();
    val.serialize_compressed(&mut bytes).map_err(serde::ser::Error::custom)?;
    bytes.serialize(serializer)
}

pub fn deserialize_g1affine<'de, D: Deserializer<'de>>(deserializer: D) -> Result<G1Affine, D::Error> {
    let bytes = Vec::<u8>::deserialize(deserializer)?;
    G1Affine::deserialize_compressed(bytes.as_slice()).map_err(serde::de::Error::custom)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;
    use rand::SeedableRng;
    use rand_chacha::ChaCha12Rng;

    #[test]
    fn test_groth16_vk_x() {
        let mut rng = ChaCha12Rng::seed_from_u64(1);
        let g0 = ark_bn254::G1Projective::rand(&mut rng).into_affine();
        let g1 = ark_bn254::G1Projective::rand(&mut rng).into_affine();
        let g2 = ark_bn254::G1Projective::rand(&mut rng).into_affine();
        let vk = Groth16VerifyingKey::<ark_bn254::Bn254> {
            gamma_abc_g1: vec![g0, g1, g2],
            ..Default::default()
        };

        let x1 = Fr::from(3u64);
        let x2 = Fr::from(5u64);
        let expected = (g0.into_group() + g1.into_group() * x1 + g2.into_group() * x2).into_affine();
        let actual = groth16_vk_x(&vk, &[x1, x2]).unwrap().into_affine();
        assert_eq!(actual, expected);

        // length mismatch: public_inputs.len() + 1 != gamma_abc_g1.len()
        assert!(groth16_vk_x(&vk, &[x1]).is_none());
        assert!(groth16_vk_x(&vk, &[x1, x2, Fr::from(7u64)]).is_none());
    }

    #[test]
    fn test_public_input_layout() {
        let mut rng = ChaCha12Rng::seed_from_u64(6);
        let vk = Groth16VerifyingKey::<ark_bn254::Bn254> {
            gamma_abc_g1: (0..=NUM_PUBLIC_INPUTS)
                .map(|_| ark_bn254::G1Projective::rand(&mut rng).into_affine())
                .collect(),
            ..Default::default()
        };
        let statics: StaticInputs = [Fr::from(3u64), Fr::from(5u64)];
        let x_d = Fr::from(7u64);

        // Placement follows STATIC_SLOTS / DYNAMIC_SLOTS.
        let full = full_public_inputs(&statics, &[x_d]);
        assert_eq!(full, vec![Fr::from(3u64), x_d, Fr::from(5u64)]);

        // static part + dynamic part == full vk_x.
        let p_s = static_vk_x(&vk, &statics).unwrap();
        let q = dynamic_base(&vk).unwrap() * x_d;
        assert_eq!((p_s + q).into_affine(), groth16_vk_x(&vk, &full).unwrap().into_affine());

        // vk with the wrong number of public inputs is rejected.
        let mut short_vk = vk.clone();
        short_vk.gamma_abc_g1.pop();
        assert!(check_vk_layout(&short_vk).is_err());
        assert!(static_vk_x(&short_vk, &statics).is_err());
        assert!(dynamic_base(&short_vk).is_err());
    }

    #[test]
    fn test_ziren_static_inputs_big_endian() {
        let mut vkey_hash = [0u8; 32];
        vkey_hash[31] = 2;
        let mut vk_root = [0u8; 32];
        vk_root[30] = 1;
        assert_eq!(ziren_static_inputs(&vkey_hash, &vk_root), [Fr::from(2u64), Fr::from(256u64)]);
    }

    #[test]
    fn test_g1_from_ser_checked() {
        let mut rng = ChaCha12Rng::seed_from_u64(2);
        let p = ark_bn254::G1Projective::rand(&mut rng).into_affine();
        let mut valid_bytes = Vec::new();
        p.serialize_compressed(&mut valid_bytes).unwrap();
        assert_eq!(g1_from_ser_checked(&valid_bytes).unwrap().into_affine(), p);

        let mut identity_bytes = Vec::new();
        G1Affine::zero().serialize_compressed(&mut identity_bytes).unwrap();
        assert!(g1_from_ser_checked(&identity_bytes).is_none());

        assert!(g1_from_ser_checked(&[0xFFu8; 32]).is_none());
    }

    #[test]
    fn test_g2_from_ser_checked() {
        let mut rng = ChaCha12Rng::seed_from_u64(3);
        let p = ark_bn254::G2Projective::rand(&mut rng).into_affine();
        let mut valid_bytes = Vec::new();
        p.serialize_compressed(&mut valid_bytes).unwrap();
        assert_eq!(g2_from_ser_checked(&valid_bytes).unwrap().into_affine(), p);

        let mut identity_bytes = Vec::new();
        G2Affine::zero().serialize_compressed(&mut identity_bytes).unwrap();
        assert!(g2_from_ser_checked(&identity_bytes).is_none());

        assert!(g2_from_ser_checked(&[0xFFu8; 64]).is_none());
    }

    #[test]
    fn test_pi1_xd_to_wots96_msg_byte_layout() {
        let mut rng = ChaCha12Rng::seed_from_u64(4);
        let pi1 = ark_bn254::G1Projective::rand(&mut rng).into_affine();
        let x_d = Fr::rand(&mut rng);
        let msg = pi1_xd_to_wots96_msg(&pi1, x_d);

        let mut x_bytes = Vec::new();
        pi1.x.serialize_uncompressed(&mut x_bytes).unwrap();
        let mut y_bytes = Vec::new();
        pi1.y.serialize_uncompressed(&mut y_bytes).unwrap();
        let mut xd_bytes = Vec::new();
        x_d.serialize_uncompressed(&mut xd_bytes).unwrap();

        assert_eq!(&msg[0..32], x_bytes.as_slice());
        assert_eq!(&msg[32..64], y_bytes.as_slice());
        assert_eq!(&msg[64..96], xd_bytes.as_slice());
    }

    #[test]
    fn test_ro_from_pairing_bytes() {
        let seed1 = b"seed-one".as_slice();
        let seed2 = b"seed-two".as_slice();

        let out1a = ro_from_pairing_bytes(seed1, 40);
        let out1b = ro_from_pairing_bytes(seed1, 40);
        let out2 = ro_from_pairing_bytes(seed2, 40);

        assert_eq!(out1a.len(), 40);
        assert_eq!(out1a, out1b, "same seed must be deterministic");
        assert_ne!(out1a, out2, "different seeds must diverge");

        // Stream is CTR-based over blocks derived from (key, nonce) alone, so a shorter
        // request must be a prefix of a longer one for the same seed.
        let out_short = ro_from_pairing_bytes(seed1, 5);
        assert_eq!(out_short.as_slice(), &out1a[..5]);
    }

    #[test]
    fn test_serde_shims_roundtrip() {
        #[derive(Serialize, Deserialize)]
        struct FqWrap(
            #[serde(serialize_with = "serialize_fq", deserialize_with = "deserialize_fq")] Fq,
        );
        #[derive(Serialize, Deserialize)]
        struct G1Wrap(
            #[serde(serialize_with = "serialize_g1affine", deserialize_with = "deserialize_g1affine")]
            G1Affine,
        );

        let mut rng = ChaCha12Rng::seed_from_u64(5);

        let fq = Fq::rand(&mut rng);
        let bytes = bincode::serialize(&FqWrap(fq)).unwrap();
        let back: FqWrap = bincode::deserialize(&bytes).unwrap();
        assert_eq!(back.0, fq);

        let g1 = ark_bn254::G1Projective::rand(&mut rng).into_affine();
        let bytes = bincode::serialize(&G1Wrap(g1)).unwrap();
        let back: G1Wrap = bincode::deserialize(&bytes).unwrap();
        assert_eq!(back.0, g1);
    }
}
