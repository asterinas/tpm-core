use vstd::prelude::*;
use vstd::array::*;

verus! {

// ===========================================================================
// Size constants
// ===========================================================================

/// SHA-256 digest length. The nonce, session key and HMAC fields in this layer all use this length.
pub const SHA256_LEN: usize = 32;

/// Session nonce length. The specification allows any value between 16 and the digest length; the upper limit is taken here:
/// the longer the nonce, the smaller the replay window, at the cost of only a few dozen extra bytes in the message.
pub const NONCE_LEN: usize = SHA256_LEN;

pub const AES_KEY_LEN: usize = 16;
pub const AES_BLOCK_LEN: usize = 16;

/// Key material needed for parameter encryption/decryption: an AES key followed by an initialization vector.
///
/// It is exactly one digest block long, which [`kdfa32`] uses to fix the derivation to
/// a single round; see the note there.
pub const CFB_MATERIAL_LEN: usize = AES_KEY_LEN + AES_BLOCK_LEN;

/// Upper limit for storing the passphrase in the session structure.
pub const PASSPHRASE_MAX: usize = SHA256_LEN;

/// Upper limit of HMAC key material: the session key followed by the passphrase.
pub(crate) const KEY_MATERIAL_MAX: usize = SHA256_LEN + PASSPHRASE_MAX;

// ===========================================================================
// Big-endian sequences
// ===========================================================================
//
// These two spec fns are not a new byte-order convention; they lift the postconditions of `cursor::be16_bytes` /
// `cursor::be32_bytes` to the sequence level -- hash input is naturally a concatenation of sequences,
// and writing the spec in array form would make every equation drag an `@` along. The two agree byte by byte, guaranteed by the proofs of the
// two wrapper functions below.

pub open spec fn be16_seq(v: u16) -> Seq<u8> {
    seq![(v / 256) as u8, (v % 256) as u8]
}

pub open spec fn be32_seq(v: u32) -> Seq<u8> {
    seq![
        (v / 16777216) as u8,
        ((v / 65536) % 256) as u8,
        ((v / 256) % 256) as u8,
        (v % 256) as u8,
    ]
}

pub(crate) fn be16_arr(v: u16) -> (r: [u8; 2])
    ensures
        r@ =~= be16_seq(v),
{
    crate::cursor::be16_bytes(v)
}

pub(crate) fn be32_arr(v: u32) -> (r: [u8; 4])
    ensures
        r@ =~= be32_seq(v),
{
    crate::cursor::be32_bytes(v)
}

// ===========================================================================
// Uninterpreted crypto functions
// ===========================================================================
//
// These four functions are deliberately left undefined: none of the properties proved in this layer depends on their internal structure.
// The formal content of "the response passes verification" is **byte-wise equality** -- the received MAC equals the MAC recomputed locally
// with the same key and the same nonce pair -- and this property holds equally when the hash is treated as an
// arbitrary function, so SHA-256's compression function need not be dragged into the proof.
//
// Conversely, "an attacker cannot forge a MAC" is outside the proof scope of this layer; it is a cryptographic assumption,
// part of the trust base, and should be written into the TCB document rather than treated as a theorem.

pub uninterp spec fn spec_sha256(msg: Seq<u8>) -> Seq<u8>;

pub uninterp spec fn spec_hmac_sha256(key: Seq<u8>, msg: Seq<u8>) -> Seq<u8>;

/// `encrypt` true means the encryption direction, false means decryption.
pub uninterp spec fn spec_aes_cfb(
    key: Seq<u8>,
    iv: Seq<u8>,
    input: Seq<u8>,
    encrypt: bool,
) -> Seq<u8>;

/// The random string obtained by the `gen`-th draw.
///
/// The generation number is the **only** modeled property: it makes "this round's nonce is not the previous one" a provable
/// syntactic fact. That the values of two draws really differ is a probabilistic property of the random source and is not
/// asserted here.
pub uninterp spec fn spec_draw(gen: nat) -> Seq<u8>;

// ===========================================================================
// Trusted axioms
// ===========================================================================
//
// Only length and invertibility are declared. Any assertion beyond these two kinds would quietly thicken the TCB.

#[verifier::external_body]
pub broadcast proof fn axiom_sha256_len(msg: Seq<u8>)
    ensures
        #[trigger] spec_sha256(msg).len() == SHA256_LEN as nat,
{
}

#[verifier::external_body]
pub broadcast proof fn axiom_hmac_len(key: Seq<u8>, msg: Seq<u8>)
    ensures
        #[trigger] spec_hmac_sha256(key, msg).len() == SHA256_LEN as nat,
{
}

#[verifier::external_body]
pub broadcast proof fn axiom_draw_len(gen: nat)
    ensures
        #[trigger] spec_draw(gen).len() == NONCE_LEN as nat,
{
}

/// A stream cipher does not change length. The parameter area is encrypted/decrypted in place, so the buffer layout is unaffected --
/// this is a premise of layout reasoning, not a cryptographic property.
#[verifier::external_body]
pub broadcast proof fn axiom_cfb_len(key: Seq<u8>, iv: Seq<u8>, input: Seq<u8>, enc: bool)
    ensures
        #[trigger] spec_aes_cfb(key, iv, input, enc).len() == input.len(),
{
}

/// With the same key and the same initialization vector, decryption is a left inverse of encryption.
#[verifier::external_body]
pub broadcast proof fn axiom_cfb_roundtrip(key: Seq<u8>, iv: Seq<u8>, input: Seq<u8>)
    ensures
        #[trigger] spec_aes_cfb(key, iv, spec_aes_cfb(key, iv, input, true), false) == input,
{
}

pub broadcast group group_crypto_axioms {
    axiom_sha256_len,
    axiom_hmac_len,
    axiom_draw_len,
    axiom_cfb_len,
    axiom_cfb_roundtrip,
}

// ===========================================================================
// Incremental digest interface
// ===========================================================================
//
// Made a context rather than "feed one whole block at once" because the input of a command digest is assembled from the command code, several
// handle names, and the whole parameter area, and the parameter area can be several thousand bytes. Requiring the full input to be assembled
// before hashing would need a buffer of the same size in an allocator-free environment, which is pure waste.
//
// The spec records the absorbed byte sequence with `absorbed()`, so the concatenation semantics are explicit, and a wrong
// call order is exposed at proof time rather than discovered when the books fail to match a real device.

pub trait Sha256Ctx: Sized {
    spec fn absorbed(&self) -> Seq<u8>;

    fn new() -> (r: Self)
        ensures
            r.absorbed() =~= Seq::<u8>::empty(),
    ;

    fn update(&mut self, data: &[u8])
        ensures
            final(self).absorbed() =~= old(self).absorbed() + data@,
    ;

    fn finish(self) -> (r: [u8; SHA256_LEN])
        ensures
            r@ =~= spec_sha256(self.absorbed()),
    ;
}

pub trait HmacSha256Ctx: Sized {
    spec fn key(&self) -> Seq<u8>;

    spec fn absorbed(&self) -> Seq<u8>;

    fn with_key(key: &[u8]) -> (r: Self)
        ensures
            r.key() =~= key@,
            r.absorbed() =~= Seq::<u8>::empty(),
    ;

    fn update(&mut self, data: &[u8])
        ensures
            final(self).key() =~= old(self).key(),
            final(self).absorbed() =~= old(self).absorbed() + data@,
    ;

    fn finish(self) -> (r: [u8; SHA256_LEN])
        ensures
            r@ =~= spec_hmac_sha256(self.key(), self.absorbed()),
    ;
}

// ===========================================================================
// Random source
// ===========================================================================

pub trait NonceSource {
    /// Number of draws so far. Appears only in proofs and takes no space at runtime.
    ///
    /// Not named `gen`: that is a reserved word in the 2024 edition.
    spec fn draws(&self) -> nat;

    fn nonce(&mut self) -> (r: [u8; NONCE_LEN])
        ensures
            final(self).draws() == old(self).draws() + 1,
            r@ =~= spec_draw(old(self).draws()),
    ;
}

// ===========================================================================
// Parameter encryption/decryption
// ===========================================================================

pub trait AesCfb {
    /// Encrypt in place. The first half of `material` is the key, the second half is the initialization vector.
    fn encrypt(&self, material: &[u8; CFB_MATERIAL_LEN], data: &mut [u8])
        ensures
            final(data)@ =~= spec_aes_cfb(
                material@.subrange(0, AES_KEY_LEN as int),
                material@.subrange(AES_KEY_LEN as int, CFB_MATERIAL_LEN as int),
                old(data)@,
                true,
            ),
            final(data).len() == old(data).len(),
    ;

    fn decrypt(&self, material: &[u8; CFB_MATERIAL_LEN], data: &mut [u8])
        ensures
            final(data)@ =~= spec_aes_cfb(
                material@.subrange(0, AES_KEY_LEN as int),
                material@.subrange(AES_KEY_LEN as int, CFB_MATERIAL_LEN as int),
                old(data)@,
                false,
            ),
            final(data).len() == old(data).len(),
    ;
}

// ===========================================================================
// Key derivation
// ===========================================================================

/// Input of one round of the derivation function: counter ‖ label ‖ context U ‖ context V ‖ total bits.
///
/// The label carries a trailing zero as the specification requires. It is agreed here that **the label passed in by the caller already includes the trailing zero**, rather than
/// appending it inside the function -- appending a zero would mean either preparing an extra buffer or feeding one more single byte,
/// and both leave a concatenation term in the spec that is easy to get backwards.
pub open spec fn spec_kdfa_msg(label: Seq<u8>, u: Seq<u8>, v: Seq<u8>, bits: u32) -> Seq<u8> {
    be32_seq(1) + label + u + v + be32_seq(bits)
}

pub open spec fn spec_kdfa32(key: Seq<u8>, label: Seq<u8>, u: Seq<u8>, v: Seq<u8>) -> Seq<u8> {
    spec_hmac_sha256(key, spec_kdfa_msg(label, u, v, 256))
}

/// Session key derivation label (including trailing zero).
pub const LABEL_ATH: [u8; 4] = [0x41, 0x54, 0x48, 0x00];

/// Parameter encryption/decryption key derivation label (including trailing zero).
pub const LABEL_CFB: [u8; 4] = [0x43, 0x46, 0x42, 0x00];

/// Derive 32 bytes of key material.
///
/// The counter runs for only one round. The two things this layer derives -- the session key, and the key
/// plus initialization vector for parameter encryption -- are each exactly one digest block long, so a general multi-round loop has
/// no caller here. With the derivation fixed to one round, neither a loop invariant nor termination needs proving, and the spec is left with just
/// one equation. If longer output is needed later, a separate multi-round version with `decreases` should be written,
/// rather than turning this function into a loop -- that would force the proofs at all existing call sites to be redone.
pub(crate) fn kdfa32<H: HmacSha256Ctx>(
    key: &[u8],
    label: &[u8],
    u: &[u8],
    v: &[u8],
) -> (r: [u8; SHA256_LEN])
    ensures
        r@ =~= spec_kdfa32(key@, label@, u@, v@),
{
    let mut h = H::with_key(key);

    let counter = be32_arr(1);
    let bits = be32_arr(256);

    h.update(array_as_slice(&counter));
    h.update(label);
    h.update(u);
    h.update(v);
    h.update(array_as_slice(&bits));

    proof {
        assert(h.absorbed() =~= spec_kdfa_msg(label@, u@, v@, 256));
    }

    h.finish()
}

} // verus!