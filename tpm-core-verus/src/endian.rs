use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Encoding direction: integer -> byte sequence
// ---------------------------------------------------------------------------

/// The `i`-th byte of `v` in big-endian order (i ∈ [0,2)).
pub open spec fn be16_byte(v: u16, i: int) -> u8 {
    if i == 0 {
        ((v >> 8) & 0xff) as u8
    } else {
        (v & 0xff) as u8
    }
}

/// The `i`-th byte of `v` in big-endian order (i ∈ [0,4)).
pub open spec fn be32_byte(v: u32, i: int) -> u8 {
    if i == 0 {
        ((v >> 24) & 0xff) as u8
    } else if i == 1 {
        ((v >> 16) & 0xff) as u8
    } else if i == 2 {
        ((v >> 8) & 0xff) as u8
    } else {
        (v & 0xff) as u8
    }
}

/// Spec for `u16 -> [u8; 2]`. Uses `Seq::new` rather than `seq![..]`,
/// so that `be16_bytes(v)[k] == be16_byte(v, k)` follows directly from the vstd axioms.
pub open spec fn be16_bytes(v: u16) -> Seq<u8> {
    Seq::new(2, |i: int| be16_byte(v, i))
}

/// Spec for `u32 -> [u8; 4]`.
pub open spec fn be32_bytes(v: u32) -> Seq<u8> {
    Seq::new(4, |i: int| be32_byte(v, i))
}

// ---------------------------------------------------------------------------
// Decoding direction: bytes -> integer
// ---------------------------------------------------------------------------

pub open spec fn be16_of(b0: u8, b1: u8) -> u16 {
    ((b0 as u16) << 8) | (b1 as u16)
}

pub open spec fn be32_of(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32)
}

// ---------------------------------------------------------------------------
// Round-trip consistency (one of the invariants to prove in guide phase 1: u32 -> be bytes -> u32 is the identity)
// ---------------------------------------------------------------------------

pub proof fn lemma_be16_roundtrip(v: u16)
    ensures
        be16_of(be16_byte(v, 0), be16_byte(v, 1)) == v,
{
    let b0 = ((v >> 8) & 0xff) as u8;
    let b1 = (v & 0xff) as u8;
    assert(((b0 as u16) << 8) | (b1 as u16) == v) by (bit_vector)
        requires
            b0 == ((v >> 8) & 0xff) as u8,
            b1 == (v & 0xff) as u8,
    ;
}

pub proof fn lemma_be32_roundtrip(v: u32)
    ensures
        be32_of(be32_byte(v, 0), be32_byte(v, 1), be32_byte(v, 2), be32_byte(v, 3)) == v,
{
    let b0 = ((v >> 24) & 0xff) as u8;
    let b1 = ((v >> 16) & 0xff) as u8;
    let b2 = ((v >> 8) & 0xff) as u8;
    let b3 = (v & 0xff) as u8;
    assert(((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32) == v)
        by (bit_vector)
        requires
            b0 == ((v >> 24) & 0xff) as u8,
            b1 == ((v >> 16) & 0xff) as u8,
            b2 == ((v >> 8) & 0xff) as u8,
            b3 == (v & 0xff) as u8,
    ;
}

/// The reverse direction: decode first, then encode, recovering the original bytes.
/// Used by the parsing path (response decoding in phase 2).
pub proof fn lemma_be32_of_roundtrip(b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        be32_byte(be32_of(b0, b1, b2, b3), 0) == b0,
        be32_byte(be32_of(b0, b1, b2, b3), 1) == b1,
        be32_byte(be32_of(b0, b1, b2, b3), 2) == b2,
        be32_byte(be32_of(b0, b1, b2, b3), 3) == b3,
{
    let v = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    assert(((v >> 24) & 0xff) as u8 == b0) by (bit_vector)
        requires v == ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    assert(((v >> 16) & 0xff) as u8 == b1) by (bit_vector)
        requires v == ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    assert(((v >> 8) & 0xff) as u8 == b2) by (bit_vector)
        requires v == ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    assert((v & 0xff) as u8 == b3) by (bit_vector)
        requires v == ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
}

// ---------------------------------------------------------------------------
// Exec side: call the standard library's big-endian conversion directly
//
// The signature of `from_be_bytes` carries a const generic expression, so Verus cannot write
// an `assume_specification` for it; `external_body` is therefore used here to pin the contract to the spec;
// the only thing trusted is the semantics of the standard library's big-endian conversion itself.
// ---------------------------------------------------------------------------

#[verifier::external_body]
pub(crate) fn be16_of_exec(b0: u8, b1: u8) -> (r: u16)
    ensures
        r == be16_of(b0, b1),
{
    u16::from_be_bytes([b0, b1])
}

#[verifier::external_body]
pub(crate) fn be32_of_exec(b0: u8, b1: u8, b2: u8, b3: u8) -> (r: u32)
    ensures
        r == be32_of(b0, b1, b2, b3),
{
    u32::from_be_bytes([b0, b1, b2, b3])
}

} // verus!
