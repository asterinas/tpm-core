use vstd::prelude::*;

verus! {

/// Number of slots in the context table and the session table.
pub const SLOTS: usize = 3;

/// The handle type is distinguished by the most significant byte.
pub const HANDLE_TYPE_MASK: u32 = 0xFF00_0000;

pub const HT_HMAC_SESSION: u32 = 0x0200_0000;
pub const HT_POLICY_SESSION: u32 = 0x0300_0000;
pub const HT_TRANSIENT: u32 = 0x8000_0000;

/// Sentinel in the context table meaning "saved, not yet loaded".
pub const CTX_SAVED_SENTINEL: u32 = 0xFFFF_FFFF;

// ---------------------------------------------------------------------------
// Encoding spec
// ---------------------------------------------------------------------------

/// The virtual handle corresponding to slot `i`.
pub open spec fn vhandle_of(i: int) -> u32 {
    (0x80FF_FFFF - i) as u32
}

/// Recover the slot number from a virtual handle. For invalid input the returned value falls outside `[0, SLOTS)`.
pub open spec fn slot_of(v: u32) -> int {
    0xFF_FFFF - ((v & 0xFF_FFFF) as int)
}

/// Whether the handle belongs to the transient object handle space.
pub open spec fn is_transient(h: u32) -> bool {
    (h & HANDLE_TYPE_MASK) == HT_TRANSIENT
}

/// Whether the handle belongs to the session handle space (HMAC or policy). Session handles are **not virtualized**;
/// the table only registers them so that save / load / release can be handled uniformly.
pub open spec fn is_session(h: u32) -> bool {
    (h & HANDLE_TYPE_MASK) == HT_HMAC_SESSION
        || (h & HANDLE_TYPE_MASK) == HT_POLICY_SESSION
}

/// A physical handle that can be registered in the context table: neither the empty-slot marker nor the sentinel.
pub open spec fn valid_phandle(h: u32) -> bool {
    h != 0 && h != CTX_SAVED_SENTINEL
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// A virtual handle is always of transient type.
pub proof fn lemma_vhandle_is_transient(i: int)
    requires
        0 <= i < SLOTS,
    ensures
        is_transient(vhandle_of(i)),
{
    assert(SLOTS == 3);
    if i == 0 {
        assert(is_transient(0x80FF_FFFFu32)) by (bit_vector);
    } else if i == 1 {
        assert(is_transient(0x80FF_FFFEu32)) by (bit_vector);
    } else {
        assert(is_transient(0x80FF_FFFDu32)) by (bit_vector);
    }
}

/// Encoding / decoding round trip is consistent.
pub proof fn lemma_slot_roundtrip(i: int)
    requires
        0 <= i < SLOTS,
    ensures
        slot_of(vhandle_of(i)) == i,
{
    assert(SLOTS == 3);
    if i == 0 {
        assert((0x80FF_FFFFu32 & 0xFF_FFFFu32) == 0xFF_FFFFu32) by (bit_vector);
    } else if i == 1 {
        assert((0x80FF_FFFEu32 & 0xFF_FFFFu32) == 0xFF_FFFEu32) by (bit_vector);
    } else {
        assert((0x80FF_FFFDu32 & 0xFF_FFFFu32) == 0xFF_FFFDu32) by (bit_vector);
    }
}

/// **Arithmetic core of bijectivity**: the type bits and the slot bits together make up the whole handle,
/// so two transient handles with the same slot are necessarily equal.
///
/// The upper layer's "virtual-to-real mapping is injective" follows directly from it, with no further bit manipulation.
pub proof fn lemma_transient_slot_injective(a: u32, b: u32)
    requires
        is_transient(a),
        is_transient(b),
        slot_of(a) == slot_of(b),
    ensures
        a == b,
{
    assert((a & 0xFF_FFFFu32) == (b & 0xFF_FFFFu32));
    assert(
        ((a & 0xFF00_0000u32) == (b & 0xFF00_0000u32)
            && (a & 0x00FF_FFFFu32) == (b & 0x00FF_FFFFu32)) ==> a == b
    ) by (bit_vector);
}

// ---------------------------------------------------------------------------
// Executable versions
// ---------------------------------------------------------------------------

pub(crate) fn vhandle_of_exec(i: usize) -> (r: u32)
    requires
        i < SLOTS,
    ensures
        r == vhandle_of(i as int),
        is_transient(r),
{
    proof {
        lemma_vhandle_is_transient(i as int);
    }
    0x80FF_FFFFu32 - (i as u32)
}

/// Recover the slot number. Returns `usize`; the caller checks out-of-range with `< SLOTS`.
pub(crate) fn slot_of_exec(v: u32) -> (r: usize)
    ensures
        r as int == slot_of(v),
{
    assert((v & 0xFF_FFFFu32) <= 0xFF_FFFFu32) by (bit_vector);
    (0xFF_FFFFu32 - (v & 0xFF_FFFFu32)) as usize
}

pub fn is_transient_exec(h: u32) -> (r: bool)
    ensures
        r == is_transient(h),
{
    (h & HANDLE_TYPE_MASK) == HT_TRANSIENT
}

pub fn is_session_exec(h: u32) -> (r: bool)
    ensures
        r == is_session(h),
{
    let t = h & HANDLE_TYPE_MASK;
    t == HT_HMAC_SESSION || t == HT_POLICY_SESSION
}

pub fn valid_phandle_exec(h: u32) -> (r: bool)
    ensures
        r == valid_phandle(h),
{
    h != 0 && h != CTX_SAVED_SENTINEL
}

} // verus!
