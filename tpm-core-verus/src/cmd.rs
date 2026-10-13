use vstd::prelude::*;
use vstd::array::*;

use crate::crypto::SHA256_LEN;
use crate::cursor::*;
use crate::rsp::ALG_SHA256;

verus! {

// ===================== Command codes (TPM 2.0 Part 2 §6.5.2) =====================

pub(crate) const CC_SELF_TEST: u32 = 0x0000_0143;
pub(crate) const CC_STARTUP: u32 = 0x0000_0144;
pub(crate) const CC_SHUTDOWN: u32 = 0x0000_0145;
pub const CC_CONTEXT_LOAD: u32 = 0x0000_0161;
pub(crate) const CC_CONTEXT_SAVE: u32 = 0x0000_0162;
pub const CC_FLUSH_CONTEXT: u32 = 0x0000_0165;
pub const CC_GET_CAPABILITY: u32 = 0x0000_017A;
pub(crate) const CC_GET_RANDOM: u32 = 0x0000_017B;
pub(crate) const CC_PCR_READ: u32 = 0x0000_017E;
pub(crate) const CC_PCR_EXTEND: u32 = 0x0000_0182;

// ===================== Capability categories (Part 2 §6.12) =====================

pub const CAP_HANDLES: u32 = 0x0000_0001;
pub const CAP_COMMANDS: u32 = 0x0000_0002;
pub const CAP_PCRS: u32 = 0x0000_0005;
pub(crate) const CAP_TPM_PROPERTIES: u32 = 0x0000_0006;

// ===================== Shutdown types (Part 2 §6.9) =====================

pub const SU_CLEAR: u16 = 0x0000;
pub const SU_STATE: u16 = 0x0001;

// ===================== Platform parameters =====================

/// The PC Client platform has a fixed 24 PCRs (TCG PC Client PFP).
pub const PLATFORM_PCR: u32 = 24;

/// Number of select-bitmap bytes needed to cover 24 PCRs: ceil(24 / 8).
pub const PCR_SELECT_MIN: usize = 3;

/// Upper limit for a single random-number request. Anything beyond it must be fetched in several requests.
pub const MAX_RNG_DATA: u16 = 128;

// ===================== PCR select bitmap =====================

/// The mask value for bit number `n` (0..8).
///
/// Written as branches rather than shifts: shifts need the bit-vector solver, while here the value domain has only
/// eight elements, so enumerating them directly is both obvious and adds no burden to the proof.
pub open spec fn spec_bit_value(n: u32) -> u8
    recommends
        n < 8,
{
    if n == 0 {
        1u8
    } else if n == 1 {
        2u8
    } else if n == 2 {
        4u8
    } else if n == 3 {
        8u8
    } else if n == 4 {
        16u8
    } else if n == 5 {
        32u8
    } else if n == 6 {
        64u8
    } else {
        128u8
    }
}

fn bit_value(n: u32) -> (r: u8)
    requires
        n < 8,
    ensures
        r == spec_bit_value(n),
        r != 0,
{
    if n == 0 {
        1
    } else if n == 1 {
        2
    } else if n == 2 {
        4
    } else if n == 3 {
        8
    } else if n == 4 {
        16
    } else if n == 5 {
        32
    } else if n == 6 {
        64
    } else {
        128
    }
}

/// Generate a select bitmap that selects a single PCR only.
///
/// The index is split with division and remainder rather than shift and mask: the two are fully equivalent below 24,
/// and the division form goes straight into integer reasoning without switching to the bit-vector solver.
fn pcr_select_bitmap(pcr_idx: u32) -> (r: [u8; PCR_SELECT_MIN])
    requires
        pcr_idx < PLATFORM_PCR,
    ensures
        r@.len() == PCR_SELECT_MIN,
        // the byte containing the selected bit is non-zero
        r@[(pcr_idx / 8) as int] == spec_bit_value(pcr_idx % 8),
        r@[(pcr_idx / 8) as int] != 0,
        // all other bytes are zero: exactly one PCR is selected in the bitmap
        forall|k: int| 0 <= k < PCR_SELECT_MIN && k != pcr_idx / 8 ==> r@[k] == 0,
{
    let byte_idx = pcr_idx / 8;
    let mask = bit_value(pcr_idx % 8);

    // pcr_idx < 24 implies byte_idx < 3, so the three branches are exhaustive
    if byte_idx == 0 {
        [mask, 0, 0]
    } else if byte_idx == 1 {
        [0, mask, 0]
    } else {
        [0, 0, mask]
    }
}

// ===================== PCR handles =====================

/// The handle value of a PCR.
///
/// The handle type number of a PCR is 0, so the handle value is the PCR index itself. It is a separate function not
/// for the sake of `r == pcr_idx`, but to carry this comment: the "name" of this class of handle
/// is the handle's own four bytes, so computing the command digest needs no name-table lookup -- the place that writes the digest
/// input is prone to take an extra detour here, and a wrong detour would be caught by no length check.
pub fn pcr_handle(pcr_idx: u32) -> (r: u32)
    requires
        pcr_idx < PLATFORM_PCR,
    ensures
        r == pcr_idx,
        r < PLATFORM_PCR,
{
    pcr_idx
}

// ===================== Per-command payloads =====================

/// `TPM2_PCR_Read` payload (Part 3 §22.4).
///
/// ```text
/// count        u32 = 1        ask about a single bank only
/// hashAlg      u16            digest algorithm
/// sizeofSelect u8  = 3
/// pcrSelect    u8[3]
/// ```
pub fn pcr_read_payload(alg_id: u16, pcr_idx: u32) -> (r: [u8; 10])
    requires
        pcr_idx < PLATFORM_PCR,
    ensures
        r@.len() == 10,
        spec_be32_at(r@, 0) == 1u32,
        spec_be16_at(r@, 4) == alg_id,
        r@[6] == PCR_SELECT_MIN as u8,
        r@[7 + (pcr_idx / 8) as int] == spec_bit_value(pcr_idx % 8),
{
    let cnt = be32_bytes(1);
    let alg = be16_bytes(alg_id);
    let sel = pcr_select_bitmap(pcr_idx);

    [cnt[0], cnt[1], cnt[2], cnt[3], alg[0], alg[1], PCR_SELECT_MIN as u8, sel[0], sel[1], sel[2]]
}

/// Length of the parameter area of `TPM2_PCR_Extend`: count(4) + hashAlg(2) + digest(32).
pub const PCR_EXTEND_PARM_LEN: usize = 6 + SHA256_LEN;

/// The **parameter area** of `TPM2_PCR_Extend` (Part 3 §22.2).
///
/// ```text
/// count    u32 = 1        write a single bank only
/// hashAlg  u16
/// digest   u8[32]
/// ```
///
/// This command differs in shape from the read-only one and deserves an explanation: it carries a handle and must be authorized,
/// so the whole message is
///
/// ```text
/// header 10 | pcrHandle 4 | authSize 4 | authorization area | parameter area
/// ```
///
/// This function produces only the last segment. Leaving the handle out is deliberate: the handle sits **before** the authorization area,
/// while the command digest covers the segment **after** it. If the two were mixed in one array, the assembler
/// would sooner or later feed the whole block to the digest as the parameter area -- an error that triggers no length check, whose only symptom is
/// that verification never passes, and tracing it means walking all the way back to the offset definitions.
///
/// The algorithm identifier is an input rather than a hard-coded constant so that the precondition can tie it to the digest length:
/// this takes a fixed 32 bytes, and claiming another algorithm would be lying in the message. To support a
/// second algorithm, the type of the digest parameter must change at the same time; changing only half is not possible.
pub fn pcr_extend_payload(alg_id: u16, digest: &[u8; SHA256_LEN]) -> (r: [u8; PCR_EXTEND_PARM_LEN])
    requires
        alg_id == ALG_SHA256,
    ensures
        r@.len() == PCR_EXTEND_PARM_LEN,
        spec_be32_at(r@, 0) == 1u32,
        spec_be16_at(r@, 4) == alg_id,
        forall|k: int| #![trigger r@[6 + k]] 0 <= k < SHA256_LEN ==> r@[6 + k] == digest@[k],
{
    let cnt = be32_bytes(1);
    let alg = be16_bytes(alg_id);

    let mut out = [0u8; PCR_EXTEND_PARM_LEN];
    out[0] = cnt[0];
    out[1] = cnt[1];
    out[2] = cnt[2];
    out[3] = cnt[3];
    out[4] = alg[0];
    out[5] = alg[1];

    // The loop writes only offset 6 onward; the two prefix fields are kept as they are. The invariant is stated per byte rather than
    // carrying the two big-endian equations along: that the prefix is unchanged is a byte-by-byte fact, and making the solver
    // unfold the big-endian definition again on every round is unnecessary; unfolding it once at the end is enough.
    for i in 0..SHA256_LEN
        invariant
            cnt@.len() == 4,
            alg@.len() == 2,
            spec_be32_at(cnt@, 0) == 1u32,
            spec_be16_at(alg@, 0) == alg_id,
            out@.len() == PCR_EXTEND_PARM_LEN,
            out@[0] == cnt@[0],
            out@[1] == cnt@[1],
            out@[2] == cnt@[2],
            out@[3] == cnt@[3],
            out@[4] == alg@[0],
            out@[5] == alg@[1],
            forall|k: int| #![trigger out@[6 + k]] 0 <= k < i ==> out@[6 + k] == digest@[k],
    {
        out[6 + i] = digest[i];
    }

    proof {
        assert(spec_be32_at(out@, 0) == spec_be32_at(cnt@, 0));
        assert(spec_be16_at(out@, 4) == spec_be16_at(alg@, 0));
    }

    out
}

/// `TPM2_GetCapability` payload (Part 3 §30.2).
///
/// ```text
/// capability     u32
/// property       u32
/// propertyCount  u32
/// ```
pub fn get_capability_payload(capability: u32, property: u32, count: u32) -> (r: [u8; 12])
    ensures
        r@.len() == 12,
        spec_be32_at(r@, 0) == capability,
        spec_be32_at(r@, 4) == property,
        spec_be32_at(r@, 8) == count,
{
    let a = be32_bytes(capability);
    let b = be32_bytes(property);
    let c = be32_bytes(count);
    [a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3], c[0], c[1], c[2], c[3]]
}

/// `TPM2_GetRandom` payload (Part 3 §16.1).
///
/// The upper limit is enforced at the type level: no more than `MAX_RNG_DATA` can be requested at once,
/// and the caller must batch the request itself rather than hope the peer truncates.
pub fn get_random_payload(bytes_requested: u16) -> (r: [u8; 2])
    requires
        bytes_requested > 0,
        bytes_requested <= MAX_RNG_DATA,
    ensures
        r@.len() == 2,
        spec_be16_at(r@, 0) == bytes_requested,
{
    be16_bytes(bytes_requested)
}

/// `TPM2_Shutdown` payload (Part 3 §9.4).
pub fn shutdown_payload(shutdown_type: u16) -> (r: [u8; 2])
    requires
        shutdown_type == SU_CLEAR || shutdown_type == SU_STATE,
    ensures
        r@.len() == 2,
        spec_be16_at(r@, 0) == shutdown_type,
{
    be16_bytes(shutdown_type)
}

/// `TPM2_FlushContext` payload (Part 3 §28.4). The handle follows the header; there is no authorization area.
pub fn flush_context_payload(handle: u32) -> (r: [u8; 4])
    ensures
        r@.len() == 4,
        spec_be32_at(r@, 0) == handle,
{
    be32_bytes(handle)
}

} // verus!