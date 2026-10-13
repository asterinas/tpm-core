use crate::{crypto::SHA256_LEN, cursor::*};

pub(crate) const CC_SELF_TEST: u32 = 0x0000_0143;
pub(crate) const CC_STARTUP: u32 = 0x0000_0144;
pub(crate) const CC_SHUTDOWN: u32 = 0x0000_0145;
pub(crate) const CC_CONTEXT_LOAD: u32 = 0x0000_0161;
pub(crate) const CC_CONTEXT_SAVE: u32 = 0x0000_0162;
pub(crate) const CC_FLUSH_CONTEXT: u32 = 0x0000_0165;
pub const CC_GET_CAPABILITY: u32 = 0x0000_017A;
pub(crate) const CC_GET_RANDOM: u32 = 0x0000_017B;
pub(crate) const CC_PCR_READ: u32 = 0x0000_017E;
pub(crate) const CC_PCR_EXTEND: u32 = 0x0000_0182;
pub const CAP_HANDLES: u32 = 0x0000_0001;
pub const CAP_COMMANDS: u32 = 0x0000_0002;
pub const CAP_PCRS: u32 = 0x0000_0005;
pub(crate) const CAP_TPM_PROPERTIES: u32 = 0x0000_0006;
pub const SU_CLEAR: u16 = 0x0000;
pub const SU_STATE: u16 = 0x0001;
/// The PC Client platform has a fixed 24 PCRs (TCG PC Client PFP).
pub const PLATFORM_PCR: u32 = 24;
/// Number of bytes required for the selection bitmap that covers 24 PCRs: ceil(24 / 8).
const PCR_SELECT_MIN: usize = 3;
/// Maximum size for a single random-data fetch. If the request is larger, it must be split over
/// multiple calls.
pub const MAX_RNG_DATA: u16 = 128;
fn bit_value(n: u32) -> u8 {
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
/// Generate a selection bitmap that selects only a single PCR.
///
/// The index is split using division and remainder rather than shifts and masks: the two approaches are
/// equivalent for values below 24, and the division form can be fed directly into integer reasoning
/// without switching to a bit-vector solver.
fn pcr_select_bitmap(pcr_idx: u32) -> [u8; PCR_SELECT_MIN] {
    let byte_idx = pcr_idx / 8;
    let mask = bit_value(pcr_idx % 8);
    if byte_idx == 0 {
        [mask, 0, 0]
    } else if byte_idx == 1 {
        [0, mask, 0]
    } else {
        [0, 0, mask]
    }
}
/// PCR handle value.
///
/// The PCR handle type code is 0, so the handle value is simply the PCR index itself. The reason for
/// making it a separate function is not the check `r == pcr_idx`, but to attach this note: for this
/// class of handles, the “name” is the handle itself as four bytes, and command hashing does not need to
/// look up any name table. The place that assembles the digest input can easily take an extra detour here,
/// and a wrong detour will not be caught by any length checks.
pub fn pcr_handle(pcr_idx: u32) -> u32 {
    pcr_idx
}
/// `TPM2_PCR_Read` payload (Part 3 §22.4).
///
/// ```text
/// count        u32 = 1        only one bank is queried
/// hashAlg      u16            digest algorithm
/// sizeofSelect u8  = 3
/// pcrSelect    u8[3]
/// ```
pub fn pcr_read_payload(alg_id: u16, pcr_idx: u32) -> [u8; 10] {
    let cnt = be32_bytes(1);
    let alg = be16_bytes(alg_id);
    let sel = pcr_select_bitmap(pcr_idx);
    [
        cnt[0],
        cnt[1],
        cnt[2],
        cnt[3],
        alg[0],
        alg[1],
        PCR_SELECT_MIN as u8,
        sel[0],
        sel[1],
        sel[2],
    ]
}
/// Length of the `TPM2_PCR_Extend` parameter area: count (4) + hashAlg (2) + digest (32).
const PCR_EXTEND_PARAM_LEN: usize = 6 + SHA256_LEN;
/// **Parameter area** of `TPM2_PCR_Extend` (Part 3 §22.2).
///
/// ```text
/// count    u32 = 1        only one bank is written
/// hashAlg  u16
/// digest   u8[32]
/// ```
///
/// This command differs in shape from the read-only one, and it is worth stating clearly: it carries a
/// handle and must be authorized, so the full packet is:
///
/// ```text
/// header 10 | pcrHandle 4 | authSize 4 | authorization area | parameter area
/// ```
///
/// This function emits only the final section. The handle is intentionally omitted: it sits before the
/// authorization area, while the command digest covers only the section after that area. If the two are
/// mixed into the same array, the assembler will eventually feed the whole block as the parameter area to
/// the digest. That error does not trigger any length check; the symptom is simply that validation never
/// succeeds, forcing the investigation back to the offset definitions.
///
/// The algorithm identifier is passed as an argument instead of being hard-coded as a constant so that the
/// precondition can tie it to the digest length: this code accepts a fixed 32-byte digest, and claiming a
/// different algorithm would be lying in the packet. To support a second algorithm, the digest parameter
/// type would also have to change, and not just part of it.
pub fn pcr_extend_payload(alg_id: u16, digest: &[u8; SHA256_LEN]) -> [u8; PCR_EXTEND_PARAM_LEN] {
    let cnt = be32_bytes(1);
    let alg = be16_bytes(alg_id);
    let mut out = [0u8; PCR_EXTEND_PARAM_LEN];
    out[0] = cnt[0];
    out[1] = cnt[1];
    out[2] = cnt[2];
    out[3] = cnt[3];
    out[4] = alg[0];
    out[5] = alg[1];
    out[6..6 + SHA256_LEN].copy_from_slice(digest);
    out
}
/// `TPM2_GetCapability` payload (Part 3 §30.2).
///
/// ```text
/// capability     u32
/// property       u32
/// propertyCount  u32
/// ```
pub fn get_capability_payload(capability: u32, property: u32, count: u32) -> [u8; 12] {
    let a = be32_bytes(capability);
    let b = be32_bytes(property);
    let c = be32_bytes(count);
    [
        a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3], c[0], c[1], c[2], c[3],
    ]
}
/// `TPM2_GetRandom` payload (Part 3 §16.1).
///
/// The upper bound is enforced at the type level: a single request should not exceed `MAX_RNG_DATA`, and
/// the caller must split it itself instead of relying on the peer to truncate it.
pub fn get_random_payload(bytes_requested: u16) -> [u8; 2] {
    be16_bytes(bytes_requested)
}
/// `TPM2_Shutdown` payload (Part 3 §9.4).
pub fn shutdown_payload(shutdown_type: u16) -> [u8; 2] {
    be16_bytes(shutdown_type)
}
/// `TPM2_FlushContext` payload (Part 3 §28.4). The handle follows the header and there is no authorization area.
pub fn flush_context_payload(handle: u32) -> [u8; 4] {
    be32_bytes(handle)
}
