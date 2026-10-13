use crate::{cursor::*, msg::ParseError};

/// Upper bound on the number of PCR banks that can be allocated simultaneously.
const MAX_PCR_BANKS: usize = 5;
/// Accepted upper bound for `sizeofSelect`. The PC Client platform has a fixed 24 PCRs (3 bytes), and
/// this leaves some margin while rejecting arbitrary lengths from the peer.
const PCR_SELECT_MAX: usize = 8;
/// Upper bound on digest length (SHA-512).
const MAX_DIGEST_SIZE: usize = 64;
const ALG_SHA1: u16 = 0x0004;
const ALG_SHA256: u16 = 0x000B;
const ALG_SHA384: u16 = 0x000C;
const ALG_SHA512: u16 = 0x000D;
const ALG_SM3_256: u16 = 0x0012;
/// Length of a known algorithm’s digest.
///
/// Returning `0` means “this implementation does not recognize the algorithm” — not an error, but a
/// signal that the length must be probed separately (by reading PCR 0 once). Treating an unknown
/// algorithm as an error would cause the driver to refuse to work on devices that enable new digest
/// algorithms, which is too costly.
fn digest_size_of(alg_id: u16) -> u16 {
    if alg_id == ALG_SHA1 {
        20
    } else if alg_id == ALG_SHA256 {
        32
    } else if alg_id == ALG_SHA384 {
        48
    } else if alg_id == ALG_SHA512 {
        64
    } else if alg_id == ALG_SM3_256 {
        32
    } else {
        0
    }
}
/// Parse the return value of `TPM2_GetCapability(TPM_CAP_TPM_PROPERTIES)`.
///
/// Payload layout (Part 3 §30.2):
///
/// ```text
/// moreData      u8
/// capability    u32
/// count         u32
/// [property u32, value u32] * count
/// ```
///
/// A count of zero is a legal response (for example, when the peer is in firmware-upgrade mode), but the
/// caller cannot use any value from it, so this is treated as “no data” rather than returning a fabricated
/// zero.
pub(crate) fn parse_tpm_property(body: &[u8]) -> Result<u32, ParseError> {
    let mut c = Cursor::new();
    c.read_u8(body).ok_or(ParseError::Truncated)?;
    c.read_be32(body).ok_or(ParseError::Truncated)?;
    let count = c.read_be32(body).ok_or(ParseError::Truncated)?;
    if count == 0 {
        return Err(ParseError::Unsupported);
    }
    c.read_be32(body).ok_or(ParseError::Truncated)?;
    c.read_be32(body).ok_or(ParseError::Truncated)
}
/// Table of allocated PCR banks.
///
/// `digest_sizes[i] == 0` means that the implementation does not recognize the algorithm for that bank,
/// and the length must be probed separately.
pub struct PcrBanks {
    pub algs: [u16; 5],
    pub digest_sizes: [u16; 5],
    pub count: usize,
}
impl PcrBanks {
    pub fn empty() -> PcrBanks {
        PcrBanks {
            algs: [0, 0, 0, 0, 0],
            digest_sizes: [0, 0, 0, 0, 0],
            count: 0,
        }
    }
}
/// Parse `TPM2_GetCapability(TPM_CAP_PCRS)` and determine which banks are actually allocated.
///
/// Payload layout:
///
/// ```text
/// moreData   u8
/// capability u32          == TPM_CAP_PCRS
/// count      u32          number of candidate banks
/// [hashAlg u16, sizeofSelect u8, pcrSelect u8[sizeofSelect]] * count
/// ```
///
/// A bank counts as allocated only if its selection bitmap contains at least one non-zero bit; a bitmap of
/// all zeros means the algorithm is supported but not active.
///
/// Three upper bounds constitute the entire safety argument of this function: `count <= MAX_PCR_BANKS`
/// limits the loop iterations, `sizeofSelect <= PCR_SELECT_MAX` limits the per-iteration stride, and the
/// cursor’s `read_bytes` checks the bitmap value — all three are validated before use.
pub fn parse_pcr_allocation(body: &[u8]) -> Result<PcrBanks, ParseError> {
    let mut c = Cursor::new();
    c.read_u8(body).ok_or(ParseError::Truncated)?;
    c.read_be32(body).ok_or(ParseError::Truncated)?;
    let count = c.read_be32(body).ok_or(ParseError::Truncated)?;
    if count > MAX_PCR_BANKS as u32 {
        return Err(ParseError::Capacity);
    }
    let mut banks = PcrBanks::empty();
    for _ in 0..count {
        let alg_id = c.read_be16(body).ok_or(ParseError::Truncated)?;
        let sel_size = c.read_u8(body).ok_or(ParseError::Truncated)?;
        if sel_size as usize > PCR_SELECT_MAX {
            return Err(ParseError::Malformed);
        }
        let select = c
            .read_bytes(body, sel_size as usize)
            .ok_or(ParseError::Truncated)?;
        if any_nonzero(select) {
            banks.algs[banks.count] = alg_id;
            banks.digest_sizes[banks.count] = digest_size_of(alg_id);
            banks.count += 1;
        }
    }
    Ok(banks)
}
/// Result of a single PCR read: algorithm ID + digest bytes.
pub struct PcrValue<'a> {
    pub alg_id: u16,
    pub digest: &'a [u8],
}
/// Parse a `TPM2_PCR_Read` response (Part 3 §22.4).
///
/// Payload layout:
///
/// ```text
/// pcrUpdateCounter u32
/// pcrSelectionOut  count u32, [hashAlg u16, sizeofSelect u8, pcrSelect[]] * count
/// pcrValues        count u32, [size u16, buffer[size]] * count
/// ```
///
/// Only the “one selection, one digest” form is accepted — this matches the request constructed by the
/// command side. Any extra response content from the peer is not guessed, and is rejected outright.
pub fn parse_pcr_read(body: &[u8]) -> Result<PcrValue<'_>, ParseError> {
    let mut c = Cursor::new();
    c.read_be32(body).ok_or(ParseError::Truncated)?;
    let sel_count = c.read_be32(body).ok_or(ParseError::Truncated)?;
    if sel_count != 1 {
        return Err(ParseError::Unsupported);
    }
    let alg_id = c.read_be16(body).ok_or(ParseError::Truncated)?;
    let sel_size = c.read_u8(body).ok_or(ParseError::Truncated)?;
    if sel_size as usize > PCR_SELECT_MAX {
        return Err(ParseError::Malformed);
    }
    if !c.skip(body, sel_size as usize) {
        return Err(ParseError::Truncated);
    }
    let digest_count = c.read_be32(body).ok_or(ParseError::Truncated)?;
    if digest_count != 1 {
        return Err(ParseError::Unsupported);
    }
    let digest_size = c.read_be16(body).ok_or(ParseError::Truncated)?;
    if digest_size as usize > MAX_DIGEST_SIZE {
        return Err(ParseError::Malformed);
    }
    let digest = c
        .read_bytes(body, digest_size as usize)
        .ok_or(ParseError::Truncated)?;
    Ok(PcrValue { alg_id, digest })
}
/// Parse a `TPM2_GetRandom` response (Part 3 §16.1): a single `TPM2B_DIGEST`.
///
/// This returns a borrowed slice rather than copying. The caller decides how many bytes to trim using
/// `max`; this layer only guarantees that the returned slice is within the payload and does not exceed the
/// length declared by the peer.
pub fn parse_random(body: &[u8], max: u16) -> Result<&[u8], ParseError> {
    let mut c = Cursor::new();
    let size = c.read_be16(body).ok_or(ParseError::Truncated)?;
    if size > max {
        return Err(ParseError::Malformed);
    }
    c.read_bytes(body, size as usize)
        .ok_or(ParseError::Truncated)
}
