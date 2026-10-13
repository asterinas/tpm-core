use vstd::prelude::*;
use vstd::array::*;

use crate::cursor::*;
use crate::msg::ParseError;

verus! {

// ===================== Static capacity =====================

/// Upper bound on the number of PCR banks allocated at the same time.
pub const MAX_PCR_BANKS: usize = 5;

/// Upper bound on an acceptable `sizeofSelect`. The PC Client platform has a fixed 24 PCRs (3 bytes);
/// some slack is left here, but an arbitrary length supplied by the peer is never accepted.
const PCR_SELECT_MAX: usize = 8;

/// Upper bound on digest length (SHA-512).
pub const MAX_DIGEST_SIZE: usize = 64;

// ===================== Algorithm identifiers (Part 2 §6.3) =====================

const ALG_SHA1: u16 = 0x0004;
pub const ALG_SHA256: u16 = 0x000B;
const ALG_SHA384: u16 = 0x000C;
const ALG_SHA512: u16 = 0x000D;
const ALG_SM3_256: u16 = 0x0012;

/// Digest length of a known algorithm.
///
/// Returning `0` means "this implementation does not recognize the algorithm" -- not an error, only that the length has to be probed
/// separately (reading PCR 0 once is enough). Treating an unknown algorithm as an error would make the driver refuse to work on devices with a newly enabled
/// digest algorithm, which costs too much.
fn digest_size_of(alg_id: u16) -> (r: u16)
    ensures
        r as usize <= MAX_DIGEST_SIZE,
{
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

// ===================== Capability query: a single property =====================

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
/// A zero count is a legal response (a peer in firmware-upgrade mode answers like this), but the caller gets
/// no value, so it is reported as "no data" rather than returning a made-up zero.
pub(crate) fn parse_tpm_property(body: &[u8]) -> (r: Result<u32, ParseError>) {
    let mut c = Cursor::new();

    c.read_u8(body).ok_or(ParseError::Truncated)?;
    c.read_be32(body).ok_or(ParseError::Truncated)?;
    let count = c.read_be32(body).ok_or(ParseError::Truncated)?;
    if count == 0 {
        return Err(ParseError::Unsupported);
    }
    // Take only the first entry; the property identifier itself is useless to the caller, so skip it
    c.read_be32(body).ok_or(ParseError::Truncated)?;
    c.read_be32(body).ok_or(ParseError::Truncated)
}

// ===================== PCR allocation =====================

/// Table of allocated PCR banks.
///
/// `digest_sizes[i] == 0` means this implementation does not recognize the bank's algorithm, and the length is yet to be probed.
pub struct PcrBanks {
    pub algs: [u16; 5],
    pub digest_sizes: [u16; 5],
    pub count: usize,
}

impl PcrBanks {
    pub open spec fn wf(self) -> bool {
        self.count <= MAX_PCR_BANKS
    }

    pub fn empty() -> (r: PcrBanks)
        ensures
            r.count == 0,
            r.wf(),
    {
        PcrBanks { algs: [0, 0, 0, 0, 0], digest_sizes: [0, 0, 0, 0, 0], count: 0 }
    }
}

/// Parse `TPM2_GetCapability(TPM_CAP_PCRS)` to determine which banks are actually allocated.
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
/// A bank counts as allocated only if its select bitmap has a non-zero bit; an all-zero bitmap means the algorithm
/// is merely supported, not enabled.
///
/// The three upper bounds are the whole safety argument of this function: `count <= MAX_PCR_BANKS` bounds the number of loop
/// rounds, `sizeofSelect <= PCR_SELECT_MAX` bounds the step of each round, and the cursor's
/// `read_bytes` bounds the bitmap read -- all three are checked before use.
pub fn parse_pcr_allocation(body: &[u8]) -> (r: Result<PcrBanks, ParseError>)
    ensures
        r matches Ok(b) ==> b.wf(),
{
    let mut c = Cursor::new();

    c.read_u8(body).ok_or(ParseError::Truncated)?;
    c.read_be32(body).ok_or(ParseError::Truncated)?;
    let count = c.read_be32(body).ok_or(ParseError::Truncated)?;

    if count > MAX_PCR_BANKS as u32 {
        return Err(ParseError::Capacity);
    }

    let mut banks = PcrBanks::empty();

    for i in 0..count
        invariant
            count <= MAX_PCR_BANKS as u32,
            banks.count <= i,
            banks.wf(),
            c.wf(body@.len()),
    {
        let alg_id = c.read_be16(body).ok_or(ParseError::Truncated)?;
        let sel_size = c.read_u8(body).ok_or(ParseError::Truncated)?;
        if sel_size as usize > PCR_SELECT_MAX {
            return Err(ParseError::Malformed);
        }
        let select = c.read_bytes(body, sel_size as usize).ok_or(ParseError::Truncated)?;

        if any_nonzero(select) {
            // banks.count <= i < count <= MAX_PCR_BANKS, so the index is necessarily valid
            banks.algs[banks.count] = alg_id;
            banks.digest_sizes[banks.count] = digest_size_of(alg_id);
            banks.count += 1;
        }

    }

    Ok(banks)
}

// ===================== PCR read =====================

/// The result of one PCR read: algorithm identifier + digest bytes.
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
/// Only the shape "one selection, one digest" is accepted -- this is exactly the response corresponding to the request built on the command side.
/// Extra parts the peer sends are not guessed at; they are rejected outright.
pub fn parse_pcr_read(body: &[u8]) -> (r: Result<PcrValue<'_>, ParseError>)
    ensures
        r matches Ok(v) ==> v.digest@.len() <= MAX_DIGEST_SIZE,
{
    let mut c = Cursor::new();

    // pcrUpdateCounter: not of interest at this layer
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

    let digest = c.read_bytes(body, digest_size as usize).ok_or(ParseError::Truncated)?;

    Ok(PcrValue { alg_id, digest })
}

// ===================== Random numbers =====================

/// Parse a `TPM2_GetRandom` response (Part 3 §16.1): one `TPM2B_DIGEST`.
///
/// Returns a borrow rather than a copy. The caller trims to however many bytes it wants up to `max`; this layer only guarantees
/// that the returned slice really lies within the payload and is no longer than the value the peer declared.
pub fn parse_random(body: &[u8], max: u16) -> (r: Result<&[u8], ParseError>)
    ensures
        r matches Ok(s) ==> s@.len() <= max,
{
    let mut c = Cursor::new();

    let size = c.read_be16(body).ok_or(ParseError::Truncated)?;
    // The peer giving too much is likewise abnormal: it means it did not respect the upper limit in the request
    if size > max {
        return Err(ParseError::Malformed);
    }

    c.read_bytes(body, size as usize).ok_or(ParseError::Truncated)
}

} // verus!
