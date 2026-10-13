//! Type wrappers for message header fields.
//!
//! yufan: **Currently only `buf` uses `TpmTag`; `TpmRc` has no callers yet.** The assembly and parsing layers
//! operate directly on raw `u16` / `u32`, stating the value constraints of tags and return codes in the
//! pre/postconditions of functions rather than going through this module.
//!
//! It is kept because of `TpmRc`: return codes and command codes share the same offset in the message header,
//! and if both are carried in the same raw `u32`, swapping them goes undetected by any check. To tighten this,
//! the layers should switch to this newtype, rather than deleting it.
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Command / response tag
// ---------------------------------------------------------------------------

/// The tag field of the TPM message header.
#[derive(Clone, Copy)]
pub enum TpmTag {
    /// `TPM_TAG_RQU_COMMAND` = 193 (TPM 1.2 command)
    RquCommand,
    /// `TPM2_ST_NO_SESSIONS` = 0x8001
    Tpm2NoSessions,
    /// `TPM2_ST_SESSIONS` = 0x8002
    Tpm2Sessions,
    /// 0 -- explicitly allowed by `tpm_buf_reset()` (for buffers not yet finalized)
    Null,
}

impl TpmTag {
    pub open spec fn spec_code(self) -> u16 {
        match self {
            TpmTag::RquCommand => 193u16,
            TpmTag::Tpm2NoSessions => 0x8001u16,
            TpmTag::Tpm2Sessions => 0x8002u16,
            TpmTag::Null => 0u16,
        }
    }

    pub fn code(self) -> (r: u16)
        ensures
            r == self.spec_code(),
    {
        match self {
            TpmTag::RquCommand => 193u16,
            TpmTag::Tpm2NoSessions => 0x8001u16,
            TpmTag::Tpm2Sessions => 0x8002u16,
            TpmTag::Null => 0u16,
        }
    }

    /// Parse the on-wire bytes.
    pub fn from_code(c: u16) -> (r: Option<TpmTag>)
        ensures
            match r {
                Some(t) => t.spec_code() == c,
                None => c != 193u16 && c != 0x8001u16 && c != 0x8002u16 && c != 0u16,
            },
    {
        if c == 193u16 {
            Some(TpmTag::RquCommand)
        } else if c == 0x8001u16 {
            Some(TpmTag::Tpm2NoSessions)
        } else if c == 0x8002u16 {
            Some(TpmTag::Tpm2Sessions)
        } else if c == 0u16 {
            Some(TpmTag::Null)
        } else {
            None
        }
    }

    /// Whether this tag belongs to the TPM2 message family.
    pub open spec fn is_tpm2(self) -> bool {
        match self {
            TpmTag::Tpm2NoSessions => true,
            TpmTag::Tpm2Sessions => true,
            _ => false,
        }
    }
}

// ---------------------------------------------------------------------------
// Return code
// ---------------------------------------------------------------------------

/// TPM return code (the 3rd field of the header, sharing the same offset as the ordinal).
/// A newtype rather than an enum: the return-code space is open (including vendor-defined codes), so exhaustive enumeration is impractical,
/// but at least it is no longer mixed with the ordinal in the same raw `u32`.
#[derive(Clone, Copy)]
pub struct TpmRc(pub u32);

impl TpmRc {
    pub const SUCCESS: u32 = 0x0000_0000;
    /// `TPM_WARN_RETRY`
    pub const WARN_RETRY: u32 = 0x0000_0800;
    /// `TPM_WARN_DOING_SELFTEST`
    pub const WARN_DOING_SELFTEST: u32 = 0x0000_0802;
    /// `TPM_ERR_DEACTIVATED`
    pub const ERR_DEACTIVATED: u32 = 0x0000_0006;
    /// `TPM_ERR_DISABLED`
    pub const ERR_DISABLED: u32 = 0x0000_0007;
    /// `TPM_ERR_FAILEDSELFTEST`
    pub const ERR_FAILEDSELFTEST: u32 = 0x0000_001C;
    /// `TPM_ERR_INVALID_POSTINIT`
    pub const ERR_INVALID_POSTINIT: u32 = 38;

    pub open spec fn spec_is_success(self) -> bool {
        self.0 == 0u32
    }

    pub fn is_success(self) -> (r: bool)
        ensures
            r == self.spec_is_success(),
    {
        self.0 == 0u32
    }
}

// ---------------------------------------------------------------------------
// Size constants (from tpm.h)
// ---------------------------------------------------------------------------

/// `TPM_BUFSIZE`
pub const TPM_BUFSIZE: usize = 4096;
/// `TPM2_SPACE_BUFFER_SIZE`
pub const TPM2_SPACE_BUFFER_SIZE: usize = 16384;
/// `TPM_MAX_RNG_DATA`
pub const TPM_MAX_RNG_DATA: usize = 128;
/// `TPM_RETRY`
pub const TPM_RETRY: u32 = 50;

} // verus!
