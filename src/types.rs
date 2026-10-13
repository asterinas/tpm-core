//! Type wrappers for message-header fields.
//!
//! yufan: **At the moment only `buf` uses `TpmTag` and `TpmRc`; callers do not yet use them.** The
//! assembly and parsing layers currently operate directly on raw `u16` / `u32` values, writing the tag and
//! return-code constraints into the function preconditions/postconditions instead of routing through here.
//!
//! This is kept for the `TpmRc` case: the return code and command code share the same offset in the header,
//! and if the two are mixed up with the same bare `u32`, no check will catch it. If we tighten things up,
//! the right change is for the layers to use this newtype rather than deleting it.

/// Tag field in the TPM message header.
#[derive(Clone, Copy)]
pub enum TpmTag {
    /// `TPM_TAG_RQU_COMMAND` = 193 (TPM 1.2 command)
    RquCommand,
    /// `TPM2_ST_NO_SESSIONS` = 0x8001
    Tpm2NoSessions,
    /// `TPM2_ST_SESSIONS` = 0x8002
    Tpm2Sessions,
    /// 0 — explicitly allowed by `tpm_buf_reset()` for an unfinalized buffer
    Null,
}
impl TpmTag {
    pub fn code(self) -> u16 {
        match self {
            TpmTag::RquCommand => 193u16,
            TpmTag::Tpm2NoSessions => 0x8001u16,
            TpmTag::Tpm2Sessions => 0x8002u16,
            TpmTag::Null => 0u16,
        }
    }
    /// Parse a value from the wire.
    pub fn from_code(c: u16) -> Option<TpmTag> {
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
}
/// TPM return code (the third field in the header, sharing one offset with the ordinal).
/// A newtype rather than an enum: the return-code space is open (including vendor-defined values), so an
/// exhaustive enum is unrealistic, but at least it no longer mixes with the ordinal in the same bare
/// `u32`.
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
    pub fn is_success(self) -> bool {
        self.0 == 0u32
    }
}
/// `TPM_BUFSIZE`
pub const TPM_BUFSIZE: usize = 4096;
/// `TPM2_SPACE_BUFFER_SIZE`
pub const TPM2_SPACE_BUFFER_SIZE: usize = 16384;
/// `TPM_MAX_RNG_DATA`
pub const TPM_MAX_RNG_DATA: usize = 128;
/// `TPM_RETRY`
pub const TPM_RETRY: u32 = 50;
