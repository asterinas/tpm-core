use vstd::prelude::*;

verus! {

// ===========================================================================
// Modeling scope
// ===========================================================================
//
// This layer models the semantics of the CRB 2.0 control-area registers per TCG PTP, covering only the memory-mapped /
// command-buffer start method: a command is triggered by writing the INVOKE bit of ctrl_start, and completion is the device
// clearing that bit itself.

// ===========================================================================
// Control-area register offsets
// ===========================================================================

pub(crate) const REG_LOC_STATE: u32 = 0x0000;
pub(crate) const REG_LOC_CTRL: u32 = 0x0008;
pub(crate) const REG_CTRL_REQ: u32 = 0x0040;
pub(crate) const REG_CTRL_STS: u32 = 0x0044;
pub(crate) const REG_CTRL_CANCEL: u32 = 0x0048;
pub(crate) const REG_CTRL_START: u32 = 0x004C;
pub(crate) const REG_CTRL_CMD_SIZE: u32 = 0x0058;
pub const REG_CTRL_RSP_SIZE: u32 = 0x0064;

// ===========================================================================
// Register bits
// ===========================================================================

pub(crate) const LOC_CTRL_REQUEST: u32 = 0x01;
pub(crate) const LOC_CTRL_RELINQUISH: u32 = 0x02;

pub(crate) const LOC_STATE_ASSIGNED: u32 = 0x02;
pub(crate) const LOC_STATE_VALID: u32 = 0x80;

pub(crate) const CTRL_REQ_CMD_READY: u32 = 0x01;
pub(crate) const CTRL_REQ_GO_IDLE: u32 = 0x02;

pub(crate) const CTRL_STS_ERROR: u32 = 0x01;

pub(crate) const CTRL_START_INVOKE: u32 = 0x01;

pub(crate) const CTRL_CANCEL_CLEAR: u32 = 0x00;

// ===========================================================================
// Upper bound of the buffer mapping
// ===========================================================================

pub(crate) const CMD_BUF_CAP: usize = 4096;
pub(crate) const RSP_BUF_CAP: usize = 4096;

// ===========================================================================
// Range of locality values
// ===========================================================================

pub const MAX_LOCALITY: u8 = 5;

// ===========================================================================
// Polling budget
// ===========================================================================

pub const POLL_INTERVAL_MS: u32 = 1;

/// Timeout for handshake-type actions (locality, cmd_ready, go_idle).
pub const TIMEOUT_C_MS: u32 = 750;

/// Timeout for command execution to complete.
pub(crate) const TIMEOUT_LONG_MS: u32 = 4000;

/// Convert a millisecond timeout into a poll count, returning at least 1.
#[inline]
pub fn budget_of(timeout_ms: u32) -> u32 {
    let n = timeout_ms / POLL_INTERVAL_MS;
    if n == 0 { 1 } else { n }
}

// ===========================================================================
// Errors
// ===========================================================================

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CrbErr {
    /// Physical-layer error. The bus itself has a problem.
    Phy,
    /// Polling budget exhausted.
    Timeout,
    /// Device state does not match the specification.
    Protocol,
    /// Illegal command or response length.
    BadLength,
}

} // verus!
