use vstd::prelude::*;

verus! {

// ===========================================================================
// Modeling scope
// ===========================================================================
//
// This layer is modeled on the register semantics of the TCG PC Client Platform TPM Profile, not on the actual behavior of any specific
// device. The following three kinds of compatibility switches are **explicitly excluded**:
//
// - Devices that do not set `DATA_EXPECT`. Excluding them makes the `DATA_EXPECT` check during writing
//   unconditional, which is stricter than letting them through.
// - Clock-gating switches. They belong to the platform southbridge rather than this interface; mixing them in would make the register semantics inconsistent.
// - Devices whose `STS_VALID` needs a retry. They merge "timeout" and "try again" into one return code,
//   while this layer requires the timeout budget to be consumed monotonically.
//
// Exclusion does not mean these devices do not exist. To support them, they should be modeled separately outside this layer, each spelling out
// the specific clauses in which it deviates from the specification -- mixing compromises into the main state machine would make the spec describe two mutually
// contradictory pieces of hardware at once.

// ===========================================================================
// Access register bits
// ===========================================================================

pub(crate) const ACCESS_VALID: u8 = 0x80;
pub(crate) const ACCESS_ACTIVE_LOCALITY: u8 = 0x20;
pub const ACCESS_REQUEST_PENDING: u8 = 0x04;
pub(crate) const ACCESS_REQUEST_USE: u8 = 0x02;

// ===========================================================================
// Status register bits
// ===========================================================================

pub(crate) const STS_VALID: u8 = 0x80;
pub(crate) const STS_COMMAND_READY: u8 = 0x40;
pub(crate) const STS_GO: u8 = 0x20;
pub(crate) const STS_DATA_AVAIL: u8 = 0x10;
pub(crate) const STS_DATA_EXPECT: u8 = 0x08;
pub const STS_RESPONSE_RETRY: u8 = 0x02;

// ===========================================================================
// Addresses
// ===========================================================================

/// Range of locality values.
pub const MAX_LOCALITY: u8 = 5;

/// The locality number occupies the address from bit 12 upward.
pub open spec fn spec_reg(base: u32, l: u8) -> u32 {
    (base as int + (l as int) * 4096) as u32
}

pub(crate) fn reg_access(l: u8) -> (r: u32)
    requires
        l < MAX_LOCALITY,
    ensures
        r == spec_reg(0x0000, l),
{
    (l as u32) * 4096u32
}

pub(crate) fn reg_sts(l: u8) -> (r: u32)
    requires
        l < MAX_LOCALITY,
    ensures
        r == spec_reg(0x0018, l),
{
    0x0018u32 + (l as u32) * 4096u32
}

pub(crate) fn reg_data_fifo(l: u8) -> (r: u32)
    requires
        l < MAX_LOCALITY,
    ensures
        r == spec_reg(0x0024, l),
{
    0x0024u32 + (l as u32) * 4096u32
}

pub fn reg_did_vid(l: u8) -> (r: u32)
    requires
        l < MAX_LOCALITY,
    ensures
        r == spec_reg(0x0F00, l),
{
    0x0F00u32 + (l as u32) * 4096u32
}

// ===========================================================================
// Polling budget
// ===========================================================================
//
// The original specification expresses timeouts in milliseconds, while the implementation is "read the register, sleep a little, read again". Converting
// timeouts into a **poll count** rather than staying in the time domain has two benefits:
//
// - Every polling loop can use the remaining count as its `decreases`, so termination is directly provable. The time domain lacks this
//   property -- `jiffies` wraps around, and "not yet due" can be forever true on clock wraparound.
// - The budget is an explicit parameter, so each call site must state how long it is willing to wait, instead of reusing a global default.
//
// The conversion is done once at construction: budget = timeout in ms / ms per poll interval, rounded up and
// at least one.

/// Single poll interval (ms).
pub const POLL_INTERVAL_MS: u32 = 1;

/// The four timeout classes given by the specification (ms).
pub(crate) const TIMEOUT_A_MS: u32 = 750;
pub(crate) const TIMEOUT_B_MS: u32 = 30000;
pub const TIMEOUT_C_MS: u32 = 750;
pub const TIMEOUT_D_MS: u32 = 750;

/// Convert a millisecond timeout into a poll count.
///
/// Returns at least one: a loop with a zero budget would declare a timeout without reading a single register, which is a configuration error
/// and should not show up as an occasional runtime failure.
pub fn budget_of(timeout_ms: u32) -> (r: u32)
    ensures
        r >= 1,
{
    let n = timeout_ms / POLL_INTERVAL_MS;
    if n == 0 {
        1
    } else {
        n
    }
}

// ===========================================================================
// Errors
// ===========================================================================

#[derive(Clone, Copy, PartialEq, Eq, Structural, Debug)]
pub enum TisErr {
    /// Physical-layer error. The bus itself has a problem; retrying is pointless.
    Phy,
    /// Polling budget exhausted.
    Timeout,
    /// Device state does not match the specification.
    Protocol,
    /// The length declared by the peer is smaller than a message header, or exceeds the receive buffer.
    BadLength,
}

} // verus!
