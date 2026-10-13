pub(crate) const ACCESS_VALID: u8 = 0x80;
pub(crate) const ACCESS_ACTIVE_LOCALITY: u8 = 0x20;
pub const ACCESS_REQUEST_PENDING: u8 = 0x04;
pub(crate) const ACCESS_REQUEST_USE: u8 = 0x02;
pub(crate) const STS_VALID: u8 = 0x80;
pub(crate) const STS_COMMAND_READY: u8 = 0x40;
pub(crate) const STS_GO: u8 = 0x20;
pub(crate) const STS_DATA_AVAIL: u8 = 0x10;
pub(crate) const STS_DATA_EXPECT: u8 = 0x08;
pub const STS_RESPONSE_RETRY: u8 = 0x02;
/// Allowed locality value range.
pub const MAX_LOCALITY: u8 = 5;
pub(crate) fn reg_access(l: u8) -> u32 {
    (l as u32) * 4096u32
}
pub(crate) fn reg_sts(l: u8) -> u32 {
    0x0018u32 + (l as u32) * 4096u32
}
pub(crate) fn reg_data_fifo(l: u8) -> u32 {
    0x0024u32 + (l as u32) * 4096u32
}
pub fn reg_did_vid(l: u8) -> u32 {
    0x0F00u32 + (l as u32) * 4096u32
}
/// Single polling interval in milliseconds.
pub const POLL_INTERVAL_MS: u32 = 1;
/// Four timeout tiers defined by the specification, in milliseconds.
pub(crate) const TIMEOUT_A_MS: u32 = 750;
pub(crate) const TIMEOUT_B_MS: u32 = 30000;
pub const TIMEOUT_C_MS: u32 = 750;
pub const TIMEOUT_D_MS: u32 = 750;
/// Convert a millisecond timeout to a polling budget.
///
/// It always returns at least one: a loop with a zero budget that declares a timeout without reading a
/// single register is a configuration error, not a runtime race.
pub fn budget_of(timeout_ms: u32) -> u32 {
    let n = timeout_ms / POLL_INTERVAL_MS;
    if n == 0 {
        1
    } else {
        n
    }
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TisErr {
    /// Physical-layer error; the bus itself is broken, and retries are pointless.
    Phy,
    /// Polling budget exhausted.
    Timeout,
    /// Device state does not match the specification.
    Protocol,
    /// The peer declared a length shorter than a message header or beyond the receive buffer.
    BadLength,
}
