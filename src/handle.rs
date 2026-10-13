/// Number of slots in the context table and session table.
pub const SLOTS: usize = 3;
/// Handle type is distinguished by the high byte.
const HANDLE_TYPE_MASK: u32 = 0xFF00_0000;
const HT_HMAC_SESSION: u32 = 0x0200_0000;
const HT_POLICY_SESSION: u32 = 0x0300_0000;
const HT_TRANSIENT: u32 = 0x8000_0000;
/// Sentinel value in the context table meaning “saved but not loaded yet”.
pub(crate) const CTX_SAVED_SENTINEL: u32 = 0xFFFF_FFFF;
pub(crate) fn vhandle_of_exec(i: usize) -> u32 {
    0x80FF_FFFFu32 - (i as u32)
}
/// Reverse-map a slot index. Returns `usize`; callers check bounds with `< SLOTS`.
pub(crate) fn slot_of_exec(v: u32) -> usize {
    (0xFF_FFFFu32 - (v & 0xFF_FFFFu32)) as usize
}
pub fn is_transient_exec(h: u32) -> bool {
    (h & HANDLE_TYPE_MASK) == HT_TRANSIENT
}
pub fn is_session_exec(h: u32) -> bool {
    let t = h & HANDLE_TYPE_MASK;
    t == HT_HMAC_SESSION || t == HT_POLICY_SESSION
}
pub fn valid_phandle_exec(h: u32) -> bool {
    h != 0 && h != CTX_SAVED_SENTINEL
}
