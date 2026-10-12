/// 上下文表与会话表的槽位数。
pub const SLOTS: usize = 3;
/// 句柄类型由最高字节区分。
const HANDLE_TYPE_MASK: u32 = 0xFF00_0000;
const HT_HMAC_SESSION: u32 = 0x0200_0000;
const HT_POLICY_SESSION: u32 = 0x0300_0000;
const HT_TRANSIENT: u32 = 0x8000_0000;
/// 上下文表里表示「已保存、尚未装载」的哨兵值。
pub(crate) const CTX_SAVED_SENTINEL: u32 = 0xFFFF_FFFF;
pub(crate) fn vhandle_of_exec(i: usize) -> u32 {
    0x80FF_FFFFu32 - (i as u32)
}
/// 反解槽位号。返回 `usize`，越界由调用方用 `< SLOTS` 判断。
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
