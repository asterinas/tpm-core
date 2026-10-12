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
/// locality 取值范围。
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
/// 单次轮询间隔（毫秒）。
pub const POLL_INTERVAL_MS: u32 = 1;
/// 规范给出的四档超时（毫秒）。
pub(crate) const TIMEOUT_A_MS: u32 = 750;
pub(crate) const TIMEOUT_B_MS: u32 = 30000;
pub const TIMEOUT_C_MS: u32 = 750;
pub const TIMEOUT_D_MS: u32 = 750;
/// 把毫秒超时折算成轮询次数。
///
/// 至少返回一次：预算为零的循环一次寄存器都不读就宣告超时，那是配置错误，
/// 不该表现为运行时的偶发失败。
pub fn budget_of(timeout_ms: u32) -> u32 {
    let n = timeout_ms / POLL_INTERVAL_MS;
    if n == 0 { 1 } else { n }
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TisErr {
    /// 物理层报错。总线本身出了问题，重试没有意义。
    Phy,
    /// 轮询预算耗尽。
    Timeout,
    /// 器件状态与规范不符。
    Protocol,
    /// 对端声明的长度小于一个报文头，或超出接收缓冲区。
    BadLength,
}
