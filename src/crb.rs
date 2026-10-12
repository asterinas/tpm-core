// ===========================================================================
// 建模范围
// ===========================================================================
//
// 本层按 TCG PTP 的 CRB 2.0 控制区寄存器语义建模，只覆盖 memory-mapped /
// command-buffer 启动方式：命令触发为写 ctrl_start 的 INVOKE 位，完成为器件
// 自清该位。

// ===========================================================================
// 控制区寄存器偏移
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
// 寄存器位
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
// 缓冲区映射上界
// ===========================================================================

pub(crate) const CMD_BUF_CAP: usize = 4096;
pub(crate) const RSP_BUF_CAP: usize = 4096;

// ===========================================================================
// locality 取值范围
// ===========================================================================

pub const MAX_LOCALITY: u8 = 5;

// ===========================================================================
// 轮询预算
// ===========================================================================

pub const POLL_INTERVAL_MS: u32 = 1;

/// 握手类动作（locality、cmd_ready、go_idle）的超时。
pub const TIMEOUT_C_MS: u32 = 750;

/// 命令执行完成的超时。
pub(crate) const TIMEOUT_LONG_MS: u32 = 4000;

/// 把毫秒超时折算成轮询次数，至少返回 1。
#[inline]
pub fn budget_of(timeout_ms: u32) -> u32 {
    let n = timeout_ms / POLL_INTERVAL_MS;
    if n == 0 { 1 } else { n }
}

// ===========================================================================
// 错误
// ===========================================================================

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CrbErr {
    /// 物理层报错。总线本身出了问题。
    Phy,
    /// 轮询预算耗尽。
    Timeout,
    /// 器件状态与规范不符。
    Protocol,
    /// 命令或响应长度非法。
    BadLength,
}
