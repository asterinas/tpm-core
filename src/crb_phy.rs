use crate::crb::{CMD_BUF_CAP, CrbErr, RSP_BUF_CAP};

// ===========================================================================
// 物理层：信任基
// ===========================================================================
//
// CRB 与硬件之间的唯一接触面。运行时语义由具体后端实现保证。

pub trait CrbPhy {
    // -----------------------------------------------------------------------
    // 控制区寄存器
    // -----------------------------------------------------------------------

    fn read32(&mut self, reg: u32) -> Result<u32, CrbErr>;

    fn write32(&mut self, reg: u32, value: u32) -> Result<(), CrbErr>;

    // -----------------------------------------------------------------------
    // 命令缓冲
    // -----------------------------------------------------------------------

    /// 把 data[0..n] 整块写进命令缓冲头部。
    fn write_cmd(&mut self, data: &[u8], n: usize) -> Result<(), CrbErr>;

    /// 屏障：确保命令缓冲写入在 START 之前对器件可见。
    fn fence(&mut self);

    // -----------------------------------------------------------------------
    // 响应缓冲
    // -----------------------------------------------------------------------

    /// 从响应缓冲 off 处读取 n 字节，写入 out[off..off+n]。
    fn read_rsp(&mut self, off: usize, out: &mut [u8], n: usize) -> Result<(), CrbErr>;

    // -----------------------------------------------------------------------
    // 节流
    // -----------------------------------------------------------------------

    fn delay(&mut self);
}

#[inline]
pub(crate) fn check_cmd_bounds(data: &[u8], n: usize) -> Result<(), CrbErr> {
    if n > data.len() || n > CMD_BUF_CAP {
        Err(CrbErr::BadLength)
    } else {
        Ok(())
    }
}

#[inline]
pub(crate) fn check_rsp_bounds(off: usize, out_len: usize, n: usize) -> Result<(), CrbErr> {
    let end = off.checked_add(n).ok_or(CrbErr::BadLength)?;
    if end > out_len || end > RSP_BUF_CAP {
        Err(CrbErr::BadLength)
    } else {
        Ok(())
    }
}
