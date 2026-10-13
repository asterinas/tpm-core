use crate::crb::{CrbErr, CMD_BUF_CAP, RSP_BUF_CAP};

// ===========================================================================
// Physical layer: trust boundary
// ===========================================================================
//
// This is the only contact surface between CRB and the hardware. The runtime semantics are guaranteed by
// the concrete backend implementation.

pub trait CrbPhy {
    // -----------------------------------------------------------------------
    // Control registers
    // -----------------------------------------------------------------------

    fn read32(&mut self, reg: u32) -> Result<u32, CrbErr>;

    fn write32(&mut self, reg: u32, value: u32) -> Result<(), CrbErr>;

    // -----------------------------------------------------------------------
    // Command buffer
    // -----------------------------------------------------------------------

    /// Write the entire `data[0..n]` block into the command buffer header area.
    fn write_cmd(&mut self, data: &[u8], n: usize) -> Result<(), CrbErr>;

    /// Barrier: ensure the command-buffer write is visible to the device before START.
    fn fence(&mut self);

    // -----------------------------------------------------------------------
    // Response buffer
    // -----------------------------------------------------------------------

    /// Read `n` bytes from the response buffer at offset `off` into `out[off..off + n]`.
    fn read_rsp(&mut self, off: usize, out: &mut [u8], n: usize) -> Result<(), CrbErr>;

    // -----------------------------------------------------------------------
    // Throttling
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
