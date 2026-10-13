use vstd::prelude::*;

use crate::crb::{CMD_BUF_CAP, CrbErr, RSP_BUF_CAP};

verus! {

// ===========================================================================
// Physical layer: the trust base
// ===========================================================================
//
// The only point of contact between the CRB and the hardware. Runtime semantics are guaranteed by the concrete backend.

pub trait CrbPhy {
    /// The byte sequence written to the command buffer since the last command-buffer write.
    ///
    /// Serves the same purpose as `TisPhy::fifo_written`: turns "how many bytes were successfully written" into
    /// a spec term that assertions can reference, to help record whole-block writes to the command buffer.
    spec fn cmd_written(&self) -> Seq<u8>;

    // -----------------------------------------------------------------------
    // Control-area registers
    // -----------------------------------------------------------------------

    fn read32(&mut self, reg: u32) -> (r: Result<u32, CrbErr>)
        ensures
            final(self).cmd_written() =~= old(self).cmd_written(),
    ;

    fn write32(&mut self, reg: u32, value: u32) -> (r: Result<(), CrbErr>)
        ensures
            final(self).cmd_written() =~= old(self).cmd_written(),
    ;

    // -----------------------------------------------------------------------
    // Command buffer
    // -----------------------------------------------------------------------

    /// Write data[0..n] as one block into the head of the command buffer.
    fn write_cmd(&mut self, data: &[u8], n: usize) -> (r: Result<(), CrbErr>)
        ensures
            r is Ok ==> final(self).cmd_written() =~= old(self).cmd_written() + data@.subrange(0, n as int),
            r is Err ==> old(self).cmd_written().is_prefix_of(final(self).cmd_written()),
    ;

    /// Barrier: ensures the command-buffer write is visible to the device before START.
    fn fence(&mut self)
        ensures
            final(self).cmd_written() =~= old(self).cmd_written(),
    ;

    // -----------------------------------------------------------------------
    // Response buffer
    // -----------------------------------------------------------------------

    /// Read n bytes from the response buffer at off and write them into out[off..off+n].
    fn read_rsp(&mut self, off: usize, out: &mut [u8], n: usize) -> (r: Result<(), CrbErr>)
        ensures
            final(self).cmd_written() =~= old(self).cmd_written(),
    ;

    // -----------------------------------------------------------------------
    // Throttling
    // -----------------------------------------------------------------------

    fn delay(&mut self)
        ensures
            final(self).cmd_written() =~= old(self).cmd_written(),
    ;
}

} // verus!

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
