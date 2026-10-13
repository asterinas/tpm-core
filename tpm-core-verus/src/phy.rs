use vstd::prelude::*;

use crate::tis::TisErr;

verus! {

// ===========================================================================
// Physical layer: the trust base
// ===========================================================================
//
// This is the only point of contact between the driver and the hardware. All implementations (memory-mapped, SPI, I2C) are provided with
// `#[verifier::external_body]`, so **every postcondition written below is an assumption,
// not a theorem**. They should be checked one by one against the interface specification, not reverse-engineered from an existing implementation.
//
// Made a generic parameter rather than a callback struct: the verifier does not support trait objects, and after monomorphization each backend's
// spec is independent, so one backend's assumptions are never silently inherited by another.
//
// Register access and data-port access are split into two groups of methods because their **side effects are entirely different**:
// the former is an idempotent read of a value, the latter advances the device's internal transfer state. Mixing them in one group would make
// "how many bytes were written" impossible to express in the spec.

pub trait TisPhy {
    /// The byte sequence written to the data port since the last data-port reset.
    ///
    /// It appears only in proofs and takes no space at runtime. Its sole purpose is to make "the bytes written by a send are exactly
    /// the command itself, no more and no less" a property that can be stated -- without this accumulator, the send
    /// path could only claim to have returned success, without saying what was actually put on the bus.
    spec fn fifo_written(&self) -> Seq<u8>;

    // -----------------------------------------------------------------------
    // Registers
    // -----------------------------------------------------------------------

    fn read8(&mut self, addr: u32) -> (r: Result<u8, TisErr>)
        ensures
            final(self).fifo_written() =~= old(self).fifo_written(),
    ;

    fn read32(&mut self, addr: u32) -> (r: Result<u32, TisErr>)
        ensures
            final(self).fifo_written() =~= old(self).fifo_written(),
    ;

    fn write8(&mut self, addr: u32, value: u8) -> (r: Result<(), TisErr>)
        ensures
            final(self).fifo_written() =~= old(self).fifo_written(),
    ;

    fn write32(&mut self, addr: u32, value: u32) -> (r: Result<(), TisErr>)
        ensures
            final(self).fifo_written() =~= old(self).fifo_written(),
    ;

    // -----------------------------------------------------------------------
    // Data port
    // -----------------------------------------------------------------------

    /// Read `n` bytes from the data port into `out[off..off + n]`.
    ///
    /// The content comes from the device and the spec cannot say what it is; it can only guarantee the **landing site is correct**:
    /// nothing outside the range is touched and the buffer length is unchanged. The responsibility for preventing out-of-bounds access therefore rests entirely on the caller
    /// supplying `off + n <= out.len()`, which is enforced by the type checker.
    fn read_fifo(&mut self, addr: u32, out: &mut [u8], off: usize, n: usize) -> (r: Result<
        (),
        TisErr,
    >)
        requires
            off + n <= old(out).len(),
        ensures
            final(out).len() == old(out).len(),
            final(self).fifo_written() =~= old(self).fifo_written(),
            forall|k: int|
                #![trigger final(out)@[k]]
                0 <= k < final(out).len() && (k < off || k >= off + n) ==> final(out)@[k]
                    == old(out)@[k],
    ;

    /// Write `data[off..off + n]` to the data port.
    ///
    /// On failure the device may already have consumed a prefix -- bus transfers are not atomic. The spec honestly says
    /// "the accumulator only grows" rather than "left untouched": the latter is false, and a false statement would invalidate
    /// all reasoning built on it. The caller must reset the data port on every failure path; after the reset, this imprecision
    /// no longer matters.
    fn write_fifo(&mut self, addr: u32, data: &[u8], off: usize, n: usize) -> (r: Result<
        (),
        TisErr,
    >)
        requires
            off + n <= data.len(),
        ensures
            r is Ok ==> final(self).fifo_written() =~= old(self).fifo_written() + data@.subrange(
                off as int,
                off + n,
            ),
            r is Err ==> old(self).fifo_written().is_prefix_of(final(self).fifo_written()),
    ;

    /// Abort the current command and clear the data port.
    ///
    /// Corresponds to writing the "command ready" bit. It is both the preparation step before sending and the cleanup
    /// step of every error path -- half a command left in the device is more dangerous than nothing written.
    ///
    /// No return value: a failed reset cannot be remedied, and all call sites are on error-handling paths, where one more error to handle
    /// would only make those paths easier to get wrong.
    fn reset_fifo(&mut self, addr: u32)
        ensures
            final(self).fifo_written() =~= Seq::<u8>::empty(),
    ;

    // -----------------------------------------------------------------------
    // Throttling
    // -----------------------------------------------------------------------

    /// The wait between two polls.
    ///
    /// The duration is decided by the implementation and does not appear in the spec -- this layer's timeouts are expressed as poll counts, so how long
    /// the wait takes affects only real elapsed time, not any proven property.
    fn delay(&mut self)
        ensures
            final(self).fifo_written() =~= old(self).fifo_written(),
    ;
}

} // verus!
