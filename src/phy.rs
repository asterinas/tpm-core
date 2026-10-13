use crate::tis::TisErr;

pub trait TisPhy {
    fn read8(&mut self, addr: u32) -> Result<u8, TisErr>;
    fn read32(&mut self, addr: u32) -> Result<u32, TisErr>;
    fn write8(&mut self, addr: u32, value: u8) -> Result<(), TisErr>;
    fn write32(&mut self, addr: u32, value: u32) -> Result<(), TisErr>;
    /// Read `n` bytes from the data FIFO into `out[off..off + n]`.
    ///
    /// The bytes come from the device, and the specification does not say what they are; it only
    /// guarantees that the destination is correct: bytes outside the range remain untouched and the buffer
    /// length is unchanged. Therefore the caller bears the responsibility to ensure `off + n <= out.len()`,
    /// and that is enforced by type checking.
    fn read_fifo(&mut self, addr: u32, out: &mut [u8], off: usize, n: usize) -> Result<(), TisErr>;
    /// Write `data[off..off + n]` into the data FIFO.
    ///
    /// On failure, the device may already have consumed a prefix — bus transmission is not atomic. The
    /// specification writes this as “the accumulated count only increases” rather than “the data remains
    /// unchanged”: the latter is false, and pretending otherwise invalidates all reasoning built on it.
    /// The caller must reset the FIFO on any failure path; after reset, the inexactness of this point is
    /// irrelevant.
    fn write_fifo(&mut self, addr: u32, data: &[u8], off: usize, n: usize) -> Result<(), TisErr>;
    /// Abort the current command and clear the data FIFO.
    ///
    /// This corresponds to writing the “command ready” bit. It is both the preparation action before
    /// sending and the cleanup action for every error path — leaving half a command in the device is more
    /// dangerous than writing nothing at all.
    ///
    /// There is no return value: reset failure is unrecoverable, and all call sites are already on error
    /// handling paths; adding one more error to handle only makes those paths easier to miss.
    fn reset_fifo(&mut self, addr: u32);
    /// Wait between two polling iterations.
    ///
    /// The duration is implementation-defined and not present in the specification — this layer models
    /// timeouts in terms of polling counts, and the actual waiting time only affects wall-clock latency, not
    /// any proven property.
    fn delay(&mut self);
}
