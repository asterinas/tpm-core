use crate::{cursor::Cursor, msg::TPM_HEADER_LEN, phy::TisPhy, tis::*};

pub struct Tis<P: TisPhy> {
    pub phy: P,
    /// Locality number used by this driver.
    pub locality: u8,
    /// Whether locality has been acquired and not yet returned.
    ///
    /// This is the only persistent state in this layer. Keeping it separate rather than reading the device
    /// every time is because the property we need to prove is “did the driver forget to return locality?”,
    /// which belongs to the local side and cannot be inferred from the device.
    pub held: bool,
}
impl<P: TisPhy> Tis<P> {
    fn status(&mut self) -> Result<u8, TisErr> {
        let addr = reg_sts(self.locality);
        self.phy.read8(addr)
    }
    /// Poll the status register until all bits in `mask` are set.
    ///
    /// The budget is the polling count, and `decreases` uses it directly — this is the entire benefit of
    /// moving the timeout from the time domain to the count domain: termination does not require any
    /// assumptions about clocks.
    fn wait_status(&mut self, mask: u8, budget: u32) -> Result<u8, TisErr> {
        let mut left = budget;
        while left > 0 {
            let s = self.status()?;
            if (s & mask) == mask {
                return Ok(s);
            }
            self.phy.delay();
            left -= 1;
        }
        Err(TisErr::Timeout)
    }
    /// Read how many bytes can be moved continuously in this round.
    ///
    /// The return value is guaranteed to be non-zero. A zero value means the device is not ready yet; in
    /// that case it keeps polling or times out here instead of returning a “transferred zero bytes” success —
    /// that would cause the upper transfer loop to spin forever, and no timeout budget would catch it.
    fn burstcount(&mut self, budget: u32) -> Result<u16, TisErr> {
        let mut left = budget;
        while left > 0 {
            let addr = reg_sts(self.locality);
            let v = self.phy.read32(addr)?;
            let b = ((v >> 8u32) & 0xFFFFu32) as u16;
            if b >= 1 {
                return Ok(b);
            }
            self.phy.delay();
            left -= 1;
        }
        Err(TisErr::Timeout)
    }
    /// Whether the device has already granted locality to this side.
    ///
    /// All three bits matter: `ACTIVE` alone is not enough; `VALID` must also be set to indicate the
    /// register contents are valid, and `REQUEST_USE` must already be cleared to show the request has been
    /// processed. Missing any bit in a race scenario would misclassify “request is still being processed” as
    /// “already granted”.
    fn check_locality(&mut self) -> Result<bool, TisErr> {
        let addr = reg_access(self.locality);
        let a = self.phy.read8(addr)?;
        let want = ACCESS_ACTIVE_LOCALITY | ACCESS_VALID;
        let mask = want | ACCESS_REQUEST_USE;
        Ok((a & mask) == want)
    }
    /// Request locality.
    ///
    /// On failure it guarantees no ownership is held — if a partially failed request leaves the flag as
    /// “held,” the subsequent release would free a resource that was never acquired.
    pub fn request_locality(&mut self, budget: u32) -> Result<(), TisErr> {
        if self.check_locality()? {
            self.held = true;
            return Ok(());
        }
        let addr = reg_access(self.locality);
        self.phy.write8(addr, ACCESS_REQUEST_USE)?;
        let mut left = budget;
        while left > 0 {
            if self.check_locality()? {
                self.held = true;
                return Ok(());
            }
            self.phy.delay();
            left -= 1;
        }
        Err(TisErr::Timeout)
    }
    /// Return locality.
    ///
    /// Regardless of whether the register write succeeds, the local held flag must be cleared. If the write
    /// fails, the bus is already broken; leaving the flag as “held” would make the driver think it owns the
    /// resource forever and prevent it from issuing the next command — a recoverable bus fault would become
    /// a permanent functional loss.
    pub fn relinquish_locality(&mut self) {
        let addr = reg_access(self.locality);
        let _ = self.phy.write8(addr, ACCESS_ACTIVE_LOCALITY);
        self.held = false;
    }
    /// Feed a command into the data FIFO.
    ///
    /// On success, the FIFO receives exactly the command itself — no more, no less, in the same order. On
    /// failure, the FIFO is definitely cleared and no half-command is left behind: if a half-command remains
    /// in the device, the next send would assemble a packet that nobody ever wrote.
    pub fn send_data(&mut self, cmd: &[u8], len: usize) -> Result<(), TisErr> {
        self.send_data_inner(cmd, len).inspect_err(|_| {
            let sts_addr = reg_sts(self.locality);
            self.phy.reset_fifo(sts_addr);
        })?;
        Ok(())
    }
    fn send_data_inner(&mut self, cmd: &[u8], len: usize) -> Result<(), TisErr> {
        let sts_addr = reg_sts(self.locality);
        let fifo_addr = reg_data_fifo(self.locality);
        let s0 = self.status()?;
        if (s0 & STS_COMMAND_READY) == 0 {
            self.phy.reset_fifo(sts_addr);
            self.wait_status(STS_COMMAND_READY, budget_of(TIMEOUT_B_MS))?;
        }
        let last = len - 1;
        let mut count: usize = 0;
        while count < last {
            let b = self.burstcount(budget_of(TIMEOUT_A_MS))?;
            let rem = last - count;
            let bs = b as usize;
            let n = if bs < rem { bs } else { rem };
            self.phy.write_fifo(fifo_addr, cmd, count, n)?;
            let next = count.checked_add(n).ok_or(TisErr::Protocol)?;
            count = next;
            self.wait_status(STS_VALID, budget_of(TIMEOUT_C_MS))?;
            let s1 = self.status()?;
            if (s1 & STS_DATA_EXPECT) == 0 {
                return Err(TisErr::Protocol);
            }
        }
        self.phy.write_fifo(fifo_addr, cmd, count, 1)?;
        self.wait_status(STS_VALID, budget_of(TIMEOUT_C_MS))?;
        let s2 = self.status()?;
        if (s2 & STS_DATA_EXPECT) != 0 {
            return Err(TisErr::Protocol);
        }
        Ok(())
    }
    /// Read `count` bytes from the FIFO into `out[off..]`.
    fn recv_data(&mut self, out: &mut [u8], off: usize, count: usize) -> Result<(), TisErr> {
        let fifo_addr = reg_data_fifo(self.locality);
        let mut got: usize = 0;
        while got < count {
            self.wait_status(STS_DATA_AVAIL | STS_VALID, budget_of(TIMEOUT_C_MS))?;
            let b = self.burstcount(budget_of(TIMEOUT_A_MS))?;
            let rem = count - got;
            let bs = b as usize;
            let n = if bs < rem { bs } else { rem };
            self.phy.read_fifo(fifo_addr, out, off + got, n)?;
            let next = got.checked_add(n).ok_or(TisErr::Protocol)?;
            got = next;
        }
        Ok(())
    }
    /// Receive a full response and return its length.
    ///
    /// The return value is also the **entry condition for the next layer’s decoder**: on success, the
    /// `out[0..n]` length field matches `n`, which means the packet-layer format is valid. The decoding
    /// layer therefore does not need to re-check its length, and the two layers are welded together on the
    /// understanding of “how long a response is” by this postcondition.
    pub fn recv(&mut self, out: &mut [u8]) -> Result<usize, TisErr> {
        self.recv_data(out, 0, TPM_HEADER_LEN)?;
        let mut c = Cursor::at(2);
        let expected = c.read_be32(&*out).ok_or(TisErr::BadLength)?;
        let n = expected as usize;
        if n < TPM_HEADER_LEN {
            return Err(TisErr::BadLength);
        }
        if n > out.len() {
            return Err(TisErr::BadLength);
        }
        self.recv_data(out, TPM_HEADER_LEN, n - TPM_HEADER_LEN)?;
        self.wait_status(STS_VALID, budget_of(TIMEOUT_C_MS))?;
        let s = self.status()?;
        if (s & STS_DATA_AVAIL) != 0 {
            return Err(TisErr::Protocol);
        }
        Ok(n)
    }
    /// Send a command and receive a response.
    ///
    /// **There is only one return site for locality, and it is not inside any conditional branch.** After the
    /// request is made, all potentially failing actions are moved into an internal function, making the
    /// release of locality an unconditional cleanup statement — as a result, “every path exits with locality
    /// released” does not need to be checked path by path; it is directly encoded in the control flow. This is
    /// the one place where the layer is intentionally restructured for verifiability.
    ///
    /// `exec_budget` is the upper bound on the polling count used to wait for `STS_DATA_AVAIL`, supplied by
    /// the caller according to the command code (see [`crate::xfer::poll_budget`]). Different commands can
    /// differ by two orders of magnitude in execution time; only a command-specific budget lets us satisfy
    /// both “fast commands time out quickly” and “slow commands are not falsely reported as timed out.”
    pub fn transmit(
        &mut self,
        cmd: &[u8],
        len: usize,
        out: &mut [u8],
        exec_budget: u32,
    ) -> Result<usize, TisErr> {
        self.request_locality(budget_of(TIMEOUT_A_MS))?;
        let res = self.exchange(cmd, len, out, exec_budget);
        self.relinquish_locality();
        res
    }
    fn exchange(
        &mut self,
        cmd: &[u8],
        len: usize,
        out: &mut [u8],
        exec_budget: u32,
    ) -> Result<usize, TisErr> {
        let sts_addr = reg_sts(self.locality);
        self.phy.reset_fifo(sts_addr);
        self.send_data(cmd, len)?;
        self.phy.write8(sts_addr, STS_GO).inspect_err(|_| {
            self.phy.reset_fifo(sts_addr);
        })?;
        self.wait_status(STS_DATA_AVAIL | STS_VALID, exec_budget)
            .inspect_err(|_| {
                self.phy.reset_fifo(sts_addr);
            })?;
        let n = self.recv(out).inspect_err(|_| {
            self.phy.reset_fifo(sts_addr);
        })?;
        self.phy.reset_fifo(sts_addr);
        Ok(n)
    }
}
