use vstd::prelude::*;

use crate::cursor::Cursor;
#[cfg(verus_keep_ghost)]
use crate::cursor::spec_be32_at;
use crate::msg::TPM_HEADER_LEN;
use crate::phy::TisPhy;
use crate::tis::*;

verus! {

// ===========================================================================
// Driver state
// ===========================================================================
//
// Only the polling path is kept. The interrupt path is not in this layer: the interrupt handler and the command path access the same set of registers
// concurrently, proving that would require introducing a concurrency framework at several times the cost; and this interface already comes with a complete polling
// fallback, so cutting interrupts loses no functionality, only a little throughput.
//
// Concurrency is likewise not in this layer. All methods require an exclusive `&mut Self` reference, and locking is done by the unverified glue
// layer. Thus "only one command is in flight at a time" is not a property that needs proving, but a fact
// given directly by the type system.

pub struct Tis<P: TisPhy> {
    pub phy: P,
    /// The locality number used by this driver.
    pub locality: u8,
    /// Whether a locality has been acquired and not yet relinquished.
    ///
    /// This is the only persistent state of this layer. It is listed separately rather than read from the device each time, because the property to be proved
    /// is "whether the driver itself dropped the relinquish action", which is this side's own bookkeeping and cannot be read from the device.
    pub held: bool,
}

impl<P: TisPhy> Tis<P> {
    pub open spec fn wf(self) -> bool {
        self.locality < MAX_LOCALITY
    }

    /// Does not hold the locality.
    pub open spec fn quiescent(self) -> bool {
        !self.held
    }

    // =======================================================================
    // Register reads
    // =======================================================================

    fn status(&mut self) -> (r: Result<u8, TisErr>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).held == old(self).held,
            final(self).locality == old(self).locality,
            final(self).phy.fifo_written() =~= old(self).phy.fifo_written(),
    {
        let addr = reg_sts(self.locality);
        self.phy.read8(addr)
    }

    /// Poll the status register until all bits in `mask` are set.
    ///
    /// The budget is a poll count, and `decreases` uses it directly -- this is the whole benefit of moving timeouts from the time domain to the count domain:
    /// termination needs no assumption about clocks.
    fn wait_status(&mut self, mask: u8, budget: u32) -> (r: Result<u8, TisErr>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).held == old(self).held,
            final(self).locality == old(self).locality,
            final(self).phy.fifo_written() =~= old(self).phy.fifo_written(),
            r matches Ok(s) ==> (s & mask) == mask,
    {
        let mut left = budget;
        while left > 0
            invariant
                self.wf(),
                self.held == old(self).held,
                self.locality == old(self).locality,
                self.phy.fifo_written() =~= old(self).phy.fifo_written(),
            decreases left,
        {
            let s = self.status()?;
            if (s & mask) == mask {
                return Ok(s);
            }
            self.phy.delay();
            left -= 1;
        }
        Err(TisErr::Timeout)
    }

    /// Read the number of bytes that can be transferred consecutively in this round.
    ///
    /// The return value is guaranteed non-zero. Zero means the device is not ready yet, which here shows up as continued polling
    /// or a timeout, rather than a successful "transfer zero bytes" -- the latter would make the upper layer's transfer loop spin
    /// in place, and that spinning would be caught by no timeout budget.
    fn burstcount(&mut self, budget: u32) -> (r: Result<u16, TisErr>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).held == old(self).held,
            final(self).locality == old(self).locality,
            final(self).phy.fifo_written() =~= old(self).phy.fifo_written(),
            r matches Ok(b) ==> b >= 1,
    {
        let mut left = budget;
        while left > 0
            invariant
                self.wf(),
                self.held == old(self).held,
                self.locality == old(self).locality,
                self.phy.fifo_written() =~= old(self).phy.fifo_written(),
            decreases left,
        {
            let addr = reg_sts(self.locality);
            let v = self.phy.read32(addr)?;
            assert(((v >> 8u32) & 0xFFFFu32) <= 0xFFFFu32) by (bit_vector);
            let b = ((v >> 8u32) & 0xFFFFu32) as u16;
            if b >= 1 {
                return Ok(b);
            }
            self.phy.delay();
            left -= 1;
        }
        Err(TisErr::Timeout)
    }

    // =======================================================================
    // locality
    // =======================================================================

    /// Whether the device has granted the locality to this side.
    ///
    /// All three bits are looked at together: `ACTIVE` alone is not enough; `VALID` must also be set to show the register contents are valid,
    /// and `REQUEST_USE` must have dropped to show the request has been fully processed. Missing any one bit would, under contention,
    /// mistake "the request is still being processed" for "already granted".
    fn check_locality(&mut self) -> (r: Result<bool, TisErr>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).held == old(self).held,
            final(self).locality == old(self).locality,
            final(self).phy.fifo_written() =~= old(self).phy.fifo_written(),
    {
        let addr = reg_access(self.locality);
        let a = self.phy.read8(addr)?;
        let want = ACCESS_ACTIVE_LOCALITY | ACCESS_VALID;
        let mask = want | ACCESS_REQUEST_USE;
        Ok((a & mask) == want)
    }

    /// Request the locality.
    ///
    /// On failure it is guaranteed not to be held -- if a request fails halfway but leaves the flag as "held", the later relinquish would
    /// release a resource that was never obtained.
    pub fn request_locality(&mut self, budget: u32) -> (r: Result<(), TisErr>)
        requires
            old(self).wf(),
            old(self).quiescent(),
        ensures
            final(self).wf(),
            final(self).locality == old(self).locality,
            final(self).phy.fifo_written() =~= old(self).phy.fifo_written(),
            r is Ok ==> final(self).held,
            r is Err ==> final(self).quiescent(),
    {
        match self.check_locality() {
            Ok(true) => {
                self.held = true;
                return Ok(());
            },
            Ok(false) => {},
            Err(e) => return Err(e),
        }

        let addr = reg_access(self.locality);
        self.phy.write8(addr, ACCESS_REQUEST_USE)?;

        let mut left = budget;
        while left > 0
            invariant
                self.wf(),
                !self.held,
                self.locality == old(self).locality,
                self.phy.fifo_written() =~= old(self).phy.fifo_written(),
            decreases left,
        {
            match self.check_locality() {
                Ok(true) => {
                    self.held = true;
                    return Ok(());
                },
                Ok(false) => {},
                Err(e) => return Err(e),
            }
            self.phy.delay();
            left -= 1;
        }
        Err(TisErr::Timeout)
    }

    /// Relinquish the locality.
    ///
    /// Whether or not the register write succeeds, this side's held flag must be cleared. A failed write means the bus already has
    /// a problem, and leaving the flag as "held" would only make the driver believe it holds the resource forever and refuse to
    /// issue the next command -- a recoverable bus fault would thereby become a permanent loss of function.
    pub fn relinquish_locality(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).quiescent(),
            final(self).locality == old(self).locality,
            final(self).phy.fifo_written() =~= old(self).phy.fifo_written(),
    {
        let addr = reg_access(self.locality);
        let _ = self.phy.write8(addr, ACCESS_ACTIVE_LOCALITY);
        self.held = false;
    }

    // =======================================================================
    // Sending
    // =======================================================================

    /// Push the command into the data port.
    ///
    /// On success the bytes the data port received are **exactly the command itself** -- no more, no less, in the same order. On failure
    /// the data port is always cleared and never left with half a command: if half a command remained in the device, the next
    /// send would assemble a message that nobody wrote.
    pub fn send_data(&mut self, cmd: &[u8], len: usize) -> (r: Result<(), TisErr>)
        requires
            old(self).wf(),
            old(self).held,
            1 <= len,
            len <= cmd.len(),
            old(self).phy.fifo_written().len() == 0,
        ensures
            final(self).wf(),
            final(self).held,
            final(self).locality == old(self).locality,
            r is Ok ==> final(self).phy.fifo_written() =~= cmd@.subrange(0, len as int),
            r is Err ==> final(self).phy.fifo_written().len() == 0,
    {
        let res = self.send_data_inner(cmd, len);
        match res {
            Ok(()) => Ok(()),
            Err(e) => {
                let sts_addr = reg_sts(self.locality);
                self.phy.reset_fifo(sts_addr);
                Err(e)
            },
        }
    }

    fn send_data_inner(&mut self, cmd: &[u8], len: usize) -> (r: Result<(), TisErr>)
        requires
            old(self).wf(),
            old(self).held,
            1 <= len,
            len <= cmd.len(),
            old(self).phy.fifo_written().len() == 0,
        ensures
            final(self).wf(),
            final(self).held,
            final(self).locality == old(self).locality,
            r is Ok ==> final(self).phy.fifo_written() =~= cmd@.subrange(0, len as int),
    {
        let sts_addr = reg_sts(self.locality);
        let fifo_addr = reg_data_fifo(self.locality);

        // First confirm the device is in the command-ready state. If not ready, abort the current command and wait again -- this step also clears
        // any bytes the previous command may have left behind.
        let s0 = self.status()?;
        if (s0 & STS_COMMAND_READY) == 0 {
            self.phy.reset_fifo(sts_addr);
            self.wait_status(STS_COMMAND_READY, budget_of(TIMEOUT_B_MS))?;
        }

        // The last byte is handled separately: once it is written the device considers the command fully received, and `DATA_EXPECT` should drop.
        // If it were mixed into the loop, the two judgments "keep feeding" and "fed enough" would have to share one piece of
        // code, while the status bits they expect are exactly opposite.
        let last = len - 1;
        let mut count: usize = 0;

        while count < last
            invariant
                count <= last,
                last == len - 1,
                1 <= len,
                len <= cmd.len(),
                self.wf(),
                self.held,
                self.locality == old(self).locality,
                self.phy.fifo_written() =~= cmd@.subrange(0, count as int),
            decreases last - count,
        {
            let b = self.burstcount(budget_of(TIMEOUT_A_MS))?;

            // Take the smaller of this and the remaining bytes. The transferable amount reported by the device is its own buffer slack, unrelated
            // to the length to be sent this time; without taking the minimum, memory beyond `cmd` would be read out.
            let rem = last - count;
            let bs = b as usize;
            let n = if bs < rem {
                bs
            } else {
                rem
            };

            self.phy.write_fifo(fifo_addr, cmd, count, n)?;

            proof {
                assert(cmd@.subrange(0, count as int) + cmd@.subrange(
                    count as int,
                    count + n,
                ) =~= cmd@.subrange(0, count + n));
            }

            let next = count.checked_add(n).ok_or(TisErr::Protocol)?;
            count = next;

            self.wait_status(STS_VALID, budget_of(TIMEOUT_C_MS))?;
            let s1 = self.status()?;
            // Not finished writing yet; the device must indicate it expects more.
            if (s1 & STS_DATA_EXPECT) == 0 {
                return Err(TisErr::Protocol);
            }
        }

        // Last byte
        self.phy.write_fifo(fifo_addr, cmd, count, 1)?;
        proof {
            assert(cmd@.subrange(0, last as int) + cmd@.subrange(last as int, last + 1)
                =~= cmd@.subrange(0, len as int));
        }

        self.wait_status(STS_VALID, budget_of(TIMEOUT_C_MS))?;
        let s2 = self.status()?;
        // Finished writing; the device must indicate it wants no more -- wanting more shows the two sides understand the command length
        // differently, and issuing the go command then would make the device execute a truncated command.
        if (s2 & STS_DATA_EXPECT) != 0 {
            return Err(TisErr::Protocol);
        }

        Ok(())
    }

    // =======================================================================
    // Receiving
    // =======================================================================

    /// Take `count` bytes from the data port into `out[off..]`.
    fn recv_data(&mut self, out: &mut [u8], off: usize, count: usize) -> (r: Result<(), TisErr>)
        requires
            old(self).wf(),
            old(self).held,
            off + count <= old(out).len(),
        ensures
            final(self).wf(),
            final(self).held,
            final(self).locality == old(self).locality,
            final(out).len() == old(out).len(),
            forall|k: int|
                #![trigger final(out)@[k]]
                0 <= k < final(out).len() && (k < off || k >= off + count) ==> final(out)@[k]
                    == old(out)@[k],
    {
        let fifo_addr = reg_data_fifo(self.locality);
        let mut got: usize = 0;

        while got < count
            invariant
                got <= count,
                off + count <= out.len(),
                out.len() == old(out).len(),
                self.wf(),
                self.held,
                self.locality == old(self).locality,
                forall|k: int|
                    #![trigger out@[k]]
                    0 <= k < out.len() && (k < off || k >= off + count) ==> out@[k] == old(out)@[k],
            decreases count - got,
        {
            self.wait_status(STS_DATA_AVAIL | STS_VALID, budget_of(TIMEOUT_C_MS))?;

            let b = self.burstcount(budget_of(TIMEOUT_A_MS))?;

            // Likewise take the smaller of this and the remaining bytes. Not doing so would directly write beyond the receive buffer.
            let rem = count - got;
            let bs = b as usize;
            let n = if bs < rem {
                bs
            } else {
                rem
            };

            // Before read_fifo modifies out, fix the loop invariant into out_pre.
            let ghost out_pre = out@;

            self.phy.read_fifo(fifo_addr, out, off + got, n)?;

            // Re-establish the loop invariant. read_fifo guarantees out@[k] == out_pre[k] when k < off+got or k >= off+got+n.
            // And n <= rem = count-got, so off+got+n <= off+count, i.e. the condition k >= off+count is satisfied automatically.
            // The condition k < off is likewise implied by k < off+got. Hence out@[k] == out_pre[k] == old(out)@[k].
            proof {
                assert forall|k: int|
                    #![trigger out@[k]]
                    0 <= k < out.len() && (k < off || k >= off + count)
                        implies out@[k] == old(out)@[k]
                by {
                    // Verus needs to see out@[k] == out_pre[k] (from read_fifo) and out_pre[k] == old(out)@[k] (from the loop invariant)
                    assert(out_pre[k] == old(out)@[k]);  // trigger the old loop invariant (trigger out_pre[k])
                    assert(n <= count - got);            // bounds relation
                };
            }

            let next = got.checked_add(n).ok_or(TisErr::Protocol)?;
            got = next;
        }
        Ok(())
    }

    /// Receive one complete response and return its byte count.
    ///
    /// The return value is also **the entry condition of the next layer's decoding**: on success the length field of `out[0..n]` equals
    /// `n`, i.e. it satisfies the message layer's well-formedness. The decoding layer therefore need not validate the length again, and
    /// the two layers' understanding of "how long a response is" is welded together by this postcondition.
    pub fn recv(&mut self, out: &mut [u8]) -> (r: Result<usize, TisErr>)
        requires
            old(self).wf(),
            old(self).held,
            TPM_HEADER_LEN <= old(out).len(),
        ensures
            final(self).wf(),
            final(self).held,
            final(self).locality == old(self).locality,
            final(out).len() == old(out).len(),
            r matches Ok(n) ==> {
                &&& TPM_HEADER_LEN <= n
                &&& n <= final(out).len()
                &&& spec_be32_at(final(out)@, 2) == n
            },
    {
        // Take the message header first. The length field is in it, and before it is read there is no way to know how much more to receive.
        self.recv_data(out, 0, TPM_HEADER_LEN)?;

        let mut c = Cursor::at(2);
        let expected = c.read_be32(&*out).ok_or(TisErr::BadLength)?;

        // The length field is given entirely by the peer, so both sides must be pinned down: smaller than a message header means it cannot even hold its own
        // header, and larger than the buffer means receiving further would go out of bounds.
        let n = expected as usize;
        if n < TPM_HEADER_LEN {
            return Err(TisErr::BadLength);
        }
        if n > out.len() {
            return Err(TisErr::BadLength);
        }

        let ghost after_hdr = out@;

        assert(n >= TPM_HEADER_LEN);
        assert(n <= out.len());
        self.recv_data(out, TPM_HEADER_LEN, n - TPM_HEADER_LEN)?;

        // The second segment lands after the message header; the four bytes holding the length field were not touched.
        proof {
            assert(out@[2] == after_hdr[2]);
            assert(out@[3] == after_hdr[3]);
            assert(out@[4] == after_hdr[4]);
            assert(out@[5] == after_hdr[5]);
            assert(spec_be32_at(out@, 2) == spec_be32_at(after_hdr, 2));
            assert(spec_be32_at(after_hdr, 2) == expected);
            assert(n as int == expected as int);
            assert(spec_be32_at(out@, 2) == n);
        }

        self.wait_status(STS_VALID, budget_of(TIMEOUT_C_MS))?;
        let s = self.status()?;
        // Readable data remaining means the response the device prepared is longer than it declared. What the extra part is
        // cannot be judged, so the whole response is voided -- truncating at the declared length would hand the upper layer a trimmed message
        // without it noticing.
        if (s & STS_DATA_AVAIL) != 0 {
            return Err(TisErr::Protocol);
        }

        Ok(n)
    }

    // =======================================================================
    // One complete round trip
    // =======================================================================

    /// Send a command and receive a response.
    ///
    /// **There is exactly one place that relinquishes the locality, and it is not inside any conditional branch.** Right after the request, all
    /// actions that may fail are gathered into an inner function, making the relinquish an unconditional closing statement -- so
    /// "the locality is released on exit from any path" needs no path-by-path check; it is given directly by the shape of the
    /// control flow. This is also the only place in this layer where the structure was deliberately adjusted for provability.
    pub fn transmit(
        &mut self,
        cmd: &[u8],
        len: usize,
        out: &mut [u8],
        exec_budget: u32,
    ) -> (r: Result<usize, TisErr>)
        requires
            old(self).wf(),
            old(self).quiescent(),
            TPM_HEADER_LEN <= len,
            len <= cmd.len(),
            TPM_HEADER_LEN <= old(out).len(),
        ensures
            final(self).wf(),
            // ★ All three exits -- success, failure, timeout -- no longer hold the locality
            final(self).quiescent(),
            final(self).locality == old(self).locality,
            final(out).len() == old(out).len(),
            r matches Ok(n) ==> {
                &&& TPM_HEADER_LEN <= n
                &&& n <= final(out).len()
                &&& spec_be32_at(final(out)@, 2) == n
            },
    {
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
    ) -> (r: Result<usize, TisErr>)
        requires
            old(self).wf(),
            old(self).held,
            TPM_HEADER_LEN <= len,
            len <= cmd.len(),
            TPM_HEADER_LEN <= old(out).len(),
        ensures
            final(self).wf(),
            final(self).held,
            final(self).locality == old(self).locality,
            final(out).len() == old(out).len(),
            r matches Ok(n) ==> {
                &&& TPM_HEADER_LEN <= n
                &&& n <= final(out).len()
                &&& spec_be32_at(final(out)@, 2) == n
            },
    {
        let sts_addr = reg_sts(self.locality);

        // Clear everything on entry, without assuming how the last run exited.
        self.phy.reset_fifo(sts_addr);

        self.send_data(cmd, len)?;

        // Issue the go command. Only at this step does the device start executing.
        match self.phy.write8(sts_addr, STS_GO) {
            Ok(()) => {},
            Err(e) => {
                self.phy.reset_fifo(sts_addr);
                return Err(e);
            },
        }

        // Wait for the response to become ready. The budget is converted from the command code by the caller and passed in.
        match self.wait_status(STS_DATA_AVAIL | STS_VALID, exec_budget) {
            Ok(_) => {},
            Err(e) => {
                self.phy.reset_fifo(sts_addr);
                return Err(e);
            },
        }

        let n = match self.recv(out) {
            Ok(v) => v,
            Err(e) => {
                self.phy.reset_fifo(sts_addr);
                return Err(e);
            },
        };

        // After receiving, actively abort so the device returns to the command-ready state.
        self.phy.reset_fifo(sts_addr);
        Ok(n)
    }
}

} // verus!
