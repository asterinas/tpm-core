use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::chip::lemma_be32_forms_agree;
use crate::cmd::{
    CC_CONTEXT_LOAD, CC_CONTEXT_SAVE, CC_FLUSH_CONTEXT, CC_GET_CAPABILITY, CC_GET_RANDOM,
    CC_PCR_EXTEND, CC_PCR_READ, CC_SELF_TEST, CC_SHUTDOWN, CC_STARTUP,
};
#[cfg(verus_keep_ghost)]
use crate::cursor::spec_be32_at;
use crate::msg::TPM_HEADER_LEN;
use crate::phy::TisPhy;
#[cfg(verus_keep_ghost)]
use crate::rewrite::be32_at;
use crate::rewrite::read_be32;
use crate::tis::{TisErr, budget_of};
use crate::tis_core::Tis;

verus! {

// ===========================================================================
// What this layer is responsible for
// ===========================================================================
//
// The transport layer only sends bytes out and takes bytes back, knowing nothing of message content; the command layer only
// assembles and parses messages, knowing nothing of the bus. Three things remain between them that nobody does, and this layer does the three:
//
// 1. **Consistency between the command's self-declared length and the actual buffer**. The length field in the command header is the basis of
//    all later encoding and decoding, and must be pinned down before the bytes leave this machine, rather than waiting for the peer to report an error.
// 2. **Return-code extraction**. It sits at a fixed offset in the response header, and its value needs no parsing of the message body,
//    so doing it here is earlier and cheaper than putting it in the command layer.
// 3. **Retransmission on retryable return codes**. During self-test or resource shortage the device asks to come back later; such
//    replies are not errors and should not have every upper-layer call site handle them separately.
//
// What this layer **does not** do: it does not parse message bodies, does no authorization, and touches no handles. All three need to know
// the semantics of specific commands and belong to higher layers.

// ===========================================================================
// Return codes
// ===========================================================================
//
// The values come from the return-code table of TPM 2.0 Part 2. Only the few this layer needs to **base decisions on** are listed here;
// the other return codes are passed up as they are for the caller to judge.

pub const RC_SUCCESS: u32 = 0x0000_0000;

/// Base of the warning-class return codes. Bit 11 set means "not a failure, just not possible for now".
pub const RC_WARN_BASE: u32 = 0x0000_0900;

/// The device is running its self-test, and the requested function is not ready yet.
pub const RC_TESTING: u32 = 0x0000_090A;

/// The device is currently busy; resend the same command later.
pub const RC_RETRY: u32 = 0x0000_0922;

/// The device yielded voluntarily and the command was not executed. Semantically the same kind as [`RC_RETRY`], but triggered by the device's scheduling
/// policy rather than resource shortage; resending once usually succeeds.
pub const RC_YIELDED: u32 = 0x0000_0908;

// ===========================================================================
// Retransmission policy
// ===========================================================================
//
// The backoff starts at a very short interval and doubles each round, up to a cap. Doubling rather than a fixed interval is so that
// both "the device happens to be ready in the next millisecond" and "the device stays busy for several seconds" come out fine: the former
// waits only one minimum interval extra, and for the latter the number of resends is logarithmic rather than linear.
//
// **Both** a cap on the count and a cap on the single wait are needed: limiting only the count turns into a long fixed-interval grind once the backoff hits its ceiling;
// limiting only the duration would force every resend to recompute the elapsed time, and the time domain is exactly what this project
// deliberately avoids (see the note on the polling budget). With both caps given, the bound on total waiting time is
// a constant, which can be stated without reading a clock.

/// Duration of the first backoff (ms).
const RETRY_FIRST_MS: u32 = 20;

/// Upper limit of a single backoff (ms).
const RETRY_CAP_MS: u32 = 2000;

/// Upper limit on the number of retransmissions. If the return code is still retryable after reaching this number, it is passed to the caller as is --
/// this layer does not translate "waited long and still busy" into an error; that judgment belongs to the caller.
pub const RETRY_MAX: u32 = 8;

// ===========================================================================
// Command duration table
// ===========================================================================
//
// Execution times of different commands differ by three orders of magnitude: reading a PCR takes microseconds, generating a key pair can take
// tens of seconds. Waiting for both with the same budget means either slow commands are wrongly judged timed out, or a fast command's
// fault is exposed only much later.
//
// The numbers in the table are **upper bounds**, not expected values, and should err on the large side: underestimating judges normal execution as
// a timeout, which is a functional fault; overestimating only means waiting a little longer on a fault. Commands not listed all take a conservative
// default.

const DURATION_SHORT_MS: u32 = 750;

const DURATION_MEDIUM_MS: u32 = 2000;

const DURATION_LONG_MS: u32 = 30000;

/// Default upper bound for unlisted commands. It is deliberately very large: for a command this layer does not recognize, this layer has
/// no basis to say how fast it should be.
const DURATION_DEFAULT_MS: u32 = 120000;

/// Command code -> upper bound of execution time (ms).
///
/// The return value is always positive, so the polling budget converted by [`budget_of`] is never zero.
fn duration_ms(cc: u32) -> (r: u32)
    ensures
        r >= 1,
{
    if cc == CC_STARTUP || cc == CC_SHUTDOWN || cc == CC_PCR_READ || cc == CC_PCR_EXTEND || cc
        == CC_GET_CAPABILITY {
        DURATION_SHORT_MS
    } else if cc == CC_CONTEXT_LOAD || cc == CC_CONTEXT_SAVE || cc == CC_FLUSH_CONTEXT {
        // Context swap-in/out touches the device's internal storage and is one notch slower than plain register reads and writes.
        DURATION_SHORT_MS
    } else if cc == CC_GET_RANDOM {
        // When the entropy pool is insufficient the device waits to accumulate, and the duration is not determined by the command itself.
        DURATION_MEDIUM_MS
    } else if cc == CC_SELF_TEST {
        DURATION_LONG_MS
    } else {
        DURATION_DEFAULT_MS
    }
}

/// Command code -> polling budget for waiting on the response.
pub fn poll_budget(cc: u32) -> (r: u32)
    ensures
        r >= 1,
{
    budget_of(duration_ms(cc))
}

// ===========================================================================
// Errors
// ===========================================================================

#[derive(Clone, Copy, PartialEq, Eq, Structural, Debug)]
pub enum XferErr {
    /// Transport-layer error. The bytes did not complete a round trip.
    Bus(TisErr),
    /// The command itself does not hold: the length field does not match the buffer. Not a single byte of the command was sent.
    BadCommand,
}

// ===========================================================================
// Well-formedness
// ===========================================================================

/// A sendable command: the length field equals the length the caller claims, and those bytes really are in the
/// buffer.
///
/// Both conditions are indispensable. Checking only the former, the buffer may not be that long at all; checking only the latter, the number of
/// bytes sent will not match the number the device expects to receive according to the length field, and the device will keep waiting for the second half
/// while this side is already waiting for the response -- each waiting for something different, until a timeout.
pub open spec fn spec_cmd_wf(cmd: Seq<u8>, len: int) -> bool {
    &&& TPM_HEADER_LEN <= len
    &&& len <= cmd.len()
    &&& spec_be32_at(cmd, 2) == len
}

/// Big-endian u32 read, giving the value under both spec formulations at once.
///
/// The message header is generated by the command layer (the spec uses multiply-add form), and the handle area is read by the rewrite layer (the spec uses shift-or
/// form); this layer straddles the two, and reading once lays out both forms, so that every call site need not
/// introduce the bridge lemma on its own.
pub(crate) fn peek_be32(b: &[u8], off: usize) -> (r: u32)
    requires
        off + 4 <= b.len(),
    ensures
        r == spec_be32_at(b@, off as int),
        r == be32_at(b@, off as int),
{
    proof {
        lemma_be32_forms_agree(b@, off as int);
    }
    read_be32(b, off)
}

fn cmd_wf(cmd: &[u8], len: usize) -> (r: bool)
    ensures
        r == spec_cmd_wf(cmd@, len as int),
{
    if len < TPM_HEADER_LEN {
        return false;
    }
    if len > cmd.len() {
        return false;
    }
    let d = peek_be32(cmd, 2);
    d as usize == len
}

/// The response body (the part after the message header) is no shorter than `min_body`.
///
/// Listed separately because it is **the last gate before parsing**: parsing functions all take "the body is long enough"
/// as a precondition, and if the gate is not closed, out-of-bounds reads turn from an internal implementation detail of the parsing function into the caller's
/// responsibility, which callers usually forget.
pub fn body_at_least(n: usize, min_body: usize) -> (r: bool)
    requires
        n >= TPM_HEADER_LEN,
    ensures
        r ==> n - TPM_HEADER_LEN >= min_body,
{
    n - TPM_HEADER_LEN >= min_body
}

// ===========================================================================
// Orchestrator
// ===========================================================================

pub struct Xfer<P: TisPhy> {
    pub tis: Tis<P>,
    /// Upper limit on remaining retransmissions. Made a field rather than a constant so that the boot phase (device
    /// just powered up, self-test unfinished) and steady state can use the same code with different patience.
    pub retries: u32,
}

impl<P: TisPhy> Xfer<P> {
    pub open spec fn wf(&self) -> bool {
        self.tis.wf()
    }

    /// Ready to start the next command: the locality is not held.
    pub open spec fn idle(&self) -> bool {
        self.tis.quiescent()
    }

    pub fn new(tis: Tis<P>) -> (r: Self)
        ensures
            r.tis == tis,
            r.retries == RETRY_MAX,
    {
        Xfer { tis, retries: RETRY_MAX }
    }

    /// Runtime self-check: whether the state meets the preconditions for issuing a command.
    ///
    /// It exists because of an interface boundary -- this layer is called through an interface without preconditions (the signature of that interface
    /// is determined by the verification needs of a higher layer and cannot be changed), while this layer's methods have preconditions. The difference can
    /// only be made up at runtime: check once, and report an error directly if not satisfied, so that a call that does not meet the preconditions
    /// cannot continue.
    pub fn ready(&self) -> (r: bool)
        ensures
            r ==> self.wf() && self.idle(),
    {
        self.tis.locality < crate::tis::MAX_LOCALITY && !self.tis.held
    }

    // =======================================================================
    // Backoff
    // =======================================================================

    /// Wait for `ticks` polling intervals.
    ///
    /// The wait is expressed as an integer multiple of the polling interval rather than by hooking up a sleep interface: this layer introduces no
    /// notion of time, and the actual length of the wait is decided by the throttle implementation of the physical layer. The termination of this loop
    /// therefore comes directly from the counter.
    fn backoff(&mut self, ticks: u32)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).tis.held == old(self).tis.held,
            final(self).tis.locality == old(self).tis.locality,
            final(self).retries == old(self).retries,
    {
        let mut left = ticks;
        while left > 0
            invariant
                self.wf(),
                self.tis.held == old(self).tis.held,
                self.tis.locality == old(self).tis.locality,
                self.retries == old(self).retries,
            decreases left,
        {
            self.tis.phy.delay();
            left -= 1;
        }
    }

    // =======================================================================
    // Single attempt
    // =======================================================================

    /// Send a command, receive a response, and extract the return code.
    ///
    /// The return code is taken from a fixed offset in the response header, and its value does not depend on any parsing of the message body -- the response length is already
    /// guaranteed by the transport layer to be no less than a message header, so this read holds unconditionally.
    fn attempt(
        &mut self,
        cmd: &[u8],
        len: usize,
        rsp: &mut [u8],
        exec_budget: u32,
    ) -> (r: Result<(usize, u32), XferErr>)
        requires
            old(self).wf(),
            old(self).idle(),
            spec_cmd_wf(cmd@, len as int),
            TPM_HEADER_LEN <= old(rsp).len(),
        ensures
            final(self).wf(),
            final(self).idle(),
            final(self).retries == old(self).retries,
            final(rsp).len() == old(rsp).len(),
            r matches Ok((n, rc)) ==> {
                &&& TPM_HEADER_LEN <= n
                &&& n <= final(rsp).len()
                &&& spec_be32_at(final(rsp)@, 2) == n
                &&& rc == spec_be32_at(final(rsp)@, 6)
                &&& rc == be32_at(final(rsp)@, 6)
            },
    {
        let n = match self.tis.transmit(cmd, len, rsp, exec_budget) {
            Ok(v) => v,
            Err(e) => return Err(XferErr::Bus(e)),
        };
        let rc = peek_be32(&*rsp, 6);
        Ok((n, rc))
    }

    // =======================================================================
    // One round trip with retransmission
    // =======================================================================

    /// Return codes worth resending.
    ///
    /// The self-test command is an exception for "self-test in progress": this command asks **precisely** about the self-test state,
    /// and "still testing" is a valid answer rather than a reply to be avoided. Treating it as retryable would turn a
    /// status query into a blocking wait, which the boot phase in particular should not suffer.
    pub fn retryable(rc: u32, cc: u32) -> (r: bool) {
        if rc == RC_RETRY || rc == RC_YIELDED {
            true
        } else if rc == RC_TESTING {
            cc != CC_SELF_TEST
        } else {
            false
        }
    }

    /// Send a command, resend if necessary, and return the response length and return code.
    ///
    /// Three properties are written into the signature:
    ///
    /// - **If the command does not pass the self-check, not a single byte is sent**. A badly formed command is stopped here,
    ///   and the device never sees it.
    /// - **Whichever exit is taken, the locality is no longer held**. This is guaranteed by the transport layer on each attempt,
    ///   and retransmission merely chains that guarantee together -- each attempt is a complete acquire and release, not a loop
    ///   holding the locality. Waiting a few extra milliseconds in exchange for other localities being usable during the whole
    ///   wait is a good trade.
    /// - **The return code is the value in the response header**. This layer does not rewrite, swallow or translate it; if the retransmission count
    ///   is exhausted and the return code is still retryable, it is passed up as is.
    ///
    /// Resending is safe because the command buffer is read-only: this layer receives an immutable slice,
    /// and no step from start to finish modifies it, so the bytes sent the second time are identical to the first, byte for byte.
    /// If a single buffer were shared for sending and receiving, this would no longer hold, and the original text would have to be restored before resending --
    /// an error that is easy to miss and hard to notice afterwards; separating the two buffers avoids it at the root.
    pub fn run(&mut self, cmd: &[u8], len: usize, rsp: &mut [u8]) -> (r: Result<
        (usize, u32),
        XferErr,
    >)
        requires
            old(self).wf(),
            old(self).idle(),
            TPM_HEADER_LEN <= old(rsp).len(),
        ensures
            final(self).wf(),
            final(self).idle(),
            final(rsp).len() == old(rsp).len(),
            r matches Ok((n, rc)) ==> {
                &&& TPM_HEADER_LEN <= n
                &&& n <= final(rsp).len()
                &&& spec_be32_at(final(rsp)@, 2) == n
                &&& rc == spec_be32_at(final(rsp)@, 6)
                &&& rc == be32_at(final(rsp)@, 6)
            },
    {
        if !cmd_wf(cmd, len) {
            return Err(XferErr::BadCommand);
        }
        // The length has passed the gate, so the four bytes holding the command code are necessarily within the buffer.
        let cc = peek_be32(cmd, 6);
        let exec_budget = poll_budget(cc);

        let cap = budget_of(RETRY_CAP_MS);
        let mut ticks = budget_of(RETRY_FIRST_MS);
        let mut left = self.retries;

        while left > 0
            invariant
                self.wf(),
                self.idle(),
                rsp.len() == old(rsp).len(),
                TPM_HEADER_LEN <= rsp.len(),
                spec_cmd_wf(cmd@, len as int),
            decreases left,
        {
            match self.attempt(cmd, len, rsp, exec_budget) {
                Ok((n, rc)) => {
                    if !Self::retryable(rc, cc) {
                        return Ok((n, rc));
                    }
                },
                Err(e) => return Err(e),
            }

            self.backoff(ticks);
            // Check the cap before doubling, to avoid a multiplication on the counter that could overflow.
            if ticks < cap {
                if ticks <= cap - ticks {
                    ticks += ticks;
                } else {
                    ticks = cap;
                }
            }
            left -= 1;
        }

        // Count exhausted. Send one last time, with the result no longer filtered -- "waited this long and still busy" is a fact
        // that the caller must be able to see; hiding it as a timeout error of this layer would leave the upper layer unable to tell
        // whether the device is busy or broken.
        self.attempt(cmd, len, rsp, exec_budget)
    }
}

} // verus!
