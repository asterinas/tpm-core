use vstd::prelude::*;
use vstd::set::Set;

use crate::chip::{ChipTransport, RC_SUCCESS};
use crate::cmd::{CC_CONTEXT_LOAD, CC_FLUSH_CONTEXT};
#[cfg(verus_keep_ghost)]
use crate::handle::valid_phandle;
use crate::module::IoErr;
use crate::phy::TisPhy;
#[cfg(verus_keep_ghost)]
use crate::rewrite::be32_at;
use crate::rewrite::HEADER_SIZE;
use crate::xfer::{Xfer, XferErr, peek_be32};

verus! {

// ===========================================================================
// What this layer does
// ===========================================================================
//
// The interface the orchestration layer requires is "one round trip, plus which handles the chip holds"; the transport link provides
// "one round trip". The missing half -- the handle set -- is **internal chip state**, which this side cannot observe and
// can only assume.
//
// Assumptions are unavoidable, but they can be kept very small. This module compresses it into a zero-sized ghost ledger: it does not exist
// at runtime and takes not a single byte once compiled; its only role is to carry the sentence that cannot be said aloud --
// "a handle the chip has just reported was not valid before". Every other step (length checks, command
// code dispatch, error mapping) is ordinary verifiable code.
//
// The increment to the trust base is thus the postconditions of the three functions below, no more and no less.

// ===========================================================================
// Ghost ledger (trust base)
// ===========================================================================

/// The set of handles the chip currently holds.
///
/// It has only ghost fields and is a zero-sized type at runtime. None of the methods that modify it contain executable code --
/// they do not "record" anything, they **declare this side's assumptions about chip behavior**.
pub struct LiveSet {
    pub ghost s: Set<u32>,
}

impl LiveSet {
    pub open spec fn view(&self) -> Set<u32> {
        self.s
    }

    #[verifier::external_body]
    pub fn new() -> (r: Self)
        ensures
            r.view() == Set::<u32>::empty(),
    {
        unimplemented!()
    }

    /// Record a handle newly loaded by the chip.
    ///
    /// **Trust clause (1)**: `valid_phandle(h)`.
    /// Basis: the specification states that on success a load-type command returns a handle within the transient object interval; zero and
    /// reserved values are not legal returns.
    ///
    /// **Trust clause (2)**: `!old(self).view().contains(h)`.
    /// Basis: a handle uniquely identifies a loaded object until it is explicitly released or swapped out; the chip does not
    /// hand out a still-valid handle a second time.
    ///
    /// The second is **the most substantive assumption in the whole proof chain**: the injectivity of the upper-layer handle table and the isolation between the two
    /// handle spaces ultimately reduce to it. It is also the only assumption that cannot be hardened by any
    /// check on this side -- if this side could verify for itself that a handle is new, no assumption would be needed.
    ///
    /// Calling discipline: call it only with a handle just read from the successful response of a load-type command, and that response
    /// must already have passed the length check. Any other way of calling it turns the two clauses above from assumptions into lies.
    #[verifier::external_body]
    pub fn observe_load(&mut self, _h: u32)
        ensures
            valid_phandle(_h),
            !old(self).view().contains(_h),
            final(self).view() == old(self).view().insert(_h),
    {
    }

    /// Record that a handle is no longer tracked by this side.
    ///
    /// **Trust clause (3)**: the set shrinks by `h`.
    ///
    /// The handle is a ghost value rather than a runtime value: this step does nothing at runtime, and the value is used only in proofs.
    /// This way, even if the command buffer is too short to read the handle field, the books can still be kept -- without having to
    /// add a length precondition to the command buffer that it does not otherwise need just for bookkeeping.
    ///
    /// Note that this does **not assume the chip really released it**. If the release command failed to arrive because of a bus fault, that
    /// resource stays occupied on the chip until reset. This is a known leak with no remedy, and writing it on the ledger would only
    /// make this side carry forever a handle that can never be used again.
    #[verifier::external_body]
    pub fn observe_flush(&mut self, _h: Ghost<u32>)
        ensures
            final(self).view() == old(self).view().remove(_h@),
    {
    }
}

// ===========================================================================
// Link
// ===========================================================================

pub struct ChipLink<P: TisPhy> {
    pub x: Xfer<P>,
    pub ledger: LiveSet,
}

impl<P: TisPhy> ChipLink<P> {
    pub fn new(x: Xfer<P>) -> (r: Self)
        ensures
            r.ledger.view() == Set::<u32>::empty(),
    {
        ChipLink { x, ledger: LiveSet::new() }
    }
}

impl<P: TisPhy> ChipTransport for ChipLink<P> {
    open spec fn live(&self) -> Set<u32> {
        self.ledger.view()
    }

    fn exec(&mut self, cmd: &[u8], rsp: &mut [u8]) -> (r: Result<usize, IoErr>) {
        // The command code is taken from a fixed offset in the message header. This read holds unconditionally: the interface precondition already
        // guarantees the buffer is no shorter than a message header.
        let cc = peek_be32(cmd, 6);
        let ghost fh = be32_at(cmd@, HEADER_SIZE as int);

        // The release command's bookkeeping is done **first, before every early return**. The interface's
        // spec for the release command is not conditioned on transport success: when the transport fails, this side cannot know whether the chip has released it;
        // rather than being uncertain on both sides, it is uniformly treated as "this side no longer tracks it". If this bookkeeping landed after
        // some `return`, that path would leave behind a handle that has semantically long been given up but that this side
        // still tracks.
        if cc == CC_FLUSH_CONTEXT {
            self.ledger.observe_flush(Ghost(fh));
        }

        // The interface signature carries no state precondition, so it can only be supplied here. If not satisfied, refuse outright: a command sent in the
        // wrong state at best wastes a round trip.
        if !self.x.ready() {
            return Err(IoErr::NotReady);
        }

        // How long the command is goes by what the message header says, not by the buffer capacity -- what the upper layer passes down
        // is often a whole scratch area with a large tail of unrelated bytes, and sending by buffer length would ship the
        // garbage into the device as well.
        let declared = peek_be32(cmd, 2);
        if declared < HEADER_SIZE as u32 {
            return Err(IoErr::BadCommand);
        }
        let len = declared as usize;
        if len > cmd.len() {
            return Err(IoErr::BadCommand);
        }

        let n = match self.x.run(cmd, len, rsp) {
            Ok((n, rc)) => {
                if cc == CC_CONTEXT_LOAD && rc == RC_SUCCESS {
                    // A load that succeeded but has no room for a handle means the response does not match the command. Such a
                    // response cannot be trusted and therefore cannot be booked -- at the cost that, if the chip really did load something,
                    // that handle leaks. Better to leak a handle than to record a value of unknown origin
                    // in the table as a handle.
                    if n < HEADER_SIZE + 4 {
                        return Err(IoErr::Protocol);
                    }
                    let h = peek_be32(&*rsp, HEADER_SIZE);
                    self.ledger.observe_load(h);
                }
                n
            },
            Err(e) => {
                return Err(map_err(e));
            },
        };

        Ok(n)
    }
}

/// Link error -> orchestration-layer error.
///
/// A link-layer failure has no return code to read, so the classification here is only by "transport semantics":
/// timeouts are retryable, physical faults are not retryable, the protocol frame cannot be trusted, and the command's self-description is inconsistent.
pub fn map_err(e: XferErr) -> (r: IoErr) {
    match e {
        XferErr::Bus(crate::tis::TisErr::Phy) => IoErr::Bus,
        XferErr::Bus(crate::tis::TisErr::Timeout) => IoErr::Timeout,
        XferErr::Bus(crate::tis::TisErr::Protocol) => IoErr::Protocol,
        XferErr::Bus(crate::tis::TisErr::BadLength) => IoErr::Protocol,
        XferErr::BadCommand => IoErr::BadCommand,
    }
}

} // verus!