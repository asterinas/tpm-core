use vstd::prelude::*;
use vstd::array::*;
use vstd::slice::*;

use crate::chip::MSG_MAX;
use crate::cmd::{CAP_TPM_PROPERTIES, CC_GET_CAPABILITY, CC_SELF_TEST, CC_SHUTDOWN, CC_STARTUP,
    SU_CLEAR, SU_STATE};
use crate::cursor::{be16_bytes, be32_bytes};
#[cfg(verus_keep_ghost)]
use crate::cursor::{spec_be16_at, spec_be32_at};
use crate::msg::{ParseError, RC_SUCCESS, ST_NO_SESSIONS, TPM_HEADER_LEN, build_header,
    parse_response};
use crate::phy::TisPhy;
use crate::rsp::parse_tpm_property;
use crate::xfer::{Xfer, XferErr};

verus! {

// ===========================================================================
// What this layer is responsible for
// ===========================================================================
//
// Between power-up and "ready to carry normal traffic" a device goes through a fixed sequence: announce how this side starts up,
// trigger the self-test, and ask for the device capacities. This sequence **must happen in order and only once**,
// so it belongs neither to the transport layer (which has no notion of order) nor to the session layer (a session
// cannot be established until this sequence has finished). These two points are the reason it is a layer of its own.
//
// Only session-less commands are used here. During boot no session key is available yet, and the randomness and
// digest capabilities needed for the handshake may not be ready either; forcing authorization onto boot commands would amount to resting the answer to
// "did the self-test pass" on facilities that "are unusable if the self-test failed".
//
// This layer touches no handles and creates no resource that needs releasing. This is intentional: if boot fails midway,
// the caller can simply discard the whole instance without running a cleanup first -- and cleanup paths are exactly the kind of code that is
// hardest to get right and least often executed.
//
// ---------------------------------------------------------------------------
// Handoff to later layers
// ---------------------------------------------------------------------------
//
// There is only one transport link in the whole driver, and it can be held by only one upper layer at a time: either by
// the session-less orchestration path or by the protected authorized round trip. Ownership expresses this constraint here --
// [`Boot::finish`] consumes `Boot` and hands out the link, after which no method of the boot layer can be called.
// With a "hold a reference, everyone can use it" design, "boot runs only once" would degrade into a comment.

// ===========================================================================
// Return codes
// ===========================================================================

/// The device is not yet initialized, or conversely -- it has already been initialized.
///
/// When it appears in the response to a startup command, it means "this command came too late; the device has long been started".
/// The boot layer treats it as success; see the note on [`Boot::startup`].
const RC_INITIALIZE: u32 = 0x0000_0100;

/// Self-test is in progress in the background.
pub const RC_TESTING: u32 = 0x0000_090A;

// ===========================================================================
// Property identifiers (TPM 2.0 Part 2, fixed property group)
// ===========================================================================

/// The longest command the device can accept.
const PT_MAX_COMMAND_SIZE: u32 = 0x0000_011E;

/// The longest response the device can produce.
const PT_MAX_RESPONSE_SIZE: u32 = 0x0000_011F;

/// Maximum length of a single object backup block.
const PT_MAX_OBJECT_CONTEXT: u32 = 0x0000_0121;

/// Maximum length of a single session backup block.
const PT_MAX_SESSION_CONTEXT: u32 = 0x0000_0122;

// ===========================================================================
// Self-test scope
// ===========================================================================

const SELF_TEST_FULL: u8 = 1;
const SELF_TEST_INCREMENTAL: u8 = 0;

// ===========================================================================
// Buffer capacities
// ===========================================================================

/// The longest boot command: 10 header bytes + the three u32 words of a capability query.
const BOOT_CMD_MAX: usize = 22;

/// Capacity of a boot response. The reply to a single property is 10 header bytes + a fixed 9-byte prefix + one 8-byte key-value pair =
/// 27 bytes; 128 leaves slack while keeping this scratch area small enough to sit safely on the stack.
const BOOT_RSP_MAX: usize = 128;

// ===========================================================================
// Errors
// ===========================================================================

// The derive set is constrained by the inner type: the parse error offers only equality, so this can go no further than equality.
#[derive(PartialEq, Eq, Structural)]
pub enum BootErr {
    /// The cryptographic interface provided by the host does not match this driver's assumptions.
    Abi,
    /// The link is not in a state in which commands can be issued.
    NotReady,
    /// The bytes did not complete a round trip.
    Bus(XferErr),
    /// The device returned a non-zero return code.
    Rc(u32),
    /// The response arrived but failed to parse.
    Parse(ParseError),
    /// The capacity reported by the device exceeds the space statically reserved by this driver.
    Capacity,
}

// ===========================================================================
// Device capacities
// ===========================================================================

/// The four sizes asked for during boot.
///
/// They are asked for not to be recorded but to be **reconciled**: this driver's buffers are all fixed-size, with sizes fixed at
/// compile time; if the device requires larger messages, or produces backup blocks longer than the reserved space, that
/// is a mismatch that must surface during boot. Deferred to runtime, the symptom is an occasional truncation of one particular command,
/// with no apparent connection to capacity.
pub struct Limits {
    pub max_command: u32,
    pub max_response: u32,
    pub max_object_context: u32,
    pub max_session_context: u32,
}

// ===========================================================================
// The booter
// ===========================================================================

pub struct Boot<P: TisPhy> {
    x: Xfer<P>,
    /// Command scratch area. Private: all of this layer's guarantees about the message length field rest on the outside being unable to alter
    /// it.
    cbuf: [u8; BOOT_CMD_MAX],
    rbuf: [u8; BOOT_RSP_MAX],
}

impl<P: TisPhy> Boot<P> {
    pub fn new(x: Xfer<P>) -> (r: Self) {
        Boot { x, cbuf: [0u8; BOOT_CMD_MAX], rbuf: [0u8; BOOT_RSP_MAX] }
    }

    /// Hand out the link, ending the boot phase.
    pub fn finish(self) -> (r: Xfer<P>) {
        self.x
    }

    // =======================================================================
    // Message assembly
    // =======================================================================

    /// Write the message header.
    ///
    /// The length field is fixed here once and never filled in afterwards. The payload lengths of boot commands are all compile-time
    /// constants, so there is no need to "write the payload first, then see how long it came out" -- and back-filling is precisely the only way for the length field and the actual
    /// byte count to drift apart.
    fn put_header(&mut self, cc: u32, total: usize)
        requires
            TPM_HEADER_LEN <= total,
            total <= BOOT_CMD_MAX,
        ensures
            final(self).x == old(self).x,
            final(self).rbuf@ == old(self).rbuf@,
            final(self).cbuf@.len() == BOOT_CMD_MAX,
            spec_be32_at(final(self).cbuf@, 2) == total as u32,
            spec_be32_at(final(self).cbuf@, 6) == cc,
    {
        let hdr = build_header(ST_NO_SESSIONS, cc, total as u32);
        for k in 0..TPM_HEADER_LEN
            invariant
                self.cbuf@.len() == BOOT_CMD_MAX,
                hdr@.len() == TPM_HEADER_LEN,
                spec_be32_at(hdr@, 2) == total as u32,
                spec_be32_at(hdr@, 6) == cc,
                forall|j: int| #![trigger self.cbuf@[j]] 0 <= j < k ==> self.cbuf@[j] == hdr@[j],
                self.x == old(self).x,
                self.rbuf@ == old(self).rbuf@,
        {
            self.cbuf[k] = hdr[k];
        }
        proof {
            assert(self.cbuf@[2] == hdr@[2]);
            assert(self.cbuf@[3] == hdr@[3]);
            assert(self.cbuf@[4] == hdr@[4]);
            assert(self.cbuf@[5] == hdr@[5]);
            assert(self.cbuf@[6] == hdr@[6]);
            assert(self.cbuf@[7] == hdr@[7]);
            assert(self.cbuf@[8] == hdr@[8]);
            assert(self.cbuf@[9] == hdr@[9]);
        }
    }

    /// Write a one-byte payload.
    fn put_u8(&mut self, off: usize, v: u8)
        requires
            TPM_HEADER_LEN <= off,
            off < BOOT_CMD_MAX,
        ensures
            final(self).x == old(self).x,
            final(self).rbuf@ == old(self).rbuf@,
            final(self).cbuf@.len() == BOOT_CMD_MAX,
            final(self).cbuf@[off as int] == v,
            forall|j: int|
                #![trigger final(self).cbuf@[j]]
                0 <= j < BOOT_CMD_MAX && j != off ==> final(self).cbuf@[j] == old(self).cbuf@[j],
    {
        self.cbuf[off] = v;
    }

    /// Write a big-endian u16 payload.
    fn put_be16(&mut self, off: usize, v: u16)
        requires
            TPM_HEADER_LEN <= off,
            off + 2 <= BOOT_CMD_MAX,
        ensures
            final(self).x == old(self).x,
            final(self).rbuf@ == old(self).rbuf@,
            final(self).cbuf@.len() == BOOT_CMD_MAX,
            spec_be16_at(final(self).cbuf@, off as int) == v,
            forall|j: int|
                #![trigger final(self).cbuf@[j]]
                0 <= j < BOOT_CMD_MAX && (j < off || j >= off + 2) ==> final(self).cbuf@[j]
                    == old(self).cbuf@[j],
    {
        let b = be16_bytes(v);
        self.cbuf[off] = b[0];
        self.cbuf[off + 1] = b[1];
    }

    /// Write a big-endian u32 payload.
    fn put_be32(&mut self, off: usize, v: u32)
        requires
            TPM_HEADER_LEN <= off,
            off + 4 <= BOOT_CMD_MAX,
        ensures
            final(self).x == old(self).x,
            final(self).rbuf@ == old(self).rbuf@,
            final(self).cbuf@.len() == BOOT_CMD_MAX,
            spec_be32_at(final(self).cbuf@, off as int) == v,
            forall|j: int|
                #![trigger final(self).cbuf@[j]]
                0 <= j < BOOT_CMD_MAX && (j < off || j >= off + 4) ==> final(self).cbuf@[j]
                    == old(self).cbuf@[j],
    {
        let b = be32_bytes(v);
        self.cbuf[off] = b[0];
        self.cbuf[off + 1] = b[1];
        self.cbuf[off + 2] = b[2];
        self.cbuf[off + 3] = b[3];
    }

    // =======================================================================
    // One round trip
    // =======================================================================

    /// Send out an already assembled command and get back the response length and return code.
    ///
    /// The precondition "the length field equals `len`" is not a formality: the link layer decides how many bytes to push onto the bus according to this
    /// field, and once the field disagrees with the argument, the device and this side each wait for something different,
    /// until a timeout. Writing it as a precondition hands this over to the postconditions of the assembly functions
    /// to guarantee, instead of hoping each call site remembers.
    fn exec(&mut self, len: usize) -> (r: Result<(usize, u32), BootErr>)
        requires
            TPM_HEADER_LEN <= len,
            len <= BOOT_CMD_MAX,
            spec_be32_at(old(self).cbuf@, 2) == len as u32,
        ensures
            final(self).cbuf@ == old(self).cbuf@,
            final(self).rbuf@.len() == BOOT_RSP_MAX,
            r matches Ok((n, _rc)) ==> {
                &&& TPM_HEADER_LEN <= n
                &&& n <= BOOT_RSP_MAX
                &&& spec_be32_at(final(self).rbuf@, 2) == n
            },
    {
        // The interface on the other side has no state precondition, so it can only be supplied here. If not satisfied, refuse outright: a command sent in the
        // wrong state at best wastes a round trip.
        if !self.x.ready() {
            return Err(BootErr::NotReady);
        }
        match self.x.run(&self.cbuf, len, &mut self.rbuf) {
            Ok((n, rc)) => Ok((n, rc)),
            Err(e) => Err(BootErr::Bus(e)),
        }
    }

    // =======================================================================
    // Startup
    // =======================================================================

    /// Announce how this side starts up.
    ///
    /// "Already started" is treated as success. The device's startup state is determined by the power cycle, and this side may take over
    /// after the device was already initialized by an earlier firmware stage -- in that case the rejection received for a resent startup
    /// command says "the state you asked for already holds"; treating it as failure would make the driver refuse to load on a class of
    /// perfectly normal platforms.
    ///
    /// Conversely, any other non-zero return code is reported as is, with no second interpretation.
    pub fn startup(&mut self, su: u16) -> (r: Result<(), BootErr>)
        requires
            su == SU_CLEAR || su == SU_STATE,
    {
        let total = TPM_HEADER_LEN + 2;
        self.put_header(CC_STARTUP, total);
        self.put_be16(TPM_HEADER_LEN, su);
        match self.exec(total) {
            Ok((_n, rc)) => {
                if rc == RC_SUCCESS || rc == RC_INITIALIZE {
                    Ok(())
                } else {
                    Err(BootErr::Rc(rc))
                }
            },
            Err(e) => Err(e),
        }
    }

    /// Shutdown.
    ///
    /// Unlike startup, no non-zero return code is let through here: if the shutdown did not succeed, at the next power-up the device
    /// will assume the previous round ended in an abnormal power loss and reset part of its state. The caller must know this.
    pub fn shutdown(&mut self, su: u16) -> (r: Result<(), BootErr>)
        requires
            su == SU_CLEAR || su == SU_STATE,
    {
        let total = TPM_HEADER_LEN + 2;
        self.put_header(CC_SHUTDOWN, total);
        self.put_be16(TPM_HEADER_LEN, su);
        match self.exec(total) {
            Ok((_n, rc)) => {
                if rc == RC_SUCCESS {
                    Ok(())
                } else {
                    Err(BootErr::Rc(rc))
                }
            },
            Err(e) => Err(e),
        }
    }

    // =======================================================================
    // Self-test
    // =======================================================================

    /// Trigger the self-test. When `full` is true, all algorithms must be retested; otherwise only those not yet tested.
    ///
    /// "Testing" is treated as success, for a different reason than startup: the semantics of this command are "start testing"
    /// rather than "finished testing", so the device replying that it is still testing is precisely a sign that the command took effect. The real self-test verdict has to
    /// be queried separately and this layer does not do it for the caller -- merging "started" and "passed" into one return value would let the caller
    /// believe they got the latter.
    pub fn self_test(&mut self, full: bool) -> (r: Result<(), BootErr>) {
        let total = TPM_HEADER_LEN + 1;
        self.put_header(CC_SELF_TEST, total);
        let arg = if full {
            SELF_TEST_FULL
        } else {
            SELF_TEST_INCREMENTAL
        };
        self.put_u8(TPM_HEADER_LEN, arg);
        match self.exec(total) {
            Ok((_n, rc)) => {
                if rc == RC_SUCCESS || rc == RC_TESTING {
                    Ok(())
                } else {
                    Err(BootErr::Rc(rc))
                }
            },
            Err(e) => Err(e),
        }
    }

    // =======================================================================
    // Property query
    // =======================================================================

    /// Ask for the value of one fixed property.
    ///
    /// One at a time. Batch queries save a few round trips, but the order of the key-value pairs in the reply is decided by the device, and
    /// code that matches them up one by one must handle missing, out-of-order and duplicate entries, while boot asks for only
    /// four properties in total -- the round trips saved do not pay for those branches.
    pub fn property(&mut self, pt: u32) -> (r: Result<u32, BootErr>) {
        let total = TPM_HEADER_LEN + 12;
        self.put_header(CC_GET_CAPABILITY, total);
        self.put_be32(TPM_HEADER_LEN, CAP_TPM_PROPERTIES);
        self.put_be32(TPM_HEADER_LEN + 4, pt);
        // Count is one. The device is allowed to return several at once, but this layer reads only the first, and the extra
        // only takes up response buffer space for nothing.
        self.put_be32(TPM_HEADER_LEN + 8, 1);

        let n = match self.exec(total) {
            Ok((n, rc)) => {
                if rc != RC_SUCCESS {
                    return Err(BootErr::Rc(rc));
                }
                n
            },
            Err(e) => return Err(e),
        };

        // The message is truncated to its self-declared length before parsing. The parsing layer decides field boundaries by the length of the slice itself;
        // if the unrelated bytes at the tail of the scratch area were handed up too, an out-of-bounds read would become a legal
        // read, returning leftovers of the previous response.
        let raw = &self.rbuf[0..n];
        let rsp = match parse_response(raw) {
            Ok(v) => v,
            Err(e) => return Err(BootErr::Parse(e)),
        };
        match parse_tpm_property(rsp.body) {
            Ok(v) => Ok(v),
            Err(e) => Err(BootErr::Parse(e)),
        }
    }

    /// Ask for all four sizes and reconcile them with this driver's static reservations.
    ///
    /// A failed reconciliation is reported as an error, with no degradation. Degrading would mean a runtime path "buffer too small,
    /// so fragment / truncate / skip", and on machines with ample capacity that path is never
    /// executed and therefore never tested. Better to refuse to load here.
    pub fn probe_limits(&mut self) -> (r: Result<Limits, BootErr>) {
        let max_command = self.property(PT_MAX_COMMAND_SIZE)?;
        let max_response = self.property(PT_MAX_RESPONSE_SIZE)?;
        let max_object_context = self.property(PT_MAX_OBJECT_CONTEXT)?;
        let max_session_context = self.property(PT_MAX_SESSION_CONTEXT)?;

        // The message buffers must hold both directions. What is compared here is the **device's upper bound** against this side's capacity:
        // a device claiming it can receive 8 KiB while this side reserves only 4 KiB is not an error in itself -- this side simply must not send commands that
        // long. What is truly fatal is the opposite: the device may produce a response longer than this side's scratch area,
        // and then every over-long response would be truncated.
        if max_response as usize > MSG_MAX {
            return Err(BootErr::Capacity);
        }
        // Backup blocks go in and out whole with no room for fragmentation, so enough must be reserved in both directions.
        if max_object_context as usize > MSG_MAX {
            return Err(BootErr::Capacity);
        }
        if max_session_context as usize > MSG_MAX {
            return Err(BootErr::Capacity);
        }

        Ok(
            Limits {
                max_command,
                max_response,
                max_object_context,
                max_session_context,
            },
        )
    }
}

// ===========================================================================
// The complete sequence
// ===========================================================================

/// From a freshly established link to "ready to carry traffic", handing out the device capacities along the way.
///
/// The order is fixed by dependencies, not by habit:
///
/// 1. **The result of the host interface self-check** is passed in by the caller through `abi_ok` and ruled on first, here.
///    The self-check itself needs no involvement of the device and is not this layer's job -- it touches an external interface and belongs to
///    the grounding layer; this layer is only responsible for "do not proceed if the interface does not match". It comes first because,
///    if the interface does not match, every later step fails in ways that are hard to attribute; better to stop while
///    not a single byte has been sent.
/// 2. **Startup**. Before receiving a startup command, the device rejects the vast majority of commands.
/// 3. **Self-test**. It must be triggered before any traffic commands arrive, so that it runs in parallel with later operations.
/// 4. **Capacity reconciliation**. Placed last because it is the only step that needs to parse a reply payload,
///    and payload parsing requires the device to already be in normal working state.
///
/// If any step fails midway, return immediately and the link is discarded with it. This layer has no "partial success"
/// state -- for a device whose boot did not finish, this side cannot say where it currently stands.
pub fn bring_up<P: TisPhy>(x: Xfer<P>, su: u16, abi_ok: bool) -> (r: Result<
    (Xfer<P>, Limits),
    BootErr,
>)
    requires
        su == SU_CLEAR || su == SU_STATE,
{
    // Whether the host interface is usable is checked by the grounding layer and passed in as a fact; this layer only rules on it and does not
    // touch any external interface -- that would make this crate depend back on the grounding layer and break the one-way dependency.
    if !abi_ok {
        return Err(BootErr::Abi);
    }

    let mut b = Boot::new(x);

    b.startup(su)?;
    // Incremental self-test rather than full: a full self-test retests algorithms already tested, which on the boot path is
    // a considerable wait carrying no new information. Where a full retest is needed (e.g. a compliance requirement after
    // resuming from a low-power state), the caller invokes it separately.
    b.self_test(false)?;
    let lim = b.probe_limits()?;

    Ok((b.finish(), lim))
}

} // verus!