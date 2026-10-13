use crate::{
    chip::MSG_MAX,
    cmd::{CAP_TPM_PROPERTIES, CC_GET_CAPABILITY, CC_SELF_TEST, CC_SHUTDOWN, CC_STARTUP},
    cursor::{be16_bytes, be32_bytes},
    msg::{build_header, parse_response, ParseError, RC_SUCCESS, ST_NO_SESSIONS, TPM_HEADER_LEN},
    phy::TisPhy,
    rsp::parse_tpm_property,
    xfer::{Xfer, XferErr},
};

/// The device has not been initialized, or conversely—has already been initialized.
///
/// When it appears in the response to a startup command, it means “this command arrived too late; the
/// device was already started.” The boot layer treats it as success; see the notes for [`Boot::startup`].
const RC_INITIALIZE: u32 = 0x0000_0100;
/// Self-test is already running in the background.
pub const RC_TESTING: u32 = 0x0000_090A;
/// Longest command the device can receive.
const PT_MAX_COMMAND_SIZE: u32 = 0x0000_011E;
/// Longest response the device can produce.
const PT_MAX_RESPONSE_SIZE: u32 = 0x0000_011F;
/// Maximum length of a single object backup block.
const PT_MAX_OBJECT_CONTEXT: u32 = 0x0000_0121;
/// Maximum length of a single session backup block.
const PT_MAX_SESSION_CONTEXT: u32 = 0x0000_0122;
const SELF_TEST_FULL: u8 = 1;
const SELF_TEST_INCREMENTAL: u8 = 0;
/// Longest boot command: packet header (10 bytes) + capability query with three u32 values.
const BOOT_CMD_MAX: usize = 22;
/// Capacity of the boot response. A single property response is header 10 + fixed prefix 9 + key/value
/// pair 8 = 27 bytes; using 128 leaves room, while keeping this temporary buffer small enough to sit on
/// the stack.
const BOOT_RSP_MAX: usize = 128;
#[derive(PartialEq, Eq)]
pub enum BootErr {
    /// The host-provided cryptographic interface does not match the assumptions of this driver.
    Abi,
    /// The link is not in a state that can issue a command.
    NotReady,
    /// Bytes did not complete a full round trip.
    Bus(XferErr),
    /// The device returned a non-zero return code.
    Rc(u32),
    /// The response arrived but parsing failed.
    Parse(ParseError),
    /// The device reported a capacity larger than the static space reserved by this driver.
    Capacity,
}
/// The four dimensions queried during boot.
///
/// They are queried not for logging, but for **reconciliation**: this driver uses fixed-size buffers,
/// and their sizes are fixed at compile time. If the device requires larger packets or produces backup
/// blocks longer than the reserved space, that is a mismatch that must be exposed during boot. Delaying
/// it until runtime produces symptoms like sporadic truncation of a particular command, with no obvious
/// connection to the capacity value.
pub struct Limits {
    pub max_command: u32,
    pub max_response: u32,
    pub max_object_context: u32,
    pub max_session_context: u32,
}
pub struct Boot<P: TisPhy> {
    x: Xfer<P>,
    /// Command temporary buffer. Private: all guarantees about packet length fields in this layer rely on
    /// the fact that external code cannot modify it.
    cbuf: [u8; BOOT_CMD_MAX],
    rbuf: [u8; BOOT_RSP_MAX],
}
impl<P: TisPhy> Boot<P> {
    pub fn new(x: Xfer<P>) -> Self {
        Boot {
            x,
            cbuf: [0u8; BOOT_CMD_MAX],
            rbuf: [0u8; BOOT_RSP_MAX],
        }
    }
    /// Return the link and end the boot phase.
    pub fn finish(self) -> Xfer<P> {
        self.x
    }
    /// Write the packet header.
    ///
    /// The length field is fixed here in one shot and is not rewritten later. The boot commands all have
    /// compile-time constant payload lengths, so there is no need for a “write the payload first, then see
    /// how long it was.” That write-back is precisely the one entry point through which the length field can
    /// drift away from the actual byte count.
    fn put_header(&mut self, cc: u32, total: usize) {
        let hdr = build_header(ST_NO_SESSIONS, cc, total as u32);
        self.cbuf[..TPM_HEADER_LEN].copy_from_slice(&hdr);
    }
    /// Write a single byte payload.
    fn put_u8(&mut self, off: usize, v: u8) {
        self.cbuf[off] = v;
    }
    /// Write a big-endian u16 payload.
    fn put_be16(&mut self, off: usize, v: u16) {
        let b = be16_bytes(v);
        self.cbuf[off] = b[0];
        self.cbuf[off + 1] = b[1];
    }
    /// Write a big-endian u32 payload.
    fn put_be32(&mut self, off: usize, v: u32) {
        let b = be32_bytes(v);
        self.cbuf[off] = b[0];
        self.cbuf[off + 1] = b[1];
        self.cbuf[off + 2] = b[2];
        self.cbuf[off + 3] = b[3];
    }
    /// Send the assembled command and retrieve the response length and return code.
    ///
    /// The precondition “the length field equals `len`” is not mere ceremony: the link layer uses this
    /// field to decide how many bytes to push onto the bus. If the field does not match the actual value,
    /// the device and the host will both wait for each other and time out. Writing it as a precondition
    /// here means that this fact is ensured by the postcondition of the assembler, rather than trusting
    /// each call site to remember it.
    fn exec(&mut self, len: usize) -> Result<(usize, u32), BootErr> {
        if !self.x.ready() {
            return Err(BootErr::NotReady);
        }
        match self.x.run(&self.cbuf, len, &mut self.rbuf) {
            Ok((n, rc)) => Ok((n, rc)),
            Err(e) => Err(BootErr::Bus(e)),
        }
    }
    /// Declare the sender's startup mode.
    ///
    /// “Already started” is treated as success. The device startup state is defined by the power cycle, but
    /// this side may take over after an earlier firmware has already initialized the device. In that case,
    /// re-sending a startup command receives a rejection telling us “the required state already holds.”
    /// Treating that as a failure would cause the driver to reject loading on a perfectly normal platform.
    ///
    /// Conversely, any other non-zero return code is reported as-is, without secondary interpretation.
    pub fn startup(&mut self, su: u16) -> Result<(), BootErr> {
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
            }
            Err(e) => Err(e),
        }
    }
    /// Shut down.
    ///
    /// Unlike startup, this path does not ignore any non-zero return code: if shutdown does not succeed,
    /// the device will assume the previous power cycle ended abnormally and will reset part of its state
    /// the next time it powers up. The caller must know this.
    pub fn shutdown(&mut self, su: u16) -> Result<(), BootErr> {
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
            }
            Err(e) => Err(e),
        }
    }
    /// Trigger self-test. When `full` is true, all algorithms are re-tested; otherwise only the ones not
    /// yet tested are checked.
    ///
    /// “Still testing” is treated as success, for a different reason than the startup case: the semantics
    /// of this command are “start testing,” not “testing is complete.” If the device replies that it is
    /// still testing, that is actually proof that the command took effect. The final self-test result must
    /// be queried separately; this layer does not assume that responsibility. Treating “started” and
    /// “passed” as the same return value would make the caller believe it received the latter.
    pub fn self_test(&mut self, full: bool) -> Result<(), BootErr> {
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
            }
            Err(e) => Err(e),
        }
    }
    /// Query one fixed property value.
    ///
    /// Only one property is queried at a time. A batched query could save a few round trips, but the key
    /// value pairs in the response are ordered by the device, and code that expects them to line up one by
    /// one must handle missing entries, reordering, and duplicates. The boot phase only asks for four
    /// properties in total; the round trips saved are not worth the extra branches.
    pub fn property(&mut self, pt: u32) -> Result<u32, BootErr> {
        let total = TPM_HEADER_LEN + 12;
        self.put_header(CC_GET_CAPABILITY, total);
        self.put_be32(TPM_HEADER_LEN, CAP_TPM_PROPERTIES);
        self.put_be32(TPM_HEADER_LEN + 4, pt);
        self.put_be32(TPM_HEADER_LEN + 8, 1);
        let n = match self.exec(total) {
            Ok((n, rc)) => {
                if rc != RC_SUCCESS {
                    return Err(BootErr::Rc(rc));
                }
                n
            }
            Err(e) => return Err(e),
        };
        let raw = &self.rbuf[0..n];
        let rsp = parse_response(raw).map_err(BootErr::Parse)?;
        parse_tpm_property(rsp.body).map_err(BootErr::Parse)
    }
    /// Query all four dimensions and reconcile them against the static reservations of this driver.
    ///
    /// If reconciliation fails, report an error and do not degrade. Degradation would mean there is a
    /// runtime path of “buffer too small, so split / truncate / skip,” and that path will never be
    /// exercised on a machine with sufficient capacity, so it will never be tested. It is better to fail
    /// to load here.
    pub fn probe_limits(&mut self) -> Result<Limits, BootErr> {
        let max_command = self.property(PT_MAX_COMMAND_SIZE)?;
        let max_response = self.property(PT_MAX_RESPONSE_SIZE)?;
        let max_object_context = self.property(PT_MAX_OBJECT_CONTEXT)?;
        let max_session_context = self.property(PT_MAX_SESSION_CONTEXT)?;
        if max_response as usize > MSG_MAX {
            return Err(BootErr::Capacity);
        }
        if max_object_context as usize > MSG_MAX {
            return Err(BootErr::Capacity);
        }
        if max_session_context as usize > MSG_MAX {
            return Err(BootErr::Capacity);
        }
        Ok(Limits {
            max_command,
            max_response,
            max_object_context,
            max_session_context,
        })
    }
}
/// Move from a freshly established link to “can carry traffic,” while also returning the device
/// capacity.
///
/// The order is fixed by dependency, not habit:
///
/// 1. **Host ABI self-check result** is supplied by the caller via `abi_ok` and decided first here.
///    The self-check itself does not involve the device and is not this layer’s responsibility — it
///    touches the external interface and should be handled by the platform layer. This layer only ensures
///    “if the interface does not match, do not proceed.” It is placed first because if the interface does
///    not match, every later step fails in a hard-to-diagnose way, and it is better to stop before a
///    single byte is sent.
/// 2. **Startup**. Before the device receives the startup command, it rejects most commands.
/// 3. **Self-test**. This must be triggered before any business commands arrive, allowing it to run in
///    parallel with subsequent operations.
/// 4. **Capacity reconciliation**. This is last because it is the only step that needs to parse the
///    response payload, and payload parsing requires the device to already be in a healthy state.
///
/// Any failure in the middle immediately returns and the link is discarded. This layer has no “partial
/// success” state — if the boot process is not complete, the local side cannot say where the device is
/// currently at.
pub fn bring_up<P: TisPhy>(
    x: Xfer<P>,
    su: u16,
    abi_ok: bool,
) -> Result<(Xfer<P>, Limits), BootErr> {
    if !abi_ok {
        return Err(BootErr::Abi);
    }
    let mut b = Boot::new(x);
    match b.startup(su) {
        Ok(()) => {}
        Err(e) => return Err(e),
    }
    match b.self_test(false) {
        Ok(()) => {}
        Err(e) => return Err(e),
    }
    let lim = b.probe_limits()?;
    Ok((b.finish(), lim))
}
