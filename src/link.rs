use crate::{
    chip::{ChipTransport, RC_SUCCESS},
    cmd::{CC_CONTEXT_LOAD, CC_FLUSH_CONTEXT},
    module::IoErr,
    phy::TisPhy,
    rewrite::HEADER_SIZE,
    xfer::{peek_be32, Xfer, XferErr},
};

/// The set of handles currently held by the chip.
///
/// This is a phantom field-only type at runtime and is zero-sized. All its mutating methods have no
/// executable code; they are not “recording” anything, but rather stating the local side’s assumptions
/// about chip behavior.
pub struct LiveSet;
impl LiveSet {
    pub fn new() -> Self {
        Self
    }
    pub fn observe_load(&mut self, _h: u32) {}
    pub fn observe_flush(&mut self) {}
}

impl Default for LiveSet {
    fn default() -> Self {
        Self::new()
    }
}
pub struct ChipLink<P: TisPhy> {
    pub x: Xfer<P>,
    pub ledger: LiveSet,
}
impl<P: TisPhy> ChipLink<P> {
    pub fn new(x: Xfer<P>) -> Self {
        ChipLink {
            x,
            ledger: LiveSet::new(),
        }
    }
}
impl<P: TisPhy> ChipTransport for ChipLink<P> {
    fn exec(&mut self, cmd: &[u8], rsp: &mut [u8]) -> Result<usize, IoErr> {
        let cc = peek_be32(cmd, 6);
        if cc == CC_FLUSH_CONTEXT {
            self.ledger.observe_flush();
        }
        if !self.x.ready() {
            return Err(IoErr::NotReady);
        }
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
                    if n < HEADER_SIZE + 4 {
                        return Err(IoErr::Protocol);
                    }
                    let h = peek_be32(&*rsp, HEADER_SIZE);
                    self.ledger.observe_load(h);
                }
                n
            }
            Err(e) => {
                return Err(map_err(e));
            }
        };
        Ok(n)
    }
}
/// Link error → orchestration-layer error.
///
/// The link layer has no readable return code on failure, so this only classifies the “transport
/// semantics”: timeouts are retryable, physical faults are not, protocol frames are untrusted, and the
/// command’s self-description is inconsistent.
pub fn map_err(e: XferErr) -> IoErr {
    match e {
        XferErr::Bus(crate::tis::TisErr::Phy) => IoErr::Bus,
        XferErr::Bus(crate::tis::TisErr::Timeout) => IoErr::Timeout,
        XferErr::Bus(crate::tis::TisErr::Protocol) => IoErr::Protocol,
        XferErr::Bus(crate::tis::TisErr::BadLength) => IoErr::Protocol,
        XferErr::BadCommand => IoErr::BadCommand,
    }
}
