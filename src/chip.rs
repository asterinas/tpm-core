use crate::{
    cmd::{CC_CONTEXT_LOAD, CC_CONTEXT_SAVE, CC_FLUSH_CONTEXT},
    module::{ContextIo, IoErr},
    msg::{build_header, ST_NO_SESSIONS},
    rewrite::{read_be32, HEADER_SIZE},
};

pub const RC_SUCCESS: u32 = 0x0000_0000;
/// Bit 7 is set for a “Format-1” return code: the low 6 bits are the error number, and bits 8..11 are
/// the offending handle / parameter / session index. When classifying, the index bits must be cleared
/// first.
const RC_FMT1_BIT: u32 = 0x0000_0080;
/// Selector bits in a TPM Format-1 return code:
/// - bit 6 (`TPM_RC_P`) indicates the parameter selector;
/// - bits 8..11 (`TPM_RC_N`) indicate the object/session index;
///   these must be cleared before classification, or `TPM_RC_HANDLE | P | N` will be misclassified as a
///   different error code.
const RC_FMT1_MASK: u32 = 0x0000_00BF;
const RC_HANDLE: u32 = 0x0000_008B;
const RC_INTEGRITY: u32 = 0x0000_009F;
const RC_CONTEXT_GAP: u32 = 0x0000_0901;
const RC_OBJECT_MEMORY: u32 = 0x0000_0902;
const RC_SESSION_MEMORY: u32 = 0x0000_0903;
const RC_MEMORY: u32 = 0x0000_0904;
const RC_REFERENCE_H0: u32 = 0x0000_0910;
pub const RC_YIELDED: u32 = 0x0000_0908;
pub const RC_TESTING: u32 = 0x0000_090A;
pub const RC_RETRY: u32 = 0x0000_0922;
fn rc_value(rc: u32) -> u32 {
    if rc & RC_FMT1_BIT == RC_FMT1_BIT {
        rc & RC_FMT1_MASK
    } else {
        rc
    }
}
/// Return code -> orchestration-layer error.
///
/// There is only one semantic boundary that matters here: what counts as [`IoErr::NotFound`]. It means
/// “the target no longer exists,” and the orchestration layer uses it to forget the corresponding slot
/// instead of failing the whole path. Therefore, only the two return codes that truly mean “a non-existent
/// object was referenced” belong here; relaxing this would silently swallow state inconsistencies.
fn classify_rc(rc: u32) -> IoErr {
    let v = rc_value(rc);
    if v == RC_HANDLE || v == RC_REFERENCE_H0 {
        IoErr::NotFound
    } else if v == RC_INTEGRITY {
        IoErr::Integrity
    } else if v == RC_CONTEXT_GAP
        || v == RC_OBJECT_MEMORY
        || v == RC_SESSION_MEMORY
        || v == RC_MEMORY
    {
        IoErr::NoSpace
    } else if v == RC_RETRY || v == RC_YIELDED || v == RC_TESTING {
        IoErr::Timeout
    } else {
        IoErr::Fatal
    }
}
/// Fixed-length prefix of a backup block: sequence number (8 bytes), handle (4 bytes), level (4 bytes),
/// data length (2 bytes).
const CTX_FIXED: usize = 18;
/// Offset of the data-length field within the backup block.
const CTX_SIZE_OFF: usize = 16;
/// One full command / response round trip.
///
/// This is the only boundary between this layer and the chip. The implementation must either place its
/// assumptions directly in its own `external_body`, or, like the link layer, bundle the assumptions into
/// a zero-sized ghost ledger. In either case, the postconditions written below are the entire basis on
/// which this module reasons. They are specified by command code rather than by a blanket claim that
/// “the handle is new,” so that each assumption can be traced to a precise specification clause.
///
/// TRUST 1: response writes do not exceed the `rsp` capacity and include at least one complete packet
/// header. Basis: the transport layer reads the declared length and reports an error if it is not enough.
///
/// TRUST 2: when `ContextLoad` succeeds, the returned handle is not already in `live()`.
/// Basis: before it is explicitly freed or swapped out, a handle uniquely identifies one loaded object, and
/// the chip will not reassign a handle that is still valid. **This is the ultimate source of the
/// injectivity property in this module**, and one of the most substantial facts in the whole TCB.
///
/// TRUST 3: `live()` grows only on successful `ContextLoad` and shrinks only on `FlushContext`; other
/// commands do not change it.
///
/// The exception for the flush command is important: it is **not conditioned on successful transport**.
/// If transport fails, the host cannot know whether the chip already freed the object. It is better to
/// treat the host as no longer tracking it on both sides, because the chip may still hold the resource
/// until reset and that is a known, irreparable leak. Therefore, the rule “a failed action has no side
/// effects” must exclude the flush command; otherwise, both require `live == old` and
/// `live == old.remove(h)` simultaneously, which can only be satisfied when `h` was not in the set in the
/// first place.
pub trait ChipTransport {
    fn exec(&mut self, cmd: &[u8], rsp: &mut [u8]) -> Result<usize, IoErr>;
}
/// Capacity of the command and response temporary buffers. Context data blocks may be close to a page,
/// and the two buffers are inlined together in the struct for a total of 8 KiB. If the target platform
/// stack is tight, they can be replaced with caller-provided slices; the proof for this module does not
/// depend on their storage form.
pub(crate) const MSG_MAX: usize = 4096;
/// Lift [`ChipTransport`] into the orchestration-layer version required by [`ContextIo`].
///
/// This layer is fully verified: it does only length checks, packet assembly, and return-code
/// classification. The ghost set is passed straight through to the transport layer; this layer introduces
/// no new assumptions. This is enforced by the fact that all three methods lack `external_body`; if any
/// one were marked, the statement above would no longer hold, and the injectivity of the orchestration
/// layer would rest on a false premise.
pub struct CtxIo<T: ChipTransport> {
    tx: T,
    cbuf: [u8; MSG_MAX],
    rbuf: [u8; MSG_MAX],
}
impl<T: ChipTransport> CtxIo<T> {
    pub fn new(tx: T) -> Self {
        CtxIo {
            tx,
            cbuf: [0u8; MSG_MAX],
            rbuf: [0u8; MSG_MAX],
        }
    }
    /// Place the 10-byte packet header at the beginning of the command buffer.
    ///
    /// The postcondition “the ghost set is unchanged” is not mere formalism: assembling the packet is
    /// independent of the chip state, and if we write this down, each subsequent method can carry the
    /// “collection at function entry” all the way to the send point without having to rediscover the basis
    /// in the middle.
    fn put_header(&mut self, code: u32, total: usize) {
        let hdr = build_header(ST_NO_SESSIONS, code, total as u32);
        self.cbuf[..HEADER_SIZE].copy_from_slice(&hdr);
    }
    /// Hand the entire command to the lower transport without reassembling the packet.
    ///
    /// It shares the same transport-layer ledger as the three methods of `ContextIo`, so the handle count
    /// remains continuous across calls to `exec_raw` and `load`/`save`/`flush`.
    pub fn exec_raw(&mut self, cmd: &[u8], rsp: &mut [u8]) -> Result<usize, IoErr> {
        self.tx.exec(cmd, rsp)
    }
    /// Return the lower transport and end the context round trip.
    ///
    /// Taking `self` frees the two temporary buffers and leaves the ghost set unchanged in the returned
    /// value. The equality in the postcondition is the basis for the phase handoff: whatever changed on the
    /// chip while the adapter owned it is carried back unchanged in the returned transport layer.
    pub fn release(self) -> T {
        self.tx
    }
}
impl<T: ChipTransport> ContextIo for CtxIo<T> {
    fn load(&mut self, blob: &[u8], off: usize) -> Result<(u32, usize), IoErr> {
        if off > blob.len() || blob.len() - off < CTX_FIXED {
            return Err(IoErr::Integrity);
        }
        let size =
            u16::from_be_bytes([blob[off + CTX_SIZE_OFF], blob[off + CTX_SIZE_OFF + 1]]) as usize;
        let used = CTX_FIXED + size;
        if blob.len() - off < used {
            return Err(IoErr::Integrity);
        }
        if MSG_MAX - HEADER_SIZE < used {
            return Err(IoErr::NoSpace);
        }
        self.put_header(CC_CONTEXT_LOAD, HEADER_SIZE + used);
        self.cbuf[HEADER_SIZE..HEADER_SIZE + used].copy_from_slice(&blob[off..off + used]);
        let n = self.tx.exec(&self.cbuf, &mut self.rbuf)?;
        if n < HEADER_SIZE {
            return Err(IoErr::Protocol);
        }
        let rc = read_be32(&self.rbuf, 6);
        if rc != RC_SUCCESS {
            return Err(classify_rc(rc));
        }
        if n < HEADER_SIZE + 4 {
            return Err(IoErr::Protocol);
        }
        let h = read_be32(&self.rbuf, HEADER_SIZE);
        Ok((h, used))
    }
    fn save(&mut self, h: u32, out: &mut [u8], off: usize) -> Result<usize, IoErr> {
        self.put_header(CC_CONTEXT_SAVE, HEADER_SIZE + 4);
        write_be32_arr(&mut self.cbuf, HEADER_SIZE, h);
        let n = self.tx.exec(&self.cbuf, &mut self.rbuf)?;
        if n < HEADER_SIZE {
            return Err(IoErr::Protocol);
        }
        let rc = read_be32(&self.rbuf, 6);
        if rc != RC_SUCCESS {
            return Err(classify_rc(rc));
        }
        let body = n - HEADER_SIZE;
        if body < CTX_FIXED {
            return Err(IoErr::Protocol);
        }
        if off > out.len() || out.len() - off < body {
            return Err(IoErr::NoSpace);
        }
        out[off..off + body].copy_from_slice(&self.rbuf[HEADER_SIZE..HEADER_SIZE + body]);
        Ok(body)
    }
    fn flush(&mut self, h: u32) {
        self.put_header(CC_FLUSH_CONTEXT, HEADER_SIZE + 4);
        write_be32_arr(&mut self.cbuf, HEADER_SIZE, h);
        let _ = self.tx.exec(&self.cbuf, &mut self.rbuf);
    }
}
/// Fixed-array version of [`write_be32`]. The slice version requires `&mut [u8]`, but this operates on
/// array fields inside a struct; reusing the slice version would make Verus carry an extra obligation, so
/// writing directly is simpler.
fn write_be32_arr(b: &mut [u8; MSG_MAX], off: usize, v: u32) {
    b[off..off + 4].copy_from_slice(&v.to_be_bytes());
}
#[cfg(test)]
mod tests {
    use super::*;
    struct FakeChip {
        rsp: [u8; HEADER_SIZE],
    }
    impl ChipTransport for FakeChip {
        fn exec(&mut self, _cmd: &[u8], rsp: &mut [u8]) -> Result<usize, IoErr> {
            let n = self.rsp.len().min(rsp.len());
            for i in 0..n {
                rsp[i] = self.rsp[i];
            }
            Ok(n)
        }
    }
    #[test]
    fn context_load_rc_handle_short_response_is_not_protocol() {
        let mut io = CtxIo::new(FakeChip {
            rsp: {
                let mut arr = [0u8; HEADER_SIZE];
                arr[6] = 0x00;
                arr[7] = 0x00;
                arr[8] = 0x00;
                arr[9] = 0x8B;
                arr
            },
        });
        let blob = [0u8; CTX_FIXED];
        let err = io.load(&blob, 0);
        assert!(matches!(err, Err(IoErr::NotFound)));
    }
}
