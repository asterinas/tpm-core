use vstd::prelude::*;
use vstd::set::Set;

use crate::cmd::{CC_CONTEXT_LOAD, CC_CONTEXT_SAVE, CC_FLUSH_CONTEXT};
#[cfg(verus_keep_ghost)]
use crate::cursor::spec_be32_at;
#[cfg(verus_keep_ghost)]
use crate::endian::be32_of;
#[cfg(verus_keep_ghost)]
use crate::handle::valid_phandle;
use crate::module::{ContextIo, IoErr};
use crate::msg::{ST_NO_SESSIONS, build_header};
#[cfg(verus_keep_ghost)]
use crate::rewrite::be32_at;
use crate::rewrite::{HEADER_SIZE, read_be32, write_be32};

verus! {

// ---------------------------------------------------------------------------
// Return codes
// ---------------------------------------------------------------------------

pub const RC_SUCCESS: u32 = 0x0000_0000;

/// Bit 7 set means a "format one" return code: the low 6 bits are the error number, and bits 8..11 are the index of the offending
/// handle / parameter / session. The index bits must be wiped before classifying.
pub const RC_FMT1_BIT: u32 = 0x0000_0080;
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

/// Wipe the selector bits in a format-one return code (`TPM_RC_P`/`TPM_RC_N_MASK`, etc.),
/// keeping only the real error number, so that it lines up with `RC_HANDLE` / `RC_REFERENCE_H0`.
pub open spec fn spec_rc_value(rc: u32) -> u32 {
    if rc & RC_FMT1_BIT == RC_FMT1_BIT {
        rc & 0xBFu32
    } else {
        rc
    }
}

fn rc_value(rc: u32) -> (r: u32)
    ensures
        r == spec_rc_value(rc),
{
    if rc & RC_FMT1_BIT == RC_FMT1_BIT {
        rc & RC_FMT1_MASK
    } else {
        rc
    }
}

/// Return code -> orchestration-layer error.
///
/// Only one semantic boundary of the classification matters: what counts as [`IoErr::NotFound`]. It means "the target
/// no longer exists", and the orchestration layer uses it to simply forget the corresponding slot instead of failing the whole path -- so
/// only the two return codes that truly mean "referenced a nonexistent object" may go here; widening it would let state
/// inconsistencies be swallowed silently.
fn classify_rc(rc: u32) -> (r: IoErr) {
    let v = rc_value(rc);
    if v == RC_HANDLE || v == RC_REFERENCE_H0 {
        IoErr::NotFound
    } else if v == RC_INTEGRITY {
        IoErr::Integrity
    } else if v == RC_CONTEXT_GAP || v == RC_OBJECT_MEMORY || v == RC_SESSION_MEMORY || v
        == RC_MEMORY {
        IoErr::NoSpace
    } else if v == RC_RETRY || v == RC_YIELDED || v == RC_TESTING {
        IoErr::Timeout
    } else {
        IoErr::Fatal
    }
}

// ---------------------------------------------------------------------------
// Backup block layout
// ---------------------------------------------------------------------------

/// Fixed-length prefix of a backup block: sequence number 8 bytes, handle 4 bytes, hierarchy 4 bytes, data length 2 bytes.
pub const CTX_FIXED: usize = 18;

/// Offset of the data length field within the backup block.
pub const CTX_SIZE_OFF: usize = 16;

/// How many bytes the block starting at `off` in the backup buffer occupies.
pub open spec fn spec_ctx_len(s: Seq<u8>, off: int) -> int {
    CTX_FIXED + (s[off + CTX_SIZE_OFF] as int) * 256 + (s[off + CTX_SIZE_OFF + 1] as int)
}

// ---------------------------------------------------------------------------
// A bridge between two ways of writing byte order
// ---------------------------------------------------------------------------

/// `endian` uses shift-or and `cursor` uses multiply-add; the two are the same function written two ways.
///
/// The message header is produced by `build_header` (the spec uses the multiply-add form), while the handle area is read by
/// `rewrite::read_be32` (the spec uses the shift-or form), so cross-module reasoning must go through
/// this lemma first. **This is the price of the duplicated definition**; it can be deleted once the specs are merged.
pub proof fn lemma_be32_forms_agree(s: Seq<u8>, off: int)
    requires
        0 <= off,
        off + 4 <= s.len(),
    ensures
        be32_at(s, off) == spec_be32_at(s, off),
{
    let b0 = s[off];
    let b1 = s[off + 1];
    let b2 = s[off + 2];
    let b3 = s[off + 3];
    assert(be32_of(b0, b1, b2, b3) == (b0 as u32) * 16777216 + (b1 as u32) * 65536 + (b2 as u32)
        * 256 + (b3 as u32)) by (bit_vector);
}

// ---------------------------------------------------------------------------
// Chip interface (trust base)
// ---------------------------------------------------------------------------

/// One complete command / response round trip.
///
/// This is the only point of contact between this layer and the chip. The implementer either puts the assumptions directly in their own
/// `external_body`, or, as the link layer does, collects them into a zero-sized ghost ledger;
/// either way, the postconditions written below are **the entire basis on which this module reasons**. They are given case by case on the command
/// code, instead of broadly asserting "the handle is new" -- so each assumption can be pointed at a specific
/// clause of the specification.
///
/// TRUST 1: the response is written within the capacity of `rsp` and contains at least one complete message header.
/// Basis: the transport layer receives bytes according to the declared length and reports an error if they fall short.
///
/// TRUST 2: on a successful ContextLoad, the returned handle is not in `live()`.
/// Basis: a handle uniquely identifies a loaded object until it is explicitly released or swapped out; the chip never hands out
/// a still-valid handle a second time. **This is the ultimate source of this module's injectivity**,
/// and the most substantive item in the whole TCB.
///
/// TRUST 3: `live()` grows only on a successful ContextLoad and shrinks on FlushContext;
/// other commands do not change it.
///
/// The exception for the release command: it is **not conditioned on transport success**. When the transport fails, this side cannot know
/// whether the chip has released it; rather than being uncertain on both sides, it is uniformly treated as "this side no longer tracks it" -- if the chip
/// did not actually release it, that resource stays occupied until reset, a known leak with no remedy. Therefore
/// the "failure has no side effect" clause must exclude the release command, otherwise the two clauses would require
/// both `live == old` and `live == old.remove(h)`, which can both hold only when `h` was not in the set to begin with,
/// and no implementer could satisfy that.
pub trait ChipTransport {
    /// The set of handles the chip currently holds. Pure ghost state, no runtime overhead.
    spec fn live(&self) -> Set<u32>;

    fn exec(&mut self, cmd: &[u8], rsp: &mut [u8]) -> (r: Result<usize, IoErr>)
        requires
            cmd.len() >= HEADER_SIZE + 4,
            old(rsp).len() >= HEADER_SIZE + 4,
        ensures
            final(rsp).len() == old(rsp).len(),
            r.is_ok() ==> HEADER_SIZE <= r.unwrap() <= final(rsp).len(),
            // Transport failure: no side effect. The release command is the exception; see the note above.
            (r.is_err() && be32_at(cmd@, 6) != CC_FLUSH_CONTEXT) ==> final(self).live() == old(
                self,
            ).live(),
            // ContextLoad succeeded with return code zero
            (r.is_ok() && be32_at(cmd@, 6) == CC_CONTEXT_LOAD && be32_at(final(rsp)@, 6)
                == RC_SUCCESS) ==> {
                &&& r.unwrap() >= HEADER_SIZE + 4
                &&& valid_phandle(be32_at(final(rsp)@, HEADER_SIZE as int))
                &&& !old(self).live().contains(be32_at(final(rsp)@, HEADER_SIZE as int))
                &&& final(self).live() == old(self).live().insert(
                    be32_at(final(rsp)@, HEADER_SIZE as int),
                )
            },
            // ContextLoad did not succeed
            (be32_at(cmd@, 6) == CC_CONTEXT_LOAD && (r.is_err() || be32_at(final(rsp)@, 6)
                != RC_SUCCESS)) ==> final(self).live() == old(self).live(),
            // FlushContext: whether or not the transport layer reports an error, the handle is no longer tracked
            be32_at(cmd@, 6) == CC_FLUSH_CONTEXT ==> final(self).live() == old(self).live().remove(
                be32_at(cmd@, HEADER_SIZE as int),
            ),
            // Other commands
            (be32_at(cmd@, 6) != CC_CONTEXT_LOAD && be32_at(cmd@, 6) != CC_FLUSH_CONTEXT)
                ==> final(self).live() == old(self).live(),
    ;
}

// ---------------------------------------------------------------------------
// Adapter
// ---------------------------------------------------------------------------

/// Capacity of the command and response scratch areas. A context data block can approach a page, and the two buffers
/// inlined in the struct total 8 KiB; if the target platform has a tight stack, replace them with
/// caller-provided slices -- the proofs of this module do not depend on how they are stored.
pub(crate) const MSG_MAX: usize = 4096;

/// Lift [`ChipTransport`] to the [`ContextIo`] the orchestration layer needs.
///
/// This layer is fully verified: everything it does is length checking, message assembly and return-code classification.
/// The ghost set is passed straight through to the transport layer, and this layer introduces no new assumptions -- this is guaranteed by none of the three methods
/// carrying `external_body`; if any one were marked, the sentence above would no longer hold,
/// and the injectivity of the orchestration layer is built on exactly that sentence.
pub struct CtxIo<T: ChipTransport> {
    tx: T,
    cbuf: [u8; MSG_MAX],
    rbuf: [u8; MSG_MAX],
}

impl<T: ChipTransport> CtxIo<T> {
    pub fn new(tx: T) -> (r: Self)
        ensures
            r.tx_live() == tx.live(),
    {
        CtxIo { tx, cbuf: [0u8; MSG_MAX], rbuf: [0u8; MSG_MAX] }
    }

    pub closed spec fn tx_live(&self) -> Set<u32> {
        self.tx.live()
    }

    /// Lay the 10-byte message header at the start of the command buffer.
    ///
    /// The postcondition "the ghost set is unchanged" is not formalism: assembling the message has nothing to do with the chip state,
    /// and writing this down is what lets every later method carry "the set on entering the function" all the way to
    /// the moment of sending, without having to find justification for it again midway.
    fn put_header(&mut self, code: u32, total: usize)
        requires
            total <= MSG_MAX,
        ensures
            final(self).cbuf@.len() == MSG_MAX,
            be32_at(final(self).cbuf@, 6) == code,
            final(self).tx_live() == old(self).tx_live(),
    {
        let hdr = build_header(ST_NO_SESSIONS, code, total as u32);
        for k in 0..HEADER_SIZE
            invariant
                self.cbuf@.len() == MSG_MAX,
                self.tx_live() == old(self).tx_live(),
                forall|j: int| #![trigger self.cbuf@[j]] 0 <= j < k ==> self.cbuf@[j] == hdr@[j],
        {
            self.cbuf[k] = hdr[k];
        }
        proof {
            lemma_be32_forms_agree(self.cbuf@, 6);
            assert(self.cbuf@.subrange(0, HEADER_SIZE as int) =~= hdr@);
        }
    }

    /// Hand the whole command to the underlying transport as is, without message assembly.
    ///
    /// It shares the same transport-layer ledger with the three `ContextIo` methods, so when calls alternate between `exec_raw`
    /// and `load`/`save`/`flush`, handle bookkeeping stays continuous.
    pub fn exec_raw(&mut self, cmd: &[u8], rsp: &mut [u8]) -> (r: Result<usize, IoErr>)
        requires
            cmd.len() >= HEADER_SIZE + 4,
            old(rsp).len() >= HEADER_SIZE + 4,
        ensures
            final(rsp).len() == old(rsp).len(),
            r.is_ok() ==> HEADER_SIZE <= r.unwrap() <= final(rsp).len(),
            (r.is_err() && be32_at(cmd@, 6) != CC_FLUSH_CONTEXT) ==> final(self).tx_live()
                == old(self).tx_live(),
            (r.is_ok() && be32_at(cmd@, 6) == CC_CONTEXT_LOAD && be32_at(final(rsp)@, 6)
                == RC_SUCCESS) ==> {
                &&& r.unwrap() >= HEADER_SIZE + 4
                &&& valid_phandle(be32_at(final(rsp)@, HEADER_SIZE as int))
                &&& !old(self).tx_live().contains(be32_at(final(rsp)@, HEADER_SIZE as int))
                &&& final(self).tx_live() == old(self).tx_live().insert(
                    be32_at(final(rsp)@, HEADER_SIZE as int),
                )
            },
            (be32_at(cmd@, 6) == CC_CONTEXT_LOAD && (r.is_err() || be32_at(final(rsp)@, 6)
                != RC_SUCCESS)) ==> final(self).tx_live() == old(self).tx_live(),
            be32_at(cmd@, 6) == CC_FLUSH_CONTEXT ==> final(self).tx_live() == old(self).tx_live()
                .remove(be32_at(cmd@, HEADER_SIZE as int)),
            (be32_at(cmd@, 6) != CC_CONTEXT_LOAD && be32_at(cmd@, 6) != CC_FLUSH_CONTEXT)
                ==> final(self).tx_live() == old(self).tx_live(),
    {
        self.tx.exec(cmd, rsp)
    }

    /// Hand back the underlying transport, ending the context round-trip phase.
    ///
    /// Takes `self`, the two scratch areas are released with it, and the ghost set lands on the return value unchanged. The equality in the postcondition
    /// is the basis of the phase handoff: whatever this adapter did to the chip while in custody, the transport layer handed back
    /// accepts as is, without recomputing or clearing.
    pub fn release(self) -> (r: T)
        ensures
            r.live() == self.tx_live(),
    {
        self.tx
    }
}

impl<T: ChipTransport> ContextIo for CtxIo<T> {
    open spec fn outstanding(&self) -> Set<u32> {
        self.tx_live()
    }

    fn load(&mut self, blob: &[u8], off: usize) -> (r: Result<(u32, usize), IoErr>) {
        let ghost live0 = self.tx_live();

        // ---- Length check: the fixed-length prefix first, then the variable-length data ----
        if off > blob.len() || blob.len() - off < CTX_FIXED {
            return Err(IoErr::Integrity);
        }
        let size = (blob[off + CTX_SIZE_OFF] as usize) * 256 + (blob[off + CTX_SIZE_OFF + 1]
            as usize);
        let used = CTX_FIXED + size;
        if blob.len() - off < used {
            return Err(IoErr::Integrity);
        }
        if MSG_MAX - HEADER_SIZE < used {
            return Err(IoErr::NoSpace);
        }

        // ---- Assembly: header + the backup block carried over as is ----
        self.put_header(CC_CONTEXT_LOAD, HEADER_SIZE + used);
        for k in 0..used
            invariant
                off + used <= blob.len(),
                HEADER_SIZE + used <= MSG_MAX,
                self.cbuf@.len() == MSG_MAX,
                be32_at(self.cbuf@, 6) == CC_CONTEXT_LOAD,
                self.tx_live() == live0,
        {
            self.cbuf[HEADER_SIZE + k] = blob[off + k];
        }

        // ---- Round trip ----
        //
        // The command code must still be load at this point: the interface's postconditions are given case by case on the command code, and if the command
        // code does not match, none of those conditions can be used. The copy loop writes the area after the message header, and the four
        // header bytes were never touched; this is carried by the loop invariant all the way to here.
        proof {
            assert(be32_at(self.cbuf@, 6) == CC_CONTEXT_LOAD);
        }
        let n = match self.tx.exec(&self.cbuf, &mut self.rbuf) {
            Ok(n) => n,
            Err(e) => {
                return Err(e);
            },
        };
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

    fn save(&mut self, h: u32, out: &mut [u8], off: usize) -> (r: Result<usize, IoErr>) {
        let ghost live0 = self.tx_live();
        let out_len = out.len();

        self.put_header(CC_CONTEXT_SAVE, HEADER_SIZE + 4);
        write_be32_arr(&mut self.cbuf, HEADER_SIZE, h);
        // The handle is written after the message header; the four header bytes are not within the written range.
        proof {
            assert(be32_at(self.cbuf@, 6) == CC_CONTEXT_SAVE);
        }

        let n = match self.tx.exec(&self.cbuf, &mut self.rbuf) {
            Ok(n) => n,
            Err(e) => {
                return Err(e);
            },
        };
        if n < HEADER_SIZE {
            return Err(IoErr::Protocol);
        }
        let rc = read_be32(&self.rbuf, 6);
        if rc != RC_SUCCESS {
            return Err(classify_rc(rc));
        }

        // The response body is the backup block itself, landing in the backup buffer as is.
        let body = n - HEADER_SIZE;
        if body < CTX_FIXED {
            return Err(IoErr::Protocol);
        }
        if off > out.len() || out.len() - off < body {
            return Err(IoErr::NoSpace);
        }
        for k in 0..body
            invariant
                out.len() == out_len,
                off + body <= out.len(),
                HEADER_SIZE + body <= self.rbuf@.len(),
                self.tx_live() == live0,
        {
            out[off + k] = self.rbuf[HEADER_SIZE + k];
        }
        assert(out.len() == out_len);
        Ok(body)
    }

    fn flush(&mut self, h: u32) {
        let ghost live0 = self.tx_live();

        self.put_header(CC_FLUSH_CONTEXT, HEADER_SIZE + 4);
        write_be32_arr(&mut self.cbuf, HEADER_SIZE, h);
        proof {
            assert(be32_at(self.cbuf@, 6) == CC_FLUSH_CONTEXT);
            assert(be32_at(self.cbuf@, HEADER_SIZE as int) == h);
        }

        // The return value is deliberately dropped: a failed release has no remedy, and all call sites are on error-handling paths.
        // The shrinking of the ghost set does not depend on this return value -- the interface's spec for the release command is
        // not conditioned on transport success to begin with.
        let _ = self.tx.exec(&self.cbuf, &mut self.rbuf);
    }
}

/// The fixed-length array version of [`write_be32`]. The slice version requires `&mut [u8]`, while what is operated on here is an array field
/// of the struct, and reborrowing would add another layer of obligations for Verus; writing it directly is simpler.
fn write_be32_arr(b: &mut [u8; MSG_MAX], off: usize, v: u32)
    requires
        off + 4 <= MSG_MAX,
    ensures
        be32_at(final(b)@, off as int) == v,
        forall|k: int|
            #![trigger final(b)@[k]]
            0 <= k < MSG_MAX && (k < off || k >= off + 4) ==> final(b)@[k] == old(b)@[k],
{
    proof {
        crate::endian::lemma_be32_roundtrip(v);
    }
    b[off] = ((v >> 24) & 0xff) as u8;
    b[off + 1] = ((v >> 16) & 0xff) as u8;
    b[off + 2] = ((v >> 8) & 0xff) as u8;
    b[off + 3] = (v & 0xff) as u8;
}

#[cfg(test)]
mod tests {
    use super::*;
    use vstd::set::Set;

    struct FakeChip {
        live: Set<u32>,
        rsp: [u8; HEADER_SIZE],
    }

    impl ChipTransport for FakeChip {
        spec fn live(&self) -> Set<u32> {
            self.live
        }

        fn exec(&mut self, _cmd: &[u8], rsp: &mut [u8]) -> (r: Result<usize, IoErr>) {
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
            live: Set::empty(),
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

} // verus!