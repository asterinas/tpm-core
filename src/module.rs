pub use crate::{
    handle::{
        is_session_exec as is_session, is_transient_exec as is_transient,
        valid_phandle_exec as valid_phandle, SLOTS,
    },
    rewrite::{HeaderOutcome, SpaceErr},
    table::{CtxSlot, SpaceTable},
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IoErr {
    /// The target no longer exists: the context was externally released or the counter no longer
    /// matches. Recoverable — the corresponding slot can simply be forgotten.
    NotFound,
    /// Backup data integrity check failed.
    Integrity,
    /// The backup buffer is too small.
    NoSpace,
    /// Polling budget exhausted; pure wait timeout, worth retrying with backoff.
    Timeout,
    /// Physical bus failure; retries are pointless.
    Bus,
    /// The chip returned data that violates protocol conventions (length, status bits, or specification
    /// mismatches).
    Protocol,
    /// The command the caller passed is internally inconsistent (length field does not match the buffer).
    /// This is a coding-layer logic error, not a device fault.
    BadCommand,
    /// Calling-order error: the interface was called when its preconditions were not satisfied.
    NotReady,
    /// The internal invariant between the table and chip state has already been broken; the only safe
    /// action is to clear everything and start over.
    Fatal,
}
/// Abstract interface for context access.
///
/// Implementations are provided by the outer layer; they build the request/response packets and classify
/// return codes, which are the responsibilities of the encoding/decoding layer. This module depends only
/// on the preconditions and postconditions written here.
pub trait ContextIo {
    /// Load a context from `blob[off..]` and return the new handle plus the number of bytes consumed.
    fn load(&mut self, blob: &[u8], off: usize) -> Result<(u32, usize), IoErr>;
    /// Save the context for `h` into `out[off..]` and return the number of bytes written.
    ///
    /// Saving itself does not release the handle; release must be done explicitly via [`ContextIo::flush`].
    fn save(&mut self, h: u32, out: &mut [u8], off: usize) -> Result<usize, IoErr>;
    /// Release a handle on the chip. Idempotent, no error return — if release fails, there is no
    /// recovery path, and the call sites are all on error-handling paths.
    fn flush(&mut self, h: u32);
}
/// User-visible handle space. The backup buffers are not stored here — this layer does not perform
/// allocation and relies on the outer layer to provide slices as needed.
pub struct Space {
    tbl: SpaceTable,
}
/// A working copy for a single request. Only [`Space::commit`] writes it back.
///
/// It does not implement `Clone`, and there is no public constructor: the only way to obtain it is
/// [`Space::begin`], and the only consequence of dropping it is rollback.
pub struct Transaction {
    work: SpaceTable,
}
impl Space {
    pub fn new() -> Self {
        Space {
            tbl: SpaceTable::new(),
        }
    }
}

impl Default for Space {
    fn default() -> Self {
        Self::new()
    }
}

impl Space {
    /// Take a working copy. The user-visible state remains unchanged during this period.
    pub fn begin(&self) -> Transaction {
        Transaction { work: self.tbl }
    }
    /// Write the working copy back. Only called when the entire path succeeds.
    pub fn commit(&mut self, t: Transaction) {
        self.tbl = t.work;
    }
}
impl Transaction {
    pub fn table(&mut self) -> &mut SpaceTable {
        &mut self.work
    }
    /// Cleanup after transaction failure: release residual handles on the chip, then discard the copy.
    ///
    /// `self` is taken by value instead of borrowed — after cleanup, this transaction can no longer be
    /// committed.
    pub fn abort<I: ContextIo>(self, io: &mut I) {
        let mut t = self;
        flush_all(&mut t.work, io);
    }
}
/// Release all live handles and all sessions from the table and clear both tables.
///
/// This is the cleanup action on error paths: after this call, no residual state from this space remains
/// on the chip.
fn flush_all<I: ContextIo>(tbl: &mut SpaceTable, io: &mut I) {
    for i in 0..SLOTS {
        if let CtxSlot::Live(h) = tbl.slot_at(i) {
            io.flush(h);
        }
        tbl.set_slot_free(i, false);
    }
    for i in 0..SLOTS {
        let h = tbl.session_at(i);
        if h != 0 {
            io.flush(h);
            tbl.clear_session(i);
        }
    }
}
/// Load all contexts from the backup buffers back onto the chip.
///
/// On success, no slot remains in the “saved” state — every non-empty slot corresponds to a real handle
/// that exists on the chip.
///
/// Session handling differs from objects: failed session loads are simply forgotten (the slot is cleared)
/// instead of causing the entire operation to fail. Sessions may legitimately disappear due to external
/// release, and that is considered normal.
pub fn load_space<I: ContextIo>(
    tbl: &mut SpaceTable,
    io: &mut I,
    ctx_buf: &[u8],
    ses_buf: &[u8],
) -> Result<(), IoErr> {
    let mut off: usize = 0;
    for i in 0..SLOTS {
        match tbl.slot_at(i) {
            CtxSlot::Empty => {}
            CtxSlot::Live(_) => {
                flush_all(tbl, io);
                return Err(IoErr::NotReady);
            }
            CtxSlot::Saved => match io.load(ctx_buf, off) {
                Ok((h, used)) => {
                    tbl.set_slot_live(i, h);
                    off += used;
                }
                Err(e) => {
                    flush_all(tbl, io);
                    return Err(e);
                }
            },
        }
    }
    let mut off: usize = 0;
    for i in 0..SLOTS {
        if tbl.session_at(i) != 0 {
            match io.load(ses_buf, off) {
                Ok((h, used)) => {
                    if h != tbl.session_at(i) {
                        flush_all(tbl, io);
                        return Err(IoErr::Integrity);
                    }
                    off += used;
                }
                Err(IoErr::NotFound) => {
                    tbl.clear_session(i);
                }
                Err(e) => {
                    flush_all(tbl, io);
                    return Err(e);
                }
            }
        }
    }
    Ok(())
}
/// Save all transient objects belonging to this space back into the backup buffers and release them.
///
/// On success, there are no live slots left in the table and no transient objects from this space remain
/// held on the chip — this is exactly the property that “the chip is clean after the transaction ends”.
pub fn save_space<I: ContextIo>(
    tbl: &mut SpaceTable,
    io: &mut I,
    ctx_buf: &mut [u8],
    ses_buf: &mut [u8],
) -> Result<(), IoErr> {
    let mut off: usize = 0;
    for i in 0..SLOTS {
        if let CtxSlot::Live(h) = tbl.slot_at(i) {
            match io.save(h, ctx_buf, off) {
                Ok(used) => {
                    io.flush(h);
                    tbl.set_slot_free(i, true);
                    off += used;
                }
                Err(IoErr::NotFound) => {
                    tbl.set_slot_free(i, false);
                }
                Err(e) => {
                    flush_all(tbl, io);
                    return Err(e);
                }
            }
        }
    }
    let mut off: usize = 0;
    for i in 0..SLOTS {
        let h = tbl.session_at(i);
        if h != 0 {
            match io.save(h, ses_buf, off) {
                Ok(used) => {
                    off += used;
                }
                Err(IoErr::NotFound) => {
                    tbl.clear_session(i);
                }
                Err(e) => {
                    flush_all(tbl, io);
                    return Err(e);
                }
            }
        }
    }
    Ok(())
}
