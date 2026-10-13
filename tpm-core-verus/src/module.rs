use vstd::prelude::*;
use vstd::set::Set;

#[cfg(verus_keep_ghost)]
pub use crate::handle::{SLOTS, is_session, is_transient, valid_phandle};
#[cfg(not(verus_keep_ghost))]
pub use crate::handle::{
    SLOTS,
    is_session_exec as is_session,
    is_transient_exec as is_transient,
    valid_phandle_exec as valid_phandle,
};
pub use crate::rewrite::{HeaderOutcome, SpaceErr};
#[cfg(verus_keep_ghost)]
pub use crate::table::{CtxSlot, SpaceTable, live_handle};
#[cfg(not(verus_keep_ghost))]
pub use crate::table::{CtxSlot, SpaceTable};

use crate::handle::*;
use crate::table::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Structural, Debug)]
pub enum IoErr {
    /// Target no longer exists: the context was released externally, or the counter does not match. Recoverable --
    /// simply forget the corresponding slot.
    NotFound,
    /// Backup data integrity check failed.
    Integrity,
    /// The backup buffer cannot hold it.
    NoSpace,
    /// Polling budget exhausted, a pure wait timeout, worth retrying under a backoff policy.
    Timeout,
    /// Physical bus fault; retrying is pointless.
    Bus,
    /// What the chip returned violates the protocol (length or status bits do not match the specification).
    Protocol,
    /// The command handed down by the caller is not self-consistent (the length field does not match the buffer).
    /// This is a logic error in the encoding layer, not a device fault.
    BadCommand,
    /// Call-order error: the interface was called in a state that does not meet its preconditions.
    NotReady,
    /// An internal invariant is broken and the table and the chip state can no longer be reconciled; the only safe action is to
    /// clear everything and start over.
    Fatal,
}

// ---------------------------------------------------------------------------
// Chip-side interface (trusted spec)
// ---------------------------------------------------------------------------

/// Abstract interface for context access.
///
/// The implementation is provided by the outer layer: internally it does message construction, transport and return-code classification, which are the
/// responsibilities of the codec layer. This module depends only on the pre/postconditions written here.
pub trait ContextIo {
    /// The set of handles the chip currently holds and has not released. Used only in proofs, no runtime overhead.
    spec fn outstanding(&self) -> Set<u32>;

    /// Load a context from `blob[off..]`, returning the new handle and the number of bytes consumed.
    fn load(&mut self, blob: &[u8], off: usize) -> (r: Result<(u32, usize), IoErr>)
        requires
            off <= blob.len(),
        ensures
            r.is_ok() ==> {
                let (h, used) = r.unwrap();
                &&& valid_phandle(h)
                &&& off + used <= blob.len()
                &&& used > 0
                &&& !old(self).outstanding().contains(h)
                &&& final(self).outstanding() == old(self).outstanding().insert(h)
            },
            r.is_err() ==> final(self).outstanding() == old(self).outstanding(),
    ;

    /// Save the context of `h` to `out[off..]`, returning the number of bytes written.
    ///
    /// Saving does not itself release the handle; release must be requested explicitly with [`ContextIo::flush`].
    fn save(&mut self, h: u32, out: &mut [u8], off: usize) -> (r: Result<usize, IoErr>)
        requires
            off <= old(out).len(),
        ensures
            final(out).len() == old(out).len(),
            final(self).outstanding() == old(self).outstanding(),
            r.is_ok() ==> off + r.unwrap() <= final(out).len(),
    ;

    /// Release a handle on the chip. Idempotent and returns no error -- a failed release has no remedy,
    /// and all call sites are on error-handling paths.
    fn flush(&mut self, h: u32)
        ensures
            final(self).outstanding() == old(self).outstanding().remove(h),
    ;
}

/// Every live handle in the table is in the chip's held set. This is the core invariant of the orchestration layer:
/// it guarantees that "what the table records really exists", and also that the handle obtained by the next load is new.
pub open spec fn table_backed<I: ContextIo>(tbl: SpaceTable, io: I) -> bool {
    forall|i: int|
        #![trigger tbl.slot(i)]
        0 <= i < SLOTS && live_handle(tbl.slot(i)).is_some() ==> io.outstanding().contains(
            live_handle(tbl.slot(i)).unwrap(),
        )
}

// ---------------------------------------------------------------------------
// Transactions
// ---------------------------------------------------------------------------

/// The handle space visible to users. The backup buffers are not placed here -- this layer does no allocation,
/// and the outer layer provides slices as needed.
pub struct Space {
    tbl: SpaceTable,
}

/// The working copy during one request. Only [`Space::commit`] writes it back.
///
/// It implements no `Clone` and has no public constructor: the only way to obtain one is
/// [`Space::begin`], and the only consequence of dropping it is a rollback.
pub struct Transaction {
    work: SpaceTable,
}

impl Space {
    pub closed spec fn wf(&self) -> bool {
        self.tbl.wf()
    }

    pub closed spec fn view(&self) -> SpaceTable {
        self.tbl
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
    {
        Space { tbl: SpaceTable::new() }
    }

    /// Take a working copy. The state visible to users stays unchanged in the meantime.
    pub fn begin(&self) -> (r: Transaction)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.view() == self.view(),
    {
        Transaction { work: self.tbl }
    }

    /// Write the working copy back. Called only when the whole path succeeded.
    pub fn commit(&mut self, t: Transaction)
        requires
            t.wf(),
        ensures
            final(self).wf(),
            final(self).view() == t.view(),
    {
        self.tbl = t.work;
    }
}

impl Transaction {
    pub closed spec fn wf(&self) -> bool {
        self.work.wf()
    }

    pub closed spec fn view(&self) -> SpaceTable {
        self.work
    }

    pub fn table(&mut self) -> (r: &mut SpaceTable)
        ensures
            *r == old(self).view(),
    {
        &mut self.work
    }

    /// Cleanup when a transaction fails: release the leftovers on the chip, then discard the copy.
    ///
    /// Takes `self` rather than borrowing it -- after the cleanup this transaction can never be committed.
    pub fn abort<I: ContextIo>(self, io: &mut I)
        requires
            self.wf(),
    {
        let mut t = self;
        flush_all(&mut t.work, io);
    }
}

// ---------------------------------------------------------------------------
// Bulk load / save / release
// ---------------------------------------------------------------------------

/// Release all live handles and all sessions in the tables, and clear both tables.
///
/// This is the cleanup action of the error path: after the call, nothing belonging to this space is left on the chip.
fn flush_all<I: ContextIo>(tbl: &mut SpaceTable, io: &mut I)
    requires
        old(tbl).wf(),
    ensures
        final(tbl).wf(),
        forall|i: int| 0 <= i < SLOTS ==> final(tbl).slot(i) == CtxSlot::Empty,
        forall|i: int| 0 <= i < SLOTS ==> final(tbl).session(i) == 0u32,
{
    for i in 0..SLOTS
        invariant
            tbl.wf(),
            forall|k: int| 0 <= k < i ==> tbl.slot(k) == CtxSlot::Empty,
    {
        match tbl.slot_at(i) {
            CtxSlot::Live(h) => {
                io.flush(h);
                tbl.set_slot_free(i, false);
            },
            _ => {
                tbl.set_slot_free(i, false);
            },
        }
    }

    for i in 0..SLOTS
        invariant
            tbl.wf(),
            forall|k: int| 0 <= k < SLOTS ==> tbl.slot(k) == CtxSlot::Empty,
            forall|k: int| 0 <= k < i ==> tbl.session(k) == 0u32,
    {
        let h = tbl.session_at(i);
        if h != 0 {
            io.flush(h);
            tbl.clear_session(i);
        }
    }
}

/// Load every context in the backup buffer back onto the chip.
///
/// After a successful return the table has no slot in the "saved" state -- every non-empty slot corresponds to a
/// handle that really exists on the chip.
///
/// Sessions are handled differently from objects: a session that fails to load is simply forgotten (its slot cleared) rather than
/// failing the whole operation. A session may well have been released externally, which is a normal case.
pub fn load_space<I: ContextIo>(
    tbl: &mut SpaceTable,
    io: &mut I,
    ctx_buf: &[u8],
    ses_buf: &[u8],
) -> (r: Result<(), IoErr>)
    requires
        old(tbl).wf(),
        table_backed(*old(tbl), *old(io)),
    ensures
        final(tbl).wf(),
        table_backed(*final(tbl), *final(io)),
        r.is_ok() ==> forall|i: int| 0 <= i < SLOTS ==> final(tbl).slot(i) != CtxSlot::Saved,
{
    let mut off: usize = 0;
    for i in 0..SLOTS
        invariant
            off <= ctx_buf.len(),
            tbl.wf(),
            table_backed(*tbl, *io),
            forall|k: int| 0 <= k < i ==> tbl.slot(k) != CtxSlot::Saved,
    {
        match tbl.slot_at(i) {
            CtxSlot::Empty => {},
            CtxSlot::Live(_) => {
                // There should be no live handle before loading: the table and the backup buffer are already out of sync.
                flush_all(tbl, io);
                return Err(IoErr::NotReady);
            },
            CtxSlot::Saved => {
                match io.load(ctx_buf, off) {
                    Ok((h, used)) => {
                        tbl.set_slot_live(i, h);
                        off += used;
                    },
                    Err(e) => {
                        flush_all(tbl, io);
                        return Err(e);
                    },
                }
            },
        }
    }

    let mut off: usize = 0;
    for i in 0..SLOTS
        invariant
            off <= ses_buf.len(),
            tbl.wf(),
            table_backed(*tbl, *io),
            forall|k: int| 0 <= k < SLOTS ==> tbl.slot(k) != CtxSlot::Saved,
    {
        if tbl.session_at(i) != 0 {
            match io.load(ses_buf, off) {
                Ok((h, used)) => {
                    if h != tbl.session_at(i) {
                        // The session changed identity, which means the backup does not match the chip state.
                        flush_all(tbl, io);
                        return Err(IoErr::Integrity);
                    }
                    off += used;
                },
                Err(IoErr::NotFound) => {
                    tbl.clear_session(i);
                },
                Err(e) => {
                    flush_all(tbl, io);
                    return Err(e);
                },
            }
        }
    }
    Ok(())
}

/// Save everything on the chip that belongs to this space back into the backup buffer and release it.
///
/// After a successful return the table has no live slot and the chip holds no transient object of this space --
/// which is exactly the property "the chip is clean after the transaction ends".
pub fn save_space<I: ContextIo>(
    tbl: &mut SpaceTable,
    io: &mut I,
    ctx_buf: &mut [u8],
    ses_buf: &mut [u8],
) -> (r: Result<(), IoErr>)
    requires
        old(tbl).wf(),
        table_backed(*old(tbl), *old(io)),
    ensures
        final(tbl).wf(),
        r.is_ok() ==> forall|i: int|
            #![trigger final(tbl).slot(i)]
            0 <= i < SLOTS ==> live_handle(final(tbl).slot(i)).is_none(),
{
    let mut off: usize = 0;
    for i in 0..SLOTS
        invariant
            off <= ctx_buf.len(),
            tbl.wf(),
            table_backed(*tbl, *io),
            forall|k: int|
                #![trigger tbl.slot(k)]
                0 <= k < i ==> live_handle(tbl.slot(k)).is_none(),
    {
        match tbl.slot_at(i) {
            CtxSlot::Live(h) => {
                match io.save(h, ctx_buf, off) {
                    Ok(used) => {
                        io.flush(h);
                        tbl.set_slot_free(i, true);
                        off += used;
                    },
                    Err(IoErr::NotFound) => {
                        // The object was released externally; forget it.
                        tbl.set_slot_free(i, false);
                    },
                    Err(e) => {
                        flush_all(tbl, io);
                        return Err(e);
                    },
                }
            },
            _ => {},
        }
    }

    let mut off: usize = 0;
    for i in 0..SLOTS
        invariant
            off <= ses_buf.len(),
            tbl.wf(),
            forall|k: int|
                #![trigger tbl.slot(k)]
                0 <= k < SLOTS ==> live_handle(tbl.slot(k)).is_none(),
    {
        let h = tbl.session_at(i);
        if h != 0 {
            match io.save(h, ses_buf, off) {
                Ok(used) => {
                    off += used;
                },
                Err(IoErr::NotFound) => {
                    tbl.clear_session(i);
                },
                Err(e) => {
                    flush_all(tbl, io);
                    return Err(e);
                },
            }
        }
    }
    Ok(())
}

} // verus!
