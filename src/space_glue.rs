//! Glue layer for the handle space.
//!
//! This belongs to `tpm-module` and does not go into Verus. It does only two things that the validation
//! layer deliberately does not touch: allocate the backup buffers and make the transaction boundaries of
//! the byte buffers line up with the transaction boundaries of the table.
//!
//! The second point is the only reason this file exists. `Transaction` guarantees table atomicity — the
//! changes are made on a copy, and only `commit` writes them back. But the backup buffers are two
//! multi-KiB byte arrays; putting them into `tpm-core` would force every proof to carry two large `Seq`
//! arrays, and their semantics are nothing more than “commit together or discard together.” Therefore the
//! copy remains here, and the rules are enforced by the type system: the only way to get `Work` is via
//! `begin`, `Work` has no `Clone`, and both commit and rollback consume it by value.

use tpm_core::module::{ContextIo, IoErr, Space, Transaction, load_space, save_space};
use tpm_core::rewrite::{SpaceErr, map_capability_handles, map_command_handles, map_response_handle};
use tpm_core::table::SpaceTable;

/// Backup capacity for a single space. The two buffers store objects and sessions respectively.
pub const CTX_BUF_SIZE: usize = 16 * 1024;

pub struct SpaceStore {
    space: Space,
    ctx: [u8; CTX_BUF_SIZE],
    ses: [u8; CTX_BUF_SIZE],
}

/// Full working copy for a request: the table + the two backup buffers.
///
/// There is no `Clone` and no public constructor. Dropping it is rollback.
pub struct Work {
    txn: Transaction,
    ctx: [u8; CTX_BUF_SIZE],
    ses: [u8; CTX_BUF_SIZE],
}

impl SpaceStore {
    pub fn new() -> Self {
        SpaceStore { space: Space::new(), ctx: [0u8; CTX_BUF_SIZE], ses: [0u8; CTX_BUF_SIZE] }
    }

    /// Take a working copy. The table copy is handled by `tpm-core`; the two memcpy calls are here.
    pub fn begin(&self) -> Work {
        Work { txn: self.space.begin(), ctx: self.ctx, ses: self.ses }
    }

    /// Write the whole path back in one shot. The table and buffers are updated in the same function, with
    /// no observable point where “the table is updated but the buffers are not.”
    pub fn commit(&mut self, w: Work) {
        self.ctx = w.ctx;
        self.ses = w.ses;
        self.space.commit(w.txn);
    }

    /// Cleanup on failure: release residual handles on the chip and discard the copy.
    pub fn rollback<I: ContextIo>(&self, w: Work, io: &mut I) {
        w.txn.abort(io);
        // The two buffers leave scope with `w`; the stable state remains unchanged.
    }
}

#[derive(Debug)]
pub enum SpaceError {
    Io(IoErr),
    Cmd(SpaceErr),
}

impl Work {
    fn table(&mut self) -> &mut SpaceTable {
        self.txn.table()
    }
}

/// Full request sequence.
///
/// The parameters `nr_handles`, `has_rhandle`, and `is_cap_query` all come from the command-property
/// table and are encoding-layer artifacts; this layer is only responsible for feeding them, in order, to
/// the validated functions and ensuring that any failure follows the same rollback path.
pub fn run_request<I, F>(
    store: &mut SpaceStore,
    io: &mut I,
    nr_handles: usize,
    has_rhandle: bool,
    is_cap_query: bool,
    cmd: &mut [u8],
    rsp: &mut [u8],
    transmit: F,
) -> Result<usize, SpaceError>
where
    I: ContextIo,
    F: FnOnce(&[u8], &mut [u8]) -> Result<usize, IoErr>,
{
    let mut w = store.begin();

    macro_rules! bail {
        ($e:expr) => {{
            store.rollback(w, io);
            return Err($e);
        }};
    }

    // 1. Reload the objects swapped out in the previous round back onto the chip.
    if let Err(e) = load_space(w.table(), io, &w.ctx, &w.ses) {
        bail!(SpaceError::Io(e));
    }

    // 2. Command direction: virtual handle → physical handle.
    if let Err(e) = map_command_handles(w.table(), nr_handles, cmd) {
        bail!(SpaceError::Cmd(e));
    }

    // 3. Transmit.
    let n = match transmit(cmd, rsp) {
        Ok(n) => n,
        Err(e) => bail!(SpaceError::Io(e)),
    };

    // 4. Response direction: register new handles and rewrite the handle area.
    match map_response_handle(w.table(), has_rhandle, rsp) {
        outcome if needs_flush(&outcome) => {
            // Table full: the handle cannot be adopted, so it must be released here; otherwise it will
            // occupy chip resources forever.
            if let Some(h) = flush_target(&outcome) {
                io.flush(h);
            }
            bail!(SpaceError::Io(IoErr::NoSpace));
        },
        _ => {},
    }
    let n = match map_capability_handles(w.table(), is_cap_query, rsp, n) {
        Ok(n) => n,
        Err(e) => bail!(SpaceError::Cmd(e)),
    };

    // 5. Swap out: return the chip to a clean state and write the contents back to the working copy.
    if let Err(e) = save_space(w.table(), io, &mut w.ctx, &mut w.ses) {
        bail!(SpaceError::Io(e));
    }

    // 6. Only here do we write back.
    store.commit(w);
    Ok(n)
}

use tpm_core::rewrite::HeaderOutcome;

fn needs_flush(o: &HeaderOutcome) -> bool {
    matches!(o, HeaderOutcome::OutOfSlots { .. })
}

fn flush_target(o: &HeaderOutcome) -> Option<u32> {
    match o {
        HeaderOutcome::OutOfSlots { flush } => Some(*flush),
        _ => None,
    }
}
