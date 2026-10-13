//! Glue layer for the handle space.
//!
//! Belongs to `tpm-module`, outside Verus. It does only two things the verification layer deliberately leaves alone:
//! allocating the backup buffers, and making **the transaction boundary of the byte buffers coincide with that of the table**.
//!
//! The latter is the sole reason this file exists. `Transaction` guarantees atomicity of the table -- changes
//! land on the copy and only `commit` writes them back. But the backup buffers are two byte arrays of ten-odd KiB each;
//! putting them into `tpm-core` would make every proof drag along the `Seq` of two large arrays,
//! while their semantics amount to nothing more than "commit together or discard together". So the copy is kept here, and the rule is
//! enforced by types: the only way to obtain a `Work` is `begin`, `Work` has no `Clone`,
//! and both commit and rollback take it by value.

use tpm_core::module::{ContextIo, IoErr, Space, Transaction, load_space, save_space};
use tpm_core::rewrite::{SpaceErr, map_capability_handles, map_command_handles, map_response_handle};
use tpm_core::table::SpaceTable;

/// Context backup capacity of a single space. The two buffers store objects and sessions respectively.
pub const CTX_BUF_SIZE: usize = 16 * 1024;

pub struct SpaceStore {
    space: Space,
    ctx: [u8; CTX_BUF_SIZE],
    ses: [u8; CTX_BUF_SIZE],
}

/// The complete working copy during one request: the table + two backup buffers.
///
/// No `Clone`, no public constructor. Dropping it is a rollback.
pub struct Work {
    txn: Transaction,
    ctx: [u8; CTX_BUF_SIZE],
    ses: [u8; CTX_BUF_SIZE],
}

impl SpaceStore {
    pub fn new() -> Self {
        SpaceStore { space: Space::new(), ctx: [0u8; CTX_BUF_SIZE], ses: [0u8; CTX_BUF_SIZE] }
    }

    /// Take a working copy. Copying the table is `tpm-core`'s job; the two memcpys are here.
    pub fn begin(&self) -> Work {
        Work { txn: self.space.begin(), ctx: self.ctx, ses: self.ses }
    }

    /// Write back in one go after the whole path succeeded. The table and the buffers are written in the same function,
    /// with no moment in between at which "the table is updated but the buffers are not" could be observed.
    pub fn commit(&mut self, w: Work) {
        self.ctx = w.ctx;
        self.ses = w.ses;
        self.space.commit(w.txn);
    }

    /// Failure cleanup: release the leftovers on the chip and discard the copy.
    pub fn rollback<I: ContextIo>(&self, w: Work, io: &mut I) {
        w.txn.abort(io);
        // The two buffers leave scope together with `w`, and the stable state is untouched.
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

/// The complete sequence of one request.
///
/// The parameters `nr_handles`, `has_rhandle` and `is_cap_query` all come from the command attribute table,
/// a product of the codec layer; this function is only responsible for feeding them in order to the verified functions, and for making
/// any failing step take the same rollback path.
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

    // 1. Load the objects swapped out in the previous round back onto the chip
    if let Err(e) = load_space(w.table(), io, &w.ctx, &w.ses) {
        bail!(SpaceError::Io(e));
    }

    // 2. Command direction: virtual handle -> physical handle
    if let Err(e) = map_command_handles(w.table(), nr_handles, cmd) {
        bail!(SpaceError::Cmd(e));
    }

    // 3. Send
    let n = match transmit(cmd, rsp) {
        Ok(n) => n,
        Err(e) => bail!(SpaceError::Io(e)),
    };

    // 4. Response direction: register new handles, rewrite the handle area
    match map_response_handle(w.table(), has_rhandle, rsp) {
        outcome if needs_flush(&outcome) => {
            // Table full: the handle cannot be taken over and must be released here, otherwise it permanently occupies chip resources
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

    // 5. Swap out: the chip is clean again, contents land back in the working copy
    if let Err(e) = save_space(w.table(), io, &mut w.ctx, &mut w.ses) {
        bail!(SpaceError::Io(e));
    }

    // 6. Write back only once we get here
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
