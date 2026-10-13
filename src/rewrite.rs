use super::{handle::*, table::SpaceTable};

/// Message header length: tag (2 bytes) + length (4 bytes) + command or return code (4 bytes).
pub const HEADER_SIZE: usize = 10;
/// The number of handles in a command is given by a 3-bit field, with an upper bound of 7.
pub const MAX_CHANDLES: usize = 7;
pub const RC_SUCCESS: u32 = 0;
/// The “handle list” category in capability queries.
pub const CAP_HANDLES: u32 = 0x0000_0001;
/// Capability response body layout: more-data flag (1 byte), category (4 bytes), count (4 bytes).
pub const CAP_MORE_OFF: usize = HEADER_SIZE;
const CAP_CAPABILITY_OFF: usize = HEADER_SIZE + 1;
const CAP_COUNT_OFF: usize = HEADER_SIZE + 5;
const CAP_HANDLES_OFF: usize = HEADER_SIZE + 9;
const RSP_LENGTH_OFF: usize = 2;
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SpaceErr {
    /// The packet length does not match the structure it declares.
    Malformed,
    /// The command references a virtual handle that cannot be resolved.
    BadHandle,
}
pub fn read_be32(b: &[u8], off: usize) -> u32 {
    u32::from_be_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]])
}
fn write_be32(b: &mut [u8], off: usize, v: u32) {
    b[off..off + 4].copy_from_slice(&v.to_be_bytes());
}
/// Replace the virtual handles in the command handle area with physical handles.
///
/// `nr_handles` is provided by the command-property table and is therefore a stage-2 encoding artifact;
/// here it is treated as an already-validated parameter.
pub fn map_command_handles(
    tbl: &SpaceTable,
    nr_handles: usize,
    cmd: &mut [u8],
) -> Result<(), SpaceErr> {
    for i in 0..nr_handles {
        let h = read_be32(cmd, HEADER_SIZE + 4 * i);
        if is_transient_exec(h) && tbl.resolve(h).is_none() {
            return Err(SpaceErr::BadHandle);
        }
    }
    for i in 0..nr_handles {
        let h = read_be32(cmd, HEADER_SIZE + 4 * i);
        if is_transient_exec(h) {
            let p = tbl.resolve(h).unwrap();
            write_be32(cmd, HEADER_SIZE + 4 * i, p);
        }
    }
    Ok(())
}
/// Result of processing a handle returned in the response header.
///
/// `OutOfSlots` places the obligation to release this physical handle into the return type instead of
/// leaving it as an unstated convention. The orchestrator does not compile if it does not handle it.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HeaderOutcome {
    /// There is no handle in the response, or the command itself failed; the packet is left untouched.
    NoHandle,
    /// A transient handle has been replaced by a virtual handle.
    Virtualized { vhandle: u32 },
    /// A session handle has been registered; the packet is left untouched (session handles are not
    /// virtualized).
    SessionTracked { phandle: u32 },
    /// The handle type is unknown; the packet is left untouched.
    Unknown { phandle: u32 },
    /// The table is full; `flush` must be released.
    OutOfSlots { flush: u32 },
}
/// Process the handle returned in the response header.
pub fn map_response_handle(
    tbl: &mut SpaceTable,
    has_rhandle: bool,
    rsp: &mut [u8],
) -> HeaderOutcome {
    if !has_rhandle {
        return HeaderOutcome::NoHandle;
    }
    let rc = read_be32(rsp, 6);
    if rc != RC_SUCCESS {
        return HeaderOutcome::NoHandle;
    }
    let phandle = read_be32(rsp, HEADER_SIZE);
    if is_transient_exec(phandle) {
        if phandle == 0 || phandle == CTX_SAVED_SENTINEL || tbl.lookup(phandle).is_some() {
            return HeaderOutcome::OutOfSlots { flush: phandle };
        }
        match tbl.intern(phandle) {
            Some(vhandle) => {
                write_be32(rsp, HEADER_SIZE, vhandle);
                HeaderOutcome::Virtualized { vhandle }
            }
            None => HeaderOutcome::OutOfSlots { flush: phandle },
        }
    } else if is_session_exec(phandle) {
        if phandle == 0 || tbl.has_session_exec(phandle) {
            return HeaderOutcome::OutOfSlots { flush: phandle };
        }
        if tbl.add_session(phandle) {
            HeaderOutcome::SessionTracked { phandle }
        } else {
            HeaderOutcome::OutOfSlots { flush: phandle }
        }
    } else {
        HeaderOutcome::Unknown { phandle }
    }
}
/// Rewrite the handle list in a capability response: transient handles are replaced by virtual handles,
/// transient handles unknown to this space are removed from the list, and the rest are kept as-is. The
/// list is compacted in place and the length and count fields are updated together.
///
/// Removal is a direct expression of isolation: when a space enumerates transient objects, it should only
/// see its own.
///
/// Returns the rewritten total packet length.
pub fn map_capability_handles(
    tbl: &SpaceTable,
    is_cap_query: bool,
    rsp: &mut [u8],
    len: usize,
) -> Result<usize, SpaceErr> {
    if !is_cap_query {
        return Ok(len);
    }
    if len < CAP_HANDLES_OFF {
        return Err(SpaceErr::Malformed);
    }
    let rc = read_be32(rsp, 6);
    if rc != RC_SUCCESS {
        return Ok(len);
    }
    if read_be32(rsp, CAP_CAPABILITY_OFF) != CAP_HANDLES {
        return Ok(len);
    }
    let tail = len - CAP_HANDLES_OFF;
    if !tail.is_multiple_of(4) {
        return Err(SpaceErr::Malformed);
    }
    let avail: usize = tail / 4;
    let declared = read_be32(rsp, CAP_COUNT_OFF);
    if declared as usize != avail {
        return Err(SpaceErr::Malformed);
    }
    let count: usize = avail;
    let mut j: usize = 0;
    for i in 0..count {
        let h = read_be32(rsp, CAP_HANDLES_OFF + 4 * i);
        if is_transient_exec(h) {
            if h != 0 && h != CTX_SAVED_SENTINEL {
                if let Some(v) = tbl.lookup(h) {
                    write_be32(rsp, CAP_HANDLES_OFF + 4 * j, v);
                    j += 1;
                }
            }
        } else {
            write_be32(rsp, CAP_HANDLES_OFF + 4 * j, h);
            j += 1;
        }
    }
    let new_len = CAP_HANDLES_OFF + 4 * j;
    write_be32(rsp, CAP_COUNT_OFF, j as u32);
    write_be32(rsp, RSP_LENGTH_OFF, new_len as u32);
    Ok(new_len)
}
