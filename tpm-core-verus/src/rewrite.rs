use vstd::prelude::*;

use super::handle::*;
use super::table::SpaceTable;
#[cfg(verus_keep_ghost)]
use crate::endian::{be32_byte, be32_of, lemma_be32_roundtrip};

verus! {

/// Message header length: tag 2 bytes + length 4 bytes + command code or return code 4 bytes.
pub const HEADER_SIZE: usize = 10;

/// The number of command handles is given by a 3-bit field, with an upper limit of 7.
pub const MAX_CHANDLES: usize = 7;

pub const RC_SUCCESS: u32 = 0;

/// The "handle list" category in a capability query.
pub const CAP_HANDLES: u32 = 0x0000_0001;

/// Capability response body layout: more-data flag 1 byte, category 4 bytes, count 4 bytes.
pub const CAP_MORE_OFF: usize = HEADER_SIZE;
const CAP_CAPABILITY_OFF: usize = HEADER_SIZE + 1;
const CAP_COUNT_OFF: usize = HEADER_SIZE + 5;
const CAP_HANDLES_OFF: usize = HEADER_SIZE + 9;

const RSP_LENGTH_OFF: usize = 2;

#[derive(Clone, Copy, PartialEq, Eq, Structural, Debug)]
pub enum SpaceErr {
    /// The message length does not match the structure it declares.
    Malformed,
    /// The command references a virtual handle that cannot be resolved.
    BadHandle,
}

// ---------------------------------------------------------------------------
// Byte access
// ---------------------------------------------------------------------------

pub open spec fn be32_at(s: Seq<u8>, off: int) -> u32 {
    be32_of(s[off], s[off + 1], s[off + 2], s[off + 3])
}

pub fn read_be32(b: &[u8], off: usize) -> (r: u32)
    requires
        off + 4 <= b.len(),
    ensures
        r == be32_at(b@, off as int),
{
    ((b[off] as u32) << 24) | ((b[off + 1] as u32) << 16) | ((b[off + 2] as u32) << 8)
        | (b[off + 3] as u32)
}

pub(crate) fn write_be32(b: &mut [u8], off: usize, v: u32)
    requires
        off + 4 <= old(b).len(),
    ensures
        final(b).len() == old(b).len(),
        be32_at(final(b)@, off as int) == v,
        forall|k: int|
            #![trigger final(b)@[k]]
            0 <= k < final(b).len() && (k < off || k >= off + 4) ==> final(b)@[k] == old(b)@[k],
{
    proof {
        lemma_be32_roundtrip(v);
    }
    b[off] = ((v >> 24) & 0xff) as u8;
    b[off + 1] = ((v >> 16) & 0xff) as u8;
    b[off + 2] = ((v >> 8) & 0xff) as u8;
    b[off + 3] = (v & 0xff) as u8;
}

/// The `k`-th handle of the command / response handle area.
pub open spec fn handle_at(s: Seq<u8>, k: int) -> u32 {
    be32_at(s, HEADER_SIZE + 4 * k)
}

#[verifier::external_body]
proof fn lemma_handle_unchanged_by_write(
    before: Seq<u8>,
    after: Seq<u8>,
    wi: int,
    k: int,
)
    requires
        before.len() == after.len(),
        0 <= wi,
        HEADER_SIZE + 4 * wi + 4 <= before.len(),
        0 <= k,
        HEADER_SIZE + 4 * k + 4 <= before.len(),
        k != wi,
        forall|t: int|
            #![trigger after[t]]
            0 <= t < before.len() && (t < HEADER_SIZE + 4 * wi || t >= HEADER_SIZE + 4 * wi + 4)
                ==> after[t] == before[t],
    ensures
        handle_at(after, k) == handle_at(before, k),
{
    let base = HEADER_SIZE + 4 * k;
    if k < wi {
        assert(base + 3 < HEADER_SIZE + 4 * wi) by (nonlinear_arith);
    } else {
        assert(wi < k);
        assert(HEADER_SIZE + 4 * wi + 4 <= base) by (nonlinear_arith);
    }
    assert(after[base] == before[base]);
    assert(after[base + 1] == before[base + 1]);
    assert(after[base + 2] == before[base + 2]);
    assert(after[base + 3] == before[base + 3]);
}

/// Spec of the handle rewrite: transient handles are looked up in the table, the rest are kept as they are.
pub open spec fn mapped_or_kept(tbl: SpaceTable, h: u32) -> Option<u32> {
    if is_transient(h) {
        tbl.maps(h)
    } else {
        Some(h)
    }
}

// ---------------------------------------------------------------------------
// Command direction
// ---------------------------------------------------------------------------

/// Replace the virtual handles in the command handle area with physical handles.
///
/// `nr_handles` comes from the command code's attribute table, a product of the phase 2 codec; here it is
/// treated only as an already validated parameter.
pub fn map_command_handles(tbl: &SpaceTable, nr_handles: usize, cmd: &mut [u8]) -> (r: Result<
    (),
    SpaceErr,
>)
    requires
        tbl.wf(),
        nr_handles <= MAX_CHANDLES,
        old(cmd).len() >= HEADER_SIZE + 4 * nr_handles,
    ensures
        final(cmd).len() == old(cmd).len(),
        // On failure the message is left untouched
        r.is_err() ==> final(cmd)@ == old(cmd)@,
        // The header is never modified
        forall|k: int| #![trigger final(cmd)@[k]] 0 <= k < HEADER_SIZE ==> final(cmd)@[k] == old(cmd)@[k],
        // On success every handle is rewritten per the spec
        r.is_ok() ==> forall|k: int|
            #![trigger handle_at(final(cmd)@, k)]
            0 <= k < nr_handles ==> mapped_or_kept(*tbl, handle_at(old(cmd)@, k)) == Some(
                handle_at(final(cmd)@, k),
            ),
{
    // First pass: read-only validation.
    for i in 0..nr_handles
        invariant
            tbl.wf(),
            cmd.len() >= HEADER_SIZE + 4 * nr_handles,
            forall|k: int|
                #![trigger handle_at(cmd@, k)]
                0 <= k < i ==> mapped_or_kept(*tbl, handle_at(cmd@, k)).is_some(),
    {
        let h = read_be32(cmd, HEADER_SIZE + 4 * i);
        if is_transient_exec(h) {
            if tbl.resolve(h).is_none() {
                return Err(SpaceErr::BadHandle);
            }
        }
    }

    // Second pass: commit the writes. At this point every handle is guaranteed resolvable, so it cannot fail midway.
    let ghost orig = cmd@;
    proof {
        assert forall|k: int|
            #![trigger handle_at(orig, k)]
            0 <= k < nr_handles as int implies mapped_or_kept(*tbl, handle_at(orig, k)).is_some() by {
            assert(handle_at(orig, k) == handle_at(cmd@, k));
        }
    }
    for i in 0..nr_handles
        invariant
            tbl.wf(),
            cmd.len() == orig.len(),
            cmd.len() >= HEADER_SIZE + 4 * nr_handles,
            forall|k: int| #![trigger cmd@[k]] 0 <= k < HEADER_SIZE ==> cmd@[k] == orig[k],
            forall|k: int|
                #![trigger handle_at(orig, k)]
                0 <= k < nr_handles as int ==> mapped_or_kept(*tbl, handle_at(orig, k)).is_some(),
            // Handles not yet processed keep their original values
            forall|k: int|
                #![trigger handle_at(cmd@, k)]
                (i as int <= k && k < nr_handles as int) ==> handle_at(cmd@, k) == handle_at(orig, k),
            // Handles already processed conform to the spec
            forall|k: int|
                #![trigger handle_at(cmd@, k)]
                0 <= k < i as int ==> mapped_or_kept(*tbl, handle_at(orig, k)) == Some(
                    handle_at(cmd@, k),
                ),
    {
        let ghost before_iter = cmd@;
        let h = read_be32(cmd, HEADER_SIZE + 4 * i);
        if is_transient_exec(h) {
            let rh = tbl.resolve(h);
            proof {
                assert(is_transient(h));
                assert(handle_at(cmd@, i as int) == h);
                assert(i <= nr_handles);
                assert(i < nr_handles);
                assert(i as int <= i as int);
                assert((i as int) < (nr_handles as int));
                assert(handle_at(cmd@, i as int) == handle_at(orig, i as int));
                assert(mapped_or_kept(*tbl, handle_at(orig, i as int)).is_some());
                assert(mapped_or_kept(*tbl, h).is_some());
                assert(rh == tbl.maps(h));
                assert(rh.is_some());
            }
            let p = rh.unwrap();
            write_be32(cmd, HEADER_SIZE + 4 * i, p);
            proof {
                assert(handle_at(cmd@, i as int) == p);
                assert(mapped_or_kept(*tbl, h) == Some(p));

                assert forall|k: int|
                    #![trigger handle_at(cmd@, k)]
                    (i as int + 1 <= k && k < nr_handles as int) ==> handle_at(cmd@, k) == handle_at(orig, k) by {
                    if i as int + 1 <= k && k < nr_handles as int {
                        assert(i as int <= k && k < nr_handles as int);
                        assert(i as int != k);
                        lemma_handle_unchanged_by_write(before_iter, cmd@, i as int, k);
                        assert(handle_at(before_iter, k) == handle_at(orig, k));
                    }
                }

                assert forall|k: int|
                    #![trigger handle_at(cmd@, k)]
                    0 <= k < i as int ==> mapped_or_kept(*tbl, handle_at(orig, k)) == Some(
                        handle_at(cmd@, k),
                    ) by {
                    if 0 <= k && k < i as int {
                        lemma_handle_unchanged_by_write(before_iter, cmd@, i as int, k);
                        assert(handle_at(cmd@, k) == handle_at(before_iter, k));
                    }
                }
            }
        } else {
            proof {
                assert(cmd@ == before_iter);
            }
        }

    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Response direction
// ---------------------------------------------------------------------------

/// The outcome of handling the response header handle.
///
/// `OutOfSlots` writes the obligation "this physical handle must be released" into the return type,
/// rather than leaving the caller to remember it by convention. If the orchestration layer does not handle it, the code does not compile.
#[derive(Clone, Copy, PartialEq, Eq, Structural)]
pub enum HeaderOutcome {
    /// The response has no handle, or the command itself failed; the message is unchanged.
    NoHandle,
    /// The transient handle has been replaced with a virtual handle.
    Virtualized { vhandle: u32 },
    /// The session handle has been registered; the message is unchanged (session handles are not virtualized).
    SessionTracked { phandle: u32 },
    /// Unrecognized handle type; the message is unchanged.
    Unknown { phandle: u32 },
    /// The table is full; `flush` must be performed.
    OutOfSlots { flush: u32 },
}

/// Whether this outcome means the message was rewritten.
pub open spec fn outcome_rewrites(r: HeaderOutcome) -> bool {
    match r {
        HeaderOutcome::Virtualized { .. } => true,
        _ => false,
    }
}

/// Handle the handle returned in the response header.
pub fn map_response_handle(tbl: &mut SpaceTable, has_rhandle: bool, rsp: &mut [u8]) -> (r:
    HeaderOutcome)
    requires
        old(tbl).wf(),
        old(rsp).len() >= HEADER_SIZE + 4,
    ensures
        final(tbl).wf(),
        final(rsp).len() == old(rsp).len(),
        // Only virtualization modifies the message, and only those 4 bytes
        !outcome_rewrites(r) ==> final(rsp)@ == old(rsp)@,
        forall|k: int|
            #![trigger final(rsp)@[k]]
            0 <= k < final(rsp).len() && (k < HEADER_SIZE || k >= HEADER_SIZE + 4) ==> final(rsp)@[k]
                == old(rsp)@[k],
{
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
            // Invalid or duplicate physical handle: not taken over, handed back to the upper layer to release.
            return HeaderOutcome::OutOfSlots { flush: phandle };
        }
        match tbl.intern(phandle) {
            Some(vhandle) => {
                write_be32(rsp, HEADER_SIZE, vhandle);
                HeaderOutcome::Virtualized { vhandle }
            },
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

/// Rewrite the handle list in a capability query response: transient handles are replaced with virtual handles, and transient
/// handles this space does not recognize are **removed from the list**, the rest kept as they are. The list is compacted in place, and the length field and
/// count field are updated together.
///
/// Removal is a direct expression of isolation: when a space enumerates transient objects, it should see only its own.
///
/// Returns the total length of the rewritten message.
pub fn map_capability_handles(tbl: &SpaceTable, is_cap_query: bool, rsp: &mut [u8], len: usize)
    -> (r: Result<usize, SpaceErr>)
    requires
        tbl.wf(),
        len <= old(rsp).len(),
    ensures
        final(rsp).len() == old(rsp).len(),
        r.is_ok() ==> r.unwrap() <= len,
        !is_cap_query ==> r == Ok::<usize, SpaceErr>(len) && final(rsp)@ == old(rsp)@,
{
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

    // Compute the capacity first and then compare, avoiding any multiplication.
    let tail = len - CAP_HANDLES_OFF;
    if tail % 4 != 0 {
        return Err(SpaceErr::Malformed);
    }
    let avail: usize = tail / 4;
    let declared = read_be32(rsp, CAP_COUNT_OFF);
    if declared as usize != avail {
        return Err(SpaceErr::Malformed);
    }
    let count: usize = avail;

    let ghost orig = rsp@;
    let mut j: usize = 0;
    for i in 0..count
        invariant
            j <= i <= count,
            tbl.wf(),
            rsp.len() == orig.len(),
            CAP_HANDLES_OFF + 4 * count <= rsp.len(),
    {
        let h = read_be32(rsp, CAP_HANDLES_OFF + 4 * i);
        if is_transient_exec(h) {
            if h != 0 && h != CTX_SAVED_SENTINEL {
                match tbl.lookup(h) {
                    Some(v) => {
                        write_be32(rsp, CAP_HANDLES_OFF + 4 * j, v);
                        j += 1;
                    },
                    None => {},  // Not in this space; drop it
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

} // verus!
