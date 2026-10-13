use vstd::prelude::*;
use vstd::array::*;

use crate::crypto::*;
use crate::cursor::Cursor;
#[cfg(verus_keep_ghost)]
use crate::cursor::{spec_be16_at, spec_be32_at};

verus! {

broadcast use group_crypto_axioms;

// ===========================================================================
// Message constants
// ===========================================================================

/// Tag 2 bytes + length 4 bytes + command code or return code 4 bytes.
pub const HEADER_LEN: usize = 10;

/// Message tag with an authorization area. The authorization area exists only under this tag.
pub const ST_SESSIONS: u16 = 0x8002;

/// Session attribute bits.
pub const SA_CONTINUE_SESSION: u8 = 0x01;
pub const SA_DECRYPT: u8 = 0x20;
pub const SA_ENCRYPT: u8 = 0x40;

/// Maximum number of sessions allowed in the authorization area.
///
/// The specification limit is 3. This implementation appends only its own, but a response may carry sessions attached separately by the caller,
/// and the parsing side must still be able to skip them -- the number of skip rounds must be bounded, otherwise a carefully
/// crafted response could hold the parsing loop hostage.
pub const MAX_SESSIONS: usize = 3;

// ===========================================================================
// Command-side authorization area layout
// ===========================================================================
//
// ```text
// authHandle    u32
// nonceSize     u16 = 32
// nonceCaller   u8[32]
// attributes    u8
// hmacSize      u16 = 32
// hmac          u8[32]
// ```

pub const SESS_HANDLE_OFF: usize = 0;
pub const SESS_NONCE_SIZE_OFF: usize = 4;
pub const SESS_NONCE_OFF: usize = 6;
pub const SESS_ATTRS_OFF: usize = SESS_NONCE_OFF + NONCE_LEN;
pub const SESS_HMAC_SIZE_OFF: usize = SESS_ATTRS_OFF + 1;
pub const SESS_HMAC_OFF: usize = SESS_HMAC_SIZE_OFF + 2;

/// Number of bytes occupied by a single command-side session.
pub const CMD_SESSION_LEN: usize = SESS_HMAC_OFF + NONCE_LEN;

// ===========================================================================
// Errors
// ===========================================================================

#[derive(Clone, Copy, PartialEq, Eq, Structural, Debug)]
pub enum AuthErr {
    /// The message structure does not match the length it declares.
    Malformed,
    /// This session cannot be located in the authorization area.
    NoSession,
    /// The nonce or HMAC field length is not the agreed digest length. Both lengths are controlled by the peer;
    /// letting arbitrary values through would hand all later offset reasoning over to the peer.
    BadField,
    /// The recomputed HMAC does not match the received one.
    HmacMismatch,
}

// ===========================================================================
// Hash input specs
// ===========================================================================
//
// Three concatenation rules, shared by the encoding side and the verification side with a single definition. All reasoning about "what the computed digest
// is" ultimately reduces to here, which removes any chance of the two sides
// disagreeing on field order.

/// Input of the command digest: command code ‖ handle names ‖ parameter area.
pub open spec fn spec_cp_input(ordinal: u32, names: Seq<u8>, params: Seq<u8>) -> Seq<u8> {
    be32_seq(ordinal) + names + params
}

/// Input of the response digest: return code ‖ command code ‖ parameter area.
///
/// The return code is always zero here -- only successful responses reach verification -- but it still takes part in the digest.
pub open spec fn spec_rp_input(rc: u32, ordinal: u32, params: Seq<u8>) -> Seq<u8> {
    be32_seq(rc) + be32_seq(ordinal) + params
}

/// Input of the session HMAC: digest ‖ newer nonce ‖ older nonce ‖ attribute byte.
///
/// The order of the two nonces is directional: in the command direction the local nonce comes first, in the response direction the peer
/// nonce comes first. Getting it backwards is caught by no length check and only shows up as verification never passing, so the
/// order is made a parameter given explicitly at the call site rather than hidden in the function body.
pub open spec fn spec_auth_input(
    digest: Seq<u8>,
    newer: Seq<u8>,
    older: Seq<u8>,
    attrs: u8,
) -> Seq<u8> {
    digest + newer + older + seq![attrs]
}

// ===========================================================================
// Executable side of the digest and HMAC
// ===========================================================================

pub(crate) fn auth_hmac<H: HmacSha256Ctx>(
    key: &[u8],
    digest: &[u8; SHA256_LEN],
    newer: &[u8; NONCE_LEN],
    older: &[u8; NONCE_LEN],
    attrs: u8,
) -> (r: [u8; SHA256_LEN])
    ensures
        r@ =~= spec_hmac_sha256(key@, spec_auth_input(digest@, newer@, older@, attrs)),
{
    let mut h = H::with_key(key);
    let tail: [u8; 1] = [attrs];

    h.update(array_as_slice(digest));
    h.update(array_as_slice(newer));
    h.update(array_as_slice(older));
    h.update(array_as_slice(&tail));

    proof {
        assert(tail@ =~= seq![attrs]);
        assert(h.absorbed() =~= spec_auth_input(digest@, newer@, older@, attrs));
    }

    h.finish()
}

pub(crate) fn rp_hash<S: Sha256Ctx>(rc: u32, ordinal: u32, params: &[u8]) -> (r: [u8; SHA256_LEN])
    ensures
        r@ =~= spec_sha256(spec_rp_input(rc, ordinal, params@)),
{
    let mut s = S::new();
    let rc_b = be32_arr(rc);
    let ord_b = be32_arr(ordinal);

    s.update(array_as_slice(&rc_b));
    s.update(array_as_slice(&ord_b));
    s.update(params);

    proof {
        assert(s.absorbed() =~= spec_rp_input(rc, ordinal, params@));
    }

    s.finish()
}

/// `names` is the in-order concatenation of the names of the authorized handles, prepared by the session layer.
pub(crate) fn cp_hash<S: Sha256Ctx>(ordinal: u32, names: &[u8], params: &[u8]) -> (r: [u8; SHA256_LEN])
    ensures
        r@ =~= spec_sha256(spec_cp_input(ordinal, names@, params@)),
{
    let mut s = S::new();
    let ord_b = be32_arr(ordinal);

    s.update(array_as_slice(&ord_b));
    s.update(names);
    s.update(params);

    proof {
        assert(s.absorbed() =~= spec_cp_input(ordinal, names@, params@));
    }

    s.finish()
}

// ===========================================================================
// Command side: write the authorization area
// ===========================================================================

/// Lay out one session at `out[off..]`, leaving the HMAC field empty for now.
///
/// Left empty rather than filled with random bytes: placeholder content cannot take part in any verification, but it will be written into the final message.
/// If the later [`patch_hmac`] is not reached because of an error path, what remains should be obviously
/// all zeros, not something that looks like a real MAC.
pub(crate) fn write_cmd_session(
    out: &mut [u8],
    off: usize,
    handle: u32,
    nonce: &[u8; NONCE_LEN],
    attrs: u8,
)
    requires
        off + CMD_SESSION_LEN <= old(out).len(),
    ensures
        final(out).len() == old(out).len(),
        spec_be32_at(final(out)@, off + SESS_HANDLE_OFF) == handle,
        spec_be16_at(final(out)@, off + SESS_NONCE_SIZE_OFF) == NONCE_LEN as u16,
        final(out)@.subrange(off + SESS_NONCE_OFF, off + SESS_NONCE_OFF + NONCE_LEN) =~= nonce@,
        final(out)@[off + SESS_ATTRS_OFF] == attrs,
        spec_be16_at(final(out)@, off + SESS_HMAC_SIZE_OFF) == NONCE_LEN as u16,
        forall|k: int|
            #![trigger final(out)@[k]]
            0 <= k < final(out).len() && (k < off || k >= off + CMD_SESSION_LEN) ==> final(out)@[k]
                == old(out)@[k],
{
    let ghost before = out@;
    let h = be32_arr(handle);
    let n = be16_arr(NONCE_LEN as u16);

    out[off + SESS_HANDLE_OFF] = h[0];
    out[off + SESS_HANDLE_OFF + 1] = h[1];
    out[off + SESS_HANDLE_OFF + 2] = h[2];
    out[off + SESS_HANDLE_OFF + 3] = h[3];

    out[off + SESS_NONCE_SIZE_OFF] = n[0];
    out[off + SESS_NONCE_SIZE_OFF + 1] = n[1];

    for i in 0..NONCE_LEN
        invariant
            off + CMD_SESSION_LEN <= out.len(),
            out.len() == before.len(),
            spec_be32_at(out@, off + SESS_HANDLE_OFF) == handle,
            spec_be16_at(out@, off + SESS_NONCE_SIZE_OFF) == NONCE_LEN as u16,
            forall|k: int| 0 <= k < i ==> out@[off + SESS_NONCE_OFF + k] == nonce@[k],
            forall|k: int|
                #![trigger out@[k]]
                0 <= k < out.len() && (k < off || k >= off + CMD_SESSION_LEN) ==> out@[k]
                    == before[k],
    {
        out[off + SESS_NONCE_OFF + i] = nonce[i];
    }

    out[off + SESS_ATTRS_OFF] = attrs;
    out[off + SESS_HMAC_SIZE_OFF] = n[0];
    out[off + SESS_HMAC_SIZE_OFF + 1] = n[1];

    for j in 0..NONCE_LEN
        invariant
            off + CMD_SESSION_LEN <= out.len(),
            out.len() == before.len(),
            spec_be32_at(out@, off + SESS_HANDLE_OFF) == handle,
            spec_be16_at(out@, off + SESS_NONCE_SIZE_OFF) == NONCE_LEN as u16,
            spec_be16_at(out@, off + SESS_HMAC_SIZE_OFF) == NONCE_LEN as u16,
            out@[off + SESS_ATTRS_OFF] == attrs,
            out@.subrange(off + SESS_NONCE_OFF, off + SESS_NONCE_OFF + NONCE_LEN) =~= nonce@,
            forall|k: int|
                #![trigger out@[k]]
                0 <= k < out.len() && (k < off || k >= off + CMD_SESSION_LEN) ==> out@[k]
                    == before[k],
    {
        out[off + SESS_HMAC_OFF + j] = 0;
    }
}

/// Fill the computed MAC into the placeholder.
pub(crate) fn patch_hmac(out: &mut [u8], off: usize, mac: &[u8; SHA256_LEN])
    requires
        off + CMD_SESSION_LEN <= old(out).len(),
    ensures
        final(out).len() == old(out).len(),
        final(out)@.subrange(off + SESS_HMAC_OFF, off + SESS_HMAC_OFF + SHA256_LEN) =~= mac@,
        forall|k: int|
            #![trigger final(out)@[k]]
            0 <= k < final(out).len() && (k < off + SESS_HMAC_OFF || k >= off + CMD_SESSION_LEN)
                ==> final(out)@[k] == old(out)@[k],
{
    let ghost before = out@;
    for i in 0..SHA256_LEN
        invariant
            off + CMD_SESSION_LEN <= out.len(),
            out.len() == before.len(),
            forall|k: int| 0 <= k < i ==> out@[off + SESS_HMAC_OFF + k] == mac@[k],
            forall|k: int|
                #![trigger out@[k]]
                0 <= k < out.len() && (k < off + SESS_HMAC_OFF || k >= off + CMD_SESSION_LEN)
                    ==> out@[k] == before[k],
    {
        out[off + SESS_HMAC_OFF + i] = mac[i];
    }
}

// ===========================================================================
// Response side: locate the authorization area
// ===========================================================================

/// Location information in a response that concerns this session.
///
/// Only offsets are recorded, content is not copied: the parameter area can be several thousand bytes, and verification only needs to be able to point at it.
/// The nonce is an exception -- it must persist across rounds, so it has to be copied out.
#[derive(Clone, Copy)]
pub struct RspAuth {
    /// Start of the parameter area.
    pub param_off: usize,
    /// Length of the parameter area.
    pub param_len: usize,
    /// Start of this session's nonce field.
    pub nonce_off: usize,
    /// Start of this session's HMAC field.
    pub hmac_off: usize,
    /// Session attributes reported by the peer.
    pub attrs: u8,
    /// The peer's nonce for this round.
    pub tpm_nonce: [u8; NONCE_LEN],
}

impl RspAuth {
    /// The location result is self-consistent: the segments do not overlap and all lie within the message, and this session's HMAC extends all the way to
    /// the end of the message.
    pub open spec fn wf(self, raw: Seq<u8>) -> bool {
        &&& HEADER_LEN <= self.param_off
        &&& self.param_off + self.param_len <= self.nonce_off
        &&& self.nonce_off + NONCE_LEN + 3 == self.hmac_off
        &&& self.hmac_off + SHA256_LEN == raw.len()
    }

    pub open spec fn params(self, raw: Seq<u8>) -> Seq<u8> {
        raw.subrange(self.param_off as int, self.param_off + self.param_len)
    }

    pub open spec fn mac(self, raw: Seq<u8>) -> Seq<u8> {
        raw.subrange(self.hmac_off as int, self.hmac_off + SHA256_LEN)
    }
}

/// Take a nonce starting at offset `off`.
fn read_nonce(raw: &[u8], off: usize) -> (r: [u8; NONCE_LEN])
    requires
        off + NONCE_LEN <= raw.len(),
    ensures
        r@ =~= raw@.subrange(off as int, off + NONCE_LEN),
{
    let mut out: [u8; NONCE_LEN] = [0u8; NONCE_LEN];
    for i in 0..NONCE_LEN
        invariant
            off + NONCE_LEN <= raw.len(),
            out@.len() == NONCE_LEN,
            forall|k: int| 0 <= k < i ==> out@[k] == raw@[off + k],
    {
        out[i] = raw[off + i];
    }
    out
}

/// Locate the `index`-th session (counting from zero) in the response.
///
/// `rhandles` is the number of handles the response carries, which is only zero or one, taken from the command attribute table;
/// it is not read from the message, because the message itself does not label it.
///
/// Three checks deserve separate explanation:
///
/// - **This session must be the last one.** If other sessions follow it, `hmac_off + 32` is
///   not equal to the message length. This implementation always appends its session at the end, so this is both a format
///   check and corroborating evidence that "what was obtained really is our own session".
/// - **The nonce and HMAC lengths must be exactly the digest length.** Both lengths are given by the peer; once
///   arbitrary values are let through, all later offsets are decided by the peer.
/// - **The length field must equal the received byte count.** One byte short means parsing would read data that does not belong to this
///   response, and one byte too many means the upper layer truncated wrongly.
pub(crate) fn parse_rsp_auth(raw: &[u8], rhandles: usize, index: usize) -> (r: Result<RspAuth, AuthErr>)
    requires
        rhandles <= 1,
        index < MAX_SESSIONS,
    ensures
        r matches Ok(a) ==> {
            &&& a.wf(raw@)
            &&& a.tpm_nonce@ =~= raw@.subrange(a.nonce_off as int, a.nonce_off + NONCE_LEN)
        },
{
    if raw.len() < HEADER_LEN {
        return Err(AuthErr::Malformed);
    }

    let mut c = Cursor::new();

    let tag = c.read_be16(raw).ok_or(AuthErr::Malformed)?;
    let size = c.read_be32(raw).ok_or(AuthErr::Malformed)?;
    // Skip the return code field: only successful responses reach here, and the return code used for verification takes part in the digest as
    // zero per the specification, so it need not be taken from the message.
    if !c.skip(raw, 4) {
        return Err(AuthErr::Malformed);
    }

    if tag != ST_SESSIONS {
        return Err(AuthErr::Malformed);
    }
    if size as usize != raw.len() {
        return Err(AuthErr::Malformed);
    }

    if !c.skip(raw, rhandles * 4) {
        return Err(AuthErr::Malformed);
    }

    let param_len_u32 = c.read_be32(raw).ok_or(AuthErr::Malformed)?;
    if param_len_u32 as usize > raw.len() {
        return Err(AuthErr::Malformed);
    }
    let param_len = param_len_u32 as usize;
    let param_off = c.pos;

    if !c.skip(raw, param_len) {
        return Err(AuthErr::Malformed);
    }

    // Skip the sessions that come first. The number of rounds is capped by `index`, so the loop must terminate.
    for i in 0..index
        invariant
            index < MAX_SESSIONS,
            c.wf(raw@.len()),
    {
        let nl = c.read_be16(raw).ok_or(AuthErr::Malformed)?;
        if !c.skip(raw, nl as usize) {
            return Err(AuthErr::Malformed);
        }
        if !c.skip(raw, 1) {
            return Err(AuthErr::Malformed);
        }
        let hl = c.read_be16(raw).ok_or(AuthErr::Malformed)?;
        if !c.skip(raw, hl as usize) {
            return Err(AuthErr::Malformed);
        }
    }

    let nonce_len = c.read_be16(raw).ok_or(AuthErr::NoSession)?;
    if nonce_len as usize != NONCE_LEN {
        return Err(AuthErr::BadField);
    }

    let nonce_off = c.pos;
    if !c.skip(raw, NONCE_LEN) {
        return Err(AuthErr::Malformed);
    }
    let tpm_nonce = read_nonce(raw, nonce_off);

    let attrs = c.read_u8(raw).ok_or(AuthErr::Malformed)?;

    let hmac_len = c.read_be16(raw).ok_or(AuthErr::Malformed)?;
    if hmac_len as usize != SHA256_LEN {
        return Err(AuthErr::BadField);
    }

    let hmac_off = c.pos;
    let hmac_end = hmac_off.checked_add(SHA256_LEN).ok_or(AuthErr::Malformed)?;
    if hmac_end != raw.len() {
        return Err(AuthErr::Malformed);
    }
    let param_end = param_off.checked_add(param_len).ok_or(AuthErr::Malformed)?;
    if param_end > nonce_off {
        return Err(AuthErr::Malformed);
    }

    Ok(RspAuth { param_off, param_len, nonce_off, hmac_off, attrs, tpm_nonce })
}

// ===========================================================================
// Constant-time comparison
// ===========================================================================

proof fn lemma_or_xor_zero(acc: u8, x: u8, y: u8)
    ensures
        (acc | (x ^ y)) == 0 <==> (acc == 0 && x == y),
{
    assert((acc | (x ^ y)) == 0 <==> (acc == 0 && x == y)) by (bit_vector);
}

/// Compare byte by byte, with no early return.
///
/// An early return makes the comparison time vary with the position of the first differing byte, which tells
/// anyone who can measure time how many bytes were guessed right. MAC comparison must be constant-time.
pub(crate) fn ct_eq32(a: &[u8; SHA256_LEN], b: &[u8]) -> (r: bool)
    requires
        b.len() == SHA256_LEN,
    ensures
        r == (a@ =~= b@),
{
    let mut acc: u8 = 0;
    for i in 0..SHA256_LEN
        invariant
            b.len() == SHA256_LEN,
            (acc == 0) <==> (forall|k: int| 0 <= k < i ==> a@[k] == b@[k]),
    {
        proof {
            lemma_or_xor_zero(acc, a@[i as int], b@[i as int]);
        }
        acc |= a[i] ^ b[i];
    }
    acc == 0
}

} // verus!