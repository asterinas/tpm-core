use crate::{crypto::*, cursor::Cursor};

/// Tag: 2 bytes + length: 4 bytes + command code or return code: 4 bytes.
pub const HEADER_LEN: usize = 10;
/// Tag for a packet with an authorization area. The authorization area exists only under this tag.
pub const ST_SESSIONS: u16 = 0x8002;
/// Session attribute bits.
pub const SA_CONTINUE_SESSION: u8 = 0x01;
pub const SA_DECRYPT: u8 = 0x20;
pub const SA_ENCRYPT: u8 = 0x40;
/// Maximum number of sessions allowed in the authorization area.
///
/// The spec limit is 3. This implementation appends only its own session, but the response may
/// contain additional sessions appended by the caller; the parsing side must still skip them. The
/// number of skipped sessions must be bounded, otherwise a carefully crafted response could stall
/// the parsing loop indefinitely.
pub const MAX_SESSIONS: usize = 3;
const SESS_HANDLE_OFF: usize = 0;
const SESS_NONCE_SIZE_OFF: usize = 4;
const SESS_NONCE_OFF: usize = 6;
const SESS_ATTRS_OFF: usize = SESS_NONCE_OFF + NONCE_LEN;
const SESS_HMAC_SIZE_OFF: usize = SESS_ATTRS_OFF + 1;
const SESS_HMAC_OFF: usize = SESS_HMAC_SIZE_OFF + 2;
/// Number of bytes consumed by a single command-side session.
pub const CMD_SESSION_LEN: usize = SESS_HMAC_OFF + NONCE_LEN;
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AuthErr {
    /// The packet structure does not match the length it declares.
    Malformed,
    /// The current session cannot be located in the authorization area.
    NoSession,
    /// The nonce or HMAC field length is not the expected digest length. These lengths are under the
    /// peer's control; accepting arbitrary values would effectively let the peer decide all later
    /// offset computations.
    BadField,
    /// The recomputed HMAC does not match the received one.
    HmacMismatch,
}
pub(crate) fn auth_hmac<H: HmacSha256Ctx>(
    key: &[u8],
    digest: &[u8; SHA256_LEN],
    newer: &[u8; NONCE_LEN],
    older: &[u8; NONCE_LEN],
    attrs: u8,
) -> [u8; SHA256_LEN] {
    let mut h = H::with_key(key);
    let tail: [u8; 1] = [attrs];
    h.update(&digest[..]);
    h.update(&newer[..]);
    h.update(&older[..]);
    h.update(&tail[..]);
    h.finish()
}
pub(crate) fn rp_hash<S: Sha256Ctx>(rc: u32, ordinal: u32, params: &[u8]) -> [u8; SHA256_LEN] {
    let mut s = S::new();
    let rc_b = be32_arr(rc);
    let ord_b = be32_arr(ordinal);
    s.update(&rc_b[..]);
    s.update(&ord_b[..]);
    s.update(params);
    s.finish()
}
/// `names` is the concatenation of the names of all authorized handles, prepared by the session layer.
pub(crate) fn cp_hash<S: Sha256Ctx>(ordinal: u32, names: &[u8], params: &[u8]) -> [u8; SHA256_LEN] {
    let mut s = S::new();
    let ord_b = be32_arr(ordinal);
    s.update(&ord_b[..]);
    s.update(names);
    s.update(params);
    s.finish()
}
/// Lay out a session at `out[off..]`, leaving the HMAC field blank.
///
/// We leave it blank instead of filling it with random bytes: the placeholder is not part of any
/// checksum, but it will still be written into the final packet. If a later [`patch_hmac`] call is
/// skipped because of an error path, the leftover should be an obvious all-zero pattern rather than
/// something that looks like a real MAC.
pub(crate) fn write_cmd_session(
    out: &mut [u8],
    off: usize,
    handle: u32,
    nonce: &[u8; NONCE_LEN],
    attrs: u8,
) {
    let h = be32_arr(handle);
    let n = be16_arr(NONCE_LEN as u16);
    out[off + SESS_HANDLE_OFF] = h[0];
    out[off + SESS_HANDLE_OFF + 1] = h[1];
    out[off + SESS_HANDLE_OFF + 2] = h[2];
    out[off + SESS_HANDLE_OFF + 3] = h[3];
    out[off + SESS_NONCE_SIZE_OFF] = n[0];
    out[off + SESS_NONCE_SIZE_OFF + 1] = n[1];
    let nonce_start = off + SESS_NONCE_OFF;
    out[nonce_start..nonce_start + NONCE_LEN].copy_from_slice(nonce);
    out[off + SESS_ATTRS_OFF] = attrs;
    out[off + SESS_HMAC_SIZE_OFF] = n[0];
    out[off + SESS_HMAC_SIZE_OFF + 1] = n[1];
    let hmac_start = off + SESS_HMAC_OFF;
    out[hmac_start..hmac_start + NONCE_LEN].fill(0);
}
/// Fill the reserved MAC field with the computed value.
pub(crate) fn patch_hmac(out: &mut [u8], off: usize, mac: &[u8; SHA256_LEN]) {
    let start = off + SESS_HMAC_OFF;
    out[start..start + SHA256_LEN].copy_from_slice(mac);
}
/// Session-related position information for a single response.
///
/// We record only the offsets and not the content: the parameter area may be thousands of bytes long,
/// and the checksum only needs a way to point to it. The nonce is the exception—it must survive across
/// rounds and therefore must be copied out.
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
/// Extract a nonce slice starting at `off`.
fn read_nonce(raw: &[u8], off: usize) -> [u8; NONCE_LEN] {
    let mut out = [0u8; NONCE_LEN];
    out.copy_from_slice(&raw[off..off + NONCE_LEN]);
    out
}
/// Locate the `index`-th session in the response (counting from zero).
///
/// `rhandles` is the number of handle slots returned by the response; it is either zero or one and is
/// derived from the command attribute table. It is not read from the packet itself because the packet
/// does not indicate it.
///
/// Three checks are worth calling out separately:
///
/// - **This session must be the last one.** If there are any sessions after it, `hmac_off + 32` will not
///   equal the packet length. This implementation always appends its own session last, so this check is
///   both a format check and a side condition that proves we are looking at the correct session.
/// - **The nonce and HMAC lengths must exactly match the digest length.** These lengths are chosen by the
///   peer; allowing arbitrary values would hand all later offset reasoning to the peer.
/// - **The length field must match the number of bytes actually present.** If it is one byte short, the
///   parser will read data that belongs to the next response; if it is one byte too long, the caller will
///   truncate the response incorrectly.
pub(crate) fn parse_rsp_auth(
    raw: &[u8],
    rhandles: usize,
    index: usize,
) -> Result<RspAuth, AuthErr> {
    if raw.len() < HEADER_LEN {
        return Err(AuthErr::Malformed);
    }
    let mut c = Cursor::new();
    let tag = c.read_be16(raw).ok_or(AuthErr::Malformed)?;
    let size = c.read_be32(raw).ok_or(AuthErr::Malformed)?;
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
    let param_off = c.pos();
    if !c.skip(raw, param_len) {
        return Err(AuthErr::Malformed);
    }
    for _ in 0..index {
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
    let nonce_off = c.pos();
    if !c.skip(raw, NONCE_LEN) {
        return Err(AuthErr::Malformed);
    }
    let tpm_nonce = read_nonce(raw, nonce_off);
    let attrs = c.read_u8(raw).ok_or(AuthErr::Malformed)?;
    let hmac_len = c.read_be16(raw).ok_or(AuthErr::Malformed)?;
    if hmac_len as usize != SHA256_LEN {
        return Err(AuthErr::BadField);
    }
    let hmac_off = c.pos();
    let hmac_end = hmac_off.checked_add(SHA256_LEN).ok_or(AuthErr::Malformed)?;
    if hmac_end != raw.len() {
        return Err(AuthErr::Malformed);
    }
    let param_end = param_off.checked_add(param_len).ok_or(AuthErr::Malformed)?;
    if param_end > nonce_off {
        return Err(AuthErr::Malformed);
    }
    Ok(RspAuth {
        param_off,
        param_len,
        nonce_off,
        hmac_off,
        attrs,
        tpm_nonce,
    })
}
/// Compare byte by byte without early return.
///
/// Early return makes the comparison time depend on the position of the first differing byte, which is
/// equivalent to telling the timing side how many bytes were guessed correctly. MAC comparison must be
/// constant-time.
pub(crate) fn ct_eq32(a: &[u8; SHA256_LEN], b: &[u8]) -> bool {
    let mut acc: u8 = 0;
    for i in 0..SHA256_LEN {
        acc |= a[i] ^ b[i];
    }
    acc == 0
}
