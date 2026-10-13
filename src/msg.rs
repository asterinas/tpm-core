use crate::cursor::*;

pub(crate) const TPM_HEADER_LEN: usize = 10;
/// Response tag without sessions.
pub(crate) const ST_NO_SESSIONS: u16 = 0x8001;
/// Response tag with sessions (authorization area).
pub const ST_SESSIONS: u16 = 0x8002;
/// Success return code.
pub const RC_SUCCESS: u32 = 0x0000;
#[derive(PartialEq, Eq)]
pub enum ParseError {
    /// Not enough bytes to read the next field.
    Truncated,
    /// Length field does not match the actual byte count, or a field value exceeds the specification.
    Malformed,
    /// Count exceeds the static capacity limit of this implementation.
    Capacity,
    /// The syntax is valid but this implementation does not support it (unknown algorithm, unexpected
    /// response shape).
    Unsupported,
    /// TPM reported a non-zero return code.
    TpmError(u32),
}
/// Abstract view of a message header. `code` is the command code in request direction and the return
/// code in response direction.
pub struct HeaderView {
    pub tag: u16,
    pub size: u32,
    pub code: u32,
}
/// A validated response: the three header fields plus the payload without the header.
pub struct Response<'a> {
    pub tag: u16,
    pub rc: u32,
    pub body: &'a [u8],
}
impl<'a> Response<'a> {
    pub fn is_success(&self) -> bool {
        self.rc == RC_SUCCESS
    }
}
/// Validate and split a response.
///
/// Rejects three kinds of input: length shorter than a header, `size` not matching the actual byte
/// count, and a tag that is not one of the two valid response tags. If the return code is non-zero, the
/// payload is no longer parsed — the payload contents of a failure response are undefined by the
/// specification.
pub(crate) fn parse_response(raw: &[u8]) -> Result<Response<'_>, ParseError> {
    if raw.len() < TPM_HEADER_LEN {
        return Err(ParseError::Truncated);
    }
    let mut c = Cursor::new();
    let tag = c.read_be16(raw).ok_or(ParseError::Truncated)?;
    let size = c.read_be32(raw).ok_or(ParseError::Truncated)?;
    let rc = c.read_be32(raw).ok_or(ParseError::Truncated)?;
    if size as usize != raw.len() {
        return Err(ParseError::Malformed);
    }
    if tag != ST_NO_SESSIONS && tag != ST_SESSIONS {
        return Err(ParseError::Malformed);
    }
    if rc != RC_SUCCESS {
        return Err(ParseError::TpmError(rc));
    }
    let body = &raw[TPM_HEADER_LEN..raw.len()];
    Ok(Response { tag, rc, body })
}
/// Byte layout of the request header. The command payload is constructed by the `cmd` module, and the
/// two are concatenated to form the full request.
///
/// `size` must be filled in after the payload length is known, so this module only provides a pure
/// function that generates the header from a total length; the buffer layer calls it at the end.
pub(crate) fn build_header(tag: u16, code: u32, total_size: u32) -> [u8; 10] {
    let t = be16_bytes(tag);
    let s = be32_bytes(total_size);
    let c = be32_bytes(code);
    [t[0], t[1], s[0], s[1], s[2], s[3], c[0], c[1], c[2], c[3]]
}
