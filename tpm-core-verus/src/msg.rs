use vstd::prelude::*;
use vstd::array::*;
use vstd::slice::*;

use crate::cursor::*;

verus! {

pub const TPM_HEADER_LEN: usize = 10;

/// Response tag without sessions.
pub(crate) const ST_NO_SESSIONS: u16 = 0x8001;
/// Response tag with sessions (authorization area).
pub const ST_SESSIONS: u16 = 0x8002;

/// Success return code.
pub const RC_SUCCESS: u32 = 0x0000;

// ===================== Parse errors =====================

#[derive(PartialEq, Eq, Structural)]
pub enum ParseError {
    /// Not enough bytes to take the next field.
    Truncated,
    /// The length field does not match the actual byte count, or a field value is outside the range the specification allows.
    Malformed,
    /// A count exceeds this implementation's static capacity limit.
    Capacity,
    /// Syntactically valid but unsupported by this implementation (unknown algorithm, unexpected response shape).
    Unsupported,
    /// The TPM reported a non-zero return code.
    TpmError(u32),
}

// ===================== Header spec =====================

/// Abstract view of the message header. `code` is the command code in the request direction and the return code in the response direction.
pub struct HeaderView {
    pub tag: u16,
    pub size: u32,
    pub code: u32,
}

pub open spec fn spec_header(s: Seq<u8>) -> HeaderView
    recommends
        s.len() >= TPM_HEADER_LEN,
{
    HeaderView { tag: spec_be16_at(s, 0), size: spec_be32_at(s, 2), code: spec_be32_at(s, 6) }
}

/// A response is "well-formed": it holds a header, and the length field matches the received byte count exactly.
///
/// This is the anchor property of the whole decoding layer. If a slice handed up by the transport layer does not satisfy it, parsing
/// never starts, so all later offset reasoning can safely be bounded by `s.len()`.
pub open spec fn spec_rsp_wf(s: Seq<u8>) -> bool {
    &&& s.len() >= TPM_HEADER_LEN
    &&& spec_header(s).size as nat == s.len()
}

// ===================== Response view =====================

/// A validated response: the three header fields + the payload with the header removed.
pub struct Response<'a> {
    pub tag: u16,
    pub rc: u32,
    pub body: &'a [u8],
}

impl<'a> Response<'a> {
    pub open spec fn wf(self, raw: Seq<u8>) -> bool {
        &&& spec_rsp_wf(raw)
        &&& self.tag == spec_header(raw).tag
        &&& self.rc == spec_header(raw).code
        &&& self.body@ == raw.subrange(TPM_HEADER_LEN as int, raw.len() as int)
        &&& self.body@.len() == raw.len() - TPM_HEADER_LEN
    }

    pub fn is_success(&self) -> (r: bool)
        ensures
            r == (self.rc == RC_SUCCESS),
    {
        self.rc == RC_SUCCESS
    }
}

/// Validate and take apart a response.
///
/// Rejects three kinds of input: length shorter than a header, a `size` field that does not match the received byte count, and
/// a tag that is not one of the two legal response tags. When the return code is non-zero, the payload is not parsed further --
/// the payload content of a failed response is undefined by the specification.
pub(crate) fn parse_response(raw: &[u8]) -> (r: Result<Response<'_>, ParseError>)
    ensures
        r matches Ok(rsp) ==> {
            &&& rsp.wf(raw@)
            &&& rsp.rc == RC_SUCCESS
            &&& rsp.tag == ST_NO_SESSIONS || rsp.tag == ST_SESSIONS
        },
{
    if raw.len() < TPM_HEADER_LEN {
        return Err(ParseError::Truncated);
    }

    let mut c = Cursor::new();

    let tag = c.read_be16(raw).ok_or(ParseError::Truncated)?;
    let size = c.read_be32(raw).ok_or(ParseError::Truncated)?;
    let rc = c.read_be32(raw).ok_or(ParseError::Truncated)?;

    // The length field must equal the received byte count exactly: one extra byte means the upper layer truncated wrongly,
    // one byte short means later parsing would read data that does not belong to this response.
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

// ===================== Request header =====================

/// Byte form of the request header. The command payload is built by the `cmd` module; concatenating the two gives the whole request.
///
/// `size` has to be filled in once the payload length is known, so only a pure function "generate the header
/// given the total length" is provided here, called by the buffer layer at the end.
pub(crate) fn build_header(tag: u16, code: u32, total_size: u32) -> (r: [u8; 10])
    ensures
        r@.len() == 10,
        spec_be16_at(r@, 0) == tag,
        spec_be32_at(r@, 2) == total_size,
        spec_be32_at(r@, 6) == code,
{
    let t = be16_bytes(tag);
    let s = be32_bytes(total_size);
    let c = be32_bytes(code);
    [t[0], t[1], s[0], s[1], s[2], s[3], c[0], c[1], c[2], c[3]]
}

} // verus!
