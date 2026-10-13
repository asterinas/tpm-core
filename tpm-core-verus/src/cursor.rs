use vstd::prelude::*;
use vstd::slice::*;

verus! {

// ===================== Byte-order spec =====================
//
// Messages are always big-endian (TPM 2.0 Part 1, "Data Marshaling"). This gives the **single authoritative**
// serialization spec; both the encoding and decoding sides are proved against it, so the two sides can never
// disagree on byte order. If the project already has a unified byte-order spec module, replace these three spec fns with a re-export of that
// module; never keep two definitions side by side.

/// The big-endian u16 at offset `i` in sequence `s`.
pub open spec fn spec_be16_at(s: Seq<u8>, i: int) -> u16
    recommends
        0 <= i,
        i + 2 <= s.len(),
{
    (s[i] as u16 * 256 + s[i + 1] as u16) as u16
}

/// The big-endian u32 at offset `i` in sequence `s`.
pub open spec fn spec_be32_at(s: Seq<u8>, i: int) -> u32
    recommends
        0 <= i,
        i + 4 <= s.len(),
{
    (s[i] as u32 * 16777216 + s[i + 1] as u32 * 65536 + s[i + 2] as u32 * 256 + s[i + 3] as u32)
        as u32
}

// ===================== Split / reassemble lemmas =====================
//
// The encoding side splits an integer into bytes, and the decoding side reassembles bytes into an integer per the spec above. That the two are inverse
// is the foundation of the whole codec layer; it is proved once here, and all command construction then references it directly.
//
// The split uses division and remainder rather than shifts and masks: on u16/u32 the two are fully equivalent, and the division
// form stays within integer theory, keeping the bit-vector solver out of the whole proof chain.

pub proof fn lemma_be16_split(v: u16)
    ensures
        (((v / 256) as u8) as u16 * 256 + ((v % 256) as u8) as u16) as u16 == v,
{
    assert(v / 256 < 256) by (bit_vector);
    assert(v % 256 < 256) by (bit_vector);
    assert(v == (v / 256) * 256 + v % 256) by (bit_vector);
}

pub proof fn lemma_be32_split(v: u32)
    ensures
        (((v / 16777216) as u8) as u32 * 16777216 + (((v / 65536) % 256) as u8) as u32 * 65536 + ((
        (v / 256) % 256) as u8) as u32 * 256 + ((v % 256) as u8) as u32) as u32 == v,
{
    assert(v / 16777216 < 256) by (bit_vector);
    assert((v / 65536) % 256 < 256) by (bit_vector);
    assert((v / 256) % 256 < 256) by (bit_vector);
    assert(v % 256 < 256) by (bit_vector);
    assert(v == (v / 16777216) * 16777216 + ((v / 65536) % 256) * 65536 + ((v / 256) % 256) * 256
        + v % 256) by (bit_vector);
}

/// Integer -> big-endian bytes. The inverse of `spec_be16_at`.
pub(crate) fn be16_bytes(v: u16) -> (r: [u8; 2])
    ensures
        r@.len() == 2,
        r@[0] == (v / 256) as u8,
        r@[1] == (v % 256) as u8,
        spec_be16_at(r@, 0) == v,
{
    let r = be16_bytes_std(v);
    proof {
        lemma_be16_split(v);
    }
    r
}

/// Standard library big-endian conversion. Its signature carries a const generic expression, so Verus cannot write an
/// `assume_specification`; the contract is pinned with `external_body` instead.
#[verifier::external_body]
fn be16_bytes_std(v: u16) -> (r: [u8; 2])
    ensures
        r@.len() == 2,
        r@[0] == (v / 256) as u8,
        r@[1] == (v % 256) as u8,
{
    v.to_be_bytes()
}

/// Integer -> big-endian bytes. The inverse of `spec_be32_at`.
pub(crate) fn be32_bytes(v: u32) -> (r: [u8; 4])
    ensures
        r@.len() == 4,
        r@[0] == (v / 16777216) as u8,
        r@[1] == ((v / 65536) % 256) as u8,
        r@[2] == ((v / 256) % 256) as u8,
        r@[3] == (v % 256) as u8,
        spec_be32_at(r@, 0) == v,
{
    let r = be32_bytes_std(v);
    proof {
        lemma_be32_split(v);
    }
    r
}

/// Same as [`be16_bytes_std`].
#[verifier::external_body]
fn be32_bytes_std(v: u32) -> (r: [u8; 4])
    ensures
        r@.len() == 4,
        r@[0] == (v / 16777216) as u8,
        r@[1] == ((v / 65536) % 256) as u8,
        r@[2] == ((v / 256) % 256) as u8,
        r@[3] == (v % 256) as u8,
{
    v.to_be_bytes()
}

// ===================== Cursor =====================

/// Read-only parsing cursor. The field is public so that the spec functions can stay `open`,
/// and cross-module reasoning needs no extra lemmas.
pub struct Cursor {
    pub pos: usize,
}

impl Cursor {
    /// Type invariant: the offset does not exceed the length of the sequence being parsed.
    pub open spec fn wf(self, len: nat) -> bool {
        self.pos <= len
    }

    /// Whether `n` more bytes can still be taken from the current position.
    pub open spec fn can_read(self, len: nat, n: nat) -> bool {
        self.pos + n <= len
    }

    pub fn new() -> (r: Cursor)
        ensures
            r.pos == 0,
    {
        Cursor { pos: 0 }
    }

    /// Start parsing from the given offset (used to skip a fixed prefix already validated by an upper layer).
    pub fn at(pos: usize) -> (r: Cursor)
        ensures
            r.pos == pos,
    {
        Cursor { pos }
    }

    pub fn remaining(&self, data: &[u8]) -> (r: usize)
        requires
            self.wf(data@.len()),
        ensures
            r == data@.len() - self.pos,
    {
        data.len() - self.pos
    }

    /// Whether the remaining bytes have been read exactly to the end. Used for checks such as "no extra data after the response tail".
    pub fn is_exhausted(&self, data: &[u8]) -> (r: bool)
        requires
            self.wf(data@.len()),
        ensures
            r == (self.pos == data@.len()),
    {
        self.pos == data.len()
    }

    pub fn read_u8(&mut self, data: &[u8]) -> (r: Option<u8>)
        requires
            old(self).wf(data@.len()),
        ensures
            final(self).wf(data@.len()),
            old(self).can_read(data@.len(), 1) ==> {
                &&& r == Some(data@[old(self).pos as int])
                &&& final(self).pos == old(self).pos + 1
            },
            !old(self).can_read(data@.len(), 1) ==> {
                &&& r == Option::<u8>::None
                &&& final(self).pos == old(self).pos
            },
    {
        if self.pos < data.len() {
            let v = data[self.pos];
            self.pos += 1;
            Some(v)
        } else {
            None
        }
    }

    pub fn read_be16(&mut self, data: &[u8]) -> (r: Option<u16>)
        requires
            old(self).wf(data@.len()),
        ensures
            final(self).wf(data@.len()),
            old(self).can_read(data@.len(), 2) ==> {
                &&& r == Some(spec_be16_at(data@, old(self).pos as int))
                &&& final(self).pos == old(self).pos + 2
            },
            !old(self).can_read(data@.len(), 2) ==> {
                &&& r == Option::<u16>::None
                &&& final(self).pos == old(self).pos
            },
    {
        let n = data.len();
        if n >= 2 && self.pos <= n - 2 {
            let hi = data[self.pos];
            let lo = data[self.pos + 1];
            self.pos += 2;
            Some(hi as u16 * 256 + lo as u16)
        } else {
            None
        }
    }

    pub fn read_be32(&mut self, data: &[u8]) -> (r: Option<u32>)
        requires
            old(self).wf(data@.len()),
        ensures
            final(self).wf(data@.len()),
            old(self).can_read(data@.len(), 4) ==> {
                &&& r == Some(spec_be32_at(data@, old(self).pos as int))
                &&& final(self).pos == old(self).pos + 4
            },
            !old(self).can_read(data@.len(), 4) ==> {
                &&& r == Option::<u32>::None
                &&& final(self).pos == old(self).pos
            },
    {
        let n = data.len();
        if n >= 4 && self.pos <= n - 4 {
            let b0 = data[self.pos];
            let b1 = data[self.pos + 1];
            let b2 = data[self.pos + 2];
            let b3 = data[self.pos + 3];
            self.pos += 4;
            Some(b0 as u32 * 16777216 + b1 as u32 * 65536 + b2 as u32 * 256 + b3 as u32)
        } else {
            None
        }
    }

    /// Lend out the next `n` bytes. This is the only way to take
    /// variable-length fields (`TPM2B`, PCR select bitmaps) -- the length comes from the message itself, so the bounds check must happen here.
    pub fn read_bytes<'a>(&mut self, data: &'a [u8], n: usize) -> (r: Option<&'a [u8]>)
        requires
            old(self).wf(data@.len()),
        ensures
            final(self).wf(data@.len()),
            old(self).can_read(data@.len(), n as nat) ==> {
                &&& r matches Some(s)
                &&& s@ == data@.subrange(old(self).pos as int, old(self).pos + n)
                &&& s@.len() == n
                &&& final(self).pos == old(self).pos + n
            },
            !old(self).can_read(data@.len(), n as nat) ==> {
                &&& r is None
                &&& final(self).pos == old(self).pos
            },
    {
        let len = data.len();
        if n <= len && self.pos <= len - n {
            let start = self.pos;
            let end = self.pos + n;
            let s = &data[start..end];
            self.pos = end;
            Some(s)
        } else {
            None
        }
    }

    /// Skip `n` bytes. Used to ignore fields that are not of interest at this stage but whose format is known.
    pub fn skip(&mut self, data: &[u8], n: usize) -> (r: bool)
        requires
            old(self).wf(data@.len()),
        ensures
            final(self).wf(data@.len()),
            r == old(self).can_read(data@.len(), n as nat),
            r ==> final(self).pos == old(self).pos + n,
            !r ==> final(self).pos == old(self).pos,
    {
        let len = data.len();
        if n <= len && self.pos <= len - n {
            self.pos += n;
            true
        } else {
            false
        }
    }
}

// ===================== Helper predicates =====================

/// Whether the slice contains a non-zero byte.
///
/// PCR allocation parsing relies on it to decide whether a bank is really allocated (an all-zero select bitmap means unallocated).
pub(crate) fn any_nonzero(s: &[u8]) -> (r: bool)
    ensures
        r == exists|k: int| 0 <= k < s@.len() && s@[k] != 0,
{
    let n = s.len();
    for i in 0..n
        invariant
            n == s@.len(),
            forall|k: int| 0 <= k < i ==> s@[k] == 0,
    {
        if s[i] != 0 {
            proof {
                assert(0 <= i < s@.len() && s@[i as int] != 0);
            }
            return true;
        }
    }
    false
}

} // verus!
