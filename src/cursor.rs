/// Integer to big-endian bytes. This is the inverse of `spec_be16_at`.
pub(crate) fn be16_bytes(v: u16) -> [u8; 2] {
    v.to_be_bytes()
}
/// Integer to big-endian bytes. This is the inverse of `spec_be32_at`.
pub(crate) fn be32_bytes(v: u32) -> [u8; 4] {
    v.to_be_bytes()
}
/// Read-only parsing cursor. `pos` is private; progress can only happen through `read_*`/`skip`, and
/// external code can read the current position via [`Cursor::pos`].
pub struct Cursor {
    pos: usize,
}
impl Cursor {
    pub fn new() -> Cursor {
        Cursor { pos: 0 }
    }
    /// Current parsing position. The parser uses this to record the start of each field (for example,
    /// parameter area offsets or nonce offsets).
    pub fn pos(&self) -> usize {
        self.pos
    }
}

impl Default for Cursor {
    fn default() -> Self {
        Self::new()
    }
}

impl Cursor {
    /// Parse starting at a specified offset (for skipping fixed prefixes that were already validated by a
    /// higher layer).
    pub fn at(pos: usize) -> Cursor {
        Cursor { pos }
    }
    pub fn remaining(&self, data: &[u8]) -> usize {
        data.len() - self.pos
    }
    /// Whether the remaining bytes are exactly exhausted. Used for checks such as “the response tail must
    /// contain no extra data.”
    pub fn is_exhausted(&self, data: &[u8]) -> bool {
        self.pos == data.len()
    }
    pub fn read_u8(&mut self, data: &[u8]) -> Option<u8> {
        if self.pos < data.len() {
            let v = data[self.pos];
            self.pos += 1;
            Some(v)
        } else {
            None
        }
    }
    pub fn read_be16(&mut self, data: &[u8]) -> Option<u16> {
        let n = data.len();
        if n >= 2 && self.pos <= n - 2 {
            let v = u16::from_be_bytes([data[self.pos], data[self.pos + 1]]);
            self.pos += 2;
            Some(v)
        } else {
            None
        }
    }
    pub fn read_be32(&mut self, data: &[u8]) -> Option<u32> {
        let n = data.len();
        if n >= 4 && self.pos <= n - 4 {
            let v = u32::from_be_bytes([
                data[self.pos],
                data[self.pos + 1],
                data[self.pos + 2],
                data[self.pos + 3],
            ]);
            self.pos += 4;
            Some(v)
        } else {
            None
        }
    }
    /// Borrow the next `n` bytes. This is the only way to consume variable-length fields such as `TPM2B`
    /// and PCR selection bitmaps; the length comes from the packet itself, so boundary checks must happen
    /// here.
    pub fn read_bytes<'a>(&mut self, data: &'a [u8], n: usize) -> Option<&'a [u8]> {
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
    /// Skip `n` bytes. This is used to ignore fields that are uninteresting in the current phase but whose
    /// layout is known.
    pub fn skip(&mut self, data: &[u8], n: usize) -> bool {
        let len = data.len();
        if n <= len && self.pos <= len - n {
            self.pos += n;
            true
        } else {
            false
        }
    }
}
/// Whether a slice contains any non-zero bytes.
///
/// PCR allocation parsing uses this to determine whether a bank is actually allocated; a zero selection
/// bitmap means the algorithm is supported but not active.
pub(crate) fn any_nonzero(s: &[u8]) -> bool {
    s.iter().any(|&b| b != 0)
}
