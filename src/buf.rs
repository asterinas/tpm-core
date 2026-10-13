//! Fixed-size command buffer.
//!
//! yufan: The commands used in the
//! boot phase are written directly into the fixed-size temporary buffer by `boot`, while commands
//! with authorization are described by partitions in `secure::CmdLayout`; neither path goes through
//! here. It remains because the “write the payload first, then fill in the length later” assembly
//! pattern is bound to be needed eventually, not because there is already a caller for it.
//!
//! Therefore, before we assign it a definite purpose, new commands should be written along the two
//! paths above and not modeled on this one: its error model is the sticky flags `overflow` and
//! `boundary_error` with a final uniform collection, which is not the same as the rest of the layers
//! returning `Result` inline; its byte order also follows `endian` rather than `cursor`. Having both
//! approaches coexist is already enough; there should not be a third one.

use crate::{endian::*, types::TpmTag};

/// Size of `struct tpm_header`: tag (2) + length (4) + ordinal/return_code (4).
pub const TPM_HEADER_SIZE: usize = 10;
/// TPM2B header: a single 16-bit size field.
pub const TPM2B_HEADER_SIZE: usize = 2;
/// The kernel glue layer should reimplement this as page allocation and **Box** it to avoid placing a
/// 4 KiB buffer on the kernel stack; the default implementation here is only for host-side differential
/// testing.
fn alloc_zeroed_storage<const N: usize>() -> [u8; N] {
    [0u8; N]
}
/// It differs from `overflow`/`boundary_error` in that the kind is fixed at construction time and then
/// never changes.
#[derive(Clone, Copy)]
pub enum BufKind {
    /// Ordinary command buffer with a `struct tpm_header` prefix.
    Command,
    /// TPM2B buffer with a 2-byte size prefix.
    Tpm2b,
}
pub struct TpmBuf<const N: usize> {
    pub data: [u8; N],
    pub length: usize,
    pub kind: BufKind,
    pub overflow: bool,
    pub boundary_error: bool,
    pub handles: u8,
}
impl<const N: usize> TpmBuf<N> {
    fn put_be16(&mut self, at: usize, v: u16) {
        self.data[at..at + 2].copy_from_slice(&v.to_be_bytes());
    }
    fn put_be32(&mut self, at: usize, v: u32) {
        self.data[at..at + 4].copy_from_slice(&v.to_be_bytes());
    }
    /// Write back `self.length` to the length field in the header.
    fn sync_length(&mut self) {
        match self.kind {
            BufKind::Tpm2b => {
                let sz: u16 = (self.length - TPM2B_HEADER_SIZE) as u16;
                self.put_be16(0, sz);
            }
            BufKind::Command => {
                let l: u32 = self.length as u32;
                self.put_be32(2, l);
            }
        }
    }
    /// Corresponds to `tpm_buf_reset()`: initialize an existing storage area in place as a command.
    pub fn reset_command(&mut self, tag: TpmTag, ordinal: u32) {
        self.kind = BufKind::Command;
        self.overflow = false;
        self.boundary_error = false;
        self.handles = 0;
        self.length = TPM_HEADER_SIZE;
        let t = tag.code();
        self.put_be16(0, t);
        self.put_be32(2, TPM_HEADER_SIZE as u32);
        self.put_be32(6, ordinal);
    }
    /// Corresponds to `tpm_buf_reset_sized()`.
    pub fn reset_sized(&mut self) {
        self.kind = BufKind::Tpm2b;
        self.overflow = false;
        self.boundary_error = false;
        self.handles = 0;
        self.length = TPM2B_HEADER_SIZE;
        self.put_be16(0, 0u16);
    }
    /// Corresponds to `tpm_buf_init()`: allocate + initialize.
    pub fn new_command(tag: TpmTag, ordinal: u32) -> Self {
        let mut buf = TpmBuf {
            data: alloc_zeroed_storage::<N>(),
            length: 0,
            kind: BufKind::Command,
            overflow: false,
            boundary_error: false,
            handles: 0,
        };
        buf.reset_command(tag, ordinal);
        buf
    }
    /// Corresponds to `tpm_buf_init_sized()`.
    pub fn new_sized() -> Self {
        let mut buf = TpmBuf {
            data: alloc_zeroed_storage::<N>(),
            length: 0,
            kind: BufKind::Tpm2b,
            overflow: false,
            boundary_error: false,
            handles: 0,
        };
        buf.reset_sized();
        buf
    }
    /// Corresponds to `tpm_buf_append()`.
    pub fn append(&mut self, src: &[u8]) {
        if self.overflow {
            return;
        }
        let avail: usize = N - self.length;
        if src.len() > avail {
            self.overflow = true;
            return;
        }
        let start: usize = self.length;
        self.data[start..start + src.len()].copy_from_slice(src);
        self.length = start + src.len();
        self.sync_length();
    }
    pub fn append_u8(&mut self, v: u8) {
        if self.overflow {
            return;
        }
        if self.length >= N {
            self.overflow = true;
            return;
        }
        let start = self.length;
        self.data[start] = v;
        self.length = start + 1;
        self.sync_length();
    }
    pub fn append_u16(&mut self, v: u16) {
        if self.overflow {
            return;
        }
        if N - self.length < 2 {
            self.overflow = true;
            return;
        }
        let start = self.length;
        self.put_be16(start, v);
        self.length = start + 2;
        self.sync_length();
    }
    pub fn append_u32(&mut self, v: u32) {
        if self.overflow {
            return;
        }
        if N - self.length < 4 {
            self.overflow = true;
            return;
        }
        let start = self.length;
        self.put_be32(start, v);
        self.length = start + 4;
        self.sync_length();
    }
    /// Corresponds to `tpm_buf_append_handle()`.
    pub fn append_handle(&mut self, handle: u32) -> bool {
        if self.is_tpm2b() {
            return false;
        }
        if self.handles == 255 {
            return false;
        }
        if self.overflow {
            return false;
        }
        if N - self.length < 4 {
            self.overflow = true;
            return false;
        }
        self.append_u32(handle);
        self.handles += 1;
        true
    }
    /// Corresponds to `tpm_buf_read_u8()`.
    pub fn read_u8(&mut self, offset: &mut usize) -> u8 {
        if self.boundary_error {
            return 0;
        }
        if *offset > self.length || self.length - *offset < 1 {
            self.boundary_error = true;
            return 0;
        }
        let v = self.data[*offset];
        *offset += 1;
        v
    }
    /// Corresponds to `tpm_buf_read_u16()`.
    pub fn read_u16(&mut self, offset: &mut usize) -> u16 {
        if self.boundary_error {
            return 0;
        }
        if *offset > self.length || self.length - *offset < 2 {
            self.boundary_error = true;
            return 0;
        }
        let o = *offset;
        let b0 = self.data[o];
        let b1 = self.data[o + 1];
        *offset = o + 2;
        be16_of_exec(b0, b1)
    }
    /// Corresponds to `tpm_buf_read_u32()`.
    pub fn read_u32(&mut self, offset: &mut usize) -> u32 {
        if self.boundary_error {
            return 0;
        }
        if *offset > self.length || self.length - *offset < 4 {
            self.boundary_error = true;
            return 0;
        }
        let o = *offset;
        let b0 = self.data[o];
        let b1 = self.data[o + 1];
        let b2 = self.data[o + 2];
        let b3 = self.data[o + 3];
        *offset = o + 4;
        be32_of_exec(b0, b1, b2, b3)
    }
    /// Corresponds to `tpm_buf_length()`.
    pub fn len(&self) -> usize {
        self.length
    }
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }
    pub fn is_tpm2b(&self) -> bool {
        match self.kind {
            BufKind::Tpm2b => true,
            BufKind::Command => false,
        }
    }
    pub fn has_overflow(&self) -> bool {
        self.overflow
    }
    pub fn has_boundary_error(&self) -> bool {
        self.boundary_error
    }
    pub fn handle_count(&self) -> u8 {
        self.handles
    }
    /// The raw bytes to hand to the transport layer. **This is meaningful only when there is no
    /// overflow**, so it requires `!overflow`.
    pub fn as_wire(&self) -> &[u8] {
        &self.data[0..self.length]
    }
}
