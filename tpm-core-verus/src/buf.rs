//! Fixed-size command buffer.
//!
//! yufan: **This type is currently not on the command assembly path.** Boot-phase commands are written by `boot` in place into
//! its own fixed scratch area, and authorized commands have their partitions described by `secure::CmdLayout`; neither
//! path goes through here. It is kept because the "write the payload first, then fill in the length" assembly style
//! will sooner or later be needed, not because there is an existing caller.
//!
//! Therefore, until a definite use is found for it, write new commands after the two paths above and do not use it as a template:
//! its error model is two sticky flags, `overflow` / `boundary_error`, collected at the end,
//! which is not the same as the other layers' practice of returning `Result` in place; byte order also goes through `endian`
//! rather than `cursor`. Two practices coexisting is already enough; there should not be a third.
use vstd::prelude::*;
use vstd::array::*;
use vstd::slice::*;

use crate::endian::*;
use crate::types::TpmTag;

verus! {

/// Size of `struct tpm_header`: tag(2) + length(4) + ordinal/return_code(4).
pub const TPM_HEADER_SIZE: usize = 10;

/// TPM2B header: just one 16-bit size field.
pub const TPM2B_HEADER_SIZE: usize = 2;

// ===========================================================================
// Ring B: storage acquisition (the only external_body)
// ===========================================================================

/// The kernel glue layer should reimplement it as a page allocation and **Box it**, to keep 4 KiB off the kernel stack;
/// the default implementation here is used only for host-side differential testing.
#[verifier::external_body]
fn alloc_zeroed_storage<const N: usize>() -> (r: [u8; N])
    ensures
        r@.len() == N,
        forall|i: int| 0 <= i < N ==> r@[i] == 0u8,
{
    [0u8; N]
}

// ===========================================================================
// Buffer
// ===========================================================================

/// It differs from `overflow`/`boundary_error` in that the kind is fixed at construction and never changes afterwards.
#[derive(Clone, Copy)]
pub enum BufKind {
    /// Ordinary command buffer, header is `struct tpm_header`
    Command,
    /// TPM2B buffer, header is a 2-byte size
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
    // -----------------------------------------------------------------
    // Spec layer
    // -----------------------------------------------------------------

    pub closed spec fn spec_is_tpm2b(self) -> bool {
        match self.kind {
            BufKind::Tpm2b => true,
            BufKind::Command => false,
        }
    }

    /// Header length: 2 for TPM2B, 10 for a command.
    pub open spec fn hdr_len(self) -> int {
        if self.spec_is_tpm2b() {
            TPM2B_HEADER_SIZE as int
        } else {
            TPM_HEADER_SIZE as int
        }
    }

    /// The total length **encoded in the buffer's own bytes**.
    /// Note that the TPM2B size field does not include its own 2 bytes, hence `+2`.
    pub open spec fn encoded_len(self) -> int {
        if self.spec_is_tpm2b() {
            be16_of(self.data@[0], self.data@[1]) as int + 2
        } else {
            be32_of(self.data@[2], self.data@[3], self.data@[4], self.data@[5]) as int
        }
    }

    /// Core invariant.
    pub open spec fn wf(self) -> bool {
        &&& self.data@.len() == N
        &&& self.hdr_len() <= N as int
        &&& N as int <= 0xffff
        &&& self.hdr_len() <= self.length as int
        &&& self.length as int <= N as int
        &&& self.encoded_len() == self.length as int
    }

    /// The payload after the header.
    pub open spec fn payload(self) -> Seq<u8> {
        self.data@.subrange(self.hdr_len(), self.length as int)
    }

    /// The on-wire byte sequence that is actually handed to the hardware.
    pub open spec fn wire(self) -> Seq<u8> {
        self.data@.subrange(0, self.length as int)
    }

    pub open spec fn spec_len(self) -> int {
        self.length as int
    }

    pub open spec fn spec_overflow(self) -> bool {
        self.overflow
    }

    pub open spec fn spec_boundary_error(self) -> bool {
        self.boundary_error
    }

    pub open spec fn spec_handles(self) -> int {
        self.handles as int
    }

    /// "Content entirely unchanged" -- used to express no-ops and read-only operations.
    pub open spec fn content_eq(self, other: TpmBuf<N>) -> bool {
        &&& self.data@ =~= other.data@
        &&& self.length == other.length
        &&& self.spec_is_tpm2b() == other.spec_is_tpm2b()
        &&& self.handles == other.handles
    }

    /// Whether `count` bytes can safely be read starting at `offset`.
    pub open spec fn can_read(self, offset: int, count: int) -> bool {
        &&& !self.boundary_error
        &&& 0 <= offset
        &&& offset + count <= self.length as int
    }

    // -----------------------------------------------------------------
    // Internal: fixed-position writes
    // -----------------------------------------------------------------

    fn put_be16(&mut self, at: usize, v: u16)
        requires
            old(self).data@.len() == N,
            at + 2 <= N,
        ensures
            final(self).data@.len() == N,
            final(self).data@[at as int] == be16_byte(v, 0),
            final(self).data@[at as int + 1] == be16_byte(v, 1),
            forall|i: int|
                0 <= i < N && !(at <= i < at + 2) ==> final(self).data@[i] == old(self).data@[i],
            final(self).length == old(self).length,
            final(self).kind == old(self).kind,
            final(self).overflow == old(self).overflow,
            final(self).boundary_error == old(self).boundary_error,
            final(self).handles == old(self).handles,
    {
        self.data[at] = ((v >> 8) & 0xff) as u8;
        self.data[at + 1] = (v & 0xff) as u8;
    }

    fn put_be32(&mut self, at: usize, v: u32)
        requires
            old(self).data@.len() == N,
            at + 4 <= N,
        ensures
            final(self).data@.len() == N,
            final(self).data@[at as int] == be32_byte(v, 0),
            final(self).data@[at as int + 1] == be32_byte(v, 1),
            final(self).data@[at as int + 2] == be32_byte(v, 2),
            final(self).data@[at as int + 3] == be32_byte(v, 3),
            forall|i: int|
                0 <= i < N && !(at <= i < at + 4) ==> final(self).data@[i] == old(self).data@[i],
            final(self).length == old(self).length,
            final(self).kind == old(self).kind,
            final(self).overflow == old(self).overflow,
            final(self).boundary_error == old(self).boundary_error,
            final(self).handles == old(self).handles,
    {
        self.data[at] = ((v >> 24) & 0xff) as u8;
        self.data[at + 1] = ((v >> 16) & 0xff) as u8;
        self.data[at + 2] = ((v >> 8) & 0xff) as u8;
        self.data[at + 3] = (v & 0xff) as u8;
    }

    /// Write `self.length` back into the header's length field.
    fn sync_length(&mut self)
        requires
            old(self).data@.len() == N,
            old(self).hdr_len() <= N as int,
            N as int <= 0xffff,
            old(self).hdr_len() <= old(self).length as int,
            old(self).length as int <= N as int,
        ensures
            final(self).wf(),
            final(self).length == old(self).length,
            final(self).kind == old(self).kind,
            final(self).overflow == old(self).overflow,
            final(self).boundary_error == old(self).boundary_error,
            final(self).handles == old(self).handles,
            forall|i: int|
                old(self).hdr_len() <= i < N ==> final(self).data@[i] == old(self).data@[i],
    {
        match self.kind {
            BufKind::Tpm2b => {
                // length >= 2 is guaranteed by the precondition, so the subtraction cannot underflow;
                // length <= N <= 0xffff, so the cast to u16 does not truncate.
                let sz: u16 = (self.length - TPM2B_HEADER_SIZE) as u16;
                self.put_be16(0, sz);
                proof {
                    lemma_be16_roundtrip(sz);
                }
            },
            BufKind::Command => {
                let l: u32 = self.length as u32;
                self.put_be32(2, l);
                proof {
                    lemma_be32_roundtrip(l);
                }
            },
        }
    }

    // -----------------------------------------------------------------
    // Construction and reset
    // -----------------------------------------------------------------

    /// Corresponds to `tpm_buf_reset()`: initialize a command in place on existing storage.
    pub fn reset_command(&mut self, tag: TpmTag, ordinal: u32)
        requires
            old(self).data@.len() == N,
            TPM_HEADER_SIZE <= N,
            N as int <= 0xffff,
        ensures
            final(self).wf(),
            !final(self).spec_is_tpm2b(),
            final(self).length == TPM_HEADER_SIZE,
            final(self).payload() =~= Seq::<u8>::empty(),
            !final(self).overflow,
            !final(self).boundary_error,
            final(self).handles == 0,
            be16_of(final(self).data@[0], final(self).data@[1]) == tag.spec_code(),
            be32_of(
                final(self).data@[6],
                final(self).data@[7],
                final(self).data@[8],
                final(self).data@[9],
            ) == ordinal,
    {
        self.kind = BufKind::Command;
        self.overflow = false;
        self.boundary_error = false;
        self.handles = 0;
        self.length = TPM_HEADER_SIZE;

        let t = tag.code();
        self.put_be16(0, t);
        self.put_be32(2, TPM_HEADER_SIZE as u32);
        self.put_be32(6, ordinal);

        proof {
            lemma_be16_roundtrip(t);
            lemma_be32_roundtrip(TPM_HEADER_SIZE as u32);
            lemma_be32_roundtrip(ordinal);
        }
    }

    /// Corresponds to `tpm_buf_reset_sized()`.
    pub fn reset_sized(&mut self)
        requires
            old(self).data@.len() == N,
            TPM2B_HEADER_SIZE <= N,
            N as int <= 0xffff,
        ensures
            final(self).wf(),
            final(self).spec_is_tpm2b(),
            final(self).length == TPM2B_HEADER_SIZE,
            final(self).payload() =~= Seq::<u8>::empty(),
            !final(self).overflow,
            !final(self).boundary_error,
            final(self).handles == 0,
    {
        self.kind = BufKind::Tpm2b;
        self.overflow = false;
        self.boundary_error = false;
        self.handles = 0;
        self.length = TPM2B_HEADER_SIZE;

        self.put_be16(0, 0u16);
        proof {
            lemma_be16_roundtrip(0u16);
        }
    }

    /// Corresponds to `tpm_buf_init()`: allocate + initialize.
    pub fn new_command(tag: TpmTag, ordinal: u32) -> (r: Self)
        requires
            TPM_HEADER_SIZE <= N,
            N as int <= 0xffff,
        ensures
            r.wf(),
            !r.spec_is_tpm2b(),
            r.length == TPM_HEADER_SIZE,
            r.payload() =~= Seq::<u8>::empty(),
            !r.overflow,
            !r.boundary_error,
            r.handles == 0,
    {
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
    pub fn new_sized() -> (r: Self)
        requires
            TPM2B_HEADER_SIZE <= N,
            N as int <= 0xffff,
        ensures
            r.wf(),
            r.spec_is_tpm2b(),
            r.length == TPM2B_HEADER_SIZE,
            r.payload() =~= Seq::<u8>::empty(),
            !r.overflow,
            !r.boundary_error,
            r.handles == 0,
    {
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

    // `tpm_buf_destroy()` has no counterpart: ownership and Drop handle it automatically.

    // -----------------------------------------------------------------
    // Writing
    // -----------------------------------------------------------------

    /// Corresponds to `tpm_buf_append()`.
    pub fn append(&mut self, src: &[u8])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).spec_is_tpm2b() == old(self).spec_is_tpm2b(),
            final(self).boundary_error == old(self).boundary_error,
            final(self).handles == old(self).handles,
            // (1) Already overflowed: complete no-op
            old(self).overflow ==> (final(self).overflow && final(self).content_eq(*old(self))),
            // (2) Fits: content is appended, length field synchronized
            (!old(self).overflow && src@.len() + old(self).length as int <= N as int) ==> (
                !final(self).overflow
                && final(self).length as int == old(self).length as int + src@.len()
                && final(self).payload() =~= old(self).payload() + src@
            ),
            // (3) Does not fit: set the flag, change not a single byte
            (!old(self).overflow && src@.len() + old(self).length as int > N as int) ==> (
                final(self).overflow && final(self).content_eq(*old(self))
            ),
    {
        if self.overflow {
            return;
        }
        let avail: usize = N - self.length;
        if src.len() > avail {
            self.overflow = true;
            return;
        }

        let start: usize = self.length;
        let ghost old_data = self.data@;
        let ghost n_src = src@.len();

        for i in 0..src.len()
            invariant
                src@.len() == n_src,
                start == old(self).length,
                start as int + n_src <= N as int,
                self.data@.len() == N,
                self.length == start,
                self.kind == old(self).kind,
                self.overflow == false,
                self.boundary_error == old(self).boundary_error,
                self.handles == old(self).handles,
                old_data =~= old(self).data@,
                forall|j: int| 0 <= j < i ==> self.data@[start + j] == src@[j],
                forall|j: int| #![auto]
                    0 <= j < N && !(start <= j < start + n_src) ==> self.data@[j] == old_data[j],
        {
            let b: u8 = src[i];
            self.data[start + i] = b;
        }

        self.length = start + src.len();
        self.sync_length();

        proof {
            // The payload starts at hdr_len, sync_length touches only [0, hdr_len),
            // the loop touches only [start, start + n_src); the two ranges do not overlap.
            assert(self.payload() =~= old(self).payload() + src@);
        }
    }

    pub fn append_u8(&mut self, v: u8)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).spec_is_tpm2b() == old(self).spec_is_tpm2b(),
            final(self).boundary_error == old(self).boundary_error,
            final(self).handles == old(self).handles,
            old(self).overflow ==> (final(self).overflow && final(self).content_eq(*old(self))),
            (!old(self).overflow && old(self).length as int + 1 <= N as int) ==> (
                !final(self).overflow
                && final(self).length as int == old(self).length as int + 1
                && final(self).payload() =~= old(self).payload().push(v)
            ),
            (!old(self).overflow && old(self).length as int + 1 > N as int) ==> (
                final(self).overflow && final(self).content_eq(*old(self))
            ),
    {
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
        proof {
            assert(self.payload() =~= old(self).payload().push(v));
        }
    }

    pub fn append_u16(&mut self, v: u16)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).spec_is_tpm2b() == old(self).spec_is_tpm2b(),
            final(self).boundary_error == old(self).boundary_error,
            final(self).handles == old(self).handles,
            old(self).overflow ==> (final(self).overflow && final(self).content_eq(*old(self))),
            (!old(self).overflow && old(self).length as int + 2 <= N as int) ==> (
                !final(self).overflow
                && final(self).length as int == old(self).length as int + 2
                && final(self).payload() =~= old(self).payload() + be16_bytes(v)
            ),
            (!old(self).overflow && old(self).length as int + 2 > N as int) ==> (
                final(self).overflow && final(self).content_eq(*old(self))
            ),
    {
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
        proof {
            assert(self.payload() =~= old(self).payload() + be16_bytes(v));
        }
    }

    pub fn append_u32(&mut self, v: u32)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).spec_is_tpm2b() == old(self).spec_is_tpm2b(),
            final(self).boundary_error == old(self).boundary_error,
            final(self).handles == old(self).handles,
            old(self).overflow ==> (final(self).overflow && final(self).content_eq(*old(self))),
            (!old(self).overflow && old(self).length as int + 4 <= N as int) ==> (
                !final(self).overflow
                && final(self).length as int == old(self).length as int + 4
                && final(self).payload() =~= old(self).payload() + be32_bytes(v)
            ),
            (!old(self).overflow && old(self).length as int + 4 > N as int) ==> (
                final(self).overflow && final(self).content_eq(*old(self))
            ),
    {
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
        proof {
            assert(self.payload() =~= old(self).payload() + be32_bytes(v));
        }
    }

    /// Corresponds to `tpm_buf_append_handle()`.
    pub fn append_handle(&mut self, handle: u32) -> (r: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).spec_is_tpm2b() == old(self).spec_is_tpm2b(),
            final(self).boundary_error == old(self).boundary_error,
            r ==> (
                !final(self).spec_is_tpm2b()
                && !final(self).overflow
                && final(self).handles == old(self).handles + 1
                && final(self).length as int == old(self).length as int + 4
                && final(self).payload() =~= old(self).payload() + be32_bytes(handle)
            ),
            !r ==> final(self).handles == old(self).handles,
    {
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

    // -----------------------------------------------------------------
    // Reading
    // -----------------------------------------------------------------

    /// Corresponds to `tpm_buf_read_u8()`.
    pub fn read_u8(&mut self, offset: &mut usize) -> (r: u8)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).content_eq(*old(self)),
            final(self).overflow == old(self).overflow,
            old(self).can_read(*old(offset) as int, 1) ==> (
                !final(self).boundary_error
                && *final(offset) == *old(offset) + 1
                && r == final(self).data@[*old(offset) as int]
            ),
            !old(self).can_read(*old(offset) as int, 1) ==> (
                final(self).boundary_error && *final(offset) == *old(offset) && r == 0
            ),
    {
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
    pub fn read_u16(&mut self, offset: &mut usize) -> (r: u16)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).content_eq(*old(self)),
            final(self).overflow == old(self).overflow,
            old(self).can_read(*old(offset) as int, 2) ==> (
                !final(self).boundary_error
                && *final(offset) == *old(offset) + 2
                && r == be16_of(
                    final(self).data@[*old(offset) as int],
                    final(self).data@[*old(offset) as int + 1],
                )
            ),
            !old(self).can_read(*old(offset) as int, 2) ==> (
                final(self).boundary_error && *final(offset) == *old(offset) && r == 0
            ),
    {
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
    pub fn read_u32(&mut self, offset: &mut usize) -> (r: u32)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).content_eq(*old(self)),
            final(self).overflow == old(self).overflow,
            old(self).can_read(*old(offset) as int, 4) ==> (
                !final(self).boundary_error
                && *final(offset) == *old(offset) + 4
                && r == be32_of(
                    final(self).data@[*old(offset) as int],
                    final(self).data@[*old(offset) as int + 1],
                    final(self).data@[*old(offset) as int + 2],
                    final(self).data@[*old(offset) as int + 3],
                )
            ),
            !old(self).can_read(*old(offset) as int, 4) ==> (
                final(self).boundary_error && *final(offset) == *old(offset) && r == 0
            ),
    {
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

    // -----------------------------------------------------------------
    // Accessors (`&self`, no old/final distinction)
    // -----------------------------------------------------------------

    /// Corresponds to `tpm_buf_length()`.
    pub fn len(&self) -> (r: usize)
        ensures
            r as int == self.spec_len(),
    {
        self.length
    }

    pub fn is_empty(&self) -> (r: bool)
        ensures
            r == (self.spec_len() == 0),
    {
        self.length == 0
    }

    pub fn is_tpm2b(&self) -> (r: bool)
        ensures
            r == self.spec_is_tpm2b(),
    {
        match self.kind {
            BufKind::Tpm2b => true,
            BufKind::Command => false,
        }
    }

    pub fn has_overflow(&self) -> (r: bool)
        ensures
            r == self.spec_overflow(),
    {
        self.overflow
    }

    pub fn has_boundary_error(&self) -> (r: bool)
        ensures
            r == self.spec_boundary_error(),
    {
        self.boundary_error
    }

    pub fn handle_count(&self) -> (r: u8)
        ensures
            r as int == self.spec_handles(),
    {
        self.handles
    }

    /// The on-wire bytes handed to the transport layer. **Meaningful only when there is no overflow**, hence `!overflow` is required.
    pub fn as_wire(&self) -> (r: &[u8])
        requires
            self.wf(),
            !self.spec_overflow(),
        ensures
            r@ =~= self.wire(),
            r@.len() == self.spec_len(),
    {
        &self.data[0..self.length]
    }
}

} // verus!