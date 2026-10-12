//! 定长命令缓冲区。
//!
//! yufan：**本类型当前不在命令拼装路径上。** 引导阶段的命令由 `boot` 就地写进
//! 自己的定长暂存区,带授权的命令由 `secure::CmdLayout` 描述分区,两条路
//! 都不经过这里。它保留下来是因为「先写载荷、再回填长度」这种拼装方式
//! 迟早会有需要,而不是因为有现成的调用方。
//!
//! 因此在给它找到确定用途之前,新命令请照着上述两条路写,不要以它为样板:
//! 它的错误模型是 `overflow` / `boundary_error` 两个粘滞标志、末尾统一收,
//! 与其余各层就地返回 `Result` 的做法不是一回事;字节序也走 `endian`
//! 而非 `cursor`。两种做法并存已经够了,不宜再多一处。

use crate::{endian::*, types::TpmTag};

/// `struct tpm_header` 的大小：tag(2) + length(4) + ordinal/return_code(4)。
pub const TPM_HEADER_SIZE: usize = 10;
/// TPM2B 首部：仅一个 16 位 size 字段。
pub const TPM2B_HEADER_SIZE: usize = 2;
/// 内核胶水层应把它重新实现为页分配并 **Box 化**，避免 4 KiB 落在内核栈上；
/// 这里的默认实现只用于 host 侧差分测试。
fn alloc_zeroed_storage<const N: usize>() -> [u8; N] {
    [0u8; N]
}
/// 它与 `overflow`/`boundary_error` 的区别在于：种类在构造时确定、此后不变，
#[derive(Clone, Copy)]
pub enum BufKind {
    /// 普通命令缓冲区，首部为 `struct tpm_header`
    Command,
    /// TPM2B 缓冲区，首部为 2 字节 size
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
    /// 把 `self.length` 回写进首部的长度字段。
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
    /// 对应 `tpm_buf_reset()`：在既有存储上原地初始化一条命令。
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
    /// 对应 `tpm_buf_reset_sized()`。
    pub fn reset_sized(&mut self) {
        self.kind = BufKind::Tpm2b;
        self.overflow = false;
        self.boundary_error = false;
        self.handles = 0;
        self.length = TPM2B_HEADER_SIZE;
        self.put_be16(0, 0u16);
    }
    /// 对应 `tpm_buf_init()`：分配 + 初始化。
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
    /// 对应 `tpm_buf_init_sized()`。
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
    /// 对应 `tpm_buf_append()`。
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
    /// 对应 `tpm_buf_append_handle()`。
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
    /// 对应 `tpm_buf_read_u8()`。
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
    /// 对应 `tpm_buf_read_u16()`。
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
    /// 对应 `tpm_buf_read_u32()`。
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
    /// 对应 `tpm_buf_length()`。
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
    /// 交给传输层的线上字节。**没有溢出时才有意义**，故要求 `!overflow`。
    pub fn as_wire(&self) -> &[u8] {
        &self.data[0..self.length]
    }
}
