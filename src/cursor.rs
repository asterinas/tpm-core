/// 整数 → 大端字节。与 `spec_be16_at` 互为逆运算。
pub(crate) fn be16_bytes(v: u16) -> [u8; 2] {
    v.to_be_bytes()
}
/// 整数 → 大端字节。与 `spec_be32_at` 互为逆运算。
pub(crate) fn be32_bytes(v: u32) -> [u8; 4] {
    v.to_be_bytes()
}
/// 只读解析游标。`pos` 私有，推进只能经由 `read_*`/`skip`，外部若需当前
/// 位置通过 [`Cursor::pos`] 读取。
pub struct Cursor {
    pos: usize,
}
impl Cursor {
    pub fn new() -> Cursor {
        Cursor { pos: 0 }
    }
    /// 当前解析位置。解析侧据此记录字段起点（如参数区、nonce 偏移）。
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
    /// 从指定偏移开始解析（用于跳过已由上层校验过的固定前缀）。
    pub fn at(pos: usize) -> Cursor {
        Cursor { pos }
    }
    pub fn remaining(&self, data: &[u8]) -> usize {
        data.len() - self.pos
    }
    /// 剩余字节是否恰好读完。用于"响应尾部不得有多余数据"这类检查。
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
    /// 借出接下来的 `n` 字节。这是变长字段（`TPM2B`、PCR 选择位图）
    /// 唯一的取用方式——长度来自报文本身，因此边界检查必须在这里发生。
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
    /// 跳过 `n` 字节。用于忽略当前阶段不关心但格式已知的字段。
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
/// 切片中是否存在非零字节。
///
/// PCR 分配解析要靠它判断某个 bank 是否真的被分配（选择位图全零即未分配）。
pub(crate) fn any_nonzero(s: &[u8]) -> bool {
    s.iter().any(|&b| b != 0)
}
