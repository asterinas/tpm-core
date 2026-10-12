use crate::cursor::*;

pub(crate) const TPM_HEADER_LEN: usize = 10;
/// 无会话响应标签。
pub(crate) const ST_NO_SESSIONS: u16 = 0x8001;
/// 带会话（授权区）响应标签。
pub const ST_SESSIONS: u16 = 0x8002;
/// 成功返回码。
pub const RC_SUCCESS: u32 = 0x0000;
#[derive(PartialEq, Eq)]
pub enum ParseError {
    /// 字节数不足以取出下一个字段。
    Truncated,
    /// 长度字段与实际字节数不符，或字段取值超出规范允许范围。
    Malformed,
    /// 计数超出本实现的静态容量上限。
    Capacity,
    /// 语法合法但本实现不支持（未知算法、未预期的响应形态）。
    Unsupported,
    /// TPM 报告了非零返回码。
    TpmError(u32),
}
/// 报文头的抽象视图。`code` 在请求方向是命令码，在响应方向是返回码。
pub struct HeaderView {
    pub tag: u16,
    pub size: u32,
    pub code: u32,
}
/// 已校验的响应：头部三字段 + 去掉头部的载荷。
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
/// 校验并拆解一条响应。
///
/// 拒绝三类输入：长度不足一个头部、`size` 字段与实到字节数不符、
/// 标签不是两个合法响应标签之一。返回码非零时不再往下解析载荷——
/// 失败响应的载荷内容按规范是未定义的。
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
/// 请求头的字节形态。命令载荷由 `cmd` 模块构造，两者拼接即整条请求。
///
/// `size` 需要在载荷长度确定后回填，因此这里只提供"给定总长度生成
/// 头部"的纯函数，由缓冲区层在收尾时调用。
pub(crate) fn build_header(tag: u16, code: u32, total_size: u32) -> [u8; 10] {
    let t = be16_bytes(tag);
    let s = be32_bytes(total_size);
    let c = be32_bytes(code);
    [t[0], t[1], s[0], s[1], s[2], s[3], c[0], c[1], c[2], c[3]]
}
