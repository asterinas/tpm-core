//! 报文首部字段的类型封装。
//!
//! yufan：**当前只有 `buf` 用到 `TpmTag`,`TpmRc` 尚无调用方。** 拼装与解析各层
//! 直接对裸 `u16` / `u32` 操作,把标签和返回码的取值约束写在函数的前后置
//! 条件里,没有绕道这里。
//!
//! 留着是为了 `TpmRc` 那件事:返回码与命令码复用报文首部的同一个偏移,
//! 两者混用同一个裸 `u32` 时写反了不会被任何检查发现。真要收紧,应该是
//! 让各层改用这个 newtype,而不是反过来把它删掉。

/// TPM 报文首部的 tag 字段。
#[derive(Clone, Copy)]
pub enum TpmTag {
    /// `TPM_TAG_RQU_COMMAND` = 193（TPM 1.2 命令）
    RquCommand,
    /// `TPM2_ST_NO_SESSIONS` = 0x8001
    Tpm2NoSessions,
    /// `TPM2_ST_SESSIONS` = 0x8002
    Tpm2Sessions,
    /// 0 —— `tpm_buf_reset()` 显式允许（用于尚未定型的缓冲区）
    Null,
}
impl TpmTag {
    pub fn code(self) -> u16 {
        match self {
            TpmTag::RquCommand => 193u16,
            TpmTag::Tpm2NoSessions => 0x8001u16,
            TpmTag::Tpm2Sessions => 0x8002u16,
            TpmTag::Null => 0u16,
        }
    }
    /// 解析线上字节。
    pub fn from_code(c: u16) -> Option<TpmTag> {
        if c == 193u16 {
            Some(TpmTag::RquCommand)
        } else if c == 0x8001u16 {
            Some(TpmTag::Tpm2NoSessions)
        } else if c == 0x8002u16 {
            Some(TpmTag::Tpm2Sessions)
        } else if c == 0u16 {
            Some(TpmTag::Null)
        } else {
            None
        }
    }
}
/// TPM 返回码（首部第 3 个字段，与 ordinal 复用同一偏移）。
/// newtype 而非 enum：返回码空间开放（含厂商自定义），穷举不现实，
/// 但至少不再与 ordinal 混用同一个裸 `u32`。
#[derive(Clone, Copy)]
pub struct TpmRc(pub u32);
impl TpmRc {
    pub const SUCCESS: u32 = 0x0000_0000;
    /// `TPM_WARN_RETRY`
    pub const WARN_RETRY: u32 = 0x0000_0800;
    /// `TPM_WARN_DOING_SELFTEST`
    pub const WARN_DOING_SELFTEST: u32 = 0x0000_0802;
    /// `TPM_ERR_DEACTIVATED`
    pub const ERR_DEACTIVATED: u32 = 0x0000_0006;
    /// `TPM_ERR_DISABLED`
    pub const ERR_DISABLED: u32 = 0x0000_0007;
    /// `TPM_ERR_FAILEDSELFTEST`
    pub const ERR_FAILEDSELFTEST: u32 = 0x0000_001C;
    /// `TPM_ERR_INVALID_POSTINIT`
    pub const ERR_INVALID_POSTINIT: u32 = 38;
    pub fn is_success(self) -> bool {
        self.0 == 0u32
    }
}
/// `TPM_BUFSIZE`
pub const TPM_BUFSIZE: usize = 4096;
/// `TPM2_SPACE_BUFFER_SIZE`
pub const TPM2_SPACE_BUFFER_SIZE: usize = 16384;
/// `TPM_MAX_RNG_DATA`
pub const TPM_MAX_RNG_DATA: usize = 128;
/// `TPM_RETRY`
pub const TPM_RETRY: u32 = 50;
