use crate::{cursor::*, msg::ParseError};

/// 同时可分配的 PCR bank 数上界。
const MAX_PCR_BANKS: usize = 5;
/// 可接受的 `sizeofSelect` 上界。PC Client 平台固定 24 个 PCR（3 字节），
/// 这里留出余量，但绝不接受对端给出的任意长度。
const PCR_SELECT_MAX: usize = 8;
/// 摘要长度上界（SHA-512）。
const MAX_DIGEST_SIZE: usize = 64;
const ALG_SHA1: u16 = 0x0004;
const ALG_SHA256: u16 = 0x000B;
const ALG_SHA384: u16 = 0x000C;
const ALG_SHA512: u16 = 0x000D;
const ALG_SM3_256: u16 = 0x0012;
/// 已知算法的摘要长度。
///
/// 返回 `0` 表示"本实现不认识这个算法"——不是错误，只是长度需要另行
/// 探测（读一次 PCR 0 即可）。把未知算法当成错误会让驱动在启用了新
/// 摘要算法的设备上直接拒绝工作，代价过大。
fn digest_size_of(alg_id: u16) -> u16 {
    if alg_id == ALG_SHA1 {
        20
    } else if alg_id == ALG_SHA256 {
        32
    } else if alg_id == ALG_SHA384 {
        48
    } else if alg_id == ALG_SHA512 {
        64
    } else if alg_id == ALG_SM3_256 {
        32
    } else {
        0
    }
}
/// 解析 `TPM2_GetCapability(TPM_CAP_TPM_PROPERTIES)` 的返回值。
///
/// 载荷布局（Part 3 §30.2）：
///
/// ```text
/// moreData      u8
/// capability    u32
/// count         u32
/// [property u32, value u32] * count
/// ```
///
/// 计数为零是合法响应（对端处于固件升级模式时会这样答），但调用方拿
/// 不到值，所以按"无数据"报错而不是返回一个凭空捏造的零。
pub(crate) fn parse_tpm_property(body: &[u8]) -> Result<u32, ParseError> {
    let mut c = Cursor::new();
    c.read_u8(body).ok_or(ParseError::Truncated)?;
    c.read_be32(body).ok_or(ParseError::Truncated)?;
    let count = c.read_be32(body).ok_or(ParseError::Truncated)?;
    if count == 0 {
        return Err(ParseError::Unsupported);
    }
    c.read_be32(body).ok_or(ParseError::Truncated)?;
    c.read_be32(body).ok_or(ParseError::Truncated)
}
/// 已分配的 PCR bank 表。
///
/// `digest_sizes[i] == 0` 表示该 bank 的算法本实现不认识，长度待探测。
pub struct PcrBanks {
    pub algs: [u16; 5],
    pub digest_sizes: [u16; 5],
    pub count: usize,
}
impl PcrBanks {
    pub fn empty() -> PcrBanks {
        PcrBanks {
            algs: [0, 0, 0, 0, 0],
            digest_sizes: [0, 0, 0, 0, 0],
            count: 0,
        }
    }
}
/// 解析 `TPM2_GetCapability(TPM_CAP_PCRS)`，得出实际分配了哪些 bank。
///
/// 载荷布局：
///
/// ```text
/// moreData   u8
/// capability u32          == TPM_CAP_PCRS
/// count      u32          候选 bank 数
/// [hashAlg u16, sizeofSelect u8, pcrSelect u8[sizeofSelect]] * count
/// ```
///
/// 一个 bank 只有在选择位图存在非零位时才算已分配；位图全零表示该算法
/// 只是被支持、并未启用。
///
/// 三处上界是这个函数的全部安全论据：`count <= MAX_PCR_BANKS` 限住循环
/// 轮数，`sizeofSelect <= PCR_SELECT_MAX` 限住每轮步长，游标的
/// `read_bytes` 限住位图取值——三者都在使用之前完成检查。
pub fn parse_pcr_allocation(body: &[u8]) -> Result<PcrBanks, ParseError> {
    let mut c = Cursor::new();
    c.read_u8(body).ok_or(ParseError::Truncated)?;
    c.read_be32(body).ok_or(ParseError::Truncated)?;
    let count = c.read_be32(body).ok_or(ParseError::Truncated)?;
    if count > MAX_PCR_BANKS as u32 {
        return Err(ParseError::Capacity);
    }
    let mut banks = PcrBanks::empty();
    for _ in 0..count {
        let alg_id = c.read_be16(body).ok_or(ParseError::Truncated)?;
        let sel_size = c.read_u8(body).ok_or(ParseError::Truncated)?;
        if sel_size as usize > PCR_SELECT_MAX {
            return Err(ParseError::Malformed);
        }
        let select = c
            .read_bytes(body, sel_size as usize)
            .ok_or(ParseError::Truncated)?;
        if any_nonzero(select) {
            banks.algs[banks.count] = alg_id;
            banks.digest_sizes[banks.count] = digest_size_of(alg_id);
            banks.count += 1;
        }
    }
    Ok(banks)
}
/// 一次 PCR 读取的结果：算法标识 + 摘要字节。
pub struct PcrValue<'a> {
    pub alg_id: u16,
    pub digest: &'a [u8],
}
/// 解析 `TPM2_PCR_Read` 响应（Part 3 §22.4）。
///
/// 载荷布局：
///
/// ```text
/// pcrUpdateCounter u32
/// pcrSelectionOut  count u32, [hashAlg u16, sizeofSelect u8, pcrSelect[]] * count
/// pcrValues        count u32, [size u16, buffer[size]] * count
/// ```
///
/// 只接受"一个选择、一个摘要"的形态——这正是命令侧构造的请求所对应的
/// 响应。对端多答的部分不去猜测其含义，直接拒绝。
pub fn parse_pcr_read(body: &[u8]) -> Result<PcrValue<'_>, ParseError> {
    let mut c = Cursor::new();
    c.read_be32(body).ok_or(ParseError::Truncated)?;
    let sel_count = c.read_be32(body).ok_or(ParseError::Truncated)?;
    if sel_count != 1 {
        return Err(ParseError::Unsupported);
    }
    let alg_id = c.read_be16(body).ok_or(ParseError::Truncated)?;
    let sel_size = c.read_u8(body).ok_or(ParseError::Truncated)?;
    if sel_size as usize > PCR_SELECT_MAX {
        return Err(ParseError::Malformed);
    }
    if !c.skip(body, sel_size as usize) {
        return Err(ParseError::Truncated);
    }
    let digest_count = c.read_be32(body).ok_or(ParseError::Truncated)?;
    if digest_count != 1 {
        return Err(ParseError::Unsupported);
    }
    let digest_size = c.read_be16(body).ok_or(ParseError::Truncated)?;
    if digest_size as usize > MAX_DIGEST_SIZE {
        return Err(ParseError::Malformed);
    }
    let digest = c
        .read_bytes(body, digest_size as usize)
        .ok_or(ParseError::Truncated)?;
    Ok(PcrValue { alg_id, digest })
}
/// 解析 `TPM2_GetRandom` 响应（Part 3 §16.1）：一个 `TPM2B_DIGEST`。
///
/// 返回借用而非拷贝。要多少字节由调用方按 `max` 自行裁剪，本层只保证
/// 返回的切片确实落在载荷内、且长度不超过对端声明的值。
pub fn parse_random(body: &[u8], max: u16) -> Result<&[u8], ParseError> {
    let mut c = Cursor::new();
    let size = c.read_be16(body).ok_or(ParseError::Truncated)?;
    if size > max {
        return Err(ParseError::Malformed);
    }
    c.read_bytes(body, size as usize)
        .ok_or(ParseError::Truncated)
}
