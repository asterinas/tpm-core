use crate::{crypto::SHA256_LEN, cursor::*};

pub(crate) const CC_SELF_TEST: u32 = 0x0000_0143;
pub(crate) const CC_STARTUP: u32 = 0x0000_0144;
pub(crate) const CC_SHUTDOWN: u32 = 0x0000_0145;
pub(crate) const CC_CONTEXT_LOAD: u32 = 0x0000_0161;
pub(crate) const CC_CONTEXT_SAVE: u32 = 0x0000_0162;
pub(crate) const CC_FLUSH_CONTEXT: u32 = 0x0000_0165;
pub const CC_GET_CAPABILITY: u32 = 0x0000_017A;
pub(crate) const CC_GET_RANDOM: u32 = 0x0000_017B;
pub(crate) const CC_PCR_READ: u32 = 0x0000_017E;
pub(crate) const CC_PCR_EXTEND: u32 = 0x0000_0182;
pub const CAP_HANDLES: u32 = 0x0000_0001;
pub const CAP_COMMANDS: u32 = 0x0000_0002;
pub const CAP_PCRS: u32 = 0x0000_0005;
pub(crate) const CAP_TPM_PROPERTIES: u32 = 0x0000_0006;
pub const SU_CLEAR: u16 = 0x0000;
pub const SU_STATE: u16 = 0x0001;
/// PC Client 平台固定 24 个 PCR（TCG PC Client PFP）。
pub const PLATFORM_PCR: u32 = 24;
/// 覆盖 24 个 PCR 所需的选择位图字节数：ceil(24 / 8)。
const PCR_SELECT_MIN: usize = 3;
/// 单次取随机数的上限。超过这个量要分多次取。
pub const MAX_RNG_DATA: u16 = 128;
fn bit_value(n: u32) -> u8 {
    if n == 0 {
        1
    } else if n == 1 {
        2
    } else if n == 2 {
        4
    } else if n == 3 {
        8
    } else if n == 4 {
        16
    } else if n == 5 {
        32
    } else if n == 6 {
        64
    } else {
        128
    }
}
/// 生成只选中单个 PCR 的选择位图。
///
/// 索引拆分用除法与取余而非移位与掩码：两者在 24 以内完全等价，
/// 而除法形式可以直接进入整数推理，不必切换到位向量求解器。
fn pcr_select_bitmap(pcr_idx: u32) -> [u8; PCR_SELECT_MIN] {
    let byte_idx = pcr_idx / 8;
    let mask = bit_value(pcr_idx % 8);
    if byte_idx == 0 {
        [mask, 0, 0]
    } else if byte_idx == 1 {
        [0, mask, 0]
    } else {
        [0, 0, mask]
    }
}
/// PCR 的句柄值。
///
/// PCR 的句柄类型编号为 0，因此句柄值就是 PCR 序号本身。单独成函数不是
/// 为了那句 `r == pcr_idx`，而是为了带上这条注释：这一类句柄的「名字」
/// 即句柄自身的四个字节，算命令摘要时不需要再去查任何名字表——写摘要
/// 输入的那一处很容易在这里多绕一圈，绕错了不会被任何长度检查发现。
pub fn pcr_handle(pcr_idx: u32) -> u32 {
    pcr_idx
}
/// `TPM2_PCR_Read` 载荷（Part 3 §22.4）。
///
/// ```text
/// count        u32 = 1        只问一个 bank
/// hashAlg      u16            摘要算法
/// sizeofSelect u8  = 3
/// pcrSelect    u8[3]
/// ```
pub fn pcr_read_payload(alg_id: u16, pcr_idx: u32) -> [u8; 10] {
    let cnt = be32_bytes(1);
    let alg = be16_bytes(alg_id);
    let sel = pcr_select_bitmap(pcr_idx);
    [
        cnt[0],
        cnt[1],
        cnt[2],
        cnt[3],
        alg[0],
        alg[1],
        PCR_SELECT_MIN as u8,
        sel[0],
        sel[1],
        sel[2],
    ]
}
/// `TPM2_PCR_Extend` 的参数区长度：count(4) + hashAlg(2) + digest(32)。
const PCR_EXTEND_PARAM_LEN: usize = 6 + SHA256_LEN;
/// `TPM2_PCR_Extend` 的**参数区**（Part 3 §22.2）。
///
/// ```text
/// count    u32 = 1        只写一个 bank
/// hashAlg  u16
/// digest   u8[32]
/// ```
///
/// 这条命令与只读那条的形态不同，值得说清楚：它带一个句柄、且必须授权，
/// 于是整条报文是
///
/// ```text
/// 报文头 10 | pcrHandle 4 | authSize 4 | 授权区 | 参数区
/// ```
///
/// 本函数只产出最后那一段。句柄不放进来是刻意的：句柄位于授权区**之前**，
/// 而命令摘要覆盖的是授权区**之后**那一段。两者若混在同一个数组里，拼装方
/// 迟早会把整块当作参数区喂给摘要——那种错误不触发任何长度检查，症状只是
/// 校验恒不通过，排查起来要一路回溯到偏移的定义。
///
/// 算法标识做成入参而不是写死的常量，是为了让前置条件把它和摘要长度绑在
/// 一起：这里收的是定长 32 字节，声称成别的算法就是在报文里说了谎。想支持
/// 第二种算法，摘要参数的类型必须同时改，改不动一半。
pub fn pcr_extend_payload(alg_id: u16, digest: &[u8; SHA256_LEN]) -> [u8; PCR_EXTEND_PARAM_LEN] {
    let cnt = be32_bytes(1);
    let alg = be16_bytes(alg_id);
    let mut out = [0u8; PCR_EXTEND_PARAM_LEN];
    out[0] = cnt[0];
    out[1] = cnt[1];
    out[2] = cnt[2];
    out[3] = cnt[3];
    out[4] = alg[0];
    out[5] = alg[1];
    out[6..6 + SHA256_LEN].copy_from_slice(digest);
    out
}
/// `TPM2_GetCapability` 载荷（Part 3 §30.2）。
///
/// ```text
/// capability     u32
/// property       u32
/// propertyCount  u32
/// ```
pub fn get_capability_payload(capability: u32, property: u32, count: u32) -> [u8; 12] {
    let a = be32_bytes(capability);
    let b = be32_bytes(property);
    let c = be32_bytes(count);
    [
        a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3], c[0], c[1], c[2], c[3],
    ]
}
/// `TPM2_GetRandom` 载荷（Part 3 §16.1）。
///
/// 上限在类型层面挡住：一次要不到超过 `MAX_RNG_DATA` 的量，
/// 调用方必须自己分批，而不是指望对端截断。
pub fn get_random_payload(bytes_requested: u16) -> [u8; 2] {
    be16_bytes(bytes_requested)
}
/// `TPM2_Shutdown` 载荷（Part 3 §9.4）。
pub fn shutdown_payload(shutdown_type: u16) -> [u8; 2] {
    be16_bytes(shutdown_type)
}
/// `TPM2_FlushContext` 载荷（Part 3 §28.4）。句柄在头部之后、无授权区。
pub fn flush_context_payload(handle: u32) -> [u8; 4] {
    be32_bytes(handle)
}
