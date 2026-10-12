/// SHA-256 摘要长度。本层的 nonce、会话密钥、HMAC 字段一律取这个长度。
pub const SHA256_LEN: usize = 32;
/// 会话 nonce 长度。规范允许在 16 到摘要长度之间取值，这里取上限：
/// nonce 越长重放窗口越小，代价只是报文里多几十个字节。
pub const NONCE_LEN: usize = SHA256_LEN;
pub const AES_KEY_LEN: usize = 16;
pub const AES_BLOCK_LEN: usize = 16;
/// 参数加解密所需的密钥材料：一段 AES 密钥紧跟一个初始向量。
///
/// 它恰好等于一个摘要块长度，这一点被 [`kdfa32`] 用来把派生过程固定成
/// 单轮，见那里的说明。
pub const CFB_MATERIAL_LEN: usize = AES_KEY_LEN + AES_BLOCK_LEN;
/// 口令在会话结构里的存放上限。
pub(crate) const PASSPHRASE_MAX: usize = SHA256_LEN;
/// HMAC 密钥材料上限：会话密钥后面拼接口令。
pub(crate) const KEY_MATERIAL_MAX: usize = SHA256_LEN + PASSPHRASE_MAX;
pub(crate) fn be16_arr(v: u16) -> [u8; 2] {
    crate::cursor::be16_bytes(v)
}
pub(crate) fn be32_arr(v: u32) -> [u8; 4] {
    crate::cursor::be32_bytes(v)
}
pub trait Sha256Ctx: Sized {
    fn new() -> Self;
    fn update(&mut self, data: &[u8]);
    fn finish(self) -> [u8; SHA256_LEN];
}
pub trait HmacSha256Ctx: Sized {
    fn with_key(key: &[u8]) -> Self;
    fn update(&mut self, data: &[u8]);
    fn finish(self) -> [u8; SHA256_LEN];
}
pub trait NonceSource {
    fn nonce(&mut self) -> [u8; NONCE_LEN];
}
pub trait AesCfb {
    /// 原地加密。`material` 前半是密钥、后半是初始向量。
    fn encrypt(&self, material: &[u8; CFB_MATERIAL_LEN], data: &mut [u8]);
    fn decrypt(&self, material: &[u8; CFB_MATERIAL_LEN], data: &mut [u8]);
}
/// 会话密钥派生标签（含尾零）。
pub(crate) const LABEL_ATH: [u8; 4] = [0x41, 0x54, 0x48, 0x00];
/// 参数加解密密钥派生标签（含尾零）。
pub(crate) const LABEL_CFB: [u8; 4] = [0x43, 0x46, 0x42, 0x00];
/// 派生 32 字节密钥材料。
///
/// 计数器只走一轮。本层要派生的两样东西——会话密钥、参数加解密的密钥
/// 加初始向量——长度都恰好是一个摘要块，所以通用的多轮循环在这里没有
/// 调用者。固定成单轮之后，循环不变量与终止性都不必再证，规约也只剩
/// 一条等式。若将来需要更长的输出，应当另写一个带 `decreases` 的多轮
/// 版本，而不是把这个函数改成循环——那会让现有调用点的证明全部重来。
pub(crate) fn kdfa32<H: HmacSha256Ctx>(
    key: &[u8],
    label: &[u8],
    u: &[u8],
    v: &[u8],
) -> [u8; SHA256_LEN] {
    let mut h = H::with_key(key);
    let counter = be32_arr(1);
    let bits = be32_arr(256);
    h.update(&counter[..]);
    h.update(label);
    h.update(u);
    h.update(v);
    h.update(&bits[..]);
    h.finish()
}
