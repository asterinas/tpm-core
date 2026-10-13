/// SHA-256 digest length. The nonce, session key, and HMAC fields in this layer all use this length.
pub const SHA256_LEN: usize = 32;
/// Session nonce length. The specification allows a value between 16 and the digest length, and here we
/// choose the maximum: a longer nonce reduces the replay window, at the cost of only a few extra bytes in
/// the packet.
pub const NONCE_LEN: usize = SHA256_LEN;
pub const AES_KEY_LEN: usize = 16;
pub const AES_BLOCK_LEN: usize = 16;
/// Key material needed for parameter encryption/decryption: an AES key followed by an initialization
/// vector.
///
/// It is exactly one digest-block length, and this is what [`kdfa32`] uses to fix the derivation process
/// to a single round; see the explanation there.
pub const CFB_MATERIAL_LEN: usize = AES_KEY_LEN + AES_BLOCK_LEN;
/// Maximum space for a password in the session structure.
pub(crate) const PASSPHRASE_MAX: usize = SHA256_LEN;
/// Maximum HMAC key material: session key followed by passphrase.
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
    /// In-place encryption. The first half of `material` is the key and the second half is the IV.
    fn encrypt(&self, material: &[u8; CFB_MATERIAL_LEN], data: &mut [u8]);
    fn decrypt(&self, material: &[u8; CFB_MATERIAL_LEN], data: &mut [u8]);
}
/// Session key derivation label (including trailing NUL).
pub(crate) const LABEL_ATH: [u8; 4] = [0x41, 0x54, 0x48, 0x00];
/// Parameter encryption/decryption key derivation label (including trailing NUL).
pub(crate) const LABEL_CFB: [u8; 4] = [0x43, 0x46, 0x42, 0x00];
/// Derive 32 bytes of key material.
///
/// The counter advances only once. The two values this layer must derive—session keys, and the parameter
/// encryption key plus IV—both happen to be exactly one digest-block long, so there is no generic multi-
/// round loop to call here. Once it is fixed to a single round, the loop invariant and termination proof no
/// longer matter, and the specification reduces to a single equality. If a longer output is needed in the
/// future, it should be implemented as a separate multi-round version with a `decreases` clause, not by
/// turning this function into a loop, because that would invalidate the existing proofs at every call site.
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
