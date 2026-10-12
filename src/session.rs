use crate::{auth::*, crypto::*};

/// 会话生命周期。
///
/// `Pending` 用元组变体而非具名字段：带花括号的结构体字面量在 `ensures`
/// 子句里会被解析成函数体的开始，规约里只要提一次状态就报语法错。元组
/// 形式写出来是调用式，没有这个歧义。
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SessionState {
    /// 会话可用，等待下一条命令。
    Idle,
    /// 命令已定型，等待响应。载荷是本会话在授权区里的序号。
    Pending(usize),
    /// 会话已作废。句柄还需要释放一次，之后本结构不得再参与任何运算。
    Closed,
}
/// 一个 HMAC 授权会话。
///
/// 结构体本身携带密钥材料，因此不实现 `Clone`——多一份副本就多一处需要
/// 擦除的地方。它也不实现 `Debug`：把会话密钥打进日志是最容易犯、也最难
/// 察觉的错误之一。
pub struct AuthSession {
    handle: u32,
    /// 本端本轮 nonce。
    our_nonce: [u8; NONCE_LEN],
    /// 对端最近一轮 nonce。
    tpm_nonce: [u8; NONCE_LEN],
    session_key: [u8; SHA256_LEN],
    passphrase: [u8; PASSPHRASE_MAX],
    passphrase_len: usize,
    /// 本轮命令使用的会话属性。
    attrs: u8,
    /// 本轮命令码。响应摘要要用到它，而响应报文里并不携带命令码，所以必须
    /// 由本端记住——这也正是响应无法被挪用到另一条命令上的原因。
    ordinal: u32,
    state: SessionState,
}
/// 会话密钥与口令拼成的 HMAC 密钥材料，析构即擦除。
///
/// [`AuthSession::key_buf`] 每次把结构体里的秘密拷进一块栈缓冲返回，这些
/// 临时副本和结构体本身一样需要用完即抹。包成带 `Drop` 的类型后，擦除随
/// 作用域结束自动发生，调用方无需、也无法忘记手动清理——与
/// [`AuthSession`] 自身的 `Drop` 同一套路。
struct KeyMaterial {
    buf: [u8; KEY_MATERIAL_MAX],
    len: usize,
}
impl KeyMaterial {
    fn as_slice(&self) -> &[u8] {
        &self.buf[..self.len]
    }
}
impl Drop for KeyMaterial {
    fn drop(&mut self) {
        self.buf.fill(0);
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}
impl AuthSession {
    /// 本会话的句柄。
    pub fn handle(&self) -> u32 {
        self.handle
    }
    /// 本端本轮 nonce。返回副本：nonce 不是秘密，但调用方不该借由它改写本结构。
    pub fn our_nonce(&self) -> [u8; NONCE_LEN] {
        self.our_nonce
    }
    /// 本轮会话属性。
    pub fn attrs(&self) -> u8 {
        self.attrs
    }
    /// 把会话密钥与口令拼进一块定长缓冲区。返回的 [`KeyMaterial`] 析构即擦除。
    fn key_buf(&self) -> KeyMaterial {
        let mut buf = [0u8; KEY_MATERIAL_MAX];
        let plen = self.passphrase_len;
        buf[..SHA256_LEN].copy_from_slice(&self.session_key);
        buf[SHA256_LEN..SHA256_LEN + plen].copy_from_slice(&self.passphrase[..plen]);
        KeyMaterial {
            buf,
            len: SHA256_LEN + plen,
        }
    }
    /// 由协商出的共享秘密与双方 nonce 导出会话密钥。
    ///
    /// 共享秘密只在这一步用到，之后本结构不再持有它——密钥派生是单向的，
    /// 会话密钥泄露也推不回秘密本身。
    pub fn open_session<H: HmacSha256Ctx>(
        handle: u32,
        salt: &[u8],
        our_nonce: [u8; NONCE_LEN],
        tpm_nonce: [u8; NONCE_LEN],
    ) -> AuthSession {
        let key = kdfa32::<H>(salt, &LABEL_ATH[..], &tpm_nonce[..], &our_nonce[..]);
        AuthSession {
            handle,
            our_nonce,
            tpm_nonce,
            session_key: key,
            passphrase: [0u8; PASSPHRASE_MAX],
            passphrase_len: 0,
            attrs: 0,
            ordinal: 0,
            state: SessionState::Idle,
        }
    }
    /// 设置本轮口令。尾部零字节按规范先行剥除。
    ///
    /// 剥除这一步不能省：同一个口令带不带尾零会算出不同的 MAC，而调用方传
    /// 进来的往往是定长缓冲区。
    pub fn set_passphrase(&mut self, pw: &[u8]) {
        let mut n = pw.len();
        while n > 0 && pw[n - 1] == 0 {
            n -= 1;
        }
        self.passphrase[..n].copy_from_slice(&pw[..n]);
        self.passphrase_len = n;
    }
    /// 为下一条命令换一枚新 nonce。
    ///
    /// 前置条件 `nonce_gen < rng.draws()` 与后置条件一起构成一条链：每轮的
    /// nonce 世代严格大于上一轮，因此不可能出现两轮复用同一枚 nonce。取值
    /// 层面的不可预测性是随机源的责任，不在这里断言。
    ///
    /// 属性里强行补上「会话延续」位：会话是跨命令复用的资源，若某一轮忘了置
    /// 这一位，对端会在该轮结束后单方面销毁它，而本端毫不知情，下一轮的失败
    /// 点会离真正的原因很远。
    pub fn begin<R: NonceSource>(&mut self, rng: &mut R, ordinal: u32, attrs: u8) {
        self.our_nonce = rng.nonce();
        self.ordinal = ordinal;
        self.attrs = attrs | SA_CONTINUE_SESSION;
    }
    /// 算出命令 MAC 并填进授权区。
    ///
    /// 调用时机是**唯一**的：所有参数都已写入之后。参数区哪怕再动一个字节，
    /// 算出的 MAC 就作废了。若本轮要加密首个参数，加密也必须发生在本函数之
    /// 前——摘要覆盖的是密文，不是明文。
    ///
    /// `names` 是各授权句柄名字的顺序拼接。它由调用方按句柄类型准备：可持久化
    /// 的对象用「算法标识 ‖ 摘要」形式的名字，其余用四字节句柄本身。
    pub fn finalize<S: Sha256Ctx, H: HmacSha256Ctx>(
        &mut self,
        buf: &mut [u8],
        sess_off: usize,
        index: usize,
        names: &[u8],
        param_off: usize,
        param_len: usize,
    ) {
        let params = &buf[param_off..param_off + param_len];
        let cph = cp_hash::<S>(self.ordinal, names, params);
        let km = self.key_buf();
        let key = km.as_slice();
        let mac = auth_hmac::<H>(key, &cph, &self.our_nonce, &self.tpm_nonce, self.attrs);
        patch_hmac(buf, sess_off, &mac);
        self.state = SessionState::Pending(index);
    }
    /// 校验响应 MAC。
    ///
    /// **这是本模块存在的理由。** 返回 `Ok` 意味着：报文里那段 MAC 与用本会话
    /// 密钥、本轮两枚 nonce、本轮命令码重算出来的值逐字节相同。后置条件把这句
    /// 话原样写了出来，所以任何绕过校验直接采信响应的写法都通不过。
    ///
    /// 命令码取自本端记录而非报文——响应报文根本不携带命令码。这一点让「把甲
    /// 命令的响应塞给乙命令」这类挪用在摘要层面就对不上。
    ///
    /// 任何一条失败路径都把会话置为作废。会话失败之后继续用同一把密钥重试，
    /// 等于给对面多一次猜测机会。
    pub fn check_response<S: Sha256Ctx, H: HmacSha256Ctx>(
        &mut self,
        raw: &[u8],
        rhandles: usize,
    ) -> Result<RspAuth, AuthErr> {
        let index = match self.state {
            SessionState::Pending(i) => i,
            _ => {
                self.state = SessionState::Closed;
                return Err(AuthErr::NoSession);
            }
        };
        let a = match parse_rsp_auth(raw, rhandles, index) {
            Ok(a) => a,
            Err(e) => {
                self.state = SessionState::Closed;
                return Err(e);
            }
        };
        let param_end = match a.param_off.checked_add(a.param_len) {
            Some(v) => v,
            None => {
                self.state = SessionState::Closed;
                return Err(AuthErr::Malformed);
            }
        };
        let params = &raw[a.param_off..param_end];
        let rph = rp_hash::<S>(0, self.ordinal, params);
        let km = self.key_buf();
        let key = km.as_slice();
        let expect = auth_hmac::<H>(key, &rph, &a.tpm_nonce, &self.our_nonce, self.attrs);
        let hmac_end = match a.hmac_off.checked_add(SHA256_LEN) {
            Some(v) => v,
            None => {
                self.state = SessionState::Closed;
                return Err(AuthErr::Malformed);
            }
        };
        let got = &raw[a.hmac_off..hmac_end];
        if !ct_eq32(&expect, got) {
            self.state = SessionState::Closed;
            return Err(AuthErr::HmacMismatch);
        }
        self.tpm_nonce = a.tpm_nonce;
        self.state = SessionState::Idle;
        Ok(a)
    }
    /// 主动作废会话。错误处理路径绕过 [`AuthSession::check_response`] 时用它收尾。
    pub fn close(&mut self) {
        self.state = SessionState::Closed;
    }
}
impl Drop for AuthSession {
    /// 析构即擦除密钥材料。
    ///
    /// `session_key` 与 `passphrase` 是本结构仅有的秘密。`fill(0)` 之后插一道
    /// `compiler_fence`，阻止编译器以"反正马上要释放"为由把这些写入消掉
    /// （dead-store elimination）。这不等同于 `zeroize` 的逐字节 volatile 写，
    /// 但在不给验证核引入任何依赖的前提下，是能做到的最强保证；也正是本结构
    /// 刻意不实现 `Clone` 的配套——只有一份副本，就只有这一处需要擦。
    fn drop(&mut self) {
        self.session_key.fill(0);
        self.passphrase.fill(0);
        self.passphrase_len = 0;
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}
/// 推导本轮参数加解密所需的密钥与初始向量。
///
/// 两枚 nonce 的先后决定了方向：命令方向本端 nonce 在前，响应方向对端 nonce 在
/// 前。两个方向的材料不同，这正是同一条会话上两个方向不会撞用同一段密钥流的
/// 原因。
pub fn cfb_material<H: HmacSha256Ctx>(
    session: &AuthSession,
    newer: &[u8; NONCE_LEN],
    older: &[u8; NONCE_LEN],
) -> [u8; CFB_MATERIAL_LEN] {
    let km = session.key_buf();
    let key = km.as_slice();
    kdfa32::<H>(key, &LABEL_CFB[..], &newer[..], &older[..])
}
/// 原地加密命令的首个参数。必须在 [`AuthSession::finalize`] 之前调用。
pub fn encrypt_param<A: AesCfb>(aes: &A, material: &[u8; CFB_MATERIAL_LEN], param: &mut [u8]) {
    aes.encrypt(material, param);
}
/// 原地解密响应的首个参数。必须在 [`AuthSession::check_response`] 返回 `Ok` 之后
/// 调用——对未经校验的字节做解密，等于把对端塞进来的任意数据当成明文交给上层。
pub fn decrypt_param<A: AesCfb>(aes: &A, material: &[u8; CFB_MATERIAL_LEN], param: &mut [u8]) {
    aes.decrypt(material, param);
}
