use crate::{auth::*, crypto::*};

/// Session lifecycle.
///
/// `Pending` uses a tuple variant rather than named fields: a struct literal with braces in an `ensures`
/// clause is parsed as the start of the function body, and the specification rejects a state mention if it
/// appears even once. The tuple form is a call expression and has no such ambiguity.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SessionState {
    /// Session is available and waiting for the next command.
    Idle,
    /// Command has been fixed and is waiting for the response. The payload is the index of this session
    /// in the authorization area.
    Pending(usize),
    /// Session has been invalidated. Its handle still needs to be released once, and this structure must
    /// never participate in any further computation after that.
    Closed,
}
/// An HMAC authorization session.
///
/// The struct itself carries key material, so it does not implement `Clone` — every extra copy would mean
/// another place where the secret must be erased. It also does not implement `Debug`: logging the session
/// key is one of the easiest mistakes to make and the hardest to notice.
pub struct AuthSession {
    handle: u32,
    /// Local nonce for this round.
    our_nonce: [u8; NONCE_LEN],
    /// Most recent nonce from the peer.
    tpm_nonce: [u8; NONCE_LEN],
    session_key: [u8; SHA256_LEN],
    passphrase: [u8; PASSPHRASE_MAX],
    passphrase_len: usize,
    /// Session attributes used in the current command.
    attrs: u8,
    /// Current command code. It is needed for the response digest, but the response packet does not carry
    /// the command code itself, so it must be remembered locally — this is also why a response cannot be
    /// reused for another command.
    ordinal: u32,
    state: SessionState,
}
/// HMAC key material formed by concatenating the session key and passphrase; it is erased on drop.
///
/// [`AuthSession::key_buf`] copies the secret out of the struct into a stack buffer each time; these
/// temporary copies are just like the struct itself and must be wiped immediately after use. By wrapping
/// them in a `Drop` type, erasure happens automatically when the scope ends, so the caller does not need
/// to remember to clean up manually — same pattern as [`AuthSession`]’s own `Drop`.
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
    /// Handle for this session.
    pub fn handle(&self) -> u32 {
        self.handle
    }
    /// Local nonce for this round. Returns a copy: nonces are not secret, but callers should not be able to
    /// mutate the structure through them.
    pub fn our_nonce(&self) -> [u8; NONCE_LEN] {
        self.our_nonce
    }
    /// Session attributes for the current command.
    pub fn attrs(&self) -> u8 {
        self.attrs
    }
    /// Concatenate the session key and passphrase into a fixed-length buffer. The returned
    /// [`KeyMaterial`] is erased on drop.
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
    /// Derive the session key from the negotiated shared secret and both nonces.
    ///
    /// The shared secret is used only here; the struct no longer holds it afterward — key derivation is
    /// one-way, and leaking the session key does not let the secret be reconstructed.
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
    /// Set the current passphrase. The trailing zero bytes are stripped first, as required by the
    /// specification.
    ///
    /// This stripping step cannot be skipped: the same passphrase with or without trailing zero bytes yields
    /// different MACs, and callers often pass a fixed-length buffer.
    pub fn set_passphrase(&mut self, pw: &[u8]) {
        let mut n = pw.len();
        while n > 0 && pw[n - 1] == 0 {
            n -= 1;
        }
        self.passphrase[..n].copy_from_slice(&pw[..n]);
        self.passphrase_len = n;
    }
    /// Generate a fresh nonce for the next command.
    ///
    /// The precondition `nonce_gen < rng.draws()` and the postcondition form a chain: each round’s nonce
    /// generation is strictly greater than the previous one, so the same nonce can never be reused in two
    /// rounds. The unpredictability of the value is the random source’s responsibility, not this function’s.
    ///
    /// The “continue session” bit is forcibly added to the attributes: a session is a cross-command
    /// resource, and if a round forgets to set it, the peer will tear the session down unilaterally after
    /// that round ends, and the local side will remain unaware until the next round fails for a reason far
    /// removed from the actual cause.
    pub fn begin<R: NonceSource>(&mut self, rng: &mut R, ordinal: u32, attrs: u8) {
        self.our_nonce = rng.nonce();
        self.ordinal = ordinal;
        self.attrs = attrs | SA_CONTINUE_SESSION;
    }
    /// Compute the command MAC and write it into the authorization area.
    ///
    /// This is the only valid call time: after all parameters have been written. If even a single byte in
    /// the parameter area changes, the MAC becomes invalid. If the current round needs to encrypt the first
    /// parameter, that encryption must happen before this function — the digest covers ciphertext, not
    /// plaintext.
    ///
    /// `names` is the concatenation of the authorization-handle names in order. It is prepared by the caller
    /// according to handle type: persistent objects use the “algorithm identifier || digest” form, and all
    /// others use the four-byte handle itself.
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
    /// Validate the response MAC.
    ///
    /// **This is the reason this module exists.** Returning `Ok` means the MAC in the packet is byte-for-byte
    /// identical to the value recomputed using this session’s key, the two nonces for this round, and the
    /// command code for this round. The postcondition states this explicitly, so any implementation that
    /// bypasses validation and trusts the response directly will fail verification.
    ///
    /// The command code is taken from local state rather than from the packet — the response packet does not
    /// carry the command code at all. This is why “put the response for command A into command B” is a
    /// replay that fails at the digest layer.
    ///
    /// Any failure path marks the session as closed. Retrying the same session with the same key after a
    /// failure would give the peer another chance to guess.
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
    /// Close the session immediately. Used as the cleanup path when error handling bypasses
    /// [`AuthSession::check_response`].
    pub fn close(&mut self) {
        self.state = SessionState::Closed;
    }
}
impl Drop for AuthSession {
    /// Erase key material on destruction.
    ///
    /// `session_key` and `passphrase` are the only secrets in this structure. After `fill(0)`, we insert a
    /// `compiler_fence` to stop the compiler from removing those writes on the grounds that “the object is
    /// about to be dropped” (dead-store elimination). This is not equivalent to a bytewise `volatile`
    /// zeroization, but given the constraint of not introducing verification dependencies, it is the
    /// strongest guarantee available. This is also why this structure intentionally does not implement
    /// `Clone`: there is only one copy, so there is only one place that needs erasure.
    fn drop(&mut self) {
        self.session_key.fill(0);
        self.passphrase.fill(0);
        self.passphrase_len = 0;
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}
/// Derive the key and IV needed for parameter encryption/decryption in the current round.
///
/// The order of the two nonces determines the direction: in command direction, the local nonce comes
/// first; in response direction, the peer nonce comes first. The material differs between directions,
/// which is why the two directions on the same session do not reuse the same keystream.
pub fn cfb_material<H: HmacSha256Ctx>(
    session: &AuthSession,
    newer: &[u8; NONCE_LEN],
    older: &[u8; NONCE_LEN],
) -> [u8; CFB_MATERIAL_LEN] {
    let km = session.key_buf();
    let key = km.as_slice();
    kdfa32::<H>(key, &LABEL_CFB[..], &newer[..], &older[..])
}
/// Encrypt the first parameter in place. Must be called before [`AuthSession::finalize`].
pub fn encrypt_param<A: AesCfb>(aes: &A, material: &[u8; CFB_MATERIAL_LEN], param: &mut [u8]) {
    aes.encrypt(material, param);
}
/// Decrypt the first parameter in place. Must be called only after [`AuthSession::check_response`] returns
/// `Ok` — decrypting unvalidated bytes is equivalent to treating arbitrary peer-provided data as plain
/// text for the upper layer.
pub fn decrypt_param<A: AesCfb>(aes: &A, material: &[u8; CFB_MATERIAL_LEN], param: &mut [u8]) {
    aes.decrypt(material, param);
}
