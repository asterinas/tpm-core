use vstd::prelude::*;
use vstd::array::*;
use vstd::slice::*;

use crate::auth::*;
use crate::crypto::*;

verus! {

broadcast use group_crypto_axioms;

// ===========================================================================
// State
// ===========================================================================

/// Session lifecycle.
///
/// `Pending` uses a tuple variant rather than named fields: a brace-delimited struct literal in an `ensures`
/// clause is parsed as the start of the function body, so merely mentioning the state in a spec gives a syntax error. The tuple
/// form reads like a call and has no such ambiguity.
#[derive(Clone, Copy, PartialEq, Eq, Structural, Debug)]
pub enum SessionState {
    /// The session is usable, waiting for the next command.
    Idle,
    /// The command is finalized, waiting for the response. The payload is this session's index in the authorization area.
    Pending(usize),
    /// The session has been invalidated. The handle still has to be released once; after that this structure must take no further part in any computation.
    Closed,
}

/// An HMAC authorization session.
///
/// The struct itself carries key material, so it does not implement `Clone` -- every extra copy is one more place that needs
/// wiping. It does not implement `Debug` either: printing the session key into a log is one of the easiest and hardest-to-notice
/// mistakes.
pub struct AuthSession {
    pub handle: u32,
    /// This side's nonce for the current round.
    pub our_nonce: [u8; NONCE_LEN],
    /// The peer's most recent nonce.
    pub tpm_nonce: [u8; NONCE_LEN],
    pub session_key: [u8; SHA256_LEN],
    pub passphrase: [u8; PASSPHRASE_MAX],
    pub passphrase_len: usize,
    /// Session attributes used by the current command.
    pub attrs: u8,
    /// The command code of the current round. The response digest needs it, and the response message does not carry the command code, so it must
    /// be remembered by this side -- which is exactly why a response cannot be repurposed for a different command.
    pub ordinal: u32,
    pub state: SessionState,
    /// The draw generation of this round's nonce. Appears only in proofs.
    pub nonce_gen: Ghost<nat>,
}

/// A temporary copy of the HMAC key material. Zeroed when it leaves scope, so the session key and passphrase do not linger on the stack.
struct KeyMaterial {
    buf: [u8; KEY_MATERIAL_MAX],
    len: usize,
}

impl KeyMaterial {
    closed spec fn material(self) -> Seq<u8> {
        self.buf@.subrange(0, self.len as int)
    }

    closed spec fn wf(self) -> bool {
        self.len <= KEY_MATERIAL_MAX
    }

    fn as_slice(&self) -> (r: &[u8])
        requires
            self.wf(),
        ensures
            r@ =~= self.material(),
    {
        &self.buf[0..self.len]
    }
}

#[verifier::external]
impl Drop for KeyMaterial {
    fn drop(&mut self) {
        self.buf.fill(0);
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}

impl AuthSession {
    pub open spec fn wf(self) -> bool {
        &&& self.passphrase_len <= PASSPHRASE_MAX
        &&& match self.state {
            SessionState::Pending(i) => i < MAX_SESSIONS,
            _ => true,
        }
    }

    /// Whether the session is in the "command sent, awaiting response" phase.
    ///
    /// Written as a `match` rather than a `matches` expression: every state check in the specs
    /// goes through this predicate, so call sites need not touch pattern syntax.
    pub open spec fn pending(self) -> bool {
        match self.state {
            SessionState::Pending(_) => true,
            _ => false,
        }
    }

    /// HMAC key material: the session key immediately followed by the passphrase.
    ///
    /// The two parts must be adjacent and in a fixed order -- the specification treats them as one whole key.
    pub open spec fn key_material(self) -> Seq<u8> {
        self.session_key@ + self.passphrase@.subrange(0, self.passphrase_len as int)
    }

    /// Whether this session can still accept a command.
    pub open spec fn usable(self) -> bool {
        self.state == SessionState::Idle
    }

    // -----------------------------------------------------------------------
    // Executable side of the key material
    // -----------------------------------------------------------------------

    /// Concatenate the session key and the passphrase into a fixed-size buffer and return the valid length.
    fn key_buf(&self) -> (r: KeyMaterial)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.material() =~= self.key_material(),
    {
        let mut buf: [u8; KEY_MATERIAL_MAX] = [0u8; KEY_MATERIAL_MAX];

        for i in 0..SHA256_LEN
            invariant
                buf@.len() == KEY_MATERIAL_MAX,
                forall|k: int| #![auto] 0 <= k < i ==> buf@[k] == self.session_key@[k],
        {
            buf[i] = self.session_key[i];
        }

        for j in 0..self.passphrase_len
            invariant
                self.passphrase_len <= PASSPHRASE_MAX,
                buf@.len() == KEY_MATERIAL_MAX,
                forall|k: int| #![auto] 0 <= k < SHA256_LEN ==> buf@[k] == self.session_key@[k],
                forall|k: int| #![auto] 0 <= k < j ==> buf@[SHA256_LEN + k] == self.passphrase@[k],
        {
            buf[SHA256_LEN + j] = self.passphrase[j];
        }

        KeyMaterial { buf, len: SHA256_LEN + self.passphrase_len }
    }

    // -----------------------------------------------------------------------
    // Establishment
    // -----------------------------------------------------------------------

    /// Derive the session key from the negotiated shared secret and both parties' nonces.
    ///
    /// The shared secret is used only in this step and this structure no longer holds it afterwards -- key derivation is one-way,
    /// and a leaked session key cannot be traced back to the secret itself.
    pub fn open_session<H: HmacSha256Ctx>(
        handle: u32,
        salt: &[u8],
        our_nonce: [u8; NONCE_LEN],
        tpm_nonce: [u8; NONCE_LEN],
        gen: Ghost<nat>,
    ) -> (r: AuthSession)
        ensures
            r.wf(),
            r.state == SessionState::Idle,
            r.handle == handle,
            r.our_nonce@ =~= our_nonce@,
            r.tpm_nonce@ =~= tpm_nonce@,
            r.passphrase_len == 0,
            r.key_material() =~= r.session_key@,
            r.session_key@ =~= spec_kdfa32(salt@, LABEL_ATH@, tpm_nonce@, our_nonce@),
            r.nonce_gen@ == gen@,
    {
        let key = kdfa32::<H>(
            salt,
            array_as_slice(&LABEL_ATH),
            array_as_slice(&tpm_nonce),
            array_as_slice(&our_nonce),
        );

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
            nonce_gen: gen,
        }
    }

    /// Set this round's passphrase. Trailing zero bytes are stripped first, per the specification.
    ///
    /// The stripping step cannot be omitted: the same passphrase with or without trailing zeros yields a different MAC, and what the caller passes
    /// in is often a fixed-size buffer.
    pub fn set_passphrase(&mut self, pw: &[u8])
        requires
            old(self).wf(),
            pw.len() <= PASSPHRASE_MAX,
        ensures
            final(self).wf(),
            final(self).passphrase_len <= pw.len(),
            final(self).handle == old(self).handle,
            final(self).our_nonce@ =~= old(self).our_nonce@,
            final(self).tpm_nonce@ =~= old(self).tpm_nonce@,
            final(self).session_key@ =~= old(self).session_key@,
            final(self).state == old(self).state,
            final(self).ordinal == old(self).ordinal,
            final(self).attrs == old(self).attrs,
            final(self).nonce_gen@ == old(self).nonce_gen@,
    {
        let mut n = pw.len();
        while n > 0 && pw[n - 1] == 0
            invariant
                n <= pw.len(),
            decreases n,
        {
            n -= 1;
        }

        for i in 0..n
            invariant
                n <= pw.len(),
                n <= PASSPHRASE_MAX,
                self.passphrase@.len() == PASSPHRASE_MAX,
        {
            self.passphrase[i] = pw[i];
        }
        self.passphrase_len = n;
    }

    // -----------------------------------------------------------------------
    // Start of each round
    // -----------------------------------------------------------------------

    /// Swap in a fresh nonce for the next command.
    ///
    /// The precondition `nonce_gen < rng.draws()` together with the postcondition forms a chain: each round's
    /// nonce generation is strictly greater than the previous one, so two rounds can never reuse the same nonce. Unpredictability of the
    /// values is the responsibility of the random source and is not asserted here.
    ///
    /// The "continue session" bit is forcibly added to the attributes: a session is a resource reused across commands, and if one round forgets to set
    /// this bit, the peer destroys it unilaterally at the end of that round without this side knowing, and the next round's failure
    /// point would be far from the real cause.
    pub fn begin<R: NonceSource>(&mut self, rng: &mut R, ordinal: u32, attrs: u8)
        requires
            old(self).wf(),
            old(self).usable(),
            old(self).nonce_gen@ < old(rng).draws(),
        ensures
            final(self).wf(),
            final(self).usable(),
            final(self).ordinal == ordinal,
            final(self).attrs == attrs | SA_CONTINUE_SESSION,
            final(self).our_nonce@ =~= spec_draw(old(rng).draws()),
            final(self).nonce_gen@ == old(rng).draws(),
            final(self).nonce_gen@ > old(self).nonce_gen@,
            final(self).nonce_gen@ < final(rng).draws(),
            final(self).handle == old(self).handle,
            final(self).tpm_nonce@ =~= old(self).tpm_nonce@,
            final(self).session_key@ =~= old(self).session_key@,
            final(self).passphrase_len == old(self).passphrase_len,
            final(self).key_material() =~= old(self).key_material(),
    {
        let ghost g = rng.draws();
        self.our_nonce = rng.nonce();
        self.nonce_gen = Ghost(g);
        self.ordinal = ordinal;
        self.attrs = attrs | SA_CONTINUE_SESSION;
    }

    // -----------------------------------------------------------------------
    // Command finalization
    // -----------------------------------------------------------------------

    /// Compute the command MAC and fill it into the authorization area.
    ///
    /// The call timing is **unique**: after all parameters have been written. If even one more byte of the parameter area changes,
    /// the computed MAC is void. If this round encrypts the first parameter, the encryption must also happen before this function --
    /// the digest covers the ciphertext, not the plaintext.
    ///
    /// `names` is the in-order concatenation of the names of the authorized handles. The caller prepares it by handle type: persistable
    /// objects use a name of the form "algorithm id ‖ digest", the others use the four-byte handle itself.
    pub fn finalize<S: Sha256Ctx, H: HmacSha256Ctx>(
        &mut self,
        buf: &mut [u8],
        sess_off: usize,
        index: usize,
        names: &[u8],
        param_off: usize,
        param_len: usize,
    )
        requires
            old(self).wf(),
            old(self).usable(),
            index < MAX_SESSIONS,
            sess_off + CMD_SESSION_LEN <= old(buf).len(),
            param_off + param_len <= old(buf).len(),
            sess_off + CMD_SESSION_LEN <= param_off,
        ensures
            final(self).wf(),
            final(self).state == SessionState::Pending(index),
            final(self).pending(),
            final(buf).len() == old(buf).len(),
            final(self).ordinal == old(self).ordinal,
            final(self).attrs == old(self).attrs,
            final(self).our_nonce@ =~= old(self).our_nonce@,
            final(self).tpm_nonce@ =~= old(self).tpm_nonce@,
            final(self).key_material() =~= old(self).key_material(),
            final(self).nonce_gen@ == old(self).nonce_gen@,
            // The MAC written into the message is exactly the one the spec describes
            final(buf)@.subrange(
                sess_off + SESS_HMAC_OFF,
                sess_off + SESS_HMAC_OFF + SHA256_LEN,
            ) =~= spec_hmac_sha256(
                old(self).key_material(),
                spec_auth_input(
                    spec_sha256(
                        spec_cp_input(
                            old(self).ordinal,
                            names@,
                            old(buf)@.subrange(param_off as int, param_off + param_len),
                        ),
                    ),
                    old(self).our_nonce@,
                    old(self).tpm_nonce@,
                    old(self).attrs,
                ),
            ),
            // The message is unchanged except for the MAC field
            forall|k: int|
                #![trigger final(buf)@[k]]
                0 <= k < final(buf).len() && (k < sess_off + SESS_HMAC_OFF || k >= sess_off
                    + CMD_SESSION_LEN) ==> final(buf)@[k] == old(buf)@[k],
    {
        let params = &buf[param_off..param_off + param_len];
        let cph = cp_hash::<S>(self.ordinal, names, params);

        let km = self.key_buf();
        let key = km.as_slice();

        let mac = auth_hmac::<H>(key, &cph, &self.our_nonce, &self.tpm_nonce, self.attrs);

        patch_hmac(buf, sess_off, &mac);
        self.state = SessionState::Pending(index);
    }

    // -----------------------------------------------------------------------
    // Response verification
    // -----------------------------------------------------------------------

    /// Verify the response MAC.
    ///
    /// **This is the reason this module exists.** Returning `Ok` means: the MAC segment in the message is byte-for-byte identical to the value recomputed from this session's
    /// key, this round's two nonces and this round's command code. The postcondition states exactly this
    /// sentence, so any way of trusting a response while bypassing verification fails to pass.
    ///
    /// The command code comes from this side's record rather than the message -- the response message does not carry a command code at all. This makes such misuse as "stuffing
    /// command A's response into command B" mismatch at the digest level.
    ///
    /// Every failure path marks the session invalid. Retrying with the same key after a session failure
    /// would give the other side one more chance to guess.
    pub fn check_response<S: Sha256Ctx, H: HmacSha256Ctx>(
        &mut self,
        raw: &[u8],
        rhandles: usize,
    ) -> (r: Result<RspAuth, AuthErr>)
        requires
            old(self).wf(),
            old(self).pending(),
            rhandles <= 1,
        ensures
            final(self).wf(),
            final(self).handle == old(self).handle,
            final(self).our_nonce@ =~= old(self).our_nonce@,
            final(self).key_material() =~= old(self).key_material(),
            final(self).nonce_gen@ == old(self).nonce_gen@,
            r matches Ok(a) ==> {
                &&& a.wf(raw@)
                &&& a.mac(raw@) =~= spec_hmac_sha256(
                    old(self).key_material(),
                    spec_auth_input(
                        spec_sha256(spec_rp_input(0, old(self).ordinal, a.params(raw@))),
                        a.tpm_nonce@,
                        old(self).our_nonce@,
                        old(self).attrs,
                    ),
                )
                &&& final(self).tpm_nonce@ =~= a.tpm_nonce@
                &&& final(self).state == SessionState::Idle
            },
            r is Err ==> final(self).state == SessionState::Closed,
    {
        let index = match self.state {
            SessionState::Pending(i) => i,
            _ => {
                self.state = SessionState::Closed;
                return Err(AuthErr::NoSession);
            },
        };

        let a = match parse_rsp_auth(raw, rhandles, index) {
            Ok(a) => a,
            Err(e) => {
                self.state = SessionState::Closed;
                return Err(e);
            },
        };

        let param_end = match a.param_off.checked_add(a.param_len) {
            Some(v) => v,
            None => {
                self.state = SessionState::Closed;
                return Err(AuthErr::Malformed);
            },
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
            },
        };
        let got = &raw[a.hmac_off..hmac_end];

        if !ct_eq32(&expect, got) {
            self.state = SessionState::Closed;
            return Err(AuthErr::HmacMismatch);
        }

        // State advances only after verification passes. The peer's nonce is trusted only at this moment; a message that fails verification cannot
        // leave anything in the session.
        self.tpm_nonce = a.tpm_nonce;
        self.state = SessionState::Idle;
        Ok(a)
    }

    /// Actively invalidate the session. Used to wrap up when an error-handling path bypasses [`AuthSession::check_response`].
    pub fn close(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).state == SessionState::Closed,
            final(self).handle == old(self).handle,
    {
        self.state = SessionState::Closed;
    }
}

// ===========================================================================
// Parameter encryption/decryption
// ===========================================================================
//
// The ordering between encryption/decryption and verification is deliberate, and exactly opposite in the two directions:
//
// - In the command direction, encrypt first and then compute the MAC; the digest covers the ciphertext;
// - In the response direction, verify the MAC first and then decrypt; the verification is likewise over the ciphertext.
//
// Both functions therefore take the form "this round's key material is derived on the spot by the KDF", with no cached derivation result: the key
// changes every round with the nonce, and caching a copy across rounds only creates chances to use the wrong version.

/// Derive the key and initialization vector needed for this round's parameter encryption/decryption.
///
/// The order of the two nonces determines the direction: in the command direction this side's nonce comes first, in the response direction the peer's nonce comes
/// first. The material differs between the two directions, which is exactly why the two directions of one session
/// never reuse the same segment of key stream.
pub fn cfb_material<H: HmacSha256Ctx>(
    session: &AuthSession,
    newer: &[u8; NONCE_LEN],
    older: &[u8; NONCE_LEN],
) -> (r: [u8; CFB_MATERIAL_LEN])
    requires
        session.wf(),
    ensures
        r@ =~= spec_kdfa32(session.key_material(), LABEL_CFB@, newer@, older@),
{
    let km = session.key_buf();
    let key = km.as_slice();
    kdfa32::<H>(key, array_as_slice(&LABEL_CFB), array_as_slice(newer), array_as_slice(older))
}

/// Encrypt the first parameter of a command in place. Must be called before [`AuthSession::finalize`].
pub fn encrypt_param<A: AesCfb>(aes: &A, material: &[u8; CFB_MATERIAL_LEN], param: &mut [u8])
    ensures
        final(param).len() == old(param).len(),
        final(param)@ =~= spec_aes_cfb(
            material@.subrange(0, AES_KEY_LEN as int),
            material@.subrange(AES_KEY_LEN as int, CFB_MATERIAL_LEN as int),
            old(param)@,
            true,
        ),
{
    aes.encrypt(material, param);
}

/// Decrypt the first parameter of a response in place. Must be called after [`AuthSession::check_response`] returns `Ok`
/// -- decrypting bytes that have not been verified amounts to handing arbitrary data planted by the peer to the upper layer as plaintext.
pub fn decrypt_param<A: AesCfb>(aes: &A, material: &[u8; CFB_MATERIAL_LEN], param: &mut [u8])
    ensures
        final(param).len() == old(param).len(),
        final(param)@ =~= spec_aes_cfb(
            material@.subrange(0, AES_KEY_LEN as int),
            material@.subrange(AES_KEY_LEN as int, CFB_MATERIAL_LEN as int),
            old(param)@,
            false,
        ),
{
    aes.decrypt(material, param);
}

#[verifier::external]
impl Drop for AuthSession {
    fn drop(&mut self) {
        self.session_key.fill(0);
        self.passphrase.fill(0);
        self.passphrase_len = 0;
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}

} // verus!