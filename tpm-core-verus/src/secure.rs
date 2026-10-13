use vstd::prelude::*;
use vstd::array::*;
use vstd::slice::*;

use crate::auth::{
    AuthErr, CMD_SESSION_LEN, MAX_SESSIONS, RspAuth, write_cmd_session,
};
#[cfg(verus_keep_ghost)]
use crate::auth::{spec_auth_input, spec_rp_input};
use crate::chip::MSG_MAX;
use crate::crypto::{HmacSha256Ctx, NonceSource, Sha256Ctx};
#[cfg(verus_keep_ghost)]
use crate::crypto::{spec_hmac_sha256, spec_sha256};
use crate::msg::TPM_HEADER_LEN;
use crate::phy::TisPhy;
use crate::session::AuthSession;
use crate::xfer::{RC_SUCCESS, Xfer, XferErr};

verus! {

// ===========================================================================
// What this layer is meant to block
// ===========================================================================
//
// The session layer can already prove "the MAC matched", but that only **provides** a verification function. That the function
// exists does not mean a response necessarily goes through it -- a caller can perfectly well send a command, get the bytes and parse them directly,
// with nothing along the way reminding them that a step was skipped. The most valuable property of the session layer thus stays at "can hold"
// rather than "must hold".
//
// This layer turns it into the latter, not with documentation or assertions but with **visibility**:
//
// - The response buffer is a private field of this struct; no reference to it can be obtained outside the module;
// - The only function that reads response parameters requires an [`Authenticated`] to be presented;
// - [`Authenticated`] contains a private field and cannot be constructed outside this module, while this module mints it only after the MAC
//   verification has passed.
//
// Taken together, "response bytes that have not been verified" are unreachable at the type level. This is not a
// theorem that needs proving but a fact that needs no proof -- it follows from Rust's visibility rules, and the verifier does not even have to
// take part. Any code that tries to bypass it simply does not compile.

// ===========================================================================
// Command layout
// ===========================================================================

/// The partitioning of an authorized command within the buffer.
///
/// Supplied by the caller rather than derived by this layer: the partitioning depends on how many handles the specific command has and how its parameters are arranged,
/// which is knowledge of the command layer. This layer is only responsible for **checking that the partitions do not conflict** and then filling them in.
pub struct CmdLayout {
    /// Total command length. It must agree with the length field in the message header, which the link layer re-checks.
    pub len: usize,
    /// Start of the authorization area.
    pub sess_off: usize,
    /// This session's index in the authorization area.
    pub index: usize,
    /// Start of the parameter area.
    pub param_off: usize,
    /// Length of the parameter area.
    pub param_len: usize,
    /// Number of handles in the response. The digest covers the part after the handles; miscounting by one throws off every offset.
    pub rhandles: usize,
}

impl CmdLayout {
    /// `cap` is the capacity of the command buffer.
    ///
    /// "The authorization area lies entirely before the parameter area" is an ordering fixed by the message format itself; writing it down here
    /// has an extra benefit: it also guarantees that filling in the authorization area never touches the parameter area, so
    /// "the parameters covered by the digest are the ones the caller wrote" needs no separate argument.
    pub open spec fn wf(self, cap: int) -> bool {
        &&& TPM_HEADER_LEN <= self.sess_off
        &&& self.sess_off + CMD_SESSION_LEN <= self.param_off
        &&& self.param_off + self.param_len <= self.len
        &&& TPM_HEADER_LEN <= self.len
        &&& self.len <= cap
        &&& self.index < MAX_SESSIONS
        &&& self.rhandles <= 1
    }
}

// ===========================================================================
// Credentials
// ===========================================================================

/// A credential saying "the MAC of this response has matched".
///
/// `seal` is a private zero-sized field with a single purpose: **this type cannot even be constructed outside this module**
/// -- not merely hard, but disallowed by the language; any struct literal is rejected because it cannot reach
/// this field. A credential can therefore only be minted by [`Guarded::invoke`] after verification has passed,
/// so holding one is itself evidence that verification took place.
///
/// The location result `a`, on the other hand, can be public: reading a few offsets grants no capability; the capability lies in the credential itself.
/// It is not at risk of being altered either -- [`Guarded::params`] requires presenting [`Authenticated::certified`],
/// and that property is stated about `a`, so changing a single offset makes it unprovable.
///
/// The remaining fields are ghost values recording the key material, command code, this side's nonce and attributes at minting time.
/// They take no part in runtime computation; they only let [`Authenticated::certified`] state that MAC
/// equation in full -- a credential that cannot say what it certifies degenerates into a mere marker.
pub struct Authenticated {
    pub a: RspAuth,
    pub raw: Ghost<Seq<u8>>,
    pub key: Ghost<Seq<u8>>,
    pub ordinal: Ghost<u32>,
    pub our_nonce: Ghost<Seq<u8>>,
    pub attrs: Ghost<u8>,
    /// Seal. It cannot be assigned outside this module, so this type cannot be constructed.
    #[allow(dead_code)]
    seal: (),
}

impl Authenticated {
    pub closed spec fn view(self) -> RspAuth {
        self.a
    }

    pub closed spec fn raw(self) -> Seq<u8> {
        self.raw@
    }

    pub closed spec fn key_material(self) -> Seq<u8> {
        self.key@
    }

    pub closed spec fn ordinal(self) -> u32 {
        self.ordinal@
    }

    pub closed spec fn our_nonce(self) -> Seq<u8> {
        self.our_nonce@
    }

    pub closed spec fn attrs(self) -> u8 {
        self.attrs@
    }

    /// Everything the credential asserts: the message partitioning is self-consistent, and the MAC segment in the message equals the value recomputed from the recorded
    /// key material, both nonces and the command code.
    ///
    /// The command code comes from this side's record rather than the message -- the response message does not carry a command code. This is exactly why "moving command A's
    /// response to command B" mismatches at the digest level.
    pub closed spec fn certified(self) -> bool {
        &&& self.view().wf(self.raw())
        &&& self.view().mac(self.raw()) =~= spec_hmac_sha256(
            self.key_material(),
            spec_auth_input(
                spec_sha256(spec_rp_input(0, self.ordinal(), self.view().params(self.raw()))),
                self.view().tpm_nonce@,
                self.our_nonce(),
                self.attrs(),
            ),
        )
    }
}

// ===========================================================================
// Errors
// ===========================================================================

#[derive(Clone, Copy, PartialEq, Eq, Structural, Debug)]
pub enum SecErr {
    /// The bytes did not complete a round trip.
    Bus(XferErr),
    /// The device returned a non-zero return code. Such a response has no authorization area and cannot be verified.
    Rc(u32),
    /// The response arrived, but authorization verification failed.
    Auth(AuthErr),
}

// ===========================================================================
// Protected round trip
// ===========================================================================

pub struct Guarded<P: TisPhy> {
    pub x: Xfer<P>,
    pub sess: AuthSession,
    /// Response scratch buffer. **Private** -- all guarantees of this layer rest on it being unreachable outside the module.
    rbuf: [u8; MSG_MAX],
    /// Number of valid bytes in the scratch buffer. Public is harmless: a length is not a capability, and altering it only makes
    /// the precondition of [`Guarded::params`] unprovable.
    pub rlen: usize,
}

impl<P: TisPhy> Guarded<P> {
    pub closed spec fn xfer(&self) -> Xfer<P> {
        self.x
    }

    pub closed spec fn session(&self) -> AuthSession {
        self.sess
    }

    pub closed spec fn rsp_len(&self) -> usize {
        self.rlen
    }

    pub closed spec fn idle(&self) -> bool {
        self.xfer().idle()
    }

    pub closed spec fn usable(&self) -> bool {
        self.session().usable()
    }

    pub closed spec fn nonce_gen(&self) -> nat {
        self.session().nonce_gen@
    }

    pub closed spec fn session_key_material(&self) -> Seq<u8> {
        self.session().key_material()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.x.wf()
        &&& self.sess.wf()
        &&& self.rlen <= MSG_MAX
    }

    /// Valid bytes of the most recent response.
    ///
    /// Appears only in specs. The credential records this sequence at minting time, and reading parameters requires the two to be equal,
    /// so using an old credential to read a new response is blocked at the precondition -- no
    /// version number and no runtime check are needed.
    pub closed spec fn rsp_view(&self) -> Seq<u8> {
        self.rbuf@.subrange(0, self.rlen as int)
    }

    pub fn new(x: Xfer<P>, sess: AuthSession) -> (r: Self)
        ensures
            r.xfer() == x,
            r.session() == sess,
            r.rsp_len() == 0,
            r.rsp_view() =~= Seq::<u8>::empty(),
    {
        Guarded { x, sess, rbuf: [0u8; MSG_MAX], rlen: 0 }
    }

    // =======================================================================
    // The only entry point
    // =======================================================================

    /// Send an authorized command; returns only if the MAC matches.
    ///
    /// The caller must first write the message header, handle area and parameter area, and leave room for the authorization area according to `lay`.
    /// The authorization area is filled in by this function -- it contains this round's nonce, and the nonce is only produced at the moment of the exchange,
    /// so the caller cannot fill it in beforehand.
    ///
    /// Every failure path invalidates the session. Retrying with the same key after a session failure would give the other side one more chance to
    /// guess; after invalidation a fresh handshake is needed, which costs one round trip but keeps guess opportunities from accumulating.
    pub fn invoke<S: Sha256Ctx, H: HmacSha256Ctx, R: NonceSource>(
        &mut self,
        rng: &mut R,
        cmd: &mut [u8],
        lay: CmdLayout,
        names: &[u8],
        ordinal: u32,
        attrs: u8,
    ) -> (r: Result<Authenticated, SecErr>)
        requires
            old(self).wf(),
            old(self).idle(),
            old(self).usable(),
            old(self).nonce_gen() < old(rng).draws(),
            lay.wf(old(cmd).len() as int),
        ensures
            final(self).wf(),
            final(self).idle(),
            final(cmd).len() == old(cmd).len(),
            r matches Ok(t) ==> {
                // ★ A credential can only be minted after verification passes, so this is equivalent to
                //   "this function returns Ok if and only if the response went through MAC verification"
                &&& t.certified()
                &&& t.raw() =~= final(self).rsp_view()
                &&& t.key_material() =~= old(self).session_key_material()
                &&& t.ordinal() == ordinal
                &&& final(self).usable()
            },
    {
        let ghost key0 = self.sess.key_material();

        // ---- 1. Swap the nonce, lock in this round's command code and attributes ----
        self.sess.begin(rng, ordinal, attrs);
        let ghost nonce0 = self.sess.our_nonce@;
        let ghost attrs0 = self.sess.attrs;

        // ---- 2. Fill in the authorization area skeleton: handle, this round's nonce, attributes; leave the MAC field empty ----
        let handle = self.sess.handle;
        let nonce = self.sess.our_nonce;
        let sattrs = self.sess.attrs;
        write_cmd_session(cmd, lay.sess_off, handle, &nonce, sattrs);

        // ---- 3. Finalize: compute the MAC and fill it in ----
        //
        // Must happen after the parameters are written and before sending, with not a single byte of the message changed in between. The authorization area
        // lies entirely before the parameter area, so the writes of the previous step cannot land in the parameter area -- this is given by the
        // well-formedness of the layout and needs no byte-by-byte argument.
        self.sess.finalize::<S, H>(
            cmd,
            lay.sess_off,
            lay.index,
            names,
            lay.param_off,
            lay.param_len,
        );

        // ---- 4. Round trip ----
        let n = match self.x.run(&*cmd, lay.len, &mut self.rbuf) {
            Ok((n, rc)) => {
                if rc != RC_SUCCESS {
                    // A response with a non-zero return code has no authorization area and nothing to verify. It also should not
                    // be treated as a "verification failure" -- the two mean entirely different things to the caller.
                    self.sess.close();
                    return Err(SecErr::Rc(rc));
                }
                n
            },
            Err(e) => {
                self.sess.close();
                return Err(SecErr::Bus(e));
            },
        };
        self.rlen = n;

        // ---- 5. Verification ----
        //
        // The message is truncated to its self-declared length before being handed to verification: the self-consistency check of the authorization area is based on "the MAC extends all
        // the way to the end of the message", and a scratch-buffer tail with even one extra byte would defeat that check.
        let raw = &self.rbuf[0..n];
        let a = match self.sess.check_response::<S, H>(raw, lay.rhandles) {
            Ok(a) => a,
            Err(e) => return Err(SecErr::Auth(e)),
        };

        proof {
            assert(raw@ =~= self.rsp_view());
        }

        Ok(
            Authenticated {
                a,
                raw: Ghost(raw@),
                key: Ghost(key0),
                ordinal: Ghost(ordinal),
                our_nonce: Ghost(nonce0),
                attrs: Ghost(attrs0),
                seal: (),
            },
        )
    }

    // =======================================================================
    // Using the response
    // =======================================================================

    /// Take out the parameter area of the response.
    ///
    /// This is the **only exit** through which response bytes leave this struct. The precondition requires presenting a credential matching the current
    /// scratch-buffer content: without a credential the bytes cannot be obtained, and neither can they with an expired credential.
    pub fn params<'a>(&'a self, t: &Authenticated) -> (r: &'a [u8])
        requires
            self.wf(),
            t.certified(),
            t.raw() =~= self.rsp_view(),
        ensures
            r@ =~= t.view().params(t.raw()),
    {
        let off = t.a.param_off;
        let len = t.a.param_len;

        proof {
            // Partition self-consistency puts the parameter area within the valid bytes, so taking the same segment from the whole scratch buffer
            // is the same as taking it from the valid bytes.
            assert(off + len <= self.rlen);
            assert(self.rbuf@.subrange(off as int, off + len) =~= t.raw().subrange(
                off as int,
                off + len,
            ));
        }

        &self.rbuf[off..off + len]
    }

    /// The length of the response parameter area. The credential has already fixed it, so there is no need to parse the message again before reading.
    pub fn param_len(&self, t: &Authenticated) -> (r: usize)
        ensures
            r == t.view().param_len,
    {
        t.a.param_len
    }

    /// Hand the link back, ending the authorization phase.
    ///
    /// The session disappears together with `self`, which is intended: a session that no longer holds the link has a broken nonce
    /// chain, and keeping it would only make "continuing to talk with an old session" look feasible at the type level.
    /// The response scratch buffer is released with it, so credentials minted earlier have no message left to read -- their
    /// preconditions require the message to be byte-for-byte the same as at minting time, and the message is gone.
    pub fn release(self) -> (r: Xfer<P>)
        ensures
            r == self.xfer(),
    {
        self.x
    }
}

} // verus!