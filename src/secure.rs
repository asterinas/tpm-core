use crate::{
    auth::{write_cmd_session, AuthErr, RspAuth},
    chip::MSG_MAX,
    crypto::{HmacSha256Ctx, NonceSource, Sha256Ctx},
    phy::TisPhy,
    session::AuthSession,
    xfer::{Xfer, XferErr, RC_SUCCESS},
};

/// Partition of an authorized command within the buffer.
///
/// This is provided by the caller rather than inferred by this layer: the partition depends on how
/// many handles the command has and how its parameters are arranged, which is command-layer
/// knowledge. This layer is responsible only for checking that these partitions do not overlap and
/// then filling them in.
pub struct CmdLayout {
    /// Total command length. It must match the length field in the packet header; this is checked by
    /// the link layer.
    pub len: usize,
    /// Start of the authorization area.
    pub sess_off: usize,
    /// This session's index within the authorization area.
    pub index: usize,
    /// Start of the parameter area.
    pub param_off: usize,
    /// Length of the parameter area.
    pub param_len: usize,
    /// Number of handles in the response. The digest covers the portion after the handles, and if this
    /// count is wrong, the entire offset layout becomes wrong.
    pub rhandles: usize,
}
/// A credential certifying that “this response MAC matches”.
///
/// The location result `a` can be made public: reading a few offsets does not create any capability; the
/// capability lies in the credential itself. The credential is created only after [`Guarded::invoke`]
/// validates successfully, and `#[non_exhaustive]` prevents external code from constructing one out of
/// thin air.
#[non_exhaustive]
pub struct Authenticated {
    pub a: RspAuth,
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SecErr {
    /// Bytes did not complete a full round trip.
    Bus(XferErr),
    /// The device returned a non-zero return code. This type of response has no authorization area and
    /// cannot be validated.
    Rc(u32),
    /// The response arrived, but authorization validation failed.
    Auth(AuthErr),
}
pub struct Guarded<P: TisPhy> {
    x: Xfer<P>,
    sess: AuthSession,
    /// Response buffer. All guarantees of this layer rely on the fact that the caller outside the module
    /// cannot access it.
    rbuf: [u8; MSG_MAX],
}
impl<P: TisPhy> Guarded<P> {
    pub fn new(x: Xfer<P>, sess: AuthSession) -> Self {
        Guarded {
            x,
            sess,
            rbuf: [0u8; MSG_MAX],
        }
    }
    /// Send an authorized command; it returns only if the MAC matches.
    ///
    /// The caller must have already prepared the packet header, handle area, and parameter area and must
    /// leave space for the authorization area according to `lay`. The authorization area is filled by
    /// this function; it contains the current nonce, which is generated only when the round is finalized,
    /// so the caller cannot fill it in advance.
    ///
    /// All failure paths invalidate the session. Retrying with the same key after the session has failed
    /// gives the peer one more guessing opportunity; invalidating it forces a fresh handshake, which costs
    /// one round trip but prevents guessing opportunities from accumulating.
    pub fn invoke<S: Sha256Ctx, H: HmacSha256Ctx, R: NonceSource>(
        &mut self,
        rng: &mut R,
        cmd: &mut [u8],
        lay: CmdLayout,
        names: &[u8],
        ordinal: u32,
        attrs: u8,
    ) -> Result<Authenticated, SecErr> {
        self.sess.begin(rng, ordinal, attrs);
        let handle = self.sess.handle();
        let nonce = self.sess.our_nonce();
        let sattrs = self.sess.attrs();
        write_cmd_session(cmd, lay.sess_off, handle, &nonce, sattrs);
        self.sess.finalize::<S, H>(
            cmd,
            lay.sess_off,
            lay.index,
            names,
            lay.param_off,
            lay.param_len,
        );
        let n = match self.x.run(&*cmd, lay.len, &mut self.rbuf) {
            Ok((n, rc)) => {
                if rc != RC_SUCCESS {
                    self.sess.close();
                    return Err(SecErr::Rc(rc));
                }
                n
            }
            Err(e) => {
                self.sess.close();
                return Err(SecErr::Bus(e));
            }
        };
        let raw = &self.rbuf[0..n];
        let a = match self.sess.check_response::<S, H>(raw, lay.rhandles) {
            Ok(a) => a,
            Err(e) => return Err(SecErr::Auth(e)),
        };
        Ok(Authenticated { a })
    }
    /// Extract the parameter area from the response.
    ///
    /// This is the **only exit** for response bytes from this structure. The precondition requires a
    /// credential matching the current temporary buffer contents; without a credential, the bytes cannot
    /// be obtained, and an expired credential also prevents access.
    pub fn params<'a>(&'a self, t: &Authenticated) -> &'a [u8] {
        let off = t.a.param_off;
        let len = t.a.param_len;
        &self.rbuf[off..off + len]
    }
    /// Length of the response parameter area. The credential has already fixed this value, so there is
    /// no need to parse the packet again before reading it.
    pub fn param_len(&self, t: &Authenticated) -> usize {
        t.a.param_len
    }
    /// Return the link and end the authorized phase.
    ///
    /// The session disappears together with `self`, which is exactly what we want: a session that no
    /// longer holds the link has a broken nonce chain, and leaving it behind would make it appear
    /// type-wise valid to keep speaking with an old session.
    /// The response buffer is released as well, and the previously created credentials no longer have a
    /// matching packet to read. Their preconditions require the packet to match byte-for-byte the
    /// contents at creation time, and that packet is no longer present.
    pub fn release(self) -> Xfer<P> {
        self.x
    }
}
