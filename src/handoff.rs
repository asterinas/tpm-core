use crate::{
    chip::CtxIo,
    link::{ChipLink, LiveSet},
    phy::TisPhy,
    secure::Guarded,
    session::AuthSession,
    xfer::Xfer,
};

/// Connect a freshly booted link into a chip link with a ledger.
///
/// This is the only legal call site for `LiveSet::new()`, because the statement “the chip has no
/// loaded objects” is only true at this instant: the boot sequence has just completed startup, and the
/// power-on sequence cleared all transient storage before that. Calling it elsewhere turns that into an
/// ungrounded assertion.
///
/// Accordingly, a boot should be attached only once. Attaching the same device twice would create a
/// second empty ledger out of thin air, while the device may still retain the first ledgered state.
/// This discipline is enforced by the ownership of [`Xfer`]: there is only one link, and once it is
/// handed off, it cannot be called again.
pub fn attach<P: TisPhy>(x: Xfer<P>) -> ChipLink<P> {
    ChipLink {
        x,
        ledger: LiveSet::new(),
    }
}
/// Enter the context round-trip phase.
///
/// The ledger moves with the link into the adapter, after which the adapter owns it.
pub fn open_ctx<P: TisPhy>(link: ChipLink<P>) -> CtxIo<ChipLink<P>> {
    CtxIo::new(link)
}
/// Leave the context round-trip phase and recover the link and ledger.
///
/// The equality in the postcondition is the entire value of this layer: the number of handles handed
/// out matches the number of ledger entries recovered, no more and no less. This layer does not require
/// the ledger to be empty; requiring it to be empty would force callers to release all contexts before
/// every phase switch, even though the purpose of contexts is precisely to survive across such
/// boundaries.
///
/// It is possible for the chip to still hold handles the local side no longer tracks (for example, if a
/// flush command never reached the bus). That is a known and unrecoverable leak; its accounting is
/// already recorded at the link layer, and this layer does not re-handle it or wipe the ledger just
/// because it appears “unclean”.
pub fn close_ctx<P: TisPhy>(io: CtxIo<ChipLink<P>>) -> ChipLink<P> {
    io.release()
}
/// Enter the protected round-trip phase. The link is passed to the session, and the ledger stays in the
/// caller’s hands.
///
/// During this phase the ledger is parked and does not move with the link. This is justified by an
/// interval fact: the ledger records transient object handles, while the authorization phase adds session
/// handles; the two occupy disjoint ranges in the handle space and never collide. No matter how many
/// sessions are established in the authorization phase, they cannot reuse the same handle as an entry in
/// the ledger, so the ledger remains accurate even while no one is tracking it for a while.
///
/// This fact is conditional: the authorization phase must not issue load-type commands. If it does, a
/// new transient handle falls into the ledger’s managed range while no accounting is being done. That is
/// the only calling discipline, and it means the authorization phase and context swap-in/swap-out
/// cannot interleave; if they need to, return via [`to_plain`] first.
pub fn to_auth<P: TisPhy>(link: ChipLink<P>, sess: AuthSession) -> (Guarded<P>, LiveSet) {
    let ChipLink { x, ledger } = link;
    (Guarded::new(x, sess), ledger)
}
/// Leave the protected round-trip phase and reconnect the link and parked ledger.
///
/// The ledger in the argument must be the same one returned by [`to_auth`]. The type system cannot help
/// here: [`LiveSet`] is a zero-sized type, and two ledgers look identical at runtime; a caller could
/// compile a swap with another ledger. The real protection is ownership: the whole driver creates only
/// one ledger in [`attach`], and there is no second one to hand in.
pub fn to_plain<P: TisPhy>(g: Guarded<P>, ledger: LiveSet) -> ChipLink<P> {
    ChipLink {
        x: g.release(),
        ledger,
    }
}
