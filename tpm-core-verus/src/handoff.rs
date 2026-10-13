use vstd::prelude::*;
use vstd::set::Set;

use crate::chip::CtxIo;
use crate::link::{ChipLink, LiveSet};
use crate::module::ContextIo;
use crate::phy::TisPhy;
use crate::secure::Guarded;
use crate::session::AuthSession;
use crate::xfer::Xfer;

verus! {

// ===========================================================================
// What this layer is responsible for
// ===========================================================================
//
// Up to this point each layer holds on its own, but they make mutually exclusive demands on the same thing: there is only one transport link
// in the whole driver, and both the context round trip ([`CtxIo`]) and the authorized round trip ([`Guarded`]) need
// exclusive use of it. This is no oversight in interface design -- only one party can really talk on the bus at a time.
//
// Ownership expresses this constraint exactly: the link is **handed over** between the two phases rather than **shared**,
// and a party that does not hold it cannot send even a single command. This layer is just those handoff actions and does
// nothing else.
//
// ---------------------------------------------------------------------------
// What really matters is the ledger, not the link
// ---------------------------------------------------------------------------
//
// The link is a runtime object, and handing it over is merely moving a few bytes. The ghost ledger [`LiveSet`] is different:
// it takes no space once compiled, yet carries the most substantive assumption in the whole proof chain -- "a handle the chip has just reported
// was not valid before". The injectivity of the upper-layer handle table ultimately reduces to it.
//
// Hence an iron rule: **the ledger must be passed along across phases and must never be rebuilt midway**.
//
// The temptation to rebuild is direct: drop the ledger at handoff and call `LiveSet::new()` in the next phase;
// the code is much shorter and it compiles just the same. But that `new()` declares "the chip has nothing
// loaded right now", and the chip does not spit out its contexts just because this side changed holder. Once declaration and fact
// part ways, every later "this handle is new" may be a lie, and the injectivity of the handle table
// is built on exactly that sentence -- two virtual handles in the table would map to the same real handle, and the isolation
// between spaces would be gone.
//
// So every function in this layer takes the ledger over as is and hands it out as is, with the signature stating that before and after are equal.
// [`attach`] is the **only** legitimate starting point of the ledger in the whole driver; see its own note for the reason.

// ===========================================================================
// Starting point
// ===========================================================================

/// Connect a freshly booted link into a chip link carrying a ledger.
///
/// This is the only legitimate call site of `LiveSet::new()`, because the statement "the chip has nothing loaded"
/// is true only at this moment: the boot sequence has just let the device finish starting, and the earlier power-up sequence cleared all
/// transient storage. Called anywhere else, that statement becomes an unfounded assertion.
///
/// Accordingly, attach only once per boot. Attaching a second time to the same device would conjure a second empty ledger out of thin air,
/// while the device may well still hold what the first ledger recorded. This discipline is secured by the ownership of [`Xfer`]:
/// there is only one link, and once handed out it can no longer be called.
pub fn attach<P: TisPhy>(x: Xfer<P>) -> (r: ChipLink<P>)
    ensures
        r.x == x,
        r.ledger.view() == Set::<u32>::empty(),
{
    ChipLink { x, ledger: LiveSet::new() }
}

// ===========================================================================
// Session-less phase
// ===========================================================================

/// Enter the context round-trip phase.
///
/// The ledger enters the adapter together with the link, and is thereafter held by the adapter on the caller's behalf.
pub fn open_ctx<P: TisPhy>(link: ChipLink<P>) -> (r: CtxIo<ChipLink<P>>)
    ensures
        r.outstanding() == link.ledger.view(),
{
    CtxIo::new(link)
}

/// Leave the context round-trip phase, taking back the link and the ledger.
///
/// The equality in the postcondition is the whole value of this layer: however many handles were handed out, the ledger taken back
/// records exactly that many, no more and no fewer. It is **not required that the ledger be empty** -- requiring that would be like
/// forcing the caller to release all contexts before every phase switch, while the whole point of a context is
/// to survive across such boundaries.
///
/// The chip may indeed retain handles this side no longer tracks (this happens when a release command fails to reach the bus).
/// That is a known leak with no remedy, its books were already settled in the link layer, and this layer
/// does not handle it again, let alone wipe the ledger and start over because things "look unclean".
pub fn close_ctx<P: TisPhy>(io: CtxIo<ChipLink<P>>) -> (r: ChipLink<P>)
    ensures
        r.ledger.view() == io.outstanding(),
{
    io.release()
}

// ===========================================================================
// Authorization phase
// ===========================================================================

/// Enter the protected round-trip phase. The link goes to the session, and the ledger is parked in the caller's hands.
///
/// The ledger is set aside in this phase and does not travel with the link. This stands up thanks to an interval
/// fact: the ledger records transient object handles, while the authorization phase adds session handles, and the two lie in non-overlapping
/// segments of the handle space. However many sessions the authorization phase establishes, it cannot produce a handle that collides with
/// any entry on the ledger, so the ledger does not become inaccurate because "nobody kept the books during this time".
///
/// This fact has a precondition: **no load-type command may be issued during the authorization phase**. If one is, the new transient handle
/// falls into the interval the ledger governs, and nobody is keeping the books at that time. The calling discipline is just this one rule, at the cost that the authorization
/// phase cannot be interleaved with context swap-in/out -- when interleaving is needed, come back through [`to_plain`] first.
pub fn to_auth<P: TisPhy>(link: ChipLink<P>, sess: AuthSession) -> (r: (Guarded<P>, LiveSet))
    ensures
        r.0.xfer() == link.x,
        r.0.session() == sess,
        r.1.view() == link.ledger.view(),
{
    #[allow(non_shorthand_field_patterns)]
    let ChipLink { x, ledger } = link;
    (Guarded::new(x, sess), ledger)
}

/// Leave the protected round-trip phase, reuniting the link with the parked ledger.
///
/// The ledger in the argument must be the one [`to_auth`] handed out. The type system cannot help here --
/// [`LiveSet`] is a zero-sized type, the two ledgers look identical at runtime, and a caller can swap in another one
/// and it still compiles. What really prevents this is ownership: the whole driver creates a ledger only at [`attach`],
/// so there is no second one to take.
pub fn to_plain<P: TisPhy>(g: Guarded<P>, ledger: LiveSet) -> (r: ChipLink<P>)
    ensures
        r.x == g.xfer(),
        r.ledger.view() == ledger.view(),
{
    ChipLink { x: g.release(), ledger }
}

// ===========================================================================
// One complete cycle of phase transitions
// ===========================================================================
//
// Chaining the four functions above, the driver's lifecycle is a line like this:
//
// ```text
//   bring_up            -> Xfer
//   attach              -> ChipLink            the ledger is created here, once and only once
//     open_ctx          -> CtxIo               load / save / release contexts
//     close_ctx         -> ChipLink
//     to_auth           -> Guarded + LiveSet   authorized business commands
//     to_plain          -> ChipLink
//     ...                                      the middle two pairs may alternate any number of times
// ```
//
// The middle four steps can alternate repeatedly, and the ledger is passed along this line and never rebuilt. Each end of the line has
// one action that cannot be repeated: the start is [`attach`] and the end is dropping -- the end needs no function, because
// dropping a `ChipLink` requires nothing to be done anyway. Whatever is left on the chip is cleaned up by the next power-up,
// which is the only truly reliable means of cleanup.

} // verus!
