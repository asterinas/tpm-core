use vstd::prelude::*;

use super::handle::*;

verus! {

/// Slot states of the context table.
#[derive(Clone, Copy, PartialEq, Eq, Structural)]
pub enum CtxSlot {
    /// Free slot.
    Empty,
    /// The object content has been saved to the backup buffer; there is no corresponding handle on the chip.
    Saved,
    /// The slot holds a live physical handle.
    Live(u32),
}

/// The physical handle of a live slot.
pub open spec fn live_handle(s: CtxSlot) -> Option<u32> {
    match s {
        CtxSlot::Live(h) => Some(h),
        _ => None,
    }
}

/// Abstract state of the table. All fields are public, for upper layers to write specs.
pub struct TableView {
    pub ctx: Seq<CtxSlot>,
    pub sessions: Seq<u32>,
}

#[derive(Clone, Copy)]
pub struct SpaceTable {
    ctx: [CtxSlot; SLOTS],
    /// `0` means an empty slot.
    sessions: [u32; SLOTS],
}

impl SpaceTable {
    pub closed spec fn abs(&self) -> TableView {
        TableView { ctx: self.ctx@, sessions: self.sessions@ }
    }

    // -----------------------------------------------------------------------
    // Invariants
    // -----------------------------------------------------------------------

    pub open spec fn wf(&self) -> bool {
        let v = self.abs();
        &&& v.ctx.len() == SLOTS
        &&& v.sessions.len() == SLOTS
        // A handle held by a live slot must be a valid physical handle
        &&& forall|i: int|
            #![trigger v.ctx[i]]
            0 <= i < SLOTS && live_handle(v.ctx[i]).is_some()
                ==> valid_phandle(live_handle(v.ctx[i]).unwrap())
        // Physical handles of any two live slots are distinct -- the source of injectivity
        &&& forall|i: int, j: int|
            #![trigger v.ctx[i], v.ctx[j]]
            0 <= i < SLOTS && 0 <= j < SLOTS && i != j
                && live_handle(v.ctx[i]).is_some()
                ==> live_handle(v.ctx[i]) != live_handle(v.ctx[j])
        // Registered session handles are pairwise distinct
        &&& forall|i: int, j: int|
            #![trigger v.sessions[i], v.sessions[j]]
            0 <= i < SLOTS && 0 <= j < SLOTS && i != j && v.sessions[i] != 0u32
                ==> v.sessions[i] != v.sessions[j]
    }

    // -----------------------------------------------------------------------
    // Spec-level queries
    // -----------------------------------------------------------------------

    pub open spec fn slot(&self, i: int) -> CtxSlot {
        self.abs().ctx[i]
    }

    pub open spec fn session(&self, i: int) -> u32 {
        self.abs().sessions[i]
    }

    /// Whether physical handle `p` is already registered in the table.
    pub open spec fn has_phandle(&self, p: u32) -> bool {
        exists|i: int|
            #![trigger self.slot(i)]
            0 <= i < SLOTS && live_handle(self.slot(i)) == Some(p)
    }

    /// The mapping from virtual handles to physical handles. The semantic core of the whole module.
    pub open spec fn maps(&self, v: u32) -> Option<u32> {
        let i = slot_of(v);
        if is_transient(v) && 0 <= i < SLOTS {
            live_handle(self.slot(i))
        } else {
            None
        }
    }

    // -----------------------------------------------------------------------
    // Lemmas unfolding the existential quantifier
    //
    // `has_phandle` / `has_session` are in existential form, convenient for upper layers to write; maintaining the
    // invariants, however, needs the universal form "distinct at every slot". These two lemmas are the only bridge
    // between the two forms, and the three functions that write slots all start from them.
    // -----------------------------------------------------------------------

    pub proof fn lemma_no_phandle_pointwise(&self, p: u32)
        requires
            !self.has_phandle(p),
        ensures
            forall|k: int| #![trigger self.slot(k)] 0 <= k < SLOTS ==> live_handle(self.slot(k)) != Some(p),
    {
        assert forall|k: int| 0 <= k < SLOTS implies live_handle(#[trigger] self.slot(k)) != Some(p) by {
            if live_handle(self.slot(k)) == Some(p) {
                assert(self.has_phandle(p));
            }
        }
    }

    pub proof fn lemma_no_session_pointwise(&self, h: u32)
        requires
            !self.has_session(h),
        ensures
            forall|k: int| #![trigger self.session(k)] 0 <= k < SLOTS ==> self.session(k) != h,
    {
        assert forall|k: int| 0 <= k < SLOTS implies #[trigger] self.session(k) != h by {
            if self.session(k) == h {
                assert(self.has_session(h));
            }
        }
    }

    // -----------------------------------------------------------------------
    // Bijectivity
    // -----------------------------------------------------------------------

    /// The mapping is injective: two different virtual handles cannot point to the same physical handle.
    ///
    /// Isolation between spaces ultimately reduces to this property: the table of one space cannot yield a physical handle held by
    /// another space, because each of its virtual handles can only resolve to some slot
    /// within its own table.
    pub proof fn lemma_maps_injective(&self, a: u32, b: u32)
        requires
            self.wf(),
            self.maps(a).is_some(),
            self.maps(a) == self.maps(b),
        ensures
            a == b,
    {
        let ia = slot_of(a);
        let ib = slot_of(b);
        assert(is_transient(a) && 0 <= ia < SLOTS);
        assert(is_transient(b) && 0 <= ib < SLOTS);
        if ia != ib {
            assert(live_handle(self.slot(ia)).is_some());
            assert(live_handle(self.slot(ia)) != live_handle(self.slot(ib)));
            assert(false);
        }
        lemma_transient_slot_injective(a, b);
    }

    /// Immediately after registration, it resolves back to the original physical handle.
    pub proof fn lemma_intern_resolve(&self, i: int, p: u32)
        requires
            0 <= i < SLOTS,
            self.slot(i) == CtxSlot::Live(p),
        ensures
            self.maps(vhandle_of(i)) == Some(p),
    {
        lemma_slot_roundtrip(i);
        lemma_vhandle_is_transient(i);
    }

    // -----------------------------------------------------------------------
    // Construction and slot writes
    // -----------------------------------------------------------------------

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            forall|i: int| 0 <= i < SLOTS ==> r.slot(i) == CtxSlot::Empty,
            forall|i: int| 0 <= i < SLOTS ==> r.session(i) == 0u32,
    {
        SpaceTable { ctx: [CtxSlot::Empty; SLOTS], sessions: [0u32; SLOTS] }
    }

    /// Set a slot to free or saved. These two states carry no handle and never break the invariants.
    pub fn set_slot_free(&mut self, i: usize, saved: bool)
        requires
            old(self).wf(),
            i < SLOTS,
        ensures
            final(self).wf(),
            final(self).slot(i as int) == if saved { CtxSlot::Saved } else { CtxSlot::Empty },
            forall|k: int| #![trigger final(self).slot(k)] 0 <= k < SLOTS && k != i as int ==> final(self).slot(k) == old(self).slot(k),
            forall|k: int| #![trigger final(self).session(k)] 0 <= k < SLOTS ==> final(self).session(k) == old(self).session(k),
    {
        self.ctx[i] = if saved { CtxSlot::Saved } else { CtxSlot::Empty };
    }

    /// Set a slot to live. Requires the handle to be valid and not already registered.
    ///
    /// "Not already registered" is a precondition rather than a runtime check: the call sites (`intern`, the
    /// load path) have already looked the table up once, and checking again would be pure waste. Injectivity is carried by this
    /// precondition, introducing no trust assumption.
    pub fn set_slot_live(&mut self, i: usize, p: u32)
        requires
            old(self).wf(),
            i < SLOTS,
            valid_phandle(p),
            !old(self).has_phandle(p),
        ensures
            final(self).wf(),
            final(self).slot(i as int) == CtxSlot::Live(p),
            forall|k: int| #![trigger final(self).slot(k)] 0 <= k < SLOTS && k != i as int ==> final(self).slot(k) == old(self).slot(k),
            forall|k: int| #![trigger final(self).session(k)] 0 <= k < SLOTS ==> final(self).session(k) == old(self).session(k),
    {
        let ghost before = self.ctx@;
        proof {
            assert(old(self).wf());
            old(self).lemma_no_phandle_pointwise(p);
        }

        self.ctx[i] = CtxSlot::Live(p);

        proof {
            assert(self.ctx@ =~= before.update(i as int, CtxSlot::Live(p)));
            assert(self.sessions@ =~= old(self).sessions@);
            assert(self.abs().ctx.len() == SLOTS);
            assert(self.abs().sessions.len() == SLOTS);
            assert(old(self).wf());

            // Validity: the new slot is guaranteed by the precondition, the other slots keep their old values.
            assert forall|a: int|
                0 <= a < SLOTS && live_handle(#[trigger] self.slot(a)).is_some()
                implies valid_phandle(live_handle(self.slot(a)).unwrap()) by {
                if a == i as int {
                    assert(self.slot(a) == CtxSlot::Live(p));
                    assert(live_handle(self.slot(a)).unwrap() == p);
                    assert(valid_phandle(p));
                } else {
                    assert(self.slot(a) == old(self).slot(a));
                    assert(live_handle(self.slot(a)) == live_handle(old(self).slot(a)));
                    assert(live_handle(old(self).slot(a)).is_some());
                    assert(valid_phandle(live_handle(old(self).slot(a)).unwrap())) by {
                        assert(old(self).wf());
                    }
                }
            }

            // Injectivity: three cases, each reducing to "the handle of an old slot is not equal to p".
            assert forall|a: int, b: int|
                0 <= a < SLOTS && 0 <= b < SLOTS && a != b
                    && live_handle(#[trigger] self.slot(a)).is_some()
                implies live_handle(self.slot(a)) != live_handle(#[trigger] self.slot(b)) by {
                if a == i as int {
                    assert(live_handle(self.slot(a)) == Some(p));
                    assert(self.slot(b) == old(self).slot(b));
                    assert(live_handle(old(self).slot(b)) != Some(p));
                    assert(live_handle(self.slot(b)) == live_handle(old(self).slot(b)));
                } else if b == i as int {
                    assert(live_handle(self.slot(b)) == Some(p));
                    assert(self.slot(a) == old(self).slot(a));
                    assert(live_handle(old(self).slot(a)) != Some(p));
                    assert(live_handle(self.slot(a)) == live_handle(old(self).slot(a)));
                } else {
                    assert(self.slot(a) == old(self).slot(a));
                    assert(self.slot(b) == old(self).slot(b));
                    assert(live_handle(self.slot(a)) == live_handle(old(self).slot(a)));
                    assert(live_handle(self.slot(b)) == live_handle(old(self).slot(b)));
                }
            }

            assert forall|a: int, b: int|
                #![trigger self.session(a), self.session(b)]
                0 <= a < SLOTS && 0 <= b < SLOTS && a != b && self.session(a) != 0u32
                implies self.session(a) != self.session(b) by {
                assert(self.session(a) == old(self).session(a));
                assert(self.session(b) == old(self).session(b));
                assert(old(self).wf());
            }

            assert(self.wf()) by {
                let v = self.abs();
                assert(v.ctx.len() == SLOTS);
                assert(v.sessions.len() == SLOTS);

                assert forall|a: int|
                    #![trigger v.ctx[a]]
                    0 <= a < SLOTS && live_handle(v.ctx[a]).is_some()
                    implies valid_phandle(live_handle(v.ctx[a]).unwrap()) by {
                    assert(v.ctx[a] == self.slot(a));
                    assert(live_handle(self.slot(a)).is_some());
                    assert(valid_phandle(live_handle(self.slot(a)).unwrap()));
                }

                assert forall|a: int, b: int|
                    #![trigger v.ctx[a], v.ctx[b]]
                    0 <= a < SLOTS && 0 <= b < SLOTS && a != b && live_handle(v.ctx[a]).is_some()
                    implies live_handle(v.ctx[a]) != live_handle(v.ctx[b]) by {
                    assert(v.ctx[a] == self.slot(a));
                    assert(v.ctx[b] == self.slot(b));
                    assert(live_handle(self.slot(a)).is_some());
                    assert(live_handle(self.slot(a)) != live_handle(self.slot(b)));
                }

                assert forall|a: int, b: int|
                    #![trigger v.sessions[a], v.sessions[b]]
                    0 <= a < SLOTS && 0 <= b < SLOTS && a != b && v.sessions[a] != 0u32
                    implies v.sessions[a] != v.sessions[b] by {
                    assert(v.sessions[a] == self.session(a));
                    assert(v.sessions[b] == self.session(b));
                    assert(self.session(a) != 0u32);
                    assert(self.session(a) != self.session(b));
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Query and allocation
    // -----------------------------------------------------------------------

    /// Virtual handle -> physical handle.
    pub fn resolve(&self, v: u32) -> (r: Option<u32>)
        requires
            self.wf(),
        ensures
            r == self.maps(v),
    {
        if !is_transient_exec(v) {
            return None;
        }
        let i = slot_of_exec(v);
        if i >= SLOTS {
            return None;
        }
        match self.ctx[i] {
            CtxSlot::Live(p) => Some(p),
            _ => None,
        }
    }

    /// Physical handle -> virtual handle; query only, no allocation.
    pub fn lookup(&self, p: u32) -> (r: Option<u32>)
        requires
            self.wf(),
            valid_phandle(p),
        ensures
            r.is_some() ==> self.maps(r.unwrap()) == Some(p),
            r.is_none() ==> !self.has_phandle(p),
    {
        for i in 0..SLOTS
            invariant
                self.wf(),
                valid_phandle(p),
                forall|k: int| #![trigger self.slot(k)] 0 <= k < i ==> live_handle(self.slot(k)) != Some(p),
        {
            if self.ctx[i] == CtxSlot::Live(p) {
                proof {
                    self.lemma_intern_resolve(i as int, p);
                }
                return Some(vhandle_of_exec(i));
            }
        }
        None
    }

    /// Allocate a free slot for a physical handle and return the corresponding virtual handle.
    ///
    /// Returns `None` when the table is full; the caller is then **obliged** to release this physical handle on the chip,
    /// otherwise it keeps occupying chip resources forever and can never be referenced again.
    pub fn intern(&mut self, p: u32) -> (r: Option<u32>)
        requires
            old(self).wf(),
            valid_phandle(p),
            !old(self).has_phandle(p),
        ensures
            final(self).wf(),
            forall|k: int| #![trigger final(self).session(k)] 0 <= k < SLOTS ==> final(self).session(k) == old(self).session(k),
            r.is_some() ==> final(self).maps(r.unwrap()) == Some(p),
            r.is_none() ==> final(self).abs() == old(self).abs(),
    {
        for i in 0..SLOTS
            invariant
                self.wf(),
                valid_phandle(p),
                !self.has_phandle(p),
                self.abs() == old(self).abs(),
        {
            if self.ctx[i] == CtxSlot::Empty {
                self.set_slot_live(i, p);
                proof {
                    self.lemma_intern_resolve(i as int, p);
                }
                return Some(vhandle_of_exec(i));
            }
        }
        None
    }

    // -----------------------------------------------------------------------
    // Session table
    // -----------------------------------------------------------------------

    pub open spec fn has_session(&self, h: u32) -> bool {
        exists|i: int| #![trigger self.session(i)] 0 <= i < SLOTS && self.session(i) == h
    }

    /// Register a session handle. Returns `false` when the table is full; the caller is likewise obliged to release it.
    pub fn add_session(&mut self, h: u32) -> (r: bool)
        requires
            old(self).wf(),
            h != 0u32,
            !old(self).has_session(h),
        ensures
            final(self).wf(),
            forall|k: int| #![trigger final(self).slot(k)] 0 <= k < SLOTS ==> final(self).slot(k) == old(self).slot(k),
            r ==> final(self).has_session(h),
            !r ==> final(self).abs() == old(self).abs(),
    {
        for i in 0..SLOTS
            invariant
                self.wf(),
                h != 0u32,
                !self.has_session(h),
                self.abs() == old(self).abs(),
        {
            if self.sessions[i] == 0 {
                let ghost before = self.sessions@;
                let ghost prev = *self;
                proof {
                    assert(prev.wf());
                    prev.lemma_no_session_pointwise(h);
                }

                self.sessions[i] = h;

                proof {
                    assert(self.sessions@ =~= before.update(i as int, h));
                    assert(self.ctx@ =~= prev.ctx@);
                    assert(self.abs().ctx.len() == SLOTS);
                    assert(self.abs().sessions.len() == SLOTS);
                    assert(prev.wf());

                    assert forall|k: int| #![trigger prev.session(k)] 0 <= k < SLOTS ==> prev.session(k) != h by {
                        assert(!prev.has_session(h));
                        prev.lemma_no_session_pointwise(h);
                    }

                    assert forall|a: int|
                        0 <= a < SLOTS && live_handle(#[trigger] self.slot(a)).is_some()
                        implies valid_phandle(live_handle(self.slot(a)).unwrap()) by {
                        assert(self.slot(a) == prev.slot(a));
                        assert(live_handle(prev.slot(a)).is_some());
                        assert(live_handle(self.slot(a)) == live_handle(prev.slot(a)));
                        assert(live_handle(prev.slot(a)).is_some());
                        assert(valid_phandle(live_handle(prev.slot(a)).unwrap())) by {
                            assert(prev.wf());
                        }
                    }

                    assert forall|a: int, b: int|
                        #![trigger self.slot(a), self.slot(b)]
                        0 <= a < SLOTS && 0 <= b < SLOTS && a != b
                            && live_handle(self.slot(a)).is_some()
                        implies live_handle(self.slot(a)) != live_handle(self.slot(b)) by {
                        assert(self.slot(a) == prev.slot(a));
                        assert(self.slot(b) == prev.slot(b));
                        assert(prev.wf());
                    }

                    // Pairwise distinct: the newly written h differs from any old value, and the old values keep the old invariant among themselves.
                    assert forall|a: int, b: int|
                        0 <= a < SLOTS && 0 <= b < SLOTS && a != b && #[trigger] self.session(a) != 0u32
                        implies self.session(a) != #[trigger] self.session(b) by {
                        if a == i as int {
                            assert(self.session(b) == prev.session(b));
                            assert(prev.session(b) != h);
                        } else if b == i as int {
                            assert(self.session(a) == prev.session(a));
                            assert(prev.session(a) != h);
                        } else {
                            assert(self.session(a) == prev.session(a));
                            assert(self.session(b) == prev.session(b));
                        }
                    }
                    // Existence witness: slot i is it.
                    assert(self.session(i as int) == h);
                    assert(self.has_session(h));

                    assert(self.wf()) by {
                        let v = self.abs();
                        assert(v.ctx.len() == SLOTS);
                        assert(v.sessions.len() == SLOTS);

                        assert forall|a: int|
                            #![trigger v.ctx[a]]
                            0 <= a < SLOTS && live_handle(v.ctx[a]).is_some()
                            implies valid_phandle(live_handle(v.ctx[a]).unwrap()) by {
                            assert(v.ctx[a] == self.slot(a));
                            assert(live_handle(self.slot(a)).is_some());
                            assert(valid_phandle(live_handle(self.slot(a)).unwrap()));
                        }

                        assert forall|a: int, b: int|
                            #![trigger v.ctx[a], v.ctx[b]]
                            0 <= a < SLOTS && 0 <= b < SLOTS && a != b && live_handle(v.ctx[a]).is_some()
                            implies live_handle(v.ctx[a]) != live_handle(v.ctx[b]) by {
                            assert(v.ctx[a] == self.slot(a));
                            assert(v.ctx[b] == self.slot(b));
                            assert(live_handle(self.slot(a)).is_some());
                            assert(live_handle(self.slot(a)) != live_handle(self.slot(b)));
                        }

                        assert forall|a: int, b: int|
                            #![trigger v.sessions[a], v.sessions[b]]
                            0 <= a < SLOTS && 0 <= b < SLOTS && a != b && v.sessions[a] != 0u32
                            implies v.sessions[a] != v.sessions[b] by {
                            assert(v.sessions[a] == self.session(a));
                            assert(v.sessions[b] == self.session(b));
                            assert(self.session(a) != 0u32);
                            assert(self.session(a) != self.session(b));
                        }
                    }
                }
                return true;
            }
        }
        false
    }

    pub fn has_session_exec(&self, h: u32) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == self.has_session(h),
    {
        for i in 0..SLOTS
            invariant
                self.wf(),
                forall|k: int| #![trigger self.session(k)] 0 <= k < i ==> self.session(k) != h,
        {
            if self.sessions[i] == h {
                proof {
                    assert(self.session(i as int) == h);
                    assert(self.has_session(h));
                }
                return true;
            }
        }
        proof {
            assert forall|k: int| 0 <= k < SLOTS implies #[trigger] self.session(k) != h by {}
        }
        false
    }

    pub fn session_at(&self, i: usize) -> (r: u32)
        requires
            self.wf(),
            i < SLOTS,
        ensures
            r == self.session(i as int),
    {
        self.sessions[i]
    }

    pub fn clear_session(&mut self, i: usize)
        requires
            old(self).wf(),
            i < SLOTS,
        ensures
            final(self).wf(),
            final(self).session(i as int) == 0u32,
            forall|k: int| #![trigger final(self).session(k)] 0 <= k < SLOTS && k != i as int ==> final(self).session(k) == old(self).session(k),
            forall|k: int| #![trigger final(self).slot(k)] 0 <= k < SLOTS ==> final(self).slot(k) == old(self).slot(k),
    {
        self.sessions[i] = 0;
    }

    pub fn slot_at(&self, i: usize) -> (r: CtxSlot)
        requires
            self.wf(),
            i < SLOTS,
        ensures
            r == self.slot(i as int),
    {
        self.ctx[i]
    }
}

} // verus!