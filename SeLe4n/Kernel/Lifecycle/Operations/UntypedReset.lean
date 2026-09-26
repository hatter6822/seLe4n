-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.RetypeWrappers
import SeLe4n.Kernel.Architecture.PageTeardown

/-!
# The untyped reset — memory returns to the untyped it was carved from

**WS-BP BP7.1, slice 3 (`v0.36.6`); carved subtrees at slice 4 (`v0.36.8`).**
Slice 2 made memory reachable only by a carve (`untypedRetypeObject`); this
module is the other half of seL4's untyped life cycle, `resetUntypedCap`: once
nothing can reach any object carved from an untyped, the untyped's memory is
handed back to it and may be carved again.

## Which objects the reset retires

Everything whose memory is the untyped's: its **carved subtree**
(`untypedCarvedSubtree`) — the objects on its child list, and, since slice 4
carves child untypeds, the objects on theirs, at any depth.  The subtree is
derived by a bounded walk over the child lists and proved to contain every child
and to be closed (`untypedCarvedSubtree_spec`); a walk that cannot finish is a
refusal, never a smaller subtree.  Retiring the whole subtree in one reset is
what seL4 does implicitly — revoking an untyped capability deletes every
capability derived from it, a child untyped's included, and the reset then
rewinds the free index over memory no capability names — and it is forced here:
revoking the parent capability also destroys the child untyped's capabilities,
so a design that required each child to be reset first would leave the parent
unresettable for good.

## What "nothing can reach" means, and why it is decided over the whole store

In seL4 each untyped capability carries its own free index, so "no child
capability survives" is `ensureNoChildren` on the invoked slot.  This model keeps
the watermark on the untyped **object**, shared by every capability to it — which
is what stops two copies of one untyped capability from carving one page twice —
so the per-slot test is not sufficient here: a sibling copy's children are not
CDT descendants of the invoked slot.  The question is therefore asked of the
objects themselves (`carvedSubtreeUnreferenced`): no CNode slot, and no
capability parked in a blocked sender's message, names any object of the
subtree.

A capability is not the only way to reach memory.  A **mapping** is recorded on
the frame capability that made it (`Capability.mapping`, `v0.36.7`), and
destroying that capability removes it (`cspaceDeleteSlotFinalising`,
`cspaceRevokeCdtFinalising`) — but a record can go stale, since a VSpace
capability may unmap the address and a copy may map the frame again, so the
reset does not rely on the records.  It **finalises** the frames the way seL4's
`finaliseCap` does when the last frame capability goes: every mapping
of a page in the untyped's region is removed, through the one verified unmap the
`.vspaceUnmap` arm runs (`vspaceUnmapPageWithShootdownAndIcacheBroadcast` — the
page-table erase, the local flush, the `.vae1` shootdown round, the initiator's
own per-core drain and the instruction-cache broadcast for an executable page).
The mappings to remove are collected from the pre-state, and the result is
**checked**, not trusted (`untypedRegionUnmapped`): a mapping the collection
missed makes the reset refuse rather than hand the page out again.  Every frame
of the subtree lies in the region — a carve places each object inside its
parent's — and that too is decided (`carvedSubtreeFramesInRegion`), so the
region-wide pass reaches a frame at any depth
(`untypedReset_ok_retired_pages_unmapped`).

## What the reset writes

1. every mapping of a page meeting the region, removed (`unmapLivePages`, the
   page teardown this reset shares with a frame capability's destruction);
2. every object of the subtree **retired** — erased from the object store with
   its index and metadata rows (`retireCarvedObject`), so its object id and its
   store capacity return too.  Leaving a capless frame in the store would be
   unreachable but would consume a store slot per carve, and a holder of one
   small untyped could then exhaust the global object store by carving and
   resetting in a loop;
3. the untyped's watermark and child list cleared (`UntypedObject.reset`, the
   model's own reset, whose `reset_wellFormed` says the result is well formed).

No memory is zeroed here: the carve zeroes every RAM page before any capability
to it exists (`carveZeroFrame`), so a page is scrubbed exactly when it is handed
out, whatever happened to it in between.

## What it refuses

* an object of the subtree that is neither a frame nor an untyped
  (`.revocationRequired`) — the carve makes only those two, and a kernel object
  has no destroy operation that returns its memory;
* an object of the subtree some capability still names (`.revocationRequired`) —
  revoke the untyped capability (`.cspaceRevoke`), which reaches every
  capability derived from it, then reset;
* a subtree walk that cannot finish, a subtree naming the untyped itself, a
  frame of the subtree outside the region, a mapping of the region surviving
  the unmap pass, or an object table without the headroom an erase needs
  (`.illegalState`) — none is reachable on a well-formed state, and each is
  decided rather than assumed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The region, the carved subtree, and what names it
-- ============================================================================

/-- **Does the page at `p` meet the untyped's region?**  A mapping names the
base of one page, `[p, p + pageBytes)`; it reaches the untyped's memory exactly
when that page overlaps `[regionBase, regionBase + regionSize)`.  Asked as an
overlap rather than as "`p` lies in the region" so that no page straddling the
region's start can escape the test, whatever alignment the region has. -/
def _root_.SeLe4n.Model.UntypedObject.regionMeetsPage (ut : UntypedObject) (p : SeLe4n.PAddr) : Bool :=
  decide (p.toNat < ut.regionBase.toNat + ut.regionSize) &&
    decide (ut.regionBase.toNat < p.toNat + SeLe4n.pageBytes)

/-- **WS-BP BP7.1 slice 4 (`v0.36.8`): one step of the walk over an untyped's
carved subtree.**

A worklist walk: pop an id; if it was already visited skip it, otherwise record
it and, when it holds an untyped, push that untyped's own children.  So the
result is every object carved from the untyped, every object carved from those,
and so on — the objects whose memory is the untyped's.  `fuel` bounds the pops,
and running out is `none`, which the reset refuses rather than reading as a
smaller subtree: *a failed derivation is not an empty one*. -/
def carvedSubtreeWalk (st : SystemState) :
    Nat → List SeLe4n.ObjId → List SeLe4n.ObjId → Option (List SeLe4n.ObjId)
  | _, [], acc => some acc
  | 0, _ :: _, _ => none
  | fuel + 1, id :: rest, acc =>
    if id ∈ acc then carvedSubtreeWalk st fuel rest acc
    else
      match st.getUntyped? id with
      | some u => carvedSubtreeWalk st fuel (u.children.map (·.objId) ++ rest) (id :: acc)
      | none => carvedSubtreeWalk st fuel rest (id :: acc)

/-- **The walk's fuel.**  On a reachable state every child-list entry names a
live object and no object is listed twice — a carve's child id is fresh
(`retypeFromUntyped`'s collision guards), boot untypeds carry no children, and
a reset clears its untyped's list as it retires the objects the list names — so
the walk pops at most one entry per object and the store's capacity bounds it.
A state that needs more is refused, never truncated. -/
def carvedSubtreeFuel : Nat := maxObjects + 1

/-- **WS-BP BP7.1 slice 4: the carved subtree of an untyped** — every object
whose memory is the untyped's, at any depth (`carvedSubtreeWalk`), or `none`
when the walk cannot finish. -/
def untypedCarvedSubtree (st : SystemState) (ut : UntypedObject) : Option (List SeLe4n.ObjId) :=
  carvedSubtreeWalk st carvedSubtreeFuel (ut.children.map (·.objId)) []

/-- **A subtree is closed** when every untyped in it has its own children in
it — so nothing carved from a member lies outside. -/
def carvedSubtreeClosed (st : SystemState) (ids : List SeLe4n.ObjId) : Prop :=
  ∀ x ∈ ids, ∀ u, st.getUntyped? x = some u → ∀ c ∈ u.children, c.objId ∈ ids

/-- The walk's invariant: every visited untyped has each child visited or still
queued. -/
private def walkInv (st : SystemState) (acc work : List SeLe4n.ObjId) : Prop :=
  ∀ x ∈ acc, ∀ u, st.getUntyped? x = some u → ∀ c ∈ u.children, c.objId ∈ acc ∨ c.objId ∈ work

private theorem carvedSubtreeWalk_spec (st : SystemState) :
    ∀ (fuel : Nat) (work acc r : List SeLe4n.ObjId),
      carvedSubtreeWalk st fuel work acc = some r →
      (∀ x ∈ acc, x ∈ r) ∧ (∀ x ∈ work, x ∈ r) ∧ (walkInv st acc work → carvedSubtreeClosed st r)
  | _, [], acc, r, h => by
      simp only [carvedSubtreeWalk, Option.some.injEq] at h
      subst h
      refine ⟨?_, ?_, ?_⟩
      · intro x hx; exact hx
      · intro x hx; exact absurd hx List.not_mem_nil
      · intro hI x hx u hu c hc
        rcases hI x hx u hu c hc with h | h
        · exact h
        · exact absurd h List.not_mem_nil
  | 0, _ :: _, _, _, h => by simp [carvedSubtreeWalk] at h
  | fuel + 1, id :: rest, acc, r, h => by
      simp only [carvedSubtreeWalk] at h
      by_cases hMem : id ∈ acc
      · rw [if_pos hMem] at h
        obtain ⟨hA, hW, hC⟩ := carvedSubtreeWalk_spec st fuel rest acc r h
        refine ⟨hA, fun x hx => ?_, fun hI => hC fun x hx u hu c hc => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hA _ hMem
          · exact hW x hx
        · rcases hI x hx u hu c hc with h1 | h1
          · exact Or.inl h1
          · rcases List.mem_cons.mp h1 with h2 | h2
            · exact Or.inl (h2 ▸ hMem)
            · exact Or.inr h2
      · rw [if_neg hMem] at h
        cases hU : st.getUntyped? id with
        | some u =>
          rw [hU] at h
          obtain ⟨hA, hW, hC⟩ := carvedSubtreeWalk_spec st fuel _ _ r h
          refine ⟨fun x hx => hA x (List.mem_cons_of_mem _ hx), fun x hx => ?_,
            fun hI => hC fun x hx u' hu' c hc => ?_⟩
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hA _ List.mem_cons_self
            · exact hW x (List.mem_append_right _ hx)
          · rcases List.mem_cons.mp hx with rfl | hx
            · rw [hU] at hu'; cases hu'
              exact Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
            · rcases hI x hx u' hu' c hc with h1 | h1
              · exact Or.inl (List.mem_cons_of_mem _ h1)
              · rcases List.mem_cons.mp h1 with h2 | h2
                · exact Or.inl (h2 ▸ List.mem_cons_self)
                · exact Or.inr (List.mem_append_right _ h2)
        | none =>
          rw [hU] at h
          obtain ⟨hA, hW, hC⟩ := carvedSubtreeWalk_spec st fuel rest _ r h
          refine ⟨fun x hx => hA x (List.mem_cons_of_mem _ hx), fun x hx => ?_,
            fun hI => hC fun x hx u' hu' c hc => ?_⟩
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hA _ List.mem_cons_self
            · exact hW x hx
          · rcases List.mem_cons.mp hx with rfl | hx
            · rw [hU] at hu'; cases hu'
            · rcases hI x hx u' hu' c hc with h1 | h1
              · exact Or.inl (List.mem_cons_of_mem _ h1)
              · rcases List.mem_cons.mp h1 with h2 | h2
                · exact Or.inl (h2 ▸ List.mem_cons_self)
                · exact Or.inr h2

/-- **WS-BP BP7.1 slice 4: what the walk answers.**  The subtree contains every
child of the untyped, and it is closed: an untyped in it has all its own
children in it.  Together, every object carved from the untyped at any depth is
in the list — so a reset that retires the list leaves no object whose memory
was the untyped's. -/
theorem untypedCarvedSubtree_spec (st : SystemState) (ut : UntypedObject)
    (ids : List SeLe4n.ObjId) (h : untypedCarvedSubtree st ut = some ids) :
    (∀ c ∈ ut.children, c.objId ∈ ids) ∧ carvedSubtreeClosed st ids := by
  obtain ⟨-, hW, hC⟩ := carvedSubtreeWalk_spec st _ _ _ ids h
  exact ⟨fun c hc => hW _ (List.mem_map.mpr ⟨c, hc, rfl⟩),
    hC fun x hx => by cases hx⟩

/-- **Every object in the subtree is retirable**: a frame or an untyped.  The
reset retires memory and nothing else — a kernel object carved by the in-place
path has no operation here that returns its memory. -/
def carvedSubtreeRetirable (st : SystemState) (ids : List SeLe4n.ObjId) : Bool :=
  ids.all fun id => (st.getFrame? id).isSome || (st.getUntyped? id).isSome

/-- **Every frame in the subtree lies in the untyped's region.**  What makes the
region-wide unmap pass reach every retired page: a frame the carve placed
elsewhere would keep its mapping past the reset.  True of every reachable state
— a carve places each object inside its parent's region
(`untypedNextFrame_of_retype_ok`, `untypedNextChild_of_retype_ok`) — and decided
here rather than assumed. -/
def carvedSubtreeFramesInRegion (st : SystemState) (ut : UntypedObject)
    (ids : List SeLe4n.ObjId) : Bool :=
  ids.all fun id =>
    match st.getFrame? id with
    | some f => ut.regionMeetsPage f.base
    | none => true

/-- **Does this capability name an object in the subtree?**  Only an `.object`
target names an object; a CNode-slot, reply or audit-trail target names none. -/
def capNamesListed (ids : List SeLe4n.ObjId) (cap : Capability) : Bool :=
  match cap.target with
  | .object id => ids.contains id
  | _ => false

/-- **Does this stored object hold a capability naming an object in the
subtree?**  The two places a capability lives: a CNode slot, and the message a
blocked sender has parked (its transfer capabilities install at the receiver
later, so they are authority in flight).  No other object kind holds a
`Capability`. -/
def objectNamesListed (ids : List SeLe4n.ObjId) : KernelObject → Bool
  | .cnode cn => !(cn.slots.fold true (fun acc _ cap => acc && !capNamesListed ids cap))
  | .tcb t =>
      match t.pendingMessage with
      | some msg => msg.caps.any (fun tc => capNamesListed ids tc.cap)
      | none => false
  | _ => false

/-- **The whole-store check: no capability anywhere names an object in the
subtree.**  A conjunction folded over the object table, which is what makes the
payoff (`untypedReset_ok_unreferenced`) a statement about every key the table
resolves rather than about the keys an index happens to list. -/
def carvedSubtreeUnreferenced (st : SystemState) (ids : List SeLe4n.ObjId) : Bool :=
  st.objects.fold true (fun acc _ o => acc && !objectNamesListed ids o)

/-- **Does this VSpace root map no page meeting the region?** -/
def vspaceRootMapsNoPageOf (ut : UntypedObject) (root : VSpaceRoot) : Bool :=
  root.mappings.fold true (fun acc _ e => acc && !ut.regionMeetsPage e.1)

/-- **Does this stored object map no page meeting the region?**  Only a VSpace
root maps anything. -/
def objectMapsNoPageOf (ut : UntypedObject) : KernelObject → Bool
  | .vspaceRoot root => vspaceRootMapsNoPageOf ut root
  | _ => true

/-- **The whole-store check: no VSpace root maps a page of the region.** -/
def untypedRegionUnmapped (st : SystemState) (ut : UntypedObject) : Bool :=
  st.objects.fold true (fun acc _ o => acc && objectMapsNoPageOf ut o)

/-- **The mappings the unmap pass removes**: every `(asid, vaddr)` a VSpace root
maps to a page meeting the region, read off the pre-state.  Collected, not
trusted — `untypedRegionUnmapped` decides afterwards whether anything was
missed. -/
def untypedRegionMappings (st : SystemState) (ut : UntypedObject) :
    List MappedPage :=
  st.objects.fold [] (fun acc _ o =>
    match o with
    | .vspaceRoot root =>
        root.mappings.fold acc (fun acc' v e =>
          if ut.regionMeetsPage e.1 then
            { asid := root.asid, vaddr := v, paddr := e.1 } :: acc'
          else acc')
    | _ => acc)

-- ============================================================================
-- §2  The unmap pass
-- ============================================================================

-- The unmap pass is `unmapLivePages` (`Architecture/PageTeardown.lean`), with
-- the frames that say what it can change (`vspaceRootOnlyWrite`,
-- `unmapLivePages_ok_frame`): the one teardown this reset shares with a frame
-- capability's destruction, so the two cannot come to disagree about how a
-- mapping is removed.

-- ============================================================================
-- §3  Retiring a carved object
-- ============================================================================

/-- **Is the object at `oid` one a carve makes** — a frame or an untyped? -/
def carvedAt (st : SystemState) (oid : SeLe4n.ObjId) : Prop :=
  (∃ f, st.objects[oid]? = some (KernelObject.frame f)) ∨
    (∃ u, st.objects[oid]? = some (KernelObject.untyped u))

/-- **Erase a carved object — a frame or an untyped — from the object store**,
with its index row, its index-set entry and its object-type metadata.  A no-op
at a key holding anything else, so no other kind of object can be erased through
it: an erased TCB, Reply or SchedContext would leave every structure naming it
dangling, while a frame or an untyped is named only by capabilities, mappings
and its parent's child list — which the reset has already shown to be gone, or
is about to clear.  Neither kind registers an ASID, so the ASID table is
untouched.

*Tombstone:* `retireFrame` (`v0.36.6`–`v0.36.7`) was this primitive at frames
only; slice 4 (`v0.36.8`) retires child untypeds with the frames carved from
them. -/
def retireCarvedObject (st : SystemState) (id : SeLe4n.ObjId) : SystemState :=
  if (st.getFrame? id).isSome || (st.getUntyped? id).isSome then
    { st with
        objects := st.objects.erase id
        objectIndex := st.objectIndex.filter (· != id)
        objectIndexSet := st.objectIndexSet.erase id
        lifecycle := { objectTypes := st.lifecycle.objectTypes.erase id } }
  else st

/-- Retire every listed carved object, in order. -/
def retireCarvedObjects (st : SystemState) (ids : List SeLe4n.ObjId) : SystemState :=
  ids.foldl retireCarvedObject st

-- ============================================================================
-- §4  The reset
-- ============================================================================

/-- **WS-BP BP7.1 slice 3 (`v0.36.6`), subtrees at slice 4 (`v0.36.8`): reset an
untyped — seL4's `resetUntypedCap`.**

Six refusals, each committing nothing, then the three writes the module
docstring lists.  `executingCore` is the core the invoking thread runs on; it is
the initiator of every shootdown round the unmap pass posts. -/
def untypedReset (executingCore : Concurrency.CoreId) (untypedId : SeLe4n.ObjId) : Kernel Unit :=
  fun st =>
    match st.getUntyped? untypedId with
    | none => .error .untypedTypeMismatch
    | some ut =>
      match untypedCarvedSubtree st ut with
      | none => .error .illegalState
      | some ids =>
        if untypedId ∈ ids then .error .illegalState
        else if !carvedSubtreeRetirable st ids then .error .revocationRequired
        else if !carvedSubtreeFramesInRegion st ut ids then .error .illegalState
        else if !carvedSubtreeUnreferenced st ids then .error .revocationRequired
        else
          match unmapLivePages executingCore (untypedRegionMappings st ut) st with
          | .error e => .error e
          | .ok ((), st1) =>
            if !untypedRegionUnmapped st1 ut then .error .illegalState
            else if !decide (st1.objects.size < st1.objects.capacity) then .error .illegalState
            else
              storeObject untypedId (.untyped ut.reset) (retireCarvedObjects st1 ids)

-- ============================================================================
-- §5  Frames: what each step of the reset can change
-- ============================================================================

/-- The retire's guard, read back: it fires exactly at a carved object. -/
theorem retireCarvedObject_guard_iff (st : SystemState) (id : SeLe4n.ObjId) :
    ((st.getFrame? id).isSome || (st.getUntyped? id).isSome) = true ↔ carvedAt st id := by
  constructor
  · intro h
    rcases Bool.or_eq_true_iff.mp h with hF | hU
    · cases hG : st.getFrame? id with
      | none => rw [hG] at hF; cases hF
      | some f => exact Or.inl ⟨f, (SystemState.getFrame?_eq_some_iff st id f).mp hG⟩
    · cases hG : st.getUntyped? id with
      | none => rw [hG] at hU; cases hU
      | some u => exact Or.inr ⟨u, (SystemState.getUntyped?_eq_some_iff st id u).mp hG⟩
  · rintro (⟨f, hf⟩ | ⟨u, hu⟩)
    · simp [(SystemState.getFrame?_eq_some_iff st id f).mpr hf]
    · simp [(SystemState.getUntyped?_eq_some_iff st id u).mpr hu]

/-- **Retiring one carved object**: the key erased held a frame or an untyped;
every other key is unchanged.  Stated with the headroom an erase needs
(`size < capacity`), which the reset decides before it retires anything and
which an erase preserves. -/
theorem retireCarvedObject_frame (st : SystemState) (id : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt) (hSize : st.objects.size < st.objects.capacity) :
    (retireCarvedObject st id).objects.invExt ∧
    (retireCarvedObject st id).objects.size < (retireCarvedObject st id).objects.capacity ∧
    (retireCarvedObject st id).scheduler = st.scheduler ∧
    (∀ oid : SeLe4n.ObjId, (retireCarvedObject st id).objects[oid]? = st.objects[oid]? ∨
      (carvedAt st oid ∧ (retireCarvedObject st id).objects[oid]? = none)) ∧
    (st.objects[id]? = none ∨ carvedAt st id → (retireCarvedObject st id).objects[id]? = none) := by
  unfold retireCarvedObject
  by_cases hC : ((st.getFrame? id).isSome || (st.getUntyped? id).isSome) = true
  · rw [if_pos hC]
    have hAt := (retireCarvedObject_guard_iff st id).mp hC
    have hSelf : (st.objects.erase id)[id]? = none :=
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self st.objects id hObjInv
    refine ⟨SeLe4n.Kernel.RobinHood.RHTable.erase_preserves_invExt st.objects id hObjInv hSize,
      SeLe4n.Kernel.RobinHood.RHTable.erase_size_lt_capacity st.objects id hSize, rfl,
      fun oid => ?_, fun _ => hSelf⟩
    by_cases hK : oid = id
    · subst hK; exact Or.inr ⟨hAt, hSelf⟩
    · have hNe : ¬(id == oid) = true := by
        intro h; exact hK (eq_of_beq h).symm
      exact Or.inl (SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne st.objects id oid hNe
        hObjInv hSize)
  · rw [if_neg hC]
    refine ⟨hObjInv, hSize, rfl, fun _ => Or.inl rfl, ?_⟩
    rintro (h | hAt)
    · exact h
    · exact absurd ((retireCarvedObject_guard_iff st id).mpr hAt) hC

/-- **A carved-object retire write**: at every key the object is unchanged, or a
carved object that is now absent. -/
def carvedRetireWrite (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    (carvedAt st oid ∧ st'.objects[oid]? = none)

theorem carvedRetireWrite.refl (st : SystemState) : carvedRetireWrite st st :=
  fun _ => Or.inl rfl

theorem carvedRetireWrite.trans {s1 s2 s3 : SystemState}
    (hFirst : carvedRetireWrite s1 s2) (hSecond : carvedRetireWrite s2 s3) :
    carvedRetireWrite s1 s3 := by
  intro oid
  rcases hFirst oid with e12 | ⟨c1, n2⟩ <;> rcases hSecond oid with e23 | ⟨c2, n3⟩
  · exact Or.inl (e23.trans e12)
  · refine Or.inr ⟨?_, n3⟩
    unfold carvedAt at c2 ⊢; rw [← e12]; exact c2
  · exact Or.inr ⟨c1, by rw [e23]; exact n2⟩
  · exact Or.inr ⟨c1, n3⟩

/-- A key that holds something after a carved-object retire held the same thing
before. -/
theorem carvedRetireWrite.eq_of_isSome {st st' : SystemState}
    (h : carvedRetireWrite st st') {oid : SeLe4n.ObjId} {o : KernelObject}
    (hPost : st'.objects[oid]? = some o) : st.objects[oid]? = some o := by
  rcases h oid with e | ⟨_, hn⟩
  · rw [← e]; exact hPost
  · rw [hn] at hPost; cases hPost

/-- **Retiring a list of carved objects**: a carved-object retire write that
keeps the table's invariant and headroom and the scheduler, and after which
every listed key that held a carved object, or nothing, holds nothing. -/
theorem retireCarvedObjects_frame :
    ∀ (ids : List SeLe4n.ObjId) (st : SystemState),
      st.objects.invExt → st.objects.size < st.objects.capacity →
      (retireCarvedObjects st ids).objects.invExt ∧
      (retireCarvedObjects st ids).objects.size < (retireCarvedObjects st ids).objects.capacity ∧
      (retireCarvedObjects st ids).scheduler = st.scheduler ∧
      carvedRetireWrite st (retireCarvedObjects st ids) ∧
      (∀ id ∈ ids, (st.objects[id]? = none ∨ carvedAt st id) →
        (retireCarvedObjects st ids).objects[id]? = none)
  | [], st, hInv, hSize => by
      refine ⟨hInv, hSize, rfl, carvedRetireWrite.refl _, ?_⟩
      intro id hMem; cases hMem
  | h :: t, st, hInv, hSize => by
      have hFold : retireCarvedObjects st (h :: t) = retireCarvedObjects (retireCarvedObject st h) t := rfl
      obtain ⟨hInv1, hSize1, hSch1, hW1, hSelf1⟩ := retireCarvedObject_frame st h hInv hSize
      obtain ⟨hInv2, hSize2, hSch2, hW2, hNone2⟩ :=
        retireCarvedObjects_frame t (retireCarvedObject st h) hInv1 hSize1
      rw [hFold]
      refine ⟨hInv2, hSize2, hSch2.trans hSch1, carvedRetireWrite.trans hW1 hW2, ?_⟩
      intro id hMem hPre
      -- a key that held a carved object or nothing still does after one retire
      have hPre1 : (retireCarvedObject st h).objects[id]? = none ∨
          carvedAt (retireCarvedObject st h) id := by
        rcases hW1 id with e | ⟨_, hn⟩
        · rcases hPre with hp | hp
          · exact Or.inl (e.trans hp)
          · right; unfold carvedAt at hp ⊢; rw [e]; exact hp
        · exact Or.inl hn
      rcases List.mem_cons.mp hMem with hEq | hTail
      · subst hEq
        have hN1 := hSelf1 hPre
        rcases hW2 id with e | ⟨hc, _⟩
        · rw [e]; exact hN1
        · rcases hc with ⟨f, hf⟩ | ⟨u, hu⟩
          · rw [hN1] at hf; cases hf
          · rw [hN1] at hu; cases hu
      · exact hNone2 id hTail hPre1

-- ============================================================================
-- §6  What a successful reset consists of, and what it guarantees
-- ============================================================================

/-- **What a successful reset consists of** — its guards and its three writes,
read back.  One owner for the case analysis, so the theorems below and the
bundle proof read these equations rather than re-running the operation's
`match`. -/
theorem untypedReset_ok_decompose (ec : Concurrency.CoreId) (untypedId : SeLe4n.ObjId)
    (st st' : SystemState)
    (hStep : untypedReset ec untypedId st = .ok ((), st')) :
    ∃ (ut : UntypedObject) (ids : List SeLe4n.ObjId) (st1 : SystemState),
      st.getUntyped? untypedId = some ut ∧
      untypedCarvedSubtree st ut = some ids ∧
      untypedId ∉ ids ∧
      carvedSubtreeRetirable st ids = true ∧
      carvedSubtreeFramesInRegion st ut ids = true ∧
      carvedSubtreeUnreferenced st ids = true ∧
      unmapLivePages ec (untypedRegionMappings st ut) st = .ok ((), st1) ∧
      untypedRegionUnmapped st1 ut = true ∧
      st1.objects.size < st1.objects.capacity ∧
      storeObject untypedId (.untyped ut.reset) (retireCarvedObjects st1 ids) = .ok ((), st') := by
  unfold untypedReset at hStep
  cases hUt : st.getUntyped? untypedId with
  | none => rw [hUt] at hStep; cases hStep
  | some ut =>
    rw [hUt] at hStep
    simp only at hStep
    cases hW : untypedCarvedSubtree st ut with
    | none => rw [hW] at hStep; cases hStep
    | some ids =>
      rw [hW] at hStep
      simp only at hStep
      by_cases hK : untypedId ∈ ids
      · simp [hK] at hStep
      · cases hR : carvedSubtreeRetirable st ids
        · simp [hK, hR] at hStep
        cases hG : carvedSubtreeFramesInRegion st ut ids
        · simp [hK, hR, hG] at hStep
        cases hU : carvedSubtreeUnreferenced st ids
        · simp [hK, hR, hG, hU] at hStep
        simp only [hK, hR, hG, hU, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
        cases hM : unmapLivePages ec (untypedRegionMappings st ut) st with
        | error e => rw [hM] at hStep; cases hStep
        | ok pr =>
          obtain ⟨u, st1⟩ := pr; cases u
          rw [hM] at hStep
          simp only at hStep
          cases hC : untypedRegionUnmapped st1 ut
          · simp [hC] at hStep
          by_cases hSz : st1.objects.size < st1.objects.capacity
          · simp only [hC, hSz, decide_true, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte] at hStep
            exact ⟨ut, ids, st1, rfl, hW, hK, hR, hG, hU, hM, hC, hSz, hStep⟩
          · simp [hC, hSz] at hStep

/-- Every member of the subtree is a carved object at its key, and none is the
untyped's own key. -/
private theorem subtree_member {st : SystemState} {untypedId : SeLe4n.ObjId}
    {ids : List SeLe4n.ObjId} (hK : untypedId ∉ ids)
    (hR : carvedSubtreeRetirable st ids = true) {id : SeLe4n.ObjId} (hId : id ∈ ids) :
    id ≠ untypedId ∧ carvedAt st id :=
  ⟨fun hEq => hK (hEq ▸ hId),
    (retireCarvedObject_guard_iff st id).mp (List.all_eq_true.mp hR id hId)⟩

/-- The whole-reset frames, collected: the table invariant, the scheduler, the
unmap pass's VSpace-root-only write and the retire's carved-object retire
write. -/
private theorem untypedReset_ok_frames {ec : Concurrency.CoreId}
    {st st1 : SystemState} {ut : UntypedObject} {ids : List SeLe4n.ObjId}
    (hObjInv : st.objects.invExt)
    (hM : unmapLivePages ec (untypedRegionMappings st ut) st = .ok ((), st1))
    (hSz : st1.objects.size < st1.objects.capacity) :
    let st2 := retireCarvedObjects st1 ids
    st1.objects.invExt ∧ vspaceRootOnlyWrite st st1 ∧ st1.scheduler = st.scheduler ∧
    st2.objects.invExt ∧ st2.scheduler = st1.scheduler ∧ carvedRetireWrite st1 st2 ∧
    (∀ id ∈ ids, (st1.objects[id]? = none ∨ carvedAt st1 id) → st2.objects[id]? = none) := by
  obtain ⟨hInv1, hW1, hS1⟩ := unmapLivePages_ok_frame ec _ st st1 hObjInv hM
  obtain ⟨hInv2, -, hS2, hW2, hN2⟩ := retireCarvedObjects_frame ids st1 hInv1 hSz
  exact ⟨hInv1, hW1, hS1, hInv2, hS2, hW2, hN2⟩

/-- **After a reset the untyped holds its memory again**: watermark `0`, no
children, region, device flag and parent unchanged. -/
theorem untypedReset_ok_untyped (ec : Concurrency.CoreId) (untypedId : SeLe4n.ObjId)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedReset ec untypedId st = .ok ((), st')) :
    ∃ ut, st.getUntyped? untypedId = some ut ∧
      st'.objects[untypedId]? = some (.untyped ut.reset) := by
  obtain ⟨ut, ids, st1, hUt, -, -, -, -, -, hM, -, hSz, hSt⟩ :=
    untypedReset_ok_decompose ec untypedId st st' hStep
  obtain ⟨-, -, -, hInv2, -, -, -⟩ := untypedReset_ok_frames (ids := ids) hObjInv hM hSz
  exact ⟨ut, hUt, storeObject_objects_eq _ _ _ _ hInv2 hSt⟩

/-- **WS-BP BP7.1 slice 4 (`v0.36.8`): after a reset no object carved from the
untyped exists, at any depth.**  The reset retired its carved subtree, which
holds every child of the untyped and is closed — an untyped in it has all its
own children in it (`untypedCarvedSubtree_spec`) — and every member is gone from
the store, so its id and its store capacity are free again.  A frame carved from
a child untyped is retired with that child: the memory of the whole subtree is
the untyped's, and it returns in one reset.

*Tombstone:* `untypedReset_ok_children_absent` (`v0.36.6`–`v0.36.7`) was this
statement over the untyped's direct children, which were frames only. -/
theorem untypedReset_ok_subtree_absent (ec : Concurrency.CoreId) (untypedId : SeLe4n.ObjId)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedReset ec untypedId st = .ok ((), st')) :
    ∃ ut ids, st.getUntyped? untypedId = some ut ∧
      untypedCarvedSubtree st ut = some ids ∧
      (∀ c ∈ ut.children, c.objId ∈ ids) ∧ carvedSubtreeClosed st ids ∧
      ∀ id ∈ ids, st'.objects[id]? = none := by
  obtain ⟨ut, ids, st1, hUt, hWalk, hK, hR, -, -, hM, -, hSz, hSt⟩ :=
    untypedReset_ok_decompose ec untypedId st st' hStep
  obtain ⟨-, hW1, -, hInv2, -, -, hN2⟩ :=
    untypedReset_ok_frames (ids := ids) hObjInv hM hSz
  obtain ⟨hKids, hClosed⟩ := untypedCarvedSubtree_spec st ut ids hWalk
  refine ⟨ut, ids, hUt, hWalk, hKids, hClosed, fun id hId => ?_⟩
  obtain ⟨hNe, hC⟩ := subtree_member hK hR hId
  rw [storeObject_objects_ne _ _ _ _ _ hNe hInv2 hSt]
  have hNotRoot : ∀ r, st.objects[id]? ≠ some (.vspaceRoot r) := by
    intro r h; rcases hC with ⟨f, hf⟩ | ⟨u, hu⟩
    · rw [hf] at h; cases h
    · rw [hu] at h; cases h
  have hC1 : carvedAt st1 id := by
    unfold carvedAt; rw [hW1.eq_of_not_root hNotRoot]; exact hC
  exact hN2 id hId (Or.inr hC1)

/-- **After a reset no VSpace root maps a page of the region** — the check the
reset decides after its unmap pass, carried to the state it commits.  With the
subtree gone and the capabilities to it already gone, this is what makes a page
the reset hands back unreachable by any thread: the next carve's zeroed page is
the only name any thread will have for it. -/
theorem untypedReset_ok_unmapped (ec : Concurrency.CoreId) (untypedId : SeLe4n.ObjId)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedReset ec untypedId st = .ok ((), st')) :
    ∃ ut, st.getUntyped? untypedId = some ut ∧
      ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot) (v : SeLe4n.VAddr)
        (e : SeLe4n.PAddr × PagePermissions),
        st'.objects[oid]? = some (.vspaceRoot root) →
        root.mappings[v]? = some e → ut.regionMeetsPage e.1 = false := by
  obtain ⟨ut, ids, st1, hUt, -, -, -, -, -, hM, hC, hSz, hSt⟩ :=
    untypedReset_ok_decompose ec untypedId st st' hStep
  obtain ⟨-, -, -, hInv2, -, hW2, -⟩ :=
    untypedReset_ok_frames (ids := ids) hObjInv hM hSz
  refine ⟨ut, hUt, fun oid root v e hRoot hMap => ?_⟩
  have hNe : oid ≠ untypedId := by
    intro hEq; rw [hEq, storeObject_objects_eq _ _ _ _ hInv2 hSt] at hRoot; cases hRoot
  rw [storeObject_objects_ne _ _ _ _ _ hNe hInv2 hSt] at hRoot
  have hRoot1 := hW2.eq_of_isSome hRoot
  have hObj := SeLe4n.Kernel.RobinHood.RHTable.fold_and_true_of_get? st1.objects
    (fun _ o => objectMapsNoPageOf ut o) hC hRoot1
  have hE := SeLe4n.Kernel.RobinHood.RHTable.fold_and_true_of_get? root.mappings
    (fun _ e => !ut.regionMeetsPage e.1) hObj hMap
  simpa using hE

/-- **WS-BP BP7.1 slice 4 (`v0.36.8`): no retired frame's page is still mapped.**
Every frame in the subtree lies in the untyped's region (the reset decides it,
`carvedSubtreeFramesInRegion`), and no mapping of the region survives
(`untypedReset_ok_unmapped`) — so whatever depth a frame was carved at, the page
it named is mapped by no VSpace root once the reset commits. -/
theorem untypedReset_ok_retired_pages_unmapped (ec : Concurrency.CoreId)
    (untypedId : SeLe4n.ObjId) (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedReset ec untypedId st = .ok ((), st')) :
    ∃ ut ids, st.getUntyped? untypedId = some ut ∧ untypedCarvedSubtree st ut = some ids ∧
      ∀ id ∈ ids, ∀ f : FrameObject, st.objects[id]? = some (.frame f) →
        ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot) (v : SeLe4n.VAddr)
          (e : SeLe4n.PAddr × PagePermissions),
          st'.objects[oid]? = some (.vspaceRoot root) → root.mappings[v]? = some e →
          e.1 ≠ f.base := by
  obtain ⟨ut, ids, st1, hUt, hWalk, -, -, hG, -, -, -, -, -⟩ :=
    untypedReset_ok_decompose ec untypedId st st' hStep
  obtain ⟨ut', hUt', hUnm⟩ := untypedReset_ok_unmapped ec untypedId st st' hObjInv hStep
  rw [hUt] at hUt'; cases hUt'
  refine ⟨ut, ids, hUt, hWalk, fun id hId f hF oid root v e hRoot hMap hEq => ?_⟩
  have hIn := List.all_eq_true.mp hG id hId
  rw [(SystemState.getFrame?_eq_some_iff st id f).mpr hF] at hIn
  have hOff := hUnm oid root v e hRoot hMap
  rw [hEq] at hOff
  simp only at hIn
  rw [hIn] at hOff; cases hOff

/-- **After a reset no capability names an object of the subtree** — in no CNode
slot and in no message a blocked sender has parked.  The reset decided this of
its pre-state and writes neither CNodes nor TCBs, so the committed state
inherits it: once an id is reused by the next carve, no capability left over
from the retired object can name the new one. -/
theorem untypedReset_ok_unreferenced (ec : Concurrency.CoreId) (untypedId : SeLe4n.ObjId)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedReset ec untypedId st = .ok ((), st')) :
    ∃ ut ids, st.getUntyped? untypedId = some ut ∧ untypedCarvedSubtree st ut = some ids ∧
      (∀ (oid : SeLe4n.ObjId) (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability),
        st'.objects[oid]? = some (.cnode cn) → cn.lookup slot = some cap →
        capNamesListed ids cap = false) ∧
      (∀ (oid : SeLe4n.ObjId) (t : TCB) (msg : IpcMessage),
        st'.objects[oid]? = some (.tcb t) → t.pendingMessage = some msg →
        msg.caps.any (fun tc => capNamesListed ids tc.cap) = false) := by
  obtain ⟨ut, ids, st1, hUt, hWalk, -, -, -, hRef, hM, -, hSz, hSt⟩ :=
    untypedReset_ok_decompose ec untypedId st st' hStep
  obtain ⟨-, hW1, -, hInv2, -, hW2, -⟩ :=
    untypedReset_ok_frames (ids := ids) hObjInv hM hSz
  -- a CNode or TCB in the committed state was there, unchanged, in the pre-state
  have hBack : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), (∀ r, o ≠ .vspaceRoot r) →
      (∀ u, o ≠ .untyped u) → st'.objects[oid]? = some o → st.objects[oid]? = some o := by
    intro oid o hNR hNU hPost
    have hNe : oid ≠ untypedId := by
      intro hEq; rw [hEq, storeObject_objects_eq _ _ _ _ hInv2 hSt] at hPost
      exact hNU _ (Option.some.inj hPost).symm
    rw [storeObject_objects_ne _ _ _ _ _ hNe hInv2 hSt] at hPost
    have h1 := hW2.eq_of_isSome hPost
    rw [← hW1.eq_of_not_root' (fun r h => by rw [h1] at h; exact hNR r (Option.some.inj h))]
    exact h1
  have hClean : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), st.objects[oid]? = some o →
      objectNamesListed ids o = false := by
    intro oid o h
    have := SeLe4n.Kernel.RobinHood.RHTable.fold_and_true_of_get? st.objects
      (fun _ o => !objectNamesListed ids o) hRef h
    simpa using this
  refine ⟨ut, ids, hUt, hWalk, ?_, ?_⟩
  · intro oid cn slot cap hCn hLk
    have hPre := hBack oid (.cnode cn) (fun _ h => by cases h) (fun _ h => by cases h) hCn
    have hN := hClean oid _ hPre
    simp only [objectNamesListed, Bool.not_eq_false'] at hN
    have hc := SeLe4n.Kernel.RobinHood.RHTable.fold_and_true_of_get? cn.slots.table
      (fun _ cap => !capNamesListed ids cap) hN hLk
    simpa using hc
  · intro oid t msg hT hMsg
    have hPre := hBack oid (.tcb t) (fun _ h => by cases h) (fun _ h => by cases h) hT
    have hN := hClean oid _ hPre
    simpa [objectNamesListed, hMsg] using hN

/-- **The object kinds a reset can touch**: an absent key, a VSpace root (the
unmap pass), a frame or an untyped (the retire), and the untyped (the watermark
reset).  Every one of them lies outside what the IPC bundle reads, and none is a
CNode or a TCB. -/
def resetTouched : Option KernelObject → Prop
  | none => True
  | some (.vspaceRoot _) => True
  | some (.frame _) => True
  | some (.untyped _) => True
  | _ => False

/-- **The whole reset's object-store frame**: every key is unchanged, or a kind
the reset touches on both sides; the scheduler is unchanged.  What every bundle
the reset must carry is transported through. -/
theorem untypedReset_ok_frame (ec : Concurrency.CoreId) (untypedId : SeLe4n.ObjId)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedReset ec untypedId st = .ok ((), st')) :
    st'.objects.invExt ∧ st'.scheduler = st.scheduler ∧
    ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
      (resetTouched st.objects[oid]? ∧ resetTouched st'.objects[oid]?) := by
  obtain ⟨ut, ids, st1, hUt, -, -, -, -, -, hM, -, hSz, hSt⟩ :=
    untypedReset_ok_decompose ec untypedId st st' hStep
  obtain ⟨-, hW1, hS1, hInv2, hS2, hW2, -⟩ := untypedReset_ok_frames (ids := ids) hObjInv hM hSz
  have hUtAt := (SystemState.getUntyped?_eq_some_iff st untypedId ut).mp hUt
  have hCT : ∀ s oid, carvedAt s oid → resetTouched s.objects[oid]? := by
    intro s oid h; rcases h with ⟨f, hf⟩ | ⟨u, hu⟩
    · rw [hf]; trivial
    · rw [hu]; trivial
  refine ⟨storeObject_preserves_objects_invExt _ _ _ _ hInv2 hSt,
    (storeObject_scheduler_eq _ _ _ _ hSt).trans (hS2.trans hS1), fun oid => ?_⟩
  by_cases hK : oid = untypedId
  · subst hK
    rw [storeObject_objects_eq _ _ _ _ hInv2 hSt, hUtAt]
    exact Or.inr ⟨trivial, trivial⟩
  · rw [storeObject_objects_ne _ _ _ _ _ hK hInv2 hSt]
    rcases hW2 oid with e2 | ⟨hc, hn⟩
    · rw [e2]
      rcases hW1 oid with e1 | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
      · exact Or.inl e1
      · rw [hr, hr']; exact Or.inr ⟨trivial, trivial⟩
    · rw [hn]
      rcases hW1 oid with e1 | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
      · have := hCT st1 oid hc; rw [e1] at this; exact Or.inr ⟨this, trivial⟩
      · rw [hr]; exact Or.inr ⟨trivial, trivial⟩

end SeLe4n.Kernel
