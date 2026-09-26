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

**WS-BP BP7.1, slice 3 (`v0.36.6`).**  Slice 2 made memory reachable only by a
carve (`untypedRetypeFrame`); this module is the other half of seL4's untyped
life cycle, `resetUntypedCap`: once nothing can reach any object carved from an
untyped, the untyped's memory is handed back to it and may be carved again.

## What "nothing can reach" means, and why it is decided over the whole store

In seL4 each untyped capability carries its own free index, so "no child
capability survives" is `ensureNoChildren` on the invoked slot.  This model keeps
the watermark on the untyped **object**, shared by every capability to it — which
is what stops two copies of one untyped capability from carving one page twice —
so the per-slot test is not sufficient here: a sibling copy's children are not
CDT descendants of the invoked slot.  The question is therefore asked of the
objects themselves (`untypedChildrenUnreferenced`): no CNode slot, and no
capability parked in a blocked sender's message, names any carved child.

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
missed makes the reset refuse rather than hand the page out again.

## What the reset writes

1. every mapping of a page meeting the region, removed (`unmapLivePages`, the
   page teardown this reset shares with a frame capability's destruction);
2. every carved child **retired** — erased from the object store with its index
   and metadata rows (`retireFrame`), so its object id and its store capacity
   return too.  Leaving a capless frame in the store would be unreachable but
   would consume a store slot per carve, and a holder of one small untyped could
   then exhaust the global object store by carving and resetting in a loop;
3. the untyped's watermark and child list cleared (`UntypedObject.reset`, the
   model's own reset, whose `reset_wellFormed` says the result is well formed).

No memory is zeroed here: the carve zeroes every RAM page before any capability
to it exists (`carveZeroFrame`), so a page is scrubbed exactly when it is handed
out, whatever happened to it in between.

## What it refuses

* a child that is not a frame (`.revocationRequired`) — slice 2 carves frames
  only, and a kernel object carved by the in-place path has no destroy operation
  that returns its memory; resetting under one would hand its page out while it
  lives;
* a child some capability still names (`.revocationRequired`) — revoke the
  untyped capability (`.cspaceRevoke`), which reaches every capability derived
  from it, then reset;
* a mapping of the region surviving the unmap pass, or an object table without
  the headroom an erase needs (`.illegalState`) — neither is reachable on a
  well-formed state, and both are decided rather than assumed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The region, and what names it
-- ============================================================================

/-- **Does the page at `p` meet the untyped's region?**  A mapping names the
base of one page, `[p, p + pageBytes)`; it reaches the untyped's memory exactly
when that page overlaps `[regionBase, regionBase + regionSize)`.  Asked as an
overlap rather than as "`p` lies in the region" so that no page straddling the
region's start can escape the test, whatever alignment the region has. -/
def _root_.SeLe4n.Model.UntypedObject.regionMeetsPage (ut : UntypedObject) (p : SeLe4n.PAddr) : Bool :=
  decide (p.toNat < ut.regionBase.toNat + ut.regionSize) &&
    decide (ut.regionBase.toNat < p.toNat + SeLe4n.pageBytes)

/-- Is `id` one of the untyped's carved children? -/
def _root_.SeLe4n.Model.UntypedObject.carvedChild (ut : UntypedObject) (id : SeLe4n.ObjId) : Bool :=
  ut.children.any (fun c => c.objId == id)

/-- **Does this capability name an object carved from `ut`?**  Only an
`.object` target names an object; a CNode-slot, reply or audit-trail target
names none of a carve's children. -/
def capNamesCarvedChild (ut : UntypedObject) (cap : Capability) : Bool :=
  match cap.target with
  | .object id => ut.carvedChild id
  | _ => false

/-- **Does this stored object hold a capability naming a carved child?**  The
two places a capability lives: a CNode slot, and the message a blocked sender
has parked (its transfer capabilities install at the receiver later, so they are
authority in flight).  No other object kind holds a `Capability`. -/
def objectNamesCarvedChild (ut : UntypedObject) : KernelObject → Bool
  | .cnode cn => !(cn.slots.fold true (fun acc _ cap => acc && !capNamesCarvedChild ut cap))
  | .tcb t =>
      match t.pendingMessage with
      | some msg => msg.caps.any (fun tc => capNamesCarvedChild ut tc.cap)
      | none => false
  | _ => false

/-- **The whole-store check: no capability anywhere names a carved child.**
A conjunction folded over the object table, which is what makes the payoff
(`untypedChildrenUnreferenced_sound`) a statement about every key the table
resolves rather than about the keys an index happens to list. -/
def untypedChildrenUnreferenced (st : SystemState) (ut : UntypedObject) : Bool :=
  st.objects.fold true (fun acc _ o => acc && !objectNamesCarvedChild ut o)

/-- **Every carved child is a frame.**  The reset retires frames and nothing
else: a kernel object has no operation here that returns its memory. -/
def untypedChildrenRetirable (st : SystemState) (ut : UntypedObject) : Bool :=
  ut.children.all fun c =>
    match st.getFrame? c.objId with
    | some _ => true
    | none => false

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
-- §3  Retiring a frame
-- ============================================================================

/-- **Erase a frame from the object store**, with its index row, its index-set
entry and its object-type metadata.  A no-op at a key that does not hold a
frame, so no other kind of object can be erased through it: an erased TCB,
Reply or SchedContext would leave every structure naming it dangling, while a
frame is named only by capabilities and mappings — which the reset has already
shown to be gone.  Frames register no ASID, so the ASID table is untouched. -/
def retireFrame (st : SystemState) (id : SeLe4n.ObjId) : SystemState :=
  match st.getFrame? id with
  | none => st
  | some _ =>
    { st with
        objects := st.objects.erase id
        objectIndex := st.objectIndex.filter (· != id)
        objectIndexSet := st.objectIndexSet.erase id
        lifecycle := { objectTypes := st.lifecycle.objectTypes.erase id } }

/-- Retire every listed frame, in order. -/
def retireFrames (st : SystemState) (ids : List SeLe4n.ObjId) : SystemState :=
  ids.foldl retireFrame st

-- ============================================================================
-- §4  The reset
-- ============================================================================

/-- **WS-BP BP7.1 slice 3: reset an untyped — seL4's `resetUntypedCap`.**

Four refusals, each committing nothing, then the three writes the module
docstring lists.  `executingCore` is the core the invoking thread runs on; it is
the initiator of every shootdown round the unmap pass posts. -/
def untypedReset (executingCore : Concurrency.CoreId) (untypedId : SeLe4n.ObjId) : Kernel Unit :=
  fun st =>
    match st.getUntyped? untypedId with
    | none => .error .untypedTypeMismatch
    | some ut =>
      if !untypedChildrenRetirable st ut then .error .revocationRequired
      else if !untypedChildrenUnreferenced st ut then .error .revocationRequired
      else
        match unmapLivePages executingCore (untypedRegionMappings st ut) st with
        | .error e => .error e
        | .ok ((), st1) =>
          if !untypedRegionUnmapped st1 ut then .error .illegalState
          else if !decide (st1.objects.size < st1.objects.capacity) then .error .illegalState
          else
            storeObject untypedId (.untyped ut.reset)
              (retireFrames st1 (ut.children.map (·.objId)))

-- ============================================================================
-- §5  Frames: what each step of the reset can change
-- ============================================================================

/-- **Retiring one frame**: the key erased held a frame; every other key is
unchanged.  Stated with the headroom an erase needs (`size < capacity`), which
the reset decides before it retires anything and which an erase preserves. -/
theorem retireFrame_frame (st : SystemState) (id : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt) (hSize : st.objects.size < st.objects.capacity) :
    (retireFrame st id).objects.invExt ∧
    (retireFrame st id).objects.size < (retireFrame st id).objects.capacity ∧
    (retireFrame st id).scheduler = st.scheduler ∧
    (∀ oid : SeLe4n.ObjId, (retireFrame st id).objects[oid]? = st.objects[oid]? ∨
      ((∃ f, st.objects[oid]? = some (KernelObject.frame f)) ∧
        (retireFrame st id).objects[oid]? = none)) ∧
    (st.objects[id]? = none ∨ (∃ f, st.objects[id]? = some (KernelObject.frame f)) →
      (retireFrame st id).objects[id]? = none) := by
  unfold retireFrame
  cases hF : st.getFrame? id with
  | none =>
    refine ⟨hObjInv, hSize, rfl, fun _ => Or.inl rfl, ?_⟩
    rintro (h | ⟨f, hf⟩)
    · exact h
    · exact absurd ((SystemState.getFrame?_eq_some_iff st id f).mpr hf) (by rw [hF]; simp)
  | some f =>
    have hAt : st.objects[id]? = some (.frame f) := (SystemState.getFrame?_eq_some_iff st id f).mp hF
    have hSelf : (st.objects.erase id)[id]? = none :=
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self st.objects id hObjInv
    refine ⟨SeLe4n.Kernel.RobinHood.RHTable.erase_preserves_invExt st.objects id hObjInv hSize,
      SeLe4n.Kernel.RobinHood.RHTable.erase_size_lt_capacity st.objects id hSize, rfl,
      fun oid => ?_, fun _ => hSelf⟩
    by_cases hK : oid = id
    · subst hK; exact Or.inr ⟨⟨f, hAt⟩, hSelf⟩
    · have hNe : ¬(id == oid) = true := by
        intro h; exact hK (eq_of_beq h).symm
      exact Or.inl (SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne st.objects id oid hNe
        hObjInv hSize)

/-- **A frame-retire write**: at every key the object is unchanged, or a frame
that is now absent. -/
def frameRetireWrite (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    ((∃ f, st.objects[oid]? = some (KernelObject.frame f)) ∧ st'.objects[oid]? = none)

theorem frameRetireWrite.refl (st : SystemState) : frameRetireWrite st st :=
  fun _ => Or.inl rfl

theorem frameRetireWrite.trans {s1 s2 s3 : SystemState}
    (hFirst : frameRetireWrite s1 s2) (hSecond : frameRetireWrite s2 s3) :
    frameRetireWrite s1 s3 := by
  intro oid
  rcases hFirst oid with e12 | ⟨f1, n2⟩ <;> rcases hSecond oid with e23 | ⟨f2, n3⟩
  · exact Or.inl (e23.trans e12)
  · exact Or.inr ⟨by rw [← e12]; exact f2, n3⟩
  · exact Or.inr ⟨f1, by rw [e23]; exact n2⟩
  · exact Or.inr ⟨f1, n3⟩

/-- A key that holds something after a frame-retire write held the same thing
before. -/
theorem frameRetireWrite.eq_of_isSome {st st' : SystemState}
    (h : frameRetireWrite st st') {oid : SeLe4n.ObjId} {o : KernelObject}
    (hPost : st'.objects[oid]? = some o) : st.objects[oid]? = some o := by
  rcases h oid with e | ⟨_, hn⟩
  · rw [← e]; exact hPost
  · rw [hn] at hPost; cases hPost

/-- **Retiring a list of frames**: a frame-retire write that keeps the table's
invariant and headroom and the scheduler, and after which every listed key that
held a frame, or nothing, holds nothing. -/
theorem retireFrames_frame :
    ∀ (ids : List SeLe4n.ObjId) (st : SystemState),
      st.objects.invExt → st.objects.size < st.objects.capacity →
      (retireFrames st ids).objects.invExt ∧
      (retireFrames st ids).objects.size < (retireFrames st ids).objects.capacity ∧
      (retireFrames st ids).scheduler = st.scheduler ∧
      frameRetireWrite st (retireFrames st ids) ∧
      (∀ id ∈ ids, (st.objects[id]? = none ∨
          ∃ f, st.objects[id]? = some (KernelObject.frame f)) →
        (retireFrames st ids).objects[id]? = none)
  | [], st, hInv, hSize => by
      refine ⟨hInv, hSize, rfl, frameRetireWrite.refl _, ?_⟩
      intro id hMem; cases hMem
  | h :: t, st, hInv, hSize => by
      have hFold : retireFrames st (h :: t) = retireFrames (retireFrame st h) t := rfl
      obtain ⟨hInv1, hSize1, hSch1, hW1, hSelf1⟩ := retireFrame_frame st h hInv hSize
      obtain ⟨hInv2, hSize2, hSch2, hW2, hNone2⟩ :=
        retireFrames_frame t (retireFrame st h) hInv1 hSize1
      rw [hFold]
      refine ⟨hInv2, hSize2, hSch2.trans hSch1, frameRetireWrite.trans hW1 hW2, ?_⟩
      intro id hMem hPre
      -- a key that held a frame or nothing still does after one retire
      have hPre1 : (retireFrame st h).objects[id]? = none ∨
          ∃ f, (retireFrame st h).objects[id]? = some (KernelObject.frame f) := by
        rcases hW1 id with e | ⟨_, hn⟩
        · rw [e]; exact hPre
        · exact Or.inl hn
      rcases List.mem_cons.mp hMem with hEq | hTail
      · subst hEq
        have hN1 := hSelf1 hPre
        rcases hW2 id with e | ⟨⟨f, hf⟩, _⟩
        · rw [e]; exact hN1
        · rw [hN1] at hf; cases hf
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
    ∃ (ut : UntypedObject) (st1 : SystemState),
      st.getUntyped? untypedId = some ut ∧
      untypedChildrenRetirable st ut = true ∧
      untypedChildrenUnreferenced st ut = true ∧
      unmapLivePages ec (untypedRegionMappings st ut) st = .ok ((), st1) ∧
      untypedRegionUnmapped st1 ut = true ∧
      st1.objects.size < st1.objects.capacity ∧
      storeObject untypedId (.untyped ut.reset)
        (retireFrames st1 (ut.children.map (·.objId))) = .ok ((), st') := by
  unfold untypedReset at hStep
  cases hUt : st.getUntyped? untypedId with
  | none => rw [hUt] at hStep; cases hStep
  | some ut =>
    rw [hUt] at hStep
    simp only at hStep
    cases hR : untypedChildrenRetirable st ut
    · simp [hR] at hStep
    cases hU : untypedChildrenUnreferenced st ut
    · simp [hR, hU] at hStep
    simp only [hR, hU, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
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
        exact ⟨ut, st1, rfl, hR, hU, hM, hC, hSz, hStep⟩
      · simp [hC, hSz] at hStep

/-- The untyped lies at its own key, and the carved children are frames there:
so no child key is the untyped's own. -/
private theorem child_ne_untyped {st : SystemState} {untypedId : SeLe4n.ObjId}
    {ut : UntypedObject} (hUt : st.getUntyped? untypedId = some ut)
    (hR : untypedChildrenRetirable st ut = true) {c : UntypedChild} (hc : c ∈ ut.children) :
    c.objId ≠ untypedId ∧ ∃ f, st.objects[c.objId]? = some (KernelObject.frame f) := by
  have hAll := List.all_eq_true.mp hR c hc
  cases hF : st.getFrame? c.objId with
  | none => rw [hF] at hAll; cases hAll
  | some f =>
    have hAt := (SystemState.getFrame?_eq_some_iff st c.objId f).mp hF
    refine ⟨fun hEq => ?_, f, hAt⟩
    rw [hEq] at hAt
    have hU := (SystemState.getUntyped?_eq_some_iff st untypedId ut).mp hUt
    rw [hU] at hAt; cases hAt

/-- The whole-reset frames, collected: the table invariant, the scheduler, the
unmap pass's VSpace-root-only write and the retire's frame-retire write. -/
private theorem untypedReset_ok_frames {ec : Concurrency.CoreId}
    {st st1 : SystemState} {ut : UntypedObject} (hObjInv : st.objects.invExt)
    (hM : unmapLivePages ec (untypedRegionMappings st ut) st = .ok ((), st1))
    (hSz : st1.objects.size < st1.objects.capacity) :
    let st2 := retireFrames st1 (ut.children.map (·.objId))
    st1.objects.invExt ∧ vspaceRootOnlyWrite st st1 ∧ st1.scheduler = st.scheduler ∧
    st2.objects.invExt ∧ st2.scheduler = st1.scheduler ∧ frameRetireWrite st1 st2 ∧
    (∀ id ∈ ut.children.map (·.objId), (st1.objects[id]? = none ∨
        ∃ f, st1.objects[id]? = some (KernelObject.frame f)) → st2.objects[id]? = none) := by
  obtain ⟨hInv1, hW1, hS1⟩ := unmapLivePages_ok_frame ec _ st st1 hObjInv hM
  obtain ⟨hInv2, -, hS2, hW2, hN2⟩ := retireFrames_frame (ut.children.map (·.objId)) st1 hInv1 hSz
  exact ⟨hInv1, hW1, hS1, hInv2, hS2, hW2, hN2⟩

/-- **After a reset the untyped holds its memory again**: watermark `0`, no
children, region, device flag and parent unchanged. -/
theorem untypedReset_ok_untyped (ec : Concurrency.CoreId) (untypedId : SeLe4n.ObjId)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedReset ec untypedId st = .ok ((), st')) :
    ∃ ut, st.getUntyped? untypedId = some ut ∧
      st'.objects[untypedId]? = some (.untyped ut.reset) := by
  obtain ⟨ut, st1, hUt, -, -, hM, -, hSz, hSt⟩ := untypedReset_ok_decompose ec untypedId st st' hStep
  obtain ⟨-, -, -, hInv2, -, -, -⟩ := untypedReset_ok_frames hObjInv hM hSz
  exact ⟨ut, hUt, storeObject_objects_eq _ _ _ _ hInv2 hSt⟩

/-- **After a reset no carved child exists**: every object the untyped's child
list named is gone from the store, so its id — and its store capacity — are free
again. -/
theorem untypedReset_ok_children_absent (ec : Concurrency.CoreId) (untypedId : SeLe4n.ObjId)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedReset ec untypedId st = .ok ((), st')) :
    ∃ ut, st.getUntyped? untypedId = some ut ∧
      ∀ c ∈ ut.children, st'.objects[c.objId]? = none := by
  obtain ⟨ut, st1, hUt, hR, -, hM, -, hSz, hSt⟩ :=
    untypedReset_ok_decompose ec untypedId st st' hStep
  obtain ⟨-, hW1, -, hInv2, -, -, hN2⟩ :=
    untypedReset_ok_frames hObjInv hM hSz
  refine ⟨ut, hUt, fun c hc => ?_⟩
  obtain ⟨hNe, f, hF⟩ := child_ne_untyped hUt hR hc
  rw [storeObject_objects_ne _ _ _ _ _ hNe hInv2 hSt]
  have hF1 : st1.objects[c.objId]? = some (KernelObject.frame f) := by
    rw [hW1.eq_of_not_root (fun r h => by rw [hF] at h; cases h)]; exact hF
  exact hN2 c.objId (List.mem_map.mpr ⟨c, hc, rfl⟩) (Or.inr ⟨f, hF1⟩)

/-- **After a reset no VSpace root maps a page of the region** — the check the
reset decides after its unmap pass, carried to the state it commits.  With the
children gone and the capabilities to them already gone, this is what makes a
page the reset hands back unreachable by any thread: the next carve's zeroed
page is the only name any thread will have for it. -/
theorem untypedReset_ok_unmapped (ec : Concurrency.CoreId) (untypedId : SeLe4n.ObjId)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedReset ec untypedId st = .ok ((), st')) :
    ∃ ut, st.getUntyped? untypedId = some ut ∧
      ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot) (v : SeLe4n.VAddr)
        (e : SeLe4n.PAddr × PagePermissions),
        st'.objects[oid]? = some (.vspaceRoot root) →
        root.mappings[v]? = some e → ut.regionMeetsPage e.1 = false := by
  obtain ⟨ut, st1, hUt, -, -, hM, hC, hSz, hSt⟩ :=
    untypedReset_ok_decompose ec untypedId st st' hStep
  obtain ⟨-, -, -, hInv2, -, hW2, -⟩ :=
    untypedReset_ok_frames hObjInv hM hSz
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

/-- **After a reset no capability names a carved child** — in no CNode slot and
in no message a blocked sender has parked.  The reset decided this of its
pre-state and writes neither CNodes nor TCBs, so the committed state inherits it:
once a child's id is reused by the next carve, no capability left over from the
retired frame can name the new one. -/
theorem untypedReset_ok_unreferenced (ec : Concurrency.CoreId) (untypedId : SeLe4n.ObjId)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedReset ec untypedId st = .ok ((), st')) :
    ∃ ut, st.getUntyped? untypedId = some ut ∧
      (∀ (oid : SeLe4n.ObjId) (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability),
        st'.objects[oid]? = some (.cnode cn) → cn.lookup slot = some cap →
        capNamesCarvedChild ut cap = false) ∧
      (∀ (oid : SeLe4n.ObjId) (t : TCB) (msg : IpcMessage),
        st'.objects[oid]? = some (.tcb t) → t.pendingMessage = some msg →
        msg.caps.any (fun tc => capNamesCarvedChild ut tc.cap) = false) := by
  obtain ⟨ut, st1, hUt, -, hRef, hM, -, hSz, hSt⟩ :=
    untypedReset_ok_decompose ec untypedId st st' hStep
  obtain ⟨-, hW1, -, hInv2, -, hW2, -⟩ :=
    untypedReset_ok_frames hObjInv hM hSz
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
      objectNamesCarvedChild ut o = false := by
    intro oid o h
    have := SeLe4n.Kernel.RobinHood.RHTable.fold_and_true_of_get? st.objects
      (fun _ o => !objectNamesCarvedChild ut o) hRef h
    simpa using this
  refine ⟨ut, hUt, ?_, ?_⟩
  · intro oid cn slot cap hCn hLk
    have hPre := hBack oid (.cnode cn) (fun _ h => by cases h) (fun _ h => by cases h) hCn
    have hN := hClean oid _ hPre
    simp only [objectNamesCarvedChild, Bool.not_eq_false'] at hN
    have hc := SeLe4n.Kernel.RobinHood.RHTable.fold_and_true_of_get? cn.slots.table
      (fun _ cap => !capNamesCarvedChild ut cap) hN hLk
    simpa using hc
  · intro oid t msg hT hMsg
    have hPre := hBack oid (.tcb t) (fun _ h => by cases h) (fun _ h => by cases h) hT
    have hN := hClean oid _ hPre
    simpa [objectNamesCarvedChild, hMsg] using hN

/-- **The object kinds a reset can touch**: an absent key, a VSpace root (the
unmap pass), a frame (the retire) and an untyped (the watermark reset).  Every
one of them lies outside what the IPC bundle reads, and none is a CNode or a
TCB. -/
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
  obtain ⟨ut, st1, hUt, -, -, hM, -, hSz, hSt⟩ :=
    untypedReset_ok_decompose ec untypedId st st' hStep
  obtain ⟨-, hW1, hS1, hInv2, hS2, hW2, -⟩ := untypedReset_ok_frames hObjInv hM hSz
  have hUtAt := (SystemState.getUntyped?_eq_some_iff st untypedId ut).mp hUt
  refine ⟨storeObject_preserves_objects_invExt _ _ _ _ hInv2 hSt,
    (storeObject_scheduler_eq _ _ _ _ hSt).trans (hS2.trans hS1), fun oid => ?_⟩
  by_cases hK : oid = untypedId
  · subst hK
    rw [storeObject_objects_eq _ _ _ _ hInv2 hSt, hUtAt]
    exact Or.inr ⟨trivial, trivial⟩
  · rw [storeObject_objects_ne _ _ _ _ _ hK hInv2 hSt]
    rcases hW2 oid with e2 | ⟨⟨f, hf⟩, hn⟩
    · rw [e2]
      rcases hW1 oid with e1 | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
      · exact Or.inl e1
      · rw [hr, hr']; exact Or.inr ⟨trivial, trivial⟩
    · rw [hn]
      rcases hW1 oid with e1 | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
      · rw [← e1, hf]; exact Or.inr ⟨trivial, trivial⟩
      · rw [hr]; exact Or.inr ⟨trivial, trivial⟩

end SeLe4n.Kernel
