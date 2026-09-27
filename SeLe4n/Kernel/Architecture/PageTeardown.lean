-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.PerCoreCacheModel

/-!
# Page teardown — removing a list of mappings through the verified unmap

**WS-BP BP7.1 (`v0.36.7`).**  Two operations remove mappings they did not ask
for by address: the untyped reset removes every mapping of a page in the region
it hands back (`untypedReset`), and destroying a frame capability removes the
mapping that capability made (`cspaceDeleteSlotFinalising`,
`cspaceRevokeCdtFinalising`) — seL4's `finaliseCap` → `unmapPage`.  Both are one
question, so they share one answer here: a list of `MappedPage`s, each removed
through the one verified unmap the `.vspaceUnmap` arm runs
(`vspaceUnmapPageWithShootdownAndIcacheBroadcast` — the page-table erase, the
local flush, the `.vae1` shootdown round, the initiator's own per-core drain and
the instruction-cache broadcast for an executable page), so the TLB and cache
discipline a single unmap owes is owed — and paid — per page.

## Only a live translation is removed

A page is removed only while its address space still maps the address to *that*
physical page (`mappedPageLive`).  A frame capability's record can go stale — the
address space unmapped the address through its own capability, or was destroyed
and its ASID reused — and a stale record must remove nothing that is not its
own: the check compares the physical page, as seL4's `unmapPage` compares the
PTE's frame address before it clears it.  The same check makes a repeated entry
harmless, which two records of one mapping would otherwise make fatal.

## The result is checked, not trusted

`livePagesCleared` decides afterwards that no listed page is still live.  Every
step only removes translations, so it cannot fail on a well-formed state; the
callers refuse (`.illegalState`) if it ever does rather than claim a teardown
that did not happen, and their payoff theorems are read off the check.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  Live pages, and the teardown
-- ============================================================================

/-- **Is this page still mapped where it says?**  The address space the ASID
resolves to maps the virtual address, and the translation names this physical
page. -/
def mappedPageLive (st : SystemState) (p : MappedPage) : Bool :=
  match Architecture.resolveAsidRoot st p.asid with
  | some (_, root) => ((root.lookup p.vaddr).map Prod.fst) == some p.paddr
  | none => false

/-- **Remove each listed page that is still live**, in order, through the
verified unmap, stopping at the first failure.  A page no longer live is
skipped. -/
def unmapLivePages (executingCore : Concurrency.CoreId) :
    List MappedPage → Kernel Unit
  | [] => fun st => .ok ((), st)
  | p :: rest => fun st =>
      if mappedPageLive st p then
        match Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast
            executingCore p.asid p.vaddr st with
        | .error e => .error e
        | .ok ((), st1) => unmapLivePages executingCore rest st1
      else unmapLivePages executingCore rest st

/-- **No listed page is live** — the teardown's result, decided. -/
def livePagesCleared (st : SystemState) (pages : List MappedPage) : Bool :=
  pages.all fun p => !mappedPageLive st p

/-- The decided result, as a proposition about every listed page. -/
theorem livePagesCleared_spec {st : SystemState} {pages : List MappedPage}
    (h : livePagesCleared st pages = true) :
    ∀ p ∈ pages, mappedPageLive st p = false := by
  intro p hp
  unfold livePagesCleared at h
  have := List.all_eq_true.mp h p hp
  simpa using this

-- ============================================================================
-- §2  Frames: what a teardown can change
-- ============================================================================

/-- **A write that touches VSpace roots only**: at every key the object is
unchanged, or a VSpace root on both sides.  What one unmap does, and so what the
whole unmap pass does. -/
def vspaceRootOnlyWrite (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    ((∃ r, st.objects[oid]? = some (.vspaceRoot r)) ∧
     (∃ r', st'.objects[oid]? = some (.vspaceRoot r')))

theorem vspaceRootOnlyWrite.refl (st : SystemState) : vspaceRootOnlyWrite st st :=
  fun _ => Or.inl rfl

theorem vspaceRootOnlyWrite.trans {s1 s2 s3 : SystemState}
    (hFirst : vspaceRootOnlyWrite s1 s2) (hSecond : vspaceRootOnlyWrite s2 s3) :
    vspaceRootOnlyWrite s1 s3 := by
  intro oid
  rcases hFirst oid with e12 | ⟨r1, r2⟩ <;> rcases hSecond oid with e23 | ⟨r2', r3⟩
  · exact Or.inl (e23.trans e12)
  · exact Or.inr ⟨by rw [← e12]; exact r2', r3⟩
  · exact Or.inr ⟨r1, by rw [e23]; exact r2⟩
  · exact Or.inr ⟨r1, r3⟩

/-- A key a VSpace-root-only write leaves unchanged: every key that does not hold
a VSpace root beforehand. -/
theorem vspaceRootOnlyWrite.eq_of_not_root {st st' : SystemState}
    (h : vspaceRootOnlyWrite st st') {oid : SeLe4n.ObjId}
    (hNot : ∀ r, st.objects[oid]? ≠ some (.vspaceRoot r)) :
    st'.objects[oid]? = st.objects[oid]? := by
  rcases h oid with e | ⟨⟨r, hr⟩, _⟩
  · exact e
  · exact absurd hr (hNot r)

/-- ...and a key that holds no VSpace root afterwards is unchanged too. -/
theorem vspaceRootOnlyWrite.eq_of_not_root' {st st' : SystemState}
    (h : vspaceRootOnlyWrite st st') {oid : SeLe4n.ObjId}
    (hNot : ∀ r, st'.objects[oid]? ≠ some (.vspaceRoot r)) :
    st'.objects[oid]? = st.objects[oid]? := by
  rcases h oid with e | ⟨_, ⟨r, hr⟩⟩
  · exact e
  · exact absurd hr (hNot r)

/-- **One page-table unmap** stores a VSpace root at the key the ASID resolved
to, which held a VSpace root; nothing else moves in the object store. -/
theorem vspaceUnmapPage_ok_frame (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler := by
  unfold Architecture.vspaceUnmapPage at hStep
  cases hRes : Architecture.resolveAsidRoot st asid with
  | none => rw [hRes] at hStep; cases hStep
  | some pr =>
    obtain ⟨rootId, root⟩ := pr
    rw [hRes] at hStep
    simp only at hStep
    cases hUn : root.unmapPage vaddr with
    | none => rw [hUn] at hStep; cases hStep
    | some root' =>
      rw [hUn] at hStep
      simp only at hStep
      obtain ⟨_, hObj, _⟩ :=
        Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hRes
      refine ⟨storeObject_preserves_objects_invExt (Architecture.recordPhysicalWrites st _) _ _ _ hObjInv hStep, ?_,
        (by have h := storeObject_scheduler_eq _ _ _ _ hStep; exact h)⟩
      intro oid
      by_cases hK : oid = rootId
      · subst hK
        exact Or.inr ⟨⟨root, hObj⟩, ⟨root', storeObject_objects_eq (Architecture.recordPhysicalWrites st _) _ _ _ hObjInv hStep⟩⟩
      · exact Or.inl (storeObject_objects_ne (Architecture.recordPhysicalWrites st _) _ _ _ _ hK hObjInv hStep)

/-- **The verified unmap the `.vspaceUnmap` arm runs** changes the object store
exactly as its page-table erase does: the local flush, the shootdown round, the
initiator's drain and the instruction-cache broadcast write only TLB, shootdown
and cache state. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame
    (ec : Concurrency.CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) :
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler := by
  unfold Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast at hStep
  cases hK : Architecture.vspaceUnmapPageWithShootdownPerCore ec asid vaddr st with
  | error e =>
    rw [(Architecture.withIcacheBroadcast_error_iff _ _ st e).mpr hK] at hStep
    cases hStep
  | ok pr =>
    obtain ⟨u, stK⟩ := pr; cases u
    obtain ⟨hObjsK, -, hSchedK, -⟩ := Architecture.withIcacheBroadcast_frame hK hStep
    unfold Architecture.vspaceUnmapPageWithShootdownPerCore at hK
    cases hS : Architecture.vspaceUnmapPageWithShootdown ec asid vaddr st with
    | error e => rw [hS] at hK; cases hK
    | ok pr2 =>
      obtain ⟨u2, stS⟩ := pr2; cases u2
      rw [hS] at hK
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hK
      subst hK
      unfold Architecture.vspaceUnmapPageWithShootdown at hS
      cases hF : Architecture.vspaceUnmapPageWithFlush asid vaddr st with
      | error e => rw [hF] at hS; cases hS
      | ok pr3 =>
        obtain ⟨u3, stF⟩ := pr3; cases u3
        rw [hF] at hS
        simp only [Architecture.withShootdownRound_total, Except.ok.injEq, Prod.mk.injEq,
          true_and] at hS
        subst hS
        unfold Architecture.vspaceUnmapPageWithFlush at hF
        cases hU : Architecture.vspaceUnmapPage asid vaddr st with
        | error e => rw [hU] at hF; cases hF
        | ok pr4 =>
          obtain ⟨u4, stU⟩ := pr4; cases u4
          rw [hU] at hF
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hF
          subst hF
          obtain ⟨hInvU, hWU, hSchU⟩ := vspaceUnmapPage_ok_frame asid vaddr st stU hObjInv hU
          have hObjs : st'.objects = stU.objects := hObjsK
          have hSch : st'.scheduler = stU.scheduler := hSchedK
          refine ⟨hObjs ▸ hInvU, fun oid => ?_, hSch.trans hSchU⟩
          rw [hObjs]; exact hWU oid

/-- **One page-table map** stores a VSpace root at the key the ASID resolved to,
which held a VSpace root; nothing else moves in the object store.  The map's twin
of `vspaceUnmapPage_ok_frame`. -/
theorem vspaceMapPage_ok_frame (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler := by
  unfold Architecture.vspaceMapPage at hStep
  cases hRes : Architecture.resolveAsidRoot st asid with
  | none => rw [hRes] at hStep; cases hStep
  | some pr =>
    obtain ⟨rootId, root⟩ := pr
    rw [hRes] at hStep
    simp only at hStep
    split at hStep
    · cases hStep
    · split at hStep
      · cases hStep
      · cases hMp : root.mapPage vaddr paddr perms with
        | none => rw [hMp] at hStep; cases hStep
        | some root' =>
          rw [hMp] at hStep
          simp only at hStep
          obtain ⟨_, hObj, _⟩ :=
            Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hRes
          refine ⟨storeObject_preserves_objects_invExt (Architecture.recordPhysicalWrites st _) _ _ _ hObjInv hStep, ?_,
            (by have h := storeObject_scheduler_eq _ _ _ _ hStep; exact h)⟩
          intro oid
          by_cases hK : oid = rootId
          · subst hK
            exact Or.inr ⟨⟨root, hObj⟩, ⟨root', storeObject_objects_eq (Architecture.recordPhysicalWrites st _) _ _ _ hObjInv hStep⟩⟩
          · exact Or.inl (storeObject_objects_ne (Architecture.recordPhysicalWrites st _) _ _ _ _ hK hObjInv hStep)

/-- **The verified map the `.vspaceMap` arm runs** changes the object store
exactly as its page-table write does: the bounds guards write nothing, and the
local flush, the remap shootdown round, the initiator's drain and its fill write
only TLB and shootdown state. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame
    (ec : Concurrency.CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore ec asid vaddr
      paddr perms st = .ok ((), st')) :
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler := by
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore at hStep
  cases hS : Architecture.vspaceMapPageCheckedWithShootdownFromState ec asid vaddr paddr
      perms st with
  | error e => rw [hS] at hStep; cases hStep
  | ok pr =>
    obtain ⟨u, stM⟩ := pr; cases u
    rw [hS] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
    -- The drain and the fill write `perCoreTlb` alone.
    have hTail : st'.objects = stM.objects ∧ st'.scheduler = stM.scheduler := by
      subst hStep
      unfold Architecture.tlbFillOnCore Architecture.drainInitiatorPerCoreView
      split <;> exact ⟨rfl, rfl⟩
    unfold Architecture.vspaceMapPageCheckedWithShootdownFromState at hS
    dsimp only at hS
    cases hF : Architecture.vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st with
    | error e => rw [hF] at hS; cases hS
    | ok pr2 =>
      obtain ⟨u2, stF⟩ := pr2; cases u2
      rw [hF] at hS
      simp only at hS
      -- The optional round writes shootdown state alone.
      have hRound : stM.objects = stF.objects ∧ stM.scheduler = stF.scheduler := by
        split at hS
        · rw [Architecture.withShootdownRound_total] at hS
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
          subst hS
          exact ⟨(Architecture.tlbShootdownBroadcastCoalescing_frame stF ec _ _).1,
            (Architecture.tlbShootdownBroadcastCoalescing_frame stF ec _ _).2.1⟩
        · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
          subst hS; exact ⟨rfl, rfl⟩
      unfold Architecture.vspaceMapPageCheckedWithFlushFromState at hF
      split at hF
      · cases hF
      · split at hF
        · cases hF
        · split at hF
          · cases hF
          · unfold Architecture.vspaceMapPageWithFlush at hF
            cases hB : Architecture.vspaceMapPage asid vaddr paddr perms st with
            | error e => rw [hB] at hF; cases hF
            | ok pr3 =>
              obtain ⟨u3, stB⟩ := pr3; cases u3
              rw [hB] at hF
              simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hF
              subst hF
              obtain ⟨hInvB, hWB, hSchB⟩ :=
                vspaceMapPage_ok_frame asid vaddr paddr perms st stB hObjInv hB
              have hObjs : st'.objects = stB.objects := hTail.1.trans hRound.1
              refine ⟨hObjs ▸ hInvB, fun oid => ?_, hTail.2.trans (hRound.2.trans hSchB)⟩
              rw [hObjs]; exact hWB oid

/-- **The teardown** is a VSpace-root-only write that keeps the scheduler and the
object table's invariant. -/
theorem unmapLivePages_ok_frame (ec : Concurrency.CoreId) :
    ∀ (ps : List MappedPage) (st st' : SystemState),
      st.objects.invExt →
      unmapLivePages ec ps st = .ok ((), st') →
      st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler
  | [], st, st', hInv, hStep => by
      simp only [unmapLivePages, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      exact ⟨hInv, vspaceRootOnlyWrite.refl _, rfl⟩
  | p :: rest, st, st', hInv, hStep => by
      simp only [unmapLivePages] at hStep
      split at hStep
      · cases h1 : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast
            ec p.asid p.vaddr st with
        | error e => rw [h1] at hStep; cases hStep
        | ok pr =>
          obtain ⟨u, st1⟩ := pr; cases u
          rw [h1] at hStep
          obtain ⟨hInv1, hW1, hS1⟩ :=
            vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame ec p.asid p.vaddr
              st st1 hInv h1
          obtain ⟨hInv2, hW2, hS2⟩ := unmapLivePages_ok_frame ec rest st1 st' hInv1 hStep
          exact ⟨hInv2, hW1.trans hW2, hS2.trans hS1⟩
      · exact unmapLivePages_ok_frame ec rest st st' hInv hStep

-- ============================================================================
-- §3  Does any capability still name an object?
-- ============================================================================
--
-- Asked by the untyped reset (no capability may name a retired object) and by
-- capability finalisation (a page table whose last capability is destroyed
-- leaves its address space).  Moved here from `UntypedReset.lean` at
-- `v0.36.12` so both askers reach one answer.

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
      -- Slice 4b (`v0.36.10`): a thread's address space is named by its TCB's
      -- `vspaceRoot` field, not by a capability, so a carved root a thread
      -- still runs in is reached without one.
      ids.contains t.vspaceRoot ||
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

end SeLe4n.Kernel
