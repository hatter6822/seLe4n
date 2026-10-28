-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.VSpaceUnmapPerform
import SeLe4n.Model.TableReferences

/-!
# Page teardown — removing a list of mappings through the verified unmap

**WS-BP BP7.1 (`v0.36.7`).**  Destroying a frame capability removes the
mapping that capability made, and destroying a page table's last capability the
mappings it held (`cspaceDeleteSlotFinalising`, `cspaceRevokeCdtFinalising`) —
seL4's `finaliseCap` → `unmapPage`.  The removal is a list of `MappedPage`s, each removed
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

## The result is a theorem

The pass never refuses (`unmapLivePages_eq_ok_state`), and on a well-formed
state — every mapping table well formed, every root resolved by its own ASID
(`teardownWellFormed`) — no listed page is live after it
(`unmapLivePagesState_clears`, in `PageTeardownClears`).  Before `v0.36.110`
the callers decided that result afterwards and refused if it failed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  Live pages, and the teardown
-- ============================================================================

/-- **Is this page still mapped where it says?**  The address space the ASID
resolves to maps the virtual address, the translation names this physical page,
and — for a page a capability's record names — the address space's entry
carries the record's mapping epoch (`VSpaceRoot.mappingEpochs`).

The epoch clause is what makes a record identify *its own* mapping (PR #904
review, `v0.36.41`).  Without it, a record gone stale matched any later
translation of the same frame at the same address: an address space destroyed
when its last capability is deleted releases its ASID, a later carve may be handed that ASID,
and another capability to the frame may map it there — deleting the stale
capability then removed a mapping it never made.  The same held inside one
address space after an unmap through the address-space capability.  A page read
off an address space itself (`epoch = none`) is removed whatever made it. -/
def mappedPageLive (st : SystemState) (p : MappedPage) : Bool :=
  match Architecture.resolveAsidRoot st p.asid with
  | some (_, root) =>
    ((root.lookup p.vaddr).map Prod.fst) == some p.paddr &&
      match p.epoch with
      | none => true
      | some e => root.mappingEpochs[p.vaddr]? == some e
  | none => false

/-- WS-ZA ZA5.4: **`mappedPageLive` on a page's words**, for a page a
capability's record names (`epoch = some e`): the ASID's root, its entry at the
address and its epoch at the address are matched where they are read, so no
`MappedPage`, pair or `Option` is built (`mappedPageLive_eq_words`). -/
@[inline] def mappedPageLiveWords (st : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (epoch : Nat) : Bool :=
  match Architecture.resolveAsidRoot st asid with
  | some (_, root) =>
    (match root.mappings.getEntry? vaddr with
     | some e => e.value.1 == paddr
     | none => false) &&
      match root.mappingEpochs.getEntry? vaddr with
      | some e => e.value == epoch
      | none => false
  | none => false

theorem mappedPageLive_eq_words (st : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (epoch : Nat) :
    mappedPageLive st { asid := asid, vaddr := vaddr, paddr := paddr, epoch := some epoch } =
      mappedPageLiveWords st asid vaddr paddr epoch := by
  unfold mappedPageLive mappedPageLiveWords
  cases Architecture.resolveAsidRoot st asid with
  | none => rfl
  | some pr =>
    obtain ⟨_, root⟩ := pr
    dsimp only
    have h1 : root.lookup vaddr = (root.mappings.getEntry? vaddr).map (·.value) := by
      show root.mappings.get? vaddr = _
      rw [SeLe4n.Kernel.RobinHood.RHTable.get?_eq_getEntry?_map]
    have h2 : root.mappingEpochs[vaddr]? = (root.mappingEpochs.getEntry? vaddr).map (·.value) := by
      show root.mappingEpochs.get? vaddr = _
      rw [SeLe4n.Kernel.RobinHood.RHTable.get?_eq_getEntry?_map]
    rw [h1, h2]
    cases root.mappings.getEntry? vaddr <;> cases root.mappingEpochs.getEntry? vaddr <;> rfl

/-- **PR #904 review (`v0.36.41`): give a capability's new mapping its epoch.**
The frame's current `mapEpoch` is written beside the translation in the address
space the ASID resolves to (`VSpaceRoot.mappingEpochs`), the frame's counter
advances, and the epoch is returned for the capability's record.  Run by
`.vspaceMap` right after the translation is installed, so the address space
resolves (a failure is `.illegalState`, never a partial tag). -/
def tagFrameMapping (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (frameId : SeLe4n.ObjId) : Kernel Nat :=
  fun st =>
    match st.getFrame? frameId, Architecture.resolveAsidRoot st asid with
    | some f, some (rootId, root) =>
      match storeObject rootId
          (.vspaceRoot { root with mappingEpochs := root.mappingEpochs.insert vaddr f.mapEpoch })
          st with
      | .error e => .error e
      | .ok ((), st1) =>
        match storeObject frameId (.frame { f with mapEpoch := f.mapEpoch + 1 }) st1 with
        | .error e => .error e
        | .ok ((), st2) => .ok (f.mapEpoch, st2)
    | _, _ => .error .illegalState

/-- **The tag, decomposed**: the frame and the address space resolved, the epoch
handed back is the frame's counter before the step, and the step is those two
stores in that order. -/
theorem tagFrameMapping_ok (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (frameId : SeLe4n.ObjId) (st st' : SystemState) (e : Nat)
    (h : tagFrameMapping asid vaddr frameId st = .ok (e, st')) :
    ∃ (f : FrameObject) (rootId : SeLe4n.ObjId) (root : VSpaceRoot) (st1 : SystemState),
      st.getFrame? frameId = some f ∧
      Architecture.resolveAsidRoot st asid = some (rootId, root) ∧
      e = f.mapEpoch ∧
      storeObject rootId
        (.vspaceRoot { root with mappingEpochs := root.mappingEpochs.insert vaddr f.mapEpoch })
        st = .ok ((), st1) ∧
      storeObject frameId (.frame { f with mapEpoch := f.mapEpoch + 1 }) st1
        = .ok ((), st') := by
  unfold tagFrameMapping at h
  cases hF : st.getFrame? frameId with
  | none => rw [hF] at h; cases h
  | some f =>
    cases hR : Architecture.resolveAsidRoot st asid with
    | none => rw [hF, hR] at h; cases h
    | some pr =>
      obtain ⟨rootId, root⟩ := pr
      rw [hF, hR] at h
      simp only at h
      cases h1 : storeObject rootId
          (.vspaceRoot { root with mappingEpochs := root.mappingEpochs.insert vaddr f.mapEpoch })
          st with
      | error err => rw [h1] at h; cases h
      | ok p1 =>
        obtain ⟨u, st1⟩ := p1; cases u
        rw [h1] at h
        simp only at h
        cases h2 : storeObject frameId (.frame { f with mapEpoch := f.mapEpoch + 1 }) st1 with
        | error err => rw [h2] at h; cases h
        | ok p2 =>
          obtain ⟨u, st2⟩ := p2; cases u
          rw [h2] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨f, rootId, root, st1, rfl, rfl, rfl, h1, h2⟩

/-- The tag writes neither the scheduler nor the machine — two object stores. -/
theorem tagFrameMapping_scheduler_machine (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (frameId : SeLe4n.ObjId) (st st' : SystemState) (e : Nat)
    (h : tagFrameMapping asid vaddr frameId st = .ok (e, st')) :
    st'.scheduler = st.scheduler ∧ st'.machine = st.machine := by
  obtain ⟨_, _, _, st1, -, -, -, h1, h2⟩ := tagFrameMapping_ok asid vaddr frameId st st' e h
  exact ⟨by rw [storeObject_scheduler_eq st1 st' _ _ h2, storeObject_scheduler_eq st st1 _ _ h1],
    by rw [storeObject_machine_eq st1 st' _ _ h2, storeObject_machine_eq st st1 _ _ h1]⟩

/-- **What the tag can change**: the scheduler and the machine are untouched, the
object store stays well-formed, and at every key the object is unchanged, or a
VSpace root on both sides, or a frame on both sides — so a CNode, a TCB and every
other kind survive it exactly. -/
theorem tagFrameMapping_ok_frame (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (frameId : SeLe4n.ObjId) (st st' : SystemState) (e : Nat)
    (hObjInv : st.objects.invExt)
    (h : tagFrameMapping asid vaddr frameId st = .ok (e, st')) :
    st'.objects.invExt ∧ st'.scheduler = st.scheduler ∧ st'.machine = st.machine ∧
    ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
      ((∃ r, st.objects[oid]? = some (.vspaceRoot r)) ∧
        (∃ r', st'.objects[oid]? = some (.vspaceRoot r'))) ∨
      ((∃ g, st.objects[oid]? = some (.frame g)) ∧
        (∃ g', st'.objects[oid]? = some (.frame g'))) := by
  obtain ⟨f, rootId, root, st1, hF, hR, -, h1, h2⟩ :=
    tagFrameMapping_ok asid vaddr frameId st st' e h
  have hInv1 := storeObject_preserves_objects_invExt st st1 _ _ hObjInv h1
  have hInv2 := storeObject_preserves_objects_invExt st1 st' _ _ hInv1 h2
  have hRootPre := (Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hR).2.1
  have hFramePre := (SystemState.getFrame?_eq_some_iff st frameId f).mp hF
  have hNe : frameId ≠ rootId := by
    intro hEq; rw [hEq, hRootPre] at hFramePre; cases hFramePre
  refine ⟨hInv2, ?_, ?_, ?_⟩
  · rw [storeObject_scheduler_eq st1 st' _ _ h2, storeObject_scheduler_eq st st1 _ _ h1]
  · rw [storeObject_machine_eq st1 st' _ _ h2, storeObject_machine_eq st st1 _ _ h1]
  · intro oid
    by_cases hF' : oid = frameId
    · subst hF'
      refine Or.inr (Or.inr ⟨⟨f, hFramePre⟩, ⟨_, storeObject_objects_eq st1 st' _ _ hInv1 h2⟩⟩)
    · by_cases hR' : oid = rootId
      · subst hR'
        rw [storeObject_objects_ne st1 st' _ _ _ hF' hInv1 h2]
        exact Or.inr (Or.inl ⟨⟨root, hRootPre⟩, ⟨_, storeObject_objects_eq st st1 _ _ hObjInv h1⟩⟩)
      · left
        rw [storeObject_objects_ne st1 st' _ _ _ hF' hInv1 h2,
          storeObject_objects_ne st st1 _ _ _ hR' hObjInv h1]

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

/-- **The state a store leaves.**  `storeObject` never refuses
(`storeObject_isOk`), so a step that cannot fail reads its state off it. -/
@[inline] def storeObjectState (id : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState) :
    SystemState :=
  match storeObject id obj st with
  | .ok ((), st') => st'
  | .error _ => st

theorem storeObject_eq_storeObjectState (id : SeLe4n.ObjId) (obj : KernelObject)
    (st : SystemState) : storeObject id obj st = .ok ((), storeObjectState id obj st) := rfl

/-- WS-ZA ZA5.3: **one page's unmap, as a step that cannot fail.**  The ASID's
root and the root without the page are read before any write; when either is
missing the page is not mapped and the state is left as it is.  Otherwise it is
`vspaceUnmapPageWithShootdownAndIcacheBroadcast` written out: the root stored
without the page, the local flush, the shootdown round, the initiator's drain,
and the instruction-cache broadcast the mapping owes
(`vspaceUnmap_eq_unmapPageState`). -/
def unmapPageState (executingCore : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (st : SystemState) : SystemState :=
  match Architecture.resolveAsidRoot st asid with
  | none => st
  | some (rootId, root) =>
    match root.unmapPage vaddr with
    | none => st
    | some root' =>
      let op? := Architecture.unmapIcacheOperand st asid vaddr
      let st1 := storeObjectState rootId (.vspaceRoot root')
        (Architecture.recordPhysicalWrites st (Architecture.mappingStore? st root' vaddr).toList)
      let inv := Architecture.encodePageInvalidation asid vaddr
      let st2 := Architecture.drainInitiatorPerCoreView
        (Architecture.tlbShootdownBroadcastCoalescing
          { st1 with tlb := adapterFlushTlbByVAddr st1.tlb asid vaddr } executingCore
          (Architecture.shootdownTargets executingCore) inv) executingCore [inv]
      match op? with
      | none => st2
      | some op =>
        Architecture.recordIcacheMaintenance
          (Architecture.icInvalidateBroadcast st2 Architecture.icBroadcastReach op) op

/-- The unmap the teardown runs succeeds as `unmapPageState` wherever the ASID
resolves and its root maps the address. -/
theorem vspaceUnmap_eq_unmapPageState (ec : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (st : SystemState) (rootId : SeLe4n.ObjId) (root root' : VSpaceRoot)
    (hR : Architecture.resolveAsidRoot st asid = some (rootId, root))
    (hU : root.unmapPage vaddr = some root') :
    Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st =
      .ok ((), unmapPageState ec asid vaddr st) := by
  unfold Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast
    Architecture.withIcacheBroadcast Architecture.vspaceUnmapPageWithShootdownPerCore
    Architecture.vspaceUnmapPageWithShootdown Architecture.vspaceUnmapPageWithFlush
    Architecture.vspaceUnmapPage Architecture.withShootdownRound unmapPageState
  rw [hR]
  simp only [hU, storeObject_eq_storeObjectState]
  cases Architecture.unmapIcacheOperand st asid vaddr <;> rfl

/-- WS-ZA ZA5.4: **the teardown's unmap, in place where it is admitted** — the
unmap's checks (`vspaceUnmapAdmittedAt`) on the root the ASID resolves to, then
its writes in the root's slot (`vspaceUnmapPerformAt`); any other state runs
`unmapPageState`.  `unmapPageState_eq_inPlace` is the equality, so a revoke or
delete that destroys a mapped frame no longer copies the root to erase it. -/
def unmapPageStateInPlace (executingCore : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (st : SystemState) : SystemState :=
  match Architecture.resolveAsidRoot st asid with
  | none => st
  | some (rootId, _) =>
    if vspaceUnmapAdmittedAt st asid vaddr rootId then
      vspaceUnmapPerformAt executingCore asid vaddr rootId st
    else unmapPageState executingCore asid vaddr st

@[csimp] theorem unmapPageState_eq_inPlace : @unmapPageState = @unmapPageStateInPlace := by
  funext ec asid vaddr st
  unfold unmapPageStateInPlace
  cases hR : Architecture.resolveAsidRoot st asid with
  | none => unfold unmapPageState; rw [hR]
  | some p =>
    obtain ⟨rootId, root⟩ := p
    dsimp only
    split
    · next hA =>
      have hA' := hA
      unfold vspaceUnmapAdmittedAt at hA'
      obtain ⟨-, hObj, -⟩ := Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hR
      have hGR : st.getVSpaceRoot? rootId = some root := by
        simp only [SystemState.getVSpaceRoot?, hObj]
      simp only [hGR, Bool.and_eq_true, Option.isSome_iff_exists] at hA'
      obtain ⟨⟨⟨-, e, hE⟩, -⟩, -⟩ := hA'
      have hU : root.unmapPage vaddr =
          some { root with mappings := root.mappings.erase vaddr,
                           mappingEpochs := root.mappingEpochs.erase vaddr } := by
        unfold VSpaceRoot.unmapPage; rw [hE]
      have h1 := vspaceUnmap_eq_unmapPageState ec asid vaddr st rootId root _ hR hU
      rw [vspaceUnmapPageWithShootdownAndIcacheBroadcast_of_admitted ec asid vaddr rootId st hA] at h1
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h1
      exact h1.symm
    · rfl

/-- **Is the page mapped?**  A live page's ASID resolves and its root maps the
address, so its unmap succeeds. -/
theorem mappedPageLive_unmapPage {st : SystemState} {p : MappedPage}
    (h : mappedPageLive st p = true) :
    ∃ rootId root root', Architecture.resolveAsidRoot st p.asid = some (rootId, root) ∧
      root.unmapPage p.vaddr = some root' := by
  unfold mappedPageLive at h
  cases hR : Architecture.resolveAsidRoot st p.asid with
  | none => rw [hR] at h; cases h
  | some pr =>
    obtain ⟨rootId, root⟩ := pr
    rw [hR] at h
    simp only at h
    cases hL : root.mappings[p.vaddr]? with
    | none =>
      have hN : root.lookup p.vaddr = none := hL
      rw [hN] at h
      simp at h
    | some e =>
      exact ⟨rootId, root, { root with mappings := root.mappings.erase p.vaddr,
                                       mappingEpochs := root.mappingEpochs.erase p.vaddr }, rfl,
        by simp [VSpaceRoot.unmapPage, hL]⟩

/-- WS-ZA ZA5.3: **the teardown, as a step that cannot fail**: each listed page
still live is unmapped (`unmapPageState`), in order; the compiled
`unmapLivePages` (`unmapLivePages_eq_impl`). -/
def unmapLivePagesState (executingCore : Concurrency.CoreId) :
    List MappedPage → SystemState → SystemState
  | [], st => st
  | p :: rest, st =>
      if mappedPageLive st p then
        unmapLivePagesState executingCore rest (unmapPageState executingCore p.asid p.vaddr st)
      else unmapLivePagesState executingCore rest st

theorem unmapLivePages_eq_ok_state (ec : Concurrency.CoreId) :
    ∀ (ps : List MappedPage) (st : SystemState),
      unmapLivePages ec ps st = .ok ((), unmapLivePagesState ec ps st)
  | [], _ => rfl
  | p :: rest, st => by
    unfold unmapLivePages unmapLivePagesState
    split
    · next hL =>
      obtain ⟨rootId, root, root', hR, hU⟩ := mappedPageLive_unmapPage hL
      rw [vspaceUnmap_eq_unmapPageState ec p.asid p.vaddr st rootId root root' hR hU]
      exact unmapLivePages_eq_ok_state ec rest _
    · exact unmapLivePages_eq_ok_state ec rest st

/-- The teardown never refuses: compiled, it is `unmapLivePagesState`. -/
@[inline] def unmapLivePagesImpl (executingCore : Concurrency.CoreId) (ps : List MappedPage) :
    Kernel Unit :=
  fun st => .ok ((), unmapLivePagesState executingCore ps st)

@[csimp] theorem unmapLivePages_eq_impl : @unmapLivePages = @unmapLivePagesImpl := by
  funext ec ps st
  exact unmapLivePages_eq_ok_state ec ps st

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
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler ∧
      st'.referenceTables = st.referenceTables := by
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
        (by have h := storeObject_scheduler_eq _ _ _ _ hStep; exact h),
        (storeObject_referenceTables hStep).trans rfl⟩
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
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler ∧
      st'.referenceTables = st.referenceTables := by
  unfold Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast at hStep
  cases hK : Architecture.vspaceUnmapPageWithShootdownPerCore ec asid vaddr st with
  | error e =>
    rw [(Architecture.withIcacheBroadcast_error_iff _ _ st e).mpr hK] at hStep
    cases hStep
  | ok pr =>
    obtain ⟨u, stK⟩ := pr; cases u
    obtain ⟨hObjsK, -, hSchedK, -, -, -, -, hIrqK⟩ :=
      Architecture.withIcacheBroadcast_frame hK hStep
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
          obtain ⟨hInvU, hWU, hSchU, hTU⟩ := vspaceUnmapPage_ok_frame asid vaddr st stU hObjInv hU
          have hObjs : st'.objects = stU.objects := hObjsK
          have hSch : st'.scheduler = stU.scheduler := hSchedK
          have hT : st'.referenceTables = stU.referenceTables := by
            simp only [SystemState.referenceTables, hIrqK]; rfl
          refine ⟨hObjs ▸ hInvU, fun oid => ?_, hSch.trans hSchU, hT.trans hTU⟩
          rw [hObjs]; exact hWU oid

/-- **One page-table map** stores a VSpace root at the key the ASID resolved to,
which held a VSpace root; nothing else moves in the object store.  The map's twin
of `vspaceUnmapPage_ok_frame`. -/
theorem vspaceMapPage_ok_frame (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler ∧
      st'.referenceTables = st.referenceTables := by
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
            (by have h := storeObject_scheduler_eq _ _ _ _ hStep; exact h),
            (storeObject_referenceTables hStep).trans rfl⟩
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
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler ∧
      st'.referenceTables = st.referenceTables := by
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore at hStep
  cases hS : Architecture.vspaceMapPageCheckedWithShootdownFromState ec asid vaddr paddr
      perms st with
  | error e => rw [hS] at hStep; cases hStep
  | ok pr =>
    obtain ⟨u, stM⟩ := pr; cases u
    rw [hS] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
    -- The drain and the fill write `perCoreTlb` alone.
    have hTail : st'.objects = stM.objects ∧ st'.scheduler = stM.scheduler ∧
        st'.referenceTables = stM.referenceTables := by
      subst hStep
      unfold Architecture.tlbFillOnCore Architecture.drainInitiatorPerCoreView
      split
      · exact ⟨rfl, rfl, rfl⟩
      · exact ⟨(Architecture.tlbInsertOnCore_frame _ _ _).1,
          (Architecture.tlbInsertOnCore_frame _ _ _).2.2.1, by
            unfold Architecture.tlbInsertOnCore; split <;> rfl⟩
    unfold Architecture.vspaceMapPageCheckedWithShootdownFromState at hS
    dsimp only at hS
    cases hF : Architecture.vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st with
    | error e => rw [hF] at hS; cases hS
    | ok pr2 =>
      obtain ⟨u2, stF⟩ := pr2; cases u2
      rw [hF] at hS
      simp only at hS
      -- The optional round writes shootdown state alone.
      have hRound : stM.objects = stF.objects ∧ stM.scheduler = stF.scheduler ∧
          stM.referenceTables = stF.referenceTables := by
        split at hS
        · rw [Architecture.withShootdownRound_total] at hS
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
          subst hS
          exact ⟨(Architecture.tlbShootdownBroadcastCoalescing_frame stF ec _ _).1,
            (Architecture.tlbShootdownBroadcastCoalescing_frame stF ec _ _).2.1, rfl⟩
        · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
          subst hS; exact ⟨rfl, rfl, rfl⟩
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
              obtain ⟨hInvB, hWB, hSchB, hTB⟩ :=
                vspaceMapPage_ok_frame asid vaddr paddr perms st stB hObjInv hB
              have hObjs : st'.objects = stB.objects := hTail.1.trans hRound.1
              refine ⟨hObjs ▸ hInvB, fun oid => ?_, hTail.2.1.trans (hRound.2.1.trans hSchB),
                hTail.2.2.trans (hRound.2.2.trans (Eq.trans rfl hTB))⟩
              rw [hObjs]; exact hWB oid

/-- **The teardown** is a VSpace-root-only write that keeps the scheduler and the
object table's invariant. -/
theorem unmapLivePages_ok_frame (ec : Concurrency.CoreId) :
    ∀ (ps : List MappedPage) (st st' : SystemState),
      st.objects.invExt →
      unmapLivePages ec ps st = .ok ((), st') →
      st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler ∧
        st'.referenceTables = st.referenceTables
  | [], st, st', hInv, hStep => by
      simp only [unmapLivePages, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      exact ⟨hInv, vspaceRootOnlyWrite.refl _, rfl, rfl⟩
  | p :: rest, st, st', hInv, hStep => by
      simp only [unmapLivePages] at hStep
      split at hStep
      · cases h1 : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast
            ec p.asid p.vaddr st with
        | error e => rw [h1] at hStep; cases hStep
        | ok pr =>
          obtain ⟨u, st1⟩ := pr; cases u
          rw [h1] at hStep
          obtain ⟨hInv1, hW1, hS1, hT1⟩ :=
            vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame ec p.asid p.vaddr
              st st1 hInv h1
          obtain ⟨hInv2, hW2, hS2, hT2⟩ := unmapLivePages_ok_frame ec rest st1 st' hInv1 hStep
          exact ⟨hInv2, hW1.trans hW2, hS2.trans hS1, hT2.trans hT1⟩
      · exact unmapLivePages_ok_frame ec rest st st' hInv hStep

end SeLe4n.Kernel
