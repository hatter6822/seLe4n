-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.Capability.Invariant.Preservation.MappingRecords

/-! # The API arms keep the live mappings recorded

`SystemState.liveMappingsRecorded` (`Model/MappingRecords.lean`) says every
mapping an address space makes under a mapping epoch is recorded on a
capability to its frame.  This module proves that the arms defined over
`Kernel.API` keep it: the `.vspaceMap` arm, which adds a mapping and records it
on the capability that made it
(`vspaceMapFromFrameCap_preserves_liveMappingsRecorded`); the unmap and the
instruction-page unify, which only remove or keep mappings; the page-table
writes, which keep every object's kind and mapping view; and the reset, which
writes one free index.  The capability arms (copy, mint, move, the reply-cap
mint, the finalising delete, the revocation and the zombie delete) are in
`Capability/Invariant/Preservation/MappingRecords.lean`.  A write that keeps
each object's kind and mapping view keeps it too
(`SystemState.liveMappingsRecorded.of_kindPreservingWrite`).  The steps of
the other arms (the IPC paths with their capability transfer, the thread,
scheduling-context, notification, service, audit and fault arms, the scheduling
point, the timer tick and the retype) are each a `MappingStage`
(`Kernel/MappingRecordStage/*.lean`), and the thread-space set is proven in
`Capability/Invariant/Preservation/SetSpaceMappingRecords.lean`.  The
dispatchers and the kernel entries compose them
(`Kernel/MappingRecordStage/Dispatch.lean`, `Kernel/MappingRecordStage/Entry.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The map's page-table write
-- ============================================================================

/-- **One page-table map, exactly**: the root the ASID resolves to takes the new
translation, and no other key moves. -/
theorem vspaceMapPage_ok_objects {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {paddr : SeLe4n.PAddr} {perms : PagePermissions} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    ∃ (rootId : SeLe4n.ObjId) (root root' : VSpaceRoot),
      Architecture.resolveAsidRoot st asid = some (rootId, root) ∧
      root.mapPage vaddr paddr perms = some root' ∧
      st'.objects.invExt ∧ st'.objects[rootId]? = some (.vspaceRoot root') ∧
      ∀ k, k ≠ rootId → st'.objects[k]? = st.objects[k]? := by
  unfold Architecture.vspaceMapPage at h
  cases hRes : Architecture.resolveAsidRoot st asid with
  | none => rw [hRes] at h; cases h
  | some pr =>
    obtain ⟨rootId, root⟩ := pr
    rw [hRes] at h
    simp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hMp : root.mapPage vaddr paddr perms with
        | none => rw [hMp] at h; cases h
        | some root' =>
          rw [hMp] at h
          simp only at h
          exact ⟨rootId, root, root', rfl, hMp,
            storeObject_preserves_objects_invExt (Architecture.recordPhysicalWrites st _) _ _ _
              hObjInv h,
            storeObject_objects_eq (Architecture.recordPhysicalWrites st _) _ _ _ hObjInv h,
            fun k hk => storeObject_objects_ne (Architecture.recordPhysicalWrites st _) _ _ k _ hk
              hObjInv h⟩

/-- **The verified map the `.vspaceMap` arm runs writes the objects its
page-table write does**: the guards write nothing, and the flush, the shootdown
round, the drain and the fill write only TLB and shootdown state. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_objects
    (ec : Concurrency.CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) (st st' : SystemState)
    (hStep : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore ec asid vaddr
      paddr perms st = .ok ((), st')) :
    ∃ stB, Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), stB) ∧
      st'.objects = stB.objects := by
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore at hStep
  cases hS : Architecture.vspaceMapPageCheckedWithShootdownFromState ec asid vaddr paddr
      perms st with
  | error e => rw [hS] at hStep; cases hStep
  | ok pr =>
    obtain ⟨u, stM⟩ := pr; cases u
    rw [hS] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
    have hTail : st'.objects = stM.objects := by
      subst hStep
      unfold Architecture.tlbFillOnCore Architecture.drainInitiatorPerCoreView
      split
      · rfl
      · exact (Architecture.tlbInsertOnCore_frame _ _ _).1
    unfold Architecture.vspaceMapPageCheckedWithShootdownFromState at hS
    dsimp only at hS
    cases hF : Architecture.vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st with
    | error e => rw [hF] at hS; cases hS
    | ok pr2 =>
      obtain ⟨u2, stF⟩ := pr2; cases u2
      rw [hF] at hS
      simp only at hS
      have hRound : stM.objects = stF.objects := by
        split at hS
        · rw [Architecture.withShootdownRound_total] at hS
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
          subst hS
          exact (Architecture.tlbShootdownBroadcastCoalescing_frame stF ec _ _).1
        · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
          subst hS; rfl
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
              exact ⟨stB, rfl, hTail.trans hRound⟩

/-- **What `mapPage` makes**: the root with the one new translation, at an
address it did not map. -/
theorem VSpaceRoot.mapPage_some_eq {root root' : VSpaceRoot} {vaddr : SeLe4n.VAddr}
    {paddr : SeLe4n.PAddr} {perms : PagePermissions}
    (h : root.mapPage vaddr paddr perms = some root') :
    root.mappings[vaddr]? = none ∧
      root' = { root with mappings := root.mappings.insert vaddr (paddr, perms) } := by
  unfold VSpaceRoot.mapPage at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · next hNone => cases h; exact ⟨hNone, rfl⟩

/-- **A capability whose record is not live witnesses no live mapping**: on a
well-formed state, a record naming an address space's mapping under its epoch,
to the base of the frame the capability targets, is live
(`capabilityMappingLive`). -/
theorem slotWitnessesNoMapping_of_notLive {st : SystemState} {s : SlotRef} {cap : Capability}
    (hW : teardownWellFormed st) (hC : st.slotCapAt s = some cap)
    (hLive : capabilityMappingLive st cap = false) : st.slotWitnessesNoMapping s := by
  intro c fid f rid root v perms e hc ht hf hr hm he hmap
  rw [hC] at hc; cases hc
  have hG : st.getFrame? fid = some f := (SystemState.getFrame?_eq_some_iff st fid f).2 hf
  have hRes := resolveAsidRoot_of_root hW hr
  unfold capabilityMappingLive capabilityMappedPage mappedPageLive at hLive
  simp only [hmap, ht, hG, Option.map_some, hRes, VSpaceRoot.lookup, hm, he] at hLive
  simp at hLive

-- ============================================================================
-- §2  The `.vspaceMap` arm
-- ============================================================================

/-- **The `.vspaceMap` arm keeps every live mapping recorded.**  It adds one
mapping — the frame's base at the address, in the address space the ASID
resolves to, under the frame's current epoch — and records exactly that on the
capability it resolved, in that capability's own slot.  The record it
overwrites witnessed nothing: the arm refuses a capability whose record is live
(`capabilityMappingLive`), and on a well-formed state a record naming a mapping
an address space still makes is live (`slotWitnessesNoMapping_of_notLive`).  It
writes one root, one frame's epoch counter and one CNode slot, so every other
record keeps its slot and its frame's base. -/
theorem vspaceMapFromFrameCap_preserves_liveMappingsRecorded (tid : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (args : Architecture.SyscallArgDecode.VSpaceMapArgs) (st st' : SystemState)
    (hW : teardownWellFormed st) (hL : st.liveMappingsRecorded)
    (h : vspaceMapFromFrameCap tid ec args st = .ok ((), st')) :
    st'.liveMappingsRecorded := by
  obtain ⟨frameSlot, frameCap, frame, st1, hR, -, hLive, -, -, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid ec args st st' h
  obtain ⟨_, _, fid, _, _, _, _, hTgt, hGF, -, hSlotCap⟩ :=
    resolveVSpaceMapFrame_ok_authorised tid args st frameSlot frameCap frame hR
  have hFid : frameCapObjId frameCap = fid := by simp [frameCapObjId, hTgt]
  rw [hFid] at hT
  have hFr : st.objects[fid]? = some (.frame frame) := (SystemState.getFrame?_eq_some_iff _ _ _).1 hGF
  have hCap : st.slotCapAt frameSlot = some frameCap := SystemState.slotCapAt_of_lookupSlotCap hSlotCap
  -- The map: one root takes the translation.
  obtain ⟨stB, hB, hO1⟩ :=
    vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_objects _ _ _ _ _ st st1 hMap
  obtain ⟨rootId, root, root', hRes, hMp, hIB, hAtB, hNeB⟩ := vspaceMapPage_ok_objects hW.1 hB
  obtain ⟨hNone, rfl⟩ := VSpaceRoot.mapPage_some_eq hMp
  obtain ⟨-, hRoot, hAsid⟩ := Architecture.resolveAsidRoot_some_implies_obj st _ _ _ hRes
  have hI1 : st1.objects.invExt := hO1 ▸ hIB
  have hAt1 : st1.objects[rootId]? = some (.vspaceRoot
      { root with mappings := root.mappings.insert args.vaddr (frame.base, args.perms) }) :=
    hO1 ▸ hAtB
  have hNe1 : ∀ k, k ≠ rootId → st1.objects[k]? = st.objects[k]? := fun k hk => hO1 ▸ hNeB k hk
  have hFR : fid ≠ rootId := fun e => by subst e; rw [hFr] at hRoot; cases hRoot
  -- The tag: the same root takes the epoch, the frame its next counter.
  obtain ⟨f, rootId2, root2, stT, hF1, hRes1, hE, hS1, hS2⟩ :=
    tagFrameMapping_ok _ _ _ st1 st2 epoch hT
  subst hE
  have hfEq : frame = f := by
    rw [SystemState.getFrame?_eq_some_iff, hNe1 fid hFR, hFr] at hF1; cases hF1; rfl
  subst hfEq
  obtain ⟨-, hRoot2, hAsid2⟩ := Architecture.resolveAsidRoot_some_implies_obj st1 _ _ _ hRes1
  have hId2 : rootId = rootId2 := by
    by_cases hne : rootId2 = rootId
    · exact hne.symm
    exfalso
    rw [hNe1 _ hne] at hRoot2
    have h2 := resolveAsidRoot_of_root hW hRoot2
    rw [hAsid2, hRes] at h2
    cases h2; exact hne rfl
  subst hId2
  rw [hAt1] at hRoot2; cases hRoot2
  have hIT := storeObject_preserves_objects_invExt _ _ _ _ hI1 hS1
  have hI2 := storeObject_preserves_objects_invExt _ _ _ _ hIT hS2
  -- The record: the resolved slot's capability takes the mapping.
  obtain ⟨cn, cap, hCn, hLk, hS3⟩ := cspaceRecordFrameMapping_ok_decompose _ _ st2 st' hRec
  have hCn2 := (SystemState.getCNode?_eq_some_iff _ _ _).1 hCn
  have hCR : frameSlot.cnode ≠ rootId := fun e => by
    rw [e, storeObject_objects_ne _ _ _ _ _ hFR.symm hIT hS2,
      storeObject_objects_eq _ _ _ _ hI1 hS1] at hCn2; cases hCn2
  have hCF : frameSlot.cnode ≠ fid := fun e => by
    rw [e, storeObject_objects_eq _ _ _ _ hIT hS2] at hCn2; cases hCn2
  have hCnPre : st.objects[frameSlot.cnode]? = some (.cnode cn) := by
    rw [storeObject_objects_ne _ _ _ _ _ hCF hIT hS2, storeObject_objects_ne _ _ _ _ _ hCR hI1 hS1,
      hNe1 _ hCR] at hCn2
    exact hCn2
  have hCapEq : cap = frameCap := by
    rw [SystemState.slotCapAt_of_object hCnPre] at hCap
    exact Option.some.inj (hLk.symm.trans hCap)
  subst hCapEq
  -- The post-state, key by key.
  have hObj : ∀ k, st'.objects[k]? =
      if k = frameSlot.cnode then
        some (.cnode (cn.insert frameSlot.slot (cap.withMapping
          (some { asid := args.asid, vaddr := args.vaddr, epoch := frame.mapEpoch }))))
      else if k = fid then some (.frame { frame with mapEpoch := frame.mapEpoch + 1 })
      else if k = rootId then some (.vspaceRoot
        { root with mappings := root.mappings.insert args.vaddr (frame.base, args.perms),
                    mappingEpochs := root.mappingEpochs.insert args.vaddr frame.mapEpoch })
      else st.objects[k]? := by
    intro k
    by_cases h1 : k = frameSlot.cnode
    · subst h1; rw [if_pos rfl]; exact storeObject_objects_eq _ _ _ _ hI2 hS3
    rw [if_neg h1, storeObject_objects_ne _ _ _ _ _ h1 hI2 hS3]
    by_cases h2 : k = fid
    · subst h2; rw [if_pos rfl]; exact storeObject_objects_eq _ _ _ _ hIT hS2
    rw [if_neg h2, storeObject_objects_ne _ _ _ _ _ h2 hIT hS2]
    by_cases h3 : k = rootId
    · subst h3; rw [if_pos rfl]; exact storeObject_objects_eq _ _ _ _ hI1 hS1
    rw [if_neg h3, storeObject_objects_ne _ _ _ _ _ h3 hI1 hS1, hNe1 _ h3]
  have hWF := hW.2.2.2.2.2.2.2.2.2 rootId root hRoot
  have hMI : root.mappings.invExt := hWF.1.1
  have hEI : root.mappingEpochs.invExt := hWF.2.1
  refine SystemState.liveMappingsRecorded.of_step frameSlot args.asid args.vaddr frame.base
    frame.mapEpoch ?_ ?_ ?_ ?_ (slotWitnessesNoMapping_of_notLive hW hCap hLive) ?_ hL
  · intro rid r' v p perms e hR' hM hE'
    rw [hObj] at hR'
    by_cases h1 : rid = frameSlot.cnode
    · rw [if_pos h1] at hR'; cases hR'
    rw [if_neg h1] at hR'
    by_cases h2 : rid = fid
    · rw [if_pos h2] at hR'; cases hR'
    rw [if_neg h2] at hR'
    by_cases h3 : rid = rootId
    · rw [if_pos h3] at hR'; cases hR'
      subst h3
      simp only [RHTable_getElem?_eq_get?] at hM hE'
      by_cases hv : v = args.vaddr
      · subst hv
        rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hMI] at hM
        rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hEI] at hE'
        cases hM; cases hE'
        exact .inl ⟨hAsid, rfl, rfl, rfl⟩
      · have hne : ¬(args.vaddr == v) = true := fun hb => hv (eq_of_beq hb).symm
        rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _ hne hMI] at hM
        rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _ hne hEI] at hE'
        exact .inr ⟨root, hRoot, rfl, by rw [RHTable_getElem?_eq_get?]; exact hM,
          by rw [RHTable_getElem?_eq_get?]; exact hE'⟩
    · rw [if_neg h3] at hR'
      exact .inr ⟨r', hR', rfl, hM, hE'⟩
  · have hAddr := CNode.slotAddressable_of_lookup cn _ _ hLk
    refine ⟨frameSlot, cap.withMapping
      (some { asid := args.asid, vaddr := args.vaddr, epoch := frame.mapEpoch }), fid,
      { frame with mapEpoch := frame.mapEpoch + 1 }, ?_, ?_, ?_, rfl, ?_⟩
    · rw [SystemState.slotCapAt_eq_bind, hObj, if_pos rfl]
      exact CNode.lookup_insert_eq cn _ _ (CNode.slotsUnique_holds cn) hAddr
    · rw [← hTgt]; rfl
    · rw [hObj, if_neg (Ne.symm hCF), if_pos rfl]
    · simp [Capability.mapping, Capability.withMapping]
  · intro r c hr hc
    rw [SystemState.slotCapAt_eq_bind] at hc ⊢
    rw [hObj]
    by_cases h1 : r.cnode = frameSlot.cnode
    · rw [if_pos h1]
      rw [h1, hCnPre] at hc
      have hs : frameSlot.slot ≠ r.slot := fun e => hr (by
        cases r; cases frameSlot; simp_all)
      show (cn.insert frameSlot.slot _).lookup r.slot = some c
      rw [CNode.lookup_insert_ne cn _ _ _ hs (CNode.slotsUnique_holds cn)]
      exact hc
    rw [if_neg h1]
    by_cases h2 : r.cnode = fid
    · rw [h2, hFr] at hc; cases hc
    rw [if_neg h2]
    by_cases h3 : r.cnode = rootId
    · rw [h3, hRoot] at hc; cases hc
    rw [if_neg h3]
    exact hc
  · intro k g hg
    rw [hObj]
    by_cases h1 : k = frameSlot.cnode
    · rw [h1, hCnPre] at hg; cases hg
    rw [if_neg h1]
    by_cases h2 : k = fid
    · rw [if_pos h2]; rw [h2, hFr] at hg; cases hg; exact ⟨_, rfl, rfl⟩
    rw [if_neg h2]
    by_cases h3 : k = rootId
    · rw [h3, hRoot] at hg; cases hg
    rw [if_neg h3]
    exact ⟨g, hg, rfl⟩
  · intro k t' sl c hT hc
    rw [hObj] at hT
    by_cases h1 : k = frameSlot.cnode
    · rw [if_pos h1] at hT; cases hT
    rw [if_neg h1] at hT
    by_cases h2 : k = fid
    · rw [if_pos h2] at hT; cases hT
    rw [if_neg h2] at hT
    by_cases h3 : k = rootId
    · rw [if_pos h3] at hT; cases hT
    rw [if_neg h3] at hT
    exact .inr ⟨t', hT, hc⟩

-- ============================================================================
-- §3  The address-space arms that remove a mapping or touch none
-- ============================================================================

/-- **A store of one root that only loses translations and epochs keeps the
mappings recorded**: the root keeps its ASID, no slot or frame moves. -/
theorem liveMappingsRecorded_of_rootShrinkStore {st st' : SystemState} {rootId : SeLe4n.ObjId}
    {root root' : VSpaceRoot} (hRoot : st.objects[rootId]? = some (.vspaceRoot root))
    (hAt : st'.objects[rootId]? = some (.vspaceRoot root'))
    (hNe : ∀ k, k ≠ rootId → st'.objects[k]? = st.objects[k]?)
    (hAsid : root'.asid = root.asid)
    (hSub : ∀ (v : SeLe4n.VAddr) (e : SeLe4n.PAddr × PagePermissions),
      root'.mappings[v]? = some e → root.mappings[v]? = some e)
    (hEp : ∀ (v : SeLe4n.VAddr) (n : Nat), root'.mappingEpochs[v]? = some n →
      root.mappingEpochs[v]? = some n)
    (hL : st.liveMappingsRecorded) : st'.liveMappingsRecorded := by
  refine SystemState.liveMappingsRecorded.of_shrink (fun rid r' hR => ?_)
    (SystemState.mappingRecordsKept.of_fwd (fun r cap hc _ => ?_) (fun fid f hf => ?_))
    (SystemState.threadSlotsDrawnFrom.of_key rootId hNe fun t' hT => by rw [hAt] at hT; cases hT) hL
  · by_cases hk : rid = rootId
    · subst hk; rw [hAt] at hR; cases hR; exact ⟨root, hRoot, hAsid, hSub, hEp⟩
    · rw [hNe rid hk] at hR; exact ⟨r', hR, rfl, fun _ _ h => h, fun _ _ h => h⟩
  · refine ⟨r, cap, ?_, rfl, rfl⟩
    rw [SystemState.slotCapAt_eq_bind] at hc ⊢
    by_cases hk : r.cnode = rootId
    · rw [hk, hRoot] at hc; cases hc
    · rw [hNe _ hk]; exact hc
  · have hk : fid ≠ rootId := fun e => by subst e; rw [hRoot] at hf; cases hf
    exact ⟨f, (hNe fid hk).trans hf, rfl⟩

/-- **One page-table unmap keeps the mappings recorded**: its root loses the
address's translation and epoch, and nothing else moves. -/
theorem vspaceUnmapPage_preserves_liveMappingsRecorded {asid : SeLe4n.ASID}
    {vaddr : SeLe4n.VAddr} {st st' : SystemState} (hW : teardownWellFormed st)
    (hL : st.liveMappingsRecorded)
    (h : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    st'.liveMappingsRecorded := by
  unfold Architecture.vspaceUnmapPage at h
  cases hRes : Architecture.resolveAsidRoot st asid with
  | none => rw [hRes] at h; cases h
  | some pr =>
    obtain ⟨rootId, root⟩ := pr
    rw [hRes] at h
    simp only at h
    cases hUn : root.unmapPage vaddr with
    | none => rw [hUn] at h; cases h
    | some root' =>
      rw [hUn] at h
      simp only at h
      obtain ⟨-, hObj, -⟩ := Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hRes
      have hKK := hW.2.2.2.2.2.2.2.2.2 rootId root hObj
      exact liveMappingsRecorded_of_rootShrinkStore hObj
        (storeObject_objects_eq (Architecture.recordPhysicalWrites st _) _ _ _ hW.1 h)
        (fun k hk => storeObject_objects_ne (Architecture.recordPhysicalWrites st _) _ _ k _ hk
          hW.1 h)
        (VSpaceRoot.unmapPage_asid_eq root root' vaddr hUn)
        (Architecture.VSpaceRoot.unmapPage_mappings_sub root root' vaddr hKK.1 hUn)
        (Architecture.VSpaceRoot.unmapPage_mappingEpochs_sub root root' vaddr hKK.2 hUn) hL

/-- **The verified unmap the `.vspaceUnmap` arm runs writes the objects its
page-table erase does**: the flush, the shootdown round, the drain and the
instruction-cache broadcast write only TLB, shootdown and cache state. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_objects
    (ec : Concurrency.CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (hStep : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) :
    ∃ stU, Architecture.vspaceUnmapPage asid vaddr st = .ok ((), stU) ∧
      st'.objects = stU.objects := by
  unfold Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast at hStep
  cases hK : Architecture.vspaceUnmapPageWithShootdownPerCore ec asid vaddr st with
  | error e =>
    rw [(Architecture.withIcacheBroadcast_error_iff _ _ st e).mpr hK] at hStep
    cases hStep
  | ok pr =>
    obtain ⟨u, stK⟩ := pr; cases u
    obtain ⟨hObjsK, -⟩ := Architecture.withIcacheBroadcast_frame hK hStep
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
          exact ⟨stU, rfl, hObjsK⟩

/-- **The `.vspaceUnmap` arm keeps the mappings recorded**: it removes one
translation and its epoch, and records nothing a slot reads. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_liveMappingsRecorded
    (ec : Concurrency.CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState) (hW : teardownWellFormed st) (hL : st.liveMappingsRecorded)
    (h : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) : st'.liveMappingsRecorded := by
  obtain ⟨stU, hU, hO⟩ := vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_objects ec asid vaddr
    st st' h
  exact SystemState.liveMappingsRecorded.of_objects_eq hO
    (vspaceUnmapPage_preserves_liveMappingsRecorded hW hL hU)

/-- **The `.vspaceUnifyInstruction` arm keeps the mappings recorded**: a cache
operation, it writes no object. -/
theorem vspaceUnifyInstructionPage_preserves_liveMappingsRecorded {asid : SeLe4n.ASID}
    {vaddr : SeLe4n.VAddr} {st st' : SystemState} (hL : st.liveMappingsRecorded)
    (h : Architecture.vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    st'.liveMappingsRecorded :=
  SystemState.liveMappingsRecorded.of_objects_eq (Architecture.vspaceUnifyInstructionPage_frame h).1 hL

/-- **The page-table install keeps every object's kind and mapping facts**: it
stores the table with its install record and the root with one more table
slot, its ASID, translations and epochs unchanged. -/
theorem pageTableMap_kindPreservingWrite {tableId rootId : SeLe4n.ObjId} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState} (hObjInv : st.objects.invExt)
    (h : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    kindPreservingWrite st st' := by
  obtain ⟨table, root, level, st1, hT, hR, -, -, -, -, hS1, hS2⟩ :=
    Architecture.pageTableMap_ok tableId rootId vaddr st st' h
  have hTo := (SystemState.getPageTable?_eq_some_iff _ _ _).1 hT
  have hRo := (SystemState.getVSpaceRoot?_eq_some_iff _ _ _).1 hR
  have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS1
  have hNe : rootId ≠ tableId := fun e => by subst e; rw [hTo] at hRo; cases hRo
  have hR1 : st1.objects[rootId]? = some (.vspaceRoot root) := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hObjInv hS1]; exact hRo
  exact (storeObject_kindPreservingWrite hObjInv hS1 hTo rfl
      (by simp [KernelObject.objectType])).trans
    (storeObject_kindPreservingWrite (st := Architecture.recordPhysicalWrites st1 _) hI1 hS2 hR1
      rfl (by simp [KernelObject.objectType]))

/-- **The page-table removal keeps every object's kind and mapping facts**: it
clears the table's install record and, when its root still holds it, takes the
table slot out of the root. -/
theorem pageTableUnmap_kindPreservingWrite {tableId : SeLe4n.ObjId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : Architecture.pageTableUnmap tableId st = .ok ((), st')) :
    kindPreservingWrite st st' := by
  unfold Architecture.pageTableUnmap at h
  cases hT : st.getPageTable? tableId with
  | none => rw [hT] at h; cases h
  | some table =>
    rw [hT] at h
    have hTo := (SystemState.getPageTable?_eq_some_iff _ _ _).1 hT
    have hTab : ∀ {s'}, storeObject tableId (.pageTable table.uninstalled) st = .ok ((), s') →
        kindPreservingWrite st s' := fun hS =>
      storeObject_kindPreservingWrite hObjInv hS hTo rfl (by simp [KernelObject.objectType])
    simp only at h
    split at h
    · cases h; exact .refl st
    · next inst _ =>
      split at h
      · exact hTab h
      · next root hR =>
        have hRo := (SystemState.getVSpaceRoot?_eq_some_iff _ _ _).1 hR
        split at h
        · split at h
          · cases h
          · cases hS1 : storeObject tableId (.pageTable table.uninstalled) st with
            | error e => rw [hS1] at h; cases h
            | ok p =>
              obtain ⟨⟨⟩, st1⟩ := p
              rw [hS1] at h
              have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS1
              have hNe : inst.root ≠ tableId := fun e => by
                rw [e, hTo] at hRo; cases hRo
              have hR1 : st1.objects[inst.root]? = some (.vspaceRoot root) := by
                rw [storeObject_objects_ne _ _ _ _ _ hNe hObjInv hS1]; exact hRo
              exact (hTab hS1).trans
                (storeObject_kindPreservingWrite (st := Architecture.recordPhysicalWrites st1 _)
                  hI1 h hR1 rfl (by simp [KernelObject.objectType]))
        · exact hTab h

/-- **The `.pageTableMap` arm keeps the mappings recorded.** -/
theorem pageTableMap_preserves_liveMappingsRecorded {tableId rootId : SeLe4n.ObjId}
    {vaddr : SeLe4n.VAddr} {st st' : SystemState} (hObjInv : st.objects.invExt)
    (hL : st.liveMappingsRecorded)
    (h : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    st'.liveMappingsRecorded :=
  hL.of_kindPreservingWrite (pageTableMap_kindPreservingWrite hObjInv h)

/-- **The `.pageTableUnmap` arm keeps the mappings recorded.** -/
theorem pageTableUnmap_preserves_liveMappingsRecorded {tableId : SeLe4n.ObjId}
    {st st' : SystemState} (hObjInv : st.objects.invExt) (hL : st.liveMappingsRecorded)
    (h : Architecture.pageTableUnmap tableId st = .ok ((), st')) :
    st'.liveMappingsRecorded :=
  hL.of_kindPreservingWrite (pageTableUnmap_kindPreservingWrite hObjInv h)
/-! ## The reset

The reset writes only the free index of the invoked capability, which keeps
its target and its record. -/

/-- **The reset keeps every live mapping recorded.** -/
theorem untypedResetSlot_preserves_liveMappingsRecorded {srcCnode : SeLe4n.ObjId}
    {srcSlot : SeLe4n.Slot} {st st' : SystemState} (hInv : st.objects.invExt)
    (hL : st.liveMappingsRecorded) (h : untypedResetSlot srcCnode srcSlot st = .ok ((), st')) :
    st'.liveMappingsRecorded := by
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := untypedResetSlot_ok h
  exact setCapFreeIndex_preserves_liveMappingsRecorded hInv hL

/-- **The `.untypedReset` arm keeps every live mapping recorded.** -/
theorem untypedResetFromCap_preserves_liveMappingsRecorded (tid : SeLe4n.ThreadId)
    (srcAddr : SeLe4n.CPtr) {st st' : SystemState} (hInv : st.objects.invExt)
    (hL : st.liveMappingsRecorded) (h : untypedResetFromCap tid srcAddr st = .ok ((), st')) :
    st'.liveMappingsRecorded := by
  obtain ⟨_, _, _, _, _, hR⟩ := untypedResetFromCap_ok tid srcAddr st st' h
  exact untypedResetSlot_preserves_liveMappingsRecorded hInv hL hR

end SeLe4n.Kernel
