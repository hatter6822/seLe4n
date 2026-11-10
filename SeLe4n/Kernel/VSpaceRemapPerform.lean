-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.VSpacePerform

/-!
# The frame remap, in place

seL4's `seL4_ARM_Page_Map` on a frame capability whose recorded mapping is in
place remaps it (`vspaceMapOrRemapFromFrameCap`): the mapping is taken down
where it stands and the frame mapped again with the rights the call asks for.
This module is the remap's compiled form: its refusals and in-place conditions
read before any write (`vspaceRemapRefusal`, `vspaceRemapInPlaceAt`), then the
unmap in place (`vspaceUnmapPerformAt`) and the map in place on the state it
leaves (`vspaceMapPerformAt`, admitted there by
`vspaceMapAdmittedAt_of_remapInPlace`), proven equal to the specification
(`vspaceMapOrRemapFromFrameCap_of_remapAdmitted`).
-/
namespace SeLe4n.Kernel
open SeLe4n.Model

open SeLe4n.Kernel.RobinHood in
/-- The unmap's writes, read at the object table, the ASID table and the
machine: the root rewritten in its slot without the mapping, the rest as it
was. -/
theorem vspaceUnmapPerformAt_fields {ec : Concurrency.CoreId} {asid : SeLe4n.ASID}
    {vaddr : SeLe4n.VAddr} {rootId : SeLe4n.ObjId} {st : SystemState} {root : VSpaceRoot}
    (hR : st.objects[rootId]? = some (.vspaceRoot root))
    (hH : st.asidTable.holds root.asid rootId = true) :
    (vspaceUnmapPerformAt ec asid vaddr rootId st).objects =
        st.objects.insert rootId (.vspaceRoot (rootWithoutMapping vaddr root)) ∧
      (vspaceUnmapPerformAt ec asid vaddr rootId st).asidTable = st.asidTable ∧
      (vspaceUnmapPerformAt ec asid vaddr rootId st).machine = st.machine := by
  have hf : (rootWithoutMapping vaddr root).asid = root.asid := rfl
  have hO := SystemState.storeVSpaceRootWith_objects hR (rootWithoutMapping vaddr) hf
  have hA := SystemState.storeVSpaceRootWith_asidTable hR (rootWithoutMapping vaddr) hf hH
  have hM : (st.storeVSpaceRootWith rootId (rootWithoutMapping vaddr)).machine = st.machine := by
    have hS := SystemState.storeObject_vspaceRoot_eq_storeVSpaceRootWith hR
      (rootWithoutMapping vaddr) hf
    unfold storeObject at hS
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
    rw [← hS]
  unfold vspaceUnmapPerformAt
  dsimp only
  cases Architecture.unmapIcacheOperand st asid vaddr <;>
    simp [Architecture.drainInitiatorPageOnCore, Architecture.drainInitiatorPerCoreView,
      Architecture.setTlbOnCore, Architecture.recordPhysicalWrites_objects,
      Architecture.recordPhysicalWrites_asidTable, Architecture.recordPhysicalWrites_machine,
      Architecture.tlbShootdownBroadcastPage_eq, Architecture.tlbShootdownBroadcastCoalescing,
      Architecture.recordIcacheMaintenance, Architecture.icInvalidateBroadcast, hO, hA, hM]

/-- A frame resolution reads threads, CNodes and frames alone. -/
theorem resolveVSpaceMapFrame_congr {s t : SystemState} (tid : SeLe4n.ThreadId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (hT : ∀ id, s.getTcb? id = t.getTcb? id) (hC : ∀ id, s.getCNode? id = t.getCNode? id)
    (hF : ∀ id, s.getFrame? id = t.getFrame? id) :
    resolveVSpaceMapFrame tid args s = resolveVSpaceMapFrame tid args t := by
  unfold resolveVSpaceMapFrame syscallLookupCap syscallResolveCap
  rw [hT]
  split
  · rfl
  · next tcb _ =>
    rw [hC]
    split
    · rfl
    · next cn _ =>
      dsimp only
      simp only [resolveCapAddress_congr_getCNode? s t hC, lookupSlotCap_congr_getCNode? s t hC, hF]
      cases resolveCapAddress tcb.cspaceRoot args.frame cn.depth t with
      | error e => rfl
      | ok ref =>
        dsimp only
        cases t.lookupSlotCap ref with
        | none => rfl
        | some cap =>
          dsimp only
          by_cases h1 : capTargetsReservedKernelObject cap = true
          · simp [h1]
          · simp only [h1, Bool.false_eq_true, ↓reduceIte]
            by_cases h2 : cap.hasRight AccessRight.read = true
            · simp only [h2, ↓reduceIte]
            · simp [h2]

/-- **The remap's in-place conditions**, read before any write: the unmap of
the address is admitted in place (`vspaceUnmapAdmittedAt`), the root holds the
address in one slot only, so the unmap's erase leaves it absent
(`RHTable.keyOnlyAt`), and the frame's object is rewritten in its slot.  With
the remap's refusals passed (`vspaceRemapRefusal`), these are what make the
map half admitted on the state the unmap leaves
(`vspaceMapAdmittedAt_of_remapInPlace`).  Inline, so the decoded arguments are
read as words and no record of them is built. -/
@[inline] def vspaceRemapInPlaceAt (st : SystemState)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs) (frameCap : Capability)
    (rootId : SeLe4n.ObjId) : Bool :=
  vspaceUnmapAdmittedAt st args.asid args.vaddr rootId &&
  (match st.getVSpaceRoot? rootId with
   | some root => root.mappings.keyOnlyAt args.vaddr
   | none => false) &&
  st.objects.findsInPlace (frameCapObjId frameCap)

/-- What a remap that passes its refusals has established, one fact per check. -/
theorem vspaceRemapRefusal_ok {st : SystemState}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {frameCap : Capability}
    {frame : FrameObject} (h : vspaceRemapRefusal st args frameCap frame = .ok ()) :
    ∃ oid root, Architecture.resolveAsidRoot st args.asid = some (oid, root) ∧
      Architecture.pageMappingAligned args.vaddr frame.base = true ∧
      frameCap.mapAsid = args.asid ∧ frameCap.mapVaddr = args.vaddr ∧
      root.translationReady args.vaddr = true ∧
      frameMappingAdmissible frameCap frame args.perms = .ok () ∧
      args.vaddr.inUserWindow = true ∧
      (∃ p, Architecture.SyscallArgDecode.validateVSpaceMapPermsForMemoryKind frame.base
        args.perms st.machine.memoryMap = .ok p) ∧
      args.vaddr.isCanonical = true ∧
      frame.base.toNat < 2 ^ st.machine.physicalAddressWidth ∧
      args.perms.wxCompliant = true := by
  unfold vspaceRemapRefusal at h
  split at h
  · cases h
  next oid root hRes =>
  split at h
  · cases h
  next h1 =>
  split at h
  · cases h
  next h2 =>
  split at h
  · cases h
  next h3 =>
  split at h
  · cases h
  next h4 =>
  split at h
  · cases h
  next hAd =>
  split at h
  · cases h
  next h5 =>
  split at h
  · cases h
  next p hV =>
  split at h
  · cases h
  next h6 =>
  split at h
  · cases h
  next h7 =>
  split at h
  · cases h
  next h8 =>
  exact ⟨oid, root, hRes, by simpa using h1, by simpa using h2, by simpa using h3,
    by simpa using h4, hAd, by simpa using h5, ⟨p, hV⟩, by simpa using h6, by simpa using h7,
    by simpa using h8⟩

/-- A capability whose recorded address its address space no longer maps has
no live mapping. -/
theorem capabilityMappingLive_of_lookup_none {st : SystemState} {cap : Capability}
    {rootId : SeLe4n.ObjId} {root : VSpaceRoot}
    (hRes : Architecture.resolveAsidRoot st cap.mapAsid = some (rootId, root))
    (hL : root.lookup cap.mapVaddr = none) : capabilityMappingLive st cap = false := by
  unfold capabilityMappingLive capabilityMappedPage
  rw [Capability.mapping]
  by_cases hM : cap.mapped = true
  · simp only [hM, ↓reduceIte]
    cases cap.target with
    | object frameId =>
      cases hF : st.getFrame? frameId with
      | none => simp [hF]
      | some f => simp [hF, mappedPageLive, hRes, hL]
    | _ => rfl
  · simp [hM]

open SeLe4n.Kernel.RobinHood in
/-- **A remap's map half is admitted on the state its unmap leaves**: the
refusals passed before the unmap, and the unmap clears exactly the two the
fresh mapping adds — the capability's live record and the address already
mapped — so nothing it leaves behind refuses the map. -/
theorem vspaceMapAdmittedAt_of_remapInPlace (ec : Concurrency.CoreId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs) (st : SystemState)
    (frameCap : Capability) (frame : FrameObject) (rootId : SeLe4n.ObjId)
    (hRf : vspaceRemapRefusal st args frameCap frame = .ok ())
    (hIn : vspaceRemapInPlaceAt st args frameCap rootId = true) :
    vspaceMapAdmittedAt (vspaceUnmapPerformAt ec args.asid args.vaddr rootId st) args frameCap
      frame rootId = true := by
  obtain ⟨oid, root0, hRes0, hAl, hAs, hVa, hTr, hAd, hWin, ⟨p, hV⟩, hCan, hPa, hWx⟩ :=
    vspaceRemapRefusal_ok hRf
  unfold vspaceRemapInPlaceAt at hIn
  simp only [Bool.and_eq_true] at hIn
  obtain ⟨⟨hU, hK⟩, hFF⟩ := hIn
  unfold vspaceUnmapAdmittedAt at hU
  cases hGR : st.getVSpaceRoot? rootId with
  | none => simp [hGR] at hU
  | some root =>
  have hR : st.objects[rootId]? = some (.vspaceRoot root) :=
    (SystemState.getVSpaceRoot?_eq_some_iff st rootId root).1 hGR
  simp only [hGR, Bool.and_eq_true, beq_iff_eq] at hU hK
  obtain ⟨⟨⟨hRA, -⟩, hH⟩, hInR⟩ := hU
  have hRes := resolveAsidRoot_of_holds hH hR hRA
  rw [hRes] at hRes0
  have hEq := Option.some.inj hRes0
  simp only [Prod.mk.injEq] at hEq
  obtain ⟨hE1, hE2⟩ := hEq
  subst hE2
  subst hE1
  have hH' : st.asidTable.holds root.asid rootId = true := by rw [hRA]; exact hH
  obtain ⟨hO, hA, hM⟩ := vspaceUnmapPerformAt_fields (ec := ec) (vaddr := args.vaddr)
    (asid := args.asid) hR hH'
  have hR0 : (vspaceUnmapPerformAt ec args.asid args.vaddr rootId st).objects[rootId]? =
      some (.vspaceRoot (rootWithoutMapping args.vaddr root)) := by
    rw [hO, RHTable_getElem?_eq_get?]
    exact RHTable.get?_insert_self_of_findsInPlace _ hInR
  have hGR0 : (vspaceUnmapPerformAt ec args.asid args.vaddr rootId st).getVSpaceRoot? rootId =
      some (rootWithoutMapping args.vaddr root) :=
    (SystemState.getVSpaceRoot?_eq_some_iff _ rootId _).2 hR0
  have hH0 : (vspaceUnmapPerformAt ec args.asid args.vaddr rootId st).asidTable.holds
      args.asid rootId = true := by rw [hA]; exact hH
  have hRes0 := resolveAsidRoot_of_holds hH0 hR0 hRA
  have hErase : (rootWithoutMapping args.vaddr root).mappings[args.vaddr]? = none := by
    rw [RHTable_getElem?_eq_get?]
    exact RHTable.get?_erase_self_of_keyOnlyAt _ _ hK
  have hNotLive : capabilityMappingLive (vspaceUnmapPerformAt ec args.asid args.vaddr rootId st)
      frameCap = false :=
    capabilityMappingLive_of_lookup_none (by rw [hAs]; exact hRes0)
      (by rw [hVa]; exact hErase)
  have hTr0 : (rootWithoutMapping args.vaddr root).translationReady args.vaddr = true := hTr
  have hA0 : (rootWithoutMapping args.vaddr root).asid = args.asid := hRA
  unfold Architecture.pageMappingAligned at hAl
  simp only [Bool.and_eq_true] at hAl
  unfold vspaceMapAdmittedAt
  rw [hAd, hNotLive, hM, hV, hGR0, hA, hO, RHTable.findsInPlace_insert_of_findsInPlace _ _ hInR,
    RHTable.findsInPlace_insert_of_findsInPlace _ _ hInR]
  simp [Architecture.asidTranslationReady, hRes0, hErase, hTr0, hWin, hCan, hPa, hWx,
    Architecture.pageMappingAligned, hAl.1, hAl.2, hA0, hH, hInR, hFF]

open SeLe4n.Kernel.RobinHood in
/-- **An admitted remap is its writes**: the unmap in place, then the map in
place on the state it leaves — no refusal after the first write. -/
theorem vspaceMapOrRemapFromFrameCap_of_remapAdmitted (tid : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st : SystemState) (frameSlot : CSpaceAddr) (frameCap : Capability) (frame : FrameObject)
    (rootId : SeLe4n.ObjId)
    (hRes : resolveVSpaceMapFrame tid args st = .ok (frameSlot, frameCap, frame))
    (hLive : capabilityMappingLive st frameCap = true)
    (hRf : vspaceRemapRefusal st args frameCap frame = .ok ())
    (hIn : vspaceRemapInPlaceAt st args frameCap rootId = true) :
    vspaceMapOrRemapFromFrameCap tid ec args st =
      .ok ((), vspaceMapPerformAt ec args.asid args.vaddr frame.base args.perms rootId
        (frameCapObjId frameCap) frameSlot.cnode frameSlot.slot
        (vspaceUnmapPerformAt ec args.asid args.vaddr rootId st)) := by
  have hMA := vspaceMapAdmittedAt_of_remapInPlace ec args st frameCap frame rootId hRf hIn
  have hIn' := hIn
  unfold vspaceRemapInPlaceAt at hIn'
  simp only [Bool.and_eq_true] at hIn'
  obtain ⟨⟨hU, -⟩, -⟩ := hIn'
  have hU' := hU
  unfold vspaceUnmapAdmittedAt at hU'
  cases hGR : st.getVSpaceRoot? rootId with
  | none => simp [hGR] at hU'
  | some root =>
  have hR : st.objects[rootId]? = some (.vspaceRoot root) :=
    (SystemState.getVSpaceRoot?_eq_some_iff st rootId root).1 hGR
  simp only [hGR, Bool.and_eq_true, beq_iff_eq] at hU'
  obtain ⟨⟨⟨hRA, -⟩, hH⟩, hInR⟩ := hU'
  have hH' : st.asidTable.holds root.asid rootId = true := by rw [hRA]; exact hH
  obtain ⟨hO, -, -⟩ := vspaceUnmapPerformAt_fields (ec := ec) (vaddr := args.vaddr)
    (asid := args.asid) hR hH'
  let st0 := vspaceUnmapPerformAt ec args.asid args.vaddr rootId st
  have hGet : ∀ id, st0.objects[id]? = st.objects[id]? ∨
      (id = rootId ∧ st0.objects[id]? = some (.vspaceRoot (rootWithoutMapping args.vaddr root))) := by
    intro id
    show (vspaceUnmapPerformAt ec args.asid args.vaddr rootId st).objects[id]? = _ ∨ _
    rw [hO, RHTable_getElem?_eq_get?, RHTable_getElem?_eq_get?]
    by_cases hEq : rootId = id
    · subst hEq
      exact .inr ⟨rfl, RHTable.get?_insert_self_of_findsInPlace _ hInR⟩
    · exact .inl (RHTable.get?_insert_ne_of_findsInPlace _ _ hInR hEq)
  have hT : ∀ id, st0.getTcb? id = st.getTcb? id := by
    intro id; unfold SystemState.getTcb?
    rcases hGet id.toObjId with h | ⟨h0, h⟩
    · rw [h]
    · rw [h, h0, hR]
  have hCn : ∀ id, st0.getCNode? id = st.getCNode? id := by
    intro id; unfold SystemState.getCNode?
    rcases hGet id with h | ⟨rfl, h⟩
    · rw [h]
    · rw [h, hR]
  have hF : ∀ id, st0.getFrame? id = st.getFrame? id := by
    intro id; unfold SystemState.getFrame?
    rcases hGet id with h | ⟨rfl, h⟩
    · rw [h]
    · rw [h, hR]
  have hRes0 : resolveVSpaceMapFrame tid args st0 = .ok (frameSlot, frameCap, frame) := by
    rw [resolveVSpaceMapFrame_congr tid args hT hCn hF]; exact hRes
  unfold vspaceMapOrRemapFromFrameCap
  rw [hRes]
  simp only [hLive, ↓reduceIte, hRf]
  rw [vspaceUnmapPageWithShootdownAndIcacheBroadcast_of_admitted ec args.asid args.vaddr rootId st hU]
  exact vspaceMapFromFrameCap_of_admitted tid ec args _ frameSlot frameCap frame rootId hRes0 hMA

/-- **An admitted fresh map through the remap's entry is its writes**: its
checks read the capability's record as not in place, so the call is the fresh
mapping (`vspaceMapFromFrameCap_of_admitted`). -/
theorem vspaceMapOrRemapFromFrameCap_of_admitted (tid : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st : SystemState) (frameSlot : CSpaceAddr) (frameCap : Capability) (frame : FrameObject)
    (rootId : SeLe4n.ObjId)
    (hRes : resolveVSpaceMapFrame tid args st = .ok (frameSlot, frameCap, frame))
    (hA : vspaceMapAdmittedAt st args frameCap frame rootId = true) :
    vspaceMapOrRemapFromFrameCap tid ec args st =
      .ok ((), vspaceMapPerformAt ec args.asid args.vaddr frame.base args.perms rootId
        (frameCapObjId frameCap) frameSlot.cnode frameSlot.slot st) := by
  have hLive : capabilityMappingLive st frameCap = false := by
    have h := hA
    unfold vspaceMapAdmittedAt at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1.1.1.1.1.1.1.1.1.2
  unfold vspaceMapOrRemapFromFrameCap
  rw [hRes]
  simp only [hLive, Bool.false_eq_true, ↓reduceIte]
  exact vspaceMapFromFrameCap_of_admitted tid ec args st frameSlot frameCap frame rootId hRes hA

end SeLe4n.Kernel
