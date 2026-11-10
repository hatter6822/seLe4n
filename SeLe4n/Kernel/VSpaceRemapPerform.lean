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
This module is the remap's compiled form: its checks read before any write
(`vspaceRemapAdmittedAt`), then the unmap in place (`vspaceUnmapPerformAt`) and
the map half on the state it leaves (`vspaceRemapMapAt`), proven equal to the
specification (`vspaceMapOrRemapFromFrameCap_of_remapAdmitted`).
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

/-- **The remap's checks**, read before any write: the frame capability's
recorded mapping is in place and names the address space and the address the
call names (`vspaceMapOrRemapFromFrameCap`'s remap), the unmap of that address
is admitted in place (`vspaceUnmapAdmittedAt`), and the map's checks that read
nothing the unmap writes hold (`vspaceRemapChecks`). -/
def vspaceRemapAdmittedAt (st : SystemState) (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (frameCap : Capability) (frame : FrameObject) (rootId : SeLe4n.ObjId) : Bool :=
  capabilityMappingLive st frameCap && frameCap.mapAsid == args.asid &&
    frameCap.mapVaddr == args.vaddr &&
    vspaceUnmapAdmittedAt st args.asid args.vaddr rootId &&
    vspaceRemapChecks st args frameCap frame

/-- **The remap's map half, on the state the unmap left**: the frame mapped in
place (`vspaceMapPerformAt`) when its checks hold there; otherwise the fresh
mapping as specified, or — where it refuses — the state the unmap left. -/
def vspaceRemapMapAt (tid : SeLe4n.ThreadId) (ec : Concurrency.CoreId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs) (frameCap : Capability)
    (frame : FrameObject) (rootId frameCnode : SeLe4n.ObjId) (frameSlot : SeLe4n.Slot)
    (st0 : SystemState) : SystemState :=
  if vspaceMapAdmittedAt st0 args frameCap frame rootId then
    vspaceMapPerformAt ec args.asid args.vaddr frame.base args.perms rootId
      (frameCapObjId frameCap) frameCnode frameSlot st0
  else
    match vspaceMapFromFrameCap tid ec args st0 with
    | .ok ((), s) => s
    | .error _ => st0

open SeLe4n.Kernel.RobinHood in
/-- **An admitted remap is its writes**: the unmap in place, then the map half
on the state it leaves. -/
theorem vspaceMapOrRemapFromFrameCap_of_remapAdmitted (tid : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st : SystemState) (frameSlot : CSpaceAddr) (frameCap : Capability) (frame : FrameObject)
    (rootId : SeLe4n.ObjId)
    (hRes : resolveVSpaceMapFrame tid args st = .ok (frameSlot, frameCap, frame))
    (hA : vspaceRemapAdmittedAt st args frameCap frame rootId = true) :
    vspaceMapOrRemapFromFrameCap tid ec args st =
      .ok ((), vspaceRemapMapAt tid ec args frameCap frame rootId frameSlot.cnode frameSlot.slot
        (vspaceUnmapPerformAt ec args.asid args.vaddr rootId st)) := by
  unfold vspaceRemapAdmittedAt at hA
  simp only [Bool.and_eq_true, beq_iff_eq] at hA
  obtain ⟨⟨⟨⟨hLive, hAs⟩, hVa⟩, hU⟩, hC⟩ := hA
  have hU' := hU
  unfold vspaceUnmapAdmittedAt at hU'
  cases hGR : st.getVSpaceRoot? rootId with
  | none => simp [hGR] at hU'
  | some root =>
  have hR : st.objects[rootId]? = some (.vspaceRoot root) :=
    (SystemState.getVSpaceRoot?_eq_some_iff st rootId root).1 hGR
  simp only [hGR, Bool.and_eq_true, beq_iff_eq] at hU'
  obtain ⟨⟨⟨hRA, -⟩, hH⟩, hIn⟩ := hU'
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
      exact .inr ⟨rfl, RHTable.get?_insert_self_of_findsInPlace _ hIn⟩
    · exact .inl (RHTable.get?_insert_ne_of_findsInPlace _ _ hIn hEq)
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
  simp only [hLive, hAs, hVa, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [vspaceUnmapPageWithShootdownAndIcacheBroadcast_of_admitted ec args.asid args.vaddr rootId st hU]
  simp only
  unfold vspaceRemapMapAt
  by_cases hM : vspaceMapAdmittedAt st0 args frameCap frame rootId = true
  · rw [vspaceMapFromFrameCap_of_admitted tid ec args _ frameSlot frameCap frame rootId hRes0 hM]
    exact congrArg (fun x => Except.ok ((), x)) (if_pos hM).symm
  · have hM' : vspaceMapAdmittedAt st0 args frameCap frame rootId = false := by
      simpa using hM
    show _ = Except.ok ((), if vspaceMapAdmittedAt st0 args frameCap frame rootId = true then _ else _)
    rw [hM']
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hFr : vspaceMapFromFrameCap tid ec args st0 with
    | ok r => obtain ⟨⟨⟩, s⟩ := r; rfl
    | error e => simp only [hC, ↓reduceIte]
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
