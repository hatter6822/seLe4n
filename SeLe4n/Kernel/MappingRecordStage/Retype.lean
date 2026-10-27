-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.Basic

/-! # The carve keeps the mappings recorded

A carve (`untypedRetypeObject`) writes its untyped's watermark, stores its child
at an id no object held, sets the authority capability's free index, scrubs the
child's memory, inserts the child's capability into an empty slot and records the
derivation edge.  Only the child's store adds an object, and the child holds no
live mapping: a carved address space has a fresh ASID and no mapping epoch
(`untypedNextVSpaceRoot`), so it adds no mapping to record, a carved thread's
space slots are empty (`carvedTcb`), so it adds no thread slot's record, and
every frame and every capability already recording a mapping keeps its key
(`liveMappingsRecorded.of_freshObject`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (MappingStage)

/-- **A carved object holds no mapping epoch**: only a carved address space is
a root, and it is carved with an empty epoch table. -/
theorem CarveRequest.object_noMappingEpoch (untypedId childId : SeLe4n.ObjId)
    (ut : UntypedObject) (idx : Nat) (req : CarveRequest) :
    ∀ root, req.object untypedId childId ut idx = .vspaceRoot root →
      ∀ (v : SeLe4n.VAddr) (e : Nat), root.mappingEpochs[v]? = some e → False := by
  intro root hR v e hE
  cases req <;> simp only [CarveRequest.object] at hR <;> try cases hR
  rw [show (untypedNextVSpaceRoot ut idx _).mappingEpochs[v]? = none from
    SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty 16 (by omega) v] at hE
  cases hE

/-- **A carved thread's space slots are empty** (`carvedTcb`: seL4's
`createObject` makes a thread whose `tcbCTable` and `tcbVTable` hold null
capabilities), so they record no mapping. -/
theorem CarveRequest.object_threadSlotsEmpty (untypedId childId : SeLe4n.ObjId)
    (ut : UntypedObject) (idx : Nat) (req : CarveRequest) :
    ∀ t, req.object untypedId childId ut idx = .tcb t →
      ∀ (s : SeLe4n.Slot) (cap : Capability), t.spaceSlotCap s = some cap → cap.mapping = none := by
  intro t hT s cap hc
  cases req <;> simp only [CarveRequest.object] at hT <;> try cases hT
  unfold TCB.spaceSlotCap at hc
  split at hc
  · next hs =>
    have : s.toNat = 0 ∨ s.toNat = 1 := by omega
    rcases this with h | h <;> simp [carvedTcb, h] at hc
  · cases hc

/-- **The carve keeps the mappings recorded.** -/
theorem untypedRetypeObject_mappingStage {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st st' : SystemState}
    (h : untypedRetypeObject src childId dst req st = .ok ((), st')) : MappingStage st st' := by
  refine MappingStage.of_invExt fun hInv => ?_
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hInv h
  have hFresh := retypeFromUntyped_childId_fresh src untypedId childId _ _ st st1 hRt
  obtain ⟨ut₀, ut', cap, stUt, _, stCh, cn, hUt, _, _, _, _, _, _, hLk, _, _, hStUt, hStCh, hOCh,
    hStIdx⟩ := retypeFromUntyped_ok_stores st st1 src untypedId childId _ _ hInv hRt
  have hNe : childId ≠ untypedId := by
    intro h; rw [h, hUt] at hFresh; simp at hFresh
  have hChildNone : stUt.objects[childId]? = none := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hInv hStUt]
    cases h : st.objects[childId]? with
    | none => rfl
    | some _ => rw [h] at hFresh; simp at hFresh
  have hInvUt := storeObject_preserves_objects_invExt _ _ _ _ hInv hStUt
  have hInvCh := storeObject_preserves_objects_invExt _ _ _ _ hInvUt hStCh
  have k1 : MappingStage st stUt :=
    MappingStage.storeObject hStUt hUt rfl (by simp [KernelObject.objectType])
  have k2 : MappingStage stUt stCh :=
    MappingStage.of_preserves (fun _ => hInvCh) fun _ hL =>
      hL.of_freshObject hChildNone (storeObject_objects_eq _ _ _ _ hInvUt hStCh)
        (fun j hj => storeObject_objects_ne _ _ _ _ _ hj hInvUt hStCh)
        (CarveRequest.object_noMappingEpoch _ _ _ _ req)
        (CarveRequest.object_threadSlotsEmpty _ _ _ _ req)
  rw [← CNode.setFreeIndex_of_lookup hLk, setCapFreeIndex_eq_storeObject hOCh] at hStIdx
  cases hStIdx
  refine (((((k1.trans k2).trans ?_).trans
    (MappingStage.of_objects_eq (CarveRequest.scrub_objects _ _ _ _))).trans
    (MappingStage.of_preserves (fun hI => cspaceInsertSlot_objects_invExt hI hIns)
      fun hI hL => cspaceInsertSlot_preserves_liveMappingsRecorded hI hIns hL)).trans
    (MappingStage.of_preserves (fun hI => (SystemState.cdtAddChild_reach st2 _ _ _).invExt hI)
      fun hI hL => cdtAddChild_preserves_liveMappingsRecorded hI hL))
  exact MappingStage.of_preserves
    (fun _ => storeObject_preserves_objects_invExt _ _ _ _ hInvCh
      (setCapFreeIndex_eq_storeObject hOCh))
    fun _ hL => setCapFreeIndex_preserves_liveMappingsRecorded hInvCh hL

/-- The live `.untypedRetype` arm: the carve. -/
theorem untypedRetypeFromCap_mappingStage {tid : SeLe4n.ThreadId}
    {ec : Concurrency.CoreId} {srcAddr : SeLe4n.CPtr}
    {args? : Except KernelError SeLe4n.Kernel.Architecture.SyscallArgDecode.UntypedRetypeArgs}
    {st st' : SystemState} (h : untypedRetypeFromCap tid ec srcAddr args? st = .ok ((), st')) :
    MappingStage st st' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hCarve⟩ :=
    untypedRetypeFromCap_ok tid ec srcAddr args? st st' h
  exact untypedRetypeObject_mappingStage hCarve

end SeLe4n.Kernel
