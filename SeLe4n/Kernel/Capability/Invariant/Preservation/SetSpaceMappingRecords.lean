-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.ThreadSpaceCopy
import SeLe4n.Kernel.Capability.Invariant.Preservation.MappingRecords

/-! # The thread-space set keeps every live mapping recorded

seL4's `TCB_SetSpace` deletes a thread's old CSpace and VSpace root capabilities
and inserts derived copies of the new ones.  Here each slot set
(`threadSlotCopied`) clears the slot and writes the copy without unmapping what
the old capability records.  That loses no record of a live mapping because no
thread's space slot holds one (`SystemState.threadSlotsRecordNoMapping`, the
second half of `SystemState.liveMappingsRecorded`): the copy carries none
(`TCB.spaceCopyOf`, as seL4's `deriveCap` clears a frame capability's mapped
address), so the slot keeps holding none.

The retire that follows each slot set (`threadSlotSet`) erases the object the
old capability was the last capability to, which no slot names after the copy
(`threadSlotCopied_retireTargetUnnamed`); a frame witnessing a live mapping is
named by its witness, so it is not that object
(`retireFinalObject_preserves_liveMappingsRecorded`).  The zombie loop's passes
before the set are finalising deletes and finalisations, which keep the records
on a state whose capability invariants and teardown well-formedness hold
(`mappingRecordsCarried`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The capability a space slot is set from records no mapping. -/
@[simp] theorem TCB.spaceCopyOf_mapping (cap : Capability) (rights : AccessRightSet) :
    (TCB.spaceCopyOf cap rights).mapping = none := rfl

/-- **The retire keeps the mappings recorded when no slot names its target**:
it keeps every slot's capability and every root it does not erase, and it
erases only its target among the frames, which a frame witnessing a live
mapping is not, its witness naming it. -/
theorem retireFinalObject_preserves_liveMappingsRecorded (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (hInv : st.objects.invExt)
    (hNamed : target ≠ 0 →
      ∀ r, ¬ SystemState.namesAt st.slotCapAt r (SeLe4n.ObjId.ofNat (target - 1)))
    (hL : st.liveMappingsRecorded) :
    (retireFinalObject ec target recorder st).liveMappingsRecorded := by
  refine ⟨fun rid r' v p perms e hR hM hE => ?_,
    hL.2.of_drawnFrom (retireFinalObject_threadSlotsDrawnFrom ec target recorder st hInv)⟩
  have hR0 : st.objects[rid]? = some (.vspaceRoot r') := by
    rcases retireFinalObject_key ec target recorder st hInv rid with e | ⟨-, -, hn | ⟨U, hU⟩⟩
    · rw [← e]; exact hR
    · rw [hR] at hn; cases hn
    · rw [hR] at hU; cases hU
  obtain ⟨s, cap, fid, f, hc, ht, hf, hb, hmap⟩ := hL.1 rid r' v p perms e hR0 hM hE
  refine ⟨s, cap, fid, f, ?_, ht, ?_, hb, hmap⟩
  · rw [retireFinalObject_slotCapAt ec target recorder st hInv]; exact hc
  · rcases retireFinalObject_keeps_frame ec target recorder st hInv hf with hk | ⟨hT, hx⟩
    · exact hk
    · exact absurd ⟨cap, hc, by rw [← hx]; simp [Capability.namedObject, ht]⟩ (hNamed hT s)

/-- **A slot copy draws every thread slot from the pre-state**: every other
object agrees off its derivation links, and the thread's slot holds the copy,
which records nothing, or nothing. -/
theorem threadSlotCopied_threadSlotsDrawnFrom {st : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    SystemState.threadSlotsDrawnFrom st (threadSlotCopied st tid slot srcCNode srcSlot rights) := by
  obtain ⟨hFar, t', hT', hW⟩ := threadSlotCopied_frame hObjInv hT slot srcCNode srcSlot rights
  have hPre := (SystemState.getTcb?_eq_some_iff st tid t).mp hT
  intro k t2 s c hT2 hc
  by_cases hk : k = tid.toObjId
  · subst hk
    rw [(SystemState.getTcb?_eq_some_iff _ tid t').mp hT'] at hT2
    cases hT2
    rw [← TCB.spaceSlotCap_withoutLinks, hW, TCB.spaceSlotCap_withoutLinks] at hc
    split at hc
    · exact .inr ⟨t, hPre, TCB.spaceSlotCap_removeSpaceCap_back hc⟩
    · rcases TCB.spaceSlotCap_insertSpaceCap_back hc with rfl | hc'
      · exact .inl (TCB.spaceCopyOf_mapping _ _)
      · exact .inr ⟨t, hPre, TCB.spaceSlotCap_removeSpaceCap_back hc'⟩
  · rcases hFar k hk with e | ⟨cn, cn', h1, h2, hw⟩ | ⟨t0, t0', h1, h2, hw⟩
    · exact .inr ⟨t2, e ▸ hT2, hc⟩
    · rw [hT2] at h2; cases h2
    · rw [hT2] at h2; cases h2
      exact .inr ⟨t0, h1, by
        rw [← TCB.spaceSlotCap_withoutLinks, ← hw, TCB.spaceSlotCap_withoutLinks]; exact hc⟩

/-- **A slot copy keeps the mappings recorded.**  It writes the thread's slot
and derivation links alone: every root and every frame keeps its key, and every
other slot its capability.  The capability the slot held before records no
mapping (`threadSlotsRecordNoMapping`), so the record it loses witnessed
nothing, and the copy it writes records none. -/
theorem threadSlotCopied_preserves_liveMappingsRecorded {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t)
    {slot : SeLe4n.Slot} (hs : slot.toNat < 2) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) (hL : st.liveMappingsRecorded) :
    (threadSlotCopied st tid slot srcCNode srcSlot rights).liveMappingsRecorded := by
  obtain ⟨hFar, -⟩ := threadSlotCopied_frame hObjInv hT slot srcCNode srcSlot rights
  have hPre := (SystemState.getTcb?_eq_some_iff st tid t).mp hT
  -- A key holding a root or a frame after the copy is no thread's: it agrees.
  have hNotTcb : ∀ (k : SeLe4n.ObjId) (o : KernelObject),
      (threadSlotCopied st tid slot srcCNode srcSlot rights).objects[k]? = some o →
      (∀ cn, o ≠ .cnode cn) → (∀ t0, o ≠ .tcb t0) → st.objects[k]? = some o := by
    intro k o hk hCn hTcb
    have hne : k ≠ tid.toObjId := by
      intro e; subst e
      obtain ⟨-, t', hT', -⟩ := threadSlotCopied_frame hObjInv hT slot srcCNode srcSlot rights
      rw [(SystemState.getTcb?_eq_some_iff _ tid t').mp hT'] at hk
      cases hk; exact hTcb t' rfl
    rcases hFar k hne with e | ⟨cn, cn', h1, h2, hw⟩ | ⟨t0, t0', h1, h2, hw⟩
    · rw [← e]; exact hk
    · rw [hk] at h2; cases h2; exact absurd rfl (hCn cn')
    · rw [hk] at h2; cases h2; exact absurd rfl (hTcb t0')
  refine SystemState.liveMappingsRecorded.of_shrink (fun rid r' hR => ?_)
    (SystemState.mappingRecordsKept.of_fwd (fun r cap hc hm => ?_) (fun fid f hf => ?_))
    (threadSlotCopied_threadSlotsDrawnFrom hObjInv hT slot srcCNode srcSlot rights) hL
  · exact ⟨r', hNotTcb rid _ hR (fun _ h => by cases h) (fun _ h => by cases h), rfl,
      fun _ _ h => h, fun _ _ h => h⟩
  · refine ⟨r, cap, ?_, rfl, rfl⟩
    rw [threadSlotCopied_slotCapAt hObjInv hT hs, if_neg]
    · exact hc
    · rintro ⟨hk, hsl⟩
      have hNone := hL.2 r.cnode t r.slot cap (hk ▸ hPre) (by
        rw [SystemState.slotCapAt_eq_bind, hk, hPre] at hc; exact hc)
      unfold Capability.mapping at hNone
      rw [if_pos hm] at hNone; cases hNone
  · have hne : fid ≠ tid.toObjId := by intro e; rw [e, hPre] at hf; cases hf
    rcases hFar fid hne with e | ⟨cn, cn', h1, h2, hw⟩ | ⟨t0, t0', h1, h2, hw⟩
    · exact ⟨f, e.trans hf, rfl⟩
    · rw [hf] at h1; cases h1
    · rw [hf] at h1; cases h1

/-- **A thread space slot's set keeps the mappings recorded**: the copy keeps
them (`threadSlotCopied_preserves_liveMappingsRecorded`), and the retire of what
the old capability was the last capability to keeps them, no slot naming that
object after the copy (`threadSlotCopied_retireTargetUnnamed`). -/
theorem threadSlotSet_preserves_liveMappingsRecorded (ec : Concurrency.CoreId)
    {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB} {slot : SeLe4n.Slot}
    (hInv : capabilityInvariantBundle st) (hT : st.getTcb? tid = some t)
    (hs : slot.toNat < 2) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) (hL : st.liveMappingsRecorded) :
    (threadSlotSet ec st tid slot srcCNode srcSlot rights).liveMappingsRecorded := by
  have hObjInv := objects_invExt_of_capabilityInvariantBundle st hInv
  unfold threadSlotSet
  dsimp only
  exact retireFinalObject_preserves_liveMappingsRecorded ec _ _ _
    (threadSlotCopied_tcb hObjInv hT slot srcCNode srcSlot rights).2
    (threadSlotCopied_retireTargetUnnamed hInv hT hs srcCNode srcSlot rights)
    (threadSlotCopied_preserves_liveMappingsRecorded hObjInv hT hs srcCNode srcSlot rights hL)

/-- **Setting a thread's space keeps the mappings recorded**: each of its two
slot sets does (`threadSlotSet_preserves_liveMappingsRecorded`), the second from
the capability bundle the first keeps
(`threadSlotSet_preserves_capabilityInvariantBundle`). -/
theorem copyThreadSpaces_preserves_liveMappingsRecorded (ec : Concurrency.CoreId)
    {st st' : SystemState} {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr}
    (hInv : capabilityInvariantBundle st) (hL : st.liveMappingsRecorded)
    (hStep : copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st') :
    st'.liveMappingsRecorded := by
  obtain ⟨tcb, hT, -, -, hCn, -, rfl⟩ := copyThreadSpaces_ok hStep
  have hObjInv := objects_invExt_of_capabilityInvariantBundle st hInv
  have hL1 := threadSlotSet_preserves_liveMappingsRecorded ec hInv hT (by decide) cnSrc.cnode
    cnSrc.slot TCB.cspaceRootRights (slot := TCB.cspaceRootSlot) hL
  obtain ⟨t1, hT1⟩ := cspaceRootSet_getTcb? ec hObjInv hT hCn
  exact threadSlotSet_preserves_liveMappingsRecorded ec
    (cspaceRootSet_preserves_capabilityInvariantBundle ec hInv hT hCn) hT1 (by decide)
    vrSrc.cnode vrSrc.slot TCB.vspaceRootRights hL1

/-- **Setting a thread's space through the zombie delete keeps the mappings
recorded**: the loop's passes are finalising deletes and finalisations, which
keep them with the capability bundle and the teardown's well-formedness
(`mappingRecordsCarried`), and the plain space change after them keeps them
(`copyThreadSpaces_preserves_liveMappingsRecorded`).  seL4's `TCB_SetSpace`
deletes the old roots by `cteDelete`, the zombie loop, before it inserts the new
ones. -/
theorem copyThreadSpacesZombie_preserves_liveMappingsRecorded (ec : Concurrency.CoreId)
    {st st' : SystemState} {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr}
    (hInv : capabilityInvariantBundle st) (hW : teardownWellFormed st)
    (hL : st.liveMappingsRecorded)
    (hStep : copyThreadSpacesZombie ec st vtid cnSrc vrSrc = .ok st') :
    st'.liveMappingsRecorded := by
  rcases copyThreadSpacesZombie_cases hStep with h1 | ⟨n, s, hR, rfl | h2⟩
  · exact copyThreadSpaces_preserves_liveMappingsRecorded ec hInv hL h1
  · exact (hR.chain.closed mappingRecordsCarried
      (cspaceDeleteSlotFinalising_preserves_mappingRecordsCarried ec)
      finaliseFinalObject_preserves_mappingRecordsCarried ⟨hInv, hW, hL⟩).2.2
  · have hC := hR.chain.closed mappingRecordsCarried
      (cspaceDeleteSlotFinalising_preserves_mappingRecordsCarried ec)
      finaliseFinalObject_preserves_mappingRecordsCarried ⟨hInv, hW, hL⟩
    exact copyThreadSpaces_preserves_liveMappingsRecorded ec hC.1 hC.2.2 h2

end SeLe4n.Kernel
