-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.Basic

/-! # The IPC arms keep the mappings recorded

Every IPC step but the capability transfer is a kind-preserving write: the
queue links, IPC states, staged messages, reply links and donation words live in
endpoints, notifications, replies, scheduling contexts and TCBs, none of which
holds a mapping fact or a slot the IPC writes.  Each per-core leg agrees off the
run-queue links with its single-core leg (`OffSchedulerAgrees`), which is a
kind-preserving write, so the leg's stage is read off the two.

The capability transfer inserts each transferred capability into an empty slot
of the receiver's CNode, with a derivation edge and the source's untyped set
full; each of the three keeps the mappings recorded
(`cspaceInsertSlot_preserves_liveMappingsRecorded`,
`cdtAddChild_preserves_liveMappingsRecorded`,
`untypedSourceSetFull_preserves_liveMappingsRecorded`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (MappingStage)
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-- A per-core leg that agrees off the run-queue links with a kind-preserving
single-core leg keeps the mappings recorded. -/
theorem MappingStage.of_postAgrees {st r1 st' : SystemState}
    (hI : st.objects.invExt → st'.objects.invExt)
    (hK : st.objects.invExt → kindPreservingWrite st r1) (hA : OffSchedulerAgrees r1 st') :
    MappingStage st st' :=
  MappingStage.of_kindPreservingWrite hI fun h => (hK h).trans hA.objects.kindPreserving

/-! ### The capability transfer -/

theorem ipcTransferSingleCap_mappingStage {cap : Capability} {srcNode : SlotRef}
    {receiverRoot : SeLe4n.ObjId} {slotBase : SeLe4n.Slot} {scanLimit : Nat}
    {st st' : SystemState} {result : CapTransferResult}
    (h : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st = .ok (result, st')) :
    MappingStage st st' := fun hInv => by
  refine ⟨ipcTransferSingleCap_preserves_objects_invExt _ _ _ _ _ _ _ _ hInv h, fun hL => ?_⟩
  obtain ⟨_, -, ⟨rfl, -⟩ | ⟨_, st2, -, -, -, hIns, -, rfl⟩⟩ := ipcTransferSingleCap_ok_cases h
  · exact hL
  · have hI2 := cspaceInsertSlot_objects_invExt hInv hIns
    exact untypedSourceSetFull_preserves_liveMappingsRecorded
      ((SystemState.cdtAddChild_reach st2 _ _ _).invExt hI2)
      (cdtAddChild_preserves_liveMappingsRecorded hI2
        (cspaceInsertSlot_preserves_liveMappingsRecorded hInv hIns hL))

theorem ipcUnwrapCapsLoop_mappingStage {caps : Array TransferCap} {receiverRoot : SeLe4n.ObjId}
    {idx : Nat} {nextBase : SeLe4n.Slot} {accResults : Array CapTransferResult} {fuel : Nat}
    {st st' : SystemState} {summary : CapTransferSummary}
    (h : ipcUnwrapCapsLoop caps receiverRoot idx nextBase accResults fuel st = .ok (summary, st')) :
    MappingStage st st' := by
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    simp [ipcUnwrapCapsLoop] at h
    obtain ⟨_, rfl⟩ := h; exact MappingStage.refl _
  | succ n ih =>
    simp only [ipcUnwrapCapsLoop] at h
    cases hCap : caps[idx]? with
    | none => simp [hCap] at h; obtain ⟨_, rfl⟩ := h; exact MappingStage.refl _
    | some tc =>
      simp [hCap] at h
      cases hT : ipcTransferSingleCap tc.cap tc.srcSlot receiverRoot nextBase maxExtraCaps st with
      | error e => simp [hT] at h; obtain ⟨_, rfl⟩ := h; exact MappingStage.refl _
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have h1 := ipcTransferSingleCap_mappingStage hT
        simp [hT] at h
        cases result <;> exact h1.trans (ih h)

theorem ipcUnwrapCaps_mappingStage {caps : Array TransferCap} {receiverRoot : SeLe4n.ObjId}
    {slotBase : SeLe4n.Slot} {grantRight : Bool} {st st' : SystemState}
    {summary : CapTransferSummary}
    (h : ipcUnwrapCaps caps receiverRoot slotBase grantRight st = .ok (summary, st')) :
    MappingStage st st' := by
  unfold ipcUnwrapCaps at h
  split at h
  · simp at h; obtain ⟨_, rfl⟩ := h; exact MappingStage.refl _
  · exact ipcUnwrapCapsLoop_mappingStage h

theorem receiveTransferCaps_mappingStage
    {req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)} {root : SeLe4n.ObjId}
    {base : SeLe4n.Slot} {st st' : SystemState} {summary : CapTransferSummary}
    (h : receiveTransferCaps req root base st = .ok (summary, st')) : MappingStage st st' := by
  obtain ⟨stR, _, hO, -, _, hOr⟩ := receiveTransferCaps_frame h
  have h1 : MappingStage st stR := MappingStage.of_objects_eq hO
  rcases hOr with rfl | hU
  · exact h1
  · exact h1.trans (ipcUnwrapCaps_mappingStage hU)

/-! ### Send -/

theorem endpointSendDualOnCore_mappingStage {endpointId : SeLe4n.ObjId}
    {sender : SeLe4n.ThreadId} {payload : SendPayload} {executingCore : CoreId}
    {st : SystemState} :
    MappingStage st (endpointSendDualOnCore endpointId sender payload executingCore st).1 :=
  fun hInv => by
    rcases endpointSendDualOnCore_post_agrees endpointId sender payload executingCore st hInv
      with h | ⟨r1, hS, hA⟩
    · rw [h]; exact ⟨hInv, id⟩
    · exact MappingStage.of_postAgrees
        (fun h => endpointSendDualOnCore_preserves_objects_invExt _ _ _ _ _ h)
        (fun h => endpointSendDual_kindPreservingWrite _ _ _ _ _ h hS) hA hInv

/-- The send with capability transfer keeps the mappings recorded. -/
theorem endpointSendDualWithCapsOnCore_mappingStage {endpointId : SeLe4n.ObjId}
    {sender : SeLe4n.ThreadId} {payload : SendPayload}
    {receiverSlotBase : SeLe4n.Slot} {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointSendDualWithCapsOnCore endpointId sender payload
      receiverSlotBase executingCore st).1 := by
  unfold endpointSendDualWithCapsOnCore
  have hSend := endpointSendDualOnCore_mappingStage (endpointId := endpointId) (sender := sender)
    (payload := payload) (executingCore := executingCore) (st := st)
  generalize endpointSendDualOnCore endpointId sender payload executingCore st = r at hSend
  obtain ⟨st1, res⟩ := r
  dsimp only at hSend ⊢
  cases res with
  | error _ => exact hSend
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact hSend
      | (rename_i hU; exact hSend.trans (receiveTransferCaps_mappingStage hU))

theorem endpointSendCrossCoreDispatchChecked_mappingStage {ctx : LabelingContext}
    {endpointId : SeLe4n.ObjId} {sender : SeLe4n.ThreadId} {payload : SendPayload}
    {receiverSlotBase : SeLe4n.Slot} {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointSendCrossCoreDispatchChecked ctx endpointId sender payload
      receiverSlotBase executingCore st).1 := by
  unfold endpointSendCrossCoreDispatchChecked
  split
  · exact endpointSendDualWithCapsOnCore_mappingStage
  · exact MappingStage.refl _

/-! ### Receive -/

theorem endpointReceiveDualOnCore_mappingStage {endpointId : SeLe4n.ObjId}
    {receiver : SeLe4n.ThreadId} {replyId : Option SeLe4n.ReplyId} {executingCore : CoreId}
    {st : SystemState} :
    MappingStage st (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 :=
  fun hInv => by
    rcases endpointReceiveDualOnCore_post_agrees endpointId receiver replyId executingCore st hInv
      with h | ⟨sender, r1, hS, hA⟩
    · rw [h]; exact ⟨hInv, id⟩
    · exact MappingStage.of_postAgrees
        (fun h => endpointReceiveDualOnCore_preserves_objects_invExt _ _ _ _ _ h)
        (fun h => endpointReceiveDual_kindPreservingWrite _ _ _ _ _ _ h hS) hA hInv

theorem endpointReceiveDualWithCapsOnCore_mappingStage {endpointId : SeLe4n.ObjId}
    {receiver : SeLe4n.ThreadId} {replyId : Option SeLe4n.ReplyId}
    {receiverCspaceRoot : SeLe4n.ObjId} {receiverSlotBase : SeLe4n.Slot}
    {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointReceiveDualWithCapsOnCore endpointId receiver replyId
      receiverCspaceRoot receiverSlotBase executingCore st).1 := by
  unfold endpointReceiveDualWithCapsOnCore
  have hRcv := endpointReceiveDualOnCore_mappingStage (endpointId := endpointId)
    (receiver := receiver) (replyId := replyId) (executingCore := executingCore) (st := st)
  generalize endpointReceiveDualOnCore endpointId receiver replyId executingCore st = r at hRcv
  obtain ⟨st1, res⟩ := r
  dsimp only at hRcv ⊢
  cases res with
  | error _ => exact hRcv
  | ok p =>
    obtain ⟨senderId, sgi⟩ := p
    dsimp only
    repeat' split
    all_goals first
      | exact hRcv
      | (rename_i hU; exact hRcv.trans (receiveTransferCaps_mappingStage hU))

/-! ### The donation lend and the chain walk -/

theorem propagatePipChainCrossCore_mappingStage {st : SystemState} {tid : SeLe4n.ThreadId}
    {ec : CoreId} {fuel : Nat} :
    MappingStage st (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1 :=
  MappingStage.of_kindPreservingWrite
    (PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt st tid ec fuel)
    (propagatePipChainCrossCore_kindPreservingWrite st tid ec fuel)

theorem applyCallDonationOnCore_mappingStage {st st' : SystemState}
    {callerVtid receiverVtid : SeLe4n.ValidThreadId} {donorHome doneeHome : CoreId}
    (h : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st') :
    MappingStage st st' :=
  MappingStage.of_kindPreservingWrite
    (fun hI => applyCallDonationOnCore_preserves_objects_invExt _ _ _ _ _ _ hI h)
    (fun hI => applyCallDonationOnCore_kindPreservingWrite _ _ _ _ _ _ hI h)

theorem applyReceiveRendezvousHandoff_mappingStage {st st' : SystemState}
    {receiver dequeued : SeLe4n.ThreadId} {executingCore : CoreId}
    (h : applyReceiveRendezvousHandoff st receiver dequeued executingCore = .ok st') :
    MappingStage st st' := by
  obtain ⟨stDon, hDon, rfl⟩ := applyReceiveRendezvousHandoff_ok_decompose _ _ _ _ _ h
  have hD : MappingStage st stDon := by
    unfold applyReceiveRendezvousDonation at hDon
    split at hDon
    · unfold applyRendezvousCallDonation at hDon
      split at hDon
      · exact applyCallDonationOnCore_mappingStage hDon
      · cases hDon
    · cases hDon; exact MappingStage.refl _
  split
  · exact hD.trans propagatePipChainCrossCore_mappingStage
  · exact hD

/-! ### Call -/

theorem endpointCallOnCore_mappingStage {endpointId : SeLe4n.ObjId}
    {caller : SeLe4n.ThreadId} {payload : SendPayload} {executingCore : CoreId}
    {st : SystemState} :
    MappingStage st (endpointCallOnCore endpointId caller payload executingCore st).1 :=
  MappingStage.of_kindPreservingWrite
    (endpointCallOnCore_preserves_objects_invExt _ _ _ _ _)
    (endpointCallOnCore_kindPreservingWrite _ _ _ _ _)

theorem endpointCallWithCapsOnCore_mappingStage {endpointId : SeLe4n.ObjId}
    {caller : SeLe4n.ThreadId} {payload : SendPayload}
    {receiverSlotBase : SeLe4n.Slot} {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointCallWithCapsOnCore endpointId caller payload
      receiverSlotBase executingCore st).1 := by
  unfold endpointCallWithCapsOnCore
  have hC := endpointCallOnCore_mappingStage (endpointId := endpointId) (caller := caller)
    (payload := payload) (executingCore := executingCore) (st := st)
  generalize endpointCallOnCore endpointId caller payload executingCore st = r at hC
  obtain ⟨st1, res⟩ := r
  dsimp only at hC ⊢
  cases res with
  | error _ => exact hC
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact hC
      | (rename_i hU; exact hC.trans (receiveTransferCaps_mappingStage hU))

theorem endpointCallCrossCoreDispatch_mappingStage {endpointId : SeLe4n.ObjId}
    {caller : SeLe4n.ThreadId} {payload : SendPayload}
    {receiverSlotBase : SeLe4n.Slot} {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointCallCrossCoreDispatch endpointId caller payload
      receiverSlotBase executingCore st).1 := by
  unfold endpointCallCrossCoreDispatch
  have hC := endpointCallWithCapsOnCore_mappingStage (endpointId := endpointId)
    (caller := caller) (payload := payload) (receiverSlotBase := receiverSlotBase)
    (executingCore := executingCore) (st := st)
  generalize endpointCallWithCapsOnCore endpointId caller payload
    receiverSlotBase executingCore st = r at hC
  obtain ⟨st1, res⟩ := r
  dsimp only at hC ⊢
  cases res with
  | error _ => exact hC
  | ok p =>
    obtain ⟨summary, sgi⟩ := p
    dsimp only
    repeat' split
    all_goals first
      | exact hC
      | (rename_i hD
         exact (hC.trans (applyCallDonationOnCore_mappingStage hD)).trans
           propagatePipChainCrossCore_mappingStage)

theorem endpointCallCrossCoreDispatchChecked_mappingStage {ctx : LabelingContext}
    {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId} {payload : SendPayload}
    {receiverSlotBase : SeLe4n.Slot} {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointCallCrossCoreDispatchChecked ctx endpointId caller payload
      receiverSlotBase executingCore st).1 := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · exact endpointCallCrossCoreDispatch_mappingStage
  · exact MappingStage.refl _

/-! ### Return-frame staging and TCB writes -/

/-- A TCB rewrite that keeps the thread's slots and binding code. -/
theorem updateTcb_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hf : ∀ t, (f t).spaceCells = t.spaceCells ∧ (f t).spaceLinks = t.spaceLinks ∧
      (f t).boundNotificationCode = t.boundNotificationCode := by
      intro _; exact ⟨rfl, rfl, rfl⟩)
    (hW : ∀ t, (f t).taintWords = t.taintWords := by taint_words_kept) :
    MappingStage st (st.updateTcb tid f) :=
  MappingStage.of_kindPreservingWrite (SystemState.updateTcb_preserves_objects_invExt _ _ _)
    (fun h => SystemState.updateTcb_kindPreservingWrite st tid f h hf hW)

theorem writeReturnFrameToTcb_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Architecture.SyscallReturnFrame) :
    MappingStage st (Architecture.writeReturnFrameToTcb st tid frame) :=
  updateTcb_mappingStage st tid _

theorem stageDeliveredMessage_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) (n : Nat) :
    MappingStage st (Architecture.stageDeliveredMessage st tid n) :=
  MappingStage.of_kindPreservingWrite (stageDeliveredMessage_objects_invExt st tid n)
    (Architecture.stageDeliveredMessage_kindPreservingWrite st tid n)

theorem stageWokenDelivery_mappingStage (st : SystemState) (woken? : Option SeLe4n.ThreadId)
    (n : Nat) : MappingStage st (Architecture.stageWokenDelivery st woken? n) := by
  cases woken? with
  | none => exact MappingStage.refl _
  | some tid => exact stageDeliveredMessage_mappingStage st tid n

theorem stageWokenSendCompletion_mappingStage (st : SystemState) (woken? : Option SeLe4n.ThreadId) :
    MappingStage st (Architecture.stageWokenSendCompletion st woken?) := by
  unfold Architecture.stageWokenSendCompletion
  split
  · exact MappingStage.refl _
  · split
    · split
      · exact writeReturnFrameToTcb_mappingStage st _ _
      · exact MappingStage.refl _
    · exact MappingStage.refl _

theorem descheduleAtPlacement_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    MappingStage st (descheduleAtPlacement st tid) :=
  MappingStage.of_objectsAgreeOffRunLinks (descheduleAtPlacement_preserves_objects_invExt st tid)
    (descheduleAtPlacement_objectsAgreeOffRunLinks st tid)

theorem migrateSchedContextReplenishment_mappingStage (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) :
    MappingStage st (migrateSchedContextReplenishment st scId fromCore toCore) :=
  MappingStage.of_objects_eq (migrateSchedContextReplenishment_objects st scId fromCore toCore)

theorem returnDonatedSchedContext_mappingStage {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId}
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    MappingStage st st' :=
  MappingStage.of_kindPreservingWrite
    (fun hI => returnDonatedSchedContext_preserves_objects_invExt _ _ _ _ _ hI _ h)
    (fun hI => returnDonatedSchedContext_kindPreservingWrite hI h)

theorem returnDonatedSchedContextResolved_mappingStage {st st' : SystemState}
    {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {originalOwner : SeLe4n.ThreadId}
    (h : returnDonatedSchedContextResolved st serverTid scId originalOwner = .ok st') :
    MappingStage st st' := by
  obtain ⟨_, -, hR⟩ := returnDonatedSchedContextResolved_ok_decompose h
  exact returnDonatedSchedContext_mappingStage hR

/-! ### Reply -/

theorem endpointReplyOnCore_mappingStage {replier target : SeLe4n.ThreadId} {msg : IpcMessage}
    {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointReplyOnCore replier target msg executingCore st).1 :=
  fun hInv => by
    rcases endpointReplyOnCore_post_agrees replier target msg executingCore st hInv
      with h | ⟨expected, r1, hS, hA⟩
    · rw [h]; exact ⟨hInv, id⟩
    · exact MappingStage.of_postAgrees
        (fun h => endpointReplyOnCore_preserves_objects_invExt _ _ _ _ _ h)
        (fun h => endpointReply_kindPreservingWrite _ _ _ _ _ h hS) hA hInv

theorem applyReplyDonationOnCore_mappingStage {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {targetVtid : SeLe4n.ValidThreadId} {holderHome ownerHome : CoreId}
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st') :
    MappingStage st st' := by
  refine MappingStage.of_kindPreservingWrite
    (fun hI => applyReplyDonationOnCore_preserves_objects_invExt _ _ _ _ _ _ hI h) fun hI => ?_
  rcases applyReplyDonationOnCore_objects_frame _ _ _ _ _ _ h with ⟨-, hO⟩ | ⟨_, _, _, s, hR, hA⟩
  · exact kindPreservingWrite.of_objects_eq hO
  · exact (returnDonatedSchedContext_kindPreservingWrite hI hR).trans hA.kindPreserving

theorem endpointReplyCrossCoreDispatch_mappingStage {replier target : SeLe4n.ThreadId}
    {msg : IpcMessage} {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 := by
  unfold endpointReplyCrossCoreDispatch
  have hR := endpointReplyOnCore_mappingStage (replier := replier) (target := target)
    (msg := msg) (executingCore := executingCore) (st := st)
  generalize endpointReplyOnCore replier target msg executingCore st = r at hR
  obtain ⟨st1, res⟩ := r
  dsimp only at hR ⊢
  cases res with
  | error _ => exact MappingStage.refl _
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact MappingStage.refl _
      | exact hR.trans propagatePipChainCrossCore_mappingStage
      | (rename_i hD
         exact (hR.trans (applyReplyDonationOnCore_mappingStage hD)).trans
           propagatePipChainCrossCore_mappingStage)

theorem endpointReplyCrossCoreDispatchChecked_mappingStage {ctx : LabelingContext}
    {replier target : SeLe4n.ThreadId} {msg : IpcMessage} {executingCore : CoreId}
    {st : SystemState} :
    MappingStage st (endpointReplyCrossCoreDispatchChecked ctx replier target msg
      executingCore st).1 := by
  unfold endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch_mappingStage
  · exact MappingStage.refl _

theorem faultReplyOnCore_mappingStage {replier faulted : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {executingCore : CoreId} {st : SystemState} :
    MappingStage st (faultReplyOnCore replier faulted mi regs executingCore st).1 := by
  unfold faultReplyOnCore
  split
  · exact MappingStage.refl _
  split
  · exact MappingStage.refl _
  dsimp only
  have hR := endpointReplyCrossCoreDispatch_mappingStage (replier := replier) (target := faulted)
    (msg := IpcMessage.empty) (executingCore := executingCore) (st := st)
  generalize endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty executingCore st = r
    at hR
  obtain ⟨st1, res⟩ := r
  dsimp only at hR ⊢
  cases res with
  | error _ => exact MappingStage.refl _
  | ok sgi =>
    dsimp only
    unfold faultReplyApplyOnCore
    split
    · exact hR.trans (MappingStage.of_kindPreservingWrite
        (fun h => by unfold applyFaultRestart; exact SystemState.updateTcb_preserves_objects_invExt _ _ _ h)
        (fun h => applyFaultRestart_kindPreservingWrite _ _ _ h))
    · exact hR.trans (MappingStage.of_kindPreservingWrite
        (fun h => faultAbandonOnCore_preserves_objects_invExt _ _ _ h)
        (fun h => faultAbandonOnCore_kindPreservingWrite _ _ _ h))

theorem replyTransferOnCoreChecked_mappingStage {ctx : LabelingContext}
    {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo} {regs : Array SeLe4n.RegValue}
    {msg : IpcMessage} {executingCore : CoreId} {st st' : SystemState}
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg executingCore st
      = .ok ((), st')) :
    MappingStage st st' := by
  unfold replyTransferOnCoreChecked at h
  split at h
  · have hF := faultReplyOnCore_mappingStage (replier := replier) (faulted := callerTid)
      (mi := mi) (regs := regs) (executingCore := executingCore) (st := st)
    revert h hF
    generalize faultReplyOnCore replier callerTid mi regs executingCore st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h; cases h
    | ok _ => intro h hF; cases h; exact hF
  · have hR := endpointReplyCrossCoreDispatchChecked_mappingStage (ctx := ctx)
      (replier := replier) (target := callerTid) (msg := msg) (executingCore := executingCore)
      (st := st)
    revert h hR
    generalize endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg executingCore st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h; cases h
    | ok _ =>
      intro h hR
      cases h
      exact hR.trans (stageDeliveredMessage_mappingStage s callerTid 0)

/-! ### Notifications -/

theorem wakeThread_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    MappingStage st (wakeThread st tid c).1 :=
  MappingStage.of_kindPreservingWrite (wakeThread_preserves_objects_invExt st tid c)
    (wakeThread_kindPreservingWrite st tid c)

theorem notificationSignalOnCore_mappingStage {notificationId : SeLe4n.ObjId}
    {badge : SeLe4n.Badge} {executingCore : CoreId} {st : SystemState} :
    MappingStage st (notificationSignalOnCore notificationId badge executingCore st).1 :=
  fun hInv => by
    rcases notificationSignalOnCore_post_agrees notificationId badge executingCore st hInv
      with h | ⟨r1, hS, hA⟩
    · rw [h]; exact ⟨hInv, id⟩
    · exact MappingStage.of_postAgrees
        (fun h => notificationSignalOnCore_preserves_objects_invExt _ _ _ _ h)
        (fun h => notificationSignal_kindPreservingWrite _ _ _ _ h hS) hA hInv

theorem notificationSignalBoundOnCore_mappingStage {notificationId : SeLe4n.ObjId}
    {badge : SeLe4n.Badge} {executingCore : CoreId} {st : SystemState} :
    MappingStage st (notificationSignalBoundOnCore notificationId badge executingCore st).1 := by
  unfold notificationSignalBoundOnCore
  split
  · dsimp only
    split
    · exact MappingStage.refl _
    · rename_i st1 hR
      have h1 : MappingStage st st1 := MappingStage.of_kindPreservingWrite
        (fun h => endpointQueueRemoveDual_preserves_objects_invExt _ _ _ _ _ h hR)
        (fun h => endpointQueueRemoveDual_kindPreservingWrite _ _ _ _ _ h hR)
      split
      · exact MappingStage.refl _
      · rename_i st2 hT
        have h2 : MappingStage st1 st2 := MappingStage.of_kindPreservingWrite
          (fun h => storeTcbReceiveComplete_preserves_objects_invExt _ _ _ _ h hT)
          (fun h => storeTcbReceiveComplete_kindPreservingWrite h hT)
        exact (h1.trans h2).trans (wakeThread_mappingStage _ _ executingCore)
  · exact notificationSignalOnCore_mappingStage

theorem notificationSignalBoundCrossCoreDispatchChecked_mappingStage {ctx : LabelingContext}
    {notificationId : SeLe4n.ObjId} {signaler : SeLe4n.ThreadId} {badge : SeLe4n.Badge}
    {executingCore : CoreId} {st : SystemState} :
    MappingStage st (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler
      badge executingCore st).1 := by
  unfold notificationSignalBoundCrossCoreDispatchChecked
  split
  · split
    · split
      · exact notificationSignalBoundOnCore_mappingStage
      · exact MappingStage.refl _
    · exact notificationSignalBoundOnCore_mappingStage
  · exact MappingStage.refl _

/-- The single-core wait is a kind-preserving write: the park, then the waiter's
queue links. -/
theorem notificationWait_kindPreservingWrite {notifId : SeLe4n.ObjId} {waiter : SeLe4n.ThreadId}
    {st st' : SystemState} {r : Option SeLe4n.Badge} (hInv : st.objects.invExt)
    (h : notificationWait notifId waiter st = .ok (r, st')) : kindPreservingWrite st st' := by
  rcases notificationWait_ok_cases h with ⟨_, -, hP⟩ | ⟨-, stP, hP, hL⟩
  · exact notificationWaitPark_kindPreservingWrite _ _ _ _ _ hInv hP
  · have hIP := notificationWaitPark_preserves_objects_invExt hInv hP
    obtain ⟨st3, h3, h4⟩ := linkNtfnWaiter_ok_cases hL
    exact ((notificationWaitPark_kindPreservingWrite _ _ _ _ _ hInv hP).trans
      (modifyTcb_kindPreservingWrite hIP h3)).trans
      (modifyTcbOpt_kindPreservingWrite (modifyTcb_preserves_objects_invExt hIP h3) h4)

theorem notificationWaitOnCore_mappingStage {notificationId : SeLe4n.ObjId}
    {waiter : SeLe4n.ThreadId} {executingCore : CoreId} {st : SystemState} :
    MappingStage st (notificationWaitOnCore notificationId waiter executingCore st).1 :=
  fun hInv => by
    rcases notificationWaitOnCore_post_agrees notificationId waiter executingCore st hInv
      with h | ⟨r1, _, hS, hA⟩
    · rw [h]; exact ⟨hInv, id⟩
    · exact MappingStage.of_postAgrees
        (fun h => notificationWaitOnCore_preserves_objects_invExt _ _ _ _ h)
        (fun h => notificationWait_kindPreservingWrite h hS) hA hInv

theorem notificationWaitCrossCoreDispatchChecked_mappingStage {ctx : LabelingContext}
    {notificationId : SeLe4n.ObjId} {waiter : SeLe4n.ThreadId} {executingCore : CoreId}
    {st : SystemState} :
    MappingStage st (notificationWaitCrossCoreDispatchChecked ctx notificationId waiter
      executingCore st).1 := by
  unfold notificationWaitCrossCoreDispatchChecked
  split
  · exact notificationWaitOnCore_mappingStage
  · exact MappingStage.refl _

/-! ### ReplyRecv -/

theorem applyRendezvousCallDonation_mappingStage {st st' : SystemState}
    {receiver donor : SeLe4n.ThreadId}
    (h : applyRendezvousCallDonation st receiver donor = .ok st') : MappingStage st st' := by
  unfold applyRendezvousCallDonation at h
  split at h
  · exact applyCallDonationOnCore_mappingStage h
  · cases h

theorem replyRecvPopDonation_mappingStage {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {st st' : SystemState} {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (h : replyRecvPopDonation rid target st = .ok (r, st')) : MappingStage st st' := by
  unfold replyRecvPopDonation at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · cases h
      · rename_i st1 hRet
        cases h
        exact (returnDonatedSchedContextResolved_mappingStage hRet).trans
          (migrateSchedContextReplenishment_mappingStage _ _ _ _)
    · cases h
  · cases h; exact MappingStage.refl _

theorem replyRecvPostReceiveDonation_mappingStage
    {tid recordedServer nextThread : SeLe4n.ThreadId} {serverCore : CoreId}
    {returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {st st' : SystemState}
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
      = .ok ((), st')) : MappingStage st st' := by
  unfold replyRecvPostReceiveDonation at h
  split at h
  · cases h; exact propagatePipChainCrossCore_mappingStage
  · rename_i holder
    have hH : MappingStage st (replyRecvHolderDeschedule tid holder st) := by
      unfold replyRecvHolderDeschedule
      split
      · exact MappingStage.refl _
      · exact descheduleAtPlacement_mappingStage st holder
    split at h
    · split at h
      · cases h
      · rename_i st2 hD
        cases h
        exact (hH.trans (applyRendezvousCallDonation_mappingStage hD)).trans
          propagatePipChainCrossCore_mappingStage
    · cases h
      exact (descheduleAtPlacement_mappingStage st holder).trans
        propagatePipChainCrossCore_mappingStage

theorem applyReceiveLegPipHandoff_mappingStage (st : SystemState)
    (receiver dequeued alreadyWalked : SeLe4n.ThreadId) (executingCore : CoreId) :
    MappingStage st (applyReceiveLegPipHandoff st receiver dequeued alreadyWalked executingCore) := by
  unfold applyReceiveLegPipHandoff
  split
  · exact MappingStage.refl _
  split
  · exact propagatePipChainCrossCore_mappingStage
  · exact MappingStage.refl _

theorem endpointReplyRecvOnCore_mappingStage {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId}
    {msg : IpcMessage} {receiverCspaceRoot : SeLe4n.ObjId} {receiverSlotBase : SeLe4n.Slot}
    {executingCore : CoreId} {st st' : SystemState} {summary : CapTransferSummary}
    (h : endpointReplyRecvOnCore epId tid rid prevCaller msg receiverCspaceRoot receiverSlotBase
      executingCore st = .ok (summary, st')) : MappingStage st st' := by
  unfold endpointReplyRecvOnCore at h
  dsimp only at h
  have hR := endpointReplyOnCore_mappingStage (replier := tid) (target := prevCaller)
    (msg := msg) (executingCore := executingCore) (st := st)
  revert h hR
  generalize endpointReplyOnCore tid prevCaller msg executingCore st = r1
  obtain ⟨st1, res1⟩ := r1
  cases res1 with
  | error _ => intro h; cases h
  | ok _ =>
  intro h hR
  dsimp only at h hR
  split at h
  · cases h
  rename_i ret st1p hPop
  have hP := replyRecvPopDonation_mappingStage hPop
  have hV := endpointReceiveDualWithCapsOnCore_mappingStage (endpointId := epId)
    (receiver := tid) (replyId := some rid) (receiverCspaceRoot := receiverCspaceRoot)
    (receiverSlotBase := receiverSlotBase) (executingCore := executingCore) (st := st1p)
  revert h hV
  generalize endpointReceiveDualWithCapsOnCore epId tid (some rid) receiverCspaceRoot
    receiverSlotBase executingCore st1p = r2
  obtain ⟨st2, res2⟩ := r2
  cases res2 with
  | error _ => intro h; cases h
  | ok q =>
  obtain ⟨nextThread, summ, _⟩ := q
  intro h hV
  dsimp only at h hV
  split at h
  · cases h
  rename_i st3 hPost
  cases h
  exact (((((hR.trans hP).trans hV).trans (replyRecvPostReceiveDonation_mappingStage hPost)).trans
    (applyReceiveLegPipHandoff_mappingStage _ _ _ _ _)).trans
    (stageDeliveredMessage_mappingStage _ _ _)).trans (stageWokenSendCompletion_mappingStage _ _)

end SeLe4n.Kernel
