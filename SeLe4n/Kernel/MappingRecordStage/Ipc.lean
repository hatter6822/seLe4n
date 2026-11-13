-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.Basic
import SeLe4n.Kernel.Capability.Invariant.Preservation.Bookkeeping

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

/-- A per-core leg that agrees off the scheduler links with a kind-preserving
single-core leg, and shrinks no object table, keeps the mappings recorded. -/
theorem MappingStage.of_postAgrees {st r1 st' : SystemState}
    (hI : st.objects.invExt → st'.objects.invExt)
    (hC : st.objects.invExt → st.objects.capacity ≤ st'.objects.capacity)
    (hK : st.objects.invExt → kindPreservingWrite st r1) (hA : OffSchedulerAgrees r1 st') :
    MappingStage st st' :=
  MappingStage.of_kindPreservingWrite hI fun h =>
    ⟨fun oid => ((hK h) oid).trans (hA.objects.kindPreservingAt oid),
      ⟨hA.objectIndex.trans (hK h).ghosts.index, hA.objectIndexSet.trans (hK h).ghosts.indexSet,
        by rw [hA.lifecycle]; exact (hK h).ghosts.types, hC h,
        by rw [hA.asidTable]; exact (hK h).ghosts.asidCapacity⟩⟩

/-! ### The per-core legs shrink no object table

A per-core leg agrees with its single-core twin off the scheduler links, which
says nothing of the table's capacity; each leg's writes are inserts and in-place
rewrites, so it keeps a boot-sized store boot-sized on its own. -/

/-- WS-UC UC3: the cross-core signal shrinks no object table. -/
theorem notificationSignalOnCore_objects_capacity_le
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    st.objects.capacity ≤
      (notificationSignalOnCore notificationId badge executingCore st).1.objects.capacity := by
  unfold notificationSignalOnCore
  cases hObjN : st.getNotification? notificationId with
  | none => simp only; split <;> exact Nat.le_refl _
  | some ntfn =>
    simp only
    cases hWaiters : ntfn.waitHead with
    | none =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact Nat.le_refl _
      | ok pair => simp only; exact (storeObject_capacity_le hStore).1
    | some waiter =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact Nat.le_refl _
      | ok pair =>
        simp only
        have hC1 := (storeObject_capacity_le hStore).1
        have hObj1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
        cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
            (some { IpcMessage.empty with badge := some badge }) with
        | error e => simp only; exact Nat.le_refl _
        | ok st'' =>
          simp only
          have hC2 := (storeTcbIpcStateAndMessage_kindPreservingWrite hObj1 hTcb).ghosts.objectsCapacity
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2 st'' waiter _ _ hObj1 hTcb
          show _ ≤ (wakeThread _ waiter executingCore).1.objects.capacity
          exact Nat.le_trans (le_detachNtfnHead_objects_capacity _ _ _ (Nat.le_trans hC1 hC2))
            (wakeThread_kindPreservingWrite _ waiter executingCore
              (detachNtfnHead_linksRewritten _ _ _ hObj2).2.1).ghosts.objectsCapacity

/-- WS-UC UC3: the cross-core wait shrinks no object table. -/
theorem notificationWaitOnCore_objects_capacity_le
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    st.objects.capacity ≤
      (notificationWaitOnCore notificationId waiter executingCore st).1.objects.capacity := by
  unfold notificationWaitOnCore
  cases hObjN : st.getNotification? notificationId with
  | none => simp only; split <;> exact Nat.le_refl _
  | some ntfn =>
    simp only
    cases hBadge : ntfn.pendingBadge with
    | some badge =>
      simp only
      cases hStore : storeObject notificationId _ st with
      | error e => simp only; exact Nat.le_refl _
      | ok pair =>
        simp only
        have hObj1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
        cases hTcb : storeTcbIpcState pair.2 waiter .ready with
        | error e => simp only; exact Nat.le_refl _
        | ok st'' =>
          simp only
          exact Nat.le_trans (storeObject_capacity_le hStore).1
            (storeTcbIpcState_kindPreservingWrite hObj1 hTcb).ghosts.objectsCapacity
    | none =>
      simp only
      cases hLk : lookupTcb st waiter with
      | none => simp only; exact Nat.le_refl _
      | some tcb =>
        simp only
        split
        · exact Nat.le_refl _
        · cases hStore : storeObject notificationId _ st with
          | error e => simp only; exact Nat.le_refl _
          | ok pair =>
            simp only
            have hC1 := (storeObject_capacity_le hStore).1
            have hObj1 := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
            cases hTcb : storeTcbIpcStateAndMessage_fromTcb pair.2 waiter tcb
                (.blockedOnNotification notificationId) none with
            | error e => simp only; exact Nat.le_refl _
            | ok st2 =>
              simp only
              have hObj2 : st2.objects.invExt ∧ pair.2.objects.capacity ≤ st2.objects.capacity := by
                unfold storeTcbIpcStateAndMessage_fromTcb at hTcb
                cases hSO : storeObject waiter.toObjId
                    (.tcb (TCB.setIpcState { tcb with pendingMessage := none } (.blockedOnNotification notificationId)))
                    pair.2 with
                | error e => simp [hSO] at hTcb
                | ok p =>
                  simp only [hSO] at hTcb
                  have hE := Except.ok.inj hTcb; subst hE
                  exact ⟨storeObject_preserves_objects_invExt' pair.2 waiter.toObjId _ p hObj1 hSO,
                    (storeObject_capacity_le hSO).1⟩
              cases hLink : linkNtfnWaiter st2 waiter ntfn.waitTail with
              | error e => simp only; exact Nat.le_refl _
              | ok st'' =>
                simp only
                obtain ⟨st3, h3, h4⟩ := linkNtfnWaiter_ok_cases hLink
                have hK3 := modifyTcb_kindPreservingWrite hObj2.1 h3
                have hK4 := modifyTcbOpt_kindPreservingWrite
                  (modifyTcb_preserves_objects_invExt hObj2.1 h3) h4
                simpa using Nat.le_trans (Nat.le_trans (Nat.le_trans hC1 hObj2.2)
                  hK3.ghosts.objectsCapacity) hK4.ghosts.objectsCapacity

/-- WS-UC UC3: the cross-core reply shrinks no object table. -/
theorem endpointReplyOnCore_objects_capacity_le
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    st.objects.capacity ≤
      (endpointReplyOnCore replier target msg executingCore st).1.objects.capacity := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', server, pre, hLk, hStore, hPost, hTail⟩
  · rw [hEq]; exact Nat.le_refl _
  · rw [hPost, SystemState.unlinkReplyWaiterOpt_objects_capacity]
    have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hObj1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready
      (some msg) hObjInv hStore'
    have hC := Nat.le_trans (storeTcbIpcStateAndMessage_kindPreservingWrite hObjInv
      hStore').ghosts.objectsCapacity
      (wakeThread_kindPreservingWrite st' target executingCore hObj1).ghosts.objectsCapacity
    rcases hTail with ⟨_, hEq⟩ | ⟨rid, _, hCons⟩
    · rw [hEq]; exact hC
    · exact Nat.le_trans hC (removeCallerReplyFrame_kindPreservingWrite _ _ target rid
        (wakeThread_preserves_objects_invExt st' target executingCore hObj1) hCons).ghosts.objectsCapacity


/-! ### The capability transfer -/

theorem ipcTransferSingleCap_mappingStage {cap : Capability} {srcNode : SlotRef}
    {dst : CSpaceAddr} {st st' : SystemState}
    (h : ipcTransferSingleCap cap srcNode dst st = .ok ((), st')) :
    MappingStage st st' := fun hInv => by
  have hI' := ipcTransferSingleCap_preserves_objects_invExt _ _ _ _ _ hInv h
  obtain ⟨_, st2, -, -, -, hIns, rfl⟩ := ipcTransferSingleCap_ok_cases h
  have hI2 := cspaceInsertSlot_objects_invExt hInv hIns
  exact ⟨hI', fun hL => untypedSourceSetFull_preserves_liveMappingsRecorded
    ((SystemState.cdtAddChild_reach st2 _ _ _).invExt hI2)
    (cdtAddChild_preserves_liveMappingsRecorded hI2
      (cspaceInsertSlot_preserves_liveMappingsRecorded hInv hIns hL)),
    fun hB => untypedSourceSetFull_preserves_bookkeepingAgrees
    ((SystemState.cdtAddChild_reach st2 _ _ _).invExt hI2)
    (cdtAddChild_preserves_bookkeepingAgrees hI2
      (cspaceInsertSlot_preserves_bookkeepingAgrees hInv hB hIns))⟩

theorem ipcUnwrapCaps_mappingStage {caps : Array TransferCap} {endpointId : Option SeLe4n.ObjId}
    {rtcb : TCB} {slot? : Option CSpaceAddr} {st st' : SystemState}
    {summary : CapTransferSummary}
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    MappingStage st st' :=
  ipcUnwrapCaps_rel (fun a b => MappingStage b a) (fun _ => MappingStage.refl _)
    (fun _ _ _ h1 h2 => h2.trans h1)
    (fun _ _ _ => MappingStage.of_objects_eq (recordUnwrappedBadge_objects _ _ _ _)
      (recordUnwrappedBadge_ghostsKept _ _ _ _))
    (fun _ _ _ _ _ _ hT => ipcTransferSingleCap_mappingStage hT) h

/-- The rendezvous capability transfer is the identity or one unwrap from the
state it starts from. -/
theorem receiveTransferCaps_cases
    {req : Option (Capability × Array SeLe4n.CPtr)} {endpointId : Option SeLe4n.ObjId}
    {target? : Option (TCB × Option CSpaceAddr)} {st st'' : SystemState}
    {summary : CapTransferSummary}
    (h : receiveTransferCaps req endpointId target? st = .ok (summary, st'')) :
    st'' = st ∨ ∃ (caps : Array TransferCap) (rtcb : TCB) (slot? : Option CSpaceAddr),
      ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st'') := by
  unfold receiveTransferCaps at h
  cases req with
  | none => simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
  | some r =>
      obtain ⟨cr, addrs⟩ := r
      simp only at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
      · cases target? with
        | none => simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
        | some t =>
          obtain ⟨rtcb, slot?⟩ := t
          exact .inr ⟨_, rtcb, slot?, h⟩

theorem receiveTransferCaps_mappingStage
    {req : Option (Capability × Array SeLe4n.CPtr)} {endpointId : Option SeLe4n.ObjId}
    {target? : Option (TCB × Option CSpaceAddr)} {st st' : SystemState}
    {summary : CapTransferSummary}
    (h : receiveTransferCaps req endpointId target? st = .ok (summary, st')) :
    MappingStage st st' := by
  rcases receiveTransferCaps_cases h with rfl | ⟨_, rtcb, slot?, hU⟩
  · exact MappingStage.refl _
  · exact ipcUnwrapCaps_mappingStage hU

/-! ### Send -/

theorem endpointSendDualOnCore_mappingStage {endpointId : SeLe4n.ObjId}
    {sender : SeLe4n.ThreadId} {payload : SendPayload} {executingCore : CoreId}
    {st : SystemState} :
    MappingStage st (endpointSendDualOnCore endpointId sender payload executingCore st).1 :=
  fun hInv => by
    rcases endpointSendDualOnCore_post_agrees endpointId sender payload executingCore st hInv
      with h | ⟨r1, hS, hA⟩
    · rw [h]; exact ⟨hInv, id, id⟩
    · exact MappingStage.of_postAgrees
        (fun h => endpointSendDualOnCore_preserves_objects_invExt _ _ _ _ _ h)
        (endpointSendDualOnCore_objects_capacity_le _ _ _ _ _)
        (fun h => endpointSendDual_kindPreservingWrite _ _ _ _ _ h hS) hA hInv

/-- The send with capability transfer keeps the mappings recorded. -/
theorem endpointSendDualWithCapsOnCore_mappingStage {endpointId : SeLe4n.ObjId}
    {sender : SeLe4n.ThreadId} {payload : SendPayload}
    {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointSendDualWithCapsOnCore endpointId sender payload
      executingCore st).1 := by
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
    {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointSendCrossCoreDispatchChecked ctx endpointId sender payload
      executingCore st).1 := by
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
    · rw [h]; exact ⟨hInv, id, id⟩
    · exact MappingStage.of_postAgrees
        (fun h => endpointReceiveDualOnCore_preserves_objects_invExt _ _ _ _ _ h)
        (endpointReceiveDualOnCore_objects_capacity_le _ _ _ _ _)
        (fun h => endpointReceiveDual_kindPreservingWrite _ _ _ _ _ _ h hS) hA hInv

theorem endpointReceiveDualWithCapsOnCore_mappingStage {endpointId : SeLe4n.ObjId}
    {receiver : SeLe4n.ThreadId} {replyId : Option SeLe4n.ReplyId}

    {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointReceiveDualWithCapsOnCore endpointId receiver replyId executingCore st).1 := by
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
    {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointCallWithCapsOnCore endpointId caller payload
      executingCore st).1 := by
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
    {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointCallCrossCoreDispatch endpointId caller payload
      executingCore st).1 := by
  unfold endpointCallCrossCoreDispatch
  have hC := endpointCallWithCapsOnCore_mappingStage (endpointId := endpointId)
    (caller := caller) (payload := payload)
    (executingCore := executingCore) (st := st)
  generalize endpointCallWithCapsOnCore endpointId caller payload
    executingCore st = r at hC
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
    {executingCore : CoreId} {st : SystemState} :
    MappingStage st (endpointCallCrossCoreDispatchChecked ctx endpointId caller payload
      executingCore st).1 := by
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
  MappingStage.of_kindPreservingWrite
    (migrateSchedContextReplenishment_preserves_objects_invExt st scId fromCore toCore)
    fun _ => (SystemState.objectsAgreeOffSchedulerLinks.of_releaseLinks
      (migrateSchedContextReplenishment_agree st scId fromCore toCore)).kindPreserving

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
    · rw [h]; exact ⟨hInv, id, id⟩
    · exact MappingStage.of_postAgrees
        (fun h => endpointReplyOnCore_preserves_objects_invExt _ _ _ _ _ h)
        (endpointReplyOnCore_objects_capacity_le _ _ _ _ _)
        (fun h => endpointReply_kindPreservingWrite _ _ _ _ _ h hS) hA hInv

/-- **The pop at an unheld head is a mapping stage**: the unheld pop's three
stores keep every object's kind, and the settle writes scheduler links alone;
the sever's two stores keep every kind as well. -/
theorem popUnheldReplyHead_mappingStage {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} {home : CoreId}
    (h : popUnheldReplyHead st rid target home = .ok st') : MappingStage st st' := by
  rcases popUnheldReplyHead_objects_frame h with ⟨-, rfl⟩ | ⟨_, _, st1, -, -, hP, rfl⟩ |
      ⟨_, _, -, -, hS⟩
  · exact MappingStage.refl _
  rotate_left
  · exact MappingStage.of_kindPreservingWrite
      (fun hI => severUnheldSchedContext_objects_invExt hI hS)
      (fun hI => severUnheldSchedContext_kindPreservingWrite hI hS)
  · exact (MappingStage.of_kindPreservingWrite
      (fun hI => returnUnheldSchedContext_objects_invExt hI hP)
      (fun hI => returnUnheldSchedContext_kindPreservingWrite hI hP)).trans
      (MappingStage.of_kindPreservingWrite
        (SchedContextOps.settleReturnedContext_objects_invExt _ _ _)
        fun _ => (SystemState.objectsAgreeOffSchedulerLinks.of_releaseLinks
          (SchedContextOps.settleReturnedContext_agree _ _ _)).kindPreserving)

theorem applyReplyDonationOnCore_mappingStage {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {targetVtid : SeLe4n.ValidThreadId} {ownerHome : CoreId}
    (h : applyReplyDonationOnCore st rid targetVtid ownerHome = .ok st') :
    MappingStage st st' := by
  rcases applyReplyDonationOnCore_ok_decompose _ _ _ _ _ h with
    ⟨-, hP⟩ | ⟨_, holderVtid, _, _, -, -, hR, rfl⟩
  · exact popUnheldReplyHead_mappingStage hP
  · exact ((returnDonatedSchedContext_mappingStage hR).trans
      (MappingStage.of_kindPreservingWrite
        (SchedContextOps.settleReturnedContext_objects_invExt _ _ _)
        fun _ => (SystemState.objectsAgreeOffSchedulerLinks.of_releaseLinks
          (SchedContextOps.settleReturnedContext_agree _ _ _)).kindPreserving)).trans
      (descheduleAtPlacement_mappingStage _ holderVtid.val)

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
      | exact hR
      | exact hR.trans propagatePipChainCrossCore_mappingStage
      | (rename_i hD
         exact (hR.trans (applyReplyDonationOnCore_mappingStage hD)).trans
           propagatePipChainCrossCore_mappingStage)
      | (rename_i hD
         exact hR.trans (applyReplyDonationOnCore_mappingStage hD))

theorem endpointReplyCrossCoreDispatchChecked_mappingStage {ctx : LabelingContext}
    {replier target : SeLe4n.ThreadId} {msg : IpcMessage} {executingCore : CoreId}
    {st : SystemState} :
    MappingStage st (endpointReplyCrossCoreDispatchChecked ctx replier target msg
      executingCore st).1 := by
  unfold endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch_mappingStage
  · exact MappingStage.refl _

/-- The fault reply's decoded outcome is a kind-preserving TCB write: the
restart frame, or the abandon's deschedule and `.Inactive` mark. -/
theorem faultReplyApplyOnCore_mappingStage (st : SystemState) (faulted : SeLe4n.ThreadId)
    (outcome : Architecture.FaultReplyOutcome) :
    MappingStage st (faultReplyApplyOnCore st faulted outcome) := by
  unfold faultReplyApplyOnCore
  split
  · exact MappingStage.of_kindPreservingWrite
      (fun h => by unfold applyFaultRestart; exact SystemState.updateTcb_preserves_objects_invExt _ _ _ h)
      (fun h => applyFaultRestart_kindPreservingWrite _ _ _ h)
  · exact MappingStage.of_kindPreservingWrite
      (fun h => faultAbandonOnCore_preserves_objects_invExt _ _ _ h)
      (fun h => faultAbandonOnCore_kindPreservingWrite _ _ _ h)

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
    exact hR.trans (faultReplyApplyOnCore_mappingStage _ _ _)

theorem replyTransferOnCoreChecked_mappingStage {ctx : LabelingContext}
    {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo} {regs : Array SeLe4n.RegValue}
    {msg : IpcMessage} {grant : Bool} {executingCore : CoreId} {st st' : SystemState}
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant executingCore st
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
      simp only [] at h
      cases hX : replyTransferCaps st replier callerTid grant s with
      | error _ => rw [hX] at h; cases h
      | ok p =>
        obtain ⟨summary, sX⟩ := p
        rw [hX] at h
        cases h
        exact (hR.trans (receiveTransferCaps_mappingStage hX)).trans
          (stageDeliveredMessage_mappingStage sX callerTid summary.capInfo)

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
    · rw [h]; exact ⟨hInv, id, id⟩
    · exact MappingStage.of_postAgrees
        (fun h => notificationSignalOnCore_preserves_objects_invExt _ _ _ _ h)
        (notificationSignalOnCore_objects_capacity_le _ _ _ _)
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
    · rw [h]; exact ⟨hInv, id, id⟩
    · exact MappingStage.of_postAgrees
        (fun h => notificationWaitOnCore_preserves_objects_invExt _ _ _ _ h)
        (notificationWaitOnCore_objects_capacity_le _ _ _ _)
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
          (MappingStage.of_kindPreservingWrite
            (SchedContextOps.settleReturnedContext_objects_invExt _ _ _)
            fun _ => (SystemState.objectsAgreeOffSchedulerLinks.of_releaseLinks
              (SchedContextOps.settleReturnedContext_agree _ _ _)).kindPreserving)
    · cases h
  · split at h
    · cases h
    · rename_i st1 hPop
      cases h
      exact popUnheldReplyHead_mappingStage hPop

theorem replyRecvPostReceiveDonation_mappingStage
    {tid recordedServer nextThread : SeLe4n.ThreadId} {serverCore : CoreId}
    {returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {st st' : SystemState}
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
      = .ok ((), st')) : MappingStage st st' := by
  unfold replyRecvPostReceiveDonation at h
  split at h
  · split at h
    · split at h
      · cases h
      · rename_i st2 hD
        cases h
        exact (applyRendezvousCallDonation_mappingStage hD).trans
          propagatePipChainCrossCore_mappingStage
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

/-- The reply leg's answer to its caller: the ordinary staging, or the fault
reply's decoded outcome. -/
theorem replyRecvAnswerCaller_mappingStage (answer : Option Architecture.FaultReplyOutcome)
    (st : SystemState) (prevCaller : SeLe4n.ThreadId) (capInfo : Nat) :
    MappingStage st (replyRecvAnswerCaller answer st prevCaller capInfo) := by
  cases answer with
  | none => exact stageDeliveredMessage_mappingStage _ _ _
  | some o => exact faultReplyApplyOnCore_mappingStage _ _ o

theorem endpointReplyRecvOnCore_mappingStage {answer : Option Architecture.FaultReplyOutcome}
    {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId}
    {msg : IpcMessage} {grant : Bool}
    {executingCore : CoreId} {st st' : SystemState} {summary : CapTransferSummary}
    (h : endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg grant executingCore st
      = .ok (summary, st')) : MappingStage st st' := by
  unfold endpointReplyRecvAnsweringOnCore at h
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
  rename_i ret st1q hPop
  have hP := replyRecvPopDonation_mappingStage hPop
  split at h
  · cases h
  rename_i xs st1p hX
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX
  have hXs := receiveTransferCaps_mappingStage hX
  have hV := endpointReceiveDualWithCapsOnCore_mappingStage (endpointId := epId)
    (receiver := tid) (replyId := some rid)
    (executingCore := executingCore) (st := st1p)
  revert h hV
  generalize endpointReceiveDualWithCapsOnCore epId tid (some rid) executingCore st1p = r2
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
  exact ((((((hR.trans hP).trans hXs).trans hV).trans
    (replyRecvPostReceiveDonation_mappingStage hPost)).trans
    (applyReceiveLegPipHandoff_mappingStage _ _ _ _ _)).trans
    (replyRecvAnswerCaller_mappingStage answer _ prevCaller _)).trans
    (stageWokenSendCompletion_mappingStage _ _)

end SeLe4n.Kernel
