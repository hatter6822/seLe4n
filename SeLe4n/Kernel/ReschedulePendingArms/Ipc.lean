-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ReschedulePendingArms.Lifecycle

/-!
# The IPC arms cover

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md`, PR B2.  The IPC object
writes (queue links, IPC state, staged messages, transferred capabilities) move
no key input; the scheduler writes are a wake (which flags the core it inserts
on), the caller's own deschedule on the executing core, and the donation lend
and return, which end in their key hooks.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-! ### The TCB and endpoint writes -/

/-- A TCB write that keeps the key fields moves no key input. -/
theorem modifyTcb_keyFrame {st st' : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hF : ∀ t, tcbKeyFields (f t) = tcbKeyFields t) (hInv : st.objects.invExt)
    (h : modifyTcb st tid f = .ok st') : capabilityKeyFrame st st' := by
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  exact storeObject_tcbKeyKeeping_keyFrame hInv (lookupTcb_some_objects _ _ _ hL) hS (hF tcb)

theorem storeTcbQueueLinks_keyFrame {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {prev : Option SeLe4n.ThreadId} {pprev : Option QueuePPrev} {next : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    capabilityKeyFrame st st' := by
  unfold storeTcbQueueLinks at h
  exact modifyTcb_keyFrame (f := fun tcb => tcbWithQueueLinks tcb prev pprev next)
    (fun _ => rfl) hInv h

/-- A store over a slot no key reads, of an object no key reads. -/
theorem storeObject_endpoint_keyFrame {st : SystemState} {oid : SeLe4n.ObjId}
    {ep ep' : Endpoint} (hInv : st.objects.invExt)
    (hPre : st.objects[oid]? = some (.endpoint ep))
    {pair : Unit × SystemState}
    (h : storeObject oid (.endpoint ep') st = .ok pair) : capabilityKeyFrame st pair.2 :=
  storeObject_inert_keyFrame hInv h (by rw [hPre]; rfl) rfl

/-- Popping an endpoint queue's head rewrites the endpoint and two queue links. -/
theorem endpointQueuePopHead_keyFrame {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {st st' : SystemState} {rTid : SeLe4n.ThreadId} {rTcb : TCB} (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    capabilityKeyFrame st st' := by
  unfold endpointQueuePopHead SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          split at hStep
          · simp at hStep
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hS1 : capabilityKeyFrame st pair.2 := storeObject_endpoint_keyFrame hObjInv hObj hStore
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact hS1.trans (storeTcbQueueLinks_keyFrame hInv1 hFinal)
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact (hS1.trans (storeTcbQueueLinks_keyFrame hInv1 hLink)).trans
                      (storeTcbQueueLinks_keyFrame hInv2 hFinal)

/-- Enqueueing on an endpoint rewrites the endpoint and at most two queue links. -/
theorem endpointQueueEnqueue_keyFrame {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    capabilityKeyFrame st st' := by
  unfold endpointQueueEnqueue SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        split at hStep
        · simp at hStep
        · split at hStep
          · simp at hStep
          · revert hStep
            cases (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                intro hStep
                exact (storeObject_endpoint_keyFrame hObjInv hObj hStore).trans
                  (storeTcbQueueLinks_keyFrame hInv1 hStep)
            | some tailTid =>
              cases hLookupT : lookupTcb st tailTid
              · simp [hLookupT]
              · rename_i tailTcb
                simp only [hLookupT]
                cases hStore : storeObject endpointId _ st
                · simp
                · rename_i pair
                  simp only []
                  have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid _ _ (some tid)
                  · simp
                  · rename_i st2
                    simp only []
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    intro hStep
                    exact ((storeObject_endpoint_keyFrame hObjInv hObj hStore).trans
                      (storeTcbQueueLinks_keyFrame hInv1 hLink1)).trans
                      (storeTcbQueueLinks_keyFrame hInv2 hStep)

theorem storeTcbIpcStateAndMessage_keyFrame {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {ipc : ThreadIpcState} {msg : Option IpcMessage} (hInv : st.objects.invExt)
    (h : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') : capabilityKeyFrame st st' := by
  unfold storeTcbIpcStateAndMessage at h
  exact modifyTcb_keyFrame (f := fun tcb => { tcb with ipcState := ipc, pendingMessage := msg })
    (fun _ => rfl) hInv h

theorem storeTcbReceiveComplete_keyFrame {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {msg : Option IpcMessage} (hInv : st.objects.invExt)
    (h : storeTcbReceiveComplete st tid msg = .ok st') : capabilityKeyFrame st st' := by
  unfold storeTcbReceiveComplete at h
  exact modifyTcb_keyFrame
    (f := fun tcb => { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none })
    (fun _ => rfl) hInv h

/-! ### The scheduler writes -/

/-- A wake covers: it flags the core it inserts on. -/
theorem wakeThread_stepCovers (e : CoreId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (hInv : st.objects.invExt) :
    stepCovers e st (wakeThread st tid executingCore).1 ∧
      (wakeThread st tid executingCore).1.objects.invExt := by
  refine ⟨?_, wakeThread_preserves_objects_invExt st tid executingCore hInv⟩
  rw [wakeThread_state_eq_enqueue]
  exact ⟨enqueueRunnableOnCore_covers e _ st tid hInv, enqueueRunnableOnCore_monotone e _ st tid⟩

theorem removeRunnableOnCore_stepCovers (e : CoreId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) : stepCovers e st (removeRunnableOnCore st tid c) :=
  ⟨removeRunnableOnCore_covers e st tid c, removeRunnableOnCore_monotone e st tid c⟩

/-! ### Send -/

/-- The per-core send covers on every outcome: an error returns the pre-state,
the rendezvous wakes the receiver, and the block takes the sender off the
executing core. -/
theorem endpointSendDualOnCore_stepCovers (e : CoreId) {endpointId : SeLe4n.ObjId}
    {sender : SeLe4n.ThreadId} {msg : IpcMessage} {executingCore : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (endpointSendDualOnCore endpointId sender msg executingCore st).1 ∧
      (endpointSendDualOnCore endpointId sender msg executingCore st).1.objects.invExt := by
  unfold endpointSendDualOnCore
  split
  · exact ⟨stepCovers_refl e st, hInv⟩
  split
  · exact ⟨stepCovers_refl e st, hInv⟩
  split
  · rename_i ep _
    split
    · split
      · exact ⟨stepCovers_refl e st, hInv⟩
      · split
        · exact ⟨stepCovers_refl e st, hInv⟩
        · rename_i receiver _tcb st1 hPop
          split
          · exact ⟨stepCovers_refl e st, hInv⟩
          · rename_i st2 hRecv
            have hF1 := endpointQueuePopHead_keyFrame hInv hPop
            have hInv1 := endpointQueuePopHead_preserves_objects_invExt _ _ _ _ _ _ hInv hPop
            have hF2 := storeTcbReceiveComplete_keyFrame hInv1 hRecv
            have hInv2 := storeTcbReceiveComplete_preserves_objects_invExt _ _ _ _ hInv1 hRecv
            obtain ⟨hW, hWInv⟩ := wakeThread_stepCovers e st2 receiver executingCore hInv2
            exact ⟨stepCovers_trans (hF1.trans hF2).stepCovers hW, hWInv⟩
    · split
      · exact ⟨stepCovers_refl e st, hInv⟩
      · rename_i st1 hEnq
        split
        · exact ⟨stepCovers_refl e st, hInv⟩
        · rename_i st2 hBlk
          have hF1 := endpointQueueEnqueue_keyFrame hInv hEnq
          have hInv1 := endpointQueueEnqueue_preserves_objects_invExt _ _ _ _ _ hInv hEnq
          have hF2 := storeTcbIpcStateAndMessage_keyFrame hInv1 hBlk
          have hInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hInv1 hBlk
          exact ⟨stepCovers_trans (hF1.trans hF2).stepCovers
            (removeRunnableOnCore_stepCovers e st2 sender executingCore), hInv2⟩
  · split <;> exact ⟨stepCovers_refl e st, hInv⟩

/-- Installing transferred capabilities writes CNodes and the CDT only. -/
theorem ipcUnwrapCaps_keyFrame {msg : IpcMessage} {receiverRoot : SeLe4n.ObjId}
    {slotBase : SeLe4n.Slot} {grantRight : Bool} {st st' : SystemState}
    {summary : CapTransferSummary} (hInv : st.objects.invExt)
    (h : ipcUnwrapCaps msg receiverRoot slotBase grantRight st = .ok (summary, st')) :
    capabilityKeyFrame st st' :=
  ⟨keyInputsEq_of_lookups_eq
      (fun t => ipcUnwrapCaps_getTcb?_eq _ _ _ _ _ _ _ t hInv h)
      (fun s => ipcUnwrapCaps_getSchedContext?_eq _ _ _ _ _ _ _ s hInv h),
    ipcUnwrapCaps_preserves_scheduler _ _ _ _ _ _ _ h,
    ipcUnwrapCaps_preserves_objects_invExt _ _ _ _ _ _ _ hInv h⟩

/-- The send with capability transfer covers on every outcome. -/
theorem endpointSendDualWithCapsOnCore_stepCovers (e : CoreId) {endpointId : SeLe4n.ObjId}
    {sender : SeLe4n.ThreadId} {msg : IpcMessage} {endpointRights : AccessRightSet}
    {receiverSlotBase : SeLe4n.Slot} {executingCore : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
      receiverSlotBase executingCore st).1 ∧
    (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
      receiverSlotBase executingCore st).1.objects.invExt := by
  unfold endpointSendDualWithCapsOnCore
  obtain ⟨hSend, hSendInv⟩ := endpointSendDualOnCore_stepCovers e
    (endpointId := endpointId) (sender := sender)
    (msg := { msg with capsGranted := endpointRights.mem .grant })
    (executingCore := executingCore) hInv
  generalize endpointSendDualOnCore endpointId sender
    { msg with capsGranted := endpointRights.mem .grant } executingCore st = r at hSend hSendInv
  obtain ⟨st1, res⟩ := r
  dsimp only at hSend hSendInv ⊢
  cases res with
  | error _ => exact ⟨hSend, hSendInv⟩
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact ⟨hSend, hSendInv⟩
      | (rename_i hU
         have hF := ipcUnwrapCaps_keyFrame hSendInv hU
         exact ⟨stepCovers_trans hSend hF.stepCovers, hF.2.2⟩)

/-- The live checked send covers on every outcome. -/
theorem endpointSendCrossCoreDispatchChecked_stepCovers (e : CoreId) {ctx : LabelingContext}
    {endpointId : SeLe4n.ObjId} {sender : SeLe4n.ThreadId} {msg : IpcMessage}
    {endpointRights : AccessRightSet} {receiverSlotBase : SeLe4n.Slot} {executingCore : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    stepCovers e st (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg
      endpointRights receiverSlotBase executingCore st).1 ∧
    (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg
      endpointRights receiverSlotBase executingCore st).1.objects.invExt := by
  unfold endpointSendCrossCoreDispatchChecked
  split
  · exact ⟨stepCovers_refl e st, hInv⟩
  split
  · exact ⟨stepCovers_refl e st, hInv⟩
  split
  · exact endpointSendDualWithCapsOnCore_stepCovers e hInv
  · exact ⟨stepCovers_refl e st, hInv⟩

/-! ### Receive -/

/-- Linking a caller to a reply object writes the reply and the caller's
`replyObject`, neither of them a key input. -/
theorem linkReply_keyFrame {rid : SeLe4n.ReplyId} {caller : SeLe4n.ThreadId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SystemState.linkReply rid caller st = .ok ((), st')) : capabilityKeyFrame st st' := by
  unfold SystemState.linkReply at h
  cases hR : st.getReply? rid with
  | none => simp [hR] at h
  | some r =>
    simp only [hR] at h
    split at h
    · exact storeObject_inert_keyFrame hInv h
        (by rw [(SystemState.getReply?_eq_some_iff st rid r).mp hR]; rfl) rfl
    · simp at h

theorem linkCallerReply_keyFrame {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  unfold SystemState.linkCallerReply at h
  cases hLink : SystemState.linkReply rid caller st with
  | error e => simp [hLink] at h
  | ok p1 =>
    obtain ⟨⟨⟩, st1⟩ := p1
    simp only [hLink] at h
    have hF1 := linkReply_keyFrame hInv hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at h
    | some tcb =>
      simp only [hT] at h
      split at h
      · exact hF1.trans (storeObject_tcbKeyKeeping_keyFrame hF1.2.2
          ((SystemState.getTcb?_eq_some_iff st1 caller tcb).mp hT) h rfl)
      · simp at h

/-- The pre-receive cleanup covers: the donated context's return ends in its key
hooks, and the replenishment migration moves no key and no remote slot. -/
theorem cleanupPreReceiveDonationMigrated_stepCovers (e : CoreId) {st st' : SystemState}
    {receiver : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : cleanupPreReceiveDonationMigrated st receiver = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  refine ⟨?_, cleanupPreReceiveDonationMigrated_preserves_objects_invExt st st' receiver hInv h⟩
  obtain ⟨stClean, hC, rfl⟩ := cleanupPreReceiveDonationMigrated_ok_decompose h
  have hClean : stepCovers e st stClean := by
    unfold cleanupPreReceiveDonationChecked at hC
    split at hC
    · cases hC; exact stepCovers_refl e st
    · split at hC
      · exact (returnDonatedSchedContextResolved_stepCovers e hInv hC).1
      · cases hC; exact stepCovers_refl e st
  refine stepCovers_trans hClean ?_
  unfold preReceiveReturnMigration
  split
  · exact migrateSchedContextReplenishment_stepCovers e _ _ _ _
  · exact stepCovers_refl e _

/-- The per-core receive covers on every outcome: a call rendezvous moves no key
and no slot, a send rendezvous wakes the sender, and the block runs the
pre-receive cleanup and takes the receiver off the executing core. -/
theorem endpointReceiveDualOnCore_stepCovers (e : CoreId) {endpointId : SeLe4n.ObjId}
    {receiver : SeLe4n.ThreadId} {replyId : Option SeLe4n.ReplyId} {executingCore : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    stepCovers e st (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 ∧
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1.objects.invExt := by
  have hRefl : stepCovers e st st ∧ st.objects.invExt := ⟨stepCovers_refl e st, hInv⟩
  unfold endpointReceiveDualOnCore
  split
  · split
    · -- a sender is waiting
      split
      · exact hRefl
      · rename_i sender senderTcb st1 hPop
        have hF1 := endpointQueuePopHead_keyFrame hInv hPop
        dsimp only
        split <;> simp only [↓reduceIte, Bool.false_eq_true]
        · -- the sender called: no wake
          split
          · exact hRefl
          · rename_i st2 hBlk
            have hF2 := hF1.trans (storeTcbIpcStateAndMessage_keyFrame hF1.2.2 hBlk)
            split
            · exact hRefl
            · split
              · exact hRefl
              · rename_i stL hL
                have hF3 := hF2.trans (linkCallerReply_keyFrame hF2.2.2 hL)
                split
                · rename_i st4 hRdy
                  have hF4 := hF3.trans (storeTcbIpcStateAndMessage_keyFrame hF3.2.2 hRdy)
                  exact ⟨hF4.stepCovers, hF4.2.2⟩
                · exact hRefl
        · split
          · exact hRefl
          · rename_i st2 hRdy
            have hF2 := hF1.trans (storeTcbIpcStateAndMessage_keyFrame hF1.2.2 hRdy)
            obtain ⟨hW, hWInv⟩ := wakeThread_stepCovers e st2 sender executingCore hF2.2.2
            split
            · rename_i st4 hRcv
              have hF4 := storeTcbIpcStateAndMessage_keyFrame hWInv hRcv
              exact ⟨stepCovers_trans (stepCovers_trans hF2.stepCovers hW) hF4.stepCovers, hF4.2.2⟩
            · exact hRefl
    · -- no sender: block
      split
      · exact hRefl
      · rename_i stClean hClean
        obtain ⟨hC, hCInv⟩ := cleanupPreReceiveDonationMigrated_stepCovers e hInv hClean
        split
        · exact hRefl
        · rename_i st1 hEnq
          have hF1 := endpointQueueEnqueue_keyFrame hCInv hEnq
          split
          · exact hRefl
          · rename_i st2 hBlk
            have hF2 := hF1.trans (storeTcbIpcStateAndMessage_keyFrame hF1.2.2 hBlk)
            have hPre := stepCovers_trans hC hF2.stepCovers
            split
            · exact ⟨stepCovers_trans hPre (removeRunnableOnCore_stepCovers e _ _ _), hF2.2.2⟩
            · rename_i rTcb hT
              split
              · split
                · exact hRefl
                · rename_i stS hS
                  have hF3 := storeObject_tcbKeyKeeping_keyFrame hF2.2.2
                    ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hS rfl
                  exact ⟨stepCovers_trans (stepCovers_trans hPre hF3.stepCovers)
                    (removeRunnableOnCore_stepCovers e _ _ _), hF3.2.2⟩
              · exact hRefl
  · split <;> exact hRefl

/-- The receive with capability transfer covers on every outcome. -/
theorem endpointReceiveDualWithCapsOnCore_stepCovers (e : CoreId) {endpointId : SeLe4n.ObjId}
    {receiver : SeLe4n.ThreadId} {replyId : Option SeLe4n.ReplyId}
    {receiverCspaceRoot : SeLe4n.ObjId} {receiverSlotBase : SeLe4n.Slot}
    {executingCore : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    stepCovers e st (endpointReceiveDualWithCapsOnCore endpointId receiver replyId
      receiverCspaceRoot receiverSlotBase executingCore st).1 ∧
    (endpointReceiveDualWithCapsOnCore endpointId receiver replyId
      receiverCspaceRoot receiverSlotBase executingCore st).1.objects.invExt := by
  unfold endpointReceiveDualWithCapsOnCore
  obtain ⟨hRcv, hRcvInv⟩ := endpointReceiveDualOnCore_stepCovers e
    (endpointId := endpointId) (receiver := receiver) (replyId := replyId)
    (executingCore := executingCore) hInv
  generalize endpointReceiveDualOnCore endpointId receiver replyId executingCore st = r
    at hRcv hRcvInv
  obtain ⟨st1, res⟩ := r
  dsimp only at hRcv hRcvInv ⊢
  cases res with
  | error _ => exact ⟨hRcv, hRcvInv⟩
  | ok p =>
    obtain ⟨senderId, sgi⟩ := p
    dsimp only
    repeat' split
    all_goals first
      | exact ⟨hRcv, hRcvInv⟩
      | (rename_i hU
         have hF := ipcUnwrapCaps_keyFrame hRcvInv hU
         exact ⟨stepCovers_trans hRcv hF.stepCovers, hF.2.2⟩)

/-! ### The donation lend -/

/-- **The donation lend covers**: it rebinds the donor and the server and ends
in a key hook for each. -/
theorem donateSchedContext_stepCovers (e : CoreId) {st st' : SystemState}
    {clientTid serverTid : SeLe4n.ThreadId} {clientScId : SeLe4n.SchedContextId}
    (hInv : st.objects.invExt)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  refine ⟨?_, donateSchedContext_preserves_objects_invExt _ _ _ _ _ hInv h⟩
  unfold donateSchedContext at h
  revert h
  cases hSc : st.getSchedContext? clientScId with
  | none => intro h; cases h
  | some sc =>
    have hObj := (SystemState.getSchedContext?_eq_some_iff st clientScId sc).mp hSc
    simp only []
    split
    · intro h; cases h
    cases hD : lookupTcb st clientTid with
    | none => intro h; cases h
    | some donorTcb =>
      simp only []
      cases hFrame : donationPushFrame? st donorTcb with
      | error _ => intro h; cases h
      | ok pr =>
        obtain ⟨pushRid, pushReply⟩ := pr
        simp only []
        cases hS1 : storeObject clientScId.toObjId _ st with
        | error _ => intro h; cases h
        | ok p1 =>
          obtain ⟨⟨⟩, s1⟩ := p1
          simp only []
          cases hS2 : storeDonationFramePush clientScId pushRid pushReply sc.scReply s1 with
          | error _ => intro h; cases h
          | ok s2 =>
            simp only []
            cases hL1 : lookupTcb s2 clientTid with
            | none => intro h; cases h
            | some clientTcb =>
              simp only []
              cases hS3 : storeObject clientTid.toObjId
                  (.tcb { clientTcb with schedContextBinding := .unbound }) s2 with
              | error _ => intro h; cases h
              | ok p3 =>
                obtain ⟨⟨⟩, s3⟩ := p3
                simp only []
                cases hL2 : lookupTcb s3 serverTid with
                | none => intro h; cases h
                | some serverTcb =>
                  simp only []
                  cases hS4 : storeObject serverTid.toObjId
                      (.tcb { serverTcb with
                        schedContextBinding := .donated clientScId clientTid }) s3 with
                  | error _ => intro h; cases h
                  | ok p4 =>
                    obtain ⟨⟨⟩, s4⟩ := p4
                    simp only []
                    intro h
                    cases h
                    have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
                    have hRepPre : st.getReply? pushRid = some pushReply :=
                      (donationPushFrame?_ok st donorTcb pushRid pushReply hFrame).2.1
                    have hKeyNe := getReply?_getSchedContext?_key_ne st pushRid clientScId
                      pushReply sc hRepPre hSc
                    have hRep1 : s1.getReply? pushRid = some pushReply := by
                      rw [SystemState.getReply?_eq_some_iff,
                        storeObject_objects_ne st s1 clientScId.toObjId pushRid.toObjId _ hKeyNe
                          hInv hS1]
                      exact (SystemState.getReply?_eq_some_iff st pushRid pushReply).mp hRepPre
                    have hInv2 := storeDonationFramePush_preserves_objects_invExt hInv1 hS2
                    have hInv3 := storeObject_preserves_objects_invExt _ _ _ _ hInv2 hS3
                    have k1 : keyInputsEq st s1 :=
                      keyInputsEq_storeObject hInv hS1 (by rw [hObj]; rfl)
                    have k2 := keyInputsEq_trans k1 (keyInputsEq_of_lookups_eq
                      (storeDonationFramePush_getTcb?_eq hInv1 hRep1 hS2)
                      (storeDonationFramePush_getSchedContext?_eq hInv1 hRep1 hS2))
                    have k3 := keyInputsEqExcept_storeObject_tcb hInv2
                      (lookupTcb_some_objects _ _ _ hL1) hS3
                    have k4 := keyInputsEqExcept_storeObject_tcb hInv3
                      (lookupTcb_some_objects _ _ _ hL2) hS4
                    refine stepCovers_markKeyChangeFrom_pair (fun t hc hs => ?_) ?_
                    · show schedKeyView s4 t = schedKeyView st t
                      rw [schedKeyView_eq_of_keyInputsEqExcept k4 hs,
                        schedKeyView_eq_of_keyInputsEqExcept k3 hc,
                        schedKeyView_eq_of_keyInputsEq k2]
                    · show s4.scheduler = st.scheduler
                      rw [storeObject_scheduler_eq _ _ _ _ hS4, storeObject_scheduler_eq _ _ _ _ hS3,
                        storeDonationFramePush_scheduler_eq hS2,
                        storeObject_scheduler_eq _ _ _ _ hS1]

theorem applyCallDonation_stepCovers (e : CoreId) {st st' : SystemState}
    {callerVtid receiverVtid : SeLe4n.ValidThreadId} (hInv : st.objects.invExt)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold applyCallDonation at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨stepCovers_refl e st, hInv⟩)
    | (cases h; rename_i hD; exact donateSchedContext_stepCovers e hInv hD)
    | (cases h; done)

theorem applyCallDonationOnCore_stepCovers (e : CoreId) {st st' : SystemState}
    {callerVtid receiverVtid : SeLe4n.ValidThreadId} {donorHome doneeHome : CoreId}
    (hInv : st.objects.invExt)
    (h : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  refine ⟨?_, applyCallDonationOnCore_preserves_objects_invExt _ _ _ _ _ _ hInv h⟩
  obtain ⟨st1, hDon, hArm⟩ := applyCallDonationOnCore_ok_decompose _ _ _ _ _ _ h
  have h1 := (applyCallDonation_stepCovers e hInv hDon).1
  rcases hArm with ⟨_, rfl⟩ | ⟨scId, _, rfl⟩
  · exact h1
  · exact stepCovers_trans h1 (migrateSchedContextReplenishment_stepCovers e _ _ _ _)

/-- The receive rendezvous' hand-off covers: the lend, then the chain walk. -/
theorem applyReceiveRendezvousHandoff_stepCovers (e : CoreId) {st st' : SystemState}
    {receiver dequeued : SeLe4n.ThreadId} {executingCore : CoreId} (hInv : st.objects.invExt)
    (h : applyReceiveRendezvousHandoff st receiver dequeued executingCore = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  obtain ⟨stDon, hDon, rfl⟩ := applyReceiveRendezvousHandoff_ok_decompose _ _ _ _ _ h
  have hD : stepCovers e st stDon ∧ stDon.objects.invExt := by
    unfold applyReceiveRendezvousDonation at hDon
    split at hDon
    · unfold applyRendezvousCallDonation at hDon
      split at hDon
      · exact applyCallDonationOnCore_stepCovers e hInv hDon
      · cases hDon
    · cases hDon; exact ⟨stepCovers_refl e st, hInv⟩
  split
  · obtain ⟨hW, hWInv⟩ := propagatePipChainCrossCore_stepCovers e executingCore _ stDon receiver hD.2
    exact ⟨stepCovers_trans hD.1 hW, hWInv⟩
  · exact hD

/-! ### Return-frame staging -/

theorem stageDeliveredMessage_keyFrame (st : SystemState) (tid : SeLe4n.ThreadId) (n : Nat)
    (hInv : st.objects.invExt) :
    capabilityKeyFrame st (Architecture.stageDeliveredMessage st tid n) := by
  have hRefl := capabilityKeyFrame_of_objects_scheduler_eq hInv rfl rfl
  unfold Architecture.stageDeliveredMessage
  split
  · split
    · split
      · exact (writeReturnFrameToTcb_keyFrame st tid _ hInv).trans
          (recordPhysicalWrites_keyFrame (writeReturnFrameToTcb_keyFrame st tid _ hInv).2.2 _)
      · exact hRefl
    · exact hRefl
  · exact hRefl

theorem stageWokenDelivery_keyFrame (st : SystemState) (woken? : Option SeLe4n.ThreadId)
    (n : Nat) (hInv : st.objects.invExt) :
    capabilityKeyFrame st (Architecture.stageWokenDelivery st woken? n) := by
  unfold Architecture.stageWokenDelivery
  split
  · exact stageDeliveredMessage_keyFrame st _ n hInv
  · exact capabilityKeyFrame_of_objects_scheduler_eq hInv rfl rfl

theorem stageWokenSendCompletion_keyFrame (st : SystemState) (woken? : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    capabilityKeyFrame st (Architecture.stageWokenSendCompletion st woken?) := by
  have hRefl := capabilityKeyFrame_of_objects_scheduler_eq hInv rfl rfl
  unfold Architecture.stageWokenSendCompletion
  split
  · exact hRefl
  · split
    · split
      · exact writeReturnFrameToTcb_keyFrame st _ _ hInv
      · exact hRefl
    · exact hRefl

/-! ### Call -/

theorem linkServerStashedReply_keyFrame {caller server : SeLe4n.ThreadId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  unfold SystemState.linkServerStashedReply at h
  split at h
  · cases h
  · rename_i rid _
    cases hL : SystemState.linkCallerReply caller rid st with
    | error _ => simp [hL] at h
    | ok p1 =>
      obtain ⟨⟨⟩, st1⟩ := p1
      simp only [hL] at h
      have hF1 := linkCallerReply_keyFrame hInv hL
      split at h
      · cases h; exact hF1
      · rename_i sTcb hT
        exact hF1.trans (storeObject_tcbKeyKeeping_keyFrame hF1.2.2
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) h rfl)

/-- The per-core call covers on every outcome. -/
theorem endpointCallOnCore_stepCovers (e : CoreId) {endpointId : SeLe4n.ObjId}
    {caller : SeLe4n.ThreadId} {msg : IpcMessage} {executingCore : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (endpointCallOnCore endpointId caller msg executingCore st).1 ∧
      (endpointCallOnCore endpointId caller msg executingCore st).1.objects.invExt := by
  have hRefl : stepCovers e st st ∧ st.objects.invExt := ⟨stepCovers_refl e st, hInv⟩
  unfold endpointCallOnCore
  split
  · exact hRefl
  split
  · exact hRefl
  split
  · split
    · split
      · exact hRefl
      · rename_i receiver _tcb st1 hPop
        have hF1 := endpointQueuePopHead_keyFrame hInv hPop
        split
        · exact hRefl
        · rename_i st2 hRdy
          have hF2 := hF1.trans (storeTcbIpcStateAndMessage_keyFrame hF1.2.2 hRdy)
          obtain ⟨hW, hWInv⟩ := wakeThread_stepCovers e st2 receiver executingCore hF2.2.2
          split
          · exact hRefl
          · rename_i st4 hBlk
            have hF4 := storeTcbIpcStateAndMessage_keyFrame hWInv hBlk
            split
            · exact hRefl
            · rename_i st5 hLink
              have hF5 := hF4.trans (linkServerStashedReply_keyFrame hF4.2.2 hLink)
              exact ⟨stepCovers_trans (stepCovers_trans (stepCovers_trans hF2.stepCovers hW)
                hF5.stepCovers) (removeRunnableOnCore_stepCovers e _ _ _), hF5.2.2⟩
    · split
      · exact hRefl
      · rename_i st1 hEnq
        have hF1 := endpointQueueEnqueue_keyFrame hInv hEnq
        split
        · exact hRefl
        · rename_i st2 hBlk
          have hF2 := hF1.trans (storeTcbIpcStateAndMessage_keyFrame hF1.2.2 hBlk)
          exact ⟨stepCovers_trans hF2.stepCovers (removeRunnableOnCore_stepCovers e _ _ _),
            hF2.2.2⟩
  · split <;> exact hRefl

theorem endpointCallWithCapsOnCore_stepCovers (e : CoreId) {endpointId : SeLe4n.ObjId}
    {caller : SeLe4n.ThreadId} {msg : IpcMessage} {endpointRights : AccessRightSet}
    {receiverSlotBase : SeLe4n.Slot} {executingCore : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st).1 ∧
    (endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st).1.objects.invExt := by
  unfold endpointCallWithCapsOnCore
  obtain ⟨hC, hCInv⟩ := endpointCallOnCore_stepCovers e
    (endpointId := endpointId) (caller := caller)
    (msg := { msg with capsGranted := endpointRights.mem .grant })
    (executingCore := executingCore) hInv
  generalize endpointCallOnCore endpointId caller
    { msg with capsGranted := endpointRights.mem .grant } executingCore st = r at hC hCInv
  obtain ⟨st1, res⟩ := r
  dsimp only at hC hCInv ⊢
  cases res with
  | error _ => exact ⟨hC, hCInv⟩
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact ⟨hC, hCInv⟩
      | (rename_i hU
         have hF := ipcUnwrapCaps_keyFrame hCInv hU
         exact ⟨stepCovers_trans hC hF.stepCovers, hF.2.2⟩)

/-- The live call covers: the rendezvous, the lend to a passive receiver, and
the chain walk from it. -/
theorem endpointCallCrossCoreDispatch_stepCovers (e : CoreId) {endpointId : SeLe4n.ObjId}
    {caller : SeLe4n.ThreadId} {msg : IpcMessage} {endpointRights : AccessRightSet}
    {receiverSlotBase : SeLe4n.Slot} {executingCore : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (endpointCallCrossCoreDispatch endpointId caller msg endpointRights
      receiverSlotBase executingCore st).1 ∧
    (endpointCallCrossCoreDispatch endpointId caller msg endpointRights
      receiverSlotBase executingCore st).1.objects.invExt := by
  unfold endpointCallCrossCoreDispatch
  obtain ⟨hC, hCInv⟩ := endpointCallWithCapsOnCore_stepCovers e
    (endpointId := endpointId) (caller := caller) (msg := msg)
    (endpointRights := endpointRights) (receiverSlotBase := receiverSlotBase)
    (executingCore := executingCore) hInv
  generalize endpointCallWithCapsOnCore endpointId caller msg endpointRights
    receiverSlotBase executingCore st = r at hC hCInv
  obtain ⟨st1, res⟩ := r
  dsimp only at hC hCInv ⊢
  cases res with
  | error _ => exact ⟨hC, hCInv⟩
  | ok p =>
    obtain ⟨summary, sgi⟩ := p
    dsimp only
    repeat' split
    all_goals first
      | exact ⟨hC, hCInv⟩
      | (rename_i hD
         obtain ⟨hDc, hDInv⟩ := applyCallDonationOnCore_stepCovers e hCInv hD
         exact (propagatePipChainCrossCore_stepCovers e executingCore _ _ _ hDInv).imp_left
           (stepCovers_trans (stepCovers_trans hC hDc)))

theorem endpointCallCrossCoreDispatchChecked_stepCovers (e : CoreId) {ctx : LabelingContext}
    {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId} {msg : IpcMessage}
    {endpointRights : AccessRightSet} {receiverSlotBase : SeLe4n.Slot} {executingCore : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    stepCovers e st (endpointCallCrossCoreDispatchChecked ctx endpointId caller msg
      endpointRights receiverSlotBase executingCore st).1 ∧
    (endpointCallCrossCoreDispatchChecked ctx endpointId caller msg
      endpointRights receiverSlotBase executingCore st).1.objects.invExt := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · exact endpointCallCrossCoreDispatch_stepCovers e hInv
  · exact ⟨stepCovers_refl e st, hInv⟩

/-! ### Reply -/

/-- A TCB rewrite that keeps the key fields, in its total form. -/
theorem updateTcb_keyFrame (st : SystemState) (tid : SeLe4n.ThreadId) {f : TCB → TCB}
    (hF : ∀ t, tcbKeyFields (f t) = tcbKeyFields t) (hInv : st.objects.invExt) :
    capabilityKeyFrame st (st.updateTcb tid f) :=
  ⟨keyInputsEq_updateTcb hInv hF, SystemState.updateTcb_scheduler _ _ _,
   SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv⟩

theorem spliceReplyFrameOutOrSelf_keyFrame (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) : capabilityKeyFrame st (spliceReplyFrameOutOrSelf st rid) := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]; exact capabilityKeyFrame_of_objects_scheduler_eq hInv rfl rfl
  · exact ⟨keyInputsEq_of_lookups_eq (spliceReplyFrameOut_getTcb?_eq hInv h)
      (spliceReplyFrameOutOrSelf_getSchedContext?_eq st rid hInv),
      spliceReplyFrameOutOrSelf_scheduler_eq st rid,
      spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hInv⟩

theorem consumeCallerReply_keyFrame {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    capabilityKeyFrame st st' :=
  ⟨consumeCallerReply_keyInputsEq hInv h, SystemState.consumeCallerReply_scheduler_eq _ _ _ _ h,
   SystemState.consumeCallerReply_preserves_objects_invExt _ _ _ _ hInv h⟩

theorem removeCallerReplyFrame_keyFrame {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : removeCallerReplyFrame caller rid st = .ok ((), st')) : capabilityKeyFrame st st' := by
  unfold removeCallerReplyFrame at h
  have h1 := spliceReplyFrameOutOrSelf_keyFrame st rid hInv
  exact h1.trans (consumeCallerReply_keyFrame h1.2.2 h)

/-- The per-core reply covers on every outcome: the caller's TCB store keeps its
key, the wake flags the core it inserts on, and the frame removal is object-only. -/
theorem endpointReplyOnCore_stepCovers (e : CoreId) {replier target : SeLe4n.ThreadId}
    {msg : IpcMessage} {executingCore : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    stepCovers e st (endpointReplyOnCore replier target msg executingCore st).1 ∧
      (endpointReplyOnCore replier target msg executingCore st).1.objects.invExt := by
  have hRefl : stepCovers e st st ∧ st.objects.invExt := ⟨stepCovers_refl e st, hInv⟩
  unfold endpointReplyOnCore
  split
  · exact hRefl
  split
  · exact hRefl
  split
  · exact hRefl
  · rename_i tcb hL
    split
    · split
      · exact hRefl
      · split
        · exact hRefl
        · rename_i st1 hS
          unfold storeTcbIpcStateAndMessage_fromTcb at hS
          have hF1 : capabilityKeyFrame st st1 := by
            revert hS
            cases hSt : storeObject target.toObjId _ st with
            | error _ => intro h; cases h
            | ok p =>
              obtain ⟨⟨⟩, s⟩ := p
              intro h; cases h
              exact storeObject_tcbKeyKeeping_keyFrame hInv (lookupTcb_some_objects _ _ _ hL) hSt rfl
          obtain ⟨hW, hWInv⟩ := wakeThread_stepCovers e st1 target executingCore hF1.2.2
          have hPre := stepCovers_trans hF1.stepCovers hW
          split
          · exact ⟨hPre, hWInv⟩
          · split
            · rename_i st2 hR
              have hF2 := removeCallerReplyFrame_keyFrame hWInv hR
              exact ⟨stepCovers_trans hPre hF2.stepCovers, hF2.2.2⟩
            · exact hRefl
    · exact hRefl

/-- The reply's donation return covers: the resolved return, the replenishment
migration, and the holder's deschedule. -/
theorem applyReplyDonationOnCore_stepCovers (e : CoreId) {st st' : SystemState}
    {rid : SeLe4n.ReplyId} {targetVtid : SeLe4n.ValidThreadId} {holderHome ownerHome : CoreId}
    (hInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold applyReplyDonationOnCore at h
  dsimp only at h
  split at h
  · cases h; exact ⟨stepCovers_refl e st, hInv⟩
  · split at h
    · split at h
      · cases h
      · rename_i st1 hRet
        cases h
        obtain ⟨h1, h1Inv⟩ := returnDonatedSchedContextResolved_stepCovers e hInv hRet
        refine ⟨stepCovers_trans (stepCovers_trans h1
          (migrateSchedContextReplenishment_stepCovers e _ _ _ _))
          (descheduleAt_stepCovers e _ _ _), ?_⟩
        unfold descheduleAtPlacement
        rw [descheduleAt_objects, migrateSchedContextReplenishment_objects]
        exact h1Inv
    · cases h

/-- The live reply covers on every outcome: the reply leg, the donation
return, and the chain walk from the recorded server. -/
theorem endpointReplyCrossCoreDispatch_stepCovers (e : CoreId) {replier target : SeLe4n.ThreadId}
    {msg : IpcMessage} {executingCore : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    stepCovers e st (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 ∧
      (endpointReplyCrossCoreDispatch replier target msg executingCore st).1.objects.invExt := by
  have hRefl : stepCovers e st st ∧ st.objects.invExt := ⟨stepCovers_refl e st, hInv⟩
  unfold endpointReplyCrossCoreDispatch
  obtain ⟨hR, hRInv⟩ := endpointReplyOnCore_stepCovers e (replier := replier) (target := target)
    (msg := msg) (executingCore := executingCore) hInv
  generalize endpointReplyOnCore replier target msg executingCore st = r at hR hRInv
  obtain ⟨st1, res⟩ := r
  dsimp only at hR hRInv ⊢
  cases res with
  | error _ => exact hRefl
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact hRefl
      | exact propagatePipChainCrossCore_stepCovers e executingCore _ _ _ hRInv |>.imp_left
          (stepCovers_trans hR)
      | (rename_i hD
         obtain ⟨hDc, hDInv⟩ := applyReplyDonationOnCore_stepCovers e hRInv hD
         exact (propagatePipChainCrossCore_stepCovers e executingCore _ _ _ hDInv).imp_left
           (stepCovers_trans (stepCovers_trans hR hDc)))

theorem endpointReplyCrossCoreDispatchChecked_stepCovers (e : CoreId) {ctx : LabelingContext}
    {replier target : SeLe4n.ThreadId} {msg : IpcMessage} {executingCore : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    stepCovers e st (endpointReplyCrossCoreDispatchChecked ctx replier target msg
      executingCore st).1 ∧
    (endpointReplyCrossCoreDispatchChecked ctx replier target msg executingCore st).1.objects.invExt := by
  unfold endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch_stepCovers e hInv
  · exact ⟨stepCovers_refl e st, hInv⟩

/-- The fault reply covers: the reply chain, then the restart frame or the
abandon's deschedule. -/
theorem faultReplyOnCore_stepCovers (e : CoreId) {replier faulted : SeLe4n.ThreadId}
    {mi : MessageInfo} {regs : Array SeLe4n.RegValue} {executingCore : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    stepCovers e st (faultReplyOnCore replier faulted mi regs executingCore st).1 := by
  unfold faultReplyOnCore
  split
  · exact stepCovers_refl e st
  split
  · exact stepCovers_refl e st
  dsimp only
  obtain ⟨hR, hRInv⟩ := endpointReplyCrossCoreDispatch_stepCovers e (replier := replier)
    (target := faulted) (msg := IpcMessage.empty) (executingCore := executingCore) hInv
  generalize endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty executingCore st = r
    at hR hRInv
  obtain ⟨st1, res⟩ := r
  dsimp only at hR hRInv ⊢
  cases res with
  | error _ => exact stepCovers_refl e st
  | ok sgi =>
    dsimp only
    refine stepCovers_trans hR ?_
    unfold faultReplyApplyOnCore
    split
    · unfold applyFaultRestart
      apply capabilityKeyFrame.stepCovers
      exact updateTcb_keyFrame st1 faulted (fun _ => rfl) hRInv
    · unfold faultAbandonOnCore
      refine stepCovers_trans
        (removeRunnableOnCore_stepCovers e st1 faulted (determineTargetCore st1 faulted)) ?_
      apply capabilityKeyFrame.stepCovers
      exact updateTcb_keyFrame _ faulted (fun _ => rfl) (by
        exact hRInv)

/-- The checked reply transfer covers on its `.ok`. -/
theorem replyTransferOnCoreChecked_stepCovers (e : CoreId) {ctx : LabelingContext}
    {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo} {regs : Array SeLe4n.RegValue}
    {msg : IpcMessage} {executingCore : CoreId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg executingCore st
      = .ok ((), st')) :
    stepCovers e st st' := by
  unfold replyTransferOnCoreChecked at h
  split at h
  · have hF := faultReplyOnCore_stepCovers e (replier := replier) (faulted := callerTid)
      (mi := mi) (regs := regs) (executingCore := executingCore) hInv
    revert h hF
    generalize faultReplyOnCore replier callerTid mi regs executingCore st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h; cases h
    | ok _ => intro h hF; cases h; exact hF
  · obtain ⟨hR, hRInv⟩ := endpointReplyCrossCoreDispatchChecked_stepCovers e (ctx := ctx)
      (replier := replier) (target := callerTid) (msg := msg) (executingCore := executingCore) hInv
    revert h hR hRInv
    generalize endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg executingCore st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h; cases h
    | ok _ =>
      intro h hR hRInv
      cases h
      exact stepCovers_trans hR (stageDeliveredMessage_keyFrame s callerTid 0 hRInv).stepCovers

/-! ### Notifications -/

theorem capabilityKeyFrame_refl {st : SystemState} (hInv : st.objects.invExt) :
    capabilityKeyFrame st st :=
  capabilityKeyFrame_of_objects_scheduler_eq hInv rfl rfl

/-- An endpoint store over a slot that held an endpoint at the start. -/
theorem keyFrame_storeObject_endpoint {st s : SystemState} {oid : SeLe4n.ObjId}
    {ep ep' : Endpoint} {pair : Unit × SystemState}
    (hObj : st.objects[oid]? = some (.endpoint ep)) (hF : capabilityKeyFrame st s)
    (h : storeObject oid (.endpoint ep') s = .ok pair) : capabilityKeyFrame st pair.2 := by
  obtain ⟨⟨⟩, s'⟩ := pair
  exact hF.trans (storeObject_inert_keyFrame hF.2.2 h (by rw [hF.1 oid, hObj]; rfl) rfl)

/-- Removing a thread from an endpoint queue rewrites the endpoint and queue
links only. -/
theorem endpointQueueRemoveDual_keyFrame {st st' : SystemState} {endpointId : SeLe4n.ObjId}
    {isReceiveQ : Bool} {tid : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  have epStore := @keyFrame_storeObject_endpoint
  unfold endpointQueueRemoveDual dualQueueRemovalEnabled dualQueueRemovalGuard SystemState.getObject? at hStep; revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp
    | endpoint ep =>
      simp only []
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcb =>
        simp only []
        cases hPPrev : tcb.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          generalize (if isReceiveQ then ep.receiveQ else ep.sendQ) = q
          -- `v0.35.59`: `cases pprev` precedes the `split`.  With the two
          -- preconditions collapsed into `dualQueueRemovalEnabled`, unfolding the
          -- guard exposes the guard's own `match pprev` *inside* the `if`
          -- condition, and `split` takes that before the `if` -- so the
          -- constructor split has to come first.
          cases pprev with
            | endpointHead =>
              simp only []
              split
              · simp
              · cases hStore1 : storeObject endpointId _ st with
                | error e => simp
                | ok pair1 =>
                simp only []; cases hNext : tcb.queueNext with
                | none =>
                  simp only []
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have f1 := epStore hObj (capabilityKeyFrame_refl hInv) hStore1
                    have f2 := epStore hObj f1 hStore2
                    exact f2.trans (storeTcbQueueLinks_keyFrame f2.2.2 hFinal)
                | some nextTid =>
                  simp only []
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only []; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only []; cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have f1 := epStore hObj (capabilityKeyFrame_refl hInv) hStore1
                    have f2 := f1.trans (storeTcbQueueLinks_keyFrame f1.2.2 hLink)
                    have f3 := epStore hObj f2 hStore2
                    exact f3.trans (storeTcbQueueLinks_keyFrame f3.2.2 hFinal)
            | tcbNext prevTid =>
              dsimp only
              split
              · simp
              · cases hLookupP : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                dsimp only [hLookupP]; split
                · simp
                · -- split introduced heq✝ : (if ... then .error else match storeTcbQueueLinks ... with ...) = .ok st''✝
                  -- and the goal uses st''✝. Resolve heq✝ to extract the actual state.
                  rename_i _ _ stAp heqAp
                  split at heqAp
                  · simp at heqAp
                  · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcb.queueNext with
                    | error e => simp [hLink0] at heqAp
                    | ok stPrev =>
                    simp [hLink0] at heqAp; subst heqAp
                    -- Now stAp = stPrev, goal uses stPrev
                    cases hNext : tcb.queueNext with
                    | none =>
                      dsimp only [hNext]
                      cases hStore2 : storeObject endpointId _ stPrev with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have f1 := storeTcbQueueLinks_keyFrame hInv hLink0
                        have f2 := epStore hObj f1 hStore2
                        exact f2.trans (storeTcbQueueLinks_keyFrame f2.2.2 hFinal)
                    | some nextTid =>
                      dsimp only [hNext]
                      cases hLookupN : lookupTcb stPrev nextTid with
                      | none => simp
                      | some nextTcb =>
                      dsimp only [hLookupN]; cases hLink1 : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      dsimp only [hLink1]; cases hStore2 : storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have f1 := storeTcbQueueLinks_keyFrame hInv hLink0
                        have f2 := f1.trans (storeTcbQueueLinks_keyFrame f1.2.2 hLink1)
                        have f3 := epStore hObj f2 hStore2
                        exact f3.trans (storeTcbQueueLinks_keyFrame f3.2.2 hFinal)



/-- A store over a slot that fed no key at the start, of an object that feeds
none, after a key-preserving prefix. -/
theorem keyFrame_storeObject_inert_after {st s : SystemState} {oid : SeLe4n.ObjId}
    {obj : KernelObject} {pair : Unit × SystemState}
    (hPre : keyInputsOf st.objects[oid]? = none) (hObj : keyInputsOf (some obj) = none)
    (hF : capabilityKeyFrame st s) (h : storeObject oid obj s = .ok pair) :
    capabilityKeyFrame st pair.2 := by
  obtain ⟨⟨⟩, s'⟩ := pair
  exact hF.trans (storeObject_inert_keyFrame hF.2.2 h (by rw [hF.1 oid]; exact hPre) hObj)

/-- A TCB store keeping the key fields of the TCB the slot held at the start,
after a key-preserving prefix. -/
theorem keyFrame_storeObject_tcbKeeping_after {st s : SystemState} {tid : SeLe4n.ThreadId}
    {t t' : TCB} {pair : Unit × SystemState}
    (hPre : st.objects[tid.toObjId]? = some (.tcb t)) (hKey : tcbKeyFields t' = tcbKeyFields t)
    (hF : capabilityKeyFrame st s) (h : storeObject tid.toObjId (.tcb t') s = .ok pair) :
    capabilityKeyFrame st pair.2 := by
  obtain ⟨⟨⟩, s'⟩ := pair
  refine hF.trans ⟨keyInputsEq_storeObject hF.2.2 h ?_, storeObject_scheduler_eq _ _ _ _ h,
    storeObject_preserves_objects_invExt _ _ _ _ hF.2.2 h⟩
  rw [hF.1 tid.toObjId, hPre]
  simp only [tcbKeyFields, Prod.mk.injEq] at hKey
  simp only [keyInputsOf, hKey]

theorem storeTcbIpcState_keyFrame {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {ipc : ThreadIpcState} (hInv : st.objects.invExt)
    (h : storeTcbIpcState st tid ipc = .ok st') : capabilityKeyFrame st st' := by
  unfold storeTcbIpcState at h
  exact modifyTcb_keyFrame (f := fun tcb => { tcb with ipcState := ipc }) (fun _ => rfl) hInv h

/-- The per-core signal covers on every outcome. -/
theorem notificationSignalOnCore_stepCovers (e : CoreId) {notificationId : SeLe4n.ObjId}
    {badge : SeLe4n.Badge} {executingCore : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (notificationSignalOnCore notificationId badge executingCore st).1 ∧
      (notificationSignalOnCore notificationId badge executingCore st).1.objects.invExt := by
  have hRefl : stepCovers e st st ∧ st.objects.invExt := ⟨stepCovers_refl e st, hInv⟩
  unfold notificationSignalOnCore
  split
  · rename_i ntfn hN
    have hPre : keyInputsOf st.objects[notificationId]? = none := by
      rw [(SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hN]; rfl
    split
    · dsimp only
      cases hS : storeObject notificationId _ st with
      | error _ => exact hRefl
      | ok p =>
        obtain ⟨⟨⟩, st1⟩ := p
        have hF1 := keyFrame_storeObject_inert_after (pair := ((), st1)) hPre rfl
          (capabilityKeyFrame_refl hInv) hS
        dsimp only
        split
        · exact hRefl
        · rename_i st2 hT
          have hF2 := hF1.trans (storeTcbIpcStateAndMessage_keyFrame hF1.2.2 hT)
          exact (wakeThread_stepCovers e st2 _ executingCore hF2.2.2).imp_left
            (stepCovers_trans hF2.stepCovers)
    · dsimp only
      cases hS : storeObject notificationId _ st with
      | error _ => exact hRefl
      | ok p =>
        obtain ⟨⟨⟩, st1⟩ := p
        have hF1 := keyFrame_storeObject_inert_after (pair := ((), st1)) hPre rfl
          (capabilityKeyFrame_refl hInv) hS
        exact ⟨hF1.stepCovers, hF1.2.2⟩
  · split <;> exact hRefl

theorem notificationSignalBoundOnCore_stepCovers (e : CoreId) {notificationId : SeLe4n.ObjId}
    {badge : SeLe4n.Badge} {executingCore : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (notificationSignalBoundOnCore notificationId badge executingCore st).1 ∧
      (notificationSignalBoundOnCore notificationId badge executingCore st).1.objects.invExt := by
  unfold notificationSignalBoundOnCore
  split
  · dsimp only
    split
    · exact ⟨stepCovers_refl e st, hInv⟩
    · rename_i st1 hR
      have hF1 := endpointQueueRemoveDual_keyFrame hInv hR
      split
      · exact ⟨stepCovers_refl e st, hInv⟩
      · rename_i st2 hT
        have hF2 := hF1.trans (storeTcbReceiveComplete_keyFrame hF1.2.2 hT)
        exact (wakeThread_stepCovers e st2 _ executingCore hF2.2.2).imp_left
          (stepCovers_trans hF2.stepCovers)
  · exact notificationSignalOnCore_stepCovers e hInv

theorem notificationSignalBoundCrossCoreDispatchChecked_stepCovers (e : CoreId)
    {ctx : LabelingContext} {notificationId : SeLe4n.ObjId} {signaler : SeLe4n.ThreadId}
    {badge : SeLe4n.Badge} {executingCore : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler
      badge executingCore st).1 ∧
    (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler
      badge executingCore st).1.objects.invExt := by
  unfold notificationSignalBoundCrossCoreDispatchChecked
  repeat' split
  all_goals first
    | exact notificationSignalBoundOnCore_stepCovers e hInv
    | exact ⟨stepCovers_refl e st, hInv⟩

/-- The per-core wait covers on every outcome: consuming a badge keeps the
waiter runnable, and blocking takes it off the executing core. -/
theorem notificationWaitOnCore_stepCovers (e : CoreId) {notificationId : SeLe4n.ObjId}
    {waiter : SeLe4n.ThreadId} {executingCore : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (notificationWaitOnCore notificationId waiter executingCore st).1 ∧
      (notificationWaitOnCore notificationId waiter executingCore st).1.objects.invExt := by
  have hRefl : stepCovers e st st ∧ st.objects.invExt := ⟨stepCovers_refl e st, hInv⟩
  unfold notificationWaitOnCore
  split
  · rename_i ntfn hN
    have hPre : keyInputsOf st.objects[notificationId]? = none := by
      rw [(SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hN]; rfl
    split
    · dsimp only
      split
      · exact hRefl
      · rename_i st1 hS
        have hF1 := keyFrame_storeObject_inert_after (pair := ((), st1)) hPre rfl
          (capabilityKeyFrame_refl hInv) hS
        split
        · exact hRefl
        · rename_i st2 hT
          have hF2 := hF1.trans (storeTcbIpcState_keyFrame hF1.2.2 hT)
          exact ⟨hF2.stepCovers, hF2.2.2⟩
    · split
      · exact hRefl
      · rename_i tcb hL
        split
        · exact hRefl
        · split
          · exact hRefl
          · dsimp only
            split
            · exact hRefl
            · rename_i st1 hS
              have hF1 := keyFrame_storeObject_inert_after (pair := ((), st1)) hPre rfl
                (capabilityKeyFrame_refl hInv) hS
              split
              · exact hRefl
              · rename_i st2 hT
                unfold storeTcbIpcStateAndMessage_fromTcb at hT
                have hF2 : capabilityKeyFrame st st2 := by
                  revert hT
                  cases hSt : storeObject waiter.toObjId _ st1 with
                  | error _ => intro h; cases h
                  | ok p =>
                    obtain ⟨⟨⟩, s⟩ := p
                    intro h; cases h
                    exact keyFrame_storeObject_tcbKeeping_after (pair := ((), _))
                      (lookupTcb_some_objects _ _ _ hL) (by rfl) hF1 hSt
                exact ⟨stepCovers_trans hF2.stepCovers (removeRunnableOnCore_stepCovers e _ _ _),
                  hF2.2.2⟩
  · split <;> exact hRefl

theorem notificationWaitCrossCoreDispatchChecked_stepCovers (e : CoreId) {ctx : LabelingContext}
    {notificationId : SeLe4n.ObjId} {waiter : SeLe4n.ThreadId} {executingCore : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    stepCovers e st (notificationWaitCrossCoreDispatchChecked ctx notificationId waiter
      executingCore st).1 ∧
    (notificationWaitCrossCoreDispatchChecked ctx notificationId waiter
      executingCore st).1.objects.invExt := by
  unfold notificationWaitCrossCoreDispatchChecked
  split
  · exact notificationWaitOnCore_stepCovers e hInv
  · exact ⟨stepCovers_refl e st, hInv⟩

/-! ### ReplyRecv -/

theorem applyRendezvousCallDonation_stepCovers (e : CoreId) {st st' : SystemState}
    {receiver donor : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : applyRendezvousCallDonation st receiver donor = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold applyRendezvousCallDonation at h
  split at h
  · exact applyCallDonationOnCore_stepCovers e hInv h
  · cases h

theorem descheduleAtPlacement_stepCovers (e : CoreId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    stepCovers e st (descheduleAtPlacement st tid) ∧ (descheduleAtPlacement st tid).objects.invExt :=
  ⟨descheduleAt_stepCovers e _ _ _, by unfold descheduleAtPlacement; rw [descheduleAt_objects]; exact hInv⟩

theorem replyRecvPopDonation_stepCovers (e : CoreId) {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} {st st' : SystemState}
    {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} (hInv : st.objects.invExt)
    (h : replyRecvPopDonation rid target st = .ok (r, st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold replyRecvPopDonation at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · cases h
      · rename_i st1 hRet
        cases h
        obtain ⟨h1, h1Inv⟩ := returnDonatedSchedContextResolved_stepCovers e hInv hRet
        exact ⟨stepCovers_trans h1 (migrateSchedContextReplenishment_stepCovers e _ _ _ _),
          by rw [migrateSchedContextReplenishment_objects]; exact h1Inv⟩
    · cases h
  · cases h; exact ⟨stepCovers_refl e st, hInv⟩

theorem replyRecvPostReceiveDonation_stepCovers (e : CoreId)
    {tid recordedServer nextThread : SeLe4n.ThreadId} {serverCore : CoreId}
    {returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
      = .ok ((), st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold replyRecvPostReceiveDonation at h
  split at h
  · cases h
    exact propagatePipChainCrossCore_stepCovers e serverCore _ st recordedServer hInv
  · rename_i holder
    split at h
    · split at h
      · cases h
      · rename_i st2 hD
        cases h
        have hH : stepCovers e st (replyRecvHolderDeschedule tid holder st) ∧
            (replyRecvHolderDeschedule tid holder st).objects.invExt := by
          unfold replyRecvHolderDeschedule
          split
          · exact ⟨stepCovers_refl e st, hInv⟩
          · exact descheduleAtPlacement_stepCovers e st holder hInv
        obtain ⟨hDc, hDInv⟩ := applyRendezvousCallDonation_stepCovers e hH.2 hD
        exact (propagatePipChainCrossCore_stepCovers e serverCore _ st2 recordedServer hDInv).imp_left
          (stepCovers_trans (stepCovers_trans hH.1 hDc))
    · cases h
      obtain ⟨hP, hPInv⟩ := descheduleAtPlacement_stepCovers e st holder hInv
      exact (propagatePipChainCrossCore_stepCovers e serverCore _ _ recordedServer hPInv).imp_left
        (stepCovers_trans hP)

theorem applyReceiveLegPipHandoff_stepCovers (e : CoreId) (st : SystemState)
    (receiver dequeued alreadyWalked : SeLe4n.ThreadId) (executingCore : CoreId)
    (hInv : st.objects.invExt) :
    stepCovers e st (applyReceiveLegPipHandoff st receiver dequeued alreadyWalked executingCore) ∧
      (applyReceiveLegPipHandoff st receiver dequeued alreadyWalked executingCore).objects.invExt := by
  unfold applyReceiveLegPipHandoff
  split
  · exact ⟨stepCovers_refl e st, hInv⟩
  split
  · exact propagatePipChainCrossCore_stepCovers e executingCore _ st receiver hInv
  · exact ⟨stepCovers_refl e st, hInv⟩

/-- The per-core reply-and-receive covers on its `.ok`: the reply leg, the
donation pop, the receive leg, the post-receive donation, the chain walk and the
staging. -/
theorem endpointReplyRecvOnCore_stepCovers (e : CoreId) {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId}
    {msg : IpcMessage} {receiverCspaceRoot : SeLe4n.ObjId} {receiverSlotBase : SeLe4n.Slot}
    {executingCore : CoreId} {st st' : SystemState} {summary : CapTransferSummary}
    (hInv : st.objects.invExt)
    (h : endpointReplyRecvOnCore epId tid rid prevCaller msg receiverCspaceRoot receiverSlotBase
      executingCore st = .ok (summary, st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold endpointReplyRecvOnCore at h
  dsimp only at h
  obtain ⟨hR, hRInv⟩ := endpointReplyOnCore_stepCovers e (replier := tid) (target := prevCaller)
    (msg := msg) (executingCore := executingCore) hInv
  revert h hR hRInv
  generalize endpointReplyOnCore tid prevCaller msg executingCore st = r1
  obtain ⟨st1, res1⟩ := r1
  cases res1 with
  | error _ => intro h; cases h
  | ok _ =>
  intro h hR hRInv
  dsimp only at h hR hRInv
  split at h
  · cases h
  rename_i ret st1p hPop
  obtain ⟨hP, hPInv⟩ := replyRecvPopDonation_stepCovers e hRInv hPop
  obtain ⟨hV, hVInv⟩ := endpointReceiveDualWithCapsOnCore_stepCovers e (endpointId := epId)
    (receiver := tid) (replyId := some rid) (receiverCspaceRoot := receiverCspaceRoot)
    (receiverSlotBase := receiverSlotBase) (executingCore := executingCore) hPInv
  revert h hV hVInv
  generalize endpointReceiveDualWithCapsOnCore epId tid (some rid) receiverCspaceRoot
    receiverSlotBase executingCore st1p = r2
  obtain ⟨st2, res2⟩ := r2
  cases res2 with
  | error _ => intro h; cases h
  | ok q =>
  obtain ⟨nextThread, summ, _⟩ := q
  intro h hV hVInv
  dsimp only at h hV hVInv
  split at h
  · cases h
  rename_i st3 hPost
  cases h
  obtain ⟨hD, hDInv⟩ := replyRecvPostReceiveDonation_stepCovers e hVInv hPost
  obtain ⟨hW, hWInv⟩ := applyReceiveLegPipHandoff_stepCovers e st3 tid nextThread
    ((recordedReplyServer? st prevCaller).getD tid) executingCore hDInv
  have hS1 := stageDeliveredMessage_keyFrame _ prevCaller 0 hWInv
  have hS2 := stageWokenSendCompletion_keyFrame _ ((st1p.getEndpoint? epId).bind (·.sendQ.head))
    hS1.2.2
  exact ⟨stepCovers_trans (stepCovers_trans (stepCovers_trans (stepCovers_trans
    (stepCovers_trans (stepCovers_trans hR hP) hV) hD) hW) hS1.stepCovers) hS2.stepCovers,
    hS2.2.2⟩

end SeLe4n.Kernel
