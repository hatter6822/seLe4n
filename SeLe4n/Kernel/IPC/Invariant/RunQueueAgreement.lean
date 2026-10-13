/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.CrossCore.Fault

/-!
# IPC steps keep the run-queue link agreement

WS-ZA ZA4.5 part 2.  Every core's run queue is read through the threads' TCB
run-queue links, and `SystemState.runQueueRefined` says the links agree with the
abstract queue.  This module proves the agreement is a stage
(`SystemState.RunQueueStage`) of every IPC step: the object writes that leave
every TCB's run-queue fields alone, and the scheduler writes that move a thread
on or off a queue through the link-writing primitives.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)

/-- A TCB write through `modifyTcb` that keeps the run-queue fields. -/
theorem modifyTcb_runQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {f : TCB → TCB} (h : modifyTcb st tid f = .ok st')
    (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c) : RunQueueStage st st' := by
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  exact RunQueueStage.storeObject_tcb hS (lookupTcb_some_objects st tid tcb hL) (hf tcb)

theorem storeTcbQueueLinks_runQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {prev : Option SeLe4n.ThreadId} {pprev : Option QueuePPrev} {next : Option SeLe4n.ThreadId}
    (h : storeTcbQueueLinks st tid prev pprev next = .ok st') : RunQueueStage st st' :=
  modifyTcb_runQueueStage h (fun _ _ => rfl)

theorem storeTcbIpcState_runQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {s : ThreadIpcState} (h : storeTcbIpcState st tid s = .ok st') : RunQueueStage st st' :=
  modifyTcb_runQueueStage h (fun _ _ => rfl)

theorem storeTcbIpcStateAndMessage_runQueueStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {s : ThreadIpcState} {m : Option IpcMessage}
    (h : storeTcbIpcStateAndMessage st tid s m = .ok st') : RunQueueStage st st' :=
  modifyTcb_runQueueStage h (fun _ _ => rfl)

/-- An endpoint stored over an endpoint. -/
theorem storeObject_endpoint_runQueueStage {st st' : SystemState} {k : SeLe4n.ObjId}
    {ep ep' : Endpoint} (hOld : st.objects[k]? = some (.endpoint ep))
    (hS : storeObject k (.endpoint ep') st = .ok ((), st')) : RunQueueStage st st' :=
  RunQueueStage.storeObject hS (fun c => by rw [hOld]; rfl)

/-- A TCB stored over the thread's TCB with the same run-queue fields. -/
theorem storeObject_tcbOver_runQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {t old : TCB} (hOld : st.getTcb? tid = some old)
    (hS : storeObject tid.toObjId (.tcb t) st = .ok ((), st'))
    (h : ∀ c, t.runLinkOn c = old.runLinkOn c) : RunQueueStage st st' :=
  RunQueueStage.storeObject_tcb hS ((SystemState.getTcb?_eq_some_iff st tid old).mp hOld) h

/-- A Reply stored over a Reply. -/
theorem storeObject_replyOver_runQueueStage {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {r r' : SeLe4n.Kernel.Reply} (hOld : st.getReply? rid = some r)
    (hS : storeObject rid.toObjId (.reply r') st = .ok ((), st')) : RunQueueStage st st' :=
  RunQueueStage.storeObject hS (fun c => by
    rw [(SystemState.getReply?_eq_some_iff st rid r).mp hOld]; rfl)

theorem linkReply_runQueueStage {rid : SeLe4n.ReplyId} {caller : SeLe4n.ThreadId}
    {st st' : SystemState} (h : SystemState.linkReply rid caller st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold SystemState.linkReply at h
  split at h
  · rename_i r hR
    split at h
    · exact storeObject_replyOver_runQueueStage hR h
    · cases h
  · cases h

theorem consumeReply_runQueueStage {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (h : SystemState.consumeReply rid st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold SystemState.consumeReply at h
  split at h
  · rename_i r hR
    exact storeObject_replyOver_runQueueStage hR h
  · cases h; exact RunQueueStage.refl _

theorem linkCallerReply_runQueueStage {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (h : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold SystemState.linkCallerReply at h
  split at h
  · cases h
  · rename_i st1 h1
    split at h
    · cases h
    · rename_i tcb hT
      split at h
      · exact (linkReply_runQueueStage h1).trans
          (storeObject_tcbOver_runQueueStage hT h (fun _ => rfl))
      · cases h

theorem consumeCallerReply_runQueueStage {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (h : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold SystemState.consumeCallerReply at h
  split at h
  · cases h
  · rename_i st1 h1
    split at h
    · cases h; exact consumeReply_runQueueStage h1
    · rename_i tcb hT
      exact (consumeReply_runQueueStage h1).trans
        (storeObject_tcbOver_runQueueStage hT h (fun _ => rfl))

theorem linkServerStashedReply_runQueueStage {caller server : SeLe4n.ThreadId}
    {st st' : SystemState}
    (h : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold SystemState.linkServerStashedReply at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i st1 h1
      split at h
      · cases h; exact linkCallerReply_runQueueStage h1
      · rename_i tcb hT
        exact (linkCallerReply_runQueueStage h1).trans
          (storeObject_tcbOver_runQueueStage hT h (fun _ => rfl))

/-- The head pop: an endpoint store and queue-link writes. -/
theorem endpointQueuePopHead_runQueueStage {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {st st' : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    (h : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, tcb, st')) :
    RunQueueStage st st' := by
  unfold endpointQueuePopHead SystemState.getObject? at h
  dsimp only at h
  split at h
  · rename_i ep hEp
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i st1 hS1
            have s1 := storeObject_endpoint_runQueueStage hEp hS1
            split at h
            · cases h
            · rename_i st2 hS2
              have s2 : RunQueueStage st1 st2 := by
                split at hS2
                · cases hS2; exact RunQueueStage.refl _
                · split at hS2
                  · cases hS2
                  · exact storeTcbQueueLinks_runQueueStage hS2
              split at h
              · cases h
              · rename_i st3 hS3
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨-, -, rfl⟩ := h
                exact (s1.trans s2).trans (storeTcbQueueLinks_runQueueStage hS3)
  · cases h
  · cases h

/-- The enqueue: an endpoint store and queue-link writes. -/
theorem endpointQueueEnqueue_runQueueStage {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (h : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    RunQueueStage st st' := by
  unfold endpointQueueEnqueue SystemState.getObject? at h
  dsimp only at h
  split at h
  · rename_i ep hEp
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · split at h
            · cases h
            · rename_i st1 hS1
              exact (storeObject_endpoint_runQueueStage hEp hS1).trans
                (storeTcbQueueLinks_runQueueStage h)
          · split at h
            · cases h
            · split at h
              · cases h
              · rename_i st1 hS1
                split at h
                · cases h
                · rename_i st2 hS2
                  exact ((storeObject_endpoint_runQueueStage hEp hS1).trans
                    (storeTcbQueueLinks_runQueueStage hS2)).trans
                    (storeTcbQueueLinks_runQueueStage h)
  · cases h
  · cases h

-- ============================================================================
-- Wake and deschedule
-- ============================================================================

/-- The wake: the `.ready` mark and the link-writing enqueue. -/
theorem enqueueRunnableOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) : RunQueueStage st (enqueueRunnableOnCore st c tid) :=
  fun h r => ⟨enqueueRunnableOnCore_preserves_objects_invExt st c tid h,
    enqueueRunnableOnCore_runQueueRefined c tid h r⟩

theorem wakeThread_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : Concurrency.CoreId) : RunQueueStage st (wakeThread st tid c).1 :=
  enqueueRunnableOnCore_runQueueStage st _ tid

-- ============================================================================
-- Call
-- ============================================================================

/-- The cross-core call: queue operations, IPC-state stores, the receiver's
wake, the reply link and the caller's deschedule. -/
theorem endpointCallOnCore_runQueueStage (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (c : Concurrency.CoreId)
    (st : SystemState) :
    RunQueueStage st (endpointCallOnCore endpointId caller msg c st).1 := by
  unfold endpointCallOnCore
  split
  · exact RunQueueStage.refl _
  split
  · exact RunQueueStage.refl _
  split
  · split
    · split
      · exact RunQueueStage.refl _
      · rename_i st1 hPop
        split
        · exact RunQueueStage.refl _
        · rename_i st2 hS2
          split
          · exact RunQueueStage.refl _
          · rename_i st4 hS4
            split
            · exact RunQueueStage.refl _
            · rename_i st5 hS5
              exact ((((endpointQueuePopHead_runQueueStage hPop).trans
                (storeTcbIpcStateAndMessage_runQueueStage hS2)).trans
                (wakeThread_runQueueStage _ _ _)).trans
                ((storeTcbIpcStateAndMessage_runQueueStage hS4).trans
                (linkServerStashedReply_runQueueStage hS5))).trans
                (removeRunnableOnCore_runQueueStage _ _ _)
    · split
      · exact RunQueueStage.refl _
      · rename_i st1 hE
        split
        · exact RunQueueStage.refl _
        · rename_i st2 hS2
          exact ((endpointQueueEnqueue_runQueueStage hE).trans
            (storeTcbIpcStateAndMessage_runQueueStage hS2)).trans
            (removeRunnableOnCore_runQueueStage _ _ _)
  · split <;> exact RunQueueStage.refl _

-- ============================================================================
-- Capability transfer and donation
-- ============================================================================

/-- The cap transfer writes CNodes and the derivation tree: every thread's TCB
reads as it did. -/
theorem ipcUnwrapCaps_runQueueStage {msg : IpcMessage} {root : SeLe4n.ObjId}
    {base : SeLe4n.Slot} {grant : Bool} {st st' : SystemState} {summary : CapTransferSummary}
    (h : ipcUnwrapCaps msg root base grant st = .ok (summary, st')) : RunQueueStage st st' :=
  have hS := ipcUnwrapCaps_preserves_scheduler msg root base grant st st' summary h
  RunQueueStage.of_placement
    (fun hInv => ipcUnwrapCaps_preserves_objects_invExt msg root base grant st st' summary hInv h)
    (by rw [hS]) (by rw [hS])
    (fun hInv x => by rw [ipcUnwrapCaps_getTcb?_eq msg root base grant st st' summary x hInv h])

/-- The donation rebinds a context and two threads' bindings: no run-queue
field moves. -/
theorem donateSchedContext_runQueueStage {st st' : SystemState}
    {client server : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    (h : donateSchedContext st client server scId = .ok st') : RunQueueStage st st' :=
  have hS := donateSchedContext_scheduler_eq st st' client server scId h
  RunQueueStage.of_placement
    (fun hInv => donateSchedContext_preserves_objects_invExt st st' client server scId hInv h)
    (by rw [hS]) (by rw [hS])
    (fun hInv x => donateSchedContext_getTcb?_placement_eq st st' client server scId hInv h x)

theorem applyCallDonation_runQueueStage {st st' : SystemState}
    {callerV receiverV : SeLe4n.ValidThreadId}
    (h : applyCallDonation st callerV receiverV = .ok st') : RunQueueStage st st' := by
  rw [applyCallDonation_characterisation] at h
  split at h
  · exact donateSchedContext_runQueueStage h
  · cases h; exact RunQueueStage.refl _

theorem applyCallDonationOnCore_runQueueStage {st st' : SystemState}
    {callerV receiverV : SeLe4n.ValidThreadId} {donorHome doneeHome : Concurrency.CoreId}
    (h : applyCallDonationOnCore st callerV receiverV donorHome doneeHome = .ok st') :
    RunQueueStage st st' := by
  obtain ⟨st1, hDon, harm⟩ :=
    applyCallDonationOnCore_ok_decompose st st' callerV receiverV donorHome doneeHome h
  rcases harm with ⟨-, rfl⟩ | ⟨scId, -, rfl⟩
  · exact applyCallDonation_runQueueStage hDon
  · exact (applyCallDonation_runQueueStage hDon).trans
      (migrateSchedContextReplenishment_runQueueStage _ _ _ _)

-- ============================================================================
-- Call dispatch
-- ============================================================================

theorem endpointCallWithCapsOnCore_runQueueStage (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (rights : AccessRightSet)
    (base : SeLe4n.Slot) (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st (endpointCallWithCapsOnCore endpointId caller msg rights base c st).1 := by
  have s0 := endpointCallOnCore_runQueueStage endpointId caller
    { msg with capsGranted := rights.mem .grant } c st
  unfold endpointCallWithCapsOnCore
  generalize endpointCallOnCore endpointId caller { msg with capsGranted := rights.mem .grant }
    c st = r at s0 ⊢
  obtain ⟨st1, r⟩ := r
  cases r with
  | error e => exact s0
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact s0
      | (rename_i hU; exact s0.trans (ipcUnwrapCaps_runQueueStage hU))

theorem endpointCallCrossCoreDispatch_runQueueStage (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (rights : AccessRightSet)
    (base : SeLe4n.Slot) (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st
      (endpointCallCrossCoreDispatch endpointId caller msg rights base c st).1 := by
  have s0 := endpointCallWithCapsOnCore_runQueueStage endpointId caller msg rights base c st
  unfold endpointCallCrossCoreDispatch
  generalize endpointCallWithCapsOnCore endpointId caller msg rights base c st = r at s0 ⊢
  obtain ⟨st1, r⟩ := r
  cases r with
  | error e => exact s0
  | ok res =>
    dsimp only
    repeat' split
    all_goals first
      | exact s0
      | (rename_i hD; exact (s0.trans (applyCallDonationOnCore_runQueueStage hD)).trans
          (PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _))

-- ============================================================================
-- Delivery staging and fault delivery
-- ============================================================================

theorem writeReturnFrameToTcb_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Architecture.SyscallReturnFrame) :
    RunQueueStage st (Architecture.writeReturnFrameToTcb st tid frame) :=
  RunQueueStage.updateTcb st tid (fun _ _ => rfl)

theorem recordPhysicalWrites_runQueueStage (st : SystemState)
    (ws : List Architecture.PhysicalWrite) :
    RunQueueStage st (Architecture.recordPhysicalWrites st ws) :=
  RunQueueStage.of_frame rfl rfl rfl

theorem stageDeliveredMessage_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (n : Nat) : RunQueueStage st (Architecture.stageDeliveredMessage st tid n) := by
  unfold Architecture.stageDeliveredMessage
  repeat' split
  all_goals first
    | exact RunQueueStage.refl _
    | exact (writeReturnFrameToTcb_runQueueStage _ _ _).trans
        (recordPhysicalWrites_runQueueStage _ _)

theorem stageWokenDelivery_runQueueStage (st : SystemState) (w? : Option SeLe4n.ThreadId)
    (n : Nat) : RunQueueStage st (Architecture.stageWokenDelivery st w? n) := by
  cases w? with
  | none => exact RunQueueStage.refl _
  | some tid => exact stageDeliveredMessage_runQueueStage st tid n

theorem recordPendingFault_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (tf : ThreadFault) : RunQueueStage st (recordPendingFault st tid tf) :=
  RunQueueStage.updateTcb st tid (fun _ _ => rfl)

theorem faultSuspendOnCore_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : Concurrency.CoreId) : RunQueueStage st (faultSuspendOnCore st tid c) :=
  (removeRunnableOnCore_runQueueStage st tid c).trans
    (RunQueueStage.updateTcb _ tid (fun _ _ => rfl))

theorem faultAbandonOnCore_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : Concurrency.CoreId) : RunQueueStage st (faultAbandonOnCore st tid c) :=
  (removeRunnableOnCore_runQueueStage st tid c).trans
    (RunQueueStage.updateTcb _ tid (fun _ _ => rfl))

theorem writeFaultRegistersToTcb_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) : RunQueueStage st (writeFaultRegistersToTcb st tid w) :=
  RunQueueStage.updateTcb st tid (fun _ _ => rfl)

/-- The fault delivery: the handler call, or the fail-closed suspend; then the
woken handler's frame and the fault record. -/
theorem faultDeliverOnCore_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (f : Fault) (fctx : FaultContext) (c : Concurrency.CoreId) :
    RunQueueStage st (faultDeliverOnCore st tid f fctx c).1 := by
  unfold faultDeliverOnCore
  split
  · exact (faultSuspendOnCore_runQueueStage _ _ _).trans (recordPendingFault_runQueueStage _ _ _)
  · rename_i tgt _
    have s0 := endpointCallCrossCoreDispatch_runQueueStage tgt.endpoint tid
      (faultMessage f fctx tgt.cap.badge) tgt.cap.rights (SeLe4n.Slot.ofNat 0) c st
    generalize endpointCallCrossCoreDispatch tgt.endpoint tid
      (faultMessage f fctx tgt.cap.badge) tgt.cap.rights (SeLe4n.Slot.ofNat 0) c st = r at s0 ⊢
    obtain ⟨st1, r⟩ := r
    cases r with
    | error e =>
      exact (faultSuspendOnCore_runQueueStage _ _ _).trans (recordPendingFault_runQueueStage _ _ _)
    | ok res =>
      exact (s0.trans (stageWokenDelivery_runQueueStage _ _ _)).trans
        (recordPendingFault_runQueueStage _ _ _)

theorem faultDeliverOnCoreChecked_runQueueStage (ctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext) (c : Concurrency.CoreId) :
    RunQueueStage st (faultDeliverOnCoreChecked ctx st tid f fctx c).1 := by
  unfold faultDeliverOnCoreChecked
  split
  · exact (faultSuspendOnCore_runQueueStage _ _ _).trans (recordPendingFault_runQueueStage _ _ _)
  · split
    · exact faultDeliverOnCore_runQueueStage st tid f fctx c
    · exact (faultSuspendOnCore_runQueueStage _ _ _).trans (recordPendingFault_runQueueStage _ _ _)

end SeLe4n.Kernel
