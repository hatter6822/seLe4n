/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Capability

/-!
# Notification, reply and reply-receive keep the run-queue link agreement

WS-ZA ZA4.5 part 2.  The notification signal and wait, the reply (ordinary and
fault) and the reply-receive are `RunQueueStage`s: they wake and deschedule
through the stages `IPC.Invariant.RunQueueAgreement` proves and write no other
run-queue field.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)

theorem modifyTcbOpt_runQueueStage {st st' : SystemState} {t? : Option SeLe4n.ThreadId}
    {f : TCB → TCB} (h : modifyTcbOpt st t? f = .ok st')
    (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c) : RunQueueStage st st' := by
  unfold modifyTcbOpt at h
  split at h
  · cases h; exact RunQueueStage.refl _
  · exact modifyTcb_runQueueStage h hf

theorem linkNtfnWaiter_runQueueStage {st st' : SystemState} {w : SeLe4n.ThreadId}
    {tail : Option SeLe4n.ThreadId} (h : linkNtfnWaiter st w tail = .ok st') :
    RunQueueStage st st' := by
  unfold linkNtfnWaiter at h
  split at h
  · cases h
  · rename_i st3 h3
    exact (modifyTcb_runQueueStage h3 (fun _ _ => rfl)).trans
      (modifyTcbOpt_runQueueStage h (fun _ _ => rfl))

/-- A TCB stored over the slot a lookup in an earlier state found, the slot
unchanged since. -/
theorem storeObject_tcbAt_runQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {t old : TCB} (hOld : st.objects[tid.toObjId]? = some (.tcb old))
    (hS : storeObject tid.toObjId (.tcb t) st = .ok ((), st'))
    (h : ∀ c, t.runLinkOn c = old.runLinkOn c) : RunQueueStage st st' :=
  RunQueueStage.storeObject_tcb hS hOld h

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (storeTcbIpcState_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (storeTcbQueueLinks_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (linkNtfnWaiter_runQueueStage (by with_reducible assumption)))

/-- The guarded removal of a thread from an endpoint queue: endpoint stores and
queue-link writes. -/
theorem endpointQueueRemoveDual_runQueueStage {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (h : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    RunQueueStage st st' := by
  refine RunQueueStage.of_inv fun hInv => ?_
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid h with
  | headLast ep tcb s1 s2 hEp _ _ _ _ _ _ hS1 hS2 hClear =>
    exact ((storeObject_endpoint_runQueueStage hEp hS1).trans
      (storeObject_endpoint_runQueueStage
        (storeObject_objects_eq _ _ _ _ hInv hS1) hS2)).trans
      (storeTcbQueueLinks_runQueueStage hClear)
  | headMore ep tcb nextTcb nextTid s1 s2 s3 hEp _ _ _ _ _ _ hS1 _ hRelink hS2 hClear =>
    have i1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
    obtain ⟨_, hEp2⟩ := storeTcbQueueLinks_endpoint_forward _ _ _ _ _ _ _ _ i1 hRelink
      (storeObject_objects_eq _ _ _ _ hInv hS1)
    exact (((storeObject_endpoint_runQueueStage hEp hS1).trans
      (storeTcbQueueLinks_runQueueStage hRelink)).trans
      (storeObject_endpoint_runQueueStage hEp2 hS2)).trans
      (storeTcbQueueLinks_runQueueStage hClear)
  | midLast ep tcb prevTcb prevTid s1 s2 hEp _ _ _ _ _ _ _ _ _ hRelink hS hClear =>
    obtain ⟨_, hEp1⟩ := storeTcbQueueLinks_endpoint_forward _ _ _ _ _ _ _ _ hInv hRelink hEp
    exact ((storeTcbQueueLinks_runQueueStage hRelink).trans
      (storeObject_endpoint_runQueueStage hEp1 hS)).trans
      (storeTcbQueueLinks_runQueueStage hClear)
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp _ _ _ _ _ _ _ _ _
      hRelinkPrev _ hRelinkNext hS hClear =>
    have i1 := storeTcbQueueLinks_preserves_objects_invExt _ _ _ _ _ _ hInv hRelinkPrev
    obtain ⟨_, hEp1⟩ := storeTcbQueueLinks_endpoint_forward _ _ _ _ _ _ _ _ hInv hRelinkPrev hEp
    obtain ⟨_, hEp2⟩ := storeTcbQueueLinks_endpoint_forward _ _ _ _ _ _ _ _ i1 hRelinkNext hEp1
    exact (((storeTcbQueueLinks_runQueueStage hRelinkPrev).trans
      (storeTcbQueueLinks_runQueueStage hRelinkNext)).trans
      (storeObject_endpoint_runQueueStage hEp2 hS)).trans
      (storeTcbQueueLinks_runQueueStage hClear)

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (endpointQueueRemoveDual_runQueueStage (by with_reducible assumption)))

/-- A notification stored over a notification. -/
theorem storeObject_notificationOver_runQueueStage {st st' : SystemState} {k : SeLe4n.ObjId}
    {n n' : Notification} (hOld : st.getNotification? k = some n)
    (hS : storeObject k (.notification n') st = .ok ((), st')) : RunQueueStage st st' :=
  RunQueueStage.storeObject hS (fun c => by
    rw [(SystemState.getNotification?_eq_some_iff st k n).mp hOld]; rfl)

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_
    (storeObject_notificationOver_runQueueStage (by with_reducible assumption)
      (by with_reducible assumption)))

/-- A step that rewrites only notification-queue links (`ntfnLinksRewritten`)
keeps the run-queue agreement: a TCB's run-queue entries are read off its
run-queue fields, which the rewrite leaves alone. -/
theorem runQueueStage_of_ntfnLinksRewritten {st s : SystemState}
    (h : st.objects.invExt → ntfnLinksRewritten st s) : RunQueueStage st s := by
  intro hInv hR
  have hD := h hInv
  refine ⟨hD.2.1, SystemState.runQueueRefined_of_frame (fun c t => ?_)
    (by rw [hD.scheduler_eq]) (by rw [hD.scheduler_eq]) hR⟩
  rw [SystemState.runLinkOn_eq_objRunLinkOn, SystemState.runLinkOn_eq_objRunLinkOn]
  rcases hD.2.2 t.toObjId with e | ⟨t0, t1, h0, h1, np, nn, rfl⟩
  · rw [e]
  · rw [h0, h1]; rfl

theorem detachNtfnHead_runQueueStage (st : SystemState) (head : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) : RunQueueStage st (detachNtfnHead st head next) :=
  runQueueStage_of_ntfnLinksRewritten (detachNtfnHead_linksRewritten st head next)

theorem notificationSignalOnCore_runQueueStage (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st (notificationSignalOnCore notificationId badge c st).1 := by
  unfold notificationSignalOnCore
  repeat' (first | split | dsimp only)
  all_goals first
    | exact RunQueueStage.refl _
    | exact (((storeObject_notificationOver_runQueueStage (by assumption) (by assumption)).trans
         (storeTcbIpcStateAndMessage_runQueueStage (by assumption))).trans
         (detachNtfnHead_runQueueStage _ _ _)).trans
         (wakeThread_runQueueStage _ _ _)
    | exact storeObject_notificationOver_runQueueStage (by assumption) (by assumption)

theorem notificationSignalBoundOnCore_runQueueStage (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st (notificationSignalBoundOnCore notificationId badge c st).1 := by
  unfold notificationSignalBoundOnCore
  repeat' (first | split | dsimp only)
  all_goals first
    | exact RunQueueStage.refl _
    | exact notificationSignalOnCore_runQueueStage _ _ _ _
    | exact ((endpointQueueRemoveDual_runQueueStage (by assumption)).trans
         (storeTcbReceiveComplete_runQueueStage (by assumption))).trans
         (wakeThread_runQueueStage _ _ _)

/-- The waiter's state write after the notification store: the TCB was read
before the store, and the store wrote the notification's own slot. -/
private theorem notificationWait_blockStore_runQueueStage {st st1 st2 : SystemState}
    {notificationId : SeLe4n.ObjId} {ntfn n' : Notification} {waiter : SeLe4n.ThreadId}
    {tcb : TCB} {s : ThreadIpcState} {m : Option IpcMessage}
    (hN : st.getNotification? notificationId = some ntfn)
    (hT : lookupTcb st waiter = some tcb)
    (hS1 : storeObject notificationId (.notification n') st = .ok ((), st1))
    (hS2 : storeTcbIpcStateAndMessage_fromTcb st1 waiter tcb s m = .ok st2) :
    RunQueueStage st st2 := by
  refine RunQueueStage.of_inv fun hInv => ?_
  have hNo := (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hN
  have hTo := lookupTcb_some_objects st waiter tcb hT
  have hNe : waiter.toObjId ≠ notificationId := by
    intro hEq; rw [hEq, hNo] at hTo; cases hTo
  have hT1 : st1.objects[waiter.toObjId]? = some (.tcb tcb) := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hInv hS1, hTo]
  unfold storeTcbIpcStateAndMessage_fromTcb at hS2
  split at hS2
  · cases hS2
  · rename_i hS; cases hS2
    exact (storeObject_notificationOver_runQueueStage hN hS1).trans
      (RunQueueStage.storeObject_tcb hS hT1 (fun _ => rfl))

theorem notificationWaitOnCore_runQueueStage (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st (notificationWaitOnCore notificationId waiter c st).1 := by
  unfold notificationWaitOnCore
  repeat' (first | split | dsimp only)
  all_goals first
    | exact RunQueueStage.refl _
    | exact (storeObject_notificationOver_runQueueStage (by assumption) (by assumption)).trans
         (storeTcbIpcState_runQueueStage (by assumption))
    | exact ((notificationWait_blockStore_runQueueStage (by assumption) (by assumption)
         (by assumption) (by assumption)).trans
         (linkNtfnWaiter_runQueueStage (by assumption))).trans
         (removeRunnableOnCore_runQueueStage _ _ _)

/-- The reply-frame splice rewrites Reply objects only. -/
theorem spliceReplyFrameOutOrSelf_runQueueStage (st : SystemState) (rid : SeLe4n.ReplyId) :
    RunQueueStage st (spliceReplyFrameOutOrSelf st rid) := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]; exact RunQueueStage.refl _
  · refine RunQueueStage.of_slots fun hInv =>
      ⟨spliceReplyFrameOut_preserves_objects_invExt hInv h, fun oid c => ?_,
       spliceReplyFrameOut_scheduler_eq h⟩
    rcases spliceReplyFrameOut_objects_rewrite hInv h oid with e | ⟨_, _, h1, h2, _⟩
    · rw [e]
    · rw [h1, h2]; rfl

theorem removeCallerReplyFrame_runQueueStage {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (h : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    RunQueueStage st st' :=
  (spliceReplyFrameOutOrSelf_runQueueStage st rid).trans (consumeCallerReply_runQueueStage h)

/-- A state write from a TCB record read from the same state. -/
theorem storeTcbIpcStateAndMessage_fromTcb_runQueueStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {s : ThreadIpcState} {m : Option IpcMessage}
    (hT : lookupTcb st tid = some tcb)
    (h : storeTcbIpcStateAndMessage_fromTcb st tid tcb s m = .ok st') : RunQueueStage st st' := by
  unfold storeTcbIpcStateAndMessage_fromTcb at h
  split at h
  · cases h
  · rename_i hS; cases h
    exact RunQueueStage.storeObject_tcb hS (lookupTcb_some_objects _ _ _ hT) (fun _ => rfl)

theorem endpointReplyOnCore_runQueueStage (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st (endpointReplyOnCore replier target msg c st).1 := by
  unfold endpointReplyOnCore
  repeat' (first | split | dsimp only)
  all_goals first
    | exact RunQueueStage.refl _
    | exact (storeTcbIpcStateAndMessage_fromTcb_runQueueStage (by assumption) (by assumption)).trans
        (wakeThread_runQueueStage _ _ _)
    | exact ((storeTcbIpcStateAndMessage_fromTcb_runQueueStage (by assumption)
        (by assumption)).trans (wakeThread_runQueueStage _ _ _)).trans
        (removeCallerReplyFrame_runQueueStage (by assumption))

theorem applyReplyDonationOnCore_runQueueStage {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {targetV : SeLe4n.ValidThreadId} {holderHome ownerHome : Concurrency.CoreId}
    (h : applyReplyDonationOnCore st rid targetV holderHome ownerHome = .ok st') :
    RunQueueStage st st' := by
  unfold applyReplyDonationOnCore at h
  repeat' (first | split at h | dsimp only at h)
  all_goals first
    | (cases h; exact RunQueueStage.refl _)
    | (cases h; done)
    | (cases h
       exact ((returnDonatedSchedContextResolved_runQueueStage (by assumption)).trans
         (migrateSchedContextReplenishment_runQueueStage _ _ _ _)).trans
         (descheduleAt_runQueueStage _ _ _))

theorem endpointReplyCrossCoreDispatch_runQueueStage (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st (endpointReplyCrossCoreDispatch replier target msg c st).1 := by
  have hE := endpointReplyOnCore_runQueueStage replier target msg c st
  unfold endpointReplyCrossCoreDispatch
  generalize endpointReplyOnCore replier target msg c st = p at hE ⊢
  obtain ⟨st1, r⟩ := p
  dsimp only at hE
  cases r <;> dsimp only
  · exact RunQueueStage.refl _
  repeat' (first | split | dsimp only)
  all_goals first
    | exact RunQueueStage.refl _
    | exact hE.trans (PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _)
    | exact (hE.trans (applyReplyDonationOnCore_runQueueStage (by assumption))).trans
        (PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _)

theorem endpointReplyCrossCoreDispatchChecked_runQueueStage (ctx : LabelingContext)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : Concurrency.CoreId)
    (st : SystemState) :
    RunQueueStage st (endpointReplyCrossCoreDispatchChecked ctx replier target msg c st).1 := by
  unfold endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch_runQueueStage _ _ _ _ _
  · exact RunQueueStage.refl _

theorem faultReplyApplyOnCore_runQueueStage (st : SystemState) (faulted : SeLe4n.ThreadId)
    (outcome : Architecture.FaultReplyOutcome) : RunQueueStage st (faultReplyApplyOnCore st faulted outcome) := by
  unfold faultReplyApplyOnCore
  split
  · exact RunQueueStage.updateTcb _ _ (fun _ _ => rfl)
  · exact faultAbandonOnCore_runQueueStage _ _ _

theorem faultReplyOnCore_runQueueStage (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st (faultReplyOnCore replier faulted mi regs c st).1 := by
  have hE := endpointReplyCrossCoreDispatch_runQueueStage replier faulted IpcMessage.empty c st
  unfold faultReplyOnCore
  repeat' (first | split | dsimp only)
  all_goals first
    | exact RunQueueStage.refl _
    | (rename_i hR; rw [hR] at hE; exact hE.trans (faultReplyApplyOnCore_runQueueStage _ _ _))

theorem replyTransferOnCore_runQueueStage {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {c : Concurrency.CoreId}
    {st st' : SystemState}
    (h : replyTransferOnCore replier callerTid mi regs msg c st = .ok ((), st')) :
    RunQueueStage st st' := by
  have hF := faultReplyOnCore_runQueueStage replier callerTid mi regs c st
  have hE := endpointReplyCrossCoreDispatch_runQueueStage replier callerTid msg c st
  unfold replyTransferOnCore at h
  repeat' (first | split at h | dsimp only at h)
  all_goals first
    | (cases h; done)
    | (rename_i hR; cases h; rw [hR] at hF; exact hF)
    | (rename_i hR; cases h; rw [hR] at hE
       exact hE.trans (stageDeliveredMessage_runQueueStage _ _ _))

theorem replyTransferOnCoreChecked_runQueueStage {ctx : LabelingContext}
    {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {c : Concurrency.CoreId}
    {st st' : SystemState}
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg c st = .ok ((), st')) :
    RunQueueStage st st' := by
  have hF := faultReplyOnCore_runQueueStage replier callerTid mi regs c st
  have hE := endpointReplyCrossCoreDispatchChecked_runQueueStage ctx replier callerTid msg c st
  unfold replyTransferOnCoreChecked at h
  repeat' (first | split at h | dsimp only at h)
  all_goals first
    | (cases h; done)
    | (rename_i hR; cases h; rw [hR] at hF; exact hF)
    | (rename_i hR; cases h; rw [hR] at hE
       exact hE.trans (stageDeliveredMessage_runQueueStage _ _ _))

theorem stageWokenSendCompletion_runQueueStage (st : SystemState)
    (w? : Option SeLe4n.ThreadId) :
    RunQueueStage st (Architecture.stageWokenSendCompletion st w?) := by
  unfold Architecture.stageWokenSendCompletion
  repeat' split
  all_goals first
    | exact RunQueueStage.refl _
    | exact writeReturnFrameToTcb_runQueueStage _ _ _

theorem applyRendezvousCallDonation_runQueueStage {st st' : SystemState}
    {receiver donor : SeLe4n.ThreadId}
    (h : applyRendezvousCallDonation st receiver donor = .ok st') : RunQueueStage st st' := by
  unfold applyRendezvousCallDonation at h
  split at h
  · exact applyCallDonationOnCore_runQueueStage h
  · cases h

theorem applyReceiveRendezvousHandoff_runQueueStage {st st' : SystemState}
    {receiver dequeued : SeLe4n.ThreadId} {c : Concurrency.CoreId}
    (h : applyReceiveRendezvousHandoff st receiver dequeued c = .ok st') :
    RunQueueStage st st' := by
  obtain ⟨stDon, hDon, rfl⟩ := applyReceiveRendezvousHandoff_ok_decompose st st' receiver
    dequeued c h
  have s0 : RunQueueStage st stDon := by
    unfold applyReceiveRendezvousDonation at hDon
    repeat' split at hDon
    all_goals first
      | (cases hDon; exact RunQueueStage.refl _)
      | exact applyRendezvousCallDonation_runQueueStage hDon
      | cases hDon
  split
  · exact s0.trans (PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _)
  · exact s0

theorem applyReceiveLegPipHandoff_runQueueStage (st : SystemState)
    (receiver dequeued walked : SeLe4n.ThreadId) (c : Concurrency.CoreId) :
    RunQueueStage st (applyReceiveLegPipHandoff st receiver dequeued walked c) := by
  unfold applyReceiveLegPipHandoff applyReceiverPipHandoff
  repeat' split
  all_goals first
    | exact RunQueueStage.refl _
    | exact PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _

theorem replyRecvPopDonation_runQueueStage {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {st st' : SystemState} {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (h : replyRecvPopDonation rid target st = .ok (r, st')) : RunQueueStage st st' := by
  unfold replyRecvPopDonation at h
  repeat' (first | split at h | dsimp only at h)
  all_goals first
    | (cases h; exact RunQueueStage.refl _)
    | (cases h; done)
    | (cases h
       exact (returnDonatedSchedContextResolved_runQueueStage (by assumption)).trans
         (migrateSchedContextReplenishment_runQueueStage _ _ _ _))

theorem replyRecvHolderDeschedule_runQueueStage (tid holder : SeLe4n.ThreadId)
    (st : SystemState) : RunQueueStage st (replyRecvHolderDeschedule tid holder st) := by
  unfold replyRecvHolderDeschedule
  split
  · exact RunQueueStage.refl _
  · exact descheduleAt_runQueueStage _ _ _

theorem replyRecvPostReceiveDonation_runQueueStage {tid recordedServer nextThread : SeLe4n.ThreadId}
    {c : Concurrency.CoreId} {returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    {st st' : SystemState}
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread c returned? st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold replyRecvPostReceiveDonation at h
  repeat' (first | split at h | dsimp only at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _)
    | (cases h
       exact ((replyRecvHolderDeschedule_runQueueStage _ _ _).trans
         (applyRendezvousCallDonation_runQueueStage (by assumption))).trans
         (PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _))
    | (cases h
       exact (descheduleAt_runQueueStage _ _ _).trans
         (PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _))

theorem endpointReplyRecvOnCore_runQueueStage {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage}
    {root : SeLe4n.ObjId} {base : SeLe4n.Slot} {c : Concurrency.CoreId}
    {st st' : SystemState} {s : CapTransferSummary}
    (h : endpointReplyRecvOnCore epId tid rid prevCaller msg root base c st = .ok (s, st')) :
    RunQueueStage st st' := by
  have hE := endpointReplyOnCore_runQueueStage tid prevCaller msg c st
  unfold endpointReplyRecvOnCore at h
  dsimp only at h
  generalize endpointReplyOnCore tid prevCaller msg c st = p at hE h
  obtain ⟨st1, r⟩ := p
  dsimp only at hE
  cases r <;> dsimp only at h
  · cases h
  split at h
  · cases h
  rename_i ret st1p hPop
  have hR := endpointReceiveDualWithCapsOnCore_runQueueStage epId tid (some rid) root base c st1p
  generalize endpointReceiveDualWithCapsOnCore epId tid (some rid) root base c st1p = q at hR h
  obtain ⟨st2, r2⟩ := q
  dsimp only at hR
  rcases r2 with _ | ⟨nt, sm, _⟩ <;> dsimp only at h
  · cases h
  split at h
  · cases h
  rename_i st3 hPost
  cases h
  exact ((((((hE.trans (replyRecvPopDonation_runQueueStage hPop)).trans hR).trans
    (replyRecvPostReceiveDonation_runQueueStage hPost)).trans
    (applyReceiveLegPipHandoff_runQueueStage _ _ _ _ _)).trans
    (stageDeliveredMessage_runQueueStage _ _ _)).trans
    (stageWokenSendCompletion_runQueueStage _ _))

end SeLe4n.Kernel
