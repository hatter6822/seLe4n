/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Capability

/-!
# Notification, reply and reply-receive keep the run-queue link agreement

WS-ZA ZA4.5 part 2.  The notification signal and the ordinary reply are
`RunQueueStage`s: each wakes a blocked thread through the stages
`IPC.Invariant.RunQueueAgreement` proves.  The notification wait, the fault reply
and the reply-receive are kernel entries (`SystemState.RunQueueEntryStage`): the
wait blocks core `c`'s current thread and deschedules it, the abandon deschedules
the faulted thread where it is placed before it marks it inactive, and the
reply-receive's receive may block its caller.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)

theorem modifyTcbOpt_runQueueStage {st st' : SystemState} {t? : Option SeLe4n.ThreadId}
    {f : TCB → TCB} (h : modifyTcbOpt st t? f = .ok st')
    (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hm : TCB.StateMono f := by tcb_state_mono)
    (hW : ∀ x, (f x).taintWords = x.taintWords := by taint_words_kept)
    (hY : ∀ x, (f x).yieldToCode = x.yieldToCode := by yield_code_kept) : RunQueueStage st st' := by
  unfold modifyTcbOpt at h
  split at h
  · cases h; exact RunQueueStage.refl _
  · exact modifyTcb_runQueueStage h hf hm hW hY

theorem linkNtfnWaiter_runQueueStage {st st' : SystemState} {w : SeLe4n.ThreadId}
    {tail : Option SeLe4n.ThreadId} (h : linkNtfnWaiter st w tail = .ok st') :
    RunQueueStage st st' := by
  unfold linkNtfnWaiter at h
  split at h
  · cases h
  · rename_i st3 h3
    exact (modifyTcb_runQueueStage h3 (fun _ _ => rfl)).trans
      (modifyTcbOpt_runQueueStage h (fun _ _ => rfl))

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (storeTcbIpcState_runQueueStage (by with_reducible assumption) rfl))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (storeTcbQueueLinks_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (linkNtfnWaiter_runQueueStage (by with_reducible assumption)))

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (endpointQueueRemoveDual_runQueueStage (by with_reducible assumption)))

/-- A notification stored over a notification. -/
theorem storeObject_notificationOver_runQueueStage {st st' : SystemState} {k : SeLe4n.ObjId}
    {n n' : Notification} (hOld : st.getNotification? k = some n)
    (hS : storeObject k (.notification n') st = .ok ((), st'))
    (hI : n'.irqBound = n.irqBound := by first | rfl | (simp_all; done))
    (hNW : n'.taintWords = n.taintWords := by taint_words_kept) : RunQueueStage st st' :=
  RunQueueStage.storeObject hS (fun c => by
    rw [(SystemState.getNotification?_eq_some_iff st k n).mp hOld]; rfl)
    (SystemState.objStateMono_nonTcb
      (by rw [(SystemState.getNotification?_eq_some_iff st k n).mp hOld]; rfl) rfl)
    (by rw [(SystemState.getNotification?_eq_some_iff st k n).mp hOld]
        simp only [objTableBackLinks_some, KernelObject.tableBackLinks, hI, hNW])
    (fun c => by rw [(SystemState.getNotification?_eq_some_iff st k n).mp hOld]; rfl)
    (by rw [(SystemState.getNotification?_eq_some_iff st k n).mp hOld]; rfl)
    (by rw [(SystemState.getNotification?_eq_some_iff st k n).mp hOld]; rfl)

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_
    (storeObject_notificationOver_runQueueStage (by with_reducible assumption)
      (by with_reducible assumption)))

/-- A step that rewrites only notification-queue links (`ntfnLinksRewritten`)
keeps the run-queue agreement: a TCB's run-queue entries are read off its
run-queue fields, which the rewrite leaves alone. -/
theorem runQueueStage_of_ntfnLinksRewritten {st s : SystemState}
    (h : st.objects.invExt → ntfnLinksRewritten st s) : RunQueueStage st s :=
  RunQueueStage.of_invExt fun hInv => by
    have hD := h hInv
    have hL : ∀ c t, s.runLinkOn c t = st.runLinkOn c t := fun c t => by
      rw [SystemState.runLinkOn_eq_objRunLinkOn, SystemState.runLinkOn_eq_objRunLinkOn]
      rcases hD.2.2 t.toObjId with e | ⟨t0, t1, h0, h1, np, nn, rfl⟩
      · rw [e]
      · rw [h0, h1]; rfl
    have hM : SystemState.StateMono st s := SystemState.StateMono.of_slots fun oid => by
      rcases hD.2.2 oid with e | ⟨t0, t1, h0, h1, np, nn, rfl⟩
      · exact SystemState.slotStateMono.of_eq e
      · rw [h0]; exact SystemState.slotStateMono.of_obj h1 (SystemState.objStateMono_tcb ⟨id, id, rfl⟩)
    have hF : SystemState.TableReferenceFrame st s := ⟨by rw [hD.1]; rfl, fun k => by
      rcases hD.2.2 k with e | ⟨t0, t1, h0, h1, np, nn, rfl⟩
      · rw [e]
      · rw [h0, h1]; rfl⟩
    exact ⟨.of_tableFrame (fun _ hR => ⟨hD.2.1, SystemState.runQueueRefined_of_frame
        (fun c t => hL c t) (by rw [hD.scheduler_eq]) (by rw [hD.scheduler_eq]) hR⟩)
        (fun _ => hF) (fun _ => ⟨.of_objReleaseLinkOn fun k c => by
          rcases hD.2.2 k with e | ⟨t0, t1, h0, h1, np, nn, rfl⟩
          · rw [e]
          · rw [h0, h1]; rfl, by rw [hD.scheduler_eq]⟩)
        (fun _ => .of_eq fun k => by
          rcases hD.2.2 k with e | ⟨t0, t1, h0, h1, np, nn, rfl⟩
          · rw [e]
          · rw [h0, h1]; rfl)
        (fun _ k => by
          rcases hD.2.2 k with e | ⟨t0, t1, h0, h1, np, nn, rfl⟩
          · rw [e]
          · rw [h0, h1]; rfl) (congrArg (fun x => x.machine.residentCode) hD.1),
      fun _ _ _ _ d => SystemState.currentDequeuedUniqueExcept_of_eq
        (by rw [hD.scheduler_eq]) hL hM d, fun _ _ => hM⟩

theorem detachNtfnHead_runQueueStage (st : SystemState) (head : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) : RunQueueStage st (detachNtfnHead st head next) :=
  runQueueStage_of_ntfnLinksRewritten (detachNtfnHead_linksRewritten st head next)

/-- The bound thread a signal delivers to is current nowhere: it is blocked in
a receive. -/
theorem blockedCurrentNowhere.boundTarget {st : SystemState}
    (h : blockedCurrentNowhere st) {nid : SeLe4n.ObjId} {t : SeLe4n.ThreadId} {e : SeLe4n.ObjId}
    (hB : boundDeliveryTarget? st nid = some (t, e)) : st.currentNowhere t :=
  let ⟨_, hT, hS⟩ := boundDeliveryTarget?_some st nid t e hB
  h.blockedOnReceive hT hS

macro_rules | `(tactic| run_queue_current_nowhere_step) => `(tactic|
  exact notificationHeadsWakeable.head (by assumption) (by assumption) (by assumption))
macro_rules | `(tactic| run_queue_current_nowhere_step) => `(tactic|
  refine SystemState.currentNowhere.of_scheduler_eq
    (endpointQueueRemoveDual_scheduler_eq _ _ _ _ _ (by with_reducible assumption)) ?_)
macro_rules | `(tactic| run_queue_current_nowhere_step) => `(tactic|
  exact blockedCurrentNowhere.boundTarget (by assumption) (by assumption))

/-- The bound thread a signal delivers to is blocked in a receive. -/
theorem boundTarget_blockedAt {st : SystemState} {nid : SeLe4n.ObjId} {t : SeLe4n.ThreadId}
    {e : SeLe4n.ObjId} (hB : boundDeliveryTarget? st nid = some (t, e)) : blockedAt st t :=
  let ⟨tcb, hT, hS⟩ := boundDeliveryTarget?_some st nid t e hB
  ⟨tcb, hT, by rw [hS]; exact fun h => by cases h⟩
macro_rules | `(tactic| run_queue_current_nowhere_step) => `(tactic|
  refine SystemState.currentNowhere.of_scheduler_eq (detachNtfnHead_scheduler _ _ _) ?_)

/-- The signal: the waiter it wakes is the notification's head, which
`hHeads` says is blocked and current nowhere. -/
theorem notificationSignalOnCore_runQueueStage (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : Concurrency.CoreId) (st : SystemState)
    (hHeads : notificationHeadsWakeable st) :
    RunQueueStage st (notificationSignalOnCore notificationId badge c st).1 := by
  unfold notificationSignalOnCore
  repeat' (first | split | dsimp only)
  all_goals first
    | exact RunQueueStage.refl _
    | (refine (((storeObject_notificationOver_runQueueStage (by assumption) (by assumption)).trans
         (storeTcbIpcStateAndMessage_runQueueStage (by assumption) rfl)).trans
         (detachNtfnHead_runQueueStage _ _ _)).then_wake _ ?_
         (notificationHeadsWakeable.blocked hHeads (by assumption) (by assumption))
       run_queue_current_nowhere; done)
    | exact storeObject_notificationOver_runQueueStage (by assumption) (by assumption)

/-- The signal to a bound thread blocked in a receive, or the plain signal. -/
theorem notificationSignalBoundOnCore_runQueueStage (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : Concurrency.CoreId) (st : SystemState)
    (hHeads : notificationHeadsWakeable st) (hBlk : blockedCurrentNowhere st) :
    RunQueueStage st (notificationSignalBoundOnCore notificationId badge c st).1 := by
  unfold notificationSignalBoundOnCore
  repeat' (first | split | dsimp only)
  all_goals first
    | exact RunQueueStage.refl _
    | exact notificationSignalOnCore_runQueueStage _ _ _ _ hHeads
    | (refine ((endpointQueueRemoveDual_runQueueStage (by assumption)).trans
         (storeTcbReceiveComplete_runQueueStage (by assumption))).then_wake _ ?_
         (boundTarget_blockedAt (by assumption))
       run_queue_current_nowhere; done)

/-- The reply-frame splice rewrites Reply objects only. -/
theorem spliceReplyFrameOutOrSelf_runQueueStage (st : SystemState) (rid : SeLe4n.ReplyId) :
    RunQueueStage st (spliceReplyFrameOutOrSelf st rid) := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]; exact RunQueueStage.refl _
  · refine RunQueueStage.of_slots (fun hInv =>
      ⟨spliceReplyFrameOut_preserves_objects_invExt hInv h, fun oid c => ?_, fun oid => ?_,
       spliceReplyFrameOut_scheduler_eq h⟩) (fun hInv =>
      ⟨spliceReplyFrameOut_referenceTables h, fun oid => by
        rcases spliceReplyFrameOut_objects_rewrite hInv h oid with e | ⟨_, _, h1, h2, _⟩
        · rw [e]
        · rw [h1, h2]; rfl⟩) (fun hInv oid c => ?_) (fun hInv oid => ?_) (fun hInv oid => ?_)
      (by rw [spliceReplyFrameOut_machine_eq h])
    · rcases spliceReplyFrameOut_objects_rewrite hInv h oid with e | ⟨_, _, h1, h2, _⟩
      · rw [e]
      · rw [h1, h2]; rfl
    · rcases spliceReplyFrameOut_objects_rewrite hInv h oid with e | ⟨_, _, h1, h2, _⟩
      · exact SystemState.slotStateMono.of_eq e
      · exact SystemState.slotStateMono.of_obj h2
          (SystemState.objStateMono_nonTcb (by rw [h1]; rfl) rfl)
    · rcases spliceReplyFrameOut_objects_rewrite hInv h oid with e | ⟨_, _, h1, h2, _⟩
      · rw [e]
      · rw [h1, h2]; rfl
    · rcases spliceReplyFrameOut_objects_rewrite hInv h oid with e | ⟨_, _, h1, h2, _⟩
      · rw [e]
      · rw [h1, h2]; rfl
    · rcases spliceReplyFrameOut_objects_rewrite hInv h oid with e | ⟨_, _, h1, h2, _⟩
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
    (h : storeTcbIpcStateAndMessage_fromTcb st tid tcb s m = .ok st') (hs : s = .ready) :
    RunQueueStage st st' := by
  subst hs
  unfold storeTcbIpcStateAndMessage_fromTcb at h
  split at h
  · cases h
  · rename_i hS; cases h
    exact RunQueueStage.storeObject_tcb hS (lookupTcb_some_objects _ _ _ hT) (fun _ => rfl)

theorem storeTcbIpcStateAndMessage_fromTcb_scheduler_eq {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {s : ThreadIpcState} {m : Option IpcMessage}
    (h : storeTcbIpcStateAndMessage_fromTcb st tid tcb s m = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold storeTcbIpcStateAndMessage_fromTcb at h
  split at h
  · cases h
  · rename_i hS; cases h; exact storeObject_scheduler_eq _ _ _ _ hS

/-- **The wait's block**: the notification store, the waiter's block write from
the TCB read before it (the store wrote the notification's own slot), its link
onto the waiter list, then its deschedule — core `c`'s current thread blocked
and descheduled. -/
theorem notificationWait_block_runQueueEntryStage {st st1 st2 st3 : SystemState}
    {notificationId : SeLe4n.ObjId} {ntfn n' : Notification} {waiter : SeLe4n.ThreadId}
    {tcb : TCB} {s : ThreadIpcState} {m : Option IpcMessage} {tail : Option SeLe4n.ThreadId}
    {c : Concurrency.CoreId}
    (hN : st.getNotification? notificationId = some ntfn)
    (hT : lookupTcb st waiter = some tcb)
    (hS1 : storeObject notificationId (.notification n') st = .ok ((), st1))
    (hS2 : storeTcbIpcStateAndMessage_fromTcb st1 waiter tcb s m = .ok st2)
    (hL : linkNtfnWaiter st2 waiter tail = .ok st3)
    (hCur : st.scheduler.currentOnCore c = some waiter) (hNI : isIdleThreadId waiter = false)
    (hI : n'.irqBound = ntfn.irqBound := by first | rfl | (simp_all; done))
    (hNW : n'.taintWords = ntfn.taintWords := by taint_words_kept) :
    SystemState.RunQueueEntryStage st (removeRunnableOnCore st3 waiter c) := by
  have hC1 : st1.scheduler.currentOnCore c = some waiter :=
    currentOnCore_of_scheduler_eq (storeObject_scheduler_eq _ _ _ _ hS1) hCur
  have hC3 : st3.scheduler.currentOnCore c = some waiter :=
    currentOnCore_of_scheduler_eq (linkNtfnWaiter_scheduler_eq hL)
      (currentOnCore_of_scheduler_eq (storeTcbIpcStateAndMessage_fromTcb_scheduler_eq hS2) hC1)
  have w : SystemState.RunQueueWindowStage (.block c) st st2 :=
    SystemState.RunQueueWindowStage.of_invExt fun hInv => by
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
        exact ((storeObject_notificationOver_runQueueStage hN hS1 hI hNW).window _).trans
          (SystemState.RunQueueWindowStage.storeObject_block hS
            ((SystemState.getTcb?_eq_some_iff st1 waiter tcb).mpr hT1) (fun _ => rfl) rfl hC1 hNI)
  exact (w.trans ((linkNtfnWaiter_runQueueStage hL).window _)).dispatch
    (SystemState.RunQueueDispatchStage.descheduleCurrent st3 c waiter hC3)

/-- The wait of core `c`'s current thread: a pending badge is taken with a
`.ready` mark; otherwise the waiter blocks. -/
theorem notificationWaitOnCore_runQueueEntryStage (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (c : Concurrency.CoreId) (st : SystemState)
    (hCur : st.scheduler.currentOnCore c = some waiter) (hNI : isIdleThreadId waiter = false) :
    SystemState.RunQueueEntryStage st (notificationWaitOnCore notificationId waiter c st).1 := by
  unfold notificationWaitOnCore
  repeat' (first | split | dsimp only)
  all_goals first
    | exact (RunQueueStage.refl _).entry
    | exact ((storeObject_notificationOver_runQueueStage (by assumption) (by assumption)).trans
         (storeTcbIpcState_runQueueStage (by assumption) rfl)).entry
    | exact notificationWait_block_runQueueEntryStage (by assumption) (by assumption)
         (by assumption) (by assumption) (by assumption) hCur hNI

macro_rules | `(tactic| run_queue_current_nowhere_step) => `(tactic|
  refine SystemState.currentNowhere.of_scheduler_eq
    (storeTcbIpcStateAndMessage_fromTcb_scheduler_eq (by with_reducible assumption)) ?_)
macro_rules | `(tactic| run_queue_current_nowhere_step) => `(tactic|
  exact blockedCurrentNowhere.blockedOnReply (by assumption) (by assumption) (by assumption))

/-- A thread blocked on a reply is blocked. -/
theorem blockedAt_of_blockedOnReply {st : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    {e : SeLe4n.ObjId} {r : Option SeLe4n.ThreadId} (hT : lookupTcb st t = some tcb)
    (hS : tcb.ipcState = .blockedOnReply e r) : blockedAt st t :=
  ⟨tcb, getTcb?_of_lookupTcb st t tcb hT, by rw [hS]; exact fun h => by cases h⟩

/-- The reply: the thread it wakes is blocked on the reply, which `hBlk` says is
current nowhere. -/
theorem endpointReplyOnCore_runQueueStage (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (c : Concurrency.CoreId) (st : SystemState) (hBlk : blockedCurrentNowhere st) :
    RunQueueStage st (endpointReplyOnCore replier target msg c st).1 := by
  unfold endpointReplyOnCore
  repeat' (first | split | dsimp only)
  all_goals first
    | exact RunQueueStage.refl _
    | (refine RunQueueStage.trans ?_ (SystemState.unlinkReplyWaiter_runQueueStage _ _ _)
       first
        | (refine (storeTcbIpcStateAndMessage_fromTcb_runQueueStage (by assumption)
              (by assumption) rfl).then_wake _ ?_
              (blockedAt_of_blockedOnReply (by assumption) (by assumption))
           run_queue_current_nowhere; done)
        | (refine ((storeTcbIpcStateAndMessage_fromTcb_runQueueStage (by assumption)
            (by assumption) rfl).then_wake _ ?_
              (blockedAt_of_blockedOnReply (by assumption) (by assumption))).trans
            (removeCallerReplyFrame_runQueueStage (by assumption))
           run_queue_current_nowhere; done))

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
    (msg : IpcMessage) (c : Concurrency.CoreId) (st : SystemState)
    (hBlk : blockedCurrentNowhere st) :
    RunQueueStage st (endpointReplyCrossCoreDispatch replier target msg c st).1 := by
  have hE := endpointReplyOnCore_runQueueStage replier target msg c st hBlk
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
    (st : SystemState) (hBlk : blockedCurrentNowhere st) :
    RunQueueStage st (endpointReplyCrossCoreDispatchChecked ctx replier target msg c st).1 := by
  unfold endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch_runQueueStage _ _ _ _ _ hBlk
  · exact RunQueueStage.refl _

/-- A reply dispatch that succeeds ran a reply that succeeded. -/
theorem endpointReplyCrossCoreDispatch_ok_reply {replier target : SeLe4n.ThreadId}
    {msg : IpcMessage} {c : Concurrency.CoreId} {st : SystemState}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (hOk : (endpointReplyCrossCoreDispatch replier target msg c st).2 = .ok sgi?) :
    ∃ s, (endpointReplyOnCore replier target msg c st).2 = .ok s := by
  unfold endpointReplyCrossCoreDispatch at hOk
  cases hRep : endpointReplyOnCore replier target msg c st with
  | mk st1 res =>
    rw [hRep] at hOk
    cases res with
    | error e => exact absurd hOk (by simp)
    | ok s => exact ⟨s, rfl⟩

/-- The decoded outcome: a restart writes the faulted thread's frame; an abandon
deschedules it where it is placed and marks it inactive, the reply having made
it ready (`hRdy`). -/
theorem faultReplyApplyOnCore_runQueueEntryStage (st : SystemState) (faulted : SeLe4n.ThreadId)
    (outcome : Architecture.FaultReplyOutcome)
    (hRdy : ∀ x, st.getTcb? faulted = some x → x.ipcState = .ready)
    (hNI : isIdleThreadId faulted = false) :
    SystemState.RunQueueEntryStage st (faultReplyApplyOnCore st faulted outcome) := by
  unfold faultReplyApplyOnCore
  split
  · exact (RunQueueStage.updateTcb (f := fun tcb => { tcb.withRestartFrame _ with pendingFault := none })
      _ _ (fun _ _ => rfl)).entry
  · unfold faultAbandonOnCore faultAbandonCore
    exact placedThenOffWrite_runQueueEntryStage st faulted _ (fun _ => hRdy) hNI
      (fun _ _ => rfl) (fun _ h => h)

/-- The fault reply: the reply chain wakes the faulted thread, blocked on the
reply and so no idle thread, then the decoded outcome. -/
theorem faultReplyOnCore_runQueueEntryStage (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (c : Concurrency.CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hD : st.currentDequeuedUnique) :
    SystemState.RunQueueEntryStage st (faultReplyOnCore replier faulted mi regs c st).1 := by
  have hE := endpointReplyCrossCoreDispatch_runQueueStage replier faulted IpcMessage.empty c st
    (blockedCurrentNowhere_of_currentDequeuedUnique hD)
  unfold faultReplyOnCore
  split
  · exact (RunQueueStage.refl _).entry
  split
  · exact (RunQueueStage.refl _).entry
  dsimp only
  split
  · exact (RunQueueStage.refl _).entry
  · rename_i stR sgi hR
    rw [hR] at hE
    obtain ⟨s, hOk⟩ := endpointReplyCrossCoreDispatch_ok_reply (by rw [hR])
    obtain ⟨-, tcb', ep, ex, -, hL, hS, -⟩ := endpointReplyOnCore_ok_decompose _ _ _ _ _ hOk
    exact hE.entry.trans (faultReplyApplyOnCore_runQueueEntryStage stR faulted _
      (fun x hx => endpointReplyCrossCoreDispatch_ok_target_ready replier faulted _ c st hInv
        (by rw [hR]) (by rw [hR]; exact hx))
      (notIdle_of_blocked hD (getTcb?_of_lookupTcb _ _ _ hL)
        (by rw [hS]; exact fun h => by cases h)))

theorem replyTransferOnCore_runQueueEntryStage {replier callerTid : SeLe4n.ThreadId}
    {mi : MessageInfo} {regs : Array SeLe4n.RegValue} {msg : IpcMessage}
    {c : Concurrency.CoreId} {st st' : SystemState}
    (hInv : st.objects.invExt) (hD : st.currentDequeuedUnique)
    (h : replyTransferOnCore replier callerTid mi regs msg c st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  have hF := faultReplyOnCore_runQueueEntryStage replier callerTid mi regs c st hInv hD
  have hE := endpointReplyCrossCoreDispatch_runQueueStage replier callerTid msg c st
    (blockedCurrentNowhere_of_currentDequeuedUnique hD)
  unfold replyTransferOnCore at h
  repeat' (first | split at h | dsimp only at h)
  all_goals first
    | (cases h; done)
    | (rename_i hR; cases h; rw [hR] at hF; exact hF)
    | (rename_i hR; cases h; rw [hR] at hE
       exact (hE.trans (stageDeliveredMessage_runQueueStage _ _ _)).entry)

theorem replyTransferOnCoreChecked_runQueueEntryStage {ctx : LabelingContext}
    {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {c : Concurrency.CoreId}
    {st st' : SystemState}
    (hInv : st.objects.invExt) (hD : st.currentDequeuedUnique)
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg c st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  have hF := faultReplyOnCore_runQueueEntryStage replier callerTid mi regs c st hInv hD
  have hE := endpointReplyCrossCoreDispatchChecked_runQueueStage ctx replier callerTid msg c st
    (blockedCurrentNowhere_of_currentDequeuedUnique hD)
  unfold replyTransferOnCoreChecked at h
  repeat' (first | split at h | dsimp only at h)
  all_goals first
    | (cases h; done)
    | (rename_i hR; cases h; rw [hR] at hF; exact hF)
    | (rename_i hR; cases h; rw [hR] at hE
       exact (hE.trans (stageDeliveredMessage_runQueueStage _ _ _)).entry)

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

/-- The reply keeps every current slot. -/
theorem endpointReplyOnCore_currentOnCore (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (c : Concurrency.CoreId) (st : SystemState) (c' : Concurrency.CoreId) :
    (endpointReplyOnCore replier target msg c st).1.scheduler.currentOnCore c' =
      st.scheduler.currentOnCore c' := by
  rcases endpointReplyOnCore_state_eq replier target msg c st with
    hEq | ⟨tcb, st1, server, pre, -, hStore, hPost, hTail⟩
  · rw [hEq]
  · rw [hPost, SchedulerState.currentOnCore, SystemState.unlinkReplyWaiter_scheduler,
      ← SchedulerState.currentOnCore]
    have hS1 := storeTcbIpcStateAndMessage_fromTcb_scheduler_eq hStore
    rcases hTail with ⟨-, hEq⟩ | ⟨rid, -, hR⟩
    · rw [hEq, wakeThread_state_eq_enqueue, enqueueRunnableOnCore_currentOnCore, hS1]
    · rw [removeCallerReplyFrame_scheduler_eq _ _ _ _ hR, wakeThread_state_eq_enqueue,
        enqueueRunnableOnCore_currentOnCore, hS1]

/-- A reply that succeeds keeps every endpoint head blocked: the one thread it
makes ready was blocked on the reply, so it heads no endpoint queue. -/
theorem endpointReplyOnCore_preserves_queueHeadBlockedConsistent (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (c : Concurrency.CoreId) (st : SystemState) (hInv : st.objects.invExt)
    (hQ : queueHeadBlockedConsistent st) {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (hOk : (endpointReplyOnCore replier target msg c st).2 = .ok sgi?) :
    queueHeadBlockedConsistent (endpointReplyOnCore replier target msg c st).1 := by
  obtain ⟨-, tcb0, e, ex, -, hL0, hS0, -⟩ := endpointReplyOnCore_ok_decompose _ _ _ _ _ hOk
  rcases endpointReplyOnCore_state_eq replier target msg c st with
    hEq | ⟨tcb, st1, server, pre, hL, hStore, hPost, hTail⟩
  · rw [hEq]; exact hQ
  · rw [hPost]
    refine queueHeadBlockedConsistent_of_readViewAgreement (.of_objectsAgreeOffRunLinks
      (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks _ _ _)) ?_
    obtain rfl : tcb0 = tcb := Option.some.inj (hL0.symm.trans hL)
    have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st1 := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hL]; exact hStore
    have hTo := lookupTcb_some_objects st target tcb0 hL
    have hQ1 := storeTcbIpcStateAndMessage_preserves_queueHeadBlockedConsistent st st1 target .ready
      (some msg) hQ hInv hStore' fun epId ep hEp => by
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have h' := (hQ epId ep target tcb0 hEp hTo).1 h
          rw [hS0] at h'; cases h'
        · rcases (hQ epId ep target tcb0 hEp hTo).2 h with h' | h' <;> rw [hS0] at h' <;> cases h'
    have hInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 target .ready
      (some msg) hInv hStore'
    obtain ⟨tr, hTrGet, hTrReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st1 target .ready (some msg) hInv hStore'
    have hQ2 := queueHeadBlockedConsistent_of_readViewAgreement (.of_objectsAgreeOffRunLinks
      (wakeThread_objectsAgreeOffRunLinks_of_ready st1 target c tr hTrGet hTrReady hInv1)) hQ1
    rcases hTail with ⟨-, hEq⟩ | ⟨rid, -, hR⟩
    · rw [hEq]; exact hQ2
    · exact removeCallerReplyFrame_preserves_queueHeadBlockedConsistent _ _ target rid
        (wakeThread_preserves_objects_invExt st1 target c hInv1) hQ2 hR

/-- The donation pop writes only scheduling-context bindings and replenishment
queues: it adds no endpoint, keeps every current slot and every IPC state. -/
theorem replyRecvPopDonation_frame {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {st st' : SystemState} {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (hInv : st.objects.invExt) (h : replyRecvPopDonation rid target st = .ok (r, st')) :
    (∀ (oid : SeLe4n.ObjId) (ep : Endpoint), st'.objects[oid]? = some (.endpoint ep) →
      st.objects[oid]? = some (.endpoint ep)) ∧
    (∀ c, st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) ∧
    (∀ (y : SeLe4n.ThreadId) (tcb' : TCB), st'.objects[y.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState) := by
  unfold replyRecvPopDonation at h
  repeat' (first | split at h | dsimp only at h)
  all_goals first
    | (cases h; exact ⟨fun _ _ h => h, fun _ => rfl, fun _ t h => ⟨t, h, rfl⟩⟩)
    | (cases h; done)
    | skip
  rename_i st1 hRet
  cases h
  refine ⟨fun oid ep hE => ?_, fun c' => ?_, fun t tcb' hT => ?_⟩
  · replace hE := (migrateSchedContextReplenishment_agree _ _ _ _).symm.get_of_not_sc
      (fun _ e => KernelObject.noConfusion e) hE
    exact returnDonatedSchedContextResolved_lift (P := fun s =>
      s.objects[oid]? = some (.endpoint ep) → st.objects[oid]? = some (.endpoint ep)) hRet
      (fun n s hS => returnDonatedSchedContext_endpoint_backward st s _ _ _ hInv n hS oid ep) hE
  · rw [(migrateSchedContextReplenishment_runQueue_current_eq _ _ _ _ c').2]
    exact returnDonatedSchedContextResolved_lift (P := fun s =>
      s.scheduler.currentOnCore c' = st.scheduler.currentOnCore c') hRet
      (fun n s hS => by
        show s.scheduler.currentOnCore c' = _
        rw [returnDonatedSchedContext_scheduler_eq st s _ _ _ n hS]; rfl)
  · replace hT := (migrateSchedContextReplenishment_agree _ _ _ _).symm.get_of_not_sc
      (fun _ e => KernelObject.noConfusion e) hT
    exact returnDonatedSchedContextResolved_lift (P := fun s =>
      s.objects[t.toObjId]? = some (.tcb tcb') →
        ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState)
      hRet (fun n s hS hT => by
        obtain ⟨tcb, h0, hS', -⟩ := returnDonatedSchedContext_tcb_ipcState_replyObject_backward
          st s _ _ _ hInv n hS t.toObjId tcb' hT
        exact ⟨tcb, h0, hS'⟩) hT

/-- `ReplyRecv`: the reply, the donation pop, then a receive on the same core by
the same current thread.  The reply and the pop keep every endpoint head
wakeable and the caller current, so the receive half is a kernel entry. -/
theorem endpointReplyRecvOnCore_runQueueEntryStage {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage}
    {root : SeLe4n.ObjId} {base : SeLe4n.Slot} {c : Concurrency.CoreId}
    {st st' : SystemState} {s : CapTransferSummary}
    (hInv : st.objects.invExt) (hD : st.currentDequeuedUnique) (hQ : queueHeadBlockedConsistent st)
    (hCur : st.scheduler.currentOnCore c = some tid) (hNI : isIdleThreadId tid = false)
    (h : endpointReplyRecvOnCore epId tid rid prevCaller msg root base c st = .ok (s, st')) :
    SystemState.RunQueueEntryStage st st' := by
  have hE := endpointReplyOnCore_runQueueStage tid prevCaller msg c st
    (blockedCurrentNowhere_of_currentDequeuedUnique hD)
  have hC1 : (endpointReplyOnCore tid prevCaller msg c st).1.scheduler.currentOnCore c = some tid :=
    (endpointReplyOnCore_currentOnCore tid prevCaller msg c st c).trans hCur
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt tid prevCaller msg c st hInv
  have hEB := endpointReplyOnCore_endpoint_backward tid prevCaller msg c st hInv
  have hCB := endpointReplyOnCore_currentOnCore tid prevCaller msg c st
  have hQ1 : ∀ sgi?, (endpointReplyOnCore tid prevCaller msg c st).2 = .ok sgi? →
      queueHeadBlockedConsistent (endpointReplyOnCore tid prevCaller msg c st).1 := fun _ hOk =>
    endpointReplyOnCore_preserves_queueHeadBlockedConsistent tid prevCaller msg c st hInv hQ hOk
  unfold endpointReplyRecvOnCore at h
  dsimp only at h
  generalize endpointReplyOnCore tid prevCaller msg c st = p at hE h hC1 hInv1 hEB hCB hQ1
  obtain ⟨st1, r⟩ := p
  dsimp only at hE hC1 hInv1 hEB hCB hQ1
  cases r with
  | error => cases h
  | ok sgi =>
  dsimp only at h
  have hH1 := (endpointHeadsWakeable_of hD hQ).of_frame hEB hCB (hQ1 _ rfl)
  split at h
  · cases h
  rename_i ret st1p hPop
  obtain ⟨hPE, hPC, hPT⟩ := replyRecvPopDonation_frame hInv1 hPop
  have hR := endpointReceiveDualWithCapsOnCore_runQueueEntryStage epId tid (some rid) root base c
    st1p (hH1.of_frame hPE hPC (queueHeadBlockedConsistent_of_endpoint_tcb_backward _ _ hPE hPT
      (hQ1 _ rfl))) ((hPC c).trans hC1) hNI
  generalize endpointReceiveDualWithCapsOnCore epId tid (some rid) root base c st1p = q at hR h
  obtain ⟨st2, r2⟩ := q
  dsimp only at hR
  rcases r2 with _ | ⟨nt, sm, _⟩ <;> dsimp only at h
  · cases h
  split at h
  · cases h
  rename_i st3 hPost
  cases h
  exact ((hE.trans (replyRecvPopDonation_runQueueStage hPop)).entry.trans hR).trans
    (((((replyRecvPostReceiveDonation_runQueueStage hPost).trans
    (applyReceiveLegPipHandoff_runQueueStage _ _ _ _ _)).trans
    (stageDeliveredMessage_runQueueStage _ _ _)).trans
    (stageWokenSendCompletion_runQueueStage _ _)).entry)

end SeLe4n.Kernel
