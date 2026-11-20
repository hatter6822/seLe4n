/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyInvariant
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatchInvariant
import SeLe4n.Kernel.IPC.Invariant.UnheldContextPop
import SeLe4n.Kernel.Capability.Invariant.Authority
import SeLe4n.Kernel.IPC.Invariant.Structural.DualQueueMembership

/-!
# The reply writes no notification and no binding

seL4-MCS's `handleReplyRecv` answers the caller (`doReplyTransfer`) and then
runs `receiveIPC`, whose first test is the receiver's bound notification: is it
active?  The model's reply-receive tests it on the entry state and runs the
reply then the completion (`replyRecvCompletesSignalArm`), so the two tests
must agree.  They do because the reply leg (`replyTransferOnCoreChecked`)
writes no notification and no binding code: every notification the pre-state
holds is in the post-state as it was, and every slot keeps its
bound-notification / bound-thread codes (`notificationsAndBindingsKept`).

Each step of the reply is a frame of this shape: the delivery store and the
reply-frame removal (`endpointReply`), the run-queue and release-queue writes
(objects agreeing off the scheduler links), the priority-inheritance revert,
the donated context's return, the capability transfer (CNode writes) and the
delivered message's frame (a TCB write).
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **Every notification kept, every binding code kept**: a notification the
pre-state holds is in the post-state unchanged, and every slot holds the
bound-notification / bound-thread codes it held. -/
def notificationsAndBindingsKept (st st' : SystemState) : Prop :=
  (∀ (oid : SeLe4n.ObjId) (n : Notification),
    st.objects[oid]? = some (.notification n) → st'.objects[oid]? = some (.notification n)) ∧
  sameNotificationBindings st st'

namespace notificationsAndBindingsKept

theorem refl (st : SystemState) : notificationsAndBindingsKept st st :=
  ⟨fun _ _ h => h, sameNotificationBindings.refl st⟩

theorem trans {a b c : SystemState} (h1 : notificationsAndBindingsKept a b)
    (h2 : notificationsAndBindingsKept b c) : notificationsAndBindingsKept a c :=
  ⟨fun oid n h => h2.1 oid n (h1.1 oid n h), h1.2.trans h2.2⟩

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    notificationsAndBindingsKept st st' :=
  ⟨fun _ _ hn => by rw [h]; exact hn, sameNotificationBindings.of_objects_eq h⟩

/-- A write whose every key is a kind-preserving write, and which creates no
notification content the pre-state did not hold. -/
theorem of_kindPreservingAt {st st' : SystemState}
    (hK : ∀ oid, kindPreservingWriteAt st st' oid)
    (hB : ∀ (oid : SeLe4n.ObjId) (n : Notification),
      st'.objects[oid]? = some (.notification n) → st.objects[oid]? = some (.notification n)) :
    notificationsAndBindingsKept st st' := by
  refine ⟨fun oid n hn => ?_, fun oid => ?_⟩
  · rcases hK oid with e | ⟨pre, post, hp, hq, ht, -, -, -, -, -, -⟩
    · rw [e]; exact hn
    · rw [hn] at hp; cases hp
      cases post <;> simp [KernelObject.objectType] at ht
      rename_i n'
      have := hB oid n' hq
      rw [hn] at this; cases this
      exact hq
  · rcases hK oid with e | ⟨pre, post, hp, hq, -, -, -, -, hb, -, -⟩
    · rw [e]
    · rw [hp, hq]; simp only [notificationBindingCodes, hb]

theorem of_kindPreservingWrite {st st' : SystemState} (hK : kindPreservingWrite st st')
    (hB : ∀ (oid : SeLe4n.ObjId) (n : Notification),
      st'.objects[oid]? = some (.notification n) → st.objects[oid]? = some (.notification n)) :
    notificationsAndBindingsKept st st' :=
  of_kindPreservingAt hK.objectsAt hB

/-- Objects agreeing off the scheduler links (run-queue links in a TCB, release
links in a context) hold the same notifications and the same codes. -/
theorem of_offSchedulerLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffSchedulerLinks st) : notificationsAndBindingsKept st st' :=
  of_kindPreservingAt h.kindPreservingAt (fun _ _ hn => h.get_notification_iff.mp hn)

theorem of_offRunLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffRunLinks st) : notificationsAndBindingsKept st st' :=
  of_offSchedulerLinks (.of_runLinks h)


open SeLe4n.Model.SystemState in
/-- The single-core reply: the delivery store, a link-only wake and the
reply-frame removal. -/
theorem of_endpointReply
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    notificationsAndBindingsKept st st' := by
  refine ⟨?_, sameNotificationBindings.of_kindPreservingWrite
    (endpointReply_kindPreservingWrite st st' replier target msg hObjInv hStep)⟩
  intro oid n hn
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      split at hStep
      · cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
        | error e => simp [hMsg] at hStep
        | ok st'' =>
          simp only [hMsg] at hStep
          have h1 := storeTcbIpcStateAndMessage_preserves_notification st st'' target .ready
            (some msg) oid n hObjInv hn hMsg
          have h2 : (ensureRunnable st'' target).objects[oid]? = some (.notification n) :=
            (of_offRunLinks (ensureRunnable_objectsAgreeOffRunLinks st'' target)).1 oid n h1
          have hObjInvMid : (ensureRunnable st'' target).objects.invExt := by
            apply ensureRunnable_objects_invExt
            exact storeTcbIpcStateAndMessage_preserves_objects_invExt st st'' target .ready
              (some msg) hObjInv hMsg
          cases hRO : tcb.replyObject with
          | none =>
            simp only [hRO, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
            rw [← hStep]
            exact (of_offRunLinks (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks
              _ _ _)).1 oid n h2
          | some rid =>
            simp only [hRO] at hStep
            obtain ⟨st2, hRm, rfl⟩ := removeCallerReplyFrame_unlink_ok hStep
            have h3 : st2.objects[oid]? = some (.notification n) :=
              (removeCallerReplyFrame_nonTcbNonReply_agree _ _ target rid hObjInvMid hRm oid
                (.notification n) (fun _ e => KernelObject.noConfusion e)
                (fun _ e => KernelObject.noConfusion e)).mpr h2
            exact (of_offRunLinks (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks
              _ _ _)).1 oid n h3
      · simp at hStep

/-- The cross-core reply leg: the single-core reply, with objects agreeing off
the scheduler links. -/
theorem of_endpointReplyOnCore
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    notificationsAndBindingsKept st (endpointReplyOnCore replier target msg c st).1 := by
  rcases endpointReplyOnCore_post_agrees replier target msg c st hObjInv with
    hEq | ⟨expected, r1, hR, hA⟩
  · rw [hEq]; exact refl st
  · exact (of_endpointReply st r1 expected target msg hObjInv hR).trans
      (of_offSchedulerLinks hA.objects)


/-- The priority-inheritance revert writes only threads' priorities and run links. -/
theorem of_propagatePipChainCrossCore (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (fuel : Nat) (hObjInv : st.objects.invExt) :
    notificationsAndBindingsKept st
      (PriorityInheritance.propagatePipChainCrossCore st tid c fuel).1 :=
  of_kindPreservingWrite (propagatePipChainCrossCore_kindPreservingWrite st tid c fuel hObjInv)
    (fun oid n h => PriorityInheritance.propagatePipChainCrossCore_notification_backward
      st tid c fuel hObjInv oid n h)

/-- The donated context's return, on each of its four arms. -/
theorem of_applyReplyDonationOnCore (st st' : SystemState) (rid : SeLe4n.ReplyId)
    (targetVtid : SeLe4n.ValidThreadId) (ownerHome : CoreId) (hObjInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st rid targetVtid ownerHome = .ok st') :
    notificationsAndBindingsKept st st' := by
  rcases applyReplyDonationOnCore_objects_frame st st' rid targetVtid ownerHome h with
    ⟨-, hEq⟩ | ⟨scId, n, s1, -, -, -, hRet, hA⟩ | ⟨scId, holder, n, s1, hRet, hA⟩ |
    ⟨scId, n, -, -, -, hSev⟩
  · exact of_objects_eq hEq
  · exact (of_kindPreservingWrite (returnUnheldSchedContext_kindPreservingWrite hObjInv hRet)
      (fun k nt hk => (returnUnheldSchedContext_notification_iff hObjInv hRet k nt).mp hk)).trans
      (of_offSchedulerLinks hA)
  · exact (of_kindPreservingWrite (returnDonatedSchedContext_kindPreservingWrite hObjInv hRet)
      (fun k nt hk => returnDonatedSchedContext_notification_backward _ _ _ _ _ hObjInv _ hRet
        k nt hk)).trans (of_offSchedulerLinks hA)
  · exact of_kindPreservingWrite (severUnheldSchedContext_kindPreservingWrite hObjInv hSev)
      (fun k nt hk => (severUnheldSchedContext_notification_iff hObjInv hSev k nt).mp hk)

/-- The cross-core reply dispatch: the reply leg, the donation return and the
priority-inheritance revert. -/
theorem of_endpointReplyCrossCoreDispatch
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    notificationsAndBindingsKept st (endpointReplyCrossCoreDispatch replier target msg c st).1 := by
  have hRep := of_endpointReplyOnCore replier target msg c st hObjInv
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt replier target msg c st hObjInv
  unfold endpointReplyCrossCoreDispatch
  cases hRepEq : endpointReplyOnCore replier target msg c st with
  | mk st1 res1 =>
      rw [hRepEq] at hRep hInv1
      simp only at hRep hInv1 ⊢
      cases res1 with
      | error e => exact refl st
      | ok replySgi? =>
          simp only
          split
          · split
            · split
              · exact hRep.trans (of_propagatePipChainCrossCore _ _ _ _ hInv1)
              · split
                · exact refl st
                · split
                  · exact refl st
                  · rename_i st2 hRet
                    exact (hRep.trans (of_applyReplyDonationOnCore _ _ _ _ _ hInv1 hRet)).trans
                      (of_propagatePipChainCrossCore _ _ _ _
                        (applyReplyDonationOnCore_preserves_objects_invExt _ _ _ _ _ hInv1 hRet))
            · exact refl st
          · split
            · exact hRep
            · split
              · exact refl st
              · split
                · exact refl st
                · rename_i st2 hRet
                  exact hRep.trans (of_applyReplyDonationOnCore _ _ _ _ _ hInv1 hRet)

theorem of_endpointReplyCrossCoreDispatchChecked (ctx : LabelingContext)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    notificationsAndBindingsKept st
      (endpointReplyCrossCoreDispatchChecked ctx replier target msg c st).1 := by
  unfold endpointReplyCrossCoreDispatchChecked
  split
  · exact of_endpointReplyCrossCoreDispatch replier target msg c st hObjInv
  · exact refl st

/-- A thread write keeps every notification (it writes a TCB slot only). -/
theorem notification_updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hObjInv : st.objects.invExt) (oid : SeLe4n.ObjId) (n : Notification)
    (hn : st.objects[oid]? = some (.notification n)) :
    (st.updateTcb tid f).objects[oid]? = some (.notification n) := by
  by_cases hEq : tid.toObjId = oid
  · subst hEq
    cases hT : st.getTcb? tid with
    | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact hn
    | some t =>
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT] at hn; cases hn
  · rw [SystemState.updateTcb_objects_ne _ _ _ _ hEq hObjInv]; exact hn


/-- The reply's capability transfer writes CNodes alone. -/
theorem of_replyTransferCaps (pre : SystemState) (replier caller : SeLe4n.ThreadId)
    (grant : Bool) {st st' : SystemState} {summary : CapTransferSummary}
    (hObjInv : st.objects.invExt)
    (h : replyTransferCaps pre replier caller grant st = .ok (summary, st')) :
    notificationsAndBindingsKept st st' := by
  unfold replyTransferCaps at h
  obtain ⟨stR, caps, hO, -, -, hOr⟩ := receiveTransferCaps_frame h
  have hR : notificationsAndBindingsKept st stR := of_objects_eq hO
  rcases hOr with rfl | ⟨rtcb, slot?, hU⟩
  · exact hR
  · have hInvR : stR.objects.invExt := hO ▸ hObjInv
    exact hR.trans ⟨fun oid n hn => ipcUnwrapCaps_preserves_ntfn_objects caps none rtcb slot?
        stR st' summary oid n hn hInvR hU,
      ipcUnwrapCaps_sameNotificationBindings caps none rtcb slot? stR st' summary hInvR hU⟩

/-- The delivered message's frame is a write of the answered thread's TCB. -/
theorem of_stageDeliveredMessage (st : SystemState) (tid : SeLe4n.ThreadId) (capInfo : Nat)
    (hObjInv : st.objects.invExt) :
    notificationsAndBindingsKept st (Architecture.stageDeliveredMessage st tid capInfo) := by
  refine ⟨fun oid n hn => ?_, sameNotificationBindings.of_kindPreservingWrite
    (Architecture.stageDeliveredMessage_kindPreservingWrite st tid capInfo hObjInv)⟩
  unfold Architecture.stageDeliveredMessage
  cases st.getTcb? tid with
  | none => exact hn
  | some tcb =>
    by_cases hReady : tcb.ipcState = .ready
    · simp only [hReady, if_pos]
      cases tcb.pendingMessage with
      | none => exact hn
      | some msg =>
        exact notification_updateTcb st tid _ hObjInv oid n hn
    · simp only [hReady, if_false]; exact hn

/-- The fault reply's outcome: the restart frame installed, or the thread
abandoned (descheduled and `.Inactive`). -/
theorem of_faultReplyApplyOnCore (st : SystemState) (faulted : SeLe4n.ThreadId)
    (o : Architecture.FaultReplyOutcome) (hObjInv : st.objects.invExt) :
    notificationsAndBindingsKept st (faultReplyApplyOnCore st faulted o) := by
  cases o with
  | restart frame =>
    exact ⟨fun oid n hn => notification_updateTcb st faulted _ hObjInv oid n hn,
      sameNotificationBindings.of_kindPreservingWrite
        (applyFaultRestart_kindPreservingWrite st faulted frame hObjInv)⟩
  | abandon =>
    refine ⟨fun oid n hn => ?_, sameNotificationBindings.of_kindPreservingWrite
      (faultAbandonOnCore_kindPreservingWrite st faulted _ hObjInv)⟩
    show (faultAbandonOnCore st faulted _).objects[oid]? = _
    unfold faultAbandonOnCore
    exact notification_updateTcb _ faulted _
      (removeRunnableOnCore_objects_invExt st faulted _ hObjInv) oid n
      ((of_offRunLinks (removeRunnableOnCore_objectsAgreeOffRunLinks st faulted _)).1 oid n hn)

theorem of_faultReplyOnCore (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (c : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    notificationsAndBindingsKept st (faultReplyOnCore replier faulted mi regs c st).1 := by
  have hE := of_endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty c st hObjInv
  have hI := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier faulted
    IpcMessage.empty c st hObjInv
  unfold faultReplyOnCore
  split
  · exact refl st
  split
  · exact refl st
  dsimp only
  split
  · exact refl st
  · rename_i stR sgi hR
    rw [hR] at hE hI
    exact hE.trans (of_faultReplyApplyOnCore _ _ _ hI)

/-- **The checked reply transfer writes no notification and no binding code**,
on both of its branches. -/
theorem of_replyTransferOnCoreChecked {ctx : LabelingContext}
    {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {grant : Bool} {c : CoreId}
    {st st' : SystemState} (hObjInv : st.objects.invExt)
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant c st = .ok ((), st')) :
    notificationsAndBindingsKept st st' := by
  unfold replyTransferOnCoreChecked at h
  split at h
  · have hF := of_faultReplyOnCore replier callerTid mi regs c st hObjInv
    revert h hF
    generalize faultReplyOnCore replier callerTid mi regs c st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h _; cases h
    | ok _ => intro h hF; cases h; exact hF
  · have hE := of_endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg c st hObjInv
    have hI : (endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg c st).1.objects.invExt := by
      unfold endpointReplyCrossCoreDispatchChecked
      split
      · exact endpointReplyCrossCoreDispatch_preserves_objects_invExt _ _ _ _ _ hObjInv
      · exact hObjInv
    revert h hE hI
    generalize endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg c st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h _ _; cases h
    | ok _ =>
      intro h hE hI
      simp only [] at h
      cases hX : replyTransferCaps st replier callerTid grant s with
      | error _ => rw [hX] at h; cases h
      | ok p =>
        obtain ⟨summary, sX⟩ := p
        rw [hX] at h
        cases h
        have hX' := of_replyTransferCaps st replier callerTid grant hI hX
        have hIX : sX.objects.invExt := by
          unfold replyTransferCaps at hX
          obtain ⟨stR, caps, hO, -, -, hOr⟩ := receiveTransferCaps_frame hX
          rcases hOr with rfl | ⟨rtcb, slot?, hU⟩
          · exact hO ▸ hI
          · exact ipcUnwrapCaps_preserves_objects_invExt caps none rtcb slot? stR sX summary
              (hO ▸ hI) hU
        exact (hE.trans hX').trans (of_stageDeliveredMessage _ _ _ hIX)

end notificationsAndBindingsKept

/-- WS-RR RR4.18: and the reply preserves the object-store invariant. -/
theorem faultReplyOnCore_preserves_objects_invExt
    (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (c : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    (faultReplyOnCore replier faulted mi regs c st).1.objects.invExt := by
  cases hTcb : st.getTcb? faulted with
  | none => simpa only [faultReplyOnCore, hTcb] using hObjInv
  | some tcb =>
      cases hFault : tcb.pendingFault with
      | none => simpa only [faultReplyOnCore, hTcb, hFault] using hObjInv
      | some tf =>
          have hRepObj := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier
            faulted IpcMessage.empty c st hObjInv
          rcases hStep : endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty c st
            with ⟨stR, res⟩
          rw [hStep] at hRepObj
          simp only at hRepObj
          cases res with
          | error e => simpa only [faultReplyOnCore, hTcb, hFault, hStep] using hObjInv
          | ok sgi? =>
              simp only [faultReplyOnCore, hTcb, hFault, hStep, faultReplyApplyOnCore]
              cases hOut : Architecture.decodeFaultReply tf.fault tf.context mi regs with
              | restart frame =>
                  simpa only [hOut] using
                    applyFaultRestart_preserves_objects_invExt stR faulted frame hRepObj
              | abandon =>
                  simpa only [hOut] using
                    faultAbandonOnCore_preserves_objects_invExt stR faulted
                      (faultAbandonCore stR faulted) hRepObj

end SeLe4n.Kernel
