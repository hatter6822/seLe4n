/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation
import SeLe4n.Kernel.IPC.Invariant.CancelAllFrame
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationNotificationShape
import SeLe4n.Kernel.IPC.Invariant.CancellationBundle

/-!
# The finalisation keeps the IPC invariants

WS-ZA ZA5.4 part 23: `finaliseFinalObject` cancels an endpoint's or a
notification's waiters and unbinds a notification before a final delete's
retire (`IPC/Operations/CancelAll.lean`).  This module proves that each cancel,
and so the whole finalisation, keeps the IPC bundle (`ipcInvariantFull`).

* **An endpoint waiter's cancel** is the pop of its queue's head
  (`endpointQueuePopHead`, which `storePopHead` is under the walk's guard), the
  receive-completing store with no message, the cancellation frame staged, and
  the wake of the now-`.ready` thread.  The pop leaves the bundle relaxed at the
  popped thread (`endpointQueuePopHead_establishes_ipcInvariantFullExceptMembership`),
  the store closes it (`storeTcbReceiveComplete_closes_exceptMembership`), the
  staging and the wake move nothing the bundle reads.
* **A notification waiter's cancel** is the cancellation's notification arm
  (`cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull`), its one
  premise the walk's own check that the waiter is in no endpoint queue, and
  the wake.
* **The unbind** is `unbindNotification` (`unbindNotification_of_inPlace`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The pop of a queue's head relaxes the bundle at the popped thread
-- ============================================================================

/-- A kind-preserving write keeps every scheduling context present. -/
theorem schedContext_fwd_of_kindPreservingWrite {st st' : SystemState}
    (h : kindPreservingWrite st st') {o : SeLe4n.ObjId} {sc : SeLe4n.Kernel.SchedContext}
    (hO : st.objects[o]? = some (.schedContext sc)) :
    ∃ sc', st'.objects[o]? = some (.schedContext sc') := by
  rcases h o with e | ⟨pre, post, hp, hq, ht, -⟩
  · exact ⟨sc, e.trans hO⟩
  · rw [hO] at hp; cases hp
    cases post <;> simp [KernelObject.objectType] at ht
    exact ⟨_, hq⟩

/-- **The pop of an endpoint queue's head takes the bundle to the bundle with
the membership conjunct relaxed at the popped thread** — the splice's
`endpointQueueRemoveDual_establishes_ipcInvariantFullExceptMembership` for the
head, conjunct by conjunct from the pop's own preservation theorems. -/
theorem endpointQueuePopHead_establishes_ipcInvariantFullExceptMembership
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (headTcb : TCB) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head = some tid)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb headTcb))
    (hInv : ipcInvariantFull st)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    ipcInvariantFullExceptMembership st' tid := by
  obtain ⟨hIpc, hDual, hBnd, hBadge, hPend, hNoDup, hMem, hQNB, hQHB, hTimeout,
    _hAcyc, hOwner, hPassive, hBudget, hReplyTarget, hReplyLink, hStash, hUnique, hTail,
    hQNT⟩ := hInv
  have hDual' := endpointQueuePopHead_preserves_dualQueueSystemInvariant endpointId isReceiveQ
    st st' tid hObjInv hStep hDual
  have hHeadBlocked : if isReceiveQ
      then headTcb.ipcState = .blockedOnReceive endpointId
      else headTcb.ipcState = .blockedOnSend endpointId ∨
           headTcb.ipcState = .blockedOnCall endpointId := by
    have hQ := hQHB endpointId ep tid headTcb hObj hTcb
    cases isReceiveQ
    · exact hQ.2 hHead
    · exact hQ.1 hHead
  have hSame := endpointQueuePopHead_sameSchedContextBindings endpointId isReceiveQ st st' tid
    headTcb hObjInv hStep
  have hOwner' : donationOwnerValid st' :=
    donationOwnerValid_of_frames hSame
      (endpointQueuePopHead_donationOwnerFrame endpointId isReceiveQ st st' tid headTcb hObjInv
        hStep) hOwner
  have hKind := endpointQueuePopHead_kindPreservingWrite hObjInv hStep
  have hTimeout' : blockedThreadTimeoutConsistent st' := by
    refine blockedThreadTimeoutConsistent_of_rewrites hTimeout (fun t tcb' scId hT hB => ?_)
      (fun o sc hO => schedContext_fwd_of_kindPreservingWrite hKind hO)
    obtain ⟨tcb, h0, hb⟩ := endpointQueuePopHead_timeoutBudgetFrame endpointId isReceiveQ st st'
      tid headTcb hObjInv hStep t tcb' hT
    obtain ⟨tcb2, h2, hi⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId isReceiveQ st
      st' tid t tcb' hObjInv hStep hT
    rw [h0] at h2; cases h2
    exact ⟨tcb, h0, hb.trans hB, hi⟩
  exact ⟨endpointQueuePopHead_preserves_ipcInvariant endpointId isReceiveQ st st' tid hIpc
      hObjInv hStep,
    hDual',
    endpointQueuePopHead_preserves_allPendingMessagesBounded endpointId isReceiveQ st st' tid
      headTcb hObjInv hStep hBnd,
    endpointQueuePopHead_preserves_badgeWellFormed endpointId isReceiveQ st st' tid headTcb
      hObjInv hStep hBadge,
    endpointQueuePopHead_preserves_blockedThreadsPendingMessageConsistent endpointId isReceiveQ
      st st' tid headTcb hObjInv hPend hStep,
    endpointQueuePopHead_preserves_endpointQueueNoDup endpointId isReceiveQ st st' tid headTcb
      hNoDup hDual hDual' hObjInv hStep,
    endpointQueuePopHead_preserves_ipcStateQueueMembershipConsistent_except_head endpointId
      isReceiveQ st st' tid headTcb ep hMem hObjInv hQNB hObj hHeadBlocked hStep,
    endpointQueuePopHead_preserves_queueNextBlockingConsistent endpointId isReceiveQ st st' tid
      headTcb hObjInv hQNB hStep,
    endpointQueuePopHead_preserves_queueHeadBlockedConsistent endpointId isReceiveQ st st' tid
      headTcb ep hObjInv hObj hQHB hQNT hStep,
    hTimeout',
    donationOwnerValid_implies_donationChainAcyclic st' hOwner',
    hOwner',
    passiveServerIdle_of_frame
      (endpointQueuePopHead_passiveServerIdleFrame endpointId isReceiveQ st st' tid headTcb
        hObjInv hStep) hPassive,
    donationBudgetTransfer_of_sameSchedContextBindings hSame hBudget,
    endpointQueuePopHead_preserves_blockedOnReplyHasTarget endpointId isReceiveQ st st' tid
      headTcb hObjInv hReplyTarget hStep,
    ⟨replyCallerLinkageReciprocal_of_frame
        (endpointQueuePopHead_replyLinkageFrame endpointId isReceiveQ st st' tid headTcb hObjInv
          hStep) hReplyLink.1,
      endpointQueuePopHead_preserves_blockedOnReplyHasReplyObject endpointId isReceiveQ st st'
        tid headTcb hObjInv hReplyLink.2 hStep⟩,
    endpointQueuePopHead_preserves_pendingReceiveReplyWellFormed endpointId isReceiveQ st st' tid
      headTcb hObjInv hStash hStep,
    donationOwnerUnique_of_sameSchedContextBindings hSame hUnique,
    endpointQueuePopHead_preserves_endpointQueueTailBlockedConsistent endpointId isReceiveQ st
      st' tid headTcb hObjInv hTail hStep,
    endpointQueuePopHead_preserves_queueNextTargetBlocked endpointId isReceiveQ st st' tid
      headTcb hObjInv hQNT hStep⟩

-- ============================================================================
-- §2  An endpoint waiter's cancel
-- ============================================================================

/-- What the walk's endpoint check admits. -/
theorem endpointWaiterCancellable_parts {st : SystemState} {endpointId : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} {tcb : TCB} (h : endpointWaiterCancellable st endpointId t tcb = true) :
    cancelledWaiterWakeable st t tcb = true ∧ tcb.timeoutBudget = none ∧
      sendWakesInPlace st endpointId t tcb.queueNext = true := by
  simp only [endpointWaiterCancellable, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **An endpoint waiter's cancel keeps the bundle.**  The pop relaxes it at the
waiter (`endpointQueuePopHead_establishes_ipcInvariantFullExceptMembership`) and
leaves the waiter out of every queue (`endpointQueuePopHead_popped_not_head`,
`_not_tail`, `_no_incoming`); the receive-completing store with no message closes
it (`storeTcbReceiveComplete_closes_exceptMembership`) — the waiter, a queue's
head, is blocked on a send, a call or a receive, so not on a reply, and the walk
admitted it with no timeout budget; the cancellation frame moves only its saved
registers (`writeReturnFrameToTcb_preserves_ipcInvariantFull`), and the one store
the cancel commits agrees with that two-store reading key by key; the wake is of
a `.ready` thread (`enqueueRunnableOnCore_preserves_ipcInvariantFull`). -/
theorem storeEndpointWaiterCancelled_preserves_ipcInvariantFull
    (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (ep : Endpoint)
    (t : SeLe4n.ThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hE : st.getEndpoint? endpointId = some ep)
    (hH : (endpointWaitQueue ep isReceiveQ).head = some t)
    (hT : st.getTcb? t = some tcb)
    (hC : endpointWaiterCancellable st endpointId t tcb = true) :
    ipcInvariantFull (storeEndpointWaiterCancelled st endpointId isReceiveQ t tcb.queueNext) := by
  obtain ⟨-, hNoBudget, hG⟩ := endpointWaiterCancellable_parts hC
  have hNotRes : ¬ t.isReserved := by
    simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
    simp [hG.1.1.1.1.1]
  have hEo := (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hE
  have hTo := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
  have hH' : (if isReceiveQ then ep.receiveQ else ep.sendQ).head = some t := hH
  obtain ⟨hPop, hFr⟩ := popHead_inPlace st endpointId isReceiveQ ep t tcb hEo hH' hTo hG
  unfold storeEndpointWaiterCancelled
  generalize storePopHead st endpointId isReceiveQ t tcb.queueNext = s1 at hPop hFr ⊢
  have hI1 : s1.objects.invExt :=
    endpointQueuePopHead_preserves_objects_invExt endpointId isReceiveQ st s1 t tcb hObjInv hPop
  have hEx := endpointQueuePopHead_establishes_ipcInvariantFullExceptMembership endpointId
    isReceiveQ st s1 t tcb ep hObjInv hEo hH' hTo hInv hPop
  have hNotHead := endpointQueuePopHead_popped_not_head endpointId isReceiveQ st s1 t tcb ep
    hObjInv hEo hInv.dualQueueSystemInvariant hInv.queueHeadBlockedConsistent hPop
  have hNotTail := endpointQueuePopHead_popped_not_tail endpointId isReceiveQ st s1 t tcb ep
    hObjInv hEo hInv.dualQueueSystemInvariant hInv.queueHeadBlockedConsistent
    hInv.endpointQueueTailBlockedConsistent hPop
  have hNoInc := endpointQueuePopHead_popped_no_incoming endpointId isReceiveQ st s1 t tcb
    hObjInv hInv.dualQueueSystemInvariant hPop
  have hT1 : s1.objects[t.toObjId]? = some (.tcb (tcbOffQueue tcb)) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hFr.head_tcb
  have hBlk : tcb.ipcState = .blockedOnReceive endpointId ∨
      tcb.ipcState = .blockedOnSend endpointId ∨ tcb.ipcState = .blockedOnCall endpointId := by
    have hQ := hInv.queueHeadBlockedConsistent endpointId ep t tcb hEo hTo
    cases isReceiveQ
    · exact Or.inr (hQ.2 (by simpa using hH'))
    · exact Or.inl (hQ.1 (by simpa using hH'))
  have hOffIpc : (tcbOffQueue tcb).ipcState = tcb.ipcState := rfl
  have hNotReply1 : ∀ (tcbX : TCB), s1.objects[t.toObjId]? = some (.tcb tcbX) →
      ∀ e r, tcbX.ipcState ≠ .blockedOnReply e r := by
    intro tcbX hX e r hEq
    rw [hT1] at hX; cases hX
    rw [hOffIpc] at hEq
    rcases hBlk with h | h | h <;> rw [h] at hEq <;> cases hEq
  -- The two-store reading: the receive completion, then the frame staged.
  let rc : TCB := TCB.setIpcState
    { tcbOffQueue tcb with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready
  obtain ⟨sRc, hStoreRc⟩ : ∃ s, storeObject t.toObjId (.tcb rc) s1 = .ok ((), s) := ⟨_, rfl⟩
  have hRc : storeTcbReceiveComplete s1 t none = .ok sRc := by
    unfold storeTcbReceiveComplete modifyTcb
    rw [lookupTcb_of_objects_of_not_reserved s1 t _ hT1 hNotRes]
    simp only []
    rw [hStoreRc]
  have hFullRc : ipcInvariantFull sRc :=
    storeTcbReceiveComplete_closes_exceptMembership s1 sRc t none hI1 (fun _ hm => by cases hm)
      (fun tcbX hX => by rw [hT1] at hX; cases hX; exact hNoBudget)
      hNotReply1 hNotHead hNotTail hNoInc hEx hRc
  have hIRc : sRc.objects.invExt :=
    storeObject_preserves_objects_invExt s1 sRc t.toObjId _ hI1 hStoreRc
  have hRcAt : sRc.objects[t.toObjId]? = some (.tcb rc) :=
    storeObject_objects_eq s1 sRc t.toObjId _ hI1 hStoreRc
  have hFullStage := writeReturnFrameToTcb_preserves_ipcInvariantFull sRc t
    Architecture.cancelledIpcFrame hIRc hFullRc
  have hRcG : sRc.getTcb? t = some rc := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hRcAt
  have hAgree : objectStoreAgrees (Architecture.writeReturnFrameToTcb sRc t
      Architecture.cancelledIpcFrame) (s1.updateTcb t cancelledEndpointWaiterTcb) := by
    intro k
    unfold Architecture.writeReturnFrameToTcb
    rw [SystemState.updateTcb_eq_of_some hFr.head_tcb, SystemState.updateTcb_eq_of_some hRcG]
    show (s1.objects.insert t.toObjId _)[k]? = (sRc.objects.insert t.toObjId _)[k]?
    by_cases hk : k = t.toObjId
    · subst hk
      rw [RHTable_getElem?_eq_get?, RHTable_getElem?_eq_get?,
        RobinHood.RHTable.getElem?_insert_self _ _ _ hI1,
        RobinHood.RHTable.getElem?_insert_self _ _ _ hIRc]
      rfl
    · have hne : (t.toObjId == k) = false := by simp [Ne.symm hk]
      rw [RHTable_getElem?_eq_get?, RHTable_getElem?_eq_get?,
        RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (by simp [hne]) hI1,
        RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (by simp [hne]) hIRc,
        ← RHTable_getElem?_eq_get?, ← RHTable_getElem?_eq_get?,
        storeObject_objects_ne s1 sRc t.toObjId k _ hk hI1 hStoreRc]
  have hSched : (s1.updateTcb t cancelledEndpointWaiterTcb).scheduler =
      (Architecture.writeReturnFrameToTcb sRc t Architecture.cancelledIpcFrame).scheduler := by
    unfold Architecture.writeReturnFrameToTcb
    rw [SystemState.updateTcb_eq_of_some hFr.head_tcb, SystemState.updateTcb_eq_of_some hRcG]
    exact (storeObject_scheduler_eq s1 sRc t.toObjId _ hStoreRc).symm
  have hFull2 := ipcInvariantFull_of_storeAgrees_of_scheduler_eq hAgree hSched hFullStage
  have hI2 : (s1.updateTcb t cancelledEndpointWaiterTcb).objects.invExt :=
    SystemState.updateTcb_preserves_objects_invExt _ _ _ hI1
  refine enqueueRunnableOnCore_preserves_ipcInvariantFull _ _ t hI2 (fun tcbX hX => ?_) hFull2
  rw [SystemState.updateTcb_getTcb?_self _ _ _ hI1, hFr.head_tcb] at hX
  cases hX
  exact TCB.ipcState_setIpcState { tcbOffQueue tcb with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready

-- ============================================================================
-- §3  A notification waiter's cancel, and the unbind
-- ============================================================================

/-- **A notification waiter's cancel keeps the bundle**: the cancellation's
notification arm (`cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull`),
whose one premise — the waiter is in no endpoint queue — the walk checked, then
the wake of the restored, `.ready` thread. -/
theorem notificationWaiterCancel_preserves_ipcInvariantFull
    (st : SystemState) (notificationId : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hT : st.getTcb? t = some tcb)
    (hC : notificationWaiterCancellable st notificationId t tcb = true) :
    ipcInvariantFull (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking st t tcb) t) := by
  obtain ⟨hNotRes, hB, hP, hN, -⟩ := notificationWaiterCancellable_parts hC
  have hTo := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
  have hLookup : lookupTcb st t = some tcb := lookupTcb_of_objects_of_not_reserved st t tcb hTo hNotRes
  have hOff : sweptThreadOffQueueChains st t := by
    intro tcbX hX; rw [hLookup] at hX; cases hX; exact ⟨hP, hN⟩
  have h1 := cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull st t tcb notificationId
    hObjInv hLookup hB hInv hOff
  have hI1 := (FinaliseFrame.notificationCancel st t tcb notificationId hObjInv hB).invExt
  refine enqueueRunnableOnCore_preserves_ipcInvariantFull _ _ t hI1 (fun tcbX hX => ?_) h1
  exact cancelIpcBlocking_victim_ready st t tcb hObjInv hLookup tcbX
    ((SystemState.getTcb?_eq_some_iff _ _ _).mp hX)

/-- **The unbind keeps the bundle**: it is `unbindNotification`
(`unbindNotification_of_inPlace`). -/
theorem storeUnbindNotification_preserves_ipcInvariantFull
    (st : SystemState) (notificationId : SeLe4n.ObjId) (t : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hCode : boundNotificationCodeOf st t = notificationId.val + 1)
    (hIn : unbindNotificationInPlace st t = true) :
    ipcInvariantFull (storeUnbindNotification st t notificationId) := by
  have hSpec := unbindNotification_of_inPlace st t hIn
  rw [hCode, Nat.add_sub_cancel] at hSpec
  exact unbindNotification_preserves_ipcInvariantFull _ _ _ hObjInv hInv hSpec

/-- **A context's release of its holder keeps the bundle**: the per-core unbind
read through the owner-cleared view
(`cancelBoundDonationOnCore_view_preserves_ipcInvariantFull`), on a thread whose
context — its own or on loan — is bound back to it and whose IPC state an
unbound thread may idle in.  The thread finalisation's unbind is the case of a
`.bound` holder (`FinaliseScReleaseStep.scUnbind`). -/
theorem finaliseScReleaseStep_keepsIpcInvariantFull :
    FinaliseScReleaseStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s s' t tcb sc x h hT hS hA hSc hB hOk
  refine ⟨cancelBoundDonationOnCore_view_preserves_ipcInvariantFull s s' t tcb _ _ h.2 h.1
    ((SystemState.getTcb?_eq_some_iff s t tcb).mp hT) (passiveServerIdleAllowed_of_codes hA)
    (fun scId hb => ?_) hOk, (FinaliseFrame.cancelBoundDonationOnCore h.2 hOk).invExt⟩
  rw [schedContextBinding_ownerCleared hS] at hb
  cases hb
  refine ⟨sc, (SystemState.getSchedContext?_eq_some_iff s _ sc).mp hSc, ?_⟩
  unfold SchedContext.boundThread; rw [hB]; exact threadOfOptCode_succ t

/-- **A context's deschedule of its holder keeps the bundle**: the holder idles
in no IPC state (codes `0`/`0`), so it is `.ready` and the dequeue
(`descheduleAt_preserves_ipcInvariantFull`) applies. -/
theorem finaliseScDescheduleStep_keepsIpcInvariantFull :
    FinaliseScDescheduleStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s t tcb h hT hS hO _
  have hReady : ∀ x : TCB, s.getTcb? t = some x → x.ipcState = .ready := by
    intro x hx; rw [hT] at hx; cases hx
    unfold TCB.ipcState; rw [hS, hO]; rfl
  exact ⟨descheduleAt_preserves_ipcInvariantFull s t _ hReady h.1,
    (FinaliseFrame.descheduleAt s t _ h.2).invExt⟩

/-- **A context's reply-stack unlink keeps the bundle**: the head reply's
upward link is a stack link, not its caller
(`storeObject_reply_stackLinks_preserves_ipcInvariantFull`), and the context's
head is content the bundle does not read
(`insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull`). -/
theorem finaliseUnstackStep_keepsIpcInvariantFull :
    FinaliseUnstackStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s s1 x _ rid r h _ _ hR _ hS
  have h1 := storeObject_reply_stackLinks_preserves_ipcInvariantFull (a' := { r with next := none }) h.2 h.1 hR
    rfl hS
  have hI1 := storeObject_preserves_objects_invExt s s1 _ _ h.2 hS
  cases hG : s1.getSchedContext? ⟨x.val⟩ with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hG]; exact ⟨h1, hI1⟩
  | some y =>
    rw [SystemState.updateSchedContext_eq_of_some hG]
    exact ⟨insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull s1 _ y _ hI1 h1
      ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hG) rfl,
      RHTable_insert_preserves_invExt _ _ _ hI1⟩

/-- **A thread's stash cleared in place keeps the bundle**: the in-place rewrite
agrees, object for object and on the scheduler, with the store of the cleared
thread (`storeObject_stashCleared_preserves_ipcInvariantFull`). -/
theorem updateTcb_stashCleared_preserves_ipcInvariantFull (s : SystemState)
    (tid : SeLe4n.ThreadId) (t : TCB) (hInv : s.objects.invExt) (hFull : ipcInvariantFull s)
    (hT : s.getTcb? tid = some t) :
    ipcInvariantFull (s.updateTcb tid TCB.stashCleared) := by
  obtain ⟨s1, hS⟩ : ∃ s1, storeObject tid.toObjId (.tcb (TCB.stashCleared t)) s = .ok ((), s1) :=
    ⟨_, rfl⟩
  have h1 := storeObject_stashCleared_preserves_ipcInvariantFull s s1 tid t hInv hFull hT hS
  rw [SystemState.updateTcb_eq_of_some hT]
  refine ipcInvariantFull_of_storeAgrees_of_scheduler_eq (fun k => ?_)
    (storeObject_scheduler_eq s s1 _ _ hS).symm h1
  show (s.objects.insert tid.toObjId _)[k]? = s1.objects[k]?
  by_cases hk : k = tid.toObjId
  · subst hk
    rw [storeObject_objects_eq s s1 _ _ hInv hS, RHTable_getElem?_eq_get?,
      RobinHood.RHTable.getElem?_insert_self _ _ _ hInv]
  · have hne : (tid.toObjId == k) = false := by simp [Ne.symm hk]
    rw [storeObject_objects_ne s s1 _ k _ hk hInv hS, RHTable_getElem?_eq_get?,
      RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (by simp [hne]) hInv,
      ← RHTable_getElem?_eq_get?]

/-- **A stashed reply's unlink keeps the bundle**: the receiver's stash cleared
in its slot (`updateTcb_stashCleared_preserves_ipcInvariantFull`). -/
theorem finaliseUnstashStep_keepsIpcInvariantFull :
    FinaliseUnstashStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s s1 _ tid t h hT _ e
  subst e
  exact ⟨updateTcb_stashCleared_preserves_ipcInvariantFull s tid t h.2 h.1 hT,
    SystemState.updateTcb_preserves_objects_invExt _ _ _ h.2⟩

/-- **A reply's caller cancel keeps the bundle**: the reply arm of the cancel
with no donation to return — the splice
(`spliceThreadReplyFrameOut_preserves_ipcInvariantFull`), the restore and
teardown pair (`restoredAndConsumed_preserves_ipcInvariantFull`, at a caller
holding no timeout budget, linked into no queue and lending to no thread) — then
the revert of the boost it lent its server
(`propagatePipChainCrossCore_preserves_ipcInvariantFull`). -/
theorem finaliseReplyStep_keepsIpcInvariantFull :
    FinaliseReplyStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s x r c t h hX hC hT hF
  obtain ⟨-, hNotRes, -, -, ⟨ep, rt, hB⟩, -, hN, hP, hBud, hNoLoan, hD⟩ :=
    replyCallerFinalisable_parts hX hC hF
  have hTo := (SystemState.getTcb?_eq_some_iff s c t).mp hT
  have hRet : Lifecycle.Suspend.returnDonationToCancelledCaller s c t = s := by
    unfold Lifecycle.Suspend.returnDonationToCancelledCaller; rw [hD]
  have hEq := cancelIpcBlocking_reply_arm_eq s c t ep rt hB
  rw [hRet] at hEq
  have hInvS := spliceThreadReplyFrameOut_preserves_objects_invExt s t h.2
  have hBundleS := spliceThreadReplyFrameOut_preserves_ipcInvariantFull s t h.2 h.1
  have hAtS := spliceThreadReplyFrameOut_tcb_eq s t h.2 c.toObjId t hTo
  have hLkS : lookupTcb (spliceThreadReplyFrameOut s t) c = some t :=
    lookupTcb_of_objects_of_not_reserved _ c t hAtS hNotRes
  have hOffS : sweptThreadOffQueueChains (spliceThreadReplyFrameOut s t) c := by
    intro tcbX hX; rw [hLkS] at hX; cases hX; exact ⟨hP, hN⟩
  have h1 : ipcInvariantFull (Lifecycle.Suspend.cancelIpcBlocking s c t) := by
    rw [hEq]
    exact restoredAndConsumed_preserves_ipcInvariantFull _ c t _ ep rt hInvS hLkS hB hBundleS hBud
      hOffS (fun tid tcb scId hA => hNoLoan tid tcb scId
        (spliceThreadReplyFrameOut_tcb_backward s t h.2 tid.toObjId tcb hA))
  have hI1 := (FinaliseFrameAny.replyCancel s c t h.2 hB hD).invExt
  cases hSv : t.blockingServer? with
  | none => exact ⟨h1, hI1⟩
  | some sv =>
    exact ⟨propagatePipChainCrossCore_preserves_ipcInvariantFull _ sv _ _ hI1 h1,
      (FinaliseFrame.propagatePip _ sv _ _ hI1).invExt⟩

/-- **A thread's notification cancel, without the wake, keeps the bundle**
(`cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull`). -/
theorem finaliseCancelStep_keepsIpcInvariantFull :
    FinaliseCancelStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s n t tcb _ h hT hI _ _ hC
  obtain ⟨hNotRes, -, hP, hN, -⟩ := notificationWaiterCancellable_parts hC
  have hTo := (SystemState.getTcb?_eq_some_iff s t tcb).mp hT
  have hLookup : lookupTcb s t = some tcb := lookupTcb_of_objects_of_not_reserved s t tcb hTo hNotRes
  have hOff : sweptThreadOffQueueChains s t := by
    intro tcbX hX; rw [hLookup] at hX; cases hX; exact ⟨hP, hN⟩
  exact ⟨cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull s t tcb n h.2 hLookup hI h.1
    hOff, (FinaliseFrame.notificationCancel s t tcb n h.2 hI).invExt⟩

/-- **The suspend's mark keeps the bundle**: `threadState` is a field the
bundle does not read (`insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull`). -/
theorem inactiveMark_keepsIpcInvariantFull (s : SystemState) (t : SeLe4n.ThreadId)
    (h : ipcInvariantFull s ∧ s.objects.invExt) :
    ipcInvariantFull (s.updateTcb t (fun t => { t with threadState := .Inactive })) ∧
      (s.updateTcb t (fun t => { t with threadState := .Inactive })).objects.invExt := by
  cases hT : s.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact h
  | some tcb =>
    rw [SystemState.updateTcb_eq_of_some hT]
    exact ⟨insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull s t tcb
      { tcb with threadState := .Inactive } h.2 h.1 ((SystemState.getTcb?_eq_some_iff s t tcb).mp hT)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl, RHTable_insert_preserves_invExt _ _ _ h.2⟩

/-- **The suspend keeps the bundle**: the deschedule of a ready thread
(`descheduleAt_preserves_ipcInvariantFull`), then the `.Inactive` mark. -/
theorem finaliseSuspendStep_keepsIpcInvariantFull :
    FinaliseSuspendStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s t tcb h hT hS hO _ _
  have hReady : ∀ x : TCB, s.getTcb? t = some x → x.ipcState = .ready := by
    intro x hx; rw [hT] at hx; cases hx
    unfold TCB.ipcState; rw [hS, hO]; rfl
  exact inactiveMark_keepsIpcInvariantFull _ t
    ⟨descheduleAt_preserves_ipcInvariantFull s t _ hReady h.1,
      (FinaliseFrame.descheduleAt s t _ h.2).invExt⟩

/-- **The release keeps the bundle**: it writes neither the objects nor the
scheduler. -/
theorem finaliseReleaseStep_keepsIpcInvariantFull :
    FinaliseReleaseStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s t h
  refine ⟨ipcInvariantFull_of_storeAgrees_of_scheduler_eq (fun k => ?_)
    (finaliseThreadReleaseCores_scheduler s t) h.1, (FinaliseFrame.releaseCores s t h.2).invExt⟩
  rw [finaliseThreadReleaseCores_objects]

-- ============================================================================
-- §4  The finalisation
-- ============================================================================

/-- **The finalisation keeps the IPC bundle**, every step of it
(`finaliseFinalObject_closed`), with the object table's well-formedness carried
alongside. -/
theorem finaliseFinalObject_preserves_ipcInvariantFull (target : Nat) (st : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (finaliseFinalObject target st) :=
  (finaliseFinalObject_closed (fun s => ipcInvariantFull s ∧ s.objects.invExt)
    (fun e q s ep t tcb h hE hH hT hC =>
      ⟨storeEndpointWaiterCancelled_preserves_ipcInvariantFull s e q ep t tcb h.2 h.1 hE hH hT hC,
        (FinaliseFrame.storeEndpointWaiterCancelled s e q t _ h.2).invExt⟩)
    (fun n s _ t tcb h _ _ hT hC =>
      ⟨notificationWaiterCancel_preserves_ipcInvariantFull s n t tcb h.2 h.1 hT hC,
        ((FinaliseFrame.notificationCancel s t tcb n h.2
          (notificationWaiterCancellable_blocked hC)).trans
          (FinaliseFrame.wakeCancelledWaiter _ t
            (FinaliseFrame.notificationCancel s t tcb n h.2
              (notificationWaiterCancellable_blocked hC)).invExt)).invExt⟩)
    (fun n s _ t h _ _ hCode hIn =>
      ⟨storeUnbindNotification_preserves_ipcInvariantFull s n t h.2 h.1 hCode hIn,
        (FinaliseFrame.storeUnbindNotification s t n h.2).invExt⟩)
    finaliseScDescheduleStep_keepsIpcInvariantFull
    finaliseScReleaseStep_keepsIpcInvariantFull finaliseCancelStep_keepsIpcInvariantFull
    finaliseSuspendStep_keepsIpcInvariantFull finaliseReleaseStep_keepsIpcInvariantFull
    finaliseUnstackStep_keepsIpcInvariantFull finaliseReplyStep_keepsIpcInvariantFull
    finaliseUnstashStep_keepsIpcInvariantFull
    target st ⟨hInv, hObjInv⟩).1

/-- **The retire after the finalisation keeps the IPC bundle**: the
finalisation's (`finaliseFinalObject_preserves_ipcInvariantFull`), then the
retire's (`retireFinalObject_preserves_ipcInvariantFull`). -/
theorem retireFinalisedObject_preserves_ipcInvariantFull (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (retireFinalisedObject ec target recorder st) ∧
      (retireFinalisedObject ec target recorder st).objects.invExt :=
  retireFinalObject_preserves_ipcInvariantFull ec target recorder _
    (finaliseFinalObject_frame target st hObjInv).invExt
    (finaliseFinalObject_preserves_ipcInvariantFull target st hObjInv hInv)

-- ============================================================================
-- §5  The finalising delete and revocation
-- ============================================================================

/-- `.cspaceDelete`: the finalising delete preserves the bundle — the delete's
own theorem, then the teardown's, then the finalisation's and the retire's. -/
theorem cspaceDeleteSlotFinalising_preserves_ipcInvariantFull
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' hStep
  have h2 := finaliseDestroyedCapabilities_preserves_ipcInvariantFull ec _ _ st1 st2
    (cspaceDeleteSlot_preserves_objects_invExt st st1 addr hObjInv hD)
    (cspaceDeleteSlot_preserves_ipcInvariantFull st st1 addr hObjInv hInv hD) hF
  exact (retireFinalisedObject_preserves_ipcInvariantFull ec _ _ st2 h2.2 h2.1).1

/-- `.cspaceRevoke`: the finalising revocation preserves the bundle — the
revocation's own theorem at the state it reaches, then the teardown's. -/
theorem cspaceRevokeCdtFinalising_preserves_ipcInvariantFull
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  refine (cspaceRevokeCdtFinalising_closed (fun s => ipcInvariantFull s ∧ s.objects.invExt)
    (fun c s s' hQ hD => ⟨cspaceDeleteSlotFinalising_preserves_ipcInvariantFull ec c s s'
      hQ.2 hQ.1 hD, cspaceDeleteSlotFinalising_preserves_objects_invExt ec c s s' hQ.2 hD⟩)
    ⟨hInv, hObjInv⟩ hStep).1


end SeLe4n.Kernel
