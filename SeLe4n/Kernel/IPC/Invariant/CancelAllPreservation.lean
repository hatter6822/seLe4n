/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation
import SeLe4n.Kernel.IPC.Invariant.CancelAllFrame
import SeLe4n.Kernel.IPC.Invariant.FinaliseLoanCoherence
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
    _hAcyc, hOwner, hBudget, hReplyTarget, hReplyLink, hStash, hUnique, hTail,
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

/-- **A detached waiter whose IPC is ended closes the bundle**: a thread `t`,
held at `x`, that heads, ends and follows nothing in any endpoint queue, holds
no timeout budget and is blocked on no reply, made a cancelled waiter
(`cancelledEndpointWaiterTcb`), takes the bundle with membership relaxed at `t`
to the bundle.  Read as two stores — the receive completion with no message,
which closes the bundle (`storeTcbReceiveComplete_closes_exceptMembership`),
then the cancellation frame staged, which moves only saved registers
(`writeReturnFrameToTcb_preserves_ipcInvariantFull`) — that agree key by key
with the one store the cancel commits. -/
theorem cancelledEndpointWaiter_closes (s1 : SystemState) (t : SeLe4n.ThreadId) (x : TCB)
    (hI1 : s1.objects.invExt) (hNotRes : ¬ t.isReserved)
    (hT1 : s1.objects[t.toObjId]? = some (.tcb x)) (hNoBudget : x.timeoutBudget = none)
    (hNotReply : ∀ e r, x.ipcState ≠ .blockedOnReply e r)
    (hNotHead : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint), s1.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.head ≠ some t ∧ ep.sendQ.head ≠ some t)
    (hNotTail : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint), s1.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.tail ≠ some t ∧ ep.sendQ.tail ≠ some t)
    (hNoInc : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
      s1.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some t)
    (hEx : ipcInvariantFullExceptMembership s1 t) :
    ipcInvariantFull (s1.updateTcb t cancelledEndpointWaiterTcb) := by
  have hG1 : s1.getTcb? t = some x := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT1
  have hNotReply1 : ∀ (tcbX : TCB), s1.objects[t.toObjId]? = some (.tcb tcbX) →
      ∀ e r, tcbX.ipcState ≠ .blockedOnReply e r := by
    intro tcbX hX e r
    rw [hT1] at hX; cases hX
    exact hNotReply e r
  -- The two-store reading: the receive completion, then the frame staged.
  let rc : TCB := TCB.setIpcState
    { x with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready
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
    rw [SystemState.updateTcb_eq_of_some hG1, SystemState.updateTcb_eq_of_some hRcG]
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
  exact ipcInvariantFull_of_storeAgrees hAgree hFullStage

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
  have hFull2 := cancelledEndpointWaiter_closes s1 t (tcbOffQueue tcb) hI1 hNotRes hT1 hNoBudget
    (fun e r hEq => by rcases hBlk with h | h | h <;> rw [show (tcbOffQueue tcb).ipcState =
      tcb.ipcState from rfl, h] at hEq <;> cases hEq)
    hNotHead hNotTail hNoInc hEx
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
context — its own or on loan — is bound back to it.  The thread finalisation's unbind is the case of a
`.bound` holder (`FinaliseScReleaseStep.scUnbind`). -/
theorem finaliseScReleaseStep_keepsIpcInvariantFull :
    FinaliseScReleaseStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s s' t tcb sc x h hT hS hSc hB hOk
  refine ⟨cancelBoundDonationOnCore_view_preserves_ipcInvariantFull s s' t tcb _ _ h.2 h.1
    ((SystemState.getTcb?_eq_some_iff s t tcb).mp hT)
    (fun scId hb => ?_) hOk, (FinaliseFrame.cancelBoundDonationOnCore h.2 hOk).invExt⟩
  rw [schedContextBinding_ownerCleared hS] at hb
  cases hb
  refine ⟨sc, (SystemState.getSchedContext?_eq_some_iff s _ sc).mp hSc, ?_⟩
  unfold SchedContext.boundThread; rw [hB]; exact threadOfOptCode_succ t

/-- **A context's deschedule of its holder keeps the bundle**: the dequeue
(`descheduleAt_preserves_ipcInvariantFull`) writes only run-queue links. -/
theorem finaliseScDescheduleStep_keepsIpcInvariantFull :
    FinaliseScDescheduleStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s t _ h _ _ _ _
  exact ⟨descheduleAt_preserves_ipcInvariantFull s t _ h.1,
    (FinaliseFrame.descheduleAt s t _ h.2).invExt⟩

/-- **A context's reply-stack unlink keeps the bundle**: the head reply's
upward link is a stack link, not its caller
(`storeObject_reply_stackLinks_preserves_ipcInvariantFull`), and the context's
head is content the bundle does not read
(`insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull`). -/
theorem finaliseUnstackStep_keepsIpcInvariantFull :
    FinaliseUnstackStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s s1 x _ rid r h _ _ hR _ hS _ _ _ _
  have h1 := storeObject_reply_stackLinks_preserves_ipcInvariantFull (a' := { r with next := none }) h.2 h.1 hR
    rfl rfl hS
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
  refine ipcInvariantFull_of_storeAgrees (fun k => ?_) h1
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

/-- **The bundle the finalising delete carries**: the IPC bundle, the object
table's well-formedness, and the delete's stated lent-context fact
(`lentContextHeadsLenderFrame`), which the reply cancel reads. -/
def finaliseLoanBundle (s : SystemState) : Prop :=
  ipcInvariantFull s ∧ s.objects.invExt ∧ lentContextHeadsLenderFrame s

/-- **A reply's caller cancel keeps the bundle**: the reply arm of the cancel
with no donation to return — the splice
(`spliceThreadReplyFrameOut_preserves_ipcInvariantFull`), the restore and
teardown pair (`restoredAndConsumed_preserves_ipcInvariantFull`, at a caller
holding no timeout budget, linked into no queue and lending to no thread, which
the lent-context fact gives: `replyCaller_lendsNone`) — then the revert of the
boost it lent its server (`propagatePipChainCrossCore_preserves_ipcInvariantFull`);
and the fact itself (`finaliseReplyStep_keepsLentContextHeads`). -/
theorem finaliseReplyStep_keepsIpcInvariantFull : FinaliseReplyStep finaliseLoanBundle := by
  intro s x r c t h hX _ hT hF
  obtain ⟨hHd, hNotRes, -, -, ⟨ep, rt, hB⟩, hRO, hN, hP, hBud, hD⟩ :=
    replyCallerFinalisable_parts hX hF
  have hNoLoan := replyCaller_lendsNone h.2.2 hX hT hHd hRO
  have hW' := finaliseReplyStep_keepsLentContextHeads h.2.1 h.2.2 hX hT hF
  replace h : ipcInvariantFull s ∧ s.objects.invExt := ⟨h.1, h.2.1⟩
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
  revert hW'
  cases hSv : t.blockingServer? with
  | none => exact fun hW' => ⟨h1, hI1, hW'⟩
  | some sv =>
    exact fun hW' => ⟨propagatePipChainCrossCore_preserves_ipcInvariantFull _ sv _ _ hI1 h1,
      (FinaliseFrame.propagatePip _ sv _ _ hI1).invExt, hW'⟩

/-- **A thread's notification cancel, without the wake, keeps the bundle**
(`cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull`), wherever the
thread waits in the queue. -/
theorem finaliseNotificationCancelStep_keepsIpcInvariantFull :
    FinaliseNotificationCancelStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s n t tcb _ h hT hI _ hC
  obtain ⟨hNotRes, -, hP, hN, -⟩ := notificationWaiterCancellable_parts hC
  have hTo := (SystemState.getTcb?_eq_some_iff s t tcb).mp hT
  have hLookup : lookupTcb s t = some tcb := lookupTcb_of_objects_of_not_reserved s t tcb hTo hNotRes
  have hOff : sweptThreadOffQueueChains s t := by
    intro tcbX hX; rw [hLookup] at hX; cases hX; exact ⟨hP, hN⟩
  exact ⟨cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull s t tcb n h.2 hLookup hI h.1
    hOff, (FinaliseFrame.notificationCancel s t tcb n h.2 hI).invExt⟩

-- ============================================================================
-- §4  A thread's endpoint cancel
-- ============================================================================

/-- What the endpoint cancel's check admits. -/
theorem endpointBlockedCancellable_parts {st : SystemState} {e : SeLe4n.ObjId} {q : Bool}
    {t : SeLe4n.ThreadId} {ep : Endpoint} {tcb : TCB}
    (h : endpointBlockedCancellable st e q t ep tcb = true) :
    blockedOnQueueSide q e tcb = true ∧ tcb.timeoutBudget = none ∧
      queueRemoveInPlace st e q t ep tcb = true ∧
      (∀ p, tcb.queueNext = none → tcb.queuePPrev = some (.tcbNext p) →
        ∀ pt, st.getTcb? p = some pt → blockedOnQueueSide q e pt = true) := by
  simp only [endpointBlockedCancellable, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun p hN hP pt hpt => ?_⟩
  rw [hN, hP] at h4; simp only [hpt] at h4; exact h4

/-- **The removal detaches the removed thread**, on either side: no endpoint's
queue starts or ends at it and no thread links to it — the receive side's
`endpointQueueRemoveDual_removed_detached`, and the send side's from the same
three facts. -/
theorem endpointQueueRemoveDual_removed_detached_side
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hDual : dualQueueSystemInvariant st)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (tcbPost : TCB) (hTid : st'.objects[tid.toObjId]? = some (.tcb tcbPost))
    (hState : spliceSideBlocked isReceiveQ endpointId tcbPost.ipcState)
    (hQHB : queueHeadBlockedConsistent st') (hQTB : endpointQueueTailBlockedConsistent st')
    (hLink : tcbQueueLinkIntegrity st') :
    (∀ (e : SeLe4n.ObjId) (ep : Endpoint), st'.objects[e]? = some (.endpoint ep) →
        ep.receiveQ.head ≠ some tid ∧ ep.sendQ.head ≠ some tid) ∧
    (∀ (e : SeLe4n.ObjId) (ep : Endpoint), st'.objects[e]? = some (.endpoint ep) →
        ep.receiveQ.tail ≠ some tid ∧ ep.sendQ.tail ≠ some tid) ∧
    (∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
        st'.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some tid) := by
  cases isReceiveQ with
  | true =>
    exact endpointQueueRemoveDual_removed_detached st st' endpointId tid hObjInv hDual hStep
      tcbPost hTid (hState.1 rfl) hQHB hQTB hLink
  | false =>
    have hS := hState.2 rfl
    have hB := endpointQueueRemoveDual_removed_not_boundary st st' endpointId false tid hObjInv
      hDual hStep
    have hSame : ∀ e, (tcbPost.ipcState = .blockedOnSend e ∨ tcbPost.ipcState = .blockedOnCall e) →
        endpointId = e := by
      intro e he
      rcases hS with h | h <;> rcases he with h' | h' <;> rw [h] at h' <;> cases h' <;> rfl
    refine ⟨fun e ep hEp => ⟨fun hHd => ?_, fun hHd => ?_⟩,
      fun e ep hEp => ⟨fun hTl => ?_, fun hTl => ?_⟩,
      endpointQueueRemoveDual_removed_no_incoming st st' endpointId false tid hObjInv hLink hStep⟩
    · have hIpc := (hQHB e ep tid tcbPost hEp hTid).1 hHd
      rcases hS with h | h <;> rw [h] at hIpc <;> cases hIpc
    · obtain rfl := hSame e ((hQHB e ep tid tcbPost hEp hTid).2 hHd)
      exact (hB ep hEp).1 (by simpa [spliceQueue] using hHd)
    · have hIpc := (hQTB e ep tid tcbPost hEp hTid).1 hTl
      rcases hS with h | h <;> rw [h] at hIpc <;> cases hIpc
    · obtain rfl := hSame e ((hQTB e ep tid tcbPost hEp hTid).2 hTl)
      exact (hB ep hEp).2 (by simpa [spliceQueue] using hTl)

/-- **A thread's endpoint cancel keeps the bundle**, wherever the thread waits
in its queue.  The removal (`endpointQueueRemoveDual`, which
`storeQueueRemove` is under the check, `queueRemove_inPlace`) relaxes the
bundle at the thread
(`endpointQueueRemoveDual_establishes_ipcInvariantFullExceptMembership`, whose
predecessor premise the check read) and detaches it
(`endpointQueueRemoveDual_removed_detached_side`); the thread, blocked sending,
calling or receiving and holding no timeout budget, is made a cancelled waiter,
which closes the bundle (`cancelledEndpointWaiter_closes`). -/
theorem storeEndpointBlockedCancelled_preserves_ipcInvariantFull
    (st : SystemState) (e : SeLe4n.ObjId) (q : Bool) (t : SeLe4n.ThreadId) (ep : Endpoint)
    (tcb : TCB) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hT : st.getTcb? t = some tcb) (hE : st.getEndpoint? e = some ep)
    (hC : endpointBlockedCancellable st e q t ep tcb = true) :
    ipcInvariantFull (storeEndpointBlockedCancelled st e q t ep tcb) := by
  obtain ⟨hSide, hNoBudget, hG, hPredG⟩ := endpointBlockedCancellable_parts hC
  have hNotRes : ¬ t.isReserved := by
    have h := hG
    simp only [queueRemoveInPlace, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [h.1.1.1.1.1.1]
  have hEo := (SystemState.getEndpoint?_eq_some_iff st e ep).mp hE
  have hTo := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
  have hLookup := lookupTcb_of_objects_of_not_reserved st t tcb hTo hNotRes
  obtain ⟨hRem, hFr⟩ := queueRemove_inPlace st e q t ep tcb hEo hTo hG
  have hPred : splicePredecessorBlocked q e st t := by
    intro tcb' hL hN p hP pTcb hLp
    rw [hLookup] at hL; cases hL
    exact blockedOnQueueSide_ipcState (hPredG p hN hP pTcb (getTcb?_of_lookupTcb st p pTcb hLp))
  have hSideS : spliceSideBlocked q e (tcbOffQueue tcb).ipcState :=
    blockedOnQueueSide_ipcState hSide
  unfold storeEndpointBlockedCancelled
  generalize storeQueueRemove st e q t ep tcb = s1 at hRem hFr ⊢
  have hI1 := endpointQueueRemoveDual_preserves_objects_invExt st s1 e q t hObjInv hRem
  have hEx := endpointQueueRemoveDual_establishes_ipcInvariantFullExceptMembership st s1 e q t
    hObjInv hRem hInv hPred
  have hT1 : s1.objects[t.toObjId]? = some (.tcb (tcbOffQueue tcb)) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hFr.removed_tcb
  have hEx' := hEx
  obtain ⟨-, hDual1, -, -, -, -, -, -, hQHB1, -, -, -, -, -, -, -, -, hQTB1, -⟩ := hEx'
  obtain ⟨hNotHead, hNotTail, hNoInc⟩ := endpointQueueRemoveDual_removed_detached_side st s1 e q
    t hObjInv hInv.dualQueueSystemInvariant hRem _ hT1 hSideS hQHB1 hQTB1 hDual1.2.1
  refine cancelledEndpointWaiter_closes s1 t (tcbOffQueue tcb) hI1 hNotRes hT1 hNoBudget
    (fun e' r hEq => ?_) hNotHead hNotTail hNoInc hEx
  cases q
  · rcases hSideS.2 rfl with h | h <;> rw [h] at hEq <;> cases hEq
  · rw [hSideS.1 rfl] at hEq; cases hEq

/-- **A thread's endpoint cancel keeps the bundle and the table's
well-formedness**, as the closure asks it. -/
theorem finaliseEndpointCancelStep_keepsIpcInvariantFull :
    FinaliseEndpointCancelStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) :=
  fun s e q t ep tcb h hT hE hC =>
    ⟨storeEndpointBlockedCancelled_preserves_ipcInvariantFull s e q t ep tcb h.2 h.1 hT hE hC,
      (FinaliseFrame.storeEndpointBlockedCancelled s e q t ep tcb h.2).invExt⟩

/-- **The suspend's mark keeps the bundle**: `threadState` is a field the bundle
does not read, and the message of a ready thread is one it asks nothing of
(`pendingMessageReadAgrees_ready_none`), so the mark is a field update the bundle
agrees with (`ipcInvariantFull_of_tcbFieldUpdateAgree`). -/
theorem finalisedSuspendMark_keepsIpcInvariantFull (s : SystemState) (t : SeLe4n.ThreadId)
    (h : ipcInvariantFull s ∧ s.objects.invExt)
    (hReady : ∀ x : TCB, s.getTcb? t = some x → x.ipcState = .ready) :
    ipcInvariantFull (s.updateTcb t finalisedSuspendMark) ∧
      (s.updateTcb t finalisedSuspendMark).objects.invExt := by
  cases hT : s.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact h
  | some tcb =>
    have hPre := (SystemState.getTcb?_eq_some_iff s t tcb).mp hT
    have hAt := updateTcb_objects_self_of_tcb finalisedSuspendMark h.2 hPre
    have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ t.toObjId →
        (s.updateTcb t finalisedSuspendMark).objects[oid]? = s.objects[oid]? :=
      fun oid hNe => SystemState.updateTcb_objects_ne _ _ _ _ (Ne.symm hNe) h.2
    have hSched : (s.updateTcb t finalisedSuspendMark).scheduler = s.scheduler := by
      rw [SystemState.updateTcb_eq_objects_update]
    have hMsg : pendingMessageReadAgrees tcb.ipcState (finalisedSuspendMark tcb).pendingMessage
        tcb.pendingMessage := by
      rw [hReady tcb hT]; exact pendingMessageReadAgrees_ready_none _
    exact ⟨ipcInvariantFull_of_tcbFieldUpdateAgree s _ t.toObjId tcb (finalisedSuspendMark tcb)
        h.1 hPre hAt hFrame rfl hMsg rfl rfl rfl rfl rfl rfl rfl
        ,
      SystemState.updateTcb_preserves_objects_invExt s t _ h.2⟩

/-- **The suspend keeps the bundle**: the deschedule of a ready thread
(`descheduleAt_preserves_ipcInvariantFull`), which keeps it ready, then the
mark. -/
theorem finaliseSuspendStep_keepsIpcInvariantFull :
    FinaliseSuspendStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s t tcb h hT hS hO _ _
  have hReady : ∀ x : TCB, s.getTcb? t = some x → x.ipcState = .ready := by
    intro x hx; rw [hT] at hx; cases hx
    unfold TCB.ipcState; rw [hS, hO]; rfl
  have hReadyD : ∀ x : TCB, (descheduleAtPlacement s t).getTcb? t = some x →
      x.ipcState = .ready := by
    intro x hx
    have hxo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hx
    run_links_back (descheduleAtPlacement_objectsAgreeOffRunLinks s t) at x hxo
    exact hReady x ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hxo)
  exact finalisedSuspendMark_keepsIpcInvariantFull _ t
    ⟨descheduleAt_preserves_ipcInvariantFull s t _ h.1,
      (FinaliseFrame.descheduleAt s t _ h.2).invExt⟩ hReadyD

/-- **The release keeps the bundle**: it writes neither the objects nor the
scheduler. -/
theorem finaliseReleaseStep_keepsIpcInvariantFull :
    FinaliseReleaseStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s t h
  refine ⟨ipcInvariantFull_of_storeAgrees (fun k => ?_) h.1,
    (FinaliseFrame.releaseCores s t h.2).invExt⟩
  rw [finaliseThreadReleaseCores_objects]

-- ============================================================================
-- §4  The finalisation
-- ============================================================================

/-- A step whose frame is a `FinaliseFrame` keeps the bundle the delete carries
once it keeps the IPC bundle: the frame keeps the table well formed and every
lent context headed by its lender. -/
theorem finaliseLoanBundle.of_frame {s s' : SystemState} (h : finaliseLoanBundle s)
    (hI : ipcInvariantFull s') (F : FinaliseFrame s s') : finaliseLoanBundle s' :=
  ⟨hI, F.invExt, h.2.2.of_loanWrite F.loan⟩

/-- **The finalisation keeps the bundle the delete carries**, every step of it
(`finaliseFinalObject_closed`): each step's IPC theorem, its frame for the
table and the lent-context fact, and the two steps that read the fact — the
unstack (`finaliseUnstack_keepsLentContextHeads`, on a context its holder's
unbind left bound to no thread, `finaliseSchedContextUnbind_unbound`) and the
reply cancel (`finaliseReplyStep_keepsIpcInvariantFull`). -/
theorem finaliseFinalObject_preserves_finaliseLoanBundle (target : Nat) (st : SystemState)
    (h : finaliseLoanBundle st) : finaliseLoanBundle (finaliseFinalObject target st) :=
  finaliseFinalObject_closed finaliseLoanBundle
    (fun e q s ep t tcb h hE hH hT hC =>
      h.of_frame (storeEndpointWaiterCancelled_preserves_ipcInvariantFull s e q ep t tcb h.2.1 h.1
        hE hH hT hC) (FinaliseFrame.storeEndpointWaiterCancelled s e q t _ h.2.1))
    (fun n s _ t tcb h _ _ hT hC =>
      have F := FinaliseFrame.notificationCancel s t tcb n h.2.1
        (notificationWaiterCancellable_blocked hC)
      h.of_frame (notificationWaiterCancel_preserves_ipcInvariantFull s n t tcb h.2.1 h.1 hT hC)
        (F.trans (FinaliseFrame.wakeCancelledWaiter _ t F.invExt)))
    (fun n s _ t h _ _ hCode hIn =>
      h.of_frame (storeUnbindNotification_preserves_ipcInvariantFull s n t h.2.1 h.1 hCode hIn)
        (FinaliseFrame.storeUnbindNotification s t n h.2.1))
    (fun s t tcb h hT hS hO hId =>
      h.of_frame (finaliseScDescheduleStep_keepsIpcInvariantFull s t tcb ⟨h.1, h.2.1⟩ hT hS hO hId).1
        (FinaliseFrame.descheduleAt s t _ h.2.1))
    (fun s s' t tcb sc x h hT hS hSc hB hOk =>
      h.of_frame (finaliseScReleaseStep_keepsIpcInvariantFull s s' t tcb sc x ⟨h.1, h.2.1⟩ hT hS
        hSc hB hOk).1 (FinaliseFrame.cancelBoundDonationOnCore h.2.1 hOk))
    (fun s n t tcb nt h hT hI hN hC =>
      h.of_frame (finaliseNotificationCancelStep_keepsIpcInvariantFull s n t tcb nt ⟨h.1, h.2.1⟩ hT
        hI hN hC).1 (FinaliseFrame.notificationCancel s t tcb n h.2.1 hI))
    (fun s e q t ep tcb h hT hE hC =>
      h.of_frame (finaliseEndpointCancelStep_keepsIpcInvariantFull s e q t ep tcb ⟨h.1, h.2.1⟩ hT hE
        hC).1 (FinaliseFrame.storeEndpointBlockedCancelled s e q t ep tcb h.2.1))
    (fun s t tcb h hT hS hO hI hId =>
      h.of_frame (finaliseSuspendStep_keepsIpcInvariantFull s t tcb ⟨h.1, h.2.1⟩ hT hS hO hI hId).1
        (FinaliseFrame.suspend s t h.2.1))
    (fun s t h =>
      h.of_frame (finaliseReleaseStep_keepsIpcInvariantFull s t ⟨h.1, h.2.1⟩).1
        (FinaliseFrame.releaseCores s t h.2.1))
    (fun s s1 x sc rid r h hSc hRep hR hN hS s₀ h₀ hA hS₀ =>
      have hI := finaliseUnstackStep_keepsIpcInvariantFull s s1 x sc rid r ⟨h.1, h.2.1⟩ hSc hRep hR
        hN hS s₀ ⟨h₀.1, h₀.2.1⟩ hA hS₀
      ⟨hI.1, hI.2, finaliseUnstack_keepsLentContextHeads h.2.1 h.1.donationOwnerValid h.2.2 hSc
        (finaliseSchedContextUnbind_unbound h₀.2.1 hA (hS₀ ▸ hSc)) hR hN hS⟩)
    finaliseReplyStep_keepsIpcInvariantFull
    (fun s s1 x tid t h hT hC e =>
      have hI := finaliseUnstashStep_keepsIpcInvariantFull s s1 x tid t ⟨h.1, h.2.1⟩ hT hC e
      ⟨hI.1, hI.2, h.2.2.of_loanWrite (e ▸ (FinaliseFrame.updateTcb s tid _ h.2.1).loan)⟩)
    target st h

/-- **The finalisation keeps the IPC bundle**, on a state where every lent
context is headed by its lender (`finaliseFinalObject_preserves_finaliseLoanBundle`). -/
theorem finaliseFinalObject_preserves_ipcInvariantFull (target : Nat) (st : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hW : lentContextHeadsLenderFrame st) :
    ipcInvariantFull (finaliseFinalObject target st) :=
  (finaliseFinalObject_preserves_finaliseLoanBundle target st ⟨hInv, hObjInv, hW⟩).1

/-- **The retire after the finalisation keeps the bundle the delete carries**:
the finalisation's (`finaliseFinalObject_preserves_finaliseLoanBundle`), then
the retire's (`retireFinalObject_preserves_ipcInvariantFull`,
`retireFinalObject_keepsLentContextHeads`). -/
theorem retireFinalisedObject_preserves_finaliseLoanBundle (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (h : finaliseLoanBundle st) :
    finaliseLoanBundle (retireFinalisedObject ec target recorder st) := by
  have h1 := finaliseFinalObject_preserves_finaliseLoanBundle target st h
  have h2 := retireFinalObject_preserves_ipcInvariantFull ec target recorder _ h1.2.1 h1.1
  exact ⟨h2.1, h2.2, retireFinalObject_keepsLentContextHeads ec target recorder _ h1.2.1 h1.2.2⟩

-- ============================================================================
-- §5  The finalising delete and revocation
-- ============================================================================

/-- `.cspaceDelete`: the finalising delete keeps the bundle it carries — the
delete's own theorems, then the teardown's, then the finalisation's and the
retire's. -/
theorem cspaceDeleteSlotFinalising_preserves_finaliseLoanBundle
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (h : finaliseLoanBundle st)
    (hStep : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    finaliseLoanBundle st' := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' hStep
  have hI1 := cspaceDeleteSlot_preserves_objects_invExt st st1 addr h.2.1 hD
  have h2 := finaliseDestroyedCapabilities_preserves_ipcInvariantFull ec _ _ st1 st2 hI1
    (cspaceDeleteSlot_preserves_ipcInvariantFull st st1 addr h.2.1 h.1 hD) hF
  exact retireFinalisedObject_preserves_finaliseLoanBundle ec _ _ st2 ⟨h2.1, h2.2,
    finaliseDestroyedCapabilities_keepsLentContextHeads ec _ _ st1 st2 hI1
      (cspaceDeleteSlot_keepsLentContextHeads st st1 addr h.2.1 h.2.2 hD) hF⟩

/-- `.cspaceDelete`: the finalising delete preserves the IPC bundle, on a state
where every lent context is headed by its lender. -/
theorem cspaceDeleteSlotFinalising_preserves_ipcInvariantFull
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hW : lentContextHeadsLenderFrame st)
    (hStep : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    ipcInvariantFull st' :=
  (cspaceDeleteSlotFinalising_preserves_finaliseLoanBundle ec addr st st' ⟨hInv, hObjInv, hW⟩
    hStep).1

/-- `.cspaceRevoke`: the finalising revocation preserves the IPC bundle — the
revocation's own theorem at the state it reaches, carrying the bundle the
delete carries through every delete it runs. -/
theorem cspaceRevokeCdtFinalising_preserves_ipcInvariantFull
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hW : lentContextHeadsLenderFrame st)
    (hStep : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    ipcInvariantFull st' :=
  (cspaceRevokeCdtFinalising_closed finaliseLoanBundle
    (fun c s s' hQ hD => cspaceDeleteSlotFinalising_preserves_finaliseLoanBundle ec c s s' hQ hD)
    ⟨hInv, hObjInv, hW⟩ hStep).1


end SeLe4n.Kernel
