/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation
import SeLe4n.Kernel.IPC.Invariant.CancelAllFrame
import SeLe4n.Kernel.IPC.Invariant.ReplyServerForget
import SeLe4n.Kernel.IPC.Invariant.FinaliseLoanCoherence
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationNotificationShape
import SeLe4n.Kernel.IPC.Invariant.CancellationBundle
import SeLe4n.Kernel.IPC.Invariant.SchedLinkFrame

/-!
# The finalisation keeps the IPC invariants

WS-ZA ZA5.4 part 23: `finaliseFinalObject` cancels an endpoint's or a
notification's waiters and unbinds a notification before a final delete's
retire (`IPC/Operations/CancelAll.lean`).  This module proves that each cancel,
and so the whole finalisation, keeps the IPC bundle (`ipcInvariantFull`).

* **An endpoint waiter's cancel** is the pop of its queue's head
  (`endpointQueuePopHead`, which `storePopHead` is under the walk's guard), the
  receive-completing store with no message, the thread set to restart, and
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
    _hAcyc, hOwner, hBudget, hReplyLink, hStash, hUnique, hTail,
    hQNT, hNBR, hLinks⟩ := hInv
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
      headTcb hObjInv hQNT hStep,
    notificationBindingReciprocal.of_kindPreservingWrite hKind hNBR,
    endpointQueuePopHead_preserves_endpointQueueLinksOnlyBlocked endpointId isReceiveQ st st' tid
      headTcb hObjInv hLinks hStep,
    endpointQueuePopHead_popped_next_none endpointId isReceiveQ st st' tid headTcb hObjInv hStep⟩

-- ============================================================================
-- §2  An endpoint waiter's cancel
-- ============================================================================

/-- What the walk's endpoint check admits. -/
theorem endpointWaiterCancellable_parts {st : SystemState} {endpointId : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} {tcb : TCB} (h : endpointWaiterCancellable st endpointId t tcb = true) :
    cancelledWaiterWakeable st t tcb = true ∧ tcb.timeoutBudget = none ∧
      sendWakesInPlace st endpointId t tcb.queueNext = true := by
  simp only [endpointWaiterCancellable, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

/-- **A cancellable endpoint waiter is blocked in an IPC.** -/
theorem endpointWaiterCancellable_blocked {st : SystemState} {endpointId : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} {tcb : TCB} (h : endpointWaiterCancellable st endpointId t tcb = true) :
    tcb.ipcState ≠ .ready := by
  simp only [endpointWaiterCancellable, Bool.and_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
  intro hR
  have hC : tcb.ipcStateCode = 0 ∧ tcb.ipcObjectCode = 0 := by
    unfold TCB.ipcState at hR
    revert hR
    cases tcb.ipcStateCode with
    | zero => cases tcb.ipcObjectCode <;> simp [ThreadIpcState.ofCodes]
    | succ n => rcases n with _ | _ | _ | n <;> simp [ThreadIpcState.ofCodes]
  rcases h.2 with h' | h'
  · exact h' hC.1
  · exact h' hC.2

/-- The receive completion with no message, the first of the two stores a
cancelled waiter's TCB write is read as. -/
@[reducible] def endedWaiterTcb (x : TCB) : TCB :=
  TCB.setIpcState { x with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready

/-- **A detached waiter whose IPC is ended closes the bundle**: a thread `t`,
held at `x`, that heads, ends and follows nothing in any endpoint queue, holds
no timeout budget and is blocked on no reply, made a cancelled waiter
(`cancelledEndpointWaiterTcb`), takes the bundle with membership relaxed at `t`
to the bundle.  Read as two stores — the receive completion with no message,
which closes the bundle (`storeTcbReceiveComplete_closes_exceptMembership`),
then the restart, which moves only the saved PC and the thread state
(`writeReturnFrameToTcb_preserves_ipcInvariantFull`) — that agree key by key
with the one store the cancel commits. -/
theorem cancelledEndpointWaiter_closes (f : TCB → TCB) (s1 : SystemState) (t : SeLe4n.ThreadId)
    (x : TCB) (hI1 : s1.objects.invExt) (hNotRes : ¬ t.isReserved)
    (hT1 : s1.objects[t.toObjId]? = some (.tcb x)) (hNoBudget : x.timeoutBudget = none)
    (hNotReply : ∀ e r, x.ipcState ≠ .blockedOnReply e r)
    (hNotHead : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint), s1.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.head ≠ some t ∧ ep.sendQ.head ≠ some t)
    (hNotTail : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint), s1.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.tail ≠ some t ∧ ep.sendQ.tail ≠ some t)
    (hNoInc : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
      s1.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some t)
    (hEx : ipcInvariantFullExceptMembership s1 t)
    (hIpc : (f x).ipcState = (endedWaiterTcb x).ipcState := by rfl)
    (hMsg : (f x).pendingMessage = (endedWaiterTcb x).pendingMessage := by rfl)
    (hNext : (f x).queueNext = (endedWaiterTcb x).queueNext := by rfl)
    (hPrev : (f x).queuePrev = (endedWaiterTcb x).queuePrev := by rfl)
    (hPPrev : (f x).queuePPrev = (endedWaiterTcb x).queuePPrev := by rfl)
    (hBudget : (f x).timeoutBudget = (endedWaiterTcb x).timeoutBudget := by rfl)
    (hReply : (f x).replyObject = (endedWaiterTcb x).replyObject := by rfl)
    (hStash : (f x).pendingReceiveReply = (endedWaiterTcb x).pendingReceiveReply := by rfl)
    (hBind : (f x).schedContextBinding = (endedWaiterTcb x).schedContextBinding := by rfl)
    (hSl : ∀ sl, (f x).spaceSlotCap sl = (endedWaiterTcb x).spaceSlotCap sl := by intro _; rfl)
    (hBnc : (f x).boundNotificationCode = (endedWaiterTcb x).boundNotificationCode := by rfl) :
    ipcInvariantFull (s1.updateTcb t f) := by
  have hG1 : s1.getTcb? t = some x := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT1
  have hNotReply1 : ∀ (tcbX : TCB), s1.objects[t.toObjId]? = some (.tcb tcbX) →
      ∀ e r, tcbX.ipcState ≠ .blockedOnReply e r := by
    intro tcbX hX e r
    rw [hT1] at hX; cases hX
    exact hNotReply e r
  -- The two-store reading: the receive completion, then the restart.
  let rc : TCB := endedWaiterTcb x
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
  have hRcG : sRc.getTcb? t = some rc := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hRcAt
  -- WS-SX SX4: the restart, a second store of fields no conjunct reads — the
  -- saved PC moved back to the restart PC, `.Restart`, and (WS-ZA ZA6.22) the
  -- fault record retired.
  have hFullClr : ipcInvariantFull (sRc.updateTcb t fun _ => f x) := by
    rw [SystemState.updateTcb_eq_of_some hRcG]
    exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull sRc t rc _ hIRc hFullRc
      hRcAt hIpc hMsg hNext hPrev hPPrev hBudget hReply hStash hBind
      (fun sl _ _ h _ => (hSl sl) ▸ h) hBnc
  have hAgree : objectStoreAgrees (sRc.updateTcb t fun _ => f x)
      (s1.updateTcb t f) := by
    intro k
    rw [SystemState.updateTcb_eq_of_some hG1, SystemState.updateTcb_eq_of_some hRcG]
    show (s1.objects.insert t.toObjId _)[k]? = (sRc.objects.insert t.toObjId _)[k]?
    by_cases hk : k = t.toObjId
    · subst hk
      rw [RHTable_getElem?_eq_get?, RHTable_getElem?_eq_get?,
        RobinHood.RHTable.getElem?_insert_self _ _ _ hI1,
        RobinHood.RHTable.getElem?_insert_self _ _ _ hIRc]
    · have hne : (t.toObjId == k) = false := by simp [Ne.symm hk]
      rw [RHTable_getElem?_eq_get?, RHTable_getElem?_eq_get?,
        RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (by simp [hne]) hI1,
        RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (by simp [hne]) hIRc,
        ← RHTable_getElem?_eq_get?, ← RHTable_getElem?_eq_get?]
      exact (storeObject_objects_ne s1 sRc t.toObjId k _ hk hI1 hStoreRc).symm
  exact ipcInvariantFull_of_storeAgrees hAgree hFullClr

/-- **An endpoint waiter's cancel keeps the bundle.**  The pop relaxes it at the
waiter (`endpointQueuePopHead_establishes_ipcInvariantFullExceptMembership`) and
leaves the waiter out of every queue (`endpointQueuePopHead_popped_not_head`,
`_not_tail`, `_no_incoming`); the receive-completing store with no message closes
it (`storeTcbReceiveComplete_closes_exceptMembership`) — the waiter, a queue's
head, is blocked on a send, a call or a receive, so not on a reply, and the walk
admitted it with no timeout budget; the restart moves only its saved PC, its
`threadState` and its fault record (WS-SX SX4), and the one store
the cancel commits agrees with that two-store reading key by key; the wake is of
a `.ready` thread (`enqueueRunnableOnCore_preserves_ipcInvariantFull`). -/
theorem storeEndpointWaiterCancelled_preserves_ipcInvariantFull
    (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (ep : Endpoint)
    (t : SeLe4n.ThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hE : st.getEndpoint? endpointId = some ep)
    (hH : (endpointWaitQueue ep isReceiveQ).head = some t)
    (hT : st.getTcb? t = some tcb)
    (hC : endpointWaiterCancellable st endpointId t tcb = true) (faulted : Bool) :
    ipcInvariantFull
      (storeEndpointWaiterCancelled st endpointId isReceiveQ t tcb.queueNext faulted) := by
  obtain ⟨-, hNoBudget, hG⟩ := endpointWaiterCancellable_parts hC
  have hNotRes : ¬ t.isReserved := by
    simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
    simp [hG.1.1.1.1.1]
  have hEo := (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hE
  have hTo := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
  have hH' : (if isReceiveQ then ep.receiveQ else ep.sendQ).head = some t := hH
  obtain ⟨hPop, hFr⟩ := popHead_inPlace st endpointId isReceiveQ ep t tcb hEo hH' hTo hG
  unfold storeEndpointWaiterCancelled storeEndpointWaiterFaulted storeEndpointWaiterRestarted
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
  have hNotReply : ∀ e r, (tcbOffQueue tcb).ipcState ≠ .blockedOnReply e r :=
    fun e r hEq => by rcases hBlk with h | h | h <;> rw [show (tcbOffQueue tcb).ipcState =
      tcb.ipcState from rfl, h] at hEq <;> cases hEq
  -- A faulted waiter: the same receive completion, then `Inactive` with its fault.
  split
  · exact cancelledEndpointWaiter_closes faultedEndpointWaiterTcb s1 t (tcbOffQueue tcb) hI1
      hNotRes hT1 hNoBudget hNotReply hNotHead hNotTail hNoInc hEx
  have hFull2 := cancelledEndpointWaiter_closes cancelledEndpointWaiterTcb s1 t (tcbOffQueue tcb)
    hI1 hNotRes hT1 hNoBudget hNotReply hNotHead hNotTail hNoInc hEx
  have hI2 : (s1.updateTcb t cancelledEndpointWaiterTcb).objects.invExt :=
    SystemState.updateTcb_preserves_objects_invExt _ _ _ hI1
  refine enqueueRunnableOnCore_preserves_ipcInvariantFull _ _ t hI2 (fun tcbX hX => ?_) hFull2
  rw [SystemState.updateTcb_getTcb?_self _ _ _ hI1, hFr.head_tcb] at hX
  cases hX
  exact TCB.ipcState_setIpcState
    (TCB.setPendingFault { tcbOffQueue tcb with
        pendingMessage := none
        pendingReceiveReplyCode := 0 } none) .ready

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
context — its own or on loan — is bound back to it, the thread finalisation's
unbind among them. -/
theorem finaliseScReleaseStep_keepsIpcInvariantFull :
    FinaliseScReleaseStep (fun s => ipcInvariantFull s ∧ s.objects.invExt) := by
  intro s s' t tcb sc x h hT hS hSc hB hOk
  refine ⟨cancelBoundDonationOnCore_view_preserves_ipcInvariantFull s s' t tcb _ h.2 h.1
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

/-- **What a finalised reply's cancel owes the reply arm**, on the delete's
bundle: the reply-stack resolution answers, the head is held on loan from the
caller, the caller's one loan is that head, and the outer caller is a waiting
donor that nobody holds a loan from.  A reply heading no stack owes nothing:
its caller lends to no one (`replyCaller_lendsNone`).  A head reply's admission
read the first two (`donatedReturnCommits`, the holder's binding codes); the
third is `donationOwnerUnique`; and a loan from the outer caller would make the
outer caller's frame a head (`lentContextHeadsLenderFrame`), where the reply
stack reads a frame link (`replyStackOuterCaller?_ok_some`, `replyCallerLinkage`). -/
theorem finaliseReply_armPremises {s : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    {c : SeLe4n.ThreadId} {t : TCB} (hInv : s.objects.invExt) (hFull : ipcInvariantFull s)
    (hW : lentContextHeadsLenderFrame s) (hX : s.getObject? x = some (.reply r))
    (hT : s.getTcb? c = some t) (hF : replyCallerFinalisable s x r c t = true) :
    cancelDonationResolves s c t ∧
      (∀ rid, t.replyObject = some rid → replyFrameHeadHolderDonation s rid c) ∧
      donatedContextIsOwnerFrameHead s c ∧ cancelDonationStackValid s c t := by
  obtain ⟨-, hNotRes, -, -, ⟨ep, rt, hB⟩, hRO, -, -, -⟩ := replyCallerFinalisable_parts hF
  have hTo := (SystemState.getTcb?_eq_some_iff s c t).mp hT
  have hLk : lookupTcb s c = some t := lookupTcb_of_objects_of_not_reserved s c t hTo hNotRes
  have hDonEq : Lifecycle.Suspend.cancelledCallerDonation? s c t =
      replyFrameHeadHolder? s ⟨x.val⟩ := by
    unfold Lifecycle.Suspend.cancelledCallerDonation?
    rw [hB]
    simp only [hRO]
  rcases replyCallerFinalisable_cases hX hF with ⟨hHd, hD⟩ |
    ⟨sd, sc, hd, htd, -, hSc, -, hBt, hTd, hBd, hC, hD⟩
  · have hNo := replyCaller_lendsNone hW hX hT hHd hRO
    refine ⟨fun _ _ e => (by rw [hD] at e; cases e), fun rid e => ?_,
      fun _ _ holder ht sd hH hBd => absurd hBd (hNo holder ht sd hH),
      fun _ _ e => (by rw [hD] at e; cases e)⟩
    rw [hRO] at e
    cases e
    exact replyFrameHeadHolderDonation_of_no_head _ _ _ (hDonEq.symm.trans hD)
  · obtain ⟨n, -, hResN, -, -⟩ := replyHeadPop_commits hInv hT hD hC
    have hC' := hC
    unfold donatedReturnCommits at hC'
    rw [hResN, hSc] at hC'
    simp only [Bool.and_eq_true] at hC'
    obtain ⟨⟨⟨⟨-, hOut⟩, -⟩, -⟩, hSv⟩ := hC'
    have hTdO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTd
    have hLkd : lookupTcb s hd = some htd := by
      obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp hSv
      rw [ht']
      have := lookupTcb_some_objects s hd t' ht'
      rw [hTdO] at this
      rw [KernelObject.tcb.inj (Option.some.inj this)]
    refine ⟨fun sd' hd' e _ _ => ?_, fun rid e => ?_, fun ot hLkc holder ht sd' hH hBd' => ?_,
      fun sd' hd' e n' hRes' => ?_⟩
    · rw [hD] at e
      obtain ⟨e1, -⟩ := Prod.mk.inj (Option.some.inj e)
      exact ⟨n, e1 ▸ hResN⟩
    · rw [hRO] at e
      cases e
      intro sd' hd' e'
      rw [← hDonEq, hD] at e'
      obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj e')
      subst e1 e2
      unfold replyDonationReturn?
      rw [hLkd]
      simp only [hBd]
    · have eH : holder = hd := hFull.donationOwnerUnique holder hd ht htd sd' sd c hH hTdO hBd' hBd
      subst eH
      have eT : ht = htd := KernelObject.tcb.inj (Option.some.inj (hH.symm.trans hTdO))
      subst eT
      rw [hBd] at hBd'
      have eS : sd = sd' := (SchedContextBinding.donated.inj hBd').1
      subst eS
      have eO : ot = t := Option.some.inj (hLkc.symm.trans hLk)
      subst eO
      exact ⟨by rw [← Lifecycle.Suspend.cancelledCallerDonation?_eq_answeredFrameHeadContext? s c ot
        hLkc ep rt hB, hD], hLkd⟩
    · rw [hD] at e
      obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj e)
      subst e1 e2
      rw [hResN] at hRes'
      have eN : n = n' := Except.ok.inj hRes'
      subst eN
      refine ⟨hOut, fun outer hn tid tcb scIdx hTid hBindO => ?_⟩
      subst hn
      obtain ⟨-, ridH, -, below, b, -, -, -, hBelow, hBN, hBC⟩ :=
        replyStackOuterCaller?_ok_some s sd outer hResN
      have hBo := (SystemState.getReply?_eq_some_iff _ _ _).mp hBelow
      obtain ⟨tcbO, hTO, hROO, -⟩ := hFull.replyCallerLinkage.1.2 below b outer hBo hBC
      obtain ⟨rid', r', hRO', hR', hN'⟩ := hW tid tcb scIdx outer tcbO hTid hBindO hTO
      rw [hROO] at hRO'
      cases hRO'
      rw [hBo] at hR'
      have eB : b = r' := KernelObject.reply.inj (Option.some.inj hR')
      rw [← eB, hBN] at hN'
      cases hN'

/-- **A reply's caller cancel keeps the bundle**: the reply arm of the cancel
(`cancelIpcBlocking_replyArm_preserves_ipcInvariantFull`, its premises from the
admission: `finaliseReply_armPremises`), carried across the head reply's
replenishment migration and holder deschedule, which agree with the cancel off
the run links (`cancelIpcBlockingReclaimed_objectsAgreeOffRunLinks`), then the
revert of the boost it lent its server
(`propagatePipChainCrossCore_preserves_ipcInvariantFull`); and the lent-context
fact itself (`finaliseReplyStep_keepsLentContextHeads`). -/
theorem finaliseReplyStep_keepsIpcInvariantFull : FinaliseReplyStep finaliseLoanBundle := by
  intro s x r c t h hX _ hT hF
  obtain ⟨-, hNotRes, -, -, ⟨ep, rt, hB⟩, -, hN, hP, hBud⟩ := replyCallerFinalisable_parts hF
  obtain ⟨hResolves, hOwed, hHolder, hStack⟩ :=
    finaliseReply_armPremises h.2.1 h.1 h.2.2 hX hT hF
  have hW' := finaliseReplyStep_keepsLentContextHeads h.2.1 h.1 h.2.2 hX hT hF
  have hTo := (SystemState.getTcb?_eq_some_iff s c t).mp hT
  have hLk : lookupTcb s c = some t := lookupTcb_of_objects_of_not_reserved s c t hTo hNotRes
  have hOff : sweptThreadOffQueueChains s c := by
    intro tcbX e; rw [hLk] at e; cases e; exact ⟨hP, hN⟩
  have h0 := cancelIpcBlocking_replyArm_preserves_ipcInvariantFull s c t ep rt h.2.1 hLk hB h.1
    hResolves hBud hOff hOwed hHolder hStack
  have h1 := ipcInvariantFull_of_objectsAgreeOffRunLinks
    (cancelIpcBlockingReclaimed_objectsAgreeOffRunLinks c t s)
    (ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
      (.of_releaseLinks (cancelIpcBlockingMigrated_agree c t s)) h0)
  have hI1 := (FinaliseFrameAny.cancelIpcBlockingReclaimed s c t h.2.1 hB).invExt
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
  obtain ⟨-, hDual1, -, -, -, -, -, -, hQHB1, -, -, -, -, -, -, -, hQTB1, -⟩ := hEx'
  obtain ⟨hNotHead, hNotTail, hNoInc⟩ := endpointQueueRemoveDual_removed_detached_side st s1 e q
    t hObjInv hInv.dualQueueSystemInvariant hRem _ hT1 hSideS hQHB1 hQTB1 hDual1.2.1
  refine cancelledEndpointWaiter_closes cancelledEndpointWaiterTcb s1 t (tcbOffQueue tcb) hI1
    hNotRes hT1 hNoBudget
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

/-- **A reply's pop off a context no thread holds keeps the bundle** (seL4-MCS's
`reply_pop` after the holder's `schedContext_unbindTCB`): the IPC bundle across
the pop (`returnUnheldSchedContext_preserves_ipcInvariantFull`), from three
pre-state facts.  No thread names the context in its binding: one holding it as
its own would be the thread the context is bound to (the binding pair,
`schedContextBindingConsistent`), one holding it on loan likewise
(`donationOwnerValid`), and the context is bound to none.  No loan names the
caller: its lender's frame — the caller's reply — would head the lent context
(`lentContextHeadsLenderFrame`), which is then the popped context, bound to no
thread.  None names the outer caller: its frame is the frame below the head,
which links to the head and heads nothing.  The lent-context fact itself is
`returnUnheldSchedContext_keepsLentContextHeads`; the settle after the pop
writes release fields and queues alone.  A caller that holds a context of its
own is handed nothing: the sever writes no thread and keeps the bundle and the
lender frames outright (`severUnheldSchedContext_preserves_ipcInvariantFull`,
`severUnheldSchedContext_keepsLentContextHeads`). -/
theorem finaliseUnheldStep_keepsFinaliseLoanBundle (s : SystemState) (x : SeLe4n.ObjId)
    (r : Reply) (c : SeLe4n.ThreadId) (t : TCB) (h : finaliseLoanBundle s)
    (hL : schedContextLinkInvariant s) (hX : s.getObject? x = some (.reply r))
    (hT : s.getTcb? c = some t) (hA : replyUnheldPopAdmitted s x r c t = true) :
    finaliseLoanBundle (finaliseReplyUnheldPop s r c) := by
  obtain ⟨sId, hN, hRO⟩ := replyUnheldPopAdmitted_parts hA
  rcases finaliseReplyUnheldPop_cases s r c with e | ⟨sId', n, st', hN', hRes, hOk, e⟩ |
      ⟨sId', n, st', hN', -, hRes, hOk, e⟩ <;> rw [e]
  · exact h
  rotate_left
  · rw [hN] at hN'; cases hN'
    exact ⟨severUnheldSchedContext_preserves_ipcInvariantFull h.2.1 h.1 hOk,
      (FinaliseFrameAny.severUnheldSchedContext h.2.1 hOk).invExt,
      severUnheldSchedContext_keepsLentContextHeads h.2.1 h.2.2 h.1.donationOwnerValid hRes hOk⟩
  rw [hN] at hN'; cases hN'
  obtain ⟨sc, -, -, hSc, hB0, -, -, -, -, -, -, -, -, -, -⟩ :=
    returnUnheldSchedContext_objects h.2.1 hOk
  have hUnheld : ∀ (X : SeLe4n.ThreadId) (sc1 : SchedContext),
      s.objects[sId.toObjId]? = some (.schedContext sc1) → sc1.boundThread ≠ some X := by
    intro X sc1 h1 e
    rw [hSc] at h1; cases h1
    unfold SchedContext.boundThread at e; rw [hB0] at e; cases e
  have hTo := (SystemState.getTcb?_eq_some_iff s c t).mp hT
  have hFree : ∀ (X : SeLe4n.ThreadId) (tX : TCB), s.objects[X.toObjId]? = some (.tcb tX) →
      tX.schedContextBinding.scId? ≠ some sId := by
    intro X tX hX' e
    cases hb : tX.schedContextBinding with
    | unbound => rw [hb] at e; cases e
    | bound s' =>
      rw [hb] at e; cases e
      obtain ⟨sc1, h1, hbt⟩ := hL.binding.1 X tX hX' _ hb
      exact hUnheld X sc1 h1 hbt
    | donated s' o =>
      rw [hb] at e; cases e
      obtain ⟨⟨sc1, h1, hbt⟩, -⟩ := h.1.donationOwnerValid X tX _ o hX' hb
      exact hUnheld X sc1 h1 hbt
  have hNoOwner : ∀ (X : SeLe4n.ThreadId) (tX : TCB) (s' : SeLe4n.SchedContextId),
      s.objects[X.toObjId]? = some (.tcb tX) → tX.schedContextBinding ≠ .donated s' c := by
    intro X tX s' hX' hb
    obtain ⟨rid, r', hRO', hR', hN'⟩ := h.2.2 X tX s' c t hX' hb hTo
    rw [hRO] at hRO'; cases hRO'
    rw [show (⟨x.val⟩ : SeLe4n.ReplyId).toObjId = x from rfl, ← SystemState.getObject?_eq_getElem,
      hX] at hR'
    cases hR'
    rw [hN] at hN'
    cases hN'
    obtain ⟨⟨sc1, h1, hbt⟩, -⟩ := h.1.donationOwnerValid X tX _ c hX' hb
    exact hUnheld X sc1 h1 hbt
  have hOuterFree : ∀ outer, n = some outer → ∀ (X : SeLe4n.ThreadId) (tX : TCB)
      (s' : SeLe4n.SchedContextId),
      s.objects[X.toObjId]? = some (.tcb tX) → tX.schedContextBinding ≠ .donated s' outer := by
    intro outer hn X tX s' hX' hBindO
    subst hn
    obtain ⟨-, ridH, -, below, b, -, -, -, hBelow, hBN, hBC⟩ :=
      replyStackOuterCaller?_ok_some s sId outer hRes
    have hBo := (SystemState.getReply?_eq_some_iff _ _ _).mp hBelow
    obtain ⟨tcbO, hTO, hROO, -⟩ := h.1.replyCallerLinkage.1.2 below b outer hBo hBC
    obtain ⟨rid', r', hRO', hR', hN'⟩ := h.2.2 X tX s' outer tcbO hX' hBindO hTO
    rw [hROO] at hRO'
    cases hRO'
    rw [hBo] at hR'
    have eB : b = r' := KernelObject.reply.inj (Option.some.inj hR')
    rw [← eB, hBN] at hN'
    cases hN'
  have hInv1 := (FinaliseFrameAny.returnUnheldSchedContext h.2.1 hOk).invExt
  have F := FinaliseFrame.of_releaseOnlyWrite
    (SchedContextOps.settleReturnedContext_releaseOnlyWrite st' (determineTargetCore st' c) sId)
    (SchedContextOps.settleReturnedContext_agree _ _ _)
    (SchedContextOps.settleReturnedContext_objects_invExt _ _ _ hInv1)
  exact ⟨settleReturnedContext_preserves_ipcInvariantFull _ _ _
      (returnUnheldSchedContext_preserves_ipcInvariantFull h.2.1 h.1 hFree hNoOwner
        hOuterFree hOk), F.invExt,
    (returnUnheldSchedContext_keepsLentContextHeads h.2.1 h.2.2 h.1.donationOwnerValid
      h.1.replyCallerLinkage.1 hRes hOk).of_loanWrite F.loan⟩

/-- **A holder's loan made its own keeps the bundle** (WS-ZA ZA6.34, the
thread-side cut's last write): the holder's owner code cleared, so its binding
`.donated scId o` becomes `.bound scId`, every other field kept.  The fourteen
binding-free conjuncts ride `donationReadAgreement`; of the donation conjuncts,
every post-state loan is a pre-state loan of another thread (the holder holds
none after), a loan's owner is never the holder (an owner is unbound, the
holder is not), and the holder's context is the one it held. -/
theorem updateTcb_ownerCleared_preserves_ipcInvariantFull (st : SystemState)
    (h : SeLe4n.ThreadId) (ht : TCB) (scId : SeLe4n.SchedContextId) (o : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) (hT : st.getTcb? h = some ht)
    (hB : ht.schedContextBinding = .donated scId o) :
    ipcInvariantFull (st.updateTcb h fun t => { t with scBindingOwnerCode := 0 }) := by
  rw [SystemState.updateTcb_eq_of_some hT]
  have hPre := (SystemState.getTcb?_eq_some_iff st h ht).mp hT
  have hAt := insertObjects_getElem_self st h.toObjId
    (.tcb { ht with scBindingOwnerCode := 0 }) hObjInv
  have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ h.toObjId →
      ({ st with objects := (st.objects.insert h.toObjId
          (.tcb { ht with scBindingOwnerCode := 0 })) } : SystemState).objects[oid]? =
        st.objects[oid]? :=
    fun oid hne => insertObjects_getElem_ne st h.toObjId _ oid hne hObjInv
  have hAgree := donationReadAgreement_of_tcbFieldUpdateAgree st _ h.toObjId ht
    { ht with scBindingOwnerCode := 0 } hPre hAt hFrame rfl (pendingMessageReadAgrees_refl _)
    rfl rfl rfl rfl rfl rfl
  have hNoLoan : ∀ s' o', ({ ht with scBindingOwnerCode := 0 } : TCB).schedContextBinding ≠
      .donated s' o' := TCB.ownerCleared_not_donated ht
  -- A post-state loan is a pre-state loan of another thread.
  have hBwd : ∀ (t : SeLe4n.ThreadId) (tx : TCB) (s' : SeLe4n.SchedContextId)
      (o' : SeLe4n.ThreadId),
      ({ st with objects := (st.objects.insert h.toObjId
          (.tcb { ht with scBindingOwnerCode := 0 })) } : SystemState).objects[t.toObjId]? =
        some (.tcb tx) → tx.schedContextBinding = .donated s' o' →
      t.toObjId ≠ h.toObjId ∧ st.objects[t.toObjId]? = some (.tcb tx) := by
    intro t tx s' o' hx hd
    by_cases hk : t.toObjId = h.toObjId
    · rw [hk, hAt] at hx; cases hx; exact absurd hd (hNoLoan s' o')
    · exact ⟨hk, (hFrame _ hk) ▸ hx⟩
  refine ipcInvariantFull_of_donationReadAgreement st _ hInv hAgree ?_ ?_ ?_ ?_
  · intro t1 t2 tcb1 tcb2 s1 s2 h1 h2 hB1 hB2
    exact hInv.donationChainAcyclic t1 t2 tcb1 tcb2 s1 s2 (hBwd _ _ _ _ h1 hB1).2
      (hBwd _ _ _ _ h2 hB2).2 hB1 hB2
  · intro t tx s' owner hx hd
    obtain ⟨-, hx0⟩ := hBwd _ _ _ _ hx hd
    obtain ⟨⟨sc, hScAt, hBound⟩, ownerTcb, hOwner, hOwnerUnbound, hOwnerBlk⟩ :=
      hInv.donationOwnerValid t tx s' owner hx0 hd
    have hOk : owner.toObjId ≠ h.toObjId := by
      intro e; rw [e, hPre] at hOwner; cases hOwner; rw [hB] at hOwnerUnbound; cases hOwnerUnbound
    have hSk : s'.toObjId ≠ h.toObjId := by
      intro e; rw [e, hPre] at hScAt; cases hScAt
    exact ⟨⟨sc, by rw [hFrame _ hSk]; exact hScAt, hBound⟩, ownerTcb,
      by rw [hFrame _ hOk]; exact hOwner, hOwnerUnbound, hOwnerBlk⟩
  · intro t1 t2 tcb1 tcb2 s h1 h2 hNe hS1 hS2
    have back : ∀ (t : SeLe4n.ThreadId) (tx : TCB),
        ({ st with objects := (st.objects.insert h.toObjId
            (.tcb { ht with scBindingOwnerCode := 0 })) } : SystemState).objects[t.toObjId]? =
          some (.tcb tx) → tx.schedContextBinding.scId? = some s →
        ∃ ty, st.objects[t.toObjId]? = some (.tcb ty) ∧ ty.schedContextBinding.scId? = some s := by
      intro t tx hx hs
      by_cases hk : t.toObjId = h.toObjId
      · rw [hk, hAt] at hx; cases hx
        refine ⟨ht, hk ▸ hPre, ?_⟩
        rw [hB]
        have e : ({ ht with scBindingOwnerCode := 0 } : TCB).schedContextBinding = .bound scId := by
          unfold TCB.schedContextBinding SchedContextBinding.ofCodes
          have hb := hB
          unfold TCB.schedContextBinding SchedContextBinding.ofCodes at hb
          split at hb
          · cases hb
          · split at hb
            · cases hb
            · cases hb; simp_all
        rw [e] at hs; exact hs
      · exact ⟨tx, (hFrame _ hk) ▸ hx, hs⟩
    obtain ⟨y1, hy1, e1⟩ := back t1 tcb1 h1 hS1
    obtain ⟨y2, hy2, e2⟩ := back t2 tcb2 h2 hS2
    exact hInv.donationBudgetTransfer t1 t2 y1 y2 s hy1 hy2 hNe e1 e2
  · intro t1 t2 tcb1 tcb2 s1 s2 owner h1 h2 hB1 hB2
    exact hInv.donationOwnerUnique t1 t2 tcb1 tcb2 s1 s2 owner (hBwd _ _ _ _ h1 hB1).2
      (hBwd _ _ _ _ h2 hB2).2 hB1 hB2

/-- **The thread-side cut keeps the bundle the delete carries** (WS-ZA ZA6.34):
the head reply's upward link is a stack link
(`storeObject_reply_stackLinks_preserves_ipcInvariantFull`), the context's head and
origin are content the bundle does not read
(`insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull`), and a
holder's loan made its own is `updateTcb_ownerCleared_preserves_ipcInvariantFull`.
The lent-context fact loses the cut frame's head (`of_headLetGo`): after the cut
no thread holds the context on loan — its bound thread is the holder, whose loan
the cut made its own, or holds it as its own already. -/
theorem cutHeadFrameKeepingContext_preserves_finaliseLoanBundle (s : SystemState)
    (rid : SeLe4n.ReplyId) (h : finaliseLoanBundle s) :
    finaliseLoanBundle (Lifecycle.Suspend.cutHeadFrameKeepingContext s rid) := by
  obtain ⟨hFull, hInv, hW⟩ := h
  unfold Lifecycle.Suspend.cutHeadFrameKeepingContext
  cases hH : replyFrameHeadContext? s rid with
  | none => exact ⟨hFull, hInv, hW⟩
  | some scId =>
  obtain ⟨r0, sc0, hR0, hN0, hSc0, -⟩ := replyFrameHeadContext?_eq_some hH
  cases hR : s.getReply? rid with
  | none => rw [hR0] at hR; cases hR
  | some r =>
  rw [hR0] at hR; cases hR
  dsimp only
  cases hS : storeObject rid.toObjId (.reply { r0 with next := none }) s with
  | error => exact ⟨hFull, hInv, hW⟩
  | ok p =>
  obtain ⟨⟨⟩, s1⟩ := p
  dsimp only
  have hRo := (SystemState.getReply?_eq_some_iff _ _ _).mp hR0
  have hI1 := storeObject_preserves_objects_invExt s s1 _ _ hInv hS
  have hFull1 := storeObject_reply_stackLinks_preserves_ipcInvariantFull
    (a' := { r0 with next := none }) hInv hFull hR0 rfl rfl hS
  have hSco := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc0
  have hSk : scId.toObjId ≠ rid.toObjId := by intro e; rw [e, hRo] at hSco; cases hSco
  have hSc1 : s1.objects[scId.toObjId]? = some (.schedContext sc0) := by
    rw [storeObject_objects_ne s s1 _ _ _ hSk hInv hS]; exact hSco
  let f : SchedContext → SchedContext := fun sc => { sc with scReply := none, donationOrigin := none }
  have hSc1' : s1.getSchedContext? scId = some sc0 := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc1
  have e2 : s1.updateSchedContext scId f =
      { s1 with objects := s1.objects.insert scId.toObjId (.schedContext (f sc0)) } :=
    SystemState.updateSchedContext_eq_of_some hSc1' f
  have hFull2 : ipcInvariantFull (s1.updateSchedContext scId f) := by
    rw [e2]
    exact insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull s1 _ sc0 _ hI1 hFull1
      hSc1 rfl
  have hI2 : (s1.updateSchedContext scId f).objects.invExt :=
    SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hI1
  -- Objects of the second state: the reply cut, the context rewritten, the rest kept.
  have hO2 : ∀ k : SeLe4n.ObjId, k ≠ rid.toObjId → k ≠ scId.toObjId →
      (s1.updateSchedContext scId f).objects[k]? = s.objects[k]? := by
    intro k h1 h2
    rw [e2, insertObjects_getElem_ne s1 _ _ k h2 hI1,
      storeObject_objects_ne s s1 _ _ _ h1 hInv hS]
  have hSc2 : (s1.updateSchedContext scId f).getSchedContext? scId = some (f sc0) := by
    rw [e2, SystemState.getSchedContext?_eq_some_iff]
    exact insertObjects_getElem_self s1 _ _ hI1
  have hRid2 : (s1.updateSchedContext scId f).objects[rid.toObjId]? =
      some (.reply { r0 with next := none }) := by
    rw [e2, insertObjects_getElem_ne s1 _ _ _ (Ne.symm hSk) hI1]
    exact storeObject_objects_eq s s1 _ _ hInv hS
  have hN : ∀ r, s.objects[rid.toObjId]? = some (.reply r) → r.next = some (.head scId) := by
    intro r hr; rw [hRo] at hr; cases hr; exact hN0
  -- The frame from `s` up to the second state, off the cut reply.
  have F2 : ∀ oid : SeLe4n.ObjId, oid ≠ rid.toObjId →
      (s1.updateSchedContext scId f).objects[oid]? = s.objects[oid]? ∨
      ∃ pre post : KernelObject, s.objects[oid]? = some pre ∧
        (s1.updateSchedContext scId f).objects[oid]? = some post ∧ objectLoanKept post pre := by
    intro oid hne
    by_cases hk : oid = scId.toObjId
    · subst hk
      refine .inr ⟨.schedContext sc0, .schedContext (f sc0), hSco, ?_,
        objectLoanKept_of_inert (fun _ e => by cases e) (fun _ e => by cases e)⟩
      exact (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc2
    · exact .inl (hO2 oid hne hk)
  generalize hs2 : s1.updateSchedContext scId f = s2 at hFull2 hI2 hO2 hSc2 hRid2 F2 ⊢
  -- A loan of the context in the second state is held by its bound thread.
  have hLoanBound : ∀ (th : SeLe4n.ThreadId) (tx : TCB) (o : SeLe4n.ThreadId),
      s2.objects[th.toObjId]? = some (.tcb tx) → tx.schedContextBinding = .donated scId o →
      (s2.getSchedContext? scId).bind (·.boundThread) = some th := by
    intro th tx o hx hd
    obtain ⟨⟨sc, hs, hb⟩, -⟩ := hFull2.donationOwnerValid th tx scId o hx hd
    rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hs]; exact hb
  have hRidNoTcb2 : ∀ tx, s2.objects[rid.toObjId]? ≠ some (.tcb tx) := by
    intro tx e; rw [hRid2] at e; cases e
  -- The case with no write after the second state.
  have keep : (∀ (th : SeLe4n.ThreadId) (tx : TCB) (o : SeLe4n.ThreadId),
      s2.objects[th.toObjId]? = some (.tcb tx) → tx.schedContextBinding ≠ .donated scId o) →
      finaliseLoanBundle s2 :=
    fun hNo => ⟨hFull2, hI2, hW.of_headLetGo hN hNo hRidNoTcb2 F2⟩
  cases hB : (s2.getSchedContext? scId).bind (·.boundThread) with
  | none =>
    exact keep fun th tx o hx hd => by rw [hLoanBound th tx o hx hd] at hB; cases hB
  | some holder =>
  dsimp only
  cases hT : s2.getTcb? holder with
  | none =>
    refine keep fun th tx o hx hd => ?_
    have e := hLoanBound th tx o hx hd
    rw [hB] at e; cases e
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hx] at hT; cases hT
  | some ht =>
  dsimp only
  have notLoan : (∀ s' o', ht.schedContextBinding = .donated s' o' → s' ≠ scId) →
      finaliseLoanBundle s2 := by
    intro hne
    refine keep fun th tx o hx hd => ?_
    have e := hLoanBound th tx o hx hd
    rw [hB] at e; cases e
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hx] at hT; cases hT
    exact hne scId o hd rfl
  split
  · rename_i s' o hb
    split
    · rename_i hs
      rw [hs] at hb
      have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
      have hFull3 := updateTcb_ownerCleared_preserves_ipcInvariantFull s2 holder ht scId o hI2 hFull2 hT hb
      have hI3 := SystemState.updateTcb_preserves_objects_invExt s2 holder
        (fun t => { t with scBindingOwnerCode := 0 }) hI2
      rw [SystemState.updateTcb_eq_of_some hT] at hFull3 hI3 ⊢
      have hAt : (s2.objects.insert holder.toObjId (.tcb { ht with scBindingOwnerCode := 0 }))[holder.toObjId]? =
          some (.tcb { ht with scBindingOwnerCode := 0 }) :=
        RobinHood.RHTable.getElem?_insert_self s2.objects _ _ hI2
      have hNe3 : ∀ k : SeLe4n.ObjId, k ≠ holder.toObjId →
          (s2.objects.insert holder.toObjId (.tcb { ht with scBindingOwnerCode := 0 }))[k]? =
            s2.objects[k]? :=
        fun k hk => RobinHood.RHTable.getElem?_insert_ne s2.objects _ k _
          (fun e => hk (eq_of_beq e).symm) hI2
      have hHk : holder.toObjId ≠ rid.toObjId := by
        intro e; rw [e, hRid2] at hTo; cases hTo
      have hHs : holder.toObjId ≠ scId.toObjId := by
        intro e
        rw [e, (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc2] at hTo; cases hTo
      have hE : ∀ k : SeLe4n.ObjId, (markKeyChangeFrom s2 { s2 with objects := (s2.objects.insert holder.toObjId
          (.tcb { ht with scBindingOwnerCode := 0 })) } holder).objects[k]? =
          (s2.objects.insert holder.toObjId (.tcb { ht with scBindingOwnerCode := 0 }))[k]? :=
        fun k => by rw [markKeyChangeFrom_objects]
      refine ⟨ipcInvariantFull_of_objects_eq (markKeyChangeFrom_objects _ _ _) hFull3,
        by rw [markKeyChangeFrom_objects]; exact hI3, hW.of_headLetGo hN ?_ ?_ ?_⟩
      · intro th tx o' hx hd
        rw [hE] at hx
        by_cases hk : th.toObjId = holder.toObjId
        · rw [hk, hAt] at hx; cases hx; exact TCB.ownerCleared_not_donated ht _ _ hd
        · rw [hNe3 _ hk] at hx
          have e := hLoanBound th tx o' hx hd
          rw [hB] at e; cases e; exact hk rfl
      · intro tx
        rw [hE, hNe3 _ (Ne.symm hHk)]; exact hRidNoTcb2 tx
      · intro oid hne
        rw [hE]
        by_cases hk : oid = holder.toObjId
        · subst hk
          rw [hAt]
          refine .inr ⟨.tcb ht, _, ?_, rfl,
            objectLoanKept_tcb ⟨rfl, fun _ _ e => absurd e (TCB.ownerCleared_not_donated ht _ _)⟩⟩
          rw [← hO2 _ hHk hHs]; exact hTo
        · rw [hNe3 _ hk]; exact F2 oid hne
    · rename_i hs
      exact notLoan (fun a b e => by rw [hb] at e; cases e; exact hs)
  · rename_i hnd
    exact notLoan (fun a b e => absurd e (hnd a b))

/-- **The thread-side cut, as the closure asks it, keeps the bundle**
(`cutHeadFrameKeepingContext_preserves_finaliseLoanBundle`, at the reply the
cancelled caller waits on). -/
theorem cutCancelledCallerHead_preserves_finaliseLoanBundle (s : SystemState) (t : TCB)
    (h : finaliseLoanBundle s) :
    finaliseLoanBundle (Lifecycle.Suspend.cutCancelledCallerHead s t) := by
  unfold Lifecycle.Suspend.cutCancelledCallerHead
  split
  · unfold Lifecycle.Suspend.cutThreadHeadFrameKeepingContext
    split
    · exact h
    · exact cutHeadFrameKeepingContext_preserves_finaliseLoanBundle _ _ h
  · exact h

theorem finaliseCutStep_keepsFinaliseLoanBundle : FinaliseCutStep finaliseLoanBundle :=
  fun s _ _ _ t h _ _ _ _ => cutCancelledCallerHead_preserves_finaliseLoanBundle s t h

/-- A step whose frame is a `FinaliseFrame` keeps the bundle the delete carries
once it keeps the IPC bundle: the frame keeps the table well formed and every
lent context headed by its lender. -/
theorem finaliseLoanBundle.of_frame {s s' : SystemState} (h : finaliseLoanBundle s)
    (hI : ipcInvariantFull s') (F : FinaliseFrame s s') : finaliseLoanBundle s' :=
  ⟨hI, F.invExt, h.2.2.of_loanWrite F.loan⟩

/-- **The finalisation keeps the bundle the delete carries**, every step of it
(`finaliseFinalObject_closed_linked`, on a state whose scheduling links hold):
each step's IPC theorem, its frame for the table and the lent-context fact, the
two steps that read the fact — the unstack
(`finaliseUnstack_keepsLentContextHeads`, on a context its holder's unbind left
bound to no thread, `finaliseSchedContextUnbind_unbound`) and the reply cancel
(`finaliseReplyStep_keepsIpcInvariantFull`) — and the pop off an unheld
context, which reads the binding pair as well
(`finaliseUnheldStep_keepsFinaliseLoanBundle`). -/
theorem finaliseFinalObject_preserves_finaliseLoanBundle (target : Nat) (st : SystemState)
    (h : finaliseLoanBundle st) (hL : schedContextLinkInvariant st) :
    finaliseLoanBundle (finaliseFinalObject target st) :=
  (finaliseFinalObject_closed_linked finaliseLoanBundle
    (fun e q s ep t tcb h hE hH hT hC =>
      h.of_frame (storeEndpointWaiterCancelled_preserves_ipcInvariantFull s e q ep t tcb h.2.1 h.1
        hE hH hT hC _) (FinaliseFrame.storeEndpointWaiterCancelled s e q t _ _ h.2.1))
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
    ⟨fun s t h => h.of_frame (cancelYieldTo_preserves_ipcInvariantFull s t h.2.1 h.1)
        (FinaliseFrame.cancelYieldTo s t h.2.1),
     fun s c h => h.of_frame (completeYieldFrom_preserves_ipcInvariantFull s c h.2.1 h.1)
        (FinaliseFrame.completeYieldFrom s c h.2.1)⟩
    (fun s w x _ h hT _ hS =>
      h.of_frame (orphanReplyWaiter_preserves_ipcInvariantFull h.1 hT hS)
        (FinaliseFrame.orphanReplyWaiter s w x h.2.1))
    (fun s x r c t h _ hL hX _ hT hA => finaliseUnheldStep_keepsFinaliseLoanBundle s x r c t h hL hX hT hA)
    finaliseCutStep_keepsFinaliseLoanBundle
    target st h h.2.1 hL).1

/-- **The finalisation keeps the IPC bundle**, on a state where every lent
context is headed by its lender and the scheduling links hold
(`finaliseFinalObject_preserves_finaliseLoanBundle`). -/
theorem finaliseFinalObject_preserves_ipcInvariantFull (target : Nat) (st : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hW : lentContextHeadsLenderFrame st) (hL : schedContextLinkInvariant st) :
    ipcInvariantFull (finaliseFinalObject target st) :=
  (finaliseFinalObject_preserves_finaliseLoanBundle target st ⟨hInv, hObjInv, hW⟩ hL).1

/-- **The bundle the finalising delete carries along its whole chain**: the
finalisation's bundle (`finaliseLoanBundle`) and the scheduling links the
context retire reads its own links against (`schedContextLinkInvariant`). -/
def finalisingDeleteBundle (s : SystemState) : Prop :=
  finaliseLoanBundle s ∧ schedContextLinkInvariant s

/-- The thread-side half of the binding pair, on the bundle the delete carries
(`schedContextBindingBidirectional_of_consistent`). -/
theorem finalisingDeleteBundle.bidirectional {s : SystemState} (h : finalisingDeleteBundle s) :
    schedContextBindingBidirectional s :=
  schedContextBindingBidirectional_of_consistent h.2.binding h.1.1.donationOwnerValid

/-- The bundle reads the objects and the scheduler alone. -/
theorem finalisingDeleteBundle.of_objects_scheduler_eq {s s' : SystemState}
    (hO : s'.objects = s.objects) (hS : s'.scheduler = s.scheduler)
    (h : finalisingDeleteBundle s) : finalisingDeleteBundle s' := by
  refine ⟨⟨ipcInvariantFull_of_objects_eq hO h.1.1, by rw [hO]; exact h.1.2.1, ?_⟩,
    (SchedLinkFrame.of_objects_eq hO (by rw [hS])).preserves h.2⟩
  have := h.1.2.2
  unfold lentContextHeadsLenderFrame at this ⊢
  rw [hO]; exact this

/-- **The finalisation keeps the bundle the delete carries**: its own bundle
(`finaliseFinalObject_preserves_finaliseLoanBundle`) and the scheduling links
(`finaliseFinalObject_preserves_schedContextLinkInvariant`). -/
theorem finaliseFinalObject_preserves_finalisingDeleteBundle (target : Nat) (st : SystemState)
    (h : finalisingDeleteBundle st) : finalisingDeleteBundle (finaliseFinalObject target st) :=
  ⟨finaliseFinalObject_preserves_finaliseLoanBundle target st h.1 h.2,
    finaliseFinalObject_preserves_schedContextLinkInvariant target st h.1.2.1 h.2⟩

/-- **WS-ZA ZA5.5: a revocation keeps the bundle the delete carries**: it
rewrites one endpoint's `serviceRegistered`, which no conjunct reads
(`revokeService_preserves_ipcInvariantFull`), keeps every other object, and
writes no thread, context or reply and no scheduler field. -/
theorem revokeService_preserves_finalisingDeleteBundle {sid : ServiceId} {st st' : SystemState}
    (h : finalisingDeleteBundle st) (hR : revokeService sid st = .ok ((), st')) :
    finalisingDeleteBundle st' := by
  have hRw := revokeService_serviceRecordRewrite hR
  have hL := hRw.lookup h.1.2.1
  have hS := revokeService_preserves_scheduler st st' sid hR
  have hLoan := revokeService_loanWrite hR h.1.2.1
  have hF : SchedLinkFrame st st' := by
    refine ⟨fun oid => ?_, fun oid => ?_, fun oid => ?_, by rw [hS]⟩
    all_goals
      rcases hL oid with e | ⟨ep, c, h0, h1⟩
      · rw [e]
      · rw [h0, h1]; rfl
  exact ⟨⟨revokeService_preserves_ipcInvariantFull st st' sid h.1.2.1 h.1.1 hR,
    hRw.invExt h.1.2.1, h.1.2.2.of_loanWrite hLoan⟩, hF.preserves h.2⟩

/-- **The retire after the finalisation keeps the bundle the delete carries**:
the release's (`revokeService_preserves_finalisingDeleteBundle`), the finalisation's (`finaliseFinalObject_preserves_finalisingDeleteBundle`), then
the retire's (`retireFinalObject_preserves_ipcInvariantFull`,
`retireFinalObject_keepsLentContextHeads`,
`retireFinalObject_preserves_schedContextLinkInvariant`). -/
theorem retireFinalisedObject_preserves_finalisingDeleteBundle (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (h : finalisingDeleteBundle st) :
    finalisingDeleteBundle (retireFinalisedObject ec target recorder st) := by
  rcases retireFinalisedObject_cases ec target recorder st with ⟨_, hR⟩ | ⟨_, hR⟩ <;> rw [hR]
  · -- WS-ZA ZA6.32: an interrupt node's retire writes no object and no
    -- scheduler field.
    have hO := retireIrqNode_objects st (SeLe4n.ObjId.ofNat (target - 1))
    have hS := retireIrqNode_scheduler st (SeLe4n.ObjId.ofNat (target - 1))
    obtain ⟨⟨hI, hX, hH⟩, hL⟩ := h
    refine ⟨⟨ipcInvariantFull_of_objects_eq hO hI, by rw [hO]; exact hX, ?_⟩,
      SchedLinkFrame.preserves ⟨fun o => by rw [hO], fun o => by rw [hO], fun o => by rw [hO],
        by rw [hS]⟩ hL⟩
    unfold lentContextHeadsLenderFrame at hH ⊢
    rw [hO]; exact hH
  have h0 := releaseFinalRegistration_closed finalisingDeleteBundle
    (fun _ _ _ hs hR => revokeService_preserves_finalisingDeleteBundle hs hR) target st h
  obtain ⟨h1, hL⟩ := finaliseFinalObject_preserves_finalisingDeleteBundle target _ h0
  have h2 := retireFinalObject_preserves_ipcInvariantFull ec target recorder _ h1.2.1 h1.1
    hL.budgets
  exact ⟨⟨h2.1, h2.2, retireFinalObject_keepsLentContextHeads ec target recorder _ h1.2.1 h1.2.2⟩,
    retireFinalObject_preserves_schedContextLinkInvariant ec target recorder _ h1.2.1 hL⟩

-- ============================================================================
-- §5  The finalising delete and revocation
-- ============================================================================

/-- **The slot delete and the page teardown keep the bundle the delete
carries** — the state the finalisation then runs on. -/
theorem cspaceDeleteSlotTeardown_preserves_finalisingDeleteBundle {ec : Concurrency.CoreId}
    {addr : CSpaceAddr} {named : List SeLe4n.ObjId} {pages : List MappedPage}
    {st st1 st2 : SystemState} (h : finalisingDeleteBundle st)
    (hD : cspaceDeleteSlot addr st = .ok ((), st1))
    (hF : finaliseDestroyedCapabilities ec named pages st1 = .ok ((), st2)) :
    finalisingDeleteBundle st2 := by
  have hI1 := cspaceDeleteSlot_preserves_objects_invExt st st1 addr h.1.2.1 hD
  have h2 := finaliseDestroyedCapabilities_preserves_ipcInvariantFull ec _ _ st1 st2 hI1
    (cspaceDeleteSlot_preserves_ipcInvariantFull st st1 addr h.1.2.1 h.1.1 hD) hF
  exact ⟨⟨h2.1, h2.2, finaliseDestroyedCapabilities_keepsLentContextHeads ec _ _ st1 st2 hI1
      (cspaceDeleteSlot_keepsLentContextHeads st st1 addr h.1.2.1 h.1.2.2 hD) hF⟩,
    finaliseDestroyedCapabilities_preserves_schedContextLinkInvariant hI1
      (cspaceDeleteSlot_preserves_schedContextLinkInvariant h.1.2.1 h.2 hD) hF⟩

/-- `.cspaceDelete`: the finalising delete keeps the bundle it carries — the
delete's own theorems, then the teardown's, then the finalisation's and the
retire's. -/
theorem cspaceDeleteSlotFinalising_preserves_finalisingDeleteBundle
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (h : finalisingDeleteBundle st)
    (hStep : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    finalisingDeleteBundle st' := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' hStep
  exact retireFinalisedObject_preserves_finalisingDeleteBundle ec _ _ st2
    (cspaceDeleteSlotTeardown_preserves_finalisingDeleteBundle h hD hF)

/-- `.cspaceDelete`: the finalising delete preserves the IPC bundle, on a state
where every lent context is headed by its lender and the scheduling links hold. -/
theorem cspaceDeleteSlotFinalising_preserves_ipcInvariantFull
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hW : lentContextHeadsLenderFrame st) (hL : schedContextLinkInvariant st)
    (hStep : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    ipcInvariantFull st' :=
  (cspaceDeleteSlotFinalising_preserves_finalisingDeleteBundle ec addr st st'
    ⟨⟨hInv, hObjInv, hW⟩, hL⟩ hStep).1.1

/-- `.cspaceRevoke`: the finalising revocation keeps the bundle the delete
carries — through every delete it runs and every finalisation. -/
theorem cspaceRevokeCdtFinalising_preserves_finalisingDeleteBundle
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (h : finalisingDeleteBundle st)
    (hStep : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    finalisingDeleteBundle st' :=
  cspaceRevokeCdtFinalising_closed finalisingDeleteBundle
    (fun c s s' hQ hD => cspaceDeleteSlotFinalising_preserves_finalisingDeleteBundle ec c s s' hQ hD)
    (fun d s hQ => finaliseFinalObject_preserves_finalisingDeleteBundle d s hQ)
    h hStep

/-- `.cspaceRevoke`: the finalising revocation preserves the IPC bundle. -/
theorem cspaceRevokeCdtFinalising_preserves_ipcInvariantFull
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hW : lentContextHeadsLenderFrame st) (hL : schedContextLinkInvariant st)
    (hStep : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    ipcInvariantFull st' :=
  (cspaceRevokeCdtFinalising_preserves_finalisingDeleteBundle ec addr st st'
    ⟨⟨hInv, hObjInv, hW⟩, hL⟩ hStep).1.1

/-- `.tcbSetSpace` through the zombie delete preserves the IPC bundle: the loop's
passes are a chain of finalising deletes and finalisations carrying the bundle
the delete carries, and the plain space change after them preserves it
(`copyThreadSpaces_preserves_ipcInvariantFull`). -/
theorem copyThreadSpacesZombie_preserves_ipcInvariantFull (ec : Concurrency.CoreId)
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (cnSrc vrSrc : CSpaceAddr) (cnData : UInt64)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hW : lentContextHeadsLenderFrame st) (hL : schedContextLinkInvariant st)
    (hStep : copyThreadSpacesZombie ec st vtid cnSrc vrSrc cnData = .ok st') :
    ipcInvariantFull st' := by
  have hChain : ∀ n s, ZombieRun ec n st s → finalisingDeleteBundle s := fun _ _ hR =>
    hR.chain.closed finalisingDeleteBundle
      (fun c s s' hQ hD => cspaceDeleteSlotFinalising_preserves_finalisingDeleteBundle ec c s s' hQ hD)
      (fun d s hQ => finaliseFinalObject_preserves_finalisingDeleteBundle d s hQ)
      ⟨⟨hInv, hObjInv, hW⟩, hL⟩
  rcases copyThreadSpacesZombie_cases hStep with h1 | ⟨n, s, hR, rfl | h2⟩
  · exact copyThreadSpaces_preserves_ipcInvariantFull ec st st' vtid cnSrc vrSrc cnData hObjInv hInv
      hL.budgets h1
  · exact (hChain n _ hR).1.1
  · obtain ⟨⟨hI, hO, -⟩, hL'⟩ := hChain n s hR
    exact copyThreadSpaces_preserves_ipcInvariantFull ec s st' vtid cnSrc vrSrc cnData hO hI
      hL'.budgets h2

/-- `.cspaceDelete`: the zombie delete keeps the bundle the delete carries — a
chain of finalising deletes and finalisations (`cspaceDeleteSlotZombie_closed`). -/
theorem cspaceDeleteSlotZombie_preserves_finalisingDeleteBundle
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (h : finalisingDeleteBundle st)
    (hStep : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    finalisingDeleteBundle st' :=
  cspaceDeleteSlotZombie_closed finalisingDeleteBundle
    (fun c s s' hQ hD => cspaceDeleteSlotFinalising_preserves_finalisingDeleteBundle ec c s s' hQ hD)
    (fun d s hQ => finaliseFinalObject_preserves_finalisingDeleteBundle d s hQ)
    h hStep

/-- `.cspaceDelete`: the zombie delete preserves the IPC bundle. -/
theorem cspaceDeleteSlotZombie_preserves_ipcInvariantFull
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hW : lentContextHeadsLenderFrame st) (hL : schedContextLinkInvariant st)
    (hStep : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    ipcInvariantFull st' :=
  (cspaceDeleteSlotZombie_preserves_finalisingDeleteBundle ec addr st st'
    ⟨⟨hInv, hObjInv, hW⟩, hL⟩ hStep).1.1

/-- **`seL4_IRQHandler_SetNotification` preserves `ipcInvariantFull`**, as the
delete and the copy each do. -/
theorem irqHandlerSetNotification_preserves_ipcInvariantFull {ec : Concurrency.CoreId}
    {line : Nat} {src : CSpaceAddr} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hW : lentContextHeadsLenderFrame st) (hL : schedContextLinkInvariant st)
    (h : irqHandlerSetNotification ec line src st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨-, st1, -, -, -, hD, hC⟩ := irqHandlerSetNotification_ok hObjInv h
  have hB := cspaceDeleteSlotZombie_preserves_finalisingDeleteBundle ec _ st st1
    ⟨⟨hInv, hObjInv, hW⟩, hL⟩ hD
  exact cspaceCopy_preserves_ipcInvariantFull st1 st' src _ _ hB.1.2.1 hB.1.1 hC

end SeLe4n.Kernel
