-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.CallReplyRecv
import SeLe4n.Kernel.IPC.Invariant.NotificationPreservation
import SeLe4n.Kernel.IPC.Invariant.QueueNoDup
import SeLe4n.Kernel.IPC.Invariant.QueueMembership
import SeLe4n.Kernel.IPC.Invariant.QueueNextBlocking
import SeLe4n.Kernel.IPC.Invariant.WaitingThreadHelpers
import SeLe4n.Kernel.IPC.Invariant.Structural.QueueNextTransport
import SeLe4n.Kernel.IPC.Invariant.Structural.StoreObjectFrame

/-! # IPC Structural Preservation — Part 3 (DualQueueMembership)

Extracted from `SeLe4n.Kernel.IPC.Invariant.Structural` as part of
AN3-C (IPC-M02 / Theme 4.7) to keep each module under the
2000-LOC maintenance ceiling.  Declarations are unchanged in order,
content, and proof; only the file boundary has moved.  The parent
`Structural.lean` re-exports every child so all existing
`import SeLe4n.Kernel.IPC.Invariant.Structural` consumers continue
to typecheck without modification.

Contains the composed `ipcInvariantFull` preservation witnesses
(notificationSignal/Wait, endpointReply, endpointSendDual, etc.),
the V3-K `endpointQueueNoDup` preservation cluster, the V3-J
`ipcStateQueueConsistent` / `queueMembershipConsistent` cluster,
the WithCaps-wrapper `ipcInvariantFull` theorems, and the
T4-A/B/C compound preservation proofs.
-/

-- AN3-C: linter directives inherited from parent Structural.lean.
set_option linter.unusedVariables false

namespace SeLe4n.Kernel

open SeLe4n.Model




-- ============================================================================
-- WS-H12e/R3-B: Composed ipcInvariantFull preservation theorems
-- ============================================================================

/-- R3-B/M-18: notificationSignal preserves the full IPC invariant (self-contained).
All four components derived from pre-state invariants — no externalized hypotheses. -/
theorem notificationSignal_preserves_ipcInvariantFull
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨notificationSignal_preserves_ipcInvariant st st' notificationId badge hInv.1 hObjInv hStep,
   notificationSignal_preserves_dualQueueSystemInvariant st st' notificationId badge hInv.2.1 hObjInv hStep,
   notificationSignal_preserves_allPendingMessagesBounded st st' notificationId badge hInv.2.2.1 hObjInv hStep,
   notificationSignal_preserves_badgeWellFormed st st' notificationId badge hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', hDCA', hDOV', hPSI', hDBT', hUW', hBRT'⟩

/-- R3-B/M-18: notificationWait preserves the full IPC invariant (self-contained).
All four components derived from pre-state invariants — no externalized hypotheses. -/
theorem notificationWait_preserves_ipcInvariantFull
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcInvariantFull st' :=
  ⟨notificationWait_preserves_ipcInvariant st st' notificationId waiter result hInv.1 hObjInv hStep,
   notificationWait_preserves_dualQueueSystemInvariant st st' notificationId waiter result hInv.2.1 hObjInv hStep,
   notificationWait_preserves_allPendingMessagesBounded st st' notificationId waiter result hInv.2.2.1 hObjInv hStep,
   notificationWait_preserves_badgeWellFormed st st' notificationId waiter result hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', hDCA', hDOV', hPSI', hDBT', hUW', hBRT'⟩

/-- R3-B/M-18: endpointReply preserves the full IPC invariant (self-contained).
All four components derived from pre-state invariants. -/
theorem endpointReply_preserves_ipcInvariantFull
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointReply_preserves_ipcInvariant st st' replier target msg hInv.1 hObjInv hStep,
   endpointReply_preserves_dualQueueSystemInvariant replier target msg st st' hObjInv hStep hInv.2.1,
   endpointReply_preserves_allPendingMessagesBounded st st' replier target msg hInv.2.2.1 hObjInv hStep,
   endpointReply_preserves_badgeWellFormed st st' replier target msg hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', hDCA', hDOV', hPSI', hDBT', hUW', hBRT'⟩

-- ============================================================================
-- V3-K IPC operation proofs: endpointQueueNoDup preservation
-- ============================================================================

/-- V3-K-op-4: endpointSendDual preserves endpointQueueNoDup.
Rendezvous: PopHead + storeMsg + ensureRunnable chain.
Block: Enqueue (opposite empty) + storeMsg + removeRunnable chain. -/
theorem endpointSendDual_preserves_endpointQueueNoDup
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : endpointQueueNoDup st)
    (hDQSI : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Rendezvous path: PopHead + storeTcbIpcStateAndMessage + ensureRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hDQSI1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant endpointId true st pair.2.2 pair.1 hObjInv hPop hDQSI
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hNoDup1 := endpointQueuePopHead_preserves_endpointQueueNoDup endpointId true st pair.2.2 pair.1 pair.2.1 hInv hDQSI hDQSI1 hObjInv hPop
            exact ensureRunnable_preserves_endpointQueueNoDup _ _ <|
              storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup pair.2.2 st2 pair.1 .ready (some msg) hNoDup1 hObjInv1 hMsg
      | none =>
        -- Block path: Enqueue + storeTcbIpcStateAndMessage + removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
          have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
            endpointId false sender st st1 hEnq hDQSI hObjInv hFreshSender hSendTailFresh
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hNoDup1 := endpointQueueEnqueue_preserves_endpointQueueNoDup endpointId false sender st st1 hInv hDQSI1 hObjInv
              (fun ep' hEp' => by simp only [Bool.false_eq]; rw [hEp'] at hObj; cases hObj; exact hHead) hEnq
            exact removeRunnable_preserves_endpointQueueNoDup _ _ <|
              storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup st1 st2 sender (.blockedOnSend endpointId) (some msg) hNoDup1 hObjInv1 hMsg

/-- V3-K-op-5: endpointReceiveDual preserves endpointQueueNoDup.
Rendezvous (Call sub-path): PopHead + storeMsg + storePendingMessage chain.
Rendezvous (Send sub-path): PopHead + storeMsg + ensureRunnable + storePendingMessage chain.
Block: Enqueue (opposite empty) + storeIpcState + removeRunnable chain. -/
theorem endpointReceiveDual_preserves_endpointQueueNoDup
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (hInv : endpointQueueNoDup st)
    (hDQSI : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    endpointQueueNoDup st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Rendezvous: PopHead from sendQ
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hDQSI1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant endpointId false st pair.2.2 pair.1 hObjInv hPop hDQSI
          have hNoDup1 := endpointQueuePopHead_preserves_endpointQueueNoDup endpointId false st pair.2.2 pair.1 pair.2.1 hInv hDQSI hDQSI1 hObjInv hPop
          -- Case split on senderWasCall
          split at hStep
          · -- Call sub-path: storeTcbIpcStateAndMessage + storeTcbPendingMessage
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
              have hNoDup2 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup pair.2.2 st2 pair.1 _ none hNoDup1 hObjInv1 hMsg
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage st2 receiver .ready pair.2.1.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st3 =>
                simp only [hPend] at hStep
                obtain ⟨_, rfl⟩ := hStep
                exact storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup st2 _ receiver _ _ hNoDup2 hObjInv2 hPend
          · -- Send sub-path: storeTcbIpcStateAndMessage + ensureRunnable + storeTcbPendingMessage
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
              have hNoDup2 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup pair.2.2 st2 pair.1 _ none hNoDup1 hObjInv1 hMsg
              have hObjInvR : (ensureRunnable st2 pair.1).objects.invExt :=
                ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInv2
              have hNoDupR := ensureRunnable_preserves_endpointQueueNoDup st2 pair.1 hNoDup2
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready pair.2.1.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st3 =>
                simp only [hPend] at hStep
                obtain ⟨_, rfl⟩ := hStep
                exact storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup _ _ receiver _ _ hNoDupR hObjInvR hPend
      | none =>
        -- Block path: cleanup → Enqueue receiveQ + storeTcbIpcState + removeRunnable
        -- AI4-A: cleanupPreReceiveDonation before enqueue
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hInvClean := cleanupPreReceiveDonation_preserves_endpointQueueNoDup st receiver hObjInv hInv
          have hDQSIClean := cleanupPreReceiveDonation_preserves_dualQueueSystemInvariant st receiver hObjInv hDQSI
          have hFreshReceiverClean : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
              (cleanupPreReceiveDonation st receiver).objects[epId]? = some (.endpoint ep) →
              ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
              ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver :=
            fun epId ep hEp =>
              hFreshReceiver epId ep (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv epId ep hEp)
          have hRecvTailFreshClean : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
              (cleanupPreReceiveDonation st receiver).objects[endpointId]? = some (.endpoint ep) →
              ep.receiveQ.tail = some tailTid →
              ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
                (cleanupPreReceiveDonation st receiver).objects[epId']? = some (.endpoint ep') →
                (epId' ≠ endpointId →
                  ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
                (epId' = endpointId →
                  ep'.sendQ.tail ≠ some tailTid) :=
            fun ep tailTid hEp hTail epId' ep' hEp' =>
              hRecvTailFresh ep tailTid
                (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv endpointId ep hEp) hTail
                epId' ep'
                (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv epId' ep' hEp')
          have hObjClean := cleanupPreReceiveDonation_endpoint_forward st receiver hObjInv endpointId ep hObj
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hEnq hDQSIClean hObjInvClean hFreshReceiverClean hRecvTailFreshClean
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              have hNoDup1 := endpointQueueEnqueue_preserves_endpointQueueNoDup endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hInvClean hDQSI1 hObjInvClean
                (fun ep' hEp' => by simp only [↓reduceIte]; rw [hEp'] at hObjClean; cases hObjClean; exact hHead) hEnq
              exact removeRunnable_preserves_endpointQueueNoDup _ _ <|
                storeTcbIpcState_preserves_endpointQueueNoDup st1 st2 receiver _ hNoDup1 hObjInv1 hIpc

/-- V3-K-op-6: endpointCall preserves endpointQueueNoDup.
Rendezvous: PopHead + storeMsg + ensureRunnable + storeIpcState + removeRunnable chain.
Block: Enqueue (opposite empty) + storeMsg + removeRunnable chain. -/
theorem endpointCall_preserves_endpointQueueNoDup
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : endpointQueueNoDup st)
    (hDQSI : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Rendezvous path: PopHead + storeMsg + ensureRunnable + storeIpcState + removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hDQSI1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant endpointId true st pair.2.2 pair.1 hObjInv hPop hDQSI
          have hNoDup1 := endpointQueuePopHead_preserves_endpointQueueNoDup endpointId true st pair.2.2 pair.1 pair.2.1 hInv hDQSI hDQSI1 hObjInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ (some msg) hObjInv1 hMsg
            have hNoDup2 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup pair.2.2 st2 pair.1 _ (some msg) hNoDup1 hObjInv1 hMsg
            have hObjInvE : (ensureRunnable st2 pair.1).objects.invExt :=
                ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInv2
            have hNoDupE := ensureRunnable_preserves_endpointQueueNoDup st2 pair.1 hNoDup2
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage atomically clears caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st3 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              exact removeRunnable_preserves_endpointQueueNoDup _ _ <|
                storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup _ st3 caller _ none hNoDupE hObjInvE hIpc
      | none =>
        -- Block path: Enqueue + storeTcbIpcStateAndMessage + removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
          have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
            endpointId false caller st st1 hEnq hDQSI hObjInv hFreshCaller hSendTailFresh
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            have hNoDup1 := endpointQueueEnqueue_preserves_endpointQueueNoDup endpointId false caller st st1 hInv hDQSI1 hObjInv
              (fun ep' hEp' => by simp only [Bool.false_eq]; rw [hEp'] at hObj; cases hObj; exact hHead) hEnq
            exact removeRunnable_preserves_endpointQueueNoDup _ _ <|
              storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup st1 st2 caller _ (some msg) hNoDup1 hObjInv1 hMsg

/-- V3-K-op-7: endpointReplyRecv preserves endpointQueueNoDup.
Composes endpointReply (already proven) with endpointReceiveDual.
Freshness preconditions for the receiver are stated on the pre-state and
transported through the reply phase via endpoint backward lemmas. -/
theorem endpointReplyRecv_preserves_endpointQueueNoDup
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (st st' : SystemState)
    (hInv : endpointQueueNoDup st)
    (hDQSI : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ expectedReplier =>
      simp only [hIpc] at hStep
      -- Use suffices to extract reply phase + receiveDual structure
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
            endpointQueueNoDup stR.2) by
        -- AK1-B (I-H02): Fail-closed on expectedReplier = none
        cases expectedReplier with
        | none => simp at hStep
        | some expected =>
          simp only at hStep
          split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
      -- Main proof body: reply phase + receive phase
      intro st1 hMsg stR hRecv
      have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget .ready (some msg) hObjInv hMsg
      have hNoDup1 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup st st1 replyTarget .ready (some msg) hInv hObjInv hMsg
      have hDQSI1 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hObjInv hMsg hDQSI
      have hNoDupE := ensureRunnable_preserves_endpointQueueNoDup st1 replyTarget hNoDup1
      have hDQSIE := ensureRunnable_preserves_dualQueueSystemInvariant st1 replyTarget hDQSI1
      have hObjInvE : (ensureRunnable st1 replyTarget).objects.invExt :=
        ensureRunnable_preserves_objects st1 replyTarget ▸ hObjInv1
      -- Transport freshness through storeTcbIpcStateAndMessage + ensureRunnable
      have hFreshReceiver' : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
          (ensureRunnable st1 replyTarget).objects[epId]? = some (.endpoint ep) →
          ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
          ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver := by
        intro epId ep hEp
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp
        exact hFreshReceiver epId ep
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId ep hObjInv hMsg hEp)
      have hRecvTailFresh' : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
          (ensureRunnable st1 replyTarget).objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.tail = some tailTid →
          ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
            (ensureRunnable st1 replyTarget).objects[epId']? = some (.endpoint ep') →
            (epId' ≠ endpointId →
              ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
            (epId' = endpointId →
              ep'.sendQ.tail ≠ some tailTid) := by
        intro ep tailTid hEp hTail epId' ep' hEp'
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp hEp'
        exact hRecvTailFresh ep tailTid
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) endpointId ep hObjInv hMsg hEp)
          hTail epId' ep'
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId' ep' hObjInv hMsg hEp')
      exact endpointReceiveDual_preserves_endpointQueueNoDup endpointId receiver
        (ensureRunnable st1 replyTarget) stR.2 stR.1
        hNoDupE hDQSIE hObjInvE hFreshReceiver' hRecvTailFresh'
        (by have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)

-- ============================================================================
-- Section: Compound V3-J preservation for IPC operations
-- ============================================================================

/-- V3-J compound: endpointSendDual preserves ipcStateQueueMembershipConsistent.
Rendezvous path: PopHead(except_head) + storeTcb(.ready, partial→full) + ensureRunnable.
Block path: Enqueue + storeTcb(.blockedOnSend, general with reachability) + removeRunnable. -/
theorem endpointSendDual_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInvFull : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  have hInv := hInvFull.2.2.2.2.2.2.1
  have hDQSI := hInvFull.2.1
  have hQNBC := hInvFull.2.2.2.2.2.2.2.1
  have hQHBC := hInvFull.2.2.2.2.2.2.2.2.1
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hDQWF : dualQueueEndpointWellFormed endpointId st := hDQSI.1 endpointId ep hObj
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- RENDEZVOUS PATH: PopHead + storeTcb(.ready) + ensureRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          obtain ⟨receiver, headTcb, st1⟩ := triple
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId true st st1 receiver headTcb hObjInv hPop
          -- Derive hHeadBlocked from queueHeadBlockedConsistent
          have hHeadBlocked : headTcb.ipcState = .blockedOnReceive endpointId := by
            have hRetH := endpointQueuePopHead_returns_head endpointId true st ep receiver st1 hObj hPop
            simp only [↓reduceIte] at hRetH
            have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId true st ep receiver headTcb st1 hObj hPop
            exact (hQHBC endpointId ep receiver headTcb hObj hPreTcb).1 hRetH
          have hPartialV3J :=
            endpointQueuePopHead_preserves_ipcStateQueueMembershipConsistent_except_head
              endpointId true st st1 receiver headTcb ep hInv hObjInv hQNBC hObj
              (by simp only [↓reduceIte]; exact hHeadBlocked) hPop
          cases hMsg : storeTcbIpcStateAndMessage st1 receiver .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact ensureRunnable_preserves_ipcStateQueueMembershipConsistent st2 receiver <|
              storeTcbIpcStateAndMessage_partial_preserves_ipcStateQueueMembershipConsistent
                st1 st2 receiver .ready (some msg) hPartialV3J hObjInv1
                (fun epId h => absurd h (by simp))
                (fun epId h => absurd h (by simp))
                (fun epId h => absurd h (by simp)) hMsg
      | none =>
        -- BLOCK PATH: Enqueue + storeTcb(.blockedOnSend) + removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
            endpointId false sender st st1 hObjInv hEnq
          have hV3J1 := endpointQueueEnqueue_preserves_ipcStateQueueMembershipConsistent
            endpointId false sender st st1 hInv hObjInv hDQWF hEnq
          -- Get DQSI for st1 (for acyclicity)
          have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
            endpointId false sender st st1 hEnq hDQSI hObjInv hFreshSender
            (fun ep' tailTid hEp' hTail epId' ep'' hEp'' => by
              rw [hObj] at hEp'; cases hEp'
              exact hSendTailFresh ep tailTid hObj hTail epId' ep'' hEp'')
          -- Get reachability for sender after enqueue
          have hNotTail : ∀ ep', st.objects[endpointId]? = some (.endpoint ep') →
              (if false then ep'.receiveQ else ep'.sendQ).tail ≠ some sender := by
            intro ep' hEp'
            rw [hObj] at hEp'; cases hEp'
            exact (hFreshSender endpointId ep hObj).2.1
          have hReach := endpointQueueEnqueue_thread_reachable
            endpointId false sender st st1 hObjInv hNotTail hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            -- sender.toObjId ≠ endpointId (TCB vs endpoint)
            have hNeSenderEp : endpointId ≠ sender.toObjId := by
              intro h; unfold endpointQueueEnqueue at hEnq
              rw [hObj] at hEnq; simp only at hEnq
              cases hL : lookupTcb st sender with
              | none => simp [hL] at hEnq
              | some tcb =>
                have := lookupTcb_some_objects st sender tcb hL
                rw [← h, hObj] at this; cases this
            exact removeRunnable_preserves_ipcStateQueueMembershipConsistent st2 sender <|
              storeTcbIpcStateAndMessage_general_preserves_ipcStateQueueMembershipConsistent
                st1 st2 sender (.blockedOnSend endpointId) (some msg) hV3J1 hObjInv1 hMsg
                (fun epId hEq => by
                  cases hEq
                  obtain ⟨ep', hEp1, hR⟩ := hReach
                  have hEpFrame := storeTcbIpcStateAndMessage_preserves_objects_ne
                    st1 st2 sender (.blockedOnSend endpointId) (some msg)
                    endpointId hNeSenderEp hObjInv1 hMsg
                  rw [hEpFrame]
                  exact ⟨ep', hEp1, hR.elim Or.inl fun ⟨prev, prevTcb, hP, hQN⟩ => by
                    refine Or.inr ⟨prev, prevTcb, ?_, hQN⟩
                    have hNePrev : prev.toObjId ≠ sender.toObjId := by
                      intro h
                      have hPrevEq := ThreadId.toObjId_injective prev sender h
                      rw [hPrevEq] at hP
                      exact absurd hQN (tcbQueueChainAcyclic_no_self_loop hDQSI1.2.2 sender prevTcb hP)
                    rw [storeTcbIpcStateAndMessage_preserves_objects_ne
                      st1 st2 sender (.blockedOnSend endpointId) (some msg)
                      prev.toObjId hNePrev hObjInv1 hMsg]
                    exact hP⟩)
                (fun _ h => absurd h (by simp))
                (fun _ h => absurd h (by simp))

/-- V3-J compound: endpointReceiveDual preserves ipcStateQueueMembershipConsistent.
Rendezvous (Call sub-path): PopHead(sendQ) + storeTcb(.blockedOnReply) + storeTcbPendingMessage.
Rendezvous (Send sub-path): PopHead(sendQ) + storeTcb(.ready) + ensureRunnable + storeTcbPendingMessage.
Block path: Enqueue(receiveQ) + storeTcbIpcState(.blockedOnReceive, general) + removeRunnable. -/
theorem endpointReceiveDual_preserves_ipcStateQueueMembershipConsistent
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hDQSI : dualQueueSystemInvariant st)
    (hQNBC : queueNextBlockingConsistent st)
    (hQHBC : queueHeadBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    ipcStateQueueMembershipConsistent st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hDQWF : dualQueueEndpointWellFormed endpointId st := hDQSI.1 endpointId ep hObj
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- RENDEZVOUS: PopHead from sendQ
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          -- Head was in sendQ, so blocked on send or call
          have hHeadBlocked :
              pair.2.1.ipcState = .blockedOnSend endpointId ∨
              pair.2.1.ipcState = .blockedOnCall endpointId := by
            have hRetH := endpointQueuePopHead_returns_head endpointId false st ep pair.1 pair.2.2 hObj hPop
            have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId false st ep pair.1 pair.2.1 pair.2.2 hObj hPop
            exact (hQHBC endpointId ep pair.1 pair.2.1 hObj hPreTcb).2 hRetH
          have hPartialV3J :=
            endpointQueuePopHead_preserves_ipcStateQueueMembershipConsistent_except_head
              endpointId false st pair.2.2 pair.1 pair.2.1 ep hInv hObjInv hQNBC hObj
              hHeadBlocked hPop
          split at hStep
          · -- Call sub-path: storeTcb(.blockedOnReply) + storeTcbPendingMessage
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
              have hV3J2 :=
                storeTcbIpcStateAndMessage_partial_preserves_ipcStateQueueMembershipConsistent
                  pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hPartialV3J hObjInv1
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp)) hMsg
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage st2 receiver .ready pair.2.1.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st3 =>
                simp only [hPend] at hStep; obtain ⟨_, rfl⟩ := hStep
                exact storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent
                  st2 _ receiver .ready _ hV3J2 hObjInv2
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp)) hPend
          · -- Send sub-path: storeTcb(.ready) + ensureRunnable + storeTcbPendingMessage
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
              have hV3J2 :=
                storeTcbIpcStateAndMessage_partial_preserves_ipcStateQueueMembershipConsistent
                  pair.2.2 st2 pair.1 .ready none hPartialV3J hObjInv1
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp)) hMsg
              have hObjInvR : (ensureRunnable st2 pair.1).objects.invExt :=
                ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInv2
              have hV3JR := ensureRunnable_preserves_ipcStateQueueMembershipConsistent st2 pair.1 hV3J2
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready pair.2.1.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st3 =>
                simp only [hPend] at hStep; obtain ⟨_, rfl⟩ := hStep
                exact storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent
                  _ _ receiver .ready _ hV3JR hObjInvR
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp)) hPend
      | none =>
        -- BLOCK PATH: cleanup → Enqueue(receiveQ) + storeTcbIpcState(.blockedOnReceive) + removeRunnable
        -- AI4-A: cleanupPreReceiveDonation before enqueue
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hInvClean := cleanupPreReceiveDonation_preserves_ipcStateQueueMembershipConsistent st receiver hObjInv hInv
          have hDQSIClean := cleanupPreReceiveDonation_preserves_dualQueueSystemInvariant st receiver hObjInv hDQSI
          have hObjClean := cleanupPreReceiveDonation_endpoint_forward st receiver hObjInv endpointId ep hObj
          have hDQWFClean := cleanupPreReceiveDonation_preserves_dualQueueEndpointWellFormed st receiver hObjInv hDQSI endpointId ep hObjClean
          have hFreshReceiverClean : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
              (cleanupPreReceiveDonation st receiver).objects[epId]? = some (.endpoint ep) →
              ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
              ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver :=
            fun epId ep hEp =>
              hFreshReceiver epId ep (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv epId ep hEp)
          have hRecvTailFreshClean : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
              (cleanupPreReceiveDonation st receiver).objects[endpointId]? = some (.endpoint ep) →
              ep.receiveQ.tail = some tailTid →
              ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
                (cleanupPreReceiveDonation st receiver).objects[epId']? = some (.endpoint ep') →
                (epId' ≠ endpointId →
                  ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
                (epId' = endpointId →
                  ep'.sendQ.tail ≠ some tailTid) :=
            fun ep tailTid hEp hTail epId' ep' hEp' =>
              hRecvTailFresh ep tailTid
                (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv endpointId ep hEp) hTail
                epId' ep'
                (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv epId' ep' hEp')
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hV3J1 := endpointQueueEnqueue_preserves_ipcStateQueueMembershipConsistent
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hInvClean hObjInvClean hDQWFClean hEnq
            have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hEnq hDQSIClean hObjInvClean hFreshReceiverClean hRecvTailFreshClean
            have hNotTail : ∀ ep', (cleanupPreReceiveDonation st receiver).objects[endpointId]? = some (.endpoint ep') →
                (if true then ep'.receiveQ else ep'.sendQ).tail ≠ some receiver := by
              intro ep' hEp'
              rw [hObjClean] at hEp'; cases hEp'
              exact (hFreshReceiverClean endpointId ep hObjClean).2.2.2
            have hReach := endpointQueueEnqueue_thread_reachable
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hNotTail hEnq
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              have hNeRecvEp : endpointId ≠ receiver.toObjId := by
                intro h; unfold endpointQueueEnqueue at hEnq
                rw [hObjClean] at hEnq; simp only at hEnq
                cases hL : lookupTcb (cleanupPreReceiveDonation st receiver) receiver with
                | none => simp [hL] at hEnq
                | some tcb =>
                  have := lookupTcb_some_objects (cleanupPreReceiveDonation st receiver) receiver tcb hL
                  rw [← h, hObjClean] at this; cases this
              exact removeRunnable_preserves_ipcStateQueueMembershipConsistent st2 receiver <|
                storeTcbIpcState_general_preserves_ipcStateQueueMembershipConsistent
                  st1 st2 receiver (.blockedOnReceive endpointId) hV3J1 hObjInv1 hIpc
                  (fun _ h => absurd h (by simp))
                  (fun epId hEq => by
                    cases hEq
                    obtain ⟨ep', hEp1, hR⟩ := hReach
                    have hEpFrame := storeTcbIpcState_preserves_objects_ne
                      st1 st2 receiver (.blockedOnReceive endpointId)
                      endpointId hNeRecvEp hObjInv1 hIpc
                    rw [hEpFrame]
                    exact ⟨ep', hEp1, hR.elim Or.inl fun ⟨prev, prevTcb, hP, hQN⟩ => by
                      refine Or.inr ⟨prev, prevTcb, ?_, hQN⟩
                      have hNePrev : prev.toObjId ≠ receiver.toObjId := by
                        intro h
                        have hPrevEq := ThreadId.toObjId_injective prev receiver h
                        rw [hPrevEq] at hP
                        exact absurd hQN (tcbQueueChainAcyclic_no_self_loop hDQSI1.2.2 receiver prevTcb hP)
                      rw [storeTcbIpcState_preserves_objects_ne
                        st1 st2 receiver (.blockedOnReceive endpointId)
                        prev.toObjId hNePrev hObjInv1 hIpc]
                      exact hP⟩)
                  (fun _ h => absurd h (by simp))

/-- V3-J compound: endpointCall preserves ipcStateQueueMembershipConsistent.
Rendezvous: PopHead(receiveQ) + storeTcb(.ready, partial→full) + ensureRunnable +
storeTcbIpcState(.blockedOnReply) + removeRunnable.
Block: Enqueue(sendQ) + storeTcb(.blockedOnCall, general) + removeRunnable. -/
theorem endpointCall_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInvFull : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  have hInv := hInvFull.2.2.2.2.2.2.1
  have hDQSI := hInvFull.2.1
  have hQNBC := hInvFull.2.2.2.2.2.2.2.1
  have hQHBC := hInvFull.2.2.2.2.2.2.2.2.1
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hDQWF : dualQueueEndpointWellFormed endpointId st := hDQSI.1 endpointId ep hObj
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- RENDEZVOUS: PopHead(receiveQ) + storeTcb(.ready) + ensureRunnable + storeTcbIpcState(.blockedOnReply) + removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hHeadBlocked : pair.2.1.ipcState = .blockedOnReceive endpointId := by
            have hRetH := endpointQueuePopHead_returns_head endpointId true st ep pair.1 pair.2.2 hObj hPop
            have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId true st ep pair.1 pair.2.1 pair.2.2 hObj hPop
            exact (hQHBC endpointId ep pair.1 pair.2.1 hObj hPreTcb).1 hRetH
          have hPartialV3J :=
            endpointQueuePopHead_preserves_ipcStateQueueMembershipConsistent_except_head
              endpointId true st pair.2.2 pair.1 pair.2.1 ep hInv hObjInv hQNBC hObj
              (by simp only [↓reduceIte]; exact hHeadBlocked) hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ (some msg) hObjInv1 hMsg
            have hV3J2 :=
              storeTcbIpcStateAndMessage_partial_preserves_ipcStateQueueMembershipConsistent
                pair.2.2 st2 pair.1 .ready (some msg) hPartialV3J hObjInv1
                (fun epId h => absurd h (by simp))
                (fun epId h => absurd h (by simp))
                (fun epId h => absurd h (by simp)) hMsg
            have hObjInvE : (ensureRunnable st2 pair.1).objects.invExt :=
              ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInv2
            have hV3JE := ensureRunnable_preserves_ipcStateQueueMembershipConsistent st2 pair.1 hV3J2
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage atomically clears caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st3 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              exact removeRunnable_preserves_ipcStateQueueMembershipConsistent _ caller <|
                storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent
                  _ _ caller _ none hV3JE hObjInvE
                  (fun _ h => absurd h (by simp))
                  (fun _ h => absurd h (by simp))
                  (fun _ h => absurd h (by simp)) hIpc
      | none =>
        -- BLOCK PATH: Enqueue(sendQ) + storeTcbIpcStateAndMessage(.blockedOnCall) + removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
            endpointId false caller st st1 hObjInv hEnq
          have hV3J1 := endpointQueueEnqueue_preserves_ipcStateQueueMembershipConsistent
            endpointId false caller st st1 hInv hObjInv hDQWF hEnq
          have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
            endpointId false caller st st1 hEnq hDQSI hObjInv hFreshCaller hSendTailFresh
          have hNotTail : ∀ ep', st.objects[endpointId]? = some (.endpoint ep') →
              (if false then ep'.receiveQ else ep'.sendQ).tail ≠ some caller := by
            intro ep' hEp'
            rw [hObj] at hEp'; cases hEp'
            exact (hFreshCaller endpointId ep hObj).2.1
          have hReach := endpointQueueEnqueue_thread_reachable
            endpointId false caller st st1 hObjInv hNotTail hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hNeCallerEp : endpointId ≠ caller.toObjId := by
              intro h; unfold endpointQueueEnqueue at hEnq
              rw [hObj] at hEnq; simp only at hEnq
              cases hL : lookupTcb st caller with
              | none => simp [hL] at hEnq
              | some tcb =>
                have := lookupTcb_some_objects st caller tcb hL
                rw [← h, hObj] at this; cases this
            exact removeRunnable_preserves_ipcStateQueueMembershipConsistent st2 caller <|
              storeTcbIpcStateAndMessage_general_preserves_ipcStateQueueMembershipConsistent
                st1 st2 caller (.blockedOnCall endpointId) (some msg) hV3J1 hObjInv1 hMsg
                (fun _ h => absurd h (by simp))
                (fun _ h => absurd h (by simp))
                (fun epId hEq => by
                  cases hEq
                  obtain ⟨ep', hEp1, hR⟩ := hReach
                  have hEpFrame := storeTcbIpcStateAndMessage_preserves_objects_ne
                    st1 st2 caller (.blockedOnCall endpointId) (some msg)
                    endpointId hNeCallerEp hObjInv1 hMsg
                  rw [hEpFrame]
                  exact ⟨ep', hEp1, hR.elim Or.inl fun ⟨prev, prevTcb, hP, hQN⟩ => by
                    refine Or.inr ⟨prev, prevTcb, ?_, hQN⟩
                    have hNePrev : prev.toObjId ≠ caller.toObjId := by
                      intro h
                      have hPrevEq := ThreadId.toObjId_injective prev caller h
                      rw [hPrevEq] at hP
                      exact absurd hQN (tcbQueueChainAcyclic_no_self_loop hDQSI1.2.2 caller prevTcb hP)
                    rw [storeTcbIpcStateAndMessage_preserves_objects_ne
                      st1 st2 caller (.blockedOnCall endpointId) (some msg)
                      prev.toObjId hNePrev hObjInv1 hMsg]
                    exact hP⟩)

/-- V3-J compound: endpointReplyRecv preserves ipcStateQueueMembershipConsistent.
Composes reply phase (storeTcb + ensureRunnable) with endpointReceiveDual. -/
theorem endpointReplyRecv_preserves_ipcStateQueueMembershipConsistent
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hInvFull : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  have hInv := hInvFull.2.2.2.2.2.2.1
  have hDQSI := hInvFull.2.1
  have hQNBC := hInvFull.2.2.2.2.2.2.2.1
  have hQHBC := hInvFull.2.2.2.2.2.2.2.2.1
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some replyTcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : replyTcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ expectedReplier =>
      simp only [hIpc] at hStep
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
            ipcStateQueueMembershipConsistent stR.2) by
        -- AK1-B (I-H02): Fail-closed on expectedReplier = none
        cases expectedReplier with
        | none => simp at hStep
        | some expected =>
          simp only at hStep
          split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
      -- Main proof body
      intro st1 hMsg stR hRecv
      have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget _ (some msg) hObjInv hMsg
      have hV3J1 := storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent
        st st1 replyTarget .ready (some msg) hInv hObjInv
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h) hMsg
      have hDQSI1 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hObjInv hMsg hDQSI
      have hQNBC1 := storeTcbIpcStateAndMessage_ready_preserves_queueNextBlockingConsistent
        st st1 replyTarget (some msg) hQNBC hObjInv hMsg
      have hObjInvE : (ensureRunnable st1 replyTarget).objects.invExt :=
        ensureRunnable_preserves_objects st1 replyTarget ▸ hObjInv1
      have hV3JE := ensureRunnable_preserves_ipcStateQueueMembershipConsistent st1 replyTarget hV3J1
      have hDQSIE := ensureRunnable_preserves_dualQueueSystemInvariant st1 replyTarget hDQSI1
      have hQNBCE := ensureRunnable_preserves_queueNextBlockingConsistent st1 replyTarget hQNBC1
      -- QHBC: replyTarget was .blockedOnReply, so it's not a queue head by pre-state QHBC.
      -- storeTcbIpcStateAndMessage_preserves_queueHeadBlockedConsistent needs hNotHead.
      have hNotHead : ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
          st.objects[epId']? = some (.endpoint ep') →
          ep'.receiveQ.head ≠ some replyTarget ∧ ep'.sendQ.head ≠ some replyTarget := by
        intro epId' ep' hEp'
        constructor <;> intro hH
        · have := (hQHBC epId' ep' replyTarget replyTcb hEp'
            (lookupTcb_some_objects st replyTarget replyTcb hLookup)).1 hH
          rw [hIpc] at this; cases this
        · have := (hQHBC epId' ep' replyTarget replyTcb hEp'
            (lookupTcb_some_objects st replyTarget replyTcb hLookup)).2 hH
          rw [hIpc] at this; cases this with
          | inl h => cases h
          | inr h => cases h
      have hQHBC1 := storeTcbIpcStateAndMessage_preserves_queueHeadBlockedConsistent
        st st1 replyTarget .ready (some msg) hQHBC hObjInv hMsg hNotHead
      have hQHBCE := ensureRunnable_preserves_queueHeadBlockedConsistent st1 replyTarget hQHBC1
      -- Transport freshness conditions through reply phase
      have hFreshReceiver' : ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
          (ensureRunnable st1 replyTarget).objects[epId']? = some (.endpoint ep') →
          ep'.sendQ.head ≠ some receiver ∧ ep'.sendQ.tail ≠ some receiver ∧
          ep'.receiveQ.head ≠ some receiver ∧ ep'.receiveQ.tail ≠ some receiver := by
        intro epId' ep' hEp'
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp'
        exact hFreshReceiver epId' ep'
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId' ep' hObjInv hMsg hEp')
      have hRecvTailFresh' : ∀ (ep' : Endpoint) (tailTid : SeLe4n.ThreadId),
          (ensureRunnable st1 replyTarget).objects[endpointId]? = some (.endpoint ep') →
          ep'.receiveQ.tail = some tailTid →
          ∀ (epId' : SeLe4n.ObjId) (ep'' : Endpoint),
            (ensureRunnable st1 replyTarget).objects[epId']? = some (.endpoint ep'') →
            (epId' ≠ endpointId →
              ep''.sendQ.tail ≠ some tailTid ∧ ep''.receiveQ.tail ≠ some tailTid) ∧
            (epId' = endpointId →
              ep''.sendQ.tail ≠ some tailTid) := by
        intro ep' tailTid hEp' hTail epId' ep'' hEp''
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp' hEp''
        exact hRecvTailFresh ep' tailTid
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) endpointId ep' hObjInv hMsg hEp')
          hTail epId' ep''
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId' ep'' hObjInv hMsg hEp'')
      -- Delegate to endpointReceiveDual preservation
      exact endpointReceiveDual_preserves_ipcStateQueueMembershipConsistent
        endpointId receiver _ stR.2 stR.1
        hV3JE hDQSIE hQNBCE hQHBCE hObjInvE hFreshReceiver' hRecvTailFresh'
        (by have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)

/-- U4-K/R3-B: endpointSendDual preserves the full IPC invariant.
`allPendingMessagesBounded` and `badgeWellFormed` are now derived internally
from the pre-state invariant. Only `dualQueueSystemInvariant` requires freshness
preconditions from the caller. -/
theorem endpointSendDual_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointSendDual_preserves_ipcInvariant st st' endpointId sender msg hInv.1 hObjInv hStep,
   hDualQueue',
   endpointSendDual_preserves_allPendingMessagesBounded st st' endpointId sender msg hInv.2.2.1 hObjInv hStep,
   endpointSendDual_preserves_badgeWellFormed st st' endpointId sender msg hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', hDCA', hDOV', hPSI', hDBT', hUW', hBRT'⟩

/-- U4-K/R3-B: endpointReceiveDual preserves the full IPC invariant.
`allPendingMessagesBounded` and `badgeWellFormed` derived internally. -/
theorem endpointReceiveDual_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (receiver senderId : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    ipcInvariantFull st' :=
  ⟨endpointReceiveDual_preserves_ipcInvariant st st' endpointId receiver senderId hInv.1 hObjInv hStep,
   hDualQueue',
   endpointReceiveDual_preserves_allPendingMessagesBounded endpointId receiver senderId st st' hInv.2.2.1 hObjInv hStep,
   endpointReceiveDual_preserves_badgeWellFormed endpointId receiver senderId st st' hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', hDCA', hDOV', hPSI', hDBT', hUW', hBRT'⟩

/-- U4-K/R3-B: endpointCall preserves the full IPC invariant.
`allPendingMessagesBounded` and `badgeWellFormed` derived internally. -/
theorem endpointCall_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointCall_preserves_ipcInvariant st st' endpointId caller msg hInv.1 hObjInv hStep,
   hDualQueue',
   endpointCall_preserves_allPendingMessagesBounded st st' endpointId caller msg hInv.2.2.1 hObjInv hStep,
   endpointCall_preserves_badgeWellFormed st st' endpointId caller msg hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', hDCA', hDOV', hPSI', hDBT', hUW', hBRT'⟩

/-- U4-K: endpointReplyRecv preserves the full IPC invariant.
`allPendingMessagesBounded` and `badgeWellFormed` derived internally. -/
theorem endpointReplyRecv_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointReplyRecv_preserves_ipcInvariant st st' endpointId receiver replyTarget msg hInv.1 hObjInv hStep,
   hDualQueue',
   endpointReplyRecv_preserves_allPendingMessagesBounded st st' endpointId receiver replyTarget msg hInv.2.2.1 hObjInv hStep,
   endpointReplyRecv_preserves_badgeWellFormed st st' endpointId receiver replyTarget msg hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', hDCA', hDOV', hPSI', hDBT', hUW', hBRT'⟩

/-- T4-K (L-P10): Convenience theorem for composing `ipcInvariantFull` from its
individual components. Reduces boilerplate for callers that must manually
compose the invariant by providing all proofs in one call. -/
theorem ipcInvariantFull_compositional
    (st : SystemState)
    (hIpc : ipcInvariant st)
    (hDual : dualQueueSystemInvariant st)
    (hBounded : allPendingMessagesBounded st)
    (hBadge : badgeWellFormed st)
    (hWtpmn : waitingThreadsPendingMessageNone st)
    (hNoDup : endpointQueueNoDup st)
    (hQMC : ipcStateQueueMembershipConsistent st)
    (hQNBC : queueNextBlockingConsistent st)
    (hQHBC : queueHeadBlockedConsistent st)
    (hBlockedTimeout : blockedThreadTimeoutConsistent st)
    (hDCA : donationChainAcyclic st)
    (hDOV : donationOwnerValid st)
    (hPSI : passiveServerIdle st)
    (hDBT : donationBudgetTransfer st)
    (hUW : uniqueWaiters st)
    (hBRT : blockedOnReplyHasTarget st) :
    ipcInvariantFull st :=
  ⟨hIpc, hDual, hBounded, hBadge, hWtpmn, hNoDup, hQMC, hQNBC, hQHBC, hBlockedTimeout, hDCA, hDOV, hPSI, hDBT, hUW, hBRT⟩

-- ============================================================================
-- T4-E/F (M-IPC-3): WithCaps wrappers preserve ipcInvariantFull
-- ============================================================================

/-- T4-E (M-IPC-3): endpointSendDualWithCaps preserves the full IPC invariant.
Composes the proven ipcInvariant preservation with caller-supplied proofs for
the remaining three sub-invariants. -/
theorem endpointSendDualWithCaps_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
             senderCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    ipcInvariantFull st' :=
  ⟨endpointSendDualWithCaps_preserves_ipcInvariant endpointId sender msg
     endpointRights senderCspaceRoot receiverSlotBase st st' summary hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge', hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', hDCA', hDOV', hPSI', hDBT', hUW', hBRT'⟩

/-- T4-F (M-IPC-3): endpointReceiveDualWithCaps preserves the full IPC invariant.
Same composition pattern as T4-E for the receive path. -/
theorem endpointReceiveDualWithCaps_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (endpointRights : AccessRightSet)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hStep : endpointReceiveDualWithCaps endpointId receiver endpointRights
             receiverCspaceRoot receiverSlotBase st = .ok ((senderId, summary), st')) :
    ipcInvariantFull st' :=
  ⟨endpointReceiveDualWithCaps_preserves_ipcInvariant endpointId receiver endpointRights
     receiverCspaceRoot receiverSlotBase st st' senderId summary hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge', hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', hDCA', hDOV', hPSI', hDBT', hUW', hBRT'⟩

/-- T4-E (M-IPC-3): endpointCallWithCaps preserves the full IPC invariant. -/
theorem endpointCallWithCaps_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hStep : endpointCallWithCaps endpointId caller msg endpointRights
             callerCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    ipcInvariantFull st' :=
  ⟨endpointCallWithCaps_preserves_ipcInvariant endpointId caller msg
     endpointRights callerCspaceRoot receiverSlotBase st st' summary hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge', hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', hDCA', hDOV', hPSI', hDBT', hUW', hBRT'⟩

-- ============================================================================
-- WS-L3/L3-B: Standalone tcbQueueLinkIntegrity preservation
-- ============================================================================

/-- WS-L3/L3-B1: PopHead preserves `tcbQueueLinkIntegrity` as a standalone
property. Extracts from the bundled `dualQueueSystemInvariant` preservation. -/
theorem endpointQueuePopHead_preserves_tcbQueueLinkIntegrity
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hInv : dualQueueSystemInvariant st) :
    tcbQueueLinkIntegrity st' :=
  (endpointQueuePopHead_preserves_dualQueueSystemInvariant
    endpointId isReceiveQ st st' tid hObjInv hStep hInv).2.1

/-- WS-L3/L3-B2: Enqueue preserves `tcbQueueLinkIntegrity` as a standalone
property. Extracts from the bundled `dualQueueSystemInvariant` preservation. -/
theorem endpointQueueEnqueue_preserves_tcbQueueLinkIntegrity
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hInv : dualQueueSystemInvariant st)
    (hFreshTid : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some enqueueTid ∧ ep.sendQ.tail ≠ some enqueueTid ∧
      ep.receiveQ.head ≠ some enqueueTid ∧ ep.receiveQ.tail ≠ some enqueueTid)
    (hTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      (if isReceiveQ then ep.receiveQ else ep.sendQ).tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          (if isReceiveQ then ep'.sendQ else ep'.receiveQ).tail ≠ some tailTid)) :
    tcbQueueLinkIntegrity st' :=
  (endpointQueueEnqueue_preserves_dualQueueSystemInvariant
    endpointId isReceiveQ enqueueTid st st' hStep hInv hObjInv hFreshTid hTailFresh).2.1

-- ============================================================================
-- WS-L3/L3-C2: ipcStateQueueConsistent preservation for queue operations
-- ============================================================================

/-- WS-L3/L3-C2: PopHead preserves ipcStateQueueConsistent. PopHead does not
modify any thread's ipcState and preserves all endpoints, so the forward
implication (blocked → endpoint exists) is maintained. -/
theorem endpointQueuePopHead_preserves_ipcStateQueueConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  -- Step 1: find the pre-state TCB with same ipcState
  obtain ⟨tcb, hTcb, hIpc⟩ := endpointQueuePopHead_tcb_ipcState_backward
    endpointId isReceiveQ st st' tid tid' tcb' hObjInv hStep hTcb'
  -- Step 2: apply pre-state invariant
  have hPre := hInv tid' tcb hTcb
  -- Step 3: show endpoints survive the operation
  rw [← hIpc]
  match h : tcb.ipcState with
  | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hObjInv hStep hEp
  | .blockedOnReceive epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hObjInv hStep hEp
  | .blockedOnCall epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hObjInv hStep hEp

/-- WS-L3/L3-C2: Enqueue preserves ipcStateQueueConsistent. Enqueue does not
modify any thread's ipcState and preserves all endpoints. -/
theorem endpointQueueEnqueue_preserves_ipcStateQueueConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  obtain ⟨tcb, hTcb, hIpc⟩ := endpointQueueEnqueue_tcb_ipcState_backward
    endpointId isReceiveQ enqueueTid st st' tid' tcb' hObjInv hStep hTcb'
  have hPre := hInv tid' tcb hTcb
  rw [← hIpc]
  match h : tcb.ipcState with
  | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hObjInv hStep hEp
  | .blockedOnReceive epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hObjInv hStep hEp
  | .blockedOnCall epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hObjInv hStep hEp

-- ============================================================================
-- WS-L3/L3-C3: ipcStateQueueConsistent preservation — sub-operation helpers
-- ============================================================================

/-- WS-L3/L3-C3 helper: `ensureRunnable` preserves `ipcStateQueueConsistent`.
`ensureRunnable` only modifies the scheduler (run queue), not objects. -/
theorem ensureRunnable_preserves_ipcStateQueueConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent (ensureRunnable st tid) := by
  unfold ipcStateQueueConsistent
  simp only [ensureRunnable_preserves_objects]
  exact hInv

/-- WS-L3/L3-C3 helper: `removeRunnable` preserves `ipcStateQueueConsistent`.
`removeRunnable` only modifies the scheduler, not objects. -/
theorem removeRunnable_preserves_ipcStateQueueConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent (removeRunnable st tid) := by
  unfold ipcStateQueueConsistent
  simp only [removeRunnable_preserves_objects]
  exact hInv

/-- WS-L3/L3-C3 helper: `storeTcbIpcStateAndMessage` preserves
`ipcStateQueueConsistent` when the new ipcState satisfies the invariant
obligation in the pre-state. Specifically:
- If ipc = blockedOnSend/Receive/Call epId, then the endpoint at epId
  must exist in the pre-state (the operation preserves it).
- If ipc = ready/blockedOnReply/blockedOnNotification, no obligation. -/
theorem storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hInv : ipcStateQueueConsistent st)
    (hNewIpc : match ipc with
      | .blockedOnSend epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnReceive epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnCall epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | _ => True) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  by_cases hEq : tid'.toObjId = tid.toObjId
  · -- Target TCB: ipcState was set to `ipc`
    have hIpcEq := storeTcbIpcStateAndMessage_ipcState_eq st st' tid ipc msg hObjInv hStep tcb' (hEq ▸ hTcb')
    rw [hIpcEq]
    cases ipc with
    | ready | blockedOnNotification _ | blockedOnReply _ _ => trivial
    | blockedOnSend epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid _ msg epId ep hObjInv hEp hStep⟩
    | blockedOnReceive epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid _ msg epId ep hObjInv hEp hStep⟩
    | blockedOnCall epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid _ msg epId ep hObjInv hEp hStep⟩
  · -- Non-target TCB: object unchanged, pre-state invariant applies
    have hObjEq := storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg tid'.toObjId hEq hObjInv hStep
    rw [hObjEq] at hTcb'
    have hPre := hInv tid' tcb' hTcb'
    match h : tcb'.ipcState with
    | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
    | .blockedOnSend epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid ipc msg epId ep hObjInv hEp hStep⟩
    | .blockedOnReceive epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid ipc msg epId ep hObjInv hEp hStep⟩
    | .blockedOnCall epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid ipc msg epId ep hObjInv hEp hStep⟩

/-- WS-L3/L3-C3 helper: `storeTcbIpcState` preserves `ipcStateQueueConsistent`
under the same conditions as `storeTcbIpcStateAndMessage`. -/
theorem storeTcbIpcState_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hInv : ipcStateQueueConsistent st)
    (hNewIpc : match ipc with
      | .blockedOnSend epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnReceive epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnCall epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | _ => True) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  by_cases hEq : tid'.toObjId = tid.toObjId
  · have hIpcEq := storeTcbIpcState_ipcState_eq st st' tid ipc hObjInv hStep tcb' (hEq ▸ hTcb')
    rw [hIpcEq]
    cases ipc with
    | ready | blockedOnNotification _ | blockedOnReply _ _ => trivial
    | blockedOnSend epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid _ epId ep hEp hObjInv hStep⟩
    | blockedOnReceive epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid _ epId ep hEp hObjInv hStep⟩
    | blockedOnCall epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid _ epId ep hEp hObjInv hStep⟩
  · have hObjEq := storeTcbIpcState_preserves_objects_ne st st' tid ipc tid'.toObjId hEq hObjInv hStep
    rw [hObjEq] at hTcb'
    have hPre := hInv tid' tcb' hTcb'
    match h : tcb'.ipcState with
    | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
    | .blockedOnSend epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid ipc epId ep hEp hObjInv hStep⟩
    | .blockedOnReceive epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid ipc epId ep hEp hObjInv hStep⟩
    | .blockedOnCall epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid ipc epId ep hEp hObjInv hStep⟩

/-- WS-L3/L3-C3 helper: `storeTcbPendingMessage` preserves
`ipcStateQueueConsistent`. This operation only changes pendingMessage,
not ipcState, so the invariant is trivially preserved. -/
theorem storeTcbPendingMessage_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  obtain ⟨tcb, hTcb, hIpc⟩ := storeTcbPendingMessage_tcb_ipcState_backward st st' tid msg tid' tcb' hObjInv hStep hTcb'
  have hPre := hInv tid' tcb hTcb
  rw [← hIpc]
  match h : tcb.ipcState with
  | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact ⟨ep, storeTcbPendingMessage_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩
  | .blockedOnReceive epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact ⟨ep, storeTcbPendingMessage_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩
  | .blockedOnCall epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact ⟨ep, storeTcbPendingMessage_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩

-- ============================================================================
-- WS-L3/L3-C3: ipcStateQueueConsistent preservation — high-level IPC ops
-- ============================================================================

/-- WS-L3/L3-C3: endpointSendDual preserves ipcStateQueueConsistent.
Handshake path: PopHead (preserves) → storeTcbIpcStateAndMessage to .ready
(removes obligation) → ensureRunnable (preserves).
Blocking path: Enqueue (preserves) → storeTcbIpcStateAndMessage to
.blockedOnSend endpointId (endpoint exists from initial lookup) →
removeRunnable (preserves). -/
theorem endpointSendDual_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          obtain ⟨receiver, _tcb, stPop⟩ := triple
          cases hMsg : storeTcbIpcStateAndMessage stPop receiver .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hObjInvPop : stPop.objects.invExt :=
              endpointQueuePopHead_preserves_objects_invExt endpointId true st stPop receiver _tcb hObjInv hPop
            exact ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvPop hMsg
                (endpointQueuePopHead_preserves_ipcStateQueueConsistent endpointId true st stPop receiver _tcb
                  hObjInv hPop hInv) trivial
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hObjInvEnq : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
            exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvEnq hMsg
                (endpointQueueEnqueue_preserves_ipcStateQueueConsistent endpointId false sender st st1
                  hObjInv hEnq hInv)
                (endpointQueueEnqueue_endpoint_forward _ _ sender st st1 endpointId ep hObjInv hEnq hObj)

/-- WS-L3/L3-C3: endpointReceiveDual preserves ipcStateQueueConsistent.
Rendezvous (call): PopHead → storeTcbIpcStateAndMessage(.blockedOnReply, trivial)
→ storeTcbPendingMessage (preserves).
Rendezvous (send): PopHead → storeTcbIpcStateAndMessage(.ready, trivial) →
ensureRunnable → storeTcbPendingMessage (preserves).
Blocking: Enqueue → storeTcbIpcState(.blockedOnReceive epId, endpoint exists)
→ removeRunnable (preserves). -/
theorem endpointReceiveDual_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver resultTid : SeLe4n.ThreadId)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (resultTid, st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          obtain ⟨sender, senderTcb, stPop⟩ := triple
          have hObjInvPop : stPop.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId false st stPop sender senderTcb hObjInv hPop
          have hInvPop := endpointQueuePopHead_preserves_ipcStateQueueConsistent
            endpointId false st stPop sender senderTcb hObjInv hPop hInv
          -- Branch on senderWasCall
          split at hStep
          · -- Call path: storeTcbIpcStateAndMessage(.blockedOnReply) → storeTcbPendingMessage
            cases hMsg : storeTcbIpcStateAndMessage stPop sender (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPM : storeTcbIpcStateAndMessage st2 receiver .ready senderTcb.pendingMessage with
              | error e => simp [hPM] at hStep
              | ok st3 =>
                simp only [hPM] at hStep
                have hEq : st3 = st' := by
                  have := Except.ok.inj hStep; exact (Prod.mk.inj this).2
                subst hEq
                have hObjInvMsg : st2.objects.invExt :=
                  storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 sender _ _ hObjInvPop hMsg
                exact storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvMsg hPM
                  (storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvPop hMsg hInvPop trivial) trivial
          · -- Send path: storeTcbIpcStateAndMessage(.ready) → ensureRunnable → storeTcbPendingMessage
            cases hMsg : storeTcbIpcStateAndMessage stPop sender .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPM : storeTcbIpcStateAndMessage (ensureRunnable st2 sender) receiver .ready senderTcb.pendingMessage with
              | error e => simp [hPM] at hStep
              | ok st3 =>
                simp only [hPM] at hStep
                have hEq : st3 = st' := by
                  have := Except.ok.inj hStep; exact (Prod.mk.inj this).2
                subst hEq
                have hObjInvMsgS : st2.objects.invExt :=
                  storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 sender _ _ hObjInvPop hMsg
                have hObjInvEns : (ensureRunnable st2 sender).objects.invExt :=
                  ensureRunnable_preserves_objects st2 sender ▸ hObjInvMsgS
                exact storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvEns hPM
                  (ensureRunnable_preserves_ipcStateQueueConsistent _ _
                    (storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvPop hMsg hInvPop trivial)) trivial
      | none =>
        -- AI4-A: cleanupPreReceiveDonation before enqueue
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hInvClean := cleanupPreReceiveDonation_preserves_ipcStateQueueConsistent st receiver hObjInv hInv
          have hObjClean := cleanupPreReceiveDonation_endpoint_forward st receiver hObjInv endpointId ep hObj
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hObjInvEnqR : st1.objects.invExt :=
                endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
              exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
                storeTcbIpcState_preserves_ipcStateQueueConsistent _ _ _ _ hObjInvEnqR hIpc
                  (endpointQueueEnqueue_preserves_ipcStateQueueConsistent endpointId true receiver (cleanupPreReceiveDonation st receiver) st1
                    hObjInvClean hEnq hInvClean)
                  (endpointQueueEnqueue_endpoint_forward _ _ receiver (cleanupPreReceiveDonation st receiver) st1 endpointId ep hObjInvClean hEnq hObjClean)

/-- WS-L3/L3-C3: endpointReply preserves ipcStateQueueConsistent.
Reply sets target from blockedOnReply to .ready (removes obligation),
then ensureRunnable (preserves). The _fromTcb variant is rewritten to
the standard form via the equivalence theorem. -/
theorem endpointReply_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      -- Rewrite _fromTcb to standard form
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      -- AK1-B (I-H02): Fail-closed on replyTarget = none
      cases replyTarget with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · -- authorized = true
          cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore] at hStep
            have hEq := (Prod.mk.inj (Except.ok.inj hStep)).2; rw [← hEq]
            exact ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInv hStore hInv trivial
        · -- authorized = false → error
          simp at hStep
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ | blockedOnNotification _ =>
      simp [hIpc] at hStep

-- ============================================================================
-- T4-A/B/C (M-IPC-1): ipcStateQueueConsistent preservation for compound ops
-- ============================================================================

/-- T4-A (M-IPC-1): storeObject on a notification preserves ipcStateQueueConsistent.
Notification objects are neither TCBs nor endpoints, so the invariant—which only
queries TCB ipcState and endpoint existence—is trivially preserved. -/
theorem storeObject_notification_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (nid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : ∃ ntfn', st.objects[nid]? = some (.notification ntfn'))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject nid (.notification ntfn) st = .ok ((), st'))
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid tcb hTcb
  have hNeTcb : tid.toObjId ≠ nid := by
    intro h; obtain ⟨n', hn'⟩ := hNtfn
    rw [h, storeObject_objects_eq st st' nid _ hObjInv hStore] at hTcb; cases hTcb
  rw [storeObject_objects_ne st st' nid tid.toObjId _ hNeTcb hObjInv hStore] at hTcb
  have hOrig := hInv tid tcb hTcb
  cases hIpc : tcb.ipcState with
  | blockedOnSend epId =>
    simp only [hIpc] at hOrig; obtain ⟨ep, hEp⟩ := hOrig
    have hNeEp : epId ≠ nid := by
      intro h; obtain ⟨n', hn'⟩ := hNtfn; rw [h] at hEp; rw [hn'] at hEp; cases hEp
    exact ⟨ep, by rw [storeObject_objects_ne st st' nid epId _ hNeEp hObjInv hStore]; exact hEp⟩
  | blockedOnReceive epId =>
    simp only [hIpc] at hOrig; obtain ⟨ep, hEp⟩ := hOrig
    have hNeEp : epId ≠ nid := by
      intro h; obtain ⟨n', hn'⟩ := hNtfn; rw [h] at hEp; rw [hn'] at hEp; cases hEp
    exact ⟨ep, by rw [storeObject_objects_ne st st' nid epId _ hNeEp hObjInv hStore]; exact hEp⟩
  | blockedOnCall epId =>
    simp only [hIpc] at hOrig; obtain ⟨ep, hEp⟩ := hOrig
    have hNeEp : epId ≠ nid := by
      intro h; obtain ⟨n', hn'⟩ := hNtfn; rw [h] at hEp; rw [hn'] at hEp; cases hEp
    exact ⟨ep, by rw [storeObject_objects_ne st st' nid epId _ hNeEp hObjInv hStore]; exact hEp⟩
  | ready | blockedOnReply _ _ | blockedOnNotification _ => trivial

/-- T4-C (M-IPC-1): notificationSignal preserves ipcStateQueueConsistent.
Signal either wakes a waiter (→ .ready, trivial) or accumulates a badge
(notification-only update, no TCB ipcState change). -/
theorem notificationSignal_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
        -- Wake path: storeObject (notification) → storeTcbIpcStateAndMessage (waiter, .ready) → ensureRunnable
        simp only [hWaiters] at hStep
        generalize hStore1 : storeObject notificationId _ st = r1 at hStep
        cases r1 with
        | error e => simp at hStep
        | ok pair1 =>
          simp only [] at hStep
          generalize hMsg : storeTcbIpcStateAndMessage pair1.2 waiter .ready _ = rMsg at hStep
          cases rMsg with
          | error e => simp at hStep
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
            exact ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInv1 hMsg
                (storeObject_notification_preserves_ipcStateQueueConsistent st pair1.2 notificationId _
                  ⟨ntfn, hObj⟩ hObjInv hStore1 hInv) trivial
      | nil =>
        -- Accumulate path: storeObject (notification) only
        simp only [hWaiters] at hStep
        exact storeObject_notification_preserves_ipcStateQueueConsistent st st' notificationId _
          ⟨ntfn, hObj⟩ hObjInv hStep hInv

/-- T4-C (M-IPC-1): notificationWait preserves ipcStateQueueConsistent.
Wait either consumes a pending badge (→ .ready, trivial) or blocks the waiter
on the notification (→ .blockedOnNotification, which is _ => True). -/
theorem notificationWait_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (result : Option SeLe4n.Badge)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcStateQueueConsistent st' := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        -- Consume path: storeObject (notification) → storeTcbIpcState (waiter, .ready)
        simp only [hBadge] at hStep
        generalize hStore1 : storeObject notificationId _ st = r1 at hStep
        cases r1 with
        | error e => simp at hStep
        | ok pair1 =>
          simp only [] at hStep
          cases hIpc : storeTcbIpcState pair1.2 waiter .ready with
          | error e => simp [hIpc] at hStep
          | ok st2 =>
            simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨rfl, rfl⟩ := hStep
            have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
            exact storeTcbIpcState_preserves_ipcStateQueueConsistent _ _ _ _ hObjInv1 hIpc
              (storeObject_notification_preserves_ipcStateQueueConsistent st pair1.2 notificationId _
                ⟨ntfn, hObj⟩ hObjInv hStore1 hInv) trivial
      | none =>
        -- Block path: lookupTcb → storeObject (notification) → storeTcbIpcState_fromTcb (.blockedOnNotification) → removeRunnable
        simp only [hBadge] at hStep
        cases hLookup : lookupTcb st waiter with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          split at hStep
          · simp at hStep -- already waiting → error
          · generalize hStore1 : storeObject notificationId _ st = r1 at hStep
            cases r1 with
            | error e => simp at hStep
            | ok pair1 =>
              simp only [] at hStep
              have hTcbObj := lookupTcb_some_objects st waiter tcb hLookup
              have hNe : waiter.toObjId ≠ notificationId := by
                intro h; rw [h] at hTcbObj; rw [hObj] at hTcbObj; cases hTcbObj
              have hTcbObj' : pair1.2.objects[waiter.toObjId]? = some (.tcb tcb) := by
                rw [storeObject_objects_ne st pair1.2 notificationId waiter.toObjId _ hNe hObjInv hStore1]
                exact hTcbObj
              have hLookup' : lookupTcb pair1.2 waiter = some tcb := by
                unfold lookupTcb; split
                · -- isReserved: contradiction (original lookupTcb succeeded so not reserved)
                  rename_i hRes
                  unfold lookupTcb at hLookup; simp [hRes] at hLookup
                · rw [hTcbObj']
              rw [storeTcbIpcState_fromTcb_eq hLookup'] at hStep
              cases hIpc : storeTcbIpcState pair1.2 waiter (.blockedOnNotification notificationId) with
              | error e => simp [hIpc] at hStep
              | ok st2 =>
                simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨rfl, rfl⟩ := hStep
                have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
                exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
                  storeTcbIpcState_preserves_ipcStateQueueConsistent _ _ _ _ hObjInv1 hIpc
                    (storeObject_notification_preserves_ipcStateQueueConsistent st pair1.2 notificationId _
                      ⟨ntfn, hObj⟩ hObjInv hStore1 hInv) trivial

/-- T4-A (M-IPC-1): endpointCall preserves ipcStateQueueConsistent.
The handshake path sets receiver to .ready (trivial) and caller to .blockedOnReply
(falls under _ => True). The blocking path sets caller to .blockedOnCall with
an endpoint existence obligation discharged by endpointQueueEnqueue_endpoint_forward. -/
theorem endpointCall_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake path: PopHead → storeTcbIpcStateAndMessage(receiver, .ready) → ensureRunnable →
        --                 storeTcbIpcState(caller, .blockedOnReply) → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          obtain ⟨receiver, _tcb, stPop⟩ := triple
          cases hMsg : storeTcbIpcStateAndMessage stPop receiver .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInvPop := endpointQueuePopHead_preserves_objects_invExt endpointId true st stPop receiver _tcb hObjInv hPop
            have hObjInvMsg := storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 receiver _ _ hObjInvPop hMsg
            have hObjInvEns := ensureRunnable_preserves_objects st2 receiver ▸ hObjInvMsg
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage atomically clears caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 receiver) caller (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hIpc] at hStep
            | ok st3 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
                storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ none hObjInvEns hIpc
                  (ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
                    storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvPop hMsg
                      (endpointQueuePopHead_preserves_ipcStateQueueConsistent endpointId true st stPop receiver _tcb
                        hObjInv hPop hInv) trivial) trivial
      | none =>
        -- Blocking path: Enqueue → storeTcbIpcStateAndMessage(caller, .blockedOnCall) → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            have hObjInvEnq := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
            exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvEnq hMsg
                (endpointQueueEnqueue_preserves_ipcStateQueueConsistent endpointId false caller st st1
                  hObjInv hEnq hInv)
                (endpointQueueEnqueue_endpoint_forward _ _ caller st st1 endpointId ep hObjInv hEnq hObj)

/-- T4-B (M-IPC-1): endpointReplyRecv preserves ipcStateQueueConsistent.
ReplyRecv first replies (target → .ready, trivial obligation), then enters
the full endpointReceiveDual path, which has proven preservation. -/
theorem endpointReplyRecv_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpcS : tcb.ipcState with
    | blockedOnReply epId replyTarget' =>
      simp only [hIpcS] at hStep
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      -- AK1-B (I-H02): Fail-closed on replyTarget' = none
      cases replyTarget' with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · -- authorized
          cases hStore : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st1 =>
            simp only [hStore] at hStep
            have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget _ _ hObjInv hStore
            have hInv1 := storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInv hStore hInv trivial
            have hObjInvEns := ensureRunnable_preserves_objects st1 replyTarget ▸ hObjInv1
            have hInvEns := ensureRunnable_preserves_ipcStateQueueConsistent st1 replyTarget hInv1
            -- endpointReceiveDual on ensured state
            generalize hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = rRecv at hStep
            cases rRecv with
            | error e => simp at hStep
            | ok pair =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              exact endpointReceiveDual_preserves_ipcStateQueueConsistent _ _ _ _ pair.1 hInvEns hObjInvEns hRecv
        · simp at hStep -- unauthorized → error
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ | blockedOnNotification _ =>
      simp [hIpcS] at hStep

end SeLe4n.Kernel
