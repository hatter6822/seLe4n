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

/-! # IPC Structural Preservation — Part 2 (StoreObjectFrame)

Extracted from `SeLe4n.Kernel.IPC.Invariant.Structural` as part of
AN3-C (IPC-M02 / Theme 4.7) to keep each module under the
2000-LOC maintenance ceiling.  Declarations are unchanged in order,
content, and proof; only the file boundary has moved.  The parent
`Structural.lean` re-exports every child so all existing
`import SeLe4n.Kernel.IPC.Invariant.Structural` consumers continue
to typecheck without modification.

Contains the per-operation preservation of `dualQueueSystemInvariant`
for the compound IPC entry points (`endpointSendDual`,
`endpointReceiveDual`, `endpointCall`, the `endpointQueueEnqueue` /
`endpointQueuePopHead` pair), plus the `contextMatchesCurrent`
preservation cluster and the `allPendingMessagesBounded` frame lemma
family (U4-K / WS-H12e).
-/

-- AN3-C: linter directives inherited from parent Structural.lean.
set_option linter.unusedVariables false

namespace SeLe4n.Kernel

open SeLe4n.Model




/-- WS-H5: endpointSendDual preserves dualQueueSystemInvariant.
Requires freshness preconditions for the enqueue path. -/
theorem endpointSendDual_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : (endpointSendDual endpointId sender msg) st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st)
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
          ep'.receiveQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointSendDual at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.receiveQ.head with
      | some rcvr =>
        -- Path A: dequeue receiver, transfer message, unblock
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          cases hStore : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            obtain ⟨rcvr, headTcb1, stPop⟩ := pair
            have hInv1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant
              endpointId true st stPop rcvr hObjInv hPop hInv
            have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
              endpointId true st stPop rcvr headTcb1 hObjInv hPop
            exact ensureRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                stPop st2 rcvr .ready (some msg) hObjInv1 hStore hInv1)
      | none =>
        -- Path B: enqueue sender, store message, block
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          cases hStore : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInv1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
              endpointId false sender st st1 hEnq hInv hObjInv hFreshSender hSendTailFresh
            have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
              endpointId false sender st st1 hObjInv hEnq
            exact removeRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                st1 st2 sender (.blockedOnSend endpointId) (some msg) hObjInv1 hStore hInv1)

/-- WS-H5: endpointReceiveDual preserves dualQueueSystemInvariant.
Requires freshness preconditions for the enqueue path. -/
theorem endpointReceiveDual_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : (endpointReceiveDual endpointId receiver) st = .ok (senderId, st'))
    (hInv : dualQueueSystemInvariant st)
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
          ep'.sendQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.sendQ.head with
      | some sndr =>
        -- Path A: dequeue sender, transfer message/unblock
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          have hInv1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant
            _ _ _ _ _ hObjInv hPop hInv
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          -- Case-split on returned TCB's ipcState to determine senderWasCall
          cases hSenderIpc : pair.2.1.ipcState with
          | blockedOnCall epCall =>
            -- Call path: senderWasCall = true
            simp only [hSenderIpc, ite_true] at hStep
            cases hStore : storeTcbIpcStateAndMessage pair.2.2 pair.1
                (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hMsg : storeTcbIpcStateAndMessage st2 receiver .ready pair.2.1.pendingMessage with
              | error e => simp [hMsg] at hStep
              | ok st3 =>
                simp only [hMsg] at hStep; rcases hStep with ⟨-, rfl⟩
                have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
                  pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInv1 hStore
                exact storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                  st2 _ receiver .ready pair.2.1.pendingMessage hObjInv2 hMsg
                  (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                    pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInv1 hStore hInv1)
          | ready | blockedOnSend _ | blockedOnReceive _
            | blockedOnReply _ _ | blockedOnNotification _ =>
            -- Send path: senderWasCall = false
            simp only [hSenderIpc] at hStep
            cases hStore : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hMsg : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready
                  pair.2.1.pendingMessage with
              | error e => simp [hMsg] at hStep
              | ok st3 =>
                simp only [hMsg] at hStep; rcases hStep with ⟨-, rfl⟩
                have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
                  pair.2.2 st2 pair.1 .ready none hObjInv1 hStore
                have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt :=
                  ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInv2
                exact storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                  (ensureRunnable st2 pair.1) _ receiver .ready pair.2.1.pendingMessage hObjInvEns hMsg
                  (ensureRunnable_preserves_dualQueueSystemInvariant _ _
                    (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                      pair.2.2 st2 pair.1 .ready none hObjInv1 hStore hInv1))
      | none =>
        -- Path B: cleanup → enqueue receiver, block
        -- AI4-A: cleanupPreReceiveDonation preserves all preconditions because
        -- endpoint objects are unchanged (only TCB schedContextBinding + SchedContext modified).
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        simp only [hHead] at hStep
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          -- AI4-A-SORRY: dualQueueSystemInvariant, hFreshReceiver, hRecvTailFresh preserved
          have hInvClean : dualQueueSystemInvariant (cleanupPreReceiveDonation st receiver) :=
            cleanupPreReceiveDonation_preserves_dualQueueSystemInvariant st receiver hObjInv hInv
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
            cases hStore : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep; rcases hStep with ⟨-, rfl⟩
              have hInv1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
                endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hEnq hInvClean hObjInvClean hFreshReceiverClean hRecvTailFreshClean
              have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
                endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
              exact removeRunnable_preserves_dualQueueSystemInvariant _ _
                (storeTcbIpcState_preserves_dualQueueSystemInvariant st1 st2 receiver _ hObjInv1 hStore hInv1)

/-- WS-H12a: endpointReplyRecv preserves dualQueueSystemInvariant.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation.
Freshness preconditions are transported through the reply phase since
storeTcbIpcStateAndMessage and ensureRunnable do not modify endpoint objects. -/
theorem endpointReplyRecv_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : (endpointReplyRecv endpointId receiver replyTarget msg) st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st)
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
          ep'.sendQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointReplyRecv at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
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
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
            dualQueueSystemInvariant stR.2) by
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
      intro st1 hMsg stR hRecv
      have hInv1 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hObjInv hMsg hInv
      have hInv2 := ensureRunnable_preserves_dualQueueSystemInvariant st1 replyTarget hInv1
      -- Transport freshness: storeTcbIpcStateAndMessage + ensureRunnable don't modify endpoint objects
      -- Transport freshness through storeTcbIpcStateAndMessage + ensureRunnable
      -- Both operations preserve endpoint objects (only modify TCBs/scheduler)
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
      have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt
        st st1 replyTarget .ready (some msg) hObjInv hMsg
      have hObjInvEns1 : (ensureRunnable st1 replyTarget).objects.invExt :=
        ensureRunnable_preserves_objects st1 replyTarget ▸ hObjInv1
      exact endpointReceiveDual_preserves_dualQueueSystemInvariant _ _ _ stR.2 stR.1
        hObjInvEns1
        (by have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)
        hInv2 hFreshReceiver' hRecvTailFresh'

/-- WS-H5: endpointCall preserves dualQueueSystemInvariant.
Requires freshness preconditions for the enqueue path. -/
theorem endpointCall_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : (endpointCall endpointId caller msg) st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st)
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
          ep'.receiveQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointCall at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.receiveQ.head with
      | some rcvr =>
        -- Path A: dequeue receiver, transfer message, block caller for reply
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          have hInv1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant
            _ _ _ _ _ hObjInv hPop hInv
          have hObjInvPop1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          cases hStore1 : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hStore1] at hStep
          | ok st2 =>
            simp only [hStore1] at hStep
            have hInv2 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
              pair.2.2 st2 pair.1 .ready (some msg) hObjInvPop1 hStore1 hInv1
            have hObjInvSt2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              pair.2.2 st2 pair.1 .ready (some msg) hObjInvPop1 hStore1
            have hObjInvEns2 : (ensureRunnable st2 pair.1).objects.invExt :=
              ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInvSt2
            have hInv3 := ensureRunnable_preserves_dualQueueSystemInvariant st2 pair.1 hInv2
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage atomically clears caller's pendingMessage
            cases hStore2 : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller
                (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hStore2] at hStep
            | ok st3 =>
              simp only [hStore2, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact removeRunnable_preserves_dualQueueSystemInvariant _ _
                (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                  (ensureRunnable st2 pair.1) st3 caller _ none hObjInvEns2 hStore2 hInv3)
      | none =>
        -- Path B: enqueue caller, store message, block
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          cases hStore : storeTcbIpcStateAndMessage st1 caller
              (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInvEnq := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
              endpointId false caller st st1 hEnq hInv hObjInv hFreshCaller hSendTailFresh
            have hObjInvEnq := endpointQueueEnqueue_preserves_objects_invExt
              endpointId false caller st st1 hObjInv hEnq
            exact removeRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                st1 st2 caller (.blockedOnCall endpointId) (some msg) hObjInvEnq hStore hInvEnq)

-- ============================================================================
-- WS-H12c/H-03: contextMatchesCurrent preservation for IPC operations
-- ============================================================================

/-- WS-H12c: `storeObject` preserves `contextMatchesCurrent` when the stored
object at the current thread's ID preserves `registerContext`.

Requires `currentThreadValid` to exclude the impossible case where the current
thread has no TCB in the object store. -/
theorem storeObject_preserves_contextMatchesCurrent
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hRegCtx : ∀ tid tcb, st.scheduler.current = some tid → tid.toObjId = oid →
      st.objects[oid]? = some (.tcb tcb) →
      ∃ tcb', obj = .tcb tcb' ∧ tcb'.registerContext = tcb.registerContext) :
    contextMatchesCurrent st' := by
  have hSched : st'.scheduler = st.scheduler := storeObject_scheduler_eq st st' oid obj hStore
  have hMach : st'.machine = st.machine := storeObject_machine_eq st st' oid obj hStore
  unfold contextMatchesCurrent at hInv ⊢; rw [hSched, hMach]
  cases hCur : st.scheduler.current with
  | none => trivial
  | some tid =>
    simp only [hCur] at hInv ⊢
    simp only [currentThreadValid, hCur] at hValid
    obtain ⟨curTcb, hCurTcb⟩ := hValid
    by_cases hEq : tid.toObjId = oid
    · rw [hEq, storeObject_objects_eq st st' oid obj hObjInv hStore]
      obtain ⟨tcb', hNew, hReg⟩ := hRegCtx tid curTcb hCur hEq (hEq ▸ hCurTcb)
      rw [hNew]; simp only []
      simp only [hCurTcb] at hInv; rw [hReg]; exact hInv
    · rw [storeObject_objects_ne st st' oid tid.toObjId obj hEq hObjInv hStore]; exact hInv

/-- WS-H12c: IPC TCB stores preserve `contextMatchesCurrent`. -/
theorem storeTcbIpcState_preserves_contextMatchesCurrent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    contextMatchesCurrent st' := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hObjInv hStore
        (fun tid' tcb' hCur hEq hObj => by
          have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
          rw [hTcbObj] at hObj; cases hObj
          exact ⟨{ tcb with ipcState := ipc }, rfl, rfl⟩)

theorem storeTcbIpcStateAndMessage_preserves_contextMatchesCurrent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    contextMatchesCurrent st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hObjInv hStore
        (fun tid' tcb' hCur hEq hObj => by
          have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
          rw [hTcbObj] at hObj; cases hObj
          exact ⟨{ tcb with ipcState := ipc, pendingMessage := msg }, rfl, rfl⟩)

theorem storeTcbPendingMessage_preserves_contextMatchesCurrent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    contextMatchesCurrent st' := by
  unfold storeTcbPendingMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hObjInv hStore
        (fun tid' tcb' hCur hEq hObj => by
          have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
          rw [hTcbObj] at hObj; cases hObj
          exact ⟨{ tcb with pendingMessage := msg }, rfl, rfl⟩)

theorem storeTcbQueueLinks_preserves_contextMatchesCurrent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : contextMatchesCurrent st)
    (hValid : currentThreadValid st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    contextMatchesCurrent st' := by
  unfold storeTcbQueueLinks at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    simp only [tcbWithQueueLinks] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with queuePrev := prev, queuePPrev := pprev, queueNext := next }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      exact storeObject_preserves_contextMatchesCurrent st pair.2 tid.toObjId _ hInv hValid hObjInv hStore
        (fun tid' tcb' hCur hEq hObj => by
          have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
          rw [hTcbObj] at hObj; cases hObj
          exact ⟨{ tcb with queuePrev := prev, queuePPrev := pprev, queueNext := next }, rfl, rfl⟩)

/-- WS-H12c: `ensureRunnable` preserves `contextMatchesCurrent`. -/
theorem ensureRunnable_preserves_contextMatchesCurrent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : contextMatchesCurrent st) :
    contextMatchesCurrent (ensureRunnable st tid) := by
  unfold ensureRunnable
  split
  · exact hInv
  · cases hObj : st.objects[tid.toObjId]? with
    | none => exact hInv
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [contextMatchesCurrent]
        cases hCur : st.scheduler.current with
        | none => trivial
        | some curTid =>
          simp only [contextMatchesCurrent, hCur] at hInv
          exact hInv
      | _ => exact hInv

/-- WS-H12c: `removeRunnable` preserves `contextMatchesCurrent`. -/
theorem removeRunnable_preserves_contextMatchesCurrent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : contextMatchesCurrent st) :
    contextMatchesCurrent (removeRunnable st tid) := by
  simp only [removeRunnable]
  show contextMatchesCurrent { st with scheduler := { st.scheduler with
    runQueue := st.scheduler.runQueue.remove tid,
    current := if st.scheduler.current = some tid then none else st.scheduler.current } }
  simp only [contextMatchesCurrent]
  by_cases hEq : st.scheduler.current = some tid
  · simp only [hEq, ite_true]
  · simp only [hEq, ite_false]; exact hInv

-- ============================================================================
-- WS-H12e: allPendingMessagesBounded preservation (frame lemmas)
-- Deferred from WS-H12d — see CHANGELOG v0.14.1 line 77.
-- ============================================================================

/-- WS-H12e: ensureRunnable preserves allPendingMessagesBounded.
ensureRunnable only modifies scheduler state; the object store is unchanged. -/
theorem ensureRunnable_preserves_allPendingMessagesBounded
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded (ensureRunnable st tid) := by
  intro t tcb msg hObj hMsg
  rw [ensureRunnable_preserves_objects] at hObj
  exact hInv t tcb msg hObj hMsg

/-- WS-H12e: removeRunnable preserves allPendingMessagesBounded.
removeRunnable only modifies scheduler state; the object store is unchanged. -/
theorem removeRunnable_preserves_allPendingMessagesBounded
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded (removeRunnable st tid) := by
  intro t tcb msg hObj hMsg
  rw [removeRunnable_preserves_objects] at hObj
  exact hInv t tcb msg hObj hMsg

/-- WS-H12e: storeTcbIpcState preserves allPendingMessagesBounded.
storeTcbIpcState only changes `ipcState`, not `pendingMessage`. -/
theorem storeTcbIpcState_preserves_allPendingMessagesBounded
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          have hTcbPre := lookupTcb_some_objects st tid tcb hLookup
          intro t tcb' msg hObj hMsg
          by_cases hEq : t.toObjId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hObj
            cases hObj; simp at hMsg
            -- pendingMessage is preserved: { tcb with ipcState := ipc }.pendingMessage = tcb.pendingMessage
            exact hInv t tcb msg (by rw [hEq]; exact hTcbPre) hMsg
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hObjInv hStore] at hObj
            exact hInv t tcb' msg hObjPre hMsg

/-- WS-H12e: storeTcbIpcStateAndMessage preserves allPendingMessagesBounded
when the new pending message (if any) satisfies `bounded`. -/
theorem storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hMsgBounded : ∀ m, msg = some m → m.bounded)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          intro t tcb' m hObj hPend
          by_cases hEq : t.toObjId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hObj
            cases hObj; simp at hPend
            exact hMsgBounded m hPend
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hObjInv hStore] at hObj
            exact hInv t tcb' m hObjPre hPend

/-- WS-H12e: storeTcbPendingMessage preserves allPendingMessagesBounded
when the new pending message (if any) satisfies `bounded`. -/
theorem storeTcbPendingMessage_preserves_allPendingMessagesBounded
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hMsgBounded : ∀ m, msg = some m → m.bounded)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  unfold storeTcbPendingMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          intro t tcb' m hObj hPend
          by_cases hEq : t.toObjId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hObj
            cases hObj; simp at hPend
            exact hMsgBounded m hPend
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hObjInv hStore] at hObj
            exact hInv t tcb' m hObjPre hPend

/-- WS-H12e: storeObject for endpoint preserves allPendingMessagesBounded.
Endpoints don't carry pending messages, so the TCB predicate is unaffected. -/
theorem storeObject_endpoint_preserves_allPendingMessagesBounded
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.endpoint ep) st = .ok ((), st'))
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  intro t tcb msg hObj hMsg
  by_cases hEq : t.toObjId = oid
  · rw [hEq, storeObject_objects_eq st st' oid _ hObjInv hStore] at hObj; cases hObj
  · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb) := by
      rwa [storeObject_objects_ne st st' oid t.toObjId _ hEq hObjInv hStore] at hObj
    exact hInv t tcb msg hObjPre hMsg

/-- WS-H12e: storeTcbQueueLinks preserves allPendingMessagesBounded.
Queue link updates only change `queuePrev`/`queueNext`/`queuePPrev`,
not `pendingMessage`. -/
theorem storeTcbQueueLinks_preserves_allPendingMessagesBounded
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  unfold storeTcbQueueLinks at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId
        (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          have hTcbPre := lookupTcb_some_objects st tid tcb hLookup
          intro t tcb' msg hObj hMsg
          by_cases hEq : t.toObjId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hObj
            cases hObj; simp [tcbWithQueueLinks] at hMsg
            -- pendingMessage is preserved: queue link updates don't change pendingMessage
            exact hInv t tcb msg (by rw [hEq]; exact hTcbPre) hMsg
          · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb') := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId t.toObjId _ hEq hObjInv hStore] at hObj
            exact hInv t tcb' msg hObjPre hMsg

/-- WS-H12e: storeObject for notification preserves allPendingMessagesBounded.
Notifications are not TCBs, so no TCB's pendingMessage is affected. -/
theorem storeObject_notification_preserves_allPendingMessagesBounded
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.notification ntfn) st = .ok ((), st'))
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  intro t tcb msg hObj hMsg
  by_cases hEq : t.toObjId = oid
  · rw [hEq, storeObject_objects_eq st st' oid _ hObjInv hStore] at hObj; cases hObj
  · have hObjPre : st.objects[t.toObjId]? = some (.tcb tcb) := by
      rwa [storeObject_objects_ne st st' oid t.toObjId _ hEq hObjInv hStore] at hObj
    exact hInv t tcb msg hObjPre hMsg

-- ============================================================================
-- U4-K: endpointQueuePopHead/Enqueue preservation
-- ============================================================================

/-- U4-K: endpointQueuePopHead preserves allPendingMessagesBounded.
Composed from storeObject_endpoint + storeTcbQueueLinks (×1–2) primitives. -/
theorem endpointQueuePopHead_preserves_allPendingMessagesBounded
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep; revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 := storeObject_endpoint_preserves_allPendingMessagesBounded
              st pair.2 endpointId _ hObjInv hStore hInv
            have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact storeTcbQueueLinks_preserves_allPendingMessagesBounded
                  _ _ headTid _ _ _ hObjInv1 hFinal hInv1
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
                  have hInv2 := storeTcbQueueLinks_preserves_allPendingMessagesBounded
                    _ _ nextTid _ _ _ hObjInv1 hLink hInv1
                  have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hObjInv1 hLink
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact storeTcbQueueLinks_preserves_allPendingMessagesBounded
                      _ _ headTid _ _ _ hObjInv2 hFinal hInv2

/-- U4-K: endpointQueuePopHead preserves badgeWellFormed.
Composed from storeObject_endpoint + storeTcbQueueLinks (×1–2) primitives. -/
theorem endpointQueuePopHead_preserves_badgeWellFormed
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hInv : badgeWellFormed st) :
    badgeWellFormed st' := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep; revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 := storeObject_endpoint_preserves_badgeWellFormed
              st pair.2 endpointId _ hInv hObjInv hStore
            have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact storeTcbQueueLinks_preserves_badgeWellFormed
                  _ _ headTid _ _ _ hInv1 hObjInv1 hFinal
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
                  have hInv2 := storeTcbQueueLinks_preserves_badgeWellFormed
                    _ _ nextTid _ _ _ hInv1 hObjInv1 hLink
                  have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hObjInv1 hLink
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact storeTcbQueueLinks_preserves_badgeWellFormed
                      _ _ headTid _ _ _ hInv2 hObjInv2 hFinal

/-- U4-K: endpointQueueEnqueue preserves allPendingMessagesBounded.
Composed from storeObject_endpoint + storeTcbQueueLinks (×1–2) primitives. -/
theorem endpointQueueEnqueue_preserves_allPendingMessagesBounded
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st')
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
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
            cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                have hInv1 := storeObject_endpoint_preserves_allPendingMessagesBounded
                  st pair.2 endpointId _ hObjInv hStore hInv
                have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                intro hStep
                exact storeTcbQueueLinks_preserves_allPendingMessagesBounded
                  _ _ tid _ _ _ hObjInv1 hStep hInv1
            | some tailTid =>
              cases hLookupT : lookupTcb st tailTid
              · simp [hLookupT]
              · rename_i tailTcb
                simp only [hLookupT]
                cases hStore : storeObject endpointId _ st
                · simp
                · rename_i pair
                  simp only []
                  have hInv1 := storeObject_endpoint_preserves_allPendingMessagesBounded
                    st pair.2 endpointId _ hObjInv hStore hInv
                  have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid _ _ (some tid)
                  · simp
                  · rename_i st2
                    simp only []
                    have hInv2 := storeTcbQueueLinks_preserves_allPendingMessagesBounded
                      _ _ tailTid _ _ _ hObjInv1 hLink1 hInv1
                    have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hObjInv1 hLink1
                    intro hStep
                    exact storeTcbQueueLinks_preserves_allPendingMessagesBounded
                      _ _ tid _ _ _ hObjInv2 hStep hInv2

/-- U4-K: endpointQueueEnqueue preserves badgeWellFormed.
Composed from storeObject_endpoint + storeTcbQueueLinks (×1–2) primitives. -/
theorem endpointQueueEnqueue_preserves_badgeWellFormed
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st')
    (hInv : badgeWellFormed st) :
    badgeWellFormed st' := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
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
            cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                have hInv1 := storeObject_endpoint_preserves_badgeWellFormed
                  st pair.2 endpointId _ hInv hObjInv hStore
                have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                intro hStep
                exact storeTcbQueueLinks_preserves_badgeWellFormed
                  _ _ tid _ _ _ hInv1 hObjInv1 hStep
            | some tailTid =>
              cases hLookupT : lookupTcb st tailTid
              · simp [hLookupT]
              · rename_i tailTcb
                simp only [hLookupT]
                cases hStore : storeObject endpointId _ st
                · simp
                · rename_i pair
                  simp only []
                  have hInv1 := storeObject_endpoint_preserves_badgeWellFormed
                    st pair.2 endpointId _ hInv hObjInv hStore
                  have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid _ _ (some tid)
                  · simp
                  · rename_i st2
                    simp only []
                    have hInv2 := storeTcbQueueLinks_preserves_badgeWellFormed
                      _ _ tailTid _ _ _ hInv1 hObjInv1 hLink1
                    have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hObjInv1 hLink1
                    intro hStep
                    exact storeTcbQueueLinks_preserves_badgeWellFormed
                      _ _ tid _ _ _ hInv2 hObjInv2 hStep

-- ============================================================================
-- WS-H12e: Compound operation allPendingMessagesBounded preservation
-- ============================================================================

/-- WS-H12e: notificationSignal preserves allPendingMessagesBounded.
notificationSignal stores a notification object and calls storeTcbIpcState +
ensureRunnable. None of these modify any TCB's pendingMessage. -/
theorem notificationSignal_preserves_allPendingMessagesBounded
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : allPendingMessagesBounded st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    allPendingMessagesBounded st' := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
          simp only [hWaiters] at hStep
          revert hStep
          cases hStore : storeObject notificationId
              (.notification { state := if rest.isEmpty then .idle else .waiting,
                               waitingThreads := rest, pendingBadge := none }) st with
          | error e => simp
          | ok pair =>
              simp only []
              have hInv1 := storeObject_notification_preserves_allPendingMessagesBounded
                st pair.2 notificationId _ hObjInv hStore hInv
              -- R3-A/M-16: storeTcbIpcStateAndMessage replaces storeTcbIpcState
              cases hIpc : storeTcbIpcStateAndMessage pair.2 waiter .ready
                  (some { IpcMessage.empty with badge := some badge }) with
              | error e => simp
              | ok st'' =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hEq⟩; subst hEq
                  have hObjInvPair : pair.2.objects.invExt :=
                    storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
                  have hInv2 := storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                    pair.2 st'' waiter .ready _
                    (fun m hm => by cases hm; exact IpcMessage.empty_bounded)
                    hObjInvPair hIpc hInv1
                  exact ensureRunnable_preserves_allPendingMessagesBounded st'' waiter hInv2
      | nil =>
          simp only [hWaiters] at hStep
          exact storeObject_notification_preserves_allPendingMessagesBounded
            st st' notificationId _ hObjInv hStep hInv

/-- WS-H12e: notificationWait preserves allPendingMessagesBounded.
notificationWait stores a notification object and calls storeTcbIpcState +
ensureRunnable/removeRunnable. None of these modify any TCB's pendingMessage. -/
theorem notificationWait_preserves_allPendingMessagesBounded
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : allPendingMessagesBounded st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    allPendingMessagesBounded st' := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
          simp only [hBadge] at hStep
          revert hStep
          cases hStore : storeObject notificationId
              (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
          | error e => simp
          | ok pair =>
              simp only []
              have hInv1 := storeObject_notification_preserves_allPendingMessagesBounded
                st pair.2 notificationId _ hObjInv hStore hInv
              cases hIpc : storeTcbIpcState pair.2 waiter .ready with
              | error e => simp
              | ok st'' =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hEq⟩; subst hEq
                  have hObjInvPair : pair.2.objects.invExt :=
                    storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
                  exact storeTcbIpcState_preserves_allPendingMessagesBounded
                    pair.2 st'' waiter _ hObjInvPair hIpc hInv1
      | none =>
          simp only [hBadge] at hStep
          cases hLk : lookupTcb st waiter with
          | none => simp [hLk] at hStep
          | some tcb =>
              simp only [hLk] at hStep
              split at hStep
              · simp at hStep
              · revert hStep
                cases hStore : storeObject notificationId
                    (.notification { state := .waiting,
                                     waitingThreads := waiter :: ntfn.waitingThreads,
                                     pendingBadge := none }) st with
                | error e => simp
                | ok pair =>
                    simp only []
                    have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObj hObjInv hStore
                    simp only [storeTcbIpcState_fromTcb_eq hLk']
                    have hInv1 := storeObject_notification_preserves_allPendingMessagesBounded
                      st pair.2 notificationId _ hObjInv hStore hInv
                    have hObjInvPairN : pair.2.objects.invExt :=
                      storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
                    cases hIpc : storeTcbIpcState pair.2 waiter (.blockedOnNotification notificationId) with
                    | error e => simp
                    | ok st'' =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have hInv2 := storeTcbIpcState_preserves_allPendingMessagesBounded
                          pair.2 st'' waiter _ hObjInvPairN hIpc hInv1
                        exact removeRunnable_preserves_allPendingMessagesBounded st'' waiter hInv2

/-- WS-H12e: endpointReply preserves allPendingMessagesBounded.
endpointReply bounds-checks the message at entry, then stores it in the target
TCB via storeTcbIpcStateAndMessage with (some msg) where msg.bounded follows
from the entry-point bounds check. -/
theorem endpointReply_preserves_allPendingMessagesBounded
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : allPendingMessagesBounded st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    allPendingMessagesBounded st' := by
  unfold endpointReply at hStep
  -- WS-H12d: Extract bounds facts, then eliminate branches
  have hReg : ¬(maxMessageRegisters < msg.registers.size) := by intro h; simp [h] at hStep
  simp only [hReg, ↓reduceIte] at hStep
  have hCap : ¬(maxExtraCaps < msg.caps.size) := by intro h; simp [h] at hStep
  simp only [hCap, ↓reduceIte] at hStep
  have hMsgBounded : msg.bounded := ⟨by omega, by omega⟩
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
          -- AK1-B (I-H02): Fail-closed on replyTarget = none
          cases replyTarget with
          | none => simp at hStep
          | some expected =>
            simp only at hStep
            split at hStep
            · -- authorized = true
              revert hStep
              cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
              | error e => simp
              | ok st1 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hStEq⟩; subst hStEq
                  exact ensureRunnable_preserves_allPendingMessagesBounded st1 target
                    (storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                      st st1 target _ _ (by intro m hm; cases hm; exact hMsgBounded)
                      hObjInv hStore hInv)
            · -- authorized = false
              simp_all

-- ============================================================================
-- R3-B: Notification operation dualQueueSystemInvariant preservation
-- ============================================================================

/-- R3-B: notificationSignal preserves dualQueueSystemInvariant.
Wake path: storeObject(.notification) + storeTcbIpcStateAndMessage + ensureRunnable.
Merge path: storeObject(.notification) only. All preserve dual-queue invariant. -/
theorem notificationSignal_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    dualQueueSystemInvariant st' := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
        simp only [hWaiters] at hStep; revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := if rest.isEmpty then .idle else .waiting,
                             waitingThreads := rest, pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          have hInv1 := storeObject_notification_preserves_dualQueueSystemInvariant
            st pair.2 notificationId _ hObjInv hStore (.inl ⟨ntfn, hObj⟩) hInv
          have hObjInv1 := storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
          cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
              (some { IpcMessage.empty with badge := some badge }) with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            exact ensureRunnable_preserves_dualQueueSystemInvariant st'' waiter
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                pair.2 st'' waiter .ready _ hObjInv1 hTcb hInv1)
      | nil =>
        simp only [hWaiters] at hStep
        exact storeObject_notification_preserves_dualQueueSystemInvariant
          st st' notificationId _ hObjInv hStep (.inl ⟨ntfn, hObj⟩) hInv

/-- R3-B: notificationWait preserves dualQueueSystemInvariant.
Badge-consume path: storeObject(.notification) + storeTcbIpcState.
Block path: storeObject(.notification) + storeTcbIpcState + removeRunnable. -/
theorem notificationWait_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    dualQueueSystemInvariant st' := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hPending : ntfn.pendingBadge with
      | some pendBadge =>
        simp only [hPending] at hStep; revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          have hInv1 := storeObject_notification_preserves_dualQueueSystemInvariant
            st pair.2 notificationId _ hObjInv hStore (.inl ⟨ntfn, hObj⟩) hInv
          have hObjInv1 := storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            exact storeTcbIpcState_preserves_dualQueueSystemInvariant
              pair.2 st'' waiter .ready hObjInv1 hTcb hInv1
      | none =>
        simp only [hPending] at hStep; revert hStep
        cases hLk : lookupTcb st waiter with
        | none => simp
        | some tcb =>
          simp only []; split
          · simp
          · intro hStep; revert hStep
            cases hStore : storeObject notificationId
                (.notification { state := .waiting,
                                 waitingThreads := waiter :: ntfn.waitingThreads,
                                 pendingBadge := none }) st with
            | error e => simp
            | ok pair =>
              simp only []
              have hInv1 := storeObject_notification_preserves_dualQueueSystemInvariant
                st pair.2 notificationId _ hObjInv hStore (.inl ⟨ntfn, hObj⟩) hInv
              have hObjInv1 := storeObject_preserves_objects_invExt st pair.2 notificationId _ hObjInv hStore
              have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObj hObjInv hStore
              simp only [storeTcbIpcState_fromTcb_eq hLk']
              cases hTcb : storeTcbIpcState pair.2 waiter (.blockedOnNotification notificationId) with
              | error e => simp
              | ok st'' =>
                simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
                exact removeRunnable_preserves_dualQueueSystemInvariant st'' waiter
                  (storeTcbIpcState_preserves_dualQueueSystemInvariant
                    pair.2 st'' waiter _ hObjInv1 hTcb hInv1)

-- ============================================================================
-- R3-B: Endpoint operation badgeWellFormed preservation
-- Endpoint operations only modify TCB and endpoint objects (never notifications
-- or CNodes), so badge well-formedness is preserved by construction.
-- ============================================================================

/-- R3-B: endpointReply preserves badgeWellFormed.
Calls storeTcbIpcStateAndMessage + ensureRunnable — neither stores a
notification or CNode. -/
theorem endpointReply_preserves_badgeWellFormed
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    badgeWellFormed st' := by
  -- Mirror the structure of endpointReply_preserves_dualQueueSystemInvariant
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _
        | blockedOnCall _ => simp [hIpc] at hStep
      | blockedOnReply epId' rt =>
          simp only [hIpc] at hStep
          -- AK1-B (I-H02): Fail-closed on rt = none
          cases rt with
          | none => simp at hStep
          | some val =>
            simp only at hStep
            split at hStep
            · -- authorized = true
              cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
              | error e => simp [hStore] at hStep
              | ok st1 =>
                simp only [hStore] at hStep
                simp at hStep; subst hStep
                have hInv1 := storeTcbIpcStateAndMessage_preserves_badgeWellFormed
                  st st1 target .ready (some msg) hInv hObjInv hStore
                exact ensureRunnable_preserves_badgeWellFormed st1 target hInv1
            · simp at hStep

-- ============================================================================
-- R3-C.2/M-19: Endpoint operation notificationWaiterConsistent preservation
-- ============================================================================

/-- R3-C.2/M-19: endpointReply preserves notificationWaiterConsistent.
The target thread has `ipcState = .blockedOnReply`, so by
`notificationWaiterConsistent` it is not in any notification wait list.
`storeTcbIpcStateAndMessage` + `ensureRunnable` therefore do not affect
any notification waiter's TCB. -/
theorem endpointReply_preserves_notificationWaiterConsistent
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hConsist : notificationWaiterConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    notificationWaiterConsistent st' := by
  -- Unfold endpointReply and extract the storeTcbIpcStateAndMessage + ensureRunnable steps
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _
      | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId' rt =>
      simp only [hIpc] at hStep
      -- AK1-B (I-H02): Fail-closed on rt = none
      cases rt with
      | none => simp at hStep
      | some val =>
        simp only at hStep
        split at hStep
        · -- authorized = true
          cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st1 =>
            simp only [hStore] at hStep
            -- target has .blockedOnReply, so it is not in any notification wait list
            have hTargetNotInWaitList : ∀ (noid : SeLe4n.ObjId) (ntfn : Notification),
                st.objects[noid]? = some (.notification ntfn) → target ∉ ntfn.waitingThreads := by
              intro noid ntfn hNtfn hMem
              obtain ⟨tcb_w, hTcb_w, hIpc_w⟩ := hConsist noid ntfn target hNtfn hMem
              have hTcbTarget := lookupTcb_some_objects st target tcb hLookup
              rw [hTcb_w] at hTcbTarget; cases hTcbTarget; rw [hIpc_w] at hIpc; cases hIpc
            have hConsist1 := storeTcbIpcStateAndMessage_preserves_notificationWaiterConsistent
              st st1 target .ready (some msg) hConsist hObjInv hStore hTargetNotInWaitList
            simp at hStep; subst hStep
            intro noid ntfn tid hNtfnPost hMem
            have hNtfnSt1 : st1.objects[noid]? = some (.notification ntfn) := by
              rwa [ensureRunnable_preserves_objects] at hNtfnPost
            obtain ⟨tcb', hTcb', hIpc'⟩ := hConsist1 noid ntfn tid hNtfnSt1 hMem
            exact ⟨tcb', by rw [ensureRunnable_preserves_objects]; exact hTcb', hIpc'⟩
        · simp at hStep

-- ============================================================================
-- U4-K: Endpoint operation allPendingMessagesBounded preservation
-- ============================================================================

/-- U4-K: endpointSendDual preserves allPendingMessagesBounded.
Path A: PopHead + storeTcbIpcStateAndMessage(receiver, msg) + ensureRunnable.
Path B: Enqueue + storeTcbIpcStateAndMessage(sender, msg) + removeRunnable. -/
theorem endpointSendDual_preserves_allPendingMessagesBounded
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : allPendingMessagesBounded st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    allPendingMessagesBounded st' := by
  unfold endpointSendDual at hStep
  have hReg : ¬(maxMessageRegisters < msg.registers.size) := by intro h; simp [h] at hStep
  simp only [hReg, ↓reduceIte] at hStep
  have hCap : ¬(maxExtraCaps < msg.caps.size) := by intro h; simp [h] at hStep
  simp only [hCap, ↓reduceIte] at hStep
  have hMsgBounded : msg.bounded := ⟨by omega, by omega⟩
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.receiveQ.head with
      | some rcvr =>
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          obtain ⟨receiver, headTcb, stPop⟩ := pair
          have hInv1 := endpointQueuePopHead_preserves_allPendingMessagesBounded
            endpointId true st stPop receiver headTcb hObjInv hPop hInv
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId true st stPop receiver headTcb hObjInv hPop
          cases hStore : storeTcbIpcStateAndMessage stPop receiver .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact ensureRunnable_preserves_allPendingMessagesBounded st2 receiver
              (storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                stPop st2 receiver _ _ (by intro m hm; cases hm; exact hMsgBounded)
                hObjInv1 hStore hInv1)
      | none =>
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          have hInv1 := endpointQueueEnqueue_preserves_allPendingMessagesBounded
            endpointId false sender st st1 hObjInv hEnq hInv
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
            endpointId false sender st st1 hObjInv hEnq
          cases hStore : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact removeRunnable_preserves_allPendingMessagesBounded st2 sender
              (storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                st1 st2 sender _ _ (by intro m hm; cases hm; exact hMsgBounded)
                hObjInv1 hStore hInv1)

/-- U4-K: endpointSendDual preserves badgeWellFormed.
All steps store TCBs or endpoints (not notifications, not CNodes). -/
theorem endpointSendDual_preserves_badgeWellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    badgeWellFormed st' := by
  unfold endpointSendDual at hStep
  have hReg : ¬(maxMessageRegisters < msg.registers.size) := by intro h; simp [h] at hStep
  simp only [hReg, ↓reduceIte] at hStep
  have hCap : ¬(maxExtraCaps < msg.caps.size) := by intro h; simp [h] at hStep
  simp only [hCap, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.receiveQ.head with
      | some rcvr =>
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          obtain ⟨receiver, headTcb, stPop⟩ := pair
          have hInv1 := endpointQueuePopHead_preserves_badgeWellFormed
            endpointId true st stPop receiver headTcb hObjInv hPop hInv
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId true st stPop receiver headTcb hObjInv hPop
          cases hStore : storeTcbIpcStateAndMessage stPop receiver .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact ensureRunnable_preserves_badgeWellFormed st2 receiver
              (storeTcbIpcStateAndMessage_preserves_badgeWellFormed
                stPop st2 receiver _ _ hInv1 hObjInv1 hStore)
      | none =>
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          have hInv1 := endpointQueueEnqueue_preserves_badgeWellFormed
            endpointId false sender st st1 hObjInv hEnq hInv
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
            endpointId false sender st st1 hObjInv hEnq
          cases hStore : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact removeRunnable_preserves_badgeWellFormed st2 sender
              (storeTcbIpcStateAndMessage_preserves_badgeWellFormed
                st1 st2 sender _ _ hInv1 hObjInv1 hStore)

/-- U4-K: endpointReceiveDual preserves allPendingMessagesBounded.
Path A (sender waiting): PopHead + storeTcbIpcStateAndMessage(sender, none) +
  [ensureRunnable|id] + storeTcbPendingMessage(receiver, senderMsg).
  The senderMsg was bounded in the pre-state by the invariant.
Path B (no sender): Enqueue + storeTcbIpcState + removeRunnable. -/
theorem endpointReceiveDual_preserves_allPendingMessagesBounded
    (endpointId : SeLe4n.ObjId) (receiver senderId : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : allPendingMessagesBounded st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    allPendingMessagesBounded st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.sendQ.head with
      | some _ =>
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          obtain ⟨sender, senderTcb, stPop⟩ := pair
          have hInv1 := endpointQueuePopHead_preserves_allPendingMessagesBounded
            endpointId false st stPop sender senderTcb hObjInv hPop hInv
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId false st stPop sender senderTcb hObjInv hPop
          -- senderTcb.pendingMessage was bounded in pre-state
          have hSenderMsgBounded : ∀ m, senderTcb.pendingMessage = some m → m.bounded := by
            intro m hm
            have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId false st ep sender senderTcb stPop hObj hPop
            exact hInv sender senderTcb m hPreTcb hm
          -- Now trace through the Call/Send path split
          split at hStep
          · -- Call path: storeTcbIpcStateAndMessage(sender, none) + storeTcbPendingMessage(receiver, senderMsg)
            cases hStore : storeTcbIpcStateAndMessage stPop sender (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep
              have hInv2 := storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                stPop st2 sender _ _ (by intro m hm; cases hm) hObjInv1 hStore hInv1
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 sender _ _ hObjInv1 hStore
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage st2 receiver .ready senderTcb.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st3 =>
                simp [hPend] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                  st2 st3 receiver .ready _ hSenderMsgBounded hObjInv2 hPend hInv2
          · -- Send path: storeTcbIpcStateAndMessage(sender, none) + ensureRunnable + storeTcbPendingMessage(receiver, senderMsg)
            cases hStore : storeTcbIpcStateAndMessage stPop sender .ready none with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep
              have hInv2 := storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                stPop st2 sender _ _ (by intro m hm; cases hm) hObjInv1 hStore hInv1
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 sender _ _ hObjInv1 hStore
              have hInv3 := ensureRunnable_preserves_allPendingMessagesBounded st2 sender hInv2
              have hObjInv3 : (ensureRunnable st2 sender).objects.invExt := by
                rw [ensureRunnable_preserves_objects]; exact hObjInv2
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 sender) receiver .ready senderTcb.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st4 =>
                simp [hPend] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                  _ st4 receiver .ready _ hSenderMsgBounded hObjInv3 hPend hInv3
      | none =>
        -- AI4-A: cleanupPreReceiveDonation before enqueue
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        simp only [hHead] at hStep
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hInvClean := cleanupPreReceiveDonation_preserves_allPendingMessagesBounded st receiver hObjInv hInv
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hInv1 := endpointQueueEnqueue_preserves_allPendingMessagesBounded
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq hInvClean
            have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp [hIpc] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact removeRunnable_preserves_allPendingMessagesBounded st2 receiver
                (storeTcbIpcState_preserves_allPendingMessagesBounded
                  st1 st2 receiver _ hObjInv1 hIpc hInv1)

/-- U4-K: endpointReceiveDual preserves badgeWellFormed. -/
theorem endpointReceiveDual_preserves_badgeWellFormed
    (endpointId : SeLe4n.ObjId) (receiver senderId : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    badgeWellFormed st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.sendQ.head with
      | some _ =>
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          obtain ⟨sender, senderTcb, stPop⟩ := pair
          have hInv1 := endpointQueuePopHead_preserves_badgeWellFormed
            endpointId false st stPop sender senderTcb hObjInv hPop hInv
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId false st stPop sender senderTcb hObjInv hPop
          split at hStep
          · -- Call path
            cases hStore : storeTcbIpcStateAndMessage stPop sender (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep
              have hInv2 := storeTcbIpcStateAndMessage_preserves_badgeWellFormed
                stPop st2 sender _ _ hInv1 hObjInv1 hStore
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 sender _ _ hObjInv1 hStore
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage st2 receiver .ready senderTcb.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st3 =>
                simp [hPend] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact storeTcbIpcStateAndMessage_preserves_badgeWellFormed st2 st3 receiver .ready _ hInv2 hObjInv2 hPend
          · -- Send path
            cases hStore : storeTcbIpcStateAndMessage stPop sender .ready none with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep
              have hInv2 := storeTcbIpcStateAndMessage_preserves_badgeWellFormed
                stPop st2 sender _ _ hInv1 hObjInv1 hStore
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 sender _ _ hObjInv1 hStore
              have hInv3 := ensureRunnable_preserves_badgeWellFormed st2 sender hInv2
              have hObjInv3 : (ensureRunnable st2 sender).objects.invExt := by
                rw [ensureRunnable_preserves_objects]; exact hObjInv2
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 sender) receiver .ready senderTcb.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st4 =>
                simp [hPend] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact storeTcbIpcStateAndMessage_preserves_badgeWellFormed _ st4 receiver .ready _ hInv3 hObjInv3 hPend
      | none =>
        -- AI4-A: cleanupPreReceiveDonation before enqueue
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        simp only [hHead] at hStep
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hInvClean := cleanupPreReceiveDonation_preserves_badgeWellFormed st receiver hObjInv hInv
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hInv1 := endpointQueueEnqueue_preserves_badgeWellFormed
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq hInvClean
            have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp [hIpc] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact removeRunnable_preserves_badgeWellFormed st2 receiver
                (storeTcbIpcState_preserves_badgeWellFormed st1 st2 receiver _ hInv1 hObjInv1 hIpc)

/-- U4-K: endpointCall preserves allPendingMessagesBounded.
Path A: PopHead + storeTcbIpcStateAndMessage(receiver, msg) + ensureRunnable +
  storeTcbIpcState(caller) + removeRunnable.
Path B: Enqueue + storeTcbIpcStateAndMessage(caller, msg) + removeRunnable. -/
theorem endpointCall_preserves_allPendingMessagesBounded
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : allPendingMessagesBounded st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    allPendingMessagesBounded st' := by
  unfold endpointCall at hStep
  have hReg : ¬(maxMessageRegisters < msg.registers.size) := by intro h; simp [h] at hStep
  simp only [hReg, ↓reduceIte] at hStep
  have hCap : ¬(maxExtraCaps < msg.caps.size) := by intro h; simp [h] at hStep
  simp only [hCap, ↓reduceIte] at hStep
  have hMsgBounded : msg.bounded := ⟨by omega, by omega⟩
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.receiveQ.head with
      | some _ =>
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          obtain ⟨receiver, _tcb, stPop⟩ := pair
          have hInv1 := endpointQueuePopHead_preserves_allPendingMessagesBounded
            endpointId true st stPop receiver _tcb hObjInv hPop hInv
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId true st stPop receiver _tcb hObjInv hPop
          cases hStore : storeTcbIpcStateAndMessage stPop receiver .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore] at hStep
            have hInv2 := storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
              stPop st2 receiver _ _ (by intro m hm; cases hm; exact hMsgBounded) hObjInv1 hStore hInv1
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 receiver _ _ hObjInv1 hStore
            have hInv3 := ensureRunnable_preserves_allPendingMessagesBounded st2 receiver hInv2
            have hObjInv3 : (ensureRunnable st2 receiver).objects.invExt := by
              rw [ensureRunnable_preserves_objects]; exact hObjInv2
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage atomically clears caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 receiver) caller (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact removeRunnable_preserves_allPendingMessagesBounded st4 caller
                (storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                  _ st4 caller _ none (fun _ h => by cases h)
                  hObjInv3 hIpc hInv3)
      | none =>
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          have hInv1 := endpointQueueEnqueue_preserves_allPendingMessagesBounded
            endpointId false caller st st1 hObjInv hEnq hInv
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
            endpointId false caller st st1 hObjInv hEnq
          cases hStore : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact removeRunnable_preserves_allPendingMessagesBounded st2 caller
              (storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
                st1 st2 caller _ _ (by intro m hm; cases hm; exact hMsgBounded)
                hObjInv1 hStore hInv1)

/-- U4-K: endpointCall preserves badgeWellFormed. -/
theorem endpointCall_preserves_badgeWellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    badgeWellFormed st' := by
  unfold endpointCall at hStep
  have hReg : ¬(maxMessageRegisters < msg.registers.size) := by intro h; simp [h] at hStep
  simp only [hReg, ↓reduceIte] at hStep
  have hCap : ¬(maxExtraCaps < msg.caps.size) := by intro h; simp [h] at hStep
  simp only [hCap, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.receiveQ.head with
      | some _ =>
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          obtain ⟨receiver, _tcb, stPop⟩ := pair
          have hInv1 := endpointQueuePopHead_preserves_badgeWellFormed
            endpointId true st stPop receiver _tcb hObjInv hPop hInv
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId true st stPop receiver _tcb hObjInv hPop
          cases hStore : storeTcbIpcStateAndMessage stPop receiver .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore] at hStep
            have hInv2 := storeTcbIpcStateAndMessage_preserves_badgeWellFormed
              stPop st2 receiver _ _ hInv1 hObjInv1 hStore
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 receiver _ _ hObjInv1 hStore
            have hInv3 := ensureRunnable_preserves_badgeWellFormed st2 receiver hInv2
            have hObjInv3 : (ensureRunnable st2 receiver).objects.invExt := by
              rw [ensureRunnable_preserves_objects]; exact hObjInv2
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage atomically clears caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 receiver) caller (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact removeRunnable_preserves_badgeWellFormed st4 caller
                (storeTcbIpcStateAndMessage_preserves_badgeWellFormed _ st4 caller _ none hInv3 hObjInv3 hIpc)
      | none =>
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          have hInv1 := endpointQueueEnqueue_preserves_badgeWellFormed
            endpointId false caller st st1 hObjInv hEnq hInv
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
            endpointId false caller st st1 hObjInv hEnq
          cases hStore : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact removeRunnable_preserves_badgeWellFormed st2 caller
              (storeTcbIpcStateAndMessage_preserves_badgeWellFormed
                st1 st2 caller _ _ hInv1 hObjInv1 hStore)

/-- U4-K: endpointReplyRecv preserves allPendingMessagesBounded.
Reply part: storeTcbIpcStateAndMessage(replyTarget, msg) + ensureRunnable.
Then delegates to endpointReceiveDual. -/
theorem endpointReplyRecv_preserves_allPendingMessagesBounded
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : allPendingMessagesBounded st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    allPendingMessagesBounded st' := by
  unfold endpointReplyRecv at hStep
  have hReg : ¬(maxMessageRegisters < msg.registers.size) := by intro h; simp [h] at hStep
  simp only [hReg, ↓reduceIte] at hStep
  have hCap : ¬(maxExtraCaps < msg.caps.size) := by intro h; simp [h] at hStep
  simp only [hCap, ↓reduceIte] at hStep
  have hMsgBounded : msg.bounded := ⟨by omega, by omega⟩
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply _ expectedReplier =>
      simp only [hIpc] at hStep
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      -- AK1-B (I-H02): Fail-closed on expectedReplier = none
      cases expectedReplier with
      | none => simp at hStep
      | some expected =>
        dsimp only at hStep
        split at hStep
        · -- authorized = true
          cases hStore : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st1 =>
            simp only [hStore] at hStep
            have hInv1 := storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
              st st1 replyTarget _ _ (by intro m hm; cases hm; exact hMsgBounded) hObjInv hStore hInv
            have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget _ _ hObjInv hStore
            have hInv2 := ensureRunnable_preserves_allPendingMessagesBounded st1 replyTarget hInv1
            have hObjInv2 : (ensureRunnable st1 replyTarget).objects.invExt := by
              rw [ensureRunnable_preserves_objects]; exact hObjInv1
            cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
            | error e => simp [hRecv] at hStep
            | ok pair =>
              simp only [hRecv, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact endpointReceiveDual_preserves_allPendingMessagesBounded
                endpointId receiver pair.1 _ _ hInv2 hObjInv2 hRecv
        · simp at hStep

/-- U4-K: endpointReplyRecv preserves badgeWellFormed. -/
theorem endpointReplyRecv_preserves_badgeWellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    badgeWellFormed st' := by
  unfold endpointReplyRecv at hStep
  have hReg : ¬(maxMessageRegisters < msg.registers.size) := by intro h; simp [h] at hStep
  simp only [hReg, ↓reduceIte] at hStep
  have hCap : ¬(maxExtraCaps < msg.caps.size) := by intro h; simp [h] at hStep
  simp only [hCap, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply _ expectedReplier =>
      simp only [hIpc] at hStep
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      -- AK1-B (I-H02): Fail-closed on expectedReplier = none
      cases expectedReplier with
      | none => simp at hStep
      | some expected =>
        dsimp only at hStep
        split at hStep
        · -- authorized = true
          cases hStore : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st1 =>
            simp only [hStore] at hStep
            have hInv1 := storeTcbIpcStateAndMessage_preserves_badgeWellFormed
              st st1 replyTarget _ _ hInv hObjInv hStore
            have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget _ _ hObjInv hStore
            have hInv2 := ensureRunnable_preserves_badgeWellFormed st1 replyTarget hInv1
            have hObjInv2 : (ensureRunnable st1 replyTarget).objects.invExt := by
              rw [ensureRunnable_preserves_objects]; exact hObjInv1
            cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
            | error e => simp [hRecv] at hStep
            | ok pair =>
              simp only [hRecv, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact endpointReceiveDual_preserves_badgeWellFormed
                endpointId receiver pair.1 _ _ hInv2 hObjInv2 hRecv
        · simp at hStep

end SeLe4n.Kernel
