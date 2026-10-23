/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.IPC.DualQueue.PopInPlace
import SeLe4n.Kernel.IPC.Operations.NotificationBind

/-!
# Cancelling every waiter of an endpoint or a notification

WS-ZA ZA5.4 part 23: seL4's `finaliseCap` on the final capability to an
endpoint runs `cancelAllIPC`, and on the final capability to a notification
runs `unbindMaybeNotification` then `cancelAllSignals`.  This module holds the
three, and `finaliseFinalObject`, which a final delete runs before the retire
(`retireFinalObject`) so that a busy endpoint or a busy or bound notification
is emptied and can then be retired.

* **One waiter at a time, at the head.**  Each step takes the head of the queue
  (`cancelEndpointQueue`, `cancelNotificationQueue`): the endpoint's head is
  popped as a rendezvous pops it, each write in its slot (`storePopHead`, the
  specification's `endpointQueuePopHead` by `popHead_inPlace`); the
  notification's head leaves its queue as a cancelled thread leaves it
  (`Lifecycle.Suspend.cancelIpcBlocking`'s notification arm).  The walk follows
  the links held in the threads themselves and builds nothing.
* **What a cancelled waiter becomes.**  `.ready`, with no pending message, no
  stashed reply, and the `.ipcCancelled` frame staged in its registers
  (`Architecture.cancelledIpcFrame`), then woken on its own core
  (`determineTargetCore`, the core `wakeThread` picks).  seL4 sets the thread
  `Restart`, so it reissues the system call it was blocked in; this model's
  answer to a cancelled IPC is the `.ipcCancelled` frame, the one
  `cancelIpcBlocking` already hands a suspended thread's IPC.  The wake marks
  the core's reschedule flag (`enqueueRunnableOnCore`), and a remote core takes
  its interrupt from that flag.
* **Checks before writes.**  A step runs only when its waiter is active, runs
  on no core (`cancelledWaiterWakeable`), and, at an endpoint, waits with no
  timeout budget and every write of the pop stays in its slot
  (`endpointWaiterCancellable`), or, at a
  notification, the waiter is blocked on it and linked into no endpoint queue
  (`notificationWaiterCancellable`).  A step that is refused ends the walk;
  the object is then not quiescent, and the retire refuses it.
* **Fuel.**  Each walk takes at most the object table's size in steps, which
  bounds the number of threads; nothing is proved about the walk emptying the
  queue, because the retire asks that question itself (`passiveObjectQuiescent`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  A cancelled waiter
-- ============================================================================

/-- **Whether a cancel may wake `t`**: it is not suspended (`threadState` is not
`.Inactive`, so the wake places it) and it is no core's current thread.  A
blocked thread is both whenever the scheduler's invariants hold; the walk asks
anyway, before it writes. -/
@[inline] def cancelledWaiterWakeable (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB) :
    Bool :=
  decide (tcb.threadState ≠ .Inactive) && !runningOnSomeCore st t

/-- Wake a cancelled waiter on its own core. -/
@[inline] def wakeCancelledWaiter (st : SystemState) (t : SeLe4n.ThreadId) : SystemState :=
  enqueueRunnableOnCore st (determineTargetCore st t) t

-- ============================================================================
-- §2  `cancelAllIPC`
-- ============================================================================

/-- The queue of `ep` a walk takes: the receive queue when `isReceiveQ`. -/
@[inline] def endpointWaitQueue (ep : Endpoint) (isReceiveQ : Bool) : IntrusiveQueue :=
  if isReceiveQ then ep.receiveQ else ep.sendQ

/-- **What a cancelled endpoint waiter becomes**: `.ready`, holding no message
and no stashed reply (the receive completion `storeTcbReceiveComplete` writes,
with no message), with the cancellation frame staged in its registers. -/
@[inline] def cancelledEndpointWaiterTcb (t : TCB) : TCB :=
  (TCB.setIpcState { t with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready
    ).withReturnFrame Architecture.cancelledIpcFrame

/-- **Whether the head `t` of an endpoint's queue may be cancelled**: a cancel
may wake it, it waits with no timeout budget (a `.ready` thread holding one would
break `blockedThreadTimeoutConsistent`; no transition gives a waiter one), and
every write of its pop stays in its slot (`sendWakesInPlace`, under which the
pop is `storePopHead`, `popHead_inPlace`). -/
@[inline] def endpointWaiterCancellable (st : SystemState) (endpointId : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) (tcb : TCB) : Bool :=
  cancelledWaiterWakeable st t tcb && tcb.timeoutBudget.isNone &&
    sendWakesInPlace st endpointId t tcb.queueNext

/-- **Cancel the head `t` of one of an endpoint's queues** (`next` its
successor): the head popped (`storePopHead`), its IPC ended
(`cancelledEndpointWaiterTcb`), and the thread woken on its own core.  Out of
line, so each update is specialised in. -/
@[noinline] def storeEndpointWaiterCancelled (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (t : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) : SystemState :=
  wakeCancelledWaiter
    ((storePopHead st endpointId isReceiveQ t next).updateTcb t cancelledEndpointWaiterTcb) t

/-- **Cancel the waiters of one of an endpoint's queues**, head first, at most
`fuel` of them; a waiter `endpointWaiterCancellable` refuses ends the walk. -/
def cancelEndpointQueue (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) :
    Nat → SystemState → SystemState
  | 0, st => st
  | fuel + 1, st =>
    match st.getEndpoint? endpointId with
    | some ep =>
      match (endpointWaitQueue ep isReceiveQ).head with
      | some t =>
        match st.getTcb? t with
        | some tcb =>
          if endpointWaiterCancellable st endpointId t tcb then
            cancelEndpointQueue endpointId isReceiveQ fuel
              (storeEndpointWaiterCancelled st endpointId isReceiveQ t tcb.queueNext)
          else st
        | none => st
      | none => st
    | none => st

/-- **seL4's `cancelAllIPC`**: every sender, then every receiver. -/
def cancelAllIpc (endpointId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  let fuel := st.objects.size
  cancelEndpointQueue endpointId true fuel (cancelEndpointQueue endpointId false fuel st)

-- ============================================================================
-- §3  `cancelAllSignals` and `unbindMaybeNotification`
-- ============================================================================

/-- **Whether the head waiter `t` of the notification at `notificationId` may
be cancelled**: it is no reserved thread (the cancellation reads it as
`lookupTcb` does), it is blocked on that notification (so the removal edits that
queue), it is linked into no endpoint queue (the removal clears no endpoint
link), and a cancel may wake it. -/
@[inline] def notificationWaiterCancellable (st : SystemState) (notificationId : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) (tcb : TCB) : Bool :=
  !t.isReserved && decide (tcb.ipcState = .blockedOnNotification notificationId) &&
    tcb.queuePrevCode == 0 && tcb.queueNextCode == 0 && cancelledWaiterWakeable st t tcb

/-- **Cancel the waiters of a notification**, head first, at most `fuel` of
them: each leaves the queue and is made `.ready` with the cancellation frame, as
a cancelled thread is (`Lifecycle.Suspend.cancelIpcBlocking`'s notification
arm), then woken.  A waiter `notificationWaiterCancellable` refuses ends the
walk. -/
def cancelNotificationQueue (notificationId : SeLe4n.ObjId) :
    Nat → SystemState → SystemState
  | 0, st => st
  | fuel + 1, st =>
    match st.getNotification? notificationId with
    | some n =>
      match n.waitHead with
      | some t =>
        match st.getTcb? t with
        | some tcb =>
          if notificationWaiterCancellable st notificationId t tcb then
            cancelNotificationQueue notificationId fuel
              (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking st t tcb) t)
          else st
        | none => st
      | none => st
    | none => st


/-- **A notification head's cancel, as an update of the notification's cell**:
`next` heads the queue, the tail is kept unless the queue empties, and a
`.waiting` notification whose queue empties goes `.idle` — the writes
`removeFromNotificationWaitQueue` makes when the waiter it removes is the head.
`RHTable.modify` hands the update the cell exclusively, so it is rewritten where
it stands. -/
@[inline] def cancelPoppedObject (next : Option SeLe4n.ThreadId) : KernelObject → KernelObject
  | .notification n => .notification { n with
      waitHeadCode := SeLe4n.ThreadId.optCode next
      waitTailCode := SeLe4n.ThreadId.optCode (if next.isSome then n.waitTail else none)
      state := if n.state = .waiting ∧ next.isNone then .idle else n.state }
  | o => o

/-- **Cancel the head `t` of the notification at `notificationId`** (`next` its
successor), each write in its slot: the notification's cell rewritten
(`cancelPoppedObject`), the head detached from its neighbours
(`detachNtfnHead`), restored `.ready` with the cancellation frame
(`Lifecycle.Suspend.restoreToReadyCancelled`), and woken.  Out of line, so each
update is specialised in. -/
@[noinline] def storeNotificationWaiterCancelled (st : SystemState)
    (notificationId : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) :
    SystemState :=
  wakeCancelledWaiter
    (Lifecycle.Suspend.restoreToReadyCancelled
      (detachNtfnHead (st.modifyObject notificationId (cancelPoppedObject next)) t next) t) t

/-- **The cancel of a notification's head is its in-place writes**: on the head
`t` of the notification's queue, blocked on it, `cancelIpcBlocking` rewrites the
notification with `cancelPoppedObject`'s fields (its `rewriteObject` is the
table's `insert`, which is `modify` on a key that is present), then makes the
writes `storeNotificationWaiterCancelled` makes. -/
theorem cancelIpcBlocking_notificationHead_inPlace {st : SystemState}
    {notificationId : SeLe4n.ObjId} {ntfn : Notification} {t : SeLe4n.ThreadId} {tcb : TCB}
    (hN : st.getNotification? notificationId = some ntfn) (hH : ntfn.waitHead = some t)
    (hT : st.getTcb? t = some tcb)
    (hB : tcb.ipcState = .blockedOnNotification notificationId) :
    wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking st t tcb) t =
      storeNotificationWaiterCancelled st notificationId t tcb.ntfnNext := by
  have hNo := (SystemState.getNotification?_eq_some_iff _ _ _).mp hN
  unfold storeNotificationWaiterCancelled Lifecycle.Suspend.cancelIpcBlocking
  rw [hB]
  unfold removeFromNotificationWaitQueue
  simp only [hT, hB, SystemState.getNotificationWitnessed?_eq_some hN, hH, if_true]
  unfold SystemState.rewriteObject SystemState.modifyObject
  rw [RobinHood.RHTable.modify_of_get? (show st.objects.get? notificationId = _ from hNo)]
  rfl

/-- **`cancelNotificationQueue` as compiled**: each admitted head is cancelled
by `storeNotificationWaiterCancelled`, in place, which is the specification's
step (`cancelIpcBlocking_notificationHead_inPlace`). -/
def cancelNotificationQueueImpl (notificationId : SeLe4n.ObjId) :
    Nat → SystemState → SystemState
  | 0, st => st
  | fuel + 1, st =>
    match st.getNotification? notificationId with
    | some n =>
      match n.waitHead with
      | some t =>
        match st.getTcb? t with
        | some tcb =>
          if notificationWaiterCancellable st notificationId t tcb then
            cancelNotificationQueueImpl notificationId fuel
              (storeNotificationWaiterCancelled st notificationId t tcb.ntfnNext)
          else st
        | none => st
      | none => st
    | none => st

@[csimp] theorem cancelNotificationQueue_eq_impl :
    @cancelNotificationQueue = @cancelNotificationQueueImpl := by
  funext notificationId fuel
  induction fuel with
  | zero => funext st; rfl
  | succ fuel ih =>
    funext st
    unfold cancelNotificationQueue cancelNotificationQueueImpl
    split
    · rename_i n hN
      split
      · rename_i t hH
        split
        · rename_i tcb hT
          split
          · rename_i hC
            have hB : tcb.ipcState = .blockedOnNotification notificationId := by
              simp only [notificationWaiterCancellable, Bool.and_eq_true, decide_eq_true_eq] at hC
              exact hC.1.1.1.2
            rw [cancelIpcBlocking_notificationHead_inPlace hN hH hT hB, ih]
          · rfl
        · rfl
      · rfl
    · rfl

/-- **seL4's `cancelAllSignals`**: every waiter, compiled through the in-place step
(`cancelNotificationQueue_eq_impl`, stated above it so the compiler takes it). -/
def cancelAllSignals (notificationId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  cancelNotificationQueue notificationId st.objects.size st

/-- **seL4's `unbindMaybeNotification`**: the thread the notification is bound
to, when that thread is bound back to it, is unbound from it on both sides, each
side rewritten where it stands (`storeUnbindNotification`, which is
`unbindNotification` under `unbindNotificationInPlace`).  A binding that does
not agree on both sides is left as it is, and the retire then refuses the
notification. -/
def unbindMaybeNotification (notificationId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  match st.getNotification? notificationId with
  | some n =>
    match n.boundTCB with
    | some t =>
      if boundNotificationCodeOf st t == notificationId.val + 1 && unbindNotificationInPlace st t then
        storeUnbindNotification st t notificationId
      else st
    | none => st
  | none => st

-- ============================================================================
-- §4  The finalisation a final delete runs
-- ============================================================================

/-- **seL4's `finaliseCap` on the final capability to an endpoint or a
notification** (`target`, a word as `slotRetireTarget` reads it: `x + 1`, or
`0` for none): an endpoint's waiters are cancelled (`cancelAllIpc`); a
notification is unbound from its thread and its waiters are cancelled
(`unbindMaybeNotification`, `cancelAllSignals`).  Nothing when no object is
targeted, for any other kind, or when the object is still held outside every
slot — a service registration's endpoint capability, an interrupt's
notification — since seL4 would hold a capability there and the slot's would
not be final. -/
def finaliseFinalObject (target : Nat) (st : SystemState) : SystemState :=
  if target = 0 then st
  else
    let x := SeLe4n.ObjId.ofNat (target - 1)
    if registryNamesNone st x && irqHandlersNameNone st x then
      match st.getObjectType? x with
      | some .endpoint => cancelAllIpc x st
      | some .notification => cancelAllSignals x (unbindMaybeNotification x st)
      | _ => st
    else st

/-- **The retire of what a final delete destroyed, after its finalisation**:
`finaliseFinalObject`, then `retireFinalObject`. -/
@[inline] def retireFinalisedObject (executingCore : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) : SystemState :=
  retireFinalObject executingCore target recorder (finaliseFinalObject target st)

theorem finaliseFinalObject_zero (st : SystemState) : finaliseFinalObject 0 st = st := by
  simp [finaliseFinalObject]

theorem retireFinalisedObject_zero (ec : Concurrency.CoreId) (recorder : Nat)
    (st : SystemState) : retireFinalisedObject ec 0 recorder st = st := by
  simp [retireFinalisedObject, finaliseFinalObject_zero, retireFinalObject_zero]

end SeLe4n.Kernel
