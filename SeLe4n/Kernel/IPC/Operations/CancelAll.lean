/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.IPC.DualQueue.PopInPlace
import SeLe4n.Kernel.IPC.DualQueue.RemoveInPlace
import SeLe4n.Kernel.IPC.Operations.NotificationBind

/-!
# Cancelling every waiter of an endpoint or a notification

WS-ZA ZA5.4 part 23: seL4's `finaliseCap` on the final capability to an
endpoint runs `cancelAllIPC`, and on the final capability to a notification
runs `unbindMaybeNotification` then `cancelAllSignals`.  This module holds the
three, and `finaliseFinalObject`, which a final delete runs before the retire
(`retireFinalObject`) so that a busy endpoint or a busy or bound notification
is emptied and can then be retired.

WS-ZA ZA5.4 part 24: and on the final capability to a thread `finaliseCap`
unbinds its notification, cancels its IPC, suspends it — taking it off whichever
core holds it, queued there or current there, the executing core's own thread
included — releases every core's FP/SIMD and resident hold on it, and unbinds
its scheduling context; on the final capability to a scheduling context it
unbinds the context's thread (`finaliseThread`, `finaliseSchedContext`, §4).
Each then runs the destroy cleanup (`lifecyclePreRetypeCleanup`), so a thread
or a context leaves no reference behind and the retire can erase it; a core
whose current thread was deleted chooses a successor, or resumes its idle
loop.

WS-ZA ZA5.4 part 25: on the final capability to a reply whose caller still
waits on it `finaliseCap` runs `reply_remove`: a reply heading a scheduling
context's stack is popped, the context going back to the caller (`reply_pop`),
and any other is spliced out of its stack; the caller's call is then cancelled
and the caller made inactive (`finaliseReply`, §4).

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

/-- **Whether a waiter `t` of the notification at `notificationId` may be
cancelled** — the head a walk takes, or a finalised thread wherever it waits: it
is no reserved thread (the cancellation reads it as
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


/-- **A notification waiter's cancel, as an update of the notification's cell**
(`isHead` whether the waiter heads the queue, `prev` and `next` its neighbours):
the queue's ends rewritten as `removeFromNotificationWaitQueue` rewrites them —
the successor heads the queue when the head leaves, the predecessor ends it when
the tail leaves — and a `.waiting` notification whose queue empties goes
`.idle`.  `RHTable.modify` hands the update the cell exclusively, so it is
rewritten where it stands. -/
@[inline] def cancelledNotificationObject (isHead : Bool) (prev next : Option SeLe4n.ThreadId) :
    KernelObject → KernelObject
  | .notification n =>
    let head' := if isHead then next else n.waitHead
    .notification { n with
      waitHeadCode := SeLe4n.ThreadId.optCode head'
      waitTailCode := SeLe4n.ThreadId.optCode
        (if next.isSome then n.waitTail else if isHead then none else prev)
      state := if n.state = .waiting ∧ head'.isNone then .idle else n.state }
  | o => o

/-- **Cancel the waiter `t` of the notification at `notificationId`**, wherever it
waits in the queue (`isHead`, `prev` and `next` as `cancelledNotificationObject`
takes them), each write in its slot: the notification's cell rewritten, the
waiter's links cleared and its neighbours linked to each other
(`clearNtfnLinks`, `unlinkNtfnNeighbours`), and the waiter restored `.ready`
with the cancellation frame (`Lifecycle.Suspend.restoreToReadyCancelled`).  Out
of line, so each update is specialised in.  It wakes nothing: a walk wakes the
waiter after it, a thread's finalisation does not. -/
@[noinline] def storeNotificationBlockedCancelled (st : SystemState)
    (notificationId : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (isHead : Bool)
    (prev next : Option SeLe4n.ThreadId) : SystemState :=
  Lifecycle.Suspend.restoreToReadyCancelled
    (unlinkNtfnNeighbours
      (clearNtfnLinks (st.modifyObject notificationId (cancelledNotificationObject isHead prev next))
        t)
      (if isHead then none else prev) next) t

/-- **A notification waiter's cancel is its in-place writes**: on a waiter `t`
blocked on the notification, `cancelIpcBlocking` rewrites the notification with
`cancelledNotificationObject`'s fields (its `rewriteObject` is the table's
`insert`, which is `modify` on a key that is present), then makes the writes
`storeNotificationBlockedCancelled` makes, wherever `t` waits. -/
theorem cancelIpcBlocking_notification_inPlace {st : SystemState}
    {notificationId : SeLe4n.ObjId} {ntfn : Notification} {t : SeLe4n.ThreadId} {tcb : TCB}
    (hN : st.getNotification? notificationId = some ntfn) (hT : st.getTcb? t = some tcb)
    (hB : tcb.ipcState = .blockedOnNotification notificationId) :
    Lifecycle.Suspend.cancelIpcBlocking st t tcb =
      storeNotificationBlockedCancelled st notificationId t (ntfn.waitHead == some t)
        tcb.ntfnPrev tcb.ntfnNext := by
  have hNo := (SystemState.getNotification?_eq_some_iff _ _ _).mp hN
  unfold storeNotificationBlockedCancelled Lifecycle.Suspend.cancelIpcBlocking
  rw [hB]
  unfold removeFromNotificationWaitQueue
  simp only [hT, hB, SystemState.getNotificationWitnessed?_eq_some hN]
  unfold SystemState.rewriteObject SystemState.modifyObject
  rw [RobinHood.RHTable.modify_of_get? (show st.objects.get? notificationId = _ from hNo)]
  by_cases hH : ntfn.waitHead = some t <;> simp [hH, cancelledNotificationObject]

/-- **`cancelNotificationQueue` as compiled**: each admitted head is cancelled
by `storeNotificationBlockedCancelled`, in place, then woken, which is the
specification's step (`cancelIpcBlocking_notification_inPlace`). -/
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
              (wakeCancelledWaiter
                (storeNotificationBlockedCancelled st notificationId t true tcb.ntfnPrev
                  tcb.ntfnNext) t)
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
            rw [cancelIpcBlocking_notification_inPlace hN hT hB, ih, hH]
            simp
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
-- §4  A thread's and a scheduling context's finalisation
-- ============================================================================

/-- **No scheduling context records `c` as the origin of a reservation on loan**
(`c` a thread's id plus one): the scan `clearDonationOriginReferences` would
otherwise have work to do, which a thread being finalised may not leave it. -/
@[inline] def originsNameNone (st : SystemState) (c : Nat) : Bool :=
  st.objects.fold true fun acc _ o => acc && match o with
    | .schedContext sc => SeLe4n.ThreadId.optCode sc.donationOrigin != c
    | _ => true

/-- A thread whose binding codes name a context and no owner is `.bound` to it
(stated here, ahead of the compiled unbinds that read it). -/
theorem schedContextBinding_of_codes' {tcb : TCB} (hS : tcb.scBindingScCode ≠ 0)
    (hO : tcb.scBindingOwnerCode = 0) :
    tcb.schedContextBinding = .bound ⟨tcb.scBindingScCode - 1⟩ := by
  unfold TCB.schedContextBinding SchedContextBinding.ofCodes
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hS
  rw [hs, hO]; simp

/-- **Whether the thread `tid` (its TCB `tcb`), blocked on the endpoint `ep` at
`endpointId`, may be cancelled off that endpoint's receive queue
(`isReceiveQ`) or its send queue, wherever it waits there**: it is blocked on
that side (`blockedOnQueueSide`, which the receive-completing store needs: a
thread blocked on a reply holds a link that store does not end), it waits with
no timeout budget (a `.ready` thread holding one would break
`blockedThreadTimeoutConsistent`; no transition gives a waiter one), every write
of the removal stays in its slot (`queueRemoveInPlace`, under which the removal
is `storeQueueRemove`, `queueRemove_inPlace`), and a predecessor the removal
makes the queue's tail is blocked on the same side (the splice's
`splicePredecessorBlocked`, which the invariants do not entail). -/
@[inline] def endpointBlockedCancellable (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) : Bool :=
  blockedOnQueueSide isReceiveQ endpointId tcb && tcb.timeoutBudget.isNone &&
    queueRemoveInPlace st endpointId isReceiveQ tid ep tcb &&
    match tcb.queueNext, tcb.queuePPrev with
    | none, some (.tcbNext p) =>
      match st.getTcb? p with
      | some pt => blockedOnQueueSide isReceiveQ endpointId pt
      | none => false
    | _, _ => true

/-- **Cancel the thread `tid`, blocked on an endpoint, off its queue** (seL4's
`cancelIPC` → `blockedCancelIPC` → `tcbEPDequeue`): removed from wherever it waits
(`storeQueueRemove`, the specification's `endpointQueueRemoveDual` by
`queueRemove_inPlace`), its IPC ended as a cancelled waiter's is
(`cancelledEndpointWaiterTcb`: `.ready`, no message, no stashed reply, the
cancellation frame staged), each write in its slot.  It wakes nothing: the
thread is being finalised, and the suspend after it takes it off the scheduler.
Out of line, so each update is specialised in. -/
@[noinline] def storeEndpointBlockedCancelled (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) : SystemState :=
  (storeQueueRemove st endpointId isReceiveQ tid ep tcb).updateTcb tid cancelledEndpointWaiterTcb

/-- **The cancel of a thread blocked on the endpoint at `endpointId`**: when the
endpoint is present and `endpointBlockedCancellable` admits the thread,
`storeEndpointBlockedCancelled`; otherwise nothing is written. -/
@[inline] def cancelEndpointBlocked (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (tcb : TCB) : SystemState :=
  match st.getEndpoint? endpointId with
  | some ep =>
    if endpointBlockedCancellable st endpointId isReceiveQ tid ep tcb then
      storeEndpointBlockedCancelled st endpointId isReceiveQ tid ep tcb
    else st
  | none => st

/-- **Whether the endpoint cancel admits the thread `tid`**, as the admission
reads it: the endpoint is present and `endpointBlockedCancellable` admits the
thread, which waits in no notification queue. -/
@[inline] def endpointCancelAdmitted (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (tcb : TCB) : Bool :=
  tcb.ntfnNextCode == 0 && tcb.ntfnPrevCode == 0 &&
    match st.getEndpoint? endpointId with
    | some ep => endpointBlockedCancellable st endpointId isReceiveQ tid ep tcb
    | none => false

/-- **Whether the finalisation's cancel admits the IPC state of the thread
`tid`**, read from its two codes: ready, holding no queue link or stashed
reply (a message delivered to it is dropped by the suspend's mark,
`finalisedSuspendMark`); or blocked on a notification, which the notification
cancel admits (`notificationWaiterCancellable`), holding no stashed reply;
or blocked sending, calling or receiving on an endpoint, which the endpoint
cancel admits (`endpointCancelAdmitted`) — that cancel ends the message and the
stash.  A thread blocked on a reply is not admitted. -/
@[inline] def threadIpcCancelAdmitted (st : SystemState) (tid : SeLe4n.ThreadId) (t : TCB) :
    Bool :=
  match t.ipcStateCode with
  | 0 =>
    if t.ipcObjectCode == 0 then
      t.queueNextCode == 0 && t.queuePrevCode == 0 && t.queuePPrevCode == 0 &&
        t.pendingReceiveReplyCode == 0 && t.ntfnNextCode == 0 && t.ntfnPrevCode == 0
    else endpointCancelAdmitted st ⟨t.ipcObjectCode - 1⟩ false tid t
  | 1 => endpointCancelAdmitted st ⟨t.ipcObjectCode⟩ true tid t
  | 2 =>
    t.queuePPrevCode == 0 && t.pendingReceiveReplyCode == 0 &&
      match st.getNotification? ⟨t.ipcObjectCode⟩ with
      | some _ => notificationWaiterCancellable st ⟨t.ipcObjectCode⟩ tid t
      | none => false
  | 3 => endpointCancelAdmitted st ⟨t.ipcObjectCode⟩ false tid t
  | _ => false

/-- **Whether a final delete may finalise the thread at `x`**, read on the
pre-state before any write.  The thread is stored under its own id and is no
reserved or idle thread; its IPC state is one the cancel ends
(`threadIpcCancelAdmitted`): ready (suspended, queued, current on a core — the
executing core's own thread deleting its last capability included — or held by
a core as its FP/SIMD owner or its resident), blocked on a notification, or
blocked receiving, sending or calling on an endpoint, wherever it waits in that
queue; it is linked into no reply-waiter queue, holds no reply link or timeout
budget, and lends or borrows no reservation (a reply-blocked thread, its reply
links and a donated binding are the busy reply's finalisation, a later cut's);
its space slots are empty (their finalising delete is a later cut's); a bound
notification and a bound scheduling context are bound back to it; and nothing
else names it as a reservation's origin or as a service's owner.  Each step
below re-reads its own guard, so a state outside this set is left as it is and
the retire then refuses the thread. -/
@[inline] def threadFinaliseAdmitted (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObject? x with
  | some (.tcb t) =>
    let tid : SeLe4n.ThreadId := ⟨x.val⟩
    t.tid.val == x.val && !tid.isReserved && !isIdleThreadId tid &&
    t.replyWaiterNextCode == 0 && t.replyWaiterPrevCode == 0 && t.replyWaitersHeadCode == 0 &&
    t.replyObjectCode == 0 && t.timeoutBudget.isNone && t.scBindingOwnerCode == 0 &&
    t.spaceCells[0].isNone && t.spaceCells[1].isNone &&
    threadIpcCancelAdmitted st tid t &&
    (t.boundNotificationCode == 0 ||
      ((match st.getNotification? ⟨t.boundNotificationCode - 1⟩ with
        | some n => n.boundTCBCode == x.val + 1
        | none => false) && unbindNotificationInPlace st tid)) &&
    (t.scBindingScCode == 0 ||
      match st.getSchedContext? ⟨t.scBindingScCode - 1⟩ with
      | some sc => sc.boundThreadCode == x.val + 1
      | none => false) &&
    originsNameNone st (x.val + 1) && servicesNameNone st x
  | _ => false

/-- **Cancel the blocked IPC of a thread being finalised** (seL4's `suspend` →
`cancelIPC`): a thread blocked on a notification leaves its queue, wherever it
waits there, and is made `.ready` with the cancellation frame, as
`cancelIpcBlocking`'s notification arm makes it (`cancelSignal`); a thread
blocked receiving, sending or calling on an endpoint leaves that endpoint's
queue, wherever it waits there, and is made `.ready` with the cancellation frame
(`cancelEndpointBlocked`: `blockedCancelIPC`).  Neither is woken — the thread is
being destroyed.  A thread blocked on a reply, and any other state, is left
alone. -/
def finaliseThreadCancel (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some t =>
    match t.ipcState with
    | .blockedOnNotification n =>
      match st.getNotification? n with
      | some _ =>
        if notificationWaiterCancellable st n tid t then
          Lifecycle.Suspend.cancelIpcBlocking st tid t
        else st
      | none => st
    | .blockedOnReceive e => cancelEndpointBlocked st e true tid t
    | .blockedOnSend e => cancelEndpointBlocked st e false tid t
    | .blockedOnCall e => cancelEndpointBlocked st e false tid t
    | _ => st
  | none => st

/-- **`finaliseThreadCancel` as compiled**: the notification cancel is its
in-place writes (`storeNotificationBlockedCancelled`,
`cancelIpcBlocking_notification_inPlace`); the endpoint cancel is already
written in place. -/
def finaliseThreadCancelImpl (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some t =>
    match t.ipcState with
    | .blockedOnNotification n =>
      match st.getNotification? n with
      | some ntfn =>
        if notificationWaiterCancellable st n tid t then
          storeNotificationBlockedCancelled st n tid (ntfn.waitHead == some tid) t.ntfnPrev
            t.ntfnNext
        else st
      | none => st
    | .blockedOnReceive e => cancelEndpointBlocked st e true tid t
    | .blockedOnSend e => cancelEndpointBlocked st e false tid t
    | .blockedOnCall e => cancelEndpointBlocked st e false tid t
    | _ => st
  | none => st

@[csimp] theorem finaliseThreadCancel_eq_impl :
    @finaliseThreadCancel = @finaliseThreadCancelImpl := by
  funext st tid
  unfold finaliseThreadCancel finaliseThreadCancelImpl
  split
  · rename_i t hT
    split
    · rename_i n hB
      split
      · rename_i ntfn hN
        split
        · exact cancelIpcBlocking_notification_inPlace hN hT hB
        · rfl
      · rfl
    all_goals rfl
  · rfl

/-- **The mark a finalised thread's suspend writes** (seL4's `setThreadState
Inactive`): `.Inactive`, holding no message.  A message delivered to a ready
thread and not yet read is dropped, as the suspend syscall's
`Lifecycle.Suspend.clearPendingState` drops it: seL4 keeps a delivered message
only in the receiver's registers and IPC buffer, which die with the thread.
One field update of the thread's own cell. -/
@[inline] def finalisedSuspendMark (t : TCB) : TCB :=
  { t with threadState := .Inactive, pendingMessage := none }

/-- **Suspend a thread being finalised** (seL4's `suspend`: `setThreadState
Inactive`, then `tcbSchedDequeue`, with the `rescheduleRequired` a dequeued
running thread takes): a ready thread, no core's idle thread, that is not
already suspended leaves the scheduler where the state places it — the run
queue it waits on, or the current slot of the core running it — and is marked
`.Inactive`.  The removal is `descheduleAtPlacement`, the suspend syscall's own
(`suspendPerform`): it clears a vacated core's slot and raises
that core's reschedule flag, so the executing core, when it is the thread's
own, chooses a successor before the syscall returns
(`scheduleLocalSuccessorFrom`), and any other core takes the `.reschedule`
interrupt the flag raises and does (`dispatchVacatedCore`).  A core whose slot
is empty resumes its idle loop, never the frame it trapped with.  The mark also
drops a message delivered to the thread and not yet read
(`finalisedSuspendMark`), so a suspended thread still holding one is marked
again rather than kept. -/
def finaliseThreadSuspend (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some t =>
    if t.ipcStateCode == 0 && t.ipcObjectCode == 0 &&
        (t.threadState != .Inactive || t.pendingMessage.isSome) && !isIdleThreadId tid then
      (descheduleAtPlacement st tid).updateTcb tid finalisedSuspendMark
    else st
  | none => st

/-- **Release every core's hold on a thread being finalised** (seL4's
`fpuThreadDelete`, which `Arch_prepareThreadDelete` runs): no core's FP/SIMD
registers are recorded as its and no core records it as resident
(`MachineState.releaseThread`).  Neither the live FP/SIMD values nor the
registers a core still running it at EL0 holds are saved: the thread is being
destroyed, and the next entry on that core saves nothing for it
(`saveVacatedFrameOnCore`), so nothing of it reaches a thread later stored under
its id. -/
def finaliseThreadReleaseCores (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  { st with machine := st.machine.releaseThread tid }

@[simp] theorem finaliseThreadReleaseCores_objects (st : SystemState) (tid : SeLe4n.ThreadId) :
    (finaliseThreadReleaseCores st tid).objects = st.objects := by
  unfold finaliseThreadReleaseCores; dsimp only

@[simp] theorem finaliseThreadReleaseCores_scheduler (st : SystemState) (tid : SeLe4n.ThreadId) :
    (finaliseThreadReleaseCores st tid).scheduler = st.scheduler := by
  unfold finaliseThreadReleaseCores; dsimp only

@[simp] theorem finaliseThreadReleaseCores_machine (st : SystemState) (tid : SeLe4n.ThreadId) :
    (finaliseThreadReleaseCores st tid).machine = st.machine.releaseThread tid := by
  unfold finaliseThreadReleaseCores; dsimp only

@[simp] theorem finaliseThreadReleaseCores_getTcb? (st : SystemState) (tid t : SeLe4n.ThreadId) :
    (finaliseThreadReleaseCores st tid).getTcb? t = st.getTcb? t := by
  unfold SystemState.getTcb?; rw [finaliseThreadReleaseCores_objects]

/-- The release names a thread on no core's FP/SIMD registers and as no core's
resident. -/
theorem finaliseThreadReleaseCores_unheld (st : SystemState) (tid : SeLe4n.ThreadId) :
    (finaliseThreadReleaseCores st tid).machine.fpOwnedOnSomeCore tid = false ∧
      (finaliseThreadReleaseCores st tid).machine.residentOnSomeCore tid = false := by
  rw [finaliseThreadReleaseCores_machine]; exact MachineState.releaseThread_releases _ _

/-- **Unbind a thread being finalised from its notification** (seL4's
`unbindNotification`), when the notification is bound back to it, each side
rewritten where it stands (`storeUnbindNotification`). -/
def finaliseThreadUnbindNotification (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  let c := boundNotificationCodeOf st tid
  if c == 0 then st
  else
    match st.getNotification? ⟨c - 1⟩ with
    | some n =>
      if n.boundTCBCode == tid.val + 1 && unbindNotificationInPlace st tid then
        storeUnbindNotification st tid ⟨c - 1⟩
      else st
    | none => st

/-- **Unbind a thread being finalised from the scheduling context it owns**
(seL4's `unbindFromSC`): the reservation arm the destroy cleanup runs
(`cancelDonationArmOnCore`), at a `.bound` thread whose context is bound back
to it, and before the cleanup, so the cleanup finds the thread unbound. -/
def finaliseThreadUnbindSchedContext (st : SystemState) (tid : SeLe4n.ThreadId) :
    SystemState :=
  match st.getTcb? tid with
  | some t =>
    if t.scBindingScCode != 0 && t.scBindingOwnerCode == 0 && t.runCoreCode == 0 &&
        !threadHeldOnSomeCore st tid &&
        (match st.getSchedContext? ⟨t.scBindingScCode - 1⟩ with
          | some sc => sc.boundThreadCode == tid.val + 1
          | none => false) then
      match cancelDonationArmOnCore st tid t with
      | .ok st' => st'
      | .error _ => st
    else st
  | none => st

/-- The compiled `finaliseThreadUnbindSchedContext`: the guard names a `.bound`
binding, on which the reservation arm is the in-place unbind
(`cancelBoundDonationPerform`), so no error branch holds the pre-state across
its writes. -/
@[inline] def finaliseThreadUnbindSchedContextImpl (st : SystemState) (tid : SeLe4n.ThreadId) :
    SystemState :=
  match st.getTcb? tid with
  | some t =>
    let scCode := t.scBindingScCode
    if scCode != 0 && t.scBindingOwnerCode == 0 && t.runCoreCode == 0 &&
        !threadHeldOnSomeCore st tid &&
        (match st.getSchedContext? ⟨scCode - 1⟩ with
          | some sc => sc.boundThreadCode == tid.val + 1
          | none => false) then
      cancelBoundDonationPerform st tid ⟨scCode - 1⟩ (determineTargetCore st tid)
    else st
  | none => st

@[csimp] theorem finaliseThreadUnbindSchedContext_eq_impl :
    @finaliseThreadUnbindSchedContext = @finaliseThreadUnbindSchedContextImpl := by
  funext st tid
  unfold finaliseThreadUnbindSchedContext finaliseThreadUnbindSchedContextImpl
  cases st.getTcb? tid with
  | none => rfl
  | some t =>
    refine ite_congr rfl (fun hG => ?_) (fun _ => rfl)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hG
    rw [cancelDonationArmOnCore_of_bound st tid t _
      (schedContextBinding_of_codes' hG.1.1.1.1 hG.1.1.1.2),
      cancelBoundDonationOnCore_of_bound st tid t _ _
      (schedContextBinding_of_codes' hG.1.1.1.1 hG.1.1.1.2)]

/-- **The destroy cleanup of a finalised thread** (`lifecyclePreRetypeCleanup`'s
thread arm): run once the thread is retirable — quiescent, held by no core and
named by no object — so its reference sweeps find nothing and only its two
space slots leave the derivation tree. -/
def finaliseThreadCleanup (st : SystemState) (x : SeLe4n.ObjId) : SystemState :=
  if threadRetirable st x && x.val != 0 then
    match st.getObject? x with
    | some (.tcb t) =>
      match lifecyclePreRetypeCleanup st x (.tcb t) (.tcb t) with
      | .ok st' => st'
      | .error _ => st
    | _ => st
  else st

/-- **Whether a reply stack's head link names the context at `x`.** -/
@[inline] def replyStackLinkHeads (x : SeLe4n.ObjId) : Option ReplyStackLink → Bool
  | some (.head s) => s.val == x.val
  | _ => false

/-- **Whether a final delete may finalise the scheduling context at `x`**: a
reply stack it heads has a head that names it back; a thread it is bound to is
bound back to it, as its own (`.bound`) or on loan (`.donated`), is no core's
idle thread, is ready (queued, current on a core, or neither: the deschedule
takes it off whichever core places it) or else on no core, whatever it waits
on: a thread blocked sending or calling keeps waiting with no reservation, as
seL4's `schedContext_unbindTCB` leaves it; and a context bound to no thread is
lent by no one. -/
@[inline] def schedContextFinaliseAdmitted (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObject? x with
  | some (.schedContext sc) =>
    (match sc.scReply with
      | none => true
      | some rid =>
        match st.getReply? rid with
        | some r => replyStackLinkHeads x r.next
        | none => false) &&
    (if sc.boundThreadCode == 0 then sc.donationOrigin.isNone
     else
      let tid : SeLe4n.ThreadId := ⟨sc.boundThreadCode - 1⟩
      match st.getTcb? tid with
      | some t =>
        t.scBindingScCode == x.val + 1 && !isIdleThreadId tid &&
        ((t.ipcStateCode == 0 && t.ipcObjectCode == 0) ||
          (t.runCoreCode == 0 && !threadCurrentOnSomeCore st tid))
      | none => false)
  | _ => false

/-- **Take a scheduling context's ready holder off the scheduler** (seL4's
`schedContext_unbindTCB`: `tcbSchedDequeue`, with the `rescheduleRequired` a
running thread takes): the thread bound to the context leaves the run queue it
waits on, or the current slot of the core running it, by the suspend's own
removal (`descheduleAtPlacement`), which raises that core's reschedule flag, so
the core chooses another thread.  The thread stays ready, with no reservation:
it is not runnable until a context is bound to it again.  A holder that is not
ready waits on no core and is left as it is. -/
def finaliseSchedContextDeschedule (st : SystemState) (x : SeLe4n.ObjId) : SystemState :=
  match st.getObject? x with
  | some (.schedContext sc) =>
    if sc.boundThreadCode == 0 then st
    else
      let tid : SeLe4n.ThreadId := ⟨sc.boundThreadCode - 1⟩
      match st.getTcb? tid with
      | some t =>
        if t.scBindingScCode == x.val + 1 && t.ipcStateCode == 0 && t.ipcObjectCode == 0 &&
            !isIdleThreadId tid then
          descheduleAtPlacement st tid
        else st
      | none => st
  | _ => st

/-- **Unbind a scheduling context being finalised from its thread** (seL4's
`schedContext_unbindAllTCBs`), once the thread is off the scheduler
(`finaliseSchedContextDeschedule`): the in-place unbind of the reservation arm
(`cancelBoundDonationOnCore`), which clears both sides, the context's lender and
its replenishment on the thread's home core, with the thread's binding read as
the context's own whether it holds it as its own or on loan
(`{ t with scBindingOwnerCode := 0 }`): seL4 unbinds whichever thread runs on
the context, and the lender, if any, keeps waiting on its reply with no
reservation. -/
def finaliseSchedContextUnbind (st : SystemState) (x : SeLe4n.ObjId) : SystemState :=
  match st.getObject? x with
  | some (.schedContext sc) =>
    if sc.boundThreadCode == 0 then st
    else
      let tid : SeLe4n.ThreadId := ⟨sc.boundThreadCode - 1⟩
      match st.getTcb? tid with
      | some t =>
        if t.scBindingScCode == x.val + 1 then
          match cancelBoundDonationOnCore st tid { t with scBindingOwnerCode := 0 }
              (determineTargetCore st tid) with
          | .ok st' => st'
          | .error _ => st
        else st
      | none => st
  | _ => st

/-- The binding a thread's codes stand for once its owner code is cleared: the
context it names, as its own. -/
theorem schedContextBinding_ownerCleared {t : TCB} {x : SeLe4n.ObjId}
    (h : t.scBindingScCode = x.val + 1) :
    ({ t with scBindingOwnerCode := 0 } : TCB).schedContextBinding = .bound ⟨x.val⟩ := by
  unfold TCB.schedContextBinding SchedContextBinding.ofCodes
  simp only [h]

/-- The compiled `finaliseSchedContextUnbind`: the guard names a binding to the
context, so the reservation arm is the in-place unbind
(`cancelBoundDonationPerform`). -/
@[inline] def finaliseSchedContextUnbindImpl (st : SystemState) (x : SeLe4n.ObjId) :
    SystemState :=
  match st.getObject? x with
  | some (.schedContext sc) =>
    let bc := sc.boundThreadCode
    if bc == 0 then st
    else
      let tid : SeLe4n.ThreadId := ⟨bc - 1⟩
      match st.getTcb? tid with
      | some t =>
        if t.scBindingScCode == x.val + 1 then
          cancelBoundDonationPerform st tid ⟨x.val⟩ (determineTargetCore st tid)
        else st
      | none => st
  | _ => st

@[csimp] theorem finaliseSchedContextUnbind_eq_impl :
    @finaliseSchedContextUnbind = @finaliseSchedContextUnbindImpl := by
  funext st x
  unfold finaliseSchedContextUnbind finaliseSchedContextUnbindImpl
  split
  · next sc _ =>
    simp only
    split
    · rfl
    · cases st.getTcb? ⟨sc.boundThreadCode - 1⟩ with
      | none => rfl
      | some t =>
        simp only
        split
        · next hG =>
          simp only [beq_iff_eq] at hG
          rw [cancelBoundDonationOnCore_of_bound st _ _ _ _
            (schedContextBinding_ownerCleared hG)]
        · rfl
  · rfl

/-- **Let go of the reply stack a scheduling context being finalised heads**
(seL4's `schedContext_unbindReply`: `scReply->replyNext = 0; scReply = NULL`):
the head reply's upward link is cleared, then the context's head.  The frames
below the head stay linked to it, a stack no context carries, and their callers
keep waiting on their replies. -/
def finaliseSchedContextUnstack (st : SystemState) (x : SeLe4n.ObjId) : SystemState :=
  match st.getSchedContext? ⟨x.val⟩ with
  | some sc =>
    match sc.scReply with
    | some rid =>
      match st.getReply? rid with
      | some r =>
        if replyStackLinkHeads x r.next then
          match storeObject rid.toObjId (.reply { r with next := none }) st with
          | .ok ((), st1) => st1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }
          | .error _ => st
        else st
      | none => st
    | none => st
  | none => st

/-- **The destroy cleanup of a finalised scheduling context**
(`lifecyclePreRetypeCleanup`'s scheduling-context arm), run once the context is
bound to no thread and heads no reply stack, so its release finds no binding
(`lifecyclePreRetypeCleanup_of_schedContextFree`). -/
def finaliseSchedContextCleanup (st : SystemState) (x : SeLe4n.ObjId) : SystemState :=
  match st.getObject? x with
  | some (.schedContext sc) =>
    if sc.boundThreadCode == 0 && sc.scReply.isNone then
      match lifecyclePreRetypeCleanup st x (.schedContext sc) (.schedContext sc) with
      | .ok st' => st'
      | .error _ => st
    else st
  | _ => st

-- ============================================================================
-- §4a  What the destroy cleanup finds on a finalised object
-- ============================================================================

/-- A thread code other than `b`'s does not decode to `b`. -/
theorem threadOfOptCode_beq_some_false {n : Nat} {b : SeLe4n.ThreadId} (h : n ≠ b.val + 1) :
    (SeLe4n.ThreadId.ofOptCode n == some b) = false := by
  cases hc : (SeLe4n.ThreadId.ofOptCode n == some b)
  · rfl
  · exact absurd (threadOfOptCode_eq_some (beq_iff_eq.mp hc)) h

/-- **The run-queue sweep has nothing to do for a thread no core holds**:
queued on no core and current on none. -/
theorem removeRunnableFromAllCores_of_unoccupied {st : SystemState} {tid : SeLe4n.ThreadId}
    (h : ∀ c, threadOccupiesCore st tid c = false) : removeRunnableFromAllCores st tid = st := by
  unfold removeRunnableFromAllCores
  generalize SeLe4n.Kernel.Concurrency.allCores = cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons]
    have hc : removeRunnableStepOnCore tid st c = st := by
      unfold removeRunnableStepOnCore; rw [h c]; rfl
    rw [hc]; exact ih

/-- **What a retirable thread is**, unpacked from `threadRetirable`. -/
theorem threadRetirable_spec {st : SystemState} {x : SeLe4n.ObjId} {t : TCB}
    (hT : st.getObject? x = some (.tcb t)) (h : threadRetirable st x = true) :
    t.tid = ⟨x.val⟩ ∧ threadQuiescent t = true ∧ threadHeldOnSomeCore st t.tid = false ∧
      storeNamesThreadNone st (x.val + 1) = true := by
  unfold threadRetirable at h; rw [hT] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hId, -⟩, hQ⟩, hH⟩, hN⟩, -⟩ := h
  exact ⟨by cases ht : t.tid; rw [ht] at hId; simp only at hId; rw [hId], hQ, hH, hN⟩

/-- **The destroy cleanup of a retirable thread is the identity.**  A thread a
final delete may retire is quiescent, held by no core and named by no object
(`threadRetirable`), so each sweep of `lifecyclePreRetypeCleanup`'s thread arm
finds nothing: no reservation to end, no run queue, endpoint queue or
notification queue to leave, no reservation origin to clear, no space slot to
splice out of the derivation tree, and no reply link to refuse on.  This is the
statement that the finalisation before it left the thread nothing dangling. -/
theorem lifecyclePreRetypeCleanup_of_threadRetirable {st : SystemState} {x : SeLe4n.ObjId}
    {t : TCB} (hT : st.getObject? x = some (.tcb t)) (hR : threadRetirable st x = true)
    (hRes : x.val ≠ 0) :
    lifecyclePreRetypeCleanup st x (.tcb t) (.tcb t) = .ok st := by
  obtain ⟨hTid, hQ, hHeld, hNames⟩ := threadRetirable_spec hT hR
  obtain ⟨-, hIS, hIO, -, hQN, hQP, -, -, -, hRC, -, -, -, -, -, -, hWH, hSC, hSO, -, hRO, -,
    -, hS0, hS1⟩ := threadQuiescent_codes hQ
  have hX : t.tid.toObjId = x := by rw [hTid]; rfl
  have hObj : st.objects[x]? = some (.tcb t) := by rw [← hT]; simp
  have hGet : st.getTcb? t.tid = some t := (SystemState.getTcb?_eq_some_iff st _ t).mpr (hX ▸ hObj)
  have hNm : ∀ (k : SeLe4n.ObjId) (o : KernelObject), st.objects[k]? = some o → objectNamesThread o (x.val + 1) = false := by
    intro k o hk
    have := RobinHood.RHTable.fold_and_true_of_get? st.objects
      (fun _ o => !objectNamesThread o (x.val + 1)) hNames hk
    simpa using this
  have hCode : t.tid.val + 1 = x.val + 1 := by rw [hTid]
  -- The reservation arm: an unbound thread is left alone.
  have hUnb : t.schedContextBinding = .unbound := by
    unfold TCB.schedContextBinding; rw [hSC, hSO]; rfl
  -- The run-queue sweep: queued on no core, current on none.
  have hRun : removeRunnableFromAllCores st t.tid = st := by
    refine removeRunnableFromAllCores_of_unoccupied (fun c => ?_)
    unfold threadOccupiesCore SystemState.queuedOn
    rw [hGet]; dsimp only; rw [hRC]
    have hCur : (st.scheduler.currentOnCore c == some t.tid) = false := by
      cases hc : (st.scheduler.currentOnCore c == some t.tid)
      · rfl
      · have : threadCurrentOnSomeCore st t.tid = true :=
          (threadCurrentOnSomeCore_iff st t.tid).mpr ⟨c, beq_iff_eq.mp hc⟩
        unfold threadHeldOnSomeCore at hHeld; rw [this] at hHeld; cases hHeld
    rw [hCur]; simp
  -- The endpoint sweep: no interior link to splice, no queue end to move.
  have hSplice : spliceOutMidQueueNode st t.tid = st := by
    unfold spliceOutMidQueueNode
    have hL : lookupTcb st t.tid = some t := by
      unfold lookupTcb
      rw [hTid] at hGet ⊢
      simp only [SeLe4n.ThreadId.isReserved, hRes, decide_false, Bool.false_eq_true, if_false]
      exact hGet
    rw [hL]; dsimp only
    rw [show t.queuePrev = none by unfold TCB.queuePrev; rw [hQP]; rfl,
      show t.queueNext = none by unfold TCB.queueNext; rw [hQN]; rfl]
  have hEp : removeFromAllEndpointQueues st t.tid = st := by
    unfold removeFromAllEndpointQueues
    rw [hSplice]
    refine RobinHood.RHTable.fold_preserves _ _ _ (· = st) rfl (fun acc k v hacc => ?_)
    subst acc
    cases v with
    | endpoint _ =>
      dsimp only
      split
      · rename_i ep hEp _
        have hn := hNm k _ ((SystemState.getEndpoint?_eq_some_iff st k ep).mp hEp)
        simp only [objectNamesThread, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hn
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hn
        rw [if_neg]
        simp only [Endpoint.sendQ, Endpoint.receiveQ,
          threadOfOptCode_beq_some_false (b := t.tid) (hCode ▸ h1),
          threadOfOptCode_beq_some_false (b := t.tid) (hCode ▸ h2),
          threadOfOptCode_beq_some_false (b := t.tid) (hCode ▸ h3),
          threadOfOptCode_beq_some_false (b := t.tid) (hCode ▸ h4)]
        decide
      · rfl
    | _ => rfl
  -- The notification sweep: blocked on no notification.
  have hNtfn : removeFromNotificationWaitQueue st t.tid = st := by
    unfold removeFromNotificationWaitQueue
    rw [hGet]; dsimp only; rw [threadQuiescent_ipcState hQ]
  -- The origin sweep: no context names the thread as its reservation's origin.
  have hOrig : clearDonationOriginReferences st t.tid = st := by
    unfold clearDonationOriginReferences
    refine RobinHood.RHTable.fold_preserves_of_fold_and st.objects
      (fun _ o => !objectNamesThread o (x.val + 1)) hNames st _ (· = st) rfl
      (fun acc k v hv hacc => ?_)
    subst acc
    cases v with
    | schedContext sc =>
      simp only [objectNamesThread, Bool.not_or, Bool.and_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne] at hv
      dsimp only
      rw [if_neg]
      intro hb
      have := congrArg SeLe4n.ThreadId.optCode (beq_iff_eq.mp hb)
      exact hv.2 (by rw [this]; exact hCode)
    | _ => rfl
  have hClean : cleanupTcbReferences st t.tid = st := by
    unfold cleanupTcbReferences
    simp only [hRun, hEp, hNtfn, hOrig]
  -- The space slots: both empty, so neither is spliced.
  have hDet : detachTcbSlots st x = st := by
    refine detachTcbSlots_of_empty ?_ ?_
    · rw [SystemState.slotCapAt_of_object hObj]
      simp only [KernelObject.slotCap, TCB.spaceSlotCap, TCB.cspaceRootSlot]
      rw [dif_pos (by decide)]; exact hS0
    · rw [SystemState.slotCapAt_of_object hObj]
      simp only [KernelObject.slotCap, TCB.spaceSlotCap, TCB.vspaceRootSlot]
      rw [dif_pos (by decide)]; exact hS1
  unfold lifecyclePreRetypeCleanup
  simp only [hHeld, cancelDonationArmOnCore_of_unbound _ _ _ hUnb, Bool.false_eq_true, if_false]
  rw [hClean, hDet]
  have hRO' : t.replyObject = none := by unfold TCB.replyObject; rw [hRO]; rfl
  simp [hRO', hWH]

/-- **The destroy cleanup of a scheduling context bound to nothing and heading
no reply stack is the identity**: its release finds no binding. -/
theorem lifecyclePreRetypeCleanup_of_schedContextFree (st : SystemState) (x : SeLe4n.ObjId)
    (sc : SeLe4n.Kernel.SchedContext) (hB : sc.boundThreadCode = 0) (hR : sc.scReply = none) :
    lifecyclePreRetypeCleanup st x (.schedContext sc) (.schedContext sc) = .ok st := by
  unfold lifecyclePreRetypeCleanup
  simp only [hR, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [releaseSchedContextBinding_of_unbound _ _ _
    (by unfold SeLe4n.Kernel.SchedContext.boundThread; rw [hB]; rfl)]

/-- **A finalised thread's destroy cleanup leaves the state as it is**: it runs
only on a retirable thread, on which the cleanup is the identity
(`lifecyclePreRetypeCleanup_of_threadRetirable`). -/
theorem finaliseThreadCleanup_eq (st : SystemState) (x : SeLe4n.ObjId) :
    finaliseThreadCleanup st x = st := by
  unfold finaliseThreadCleanup
  split
  · rename_i h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    split
    · rename_i t hT
      rw [lifecyclePreRetypeCleanup_of_threadRetirable hT h.1 h.2]
    · rfl
  · rfl

/-- **A finalised scheduling context's destroy cleanup leaves the state as it
is**: it runs only on a context bound to nothing and heading no reply stack
(`lifecyclePreRetypeCleanup_of_schedContextFree`). -/
theorem finaliseSchedContextCleanup_eq (st : SystemState) (x : SeLe4n.ObjId) :
    finaliseSchedContextCleanup st x = st := by
  unfold finaliseSchedContextCleanup
  split
  · rename_i sc _
    split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
      rw [lifecyclePreRetypeCleanup_of_schedContextFree st x sc h.1 h.2]
    · rfl
  · rfl

/-- The compiled destroy cleanup of a finalised thread: what it provably is,
so the store scans its guard and sweeps would make are not run
(`finaliseThreadCleanup_eq`). -/
@[inline] def finaliseThreadCleanupImpl (st : SystemState) (_x : SeLe4n.ObjId) : SystemState := st

@[csimp] theorem finaliseThreadCleanup_eq_impl :
    @finaliseThreadCleanup = @finaliseThreadCleanupImpl := by
  funext st x; exact finaliseThreadCleanup_eq st x

/-- The compiled destroy cleanup of a finalised scheduling context
(`finaliseSchedContextCleanup_eq`). -/
@[inline] def finaliseSchedContextCleanupImpl (st : SystemState) (_x : SeLe4n.ObjId) :
    SystemState := st

@[csimp] theorem finaliseSchedContextCleanup_eq_impl :
    @finaliseSchedContextCleanup = @finaliseSchedContextCleanupImpl := by
  funext st x; exact finaliseSchedContextCleanup_eq st x

-- The finalisations are defined after their cleanups' `@[csimp]` theorems, so
-- their compiled code takes the compiled cleanups.

/-- **seL4's `finaliseCap` on the final capability to a thread**: unbound from
its notification (`unbindNotification`); suspended (`suspend`: its blocked IPC
cancelled, then `.Inactive` and off the scheduler, a core it ran on made to
choose another thread); released by every core (`fpuThreadDelete`, and the
residency record); unbound from its scheduling context (`schedContext_unbindTCB`,
whose own dequeue the suspend has made); then the destroy cleanup.  seL4 runs the
context unbind before the suspend, and the cut runs it after, so the unbind finds
the thread on no core, which is all the order changes: the whole finalisation is
one kernel step.  All of it runs only when the pre-state admits it
(`threadFinaliseAdmitted`), checks before writes. -/
def finaliseThread (x : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  if threadFinaliseAdmitted st x then
    let tid : SeLe4n.ThreadId := ⟨x.val⟩
    finaliseThreadCleanup
      (finaliseThreadUnbindSchedContext
        (finaliseThreadReleaseCores
          (finaliseThreadSuspend
            (finaliseThreadCancel
              (finaliseThreadUnbindNotification st tid) tid) tid) tid) tid) x
  else st

/-- **seL4's `finaliseCap` on the final capability to a scheduling context**:
its ready holder taken off the scheduler and unbound from it
(`schedContext_unbindAllTCBs`, `finaliseSchedContextDeschedule` then
`finaliseSchedContextUnbind`), its reply stack let go
(`schedContext_unbindReply`), then the destroy cleanup, when the pre-state admits
it (`schedContextFinaliseAdmitted`).  seL4's `schedContext_unbindNtfn` and
`schedContext_completeYieldTo` have nothing to do here: this model's context is
bound to no notification and records no yield. -/
def finaliseSchedContext (x : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  if schedContextFinaliseAdmitted st x then
    finaliseSchedContextCleanup (finaliseSchedContextUnstack
      (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x) x) x
  else st

/-- **The thread finalisation, with its cleanup read as what it is.** -/
theorem finaliseThread_eq (x : SeLe4n.ObjId) (st : SystemState) :
    finaliseThread x st =
      if threadFinaliseAdmitted st x then
        finaliseThreadUnbindSchedContext
          (finaliseThreadReleaseCores
            (finaliseThreadSuspend
              (finaliseThreadCancel
                (finaliseThreadUnbindNotification st ⟨x.val⟩) ⟨x.val⟩) ⟨x.val⟩) ⟨x.val⟩) ⟨x.val⟩
      else st := by
  unfold finaliseThread; rw [finaliseThreadCleanup_eq]

/-- **The scheduling-context finalisation, with its cleanup read as what it
is.** -/
theorem finaliseSchedContext_eq (x : SeLe4n.ObjId) (st : SystemState) :
    finaliseSchedContext x st =
      if schedContextFinaliseAdmitted st x then
        finaliseSchedContextUnstack
          (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x) x
      else st := by
  unfold finaliseSchedContext; rw [finaliseSchedContextCleanup_eq]

/-- A thread whose binding codes name a context and no owner is `.bound` to it. -/
theorem schedContextBinding_of_codes {tcb : TCB} (hS : tcb.scBindingScCode ≠ 0)
    (hO : tcb.scBindingOwnerCode = 0) :
    tcb.schedContextBinding = .bound ⟨tcb.scBindingScCode - 1⟩ := by
  unfold TCB.schedContextBinding SchedContextBinding.ofCodes
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hS
  rw [hs, hO]; simp

/-- **The reservation arm on such a thread is the per-core unbind** at its
home core. -/
theorem cancelDonationArmOnCore_of_codes (st : SystemState) (tid : SeLe4n.ThreadId) {tcb : TCB}
    (hS : tcb.scBindingScCode ≠ 0) (hO : tcb.scBindingOwnerCode = 0) :
    cancelDonationArmOnCore st tid tcb =
      cancelBoundDonationOnCore st tid tcb (determineTargetCore st tid) :=
  cancelDonationArmOnCore_of_bound st tid tcb _ (schedContextBinding_of_codes hS hO)

-- ============================================================================
-- §4b  A reply's finalisation
-- ============================================================================

/-- **Whether a reply's stack link is the head of some context's stack.** -/
@[inline] def replyStackLinkIsHead : Option ReplyStackLink → Bool
  | some (.head _) => true
  | _ => false

/-- **Whether the pop of a head reply commits, read on the pre-state** (seL4
MCS's `reply_pop` hand-back, decided before any write).  A reply that heads no
stack answers `true`: it has nothing to hand back.  A reply heading the stack of
the context `s` answers `true` when the context names it back as its head, is
bound to a thread `h` that holds it on loan from the reply's caller `c`
(`.donated s c`, read off the binding codes), and the donation return of `s`
from `h` to `c` commits (`donatedReturnCommits`, which decides every refusal of
`returnDonatedSchedContextResolved` on the state it runs on).  Each read is
`O(1)`: the context, its bound thread, that thread's two binding words, and the
return's own checks (the reply stack's head and the frame below it). -/
@[inline] def replyHeadPopCommits (st : SystemState) (x : SeLe4n.ObjId) (r : Reply)
    (c : SeLe4n.ThreadId) : Bool :=
  match r.next with
  | some (.head s) =>
    match st.getSchedContext? s with
    | some sc =>
      match sc.boundThreadCode with
      | 0 => false
      | k + 1 =>
        (match sc.scReply with
         | some rid => rid.val == x.val
         | none => false) &&
        (match st.getTcb? ⟨k⟩ with
         | some ht => ht.scBindingScCode == s.val + 1 && ht.scBindingOwnerCode == c.val + 1
         | none => false) &&
        donatedReturnCommits st ⟨k⟩ s c
    | none => false
  | _ => true

/-- **Whether a final delete may finalise the reply at `x`, whose caller `c`
(its TCB `t`) waits on it**, read on the pre-state before any write.  A reply
heading a context's stack is popped only when the pop commits
(`replyHeadPopCommits`: the context goes back to the caller, seL4's
`reply_remove` head branch, `reply_pop`); a reply heading none is spliced out
(the non-head branch).  The caller is no reserved or idle thread and is on no
run queue — a core's FP/SIMD or resident hold on it stays, as seL4 keeps a
lazily saved context across `setThreadState Inactive` — is blocked on this
reply, is linked into no endpoint queue, and waits with no timeout budget.  Each
check reads the reply, the caller and, for a head, the context and its holder,
in `O(1)`.  No check walks the store for a loan of the caller's: a thread lending
a context finds its own reply heading that context's stack (seL4 MCS pushes the
lender's reply as the head in the step that lends,
`lentContextHeadsLenderFrame`), so a caller whose reply heads no stack lends to
no one (`replyCaller_lendsNone`), and one whose reply heads `s` lends only `s`,
to the thread the pop takes it from (`donationOwnerUnique`). -/
@[inline] def replyCallerFinalisable (st : SystemState) (x : SeLe4n.ObjId) (r : Reply)
    (c : SeLe4n.ThreadId) (t : TCB) : Bool :=
  replyHeadPopCommits st x r c && !c.isReserved && !isIdleThreadId c &&
    t.runCoreCode == 0 && decide (4 ≤ t.ipcStateCode) &&
    t.replyObjectCode == x.val + 1 && t.queueNextCode == 0 && t.queuePrevCode == 0 &&
    t.timeoutBudget.isNone

/-- **A finalised reply's caller cancel** (seL4's `reply_remove`): the pop of a
head reply — the context handed back to the caller, its replenishments moved to
the caller's core, and the thread it is taken from off its core
(`cancelIpcBlockingReclaimed`, the suspend's reclaim) — or the splice of a
reply heading no stack, whose cancel has nothing to give back
(`Lifecycle.Suspend.cancelIpcBlocking`'s reply arm, which the reclaim reduces to
there, `cancelIpcBlockingReclaimed_of_no_donation`).  The branch reads the
reply's own link, which the admission has already read. -/
@[inline] def finaliseReplyCancel (st : SystemState) (r : Reply) (c : SeLe4n.ThreadId)
    (t : TCB) : SystemState :=
  if replyStackLinkIsHead r.next then cancelIpcBlockingReclaimed c t st
  else Lifecycle.Suspend.cancelIpcBlocking st c t

/-- **A thread's reply stash, cleared.** -/
@[inline] def TCB.stashCleared (t : TCB) : TCB := { t with pendingReceiveReplyCode := 0 }

/-- **seL4's `finaliseCap` on the final capability to a reply a receiver has
stashed** (`reply_unlink` on the `BlockedOnReceive` thread the reply's
`replyTCB` names): the receiver the Reply records as its stasher
(`Reply.stasherCode`, one field read) has its stash cleared in its slot
(`updateTcb`, compiled as the in-place rewrite), and it keeps waiting on its
endpoint, now for a call it receives with no reply.  The record is cleared
lazily, so the named receiver's own stash is checked before the write; a reply
whose record names no thread that still stashes it is left as it is. -/
def finaliseReplyUnstash (st : SystemState) (x : SeLe4n.ObjId) (r : Reply) : SystemState :=
  match r.stasherCode with
  | 0 => st
  | k + 1 =>
    match st.getTcb? ⟨k⟩ with
    | some t =>
      if t.pendingReceiveReplyCode == x.val + 1 then st.updateTcb ⟨k⟩ TCB.stashCleared
      else st
    | none => st

/-- **The boost a finalised reply's caller lent its server, reverted**: the
priority-inheritance walk from the server the caller was blocked on (`server?`,
read on the pre-state), as the suspend's revert runs it.  The walk's state does
not depend on the core it is run from
(`PriorityInheritance.propagatePipChainCrossCore_state_core_independent`). -/
@[inline] def finaliseReplyRevert (st : SystemState) (server? : Option SeLe4n.ThreadId) : SystemState :=
  match server? with
  | some s => (PriorityInheritance.propagatePipChainCrossCore st s Concurrency.bootCoreId).1
  | none => st

/-- **seL4's `finaliseCap` on the final capability to a reply whose caller
still waits on it** (`reply_remove`, then `reply_unlink`): the caller's blocked
call is cancelled (`finaliseReplyCancel`: a head reply popped, its context
handed back to the caller; any other reply spliced out of its stack; then the
caller restored with the cancellation frame, the reply's caller link and the
caller's reply link cleared, the caller off its server's reply-waiter queue), the boost it lent its server reverted
(`finaliseReplyRevert`), and the caller made `.Inactive`
(`finaliseThreadSuspend`, seL4's `setThreadState Inactive`).  Only when the
pre-state admits it (`replyCallerFinalisable`), checks before writes; a reply
with no caller but stashed by a receiver is unlinked from it
(`finaliseReplyUnstash`), and the retire then takes it if it is quiescent. -/
def finaliseReply (x : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  match st.getObject? x with
  | some (.reply r) =>
    if r.callerCode == 0 then finaliseReplyUnstash st x r
    else
      let c : SeLe4n.ThreadId := ⟨r.callerCode - 1⟩
      match st.getTcb? c with
      | some t =>
        if replyCallerFinalisable st x r c t then
          finaliseThreadSuspend (finaliseReplyRevert (finaliseReplyCancel st r c t) t.blockingServer?) c
        else st
      | none => st
  | _ => st

/-- **The splice of a reply heading no stack, as compiled**: the same reads and
the same stores as `spliceReplyFrameOutOrSelf`, with no `Except` cell on the
arms that write nothing (a reply linked to no frame above, the busy reply's
case). -/
@[inline] def spliceReplyFrameOutOrSelfInPlace (st : SystemState) (rid : SeLe4n.ReplyId) :
    SystemState :=
  match st.getReply? rid with
  | none => st
  | some r =>
    match r.next with
    | some (.frame above) =>
      match st.getReply? above with
      | none => st
      | some a =>
        if a.prev != some rid then st
        else
          match spliceReplyFrameStores st rid above r a with
          | .ok st' => st'
          | .error _ => st
    | _ => st

theorem spliceReplyFrameOutOrSelfInPlace_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    spliceReplyFrameOutOrSelfInPlace st rid = spliceReplyFrameOutOrSelf st rid := by
  unfold spliceReplyFrameOutOrSelfInPlace spliceReplyFrameOutOrSelf spliceReplyFrameOut
  cases st.getReply? rid with
  | none => rfl
  | some r =>
    dsimp only
    cases r.next with
    | none => rfl
    | some l =>
      cases l with
      | head _ => rfl
      | frame above =>
        dsimp only
        cases st.getReply? above with
        | none => rfl
        | some a =>
          dsimp only
          by_cases hP : (a.prev != some rid) = true
          · simp only [hP, ↓reduceIte]
          · simp only [hP, Bool.false_eq_true, ↓reduceIte]
            cases spliceReplyFrameStores st rid above r a <;> rfl

/-- **A caller's reply link consumed, as compiled**: the reply's consumed record
and the caller's cleared link, each written in its slot (`storeReplyWith`,
`storeTcbWith`) — the stores `consumeCallerReplyLink` makes.  `storeTcbWith`
writes nothing to a slot holding no thread, as the link form's `getTcb?` arm
does. -/
@[inline] def consumeCallerReplyInPlace (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : SystemState :=
  (st.storeReplyWith rid.toObjId Reply.consumed).storeTcbWith c.toObjId
    fun tcb => { tcb with replyObjectCode := 0 }

theorem consumeCallerReplyInPlace_eq (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) :
    consumeCallerReplyInPlace st c rid = st.consumeCallerReplyLink c rid := by
  have hL := SystemState.consumeCallerReply_eq_link st c rid
  suffices hS : SystemState.consumeCallerReply c rid st = .ok ((), consumeCallerReplyInPlace st c rid) by
    rw [hS] at hL
    exact (Prod.mk.inj (Except.ok.inj hL)).2
  have hR : SystemState.consumeReply rid st = .ok ((), st.storeReplyWith rid.toObjId Reply.consumed) := by
    unfold SystemState.consumeReply
    cases hg : st.getReply? rid with
    | some r => exact SystemState.storeObject_reply_eq_storeReplyWith ((SystemState.getReply?_eq_some_iff _ _ _).mp hg) _
    | none =>
      show Except.ok ((), st) = _
      unfold SystemState.storeReplyWith
      cases ho : st.objects[rid.toObjId]? with
      | none => rfl
      | some o =>
        cases o with
        | reply r =>
          rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr ho] at hg; cases hg
        | _ => rfl
  unfold SystemState.consumeCallerReply consumeCallerReplyInPlace
  rw [hR]
  dsimp only
  generalize st.storeReplyWith rid.toObjId Reply.consumed = st1
  cases ht : st1.objects[c.toObjId]? with
  | none =>
    have : st1.getTcb? c = none := by unfold SystemState.getTcb?; rw [ht]
    rw [this]
    unfold SystemState.storeTcbWith; rw [ht]
  | some o =>
    cases o with
    | tcb t =>
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr ht]
      exact SystemState.storeObject_tcb_eq_storeTcbWith ht (fun tcb => { tcb with replyObjectCode := 0 })
    | _ =>
      have : st1.getTcb? c = none := by unfold SystemState.getTcb?; rw [ht]
      rw [this]
      unfold SystemState.storeTcbWith; rw [ht]

/-- **A reply-blocked caller's cancel with nothing to give back, as compiled**:
the splice, the restore, the consume and the reply-waiter unlink of
`cancelIpcBlocking`'s reply arm, read from the caller's reply code and its
server's code, each object written in its slot. -/
@[inline] def cancelReplyArmInPlace (st : SystemState) (c : SeLe4n.ThreadId) (code : Nat)
    (serverCode : Nat) : SystemState :=
  let st1 := match code with
    | 0 => st
    | k + 1 => spliceReplyFrameOutOrSelfInPlace st ⟨k⟩
  let st2 := Lifecycle.Suspend.restoreToReadyCancelled st1 c
  let st3 := match code with
    | 0 => st2
    | k + 1 => consumeCallerReplyInPlace st2 c ⟨k⟩
  st3.unlinkReplyWaiterOpt c (SeLe4n.ThreadId.ofOptCode serverCode)

/-- **The server a caller blocked on a reply waits for, as a code**: `0` for none,
`s + 1` for the server `s` (`TCB.blockingServer?`). -/
@[inline] def replyCallerServerCode (t : TCB) : Nat :=
  match t.blockingServer? with
  | some s => s.val + 1
  | none => 0

theorem ofOptCode_replyCallerServerCode (t : TCB) :
    SeLe4n.ThreadId.ofOptCode (replyCallerServerCode t) = t.blockingServer? := by
  unfold replyCallerServerCode
  cases t.blockingServer? <;> rfl

theorem cancelReplyArmInPlace_eq (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB) :
    cancelReplyArmInPlace st c t.replyObjectCode (replyCallerServerCode t) =
      SystemState.unlinkReplyWaiterOpt
        (Lifecycle.Suspend.consumeReplyLink
          (Lifecycle.Suspend.restoreToReadyCancelled (spliceThreadReplyFrameOut st t) c) c t)
        c t.blockingServer? := by
  unfold cancelReplyArmInPlace spliceThreadReplyFrameOut Lifecycle.Suspend.consumeReplyLink
  rw [ofOptCode_replyCallerServerCode]
  unfold TCB.replyObject
  cases t.replyObjectCode with
  | zero => rfl
  | succ k =>
    simp only [SeLe4n.ReplyId.ofOptCode, spliceReplyFrameOutOrSelfInPlace_eq,
      consumeCallerReplyInPlace_eq]

/-- **The cancel of a reply heading no stack, as compiled**: on a caller blocked on
a reply with no donation to return, `cancelReplyArmInPlace`; otherwise the
cancel itself. -/
@[inline] def finaliseReplyCancelSplice (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (serverCode : Nat) : SystemState :=
  match t.ipcState with
  | .blockedOnReply _ _ =>
    match Lifecycle.Suspend.cancelledCallerDonation? st c t with
    | none => cancelReplyArmInPlace st c t.replyObjectCode serverCode
    | some _ => Lifecycle.Suspend.cancelIpcBlocking st c t
  | _ => Lifecycle.Suspend.cancelIpcBlocking st c t

theorem finaliseReplyCancelSplice_eq (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB) :
    finaliseReplyCancelSplice st c t (replyCallerServerCode t) =
      Lifecycle.Suspend.cancelIpcBlocking st c t := by
  unfold finaliseReplyCancelSplice
  split
  · next ep rt hB =>
    split
    · next hD =>
      rw [cancelReplyArmInPlace_eq]
      have hR : Lifecycle.Suspend.returnDonationToCancelledCaller st c t = st := by
        unfold Lifecycle.Suspend.returnDonationToCancelledCaller; rw [hD]
      unfold Lifecycle.Suspend.cancelIpcBlocking
      rw [hB]
      simp only [hR]
    · rfl
  · rfl

/-- **A finalised reply's caller cancelled, reverted and suspended, as
compiled**: a head reply as `finaliseReply` runs it; any other through
`finaliseReplyCancelSplice`, with the caller's reply and server read as codes
before the first write, so the caller's thread record is held by its slot alone
when the restore and the consume write it, and is rewritten there. -/
@[inline] def finaliseReplyCaller (st : SystemState) (r : Reply) (c : SeLe4n.ThreadId)
    (t : TCB) : SystemState :=
  if replyStackLinkIsHead r.next then
    finaliseThreadSuspend (finaliseReplyRevert (cancelIpcBlockingReclaimed c t st)
      t.blockingServer?) c
  else
    let serverCode := replyCallerServerCode t
    finaliseThreadSuspend (finaliseReplyRevert (finaliseReplyCancelSplice st c t serverCode)
      (SeLe4n.ThreadId.ofOptCode serverCode)) c

theorem finaliseReplyCaller_eq (st : SystemState) (r : Reply) (c : SeLe4n.ThreadId) (t : TCB) :
    finaliseReplyCaller st r c t =
      finaliseThreadSuspend (finaliseReplyRevert (finaliseReplyCancel st r c t)
        t.blockingServer?) c := by
  unfold finaliseReplyCaller finaliseReplyCancel
  split
  · rfl
  · simp only [finaliseReplyCancelSplice_eq, ofOptCode_replyCallerServerCode]

/-- **`finaliseReply` as compiled** (`finaliseReplyCaller`). -/
def finaliseReplyImpl (x : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  match st.getObject? x with
  | some (.reply r) =>
    if r.callerCode == 0 then finaliseReplyUnstash st x r
    else
      let c : SeLe4n.ThreadId := ⟨r.callerCode - 1⟩
      match st.getTcb? c with
      | some t =>
        if replyCallerFinalisable st x r c t then finaliseReplyCaller st r c t
        else st
      | none => st
  | _ => st

@[csimp] theorem finaliseReply_eq_impl : @finaliseReply = @finaliseReplyImpl := by
  funext x st
  unfold finaliseReply finaliseReplyImpl
  simp only [finaliseReplyCaller_eq]

-- ============================================================================
-- §5  The finalisation a final delete runs
-- ============================================================================

/-- **seL4's `finaliseCap` on the final capability to an endpoint, a
notification, a thread, a scheduling context or a reply** (`target`, a word as
`slotRetireTarget` reads it: `x + 1`, or `0` for none): an endpoint's waiters
are cancelled (`cancelAllIpc`); a notification is unbound from its thread and
its waiters are cancelled (`unbindMaybeNotification`, `cancelAllSignals`); a
thread is suspended and unbound (`finaliseThread`); a scheduling context is
unbound and its reply stack let go (`finaliseSchedContext`); a reply's waiting
caller is cancelled and made inactive (`finaliseReply`).  Nothing when no object is
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
      | some .tcb => finaliseThread x st
      | some .schedContext => finaliseSchedContext x st
      | some .reply => finaliseReply x st
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
