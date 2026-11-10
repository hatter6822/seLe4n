/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.IPC.DualQueue.PopInPlace
import SeLe4n.Kernel.IPC.DualQueue.RemoveInPlace
import SeLe4n.Kernel.IPC.Operations.NotificationBind
import SeLe4n.Kernel.IPC.Operations.DonationPopInPlace
import SeLe4n.Kernel.IPC.Operations.UnheldContextPopInPlace

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

/-- **What a cancelled endpoint waiter becomes**: `.ready`, holding no message,
no stashed reply (the receive completion `storeTcbReceiveComplete` writes, with
no message) and no fault record (WS-ZA ZA6.22: seL4's `cancelIPC` resets
`tcbFault`, as `TCB.restoredToReady` does), with the cancellation frame staged
in its registers. -/
@[inline] def cancelledEndpointWaiterTcb (t : TCB) : TCB :=
  (TCB.setIpcState
      (TCB.setPendingFault { t with
          pendingMessage := none
          pendingReceiveReplyCode := 0 } none) .ready
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

/-- The head **code** of one of an endpoint's queues (`endpointWaitQueue`'s
head, `0` for none). -/
@[inline] def endpointWaitHeadCode (ep : Endpoint) (isReceiveQ : Bool) : Nat :=
  if isReceiveQ then ep.recvHeadCode else ep.sendHeadCode

theorem ofOptCode_endpointWaitHeadCode (ep : Endpoint) (isReceiveQ : Bool) :
    SeLe4n.ThreadId.ofOptCode (endpointWaitHeadCode ep isReceiveQ) =
      (endpointWaitQueue ep isReceiveQ).head := by
  unfold endpointWaitHeadCode endpointWaitQueue
  cases isReceiveQ <;> rfl

/-- `storeEndpointWaiterCancelled` behind the successor's link **code**
(`storePopHeadCode`), so no `some` cell is built for a waiter with a successor
(`storeEndpointWaiterCancelledCode_eq`).  Out of line, as the spec form is. -/
@[noinline] def storeEndpointWaiterCancelledCode (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (t : SeLe4n.ThreadId) (nextCode : Nat) : SystemState :=
  wakeCancelledWaiter
    ((storePopHeadCode st endpointId isReceiveQ t nextCode).updateTcb t cancelledEndpointWaiterTcb) t

theorem storeEndpointWaiterCancelledCode_eq (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (t : SeLe4n.ThreadId) (nextCode : Nat) :
    storeEndpointWaiterCancelledCode st endpointId isReceiveQ t nextCode =
      storeEndpointWaiterCancelled st endpointId isReceiveQ t
        (SeLe4n.ThreadId.ofOptCode nextCode) := by
  unfold storeEndpointWaiterCancelledCode storeEndpointWaiterCancelled
  rw [storePopHeadCode_eq]

/-- `endpointWaiterCancellable` asked of the waiter's successor **code**
(`sendWakesInPlaceCode`). -/
@[inline] def endpointWaiterCancellableCode (st : SystemState) (endpointId : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) (tcb : TCB) : Bool :=
  cancelledWaiterWakeable st t tcb && tcb.timeoutBudget.isNone &&
    sendWakesInPlaceCode st endpointId t tcb.queueNextCode

theorem endpointWaiterCancellableCode_eq (st : SystemState) (endpointId : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) (tcb : TCB) :
    endpointWaiterCancellableCode st endpointId t tcb =
      endpointWaiterCancellable st endpointId t tcb := by
  unfold endpointWaiterCancellableCode endpointWaiterCancellable
  rw [sendWakesInPlaceCode_eq, TCB.ofOptCode_queueNextCode]

/-- `cancelEndpointQueue` as it is compiled: the queue's head and each waiter's
successor read as codes, so a queue of more than one waiter builds no cell
(`cancelEndpointQueue_eq_impl`). -/
def cancelEndpointQueueImpl (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) :
    Nat → SystemState → SystemState
  | 0, st => st
  | fuel + 1, st =>
    match st.getEndpoint? endpointId with
    | some ep =>
      match endpointWaitHeadCode ep isReceiveQ with
      | 0 => st
      | k + 1 =>
        match st.getTcb? ⟨k⟩ with
        | some tcb =>
          if endpointWaiterCancellableCode st endpointId ⟨k⟩ tcb then
            cancelEndpointQueueImpl endpointId isReceiveQ fuel
              (storeEndpointWaiterCancelledCode st endpointId isReceiveQ ⟨k⟩ tcb.queueNextCode)
          else st
        | none => st
    | none => st

@[csimp] theorem cancelEndpointQueue_eq_impl :
    @cancelEndpointQueue = @cancelEndpointQueueImpl := by
  funext endpointId isReceiveQ fuel
  induction fuel with
  | zero => funext st; rfl
  | succ fuel ih =>
    funext st
    unfold cancelEndpointQueue cancelEndpointQueueImpl
    cases st.getEndpoint? endpointId with
    | none => rfl
    | some ep =>
      dsimp only
      rw [← ofOptCode_endpointWaitHeadCode]
      cases endpointWaitHeadCode ep isReceiveQ with
      | zero => rfl
      | succ k =>
        dsimp only [SeLe4n.ThreadId.ofOptCode]
        cases st.getTcb? ⟨k⟩ with
        | none => rfl
        | some tcb =>
          dsimp only
          rw [endpointWaiterCancellableCode_eq, storeEndpointWaiterCancelledCode_eq,
            TCB.ofOptCode_queueNextCode, ih]

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

-- ============================================================================
-- §3b  What the reply finalisation and the thread finalisation share: the cancel
-- of a caller blocked on a reply
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

/-- **Whether a reply heading a context's stack is named back by that context**
(`sc.scReply` is the reply at `x`): the frame the head cut finds
(`replyFrameHeadContext?`).  A reply heading no stack answers `true`.  One
read: the context. -/
@[inline] def replyHeadNamedBack (st : SystemState) (x : SeLe4n.ObjId) (r : Reply) : Bool :=
  match r.next with
  | some (.head s) =>
    match st.getSchedContext? s with
    | some sc => sc.scReply == some ⟨x.val⟩
    | none => false
  | _ => true

/-- **Whether a thread's own final delete may cut the reply at `x` its caller
`c` (its TCB `t`) waits on**, read on the pre-state: the checks
`replyCallerFinalisable` makes of the caller, with the head pop's commit
replaced by the head being named back (`replyHeadNamedBack`), since the
thread-side cut hands no context back (seL4-MCS's `reply_remove_tcb`). -/
@[inline] def replyCallerCuttable (st : SystemState) (x : SeLe4n.ObjId) (r : Reply)
    (c : SeLe4n.ThreadId) (t : TCB) : Bool :=
  replyHeadNamedBack st x r && !c.isReserved && !isIdleThreadId c &&
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

/-- **The boost a finalised reply's caller lent its server, reverted**: the
priority-inheritance walk from the server the caller was blocked on (`server?`,
read on the pre-state), as the suspend's revert runs it.  The walk's state does
not depend on the core it is run from
(`PriorityInheritance.propagatePipChainCrossCore_state_core_independent`). -/
@[inline] def finaliseReplyRevert (st : SystemState) (server? : Option SeLe4n.ThreadId) : SystemState :=
  match server? with
  | some s => (PriorityInheritance.propagatePipChainCrossCore st s Concurrency.bootCoreId).1
  | none => st

/-- **Whether the cancel of the thread `c` (its TCB `t`), blocked on a reply, is
admitted**, read on the state it runs on before any write: the reply `t` waits on
(its reply code) is stored, names `c` back as its caller, and admits its caller's
cut (`replyCallerCuttable`: a head reply is named back by its context, the caller
is on no run queue, no endpoint queue, and waits with no timeout budget).  Each
read is `O(1)`. -/
@[inline] def replyCallerCancelAdmitted (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB) :
    Bool :=
  match st.getObject? ⟨t.replyObjectCode - 1⟩ with
  | some (.reply r) =>
    r.callerCode == c.val + 1 && replyCallerCuttable st ⟨t.replyObjectCode - 1⟩ r c t
  | _ => false

/-- **The removal of the reply the thread `c` waits on, after its head is cut**:
on the state the cut left, `c`'s reply (read off its thread record there) is
removed as the reply's own finalisation removes a reply heading no stack
(`finaliseReplyCancel`'s splice arm, admitted by `replyCallerFinalisable`), and the
boost `c` lent its server reverted (`finaliseReplyRevert`).  A state the cut
leaves where the check refuses is left alone. -/
def finaliseCutReplyCaller (st : SystemState) (c : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? c with
  | some t =>
    match st.getObject? ⟨t.replyObjectCode - 1⟩ with
    | some (.reply r) =>
      if r.callerCode == c.val + 1 && replyCallerFinalisable st ⟨t.replyObjectCode - 1⟩ r c t then
        finaliseReplyRevert (finaliseReplyCancel st r c t) t.blockingServer?
      else st
    | _ => st
  | none => st

/-- **The cancel of the thread `c` (its TCB `t`), blocked on a reply** (WS-ZA
ZA6.34): seL4-MCS's `reply_remove_tcb`, as the suspend runs it
(`Lifecycle.Suspend.cancelIpcKeepingContexts`).  A reply heading a context's
stack is cut off it, and the context **stays with the thread it is bound to**
(`Lifecycle.Suspend.cutCancelledCallerHead`, the suspend's own cut:
`sc->scReply = NULL`; a holder
holding it on loan from `c` keeps it as its own); then the reply, heading
nothing, is removed (`finaliseCutReplyCaller`: spliced out of its stack, `c`
restored with the cancellation frame, the reply's caller link and `c`'s reply link
cleared, `c` off its server's reply-waiter queue), and the boost `c` lent its
server reverted, when `replyCallerCancelAdmitted` admits it; otherwise nothing
is written.  It runs on a thread whose own final delete finalises it
(`finaliseThreadCancel`).  The reply object's own finalisation is seL4's
`reply_remove`, whose head branch is `reply_pop`, and keeps the give-back
(`finaliseReplyCancel`). -/
def finaliseReplyCallerCancel (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB) :
    SystemState :=
  match st.getObject? ⟨t.replyObjectCode - 1⟩ with
  | some (.reply r) =>
    if r.callerCode == c.val + 1 && replyCallerCuttable st ⟨t.replyObjectCode - 1⟩ r c t then
      finaliseCutReplyCaller (Lifecycle.Suspend.cutCancelledCallerHead st t) c
    else st
  | _ => st

/-- **The cancel of a reply heading no stack, as compiled**: on a caller blocked on
a reply with no donation to return, `cancelReplyArmInPlace`; otherwise the
cancel itself. -/
@[inline] def finaliseReplyCancelSplice (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (serverCode : Nat) : SystemState :=
  match t.ipcState with
  | .blockedOnReply _ _ =>
    match Lifecycle.Suspend.cancelledCallerDonation? st c t with
    | none => Lifecycle.Suspend.cancelReplyArmInPlace st c t.replyObjectCode serverCode
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
      rw [Lifecycle.Suspend.cancelReplyArmInPlace_eq]
      have hR : Lifecycle.Suspend.returnDonationToCancelledCaller st c t = st := by
        unfold Lifecycle.Suspend.returnDonationToCancelledCaller; rw [hD]
      unfold Lifecycle.Suspend.cancelIpcBlocking
      rw [hB]
      simp only [hR]
    · rfl
  · rfl

/-- **The removal after the head cut, as compiled** (`finaliseCutReplyCaller`):
a reply heading no stack is spliced in place (`finaliseReplyCancelSplice`), and
the server read as a code; the head branch, which the cut leaves unreachable on
a well-formed table, is the compiled pop (`cancelHeadReplyCaller`), so the two
forms agree on every state. -/
def finaliseCutReplyCallerImpl (st : SystemState) (c : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? c with
  | some t =>
    match st.getObject? ⟨t.replyObjectCode - 1⟩ with
    | some (.reply r) =>
      if r.callerCode == c.val + 1 && replyCallerFinalisable st ⟨t.replyObjectCode - 1⟩ r c t then
        let serverCode := replyCallerServerCode t
        finaliseReplyRevert
          (if replyStackLinkIsHead r.next then cancelHeadReplyCaller st c t
           else finaliseReplyCancelSplice st c t serverCode)
          (SeLe4n.ThreadId.ofOptCode serverCode)
      else st
    | _ => st
  | none => st

@[csimp] theorem finaliseCutReplyCaller_eq_impl :
    @finaliseCutReplyCaller = @finaliseCutReplyCallerImpl := by
  funext st c
  unfold finaliseCutReplyCaller finaliseCutReplyCallerImpl finaliseReplyCancel
  split
  · split
    · split
      · split <;> simp only [cancelHeadReplyCaller_eq, finaliseReplyCancelSplice_eq,
          ofOptCode_replyCallerServerCode]
      · rfl
    · rfl
  · rfl

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
stash; or blocked on a reply, which the reply cancel admits
(`replyCallerCancelAdmitted`). -/
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
  | _ => replyCallerCancelAdmitted st tid t

/-- **Whether the thread `tid` (its TCB `t`) may be unbound from its
notification**: it is bound to none, or the notification its code names is
stored and bound back to it, and the unbind writes in place
(`unbindNotificationInPlace`).  The thread finalisation's admission reads it on
the pre-state, where the unbind runs first (`finaliseThreadUnbindNotification`),
so the unbind itself reads nothing more. -/
@[inline] def notificationUnbindAdmitted (st : SystemState) (tid : SeLe4n.ThreadId) (t : TCB) :
    Bool :=
  t.boundNotificationCode == 0 ||
    ((match st.getNotification? ⟨t.boundNotificationCode - 1⟩ with
      | some n => n.boundTCBCode == tid.val + 1
      | none => false) && unbindNotificationInPlace st tid)

/-- **Whether a final delete may finalise the thread at `x`**, read on the
pre-state before any write.  The thread is stored under its own id and is no
reserved or idle thread; its IPC state is one the cancel ends
(`threadIpcCancelAdmitted`): ready (suspended, queued, current on a core — the
executing core's own thread deleting its last capability included — or held by
a core as its FP/SIMD owner or its resident), blocked on a notification, or
blocked receiving, sending or calling on an endpoint, wherever it waits in that
queue, or blocked on a reply, whose cancel removes the reply as the reply's own
thread's own cancel does (seL4's `reply_remove_tcb`: a head reply cut off its
context, which stays with the thread holding it); a thread not blocked on a reply is linked
into no reply-waiter queue and holds no reply link; it holds no timeout budget;
the callers waiting on it for a reply are no reason to refuse it: each is left
waiting on its reply with no server (`finaliseThreadOrphanWaiters`), whatever
stack its reply sits on;
its space slots may hold capabilities, which the zombie loop deletes after
the finalisation, by the finalising delete (`zombiePasses`); a bound
notification and a bound scheduling context are bound back to it, and a thread
naming no context names no lender either (its binding codes read as the binding
they encode).  A context that records it as a reservation's origin is no reason to refuse it: that origin
counts only while the thread's own back-link names the context
(`donationOriginRecipient?`), so the thread's record leaving with it ends the
origin.  The admission is carried across the finalisation's own steps
(`finaliseThread_quiesces`): the notification unbind, run first on this state,
reads nothing more (`notificationUnbindAdmitted`); the later steps keep their
own guards, which the reply finalisation's steps share and the compiled context
unbind rests on, and none of them refuses after an earlier step has written: the
walk over the waiters reads each head off the reply-waiter queues, whose
consistency names it a waiter of the thread (`replyWaitersConsistent`). -/
@[inline] def threadFinaliseAdmitted (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObject? x with
  | some (.tcb t) =>
    let tid : SeLe4n.ThreadId := ⟨x.val⟩
    t.tid.val == x.val && !tid.isReserved && !isIdleThreadId tid &&
    (decide (4 ≤ t.ipcStateCode) ||
      t.replyWaiterNextCode == 0 && t.replyWaiterPrevCode == 0 && t.replyObjectCode == 0) &&
    t.timeoutBudget.isNone &&
    threadIpcCancelAdmitted st tid t &&
    notificationUnbindAdmitted st tid t &&
    (t.scBindingScCode == 0 && t.scBindingOwnerCode == 0 ||
      t.scBindingScCode != 0 && match st.getSchedContext? ⟨t.scBindingScCode - 1⟩ with
      | some sc => sc.boundThreadCode == x.val + 1
      | none => false)
  | _ => false

/-- **Cancel the blocked IPC of a thread being finalised** (seL4's `suspend` →
`cancelIPC`): a thread blocked on a notification leaves its queue, wherever it
waits there, and is made `.ready` with the cancellation frame, as
`cancelIpcBlocking`'s notification arm makes it (`cancelSignal`); a thread
blocked receiving, sending or calling on an endpoint leaves that endpoint's
queue, wherever it waits there, and is made `.ready` with the cancellation frame
(`cancelEndpointBlocked`: `blockedCancelIPC`).  Neither is woken — the thread is
being destroyed.  A thread blocked on a reply has the reply removed and its
boost reverted (`finaliseReplyCallerCancel`, the reply finalisation's cancel).
Any other state is left alone. -/
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
    | .blockedOnReply _ _ => finaliseReplyCallerCancel st tid t
    | _ => st
  | none => st

/-- Whether a notification's queue is headed by `t`, read off its head code. -/
theorem Notification.waitHeadCode_beq (ntfn : Notification) (t : SeLe4n.ThreadId) :
    (ntfn.waitHeadCode == t.val + 1) = (ntfn.waitHead == some t) := by
  unfold Notification.waitHead
  cases hw : ntfn.waitHeadCode with
  | zero => simp [SeLe4n.ThreadId.ofOptCode]
  | succ w =>
    simp only [SeLe4n.ThreadId.ofOptCode]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    constructor
    · intro h
      have hv : w = t.val := by omega
      rw [hv]
    · intro h
      rw [← Option.some.inj h]

/-- **`finaliseThreadCancel` as compiled**: the notification cancel is its
in-place writes (`storeNotificationBlockedCancelled`,
`cancelIpcBlocking_notification_inPlace`); the endpoint cancel is already
written in place, and the reply cancel is compiled in place through the head
cut's and the removal's compiled forms (`cutHeadFrameKeepingContext_eq_impl`,
`finaliseCutReplyCaller_eq_impl`). -/
def finaliseThreadCancelImpl (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some t =>
    match t.ipcState with
    | .blockedOnNotification n =>
      match st.getNotification? n with
      | some ntfn =>
        if notificationWaiterCancellable st n tid t then
          storeNotificationBlockedCancelled st n tid (ntfn.waitHeadCode == tid.val + 1) t.ntfnPrev
            t.ntfnNext
        else st
      | none => st
    | .blockedOnReceive e => cancelEndpointBlocked st e true tid t
    | .blockedOnSend e => cancelEndpointBlocked st e false tid t
    | .blockedOnCall e => cancelEndpointBlocked st e false tid t
    | .blockedOnReply _ _ => finaliseReplyCallerCancel st tid t
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
        · rw [Notification.waitHeadCode_beq]; exact cancelIpcBlocking_notification_inPlace hN hT hB
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

/-- **Leave a caller `w` waiting on its reply with no server** (seL4-MCS's
`finaliseCap` on a thread: a deleted server's callers stay `BlockedOnReply`,
each reply's `replyTCB` naming its caller, and nothing records the server): the
caller's server is forgotten (`TCB.serverForgotten`) and it leaves the server
`x`'s reply-waiter queue (`unlinkReplyWaiter`).  Its reply, its reply link and
every other field are kept, so a reply cap holder can still answer it
(`doReplyTransfer`) and the delete of its reply ends it (`reply_remove`).  Both
writes are in place. -/
@[inline] def orphanReplyWaiter (st : SystemState) (w x : SeLe4n.ThreadId) : SystemState :=
  (st.mapTcbInPlace w TCB.serverForgotten).unlinkReplyWaiter w x

/-- **Leave every caller waiting on the server `x` with no server**, head first,
at most `fuel` of them: each, another thread than `x` and reply-blocked on it,
is orphaned (`orphanReplyWaiter`), which takes it off `x`'s queue, so the walk
follows `x`'s own head.  A head the guard refuses ends the walk; on a state whose
reply-waiter queues are consistent (`replyWaitersConsistent`) the head of `x`'s
queue is always a thread reply-blocked on `x`, so none is refused there
(`orphanReplyWaiters_endsAll`). -/
def orphanReplyWaiters (x : SeLe4n.ThreadId) : Nat → SystemState → SystemState
  | 0, st => st
  | fuel + 1, st =>
    match st.getTcb? x with
    | some tx =>
      match tx.replyWaitersHeadCode with
      | 0 => st
      | k + 1 =>
        match st.getTcb? ⟨k⟩ with
        | some t =>
          if k != x.val && replyCallerServerCode t == x.val + 1 then
            orphanReplyWaiters x fuel (orphanReplyWaiter st ⟨k⟩ x)
          else st
        | none => st
    | none => st

/-- **Leave every caller waiting on a finalised thread `x` with no server**
(`orphanReplyWaiters`, with the fuel `x`'s own count). -/
@[inline] def finaliseThreadOrphanWaiters (st : SystemState) (x : SeLe4n.ThreadId) :
    SystemState :=
  match st.getTcb? x with
  | some tx => orphanReplyWaiters x tx.replyWaitersCount st
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
`unbindNotification`), each side rewritten where it stands
(`storeUnbindNotification`).  It reads no guard of its own: it runs first, on
the state the finalisation's admission reads, and the admission reads the
notification bound back to the thread and the unbind in place
(`notificationUnbindAdmitted`). -/
def finaliseThreadUnbindNotification (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  let c := boundNotificationCodeOf st tid
  if c == 0 then st else storeUnbindNotification st tid ⟨c - 1⟩

/-- **Unbind a thread being finalised from the scheduling context it holds**
(seL4-MCS's `unbindFromSC`, `schedContext_unbindTCB` on `tcb->tcbSchedContext`):
the in-place unbind of the reservation arm (`cancelBoundDonationOnCore`), with
the thread's binding read as the context's own whether it holds it as its own
or on loan (`{ t with scBindingOwnerCode := 0 }`), at a thread on no core whose
context is bound back to it, and before the destroy cleanup, so the cleanup
finds the thread unbound.  A context on loan goes back to no one: seL4 unbinds
whichever thread runs on it, and the lender, left waiting on its reply with no
server (`finaliseThreadOrphanWaiters`), gets it back when its reply is popped
(`reply_remove`). -/
def finaliseThreadUnbindSchedContext (st : SystemState) (tid : SeLe4n.ThreadId) :
    SystemState :=
  match st.getTcb? tid with
  | some t =>
    if t.scBindingScCode != 0 && t.runCoreCode == 0 && !threadHeldOnSomeCore st tid &&
        (match st.getSchedContext? ⟨t.scBindingScCode - 1⟩ with
          | some sc => sc.boundThreadCode == tid.val + 1
          | none => false) then
      match cancelBoundDonationOnCore st tid { t with scBindingOwnerCode := 0 } with
      | .ok st' => st'
      | .error _ => st
    else st
  | none => st

/-- The compiled `finaliseThreadUnbindSchedContext`: the guard names a context,
which the owner-cleared binding reads as the thread's own, so the reservation
arm is the in-place unbind (`cancelBoundDonationPerform`), and no error branch
holds the pre-state across its writes. -/
@[inline] def finaliseThreadUnbindSchedContextImpl (st : SystemState) (tid : SeLe4n.ThreadId) :
    SystemState :=
  match st.getTcb? tid with
  | some t =>
    let scCode := t.scBindingScCode
    if scCode != 0 && t.runCoreCode == 0 && !threadHeldOnSomeCore st tid &&
        (match st.getSchedContext? ⟨scCode - 1⟩ with
          | some sc => sc.boundThreadCode == tid.val + 1
          | none => false) then
      cancelBoundDonationPerform st tid ⟨scCode - 1⟩
    else st
  | none => st

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
ready waits on no core and is left as it is.  It runs first, on the state the
finalisation's admission reads, and the admission reads the holder bound back to
the context and no core's idle thread (`schedContextFinaliseAdmitted`), so the
deschedule reads only whether the holder is ready. -/
def finaliseSchedContextDeschedule (st : SystemState) (x : SeLe4n.ObjId) : SystemState :=
  match st.getObject? x with
  | some (.schedContext sc) =>
    if sc.boundThreadCode == 0 then st
    else
      let tid : SeLe4n.ThreadId := ⟨sc.boundThreadCode - 1⟩
      match st.getTcb? tid with
      | some t =>
        if t.ipcStateCode == 0 && t.ipcObjectCode == 0 then descheduleAtPlacement st tid
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
              with
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
          cancelBoundDonationPerform st tid ⟨x.val⟩
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
          rw [cancelBoundDonationOnCore_of_bound st _ _ _
            (schedContextBinding_ownerCleared hG)]
        · rfl
  · rfl

@[csimp] theorem finaliseThreadUnbindSchedContext_eq_impl :
    @finaliseThreadUnbindSchedContext = @finaliseThreadUnbindSchedContextImpl := by
  funext st tid
  unfold finaliseThreadUnbindSchedContext finaliseThreadUnbindSchedContextImpl
  cases st.getTcb? tid with
  | none => rfl
  | some t =>
    refine ite_congr rfl (fun hG => ?_) (fun _ => rfl)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hG
    rw [cancelBoundDonationOnCore_of_bound st tid _ _
      (schedContextBinding_ownerCleared (x := ⟨t.scBindingScCode - 1⟩)
        (by show _ = _ - 1 + 1; omega))]

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

/-- `finaliseSchedContextUnstack` as it is compiled: the head reply's upward
link cleared in its slot (`SystemState.storeReplyWith`), so no reply record, no
object cell and no store result is built
(`finaliseSchedContextUnstack_eq_impl`). -/
@[inline] def finaliseSchedContextUnstackImpl (st : SystemState) (x : SeLe4n.ObjId) :
    SystemState :=
  match st.getSchedContext? ⟨x.val⟩ with
  | some sc =>
    match sc.scReply with
    | some rid =>
      match st.getReply? rid with
      | some r =>
        if replyStackLinkHeads x r.next then
          (st.storeReplyWith rid.toObjId fun r => { r with next := none }).updateSchedContext
            ⟨x.val⟩ fun sc => { sc with scReply := none }
        else st
      | none => st
    | none => st
  | none => st

@[csimp] theorem finaliseSchedContextUnstack_eq_impl :
    @finaliseSchedContextUnstack = @finaliseSchedContextUnstackImpl := by
  funext st x
  unfold finaliseSchedContextUnstack finaliseSchedContextUnstackImpl
  cases st.getSchedContext? ⟨x.val⟩ with
  | none => rfl
  | some sc =>
    dsimp only
    cases sc.scReply with
    | none => rfl
    | some rid =>
      dsimp only
      cases hR : st.getReply? rid with
      | none => rfl
      | some r =>
        dsimp only
        split
        · rw [SystemState.storeObject_reply_eq_storeReplyWith
            ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) (fun r => { r with next := none })]
        · rfl

/-- **The destroy cleanup of a finalised scheduling context**
(`lifecyclePreRetypeCleanup`'s scheduling-context arm), run once the context is
bound to no thread and heads no reply stack, so its release finds no binding
and what it does is complete the yield the context records
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

/-- **The destroy cleanup of a scheduling context bound to nothing and heading
no reply stack completes the yield it records**: its release finds no binding
(WS-ZA ZA6.6: before, it was the identity). -/
theorem lifecyclePreRetypeCleanup_of_schedContextFree (st : SystemState) (x : SeLe4n.ObjId)
    (sc : SeLe4n.Kernel.SchedContext) (hB : sc.boundThreadCode = 0) (hR : sc.scReply = none) :
    lifecyclePreRetypeCleanup st x (.schedContext sc) (.schedContext sc) =
      .ok (completeYieldFrom st (SeLe4n.SchedContextId.ofObjId x)) := by
  unfold lifecyclePreRetypeCleanup
  simp only [hR, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [releaseSchedContextBinding_of_unbound _ _ _
    (by unfold SeLe4n.Kernel.SchedContext.boundThread; rw [hB]; rfl)]

/-- The compiled destroy cleanup of a finalised scheduling context
(`finaliseSchedContextCleanup_eq`): the completion of the yield a context bound
to nothing and heading no reply stack records. -/
@[inline] def finaliseSchedContextCleanupImpl (st : SystemState) (x : SeLe4n.ObjId) :
    SystemState :=
  match st.getObject? x with
  | some (.schedContext sc) =>
    if sc.boundThreadCode == 0 && sc.scReply.isNone then
      completeYieldFrom st (SeLe4n.SchedContextId.ofObjId x)
    else st
  | _ => st

/-- **A finalised scheduling context's destroy cleanup completes the yield the
context records**: it runs only on a context bound to nothing and heading no
reply stack (`lifecyclePreRetypeCleanup_of_schedContextFree`). -/
theorem finaliseSchedContextCleanup_eq (st : SystemState) (x : SeLe4n.ObjId) :
    finaliseSchedContextCleanup st x = finaliseSchedContextCleanupImpl st x := by
  unfold finaliseSchedContextCleanup finaliseSchedContextCleanupImpl
  split
  · rename_i sc _
    split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
      rw [lifecyclePreRetypeCleanup_of_schedContextFree st x sc h.1 h.2]
    · rfl
  · rfl

@[csimp] theorem finaliseSchedContextCleanup_eq_impl :
    @finaliseSchedContextCleanup = @finaliseSchedContextCleanupImpl := by
  funext st x; exact finaliseSchedContextCleanup_eq st x

-- The scheduling-context finalisation is defined after its cleanup's `@[csimp]`
-- theorem, so its compiled code takes the compiled cleanup.

/-- The code of the context thread `tid` holds (`TCB.scBindingScCode`: its own
or on loan; `0` for none and for an absent thread). -/
@[inline] def threadHeldContextCode (st : SystemState) (tid : SeLe4n.ThreadId) : Nat :=
  match st.getTcb? tid with
  | some t => t.scBindingScCode
  | none => 0

/-- **seL4's `finaliseCap` on the final capability to a thread**: unbound from
its notification (`unbindNotification`); its blocked IPC cancelled (`suspend` →
`cancelIPC`, a reply removed as `reply_remove_tcb` removes it); every caller
waiting on it for a reply left waiting with no server
(`finaliseThreadOrphanWaiters`: seL4 records no server for a caller, so its
callers stay `BlockedOnReply`, each reply naming its caller, until a reply cap
holder answers them or their replies are deleted); suspended (`.Inactive` and off the
scheduler, a core it ran on made to choose another thread), the suspend ending
as seL4-MCS's `suspend` ends, with the thread's own yield link cancelled
(`schedContext_cancelYieldTo`, `cancelYieldTo`); released by every core (`fpuThreadDelete`, and the
residency record); unbound from the scheduling context it holds, its own or on loan, which goes
back to no one (seL4-MCS's
`unbindFromSC`: `schedContext_unbindTCB`, whose own dequeue the suspend has
made, then `if (sc->scYieldFrom) schedContext_completeYieldTo(sc->scYieldFrom)`,
`completeHeldYield`).  seL4 runs the context unbind before the suspend, and the
cut runs it after, so the unbind finds the thread on no core, which is all the
order changes: the whole finalisation is one kernel step.  The context the
thread held is read before the first write (`threadHeldContextCode`), as seL4
reads `tcb->tcbSchedContext` before `unbindFromSC`, so a context it borrowed is
the one whose yield completes, as in seL4.
What it leaves is read by the retire
off the thread's own links (`threadRetirable`).  All of it runs only when the
pre-state admits it (`threadFinaliseAdmitted`), checks before writes. -/
def finaliseThread (x : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  if threadFinaliseAdmitted st x then
    let tid : SeLe4n.ThreadId := ⟨x.val⟩
    let held := threadHeldContextCode st tid
    completeHeldYield
      (finaliseThreadUnbindSchedContext
        (finaliseThreadReleaseCores
          (cancelYieldTo
            (finaliseThreadSuspend
              (finaliseThreadOrphanWaiters
                (finaliseThreadCancel
                  (finaliseThreadUnbindNotification st tid) tid) tid) tid) tid) tid) tid) held
  else st

/-- **seL4's `finaliseCap` on the final capability to a scheduling context**:
its ready holder taken off the scheduler and unbound from it
(`schedContext_unbindAllTCBs`, `finaliseSchedContextDeschedule` then
`finaliseSchedContextUnbind`), its reply stack let go
(`schedContext_unbindReply`), then the destroy cleanup, which completes the yield
the context records (`schedContext_completeYieldTo` of its `scYieldFrom`,
`completeYieldFrom`), when the pre-state admits it
(`schedContextFinaliseAdmitted`).  seL4's `schedContext_unbindNtfn` has nothing
to do here: this model's context is bound to no notification. -/
def finaliseSchedContext (x : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  if schedContextFinaliseAdmitted st x then
    finaliseSchedContextCleanup (finaliseSchedContextUnstack
      (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x) x) x
  else st

/-- **The scheduling-context finalisation, with its cleanup read as what it
is.** -/
theorem finaliseSchedContext_eq (x : SeLe4n.ObjId) (st : SystemState) :
    finaliseSchedContext x st =
      if schedContextFinaliseAdmitted st x then
        finaliseSchedContextCleanupImpl (finaliseSchedContextUnstack
          (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x) x) x
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
      cancelBoundDonationOnCore st tid tcb :=
  cancelDonationArmOnCore_of_bound st tid tcb _ (schedContextBinding_of_codes hS hO)

-- ============================================================================
-- §4b  A reply's finalisation
-- ============================================================================

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

/-- **Whether a final delete may pop the reply at `x` off a context no thread
holds**, its caller `c` (TCB `t`) waiting on it, read on the pre-state before any
write: the reply heads the stack of a context that names it back as its head,
`reply_pop` of that context commits (`unheldPopCommits`: the context is bound
to no thread — its holder's finalisation unbound it, seL4-MCS's
`schedContext_unbindTCB` — and the pop back to `c` commits where `c` holds no
context of its own, the sever where it holds one), and `c` passes the caller
checks `replyCallerFinalisable` reads.  Each read is `O(1)`. -/
@[inline] def replyUnheldPopAdmitted (st : SystemState) (x : SeLe4n.ObjId) (r : Reply)
    (c : SeLe4n.ThreadId) (t : TCB) : Bool :=
  match r.next with
  | some (.head s) =>
    (match st.getSchedContext? s with
     | some sc =>
       match sc.scReply with
       | some rid => rid.val == x.val
       | none => false
     | none => false) &&
      unheldPopCommits st s c && !c.isReserved && !isIdleThreadId c &&
      t.runCoreCode == 0 && decide (4 ≤ t.ipcStateCode) &&
      t.replyObjectCode == x.val + 1 && t.queueNextCode == 0 && t.queuePrevCode == 0 &&
      t.timeoutBudget.isNone
  | _ => false

/-- **The pop of a reply heading a context no thread holds** (seL4-MCS's
`reply_remove` head branch, `reply_pop`): where the reply's caller `c` holds no
context, the context back to `c`, the frame below its new head
(`returnUnheldSchedContextResolved`), then settled as every returned context is
(`settleReturnedContext`, the tail of `schedContext_donate`): placed on `c`'s
home core's release queue by its refills while `c` is not suspended; where `c`
holds one, the head popped off the context alone, nothing handed back
(`severUnheldSchedContextResolved`).  The state unchanged where the pop
refuses. -/
@[inline] def finaliseReplyUnheldPop (st : SystemState) (r : Reply) (c : SeLe4n.ThreadId) :
    SystemState :=
  match r.next with
  | some (.head s) =>
    if donationRecipientAcceptable st c then
      match returnUnheldSchedContextResolved st s c with
      | .ok st' => SchedContextOps.settleReturnedContext st' (determineTargetCore st' c) s
      | .error _ => st
    else
      match severUnheldSchedContextResolved st s with
      | .ok st' => st'
      | .error _ => st
  | _ => st

/-- **The unheld pop, as compiled**: in place where its gate admits it
(`unheldPopsInPlace`, under which it is the specification's pop,
`unheldPopsInPlace_pop`), every check read as a code before the first write;
the specification's pop otherwise. -/
@[inline] def finaliseReplyUnheldPopImpl (st : SystemState) (r : Reply) (c : SeLe4n.ThreadId) :
    SystemState :=
  match r.next with
  | some (.head s) =>
    if unheldPopsInPlace st s c then
      let st' := returnUnheldSchedContextInPlace st c s
      SchedContextOps.settleReturnedContext st' (determineTargetCore st' c) s
    else if donationRecipientAcceptable st c then
      match returnUnheldSchedContextResolved st s c with
      | .ok st' => SchedContextOps.settleReturnedContext st' (determineTargetCore st' c) s
      | .error _ => st
    else
      match severUnheldSchedContextResolved st s with
      | .ok st' => st'
      | .error _ => st
  | _ => st

@[csimp] theorem finaliseReplyUnheldPop_eq_impl :
    @finaliseReplyUnheldPop = @finaliseReplyUnheldPopImpl := by
  funext st r c
  unfold finaliseReplyUnheldPop finaliseReplyUnheldPopImpl
  split
  · next s _ =>
    cases hG : unheldPopsInPlace st s c with
    | false => rfl
    | true =>
      have hP := unheldPopsInPlace_pop st s c hG
      simp only [donationRecipientAcceptable_of_unheldReturnCommits hP.1, hP.2, ↓reduceIte]
  · rfl

/-- **The unheld pop's three outcomes**: the state unchanged; or, the reply
heading a context `s` and `c` holding none, the pop of `s` back to `c` off the
outer caller the reply stack resolves, then its settle on `c`'s home core; or,
`c` holding a context of its own, the sever of `s` (`reply_pop`'s no-donate
arm). -/
theorem finaliseReplyUnheldPop_cases (st : SystemState) (r : Reply) (c : SeLe4n.ThreadId) :
    finaliseReplyUnheldPop st r c = st ∨
      (∃ (s : SeLe4n.SchedContextId) (n : Option SeLe4n.ThreadId) (st' : SystemState),
        r.next = some (.head s) ∧
        replyStackOuterCaller? st s = .ok n ∧ returnUnheldSchedContext st s c n = .ok st' ∧
        finaliseReplyUnheldPop st r c =
          SchedContextOps.settleReturnedContext st' (determineTargetCore st' c) s) ∨
      ∃ (s : SeLe4n.SchedContextId) (n : Option SeLe4n.ThreadId) (st' : SystemState),
        r.next = some (.head s) ∧ donationRecipientAcceptable st c = false ∧
        replyStackOuterCaller? st s = .ok n ∧ severUnheldSchedContext st s n = .ok st' ∧
        finaliseReplyUnheldPop st r c = st' := by
  unfold finaliseReplyUnheldPop
  split
  next s hN =>
    cases hA : donationRecipientAcceptable st c with
    | true =>
      simp only [↓reduceIte]
      cases hR : returnUnheldSchedContextResolved st s c with
      | error _ => exact Or.inl rfl
      | ok st' =>
        refine Or.inr (Or.inl ?_)
        unfold returnUnheldSchedContextResolved at hR
        cases hO : replyStackOuterCaller? st s with
        | error _ => rw [hO] at hR; cases hR
        | ok n =>
          rw [hO] at hR
          exact ⟨s, n, st', hN, hO, hR, rfl⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hR : severUnheldSchedContextResolved st s with
      | error _ => exact Or.inl rfl
      | ok st' =>
        refine Or.inr (Or.inr ?_)
        obtain ⟨n, hO, hP⟩ := severUnheldSchedContextResolved_ok_decompose hR
        exact ⟨s, n, st', hN, by simp, hO, hP, rfl⟩
  next => exact Or.inl rfl

/-- **A finalised reply heading a context no thread holds**: the pop
(`finaliseReplyUnheldPop`), then — the popped reply heading no stack — the
caller cancelled as the reply finalisation cancels it there (`finaliseReplyCancel`:
the caller restored, its reply link and the reply's caller link cleared, the
caller off any server's reply-waiter queue), the boost it lent a server reverted,
and the caller made `.Inactive` (seL4's `reply_unlink`).  The cancel reads the
reply and the caller again on the popped state and keeps its own guard
(`replyCallerFinalisable`), which the pop keeps on every admitted state. -/
def finaliseReplyUnheld (st : SystemState) (x : SeLe4n.ObjId) (r : Reply) (c : SeLe4n.ThreadId) :
    SystemState :=
  let st1 := finaliseReplyUnheldPop st r c
  match st1.getObject? x with
  | some (.reply r1) =>
    match st1.getTcb? c with
    | some t1 =>
      if r1.callerCode == c.val + 1 && replyCallerFinalisable st1 x r1 c t1 then
        finaliseThreadSuspend (finaliseReplyRevert (finaliseReplyCancel st1 r1 c t1)
          t1.blockingServer?) c
      else st1
    | none => st1
  | _ => st1

/-- **seL4's `finaliseCap` on the final capability to a reply whose caller
still waits on it** (`reply_remove`, then `reply_unlink`): the caller's blocked
call is cancelled (`finaliseReplyCancel`: a head reply popped, its context
handed back to the caller; any other reply spliced out of its stack; then the
caller restored with the cancellation frame, the reply's caller link and the
caller's reply link cleared, the caller off its server's reply-waiter queue), the boost it lent its server reverted
(`finaliseReplyRevert`), and the caller made `.Inactive`
(`finaliseThreadSuspend`, seL4's `setThreadState Inactive`).  Only when the
pre-state admits it (`replyCallerFinalisable`), checks before writes; a reply
heading a context no thread holds — its holder's finalisation unbound it — is
popped, the context back to the caller, then the caller cancelled and made
`.Inactive` (`finaliseReplyUnheld`, when `replyUnheldPopAdmitted` admits it); a
reply with no caller but stashed by a receiver is unlinked from it
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
        else if replyUnheldPopAdmitted st x r c t then finaliseReplyUnheld st x r c
        else st
      | none => st
  | _ => st

/-- **A finalised reply's caller cancelled, reverted and suspended, as
compiled**: a head reply as `finaliseReply` runs it; any other through
`finaliseReplyCancelSplice`, with the caller's reply and server read as codes
before the first write, so the caller's thread record is held by its slot alone
when the restore and the consume write it, and is rewritten there. -/
@[inline] def finaliseReplyCaller (st : SystemState) (r : Reply) (c : SeLe4n.ThreadId)
    (t : TCB) : SystemState :=
  if replyStackLinkIsHead r.next then
    let serverCode := replyCallerServerCode t
    finaliseThreadSuspend (finaliseReplyRevert (cancelHeadReplyCaller st c t)
      (SeLe4n.ThreadId.ofOptCode serverCode)) c
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
  · simp only [cancelHeadReplyCaller_eq, ofOptCode_replyCallerServerCode]
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
        else if replyUnheldPopAdmitted st x r c t then
          let st1 := finaliseReplyUnheldPop st r c
          match st1.getObject? x with
          | some (.reply r1) =>
            match st1.getTcb? c with
            | some t1 =>
              if r1.callerCode == c.val + 1 && replyCallerFinalisable st1 x r1 c t1 then
                finaliseReplyCaller st1 r1 c t1
              else st1
            | none => st1
          | _ => st1
        else st
      | none => st
  | _ => st

@[csimp] theorem finaliseReply_eq_impl : @finaliseReply = @finaliseReplyImpl := by
  funext x st
  unfold finaliseReply finaliseReplyImpl finaliseReplyUnheld
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
targeted, for any other kind, or when the object is still named by a table
outside every slot — an interrupt's notification, or an endpoint whose
registration the final delete has not dropped first
(`releaseFinalRegistration`, which `retireFinalisedObject` runs before this);
the object records that itself (`SystemState.tableBackLinksClear`, one field
read in place of a walk of the registry and the interrupt table). -/
def finaliseFinalObject (target : Nat) (st : SystemState) : SystemState :=
  if target = 0 then st
  else
    let x := SeLe4n.ObjId.ofNat (target - 1)
    if st.tableBackLinksClear x then
      match st.getObjectType? x with
      | some .endpoint => cancelAllIpc x st
      | some .notification => cancelAllSignals x (unbindMaybeNotification x st)
      | some .tcb => finaliseThread x st
      | some .schedContext => finaliseSchedContext x st
      | some .reply => finaliseReply x st
      | _ => st
    else st

/-- **WS-ZA ZA5.5: a final delete of an endpoint drops the service registration
it records**, as seL4's `finaliseCap` tears down what an endpoint holds.  The
registration's endpoint capability is held outside every slot, so the slot's
delete is final; without this step the registration outlived the endpoint's
last capability, no capability could revoke it, and the endpoint and the
untyped space it was carved from could never be reclaimed.  The registration
the endpoint records (`Endpoint.serviceRegistered`, under the endpoint's own id)
is revoked
(`revokeService`), which clears the record, so the endpoint's back-links are
clear and the finalisation and retire after it run as for any endpoint.  Any
other object, and an endpoint recording none, is returned as it is: a read of
one field. -/
@[inline] def releaseFinalRegistration (target : Nat) (st : SystemState) : SystemState :=
  if target = 0 then st
  else
    match st.getObject? (SeLe4n.ObjId.ofNat (target - 1)) with
    | some (.endpoint ep) =>
      match ep.serviceRegistered with
      | false => st
      | true =>
        match revokeService (ServiceId.ofNat (target - 1)) st with
        | .ok ((), st') => st'
        | .error _ => st
    | _ => st

/-- The release either leaves the state or is a successful revoke of the
registration the target endpoint records. -/
theorem releaseFinalRegistration_cases (target : Nat) (st : SystemState) :
    releaseFinalRegistration target st = st ∨
      ∃ ep, target ≠ 0 ∧ st.getObject? (SeLe4n.ObjId.ofNat (target - 1)) = some (.endpoint ep) ∧
        ep.serviceRegistered = true ∧
        revokeService (ServiceId.ofNat (target - 1)) st =
          .ok ((), releaseFinalRegistration target st) := by
  unfold releaseFinalRegistration
  split
  · exact .inl rfl
  next h0 =>
  split
  · next ep hEp =>
    split
    · exact .inl rfl
    · next hC =>
      split
      · next st' hR => exact .inr ⟨ep, h0, hEp, hC, hR⟩
      · exact .inl rfl
  · exact .inl rfl

/-- The compiled `releaseFinalRegistration`: the endpoint's record cleared
(`clearServiceRecord`, which returns any other state as it is), with no
fallback holding the state.  The specification's refusal arm kept the state
alive across the revoke, so the clear met a shared state and copied the object
store's tables on each final delete of a registered endpoint.  Proven equal
(`releaseFinalRegistration_eq_impl`). -/
def releaseFinalRegistrationImpl (target : Nat) (st : SystemState) : SystemState :=
  if target = 0 then st else clearServiceRecord st (SeLe4n.ObjId.ofNat (target - 1))

@[csimp] theorem releaseFinalRegistration_eq_impl :
    @releaseFinalRegistration = @releaseFinalRegistrationImpl := by
  funext target st
  unfold releaseFinalRegistration releaseFinalRegistrationImpl
  split
  · rfl
  · have hClear : ∀ o, st.getObject? (SeLe4n.ObjId.ofNat (target - 1)) = o →
        (∀ ep, o ≠ some (.endpoint ep) ∨ ep.serviceRegistered = false) →
        clearServiceRecord st (SeLe4n.ObjId.ofNat (target - 1)) = st := by
      intro o ho hN
      unfold clearServiceRecord
      split
      · next ep h =>
        rcases hN ep with hN | hN
        · exact absurd (ho ▸ h) hN
        · simp [hN]
      · rfl
    split
    · next ep hEp =>
      split
      · next hC => exact (hClear _ hEp (fun e => by
          by_cases he : e = ep
          · exact .inr (he ▸ hC)
          · exact .inl (fun h => he (by cases h; rfl)))).symm
      · next hC =>
        unfold revokeService
        have hP : recordedRegistrationPresent st
            (SeLe4n.ObjId.ofNat (ServiceId.ofNat (target - 1)).toNat) = true := by
          unfold recordedRegistrationPresent
          rw [ServiceId.toNat_ofNat, hEp]; exact hC
        rw [if_pos hP, ServiceId.toNat_ofNat]
    · next hN =>
      exact (hClear _ rfl (fun e => .inl (hN e))).symm

/-- **A property every successful revoke keeps holds after the release.** -/
theorem releaseFinalRegistration_closed (P : SystemState → Prop)
    (hRev : ∀ (s s' : SystemState) (sid : ServiceId), P s → revokeService sid s = .ok ((), s') →
      P s')
    (target : Nat) (st : SystemState) (h : P st) : P (releaseFinalRegistration target st) := by
  rcases releaseFinalRegistration_cases target st with hE | ⟨_, _, _, _, hR⟩
  · rw [hE]; exact h
  · exact hRev _ _ _ h hR

/-- **WS-ZA ZA6.32: whether the word `target` names an interrupt node**
(`target = x + 1`, `x` in the nodes' range), the object a line's last handler
capability takes with it. -/
@[inline] def retireTargetsIrqNode (target : Nat) : Bool :=
  target != 0 && isIrqNodeObjId InterruptLineSet.capacity (SeLe4n.ObjId.ofNat (target - 1))

/-- **The retire of what a final delete destroyed, after its finalisation**:
the registration an endpoint records dropped (`releaseFinalRegistration`), then
`finaliseFinalObject`, then `retireFinalObject`.

WS-ZA ZA6.32: the target of a line's last handler capability is the line's
interrupt node, which the kernel keeps.  Its slot has been emptied by the delete
(the zombie loop, seL4's `deletingIRQHandler`, which `cteDeleteOne`s the slot),
so what is left of seL4's `finaliseCap` on an `IRQHandlerCap` is
`deletedIRQHandler`: the line put at `IRQInactive` (`retireIrqNode`). -/
@[inline] def retireFinalisedObject (executingCore : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) : SystemState :=
  if retireTargetsIrqNode target then retireIrqNode st (SeLe4n.ObjId.ofNat (target - 1))
  else
    retireFinalObject executingCore target recorder
      (finaliseFinalObject target (releaseFinalRegistration target st))

theorem finaliseFinalObject_zero (st : SystemState) : finaliseFinalObject 0 st = st := by
  simp [finaliseFinalObject]

theorem retireFinalisedObject_zero (ec : Concurrency.CoreId) (recorder : Nat)
    (st : SystemState) : retireFinalisedObject ec 0 recorder st = st := by
  simp [retireFinalisedObject, retireTargetsIrqNode, releaseFinalRegistration,
    finaliseFinalObject_zero, retireFinalObject_zero]

/-- **WS-ZA ZA6.32: the retire's two shapes**: a node's line retired, or the
finalisation and the object retire. -/
theorem retireFinalisedObject_cases (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) :
    (retireTargetsIrqNode target = true ∧
      retireFinalisedObject ec target recorder st =
        retireIrqNode st (SeLe4n.ObjId.ofNat (target - 1))) ∨
    (retireTargetsIrqNode target = false ∧
      retireFinalisedObject ec target recorder st =
        retireFinalObject ec target recorder
          (finaliseFinalObject target (releaseFinalRegistration target st))) := by
  unfold retireFinalisedObject
  cases h : retireTargetsIrqNode target
  · exact .inr ⟨rfl, by simp⟩
  · exact .inl ⟨rfl, by simp⟩

/-- **A retire word naming a node names it by its line**: the node the word
names is the node of the line its id is offset to. -/
theorem retireTargetsIrqNode_irqNodeId {target : Nat} (hNode : retireTargetsIrqNode target = true) :
    irqNodeId ((SeLe4n.ObjId.ofNat (target - 1)).toNat - irqNodeIdBase) =
      SeLe4n.ObjId.ofNat (target - 1) := by
  simp only [retireTargetsIrqNode, isIrqNodeObjId, Bool.and_eq_true, decide_eq_true_eq] at hNode
  apply SeLe4n.ObjId.ext
  simp only [irqNodeId, SeLe4n.ObjId.ofNat, SeLe4n.ObjId.toNat] at hNode ⊢
  omega

/-- …and is a nonzero word. -/
theorem retireTargetsIrqNode_ne_zero {target : Nat} (hNode : retireTargetsIrqNode target = true) :
    target ≠ 0 := by
  rintro rfl; simp [retireTargetsIrqNode] at hNode

/-- **WS-ZA ZA6.32: a node's line retire writes no object, no scheduler field and
no derivation edge.** -/
@[simp] theorem retireIrqNode_objects (st : SystemState) (x : SeLe4n.ObjId) :
    (retireIrqNode st x).objects = st.objects :=
  Architecture.setIrqLineSignal_objects st _ false

@[simp] theorem retireIrqNode_scheduler (st : SystemState) (x : SeLe4n.ObjId) :
    (retireIrqNode st x).scheduler = st.scheduler :=
  Architecture.setIrqLineSignal_scheduler st _ false

@[simp] theorem retireIrqNode_cdt (st : SystemState) (x : SeLe4n.ObjId) :
    (retireIrqNode st x).cdt =
      st.cdt.withIrqLineIssued (x.toNat - irqNodeIdBase) false :=
  Architecture.setIrqLineSignal_cdt st _ false

@[simp] theorem retireIrqNode_asidTable (st : SystemState) (x : SeLe4n.ObjId) :
    (retireIrqNode st x).asidTable = st.asidTable :=
  Architecture.setIrqLineSignal_asidTable st _ false

@[simp] theorem retireIrqNode_objectIndex (st : SystemState) (x : SeLe4n.ObjId) :
    (retireIrqNode st x).objectIndex = st.objectIndex :=
  Architecture.setIrqLineSignal_objectIndex st _ false

@[simp] theorem retireIrqNode_lifecycle (st : SystemState) (x : SeLe4n.ObjId) :
    (retireIrqNode st x).lifecycle = st.lifecycle :=
  Architecture.setIrqLineSignal_lifecycle st _ false

@[simp] theorem retireIrqNode_getObject? (st : SystemState) (x o : SeLe4n.ObjId) :
    (retireIrqNode st x).getObject? o = st.getObject? o := by
  simp [SystemState.getObject?]

@[simp] theorem retireIrqNode_slotCapAt (st : SystemState) (x : SeLe4n.ObjId) :
    (retireIrqNode st x).slotCapAt = st.slotCapAt := by
  funext r; simp [SystemState.slotCapAt]

end SeLe4n.Kernel
