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
-- §4  A thread's and a scheduling context's finalisation
-- ============================================================================

/-- **Whether an IPC state, held as its two codes, is one an unbound thread off
every run queue may be in** (the invariants' `passiveServerIdleAllowed`): not
blocked sending and not blocked calling, so unbinding its scheduling context
strands no sender. -/
@[inline] def ipcCodesIdleAllowed (objCode stateCode : Nat) : Bool :=
  !(stateCode == 0 && objCode != 0) && stateCode != 3

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

/-- **Whether a final delete may finalise the thread at `x`**, read on the
pre-state before any write.  The thread is stored under its own id and is no
reserved or idle thread; it is ready (suspended, queued, current on a core —
the executing core's own thread deleting its last capability included — or held
by a core as its FP/SIMD owner or its resident), or the head waiter of a
notification (the one blocking state this cut cancels); it is linked into no
endpoint or reply-waiter queue, holds no reply link, stash, timeout budget or
message, and lends or borrows no reservation; its space slots are empty (their
finalising delete is a later cut's); a bound notification and a bound
scheduling context are bound back to it; and nothing else names it as a
reservation's origin or as a service's owner.  Each step below re-reads its own
guard, so a state outside this set is left as it is and the retire then refuses
the thread. -/
@[inline] def threadFinaliseAdmitted (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObject? x with
  | some (.tcb t) =>
    let tid : SeLe4n.ThreadId := ⟨x.val⟩
    t.tid.val == x.val && !tid.isReserved && !isIdleThreadId tid &&
    t.queueNextCode == 0 && t.queuePrevCode == 0 && t.queuePPrevCode == 0 &&
    t.replyWaiterNextCode == 0 && t.replyWaiterPrevCode == 0 && t.replyWaitersHeadCode == 0 &&
    t.replyObjectCode == 0 && t.pendingReceiveReplyCode == 0 && t.timeoutBudget.isNone &&
    t.pendingMessage.isNone && t.scBindingOwnerCode == 0 &&
    t.spaceCells[0].isNone && t.spaceCells[1].isNone &&
    ((t.ipcStateCode == 0 && t.ipcObjectCode == 0 &&
        t.ntfnNextCode == 0 && t.ntfnPrevCode == 0) ||
      (t.ipcStateCode == 2 && t.threadState != .Inactive && t.ntfnPrevCode == 0 &&
        match st.getNotification? ⟨t.ipcObjectCode⟩ with
        | some n => n.waitHeadCode == x.val + 1
        | none => false)) &&
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
`cancelIPC` → `cancelSignal`): the head waiter of a notification leaves its
queue and is made `.ready` with the cancellation frame, as
`cancelIpcBlocking`'s notification arm makes it, and is **not** woken — it is
being destroyed.  Any other state is left alone. -/
def finaliseThreadCancel (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some t =>
    match t.ipcState with
    | .blockedOnNotification n =>
      match st.getNotification? n with
      | some ntfn =>
        if ntfn.waitHead == some tid && notificationWaiterCancellable st n tid t then
          Lifecycle.Suspend.cancelIpcBlocking st tid t
        else st
      | none => st
    | _ => st
  | none => st

/-- **The mark a finalised thread's suspend leaves**: `.Inactive`, and, once the
thread is on no run queue, its own run links cleared.  The dequeue rewrites the
neighbours' links and the thread's core code, and leaves the thread's own links
behind, which no reader consults while the core code is `0`; the retire asks
them zero (`threadQuiescent`).  On a queued thread it writes the state alone, so
it never changes what a run queue reads (`finaliseSuspendMark_runLinkOn`). -/
@[inline] def finaliseSuspendMark (t : TCB) : TCB :=
  { t with threadState := .Inactive
           runPrevCode := if t.runCoreCode == 0 then 0 else t.runPrevCode
           runNextCode := if t.runCoreCode == 0 then 0 else t.runNextCode
           runBucketPrevCode := if t.runCoreCode == 0 then 0 else t.runBucketPrevCode
           runBucketNextCode := if t.runCoreCode == 0 then 0 else t.runBucketNextCode }

theorem finaliseSuspendMark_runLinkOn (t : TCB) (c : Concurrency.CoreId) :
    (finaliseSuspendMark t).runLinkOn c = t.runLinkOn c := by
  unfold TCB.runLinkOn
  show (if t.runCoreCode = c.val + 1 then _ else _) = (if t.runCoreCode = c.val + 1 then _ else _)
  by_cases h : t.runCoreCode = c.val + 1
  · have h0 : (t.runCoreCode == 0) = false := by rw [h]; rfl
    rw [if_pos h, if_pos h]
    simp only [TCB.runLink, finaliseSuspendMark, h0, Bool.false_eq_true, if_false]
  · rw [if_neg h, if_neg h]

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
is empty resumes its idle loop, never the frame it trapped with. -/
def finaliseThreadSuspend (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some t =>
    if t.ipcStateCode == 0 && t.ipcObjectCode == 0 && t.threadState != .Inactive &&
        !isIdleThreadId tid then
      (descheduleAtPlacement st tid).updateTcb tid finaliseSuspendMark
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
        !threadHeldOnSomeCore st tid && ipcCodesIdleAllowed t.ipcObjectCode t.ipcStateCode &&
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
        !threadHeldOnSomeCore st tid && ipcCodesIdleAllowed t.ipcObjectCode t.ipcStateCode &&
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
      (schedContextBinding_of_codes' hG.1.1.1.1.1 hG.1.1.1.1.2),
      cancelBoundDonationOnCore_of_bound st tid t _ _
      (schedContextBinding_of_codes' hG.1.1.1.1.1 hG.1.1.1.1.2)]

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

/-- **Whether a final delete may finalise the scheduling context at `x`**: it
heads no reply stack and is lent by no one, and a thread it is bound to is bound
back to it as its own (`.bound`), runs and waits on no core, and is in a state
an unbound thread may idle in. -/
@[inline] def schedContextFinaliseAdmitted (st : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match st.getObject? x with
  | some (.schedContext sc) =>
    sc.scReply.isNone && sc.donationOrigin.isNone &&
    (sc.boundThreadCode == 0 ||
      let tid : SeLe4n.ThreadId := ⟨sc.boundThreadCode - 1⟩
      match st.getTcb? tid with
      | some t =>
        t.scBindingScCode == x.val + 1 && t.scBindingOwnerCode == 0 &&
        t.runCoreCode == 0 && !threadHeldOnSomeCore st tid &&
        ipcCodesIdleAllowed t.ipcObjectCode t.ipcStateCode
      | none => false)
  | _ => false

/-- **Unbind a scheduling context being finalised from its thread** (seL4's
`schedContext_unbindAllTCBs`): the thread's reservation arm
(`cancelDonationArmOnCore`), which clears both sides and the context's
replenishment on the thread's home core. -/
def finaliseSchedContextUnbind (st : SystemState) (x : SeLe4n.ObjId) : SystemState :=
  match st.getObject? x with
  | some (.schedContext sc) =>
    if sc.boundThreadCode == 0 then st
    else
      let tid : SeLe4n.ThreadId := ⟨sc.boundThreadCode - 1⟩
      match st.getTcb? tid with
      | some t =>
        if t.scBindingScCode == x.val + 1 && t.scBindingOwnerCode == 0 && t.runCoreCode == 0 &&
            !threadHeldOnSomeCore st tid && ipcCodesIdleAllowed t.ipcObjectCode t.ipcStateCode then
          match cancelDonationArmOnCore st tid t with
          | .ok st' => st'
          | .error _ => st
        else st
      | none => st
  | _ => st

/-- The compiled `finaliseSchedContextUnbind`: the guard names a `.bound`
binding to the context, so the reservation arm is the in-place unbind
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
        if t.scBindingScCode == x.val + 1 && t.scBindingOwnerCode == 0 && t.runCoreCode == 0 &&
            !threadHeldOnSomeCore st tid && ipcCodesIdleAllowed t.ipcObjectCode t.ipcStateCode then
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
          simp only [Bool.and_eq_true, beq_iff_eq] at hG
          have hB : t.schedContextBinding = .bound ⟨x.val⟩ := by
            have h := schedContextBinding_of_codes' (by omega) hG.1.1.1.2
            rw [h, hG.1.1.1.1]; rfl
          rw [cancelDonationArmOnCore_of_bound st _ t _ hB,
            cancelBoundDonationOnCore_of_bound st _ t _ _ hB]
        · rfl
  · rfl

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
unbound from its thread, then the destroy cleanup, when the pre-state admits it
(`schedContextFinaliseAdmitted`). -/
def finaliseSchedContext (x : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  if schedContextFinaliseAdmitted st x then
    finaliseSchedContextCleanup (finaliseSchedContextUnbind st x) x
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
      if schedContextFinaliseAdmitted st x then finaliseSchedContextUnbind st x else st := by
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
-- §5  The finalisation a final delete runs
-- ============================================================================

/-- **seL4's `finaliseCap` on the final capability to an endpoint, a
notification, a thread or a scheduling context** (`target`, a word as
`slotRetireTarget` reads it: `x + 1`, or `0` for none): an endpoint's waiters
are cancelled (`cancelAllIpc`); a notification is unbound from its thread and
its waiters are cancelled (`unbindMaybeNotification`, `cancelAllSignals`); a
thread is suspended and unbound (`finaliseThread`); a scheduling context is
unbound (`finaliseSchedContext`).  Nothing when no object is
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
