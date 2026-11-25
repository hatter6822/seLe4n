-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.ReplyHolderCancel
import SeLe4n.Kernel.Scheduler.SchedFootprint
import SeLe4n.Kernel.SchedContext.NotificationDonation

/-!
# The scheduler-domain footprint of a receive that cancels its busy reply

WS-SX SX4: seL4-MCS `receiveIPC` cancels the IPC of the thread its reply is
busy with (`cancelIPC(replyTCB)`) before it receives.  The receive's
scheduler-domain footprint sits here, beside the cancel it names
(`cancelReplyHolder`): the receive's own footprint when the reply is free, and,
when it is busy, every core's run queue with the replenish queues the receive's
leg moves on the cancelled state.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId LockKey)

/-- **The replenish queues a receive's leg and its rendezvous donation move**,
read off the leg run from `st`: the leg's own pre-receive return
(`receivePreReturnReplenishCores`) and the donation of the `Call` it dequeues
(`rendezvousCallDonationReplenishCores`, at the state the donation runs on).
Each is the set its step's own frame names, so the footprint and the frame read
one answer; the chain walk that follows moves no reservation. -/
def endpointReceiveLegReplenishCores (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId) :
    List CoreId :=
  receivePreReturnReplenishCores st endpointId receiver ++
    match endpointReceiveDualWithCapsOnCore endpointId receiver replyId executingCore st with
    | (_, .error _) => []
    | (st1, .ok (dequeued, _, _)) => rendezvousCallDonationReplenishCores st1 receiver dequeued

/-- **The cores a receive's signal completion donates on** (seL4-MCS
`receiveIPC`'s `completeSignal`, then `maybeDonateSchedContext`): the receiver's
home core where seL4's guard holds on the state the completion starts from,
which is the busy reply's cancelled state when the reply names a holder and the
entry's own state otherwise.  The wait's consumption and the badge register
leave the guard's reads alone (`completeSignalArm_signalDonationCores_eq`), so
this is exact: no over-approximation. -/
def receiveDonationCores (st : SystemState) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId) : List CoreId :=
  match busyReplyHolder? st receiver replyId with
  | none => signalDonationCores st (receiverBoundNotification st receiver) receiver
  | some holder =>
      signalDonationCores (cancelReplyHolder st holder executingCore)
        (receiverBoundNotification (cancelReplyHolder st holder executingCore) receiver) receiver

/-- **The `.receive` arm's scheduler-domain footprint, its busy reply's cancel
included** (seL4-MCS `receiveIPC`'s `cancelIPC(replyTCB)`).

A receive whose named reply is free, or that names none, is the receive's own
footprint (`schedLockSet_endpointReceiveOnCore`).  One whose reply is busy with
another thread (`busyReplyHolder?`) cancels that thread first
(`cancelRecvBusyReply`): the cancel's priority revert re-buckets the run queue of
every member of a chain the cancel itself discovers, on its home core, and a
refusal after the cancel hands the cancelled state back from the entry's spilled
state rather than the dispatch's, so the run segment names every core's run
queue.  The replenish segment is exact: the cancel moves no reservation
(`cancelReplyHolder_replenishQueueOnCore`), and the receive's leg and donation
move the ones they name on the cancelled state, the leg re-run from it.  Either
way the leg is re-run on the state it runs on (`receiveLegState`): a blocking
receive first returns the bound notification's context (seL4-MCS `receiveIPC`'s
`maybeReturnSchedContext`), which moves no run queue but changes whether the
rendezvous donates, so the leg's reads are taken after it; the return takes the
context off the replenish queue that holds it, so the replenish segment names
that one core (`receiveReturnReplenishCores`, read on the state the return runs
on).  Both
segments also name the cores a completion of the receiver's bound notification
donates on (`receiveDonationCores`, seL4-MCS `maybeDonateSchedContext`). -/
def schedLockSet_receiveCancellingHolderOnCore (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId) :
    List (LockKey × Concurrency.AccessMode) :=
  -- The canonical ladder at the top, each segment chosen by the busy reply,
  -- so the shared `schedFootprintOfCores` lemmas apply at full arity; with no
  -- busy reply it is `schedLockSet_endpointReceiveOnCore` with the donation's
  -- cores appended.
  schedFootprintOfCores
    ((match busyReplyHolder? st receiver replyId with
      | none => endpointReceiveDualWriteSet (receiveLegState st receiver) endpointId executingCore
          ++ endpointReceiveHandoffChainWriteSet (receiveLegState st receiver) endpointId receiver
            replyId executingCore
      | some _ => Concurrency.allCores) ++ receiveDonationCores st receiver replyId executingCore)
    ((match busyReplyHolder? st receiver replyId with
      | none => endpointReceiveHandoffReplenishCores (receiveLegState st receiver) endpointId
          receiver replyId.isSome ++ receiveReturnReplenishCores st receiver
      | some holder => endpointReceiveLegReplenishCores
          (receiveLegState (cancelReplyHolder st holder executingCore) receiver)
          endpointId receiver replyId executingCore ++
          receiveReturnReplenishCores (cancelReplyHolder st holder executingCore) receiver) ++
      receiveDonationCores st receiver replyId executingCore)

/-- The receive's footprint, busy reply or not, is a cores footprint. -/
theorem schedLockSet_receiveCancellingHolderOnCore_ofCores (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (executingCore : CoreId) :
    ∃ run repl, schedLockSet_receiveCancellingHolderOnCore st endpointId receiver replyId
      executingCore = schedFootprintOfCores run repl := by
  exact ⟨_, _, rfl⟩

end SeLe4n.Kernel
