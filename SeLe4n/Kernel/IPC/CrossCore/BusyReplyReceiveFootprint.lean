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
move the ones they name on the cancelled state, the leg re-run from it. -/
def schedLockSet_receiveCancellingHolderOnCore (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId) :
    List (LockKey × Concurrency.AccessMode) :=
  -- The canonical ladder at the top, each segment chosen by the busy reply,
  -- so the shared `schedFootprintOfCores` lemmas apply at full arity; with no
  -- busy reply it is `schedLockSet_endpointReceiveOnCore` by definition.
  schedFootprintOfCores
    (match busyReplyHolder? st receiver replyId with
      | none => endpointReceiveDualWriteSet st endpointId executingCore
          ++ endpointReceiveHandoffChainWriteSet st endpointId receiver replyId executingCore
      | some _ => Concurrency.allCores)
    (match busyReplyHolder? st receiver replyId with
      | none => endpointReceiveHandoffReplenishCores st endpointId receiver
      | some holder => endpointReceiveLegReplenishCores (cancelReplyHolder st holder executingCore)
          endpointId receiver replyId executingCore)

/-- The receive's footprint, busy reply or not, is a cores footprint. -/
theorem schedLockSet_receiveCancellingHolderOnCore_ofCores (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (executingCore : CoreId) :
    ∃ run repl, schedLockSet_receiveCancellingHolderOnCore st endpointId receiver replyId
      executingCore = schedFootprintOfCores run repl := by
  exact ⟨_, _, rfl⟩

end SeLe4n.Kernel
