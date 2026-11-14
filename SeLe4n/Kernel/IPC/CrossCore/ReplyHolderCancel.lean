/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.SuspendAdmission
import SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation

/-!
# A reply's busy holder, and its cancel

WS-SX SX4: seL4-MCS `receiveIPC` (`endpoint.c`) first cancels the IPC of the
thread a busy reply object is linked to:

```c
if (unlikely(replyPtr->replyTCB != NULL && replyPtr->replyTCB != thread)) {
    userError("Reply object already has unexecuted reply!");
    cancelIPC(replyPtr->replyTCB);
}
```

`cancelIPC` unlinks the reply from that thread (`reply_remove_tcb` for a caller
`BlockedOnReply`, `blockedCancelIPC`'s `reply_unlink` for a receiver that
stashed it and waits `BlockedOnReceive`) and leaves it `Inactive`.

`busyReplyHolderCode` names that thread; `cancelReplyHolder` is `cancelIPC` on
it: the suspend's IPC teardown (`suspendCancelRevert` -- `cancelIpcKeepingContexts`,
the reply arm `reply_remove_tcb`, with the boost the holder lent through the
reply reverted) and the `Inactive` write.  None of the rest of `suspend` runs (no
dequeue, no release-queue removal, no yield cancel) and no scheduling point:
seL4's `receiveIPC` runs none, and the receive that follows is the receiver's,
on the core it is current on.  A boost the revert takes off a thread leaves the
scheduling point owed on its core (`markKeyChangeFor`), as every priority write
does.  The receive's arm runs the cancel once every check that can refuse it has
passed on the state it was handed (`dispatchWithCapChecked`'s `.receive` arm).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The thread a reply object is busy with, other than `tid`, as its code**
(`0` for none, `t + 1` for thread `t`) — seL4-MCS's `reply->replyTCB` when it is
not the receiver: the caller the reply is linked to, or the receiver that
stashed it and still waits (`Reply.stasherCode`, `replyStashedAt`). -/
@[inline] def busyReplyHolderCode (st : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : Nat :=
  match st.getReply? rid with
  | none => 0
  | some r =>
    match r.caller with
    | some c => if c = tid then 0 else c.val + 1
    | none =>
      if st.replyStashedAt rid r then
        if r.stasherCode = tid.val + 1 then 0 else r.stasherCode
      else 0

/-- **seL4-MCS `cancelIPC` on a reply's holder**: its IPC torn down as the
suspend tears it down (`suspendCancelRevert`: `cancelIpcKeepingContexts`, then
the boost it lent through the reply reverted) and the thread left `Inactive`. -/
def cancelReplyHolder (st : SystemState) (holder : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : SystemState :=
  match st.getTcb? holder with
  | none => st
  | some tcb =>
    (Lifecycle.Suspend.suspendCancelRevert st holder tcb executingCore).updateTcb holder
      fun t => { t with threadState := .Inactive }

/-- The holder's cancel writes no core's current slot. -/
theorem cancelReplyHolder_currentOnCore (st : SystemState) (holder : SeLe4n.ThreadId)
    (executingCore c : Concurrency.CoreId) :
    (cancelReplyHolder st holder executingCore).scheduler.currentOnCore c =
      st.scheduler.currentOnCore c := by
  unfold cancelReplyHolder
  split
  · rfl
  · rename_i tcb _
    rw [SystemState.updateTcb_scheduler]
    have hK : (Lifecycle.Suspend.cancelIpcKeepingContexts st holder tcb).scheduler.currentOnCore c =
        st.scheduler.currentOnCore c := by
      unfold Lifecycle.Suspend.cancelIpcKeepingContexts
      have hCut : (Lifecycle.Suspend.cutCancelledCallerHead st tcb).scheduler.currentOnCore c =
          st.scheduler.currentOnCore c :=
        Lifecycle.Suspend.cutCancelledCallerHead_closed
          (fun s => s.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
          (fun s s1 _ _ _ h _ _ hS => by
            show (SystemState.updateSchedContext s1 _ _).scheduler.currentOnCore c = _
            rw [SystemState.updateSchedContext_scheduler, storeObject_scheduler_eq s s1 _ _ hS]
            exact h)
          (fun s _ _ _ _ h _ _ _ => by
            dsimp only
            rw [markKeyChangeFrom_currentOnCore, SystemState.updateTcb_scheduler]; exact h)
          st tcb rfl
      rw [← hCut, Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq]
      rfl
    unfold Lifecycle.Suspend.suspendCancelRevert
    dsimp only
    split
    · rw [PriorityInheritance.propagatePipChainCrossCore_currentOnCore]; exact hK
    · exact hK

end SeLe4n.Kernel
