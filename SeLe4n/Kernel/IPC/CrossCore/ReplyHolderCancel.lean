-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.BusyReplyHolder
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

`busyReplyHolderCode` (`IPC/BusyReplyHolder.lean`) names that thread; `cancelReplyHolder` is `cancelIPC` on
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

/-- **seL4-MCS `cancelIPC` on a reply's holder**: a blocked holder has its IPC
torn down as the suspend tears it down (`suspendCancelRevert`:
`cancelIpcKeepingContexts`, then the boost it lent through the reply reverted)
and is left `Inactive`; a holder that is not blocked is left as it is, as
`cancelIPC` leaves a thread in no blocking state.  The holder is resolved as
every cancel resolves its thread (`lookupTcb`): the reserved id is the model's
null thread, which seL4's `replyTCB != NULL` test never cancels.  The blocking
question is asked of the state's codes (`ipcStateCode`, `ipcObjectCode`), so no
state record is built for it. -/
def cancelReplyHolder (st : SystemState) (holder : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : SystemState :=
  match lookupTcb st holder with
  | none => st
  | some tcb =>
    if tcb.ipcStateCode == 0 && tcb.ipcObjectCode == 0 then st
    else
      (Lifecycle.Suspend.suspendCancelRevert st holder tcb executingCore).updateTcb holder
        fun t => { t with threadState := .Inactive }

/-- The holder's cancel is the identity, or the blocked holder's teardown. -/
theorem cancelReplyHolder_cases (st : SystemState) (holder : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) :
    cancelReplyHolder st holder executingCore = st ∨
      ∃ tcb, lookupTcb st holder = some tcb ∧ tcb.ipcState ≠ .ready ∧
        cancelReplyHolder st holder executingCore =
          (Lifecycle.Suspend.suspendCancelRevert st holder tcb executingCore).updateTcb holder
            fun t => { t with threadState := .Inactive } := by
  unfold cancelReplyHolder
  split
  · exact Or.inl rfl
  · rename_i tcb hT
    split
    · exact Or.inl rfl
    · rename_i hB
      refine Or.inr ⟨tcb, hT, fun hR => hB ?_, rfl⟩
      obtain ⟨h1, h2⟩ := (TCB.ipcState_eq_iff_codes tcb .ready).mp hR
      simp [h1, h2, ThreadIpcState.objectCode, ThreadIpcState.stateCode]

/-- The holder's cancel writes no core's current slot. -/
theorem cancelReplyHolder_currentOnCore (st : SystemState) (holder : SeLe4n.ThreadId)
    (executingCore c : Concurrency.CoreId) :
    (cancelReplyHolder st holder executingCore).scheduler.currentOnCore c =
      st.scheduler.currentOnCore c := by
  rcases cancelReplyHolder_cases st holder executingCore with h | ⟨tcb, -, -, h⟩
  · rw [h]
  · rw [h, SystemState.updateTcb_scheduler]
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

/-- The holder's cancel moves no reservation: the IPC cancel writes objects and
the key hook's flags, the revert re-buckets run queues, the `Inactive` write is
a TCB's. -/
theorem cancelReplyHolder_replenishQueueOnCore (st : SystemState) (holder : SeLe4n.ThreadId)
    (executingCore c : Concurrency.CoreId) :
    (cancelReplyHolder st holder executingCore).scheduler.replenishQueueOnCore c =
      st.scheduler.replenishQueueOnCore c := by
  rcases cancelReplyHolder_cases st holder executingCore with h | ⟨tcb, -, -, h⟩
  · rw [h]
  · rw [h, SystemState.updateTcb_scheduler]
    have hK : (Lifecycle.Suspend.cancelIpcKeepingContexts st holder tcb).scheduler.replenishQueueOnCore c =
        st.scheduler.replenishQueueOnCore c := by
      unfold Lifecycle.Suspend.cancelIpcKeepingContexts
      rw [← Lifecycle.Suspend.cutCancelledCallerHead_replenishQueueOnCore st tcb c,
        Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq]; rfl
    unfold Lifecycle.Suspend.suspendCancelRevert
    dsimp only
    split
    · rw [PriorityInheritance.propagatePipChainCrossCore_replenishQueueOnCore]; exact hK
    · exact hK

end SeLe4n.Kernel
