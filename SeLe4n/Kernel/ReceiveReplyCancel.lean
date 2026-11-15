/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.RefusalCarryingEntry
import SeLe4n.Kernel.IPC.CrossCore.SuspendAdmission
import SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation

/-!
# The busy-reply cancel of a receive

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
stashed it and waits `BlockedOnReceive`) and leaves it `Inactive`.  The receive
then runs with the reply free and cannot fail.

The cancel is `cancelIPC` alone (`cancelReplyHolder`): the suspend's IPC
teardown (`suspendCancelRevert` — seL4's `cancelIPC`, the reply arm
`reply_remove_tcb`, with the boost the holder lent through the reply reverted)
and the `Inactive` write.  None of the rest of `suspend` runs (no dequeue, no
release-queue removal, no yield cancel) and no scheduling point: seL4's
`receiveIPC` runs none, and the receive that follows is the receiver's, on the
core it is current on.  A boost the revert takes off a thread leaves the
scheduling point owed on its core (`markKeyChangeFor`), as every priority write
does.

**Every refusal precedes the cancel.**  `receiveBusyHolderCode` asks, of the
state the receive is handed, every check the receive makes before its reply is
free — the caller current and not idle, the operand capability resolved, held,
an endpoint the receive accepts with the right it needs, the endpoint's flow
gate, the reply capability resolved with the write right — and the cancel's own
flow, from the receiver to the thread it cancels, which the reply capability
the receiver presents authorises.  Only then is the holder cancelled, in place,
with no copy and no rollback, as seL4's `cancelIPC` is committed; the receive is
then run on the cancelled state (`Platform.FFI.syscallDispatchFromAbi`), so a
refusal after the cancel, which no state meeting the invariants reaches,
reports the cancelled state in the specification and the compiled kernel alike.
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

/-- The busy holder of the reply capability in slot `cnode`/`slot`, as
`recvReplyCapK` reads the slot: present, not a reserved object's, carrying the
write right, a reply capability. -/
@[inline] def replySlotBusyHolderCode (st : SystemState) (tid : SeLe4n.ThreadId)
    (cap? : Option Capability) : Nat :=
  match cap? with
  | none => 0
  | some cap =>
    if capTargetsReservedKernelObject cap then 0
    else if !cap.hasRight .write then 0
    else
      match cap.target with
      | .replyCap rid => busyReplyHolderCode st tid rid
      | _ => 0

/-- The busy holder of the reply capability at `replyAddr` in `tid`'s CSpace,
resolved as `resolveRecvReplyK` resolves it. -/
@[inline] def recvReplyBusyHolderCode (st : SystemState) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr) : Nat :=
  match callerCspaceRoot st tid with
  | none => 0
  | some root =>
    lookupSlotFromK root replyAddr st (fun _ _ _ _ => 0) (fun cnode slot =>
      replySlotBusyHolderCode st tid
        (SystemState.lookupSlotCap st { cnode := cnode, slot := slot }))

/-- The receive's checks on the capability in its operand slot, then the busy
holder of its reply: held, not a reserved object's, refused neither at its type
nor its right, an endpoint whose flow gate admits the receive, and the cancel's
flow from the receiver to the holder. -/
@[inline] def receiveOperandBusyHolderCode (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr) (st : SystemState) (c : Option Capability) : Nat :=
  match c with
  | none => 0
  | some cap =>
    if capTargetsReservedKernelObject cap then 0
    else if receiveGateRefuses .receive tid st cap then 0
    else
      match cap.target with
      | .object epId =>
        if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then 0
        else
          let h := recvReplyBusyHolderCode st tid replyAddr
          if h = 0 then 0
          else if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf ⟨h - 1⟩) then h
          else 0
      | _ => 0

/-- **The thread a receive's busy reply cancels, as its code** (`0` for none):
the checks of `syscallEntryRoutedWith` and of the receive's routed arm, each
read from the state the receive is handed, then the busy holder of the reply
the receive names.  Out of line with the state borrowed: a query, it builds
nothing. -/
@[noinline] def receiveBusyHolderCode (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (st : @& SystemState) : Nat :=
  if isInsecureDefaultContext ctx then 0 else
  match st.scheduler.currentOnCore executingCore with
  | none => 0
  | some tid =>
    if isIdleThreadId tid then 0 else
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) =>
      match Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
          tcb.registerContext 32 with
      | .receive capAddr len replyAddr =>
        if len = 0 then 0 else
        lookupSlotK tcb capAddr st (fun _ _ _ _ => 0) (fun cnode slot =>
          receiveOperandBusyHolderCode ctx tid replyAddr st
            (SystemState.lookupSlotCap st { cnode := cnode, slot := slot }))
      | _ => 0
    | _ => 0

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

/-- **The busy-reply cancel** (seL4-MCS `receiveIPC`'s `cancelIPC(replyTCB)`):
the holder `receiveBusyHolderCode` names cancelled in place
(`cancelReplyHolder`); the state as it was when there is none. -/
@[inline] def cancelReceiveBusyReply (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (st : SystemState) : SystemState :=
  match receiveBusyHolderCode ctx executingCore st with
  | 0 => st
  | k + 1 => cancelReplyHolder st ⟨k⟩ executingCore

/-- The cancel is the identity or `cancelReplyHolder` of the holder it names. -/
theorem cancelReceiveBusyReply_cases (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (st : SystemState) :
    cancelReceiveBusyReply ctx executingCore st = st ∨
    ∃ k, receiveBusyHolderCode ctx executingCore st = k + 1 ∧
      cancelReceiveBusyReply ctx executingCore st = cancelReplyHolder st ⟨k⟩ executingCore := by
  unfold cancelReceiveBusyReply
  split
  · exact Or.inl rfl
  · rename_i k hk
    exact Or.inr ⟨k, hk, rfl⟩

/-- A property every holder's cancel keeps is kept by the busy-reply cancel. -/
theorem cancelReceiveBusyReply_preserves {P : SystemState → Prop}
    (ctx : LabelingContext) (executingCore : Concurrency.CoreId) (st : SystemState)
    (hC : ∀ holder, P (cancelReplyHolder st holder executingCore))
    (hP : P st) : P (cancelReceiveBusyReply ctx executingCore st) := by
  rcases cancelReceiveBusyReply_cases ctx executingCore st with h | ⟨k, -, h⟩
  · rw [h]; exact hP
  · rw [h]; exact hC _

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model

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

/-- The busy-reply cancel writes no core's current slot. -/
theorem cancelReceiveBusyReply_currentOnCore (ctx : LabelingContext)
    (executingCore c : Concurrency.CoreId) (st : SystemState) :
    (cancelReceiveBusyReply ctx executingCore st).scheduler.currentOnCore c =
      st.scheduler.currentOnCore c :=
  cancelReceiveBusyReply_preserves (P := fun s => s.scheduler.currentOnCore c =
      st.scheduler.currentOnCore c) ctx executingCore st
    (fun h => cancelReplyHolder_currentOnCore st h executingCore c) rfl

end SeLe4n.Kernel
