-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Operations.Fault
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatch
import SeLe4n.Kernel.InformationFlow.Policy

/-!
# WS-RR RR4.12 — fault delivery across cores

The per-core lift of `faultDeliver`.  A thread faults on the core that was
executing it, and its handler may be waiting anywhere in the system, so the
delivery inherits both cross-core substitutions the SM6 IPC transitions use:

* the delivery **is** the live `.call` chain
  (`endpointCallCrossCoreDispatch`): the rendezvous, the SchedContext
  donation and the priority-inheritance walk, in the order the `.call`
  syscall arm runs them.  A remote handler is enqueued on **its own** core and
  the `.reschedule` SGI the runtime fires is surfaced;
* the reply is the live `.reply` chain (`endpointReplyCrossCoreDispatch`),
  which returns the donated SchedContext and reverts the boost;
* the faulting thread is descheduled on **its own** core
  (`removeRunnableOnCore … executingCore`), not on the boot core — the
  bootCore-pinned `faultSuspend` would leave a faulting secondary-core thread
  queued and current where it faulted, which is the multi-core shape of the
  very livelock RR4 exists to close.

Delivery is **total**: no error arm, and both dispositions leave the faulting
thread neither queued nor current on the core it faulted on
(`faultDeliverOnCore_leaves_thread_not_runnable`).

## One delivery, not two

There is deliberately **no** single-core `faultDeliver` beside this.  A
bootCore-pinned form would not be this transition's `bootCoreId` instance —
it would be a *different* transition, since the Call chain's donation and
priority-inheritance legs are per-core — and two fault deliveries that can
diverge is the same defect RR4.25 removes from `trap.rs`'s classification.
The core-independent pieces (handler resolution, the message, the
dispositions, the reply decode) live in `IPC/Operations/Fault.lean`, and
`faultSuspendOnCore … bootCoreId` really is `faultSuspend`.

## Why the whole Call chain and not the bare rendezvous

seL4's `sendFaultIPC` passes `canDonate = true` to `sendIPC`, so a fault
delivered to a **passive** handler donates the faulting thread's scheduling
context — that is how a passive fault handler runs at all.  Composing the
rendezvous alone would have left such a handler with no budget: the fault
message would arrive and nothing would execute, which is the RR4 livelock
with an extra step.  Composing the chain the `.call` arm already runs gets
the donation, the replenishment migration and the priority boost, and gets
their `ipcInvariantFull` preservation with them.

## Why the flow gate is here and not in the information-flow module (§5)

`faultDeliverOnCoreChecked` is the arm `Kernel/FaultEntry.lean` calls, so it
has to be **production**: the live syscall seam gates every endpoint operation
through `syscallEntryChecked`, and an ungated fault delivery would be the one
endpoint flow in the kernel that no policy can refuse.  It reads only
`InformationFlow/Policy.lean` — itself production, and below this module in
the import order — so the gate lives beside the transition it guards.  The
*non-interference* half (projection preservation, message independence) stays
in the staged `InformationFlow/FaultFlow.lean`, which composes the staged
cross-core call NI surface.
-/

namespace SeLe4n.Kernel

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  Per-core fail-closed dispositions
-- ============================================================================

/-- WS-RR RR4.12: the per-core generalisation of `faultSuspend` — deschedule
the thread on the core it faulted on and mark it `.Inactive`.

The `bootCoreId` instance is exactly the single-core form
(`faultSuspendOnCore_bootCoreId`), the SM5.A backward-compatibility bridge. -/
def faultSuspendOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    SystemState :=
  let st1 := removeRunnableOnCore st tid c
  match st1.getTcb? tid with
  | some tcb =>
      let updated : KernelObject := .tcb { tcb with threadState := .Inactive }
      { st1 with objects := st1.objects.insert tid.toObjId updated }
  | none => st1

/-- WS-RR RR4.12: at the boot core this is the single-core `faultSuspend`. -/
@[simp] theorem faultSuspendOnCore_bootCoreId (st : SystemState)
    (tid : SeLe4n.ThreadId) : faultSuspendOnCore st tid bootCoreId = faultSuspend st tid :=
  rfl

/-- WS-RR RR4.12: the per-core generalisation of `faultAbandon` — the
reply-declined disposition, retiring the answered fault. -/
def faultAbandonOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    SystemState :=
  let st1 := removeRunnableOnCore st tid c
  match st1.getTcb? tid with
  | some tcb =>
      let updated : KernelObject :=
        .tcb { tcb with threadState := .Inactive, pendingFault := none }
      { st1 with objects := st1.objects.insert tid.toObjId updated }
  | none => st1

/-- WS-RR RR4.12: and at the boot core, the single-core form. -/
@[simp] theorem faultAbandonOnCore_bootCoreId (st : SystemState)
    (tid : SeLe4n.ThreadId) : faultAbandonOnCore st tid bootCoreId = faultAbandon st tid :=
  rfl

/-- WS-RR RR4.12 (frame): the `.Inactive` store is an object write, so the
scheduler is exactly the deschedule's. -/
theorem faultSuspendOnCore_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) :
    (faultSuspendOnCore st tid c).scheduler = (removeRunnableOnCore st tid c).scheduler := by
  simp only [faultSuspendOnCore]
  cases (removeRunnableOnCore st tid c).getTcb? tid <;> simp

/-- WS-RR RR4.12 (frame): the same for the reply-declined disposition. -/
theorem faultAbandonOnCore_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) :
    (faultAbandonOnCore st tid c).scheduler = (removeRunnableOnCore st tid c).scheduler := by
  simp only [faultAbandonOnCore]
  cases (removeRunnableOnCore st tid c).getTcb? tid <;> simp

/-- WS-RR RR4.12: a suspended thread is out of **its own** core's run queue
and is not its current thread. -/
theorem faultSuspendOnCore_not_runnable (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) :
    tid ∉ (faultSuspendOnCore st tid c).scheduler.runQueueOnCore c ∧
    (faultSuspendOnCore st tid c).scheduler.currentOnCore c ≠ some tid := by
  rw [faultSuspendOnCore_scheduler_eq]
  exact ⟨removeRunnableOnCore_not_mem_self st tid c,
         removeRunnableOnCore_currentOnCore_ne_self st tid c⟩

/-- WS-RR RR4.12: and so is an abandoned one. -/
theorem faultAbandonOnCore_not_runnable (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) :
    tid ∉ (faultAbandonOnCore st tid c).scheduler.runQueueOnCore c ∧
    (faultAbandonOnCore st tid c).scheduler.currentOnCore c ≠ some tid := by
  rw [faultAbandonOnCore_scheduler_eq]
  exact ⟨removeRunnableOnCore_not_mem_self st tid c,
         removeRunnableOnCore_currentOnCore_ne_self st tid c⟩

-- ============================================================================
-- §2  RR4.12 — the cross-core delivery transition
-- ============================================================================

/-- WS-RR RR4.12: what a cross-core fault delivery produces alongside the
post-state — the disposition, and the optional SGI the runtime must fire once
the state is committed (the handler's home core, when the handler was woken on
a core other than the faulting one). -/
structure FaultDeliveryResult where
  /-- Delivered to a handler endpoint, or suspended fail-closed. -/
  disposition : FaultDisposition
  /-- The cross-core poke to fire after the commit, if any.  `none` on the
      suspend path: a thread that was descheduled on the core it faulted on
      needs no remote core told about it, and the executing core's own
      rescheduling is the trap path's business — exactly the posture the
      `.call` chain takes for its blocked caller. -/
  sgi : Option (CoreId × SgiKind) := none
  deriving Repr, DecidableEq, Inhabited

/-- WS-RR RR4.11/RR4.12 (**fault delivery**): send a thread's fault to its
handler from the core it faulted on, or fail closed.

seL4's `handleFault`, whole:

```c
void handleFault(tcb_t *tptr) {
    if (sendFaultIPC(tptr) != EXCEPTION_NONE) handleDoubleFault(tptr, fault);
}
```

`sendFaultIPC` resolves the handler capability, checks its rights, and issues
a **Call** carrying the fault message — which is exactly
`endpointCallCrossCoreDispatch`, the transition the live `.call` syscall arm
runs.  Every failure converges on `faultSuspendOnCore`.

**Total by construction.**  There is no error arm, so no caller can decline to
handle one, and both dispositions leave the thread not runnable on the core it
faulted on.  The Call chain returns the **pre-state** on its error arm, so the
suspend runs on the state the thread faulted in and no partial Call is ever
observable.

**On the ordering.** seL4 writes `tptr->tcbFault` *before* `sendIPC`; here the
record is applied to the post-state of each arm.  The two are observationally
identical — `pendingFault` is written only by this path and read only by the
fault reply, and no step inside the Call or the suspend reads it — and the
post-state form is what lets both arms' `ipcInvariantFull` preservation be a
composition of theorems that already exist
(`IPC/Invariant/FaultPreservation.lean`), rather than a re-proof of the Call's
whole precondition pack transported across an extra TCB write. -/
def faultDeliverOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault)
    (ctx : FaultContext) (executingCore : CoreId) :
    SystemState × FaultDeliveryResult :=
  let tf : ThreadFault := { fault := f, context := ctx }
  match resolveFaultHandler st tid with
  | .error _ =>
      (recordPendingFault (faultSuspendOnCore st tid executingCore) tid tf,
       { disposition := .suspended })
  | .ok tgt =>
      match endpointCallCrossCoreDispatch tgt.endpoint tid
          (faultMessage f ctx tgt.cap.badge) tgt.cap.rights tgt.cspaceRoot
          (SeLe4n.Slot.ofNat 0) executingCore st with
      | (_, .error _) =>
          (recordPendingFault (faultSuspendOnCore st tid executingCore) tid tf,
           { disposition := .suspended })
      | (st', .ok (_summary, sgi?)) =>
          (recordPendingFault st' tid tf,
           { disposition := .delivered tgt.endpoint, sgi := sgi? })

/-- WS-RR RR4.10: a fault whose handler does not resolve — for any reason —
takes the fail-closed path. -/
theorem faultDeliverOnCore_suspends_on_unresolvable (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext) (c : CoreId)
    (e : KernelError) (hErr : resolveFaultHandler st tid = .error e) :
    faultDeliverOnCore st tid f ctx c =
      (recordPendingFault (faultSuspendOnCore st tid c) tid { fault := f, context := ctx },
       { disposition := .suspended }) := by
  unfold faultDeliverOnCore; rw [hErr]

/-- WS-RR RR4.10 (**the negative**): a thread with no `faultHandler` suspends
on its own core. -/
theorem faultDeliverOnCore_suspends_without_handler (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext) (c : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hNone : tcb.faultHandler = none) :
    faultDeliverOnCore st tid f ctx c =
      (recordPendingFault (faultSuspendOnCore st tid c) tid { fault := f, context := ctx },
       { disposition := .suspended }) :=
  faultDeliverOnCore_suspends_on_unresolvable st tid f ctx c _
    (resolveFaultHandler_none_of_noHandler st tid tcb hTcb hNone)

/-- WS-RR RR4.12: the fail-closed path fires no SGI — nothing was woken. -/
theorem faultDeliverOnCore_suspended_no_sgi (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext) (c : CoreId)
    (e : KernelError) (hErr : resolveFaultHandler st tid = .error e) :
    (faultDeliverOnCore st tid f ctx c).2.sgi = none := by
  rw [faultDeliverOnCore_suspends_on_unresolvable st tid f ctx c e hErr]

/-- WS-RR RR4.11: the disposition is binary — the delivery either reached an
endpoint or suspended the thread.  There is no third outcome, and in
particular none that leaves the thread where it was. -/
theorem faultDeliverOnCore_disposition_total (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext) (c : CoreId) :
    (∃ epId, (faultDeliverOnCore st tid f ctx c).2.disposition = .delivered epId) ∨
    (faultDeliverOnCore st tid f ctx c).2.disposition = .suspended := by
  cases h : (faultDeliverOnCore st tid f ctx c).2.disposition with
  | delivered epId => exact Or.inl ⟨epId, rfl⟩
  | suspended => exact Or.inr rfl

/-- WS-RR RR4.11: a delivered fault went to the endpoint the thread's own
`faultHandler` capability names, and the post-state is the Call chain's with
the fault recorded.  The delivery adds nothing else — which is what lets
`faultDeliverOnCore_preserves_ipcInvariantFull` be a composition rather than a
re-proof. -/
theorem faultDeliverOnCore_delivered_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (f : Fault) (ctx : FaultContext) (c : CoreId) (tgt : FaultHandlerTarget)
    (st' : SystemState) (summary : CapTransferSummary)
    (sgi? : Option (CoreId × SgiKind))
    (hRes : resolveFaultHandler st tid = .ok tgt)
    (hCall : endpointCallCrossCoreDispatch tgt.endpoint tid
        (faultMessage f ctx tgt.cap.badge) tgt.cap.rights tgt.cspaceRoot
        (SeLe4n.Slot.ofNat 0) c st = (st', .ok (summary, sgi?))) :
    faultDeliverOnCore st tid f ctx c =
      (recordPendingFault st' tid { fault := f, context := ctx },
       { disposition := .delivered tgt.endpoint, sgi := sgi? }) := by
  unfold faultDeliverOnCore; rw [hRes]; simp only; rw [hCall]

-- ============================================================================
-- §3  RR4.13–RR4.15 — the fault reply
-- ============================================================================

/-- WS-RR RR4.14/RR4.15: apply a decoded reply outcome to the faulted thread —
restart it with the frame the handler chose, or leave it inactive.

An abandoned thread is descheduled on **its own** home core, not the replier's:
the reply chain woke it onto its home core, and the handler may be running
anywhere. -/
def faultReplyApplyOnCore (st : SystemState) (faulted : SeLe4n.ThreadId)
    (outcome : FaultReplyOutcome) : SystemState :=
  match outcome with
  | .restart frame => applyFaultRestart st faulted frame
  | .abandon       => faultAbandonOnCore st faulted (determineTargetCore st faulted)

/-- WS-RR RR4.13–RR4.15 (**the fault reply**): a handler answers the fault its
client is blocked on.

Three stages, in seL4's order (`doReplyTransfer`'s fault branch):

1. **decode** the reply against the fault the thread carries — the reason
   `TCB.pendingFault` exists, since nothing else on this path knows which
   fault is being answered;
2. **unblock** through the live `.reply` chain
   (`endpointReplyCrossCoreDispatch`), which brings three things with it: the
   replay barrier (only a thread still in `.blockedOnReply` with a recorded
   target is delivered, so a consumed reply cannot be answered twice), the
   **return of the donated SchedContext** the delivery lent a passive
   handler, and the reversion of the priority-inheritance boost;
3. **apply** the outcome: install the restart frame, or leave the thread
   inactive.

The delivered message is `IpcMessage.empty` — a fault reply's payload is
*registers*, not message registers, and the register writeback is stage 3.

**Where the authority is.**  This transition, like `endpointReplyOnCore`
beneath it, does **not** gate on the replier's identity: `replier` is carried
for the donation return and the audit record, not checked against the server
the Call recorded.  The authority to answer a fault is the **reply
capability** the fault Call linked (RR4.13): the live `.reply` dispatch arm
resolves the invoked reply object to its recorded `caller` and reaches this
transition only for that thread, so a thread that does not hold a capability
to the faulted thread's reply object cannot name it here.  A delegated reply
capability (copied or minted to another server) is legitimate authority, as it
is for every seL4-MCS reply — which is why the gate is the capability and not
the thread.  A direct below-API caller therefore has to bring its own
authorisation; the dispatch arm is the one that has it.

Fails `.illegalState` for a thread carrying no fault: that is the *ordinary*
reply's business, and answering it here would let a handler rewrite a
non-faulted thread's program counter. -/
def faultReplyOnCore (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (FaultReplyOutcome × Option (CoreId × SgiKind)) :=
  match st.getTcb? faulted with
  | none => (st, .error .objectNotFound)
  | some tcb =>
      match tcb.pendingFault with
      | none => (st, .error .illegalState)
      | some tf =>
          let outcome := decodeFaultReply tf.fault tf.context mi regs
          match endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty
              executingCore st with
          | (_, .error e) => (st, .error e)
          | (st', .ok sgi?) =>
              (faultReplyApplyOnCore st' faulted outcome, .ok (outcome, sgi?))

/-- WS-RR RR4.14: **a thread carrying no fault cannot be fault-replied to.**
The negative that keeps a handler from using the fault path to move an
arbitrary thread's program counter, and keeps a second reply from re-answering
a fault the first already retired (`applyFaultRestart` clears it). -/
theorem faultReplyOnCore_rejects_unfaulted (replier faulted : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (c : CoreId)
    (st : SystemState) (tcb : TCB)
    (hTcb : st.getTcb? faulted = some tcb) (hNone : tcb.pendingFault = none) :
    faultReplyOnCore replier faulted mi regs c st = (st, .error .illegalState) := by
  simp [faultReplyOnCore, hTcb, hNone]

/-- WS-RR RR4.14: and a thread that is not a TCB at all. -/
theorem faultReplyOnCore_rejects_nonThread (replier faulted : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (c : CoreId)
    (st : SystemState) (hNone : st.getTcb? faulted = none) :
    faultReplyOnCore replier faulted mi regs c st = (st, .error .objectNotFound) := by
  simp [faultReplyOnCore, hNone]

/-- WS-RR RR4.14: the outcome a `faultReplyOnCore` reports is exactly what the
carried fault decodes the reply to — the reply semantics are the decoder's,
and the transition adds nothing to them. -/
theorem faultReplyOnCore_outcome_eq (replier faulted : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (c : CoreId)
    (st st' : SystemState) (tcb : TCB) (tf : ThreadFault)
    (outcome : FaultReplyOutcome) (sgi? : Option (CoreId × SgiKind))
    (hTcb : st.getTcb? faulted = some tcb) (hFault : tcb.pendingFault = some tf)
    (hStep : faultReplyOnCore replier faulted mi regs c st = (st', .ok (outcome, sgi?))) :
    outcome = decodeFaultReply tf.fault tf.context mi regs := by
  unfold faultReplyOnCore at hStep
  rw [hTcb] at hStep
  simp only [hFault] at hStep
  split at hStep
  · exact absurd (congrArg Prod.snd hStep) (by simp)
  · have := congrArg Prod.snd hStep
    simp only at this
    exact (congrArg Prod.fst (Except.ok.inj this)).symm

/-- WS-RR RR4.14 (**resume**): a reply that overrides nothing restarts the
thread at the instruction that faulted, with the registers it had.  This is the
ordinary VM-fault answer: the handler mapped the page, the thread retries the
access — and it is a *resume after handler action*, which is exactly what
RR4.19 permits and the pre-RR4 abort path did without. -/
theorem faultReplyOnCore_resume_restores_faultIP (replier faulted : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (c : CoreId)
    (st st' : SystemState) (tcb : TCB) (tf : ThreadFault)
    (outcome : FaultReplyOutcome) (sgi? : Option (CoreId × SgiKind))
    (hTcb : st.getTcb? faulted = some tcb) (hFault : tcb.pendingFault = some tf)
    (hLabel : mi.label = 0) (hLen : mi.length = 0)
    (hStep : faultReplyOnCore replier faulted mi regs c st = (st', .ok (outcome, sgi?))) :
    outcome = .restart (faultRestartFrameOfContext tf.context) ∧
    outcome.restartPC? = some tf.context.faultIP := by
  have hOut := faultReplyOnCore_outcome_eq replier faulted mi regs c st st' tcb tf outcome
    sgi? hTcb hFault hStep
  rw [hOut, decodeFaultReply_resume_of_empty tf.fault tf.context mi regs hLabel hLen]
  exact ⟨rfl, rfl⟩

/-- WS-RR RR4.15 (**restart**): an unknown-syscall reply carrying a restart PC
moves the thread there instead — the thread does **not** resume at the
instruction that trapped. -/
theorem faultReplyOnCore_restart_moves_pc (replier faulted : SeLe4n.ThreadId)
    (n : UInt64) (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (c : CoreId)
    (st st' : SystemState) (tcb : TCB) (tf : ThreadFault)
    (outcome : FaultReplyOutcome) (sgi? : Option (CoreId × SgiKind))
    (hTcb : st.getTcb? faulted = some tcb) (hFault : tcb.pendingFault = some tf)
    (hKind : tf.fault = .unknownSyscall n)
    (hLabel : mi.label = 0) (hLen : 8 < mi.length) (hArr : 8 < regs.size)
    (hStep : faultReplyOnCore replier faulted mi regs c st = (st', .ok (outcome, sgi?))) :
    outcome.restartPC? = some (wordAt regs 8) := by
  have hOut := faultReplyOnCore_outcome_eq replier faulted mi regs c st st' tcb tf outcome
    sgi? hTcb hFault hStep
  rw [hOut, hKind]
  exact decodeFaultReply_unknownSyscall_restartPC n tf.context mi regs hLabel hLen hArr

/-- WS-RR RR4.15 (**abandon**): a nonzero reply label on a register-carrying
fault leaves the thread unrunnable — the handler's "do not continue", obeyed. -/
theorem faultReplyOnCore_abandon_not_runnable (replier faulted : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (c : CoreId)
    (st st' : SystemState) (tcb : TCB) (tf : ThreadFault)
    (outcome : FaultReplyOutcome) (sgi? : Option (CoreId × SgiKind))
    (hTcb : st.getTcb? faulted = some tcb) (hFault : tcb.pendingFault = some tf)
    (hLabel : mi.label ≠ 0)
    (hArm : (∃ n, tf.fault = .unknownSyscall n) ∨
            (∃ n c, tf.fault = .userException n c))
    (hStep : faultReplyOnCore replier faulted mi regs c st = (st', .ok (outcome, sgi?))) :
    outcome = .abandon ∧
    ∃ home : CoreId,
      faulted ∉ st'.scheduler.runQueueOnCore home ∧
      st'.scheduler.currentOnCore home ≠ some faulted := by
  have hOut := faultReplyOnCore_outcome_eq replier faulted mi regs c st st' tcb tf outcome
    sgi? hTcb hFault hStep
  have hAb : outcome = .abandon := by
    rw [hOut]
    exact decodeFaultReply_abandon_of_label tf.fault tf.context mi regs hLabel hArm
  refine ⟨hAb, ?_⟩
  unfold faultReplyOnCore at hStep
  rw [hTcb] at hStep
  simp only [hFault] at hStep
  split at hStep
  · exact absurd (congrArg Prod.snd hStep) (by simp)
  · rename_i stR sgiR hReply
    have hSt : faultReplyApplyOnCore stR faulted
        (decodeFaultReply tf.fault tf.context mi regs) = st' :=
      congrArg Prod.fst hStep
    have hOutR : decodeFaultReply tf.fault tf.context mi regs = .abandon := by
      rw [← hOut]; exact hAb
    refine ⟨determineTargetCore stR faulted, ?_, ?_⟩ <;>
      · rw [← hSt]
        simp only [faultReplyApplyOnCore, hOutR]
        first
          | exact (faultAbandonOnCore_not_runnable stR faulted _).1
          | exact (faultAbandonOnCore_not_runnable stR faulted _).2

-- ============================================================================
-- §4  RR4.14/RR4.15 — the reply seam: seL4's `doReplyTransfer` branch
-- ============================================================================

/-- WS-RR RR4.14: does this thread have an unanswered fault?

The predicate the reply path branches on.  It is exactly seL4's
`receiver->tcbFault != seL4_Fault_NullFault` test in `doReplyTransfer`, and it
is a **pre-state** read of the answered thread's own TCB. -/
def threadHasPendingFault (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  ((st.getTcb? tid).bind (·.pendingFault)).isSome

@[simp] theorem threadHasPendingFault_of_none (st : SystemState) (tid : SeLe4n.ThreadId)
    (h : st.getTcb? tid = none) : threadHasPendingFault st tid = false := by
  simp [threadHasPendingFault, h]

theorem threadHasPendingFault_eq_false_iff (st : SystemState) (tid : SeLe4n.ThreadId) :
    threadHasPendingFault st tid = false ↔
      ∀ tcb, st.getTcb? tid = some tcb → tcb.pendingFault = none := by
  unfold threadHasPendingFault
  cases hT : st.getTcb? tid with
  | none => simp
  | some tcb =>
      cases hF : tcb.pendingFault with
      | none => simp [hF]
      | some tf => simp [hF]

/-- WS-RR RR4.14/RR4.15 (**the reply seam**): seL4's `doReplyTransfer`, whose
first act is to ask whether the thread being answered is faulted.

```c
if (receiver->tcbFault == seL4_Fault_NullFault) {
    doIPCTransfer(...); setThreadState(receiver, ThreadState_Running);
} else {
    bool_t restart = handleFaultReply(receiver, sender);
    receiver->tcbFault = seL4_Fault_NullFault;
    setThreadState(receiver, restart ? ThreadState_Restart : ThreadState_Inactive);
}
```

Without this branch the fault reply mechanism is unreachable: a handler answers
with the ordinary `seL4_Reply` on the reply capability the fault Call gave it,
so if the reply path does not consult `tcbFault`, the answered thread is woken
`.ready` with its saved PC still addressing the instruction that faulted, its
fault never retired, and `decodeFaultReply` never consulted — RR4's livelock,
one step further along.

The two branches differ in what they leave behind, which is why the frame
staging is inside rather than after: an ordinary reply stages the delivered
message for the woken caller (WS-RA RA.B.5b), while a fault reply installs a
**restart frame** (or abandons the thread) and has no delivered message to
stage.  Both branches fail closed with the post-state discarded.

## What this seam does not yet cover

`.replyRecv` — the *idiomatic* server loop, and the one a real fault handler
would use — does **not** route through here.  `replyRecvBody` composes
`endpointReplyOnCore` with a receive leg and a donation return in one
transition, so the fault branch cannot simply be substituted for its reply
leg: a fault reply restarts or abandons the answered thread instead of
delivering to it, which changes what the receive leg and the donation return
are handed.  Until that lands, a handler must answer a fault with `.reply`
and take its next request with a separate `.receive`; a `.replyRecv` answer
reaches the ordinary path and wakes the faulted thread `.ready` at the
instruction that faulted.  Registered as debt in `docs/WORKSTREAM_HISTORY.md`
(WS-RR), closure target RR7 — stated here rather than left for a reader to
infer from the absence of a call. -/
def replyTransferOnCore (replier callerTid : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) : Except KernelError (Unit × SystemState) :=
  if threadHasPendingFault st callerTid then
    match faultReplyOnCore replier callerTid mi regs executingCore st with
    | (st', .ok _) => .ok ((), st')
    | (_, .error e) => .error e
  else
    match endpointReplyCrossCoreDispatch replier callerTid msg executingCore st with
    | (st', .ok _) => .ok ((), Architecture.stageDeliveredMessage st' callerTid 0)
    | (_, .error e) => .error e

/-- WS-RR RR4.14: on a thread carrying **no** fault the seam is exactly the
pre-RR4 reply arm — same dispatch, same frame staging, same errors.  This is
what lets every existing `.reply` theorem transfer with one pre-state
hypothesis rather than be re-proved. -/
theorem replyTransferOnCore_of_no_fault (replier callerTid : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (msg : IpcMessage)
    (c : CoreId) (st : SystemState)
    (hNoFault : threadHasPendingFault st callerTid = false) :
    replyTransferOnCore replier callerTid mi regs msg c st =
      (match endpointReplyCrossCoreDispatch replier callerTid msg c st with
       | (st', .ok _) => .ok ((), Architecture.stageDeliveredMessage st' callerTid 0)
       | (_, .error e) => .error e) := by
  simp [replyTransferOnCore, hNoFault]

/-- WS-RR RR4.15: and on a faulted thread it is the fault reply — the decode,
the restart-or-abandon, and no delivered-message staging. -/
theorem replyTransferOnCore_of_fault (replier callerTid : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (msg : IpcMessage)
    (c : CoreId) (st : SystemState)
    (hFault : threadHasPendingFault st callerTid = true) :
    replyTransferOnCore replier callerTid mi regs msg c st =
      (match faultReplyOnCore replier callerTid mi regs c st with
       | (st', .ok _) => .ok ((), st')
       | (_, .error e) => .error e) := by
  simp [replyTransferOnCore, hFault]

/-- WS-RR RR4.15: **a fault reply retires the fault it answered**, on both
outcomes — so a second reply through this seam takes the *ordinary* branch, and
`faultReplyOnCore_rejects_unfaulted` refuses it there.

Stated at the transition level rather than re-derived here: the restart arm's
clear is `applyFaultRestart_clears_pendingFault` and the abandon arm's is
`faultAbandonOnCore_clears_pendingFault`, both of which need the answered
thread's TCB and the object-store invariant at the *reply dispatch's* post-state
— facts a caller has and this seam does not.  The composed statement is
exercised end to end in `tests/FaultHandlingSuite.lean` §7 ("a second reply
finds no outstanding fault to answer"). -/
theorem replyTransferOnCore_fault_branch_applies (replier callerTid : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (msg : IpcMessage)
    (c : CoreId) (st stR st' : SystemState) (tcb : TCB) (tf : ThreadFault)
    (sgi? : Option (CoreId × SgiKind))
    (hTcb : st.getTcb? callerTid = some tcb)
    (hFault : tcb.pendingFault = some tf)
    (hRep : endpointReplyCrossCoreDispatch replier callerTid IpcMessage.empty c st
      = (stR, .ok sgi?))
    (hStep : replyTransferOnCore replier callerTid mi regs msg c st = .ok ((), st')) :
    st' = faultReplyApplyOnCore stR callerTid (decodeFaultReply tf.fault tf.context mi regs) := by
  have hHas : threadHasPendingFault st callerTid = true := by
    simp [threadHasPendingFault, hTcb, hFault]
  rw [replyTransferOnCore_of_fault replier callerTid mi regs msg c st hHas] at hStep
  unfold faultReplyOnCore at hStep
  rw [hTcb] at hStep
  simp only [hFault, hRep] at hStep
  exact (congrArg Prod.snd (Except.ok.inj hStep)).symm

/-- WS-RR RR4.14/RR4.15: the flow-checked twin of the reply seam, for the
`dispatchWithCapChecked` `.reply` arm.

Only the ordinary branch differs: it routes through
`endpointReplyCrossCoreDispatchChecked`.  The fault branch does **not** need a
second gate — the checked dispatch arm applies
`securityFlowsTo replier→caller` before reaching either branch, which is the
identical test `endpointReplyCrossCoreDispatchChecked` applies, so the two
coincide under it (`replyTransferOnCoreChecked_eq_unchecked_of_flow_allowed`). -/
def replyTransferOnCoreChecked (ctx : LabelingContext)
    (replier callerTid : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) : Except KernelError (Unit × SystemState) :=
  if threadHasPendingFault st callerTid then
    match faultReplyOnCore replier callerTid mi regs executingCore st with
    | (st', .ok _) => .ok ((), st')
    | (_, .error e) => .error e
  else
    match endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg executingCore st with
    | (st', .ok _) => .ok ((), Architecture.stageDeliveredMessage st' callerTid 0)
    | (_, .error e) => .error e

/-- WS-RR RR4.14: under the arm's own flow guard, checked and unchecked reply
transfer coincide — on **both** branches.  This is what keeps
`checkedDispatch_reply_eq_unchecked_when_allowed` a two-line proof after the
fault branch was added. -/
theorem replyTransferOnCoreChecked_eq_unchecked_of_flow_allowed (ctx : LabelingContext)
    (replier callerTid : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (msg : IpcMessage) (c : CoreId) (st : SystemState)
    (hAllow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf callerTid) = true) :
    replyTransferOnCoreChecked ctx replier callerTid mi regs msg c st
      = replyTransferOnCore replier callerTid mi regs msg c st := by
  unfold replyTransferOnCoreChecked replyTransferOnCore
  rw [endpointReplyCrossCoreDispatchChecked_flow_allowed ctx replier callerTid msg c st hAllow]

-- ============================================================================
-- §5  RR4.20 — the flow gate on fault delivery (the live arm)
-- ============================================================================

/-- WS-RR RR4.20: **fault delivery under the information-flow policy.**

The gate is `endpointFlowGate` on (faulting thread's label → handler
endpoint's label) — the same global-lattice-plus-endpoint-override check the
live `.call` arm applies, so a deployment that has forbidden a flow to some
endpoint does not find the kernel making it anyway on the fault path.

The destination label is `ctx.endpointLabelOf`, **not** `ctx.objectLabelOf`,
because that is what every other endpoint-keyed gate in the kernel reads
(`endpointCallCrossCoreDispatchChecked`, `endpointSendDualCrossCoreChecked`,
the four `Enforcement/Wrappers.lean` wrappers).  `LabelingContext` carries both
and a deployment may set them differently, so reading the wrong one would give
the fault path its own — possibly more permissive — view of the same
endpoint.

**A denied flow suspends the thread; it does not error.**  This is the whole
design point of the arm: an error would hand the trap layer a state in which
the faulting thread is still runnable at the faulting instruction, which is
exactly the livelock RR4.19 exists to remove — reintroduced through the policy
layer.  Fail-closed here means *contained*, not *reported*: the thread stops,
and its `pendingFault` records why for anything permitted to look. -/
def faultDeliverOnCoreChecked (ctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext)
    (executingCore : CoreId) : SystemState × FaultDeliveryResult :=
  match resolveFaultHandler st tid with
  | .error _ =>
      (recordPendingFault (faultSuspendOnCore st tid executingCore) tid
         { fault := f, context := fctx },
       { disposition := .suspended })
  | .ok tgt =>
      if endpointFlowGate ctx tgt.endpoint (ctx.threadLabelOf tid)
          (ctx.endpointLabelOf tgt.endpoint) then
        faultDeliverOnCore st tid f fctx executingCore
      else
        (recordPendingFault (faultSuspendOnCore st tid executingCore) tid
           { fault := f, context := fctx },
         { disposition := .suspended })

/-- WS-RR RR4.20 (**fail-closed**): a fault whose delivery the policy forbids
suspends the faulting thread — the message is not delivered, and the thread is
not resumed either. -/
theorem faultDeliverOnCoreChecked_flow_denied (ctx : LabelingContext)
    (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext)
    (c : CoreId) (tgt : FaultHandlerTarget)
    (hRes : resolveFaultHandler st tid = .ok tgt)
    (hDeny : endpointFlowGate ctx tgt.endpoint (ctx.threadLabelOf tid)
      (ctx.endpointLabelOf tgt.endpoint) = false) :
    faultDeliverOnCoreChecked ctx st tid f fctx c =
      (recordPendingFault (faultSuspendOnCore st tid c) tid { fault := f, context := fctx },
       { disposition := .suspended }) := by
  simp [faultDeliverOnCoreChecked, hRes, hDeny]

/-- WS-RR RR4.20: and the refused delivery leaves the thread not runnable —
the policy refusal inherits RR4.19's guarantee rather than punching a hole in
it. -/
theorem faultDeliverOnCoreChecked_denied_not_runnable (ctx : LabelingContext)
    (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext)
    (c : CoreId) (tgt : FaultHandlerTarget)
    (hRes : resolveFaultHandler st tid = .ok tgt)
    (hDeny : endpointFlowGate ctx tgt.endpoint (ctx.threadLabelOf tid)
      (ctx.endpointLabelOf tgt.endpoint) = false) :
    tid ∉ (faultDeliverOnCoreChecked ctx st tid f fctx c).1.scheduler.runQueueOnCore c ∧
    (faultDeliverOnCoreChecked ctx st tid f fctx c).1.scheduler.currentOnCore c
      ≠ some tid := by
  rw [faultDeliverOnCoreChecked_flow_denied ctx st tid f fctx c tgt hRes hDeny]
  simp only [recordPendingFault_scheduler_eq]
  exact faultSuspendOnCore_not_runnable st tid c

/-- WS-RR RR4.20: when the policy permits the flow, the checked delivery is
exactly the unchecked one — the gate is a pure precondition, adding nothing to
the transition it guards. -/
theorem faultDeliverOnCoreChecked_flow_allowed (ctx : LabelingContext)
    (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext)
    (c : CoreId) (tgt : FaultHandlerTarget)
    (hRes : resolveFaultHandler st tid = .ok tgt)
    (hAllow : endpointFlowGate ctx tgt.endpoint (ctx.threadLabelOf tid)
      (ctx.endpointLabelOf tgt.endpoint) = true) :
    faultDeliverOnCoreChecked ctx st tid f fctx c = faultDeliverOnCore st tid f fctx c := by
  simp [faultDeliverOnCoreChecked, hRes, hAllow]

/-- WS-RR RR4.20: a delivery the checked arm performed had its flow admitted
by the **global lattice**, not merely by an endpoint override — the gate's
shape guarantees it, so no misconfigured endpoint policy can widen the
lattice on the fault path. -/
theorem faultDeliverOnCoreChecked_delivered_flows (ctx : LabelingContext)
    (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext)
    (c : CoreId) (tgt : FaultHandlerTarget) (epId : SeLe4n.ObjId)
    (hRes : resolveFaultHandler st tid = .ok tgt)
    (hDelivered : (faultDeliverOnCoreChecked ctx st tid f fctx c).2.disposition
      = .delivered epId) :
    securityFlowsTo (ctx.threadLabelOf tid) (ctx.endpointLabelOf tgt.endpoint) = true := by
  by_cases hGate : endpointFlowGate ctx tgt.endpoint (ctx.threadLabelOf tid)
      (ctx.endpointLabelOf tgt.endpoint) = true
  · exact endpointFlowGate_implies_securityFlowsTo ctx tgt.endpoint _ _ hGate
  · rw [faultDeliverOnCoreChecked_flow_denied ctx st tid f fctx c tgt hRes
      (by simpa using hGate)] at hDelivered
    exact absurd hDelivered (by simp)

end SeLe4n.Kernel
