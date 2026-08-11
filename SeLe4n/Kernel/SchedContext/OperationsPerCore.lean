-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM8.B: PRODUCTION.  The per-core SchedContext operations.  Enters the
-- production import closure through the live `.schedContextUnbind` dispatch arm
-- (`API.dispatchCapabilityOnly`).

import SeLe4n.Kernel.SchedContext.Operations
import SeLe4n.Kernel.SchedContext.PriorityManagementPerCore

/-!
# WS-SM SM8.B — per-core SchedContext operations

`schedContextUnbind` (`SchedContext/Operations.lean`) revokes a thread's
SchedContext, which **demotes it** to its legacy TCB priority.  Its Z5-H1
preemption guard cleared the thread's `current` slot "to force rescheduling",
and PR #861 review round 14 added the requeue that clearing `current` had been
missing.  Neither is a scheduling point:

* `syscallDispatchCrossCoreEntry` performs no local scheduling — it commits the
  verified post-state and fires the *diff-recovered* SGIs;
* `crossCoreSgiBody` deliberately emits nothing for the **executing** core,
  because a local reschedule is supposed to have run inline.

So a thread that unbound its own SchedContext returned to userspace still
executing while the model said its core had no current thread.  On its next
syscall `determineExecutingCore` scans for a core whose `current` is that
thread, finds none, and falls back to `bootCoreId` (`EndpointCallDispatch.lean`
— `determineExecutingCore_sound` states exactly this disjunction), so every
subsequent blocking or scheduling effect targets the wrong core.  Found by
PR #861 review round 15.

`schedContextUnbindOnCore` is the per-core form, built like its siblings
`suspendThreadOnCore` (SM6.E) and `setPriorityOnCore`: it resolves the core
**actually running** the demoted thread from the pre-state (`runningCoreOf?`,
not the queue home — the two diverge, which is why SM6.E introduced it) and
runs the shared preemption seam `priorityRescheduleOnCore`, rescheduling inline
when that core is the executing one and surfacing its `.reschedule` SGI when it
is remote.

Delegating to the scheduler rather than hand-editing `current` is what makes
this correct: `handleRescheduleSgiOnCore` re-selects against the **post-unbind**
priority and switches only if a candidate outranks it (`switchToThreadOnCore`
requeues the outgoing thread through `preemptCurrentOnCore`), so the demoted
thread either keeps its core legitimately or is preempted and queued — never
stranded, and never running a thread the model has forgotten.
-/

namespace SeLe4n.Kernel.SchedContextOps

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind bootCoreId)

/-- WS-SM SM8.B: the thread a SchedContext's scheduler effects act on — its
bound thread, read from the pre-state.

Single-sourced here in production because two consumers need it and a second
copy would drift: this module resolves the core to reschedule, and the
information-flow write set `schedContextWriteSet`
(`InformationFlow/NonInterferenceCrossCore.lean`) resolves the core to declare.
Both must name the same thread or the declared bound is not the transition's. -/
def schedContextBoundThread? (st : SystemState) (scObjId : SeLe4n.ObjId) :
    Option SeLe4n.ThreadId :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) with
  | some sc => sc.boundThread
  | none    => none

/-- WS-SM SM8.B: the core actually running the SchedContext's bound thread, if
any — the core whose scheduling decision the unbind invalidates. -/
def schedContextRunningCore? (st : SystemState) (scObjId : SeLe4n.ObjId) :
    Option CoreId :=
  match schedContextBoundThread? st scObjId with
  | some tid => Lifecycle.Suspend.runningCoreOf? st tid
  | none     => none

/-- WS-SM SM8.B (operation): **unbind a SchedContext, across cores.**

`schedContextUnbind`'s per-core form.  The revocation itself is unchanged — same
authority, same object writes, same home-core requeue — and what is added is the
scheduling point the single-core form never had: the core running the demoted
thread re-runs its scheduler, inline when it is the executing core and via a
`.reschedule` SGI when it is remote.

The running core is resolved from the **pre-state**, before the demotion, so the
transition acts on the placement it observed. -/
def schedContextUnbindOnCore (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (st : SystemState) : Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  let running? := schedContextRunningCore? st vScId.val
  match schedContextUnbind vScId st with
  | .error e      => .error e
  | .ok ((), st') =>
      SchedContext.PriorityManagement.priorityRescheduleOnCore st' running? executingCore true

/-- WS-SM SM8.B: the per-core wrapper is fail-closed — it rejects exactly what
the single-core transition rejects, and adds no state change on the error path. -/
theorem schedContextUnbindOnCore_error (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st : SystemState) (e : KernelError)
    (hStep : schedContextUnbind vScId st = .error e) :
    schedContextUnbindOnCore vScId executingCore st = .error e := by
  simp [schedContextUnbindOnCore, hStep]

/-- WS-SM SM8.B: a SchedContext whose bound thread is running **nowhere** needs
no scheduling point, and the wrapper is then exactly the single-core transition:
same state, no SGI.  This is also the single-core bridge — on one core a thread
is current on `bootCoreId` or nowhere, so the boot-pinned
`syscallDispatchInner` path sees no change of behaviour. -/
theorem schedContextUnbindOnCore_no_running_core (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st st' : SystemState)
    (hRunning : schedContextRunningCore? st vScId.val = none)
    (hStep : schedContextUnbind vScId st = .ok ((), st')) :
    schedContextUnbindOnCore vScId executingCore st = .ok (st', none) := by
  simp [schedContextUnbindOnCore, hRunning, hStep,
        SchedContext.PriorityManagement.priorityRescheduleOnCore]

/-- WS-SM SM8.B: **every SGI this operation surfaces is a `.reschedule` for a
core other than the executing one**, and that core is genuinely the one running
the demoted thread.  A local preemption is applied inline, never posted. -/
theorem schedContextUnbindOnCore_sgi_shape (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st st' : SystemState) (c : CoreId) (k : SgiKind)
    (hStep : schedContextUnbindOnCore vScId executingCore st = .ok (st', some (c, k))) :
    k = SgiKind.reschedule ∧ c ≠ executingCore
      ∧ schedContextRunningCore? st vScId.val = some c := by
  unfold schedContextUnbindOnCore at hStep
  simp only [] at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next u stMid hUnbind =>
    exact SchedContext.PriorityManagement.priorityRescheduleOnCore_sgi_shape
      stMid st' _ executingCore c true k hStep

/-- WS-SM SM8.B: the demoted thread's core is **rescheduled, not merely
cleared** — when it is the executing core the handler runs inline, so the
post-state's `current` slot is the scheduler's own decision rather than the
`none` the Z5-H1 guard used to leave behind. -/
theorem schedContextUnbindOnCore_local_reschedules (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st stMid st' : SystemState)
    (hRunning : schedContextRunningCore? st vScId.val = some executingCore)
    (hUnbind : schedContextUnbind vScId st = .ok ((), stMid))
    (hStep : schedContextUnbindOnCore vScId executingCore st = .ok (st', none)) :
    handleRescheduleSgiOnCore stMid executingCore = .ok st' := by
  unfold schedContextUnbindOnCore at hStep
  simp only [hRunning, hUnbind,
             SchedContext.PriorityManagement.priorityRescheduleOnCore] at hStep
  simp only [beq_self_eq_true, if_true] at hStep
  split at hStep
  · next st'' h => rw [Except.ok.injEq, Prod.mk.injEq] at hStep; rw [h, hStep.1]
  · exact absurd hStep (by simp)

end SeLe4n.Kernel.SchedContextOps
