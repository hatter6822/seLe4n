-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM8.B: PRODUCTION.  The per-core priority-control transitions.  Enters
-- the production import closure through the live `.tcbSetPriority` /
-- `.tcbSetMCPriority` dispatch arms (`API.dispatchCapabilityOnly`).

import SeLe4n.Kernel.SchedContext.PriorityManagement
import SeLe4n.Kernel.Lifecycle.Suspend

/-!
# WS-SM SM8.B — per-core priority control

`setPriorityOp` and `setMCPriorityOp` (`SchedContext/PriorityManagement.lean`)
are the single-core priority-control transitions, and **both were boot-pinned in
two places**:

* the run-queue **bucket migration** read and wrote `runQueueOnCore bootCoreId`,
  so for a thread queued on a secondary core the membership test failed and the
  migration was a silent no-op — the priority field changed while the run
  queue's cached band did not, leaving the scheduler dispatching the thread at
  its **old** priority indefinitely (a demotion that never takes effect; the
  PIP-inversion case `migrateRunQueueBucket` exists to prevent, one core over);
* the **preemption check** read `currentOnCore bootCoreId`, so demoting a thread
  running on a secondary core never rescheduled that core.

`setPriorityOnCore` / `setMCPriorityOnCore` are the per-core forms, built like
their SM6.E sibling `suspendThreadOnCore`: the bucket migrates on the target's
**home** core (`determineTargetCore`), and the preemption gate is keyed on the
core that is **actually running** the target (`runningCoreOf?`, the SM6.E
review-4 resolution — an unbound thread can be current on a secondary core while
its home is the boot core), running inline when that is the executing core and
surfacing a `.reschedule` SGI when it is remote.

Every authority check, priority-source update and capping rule is shared with
the single-core transitions, so what changes is *where* the effects land.
-/

namespace SeLe4n.Kernel.SchedContext.PriorityManagement

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind bootCoreId)

/-- WS-SM SM8.B: the priority ops' preemption seam — the local/remote reschedule
decision, factored out so the SGI discipline is provable arm-by-arm.

* the target is not running anywhere: nothing to preempt;
* it is running on the **executing** core: reschedule inline, surface nothing;
* it is running on a **remote** core: surface that core's `.reschedule` SGI.

A raise never preempts (`shouldPreempt = false` at the call sites), so this fires
only where the target may have lost the core it holds. -/
def priorityRescheduleOnCore (st : SystemState) (running? : Option CoreId)
    (executingCore : CoreId) (shouldPreempt : Bool) :
    Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  if shouldPreempt then
    match running? with
    | some rc =>
        if rc == executingCore then
          match handleRescheduleSgiOnCore st executingCore with
          | .ok st' => .ok (st', none)
          | .error e => .error e
        else .ok (st, some (rc, SgiKind.reschedule))
    | none => .ok (st, none)
  else .ok (st, none)

/-- WS-SM SM8.B: every SGI this seam surfaces is a `.reschedule` for a core other
than the executing one — a local preemption is applied, never posted. -/
theorem priorityRescheduleOnCore_sgi_shape (st st' : SystemState)
    (running? : Option CoreId) (ec c : CoreId) (sp : Bool) (k : SgiKind)
    (h : priorityRescheduleOnCore st running? ec sp = .ok (st', some (c, k))) :
    k = SgiKind.reschedule ∧ c ≠ ec ∧ running? = some c := by
  unfold priorityRescheduleOnCore at h
  split at h
  · split at h
    · next rc _ =>
      split at h
      · split at h <;> simp_all
      · next hne =>
        rw [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hSgi⟩ := h
        simp only [Option.some.injEq, Prod.mk.injEq] at hSgi
        obtain ⟨hc, hk⟩ := hSgi
        subst hc; subst hk
        exact ⟨rfl, by simpa using hne, rfl⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- WS-SM SM8.B: a raise (or any non-preempting change) leaves the state alone
and surfaces nothing. -/
theorem priorityRescheduleOnCore_no_preempt (st : SystemState)
    (running? : Option CoreId) (ec : CoreId) :
    priorityRescheduleOnCore st running? ec false = .ok (st, none) := by
  simp [priorityRescheduleOnCore]

/-- WS-SM SM8.B (operation): **set a thread's priority, across cores.**

`setPriorityOp`'s per-core form.  Identical authority (`validatePriorityAuthority`
against the caller's MCP) and identical priority-source update; the two
boot-pinned effects are replaced:

* the bucket migrates on `determineTargetCore st vTargetTid.val` — the target's
  own home core, which is the queue it is actually in;
* the preemption gate is keyed on `runningCoreOf? st vTargetTid.val`, so a
  demotion of a thread running on a remote core surfaces that core's SGI instead
  of silently doing nothing.

Both cores are resolved from the **pre-state**, before the priority write, so
the transition acts on the placement it observed. -/
def setPriorityOnCore (st : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newPriority : SeLe4n.Priority) (executingCore : CoreId) :
    Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  match st.getTcb? vCallerTid.val with
  | some callerTcb =>
    match validatePriorityAuthority callerTcb newPriority with
    | .error e => .error e
    | .ok () =>
      match st.getTcb? vTargetTid.val with
      | some targetTcb =>
        let oldPriority := getCurrentPriority st targetTcb
        let home := determineTargetCore st vTargetTid.val
        let running? := Lifecycle.Suspend.runningCoreOf? st vTargetTid.val
        let st1 := updatePrioritySource st vTargetTid.val targetTcb newPriority
        let st2 := migrateRunQueueBucketOnCore st1 vTargetTid.val newPriority home
        priorityRescheduleOnCore st2 running? executingCore
          (decide (newPriority.val < oldPriority.val))
      | none => .error .invalidArgument
  | none => .error .invalidArgument

/-- WS-SM SM8.B (operation): **set a thread's maximum controlled priority, across
cores.**  `setMCPriorityOp`'s per-core form; the capping rule is unchanged, and
when the cap bites it re-buckets on the target's home core and preempts the core
actually running it. -/
def setMCPriorityOnCore (st : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newMCP : SeLe4n.Priority) (executingCore : CoreId) :
    Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  match st.getTcb? vCallerTid.val with
  | some callerTcb =>
    match validatePriorityAuthority callerTcb newMCP with
    | .error e => .error e
    | .ok () =>
      match st.getTcb? vTargetTid.val with
      | some targetTcb =>
        let targetTcb' := { targetTcb with maxControlledPriority := newMCP }
        let stMcp := { st with
          objects := st.objects.insert vTargetTid.val.toObjId (.tcb targetTcb') }
        let currentPrio := getCurrentPriority stMcp targetTcb'
        if currentPrio.val > newMCP.val then
          let home := determineTargetCore stMcp vTargetTid.val
          let running? := Lifecycle.Suspend.runningCoreOf? stMcp vTargetTid.val
          let st1 := updatePrioritySource stMcp vTargetTid.val targetTcb' newMCP
          let st2 := migrateRunQueueBucketOnCore st1 vTargetTid.val newMCP home
          priorityRescheduleOnCore st2 running? executingCore true
        else
          .ok (stMcp, none)
      | none => .error .invalidArgument
  | none => .error .invalidArgument

/-- WS-SM SM8.B: a rejected authority check leaves the state untouched — both
per-core ops are fail-closed, exactly as their single-core originals. -/
theorem setPriorityOnCore_authority_rejected (st : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) (callerTcb : TCB) (e : KernelError)
    (hCaller : st.getTcb? vCallerTid.val = some callerTcb)
    (hAuth : validatePriorityAuthority callerTcb newPriority = .error e) :
    setPriorityOnCore st vCallerTid vTargetTid newPriority executingCore = .error e := by
  simp [setPriorityOnCore, hCaller, hAuth]

theorem setMCPriorityOnCore_authority_rejected (st : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newMCP : SeLe4n.Priority)
    (executingCore : CoreId) (callerTcb : TCB) (e : KernelError)
    (hCaller : st.getTcb? vCallerTid.val = some callerTcb)
    (hAuth : validatePriorityAuthority callerTcb newMCP = .error e) :
    setMCPriorityOnCore st vCallerTid vTargetTid newMCP executingCore = .error e := by
  simp [setMCPriorityOnCore, hCaller, hAuth]

/-- WS-SM SM8.B: an absent caller is rejected before anything is read. -/
theorem setPriorityOnCore_no_caller (st : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) (hCaller : st.getTcb? vCallerTid.val = none) :
    setPriorityOnCore st vCallerTid vTargetTid newPriority executingCore
      = .error .invalidArgument := by
  simp [setPriorityOnCore, hCaller]

/-- WS-SM SM8.B: **a raise surfaces no SGI.**  Preemption is gated on the
priority strictly decreasing, so raising a thread's priority never posts one —
the higher band is picked up by the next scheduling decision on its own core. -/
theorem setPriorityOnCore_raise_no_sgi (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) (sgi : Option (CoreId × SgiKind)) (callerTcb targetTcb : TCB)
    (hCaller : st.getTcb? vCallerTid.val = some callerTcb)
    (hAuth : validatePriorityAuthority callerTcb newPriority = .ok ())
    (hTarget : st.getTcb? vTargetTid.val = some targetTcb)
    (hRaise : ¬ (newPriority.val < (getCurrentPriority st targetTcb).val))
    (hStep : setPriorityOnCore st vCallerTid vTargetTid newPriority executingCore
      = .ok (st', sgi)) :
    sgi = none := by
  simp only [setPriorityOnCore, hCaller, hAuth, hTarget] at hStep
  rw [show (decide (newPriority.val < (getCurrentPriority st targetTcb).val)) = false by
        simp [hRaise], priorityRescheduleOnCore_no_preempt] at hStep
  rw [Except.ok.injEq, Prod.mk.injEq] at hStep
  exact hStep.2.symm

end SeLe4n.Kernel.SchedContext.PriorityManagement
