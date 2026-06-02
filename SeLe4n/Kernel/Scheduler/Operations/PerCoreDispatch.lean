-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick
import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdle

/-!
# WS-SM SM5.E — Per-core idle-aware dispatcher (the SM5.I dispatch-loop seed)

Establishment theorems for the production `scheduleOrIdleOnCore`
(`Scheduler/Operations/Core.lean`) — the per-core dispatcher that runs core `c`'s
**idle thread** when nothing else is runnable, instead of leaving the core at
`current = none`.  It layers on the SM5.D budget-aware selector
`scheduleEffectiveOnCore`; these theorems compose `scheduleEffectiveOnCore`'s
establishment surface (SM5.D) with the idle-dispatch case, so the mature SM5.D /
`timerTickOnCore` proof base is untouched.

* **Headline (`scheduleOrIdleOnCore_runs_idle`)** — when the selector goes idle
  and core `c`'s idle thread is *dispatchable* (installed + in-domain), the result
  has `current = some (idleThreadId c)`: idle is genuinely dispatched in a
  production transition.
* **Soundness** — the result satisfies `currentThreadValidOnCore`,
  `queueCurrentConsistentOnCore`, `objects.invExt`, and `runQueueOnCoreWellFormed`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §0  `dispatchIdleOnCore` frame lemmas (touches only scheduler + machine.regs)
-- ============================================================================

/-- WS-SM SM5.E: dispatching idle sets core `c`'s current thread to the idle
thread. -/
@[simp] theorem dispatchIdleOnCore_currentOnCore (st : SystemState) (c : CoreId) :
    (dispatchIdleOnCore st c).scheduler.currentOnCore c = some (idleThreadId c) := by
  simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_currentOnCore_self]

/-- WS-SM SM5.E: dispatching idle does not touch the object store (only the
run-queue slot, the current slot, and `machine.regs`). -/
@[simp] theorem dispatchIdleOnCore_objects (st : SystemState) (c : CoreId) :
    (dispatchIdleOnCore st c).objects = st.objects := by
  simp only [dispatchIdleOnCore, restoreIncomingContext_objects]

/-- WS-SM SM5.E: after dispatching idle, core `c`'s run queue is the old one with
the idle thread removed (dequeue-on-dispatch). -/
theorem dispatchIdleOnCore_runQueueOnCore (st : SystemState) (c : CoreId) :
    (dispatchIdleOnCore st c).scheduler.runQueueOnCore c
      = (st.scheduler.runQueueOnCore c).remove (idleThreadId c) := by
  simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_runQueueOnCore,
    restoreIncomingContext_scheduler, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]

/-- WS-SM SM5.E: dispatching idle frames core `c`'s active domain. -/
@[simp] theorem dispatchIdleOnCore_activeDomainOnCore (st : SystemState) (c : CoreId) :
    (dispatchIdleOnCore st c).scheduler.activeDomainOnCore c
      = st.scheduler.activeDomainOnCore c := by
  simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_activeDomainOnCore,
    restoreIncomingContext_scheduler, SchedulerState.setRunQueueOnCore_activeDomainOnCore]

/-- WS-SM SM5.E: dispatching idle leaves every thread's TCB resolution unchanged
(the object store is untouched). -/
theorem dispatchIdleOnCore_getTcb? (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    (dispatchIdleOnCore st c).getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?
  rw [dispatchIdleOnCore_objects]

-- ============================================================================
-- §1  Headline: idle is dispatched in a production transition
-- ============================================================================

/-- WS-SM SM5.E (the headline — *idle is dispatched in production*): when the
budget-aware selector finds nothing runnable on core `c` (`current = none`) and
core `c`'s idle thread is dispatchable (installed + in-domain), the idle-aware
dispatcher runs the idle thread — the result has `current = some (idleThreadId c)`.
This is the live production realisation of plan §4.3 ("idle is always a
fallback"): a core with nothing else to do runs its idle TCB rather than sitting
at `current = none`. -/
theorem scheduleOrIdleOnCore_runs_idle (st : SystemState) (c : CoreId) (st' st'' : SystemState)
    (hEff : scheduleEffectiveOnCore st c = .ok st')
    (hcur : st'.scheduler.currentOnCore c = none)
    (hDisp : idleDispatchableOnCore st' c = true)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    st''.scheduler.currentOnCore c = some (idleThreadId c) := by
  unfold scheduleOrIdleOnCore at hStep
  simp only [hEff, hcur] at hStep
  rw [if_pos hDisp] at hStep
  simp only [Except.ok.injEq] at hStep
  subst hStep
  exact dispatchIdleOnCore_currentOnCore st' c

-- ============================================================================
-- §2  Soundness: the idle-aware dispatcher preserves the per-core invariants
-- ============================================================================

/-- WS-SM SM5.E (soundness): `scheduleOrIdleOnCore` preserves the object-store
RobinHood invariant — the idle dispatch touches only the scheduler + `machine.regs`,
and the busy / not-dispatchable cases inherit `scheduleEffectiveOnCore`'s. -/
theorem scheduleOrIdleOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (st'' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') : st''.objects.invExt := by
  unfold scheduleOrIdleOnCore at hStep
  cases hEff : scheduleEffectiveOnCore st c with
  | error e => rw [hEff] at hStep; simp at hStep
  | ok st' =>
    rw [hEff] at hStep
    have hEffInv := scheduleEffectiveOnCore_preserves_objects_invExt st c st' hInv hEff
    cases hcur : st'.scheduler.currentOnCore c with
    | some t => simp only [hcur, Except.ok.injEq] at hStep; subst hStep; exact hEffInv
    | none =>
      simp only [hcur] at hStep
      split at hStep
      · simp only [Except.ok.injEq] at hStep; subst hStep
        rw [dispatchIdleOnCore_objects]; exact hEffInv
      · simp only [Except.ok.injEq] at hStep; subst hStep; exact hEffInv

/-- WS-SM SM5.E (soundness): `scheduleOrIdleOnCore` establishes core `c`'s
current-thread validity — the idle case resolves to the (installed) idle TCB; the
busy / not-dispatchable cases inherit `scheduleEffectiveOnCore`'s establishment. -/
theorem scheduleOrIdleOnCore_establishes_currentThreadValidOnCore (st : SystemState) (c : CoreId)
    (st'' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') : currentThreadValidOnCore st'' c := by
  unfold scheduleOrIdleOnCore at hStep
  cases hEff : scheduleEffectiveOnCore st c with
  | error e => rw [hEff] at hStep; simp at hStep
  | ok st' =>
    rw [hEff] at hStep
    have hEffVal := scheduleEffectiveOnCore_establishes_currentThreadValidOnCore st c st' hInv hEff
    cases hcur : st'.scheduler.currentOnCore c with
    | some t => simp only [hcur, Except.ok.injEq] at hStep; subst hStep; exact hEffVal
    | none =>
      simp only [hcur] at hStep
      split at hStep
      · rename_i hd
        simp only [Except.ok.injEq] at hStep; subst hStep
        unfold currentThreadValidOnCore
        simp only [dispatchIdleOnCore_currentOnCore, dispatchIdleOnCore_getTcb?]
        unfold idleDispatchableOnCore at hd
        cases hres : st'.getTcb? (idleThreadId c) with
        | none => rw [hres] at hd; simp at hd
        | some idleTcb => exact ⟨idleTcb, rfl⟩
      · simp only [Except.ok.injEq] at hStep; subst hStep; exact hEffVal

/-- WS-SM SM5.E (soundness, dequeue-on-dispatch): `scheduleOrIdleOnCore`
establishes that core `c`'s current thread is not in its run queue — the idle case
dequeues the idle thread before making it current (`RunQueue.remove`); the busy /
not-dispatchable cases inherit `scheduleEffectiveOnCore`'s. -/
theorem scheduleOrIdleOnCore_establishes_queueCurrentConsistentOnCore (st : SystemState) (c : CoreId)
    (st'' : SystemState) (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    queueCurrentConsistentOnCore st''.scheduler c := by
  unfold scheduleOrIdleOnCore at hStep
  cases hEff : scheduleEffectiveOnCore st c with
  | error e => rw [hEff] at hStep; simp at hStep
  | ok st' =>
    rw [hEff] at hStep
    have hEffQC := scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore st c st' hEff
    cases hcur : st'.scheduler.currentOnCore c with
    | some t => simp only [hcur, Except.ok.injEq] at hStep; subst hStep; exact hEffQC
    | none =>
      simp only [hcur] at hStep
      split at hStep
      · simp only [Except.ok.injEq] at hStep; subst hStep
        unfold queueCurrentConsistentOnCore
        simp only [dispatchIdleOnCore_currentOnCore, dispatchIdleOnCore_runQueueOnCore]
        exact RunQueue.not_mem_remove_toList _ (idleThreadId c)
      · simp only [Except.ok.injEq] at hStep; subst hStep; exact hEffQC

/-- WS-SM SM5.E (soundness): `scheduleOrIdleOnCore` preserves core `c`'s run-queue
well-formedness — the idle dispatch only `remove`s the idle thread (`RunQueue.remove`
preserves `wellFormed`); the busy / not-dispatchable cases inherit
`scheduleEffectiveOnCore`'s. -/
theorem scheduleOrIdleOnCore_preserves_runQueueOnCoreWellFormed (st : SystemState) (c : CoreId)
    (st'' : SystemState) (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    (st''.scheduler.runQueueOnCore c).wellFormed := by
  unfold scheduleOrIdleOnCore at hStep
  cases hEff : scheduleEffectiveOnCore st c with
  | error e => rw [hEff] at hStep; simp at hStep
  | ok st' =>
    rw [hEff] at hStep
    have hEffWf := scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed st c st' hwf hEff
    cases hcur : st'.scheduler.currentOnCore c with
    | some t => simp only [hcur, Except.ok.injEq] at hStep; subst hStep; exact hEffWf
    | none =>
      simp only [hcur] at hStep
      split at hStep
      · simp only [Except.ok.injEq] at hStep; subst hStep
        rw [dispatchIdleOnCore_runQueueOnCore]
        exact RunQueue.remove_preserves_wellFormed _ hEffWf (idleThreadId c)
      · simp only [Except.ok.injEq] at hStep; subst hStep; exact hEffWf

/-- WS-SM SM5.E (soundness, parity with `scheduleEffectiveOnCore`): the idle-aware
dispatcher establishes that core `c`'s current thread is in its active domain — the
idle case dispatches a thread whose domain matches (the `idleDispatchableOnCore`
gate checks exactly this); the busy / not-dispatchable cases inherit
`scheduleEffectiveOnCore`'s establishment.  Closes the parity gap: the wrapper is
as sound as the function it layers on. -/
theorem scheduleOrIdleOnCore_establishes_currentThreadInActiveDomainOnCore (st : SystemState)
    (c : CoreId) (st'' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    currentThreadInActiveDomainOnCore st'' c := by
  unfold scheduleOrIdleOnCore at hStep
  cases hEff : scheduleEffectiveOnCore st c with
  | error e => rw [hEff] at hStep; simp at hStep
  | ok st' =>
    rw [hEff] at hStep
    have hEffDom :=
      scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore st c st' hInv hEff
    cases hcur : st'.scheduler.currentOnCore c with
    | some t => simp only [hcur, Except.ok.injEq] at hStep; subst hStep; exact hEffDom
    | none =>
      simp only [hcur] at hStep
      split at hStep
      · rename_i hd
        simp only [Except.ok.injEq] at hStep; subst hStep
        unfold currentThreadInActiveDomainOnCore
        simp only [dispatchIdleOnCore_currentOnCore, dispatchIdleOnCore_getTcb?,
          dispatchIdleOnCore_activeDomainOnCore]
        unfold idleDispatchableOnCore at hd
        cases hres : st'.getTcb? (idleThreadId c) with
        | none => rw [hres] at hd; simp at hd
        | some idleTcb => rw [hres] at hd; simpa using hd
      · simp only [Except.ok.injEq] at hStep; subst hStep; exact hEffDom

/-- WS-SM SM5.E (soundness, parity with `scheduleEffectiveOnCore`): the idle-aware
dispatcher preserves "every runnable thread resolves to a TCB" — the idle case only
`remove`s the idle thread from the run queue (so the post run queue is a subset of
the pre run queue, which `scheduleEffectiveOnCore` already establishes as all-TCBs);
the busy / not-dispatchable cases inherit `scheduleEffectiveOnCore`'s. -/
theorem scheduleOrIdleOnCore_preserves_runnableThreadsAreTCBsOnCore (st : SystemState)
    (c : CoreId) (st'' : SystemState) (hInv : st.objects.invExt)
    (h : runnableThreadsAreTCBsOnCore st c)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    runnableThreadsAreTCBsOnCore st'' c := by
  unfold scheduleOrIdleOnCore at hStep
  cases hEff : scheduleEffectiveOnCore st c with
  | error e => rw [hEff] at hStep; simp at hStep
  | ok st' =>
    rw [hEff] at hStep
    have hEffR :=
      scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore st c st' hInv hEff h
    cases hcur : st'.scheduler.currentOnCore c with
    | some t => simp only [hcur, Except.ok.injEq] at hStep; subst hStep; exact hEffR
    | none =>
      simp only [hcur] at hStep
      split at hStep
      · simp only [Except.ok.injEq] at hStep; subst hStep
        intro tid htid
        rw [dispatchIdleOnCore_runQueueOnCore] at htid
        rw [dispatchIdleOnCore_getTcb?]
        have hMemOld : tid ∈ (st'.scheduler.runQueueOnCore c).toList := by
          rw [RunQueue.mem_toList_iff_mem, RunQueue.mem_remove] at htid
          exact (RunQueue.mem_toList_iff_mem _ _).mpr htid.1
        exact hEffR tid hMemOld
      · simp only [Except.ok.injEq] at hStep; subst hStep; exact hEffR

end SeLe4n.Kernel
