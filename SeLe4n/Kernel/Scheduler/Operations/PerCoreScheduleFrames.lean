-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsPreservation

/-!
# Per-core scheduling point: what it leaves alone

`scheduleEffectiveOnCore` on core `c` (and its idle fallback) never changes a
core's active domain, domain time or schedule index, and writes no other core's
register bank.  These frames are production facts: the live yield syscall ends
in this scheduling point, and its confinement (`yieldOnCore_confinedToCores`)
and lock-footprint coverage (`schedLockSet_yieldOnCore_coversWrites`) read
them.  The domain transitions (`PerCoreDomain`) and the per-core invariant
suite import them from here.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-SM SM5.G.3 helper: the idle fallback frames every core's active domain. -/
theorem idleFallbackOnCore_activeDomainOnCore (st : SystemState) (c c' : CoreId) :
    (idleFallbackOnCore st c).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' := by
  unfold idleFallbackOnCore
  split
  · exact dispatchIdleOnCore_activeDomainOnCore st c c'
  · simp [SchedulerState.setCurrentOnCore_activeDomainOnCore]

/-- WS-SM SM5.G.3 helper: a successful per-core reschedule frames every core's
active domain (the re-dispatch changes the current thread / run queue / object
store, never an active scheduling domain).  The frame the live preservation needs
at core `c` itself, and the yield's lock footprint at every other core; proof
mirrors `scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore`'s
`hact` step. -/
theorem scheduleEffectiveOnCore_activeDomainOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (c' : CoreId) (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.scheduler.activeDomainOnCore c' = st.scheduler.activeDomainOnCore c' := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      rw [SystemState.clearReschedulePendingOnCore_scheduler,
        SchedulerState.clearReschedulePendingOnCore_activeDomainOnCore,
        idleFallbackOnCore_activeDomainOnCore, saveOutgoingContextOnCore_scheduler_eq]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep
          rw [← hStep]
          simp only [SchedulerState.clearReschedulePendingOnCore_activeDomainOnCore,
            SchedulerState.setCurrentOnCore_activeDomainOnCore, restoreIncomingContextOnCore_scheduler,
            SchedulerState.setRunQueueOnCore_activeDomainOnCore]
          rw [saveOutgoingContextOnCore_scheduler_eq]
        · simp at hStep

/-- WS-SM SM5.G.2 helper: the idle fallback frames every core's schedule index. -/
theorem idleFallbackOnCore_domainScheduleIndexOnCore (st : SystemState) (c c' : CoreId) :
    (idleFallbackOnCore st c).scheduler.domainScheduleIndexOnCore c'
      = st.scheduler.domainScheduleIndexOnCore c' := by
  unfold idleFallbackOnCore
  split
  · simp [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore,
      restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]
  · simp [SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore]

/-- WS-SM SM5.G.2 helper: a successful per-core reschedule frames every core's
schedule index (the re-dispatch changes current / run queue / object store, never
an index). -/
theorem scheduleEffectiveOnCore_domainScheduleIndexOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (c' : CoreId) (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.scheduler.domainScheduleIndexOnCore c' = st.scheduler.domainScheduleIndexOnCore c' := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      rw [SystemState.clearReschedulePendingOnCore_scheduler,
        SchedulerState.clearReschedulePendingOnCore_domainScheduleIndexOnCore,
        idleFallbackOnCore_domainScheduleIndexOnCore, saveOutgoingContextOnCore_scheduler_eq]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep
          rw [← hStep]
          simp only [SchedulerState.clearReschedulePendingOnCore_domainScheduleIndexOnCore,
            SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore, restoreIncomingContextOnCore_scheduler,
            SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]
          rw [saveOutgoingContextOnCore_scheduler_eq]
        · simp at hStep

/-- The idle fallback frames every core's domain time. -/
theorem idleFallbackOnCore_domainTimeRemainingOnCore (st : SystemState) (c c' : CoreId) :
    (idleFallbackOnCore st c).scheduler.domainTimeRemainingOnCore c'
      = st.scheduler.domainTimeRemainingOnCore c' := by
  unfold idleFallbackOnCore
  split
  · simp [dispatchIdleOnCore, restoreIncomingContextOnCore_scheduler]
  · simp

/-- A successful per-core reschedule frames every core's domain time (the
re-dispatch changes current / run queue / object store, never a domain's
remaining time). -/
theorem scheduleEffectiveOnCore_domainTimeRemainingOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (c' : CoreId) (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.scheduler.domainTimeRemainingOnCore c' = st.scheduler.domainTimeRemainingOnCore c' := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      rw [SystemState.clearReschedulePendingOnCore_scheduler,
        SchedulerState.clearReschedulePendingOnCore_domainTimeRemainingOnCore,
        idleFallbackOnCore_domainTimeRemainingOnCore, saveOutgoingContextOnCore_scheduler_eq]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep
          rw [← hStep]
          simp only [SchedulerState.clearReschedulePendingOnCore_domainTimeRemainingOnCore,
            SchedulerState.setCurrentOnCore_domainTimeRemainingOnCore,
            restoreIncomingContextOnCore_scheduler,
            SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore]
          rw [saveOutgoingContextOnCore_scheduler_eq]
        · simp at hStep

/-- WS-SM SM5.I (register-bank sibling frame): the idle fallback on core `c` leaves
every *sibling* core's register bank untouched — both arms write at most core
`c`'s bank (`dispatchIdle`'s restore) or nothing (`current = none`). -/
theorem idleFallbackOnCore_machine_regsOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (idleFallbackOnCore st c).machine.regsOnCore c' = st.machine.regsOnCore c' := by
  unfold idleFallbackOnCore
  split
  · show (restoreIncomingContextOnCore _ c (idleThreadId c)).machine.regsOnCore c' = _
    exact restoreIncomingContextOnCore_regsOnCore_ne _ c c' (idleThreadId c) h
  · rfl

/-- WS-SM SM5.I (register-bank sibling frame): a per-core dispatch on core `c₀`
leaves every *sibling* core's register bank untouched — the only machine write is
the restore's `setRegsOnCore c₀`. -/
theorem scheduleEffectiveOnCore_machine_regsOnCore_ne (st : SystemState) (c₀ c' : CoreId)
    (st' : SystemState) (hcc : c₀ ≠ c') (hStep : scheduleEffectiveOnCore st c₀ = .ok st') :
    st'.machine.regsOnCore c' = st.machine.regsOnCore c' := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c₀ with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      rw [SystemState.clearReschedulePendingOnCore_machine,
        idleFallbackOnCore_machine_regsOnCore_ne _ c₀ c' hcc, saveOutgoingContextOnCore_machine]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          show (restoreIncomingContextOnCore _ c₀ tid).machine.regsOnCore c' = _
          rw [restoreIncomingContextOnCore_regsOnCore_ne _ c₀ c' tid hcc]
          show (saveOutgoingContextOnCore st c₀).machine.regsOnCore c' = _
          rw [saveOutgoingContextOnCore_machine]
        · simp at hStep

end SeLe4n.Kernel
