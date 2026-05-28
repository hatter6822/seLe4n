-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant.PerCore
import SeLe4n.Kernel.Scheduler.Operations.Preservation

/-!
# WS-SM SM4.C — Per-operation per-core preservation theorems

This module is the SM4.C audit-pass-4 deliverable: per-operation per-core
`schedulerInvariant_smp` preservation theorems for the boot-core scheduler
operations.  Each theorem composes (a) the existing single-core preservation
of `schedulerInvariantBundleFull` (in `Scheduler/Operations/Preservation.lean`),
(b) the SM4.C bundle bridges (`PerCore.lean` §4), and (c) the SM4.C
SMP-preservation composition (`PerCore.lean` §11).

## Boot-core scheduler operations covered

  * `schedule` — context save/restore + dequeue-on-dispatch + current write.
  * `handleYield` — re-enqueue current + reschedule.
  * `timerTick` — replenishment pipeline + budget/time-slice tick.
  * `switchDomain` — boot-core domain switch.
  * `scheduleDomain` — boot-core domain tick + possible switch.

`chooseThread` is omitted: it preserves only `schedulerInvariantBundle`
(the 3-conjunct base), not `schedulerInvariantBundleFull`, so a full
per-core preservation through the existing single-core surface is not
constructible.  Its preservation is composed inside `schedule`'s
preservation, so the SM5 per-core scheduler reaches it transitively.

## Per-operation structure

Each per-op theorem takes:
  1. `hPre : schedulerInvariant_smp st` — the pre-state SMP invariant.
  2. `hDSE : domainScheduleEntriesPositive st` — the system-wide schedule
     conjunct, needed to reconstitute `schedulerInvariantBundleFull` from
     the per-core slice at `bootCoreId`.
  3. The operation-specific hypotheses (`hwf`, `hAllTcb`, `hObjInv`, etc.)
     taken verbatim from the existing single-core preservation signature.
  4. `hStep : op st = .ok ((), st')` — the operation's step witness.
  5. `hOtherIdle` — a structural framing hypothesis asserting non-boot
     cores remain in the idle shape (`currentOnCore c = none`, empty run
     queue, positive `domainTimeRemaining`) on the post-state.  Under
     the SM4.B setter discipline (operations only write `bootCoreId`'s
     scheduler slots), the post-state non-boot slots equal the pre-state
     non-boot slots, which equal their default idle values on the
     current single-core kernel — so `hOtherIdle` holds by construction.
     The caller (typically SM5) supplies the witness from the operation's
     known structural properties.

The conclusion is `schedulerInvariant_smp st'`.

## Why this is the SM5 migration payoff

These theorems realise the migration pattern envisioned in plan §3.4:
the existing single-core preservation work is *reused verbatim* at the
boot core; non-boot cores are discharged by the structural idleness
witness via `schedulerInvariant_perCore_holds_if_idle`.  SM5 re-proves a
genuinely per-core operation's preservation only at the core it writes;
every other core continues to discharge via the structural witness.

Axiom-clean: every theorem depends only on `propext` / `Quot.sound` /
`Classical.choice`, verified via `#print axioms`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  schedule
-- ============================================================================

/-- WS-SM SM4.C: `schedule` preserves the SMP per-core scheduler invariant.

Composes `schedule_preserves_schedulerInvariantBundleFull` (the existing
single-core preservation) with the SM4.C boot-core bridge + the SMP-
preservation composition.  The structural `hOtherIdle` witness asserts
non-boot cores stay idle on the post-state (true under SM4.B's "only
writes `bootCoreId`'s slots" discipline). -/
theorem schedule_preserves_schedulerInvariant_smp
    (st st' : SystemState)
    (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    schedulerInvariant_smp st' := by
  apply schedulerInvariant_smp_of_bootCore_preservation _ hOtherIdle
  -- Boot-core preservation: reconstitute the full bundle, apply the
  -- existing single-core preservation, project back to per-core.
  have hFull : schedulerInvariantBundleFull st :=
    schedulerInvariant_perCore_bootCore_to_bundleFull (hPre bootCoreId) hDSE
  have hFull' : schedulerInvariantBundleFull st' :=
    schedule_preserves_schedulerInvariantBundleFull st st' hFull hwf hAllTcb hObjInv hStep
  exact schedulerInvariantBundleFull_to_perCore_bootCore hFull'

-- ============================================================================
-- §2  handleYield
-- ============================================================================

/-- WS-SM SM4.C: `handleYield` preserves the SMP per-core scheduler invariant.
Same composition pattern as `schedule_preserves_schedulerInvariant_smp`. -/
theorem handleYield_preserves_schedulerInvariant_smp
    (st st' : SystemState)
    (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    schedulerInvariant_smp st' := by
  apply schedulerInvariant_smp_of_bootCore_preservation _ hOtherIdle
  have hFull : schedulerInvariantBundleFull st :=
    schedulerInvariant_perCore_bootCore_to_bundleFull (hPre bootCoreId) hDSE
  have hFull' : schedulerInvariantBundleFull st' :=
    handleYield_preserves_schedulerInvariantBundleFull st st' hFull hwf hAllTcb hObjInv hStep
  exact schedulerInvariantBundleFull_to_perCore_bootCore hFull'

-- ============================================================================
-- §3  timerTick
-- ============================================================================

/-- WS-SM SM4.C: `timerTick` preserves the SMP per-core scheduler invariant.
Carries the additional `hConfigTS` (positive `configDefaultTimeSlice`)
hypothesis required by the existing single-core preservation. -/
theorem timerTick_preserves_schedulerInvariant_smp
    (st st' : SystemState)
    (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hConfigTS : st.scheduler.configDefaultTimeSlice > 0)
    (hStep : timerTick st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    schedulerInvariant_smp st' := by
  apply schedulerInvariant_smp_of_bootCore_preservation _ hOtherIdle
  have hFull : schedulerInvariantBundleFull st :=
    schedulerInvariant_perCore_bootCore_to_bundleFull (hPre bootCoreId) hDSE
  have hFull' : schedulerInvariantBundleFull st' :=
    timerTick_preserves_schedulerInvariantBundleFull st st' hFull hwf hAllTcb hObjInv hConfigTS hStep
  exact schedulerInvariantBundleFull_to_perCore_bootCore hFull'

-- ============================================================================
-- §4  switchDomain
-- ============================================================================

/-- WS-SM SM4.C: `switchDomain` preserves the SMP per-core scheduler invariant.
Lighter preconditions than `schedule` (no run-queue well-formedness or
TCB-membership hypotheses required by the single-core preservation). -/
theorem switchDomain_preserves_schedulerInvariant_smp
    (st st' : SystemState)
    (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    schedulerInvariant_smp st' := by
  apply schedulerInvariant_smp_of_bootCore_preservation _ hOtherIdle
  have hFull : schedulerInvariantBundleFull st :=
    schedulerInvariant_perCore_bootCore_to_bundleFull (hPre bootCoreId) hDSE
  have hFull' : schedulerInvariantBundleFull st' :=
    switchDomain_preserves_schedulerInvariantBundleFull st st' hFull hObjInv hStep
  exact schedulerInvariantBundleFull_to_perCore_bootCore hFull'

-- ============================================================================
-- §5  scheduleDomain
-- ============================================================================

/-- WS-SM SM4.C: `scheduleDomain` preserves the SMP per-core scheduler
invariant. -/
theorem scheduleDomain_preserves_schedulerInvariant_smp
    (st st' : SystemState)
    (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hObjInv : st.objects.invExt)
    (hStep : scheduleDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    schedulerInvariant_smp st' := by
  apply schedulerInvariant_smp_of_bootCore_preservation _ hOtherIdle
  have hFull : schedulerInvariantBundleFull st :=
    schedulerInvariant_perCore_bootCore_to_bundleFull (hPre bootCoreId) hDSE
  have hFull' : schedulerInvariantBundleFull st' :=
    scheduleDomain_preserves_schedulerInvariantBundleFull st st' hFull hwf hObjInv hStep
  exact schedulerInvariantBundleFull_to_perCore_bootCore hFull'

-- ============================================================================
-- §6  chooseThread (base aggregate only)
-- ============================================================================

/-- WS-SM SM4.C: `chooseThread` preserves a per-core *base* aggregate
(the 3-conjunct triad — `queueCurrentConsistent`, `runQueueUnique`,
`currentThreadValid`) at the boot core.  The existing single-core
preservation only proves the base bundle; the additional 7 conjuncts
of `schedulerInvariantBundleFull` are not established at the single-
core layer for `chooseThread` (its preservation is composed inside
`schedule`).  This bridge gives SM5 the base coverage it needs for the
chooseThread step. -/
theorem chooseThread_preserves_schedulerInvariantBundle_perCore_bootCore
    (st st' : SystemState) (next : Option SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : chooseThread st = .ok (next, st')) :
    schedulerInvariantBundle st' :=
  chooseThread_preserves_schedulerInvariantBundle st st' next hInv hStep

-- ============================================================================
-- §7  Per-conjunct per-operation SMP preservation (plan §3.4 Pattern 1)
-- ============================================================================
--
-- Named convenience corollaries: for each (op, conjunct) pair, one-line
-- projection from the §1..§5 aggregate per-op preservation theorem.  Each
-- of the 5 boot-core scheduler operations × 5 most-used conjuncts gives a
-- named handle SM5 will use directly (the remaining 5 conjuncts —
-- timeSlicePositive, currentTimeSlicePositive, edfCurrentHasEarliest,
-- contextMatchesCurrent, schedulerPriorityMatch — derive via the same
-- projection pattern; their explicit named forms are recorded as
-- post-SM4.C extensions if SM5 finds need for them).
--
-- Total: 5 conjuncts × 5 ops = 25 named theorems.

-- ----------------------------------------------------------------------------
-- §7.1  schedule
-- ----------------------------------------------------------------------------

theorem schedule_preserves_queueCurrentConsistentOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, queueCurrentConsistentOnCore st'.scheduler c := fun c =>
  schedulerInvariant_perCore_to_queueCurrentConsistent
    (schedule_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle c)

theorem schedule_preserves_runQueueUniqueOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, runQueueUniqueOnCore st'.scheduler c := fun c =>
  schedulerInvariant_perCore_to_runQueueUnique
    (schedule_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle c)

theorem schedule_preserves_currentThreadValidOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, currentThreadValidOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_currentThreadValid
    (schedule_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle c)

theorem schedule_preserves_domainTimeRemainingPositiveOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, domainTimeRemainingPositiveOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_domainTimeRemainingPositive
    (schedule_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle c)

theorem schedule_preserves_runnableThreadsAreTCBsOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, runnableThreadsAreTCBsOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_runnableThreadsAreTCBs
    (schedule_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle c)

-- ----------------------------------------------------------------------------
-- §7.2  handleYield  (same hypothesis shape as schedule)
-- ----------------------------------------------------------------------------

theorem handleYield_preserves_queueCurrentConsistentOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, queueCurrentConsistentOnCore st'.scheduler c := fun c =>
  schedulerInvariant_perCore_to_queueCurrentConsistent
    (handleYield_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle c)

theorem handleYield_preserves_runQueueUniqueOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, runQueueUniqueOnCore st'.scheduler c := fun c =>
  schedulerInvariant_perCore_to_runQueueUnique
    (handleYield_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle c)

theorem handleYield_preserves_currentThreadValidOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, currentThreadValidOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_currentThreadValid
    (handleYield_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle c)

theorem handleYield_preserves_domainTimeRemainingPositiveOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, domainTimeRemainingPositiveOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_domainTimeRemainingPositive
    (handleYield_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle c)

theorem handleYield_preserves_runnableThreadsAreTCBsOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, runnableThreadsAreTCBsOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_runnableThreadsAreTCBs
    (handleYield_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle c)

-- ----------------------------------------------------------------------------
-- §7.3  timerTick  (extra `hConfigTS`)
-- ----------------------------------------------------------------------------

theorem timerTick_preserves_queueCurrentConsistentOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hConfigTS : st.scheduler.configDefaultTimeSlice > 0)
    (hStep : timerTick st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, queueCurrentConsistentOnCore st'.scheduler c := fun c =>
  schedulerInvariant_perCore_to_queueCurrentConsistent
    (timerTick_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hConfigTS hStep hOtherIdle c)

theorem timerTick_preserves_runQueueUniqueOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hConfigTS : st.scheduler.configDefaultTimeSlice > 0)
    (hStep : timerTick st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, runQueueUniqueOnCore st'.scheduler c := fun c =>
  schedulerInvariant_perCore_to_runQueueUnique
    (timerTick_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hConfigTS hStep hOtherIdle c)

theorem timerTick_preserves_currentThreadValidOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hConfigTS : st.scheduler.configDefaultTimeSlice > 0)
    (hStep : timerTick st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, currentThreadValidOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_currentThreadValid
    (timerTick_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hConfigTS hStep hOtherIdle c)

theorem timerTick_preserves_domainTimeRemainingPositiveOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hConfigTS : st.scheduler.configDefaultTimeSlice > 0)
    (hStep : timerTick st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, domainTimeRemainingPositiveOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_domainTimeRemainingPositive
    (timerTick_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hConfigTS hStep hOtherIdle c)

theorem timerTick_preserves_runnableThreadsAreTCBsOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hConfigTS : st.scheduler.configDefaultTimeSlice > 0)
    (hStep : timerTick st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, runnableThreadsAreTCBsOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_runnableThreadsAreTCBs
    (timerTick_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hConfigTS hStep hOtherIdle c)

-- ----------------------------------------------------------------------------
-- §7.4  switchDomain  (lighter hypothesis shape)
-- ----------------------------------------------------------------------------

theorem switchDomain_preserves_queueCurrentConsistentOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st) (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, queueCurrentConsistentOnCore st'.scheduler c := fun c =>
  schedulerInvariant_perCore_to_queueCurrentConsistent
    (switchDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hObjInv hStep hOtherIdle c)

theorem switchDomain_preserves_runQueueUniqueOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st) (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, runQueueUniqueOnCore st'.scheduler c := fun c =>
  schedulerInvariant_perCore_to_runQueueUnique
    (switchDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hObjInv hStep hOtherIdle c)

theorem switchDomain_preserves_currentThreadValidOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st) (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, currentThreadValidOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_currentThreadValid
    (switchDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hObjInv hStep hOtherIdle c)

theorem switchDomain_preserves_domainTimeRemainingPositiveOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st) (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, domainTimeRemainingPositiveOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_domainTimeRemainingPositive
    (switchDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hObjInv hStep hOtherIdle c)

theorem switchDomain_preserves_runnableThreadsAreTCBsOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st) (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, runnableThreadsAreTCBsOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_runnableThreadsAreTCBs
    (switchDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hObjInv hStep hOtherIdle c)

-- ----------------------------------------------------------------------------
-- §7.5  scheduleDomain  (carries hwf)
-- ----------------------------------------------------------------------------

theorem scheduleDomain_preserves_queueCurrentConsistentOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hObjInv : st.objects.invExt)
    (hStep : scheduleDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, queueCurrentConsistentOnCore st'.scheduler c := fun c =>
  schedulerInvariant_perCore_to_queueCurrentConsistent
    (scheduleDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hObjInv hStep hOtherIdle c)

theorem scheduleDomain_preserves_runQueueUniqueOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hObjInv : st.objects.invExt)
    (hStep : scheduleDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, runQueueUniqueOnCore st'.scheduler c := fun c =>
  schedulerInvariant_perCore_to_runQueueUnique
    (scheduleDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hObjInv hStep hOtherIdle c)

theorem scheduleDomain_preserves_currentThreadValidOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hObjInv : st.objects.invExt)
    (hStep : scheduleDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, currentThreadValidOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_currentThreadValid
    (scheduleDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hObjInv hStep hOtherIdle c)

theorem scheduleDomain_preserves_domainTimeRemainingPositiveOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hObjInv : st.objects.invExt)
    (hStep : scheduleDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, domainTimeRemainingPositiveOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_domainTimeRemainingPositive
    (scheduleDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hObjInv hStep hOtherIdle c)

theorem scheduleDomain_preserves_runnableThreadsAreTCBsOnCore_smp
    (st st' : SystemState) (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hwf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId))
    (hObjInv : st.objects.invExt)
    (hStep : scheduleDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    ∀ c, runnableThreadsAreTCBsOnCore st' c := fun c =>
  schedulerInvariant_perCore_to_runnableThreadsAreTCBs
    (scheduleDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hObjInv hStep hOtherIdle c)

end SeLe4n.Kernel
