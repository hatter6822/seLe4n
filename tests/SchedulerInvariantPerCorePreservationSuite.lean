-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant.PerCorePreservation

/-!
# WS-SM SM4.C audit-pass-4 — Per-operation per-core preservation test suite

Surface anchors + elaboration-time witness for each of the 5 per-op
per-core preservation theorems (plus the base bridge for `chooseThread`).
A rename / removal of any per-op preservation symbol fails here at
elaboration time.

The theorems themselves are `theorem`-typed (not `def`-typed), so the
surface-anchor `#check`s + `example`s that confirm the typed signature
elaborate are the right Tier-3 coverage; runtime `assertBool`-style
testing isn't meaningful for `Prop`-valued preservation statements
(there's no `decide` over Prop arguments like
`schedulerInvariant_smp`).
-/

namespace SeLe4n.Testing.SchedulerInvariantPerCorePreservation

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  Surface anchors (Tier-3): every public per-op preservation symbol
--     resolves.  A rename / removal fails the build at elaboration time.
-- ============================================================================

#check @schedule_preserves_schedulerInvariant_smp
#check @handleYield_preserves_schedulerInvariant_smp
#check @timerTick_preserves_schedulerInvariant_smp
#check @switchDomain_preserves_schedulerInvariant_smp
#check @scheduleDomain_preserves_schedulerInvariant_smp
#check @chooseThread_preserves_schedulerInvariantBundle_perCore_bootCore

-- §7 — per-conjunct per-operation SMP preservation (plan §3.4 Pattern 1).
-- 5 conjuncts × 5 ops = 25 named theorems (one-line projections from
-- the aggregate preservation).
#check @schedule_preserves_queueCurrentConsistentOnCore_smp
#check @schedule_preserves_runQueueUniqueOnCore_smp
#check @schedule_preserves_currentThreadValidOnCore_smp
#check @schedule_preserves_domainTimeRemainingPositiveOnCore_smp
#check @schedule_preserves_runnableThreadsAreTCBsOnCore_smp
#check @handleYield_preserves_queueCurrentConsistentOnCore_smp
#check @handleYield_preserves_runQueueUniqueOnCore_smp
#check @handleYield_preserves_currentThreadValidOnCore_smp
#check @handleYield_preserves_domainTimeRemainingPositiveOnCore_smp
#check @handleYield_preserves_runnableThreadsAreTCBsOnCore_smp
#check @timerTick_preserves_queueCurrentConsistentOnCore_smp
#check @timerTick_preserves_runQueueUniqueOnCore_smp
#check @timerTick_preserves_currentThreadValidOnCore_smp
#check @timerTick_preserves_domainTimeRemainingPositiveOnCore_smp
#check @timerTick_preserves_runnableThreadsAreTCBsOnCore_smp
#check @switchDomain_preserves_queueCurrentConsistentOnCore_smp
#check @switchDomain_preserves_runQueueUniqueOnCore_smp
#check @switchDomain_preserves_currentThreadValidOnCore_smp
#check @switchDomain_preserves_domainTimeRemainingPositiveOnCore_smp
#check @switchDomain_preserves_runnableThreadsAreTCBsOnCore_smp
#check @scheduleDomain_preserves_queueCurrentConsistentOnCore_smp
#check @scheduleDomain_preserves_runQueueUniqueOnCore_smp
#check @scheduleDomain_preserves_currentThreadValidOnCore_smp
#check @scheduleDomain_preserves_domainTimeRemainingPositiveOnCore_smp
#check @scheduleDomain_preserves_runnableThreadsAreTCBsOnCore_smp

-- ============================================================================
-- §2  Elaboration-time examples: each preservation theorem applies to a
--     concrete (variable) input shape, confirming the typed signature is
--     usable by callers (SM5 will instantiate `hStep` from a concrete
--     operation step).
-- ============================================================================

/-- `schedule_preserves_schedulerInvariant_smp` applies. -/
example
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
    schedulerInvariant_smp st' :=
  schedule_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle

/-- `handleYield_preserves_schedulerInvariant_smp` applies. -/
example
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
    schedulerInvariant_smp st' :=
  handleYield_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hStep hOtherIdle

/-- `timerTick_preserves_schedulerInvariant_smp` applies (extra
`hConfigTS` hypothesis). -/
example
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
    schedulerInvariant_smp st' :=
  timerTick_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hAllTcb hObjInv hConfigTS hStep hOtherIdle

/-- `switchDomain_preserves_schedulerInvariant_smp` applies (lighter
preconditions — no `hwf`/`hAllTcb`). -/
example
    (st st' : SystemState)
    (hPre : schedulerInvariant_smp st)
    (hDSE : domainScheduleEntriesPositive st)
    (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st'))
    (hOtherIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0) :
    schedulerInvariant_smp st' :=
  switchDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hObjInv hStep hOtherIdle

/-- `scheduleDomain_preserves_schedulerInvariant_smp` applies. -/
example
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
    schedulerInvariant_smp st' :=
  scheduleDomain_preserves_schedulerInvariant_smp st st' hPre hDSE hwf hObjInv hStep hOtherIdle

/-- `chooseThread_preserves_schedulerInvariantBundle_perCore_bootCore`
applies (base-aggregate bridge — no Full preservation exists for
`chooseThread` at the single-core layer). -/
example
    (st st' : SystemState) (next : Option SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : chooseThread st = .ok (next, st')) :
    schedulerInvariantBundle st' :=
  chooseThread_preserves_schedulerInvariantBundle_perCore_bootCore st st' next hInv hStep

-- ============================================================================
-- §3  Runtime check: the 5 per-op preservation theorems are reachable at
--     runtime (their types resolve under the BaseIO unit witness).  Since
--     they're `Prop`-valued statements about arbitrary `(st, st')`, the
--     only runtime check meaningful is that the symbol exists and is
--     typed correctly (caught by the `#check` and `example` above).
--
--     A trivial IO main echoes a single PASS line so the suite has a
--     non-empty Tier-2 output.
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

def runPerCorePreservationChecks : IO Unit := do
  IO.println "WS-SM SM4.C audit-pass-4 — Per-op per-core preservation suite"
  IO.println "===================================="
  IO.println "--- §3.1 per-op preservation theorems elaborated ---"
  -- The 6 per-op preservation symbols resolve via the @check above; here
  -- we just confirm the suite executes end-to-end with no runtime error.
  assertBool "all 6 per-op preservation symbols elaborate" true
  IO.println "===================================="
  IO.println "All SM4.C per-op per-core preservation checks PASS."

end SeLe4n.Testing.SchedulerInvariantPerCorePreservation

def main : IO Unit :=
  SeLe4n.Testing.SchedulerInvariantPerCorePreservation.runPerCorePreservationChecks
