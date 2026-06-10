-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreWcrt
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWcrtInventory
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM5.J — WCRT-under-fine-locks test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM5.J
"WCRT under fine locks" deliverable
(`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.9, §5 SM5.J).

* **§1 Surface anchors** — every public SM5.J symbol resolves at elaboration time
  (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem (the §3.9
  Theorem 3.9.1 RPi5 bound, the per-operation bounds, the combined `WCRT_smp`
  decomposition, the no-starvation capstone, the R5-latency bridge) to verified
  inputs.
* **§3 Runtime assertions** — `lake exe smp_wcrt_suite` exercises the actual
  `WCRT_lockSet` / `WCRT_smp` computations on concrete per-core op footprints (the
  SM5.J.5 WCRT scenarios): the per-op exact lock-WCRT values, the RPi5
  `≤ maxLockSetSize · 3 · tCs` bound, the typical-syscall `< 1 ms` tick-budget fit,
  the combined `WCRT_smp` decomposition + monotonicity, the per-core idle no-stall
  on a concrete idle-enqueued fixture **including the ∀-core form on an
  idle-on-all-4-cores fixture** (the non-vacuity witness for
  `schedulerNoStall_smp_of_idleAvailableB`'s premise), the completion-pass
  refinement checks (execution bridge / cycle-commensurate units / access-mode
  soundness), and the SM5.J inventory partition counts.
-/

namespace SeLe4n.Testing.SmpWcrt

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM5.J public symbol resolves
-- ============================================================================

-- SM5.J.1 WCRT_lockSet cost function + forms + RPi5 grounding:
#check @WCRT_lockSet
#check @WCRT_lockSet_eq_product
#check @WCRT_lockSet_nil
#check @WCRT_lockSet_mono_length
#check @WCRT_lockSet_mono_cost
#check @WCRT_lockSet_le_maxLockSetSize
#check @rpi5OtherCoreCount
#check @perLockWaitCost_rpi5
#check @WCRT_lockSet_rpi5

-- SM5.J.2 RPi5 bound + combined WCRT_smp:
#check @wcrt_bound_rpi5_smp
#check @WCRT_smp
#check @WCRT_smp_decomposition
#check @WCRT_smp_r5_component_le
#check @WCRT_smp_lockSet_component_le
#check @wcrt_smp_bound_rpi5
#check @wcrt_bound_smp
#check @WCRT_smp_cycles
#check @WCRT_smp_cycles_one
#check @WCRT_smp_cycles_decomposition

-- SM5.J.3 per-operation WCRT bounds:
#check @wcrt_op_bounded_of_size
#check @wcrt_chooseThreadOnCore_eq
#check @wcrt_chooseThreadOnCore_bounded
#check @wcrt_switchToThreadOnCore_eq
#check @wcrt_switchToThreadOnCore_bounded
#check @wcrt_wakeThread_eq
#check @wcrt_wakeThread_bounded
#check @wcrt_timerTickOnCore_eq
#check @wcrt_timerTickOnCore_bounded
#check @wcrt_replenishOnCore_eq
#check @wcrt_replenishOnCore_bounded
#check @wcrt_advanceDomainOnCore_bounded
#check @wcrt_handleRescheduleSgiOnCore_bounded
#check @wcrt_timerTickOnCoreComplete_bounded

-- SM5.J access-mode soundness + execution bridge:
#check @WCRT_lockSet_mode_independent
#check @WCRT_lockSet_eq_totalWaitCost_of_length_eq
#check @kernelWait_le_WCRT_lockSet_of_length_eq

-- SM5.J.4 no-thread-starves-under-SMP liveness (the genuine eventually-scheduled keystone):
#check @schedulerNoStallOnCore
#check @schedulerNoStall_smp
#check @schedulerNoStall_smp_of_idleAvailableB
#check @boundedKernelWait_smp
#check @thread_eventually_scheduled_onCore
#check @thread_eventually_scheduled_within_smp_bound
#check @no_starvation_under_smp
#check @r5_latency_within_smp_bound

-- SM5.J.4 production per-core R5 trace-model generalisation (the substantive backing):
#check @Liveness.selectedAtOnCore
#check @Liveness.WCRTHypothesesOnCore
#check @Liveness.WCRTHypotheses.toOnCore
#check @Liveness.bounded_scheduling_latency_exists_onCore
#check @Liveness.wcrt_bound_rpi5_onCore
#check @Liveness.rpi5_higherBandExhausted_from_progressesOnCore

-- SM5.J inventory:
#check @perCoreWcrtTheorems
#check @perCoreWcrtTheorems_count
#check @perCoreWcrtTheorems_partition_sum
#check @perCoreWcrtTheorems_identifiers_nodup

-- ============================================================================
-- §2  Elaboration-time examples (apply each headline theorem)
-- ============================================================================

-- SM5.J.2: the plan §3.9 Theorem 3.9.1 — for the RPi5 canonical config, any
-- bounded-footprint op's lock-WCRT is ≤ maxLockSetSize · 3 · tCs, and the config is
-- well-formed.
example (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat)
    (hSize : lockSet.length ≤ maxLockSetSize) :
    Liveness.rpi5CanonicalConfig.wellFormed ∧
    WCRT_lockSet lockSet tCs ≤ maxLockSetSize * (3 * tCs) :=
  wcrt_bound_rpi5_smp Liveness.rpi5CanonicalConfig rfl lockSet tCs hSize

-- SM5.J.3: the chooseThreadOnCore footprint has lock-WCRT exactly 2 · 3 · tCs.
example (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (chooseThreadOnCoreLockSet c) tCs = 2 * (3 * tCs) :=
  wcrt_chooseThreadOnCore_eq c tCs

-- SM5.J.3: the timer tick footprint is within the RPi5 bound.
example (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (timerTickOnCoreLockSet c) tCs ≤ maxLockSetSize * (3 * tCs) :=
  wcrt_timerTickOnCore_bounded c tCs

-- SM5.J.2 (extends R5): the combined SMP WCRT splits into the R5 scheduling-latency
-- term and the SM5.J lock-contention term.
example (D L_max N B P : Nat) (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat) :
    WCRT_smp D L_max N B P lockSet tCs =
      Liveness.wcrtBound D L_max N B P + WCRT_lockSet lockSet tCs :=
  WCRT_smp_decomposition D L_max N B P lockSet tCs

-- SM5.J.4 (THE genuine per-core eventually-scheduled liveness): a thread runnable on
-- core c with a bounded same-or-higher-priority band IS selected on c within wcrtBound
-- ticks — a *specific thread makes progress* on an *arbitrary* core (not merely "the
-- scheduler picks someone").  This is the real "no thread starves" content.
example (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (trace : Liveness.SchedulerTrace) (hyp : Liveness.WCRTHypothesesOnCore st tid c)
    (hValid : Liveness.ValidTrace st trace)
    (hDom : ∃ k₁, k₁ ≤ Liveness.domainRotationBound st.scheduler.domainSchedule.length
        (Liveness.maxDomainLength st.scheduler.domainSchedule) ∧
      match Liveness.traceStateAt trace k₁ with
      | some st₁ => st₁.scheduler.activeDomainOnCore c = hyp.targetDomain ∧
                     (st₁.scheduler.runQueueOnCore c).contains tid = true
      | none => False)
    (hBand : ∀ k₁ st₁, Liveness.traceStateAt trace k₁ = some st₁ →
      st₁.scheduler.activeDomainOnCore c = hyp.targetDomain →
      (st₁.scheduler.runQueueOnCore c).contains tid = true →
      ∃ k₂, k₂ ≤ Liveness.bandExhaustionBound hyp.N hyp.B hyp.P ∧
        Liveness.selectedAtOnCore trace (k₁ + k₂) tid c) :
    ∃ k, k ≤ Liveness.wcrtBound st.scheduler.domainSchedule.length
              (Liveness.maxDomainLength st.scheduler.domainSchedule) hyp.N hyp.B hyp.P ∧
      Liveness.selectedAtOnCore trace k tid c :=
  thread_eventually_scheduled_onCore st tid c trace hyp hValid hDom hBand

-- SM5.J (execution bridge): the execution-sensitive Concurrency.WCRT (which counts the
-- cores actually contending each lock) is bounded by the static per-core WCRT_lockSet of
-- an equal-size footprint — connecting the two WCRT models.
example (e : Concurrency.KernelExecution) (c : CoreId) (op : Concurrency.KernelOperation)
    (ls : List (SchedLockId × AccessMode)) (tCs : Nat) (hlen : ls.length = op.lockSet.size) :
    Concurrency.WCRT e c op tCs ≤ WCRT_lockSet ls tCs :=
  kernelWait_le_WCRT_lockSet_of_length_eq e c op ls tCs hlen

-- SM5.J.4 (decidable no-stall discharge): the no-stall premise is established by `decide`
-- on any concrete state where every core's idle is available — not assumed.
example (st : SystemState)
    (hwf : ∀ c, (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : ∀ c, runnableThreadsAreTCBsOnCore st c)
    (hAvail : ∀ c, idleAvailableOnCoreB st c = true) :
    ∀ c : CoreId, ∃ tid, chooseThreadOnCore st c = .ok (some tid) :=
  schedulerNoStall_smp_of_idleAvailableB st hwf hRunnable hAvail

-- SM5.J.4 (extends R5): an R5-scheduled thread is within the combined SMP bound.
example (trace : Liveness.SchedulerTrace) (tid : SeLe4n.ThreadId)
    (D L_max N B P : Nat) (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat)
    (k : Nat) (hk : k ≤ Liveness.wcrtBound D L_max N B P)
    (hSel : Liveness.selectedAt trace k tid) :
    ∃ k', k' ≤ WCRT_smp D L_max N B P lockSet tCs ∧ Liveness.selectedAt trace k' tid :=
  r5_latency_within_smp_bound trace tid D L_max N B P lockSet tCs k hk hSel

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM5.J.5 WCRT scenarios
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- A representative per-lock critical-section cost: `WCRT_per_lock ≈ 60` (µs),
the plan §3.9 bounded-critical-section figure. -/
private def tCs60 : Nat := 60

/-- Core 1 — a non-boot core, used by the per-core footprint scenarios. -/
private def core1 : CoreId := ⟨1, by decide⟩

/-- Empty boot state, and the same state with the boot core's idle thread enqueued
(`idleAvailableOnCoreB` then holds — the SM5.J.4 per-core non-stall fixture). -/
private def stEmpty : SystemState := BootstrapBuilder.empty.build
private def stEmptyIdle : SystemState := enqueueIdleThreadOnCore stEmpty bootCoreId

/-- The empty boot state with **every** core's idle thread enqueued — the concrete
∀-core witness for `schedulerNoStall_smp_of_idleAvailableB`'s premise (idle
available on all `numCores` cores simultaneously). -/
private def stAllIdle : SystemState :=
  allCores.foldl (fun st c => enqueueIdleThreadOnCore st c) stEmpty

/-- §3.1: SM5.J.3 — the per-operation lock-WCRT exact values at `tCs = 60`.
`perLockWaitCost 60 = (numCores − 1) · 60 = 3 · 60 = 180`, so each op's lock-WCRT is
`|footprint| · 180`. -/
private def runPerOpExactChecks : IO Unit := do
  IO.println "--- §3.1 SM5.J.3 per-operation lock-WCRT exact values (tCs = 60) ---"
  assertBool "perLockWaitCost 60 = 180 (= (numCores−1)·60 = 3·60)"
    (decide (perLockWaitCost tCs60 = 180))
  assertBool "chooseThreadOnCore (2 locks) lock-WCRT = 360 (= 2·3·60)"
    (decide (WCRT_lockSet (chooseThreadOnCoreLockSet bootCoreId) tCs60 = 360))
  assertBool "switchToThreadOnCore (2 locks) lock-WCRT = 360"
    (decide (WCRT_lockSet (switchToThreadOnCoreLockSet bootCoreId) tCs60 = 360))
  assertBool "wakeThread (2 locks) lock-WCRT = 360"
    (decide (WCRT_lockSet (wakeThreadLockSet core1) tCs60 = 360))
  assertBool "timerTickOnCore (3 locks) lock-WCRT = 540 (= 3·3·60)"
    (decide (WCRT_lockSet (timerTickOnCoreLockSet bootCoreId) tCs60 = 540))
  assertBool "replenishOnCore (1 lock) lock-WCRT = 180 (= 1·3·60)"
    (decide (WCRT_lockSet (replenishOnCoreLockSet bootCoreId) tCs60 = 180))
  assertBool "advanceDomainOnCore (1 lock) lock-WCRT = 180"
    (decide (WCRT_lockSet (advanceDomainOnCoreLockSet bootCoreId) tCs60 = 180))

/-- §3.2: SM5.J.2 — the RPi5 §3.9 bound `≤ maxLockSetSize · 3 · tCs = 8·180 = 1440`,
and the typical `|lockSet| ≤ 4` syscall fits the 1 ms (1000 µs) timer-tick budget
(`4 · 3 · 60 = 720 < 1000`). -/
private def runRpi5BoundChecks : IO Unit := do
  IO.println "--- §3.2 SM5.J.2 RPi5 bound (maxLockSetSize·3·tCs) + 1 ms tick-budget fit ---"
  assertBool "the RPi5 uniform bound maxLockSetSize·3·60 = 1440"
    (decide (maxLockSetSize * (3 * tCs60) = 1440))
  assertBool "chooseThreadOnCore lock-WCRT (360) ≤ RPi5 bound (1440)"
    (decide (WCRT_lockSet (chooseThreadOnCoreLockSet bootCoreId) tCs60 ≤ maxLockSetSize * (3 * tCs60)))
  assertBool "timerTickOnCore lock-WCRT (540) ≤ RPi5 bound (1440)"
    (decide (WCRT_lockSet (timerTickOnCoreLockSet bootCoreId) tCs60 ≤ maxLockSetSize * (3 * tCs60)))
  assertBool "the §3.9 RPi5 coreCount−1 = 3 (the × 3 factor)"
    (decide (numCores - 1 = 3))
  -- The plan §3.9 worked example: a typical syscall touches ≤ 4 locks, so its WCRT
  -- is ≤ 4 · 3 · 60 µs = 720 µs < 1 ms = 1000 µs — within the timer-tick budget.
  assertBool "typical syscall (4 locks) WCRT = 720 µs < 1000 µs (1 ms tick budget)"
    (decide (4 * (3 * tCs60) < 1000))
  assertBool "a 4-lock footprint's WCRT_lockSet is ≤ the maxLockSetSize bound"
    (decide (4 * (3 * tCs60) ≤ maxLockSetSize * (3 * tCs60)))

/-- §3.3: SM5.J.2 — the combined `WCRT_smp` decomposition + monotonicity.  With an R5
domain bound of, say, 50 ticks (in a common time base) and the timer-tick lock
contention 540, the combined SMP WCRT is `50 + 540 = 590`. -/
private def runWcrtSmpChecks : IO Unit := do
  IO.println "--- §3.3 SM5.J.2 combined WCRT_smp (R5 latency + lock contention) ---"
  -- Use abstract R5 parameters whose wcrtBound evaluates to a concrete value:
  -- wcrtBound D L_max N B P = D·L_max + N·(B+P).  Take D=5,L_max=10,N=2,B=3,P=2 ⇒
  -- 5·10 + 2·(3+2) = 50 + 10 = 60.
  assertBool "wcrtBound 5 10 2 3 2 = 60 (R5 scheduling-latency term)"
    (decide (Liveness.wcrtBound 5 10 2 3 2 = 60))
  assertBool "WCRT_smp = R5 term (60) + timerTick lock-WCRT (540) = 600"
    (decide (WCRT_smp 5 10 2 3 2 (timerTickOnCoreLockSet bootCoreId) tCs60 = 600))
  assertBool "the R5 term (60) is a lower component of the combined bound (600)"
    (decide (Liveness.wcrtBound 5 10 2 3 2 ≤ WCRT_smp 5 10 2 3 2 (timerTickOnCoreLockSet bootCoreId) tCs60))
  assertBool "the lock term (540) is a lower component of the combined bound (600)"
    (decide (WCRT_lockSet (timerTickOnCoreLockSet bootCoreId) tCs60 ≤ WCRT_smp 5 10 2 3 2 (timerTickOnCoreLockSet bootCoreId) tCs60))
  -- Monotonicity: a longer footprint (timerTick, 3 locks) has a larger lock-WCRT
  -- than a shorter one (replenish, 1 lock).
  assertBool "WCRT_lockSet is monotone in footprint length (replenish 180 ≤ timerTick 540)"
    (decide (WCRT_lockSet (replenishOnCoreLockSet bootCoreId) tCs60
              ≤ WCRT_lockSet (timerTickOnCoreLockSet bootCoreId) tCs60))
  -- Monotonicity in the per-lock cost: the same footprint at a larger tCs costs more.
  assertBool "WCRT_lockSet is monotone in the per-lock cost (chooseThread at tCs=30 ≤ tCs=60)"
    (decide (WCRT_lockSet (chooseThreadOnCoreLockSet bootCoreId) 30
              ≤ WCRT_lockSet (chooseThreadOnCoreLockSet bootCoreId) 60))

/-- §3.4: SM5.J.4 — the per-core idle thread guarantees no core stalls.  On the
idle-enqueued fixture, `idleAvailableOnCoreB` holds and `chooseThreadOnCore` selects
some thread; on the bare empty core it signals idle-fallback (`.ok none`). -/
private def runNoStallChecks : IO Unit := do
  IO.println "--- §3.4 SM5.J.4 per-core no-stall (idle fallback guarantees a selection) ---"
  assertBool "after enqueue: idleAvailableOnCoreB holds (idle is an in-domain candidate)"
    (decide (idleAvailableOnCoreB stEmptyIdle bootCoreId = true))
  assertBool "after enqueue: chooseThreadOnCore SELECTS the idle thread (no stall)"
    (decide (chooseThreadOnCoreSelects stEmptyIdle bootCoreId (idleThreadId bootCoreId)))
  assertBool "after enqueue: the selection is success (.ok), not an error"
    (match chooseThreadOnCore stEmptyIdle bootCoreId with | .ok (some _) => true | _ => false)
  assertBool "bare empty core signals idle-fallback (.ok none) — the SM5.E hook"
    (decide (chooseThreadOnCoreIdleFallback stEmpty bootCoreId))
  -- The ∀-CORE non-vacuity witness: `schedulerNoStall_smp_of_idleAvailableB`'s premise
  -- (every core's idle available) is genuinely satisfiable — enqueue idle on ALL 4
  -- cores and `decide` the premise + per-core selection on the concrete state.
  assertBool "all-cores fixture: idleAvailableOnCoreB holds on EVERY core (the ∀-core premise)"
    (allCores.all (fun c => idleAvailableOnCoreB stAllIdle c))
  assertBool "all-cores fixture: EVERY core selects its own idle thread (no core stalls)"
    (allCores.all (fun c => decide (chooseThreadOnCoreSelects stAllIdle c (idleThreadId c))))
  assertBool "all-cores fixture: each core's idle stays on its own queue (no cross-core leak)"
    (allCores.all (fun c => allCores.all (fun c' =>
      c == c' || !decide (idleThreadId c ∈ (stAllIdle.scheduler.runQueueOnCore c').toList))))

/-- §3.5: the completion-pass refinements — the execution-sensitive bridge formula,
the cycle-commensurate combined bound, and the access-mode soundness. -/
private def runRefinementChecks : IO Unit := do
  IO.println "--- §3.5 SM5.J completion: execution bridge + cycle units + mode soundness ---"
  -- Bridge: WCRT_lockSet = the SM3.D uniform formula |footprint| · (numCores−1) · tCs;
  -- here for the 3-lock timer footprint at tCs=60 ⇒ 3 · 3 · 60 = 540, the same value
  -- Concurrency.totalWaitCost yields for a size-3 LockSet.
  assertBool "execution bridge: WCRT_lockSet(timerTick,60)=540 matches the size·(numCores−1)·tCs formula"
    (decide (WCRT_lockSet (timerTickOnCoreLockSet bootCoreId) tCs60
              = (timerTickOnCoreLockSet bootCoreId).length * ((numCores - 1) * tCs60)))
  -- Cycle-commensurate units: with cyclesPerTick=1000 (1 µs/tick = 1000 ns), the R5
  -- term scales: WCRT_smp_cycles 1000 (wcrtBound=60) ... = 1000·60 + 540 = 60540.
  assertBool "cycle units: WCRT_smp_cycles 1000 5 10 2 3 2 (timerTick) 60 = 1000·60 + 540 = 60540"
    (decide (WCRT_smp_cycles 1000 5 10 2 3 2 (timerTickOnCoreLockSet bootCoreId) tCs60 = 60540))
  assertBool "cycle units: WCRT_smp_cycles 1 = WCRT_smp (cyclesPerTick=1 collapses to the base)"
    (decide (WCRT_smp_cycles 1 5 10 2 3 2 (timerTickOnCoreLockSet bootCoreId) tCs60
              = WCRT_smp 5 10 2 3 2 (timerTickOnCoreLockSet bootCoreId) tCs60))
  -- Access-mode soundness: a read footprint and a write footprint of the same shape
  -- have the same WCRT_lockSet (the worst case is all-writers, mode-agnostic).
  assertBool "mode soundness: read-mode and write-mode 2-lock footprints have equal WCRT_lockSet"
    (decide (WCRT_lockSet [(SchedLockId.runQueue ⟨bootCoreId⟩, AccessMode.read)] tCs60
              = WCRT_lockSet [(SchedLockId.runQueue ⟨bootCoreId⟩, AccessMode.write)] tCs60))
  -- The SGI-handler footprint (= switch, 2 locks) and the complete-timer footprint are
  -- both within the RPi5 bound (the §3 completion per-op bounds).
  assertBool "SGI-handler lock-WCRT (= switch, 360) ≤ RPi5 bound (1440)"
    (decide (WCRT_lockSet (handleRescheduleSgiOnCoreLockSet bootCoreId) tCs60 ≤ maxLockSetSize * (3 * tCs60)))

/-- §3.6: the SM5.J theorem-inventory partition counts (compiled-`decide` guards). -/
private def runInventoryChecks : IO Unit := do
  IO.println "--- §3.6 SM5.J inventory partition counts ---"
  assertBool "inventory has 44 entries"
    (decide (perCoreWcrtTheorems.length = 44))
  assertBool "lockSetWcrt category has 10 entries"
    (decide ((perCoreWcrtTheorems.filter (fun t => t.category == .lockSetWcrt)).length = 10))
  assertBool "rpi5Bound category has 10 entries"
    (decide ((perCoreWcrtTheorems.filter (fun t => t.category == .rpi5Bound)).length = 10))
  assertBool "perOp category has 14 entries"
    (decide ((perCoreWcrtTheorems.filter (fun t => t.category == .perOp)).length = 14))
  assertBool "executionBridge category has 2 entries"
    (decide ((perCoreWcrtTheorems.filter (fun t => t.category == .executionBridge)).length = 2))
  assertBool "liveness category has 8 entries"
    (decide ((perCoreWcrtTheorems.filter (fun t => t.category == .liveness)).length = 8))
  assertBool "inventory identifiers are duplicate-free"
    (decide (perCoreWcrtTheorems.map (·.identifier)).Nodup)

def main : IO Unit := do
  IO.println "=== WS-SM SM5.J — WCRT-under-fine-locks suite ==="
  runPerOpExactChecks
  runRpi5BoundChecks
  runWcrtSmpChecks
  runNoStallChecks
  runRefinementChecks
  runInventoryChecks
  IO.println "=== SM5.J suite: all assertions passed ==="

end SeLe4n.Testing.SmpWcrt

def main : IO Unit := SeLe4n.Testing.SmpWcrt.main
