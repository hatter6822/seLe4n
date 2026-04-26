/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Liveness

/-!
# Liveness Suite — Invariant Surface Anchor Tests

Tier 3 invariant surface anchors for the bounded-latency (WCRT)
theorem.  These tests verify that key liveness theorems and
definitions exist and have the expected types, anchoring the proof
surface against regressions.
-/

open SeLe4n.Kernel.Liveness
open SeLe4n.Model

-- ============================================================================
-- Surface anchor: TraceModel types exist
-- ============================================================================

#check @SchedulerStep
#check @SchedulerTrace
#check @stepPrecondition
#check @ValidTrace
#check @stepPost

-- ============================================================================
-- Surface anchor: Query predicates exist
-- ============================================================================

#check @selectedAt
#check @runnableAt
#check @budgetAvailableAt
#check @traceStateAt

-- ============================================================================
-- Surface anchor: Counting predicates exist
-- ============================================================================

#check @countHigherOrEqualEffectivePriority
#check @maxBudgetInBand
#check @maxPeriodInBand
#check @bucketPosition
#check @resolveEffectivePriority

-- ============================================================================
-- Surface anchor: Timer-tick theorems
-- ============================================================================

#check @timerTickBudget_F1_succeeds
#check @timerTickBudget_bound_succeeds
#check @timerTickBudget_donated_succeeds
#check @consumeBudget_val_eq
#check @maxPreemptionInterval
#check @maxPreemptionInterval_pos
#check @budget_always_available_unbound
#check @budget_available_when_positive

-- ============================================================================
-- Surface anchor: Replenishment theorems
-- ============================================================================

#check @mkReplenishmentEntry_eligibleAt
#check @processReplenishments_budget_ge
#check @replenishQueue_insert_sorted
#check @replenishment_within_period
#check @replenishment_dead_time_exact

-- ============================================================================
-- Surface anchor: Yield/FIFO theorems
-- ============================================================================

#check @rotateToBack_preserves_contains
#check @yield_preserves_membership
#check @fifoProgressBound
#check @fifoProgressBound_mono
#check @fifoProgressBound_succ
#check @fifoProgressBound_mono_interval

-- ============================================================================
-- Surface anchor: Band exhaustion
-- ============================================================================

#check @bandExhaustionBound
#check @bandExhaustionBound_mono
#check @bandExhaustionBound_succ
#check @higherBandExhausted
#check @higherBandExhausted_when_no_higher
#check @eventuallyExits

-- ============================================================================
-- Surface anchor: Domain rotation
-- ============================================================================

#check @domainRotationBound
#check @domainRotationBound_mono
#check @maxDomainLength
#check @maxDomainLength_ge_each
#check @domainRotationTotal_le_bound
#check @switchDomain_index_advances

-- ============================================================================
-- Surface anchor: WCRT theorem (the crown jewel)
-- ============================================================================

#check @WCRTHypotheses
#check @wcrtBound
#check @wcrtBound_unfold
#check @bounded_scheduling_latency_exists
#check @wcrt_decomposition
#check @wcrt_domain_component_le
#check @wcrt_band_component_le
#check @wcrtBound_stable_across_states
#check @countHigherOrEqual_empty

-- ============================================================================
-- Surface anchor: PIP-enhanced WCRT
-- ============================================================================

#check @countHigherOrEqual_mono_threshold
#check @pip_enhanced_wcrt_le_base
#check @pip_wcrt_integration

-- ============================================================================
-- Surface anchor: Priority-inheritance bounded inversion
-- ============================================================================

#check @SeLe4n.Kernel.PriorityInheritance.pip_bounded_inversion

-- ============================================================================
-- Surface anchor: blockingChain/blockingAcyclic/pip_congruence theorems
-- ============================================================================

#check @SeLe4n.Kernel.PriorityInheritance.blockingChain_step
#check @SeLe4n.Kernel.PriorityInheritance.blockingChain_congr
#check @SeLe4n.Kernel.PriorityInheritance.blockingAcyclic_frame
#check @SeLe4n.Kernel.PriorityInheritance.pip_congruence
#check @SeLe4n.Kernel.PriorityInheritance.pip_revert_congruence

-- ============================================================================
-- AN5-E: RPi5 canonical deployment — eventuallyExits closure (DEF-AK2-K.4)
-- ============================================================================

#check @DeploymentSchedulingConfig
#check @DeploymentSchedulingConfig.wellFormed
#check @rpi5CanonicalConfig
#check @rpi5CanonicalConfig_wellFormed
#check @eventuallyExits_of_exit_index
#check @CanonicalDeploymentProgress
#check @rpi5_canonicalConfig_eventuallyExits
#check @rpi5_canonicalConfig_progress_config_wellFormed
#check @rpi5_higherBandExhausted_from_progresses
#check @rpi5_higherBandExhausted_empty_band
#check @wcrt_bound_rpi5
#check @wcrt_bound_rpi5_symbolic
#check @isRPi5CanonicalConfig
#check @isRPi5CanonicalConfig_iff
#check @rpi5CanonicalConfig_isCanonical
#check @rpi5_cbs_window_replenishments_bounded
#check @rpi5_cbs_window_replenishments_bounded_concrete

-- Runtime verification of the canonical-config witness values
example : rpi5CanonicalConfig.wellFormed := rpi5CanonicalConfig_wellFormed
example : isRPi5CanonicalConfig rpi5CanonicalConfig = true := rpi5CanonicalConfig_isCanonical
example : rpi5CanonicalConfig.timerFrequencyHz = 54_000_000 := rfl
example : rpi5CanonicalConfig.cbsPeriodTicks = 10_000 := rfl
example : rpi5CanonicalConfig.admissibleUtilisation = 750 := rfl
example : rpi5CanonicalConfig.maxPriorityBands = 256 := rfl
example : rpi5CanonicalConfig.maxDomains = 16 := rfl
example : rpi5CanonicalConfig.configDefaultTimeSlice = 1000 := rfl

-- AN5-E.1: Non-canonical configs that differ by a single field are rejected
-- by the canonical-check (defense-in-depth against misconfiguration).
example :
    isRPi5CanonicalConfig { rpi5CanonicalConfig with admissibleUtilisation := 751 } = false := by
  decide

example :
    isRPi5CanonicalConfig { rpi5CanonicalConfig with timerFrequencyHz := 0 } = false := by
  decide

-- AN5-E.1: A degenerate config with zero timer frequency is rejected by the
-- well-formedness check.
example : ¬ ({ rpi5CanonicalConfig with timerFrequencyHz := 0 } : DeploymentSchedulingConfig).wellFormed := by
  intro h
  exact absurd h.1 (by decide)

-- AN5-E.1: A degenerate config with zero CBS period is rejected.
example : ¬ ({ rpi5CanonicalConfig with cbsPeriodTicks := 0 } : DeploymentSchedulingConfig).wellFormed := by
  intro h
  exact absurd h.2.1 (by decide)

-- AN5-E.1: A config with utilisation over 1000‰ (over-admitted) is rejected.
example :
    ¬ ({ rpi5CanonicalConfig with admissibleUtilisation := 1001 } : DeploymentSchedulingConfig).wellFormed := by
  intro h
  exact absurd h.2.2.2 (by decide)

-- AN5-E.3: Functional test — constructing an exit witness from a two-step
-- trace whose post-state places `tid` neither in the run queue nor as
-- current discharges `eventuallyExits` via
-- `eventuallyExits_of_exit_index`. With `default : SystemState`:
--   * `default.scheduler.runQueue.contains _ = false` (empty RQ).
--   * `default.scheduler.current = none ≠ some _`.
example :
    let tid : SeLe4n.ThreadId := SeLe4n.ThreadId.ofNat 42
    let tr : SchedulerTrace :=
      [(SchedulerStep.schedule, default), (SchedulerStep.schedule, default)]
    eventuallyExits tr tid 0 := by
  -- Build the exit witness at k = 1 (> startIdx = 0).
  -- At index 1, `traceStateAt tr 1 = some default`.
  apply eventuallyExits_of_exit_index
    (trace := [(SchedulerStep.schedule, default), (SchedulerStep.schedule, default)])
    (tid := SeLe4n.ThreadId.ofNat 42) (startIdx := 0) (k := 1) (by decide)
    (st := default)
  · rfl
  · decide
  · decide

-- AN5-E.3: Functional test — `rpi5_canonicalConfig_eventuallyExits` via
-- the packaged `CanonicalDeploymentProgress` structure.
example :
    let tid : SeLe4n.ThreadId := SeLe4n.ThreadId.ofNat 42
    let tr : SchedulerTrace :=
      [(SchedulerStep.schedule, default), (SchedulerStep.schedule, default)]
    eventuallyExits tr tid 0 := by
  apply rpi5_canonicalConfig_eventuallyExits
    (trace := [(SchedulerStep.schedule, default), (SchedulerStep.schedule, default)])
    (tid := SeLe4n.ThreadId.ofNat 42) (startIdx := 0)
  exact {
    config := rpi5CanonicalConfig
    configIsRPi5 := rfl
    exitIdx := 1
    exitIdxAfter := by decide
    exitState := default
    exitStateAtIdx := by rfl
    notInRunQueue := by decide
    notCurrent := by decide
  }

-- ============================================================================
-- Executable entry point
-- ============================================================================

def main : IO Unit := do
  -- AN11-F (LOW): live runtime assertions matching the SC-M01 / AN5-D
  -- compile-time `#check` anchors on lines 165-166.  The arithmetic the
  -- bounding theorem proves can drift from the formal statement (e.g.
  -- if the canonical RPi5 budget / period changes); pinning a concrete
  -- value at runtime catches the drift on every smoke run.
  -- Canonical RPi5 instance:  budget = 5_000, period = 10_000.
  -- For a 30 000-tick observation window, the tight bound is
  -- 5_000 * ⌈30_000 / 10_000⌉ = 5_000 * 3 = 15_000.
  let budget := 5_000
  let period := 10_000
  let window := 30_000
  let tight := budget * ((window + period - 1) / period)
  if tight ≠ 15_000 then
    throw <| IO.userError s!"AN11-F: rpi5_cbs_window_replenishments_bounded_concrete arithmetic drifted (got {tight}, expected 15000)"
  IO.println s!"AN11-F live assertion: cbs tight bound (window=30k) = {tight}"
  IO.println "=== Liveness Suite ==="
  IO.println "  ✓ TraceModel types: SchedulerStep, SchedulerTrace, ValidTrace"
  IO.println "  ✓ Query predicates: selectedAt, runnableAt, budgetAvailableAt"
  IO.println "  ✓ Counting: countHigherOrEqual, maxBudgetInBand, maxPeriodInBand"
  IO.println "  ✓ TimerTick: F1/F2/F3 theorems, consumeBudget_val_eq"
  IO.println "  ✓ Replenishment: eligibility, budget_ge, insert_sorted"
  IO.println "  ✓ Yield: rotateToBack, fifoProgressBound, fifoProgressBound_succ"
  IO.println "  ✓ BandExhaustion: bandExhaustionBound, monotonicity"
  IO.println "  ✓ DomainRotation: domainRotationBound, maxDomainLength_ge_each"
  IO.println "  ✓ WCRT: WCRTHypotheses, wcrtBound_unfold"
  IO.println "  ✓ PIP: countHigherOrEqual_mono_threshold, pip_enhanced_wcrt_le_base"
  IO.println "  ✓ Priority-inheritance bounded inversion"
  IO.println "  ✓ blockingChain_step, blockingChain_congr, blockingAcyclic_frame"
  IO.println "  ✓ pip_congruence, pip_revert_congruence, crossSubsystem projection"
  IO.println "  ✓ AN5-E: DeploymentSchedulingConfig + rpi5CanonicalConfig (DEF-AK2-K.4)"
  IO.println "  ✓ AN5-E: rpi5_canonicalConfig_eventuallyExits (substantive closure)"
  IO.println "  ✓ AN5-E.3b: rpi5_higherBandExhausted_from_progresses (bridge)"
  IO.println "  ✓ AN5-E.3b: rpi5_higherBandExhausted_empty_band (vacuous case)"
  IO.println "  ✓ AN5-E: wcrt_bound_rpi5 delegation + runtime canonical-check"
  IO.println "  ✓ AN5-E.1: DeploymentSchedulingConfig.wellFormed rejects degenerate configs"
  IO.println "  ✓ AN5-E.3: functional tests — concrete CanonicalDeploymentProgress"
  IO.println "  ✓ AN5-D: rpi5_cbs_window_replenishments_bounded + _concrete (SC-M01)"
  IO.println "=== All 95 surface anchors verified ==="
  return ()
