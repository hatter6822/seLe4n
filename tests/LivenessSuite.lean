/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Liveness

/-!
# D5-O: Liveness Suite — Invariant Surface Anchor Tests

Tier 3 invariant surface anchors for the bounded latency theorem (D5).
These tests verify that key liveness theorems and definitions exist and
have the expected types, anchoring the proof surface against regressions.
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
-- Surface anchor: D4 integration (from BoundedInversion)
-- ============================================================================

#check @SeLe4n.Kernel.PriorityInheritance.pip_bounded_inversion

-- ============================================================================
-- Executable entry point
-- ============================================================================

def main : IO Unit := do
  IO.println "=== Liveness Suite (D5-O) ==="
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
  IO.println "  ✓ D4 integration: pip_bounded_inversion"
  IO.println "=== All 58 surface anchors verified ==="
  return ()
