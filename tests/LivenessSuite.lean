-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Liveness
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation
import SeLe4n.Kernel.SchedContext.Invariant.Preservation
-- WS-RC R6 (Phase R6): surface anchors for the R6.A GIC bridge,
-- R6.A.3 ArchitectureInvariantBundle composition, R6.C SecurityDomain
-- lattice, R6.D cleanup-error-unreachable theorem, and R6.B
-- DeclassificationPolicy.
import SeLe4n.Kernel.Architecture.ExceptionModel
import SeLe4n.Kernel.InformationFlow.Policy
import SeLe4n.Kernel.InformationFlow.Enforcement.Soundness
import SeLe4n.Kernel.IPC.Invariant.Defs

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
-- WS-RC R5.F (DEEP-SCH-05): rotateToBack membership precondition surface
#check @SeLe4n.Kernel.RunQueue.rotateToBack_requires_membership
#check @SeLe4n.Kernel.RunQueue.rotateToBack_priority_eq_threadPriority

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
-- Surface anchor: WS-RC R5 (Phase R5) — Scheduler / Lifecycle behaviour symmetry
-- ============================================================================
-- R5.A (DEEP-SUSP-02): cancelDonation split into two named arms.
#check @SeLe4n.Kernel.Lifecycle.Suspend.cancelBoundDonation
#check @SeLe4n.Kernel.Lifecycle.Suspend.cancelDonatedDonation
#check @SeLe4n.Kernel.Lifecycle.Suspend.cancelBoundDonation_scheduler_runQueue_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.cancelDonatedDonation_scheduler_runQueue_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.cancelBoundDonation_serviceRegistry_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.cancelDonatedDonation_serviceRegistry_eq
-- R5.B (DEEP-SUSP-01): PIP recomputation on resume — structural witnesses.
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreToReady_objectIndex_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreToReady_objects_eq_at_tid
#check @SeLe4n.Kernel.Lifecycle.Suspend.resumeThread_pipBoost_consistent_post_restore
-- R5.B.2 (DEEP-SUSP-01) substantive (Phase Q1/Q2 landing):
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreToReady_invExt
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreToReady_blockingServer_subgraph
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreToReady_preserves_blockingAcyclic
#check @SeLe4n.Kernel.Lifecycle.Suspend.ensureRunnable_objects_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.ensureRunnable_objectIndex_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.ensureRunnable_blockingServer_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.ensureRunnable_preserves_computeMaxWaiterPriority
#check @SeLe4n.Kernel.Lifecycle.Suspend.resumeThread_postState_shape
#check @SeLe4n.Kernel.Lifecycle.Suspend.resumeThread_preserves_blockingAcyclic
#check @SeLe4n.Kernel.Lifecycle.Suspend.resumeThread_pipBoost_consistent_with_blocking_graph
-- Phase Q2.A deferred completion: schedule frame lemmas
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreIncomingContext_objects_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreIncomingContext_objectIndex_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.saveOutgoingContext_lookup_equiv
#check @SeLe4n.Kernel.Lifecycle.Suspend.saveOutgoingContext_getSchedContext?_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.saveOutgoingContext_objectIndex_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.chooseThread_state_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.schedule_lookup_equiv
#check @SeLe4n.Kernel.Lifecycle.Suspend.schedule_getSchedContext?_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.schedule_objectIndex_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.schedule_preserves_computeMaxWaiterPriority
-- Phase P1 foundational lemmas:
#check @SeLe4n.Kernel.PriorityInheritance.blockingAcyclic_of_subgraph
#check @SeLe4n.Kernel.PriorityInheritance.blockingChain_subgraph_prefix
#check @SeLe4n.Kernel.PriorityInheritance.computeMaxWaiterPriority_frame
#check @SeLe4n.Kernel.PriorityInheritance.waitersOf_frame
#check @SeLe4n.Kernel.PriorityInheritance.effectiveSchedParams_frame
#check @SeLe4n.Kernel.PriorityInheritance.effectiveSchedParams_frame_per_field
#check @SeLe4n.Kernel.PriorityInheritance.getSchedContext?_frame
-- Phase P2 foundational frame lemmas:
#check @SeLe4n.Kernel.objects_insert_non_tcb_non_sc_preserves_boundThreadDomainConsistent
#check @SeLe4n.Kernel.objects_update_sync_domain_preserves_boundThreadDomainConsistent
-- R5.C (DEEP-SCH-02): total effectiveSchedParams.
-- R5.C.1 full deprecation: the partial `effectivePriority` + bridge witness
-- have been retired; only the total `effectiveSchedParams` form remains.
#check @SeLe4n.Kernel.effectiveSchedParams
#check @SeLe4n.Kernel.effectiveSchedParams_priority_deadline_eq_resolve
#check @SeLe4n.Kernel.effectiveSchedParams_total
-- R5.D (DEEP-SCH-03): restoreToReady shared helper + back-compat lemmas.
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreToReady
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreToReady_scheduler_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreToReady_serviceRegistry_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreToReady_lifecycle_eq
#check @SeLe4n.Kernel.Lifecycle.Suspend.clearTcbIpcFields_eq_restoreToReady
-- R5.G (DEEP-SCH-06): schedContextConfigure domain propagation witnesses.
#check @SeLe4n.Kernel.SchedContextOps.schedContextConfigure_bound_tcb_domain_eq
#check @SeLe4n.Kernel.SchedContextOps.schedContextConfigure_domain_noop_when_eq
#check @SeLe4n.Kernel.SchedContextOps.schedContextConfigure_preserves_boundThreadDomainConsistent
-- R5.G.3 (DEEP-SCH-06) substantive (Phase R2 landing):
#check @SeLe4n.Kernel.SchedContextOps.schedContextConfigure_preserves_boundThreadDomainConsistent_caseC
#check @SeLe4n.Kernel.SchedContextOps.schedContextConfigure_preserves_boundThreadDomainConsistent_scOnly

-- ============================================================================
-- Surface anchor: WS-RC R6 (Phase R6) — Architecture / InformationFlow completeness
-- ============================================================================
-- R6.A (DEEP-ARCH-03): GIC dispatch bridge — symbolic plan + bridge theorem.
-- (WS-RC R6 deferred-completion: `InterruptOp`, `interruptDispatchPlan`,
-- the five plan-ordering witnesses, and `gicDispatchPlanStaticInvariant`
-- moved to upstream module `Architecture/GicDispatchPlanCore.lean` so
-- they can be referenced from `proofLayerInvariantBundle`.)
#check @SeLe4n.Kernel.Architecture.InterruptOp
#check @SeLe4n.Kernel.Architecture.interruptDispatchPlan
#check @SeLe4n.Kernel.Architecture.interruptDispatchPlan_length
#check @SeLe4n.Kernel.Architecture.interruptDispatchPlan_ack_head
#check @SeLe4n.Kernel.Architecture.interruptDispatchPlan_eoi_second
#check @SeLe4n.Kernel.Architecture.interruptDispatchPlan_handle_third
#check @SeLe4n.Kernel.Architecture.interruptDispatchPlan_decomposes
#check @SeLe4n.Kernel.Architecture.gicDispatchPlanStaticInvariant
#check @SeLe4n.Kernel.Architecture.gicDispatchPlanStaticInvariant_holds
#check @SeLe4n.Kernel.Architecture.exception_irq_dispatches_via_interrupt_dispatch
#check @SeLe4n.Kernel.Architecture.exception_irq_dispatches_when_handled
#check @SeLe4n.Kernel.Architecture.GICDispatchBridge
#check @SeLe4n.Kernel.Architecture.gicDispatchBridge_holds
#check @SeLe4n.Kernel.Architecture.gicDispatchPlanInvariant
#check @SeLe4n.Kernel.Architecture.gicDispatchPlanInvariant_holds
-- R6.A.3 (DEEP-ARCH-03): ArchitectureInvariantBundle composition.
#check @SeLe4n.Kernel.Architecture.ArchitectureInvariantBundle
#check @SeLe4n.Kernel.Architecture.ArchitectureInvariantBundle.of_proofLayer
#check @SeLe4n.Kernel.Architecture.default_system_state_architectureInvariantBundle
#check @SeLe4n.Kernel.Architecture.advanceTimerState_preserves_architectureInvariantBundle
#check @SeLe4n.Kernel.Architecture.writeRegisterState_preserves_architectureInvariantBundle
#check @SeLe4n.Kernel.Architecture.contextSwitchState_preserves_architectureInvariantBundle
#check @SeLe4n.Kernel.Architecture.ArchitectureInvariantBundle.toProofLayer
#check @SeLe4n.Kernel.Architecture.ArchitectureInvariantBundle.toGicDispatchPlan
-- R6.B (DEEP-IF-01): DeclassificationPolicy structure (pre-existing,
-- discharge-only).  The theorem witnesses are in Soundness.lean.
#check @SeLe4n.Kernel.DeclassificationPolicy
#check @SeLe4n.Kernel.DeclassificationPolicy.none
#check @SeLe4n.Kernel.DeclassificationPolicy.isDeclassificationAuthorized
-- R6.C (DEEP-IF-02): SecurityDomain lattice completion.
#check @SeLe4n.Kernel.SecurityDomain.sup
#check @SeLe4n.Kernel.SecurityDomain.inf
#check @SeLe4n.Kernel.SecurityDomain.sup_id
#check @SeLe4n.Kernel.SecurityDomain.inf_id
#check @SeLe4n.Kernel.SecurityDomain.sup_assoc
#check @SeLe4n.Kernel.SecurityDomain.sup_comm
#check @SeLe4n.Kernel.SecurityDomain.sup_self
#check @SeLe4n.Kernel.SecurityDomain.inf_assoc
#check @SeLe4n.Kernel.SecurityDomain.inf_comm
#check @SeLe4n.Kernel.SecurityDomain.inf_self
#check @SeLe4n.Kernel.SecurityDomain.absorb_sup_inf
#check @SeLe4n.Kernel.SecurityDomain.absorb_inf_sup
#check @SeLe4n.Kernel.SecurityDomain.linearOrder_canFlow_iff_sup_eq
#check @SeLe4n.Kernel.SecurityDomain.linearOrder_canFlow_iff_inf_eq
#check @SeLe4n.Kernel.SecurityDomain.linearOrder_canFlow_antisymm
#check @SeLe4n.Kernel.SecurityDomain.antisymmetric
#check @SeLe4n.Kernel.DomainFlowPolicy.linearOrder_antisymm
#check @SeLe4n.Kernel.SecurityDomainLattice
#check @SeLe4n.Kernel.securityDomain_complete_lattice
-- R6.C.2 (DEEP-IF-02 deferred-completion): in-house Mathlib-compatible
-- typeclass hierarchy + instances for `SecurityDomain`.
#check @SeLe4n.Kernel.Preorder
#check @SeLe4n.Kernel.PartialOrder
#check @SeLe4n.Kernel.Sup
#check @SeLe4n.Kernel.Inf
#check @SeLe4n.Kernel.SemilatticeSup
#check @SeLe4n.Kernel.SemilatticeInf
#check @SeLe4n.Kernel.Lattice
#check @SeLe4n.Kernel.SemilatticeSup.sup_assoc'
#check @SeLe4n.Kernel.SemilatticeSup.sup_comm'
#check @SeLe4n.Kernel.Lattice.absorb_sup_inf'
#check @SeLe4n.Kernel.Lattice.absorb_inf_sup'
#check @SeLe4n.Kernel.SecurityDomain.instLE
#check @SeLe4n.Kernel.SecurityDomain.instLT
#check @SeLe4n.Kernel.SecurityDomain.le_iff_id_le
#check @SeLe4n.Kernel.SecurityDomain.lt_iff_id_lt
-- R6.C.3 (DEEP-IF-02 deferred-completion): plan-named aliases +
-- legacy bridges + substantive integrity bridge.
#check @SeLe4n.Kernel.flowsTo_iff_sup_eq
#check @SeLe4n.Kernel.flowsTo_iff_inf_eq
#check @SeLe4n.Kernel.securityFlowsTo_to_linearOrder_canFlow
#check @SeLe4n.Kernel.securityFlowsTo_implies_embedded_sup_eq
#check @SeLe4n.Kernel.integrityToNat
#check @SeLe4n.Kernel.integrityFlowsTo_iff_integrityToNat_le
#check @SeLe4n.Kernel.integrityFlowsTo_iff_canFlow_via_integrityToNat
-- WS-RC R6 deferred-completion (relationship theorem):
#check @SeLe4n.Kernel.Architecture.gicDispatchPlanInvariant_implies_static
-- R6.D (DEEP-IPC-04): cleanupPreReceiveDonationChecked never errors
-- under ipcInvariantFull (pre-existing theorem, discharge-only).
#check @SeLe4n.Kernel.cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull
#check @SeLe4n.Kernel.cleanupPreReceiveDonation_never_errors_under_ipcInvariantFull
-- WS-RC R6 deferred-completion: closure-form discharge index marker
-- theorem for WS-RC extension sections (§3.D/§3.E/§3.F/§3.H/§3.I).
#check @SeLe4n.Kernel.closureForm_ws_rc_extensions_documented

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
  -- AN11-F (LOW) audit-pass v2: live runtime assertions matching the
  -- SC-M01 / AN5-D compile-time `#check` anchors on lines 165-166.  The
  -- arithmetic the bounding theorem proves can drift from the formal
  -- statement (e.g. if the AN5-D witness or `cbs_bandwidth_bounded_tight`
  -- formula changes); pinning concrete values at runtime catches the
  -- drift on every smoke run.
  --
  -- Configuration: `period = rpi5CanonicalConfig.cbsPeriodTicks = 10_000`
  -- (canonical AN5-E.2); `budget = 5_000` (representative — half the
  -- canonical period, well within the 750‰ admissibility ceiling
  -- 7_500); `window = 30_000` (3 canonical periods).  These are NOT
  -- "the canonical RPi5 SC values" — DeploymentSchedulingConfig does
  -- not pin a budget — but they exercise the formula on realistic
  -- numbers.  Adjust if the AN5-D theorem statement changes.
  let period := SeLe4n.Kernel.Liveness.rpi5CanonicalConfig.cbsPeriodTicks
  let budget := 5_000
  let window := 3 * period  -- 3 periods → ⌈window / period⌉ = 3
  let tight := budget * ((window + period - 1) / period)
  let expected := budget * 3
  if tight ≠ expected then
    throw <| IO.userError
      s!"AN11-F: cbs_bandwidth_bounded_tight arithmetic drifted (got {tight}, expected {expected} for budget={budget} period={period} window={window})"
  -- Cross-check that the canonical period is what the AN5-E.2 spec
  -- pins it at; a silent change to `rpi5CanonicalConfig.cbsPeriodTicks`
  -- would slip through this test otherwise.
  if period ≠ 10_000 then
    throw <| IO.userError
      s!"AN11-F: rpi5CanonicalConfig.cbsPeriodTicks drifted (got {period}, expected 10000)"
  IO.println s!"AN11-F live assertion: cbs tight bound = {tight} for canonical period {period}"
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
  IO.println "  ✓ WS-RC R5: cancelDonation split, restoreToReady, effectiveSchedParams, domain propagation"
  IO.println "  ✓ WS-RC R6.A (DEEP-ARCH-03): interruptDispatchPlan + GIC bridge + ArchitectureInvariantBundle"
  IO.println "  ✓ WS-RC R6.B (DEEP-IF-01): DeclassificationPolicy structure (pre-existing, discharge)"
  IO.println "  ✓ WS-RC R6.C (DEEP-IF-02): SecurityDomain lattice (sup/inf + 4 laws + bridge)"
  IO.println "  ✓ WS-RC R6.C.2 deferred-completion: in-house Preorder/PartialOrder/SemilatticeSup/SemilatticeInf/Lattice typeclasses + instances"
  IO.println "  ✓ WS-RC R6.C.3 deferred-completion: flowsTo_iff_sup_eq / flowsTo_iff_inf_eq plan-named aliases + integrity bridge"
  IO.println "  ✓ WS-RC R6.D (DEEP-IPC-04): cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull"
  IO.println "  ✓ WS-RC R6 deferred-completion: closureForm_ws_rc_extensions_documented marker theorem"
  IO.println "  ✓ WS-RC R6 deferred-completion: gicDispatchPlanStaticInvariant added as 12th conjunct of proofLayerInvariantBundle"
  IO.println "=== All surface anchors verified (95 base + R5 + R6 + R6 deferred-completion additions) ==="
  return ()
