-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore

/-!
# WS-SM SM5.F — Per-core PIP theorem inventory

Aggregates the SM5.F per-core priority-inheritance substantive theorems + the
per-core PIP transition defs into a single typed inventory with size and
per-category witnesses.  Mirrors the SM5.C `CrossCoreWakeInventory.lean`, SM5.D
`PerCoreTimerInventory.lean`, and SM5.E `PerCoreIdleInventory.lean` patterns.

Eight categories matching the plan §3.6 / §5 sub-tasks:

* `.compute` — SM5.F.1 `computeMaxWaiterPriorityOnCore` + the per-core ≤ global
  decomposition + frame.
* `.updateBoost` — SM5.F.2 `updatePipBoostOnCore` (per-core bucket migration) +
  bridge / frame / blocking-graph + invariant preservation.
* `.consistent` — SM5.F.3 `pipBoost_perCore_consistent`.
* `.wake` — SM5.F.2 `pipBoostWithWake` cross-core PIP wake semantics.
* `.chain` — SM5.F.4 `propagatePipChainCrossCore` donation chain across cores.
* `.resume` — SM5.F.5 / SM5.F.6 `restoreToReadyOnCore` / `restoreToReadyWithWake`.
* `.blockingGraph` — SM5.F.7 `blockingGraphOnCore_consistent` + SM5.F.8
  `blockingAcyclic_perCore`.
* `.witness` — SM5.F.9 `priorityInheritance_perCore_witness`.

## Identifier validation

Identifiers are compile-time-validated via the `ppit!` macro (mirroring SM5.C's
`ccwt!` / SM5.D's `pctt!` / SM5.E's `pcit!`).  A typo or stale rename fails the
build at this module's elaboration step with "unknown identifier '<name>'".
-/

namespace SeLe4n.Kernel.PriorityInheritance

/-- WS-SM SM5.F: category tag for the SM5.F theorem inventory. -/
inductive PerCorePipCategory where
  /-- SM5.F.1 `computeMaxWaiterPriorityOnCore` + decomposition + frame. -/
  | compute
  /-- SM5.F.2 `updatePipBoostOnCore` per-core bucket migration + frame + preservation. -/
  | updateBoost
  /-- SM5.F.3 `pipBoost_perCore_consistent`. -/
  | consistent
  /-- SM5.F.2 `pipBoostWithWake` cross-core PIP wake semantics. -/
  | wake
  /-- SM5.F.4 `propagatePipChainCrossCore` donation chain across cores. -/
  | chain
  /-- SM5.F.5 / SM5.F.6 `restoreToReadyOnCore` / `restoreToReadyWithWake`. -/
  | resume
  /-- SM5.F.7 / SM5.F.8 per-core blocking graph slice + acyclicity. -/
  | blockingGraph
  /-- SM5.F.9 `priorityInheritance_perCore_witness`. -/
  | witness
  /-- SM5.F.4 memory-model happens-before for the cross-core PIP boost. -/
  | memoryModel
  /-- SM5.F.4 cross-core wake dispatch (the SM6 runtime firing layer). -/
  | dispatch
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM5.F: a theorem entry in the SM5.F inventory.  Records a description,
the fully-qualified name as a `String`, a compile-time elaboration witness, and a
category tag.  The `_elabCheck` field (produced by `ppit!`) forces Lean to resolve
the referenced declaration at construction time. -/
structure PerCorePipTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : PerCorePipCategory
  deriving Repr, Inhabited

/-- WS-SM SM5.F: build a `PerCorePipTheorem` with a compile-time-validated identifier. -/
syntax (name := perCorePipTheoremMacro) "ppit!" str ident term : term

macro_rules
  | `(ppit! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : PerCorePipTheorem))

/-- WS-SM SM5.F: substantive theorem inventory.  Every entry's identifier is
compile-time-validated by `ppit!`. -/
def perCorePipTheorems : List PerCorePipTheorem :=
  [-- ── SM5.F.1 computeMaxWaiterPriorityOnCore (.compute) ──
    ppit! "computeMaxWaiterPriorityOnCore: per-core waiter-priority slice (SM5.F.1)"
      computeMaxWaiterPriorityOnCore .compute,
    ppit! "optPriorityVal: numeric value of an optional priority (none ↦ 0)"
      optPriorityVal .compute,
    ppit! "computeMaxWaiterPriorityOnCore_no_waiters: no on-core waiters ⇒ none"
      computeMaxWaiterPriorityOnCore_no_waiters .compute,
    ppit! "computeMaxWaiterPriorityOnCore_le_global: per-core slice ≤ global boost (SM5.F.1)"
      computeMaxWaiterPriorityOnCore_le_global .compute,
    ppit! "computeMaxWaiterPriorityOnCore_frame: invariant under objects/objectIndex frame"
      computeMaxWaiterPriorityOnCore_frame .compute,
    ppit! "computeMaxWaiterPriority_eq_sup_perCore: global boost = sup over cores of slices (SM5.F.1 completeness)"
      computeMaxWaiterPriority_eq_sup_perCore .compute,
    ppit! "computeMaxWaiterPriority_value: closed numeric form of the global max-waiter priority"
      computeMaxWaiterPriority_value .compute,
    ppit! "computeMaxWaiterPriorityOnCore_value: closed numeric form of the per-core slice"
      computeMaxWaiterPriorityOnCore_value .compute,
    -- ── SM5.F.2 updatePipBoostOnCore (.updateBoost) ──
    ppit! "updatePipBoostOnCore: per-core single-thread PIP boost (bucket migration on core c)"
      updatePipBoostOnCore .updateBoost,
    ppit! "updatePipBoost_eq_updatePipBoostOnCore_bootCore: single-core = per-core at bootCore (bridge)"
      updatePipBoost_eq_updatePipBoostOnCore_bootCore .updateBoost,
    ppit! "updatePipBoostOnCore_preserves_objects_invExt: object-store invariant preserved"
      updatePipBoostOnCore_preserves_objects_invExt .updateBoost,
    ppit! "updatePipBoostOnCore_objects_ne: per-thread object frame (oid ≠ tid)"
      updatePipBoostOnCore_objects_ne .updateBoost,
    ppit! "updatePipBoostOnCore_preserves_objectIndex: objectIndex preserved"
      updatePipBoostOnCore_preserves_objectIndex .updateBoost,
    ppit! "updatePipBoostOnCore_preserves_blockingServer: blocking graph topology preserved"
      updatePipBoostOnCore_preserves_blockingServer .updateBoost,
    ppit! "updatePipBoostOnCore_preserves_blockingAcyclic: blocking acyclicity preserved"
      updatePipBoostOnCore_preserves_blockingAcyclic .updateBoost,
    ppit! "updatePipBoostOnCore_runQueueOnCore_ne: cross-core run-queue frame (c ≠ c')"
      updatePipBoostOnCore_runQueueOnCore_ne .updateBoost,
    ppit! "updatePipBoostOnCore_currentOnCore: never writes any core's current slot"
      updatePipBoostOnCore_currentOnCore .updateBoost,
    ppit! "updatePipBoostOnCore_getTcb?_pipBoost: post-boost pipBoost is the GLOBAL computeMaxWaiterPriority"
      updatePipBoostOnCore_getTcb?_pipBoost .updateBoost,
    ppit! "updatePipBoostOnCore_getTcb?_cpuAffinity: a boost leaves cpuAffinity untouched"
      updatePipBoostOnCore_getTcb?_cpuAffinity .updateBoost,
    ppit! "updatePipBoostOnCore_eq_self_of_getTcb?_none: a boost of a non-TCB is the identity"
      updatePipBoostOnCore_eq_self_of_getTcb?_none .updateBoost,
    ppit! "updatePipBoostOnCore_preserves_determineTargetCore: home-core stability (cpuAffinity unchanged) (SM5.F.4)"
      updatePipBoostOnCore_preserves_determineTargetCore .updateBoost,
    ppit! "updatePipBoostOnCore_establishes_perCore_dominance: post-boost holder dominates every core's slice (SM5.F.3)"
      updatePipBoostOnCore_establishes_perCore_dominance .updateBoost,
    -- ── SM5.F.3 pipBoost_perCore_consistent (.consistent) ──
    ppit! "optPriorityVal_pipBoost_le_effectiveSchedParams: pipBoost ≤ effective priority"
      optPriorityVal_pipBoost_le_effectiveSchedParams .consistent,
    ppit! "pipBoost_perCore_consistent: per-core slice ≤ holder effective priority (SM5.F.3, Thm 3.6.1)"
      pipBoost_perCore_consistent .consistent,
    -- ── SM5.F.2 pipBoostWithWake (.wake) ──
    ppit! "pipBoostWithWake: cross-core PIP wake (state + optional reschedule SGI) (SM5.F.2)"
      pipBoostWithWake .wake,
    ppit! "pipBoostWithWake_state: state component is the per-core boost on the home core"
      pipBoostWithWake_state .wake,
    ppit! "pipBoostWithWake_no_sgi_if_local: local boost emits no SGI"
      pipBoostWithWake_no_sgi_if_local .wake,
    ppit! "pipBoostWithWake_emits_sgi_if_remote: remote material boost emits a reschedule SGI"
      pipBoostWithWake_emits_sgi_if_remote .wake,
    ppit! "pipBoostWithWake_no_sgi_if_noop: a no-op boost emits no SGI (no spurious IPI)"
      pipBoostWithWake_no_sgi_if_noop .wake,
    ppit! "pipBoostWithWake_sgi_is_reschedule: any emitted SGI is .reschedule to the home core"
      pipBoostWithWake_sgi_is_reschedule .wake,
    ppit! "pipBoostWithWake_emits_at_most_one_sgi: at most one SGI per boost (no storm)"
      pipBoostWithWake_emits_at_most_one_sgi .wake,
    ppit! "pipBoostWithWake_preserves_objects_invExt: object-store invariant preserved"
      pipBoostWithWake_preserves_objects_invExt .wake,
    ppit! "pipBoostWithWake_preserves_blockingAcyclic: blocking acyclicity preserved"
      pipBoostWithWake_preserves_blockingAcyclic .wake,
    ppit! "pipBoostWithWake_bootCore_unbound: single-core bridge (unbound on boot ⇒ updatePipBoost, no SGI)"
      pipBoostWithWake_bootCore_unbound .wake,
    ppit! "pipBoostWithWake_no_sgi_if_not_runnable: a boost of a non-runnable holder fires no SGI (C9 precision)"
      pipBoostWithWake_no_sgi_if_not_runnable .wake,
    -- ── SM5.F.4 propagatePipChainCrossCore (.chain) ──
    ppit! "propagatePipChainCrossCore: donation chain across cores (state + SGI list) (SM5.F.4)"
      propagatePipChainCrossCore .chain,
    ppit! "propagatePipChainCrossCore_zero: zero fuel is identity"
      propagatePipChainCrossCore_zero .chain,
    ppit! "propagatePipChainCrossCore_step: one chain-walk step unfolding"
      propagatePipChainCrossCore_step .chain,
    ppit! "propagatePipChainCrossCoreState: state-only projection of the chain walk"
      propagatePipChainCrossCoreState .chain,
    ppit! "propagatePipChainCrossCoreState_zero: state projection at zero fuel"
      propagatePipChainCrossCoreState_zero .chain,
    ppit! "propagatePipChainCrossCoreState_step: state projection one-step recursion"
      propagatePipChainCrossCoreState_step .chain,
    ppit! "propagatePipChainCrossCore_preserves_objects_invExt: chain walk preserves object-store invariant"
      propagatePipChainCrossCore_preserves_objects_invExt .chain,
    ppit! "propagatePipChainCrossCore_preserves_blockingAcyclic: chain walk preserves blocking acyclicity"
      propagatePipChainCrossCore_preserves_blockingAcyclic .chain,
    ppit! "propagatePipChainCrossCore_zero_sgis: zero fuel collects no SGIs"
      propagatePipChainCrossCore_zero_sgis .chain,
    ppit! "propagatePipChainCrossCore_no_sgis_head_terminal: terminal head ⇒ SGI list is the head SGI"
      propagatePipChainCrossCore_no_sgis_head_terminal .chain,
    ppit! "propagatePipChainCrossCore_head_sgi_remote: a remote material chain head contributes its SGI"
      propagatePipChainCrossCore_head_sgi_remote .chain,
    ppit! "propagatePipChainCrossCore_head_emission_mem: the head's SGI is in the collected list (SM5.F.4)"
      propagatePipChainCrossCore_head_emission_mem .chain,
    ppit! "propagatePipChainCrossCore_tail_sgis_mem: every tail SGI lifts to the root list (SM5.F.4)"
      propagatePipChainCrossCore_tail_sgis_mem .chain,
    ppit! "propagatePipChainCrossCore_sgis_all_reschedule: every chain SGI is a .reschedule (well-formed)"
      propagatePipChainCrossCore_sgis_all_reschedule .chain,
    ppit! "propagatePipChainCrossCore_sgi_length_le_fuel: the SGI list is bounded by fuel (no storm)"
      propagatePipChainCrossCore_sgi_length_le_fuel .chain,
    ppit! "propagatePipChainCrossCore_second_link_sgi_remote: a remote second link contributes its SGI (depth-2)"
      propagatePipChainCrossCore_second_link_sgi_remote .chain,
    ppit! "propagatePipChainCrossCore_singleCore_no_sgis: single-core walk fires no SGI (no spurious IPI)"
      propagatePipChainCrossCore_singleCore_no_sgis .chain,
    ppit! "propagatePipChainCrossCoreState_singleCore_eq_propagate: single-core walk = legacy propagate (behaviour-identical)"
      propagatePipChainCrossCoreState_singleCore_eq_propagate .chain,
    -- ── SM5.F.5 / SM5.F.6 restoreToReadyOnCore / restoreToReadyWithWake (.resume) ──
    ppit! "restoreToReadyOnCore: per-core resume re-ready + PIP recompute + enqueue (SM5.F.5)"
      SeLe4n.Kernel.Lifecycle.Suspend.restoreToReadyOnCore .resume,
    ppit! "restoreToReadyWithWake: cross-core resume wake (state + optional SGI) (SM5.F.6)"
      SeLe4n.Kernel.Lifecycle.Suspend.restoreToReadyWithWake .resume,
    ppit! "restoreToReady_objects_invExt: restoreToReady preserves the object-store invariant"
      restoreToReady_objects_invExt .resume,
    ppit! "restoreToReadyOnCore_preserves_objects_invExt: per-core resume preserves invExt"
      restoreToReadyOnCore_preserves_objects_invExt .resume,
    ppit! "restoreToReadyOnCore_currentOnCore: per-core resume never writes a current slot"
      restoreToReadyOnCore_currentOnCore .resume,
    ppit! "restoreToReadyOnCore_runQueueOnCore_ne: per-core resume cross-core run-queue frame"
      restoreToReadyOnCore_runQueueOnCore_ne .resume,
    ppit! "restoreToReadyOnCore_pipBoost_recomputed: pipBoost recomputed from the GLOBAL graph (SM5.F.6)"
      restoreToReadyOnCore_pipBoost_recomputed .resume,
    ppit! "restoreToReadyWithWake_state: state component is the per-core resume on the home core"
      restoreToReadyWithWake_state .resume,
    ppit! "restoreToReadyWithWake_no_sgi_if_local: local resume emits no SGI"
      restoreToReadyWithWake_no_sgi_if_local .resume,
    ppit! "restoreToReadyWithWake_emits_sgi_if_remote: remote resume emits a reschedule SGI"
      restoreToReadyWithWake_emits_sgi_if_remote .resume,
    ppit! "restoreToReadyWithWake_sgi_is_reschedule: any emitted resume SGI is .reschedule to the home core"
      restoreToReadyWithWake_sgi_is_reschedule .resume,
    ppit! "restoreToReadyWithWake_preserves_objects_invExt: cross-core resume preserves invExt"
      restoreToReadyWithWake_preserves_objects_invExt .resume,
    ppit! "resumeReadyMidState_getTcb?_ready: the resume mid-state's TCB is .Ready (SM5.F.6)"
      resumeReadyMidState_getTcb?_ready .resume,
    ppit! "resumeReadyMidState_objects_invExt: the resume mid-state preserves the object-store invariant"
      resumeReadyMidState_objects_invExt .resume,
    ppit! "resumeThreadOnCore_sets_threadState: the complete per-core resume sets threadState := .Ready (SM5.F.6)"
      resumeThreadOnCore_sets_threadState .resume,
    ppit! "resumeThreadOnCore_preserves_objects_invExt: the complete resume preserves the object-store invariant"
      resumeThreadOnCore_preserves_objects_invExt .resume,
    ppit! "resumeThreadOnCore_rejects_non_inactive: resume of a non-Inactive TCB → illegalState"
      resumeThreadOnCore_rejects_non_inactive .resume,
    ppit! "resumeThreadOnCore_rejects_non_tcb: resume of a non-TCB → invalidArgument"
      resumeThreadOnCore_rejects_non_tcb .resume,
    ppit! "resumeThreadOnCore_local_no_sgi: a local complete resume fires no SGI"
      resumeThreadOnCore_local_no_sgi .resume,
    ppit! "resumeThreadOnCore_remote_sgi: a remote complete resume fires a .reschedule SGI to the home core"
      resumeThreadOnCore_remote_sgi .resume,
    -- ── SM5.F.7 / SM5.F.8 per-core blocking graph (.blockingGraph) ──
    ppit! "blockingServerOnCore: per-core slice of the blocking graph (SM5.F.7)"
      blockingServerOnCore .blockingGraph,
    ppit! "blockingServerOnCore_eq_global_of_onCore: on-core slice = global edge"
      blockingServerOnCore_eq_global_of_onCore .blockingGraph,
    ppit! "blockingServerOnCore_none_of_offCore: off-core ⇒ no slice edge"
      blockingServerOnCore_none_of_offCore .blockingGraph,
    ppit! "blockingServerOnCore_implies_global: every per-core edge is a global edge"
      blockingServerOnCore_implies_global .blockingGraph,
    ppit! "blockingServerOnCore_subgraph: per-core slice is a subgraph of the global graph"
      blockingServerOnCore_subgraph .blockingGraph,
    ppit! "blockingGraphOnCore_consistent: global graph = union of per-core slices (SM5.F.7)"
      blockingGraphOnCore_consistent .blockingGraph,
    ppit! "blockingChainOnCore: per-core blocking chain (sub-walk of the global chain)"
      blockingChainOnCore .blockingGraph,
    ppit! "blockingChainOnCore_subset: per-core chain ⊆ global chain"
      blockingChainOnCore_subset .blockingGraph,
    ppit! "blockingAcyclicOnCore: per-core blocking-acyclicity predicate"
      blockingAcyclicOnCore .blockingGraph,
    ppit! "blockingAcyclic_perCore: the per-core blocking slice is acyclic (SM5.F.8)"
      blockingAcyclic_perCore .blockingGraph,
    -- ── SM5.F.9 priorityInheritance_perCore_witness (.witness) ──
    ppit! "priorityInheritance_perCore_witness: aggregate per-core PIP soundness witness (SM5.F.9)"
      priorityInheritance_perCore_witness .witness,
    ppit! "priorityInheritance_perCore_witness_full: aggregate witness + exact decomposition (SM5.F.9 completeness)"
      priorityInheritance_perCore_witness_full .witness,
    -- ── SM5.F.4 memory-model happens-before (.memoryModel) ──
    ppit! "pipBoostOrdering_synchronizesWith: the boost release synchronizes-with the home-core acquire (SM5.F.4)"
      pipBoostOrdering_synchronizesWith .memoryModel,
    ppit! "pipBoostOrdering_happensBefore: the boost publication happens-before the home core observes it (SM5.F.4)"
      pipBoostOrdering_happensBefore .memoryModel,
    -- ── SM5.F.4 cross-core wake dispatch (.dispatch) ──
    ppit! "computeCrossCoreSgis: diff-based cross-core SGI dispatch decision (SM5.F.4)"
      computeCrossCoreSgis .dispatch,
    ppit! "computeCrossCoreSgis_all_reschedule: every dispatched SGI is a .reschedule"
      computeCrossCoreSgis_all_reschedule .dispatch,
    ppit! "computeCrossCoreSgis_nil_single_core: the diff dispatch is inert ([]) on single-core"
      computeCrossCoreSgis_nil_single_core .dispatch,
    ppit! "crossCoreWakeDispatch: the BaseIO syscall-path cross-core wake dispatch (fires the SGIs)"
      crossCoreWakeDispatch .dispatch,
    ppit! "crossCoreWakeDispatch_singleCore: the syscall dispatch is inert (pure ()) on single-core"
      crossCoreWakeDispatch_singleCore .dispatch,
    ppit! "pipChainWakeDispatch: the BaseIO chain-boost cross-core wake dispatch (fires the chain SGIs)"
      pipChainWakeDispatch .dispatch,
    ppit! "pipChainWakeDispatch_singleCore: the chain dispatch is inert (pure ()) on single-core"
      pipChainWakeDispatch_singleCore .dispatch,
    ppit! "emitBoostWakeSgi: the single-SGI boost/resume dispatch (lifts emitWakeSgi)"
      emitBoostWakeSgi .dispatch]

/-- WS-SM SM5.F: the inventory has 95 substantive entries (61 at the SM5.F landing +
34 from the completion pass: full per-core decomposition, post-boost dominance, chain
SGI completeness, the runnability-gate, memory-model HB, the complete `resumeThreadOnCore`,
and the cross-core wake dispatch).  A regression that adds a new SM5.F theorem without
registering it fails this count witness at the Tier-3 surface check. -/
theorem perCorePipTheorems_count : perCorePipTheorems.length = 95 := by decide

/-- WS-SM SM5.F: 8 entries in the `compute` category (SM5.F.1). -/
theorem perCorePipTheorems_compute_count :
    (perCorePipTheorems.filter (fun t => t.category == .compute)).length = 8 := by decide

/-- WS-SM SM5.F: 14 entries in the `updateBoost` category (SM5.F.2). -/
theorem perCorePipTheorems_updateBoost_count :
    (perCorePipTheorems.filter (fun t => t.category == .updateBoost)).length = 14 := by decide

/-- WS-SM SM5.F: 2 entries in the `consistent` category (SM5.F.3). -/
theorem perCorePipTheorems_consistent_count :
    (perCorePipTheorems.filter (fun t => t.category == .consistent)).length = 2 := by decide

/-- WS-SM SM5.F: 11 entries in the `wake` category (SM5.F.2). -/
theorem perCorePipTheorems_wake_count :
    (perCorePipTheorems.filter (fun t => t.category == .wake)).length = 11 := by decide

/-- WS-SM SM5.F: 18 entries in the `chain` category (SM5.F.4). -/
theorem perCorePipTheorems_chain_count :
    (perCorePipTheorems.filter (fun t => t.category == .chain)).length = 18 := by decide

/-- WS-SM SM5.F: 20 entries in the `resume` category (SM5.F.5 / SM5.F.6). -/
theorem perCorePipTheorems_resume_count :
    (perCorePipTheorems.filter (fun t => t.category == .resume)).length = 20 := by decide

/-- WS-SM SM5.F: 10 entries in the `blockingGraph` category (SM5.F.7 / SM5.F.8). -/
theorem perCorePipTheorems_blockingGraph_count :
    (perCorePipTheorems.filter (fun t => t.category == .blockingGraph)).length = 10 := by decide

/-- WS-SM SM5.F: 2 entries in the `witness` category (SM5.F.9). -/
theorem perCorePipTheorems_witness_count :
    (perCorePipTheorems.filter (fun t => t.category == .witness)).length = 2 := by decide

/-- WS-SM SM5.F: 2 entries in the `memoryModel` category (SM5.F.4 happens-before). -/
theorem perCorePipTheorems_memoryModel_count :
    (perCorePipTheorems.filter (fun t => t.category == .memoryModel)).length = 2 := by decide

/-- WS-SM SM5.F: 8 entries in the `dispatch` category (SM5.F.4 cross-core wake firing). -/
theorem perCorePipTheorems_dispatch_count :
    (perCorePipTheorems.filter (fun t => t.category == .dispatch)).length = 8 := by decide

/-- WS-SM SM5.F: per-category counts sum to the total. -/
theorem perCorePipTheorems_partition_sum :
    (perCorePipTheorems.filter (fun t => t.category == .compute)).length +
    (perCorePipTheorems.filter (fun t => t.category == .updateBoost)).length +
    (perCorePipTheorems.filter (fun t => t.category == .consistent)).length +
    (perCorePipTheorems.filter (fun t => t.category == .wake)).length +
    (perCorePipTheorems.filter (fun t => t.category == .chain)).length +
    (perCorePipTheorems.filter (fun t => t.category == .resume)).length +
    (perCorePipTheorems.filter (fun t => t.category == .blockingGraph)).length +
    (perCorePipTheorems.filter (fun t => t.category == .witness)).length +
    (perCorePipTheorems.filter (fun t => t.category == .memoryModel)).length +
    (perCorePipTheorems.filter (fun t => t.category == .dispatch)).length =
    perCorePipTheorems.length := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.F: every inventory identifier is unique.  Kernel-sound `decide`
(not `native_decide`): a duplicate identifier — which `native_decide` could mask by
trusting the compiled evaluation — fails this proof in the kernel.  The elevated
`maxRecDepth` only raises the recursion *limit* for the `Nodup` decision procedure
(no extra work, no axioms; the proof stays a kernel-checked `of_decide_eq_true`). -/
theorem perCorePipTheorems_identifiers_nodup :
    (perCorePipTheorems.map (·.identifier)).Nodup := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.F: every inventory description is unique.  Kernel-sound `decide` under
an elevated `maxRecDepth` (see `perCorePipTheorems_identifiers_nodup`). -/
theorem perCorePipTheorems_descriptions_nodup :
    (perCorePipTheorems.map (·.description)).Nodup := by decide

end SeLe4n.Kernel.PriorityInheritance
