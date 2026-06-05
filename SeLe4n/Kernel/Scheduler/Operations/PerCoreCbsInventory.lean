-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs

/-!
# WS-SM SM5.H — Theorem inventory

Aggregates the SM5.H per-core CBS substantive theorems into a single typed
inventory with size and per-category witnesses.  Mirrors the SM5.G
`PerCoreDomainInventory.lean` and SM5.E `PerCoreIdleInventory.lean` patterns.

Ten categories matching the plan §3.8 / §5 sub-tasks (119 entries — the original
seven plus `.lockSet` (§10 cross-domain footprints), `.liveTick` (§14 A2/A4
live-tick CBS bridge), and `.memoryModel` (§15 C10 cross-core happens-before);
audit-pass-2 added the §17 D15 composite + §18 SGI characterisation + tightened
C10 happens-before):

* `.predicate` — SM5.H.1 / SM5.H.5: the per-core CBS affinity-consistency invariant
  `replenishQueueAffinityConsistentOnCore` (+ the SMP form, default-state, frame).
* `.replenish` — SM5.H.2: the per-core CBS scheduling primitive `replenishOnCore`
  and its frame / membership lemmas.
* `.preservation` — SM5.H.3 / SM5.H.6 / SM5.H.5: `replenishOnCore` preserves
  replenish-queue validity, pipeline order, and affinity consistency.
* `.migration` — SM5.H.4: `migrateSchedContextReplenishment` (the SchedContext
  replenishment migration) — frames, the structural "moves the entries" facts, and
  validity / pipeline preservation.
* `.affinityWrite` — SM5.H.4: the affinity-write helper lemmas
  (`determineTargetCore` congruence, `setThreadCpuAffinity` SchedContext / home-core
  frames) the composite restoration proof rests on.
* `.consistency` — SM5.H.4 / SM5.H.5: the migration's affinity establish / preserve
  lemmas, the composite `setThreadCpuAffinityWithMigration`, and the headline
  restoration theorem `schedContextMigration_consistent`.
* `.budget` — SM5.H.7: the aggregate `perCoreCbsInvariant` (+ default + the
  `replenishOnCore` bundle preservation) and the CBS budget-bound accounting
  theorems.

## Identifier validation

Identifiers are compile-time-validated via the `pccbst!` macro, mirroring SM5.G's
`pcdt!`.  A typo or stale rename fails the build at this module's elaboration step
with "unknown identifier '<name>'".
-/

namespace SeLe4n.Kernel

/-- WS-SM SM5.H: category tag for the SM5.H theorem inventory. -/
inductive PerCoreCbsCategory where
  /-- SM5.H.1 / .5 the per-core CBS affinity-consistency invariant + SMP form / default / frame. -/
  | predicate
  /-- SM5.H.2 the `replenishOnCore` scheduling primitive + frames + membership. -/
  | replenish
  /-- SM5.H.3 / .6 / .5 `replenishOnCore` validity / pipeline / affinity preservation. -/
  | preservation
  /-- SM5.H.4 the `migrateSchedContextReplenishment` op + frames + structural + validity/pipeline. -/
  | migration
  /-- SM5.H.4 the affinity-write helper lemmas. -/
  | affinityWrite
  /-- SM5.H.4 / .5 the migration affinity establish/preserve + composite + headline restoration. -/
  | consistency
  /-- SM5.H.7 the per-core CBS invariant bundle + budget-bound accounting. -/
  | budget
  /-- SM5.H.4 the cross-domain lock-set footprints (`replenishOnCoreLockSet`,
      the two migration footprints, and the composite footprint) + ordering witnesses. -/
  | lockSet
  /-- SM5.H.2 (A2/A4) the live-tick CBS bridge — the replenish-queue frame chain
      (`updatePipBoost` / `revert` / `ensureRunnable` / `timeoutThread` /
      `timeoutBlockedThreads`), the `replenishOnCore` characterisation of the live
      tick, and the tick's replenish-queue-validity preservation. -/
  | liveTick
  /-- SM5.H.4 (C10) the migration's cross-core memory-model happens-before. -/
  | memoryModel
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM5.H: a theorem entry in the SM5.H inventory.  Records a description,
the fully-qualified name as a `String`, a compile-time elaboration witness, and a
category tag.  The `_elabCheck` field (produced by `pccbst!`) forces Lean to resolve
the referenced declaration at construction time. -/
structure PerCoreCbsTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : PerCoreCbsCategory
  deriving Repr, Inhabited

/-- WS-SM SM5.H: build a `PerCoreCbsTheorem` with a compile-time-validated identifier. -/
syntax (name := perCoreCbsTheoremMacro) "pccbst!" str ident term : term

macro_rules
  | `(pccbst! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : PerCoreCbsTheorem))

/-- WS-SM SM5.H: substantive theorem inventory.  Every entry's identifier is
compile-time-validated by `pccbst!`. -/
def perCoreCbsTheorems : List PerCoreCbsTheorem :=
  [-- ── SM5.H.1 / .5 the affinity-consistency invariant (.predicate) ──
    pccbst! "replenishQueueAffinityConsistentOnCore: the plan §3.8 Theorem 3.8.1 per-core CBS affinity invariant (SM5.H.5)"
      replenishQueueAffinityConsistentOnCore .predicate,
    pccbst! "replenishQueueAffinityConsistent_smp: the SMP-wide affinity-consistency invariant"
      replenishQueueAffinityConsistent_smp .predicate,
    pccbst! "replenishQueueAffinityConsistent_smp_at: the SMP form extracts the per-core form"
      replenishQueueAffinityConsistent_smp_at .predicate,
    pccbst! "default_replenishQueueAffinityConsistentOnCore: boot is affinity-consistent on every core"
      default_replenishQueueAffinityConsistentOnCore .predicate,
    pccbst! "default_replenishQueueAffinityConsistent_smp: boot is SMP-affinity-consistent"
      default_replenishQueueAffinityConsistent_smp .predicate,
    pccbst! "replenishQueueAffinityConsistentOnCore_frame: the invariant's read-footprint frame"
      replenishQueueAffinityConsistentOnCore_frame .predicate,
    -- ── SM5.H.2 the replenishOnCore primitive (.replenish) ──
    pccbst! "replenishOnCore: the per-core CBS replenishment-scheduling primitive (SM5.H.2)"
      replenishOnCore .replenish,
    pccbst! "replenishOnCore_objects: scheduling never touches the object store"
      replenishOnCore_objects .replenish,
    pccbst! "replenishOnCore_machine: scheduling never advances the machine timer"
      replenishOnCore_machine .replenish,
    pccbst! "replenishOnCore_getTcb?: scheduling frames every TCB resolution"
      replenishOnCore_getTcb? .replenish,
    pccbst! "replenishOnCore_getSchedContext?: scheduling frames every SchedContext resolution"
      replenishOnCore_getSchedContext? .replenish,
    pccbst! "replenishOnCore_determineTargetCore: scheduling frames every thread's home core"
      replenishOnCore_determineTargetCore .replenish,
    pccbst! "replenishOnCore_replenishQueueOnCore_self: core c's queue is the old queue + the insert"
      replenishOnCore_replenishQueueOnCore_self .replenish,
    pccbst! "replenishOnCore_replenishQueueOnCore_ne: scheduling frames a different core's queue"
      replenishOnCore_replenishQueueOnCore_ne .replenish,
    pccbst! "replenishOnCore_runQueueOnCore: scheduling frames every run queue"
      replenishOnCore_runQueueOnCore .replenish,
    pccbst! "replenishOnCore_currentOnCore: scheduling frames every current thread"
      replenishOnCore_currentOnCore .replenish,
    pccbst! "replenishOnCore_activeDomainOnCore: scheduling frames every active domain"
      replenishOnCore_activeDomainOnCore .replenish,
    pccbst! "replenishOnCore_mem: the scheduled entry is a member of the post-state queue"
      replenishOnCore_mem .replenish,
    -- ── SM5.H.3 / .6 / .5 replenishOnCore preservation (.preservation) ──
    pccbst! "replenishOnCore_preserves_replenishQueueValidOnCore: validity preserved on core c (SM5.H.3)"
      replenishOnCore_preserves_replenishQueueValidOnCore .preservation,
    pccbst! "replenishOnCore_preserves_replenishQueueValidOnCore_ne: validity preserved on another core"
      replenishOnCore_preserves_replenishQueueValidOnCore_ne .preservation,
    pccbst! "replenishOnCore_preserves_replenishQueueValid_smp: validity preserved on every core (SM5.H.3)"
      replenishOnCore_preserves_replenishQueueValid_smp .preservation,
    pccbst! "replenishOnCore_preserves_replenishmentPipelineOrderOnCore: pipeline order preserved on core c (SM5.H.6)"
      replenishOnCore_preserves_replenishmentPipelineOrderOnCore .preservation,
    pccbst! "replenishOnCore_preserves_replenishmentPipelineOrderOnCore_ne: pipeline order preserved on another core"
      replenishOnCore_preserves_replenishmentPipelineOrderOnCore_ne .preservation,
    pccbst! "replenishOnCore_preserves_replenishQueueAffinityConsistentOnCore: affinity consistency preserved (SM5.H.5)"
      replenishOnCore_preserves_replenishQueueAffinityConsistentOnCore .preservation,
    -- ── SM5.H.4 the migration operation (.migration) ──
    pccbst! "migrateSchedContextReplenishment: the SchedContext replenishment migration (SM5.H.4)"
      migrateSchedContextReplenishment .migration,
    pccbst! "migrateSchedContextReplenishment_noop: a self-migration is the identity"
      migrateSchedContextReplenishment_noop .migration,
    pccbst! "migrateSchedContextReplenishment_objects: the migration never touches the object store"
      migrateSchedContextReplenishment_objects .migration,
    pccbst! "migrateSchedContextReplenishment_machine: the migration never advances the timer"
      migrateSchedContextReplenishment_machine .migration,
    pccbst! "migrateSchedContextReplenishment_getSchedContext?: the migration frames SchedContext resolution"
      migrateSchedContextReplenishment_getSchedContext? .migration,
    pccbst! "migrateSchedContextReplenishment_determineTargetCore: the migration frames every home core"
      migrateSchedContextReplenishment_determineTargetCore .migration,
    pccbst! "migrateSchedContextReplenishment_replenishQueueOnCore_to: destination queue = fold of inserts"
      migrateSchedContextReplenishment_replenishQueueOnCore_to .migration,
    pccbst! "migrateSchedContextReplenishment_replenishQueueOnCore_from: source queue = pre-state with scId removed"
      migrateSchedContextReplenishment_replenishQueueOnCore_from .migration,
    pccbst! "migrateSchedContextReplenishment_replenishQueueOnCore_other: other cores' queues untouched"
      migrateSchedContextReplenishment_replenishQueueOnCore_other .migration,
    pccbst! "migrateSchedContextReplenishment_fromCore_excludes_scId: no scId entry remains on the source core"
      migrateSchedContextReplenishment_fromCore_excludes_scId .migration,
    pccbst! "migrateSchedContextReplenishment_mem_toCore: destination membership decomposition (old or moved)"
      migrateSchedContextReplenishment_mem_toCore .migration,
    pccbst! "migrateSchedContextReplenishment_preserves_replenishQueueValid_smp: validity preserved on every core (SM5.H.3)"
      migrateSchedContextReplenishment_preserves_replenishQueueValid_smp .migration,
    pccbst! "migrateSchedContextReplenishment_preserves_replenishmentPipelineOrder_smp: pipeline order preserved (SM5.H.6)"
      migrateSchedContextReplenishment_preserves_replenishmentPipelineOrder_smp .migration,
    -- ── SM5.H.4 affinity-write helpers (.affinityWrite) ──
    pccbst! "determineTargetCore_congr_getTcb?: equal TCB resolutions give equal home cores"
      determineTargetCore_congr_getTcb? .affinityWrite,
    pccbst! "setThreadCpuAffinity_determineTargetCore_ne: the affinity write frames other threads' home cores"
      setThreadCpuAffinity_determineTargetCore_ne .affinityWrite,
    pccbst! "setThreadCpuAffinity_getSchedContext?: the affinity write frames SchedContext resolution"
      setThreadCpuAffinity_getSchedContext? .affinityWrite,
    -- ── SM5.H.4 / .5 migration affinity behaviour + composite + headline (.consistency) ──
    pccbst! "migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_to: establishes consistency on the destination"
      migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_to .consistency,
    pccbst! "migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_from: establishes consistency on the source"
      migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_from .consistency,
    pccbst! "migrateSchedContextReplenishment_preserves_affinityConsistentOnCore_other: preserves consistency elsewhere"
      migrateSchedContextReplenishment_preserves_affinityConsistentOnCore_other .consistency,
    pccbst! "setThreadCpuAffinityWithMigration: the affinity-change + replenishment-migration composite (SM5.H.4)"
      setThreadCpuAffinityWithMigration .consistency,
    pccbst! "setThreadCpuAffinityWithMigration_error_of_no_tcb: the composite is fail-closed on a non-TCB target"
      setThreadCpuAffinityWithMigration_error_of_no_tcb .consistency,
    pccbst! "setThreadCpuAffinityWithMigration_bound_state_eq: the bound-case composite is affinity-write then replenishment-migration then run-queue-migration"
      setThreadCpuAffinityWithMigration_bound_state_eq .consistency,
    pccbst! "setThreadCpuAffinityWithMigration_unbound_state_eq: the unbound-case composite is the affinity write then the run-queue migration"
      setThreadCpuAffinityWithMigration_unbound_state_eq .consistency,
    pccbst! "schedContextMigration_consistent: the composite RESTORES affinity consistency on every core (SM5.H.4 headline)"
      schedContextMigration_consistent .consistency,
    -- ── SM5.H.7 per-core CBS invariant + budget accounting (.budget) ──
    pccbst! "perCoreCbsInvariant: the aggregate per-core CBS invariant (validity + pipeline + affinity) (SM5.H.7)"
      perCoreCbsInvariant .budget,
    pccbst! "default_perCoreCbsInvariant: boot satisfies the per-core CBS invariant"
      default_perCoreCbsInvariant .budget,
    pccbst! "replenishOnCore_preserves_perCoreCbsInvariant: scheduling maintains the per-core CBS invariant (SM5.H.7)"
      replenishOnCore_preserves_perCoreCbsInvariant .budget,
    pccbst! "consumeBudget_preserves_le_budget: charging budget preserves the CBS bandwidth bound (SM5.H.7)"
      consumeBudget_preserves_le_budget .budget,
    pccbst! "applyRefill_preserves_le_budget: replenishment establishes the CBS bandwidth bound (SM5.H.7)"
      applyRefill_preserves_le_budget .budget,
    pccbst! "scheduleReplenishment_replenishments_bounded: the replenishment schedule stays within maxReplenishments (SM5.H.7)"
      scheduleReplenishment_replenishments_bounded .budget,
    -- ── SM5.H.2 (B8) the faithful sc-based scheduling primitive (.replenish) ──
    pccbst! "replenishScOnCore: the faithful sc-based CBS scheduling primitive (SM5.H.2)"
      replenishScOnCore .replenish,
    pccbst! "replenishScOnCore_eq: the sc-based primitive is the scId-keyed replenishOnCore at now + sc.period"
      replenishScOnCore_eq .replenish,
    pccbst! "replenishScOnCore_objects: the sc-based primitive never touches the object store"
      replenishScOnCore_objects .replenish,
    pccbst! "replenishScOnCore_preserves_replenishmentPipelineOrderOnCore: UNCONDITIONAL pipeline-order preservation (from period > 0)"
      replenishScOnCore_preserves_replenishmentPipelineOrderOnCore .replenish,
    pccbst! "replenishScOnCore_preserves_replenishmentPipelineOrderOnCore_of_wf: wf-keyed pipeline-order preservation variant"
      replenishScOnCore_preserves_replenishmentPipelineOrderOnCore_of_wf .replenish,
    -- ── SM5.H.4 (§9) object-store invariant preservation (.preservation) ──
    pccbst! "replenishOnCore_preserves_objects_invExt: scheduling preserves the object-store invariant"
      replenishOnCore_preserves_objects_invExt .preservation,
    pccbst! "migrateSchedContextReplenishment_preserves_objects_invExt: the replenishment migration preserves the object-store invariant"
      migrateSchedContextReplenishment_preserves_objects_invExt .preservation,
    -- ── SM5.H.4 (§6c) the full-thread-migration run-queue move (.migration) ──
    pccbst! "migrateRunQueueOnAffinityChange: the run-queue migration on an affinity change (SM5.H.4 full thread migration)"
      migrateRunQueueOnAffinityChange .migration,
    pccbst! "migrateRunQueueOnAffinityChange_objects: the run-queue migration never touches the object store"
      migrateRunQueueOnAffinityChange_objects .migration,
    pccbst! "migrateRunQueueOnAffinityChange_machine: the run-queue migration never advances the timer"
      migrateRunQueueOnAffinityChange_machine .migration,
    pccbst! "migrateRunQueueOnAffinityChange_replenishQueueOnCore: the run-queue migration frames every replenish queue"
      migrateRunQueueOnAffinityChange_replenishQueueOnCore .migration,
    pccbst! "migrateRunQueueOnAffinityChange_getSchedContext?: the run-queue migration frames SchedContext resolution"
      migrateRunQueueOnAffinityChange_getSchedContext? .migration,
    pccbst! "migrateRunQueueOnAffinityChange_determineTargetCore: the run-queue migration frames every home core"
      migrateRunQueueOnAffinityChange_determineTargetCore .migration,
    pccbst! "migrateSchedContextReplenishment_runQueueOnCore: the replenishment migration frames every run queue"
      migrateSchedContextReplenishment_runQueueOnCore .migration,
    pccbst! "migrateRunQueueOnAffinityChange_preserves_objects_invExt: the run-queue migration preserves the object-store invariant"
      migrateRunQueueOnAffinityChange_preserves_objects_invExt .migration,
    pccbst! "schedContextReplMigration_consistent: the replenishment migration restores affinity consistency (generalized over affinity)"
      schedContextReplMigration_consistent .migration,
    -- ── SM5.H.4 (§11/§12/§13) composite preservation + grounding (.consistency) ──
    pccbst! "schedContextBindingConsistent_boundThread_unique: B7 — a thread is bound by at most one SchedContext (grounds hUnique)"
      schedContextBindingConsistent_boundThread_unique .consistency,
    pccbst! "schedContextMigration_consistent_of_bindingConsistent: B7 grounded headline (hUnique discharged from schedContextBindingConsistent)"
      schedContextMigration_consistent_of_bindingConsistent .consistency,
    pccbst! "setThreadCpuAffinity_machine: the affinity write leaves the machine state untouched"
      setThreadCpuAffinity_machine .consistency,
    pccbst! "migrateRunQueueOnAffinityChange_preserves_runQueueOnCoreWellFormed: the run-queue migration preserves run-queue well-formedness on every core"
      migrateRunQueueOnAffinityChange_preserves_runQueueOnCoreWellFormed .consistency,
    pccbst! "setThreadCpuAffinityWithMigration_preserves_runQueueOnCoreWellFormed: the composite preserves run-queue well-formedness (SM5.H.4)"
      setThreadCpuAffinityWithMigration_preserves_runQueueOnCoreWellFormed .consistency,
    pccbst! "setThreadCpuAffinityWithMigration_preserves_replenishQueueValid_smp: A5 — the composite preserves replenish-queue validity on every core"
      setThreadCpuAffinityWithMigration_preserves_replenishQueueValid_smp .consistency,
    pccbst! "setThreadCpuAffinityWithMigration_preserves_replenishmentPipelineOrder_smp: A5 — the composite preserves pipeline order on every core"
      setThreadCpuAffinityWithMigration_preserves_replenishmentPipelineOrder_smp .consistency,
    pccbst! "setThreadCpuAffinityWithMigration_preserves_perCoreCbsInvariant_smp: A5 — the composite preserves the FULL per-core CBS invariant on every core"
      setThreadCpuAffinityWithMigration_preserves_perCoreCbsInvariant_smp .consistency,
    pccbst! "setThreadCpuAffinityWithMigration_preserves_objects_invExt: the composite preserves the object-store invariant"
      setThreadCpuAffinityWithMigration_preserves_objects_invExt .consistency,
    -- ── SM5.H.4 (§10) the cross-domain lock-set footprints (.lockSet) ──
    pccbst! "replenishOnCoreLockSet: the replenish-queue write footprint (SM5.H.4)"
      replenishOnCoreLockSet .lockSet,
    pccbst! "replenishOnCoreLockSet_length: the footprint is a single lock"
      replenishOnCoreLockSet_length .lockSet,
    pccbst! "replenishOnCoreLockSet_write_only: the footprint is write-only"
      replenishOnCoreLockSet_write_only .lockSet,
    pccbst! "replenishOnCoreLockSet_contains_replenishQueue_write: the footprint contains the replenish-queue write"
      replenishOnCoreLockSet_contains_replenishQueue_write .lockSet,
    pccbst! "replenishOnCoreLockSet_size_le_maxLockSetSize: within the SM3.D WCRT cap"
      replenishOnCoreLockSet_size_le_maxLockSetSize .lockSet,
    pccbst! "migrateSchedContextReplenishmentLockSet: the replenishment-migration footprint (two replenish-queue writes)"
      migrateSchedContextReplenishmentLockSet .lockSet,
    pccbst! "migrateSchedContextReplenishmentLockSet_length: the footprint has two locks"
      migrateSchedContextReplenishmentLockSet_length .lockSet,
    pccbst! "migrateSchedContextReplenishmentLockSet_write_only: the footprint is write-only"
      migrateSchedContextReplenishmentLockSet_write_only .lockSet,
    pccbst! "migrateSchedContextReplenishmentLockSet_keys_nodup: the footprint's keys are distinct (under from ≠ to)"
      migrateSchedContextReplenishmentLockSet_keys_nodup .lockSet,
    pccbst! "migrateSchedContextReplenishmentLockSet_pairwise_le_of_core_le: ascending acquisition order under from ≤ to"
      migrateSchedContextReplenishmentLockSet_pairwise_le_of_core_le .lockSet,
    pccbst! "migrateSchedContextReplenishmentLockSet_size_le_maxLockSetSize: within the SM3.D WCRT cap"
      migrateSchedContextReplenishmentLockSet_size_le_maxLockSetSize .lockSet,
    pccbst! "migrateRunQueueOnAffinityChangeLockSet: the run-queue-migration footprint (two run-queue writes)"
      migrateRunQueueOnAffinityChangeLockSet .lockSet,
    pccbst! "migrateRunQueueOnAffinityChangeLockSet_length: the footprint has two locks"
      migrateRunQueueOnAffinityChangeLockSet_length .lockSet,
    pccbst! "migrateRunQueueOnAffinityChangeLockSet_pairwise_le_of_core_le: ascending acquisition order under from ≤ to"
      migrateRunQueueOnAffinityChangeLockSet_pairwise_le_of_core_le .lockSet,
    pccbst! "setThreadCpuAffinityWithMigrationLockSet: the COMPLETE composite footprint (object + 2 run-queue + 2 replenish-queue writes)"
      setThreadCpuAffinityWithMigrationLockSet .lockSet,
    pccbst! "setThreadCpuAffinityWithMigrationLockSet_length: the composite footprint has five locks"
      setThreadCpuAffinityWithMigrationLockSet_length .lockSet,
    pccbst! "setThreadCpuAffinityWithMigrationLockSet_write_only: the composite footprint is write-only"
      setThreadCpuAffinityWithMigrationLockSet_write_only .lockSet,
    pccbst! "setThreadCpuAffinityWithMigrationLockSet_contains_objStore_write: the composite footprint contains the object-store write"
      setThreadCpuAffinityWithMigrationLockSet_contains_objStore_write .lockSet,
    pccbst! "setThreadCpuAffinityWithMigrationLockSet_pairwise_le_of_core_le: §4.4 ascending order (object < runQueue < replenishQueue, then by core)"
      setThreadCpuAffinityWithMigrationLockSet_pairwise_le_of_core_le .lockSet,
    pccbst! "setThreadCpuAffinityWithMigrationLockSet_size_le_maxLockSetSize: within the SM3.D WCRT cap"
      setThreadCpuAffinityWithMigrationLockSet_size_le_maxLockSetSize .lockSet,
    -- ── SM5.H.2 (A2/A4, §14) the live-tick CBS bridge (.liveTick) ──
    pccbst! "updatePipBoost_replenishQueueOnCore: a PIP-boost update frames every replenish queue"
      updatePipBoost_replenishQueueOnCore .liveTick,
    pccbst! "revertPriorityInheritance_replenishQueueOnCore: PIP reversion frames every replenish queue"
      revertPriorityInheritance_replenishQueueOnCore .liveTick,
    pccbst! "ensureRunnable_replenishQueueOnCore: making a thread runnable frames every replenish queue"
      ensureRunnable_replenishQueueOnCore .liveTick,
    pccbst! "timeoutThread_replenishQueueOnCore: timing out one IPC-blocked thread frames every replenish queue"
      timeoutThread_replenishQueueOnCore .liveTick,
    pccbst! "timeoutBlockedThreads_replenishQueueOnCore: timing out all of an SC's blocked threads frames every replenish queue"
      timeoutBlockedThreads_replenishQueueOnCore .liveTick,
    pccbst! "timerTickBudgetOnCore_bound_exhausted_replenish_eq: A2 — the live bound-exhausted tick's replenish write IS replenishOnCore's"
      timerTickBudgetOnCore_bound_exhausted_replenish_eq .liveTick,
    pccbst! "timerTickBudgetOnCore_donated_exhausted_replenish_eq: A2 — the donated-exhausted tick's replenish write IS replenishOnCore's"
      timerTickBudgetOnCore_donated_exhausted_replenish_eq .liveTick,
    pccbst! "timerTickBudgetOnCore_preserves_replenishQueueValidOnCore: A4 — the live budget tick preserves replenish-queue validity on every core"
      timerTickBudgetOnCore_preserves_replenishQueueValidOnCore .liveTick,
    -- ── SM5.H.4 (C10, §15) the migration's cross-core memory-model HB (.memoryModel) ──
    pccbst! "affinityMigrationOrdering_synchronizesWith: the migration's release→acquire synchronizes-with edge"
      affinityMigrationOrdering_synchronizesWith .memoryModel,
    pccbst! "affinityMigrationOrdering_happensBefore: the migration's re-homing happens-before the new home observes the SGI (C10 headline)"
      affinityMigrationOrdering_happensBefore .memoryModel,
    -- ── SM5.H.4 (D15) the run-queue migration preserves SM4.C run-queue↔budget (.consistency) ──
    pccbst! "migrateRunQueueOnAffinityChange_getTcb?: the run-queue migration frames every TCB resolution"
      migrateRunQueueOnAffinityChange_getTcb? .consistency,
    pccbst! "migrateRunQueueOnAffinityChange_preserves_schedContextRunQueueConsistent_perCore: D15 — the run-queue migration preserves SM4.C run-queue↔budget consistency on every core"
      migrateRunQueueOnAffinityChange_preserves_schedContextRunQueueConsistent_perCore .consistency,
    -- ── SM5.H.4 (D15 composite, §17) the FULL affinity composite preserves SM4.C run-queue↔budget ──
    pccbst! "setThreadCpuAffinity_getTcb?_self: the affinity write reads back the target's TCB with only cpuAffinity rewritten"
      setThreadCpuAffinity_getTcb?_self .affinityWrite,
    pccbst! "setThreadCpuAffinity_preserves_schedContextRunQueueConsistent_perCore: D15 helper — the affinity write preserves SM4.C run-queue↔budget consistency"
      setThreadCpuAffinity_preserves_schedContextRunQueueConsistent_perCore .consistency,
    pccbst! "migrateSchedContextReplenishment_preserves_schedContextRunQueueConsistent_perCore: D15 helper — the replenishment migration preserves SM4.C run-queue↔budget consistency"
      migrateSchedContextReplenishment_preserves_schedContextRunQueueConsistent_perCore .consistency,
    pccbst! "setThreadCpuAffinityWithMigration_preserves_schedContextRunQueueConsistent_perCore: D15 composite — the full affinity composite preserves SM4.C run-queue↔budget consistency on every core"
      setThreadCpuAffinityWithMigration_preserves_schedContextRunQueueConsistent_perCore .consistency,
    -- ── SM5.H.4 (B8/SGI, §18) the composite's cross-core .reschedule SGI characterisation (.migration) ──
    pccbst! "setThreadCpuAffinityWithMigration_sgi_eq: the composite's emitted SGI is exactly the remote-and-runnable if-expression"
      setThreadCpuAffinityWithMigration_sgi_eq .migration,
    pccbst! "setThreadCpuAffinityWithMigration_no_sgi_if_local: a local affinity change (new home = executing core) emits no cross-core SGI"
      setThreadCpuAffinityWithMigration_no_sgi_if_local .migration,
    pccbst! "setThreadCpuAffinityWithMigration_emits_reschedule_of_remote_runnable: a remote+runnable affinity change emits exactly one .reschedule SGI to the new home"
      setThreadCpuAffinityWithMigration_emits_reschedule_of_remote_runnable .migration,
    -- ── SM5.H.4 (C10 tightened, §18) the emitted SGI pinned to the memory-model HB (.memoryModel) ──
    pccbst! "setThreadCpuAffinityWithMigration_sgi_happensBefore: the composite's emitted SGI targets the new home, is a .reschedule, and the state write happens-before the new home observes it"
      setThreadCpuAffinityWithMigration_sgi_happensBefore .memoryModel]

/-- WS-SM SM5.H: the inventory has 119 substantive entries (audit-pass-2: +8 for
the SM5.H.4 D15 composite + the §18 SGI characterisation + the tightened C10 HB).
A regression that adds a new SM5.H theorem without registering it fails this count
witness at the Tier-3 surface check. -/
theorem perCoreCbsTheorems_count : perCoreCbsTheorems.length = 119 := by decide

/-- WS-SM SM5.H: 6 entries in the `predicate` category. -/
theorem perCoreCbsTheorems_predicate_count :
    (perCoreCbsTheorems.filter (fun t => t.category == .predicate)).length = 6 := by decide

/-- WS-SM SM5.H: 17 entries in the `replenish` category. -/
theorem perCoreCbsTheorems_replenish_count :
    (perCoreCbsTheorems.filter (fun t => t.category == .replenish)).length = 17 := by decide

/-- WS-SM SM5.H: 8 entries in the `preservation` category. -/
theorem perCoreCbsTheorems_preservation_count :
    (perCoreCbsTheorems.filter (fun t => t.category == .preservation)).length = 8 := by decide

/-- WS-SM SM5.H: 22 entries in the `migration` category. -/
theorem perCoreCbsTheorems_migration_count :
    (perCoreCbsTheorems.filter (fun t => t.category == .migration)).length = 25 := by decide

/-- WS-SM SM5.H: 3 entries in the `affinityWrite` category. -/
theorem perCoreCbsTheorems_affinityWrite_count :
    (perCoreCbsTheorems.filter (fun t => t.category == .affinityWrite)).length = 4 := by decide

/-- WS-SM SM5.H: 19 entries in the `consistency` category. -/
theorem perCoreCbsTheorems_consistency_count :
    (perCoreCbsTheorems.filter (fun t => t.category == .consistency)).length = 22 := by decide

/-- WS-SM SM5.H: 6 entries in the `budget` category. -/
theorem perCoreCbsTheorems_budget_count :
    (perCoreCbsTheorems.filter (fun t => t.category == .budget)).length = 6 := by decide

/-- WS-SM SM5.H: 20 entries in the `lockSet` category. -/
theorem perCoreCbsTheorems_lockSet_count :
    (perCoreCbsTheorems.filter (fun t => t.category == .lockSet)).length = 20 := by decide

/-- WS-SM SM5.H: 8 entries in the `liveTick` category. -/
theorem perCoreCbsTheorems_liveTick_count :
    (perCoreCbsTheorems.filter (fun t => t.category == .liveTick)).length = 8 := by decide

/-- WS-SM SM5.H: 2 entries in the `memoryModel` category. -/
theorem perCoreCbsTheorems_memoryModel_count :
    (perCoreCbsTheorems.filter (fun t => t.category == .memoryModel)).length = 3 := by decide

/-- WS-SM SM5.H: per-category counts sum to the total. -/
theorem perCoreCbsTheorems_partition_sum :
    (perCoreCbsTheorems.filter (fun t => t.category == .predicate)).length +
    (perCoreCbsTheorems.filter (fun t => t.category == .replenish)).length +
    (perCoreCbsTheorems.filter (fun t => t.category == .preservation)).length +
    (perCoreCbsTheorems.filter (fun t => t.category == .migration)).length +
    (perCoreCbsTheorems.filter (fun t => t.category == .affinityWrite)).length +
    (perCoreCbsTheorems.filter (fun t => t.category == .consistency)).length +
    (perCoreCbsTheorems.filter (fun t => t.category == .budget)).length +
    (perCoreCbsTheorems.filter (fun t => t.category == .lockSet)).length +
    (perCoreCbsTheorems.filter (fun t => t.category == .liveTick)).length +
    (perCoreCbsTheorems.filter (fun t => t.category == .memoryModel)).length =
    perCoreCbsTheorems.length := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.H: every inventory identifier is unique.  Kernel-sound `decide` (not
`native_decide`): a duplicate identifier — which `native_decide` could mask by
trusting the compiled evaluation — fails this proof in the kernel. -/
theorem perCoreCbsTheorems_identifiers_nodup :
    (perCoreCbsTheorems.map (·.identifier)).Nodup := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
/-- WS-SM SM5.H: every inventory description is unique.  Kernel-sound `decide` under
an elevated `maxRecDepth` + `maxHeartbeats` (the O(n²) pairwise comparison of 119
long description strings exceeds the default heartbeat budget; still the
kernel-checked `decide`, never `native_decide`, see
`perCoreCbsTheorems_identifiers_nodup`). -/
theorem perCoreCbsTheorems_descriptions_nodup :
    (perCoreCbsTheorems.map (·.description)).Nodup := by decide

end SeLe4n.Kernel
