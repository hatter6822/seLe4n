-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdle
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDispatch

/-!
# WS-SM SM5.E — Theorem inventory

Aggregates the SM5.E per-core idle-thread substantive theorems into a single
typed inventory with size and per-category witnesses.  Mirrors the SM5.C
`CrossCoreWakeInventory.lean` and SM5.D `PerCoreTimerInventory.lean` patterns
(and, further back, the SM3.A `PerObjectLockInventory.lean`).

Four categories matching the plan §3.5 / §4.3 / §5 sub-tasks:

* `.field` — SM5.E.1 / SM5.E.2 / SM5.E.5: the idle-thread definitions
  (`idleThreadId`, `createIdleThread`) and field lemmas (`idleThread_priority_zero`,
  `createIdleThread_domain_zero`, `createIdleThread_cpuAffinity`,
  `createIdleThread_tid`).
* `.enqueue` — SM5.E.3 (run-queue form): `enqueueIdleThreadOnCore` plus its
  definitional / frame / membership / resolution / preservation lemmas.
* `.alwaysSucceeds` — SM5.E.6: the `idleThreadEnqueuedOnCore` discharge
  predicate, its constructive establishment, the keystone
  `chooseThreadOnCore_always_succeeds`, and the end-to-end non-vacuity witness.
* `.locality` — SM5.E.4: `idleThread_core_locality` (affinity-based) + the
  operational frame companion + the supporting `runQueueAffinityConsistentOnCore`.

## Identifier validation

Identifiers are compile-time-validated via the `pcit!` macro, mirroring SM5.C's
`ccwt!` / SM5.D's `pctt!`.  A typo or stale rename fails the build at this
module's elaboration step with "unknown identifier '<name>'".
-/

namespace SeLe4n.Kernel

/-- WS-SM SM5.E: category tag for the SM5.E theorem inventory. -/
inductive PerCoreIdleCategory where
  /-- SM5.E.1 / SM5.E.2 / SM5.E.5 idle-thread definitions + field lemmas. -/
  | field
  /-- SM5.E.3 `enqueueIdleThreadOnCore` op + frame / membership / preservation. -/
  | enqueue
  /-- SM5.E.3 per-core scheduler-invariant preservation (SM5.I consumption surface). -/
  | preservation
  /-- SM5.E.3 `enqueueIdleThreadOnCoreLockSet` cross-domain footprint (SM5.A–D parity). -/
  | lockSet
  /-- SM5.E.6 `chooseThreadOnCore_always_succeeds` + discharge predicate + witnesses. -/
  | alwaysSucceeds
  /-- SM5.E.4 `idleThread_core_locality` + companions + no-starvation. -/
  | locality
  /-- SM5.E (SM5.I seed) `scheduleOrIdleOnCore` idle-aware dispatcher establishment. -/
  | dispatch
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM5.E: a theorem entry in the SM5.E inventory.  Records a description,
the fully-qualified name as a `String`, a compile-time elaboration witness, and a
category tag.  The `_elabCheck` field (produced by `pcit!`) forces Lean to
resolve the referenced declaration at construction time. -/
structure PerCoreIdleTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : PerCoreIdleCategory
  deriving Repr, Inhabited

/-- WS-SM SM5.E: build a `PerCoreIdleTheorem` with a compile-time-validated identifier. -/
syntax (name := perCoreIdleTheoremMacro) "pcit!" str ident term : term

macro_rules
  | `(pcit! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : PerCoreIdleTheorem))

/-- WS-SM SM5.E: substantive theorem inventory.  Every entry's identifier is
compile-time-validated by `pcit!`. -/
def perCoreIdleTheorems : List PerCoreIdleTheorem :=
  [-- ── SM5.E.1 / .2 / .5 idle definitions + field lemmas (.field) ──
    pcit! "idleThreadId: the per-core idle thread id (SM5.E.1)"
      SeLe4n.Kernel.idleThreadId .field,
    pcit! "createIdleThread: the per-core idle TCB with cpuAffinity := some c (SM5.E.2)"
      SeLe4n.Platform.Boot.createIdleThread .field,
    pcit! "idleThread_priority_zero: idle is priority 0, never starves a higher thread (SM5.E.5)"
      idleThread_priority_zero .field,
    pcit! "createIdleThread_domain_zero: idle is in the boot active domain 0"
      createIdleThread_domain_zero .field,
    pcit! "createIdleThread_cpuAffinity: idle is pinned to its own core (SM5.E.2)"
      createIdleThread_cpuAffinity .field,
    pcit! "createIdleThread_tid: the idle TCB's id is idleThreadId c (SM5.E.1)"
      createIdleThread_tid .field,
    -- ── SM5.E.3 enqueue op + frame / membership / preservation (.enqueue) ──
    pcit! "enqueueIdleThreadOnCore: make core c's idle thread run-queue-resident (SM5.E.3)"
      enqueueIdleThreadOnCore .enqueue,
    pcit! "enqueueIdleThreadOnCore_objects: the enqueue's object-store write (definitional)"
      enqueueIdleThreadOnCore_objects .enqueue,
    pcit! "enqueueIdleThreadOnCore_scheduler: the enqueue's scheduler write (definitional)"
      enqueueIdleThreadOnCore_scheduler .enqueue,
    pcit! "enqueueIdleThreadOnCore_runQueueOnCore_self: core c's run queue gains the idle thread"
      enqueueIdleThreadOnCore_runQueueOnCore_self .enqueue,
    pcit! "enqueueIdleThreadOnCore_runQueueOnCore_ne: a different core's run queue is untouched"
      enqueueIdleThreadOnCore_runQueueOnCore_ne .enqueue,
    pcit! "enqueueIdleThreadOnCore_activeDomainOnCore: no core's active domain changes"
      enqueueIdleThreadOnCore_activeDomainOnCore .enqueue,
    pcit! "enqueueIdleThreadOnCore_currentOnCore: no core's current slot changes"
      enqueueIdleThreadOnCore_currentOnCore .enqueue,
    pcit! "enqueueIdleThreadOnCore_mem_runQueueOnCore_self: idle is a member of core c's run queue"
      enqueueIdleThreadOnCore_mem_runQueueOnCore_self .enqueue,
    pcit! "enqueueIdleThreadOnCore_getTcb?_self: idle resolves to the idle TCB"
      enqueueIdleThreadOnCore_getTcb?_self .enqueue,
    pcit! "enqueueIdleThreadOnCore_getTcb?_ne: every other thread's resolution is framed"
      enqueueIdleThreadOnCore_getTcb?_ne .enqueue,
    pcit! "enqueueIdleThreadOnCore_preserves_objects_invExt: object-store invariant preserved"
      enqueueIdleThreadOnCore_preserves_objects_invExt .enqueue,
    pcit! "enqueueIdleThreadOnCore_preserves_runQueueOnCore_wellFormed: run-queue well-formedness preserved"
      enqueueIdleThreadOnCore_preserves_runQueueOnCore_wellFormed .enqueue,
    pcit! "enqueueIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore: runnable-are-TCBs preserved"
      enqueueIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore .enqueue,
    -- ── SM5.E.3 per-core scheduler-invariant preservation (.preservation) ──
    pcit! "enqueueIdleThreadOnCore_preserves_currentThreadValidOnCore: current-thread validity preserved (unconditional)"
      enqueueIdleThreadOnCore_preserves_currentThreadValidOnCore .preservation,
    pcit! "enqueueIdleThreadOnCore_preserves_queueCurrentConsistentOnCore: dequeue-on-dispatch preserved (current ≠ idle)"
      enqueueIdleThreadOnCore_preserves_queueCurrentConsistentOnCore .preservation,
    pcit! "enqueueIdleThreadOnCore_preserves_currentThreadInActiveDomainOnCore: current-in-domain preserved (current ≠ idle)"
      enqueueIdleThreadOnCore_preserves_currentThreadInActiveDomainOnCore .preservation,
    pcit! "enqueueIdleThreadOnCore_mem_idempotent: re-enqueuing idle adds no duplicate"
      enqueueIdleThreadOnCore_mem_idempotent .preservation,
    pcit! "enqueueIdleThreadOnCore_preserves_runQueueAffinityConsistentOnCore_self: idle admitted on its own core"
      enqueueIdleThreadOnCore_preserves_runQueueAffinityConsistentOnCore_self .preservation,
    -- ── SM5.E.3 lock-set footprint (.lockSet) ──
    pcit! "enqueueIdleThreadOnCoreLockSet: cross-domain object-store + run-queue WRITE footprint (§4.4)"
      enqueueIdleThreadOnCoreLockSet .lockSet,
    pcit! "enqueueIdleThreadOnCoreLockSet_length: the footprint is the two-lock set"
      enqueueIdleThreadOnCoreLockSet_length .lockSet,
    pcit! "enqueueIdleThreadOnCoreLockSet_write_only: every lock is WRITE mode"
      enqueueIdleThreadOnCoreLockSet_write_only .lockSet,
    pcit! "enqueueIdleThreadOnCoreLockSet_contains_objStore_write: object-store write lock present"
      enqueueIdleThreadOnCoreLockSet_contains_objStore_write .lockSet,
    pcit! "enqueueIdleThreadOnCoreLockSet_contains_runQueue_write: run-queue write lock present"
      enqueueIdleThreadOnCoreLockSet_contains_runQueue_write .lockSet,
    pcit! "enqueueIdleThreadOnCoreLockSet_object_before_runQueue: §4.4 object-before-run-queue order"
      enqueueIdleThreadOnCoreLockSet_object_before_runQueue .lockSet,
    pcit! "enqueueIdleThreadOnCoreLockSet_keys_nodup: footprint keys are duplicate-free"
      enqueueIdleThreadOnCoreLockSet_keys_nodup .lockSet,
    pcit! "enqueueIdleThreadOnCoreLockSet_pairwise_le: keys form a valid withLockSet acquisition order"
      enqueueIdleThreadOnCoreLockSet_pairwise_le .lockSet,
    -- ── SM5.E.6 always-succeeds (.alwaysSucceeds) ──
    pcit! "idleThreadEnqueuedOnCore: the SM5.E.6 discharge predicate (idle is an in-domain candidate)"
      idleThreadEnqueuedOnCore .alwaysSucceeds,
    pcit! "enqueueIdleThreadOnCore_establishes_idleThreadEnqueuedOnCore: the discharge is satisfiable"
      enqueueIdleThreadOnCore_establishes_idleThreadEnqueuedOnCore .alwaysSucceeds,
    pcit! "chooseThreadOnCore_always_succeeds: selection succeeds when idle is enqueued (SM5.E.6)"
      chooseThreadOnCore_always_succeeds .alwaysSucceeds,
    pcit! "enqueueIdleThreadOnCore_chooseThreadOnCore_succeeds: end-to-end non-vacuity witness"
      enqueueIdleThreadOnCore_chooseThreadOnCore_succeeds .alwaysSucceeds,
    pcit! "idleAvailableOnCoreB: decidable companion to idleThreadEnqueuedOnCore"
      idleAvailableOnCoreB .alwaysSucceeds,
    pcit! "chooseThreadOnCore_always_succeeds_of_idleAvailableB: the decidable always-succeeds"
      chooseThreadOnCore_always_succeeds_of_idleAvailableB .alwaysSucceeds,
    pcit! "idleThreadEnqueuedOnCore_idleAvailableOnCoreB: Prop discharge implies the Bool companion"
      idleThreadEnqueuedOnCore_idleAvailableOnCoreB .alwaysSucceeds,
    -- ── SM5.E.4 core locality + no-starvation (.locality) ──
    pcit! "runQueueAffinityConsistentOnCore: run-queue and affinity coherence predicate"
      runQueueAffinityConsistentOnCore .locality,
    pcit! "idleThread_core_locality: idle c never on another core's run queue (SM5.E.4)"
      idleThread_core_locality .locality,
    pcit! "idleThread_core_locality_of_enqueue: enqueuing idle c does not leak it to another core"
      idleThread_core_locality_of_enqueue .locality,
    pcit! "idleThread_core_locality_forall: the ∀c SMP locality aggregate"
      idleThread_core_locality_forall .locality,
    pcit! "enqueueIdleThreadOnCore_selection_inputs_framed: a different core's selection inputs are framed"
      enqueueIdleThreadOnCore_selection_inputs_framed .locality,
    pcit! "idleThread_no_starvation: idle is selected only when not outranked in the top bucket (SM5.E.5)"
      idleThread_no_starvation .locality,
    -- ── SM5.E idle-aware dispatcher (SM5.I seed) (.dispatch) ──
    pcit! "idleDispatchableOnCore: the idle-dispatch admission gate"
      idleDispatchableOnCore .dispatch,
    pcit! "dispatchIdleOnCore: the idle-dispatch state (dequeue + restore + set-current)"
      dispatchIdleOnCore .dispatch,
    pcit! "scheduleOrIdleOnCore: the per-core idle-aware dispatcher (SM5.I seed)"
      scheduleOrIdleOnCore .dispatch,
    pcit! "dispatchIdleOnCore_currentOnCore: dispatching idle sets current to the idle thread"
      dispatchIdleOnCore_currentOnCore .dispatch,
    pcit! "dispatchIdleOnCore_objects: dispatching idle never touches the object store"
      dispatchIdleOnCore_objects .dispatch,
    pcit! "dispatchIdleOnCore_runQueueOnCore: idle is removed from the run queue (dequeue-on-dispatch)"
      dispatchIdleOnCore_runQueueOnCore .dispatch,
    pcit! "dispatchIdleOnCore_activeDomainOnCore: dispatching idle frames the active domain"
      dispatchIdleOnCore_activeDomainOnCore .dispatch,
    pcit! "dispatchIdleOnCore_getTcb?: dispatching idle frames every thread's resolution"
      dispatchIdleOnCore_getTcb? .dispatch,
    pcit! "scheduleOrIdleOnCore_runs_idle: idle is dispatched in production when nothing else is runnable (headline)"
      scheduleOrIdleOnCore_runs_idle .dispatch,
    pcit! "scheduleOrIdleOnCore_preserves_objects_invExt: dispatcher preserves the object-store invariant"
      scheduleOrIdleOnCore_preserves_objects_invExt .dispatch,
    pcit! "scheduleOrIdleOnCore_establishes_currentThreadValidOnCore: dispatcher establishes current-thread validity"
      scheduleOrIdleOnCore_establishes_currentThreadValidOnCore .dispatch,
    pcit! "scheduleOrIdleOnCore_establishes_queueCurrentConsistentOnCore: dispatcher establishes dequeue-on-dispatch"
      scheduleOrIdleOnCore_establishes_queueCurrentConsistentOnCore .dispatch,
    pcit! "scheduleOrIdleOnCore_preserves_runQueueOnCoreWellFormed: dispatcher preserves run-queue well-formedness"
      scheduleOrIdleOnCore_preserves_runQueueOnCoreWellFormed .dispatch]

/-- WS-SM SM5.E: the inventory has 58 substantive entries.  A regression that
adds a new SM5.E theorem without registering it fails this count witness at the
Tier-3 surface check. -/
theorem perCoreIdleTheorems_count : perCoreIdleTheorems.length = 58 := by decide

/-- WS-SM SM5.E: 6 entries in the `field` category (SM5.E.1 / .2 / .5). -/
theorem perCoreIdleTheorems_field_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .field)).length = 6 := by decide

/-- WS-SM SM5.E: 13 entries in the `enqueue` category (SM5.E.3). -/
theorem perCoreIdleTheorems_enqueue_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .enqueue)).length = 13 := by decide

/-- WS-SM SM5.E: 5 entries in the `preservation` category (SM5.E.3 invariant preservation). -/
theorem perCoreIdleTheorems_preservation_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .preservation)).length = 5 := by decide

/-- WS-SM SM5.E: 8 entries in the `lockSet` category (SM5.E.3 footprint). -/
theorem perCoreIdleTheorems_lockSet_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .lockSet)).length = 8 := by decide

/-- WS-SM SM5.E: 7 entries in the `alwaysSucceeds` category (SM5.E.6). -/
theorem perCoreIdleTheorems_alwaysSucceeds_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .alwaysSucceeds)).length = 7 := by decide

/-- WS-SM SM5.E: 6 entries in the `locality` category (SM5.E.4 + no-starvation). -/
theorem perCoreIdleTheorems_locality_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .locality)).length = 6 := by decide

/-- WS-SM SM5.E: 13 entries in the `dispatch` category (SM5.I dispatcher seed). -/
theorem perCoreIdleTheorems_dispatch_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .dispatch)).length = 13 := by decide

/-- WS-SM SM5.E: per-category counts sum to the total. -/
theorem perCoreIdleTheorems_partition_sum :
    (perCoreIdleTheorems.filter (fun t => t.category == .field)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .enqueue)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .preservation)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .lockSet)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .alwaysSucceeds)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .locality)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .dispatch)).length =
    perCoreIdleTheorems.length := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.E: every inventory identifier is unique.  Kernel-sound `decide`
(not `native_decide`): a duplicate identifier — which `native_decide` could mask
by trusting the compiled evaluation — fails this proof in the kernel.  The
elevated `maxRecDepth` only raises the recursion *limit* for the `Nodup`
decision procedure (no extra work, no axioms; the proof stays a kernel-checked
`of_decide_eq_true`). -/
theorem perCoreIdleTheorems_identifiers_nodup :
    (perCoreIdleTheorems.map (·.identifier)).Nodup := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.E: every inventory description is unique.  Kernel-sound `decide`
under an elevated `maxRecDepth` (see `perCoreIdleTheorems_identifiers_nodup`). -/
theorem perCoreIdleTheorems_descriptions_nodup :
    (perCoreIdleTheorems.map (·.description)).Nodup := by decide

end SeLe4n.Kernel
