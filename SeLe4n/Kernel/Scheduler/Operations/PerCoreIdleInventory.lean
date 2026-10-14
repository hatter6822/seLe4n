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
import SeLe4n.PackedString

/-!
# WS-SM SM5.E — Theorem inventory

Aggregates the SM5.E per-core idle-thread substantive theorems into a single
typed inventory with size and per-category witnesses.  Mirrors the SM5.C
`CrossCoreWakeInventory.lean` and SM5.D `PerCoreTimerInventory.lean` patterns
(and, further back, the SM3.B `LockSetInventory.lean`).

Seven categories matching the plan §3.5 / §4.3 / §5 sub-tasks (59 entries):

* `.field` — SM5.E.1 / SM5.E.2 / SM5.E.5: the idle-thread definitions
  (`idleThreadId`, `createIdleThread`) and field lemmas (`idleThread_priority_zero`,
  `createIdleThread_domain_zero`, `createIdleThread_cpuAffinity`,
  `createIdleThread_tid`).
* `.store` — SM5.E.3: `storeIdleThreadOnCore` plus its definitional / frame /
  resolution / preservation lemmas.  The idle thread is stored, never queued
  (seL4's posture).
* `.preservation` — SM5.E.3: the per-core scheduler-invariant preservation surface
  for `storeIdleThreadOnCore` (the SM5.I consumption surface — current-thread
  validity, dequeue-on-dispatch, the conditional current-in-domain, idle
  residency, and self-core affinity consistency).
* `.lockSet` — SM5.E.3: the `storeIdleThreadOnCoreLockSet` object-store WRITE
  footprint over SM5.A's `LockKey` and its witnesses.
* `.noStall` — SM5.E.6: the keystone `scheduleEffectiveOnCore_current_isSome`
  (a scheduling point leaves a current thread whenever the core's idle thread is
  dispatchable), the SM5.E.5 `scheduleEffectiveOnCore_idle_only_when_none`, and
  their discharge on the store and on the production boot state.
* `.locality` — SM5.E.4: `idleThread_core_locality` (affinity-based) + the
  operational frame companion + the `∀c` aggregate + the supporting
  `runQueueAffinityConsistentOnCore` and `idleTcbResidentOnCore`.
* `.dispatch` — SM5.E (SM5.I seed): the production idle-aware dispatcher
  `scheduleOrIdleOnCore` — `idleDispatchableOnCore` / `dispatchIdleOnCore` + frame
  lemmas, the headline `scheduleOrIdleOnCore_runs_idle`, and the soundness surface
  (at parity with `scheduleEffectiveOnCore`: objects-`invExt`, currentThreadValid,
  queueCurrentConsistent, runQueueWellFormed, currentThreadInActiveDomain,
  runnableThreadsAreTCBs).

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
  /-- SM5.E.3 `storeIdleThreadOnCore` op + frames. -/
  | store
  /-- SM5.E.3 per-core scheduler-invariant preservation (SM5.I consumption surface). -/
  | preservation
  /-- SM5.E.3 `storeIdleThreadOnCoreLockSet` cross-domain footprint (SM5.A–D parity). -/
  | lockSet
  /-- SM5.E.6 no-stall: a scheduling point always leaves a current thread. -/
  | noStall
  /-- SM5.E.4 `idleThread_core_locality` + companions. -/
  | locality
  /-- SM5.E (SM5.I seed) `scheduleOrIdleOnCore` idle-aware dispatcher establishment. -/
  | dispatch
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM5.E: a theorem entry in the SM5.E inventory.  Records a description and
the fully-qualified name as packed keys (`SeLe4n.PackedString`, read back
through `description` / `identifier`), a compile-time elaboration witness, and a
category tag.  The `_elabCheck` field (produced by `pcit!`) forces Lean to
resolve the referenced declaration at construction time. -/
structure PerCoreIdleTheorem where
  /-- The description as one packed key (`SeLe4n.PackedString`): one
      base-2²¹ digit per scalar value behind a leading `1`.  Read it back
      through `description`. -/
  descriptionKey : Nat
  /-- The fully-qualified name, packed the same way.  Read it back through
      `identifier`. -/
  identifierKey  : Nat
  /-- The kernel's own check, per entry, that the key packs exactly the valid
      scalar values it unpacks to — what lets distinctness of the strings be
      proven from distinctness of the keys. -/
  descriptionKey_wf : isWellFormedPacked descriptionKey = true := by decide +kernel
  identifierKey_wf  : isWellFormedPacked identifierKey = true := by decide +kernel
  _elabCheck  : Unit
  category    : PerCoreIdleCategory
  deriving Repr

/-- The default entry spells the empty string twice: `1` packs no digits. -/
instance : Inhabited PerCoreIdleTheorem :=
  ⟨{ descriptionKey := 1, identifierKey := 1, _elabCheck := (), category := default }⟩

/-- The entry's description, unpacked from its key. -/
def PerCoreIdleTheorem.description (t : PerCoreIdleTheorem) : String := stringOfPacked t.descriptionKey

/-- The entry's fully-qualified name, unpacked from its key. -/
def PerCoreIdleTheorem.identifier (t : PerCoreIdleTheorem) : String := stringOfPacked t.identifierKey

/-- WS-SM SM5.E: build a `PerCoreIdleTheorem` with a compile-time-validated identifier. -/
syntax (name := perCoreIdleTheoremMacro) "pcit!" str ident term : term

macro_rules
  | `(pcit! $desc:str $ident:ident $cat:term) => do
      let descKey := packedStringLit desc.getString
      let identKey := packedStringLit ident.getId.toString
      `(({ descriptionKey := nat_lit $descKey,
           identifierKey := nat_lit $identKey,
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
      SeLe4n.Kernel.createIdleThread .field,
    pcit! "idleThread_priority_zero: idle is priority 0, never starves a higher thread (SM5.E.5)"
      idleThread_priority_zero .field,
    pcit! "createIdleThread_domain_zero: idle is in the boot active domain 0"
      createIdleThread_domain_zero .field,
    pcit! "createIdleThread_cpuAffinity: idle is pinned to its own core (SM5.E.2)"
      createIdleThread_cpuAffinity .field,
    pcit! "createIdleThread_tid: the idle TCB's id is idleThreadId c (SM5.E.1)"
      createIdleThread_tid .field,
    -- ── SM5.E.3 idle store + frames (.store) ──
    pcit! "storeIdleThreadOnCore: store core c's ready idle TCB, queueing nothing (SM5.E.3)"
      storeIdleThreadOnCore .store,
    pcit! "storeIdleThreadOnCore_scheduler: the store writes no scheduler field"
      storeIdleThreadOnCore_scheduler .store,
    pcit! "storeIdleThreadOnCore_runQueueOnCore: no core's run queue changes"
      storeIdleThreadOnCore_runQueueOnCore .store,
    pcit! "storeIdleThreadOnCore_activeDomainOnCore: no core's active domain changes"
      storeIdleThreadOnCore_activeDomainOnCore .store,
    pcit! "storeIdleThreadOnCore_currentOnCore: no core's current slot changes"
      storeIdleThreadOnCore_currentOnCore .store,
    pcit! "storeIdleThreadOnCore_objects_self: the idle slot holds the ready idle TCB"
      storeIdleThreadOnCore_objects_self .store,
    pcit! "storeIdleThreadOnCore_objects_ne: every other slot is framed"
      storeIdleThreadOnCore_objects_ne .store,
    pcit! "storeIdleThreadOnCore_getTcb?_self: idle resolves to the idle TCB"
      storeIdleThreadOnCore_getTcb?_self .store,
    pcit! "storeIdleThreadOnCore_getTcb?_ne: every other thread's resolution is framed"
      storeIdleThreadOnCore_getTcb?_ne .store,
    pcit! "storeIdleThreadOnCore_runQueueRefined: the queues keep agreeing with the run-queue links"
      storeIdleThreadOnCore_runQueueRefined .store,
    pcit! "storeIdleThreadOnCore_preserves_objects_invExt: object-store invariant preserved"
      storeIdleThreadOnCore_preserves_objects_invExt .store,
    pcit! "storeIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore: runnable-are-TCBs preserved"
      storeIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore .store,
    -- ── SM5.E.3 per-core scheduler-invariant preservation (.preservation) ──
    pcit! "storeIdleThreadOnCore_preserves_currentThreadValidOnCore: current-thread validity preserved (unconditional)"
      storeIdleThreadOnCore_preserves_currentThreadValidOnCore .preservation,
    pcit! "storeIdleThreadOnCore_preserves_queueCurrentConsistentOnCore: dequeue-on-dispatch preserved"
      storeIdleThreadOnCore_preserves_queueCurrentConsistentOnCore .preservation,
    pcit! "storeIdleThreadOnCore_preserves_currentThreadInActiveDomainOnCore: current-in-domain preserved (current ≠ idle)"
      storeIdleThreadOnCore_preserves_currentThreadInActiveDomainOnCore .preservation,
    pcit! "storeIdleThreadOnCore_idleTcbResidentOnCore: the store makes the idle TCB resident"
      storeIdleThreadOnCore_idleTcbResidentOnCore .preservation,
    pcit! "storeIdleThreadOnCore_preserves_runQueueAffinityConsistentOnCore_self: affinity coherence kept on its own core"
      storeIdleThreadOnCore_preserves_runQueueAffinityConsistentOnCore_self .preservation,
    -- ── SM5.E.3 lock-set footprint (.lockSet) ──
    pcit! "storeIdleThreadOnCoreLockSet: object-store WRITE footprint, no run-queue lock (§4.4)"
      storeIdleThreadOnCoreLockSet .lockSet,
    pcit! "storeIdleThreadOnCoreLockSet_length: the footprint is the one-lock set"
      storeIdleThreadOnCoreLockSet_length .lockSet,
    pcit! "storeIdleThreadOnCoreLockSet_write_only: every lock is WRITE mode"
      storeIdleThreadOnCoreLockSet_write_only .lockSet,
    pcit! "storeIdleThreadOnCoreLockSet_contains_objStore_write: object-store write lock present"
      storeIdleThreadOnCoreLockSet_contains_objStore_write .lockSet,
    pcit! "storeIdleThreadOnCoreLockSet_pairwise_le: keys form a valid withLockSet acquisition order"
      storeIdleThreadOnCoreLockSet_pairwise_le .lockSet,
    -- ── SM5.E.6 no stall (.noStall) ──
    pcit! "idleDispatchableOnCore_saveOutgoingContextOnCore: saving the outgoing context keeps idle dispatchable"
      idleDispatchableOnCore_saveOutgoingContextOnCore .noStall,
    pcit! "scheduleEffectiveOnCore_current_isSome: a scheduling point leaves a current thread when idle is dispatchable (SM5.E.6)"
      scheduleEffectiveOnCore_current_isSome .noStall,
    pcit! "scheduleEffectiveOnCore_idle_only_when_none: idle runs only when the queue offers nothing (SM5.E.5)"
      scheduleEffectiveOnCore_idle_only_when_none .noStall,
    pcit! "storeIdleThreadOnCore_idleDispatchableOnCore: the store makes idle dispatchable"
      storeIdleThreadOnCore_idleDispatchableOnCore .noStall,
    pcit! "bootFromPlatformCheckedWithIdleThreads_idleDispatchableOnCore: the production boot makes every idle dispatchable"
      bootFromPlatformCheckedWithIdleThreads_idleDispatchableOnCore .noStall,
    pcit! "bootFromPlatformCheckedWithIdleThreads_scheduleEffectiveOnCore_current_isSome: no core stalls on the boot state"
      bootFromPlatformCheckedWithIdleThreads_scheduleEffectiveOnCore_current_isSome .noStall,
    -- ── SM5.E.4 core locality (.locality) ──
    pcit! "runQueueAffinityConsistentOnCore: run-queue and affinity coherence predicate"
      runQueueAffinityConsistentOnCore .locality,
    pcit! "idleTcbResidentOnCore: core c's idle slot holds its ready idle TCB"
      idleTcbResidentOnCore .locality,
    pcit! "idleThread_core_locality: idle c never on another core's run queue (SM5.E.4)"
      idleThread_core_locality .locality,
    pcit! "idleThread_core_locality_of_store: storing idle c does not leak it to another core"
      idleThread_core_locality_of_store .locality,
    pcit! "idleThread_core_locality_forall: the ∀c SMP locality aggregate"
      idleThread_core_locality_forall .locality,
    pcit! "storeIdleThreadOnCore_selection_inputs_framed: every core's selection inputs are framed"
      storeIdleThreadOnCore_selection_inputs_framed .locality,
    -- ── SM5.E idle-aware dispatcher (SM5.I seed) (.dispatch) ──
    pcit! "idleDispatchableOnCore: the idle-dispatch admission gate"
      idleDispatchableOnCore .dispatch,
    pcit! "dispatchIdleOnCore: the idle-dispatch state (dequeue + restore + set-current)"
      dispatchIdleOnCore .dispatch,
    pcit! "idleFallbackOnCore: the folded idle-or-none fallback (scheduleEffectiveOnCore's none branch)"
      idleFallbackOnCore .dispatch,
    pcit! "scheduleOrIdleOnCore: the per-core idle-aware dispatcher (SM5.I seed; = scheduleEffectiveOnCore post-fold)"
      scheduleOrIdleOnCore .dispatch,
    pcit! "dispatchIdleOnCore_currentOnCore: dispatching idle sets current to the idle thread"
      dispatchIdleOnCore_currentOnCore .dispatch,
    pcit! "dispatchIdleOnCore_objectsAgreeOffRunLinks: dispatching idle touches the object store only in run-queue links"
      dispatchIdleOnCore_objectsAgreeOffRunLinks .dispatch,
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
      scheduleOrIdleOnCore_preserves_runQueueOnCoreWellFormed .dispatch,
    pcit! "scheduleOrIdleOnCore_establishes_currentThreadInActiveDomainOnCore: dispatcher establishes current-in-domain (parity)"
      scheduleOrIdleOnCore_establishes_currentThreadInActiveDomainOnCore .dispatch,
    pcit! "scheduleOrIdleOnCore_preserves_runnableThreadsAreTCBsOnCore: dispatcher preserves runnable-are-TCBs (parity)"
      scheduleOrIdleOnCore_preserves_runnableThreadsAreTCBsOnCore .dispatch,
    pcit! "scheduleEffectiveOnCore_currentNone_imp_chooseEffectiveNone: current=none ⟹ selector found nothing"
      scheduleEffectiveOnCore_currentNone_imp_chooseEffectiveNone .dispatch,
    pcit! "scheduleOrIdleOnCore_idle_starves_no_eligible_thread: dispatcher runs idle only when nothing eligible (strong no-starvation)"
      scheduleOrIdleOnCore_idle_starves_no_eligible_thread .dispatch,
    pcit! "scheduleDomainOnCore_runs_idle: the folded idle dispatch is reachable on the live per-core domain-tick path (review #4 closure)"
      scheduleDomainOnCore_runs_idle .dispatch]

/-- WS-SM SM5.E: the inventory has 59 substantive entries.  A regression that
adds a new SM5.E theorem without registering it fails this count witness at the
Tier-3 surface check. -/
theorem perCoreIdleTheorems_count : perCoreIdleTheorems.length = 59 := by decide

/-- WS-SM SM5.E: 6 entries in the `field` category (SM5.E.1 / .2 / .5). -/
theorem perCoreIdleTheorems_field_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .field)).length = 6 := by decide

/-- WS-SM SM5.E: 12 entries in the `store` category (SM5.E.3). -/
theorem perCoreIdleTheorems_store_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .store)).length = 12 := by decide

/-- WS-SM SM5.E: 5 entries in the `preservation` category (SM5.E.3 invariant preservation). -/
theorem perCoreIdleTheorems_preservation_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .preservation)).length = 5 := by decide

/-- WS-SM SM5.E: 5 entries in the `lockSet` category (SM5.E.3 footprint). -/
theorem perCoreIdleTheorems_lockSet_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .lockSet)).length = 5 := by decide

/-- WS-SM SM5.E: 6 entries in the `noStall` category (SM5.E.6). -/
theorem perCoreIdleTheorems_noStall_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .noStall)).length = 6 := by decide

/-- WS-SM SM5.E: 6 entries in the `locality` category (SM5.E.4). -/
theorem perCoreIdleTheorems_locality_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .locality)).length = 6 := by decide

/-- WS-SM SM5.E: 19 entries in the `dispatch` category (SM5.I dispatcher seed;
post-fold `idleFallbackOnCore` + live-wiring `scheduleDomainOnCore_runs_idle`). -/
theorem perCoreIdleTheorems_dispatch_count :
    (perCoreIdleTheorems.filter (fun t => t.category == .dispatch)).length = 19 := by decide

/-- WS-SM SM5.E: per-category counts sum to the total. -/
theorem perCoreIdleTheorems_partition_sum :
    (perCoreIdleTheorems.filter (fun t => t.category == .field)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .store)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .preservation)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .lockSet)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .noStall)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .locality)).length +
    (perCoreIdleTheorems.filter (fun t => t.category == .dispatch)).length =
    perCoreIdleTheorems.length := by decide

/-- WS-SM SM5.E: every inventory identifier is unique.  Kernel-checked, never
`native_decide`: the identifiers are stored as packed keys, each entry's
`identifierKey_wf` field is the kernel's own check that its key is well
formed, and `SeLe4n.nodup_map_stringOfPacked` turns distinctness of the keys
— one `decide +kernel` over `Nat`s — into distinctness of the strings they
spell.  A duplicate identifier fails this proof in the kernel. -/
theorem perCoreIdleTheorems_identifiers_nodup :
    (perCoreIdleTheorems.map (·.identifier)).Nodup :=
  nodup_map_stringOfPacked PerCoreIdleTheorem.identifierKey (fun t _ => t.identifierKey_wf)
    (by decide +kernel)

/-- WS-SM SM5.E: every inventory description is unique — the same key-level
argument as `perCoreIdleTheorems_identifiers_nodup`, over `descriptionKey`. -/
theorem perCoreIdleTheorems_descriptions_nodup :
    (perCoreIdleTheorems.map (·.description)).Nodup :=
  nodup_map_stringOfPacked PerCoreIdleTheorem.descriptionKey (fun t _ => t.descriptionKey_wf)
    (by decide +kernel)

end SeLe4n.Kernel
