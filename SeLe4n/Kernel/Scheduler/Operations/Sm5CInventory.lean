-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.Concurrency.Runtime

/-!
# WS-SM SM5.C — Theorem inventory

Aggregates the SM5.C cross-core-wake substantive theorems into a single typed
inventory with size and per-category witnesses.  Mirrors the SM3.A
`PerObjectLockInventory.lean`, SM3.B `LockSetInventory.lean`, and SM3.C/D/E
`Sm3*Inventory.lean` patterns (added at audit-pass-1 for SM3-parity rigour — the
lighter SM5.A/SM5.B precedent left it out; per the implement-the-improvement rule
the maximally-rigorous option is taken here).

Seven categories matching the plan §3.3/§4.4/§5 sub-tasks:

* `.lockSet` — SM5.C.3 (`wakeThreadLockSet` / `handleRescheduleSgiOnCoreLockSet`
  + the cross-domain footprint witnesses).
* `.target` — SM5.C.9 (`determineTargetCore` routing theorems).
* `.enqueue` — SM5.C.1 (`enqueueRunnableOnCore` preservation / membership /
  make-ready / frame lemmas).
* `.wake` — SM5.C.2 / C.4 / C.10 / C.6 (`wakeThread` semantics: SGI emission,
  run-queue membership, losslessness + the `SchedStep` / `SchedReachable`
  closure + the multi-step dispatch liveness).
* `.handler` — SM5.C.5 (`handleRescheduleSgiOnCore` theorems).
* `.preservation` — §10 audit-pass-1 (the SM5.B-parity invariant preservation:
  `currentThreadValidOnCore`, `queueCurrentConsistentOnCore`, and the full
  `ipcSchedulerContractPredicates_perCore` IPC↔scheduler coherence bundle).
* `.latencyAffinityEmit` — SM5.C.11 (SGI delivery latency bound) + SM5.C.8
  (`setThreadCpuAffinity`) + SM5.C.4 (typed FFI SGI-emission wrappers) + §11
  (the memory-model happens-before for the wake's BKL ordering).

## Identifier validation

Identifiers are compile-time-validated via the `s5ct!` macro, mirroring SM3.A's
`polt!` / SM3.B's `lkst!` / SM3.C's `wlst!`.  A typo or stale rename fails the
build at this module's elaboration step with "unknown identifier '<name>'".
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

/-- WS-SM SM5.C: category tag for the SM5.C theorem inventory. -/
inductive Sm5CCategory where
  /-- SM5.C.3 lock-set footprints. -/
  | lockSet
  /-- SM5.C.9 `determineTargetCore` routing. -/
  | target
  /-- SM5.C.1 `enqueueRunnableOnCore` lemmas. -/
  | enqueue
  /-- SM5.C.2 / C.4 / C.10 / C.6 `wakeThread` semantics + losslessness. -/
  | wake
  /-- SM5.C.5 `handleRescheduleSgiOnCore` theorems. -/
  | handler
  /-- §10 audit-pass-1 invariant preservation. -/
  | preservation
  /-- SM5.C.11 latency + SM5.C.8 affinity op + SM5.C.4 FFI emit + §11 memory model. -/
  | latencyAffinityEmit
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM5.C: a theorem entry in the SM5.C inventory.  Records a description,
the fully-qualified name as a `String`, a compile-time elaboration witness, and a
category tag.  The `_elabCheck` field (produced by `s5ct!`) forces Lean to
resolve the referenced declaration at construction time. -/
structure Sm5CTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : Sm5CCategory
  deriving Repr, Inhabited

/-- WS-SM SM5.C: build a `Sm5CTheorem` with a compile-time-validated identifier. -/
syntax (name := s5ctMacro) "s5ct!" str ident term : term

macro_rules
  | `(s5ct! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : Sm5CTheorem))

/-- WS-SM SM5.C: substantive theorem inventory.  Every entry's identifier is
compile-time-validated by `s5ct!`. -/
def sm5CTheorems : List Sm5CTheorem :=
  [-- ── SM5.C.3 lock-set footprints (.lockSet) ──
    s5ct! "wakeThreadLockSet: the wake's cross-domain (object-store + run-queue WRITE) footprint"
      wakeThreadLockSet .lockSet,
    s5ct! "wakeThreadLockSet_write_only: every wake lock is WRITE mode"
      wakeThreadLockSet_write_only .lockSet,
    s5ct! "wakeThreadLockSet_contains_objStore_write: object-store write lock present"
      wakeThreadLockSet_contains_objStore_write .lockSet,
    s5ct! "wakeThreadLockSet_contains_runQueue_write: target run-queue write lock present"
      wakeThreadLockSet_contains_runQueue_write .lockSet,
    s5ct! "wakeThreadLockSet_object_before_runQueue: §4.4 object-before-run-queue order"
      wakeThreadLockSet_object_before_runQueue .lockSet,
    s5ct! "wakeThreadLockSet_keys_nodup: footprint keys are duplicate-free"
      wakeThreadLockSet_keys_nodup .lockSet,
    s5ct! "wakeThreadLockSet_pairwise_le: canonical SchedLockId-ascending acquisition order"
      wakeThreadLockSet_pairwise_le .lockSet,
    s5ct! "handleRescheduleSgiOnCoreLockSet: the SGI-handler footprint (= switch footprint)"
      handleRescheduleSgiOnCoreLockSet .lockSet,
    s5ct! "handleRescheduleSgiOnCoreLockSet_eq: coincides with switchToThreadOnCoreLockSet"
      handleRescheduleSgiOnCoreLockSet_eq .lockSet,
    -- ── SM5.C.9 determineTargetCore routing (.target) ──
    s5ct! "determineTargetCore: production wake-target routing"
      determineTargetCore .target,
    s5ct! "determineTargetCore_bound_eq_affinity: bound thread wakes onto its affinity core"
      determineTargetCore_bound_eq_affinity .target,
    s5ct! "determineTargetCore_unbound_eq_bootCore: unbound thread wakes onto bootCoreId"
      determineTargetCore_unbound_eq_bootCore .target,
    s5ct! "determineTargetCore_no_tcb_eq_bootCore: non-TCB defaults to bootCoreId (fail-safe)"
      determineTargetCore_no_tcb_eq_bootCore .target,
    s5ct! "determineTargetCore_in_range: the wake target is always a valid core"
      determineTargetCore_in_range .target,
    -- ── SM5.C.1 enqueueRunnableOnCore (.enqueue) ──
    s5ct! "enqueueRunnableOnCore: the per-core make-runnable primitive"
      enqueueRunnableOnCore .enqueue,
    s5ct! "enqueueRunnableOnCore_preserves_objects_invExt: preserves object-store invariant"
      enqueueRunnableOnCore_preserves_objects_invExt .enqueue,
    s5ct! "enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed: preserves run-queue well-formedness"
      enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed .enqueue,
    s5ct! "enqueueRunnableOnCore_mem_runQueueOnCore: the woken thread is enqueued"
      enqueueRunnableOnCore_mem_runQueueOnCore .enqueue,
    s5ct! "enqueueRunnableOnCore_makes_ready: the woken thread becomes ipcState=.ready"
      enqueueRunnableOnCore_makes_ready .enqueue,
    s5ct! "enqueueRunnableOnCore_runQueueOnCore_ne: sibling-core run queues framed out"
      enqueueRunnableOnCore_runQueueOnCore_ne .enqueue,
    s5ct! "enqueueRunnableOnCore_currentOnCore: never writes any current slot"
      enqueueRunnableOnCore_currentOnCore .enqueue,
    s5ct! "enqueueRunnableOnCore_getTcb?_ne: every other thread's TCB framed out (AK7-clean)"
      enqueueRunnableOnCore_getTcb?_ne .enqueue,
    s5ct! "enqueueRunnableOnCore_getTcb?_isSome: preserves TCB-resolvability of any thread"
      enqueueRunnableOnCore_getTcb?_isSome .enqueue,
    s5ct! "enqueueRunnableOnCore_no_tcb_noop: fail-closed on a non-TCB target"
      enqueueRunnableOnCore_no_tcb_noop .enqueue,
    -- ── SM5.C.2 / C.4 / C.10 / C.6 wakeThread semantics + losslessness (.wake) ──
    s5ct! "wakeThread: the cross-core wake transition (state + optional SGI)"
      wakeThread .wake,
    s5ct! "wakeThread_state_eq_enqueue: the wake's state effect is enqueueRunnableOnCore"
      wakeThread_state_eq_enqueue .wake,
    s5ct! "wakeThread_emits_sgi_if_remote: a remote wake of a TCB emits a reschedule SGI (Thm 3.3.1)"
      wakeThread_emits_sgi_if_remote .wake,
    s5ct! "wakeThread_no_sgi_if_local: a local wake emits no SGI"
      wakeThread_no_sgi_if_local .wake,
    s5ct! "wakeThread_no_sgi_if_no_tcb: a ghost (non-TCB) wake emits no SGI (audit-pass-1 guard)"
      wakeThread_no_sgi_if_no_tcb .wake,
    s5ct! "wakeThread_sgi_is_reschedule: every wake SGI is the reschedule kind"
      wakeThread_sgi_is_reschedule .wake,
    s5ct! "wakeThread_target_runQueue_contains: the woken thread is in the target run queue (SM5.C.10)"
      wakeThread_target_runQueue_contains .wake,
    s5ct! "wakeThread_preserves_objects_invExt: the wake preserves the object-store invariant"
      wakeThread_preserves_objects_invExt .wake,
    s5ct! "wakeThread_preserves_target_runQueue_wellFormed: preserves the target run-queue well-formedness"
      wakeThread_preserves_target_runQueue_wellFormed .wake,
    s5ct! "wakeThread_independent_of_other_core: cross-core independence frame"
      wakeThread_independent_of_other_core .wake,
    s5ct! "SchedStep: a single per-core scheduler step (enqueue or switch)"
      SchedStep .wake,
    s5ct! "SchedReachable: the RT-closure of scheduler steps"
      SchedReachable .wake,
    s5ct! "SchedReachable.of_enqueue: an enqueue step is reachable (non-vacuity)"
      SchedReachable.of_enqueue .wake,
    s5ct! "SchedReachable.trans: the reachability relation is transitive"
      SchedReachable.trans .wake,
    s5ct! "wakeThread_lossless: the woken thread is recoverable (Thm 3.3.2, reflexive witness)"
      wakeThread_lossless .wake,
    s5ct! "wakeThread_then_handle_dispatches_current: multi-step wake→handler dispatches to current"
      wakeThread_then_handle_dispatches_current .wake,
    s5ct! "wakeThread_roundtrip_reachable_current: full wake→SGI→current round-trip from the pre-state"
      wakeThread_roundtrip_reachable_current .wake,
    -- ── SM5.C.5 handleRescheduleSgiOnCore (.handler) ──
    s5ct! "handleRescheduleSgiOnCore: the target core's reschedule-SGI handler"
      handleRescheduleSgiOnCore .handler,
    s5ct! "handleRescheduleSgiOnCore_idle_when_none: idle when no eligible thread"
      handleRescheduleSgiOnCore_idle_when_none .handler,
    s5ct! "handleRescheduleSgiOnCore_eq_switch_of_choose_some: dispatch = switchToThreadOnCore"
      handleRescheduleSgiOnCore_eq_switch_of_choose_some .handler,
    s5ct! "handleRescheduleSgiOnCore_switches_current: a dispatch sets the chosen thread current"
      handleRescheduleSgiOnCore_switches_current .handler,
    s5ct! "handleRescheduleSgiOnCore_preserves_objects_invExt: handler preserves object-store invariant"
      handleRescheduleSgiOnCore_preserves_objects_invExt .handler,
    s5ct! "handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed: handler preserves run-queue wf"
      handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed .handler,
    s5ct! "handleRescheduleSgiOnCore_independent_of_other_core: handler cross-core independence"
      handleRescheduleSgiOnCore_independent_of_other_core .handler,
    -- ── §10 audit-pass-1 invariant preservation (.preservation) ──
    s5ct! "enqueueRunnableOnCore_preserves_currentThreadValidOnCore: preserves SM4.C current-validity"
      enqueueRunnableOnCore_preserves_currentThreadValidOnCore .preservation,
    s5ct! "enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_ne: sibling-core queue consistency"
      enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_ne .preservation,
    s5ct! "enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_self: target queue consistency (don't-wake-current)"
      enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_self .preservation,
    s5ct! "enqueueRunnableOnCore_preserves_runnableThreadIpcReady: runnable-are-ready preserved"
      enqueueRunnableOnCore_preserves_runnableThreadIpcReady .preservation,
    s5ct! "enqueueRunnableOnCore_preserves_blockedOnSendNotRunnable: send-blocked-not-runnable preserved"
      enqueueRunnableOnCore_preserves_blockedOnSendNotRunnable .preservation,
    s5ct! "enqueueRunnableOnCore_preserves_blockedOnReceiveNotRunnable: recv-blocked-not-runnable preserved"
      enqueueRunnableOnCore_preserves_blockedOnReceiveNotRunnable .preservation,
    s5ct! "enqueueRunnableOnCore_preserves_blockedOnCallNotRunnable: call-blocked-not-runnable preserved"
      enqueueRunnableOnCore_preserves_blockedOnCallNotRunnable .preservation,
    s5ct! "enqueueRunnableOnCore_preserves_blockedOnReplyNotRunnable: reply-blocked-not-runnable preserved"
      enqueueRunnableOnCore_preserves_blockedOnReplyNotRunnable .preservation,
    s5ct! "enqueueRunnableOnCore_preserves_blockedOnNotificationNotRunnable: ntfn-blocked-not-runnable preserved"
      enqueueRunnableOnCore_preserves_blockedOnNotificationNotRunnable .preservation,
    s5ct! "enqueueRunnableOnCore_preserves_ipcSchedulerContract: the full IPC↔scheduler coherence bundle"
      enqueueRunnableOnCore_preserves_ipcSchedulerContract .preservation,
    s5ct! "wakeThread_preserves_currentThreadValidOnCore: the wake preserves current-validity (every core)"
      wakeThread_preserves_currentThreadValidOnCore .preservation,
    s5ct! "wakeThread_preserves_ipcSchedulerContract: the wake preserves IPC↔scheduler coherence (gap-b headline)"
      wakeThread_preserves_ipcSchedulerContract .preservation,
    s5ct! "wakeThread_preserves_queueCurrentConsistentOnCore: the wake preserves queue/current consistency"
      wakeThread_preserves_queueCurrentConsistentOnCore .preservation,
    -- ── SM5.C.11 latency + SM5.C.8 affinity + SM5.C.4 FFI emit + §11 memory model ──
    s5ct! "wakeSgiCount: the number of SGIs a wake emits"
      wakeSgiCount .latencyAffinityEmit,
    s5ct! "wakeThread_emits_at_most_one_sgi: bounded emission (no SGI storm)"
      wakeThread_emits_at_most_one_sgi .latencyAffinityEmit,
    s5ct! "rescheduleSgi_lowest_intid: reschedule is the lowest-INTID kernel SGI"
      rescheduleSgi_lowest_intid .latencyAffinityEmit,
    s5ct! "sgiDeliveryLatencyBound_eq_zero: no kernel SGI is serviced ahead of reschedule"
      sgiDeliveryLatencyBound_eq_zero .latencyAffinityEmit,
    s5ct! "sgiDeliveryLatencyBound_counts_higher_priority_kernel_sgis: honest scoping of the =0 bound"
      sgiDeliveryLatencyBound_counts_higher_priority_kernel_sgis .latencyAffinityEmit,
    s5ct! "setThreadCpuAffinity: the affinity-control op"
      setThreadCpuAffinity .latencyAffinityEmit,
    s5ct! "setThreadCpuAffinity_sets_affinity: sets the target's affinity"
      setThreadCpuAffinity_sets_affinity .latencyAffinityEmit,
    s5ct! "setThreadCpuAffinity_error_of_no_tcb: fail-closed on a non-TCB target"
      setThreadCpuAffinity_error_of_no_tcb .latencyAffinityEmit,
    s5ct! "setThreadCpuAffinity_preserves_objects_invExt: preserves the object-store invariant"
      setThreadCpuAffinity_preserves_objects_invExt .latencyAffinityEmit,
    s5ct! "setThreadCpuAffinity_preserves_scheduler: leaves the scheduler state untouched"
      setThreadCpuAffinity_preserves_scheduler .latencyAffinityEmit,
    s5ct! "setThreadCpuAffinity_affects_determineTargetCore: binding feeds the wake target"
      setThreadCpuAffinity_affects_determineTargetCore .latencyAffinityEmit,
    s5ct! "Concurrency.emitWakeSgi: the FFI SGI-emission wrapper for the wake's optional SGI"
      SeLe4n.Kernel.Concurrency.emitWakeSgi .latencyAffinityEmit,
    s5ct! "Concurrency.sendRescheduleSgi: emit a cross-core reschedule SGI"
      SeLe4n.Kernel.Concurrency.sendRescheduleSgi .latencyAffinityEmit,
    s5ct! "Concurrency.coreIdTargetMask: CoreId → GIC single-bit target mask"
      SeLe4n.Kernel.Concurrency.coreIdTargetMask .latencyAffinityEmit,
    s5ct! "Concurrency.wakeOrdering_happensBefore: the wake's BKL release→acquire happens-before (§11)"
      SeLe4n.Kernel.Concurrency.wakeOrdering_happensBefore .latencyAffinityEmit,
    s5ct! "Concurrency.wakeOrdering_synchronizesWith: the wake's release-store synchronizes-with the acquire-load"
      SeLe4n.Kernel.Concurrency.wakeOrdering_synchronizesWith .latencyAffinityEmit,
    s5ct! "Concurrency.wakeOrderingTrace_wellFormed: the wake's ordering trace is well-formed"
      SeLe4n.Kernel.Concurrency.wakeOrderingTrace_wellFormed .latencyAffinityEmit]

/-- WS-SM SM5.C: the inventory has 78 substantive entries.  A regression that
adds a new SM5.C theorem without registering it fails this count witness at the
Tier-3 surface check. -/
theorem sm5CTheorems_count : sm5CTheorems.length = 78 := by decide

/-- WS-SM SM5.C: 9 entries in the `lockSet` category (SM5.C.3). -/
theorem sm5CTheorems_lockSet_count :
    (sm5CTheorems.filter (fun t => t.category == .lockSet)).length = 9 := by decide

/-- WS-SM SM5.C: 5 entries in the `target` category (SM5.C.9). -/
theorem sm5CTheorems_target_count :
    (sm5CTheorems.filter (fun t => t.category == .target)).length = 5 := by decide

/-- WS-SM SM5.C: 10 entries in the `enqueue` category (SM5.C.1). -/
theorem sm5CTheorems_enqueue_count :
    (sm5CTheorems.filter (fun t => t.category == .enqueue)).length = 10 := by decide

/-- WS-SM SM5.C: 17 entries in the `wake` category (SM5.C.2 / C.4 / C.10 / C.6). -/
theorem sm5CTheorems_wake_count :
    (sm5CTheorems.filter (fun t => t.category == .wake)).length = 17 := by decide

/-- WS-SM SM5.C: 7 entries in the `handler` category (SM5.C.5). -/
theorem sm5CTheorems_handler_count :
    (sm5CTheorems.filter (fun t => t.category == .handler)).length = 7 := by decide

/-- WS-SM SM5.C: 13 entries in the `preservation` category (§10 audit-pass-1). -/
theorem sm5CTheorems_preservation_count :
    (sm5CTheorems.filter (fun t => t.category == .preservation)).length = 13 := by decide

/-- WS-SM SM5.C: 16 entries in the `latencyAffinityEmit` category
(SM5.C.11 latency + SM5.C.8 affinity + SM5.C.4 FFI emit + §11 memory model). -/
theorem sm5CTheorems_latencyAffinityEmit_count :
    (sm5CTheorems.filter (fun t => t.category == .latencyAffinityEmit)).length = 17 := by decide

/-- WS-SM SM5.C: per-category counts sum to the total. -/
theorem sm5CTheorems_partition_sum :
    (sm5CTheorems.filter (fun t => t.category == .lockSet)).length +
    (sm5CTheorems.filter (fun t => t.category == .target)).length +
    (sm5CTheorems.filter (fun t => t.category == .enqueue)).length +
    (sm5CTheorems.filter (fun t => t.category == .wake)).length +
    (sm5CTheorems.filter (fun t => t.category == .handler)).length +
    (sm5CTheorems.filter (fun t => t.category == .preservation)).length +
    (sm5CTheorems.filter (fun t => t.category == .latencyAffinityEmit)).length =
    sm5CTheorems.length := by decide

/-- WS-SM SM5.C: every inventory identifier is unique. -/
theorem sm5CTheorems_identifiers_nodup :
    (sm5CTheorems.map (·.identifier)).Nodup := by native_decide

/-- WS-SM SM5.C: every inventory description is unique. -/
theorem sm5CTheorems_descriptions_nodup :
    (sm5CTheorems.map (·.description)).Nodup := by native_decide

end SeLe4n.Kernel
