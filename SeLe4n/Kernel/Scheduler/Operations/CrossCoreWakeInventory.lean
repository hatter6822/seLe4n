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

Identifiers are compile-time-validated via the `ccwt!` macro, mirroring SM3.A's
`polt!` / SM3.B's `lkst!` / SM3.C's `wlst!`.  A typo or stale rename fails the
build at this module's elaboration step with "unknown identifier '<name>'".
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

/-- WS-SM SM5.C: category tag for the SM5.C theorem inventory. -/
inductive CrossCoreWakeCategory where
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
category tag.  The `_elabCheck` field (produced by `ccwt!`) forces Lean to
resolve the referenced declaration at construction time. -/
structure CrossCoreWakeTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : CrossCoreWakeCategory
  deriving Repr, Inhabited

/-- WS-SM SM5.C: build a `CrossCoreWakeTheorem` with a compile-time-validated identifier. -/
syntax (name := crossCoreWakeTheoremMacro) "ccwt!" str ident term : term

macro_rules
  | `(ccwt! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : CrossCoreWakeTheorem))

/-- WS-SM SM5.C: substantive theorem inventory.  Every entry's identifier is
compile-time-validated by `ccwt!`. -/
def crossCoreWakeTheorems : List CrossCoreWakeTheorem :=
  [-- ── SM5.C.3 lock-set footprints (.lockSet) ──
    ccwt! "wakeThreadLockSet: the wake's cross-domain (object-store + run-queue WRITE) footprint"
      wakeThreadLockSet .lockSet,
    ccwt! "wakeThreadLockSet_write_only: every wake lock is WRITE mode"
      wakeThreadLockSet_write_only .lockSet,
    ccwt! "wakeThreadLockSet_contains_objStore_write: object-store write lock present"
      wakeThreadLockSet_contains_objStore_write .lockSet,
    ccwt! "wakeThreadLockSet_contains_runQueue_write: target run-queue write lock present"
      wakeThreadLockSet_contains_runQueue_write .lockSet,
    ccwt! "wakeThreadLockSet_object_before_runQueue: §4.4 object-before-run-queue order"
      wakeThreadLockSet_object_before_runQueue .lockSet,
    ccwt! "wakeThreadLockSet_keys_nodup: footprint keys are duplicate-free"
      wakeThreadLockSet_keys_nodup .lockSet,
    ccwt! "wakeThreadLockSet_pairwise_le: canonical SchedLockId-ascending acquisition order"
      wakeThreadLockSet_pairwise_le .lockSet,
    ccwt! "handleRescheduleSgiOnCoreLockSet: the SGI-handler footprint (= switch footprint)"
      handleRescheduleSgiOnCoreLockSet .lockSet,
    ccwt! "handleRescheduleSgiOnCoreLockSet_eq: coincides with switchToThreadOnCoreLockSet"
      handleRescheduleSgiOnCoreLockSet_eq .lockSet,
    -- ── SM5.C.9 determineTargetCore routing (.target) ──
    ccwt! "determineTargetCore: production wake-target routing"
      determineTargetCore .target,
    ccwt! "determineTargetCore_bound_eq_affinity: bound thread wakes onto its affinity core"
      determineTargetCore_bound_eq_affinity .target,
    ccwt! "determineTargetCore_unbound_eq_bootCore: unbound thread wakes onto bootCoreId"
      determineTargetCore_unbound_eq_bootCore .target,
    ccwt! "determineTargetCore_no_tcb_eq_bootCore: non-TCB defaults to bootCoreId (fail-safe)"
      determineTargetCore_no_tcb_eq_bootCore .target,
    ccwt! "determineTargetCore_in_range: the wake target is always a valid core"
      determineTargetCore_in_range .target,
    ccwt! "determineTargetCore_admits_thread: the wake target always admits the woken thread (no liveness-stranding)"
      determineTargetCore_admits_thread .target,
    -- ── SM5.C.1 enqueueRunnableOnCore (.enqueue) ──
    ccwt! "enqueueRunnableOnCore: the per-core make-runnable primitive"
      enqueueRunnableOnCore .enqueue,
    ccwt! "enqueueRunnableOnCore_preserves_woken_thread_fields: only ipcState changes on the woken thread"
      enqueueRunnableOnCore_preserves_woken_thread_fields .enqueue,
    ccwt! "enqueueRunnableOnCore_preserves_objects_invExt: preserves object-store invariant"
      enqueueRunnableOnCore_preserves_objects_invExt .enqueue,
    ccwt! "enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed: preserves run-queue well-formedness"
      enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed .enqueue,
    ccwt! "enqueueRunnableOnCore_mem_runQueueOnCore: the woken thread is enqueued"
      enqueueRunnableOnCore_mem_runQueueOnCore .enqueue,
    ccwt! "enqueueRunnableOnCore_makes_ready: the woken thread becomes ipcState=.ready"
      enqueueRunnableOnCore_makes_ready .enqueue,
    ccwt! "enqueueRunnableOnCore_runQueueOnCore_ne: sibling-core run queues framed out"
      enqueueRunnableOnCore_runQueueOnCore_ne .enqueue,
    ccwt! "enqueueRunnableOnCore_currentOnCore: never writes any current slot"
      enqueueRunnableOnCore_currentOnCore .enqueue,
    ccwt! "enqueueRunnableOnCore_getTcb?_ne: every other thread's TCB framed out (AK7-clean)"
      enqueueRunnableOnCore_getTcb?_ne .enqueue,
    ccwt! "enqueueRunnableOnCore_getTcb?_isSome: preserves TCB-resolvability of any thread"
      enqueueRunnableOnCore_getTcb?_isSome .enqueue,
    ccwt! "enqueueRunnableOnCore_no_tcb_noop: fail-closed on a non-TCB target"
      enqueueRunnableOnCore_no_tcb_noop .enqueue,
    ccwt! "enqueueRunnableOnCore_eq_self_of_runnable: single-placement reject — an already-runnable wake is the identity (Codex-P2)"
      enqueueRunnableOnCore_eq_self_of_runnable .enqueue,
    -- ── SM5.C.2 / C.4 / C.10 / C.6 wakeThread semantics + losslessness (.wake) ──
    ccwt! "wakeThread: the cross-core wake transition (state + optional SGI)"
      wakeThread .wake,
    ccwt! "wakeThread_state_eq_enqueue: the wake's state effect is enqueueRunnableOnCore"
      wakeThread_state_eq_enqueue .wake,
    ccwt! "wakeThread_emits_sgi_if_remote: a remote wake of a TCB emits a reschedule SGI (Thm 3.3.1)"
      wakeThread_emits_sgi_if_remote .wake,
    ccwt! "wakeThread_no_sgi_if_local: a local wake emits no SGI"
      wakeThread_no_sgi_if_local .wake,
    ccwt! "wakeThread_no_sgi_if_no_tcb: a ghost (non-TCB) wake emits no SGI (audit-pass-1 guard)"
      wakeThread_no_sgi_if_no_tcb .wake,
    ccwt! "wakeThread_sgi_is_reschedule: every wake SGI is the reschedule kind"
      wakeThread_sgi_is_reschedule .wake,
    ccwt! "wakeThread_target_runQueue_contains: the woken thread is in the target run queue (SM5.C.10)"
      wakeThread_target_runQueue_contains .wake,
    ccwt! "wakeThread_target_admits_thread: the wake target admits the woken thread (no liveness-stranding)"
      wakeThread_target_admits_thread .wake,
    ccwt! "wakeThread_preserves_objects_invExt: the wake preserves the object-store invariant"
      wakeThread_preserves_objects_invExt .wake,
    ccwt! "wakeThread_preserves_target_runQueue_wellFormed: preserves the target run-queue well-formedness"
      wakeThread_preserves_target_runQueue_wellFormed .wake,
    ccwt! "wakeThread_independent_of_other_core: cross-core independence frame"
      wakeThread_independent_of_other_core .wake,
    ccwt! "SchedStep: a single per-core scheduler step (enqueue or switch)"
      SchedStep .wake,
    ccwt! "SchedReachable: the RT-closure of scheduler steps"
      SchedReachable .wake,
    ccwt! "SchedReachable.of_enqueue: an enqueue step is reachable (non-vacuity)"
      SchedReachable.of_enqueue .wake,
    ccwt! "SchedReachable.trans: the reachability relation is transitive"
      SchedReachable.trans .wake,
    ccwt! "wakeThread_lossless: the woken thread is recoverable (Thm 3.3.2, reflexive witness)"
      wakeThread_lossless .wake,
    ccwt! "wakeThread_then_handle_dispatches_current: multi-step wake→handler dispatches to current"
      wakeThread_then_handle_dispatches_current .wake,
    ccwt! "wakeThread_roundtrip_reachable_current: full wake→SGI→current round-trip from the pre-state"
      wakeThread_roundtrip_reachable_current .wake,
    -- ── SM5.C.5 handleRescheduleSgiOnCore (.handler) ──
    ccwt! "handleRescheduleSgiOnCore: the target core's reschedule-SGI handler"
      handleRescheduleSgiOnCore .handler,
    ccwt! "handleRescheduleSgiOnCore_idle_when_none: idle when no eligible thread"
      handleRescheduleSgiOnCore_idle_when_none .handler,
    ccwt! "handleRescheduleSgiOnCore_eq_switch_of_choose_some: dispatch = switchToThreadOnCore"
      handleRescheduleSgiOnCore_eq_switch_of_choose_some .handler,
    ccwt! "handleRescheduleSgiOnCore_switches_current: a dispatch sets the chosen thread current"
      handleRescheduleSgiOnCore_switches_current .handler,
    ccwt! "handleRescheduleSgiOnCore_preserves_objects_invExt: handler preserves object-store invariant"
      handleRescheduleSgiOnCore_preserves_objects_invExt .handler,
    ccwt! "handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed: handler preserves run-queue wf"
      handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed .handler,
    ccwt! "handleRescheduleSgiOnCore_independent_of_other_core: handler cross-core independence"
      handleRescheduleSgiOnCore_independent_of_other_core .handler,
    ccwt! "handleRescheduleSgiOnCore_keeps_current_when_outranked: a lower-priority candidate does not preempt the running thread (Codex-P1)"
      handleRescheduleSgiOnCore_keeps_current_when_outranked .handler,
    -- ── §10 audit-pass-1 invariant preservation (.preservation) ──
    ccwt! "enqueueRunnableOnCore_preserves_currentThreadValidOnCore: preserves SM4.C current-validity"
      enqueueRunnableOnCore_preserves_currentThreadValidOnCore .preservation,
    ccwt! "enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_ne: sibling-core queue consistency"
      enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_ne .preservation,
    ccwt! "enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_self: target queue consistency (don't-wake-current)"
      enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_self .preservation,
    ccwt! "enqueueRunnableOnCore_preserves_runnableThreadIpcReady: runnable-are-ready preserved"
      enqueueRunnableOnCore_preserves_runnableThreadIpcReady .preservation,
    ccwt! "enqueueRunnableOnCore_preserves_blockedOnSendNotRunnable: send-blocked-not-runnable preserved"
      enqueueRunnableOnCore_preserves_blockedOnSendNotRunnable .preservation,
    ccwt! "enqueueRunnableOnCore_preserves_blockedOnReceiveNotRunnable: recv-blocked-not-runnable preserved"
      enqueueRunnableOnCore_preserves_blockedOnReceiveNotRunnable .preservation,
    ccwt! "enqueueRunnableOnCore_preserves_blockedOnCallNotRunnable: call-blocked-not-runnable preserved"
      enqueueRunnableOnCore_preserves_blockedOnCallNotRunnable .preservation,
    ccwt! "enqueueRunnableOnCore_preserves_blockedOnReplyNotRunnable: reply-blocked-not-runnable preserved"
      enqueueRunnableOnCore_preserves_blockedOnReplyNotRunnable .preservation,
    ccwt! "enqueueRunnableOnCore_preserves_blockedOnNotificationNotRunnable: ntfn-blocked-not-runnable preserved"
      enqueueRunnableOnCore_preserves_blockedOnNotificationNotRunnable .preservation,
    ccwt! "enqueueRunnableOnCore_preserves_ipcSchedulerContract: the full IPC↔scheduler coherence bundle"
      enqueueRunnableOnCore_preserves_ipcSchedulerContract .preservation,
    ccwt! "wakeThread_preserves_currentThreadValidOnCore: the wake preserves current-validity (every core)"
      wakeThread_preserves_currentThreadValidOnCore .preservation,
    ccwt! "wakeThread_preserves_ipcSchedulerContract: the wake preserves IPC↔scheduler coherence (gap-b headline)"
      wakeThread_preserves_ipcSchedulerContract .preservation,
    ccwt! "wakeThread_preserves_queueCurrentConsistentOnCore: the wake preserves queue/current consistency"
      wakeThread_preserves_queueCurrentConsistentOnCore .preservation,
    -- ── SM5.C.11 latency + SM5.C.8 affinity + SM5.C.4 FFI emit + §11 memory model ──
    ccwt! "wakeSgiCount: the number of SGIs a wake emits"
      wakeSgiCount .latencyAffinityEmit,
    ccwt! "wakeThread_emits_at_most_one_sgi: bounded emission (no SGI storm)"
      wakeThread_emits_at_most_one_sgi .latencyAffinityEmit,
    ccwt! "rescheduleSgi_lowest_intid: reschedule is the lowest-INTID kernel SGI"
      rescheduleSgi_lowest_intid .latencyAffinityEmit,
    ccwt! "sgiDeliveryLatencyBound_eq_zero: no kernel SGI is serviced ahead of reschedule"
      sgiDeliveryLatencyBound_eq_zero .latencyAffinityEmit,
    ccwt! "sgiDeliveryLatencyBound_counts_higher_priority_kernel_sgis: honest scoping of the =0 bound"
      sgiDeliveryLatencyBound_counts_higher_priority_kernel_sgis .latencyAffinityEmit,
    ccwt! "setThreadCpuAffinity: the affinity-control op"
      setThreadCpuAffinity .latencyAffinityEmit,
    ccwt! "setThreadCpuAffinity_sets_affinity: sets the target's affinity"
      setThreadCpuAffinity_sets_affinity .latencyAffinityEmit,
    ccwt! "setThreadCpuAffinity_error_of_no_tcb: fail-closed on a non-TCB target"
      setThreadCpuAffinity_error_of_no_tcb .latencyAffinityEmit,
    ccwt! "setThreadCpuAffinity_preserves_objects_invExt: preserves the object-store invariant"
      setThreadCpuAffinity_preserves_objects_invExt .latencyAffinityEmit,
    ccwt! "setThreadCpuAffinity_preserves_scheduler: leaves the scheduler state untouched"
      setThreadCpuAffinity_preserves_scheduler .latencyAffinityEmit,
    ccwt! "setThreadCpuAffinity_affects_determineTargetCore: binding feeds the wake target"
      setThreadCpuAffinity_affects_determineTargetCore .latencyAffinityEmit,
    ccwt! "Concurrency.emitWakeSgi: the FFI SGI-emission wrapper for the wake's optional SGI"
      SeLe4n.Kernel.Concurrency.emitWakeSgi .latencyAffinityEmit,
    ccwt! "Concurrency.sendRescheduleSgi: emit a cross-core reschedule SGI"
      SeLe4n.Kernel.Concurrency.sendRescheduleSgi .latencyAffinityEmit,
    ccwt! "Concurrency.coreIdTargetMask: CoreId → GIC single-bit target mask"
      SeLe4n.Kernel.Concurrency.coreIdTargetMask .latencyAffinityEmit,
    ccwt! "Concurrency.wakeOrdering_happensBefore: the wake's BKL release→acquire happens-before (§11)"
      SeLe4n.Kernel.Concurrency.wakeOrdering_happensBefore .latencyAffinityEmit,
    ccwt! "Concurrency.wakeOrdering_synchronizesWith: the wake's release-store synchronizes-with the acquire-load"
      SeLe4n.Kernel.Concurrency.wakeOrdering_synchronizesWith .latencyAffinityEmit,
    ccwt! "Concurrency.wakeOrderingTrace_wellFormed: the wake's ordering trace is well-formed"
      SeLe4n.Kernel.Concurrency.wakeOrderingTrace_wellFormed .latencyAffinityEmit]

/-- WS-SM SM5.C: the inventory has 81 substantive entries.  A regression that
adds a new SM5.C theorem without registering it fails this count witness at the
Tier-3 surface check. -/
theorem crossCoreWakeTheorems_count : crossCoreWakeTheorems.length = 83 := by decide

/-- WS-SM SM5.C: 9 entries in the `lockSet` category (SM5.C.3). -/
theorem crossCoreWakeTheorems_lockSet_count :
    (crossCoreWakeTheorems.filter (fun t => t.category == .lockSet)).length = 9 := by decide

/-- WS-SM SM5.C: 6 entries in the `target` category (SM5.C.9). -/
theorem crossCoreWakeTheorems_target_count :
    (crossCoreWakeTheorems.filter (fun t => t.category == .target)).length = 6 := by decide

/-- WS-SM SM5.C: 12 entries in the `enqueue` category (SM5.C.1). -/
theorem crossCoreWakeTheorems_enqueue_count :
    (crossCoreWakeTheorems.filter (fun t => t.category == .enqueue)).length = 12 := by decide

/-- WS-SM SM5.C: 18 entries in the `wake` category (SM5.C.2 / C.4 / C.10 / C.6). -/
theorem crossCoreWakeTheorems_wake_count :
    (crossCoreWakeTheorems.filter (fun t => t.category == .wake)).length = 18 := by decide

/-- WS-SM SM5.C: 8 entries in the `handler` category (SM5.C.5). -/
theorem crossCoreWakeTheorems_handler_count :
    (crossCoreWakeTheorems.filter (fun t => t.category == .handler)).length = 8 := by decide

/-- WS-SM SM5.C: 13 entries in the `preservation` category (§10 audit-pass-1). -/
theorem crossCoreWakeTheorems_preservation_count :
    (crossCoreWakeTheorems.filter (fun t => t.category == .preservation)).length = 13 := by decide

/-- WS-SM SM5.C: 17 entries in the `latencyAffinityEmit` category
(SM5.C.11 latency + SM5.C.8 affinity + SM5.C.4 FFI emit + §11 memory model). -/
theorem crossCoreWakeTheorems_latencyAffinityEmit_count :
    (crossCoreWakeTheorems.filter (fun t => t.category == .latencyAffinityEmit)).length = 17 := by decide

/-- WS-SM SM5.C: per-category counts sum to the total. -/
theorem crossCoreWakeTheorems_partition_sum :
    (crossCoreWakeTheorems.filter (fun t => t.category == .lockSet)).length +
    (crossCoreWakeTheorems.filter (fun t => t.category == .target)).length +
    (crossCoreWakeTheorems.filter (fun t => t.category == .enqueue)).length +
    (crossCoreWakeTheorems.filter (fun t => t.category == .wake)).length +
    (crossCoreWakeTheorems.filter (fun t => t.category == .handler)).length +
    (crossCoreWakeTheorems.filter (fun t => t.category == .preservation)).length +
    (crossCoreWakeTheorems.filter (fun t => t.category == .latencyAffinityEmit)).length =
    crossCoreWakeTheorems.length := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.C: every inventory identifier is unique.

    Audit-pass-2: proved by the **kernel-sound `decide`**, not `native_decide`.
    The SM3 inventories use `native_decide` here, but `native_decide` trusts the
    compiled `Decidable` evaluation (`Lean.ofReduceBool`), which — as this audit
    found — can "prove" a *false* `Nodup` when the data accidentally contains a
    duplicate (the audit caught a copy-pasted duplicate identifier that
    `native_decide` masked).  Kernel `decide` refuses a false proposition, so it
    is the correct tool: a duplicate identifier now fails the build at this
    theorem.

    Audit-pass-2 (maxRecDepth): the 81-entry list's `Nodup` decision procedure
    recurses past the default `maxRecDepth` of 512 when reducing in the kernel
    (the longer `description` strings in `crossCoreWakeTheorems_descriptions_nodup`
    overflow it first).  Both Nodup witnesses therefore run under an elevated
    `set_option maxRecDepth 10000`, which only raises the recursion *limit* (it
    adds no work and no axioms — the proof remains a kernel-checked
    `of_decide_eq_true`, not a `native_decide`). -/
theorem crossCoreWakeTheorems_identifiers_nodup :
    (crossCoreWakeTheorems.map (·.identifier)).Nodup := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.C: every inventory description is unique.  Kernel-sound `decide`
    under an elevated `maxRecDepth` (see `crossCoreWakeTheorems_identifiers_nodup` for why
    not `native_decide`, and why the depth is raised). -/
theorem crossCoreWakeTheorems_descriptions_nodup :
    (crossCoreWakeTheorems.map (·.description)).Nodup := by decide

end SeLe4n.Kernel
