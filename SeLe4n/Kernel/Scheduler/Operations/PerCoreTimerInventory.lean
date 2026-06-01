-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick
import SeLe4n.Kernel.PerCoreTimerEntry

/-!
# WS-SM SM5.D — Theorem inventory

Aggregates the SM5.D per-core-timer-tick substantive theorems into a single typed
inventory with size and per-category witnesses.  Mirrors the SM5.C
`CrossCoreWakeInventory.lean` pattern (and, before it, the SM3.A/B/C/D/E inventories): a
typed `PerCoreTimerTheorem` list whose identifiers are compile-time-validated by the
`pctt!` macro, so a typo or stale rename fails the build at this module's
elaboration step with "unknown identifier '<name>'".

Seven categories matching the plan §3.4/§4.4/§5 sub-tasks:

* `.lockSet` — SM5.D.3/§4.4 cross-domain lock-set footprints (static + the
  bound-exhausted dynamic / complete over-approximations) and the
  `SchedLockId` object < run-queue < replenish-queue order.
* `.domain` — SM5.D.6 domain accounting (`decrementDomainTimeOnCore` in-tick +
  the full `switchDomainOnCore` / `scheduleDomainOnCore` re-dispatch).
* `.replenish` — SM5.D.4 CBS replenishment + cross-core wake.
* `.budget` — SM5.D.5 budget tick + the IPC-timeout object-store preservation
  chain.
* `.tick` — SM5.D.2/.9 `timerTickOnCore` semantics / headlines + machine /
  lastTimeoutErrors frames.
* `.preservation` — §7 B1/B2/B3 per-core invariant preservation (the SM5.C-parity
  coverage: `currentThreadValidOnCore` unconditional, `runQueueOnCoreWellFormed`
  and `queueCurrentConsistentOnCore` modulo the SM5.F-tracked bound-exhausted
  timeout gap).
* `.decidability` — SM5.D.8 decidable witnesses + the SM5.D.1 export seam.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

/-- WS-SM SM5.D: category tag for the SM5.D theorem inventory. -/
inductive PerCoreTimerCategory where
  /-- SM5.D.3/§4.4 lock-set footprints + SchedLockId order. -/
  | lockSet
  /-- SM5.D.6 domain accounting + re-dispatch. -/
  | domain
  /-- SM5.D.4 CBS replenishment + cross-core wake. -/
  | replenish
  /-- SM5.D.5 budget tick + IPC-timeout preservation. -/
  | budget
  /-- SM5.D.2/.9 tick semantics / headlines + frames. -/
  | tick
  /-- §7 B1/B2/B3 per-core invariant preservation. -/
  | preservation
  /-- SM5.D.8 decidable witnesses + SM5.D.1 export seam. -/
  | decidability
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM5.D: a theorem entry in the SM5.D inventory.  Records a description,
the fully-qualified name as a `String`, a compile-time elaboration witness, and a
category tag. -/
structure PerCoreTimerTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : PerCoreTimerCategory
  deriving Repr, Inhabited

/-- WS-SM SM5.D: build a `PerCoreTimerTheorem` with a compile-time-validated identifier. -/
syntax (name := perCoreTimerTheoremMacro) "pctt!" str ident term : term

macro_rules
  | `(pctt! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : PerCoreTimerTheorem))

/-- WS-SM SM5.D: substantive theorem inventory.  Every entry's identifier is
compile-time-validated by `pctt!`. -/
def perCoreTimerTheorems : List PerCoreTimerTheorem :=
  [
    -- ── .lockSet ──
    pctt! "timerTickOnCoreLockSet: SM5.D.3 cross-domain (object/run-queue/replenish-queue WRITE) footprint"
      timerTickOnCoreLockSet .lockSet,
    pctt! "timerTickOnCoreLockSet_write_only: every static tick lock is WRITE mode"
      timerTickOnCoreLockSet_write_only .lockSet,
    pctt! "timerTickOnCoreLockSet_contains_objStore_write: object-store write lock present"
      timerTickOnCoreLockSet_contains_objStore_write .lockSet,
    pctt! "timerTickOnCoreLockSet_contains_runQueue_write: run-queue write lock present"
      timerTickOnCoreLockSet_contains_runQueue_write .lockSet,
    pctt! "timerTickOnCoreLockSet_contains_replenishQueue_write: replenish-queue write lock present"
      timerTickOnCoreLockSet_contains_replenishQueue_write .lockSet,
    pctt! "timerTickOnCoreLockSet_keys_nodup: footprint keys are duplicate-free"
      timerTickOnCoreLockSet_keys_nodup .lockSet,
    pctt! "timerTickOnCoreLockSet_pairwise_le: canonical SchedLockId-ascending acquisition order"
      timerTickOnCoreLockSet_pairwise_le .lockSet,
    pctt! "timerTickOnCoreLockSet_size_le_maxLockSetSize: SM5.D.7 WCRT size bound"
      timerTickOnCoreLockSet_size_le_maxLockSetSize .lockSet,
    pctt! "timerTickOnCoreTimeoutDynamicLockSet: SM5.D.3 bound-exhausted timeout dynamic footprint"
      timerTickOnCoreTimeoutDynamicLockSet .lockSet,
    pctt! "timerTickOnCoreTimeoutDynamicLockSet_eq: dynamic timeout footprint shape"
      timerTickOnCoreTimeoutDynamicLockSet_eq .lockSet,
    pctt! "timerTickOnCoreTimeoutDynamicLockSet_write_only: dynamic timeout footprint is WRITE-only"
      timerTickOnCoreTimeoutDynamicLockSet_write_only .lockSet,
    pctt! "timerTickOnCoreCompleteLockSet: complete (static + timeout) over-approximation footprint"
      timerTickOnCoreCompleteLockSet .lockSet,
    pctt! "timerTickOnCoreCompleteLockSet_contains_static: complete footprint contains the static set"
      timerTickOnCoreCompleteLockSet_contains_static .lockSet,
    pctt! "timerTickOnCoreCompleteLockSet_contains_timeout: complete footprint contains the timeout set"
      timerTickOnCoreCompleteLockSet_contains_timeout .lockSet,
    pctt! "timerTickOnCoreCompleteLockSet_write_only: complete footprint is WRITE-only"
      timerTickOnCoreCompleteLockSet_write_only .lockSet,
    pctt! "timerTickOnCoreCompleteLockSet_keys_nodup: complete footprint keys duplicate-free"
      timerTickOnCoreCompleteLockSet_keys_nodup .lockSet,
    pctt! "timerTickOnCoreCompleteLockSet_pairwise_le: complete footprint SchedLockId-ascending"
      timerTickOnCoreCompleteLockSet_pairwise_le .lockSet,
    pctt! "timerTickOnCoreCompleteLockSet_size_le_maxLockSetSize: complete footprint WCRT size bound"
      timerTickOnCoreCompleteLockSet_size_le_maxLockSetSize .lockSet,
    pctt! "SchedLockId.object_lt_replenishQueue: SM5.D.3/§4.4 object lock before replenish-queue lock"
      SchedLockId.object_lt_replenishQueue .lockSet,
    pctt! "SchedLockId.runQueue_lt_replenishQueue: SM5.D.3/§4.4 run-queue lock before replenish-queue lock"
      SchedLockId.runQueue_lt_replenishQueue .lockSet,
    -- ── .domain ──
    pctt! "decrementDomainTimeOnCore_decrements: non-boundary domain-time decrement (pure, no rotation)"
      decrementDomainTimeOnCore_decrements .domain,
    pctt! "decrementDomainTimeOnCore_activeDomainOnCore: the pure decrement never rotates the active domain"
      decrementDomainTimeOnCore_activeDomainOnCore .domain,
    pctt! "decrementDomainTimeOnCore_domainTimeRemainingOnCore_ne: cross-core domain-time frame"
      decrementDomainTimeOnCore_domainTimeRemainingOnCore_ne .domain,
    pctt! "decrementDomainTimeOnCore_preserves_domainTimeRemainingPositiveOnCore: B3 domain-time positivity preserved (under >1)"
      decrementDomainTimeOnCore_preserves_domainTimeRemainingPositiveOnCore .domain,
    pctt! "switchDomainOnCore_singleDomain_noop: SM5.D.6 full domain switch no-op (empty schedule)"
      switchDomainOnCore_singleDomain_noop .domain,
    pctt! "switchDomainOnCore_preserves_objects_invExt: SM5.D.6 domain switch preserves object-store invariant"
      switchDomainOnCore_preserves_objects_invExt .domain,
    pctt! "switchDomainOnCore_sets_currentOnCore_none: SM5.D.6 domain switch clears current"
      switchDomainOnCore_sets_currentOnCore_none .domain,
    pctt! "switchDomainOnCore_rotates: SM5.D.6 domain switch rotates the active domain"
      switchDomainOnCore_rotates .domain,
    pctt! "scheduleDomainOnCore_decrements: SM5.D.6 sub-boundary domain re-dispatch decrements"
      scheduleDomainOnCore_decrements .domain,
    pctt! "scheduleDomainOnCore_preserves_objects_invExt: SM5.D.6 domain re-dispatch preserves object-store invariant"
      scheduleDomainOnCore_preserves_objects_invExt .domain,
    -- ── .replenish ──
    pctt! "refillSchedContext_preserves_objects_invExt: refill preserves object-store invariant"
      refillSchedContext_preserves_objects_invExt .replenish,
    pctt! "enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed_anyCore: wake enqueue preserves run-queue well-formedness (any core)"
      enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed_anyCore .replenish,
    pctt! "wakeThread_preserves_runQueueOnCore_wellFormed_anyCore: wake preserves run-queue well-formedness (any core)"
      wakeThread_preserves_runQueueOnCore_wellFormed_anyCore .replenish,
    pctt! "processOneReplenishmentOnCore_preserves_objects_invExt: one replenishment preserves object-store invariant"
      processOneReplenishmentOnCore_preserves_objects_invExt .replenish,
    pctt! "processOneReplenishmentOnCore_preserves_runQueueOnCore_wellFormed: one replenishment preserves run-queue well-formedness"
      processOneReplenishmentOnCore_preserves_runQueueOnCore_wellFormed .replenish,
    pctt! "processReplenishmentsDueOnCore_preserves_objects_invExt: SM5.D.4 all-replenishments preserves object-store invariant"
      processReplenishmentsDueOnCore_preserves_objects_invExt .replenish,
    pctt! "processReplenishmentsDueOnCore_preserves_runQueueOnCore_wellFormed: SM5.D.4 all-replenishments preserves run-queue well-formedness"
      processReplenishmentsDueOnCore_preserves_runQueueOnCore_wellFormed .replenish,
    pctt! "processOneReplenishmentOnCore_no_sgi_if_no_target: no wake target emits no SGI"
      processOneReplenishmentOnCore_no_sgi_if_no_target .replenish,
    pctt! "processOneReplenishmentOnCore_local_no_sgi: local wake emits no cross-core SGI"
      processOneReplenishmentOnCore_local_no_sgi .replenish,
    pctt! "cbsReplenish_can_wake_remote_core: SM5.D.4 headline: cross-core CBS replenish wakes a remote core"
      cbsReplenish_can_wake_remote_core .replenish,
    pctt! "runningOnSomeCore: audit-pass-2 guard — is tid current on some core (no double-placement)"
      runningOnSomeCore .replenish,
    -- ── .budget ──
    pctt! "revertPriorityInheritance_preserves_objects_invExt: PIP revert preserves object-store invariant"
      revertPriorityInheritance_preserves_objects_invExt .budget,
    pctt! "timeoutThread_preserves_objects_invExt: timeout-thread preserves object-store invariant"
      timeoutThread_preserves_objects_invExt .budget,
    pctt! "timeoutBlockedThreads_preserves_objects_invExt: timeout-blocked-threads preserves object-store invariant"
      timeoutBlockedThreads_preserves_objects_invExt .budget,
    pctt! "timerTickBudgetOnCore_preserves_objects_invExt: SM5.D.5 budget tick preserves object-store invariant"
      timerTickBudgetOnCore_preserves_objects_invExt .budget,
    pctt! "timerTickBudgetOnCore_unbound_not_preempted: unbound running thread not preempted"
      timerTickBudgetOnCore_unbound_not_preempted .budget,
    pctt! "timerTickBudgetOnCore_unbound_preempts: unbound expired thread preempted"
      timerTickBudgetOnCore_unbound_preempts .budget,
    pctt! "timerTickBudgetOnCore_bound_preempts: bound budget-exhausted thread preempted"
      timerTickBudgetOnCore_bound_preempts .budget,
    pctt! "timerTickBudgetOnCore_bound_not_preempted: bound budget-remaining thread not preempted"
      timerTickBudgetOnCore_bound_not_preempted .budget,
    pctt! "timerTickBudgetOnCore_donated_preempts: donated budget-exhausted thread preempted"
      timerTickBudgetOnCore_donated_preempts .budget,
    pctt! "saveOutgoingContextOnCore_preserves_objects_invExt: context save preserves object-store invariant"
      saveOutgoingContextOnCore_preserves_objects_invExt .budget,
    pctt! "restoreIncomingContext_objects_eq: context restore is object-neutral"
      restoreIncomingContext_objects_eq .budget,
    pctt! "scheduleEffectiveOnCore_preserves_objects_invExt: SM5.D.5 reschedule preserves object-store invariant"
      scheduleEffectiveOnCore_preserves_objects_invExt .budget,
    -- ── .tick ──
    pctt! "timerTickOnCorePreDomain: SM5.D.2 pre-domain prepared state"
      timerTickOnCorePreDomain .tick,
    pctt! "timerTickOnCorePrepared: SM5.D.2 prepared (post-replenish/post-domain) state"
      timerTickOnCorePrepared .tick,
    pctt! "timerTickOnCorePrepared_fst_eq: prepared state is the domain-decrement of pre-domain"
      timerTickOnCorePrepared_fst_eq .tick,
    pctt! "timerTickOnCore_eq_prepared: SM5.D.2 tick = budget dispatch on the prepared state"
      timerTickOnCore_eq_prepared .tick,
    pctt! "timerTickOnCorePrepared_machine_eq: prepared state preserves the machine"
      timerTickOnCorePrepared_machine_eq .tick,
    pctt! "timerTickOnCorePrepared_lastTimeoutErrors_eq: prepared state clears lastTimeoutErrors"
      timerTickOnCorePrepared_lastTimeoutErrors_eq .tick,
    pctt! "timerTickOnCorePrepared_objects_invExt: prepared state preserves object-store invariant"
      timerTickOnCorePrepared_objects_invExt .tick,
    pctt! "timerTickOnCore_idle: SM5.D.2 idle path is the prepared state"
      timerTickOnCore_idle .tick,
    pctt! "timerTickOnCore_advances_per_core: SM5.D.2 headline: per-core advance, no global-timer advance"
      timerTickOnCore_advances_per_core .tick,
    pctt! "timerTickOnCore_clears_lastTimeoutErrors: SM5.D.9 tick clears lastTimeoutErrors"
      timerTickOnCore_clears_lastTimeoutErrors .tick,
    pctt! "timerTickOnCore_preempts_local: SM5.D.5 headline: budget exhaustion re-dispatches locally"
      timerTickOnCore_preempts_local .tick,
    pctt! "timerTickOnCore_preserves_objects_invExt: SM5.D.2 tick preserves object-store invariant"
      timerTickOnCore_preserves_objects_invExt .tick,
    pctt! "enqueueRunnableOnCore_lastTimeoutErrorsOnCore: wake enqueue frames lastTimeoutErrors"
      enqueueRunnableOnCore_lastTimeoutErrorsOnCore .tick,
    pctt! "processOneReplenishmentOnCore_machine_eq: one replenishment frames the machine"
      processOneReplenishmentOnCore_machine_eq .tick,
    pctt! "processOneReplenishmentOnCore_lastTimeoutErrorsOnCore_eq: one replenishment frames lastTimeoutErrors"
      processOneReplenishmentOnCore_lastTimeoutErrorsOnCore_eq .tick,
    pctt! "processReplenishmentsDueOnCore_machine_eq: all-replenishments frames the machine"
      processReplenishmentsDueOnCore_machine_eq .tick,
    pctt! "processReplenishmentsDueOnCore_lastTimeoutErrorsOnCore_eq: all-replenishments frames lastTimeoutErrors"
      processReplenishmentsDueOnCore_lastTimeoutErrorsOnCore_eq .tick,
    pctt! "decrementDomainTimeOnCore_lastTimeoutErrorsOnCore: domain decrement frames lastTimeoutErrors"
      decrementDomainTimeOnCore_lastTimeoutErrorsOnCore .tick,
    -- ── .preservation ──
    pctt! "decrementDomainTimeOnCore_preserves_currentThreadValidOnCore: B1: domain decrement preserves current-thread validity"
      decrementDomainTimeOnCore_preserves_currentThreadValidOnCore .preservation,
    pctt! "decrementDomainTimeOnCore_preserves_queueCurrentConsistentOnCore: B1: domain decrement preserves dequeue-on-dispatch consistency"
      decrementDomainTimeOnCore_preserves_queueCurrentConsistentOnCore .preservation,
    pctt! "decrementDomainTimeOnCore_preserves_runnableThreadsAreTCBsOnCore: B1: domain decrement preserves runnable-threads-are-TCBs"
      decrementDomainTimeOnCore_preserves_runnableThreadsAreTCBsOnCore .preservation,
    pctt! "decrementDomainTimeOnCore_preserves_runQueueOnCoreWellFormed: B2: domain decrement preserves run-queue well-formedness"
      decrementDomainTimeOnCore_preserves_runQueueOnCoreWellFormed .preservation,
    pctt! "saveOutgoingContextOnCore_scheduler_eq: context save frames the scheduler"
      saveOutgoingContextOnCore_scheduler_eq .preservation,
    pctt! "saveOutgoingContextOnCore_getTcb?_isSome: context save preserves TCB-resolvability"
      saveOutgoingContextOnCore_getTcb?_isSome .preservation,
    pctt! "scheduleEffectiveOnCore_objects_eq: reschedule object write is the context save"
      scheduleEffectiveOnCore_objects_eq .preservation,
    pctt! "scheduleEffectiveOnCore_getTcb?_isSome: reschedule preserves TCB-resolvability"
      scheduleEffectiveOnCore_getTcb?_isSome .preservation,
    pctt! "scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed: B2: reschedule preserves run-queue well-formedness"
      scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed .preservation,
    pctt! "scheduleEffectiveOnCore_establishes_currentThreadValidOnCore: B1: reschedule establishes current-thread validity"
      scheduleEffectiveOnCore_establishes_currentThreadValidOnCore .preservation,
    pctt! "scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore: B1: reschedule establishes dequeue-on-dispatch consistency"
      scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore .preservation,
    pctt! "scheduleEffectiveOnCore_runQueue_toList_subset: reschedule post run queue is a subset of the pre run queue"
      scheduleEffectiveOnCore_runQueue_toList_subset .preservation,
    pctt! "scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore: B1: reschedule preserves runnable-threads-are-TCBs"
      scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore .preservation,
    pctt! "timerTickBudgetOnCore_notPreempted_scheduler_eq: not-preempted budget tick frames the scheduler"
      timerTickBudgetOnCore_notPreempted_scheduler_eq .preservation,
    pctt! "timerTickBudgetOnCore_notPreempted_getTcb?_tid: not-preempted budget tick keeps the charged thread a TCB"
      timerTickBudgetOnCore_notPreempted_getTcb?_tid .preservation,
    pctt! "timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCoreWellFormed: B2 discharge: not-preempted budget tick preserves run-queue well-formedness"
      timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCoreWellFormed .preservation,
    pctt! "timerTickOnCore_preserves_currentThreadValidOnCore: B1 headline: the tick preserves current-thread validity (unconditional)"
      timerTickOnCore_preserves_currentThreadValidOnCore .preservation,
    pctt! "timerTickOnCorePrepared_runQueueOnCore_wellFormed: B2: the prepared state preserves run-queue well-formedness"
      timerTickOnCorePrepared_runQueueOnCore_wellFormed .preservation,
    pctt! "timerTickOnCore_preserves_runQueueOnCoreWellFormed: B2 headline: the tick preserves run-queue well-formedness (parameterized)"
      timerTickOnCore_preserves_runQueueOnCoreWellFormed .preservation,
    pctt! "timerTickOnCore_preserves_queueCurrentConsistentOnCore: the tick preserves dequeue-on-dispatch consistency (parameterized)"
      timerTickOnCore_preserves_queueCurrentConsistentOnCore .preservation,
    pctt! "saveOutgoingContextOnCore_getTcb?_domain: context save preserves a thread's domain"
      saveOutgoingContextOnCore_getTcb?_domain .preservation,
    pctt! "scheduleEffectiveOnCore_getTcb?_domain: reschedule preserves a thread's domain"
      scheduleEffectiveOnCore_getTcb?_domain .preservation,
    pctt! "scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore: reschedule dispatches in the active domain"
      scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore .preservation,
    pctt! "timerTickBudgetOnCore_notPreempted_getTcb?_domain: not-preempted budget tick preserves the charged thread's domain"
      timerTickBudgetOnCore_notPreempted_getTcb?_domain .preservation,
    pctt! "timerTickOnCore_preserves_currentThreadInActiveDomainOnCore: audit-pass-2 capstone — the tick keeps current in its active domain"
      timerTickOnCore_preserves_currentThreadInActiveDomainOnCore .preservation,
    -- ── .decidability ──
    pctt! "timerTickOnCoreSucceeds: SM5.D.8 tick-succeeds decidable predicate"
      timerTickOnCoreSucceeds .decidability,
    pctt! "timerTickOnCoreEmitsSgi: SM5.D.8 tick-emits-SGI decidable predicate"
      timerTickOnCoreEmitsSgi .decidability,
    pctt! "timerTickBudgetOnCorePreempts: SM5.D.8 budget-preempts decidable predicate"
      timerTickBudgetOnCorePreempts .decidability,
    pctt! "perCoreTimerTickEntry: SM5.D.1 C-callable per-core timer-entry seam"
      perCoreTimerTickEntry .decidability,
    pctt! "perCoreTimerTickEntry_returns_unit_marker: SM5.D.1 entry-seam placeholder marker"
      perCoreTimerTickEntry_returns_unit_marker .decidability  ]

/-- WS-SM SM5.D: the inventory has 100 substantive entries (audit-pass-2: removed
5 obsolete in-tick domain-rotation theorems + the retired `timerTickOnCore_rotates_domain`;
added 2 pure-decrement frames + 5 `currentThreadInActiveDomain` preservation theorems).
A regression that adds a new SM5.D theorem without registering it fails this count
witness at the Tier-3 surface check. -/
theorem perCoreTimerTheorems_count : perCoreTimerTheorems.length = 101 := by decide

theorem perCoreTimerTheorems_lockSet_count :
    (perCoreTimerTheorems.filter (fun t => t.category == .lockSet)).length = 20 := by decide

theorem perCoreTimerTheorems_domain_count :
    (perCoreTimerTheorems.filter (fun t => t.category == .domain)).length = 10 := by decide

theorem perCoreTimerTheorems_replenish_count :
    (perCoreTimerTheorems.filter (fun t => t.category == .replenish)).length = 11 := by decide

theorem perCoreTimerTheorems_budget_count :
    (perCoreTimerTheorems.filter (fun t => t.category == .budget)).length = 12 := by decide

theorem perCoreTimerTheorems_tick_count :
    (perCoreTimerTheorems.filter (fun t => t.category == .tick)).length = 18 := by decide

theorem perCoreTimerTheorems_preservation_count :
    (perCoreTimerTheorems.filter (fun t => t.category == .preservation)).length = 25 := by decide

theorem perCoreTimerTheorems_decidability_count :
    (perCoreTimerTheorems.filter (fun t => t.category == .decidability)).length = 5 := by decide

/-- WS-SM SM5.D: per-category counts sum to the total. -/
theorem perCoreTimerTheorems_partition_sum :
    (perCoreTimerTheorems.filter (fun t => t.category == .lockSet)).length +
    (perCoreTimerTheorems.filter (fun t => t.category == .domain)).length +
    (perCoreTimerTheorems.filter (fun t => t.category == .replenish)).length +
    (perCoreTimerTheorems.filter (fun t => t.category == .budget)).length +
    (perCoreTimerTheorems.filter (fun t => t.category == .tick)).length +
    (perCoreTimerTheorems.filter (fun t => t.category == .preservation)).length +
    (perCoreTimerTheorems.filter (fun t => t.category == .decidability)).length =
    perCoreTimerTheorems.length := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.D: every inventory identifier is unique.  Kernel-sound `decide`
(not `native_decide`): a duplicate identifier fails the build here (per the SM5.C
audit-pass-2 precedent that `native_decide` can mask a copy-paste duplicate). -/
theorem perCoreTimerTheorems_identifiers_nodup :
    (perCoreTimerTheorems.map (·.identifier)).Nodup := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.D: every inventory description is unique. -/
theorem perCoreTimerTheorems_descriptions_nodup :
    (perCoreTimerTheorems.map (·.description)).Nodup := by decide

end SeLe4n.Kernel
