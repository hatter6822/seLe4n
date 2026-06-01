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
`Sm5CInventory.lean` pattern (and, before it, the SM3.A/B/C/D/E inventories): a
typed `Sm5DTheorem` list whose identifiers are compile-time-validated by the
`s5dt!` macro, so a typo or stale rename fails the build at this module's
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
inductive Sm5DCategory where
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
structure Sm5DTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : Sm5DCategory
  deriving Repr, Inhabited

/-- WS-SM SM5.D: build a `Sm5DTheorem` with a compile-time-validated identifier. -/
syntax (name := s5dtMacro) "s5dt!" str ident term : term

macro_rules
  | `(s5dt! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : Sm5DTheorem))

/-- WS-SM SM5.D: substantive theorem inventory.  Every entry's identifier is
compile-time-validated by `s5dt!`. -/
def sm5DTheorems : List Sm5DTheorem :=
  [
    -- ── .lockSet ──
    s5dt! "timerTickOnCoreLockSet: SM5.D.3 cross-domain (object/run-queue/replenish-queue WRITE) footprint"
      timerTickOnCoreLockSet .lockSet,
    s5dt! "timerTickOnCoreLockSet_write_only: every static tick lock is WRITE mode"
      timerTickOnCoreLockSet_write_only .lockSet,
    s5dt! "timerTickOnCoreLockSet_contains_objStore_write: object-store write lock present"
      timerTickOnCoreLockSet_contains_objStore_write .lockSet,
    s5dt! "timerTickOnCoreLockSet_contains_runQueue_write: run-queue write lock present"
      timerTickOnCoreLockSet_contains_runQueue_write .lockSet,
    s5dt! "timerTickOnCoreLockSet_contains_replenishQueue_write: replenish-queue write lock present"
      timerTickOnCoreLockSet_contains_replenishQueue_write .lockSet,
    s5dt! "timerTickOnCoreLockSet_keys_nodup: footprint keys are duplicate-free"
      timerTickOnCoreLockSet_keys_nodup .lockSet,
    s5dt! "timerTickOnCoreLockSet_pairwise_le: canonical SchedLockId-ascending acquisition order"
      timerTickOnCoreLockSet_pairwise_le .lockSet,
    s5dt! "timerTickOnCoreLockSet_size_le_maxLockSetSize: SM5.D.7 WCRT size bound"
      timerTickOnCoreLockSet_size_le_maxLockSetSize .lockSet,
    s5dt! "timerTickOnCoreTimeoutDynamicLockSet: SM5.D.3 bound-exhausted timeout dynamic footprint"
      timerTickOnCoreTimeoutDynamicLockSet .lockSet,
    s5dt! "timerTickOnCoreTimeoutDynamicLockSet_eq: dynamic timeout footprint shape"
      timerTickOnCoreTimeoutDynamicLockSet_eq .lockSet,
    s5dt! "timerTickOnCoreTimeoutDynamicLockSet_write_only: dynamic timeout footprint is WRITE-only"
      timerTickOnCoreTimeoutDynamicLockSet_write_only .lockSet,
    s5dt! "timerTickOnCoreCompleteLockSet: complete (static + timeout) over-approximation footprint"
      timerTickOnCoreCompleteLockSet .lockSet,
    s5dt! "timerTickOnCoreCompleteLockSet_contains_static: complete footprint contains the static set"
      timerTickOnCoreCompleteLockSet_contains_static .lockSet,
    s5dt! "timerTickOnCoreCompleteLockSet_contains_timeout: complete footprint contains the timeout set"
      timerTickOnCoreCompleteLockSet_contains_timeout .lockSet,
    s5dt! "timerTickOnCoreCompleteLockSet_write_only: complete footprint is WRITE-only"
      timerTickOnCoreCompleteLockSet_write_only .lockSet,
    s5dt! "timerTickOnCoreCompleteLockSet_keys_nodup: complete footprint keys duplicate-free"
      timerTickOnCoreCompleteLockSet_keys_nodup .lockSet,
    s5dt! "timerTickOnCoreCompleteLockSet_pairwise_le: complete footprint SchedLockId-ascending"
      timerTickOnCoreCompleteLockSet_pairwise_le .lockSet,
    s5dt! "timerTickOnCoreCompleteLockSet_size_le_maxLockSetSize: complete footprint WCRT size bound"
      timerTickOnCoreCompleteLockSet_size_le_maxLockSetSize .lockSet,
    s5dt! "SchedLockId.object_lt_replenishQueue: SM5.D.3/§4.4 object lock before replenish-queue lock"
      SchedLockId.object_lt_replenishQueue .lockSet,
    s5dt! "SchedLockId.runQueue_lt_replenishQueue: SM5.D.3/§4.4 run-queue lock before replenish-queue lock"
      SchedLockId.runQueue_lt_replenishQueue .lockSet,
    -- ── .domain ──
    s5dt! "decrementDomainTimeOnCore_decrements: non-boundary domain-time decrement (pure, no rotation)"
      decrementDomainTimeOnCore_decrements .domain,
    s5dt! "decrementDomainTimeOnCore_activeDomainOnCore: the pure decrement never rotates the active domain"
      decrementDomainTimeOnCore_activeDomainOnCore .domain,
    s5dt! "decrementDomainTimeOnCore_domainTimeRemainingOnCore_ne: cross-core domain-time frame"
      decrementDomainTimeOnCore_domainTimeRemainingOnCore_ne .domain,
    s5dt! "decrementDomainTimeOnCore_preserves_domainTimeRemainingPositiveOnCore: B3 domain-time positivity preserved (under >1)"
      decrementDomainTimeOnCore_preserves_domainTimeRemainingPositiveOnCore .domain,
    s5dt! "switchDomainOnCore_singleDomain_noop: SM5.D.6 full domain switch no-op (empty schedule)"
      switchDomainOnCore_singleDomain_noop .domain,
    s5dt! "switchDomainOnCore_preserves_objects_invExt: SM5.D.6 domain switch preserves object-store invariant"
      switchDomainOnCore_preserves_objects_invExt .domain,
    s5dt! "switchDomainOnCore_sets_currentOnCore_none: SM5.D.6 domain switch clears current"
      switchDomainOnCore_sets_currentOnCore_none .domain,
    s5dt! "switchDomainOnCore_rotates: SM5.D.6 domain switch rotates the active domain"
      switchDomainOnCore_rotates .domain,
    s5dt! "scheduleDomainOnCore_decrements: SM5.D.6 sub-boundary domain re-dispatch decrements"
      scheduleDomainOnCore_decrements .domain,
    s5dt! "scheduleDomainOnCore_preserves_objects_invExt: SM5.D.6 domain re-dispatch preserves object-store invariant"
      scheduleDomainOnCore_preserves_objects_invExt .domain,
    -- ── .replenish ──
    s5dt! "refillSchedContext_preserves_objects_invExt: refill preserves object-store invariant"
      refillSchedContext_preserves_objects_invExt .replenish,
    s5dt! "enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed_anyCore: wake enqueue preserves run-queue well-formedness (any core)"
      enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed_anyCore .replenish,
    s5dt! "wakeThread_preserves_runQueueOnCore_wellFormed_anyCore: wake preserves run-queue well-formedness (any core)"
      wakeThread_preserves_runQueueOnCore_wellFormed_anyCore .replenish,
    s5dt! "processOneReplenishmentOnCore_preserves_objects_invExt: one replenishment preserves object-store invariant"
      processOneReplenishmentOnCore_preserves_objects_invExt .replenish,
    s5dt! "processOneReplenishmentOnCore_preserves_runQueueOnCore_wellFormed: one replenishment preserves run-queue well-formedness"
      processOneReplenishmentOnCore_preserves_runQueueOnCore_wellFormed .replenish,
    s5dt! "processReplenishmentsDueOnCore_preserves_objects_invExt: SM5.D.4 all-replenishments preserves object-store invariant"
      processReplenishmentsDueOnCore_preserves_objects_invExt .replenish,
    s5dt! "processReplenishmentsDueOnCore_preserves_runQueueOnCore_wellFormed: SM5.D.4 all-replenishments preserves run-queue well-formedness"
      processReplenishmentsDueOnCore_preserves_runQueueOnCore_wellFormed .replenish,
    s5dt! "processOneReplenishmentOnCore_no_sgi_if_no_target: no wake target emits no SGI"
      processOneReplenishmentOnCore_no_sgi_if_no_target .replenish,
    s5dt! "processOneReplenishmentOnCore_local_no_sgi: local wake emits no cross-core SGI"
      processOneReplenishmentOnCore_local_no_sgi .replenish,
    s5dt! "cbsReplenish_can_wake_remote_core: SM5.D.4 headline: cross-core CBS replenish wakes a remote core"
      cbsReplenish_can_wake_remote_core .replenish,
    -- ── .budget ──
    s5dt! "revertPriorityInheritance_preserves_objects_invExt: PIP revert preserves object-store invariant"
      revertPriorityInheritance_preserves_objects_invExt .budget,
    s5dt! "timeoutThread_preserves_objects_invExt: timeout-thread preserves object-store invariant"
      timeoutThread_preserves_objects_invExt .budget,
    s5dt! "timeoutBlockedThreads_preserves_objects_invExt: timeout-blocked-threads preserves object-store invariant"
      timeoutBlockedThreads_preserves_objects_invExt .budget,
    s5dt! "timerTickBudgetOnCore_preserves_objects_invExt: SM5.D.5 budget tick preserves object-store invariant"
      timerTickBudgetOnCore_preserves_objects_invExt .budget,
    s5dt! "timerTickBudgetOnCore_unbound_not_preempted: unbound running thread not preempted"
      timerTickBudgetOnCore_unbound_not_preempted .budget,
    s5dt! "timerTickBudgetOnCore_unbound_preempts: unbound expired thread preempted"
      timerTickBudgetOnCore_unbound_preempts .budget,
    s5dt! "timerTickBudgetOnCore_bound_preempts: bound budget-exhausted thread preempted"
      timerTickBudgetOnCore_bound_preempts .budget,
    s5dt! "timerTickBudgetOnCore_bound_not_preempted: bound budget-remaining thread not preempted"
      timerTickBudgetOnCore_bound_not_preempted .budget,
    s5dt! "timerTickBudgetOnCore_donated_preempts: donated budget-exhausted thread preempted"
      timerTickBudgetOnCore_donated_preempts .budget,
    s5dt! "saveOutgoingContextOnCore_preserves_objects_invExt: context save preserves object-store invariant"
      saveOutgoingContextOnCore_preserves_objects_invExt .budget,
    s5dt! "restoreIncomingContext_objects_eq: context restore is object-neutral"
      restoreIncomingContext_objects_eq .budget,
    s5dt! "scheduleEffectiveOnCore_preserves_objects_invExt: SM5.D.5 reschedule preserves object-store invariant"
      scheduleEffectiveOnCore_preserves_objects_invExt .budget,
    -- ── .tick ──
    s5dt! "timerTickOnCorePreDomain: SM5.D.2 pre-domain prepared state"
      timerTickOnCorePreDomain .tick,
    s5dt! "timerTickOnCorePrepared: SM5.D.2 prepared (post-replenish/post-domain) state"
      timerTickOnCorePrepared .tick,
    s5dt! "timerTickOnCorePrepared_fst_eq: prepared state is the domain-decrement of pre-domain"
      timerTickOnCorePrepared_fst_eq .tick,
    s5dt! "timerTickOnCore_eq_prepared: SM5.D.2 tick = budget dispatch on the prepared state"
      timerTickOnCore_eq_prepared .tick,
    s5dt! "timerTickOnCorePrepared_machine_eq: prepared state preserves the machine"
      timerTickOnCorePrepared_machine_eq .tick,
    s5dt! "timerTickOnCorePrepared_lastTimeoutErrors_eq: prepared state clears lastTimeoutErrors"
      timerTickOnCorePrepared_lastTimeoutErrors_eq .tick,
    s5dt! "timerTickOnCorePrepared_objects_invExt: prepared state preserves object-store invariant"
      timerTickOnCorePrepared_objects_invExt .tick,
    s5dt! "timerTickOnCore_idle: SM5.D.2 idle path is the prepared state"
      timerTickOnCore_idle .tick,
    s5dt! "timerTickOnCore_advances_per_core: SM5.D.2 headline: per-core advance, no global-timer advance"
      timerTickOnCore_advances_per_core .tick,
    s5dt! "timerTickOnCore_clears_lastTimeoutErrors: SM5.D.9 tick clears lastTimeoutErrors"
      timerTickOnCore_clears_lastTimeoutErrors .tick,
    s5dt! "timerTickOnCore_preempts_local: SM5.D.5 headline: budget exhaustion re-dispatches locally"
      timerTickOnCore_preempts_local .tick,
    s5dt! "timerTickOnCore_preserves_objects_invExt: SM5.D.2 tick preserves object-store invariant"
      timerTickOnCore_preserves_objects_invExt .tick,
    s5dt! "enqueueRunnableOnCore_lastTimeoutErrorsOnCore: wake enqueue frames lastTimeoutErrors"
      enqueueRunnableOnCore_lastTimeoutErrorsOnCore .tick,
    s5dt! "processOneReplenishmentOnCore_machine_eq: one replenishment frames the machine"
      processOneReplenishmentOnCore_machine_eq .tick,
    s5dt! "processOneReplenishmentOnCore_lastTimeoutErrorsOnCore_eq: one replenishment frames lastTimeoutErrors"
      processOneReplenishmentOnCore_lastTimeoutErrorsOnCore_eq .tick,
    s5dt! "processReplenishmentsDueOnCore_machine_eq: all-replenishments frames the machine"
      processReplenishmentsDueOnCore_machine_eq .tick,
    s5dt! "processReplenishmentsDueOnCore_lastTimeoutErrorsOnCore_eq: all-replenishments frames lastTimeoutErrors"
      processReplenishmentsDueOnCore_lastTimeoutErrorsOnCore_eq .tick,
    s5dt! "decrementDomainTimeOnCore_lastTimeoutErrorsOnCore: domain decrement frames lastTimeoutErrors"
      decrementDomainTimeOnCore_lastTimeoutErrorsOnCore .tick,
    -- ── .preservation ──
    s5dt! "decrementDomainTimeOnCore_preserves_currentThreadValidOnCore: B1: domain decrement preserves current-thread validity"
      decrementDomainTimeOnCore_preserves_currentThreadValidOnCore .preservation,
    s5dt! "decrementDomainTimeOnCore_preserves_queueCurrentConsistentOnCore: B1: domain decrement preserves dequeue-on-dispatch consistency"
      decrementDomainTimeOnCore_preserves_queueCurrentConsistentOnCore .preservation,
    s5dt! "decrementDomainTimeOnCore_preserves_runnableThreadsAreTCBsOnCore: B1: domain decrement preserves runnable-threads-are-TCBs"
      decrementDomainTimeOnCore_preserves_runnableThreadsAreTCBsOnCore .preservation,
    s5dt! "decrementDomainTimeOnCore_preserves_runQueueOnCoreWellFormed: B2: domain decrement preserves run-queue well-formedness"
      decrementDomainTimeOnCore_preserves_runQueueOnCoreWellFormed .preservation,
    s5dt! "saveOutgoingContextOnCore_scheduler_eq: context save frames the scheduler"
      saveOutgoingContextOnCore_scheduler_eq .preservation,
    s5dt! "saveOutgoingContextOnCore_getTcb?_isSome: context save preserves TCB-resolvability"
      saveOutgoingContextOnCore_getTcb?_isSome .preservation,
    s5dt! "scheduleEffectiveOnCore_objects_eq: reschedule object write is the context save"
      scheduleEffectiveOnCore_objects_eq .preservation,
    s5dt! "scheduleEffectiveOnCore_getTcb?_isSome: reschedule preserves TCB-resolvability"
      scheduleEffectiveOnCore_getTcb?_isSome .preservation,
    s5dt! "scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed: B2: reschedule preserves run-queue well-formedness"
      scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed .preservation,
    s5dt! "scheduleEffectiveOnCore_establishes_currentThreadValidOnCore: B1: reschedule establishes current-thread validity"
      scheduleEffectiveOnCore_establishes_currentThreadValidOnCore .preservation,
    s5dt! "scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore: B1: reschedule establishes dequeue-on-dispatch consistency"
      scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore .preservation,
    s5dt! "scheduleEffectiveOnCore_runQueue_toList_subset: reschedule post run queue is a subset of the pre run queue"
      scheduleEffectiveOnCore_runQueue_toList_subset .preservation,
    s5dt! "scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore: B1: reschedule preserves runnable-threads-are-TCBs"
      scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore .preservation,
    s5dt! "timerTickBudgetOnCore_notPreempted_scheduler_eq: not-preempted budget tick frames the scheduler"
      timerTickBudgetOnCore_notPreempted_scheduler_eq .preservation,
    s5dt! "timerTickBudgetOnCore_notPreempted_getTcb?_tid: not-preempted budget tick keeps the charged thread a TCB"
      timerTickBudgetOnCore_notPreempted_getTcb?_tid .preservation,
    s5dt! "timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCoreWellFormed: B2 discharge: not-preempted budget tick preserves run-queue well-formedness"
      timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCoreWellFormed .preservation,
    s5dt! "timerTickOnCore_preserves_currentThreadValidOnCore: B1 headline: the tick preserves current-thread validity (unconditional)"
      timerTickOnCore_preserves_currentThreadValidOnCore .preservation,
    s5dt! "timerTickOnCorePrepared_runQueueOnCore_wellFormed: B2: the prepared state preserves run-queue well-formedness"
      timerTickOnCorePrepared_runQueueOnCore_wellFormed .preservation,
    s5dt! "timerTickOnCore_preserves_runQueueOnCoreWellFormed: B2 headline: the tick preserves run-queue well-formedness (parameterized)"
      timerTickOnCore_preserves_runQueueOnCoreWellFormed .preservation,
    s5dt! "timerTickOnCore_preserves_queueCurrentConsistentOnCore: the tick preserves dequeue-on-dispatch consistency (parameterized)"
      timerTickOnCore_preserves_queueCurrentConsistentOnCore .preservation,
    s5dt! "saveOutgoingContextOnCore_getTcb?_domain: context save preserves a thread's domain"
      saveOutgoingContextOnCore_getTcb?_domain .preservation,
    s5dt! "scheduleEffectiveOnCore_getTcb?_domain: reschedule preserves a thread's domain"
      scheduleEffectiveOnCore_getTcb?_domain .preservation,
    s5dt! "scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore: reschedule dispatches in the active domain"
      scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore .preservation,
    s5dt! "timerTickBudgetOnCore_notPreempted_getTcb?_domain: not-preempted budget tick preserves the charged thread's domain"
      timerTickBudgetOnCore_notPreempted_getTcb?_domain .preservation,
    s5dt! "timerTickOnCore_preserves_currentThreadInActiveDomainOnCore: audit-pass-2 capstone — the tick keeps current in its active domain"
      timerTickOnCore_preserves_currentThreadInActiveDomainOnCore .preservation,
    -- ── .decidability ──
    s5dt! "timerTickOnCoreSucceeds: SM5.D.8 tick-succeeds decidable predicate"
      timerTickOnCoreSucceeds .decidability,
    s5dt! "timerTickOnCoreEmitsSgi: SM5.D.8 tick-emits-SGI decidable predicate"
      timerTickOnCoreEmitsSgi .decidability,
    s5dt! "timerTickBudgetOnCorePreempts: SM5.D.8 budget-preempts decidable predicate"
      timerTickBudgetOnCorePreempts .decidability,
    s5dt! "perCoreTimerTickEntry: SM5.D.1 C-callable per-core timer-entry seam"
      perCoreTimerTickEntry .decidability,
    s5dt! "perCoreTimerTickEntry_returns_unit_marker: SM5.D.1 entry-seam placeholder marker"
      perCoreTimerTickEntry_returns_unit_marker .decidability  ]

/-- WS-SM SM5.D: the inventory has 100 substantive entries (audit-pass-2: removed
5 obsolete in-tick domain-rotation theorems + the retired `timerTickOnCore_rotates_domain`;
added 2 pure-decrement frames + 5 `currentThreadInActiveDomain` preservation theorems).
A regression that adds a new SM5.D theorem without registering it fails this count
witness at the Tier-3 surface check. -/
theorem sm5DTheorems_count : sm5DTheorems.length = 100 := by decide

theorem sm5DTheorems_lockSet_count :
    (sm5DTheorems.filter (fun t => t.category == .lockSet)).length = 20 := by decide

theorem sm5DTheorems_domain_count :
    (sm5DTheorems.filter (fun t => t.category == .domain)).length = 10 := by decide

theorem sm5DTheorems_replenish_count :
    (sm5DTheorems.filter (fun t => t.category == .replenish)).length = 10 := by decide

theorem sm5DTheorems_budget_count :
    (sm5DTheorems.filter (fun t => t.category == .budget)).length = 12 := by decide

theorem sm5DTheorems_tick_count :
    (sm5DTheorems.filter (fun t => t.category == .tick)).length = 18 := by decide

theorem sm5DTheorems_preservation_count :
    (sm5DTheorems.filter (fun t => t.category == .preservation)).length = 25 := by decide

theorem sm5DTheorems_decidability_count :
    (sm5DTheorems.filter (fun t => t.category == .decidability)).length = 5 := by decide

/-- WS-SM SM5.D: per-category counts sum to the total. -/
theorem sm5DTheorems_partition_sum :
    (sm5DTheorems.filter (fun t => t.category == .lockSet)).length +
    (sm5DTheorems.filter (fun t => t.category == .domain)).length +
    (sm5DTheorems.filter (fun t => t.category == .replenish)).length +
    (sm5DTheorems.filter (fun t => t.category == .budget)).length +
    (sm5DTheorems.filter (fun t => t.category == .tick)).length +
    (sm5DTheorems.filter (fun t => t.category == .preservation)).length +
    (sm5DTheorems.filter (fun t => t.category == .decidability)).length =
    sm5DTheorems.length := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.D: every inventory identifier is unique.  Kernel-sound `decide`
(not `native_decide`): a duplicate identifier fails the build here (per the SM5.C
audit-pass-2 precedent that `native_decide` can mask a copy-paste duplicate). -/
theorem sm5DTheorems_identifiers_nodup :
    (sm5DTheorems.map (·.identifier)).Nodup := by decide

set_option maxRecDepth 10000 in
/-- WS-SM SM5.D: every inventory description is unique. -/
theorem sm5DTheorems_descriptions_nodup :
    (sm5DTheorems.map (·.description)).Nodup := by decide

end SeLe4n.Kernel
