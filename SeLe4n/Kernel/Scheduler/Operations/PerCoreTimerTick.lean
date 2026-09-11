-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Core
-- WS-RR RR7.11: `maxLockSetSize`, so the `_size_le_maxLockSetSize` theorems
-- below can state the bound their names claim rather than the numeral it holds.
import SeLe4n.Kernel.Concurrency.Locks.LockSet
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Preservation

/-!
# WS-SM SM5.D — Per-core timer tick (forward-looking theorems)

The per-core timer tick *transitions* (`timerTickOnCore`,
`processReplenishmentsDueOnCore`, `timerTickBudgetOnCore`,
`decrementDomainTimeOnCore`, `scheduleEffectiveOnCore`, `switchDomainOnCore`,
`scheduleDomainOnCore`) are production defs in
`Scheduler.Operations.Core` (the single-core timer home, where the CBS /
budget / domain machinery they compose lives).  This staged module carries the
SM5.D theorem surface that the runtime ISR (SM5.D.1) and SM5.I per-core
invariant suite will consume:

* **§1 — SM5.D.3** the cross-domain lock-set footprint (`timerTickOnCoreLockSet`
  over SM5.A's `SchedLockId` extended with the SM5.D.3 replenish-queue domain:
  object-store + run-queue + replenish-queue *write* locks, plan §3.4 / §4.4
  ascending order) + the WCRT-bounding size witness (SM5.D.7).
* **§2 — SM5.D.6** per-core non-boundary domain decrement: `decrementDomainTimeOnCore`
  (audit-pass-2: pure decrement, no rotation) + frame lemmas.  Domain *rotation* is
  the separate atomic `scheduleDomainOnCore` / `switchDomainOnCore` (§4b).
* **§3 — SM5.D.4** per-core CBS replenishment + cross-core wake:
  `processOneReplenishmentOnCore` / `processReplenishmentsDueOnCore` semantics +
  preservation + the headline `cbsReplenish_can_wake_remote_core`.
* **§4 — SM5.D.5** per-core budget tick: `timerTickBudgetOnCore` no-timer-advance
  / preemption / preservation + the headline `timerTickOnCore_preempts_local`.
* **§4b — SM5.D.6** full per-core domain re-dispatch: `switchDomainOnCore` /
  `scheduleDomainOnCore` no-op / decrement / rotation / current-clearing +
  objects-`invExt` preservation (the domain-boundary counterparts of §2).
* **§5 — SM5.D.2 / .9** `timerTickOnCore` semantics: idle case, the
  no-global-timer-advance SMP property, `lastTimeoutErrors` clearing (SM5.D.9),
  the headline `timerTickOnCore_advances_per_core`, and the foundation invariant
  preservation (objects `invExt`, run-queue `wellFormed`).
* **§6 — SM5.D.8** decidability witnesses for the SM5.D.10 unit tests.

`timerTickOnCore` is **not** fully per-core independent: its SM5.D.4 cross-core
replenish wake can — defensively, when a refilled SchedContext's bound thread has
migrated (`cpuAffinity` change, SM5.H.4 deferred) — enqueue onto and SGI a
*remote* core.  The independence proven here is therefore restricted to the
non-wake helpers (`decrementDomainTimeOnCore`, `timerTickBudgetOnCore`), which
are genuinely core-`c`-local; the cross-core reach is itself the SM5.D.4 headline
`cbsReplenish_can_wake_remote_core`.

Module reachability: staged via `Platform.Staged`; SM5.D.1's runtime ISR (the
`ffi_per_core_timer_tick` seam) and SM5.I's per-core invariant suite are the
first runtime exercisers.  Axiom-clean: every theorem depends only on the
standard foundational axioms (`propext` / `Quot.sound` / `Classical.choice`);
zero sorries.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId allCores SgiKind)

-- ============================================================================
-- §1  SM5.D.3 — Cross-domain lock-set footprint (+ SM5.D.7 WCRT size bound)
-- ============================================================================

/-- WS-SM SM5.D.3 (cross-domain, plan §3.4 / §4.4): the **static** timer-proper
lock-set footprint of `timerTickOnCore c`, over SM5.A's `SchedLockId` (extended at
SM5.D.3 with the replenish-queue domain).

The tick's *own* writes (the SM5.D.4 replenishment, SM5.D.6 domain accounting,
SM5.D.5 budget tick on its non-timeout branches, and the SM5.D.2 reschedule) touch
three lock domains on core `c`:
* the RobinHood **object store** (write): CBS refills + budget/time-slice writes +
  the context save/restore on preemption all `objects.insert`.  Per SM3.A.10 the
  store is guarded by the single table-level lock (`schedObjStoreLockId`), in
  **write** mode — which subsumes plan §3.4's "all TCB locks for threads whose
  SchedContext is bound to `c`" (the per-thread set), exactly the SM5.B/C
  table-lock rationale (RHTable structural safety is table-granularity);
* core `c`'s **run-queue** slot (write): re-enqueue on preemption + dispatch
  dequeue; and
* core `c`'s **replenish-queue** slot (write): `popDue` + the exhausted-budget
  replenishment insert.

So the static footprint is the three-lock set in plan §4.4 ascending order
(object < runQueue < replenishQueue):
`[(object schedObjStoreLockId, .write), (runQueue ⟨c⟩, .write), (replenishQueue ⟨c⟩, .write)]`.

**Dynamic wake extension (the honest footprint caveat).**  This static set is
**not** the *complete* footprint.  Two of the tick's arms wake a thread on the
**woken thread's own home core**, which the tick cannot name before it runs:
the SM5.D.4 replenishment drain (`processOneReplenishmentOnCore → wakeThread`,
placing via `determineTargetCore`) and the SM5.D.5 budget tick's
bound-budget-exhausted branch (`timeoutBlockedThreads → timeoutThread`, likewise
target-aware since PR #880 round 8).  Per plan §3.4 the timer lock-set is
"computed dynamically; lock-set may grow with the bound thread count": that
extension is declared explicitly as `timerTickOnCoreTimeoutDynamicLockSet`, and
the **complete** over-approximated footprint a bracket must acquire is
`timerTickOnCoreCompleteLockSet` (below).

**WS-RR RR7.39** widened both.  Until then the extension was the single
`runQueue ⟨bootCoreId⟩`, on the grounds that the timeout and PIP paths were
`bootCoreId`-pinned "pre-SM5.F" — true when it was written, false once SM5.F
landed and PR #880 rounds 7 and 8 made the wakes target-aware.  A footprint that
does not cover a write is a *false* footprint, so the extension is now **every**
core's run-queue write lock: sound unconditionally, still a function of the core
id alone, and `numCores + 2` locks against a `maxLockSetSize` of nine.

The cross-domain acquisition order is certified by `timerTickOnCoreLockSet_pairwise_le`
(static) / `timerTickOnCoreCompleteLockSet_pairwise_le` (complete); the runtime
acquisition is `SeLe4n/Kernel/SchedLockBracket.lean` (RR7.39). -/
def timerTickOnCoreLockSet (c : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.object schedObjStoreLockId, .write)
  , (SchedLockId.runQueue ⟨c⟩, .write)
  , (SchedLockId.replenishQueue ⟨c⟩, .write) ]

/-- SM5.D.3: the tick footprint is the three-lock object-store + run-queue +
replenish-queue set. -/
@[simp] theorem timerTickOnCoreLockSet_length (c : CoreId) :
    (timerTickOnCoreLockSet c).length = 3 := rfl

/-- SM5.D.3: every lock in the tick footprint is acquired in **write** mode — the
tick mutates all three domains. -/
theorem timerTickOnCoreLockSet_write_only (c : CoreId) :
    ∀ p ∈ timerTickOnCoreLockSet c, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [timerTickOnCoreLockSet, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h <;> subst h <;> rfl

/-- SM5.D.3: the object-store **write** lock is in the tick footprint (it guards
the CBS / budget / context-save object writes — and subsumes the dynamic per-TCB
lock set). -/
theorem timerTickOnCoreLockSet_contains_objStore_write (c : CoreId) :
    (SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.write)
      ∈ timerTickOnCoreLockSet c := by
  simp [timerTickOnCoreLockSet]

/-- SM5.D.3: core `c`'s run-queue **write** lock is in the tick footprint. -/
theorem timerTickOnCoreLockSet_contains_runQueue_write (c : CoreId) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ timerTickOnCoreLockSet c := by
  simp [timerTickOnCoreLockSet]

/-- SM5.D.3: core `c`'s replenish-queue **write** lock is in the tick footprint. -/
theorem timerTickOnCoreLockSet_contains_replenishQueue_write (c : CoreId) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ timerTickOnCoreLockSet c := by
  simp [timerTickOnCoreLockSet]

/-- SM5.D.3: the tick footprint's projected keys are duplicate-free (the three
locks are distinct constructors / distinct cores). -/
theorem timerTickOnCoreLockSet_keys_nodup (c : CoreId) :
    ((timerTickOnCoreLockSet c).map (·.1)).Nodup := by
  simp [timerTickOnCoreLockSet]

/-- SM5.D.3 (plan §4.4): the tick footprint's keys form a `SchedLockId`-ascending
acquisition sequence (`Pairwise (· ≤ ·)`) — object before run-queue before
replenish-queue — so the canonical `withLockSet` acquisition is the list itself
(the tick's contribution to the SM3.D deadlock-freedom ladder). -/
theorem timerTickOnCoreLockSet_pairwise_le (c : CoreId) :
    ((timerTickOnCoreLockSet c).map (·.1)).Pairwise (· ≤ ·) := by
  have hObjRq : SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.runQueue (⟨c⟩ : RunQueueLockId) :=
    (SchedLockId.object_lt_runQueue _ _).1
  have hObjRpq : SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.replenishQueue (⟨c⟩ : ReplenishQueueLockId) :=
    (SchedLockId.object_lt_replenishQueue _ _).1
  have hRqRpq : SchedLockId.runQueue (⟨c⟩ : RunQueueLockId)
      ≤ SchedLockId.replenishQueue (⟨c⟩ : ReplenishQueueLockId) :=
    (SchedLockId.runQueue_lt_replenishQueue _ _).1
  simp only [timerTickOnCoreLockSet, List.map_cons, List.map_nil]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hObjRq
    · rcases List.mem_singleton.mp ha' with rfl; exact hObjRpq
  · intro a ha
    rcases List.mem_singleton.mp ha with rfl; exact hRqRpq
  · intro a ha; simp at ha

-- SM5.D.7 (WCRT-bounded tick): the static lock-set has a fixed size of 3 (well
-- under the SM3.D `maxLockSetSize` cap), so the per-tick worst-case lock-wait
-- is bounded by `3 · (numCores − 1) · T_per_lock` (plan §3.9) — the tick fits the
-- WCRT budget.  The size pin (`_length` above) plus this bound are the SM5.D.7
-- surface; the full WCRT integration with SM3.D's `boundedWait_under_2pl` is
-- SM5.J.

/-- WS-SM SM5.D.7 (WCRT bound): the timer-tick lock-set size is within the SM3.D
`maxLockSetSize` cap, so a tick's worst-case response time is bounded by
`maxLockSetSize · (numCores − 1) · T_per_lock` (plan §3.9).  A surface witness
pinning the tick to the bounded-WCRT class.

**WS-RR RR7.11**: what fits the 1 ms tick budget is the tick's **own** footprint
— three locks, `3 · 3 · 60 µs = 540 µs` on the RPi5 figures — not the uniform
`maxLockSetSize` envelope, which is `2880 µs` at the WS-OD `v0.35.4` constant, was
`2520 µs` at OD3.13's, `2340 µs` at OD3.7's, `1980 µs` at OD3.5's, `1620 µs` at
RR7.11's and `1440 µs` before that.  The sentence here used to
attribute the fit to the envelope, which the arithmetic never supported at any
value of the constant; the envelope is a coarse upper bound over every declared
footprint, and the tick's is one of the smallest.  `SmpWcrtSuite` §3.2 pins both
figures, the envelope one *derived* from `maxLockSetSize` so it cannot go stale
the way this sentence twice has. -/
theorem timerTickOnCoreLockSet_size_le_maxLockSetSize (c : CoreId) :
    (timerTickOnCoreLockSet c).length ≤ Concurrency.maxLockSetSize := by
  rw [timerTickOnCoreLockSet_length]; decide

-- ── SM5.D.3 (honest-footprint completion): the dynamic IPC-timeout extension + the
--    complete over-approximated lock-set ──

/-- **WS-RR RR7.39**: every core's run-queue **write** lock, in `CoreId`-ascending
order — the segment a transition declares when it can enqueue on a core it
cannot name before it runs.

`allCores` is `List.finRange numCores`, so the segment is already sorted and
duplicate-free, and its length is exactly `numCores`. -/
def allCoreRunQueueLockSegment : List (SchedLockId × Concurrency.AccessMode) :=
  allCores.map (fun d => (SchedLockId.runQueue ⟨d⟩, .write))

/-- **WS-RR RR7.39**: the segment's length is the core count. -/
@[simp] theorem allCoreRunQueueLockSegment_length :
    allCoreRunQueueLockSegment.length = numCores := by
  simp [allCoreRunQueueLockSegment, Concurrency.allCores_length]

/-- **WS-RR RR7.39**: every core's run-queue write lock is in the segment. -/
theorem mem_allCoreRunQueueLockSegment (d : CoreId) :
    (SchedLockId.runQueue ⟨d⟩, Concurrency.AccessMode.write)
      ∈ allCoreRunQueueLockSegment :=
  List.mem_map.mpr ⟨d, Concurrency.mem_allCores d, rfl⟩

/-- **WS-RR RR7.39**: the segment is write-only. -/
theorem allCoreRunQueueLockSegment_write_only :
    ∀ p ∈ allCoreRunQueueLockSegment, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
  rfl

/-- **WS-RR RR7.39**: the segment names run-queue locks and nothing else — the
fact that separates it from the object and replenish keys in the nodup and
ordering proofs below. -/
theorem allCoreRunQueueLockSegment_keys_runQueue {k : SchedLockId}
    (hk : k ∈ allCoreRunQueueLockSegment.map (·.1)) :
    ∃ d : CoreId, k = SchedLockId.runQueue ⟨d⟩ := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hp
  exact ⟨d, rfl⟩

/-- **WS-RR RR7.39**: the segment's keys are `CoreId`-ascending — `allCores` is
`List.finRange numCores`, so the run-queue segment *is* its own acquisition
sequence.  Closed (no free variables), hence decidable at `numCores`. -/
theorem allCoreRunQueueLockSegment_pairwise_le :
    (allCoreRunQueueLockSegment.map (·.1)).Pairwise (· ≤ ·) := by
  unfold allCoreRunQueueLockSegment allCores
  simp only [List.map_map]
  decide

/-- **WS-RR RR7.39 (the target-aware timeout / replenish footprint)**: the
**additional** run-queue write locks the SM5.D.5 budget tick and the SM5.D.4
replenishment drain take beyond the static `timerTickOnCoreLockSet` — **every**
core's.

## Why every core, and not the boot core

Until WS-RR RR7.39 this set was the single `runQueue ⟨bootCoreId⟩`, on the stated
grounds that `timeoutThread`'s re-enqueue and `revertPriorityInheritance`'s
`updatePipBoost` were "`bootCoreId`-pinned pre-SM5.F".  SM5.F landed and PR #880
rounds 7 and 8 made both wake paths **target-aware**: the replenish drain's
`processOneReplenishmentOnCore` calls `wakeThread`, which enqueues on
`determineTargetCore` — the woken thread's `cpuAffinity`, hence an arbitrary core
— and the bound-exhausted arm's `timeoutThread` does the same, its own comment
saying in as many words "not the boot queue".  The declaration was not updated
with the code, so a tick on core `c` could write `runQueue ⟨d⟩` for a `d` the
footprint did not name.

That is a **false footprint**, the one shape this family must not take: a
declared lock set that does not cover a write leaves the 2PL argument resting on
exclusion the runtime never established.  It was not a live defect — nothing
acquired these footprints until RR7.39 gave the domain a runtime, and the SM5.I
global kernel-entry lock serialises every commit — but RR7.39 *is* the cut that
starts acquiring them, so it is fixed here rather than inherited.

## Why over-approximate rather than resolve the targets

The wake targets are, in principle, resolvable from the pre-state: the due
SchedContexts come off `replenishQueueOnCore c`, and each one's target is
`determineTargetCore` of its bound thread.  Naming exactly those cores would be a
tighter footprint — and a *state-dependent* one, resolved by reads of the object
store taken **before** the object-store lock is held, so its revalidation would
become load-bearing on a path where it is currently trivial.

The reason to take the wider set anyway is not that over-declaring is merely
*safe* (it is — `preservesFieldsOutside_mono`, the RR7.19 rule).  It is that here
it is **free**: every tick footprint contains the object-store *table* write
lock, which is one word shared by every core, so any two ticks already exclude
each other whatever their run-queue segments say.  Widening that segment from two
locks to `numCores` therefore costs no achievable concurrency at all —
`timerTickOnCoreCompleteLockSet_serialises_pairwise` is that statement, machine
checked, so the trade-off is not a claim in a comment.  What it costs is one
`maxLockSetSize` slot (six of nine, from four), and `maxLockSetSize` itself does
not move, so no other syscall's admissible critical section changes.

A target-resolving footprint would buy back nothing until the object store is
locked at finer than table granularity, which is the SM3.A.10 representation
cut.  It is an optimisation to make *there*, not the correctness fix to make
here. -/
def timerTickOnCoreTimeoutDynamicLockSet :
    List (SchedLockId × Concurrency.AccessMode) :=
  allCoreRunQueueLockSegment

/-- **WS-RR RR7.39**: the dynamic timeout extension is every core's run-queue
write lock.  (Before RR7.39 this said `[(runQueue ⟨bootCoreId⟩, .write)]`, which
the target-aware wakes had made false.) -/
theorem timerTickOnCoreTimeoutDynamicLockSet_eq :
    timerTickOnCoreTimeoutDynamicLockSet = allCoreRunQueueLockSegment := rfl

/-- SM5.D.3: the dynamic timeout extension is write-only. -/
theorem timerTickOnCoreTimeoutDynamicLockSet_write_only :
    ∀ p ∈ timerTickOnCoreTimeoutDynamicLockSet, p.2 = Concurrency.AccessMode.write :=
  allCoreRunQueueLockSegment_write_only

/-- **WS-RR RR7.39**: the timeout extension covers the wake target of *any*
thread — the statement the pre-RR7.39 single-boot-core set could not make, and
the one the tick's target-aware wakes need. -/
theorem timerTickOnCoreTimeoutDynamicLockSet_covers_any_target (d : CoreId) :
    (SchedLockId.runQueue ⟨d⟩, Concurrency.AccessMode.write)
      ∈ timerTickOnCoreTimeoutDynamicLockSet :=
  mem_allCoreRunQueueLockSegment d

/-- WS-SM SM5.D.3 (the **complete** over-approximated footprint): the full set of
locks a bracket must acquire for `timerTickOnCore c` — the object-store table
write lock, **every** core's run-queue write lock (RR7.39: the tick's wakes are
target-aware, see `timerTickOnCoreTimeoutDynamicLockSet`), and core `c`'s
replenish-queue write lock.

Ordered ascending in the SM5.A.2 ladder — object < runQueue (`CoreId`-ascending,
since `allCores` is `List.finRange numCores`) < replenishQueue — so the declared
list *is* the acquisition sequence the deadlock-freedom argument walks.

The replenish segment is core `c`'s alone, and that is exact rather than an
over-approximation: the only replenish-queue writers the tick reaches are
`processReplenishmentsDueOnCore` (which pops core `c`'s queue) and
`replenishOnCore st c` (which inserts into it).  A wake moves a thread between
*run* queues; it does not move a replenishment. -/
def timerTickOnCoreCompleteLockSet (c : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  (SchedLockId.object schedObjStoreLockId, .write) ::
    (allCoreRunQueueLockSegment ++ [(SchedLockId.replenishQueue ⟨c⟩, .write)])

/-- SM5.D.3: the complete footprint contains the static timer-proper footprint. -/
theorem timerTickOnCoreCompleteLockSet_contains_static (c : CoreId) :
    ∀ p ∈ timerTickOnCoreLockSet c, p ∈ timerTickOnCoreCompleteLockSet c := by
  intro p hp
  simp only [timerTickOnCoreLockSet, List.mem_cons, List.not_mem_nil, or_false] at hp
  unfold timerTickOnCoreCompleteLockSet
  rcases hp with rfl | rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ (mem_allCoreRunQueueLockSegment c))
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

/-- SM5.D.3: the complete footprint contains the dynamic timeout extension — now
every core's run-queue write lock, not just the boot core's. -/
theorem timerTickOnCoreCompleteLockSet_contains_timeout (c : CoreId) :
    ∀ p ∈ timerTickOnCoreTimeoutDynamicLockSet, p ∈ timerTickOnCoreCompleteLockSet c := by
  intro p hp
  exact List.mem_cons_of_mem _ (List.mem_append_left _ hp)

/-- **WS-RR RR7.39 (the widening is free)**: any two cores' complete tick
footprints already share the object-store **table** write lock.

`schedObjStoreLockId` names `SystemState.objStoreLock` — a single word, not a
per-core one — so two ticks on distinct cores exclude each other on it whatever
their run-queue segments contain.  That is why widening the run-queue segment
from two locks to every core (see `timerTickOnCoreTimeoutDynamicLockSet`) costs
no achievable concurrency: the ticks were already fully serialised against one
another, and the correction only stops the footprint from *lying* about which
queues the tick writes.

Stated as a theorem rather than argued in a comment, because the argument is the
whole justification for preferring the sound over-approximation to a tighter
state-dependent one, and a comment cannot be checked. -/
theorem timerTickOnCoreCompleteLockSet_serialises_pairwise (c d : CoreId) :
    ∃ p, p ∈ timerTickOnCoreCompleteLockSet c ∧ p ∈ timerTickOnCoreCompleteLockSet d ∧
      p.2 = Concurrency.AccessMode.write :=
  ⟨(SchedLockId.object schedObjStoreLockId, .write),
    List.mem_cons_self, List.mem_cons_self, rfl⟩

/-- SM5.D.3: every lock in the complete footprint is acquired in **write** mode. -/
theorem timerTickOnCoreCompleteLockSet_write_only (c : CoreId) :
    ∀ p ∈ timerTickOnCoreCompleteLockSet c, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  unfold timerTickOnCoreCompleteLockSet at hp
  rcases List.mem_cons.mp hp with rfl | hp'
  · rfl
  rcases List.mem_append.mp hp' with hSeg | hRep
  · exact allCoreRunQueueLockSegment_write_only p hSeg
  · rw [List.mem_singleton.mp hRep]

/-- SM5.D.3 (plan §4.4): the complete footprint's keys are duplicate-free — the
object key is not a run-queue or replenish key, `allCores` has no repeats, and
the replenish key is in neither of the other two families. -/
theorem timerTickOnCoreCompleteLockSet_keys_nodup (c : CoreId) :
    ((timerTickOnCoreCompleteLockSet c).map (·.1)).Nodup := by
  unfold timerTickOnCoreCompleteLockSet
  simp only [List.map_cons, List.map_append, List.map_cons, List.map_nil]
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · intro hmem
    rcases List.mem_append.mp hmem with hSeg | hRep
    · obtain ⟨_, hEq⟩ := allCoreRunQueueLockSegment_keys_runQueue hSeg
      exact absurd hEq (by simp)
    · exact absurd (List.mem_singleton.mp hRep) (by simp)
  · refine List.nodup_append.2 ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · -- the segment's keys are `allCores` under an injective map
      have hInj : Function.Injective (fun d : CoreId => SchedLockId.runQueue ⟨d⟩) := by
        intro a b hab
        exact congrArg RunQueueLockId.core (SchedLockId.runQueue.inj hab)
      have hKeys : allCoreRunQueueLockSegment.map (·.1)
          = allCores.map (fun d : CoreId => SchedLockId.runQueue ⟨d⟩) := by
        simp [allCoreRunQueueLockSegment, List.map_map, Function.comp]
      rw [hKeys]
      exact List.Pairwise.map _ (fun _ _ h he => h (hInj he)) Concurrency.allCores_nodup
    · intro a ha b hb
      obtain ⟨_, rfl⟩ := allCoreRunQueueLockSegment_keys_runQueue ha
      rw [List.mem_singleton.mp hb]
      simp

/-- SM5.D.3 (plan §4.4): the complete footprint's keys form a
`SchedLockId`-ascending acquisition sequence — object < every run queue (in
`CoreId`-ascending order) < replenishQueue ⟨c⟩ — the tick's contribution to the
SM3.D deadlock-freedom ladder. -/
theorem timerTickOnCoreCompleteLockSet_pairwise_le (c : CoreId) :
    ((timerTickOnCoreCompleteLockSet c).map (·.1)).Pairwise (· ≤ ·) := by
  unfold timerTickOnCoreCompleteLockSet
  simp only [List.map_cons, List.map_append, List.map_cons, List.map_nil]
  refine List.Pairwise.cons ?_ (List.pairwise_append.2
    ⟨allCoreRunQueueLockSegment_pairwise_le, List.pairwise_singleton _ _, ?_⟩)
  · intro a ha
    rcases List.mem_append.mp ha with hSeg | hRep
    · obtain ⟨_, rfl⟩ := allCoreRunQueueLockSegment_keys_runQueue hSeg
      exact (SchedLockId.object_lt_runQueue _ _).1
    · rw [List.mem_singleton.mp hRep]
      exact (SchedLockId.object_lt_replenishQueue _ _).1
  · intro a ha b hb
    obtain ⟨_, rfl⟩ := allCoreRunQueueLockSegment_keys_runQueue ha
    rw [List.mem_singleton.mp hb]
    exact (SchedLockId.runQueue_lt_replenishQueue _ _).1

/-- WS-SM SM5.D.7 (WCRT bound, complete footprint): the complete
over-approximated footprint — object + `numCores` run queues + one replenish
queue — is within the SM3.D `maxLockSetSize` cap, so the tick's worst-case
response time is bounded by `maxLockSetSize · (numCores − 1) · tCs` (plan §3.9).

RR7.39 widened the run-queue segment from at most two locks to all `numCores`;
at `numCores = 4` that is six locks against a cap of nine.  Stated against the
constant, never a numeral, per the `_size_le_maxLockSetSize` convention. -/
theorem timerTickOnCoreCompleteLockSet_size_le_maxLockSetSize (c : CoreId) :
    (timerTickOnCoreCompleteLockSet c).length
      ≤ Concurrency.maxLockSetSize := by
  unfold timerTickOnCoreCompleteLockSet
  simp only [List.length_cons, List.length_append,
    allCoreRunQueueLockSegment_length]
  decide

-- ============================================================================
-- §2  SM5.D.6 — Per-core non-boundary domain decrement (`decrementDomainTimeOnCore`)
--
--   Audit-pass-2: `decrementDomainTimeOnCore` is now a **pure** domain-time
--   decrement (it writes only core `c`'s `domainTimeRemainingOnCore` slot, never
--   the active domain) — the `else`-branch helper of `scheduleDomainOnCore`.
--   Domain *rotation* + re-dispatch is `switchDomainOnCore` / `scheduleDomainOnCore`
--   (§4b), kept atomic.  The timer tick does NOT call this (domain accounting is
--   the separate `scheduleDomainOnCore`), so the tick can never leave a running
--   thread outside its domain — the `currentThreadInActiveDomain` faithfulness fix.
-- ============================================================================

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` never touches the object store. -/
@[simp] theorem decrementDomainTimeOnCore_objects_eq (st : SystemState) (c : CoreId) :
    (decrementDomainTimeOnCore st c).objects = st.objects := rfl

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` never touches the machine state
(reads but does not advance the global timer). -/
@[simp] theorem decrementDomainTimeOnCore_machine_eq (st : SystemState) (c : CoreId) :
    (decrementDomainTimeOnCore st c).machine = st.machine := rfl

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` leaves every core's run queue
unchanged — it writes only the domain-time slot. -/
@[simp] theorem decrementDomainTimeOnCore_runQueueOnCore (st : SystemState) (c c' : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  simp [decrementDomainTimeOnCore]

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` leaves every core's current thread
unchanged. -/
@[simp] theorem decrementDomainTimeOnCore_currentOnCore (st : SystemState) (c c' : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  simp [decrementDomainTimeOnCore]

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` leaves every core's replenish queue
unchanged. -/
@[simp] theorem decrementDomainTimeOnCore_replenishQueueOnCore (st : SystemState) (c c' : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  simp [decrementDomainTimeOnCore]

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` leaves **every** core's active
domain unchanged — the pure decrement never rotates (rotation is
`scheduleDomainOnCore`'s atomic boundary branch). -/
@[simp] theorem decrementDomainTimeOnCore_activeDomainOnCore (st : SystemState) (c c' : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' := by
  simp [decrementDomainTimeOnCore, SchedulerState.setDomainTimeRemainingOnCore_activeDomainOnCore]

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` decrements core `c`'s domain time by
one (unconditionally — the pure non-boundary accounting advance; `scheduleDomainOnCore`
invokes it only when `domainTimeRemainingOnCore c > 1`, so the result stays `≥ 1`). -/
theorem decrementDomainTimeOnCore_decrements (st : SystemState) (c : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.domainTimeRemainingOnCore c
      = st.scheduler.domainTimeRemainingOnCore c - 1 := by
  simp [decrementDomainTimeOnCore, SchedulerState.setDomainTimeRemainingOnCore_domainTimeRemainingOnCore_self]

/-- WS-SM SM5.D.6 (per-core independence): for a sibling core `c' ≠ c`,
`decrementDomainTimeOnCore st c` leaves core `c'`'s domain-time slot unchanged. -/
theorem decrementDomainTimeOnCore_domainTimeRemainingOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (decrementDomainTimeOnCore st c).scheduler.domainTimeRemainingOnCore c'
      = st.scheduler.domainTimeRemainingOnCore c' := by
  simp [decrementDomainTimeOnCore,
    SchedulerState.setDomainTimeRemainingOnCore_domainTimeRemainingOnCore_ne _ c c' _ h]

/-- WS-SM SM5.D.6 / B3 (preservation): `decrementDomainTimeOnCore` preserves
`domainTimeRemainingPositiveOnCore` when core `c`'s domain has more than one tick
left (`domainTimeRemainingOnCore c > 1`) — the decrement leaves `old − 1 ≥ 1 > 0`.
`scheduleDomainOnCore` invokes it exactly under that guard, so the per-core domain
timer is never zeroed by the non-boundary path (rotation resets it to a positive
entry length). -/
theorem decrementDomainTimeOnCore_preserves_domainTimeRemainingPositiveOnCore
    (st : SystemState) (c : CoreId)
    (h : 1 < st.scheduler.domainTimeRemainingOnCore c) :
    domainTimeRemainingPositiveOnCore (decrementDomainTimeOnCore st c) c := by
  unfold domainTimeRemainingPositiveOnCore
  rw [decrementDomainTimeOnCore_decrements]
  omega

-- ============================================================================
-- §3  SM5.D.4 — Per-core CBS replenishment + cross-core wake
-- ============================================================================

/-- WS-SM SM5.D.4 (preservation): `refillSchedContext` preserves the RobinHood
object-store invariant — its only write is the refilled SchedContext `insert` (an
existing key), which preserves `invExt`; the non-SchedContext branch is the
identity. -/
theorem refillSchedContext_preserves_objects_invExt (st : SystemState)
    (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt) :
    (refillSchedContext st scId now).objects.invExt := by
  unfold refillSchedContext
  split <;>
    first
      | exact RHTable_insert_preserves_invExt st.objects _ _ hInv
      | exact hInv

/-- WS-SM SM5.D.4 (preservation helper, general core form): `enqueueRunnableOnCore`
preserves run-queue well-formedness on **every** core `c'` — on the enqueued core
`c` via `RunQueue.insert`, on a sibling core via the run-queue frame
(`_runQueueOnCore_ne`). -/
theorem enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed_anyCore (st : SystemState)
    (c c' : CoreId) (tid : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c').wellFormed) :
    ((enqueueRunnableOnCore st c tid).scheduler.runQueueOnCore c').wellFormed := by
  by_cases h : c = c'
  · subst h; exact enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed st c tid hwf
  · rw [enqueueRunnableOnCore_runQueueOnCore_ne st c c' tid h]; exact hwf

/-- WS-SM SM5.D.4 (preservation helper): `wakeThread` preserves run-queue
well-formedness on **every** core `c'` (the wake's state effect is an
`enqueueRunnableOnCore` to the target core). -/
theorem wakeThread_preserves_runQueueOnCore_wellFormed_anyCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore c' : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c').wellFormed) :
    ((wakeThread st tid executingCore).1.scheduler.runQueueOnCore c').wellFormed := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed_anyCore st
    (determineTargetCore st tid) c' tid hwf

/-- WS-SM SM5.D.4 (preservation): `processOneReplenishmentOnCore` preserves the
object-store invariant — the state is either the refilled state (refill preserves
`invExt`) or a wake on top of it (`wakeThread` preserves `invExt`). -/
theorem processOneReplenishmentOnCore_preserves_objects_invExt (st : SystemState)
    (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hInv : st.objects.invExt) :
    (processOneReplenishmentOnCore st execCore scId now).1.objects.invExt := by
  have hRef : (refillSchedContext st scId now).objects.invExt :=
    refillSchedContext_preserves_objects_invExt st scId now hInv
  simp only [processOneReplenishmentOnCore]
  split
  · -- replenishWakeTarget = some tid
    split
    · exact hRef                                          -- already running on target: refilled
    · exact wakeThread_preserves_objects_invExt _ _ execCore hRef  -- wakeThread refilled tid
  · exact hRef                                            -- no wake target: refilled

/-- WS-SM SM5.D.4 (preservation): `processOneReplenishmentOnCore` preserves
run-queue well-formedness on **every** core `c'` (refill never touches a run
queue; the wake preserves every core's run-queue well-formedness). -/
theorem processOneReplenishmentOnCore_preserves_runQueueOnCore_wellFormed (st : SystemState)
    (execCore c' : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hwf : (st.scheduler.runQueueOnCore c').wellFormed) :
    ((processOneReplenishmentOnCore st execCore scId now).1.scheduler.runQueueOnCore c').wellFormed := by
  -- `refillSchedContext` writes only the object store, so it preserves every
  -- core's run queue verbatim.
  have hRefRq : (refillSchedContext st scId now).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
    unfold refillSchedContext; split <;> rfl
  have hRef : ((refillSchedContext st scId now).scheduler.runQueueOnCore c').wellFormed := by
    rw [hRefRq]; exact hwf
  simp only [processOneReplenishmentOnCore]
  split
  · split
    · exact hRef
    · exact wakeThread_preserves_runQueueOnCore_wellFormed_anyCore _ _ execCore c' hRef
  · exact hRef

/-- WS-SM SM5.D.4 (fold preservation helper): the replenishment fold preserves the
object-store invariant — each `processOneReplenishmentOnCore` step does, so the
`List.foldl` does. -/
private theorem foldl_processOneReplenishment_preserves_objects_invExt
    (dueIds : List SeLe4n.SchedContextId) (c : CoreId) (now : Nat)
    (acc : SystemState × List (CoreId × SgiKind) × Bool) (hInv : acc.1.objects.invExt) :
    (dueIds.foldl (fun acc scId =>
        let r := processOneReplenishmentOnCore acc.1 c scId now
        (r.1, acc.2.1 ++ r.2.1.toList, acc.2.2 || r.2.2)) acc).1.objects.invExt := by
  induction dueIds generalizing acc with
  | nil => exact hInv
  | cons hd tl ih =>
      rw [List.foldl_cons]
      exact ih _ (processOneReplenishmentOnCore_preserves_objects_invExt acc.1 c hd now hInv)

/-- WS-SM SM5.D.4 (fold preservation helper): the replenishment fold preserves
run-queue well-formedness on **every** core `c'`. -/
private theorem foldl_processOneReplenishment_preserves_runQueueOnCore_wellFormed
    (dueIds : List SeLe4n.SchedContextId) (c c' : CoreId) (now : Nat)
    (acc : SystemState × List (CoreId × SgiKind) × Bool)
    (hwf : (acc.1.scheduler.runQueueOnCore c').wellFormed) :
    ((dueIds.foldl (fun acc scId =>
        let r := processOneReplenishmentOnCore acc.1 c scId now
        (r.1, acc.2.1 ++ r.2.1.toList, acc.2.2 || r.2.2)) acc).1.scheduler.runQueueOnCore c').wellFormed := by
  induction dueIds generalizing acc with
  | nil => exact hwf
  | cons hd tl ih =>
      rw [List.foldl_cons]
      exact ih _ (processOneReplenishmentOnCore_preserves_runQueueOnCore_wellFormed acc.1 c c' hd now hwf)

/-- WS-SM SM5.D.4 (preservation): `processReplenishmentsDueOnCore` preserves the
object-store invariant — the `popDue` writes only the replenish-queue slot
(objects unchanged), and the fold preserves `invExt`. -/
theorem processReplenishmentsDueOnCore_preserves_objects_invExt (st : SystemState)
    (c : CoreId) (now : Nat) (hInv : st.objects.invExt) :
    (processReplenishmentsDueOnCore st c now).1.objects.invExt := by
  simp only [processReplenishmentsDueOnCore]
  exact foldl_processOneReplenishment_preserves_objects_invExt _ c now _ hInv

/-- WS-SM SM5.D.4 (preservation): `processReplenishmentsDueOnCore` preserves
run-queue well-formedness on **every** core `c'`. -/
theorem processReplenishmentsDueOnCore_preserves_runQueueOnCore_wellFormed (st : SystemState)
    (c c' : CoreId) (now : Nat)
    (hwf : (st.scheduler.runQueueOnCore c').wellFormed) :
    ((processReplenishmentsDueOnCore st c now).1.scheduler.runQueueOnCore c').wellFormed := by
  simp only [processReplenishmentsDueOnCore]
  apply foldl_processOneReplenishment_preserves_runQueueOnCore_wellFormed _ c c' now
  -- the initial accumulator is `({st with scheduler := setReplenishQueueOnCore c _}, [])`;
  -- the replenish-queue write frames every core's run queue.
  simpa using hwf

/-- WS-SM SM5.D.4: no wake target ⇒ no cross-core SGI (a replenishment that does
not transition a thread to runnable pokes no core). -/
theorem processOneReplenishmentOnCore_no_sgi_if_no_target (st : SystemState)
    (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hNone : replenishWakeTarget st (refillSchedContext st scId now) scId = none) :
    (processOneReplenishmentOnCore st execCore scId now).2.1 = none := by
  simp only [processOneReplenishmentOnCore, hNone]

/-- WS-SM SM5.D.4: a wake whose target is the executing core itself emits no SGI
(local enqueue; since PR #880 round 7 the step instead raises the **local-wake
bit** — see `processOneReplenishmentOnCore_local_wake_bit` — which
`timerTickOnCore` resolves with the receiver-side reschedule decision after the
budget charge). -/
theorem processOneReplenishmentOnCore_local_no_sgi (st : SystemState)
    (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat) (tid : SeLe4n.ThreadId)
    (hTarget : replenishWakeTarget st (refillSchedContext st scId now) scId = some tid)
    (hLocal : determineTargetCore (refillSchedContext st scId now) tid = execCore) :
    (processOneReplenishmentOnCore st execCore scId now).2.1 = none := by
  simp only [processOneReplenishmentOnCore, hTarget]
  split
  · rfl
  · exact wakeThread_no_sgi_if_local (refillSchedContext st scId now) tid execCore hLocal

/-- WS-SM (PR #880 round 7): the local-wake **bit** fires exactly where the SGI
does not — a wake that resolves to a TCB and targets the executing core itself
raises the step's third component, making the otherwise-invisible local wake
(placement possibly suppressed by the single-placement guard, no SGI by
`processOneReplenishmentOnCore_local_no_sgi`) visible to `timerTickOnCore`'s
local reschedule decision. -/
theorem processOneReplenishmentOnCore_local_wake_bit (st : SystemState)
    (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTarget : replenishWakeTarget st (refillSchedContext st scId now) scId = some tid)
    (hNotRunning : runningOnSomeCore (refillSchedContext st scId now) tid = false)
    (hTcb : (refillSchedContext st scId now).getTcb? tid = some tcb)
    (hLocal : determineTargetCore (refillSchedContext st scId now) tid = execCore) :
    (processOneReplenishmentOnCore st execCore scId now).2.2 = true := by
  simp only [processOneReplenishmentOnCore, hTarget, hNotRunning, Bool.false_eq_true, if_false]
  simp [hTcb, hLocal]

/-- WS-SM (PR #880 round 7): no wake target ⇒ the local-wake bit stays down (a
refill that transitions no thread to runnable triggers no local reschedule
decision — the quiet tick keeps its cost profile). -/
theorem processOneReplenishmentOnCore_no_target_no_bit (st : SystemState)
    (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hNone : replenishWakeTarget st (refillSchedContext st scId now) scId = none) :
    (processOneReplenishmentOnCore st execCore scId now).2.2 = false := by
  simp only [processOneReplenishmentOnCore, hNone]

/-- WS-SM SM5.D.4 (the headline cross-core wake, plan §6.1
`cbsReplenish_can_wake_remote_core`): when a CBS replenishment transitions a
SchedContext's bound thread `tid` to runnable, `tid` resolves to a TCB, its target
core is **remote** (`≠ execCore`), and it is not already running there, the
replenishment emits a cross-core `.reschedule` SGI to `tid`'s target core.

This is the SM5.D.4 deliverable: a per-core timer tick on `execCore` can wake — and
poke via SGI — a thread that belongs to a *different* core, the defensive
migration path (`schedContextRunQueueConsistent_perCore` makes the target local in
the well-formed case, but a post-affinity-change thread targets a remote core and
the wake correctly fires the SGI). -/
theorem cbsReplenish_can_wake_remote_core (st : SystemState) (execCore : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTarget : replenishWakeTarget st (refillSchedContext st scId now) scId = some tid)
    (hTcb : (refillSchedContext st scId now).getTcb? tid = some tcb)
    (hNotRunning : runningOnSomeCore (refillSchedContext st scId now) tid = false)
    (hRemote : determineTargetCore (refillSchedContext st scId now) tid ≠ execCore) :
    (processOneReplenishmentOnCore st execCore scId now).2.1
      = some (determineTargetCore (refillSchedContext st scId now) tid, SgiKind.reschedule) := by
  -- Audit-pass-2 / Codex-P2: the wake fires only when `tid` is not running on ANY
  -- core (the strengthened guard), so a thread current on a different core than its
  -- target is never double-placed.
  simp only [processOneReplenishmentOnCore, hTarget, hNotRunning, Bool.false_eq_true, if_false]
  exact wakeThread_emits_sgi_if_remote (refillSchedContext st scId now) tid execCore tcb hTcb hRemote

-- ============================================================================
-- §4  SM5.D.5 — Per-core budget tick (+ the IPC-timeout objects preservation
--      chain) + the headline `timerTickOnCore_preempts_local`
-- ============================================================================
--
-- `timerTickBudgetOnCore`'s bound-budget-exhausted branch invokes the
-- cross-subsystem `timeoutBlockedThreads` (IPC endpoint dequeue + PIP reversion).
-- To prove the per-core tick preserves the RobinHood object-store invariant
-- (`objects.invExt` — the security-critical structural invariant SM5.B/C also
-- proved), this section first establishes the (reusable, previously-missing)
-- preservation lemmas for that IPC-timeout chain: `revertPriorityInheritance` →
-- `timeoutThread` → `timeoutBlockedThreads`.  Each step's only object writes are
-- `RHTable.insert`s (TCB / endpoint / SchedContext), all `invExt`-preserving.
--
-- ────────────────────────────────────────────────────────────────────────
-- TRACKED DEBT (closure target: SM5.F per-core PIP migration).  The
-- bound-budget-exhausted branch of `timerTickBudgetOnCore` invokes
-- `timeoutBlockedThreads`, whose re-enqueue path routes through the still
-- bootCoreId-pinned `ensureRunnable`.  Two facets of that pinning are open;
-- NEITHER affects the object-store `invExt` invariant proven in this section
-- (the writes are `invExt`-preserving `RHTable.insert`s regardless of which
-- core's run queue receives the re-enqueue):
--
--   1. Run-queue placement.  A timed-out thread on a **non-boot** core's tick
--      is re-enqueued onto the **boot core**'s run queue, not the core that was
--      executing the tick.  Cross-core run-queue coherence for the timeout path
--      is the SM5.I.8 cross-subsystem preservation suite's obligation.
--
--   2. Missing cross-core wake SGI (the security-relevant facet).  Unlike the
--      CBS-replenishment wake above — which routes through `wakeThread` and
--      therefore emits a `.reschedule` SGI (`SgiKind.reschedule`, INTID 0) to a
--      remote target via `wakeThread_emits_sgi_if_remote` — the IPC-timeout
--      re-enqueue calls `ensureRunnable` directly and emits **no** SGI.  When a
--      non-boot core's tick times a thread out, the thread lands runnable on the
--      boot core but the boot core is never poked, so it can sit undispatched
--      until the boot core independently reschedules (e.g. on its own next
--      tick).  This is a latency gap (bounded by the boot core's tick period),
--      not a safety violation: no thread is lost (`wakeThread_lossless`'s
--      analogue holds — the thread is on a run queue), no thread runs on two
--      cores (the re-enqueue does not set `current`), and the proven invariants
--      are unaffected.  The proper fix is SM5.F's target-core-aware timeout
--      wake: route the timeout re-enqueue through `wakeThread` (resolving the
--      thread's `cpuAffinity` target via `determineTargetCore`) so a remote
--      target receives the `.reschedule` SGI, exactly as the CBS-replenishment
--      path already does.  Tracked against SM5.F per-core PIP.
-- ────────────────────────────────────────────────────────────────────────

/-- WS-SM SM5.D.5 (local helper): `ensureRunnable` writes only the run queue, so
the object store is unchanged.  (The codebase's `ensureRunnable_objects_eq` lives
in the `Lifecycle.Suspend` namespace, not in this module's import closure; a thin
local copy keeps the dependency footprint minimal.) -/
private theorem ensureRunnable_objects_eq_local (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).objects = st.objects := by
  unfold ensureRunnable; split
  · rfl
  · split <;> rfl

/-- WS-SM SM5.D.5 (preservation): `revertPriorityInheritance` preserves the
object-store invariant — each fuel step is an `updatePipBoost` (a single TCB
`insert`, `invExt`-preserving). -/
theorem revertPriorityInheritance_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (fuel : Nat) (hInv : st.objects.invExt) :
    (PriorityInheritance.revertPriorityInheritance st tid fuel).objects.invExt := by
  induction fuel generalizing st tid with
  | zero => simpa [PriorityInheritance.revertPriorityInheritance] using hInv
  | succ f ih =>
      have hst' := PriorityInheritance.updatePipBoost_preserves_objects_invExt st tid hInv
      rw [PriorityInheritance.revertPriorityInheritance]; split
      · exact ih _ _ hst'
      · exact hst'

/-- WS-SM SM5.D.5 (preservation): `timeoutThread` preserves the object-store
invariant — its writes are endpointQueueRemove (preserves), the TCB `storeObject`
(insert), `ensureRunnable` (object-neutral), and `revertPriorityInheritance`
(preserves). -/
theorem timeoutThread_preserves_objects_invExt (epId : SeLe4n.ObjId) (isRecvQ : Bool)
    (tid : SeLe4n.ThreadId) (execCore : CoreId) (st : SystemState)
    (r : SystemState × Option (CoreId × SgiKind)) (hInv : st.objects.invExt)
    (hStep : timeoutThread epId isRecvQ tid execCore st = .ok r) : r.1.objects.invExt := by
  -- WS-OD OD1.2: the two object writes are the abort's, so this composes
  -- `abortPendingIpcOnEndpoint_preserves_objects_invExt` rather than re-running
  -- its case analysis; what is left here is the wake and the optional PIP
  -- revert, both of which preserve `invExt` on the state component.
  unfold timeoutThread at hStep
  split at hStep
  · simp at hStep
  · rename_i st2 hAbort
    have hInv2 := abortPendingIpcOnEndpoint_preserves_objects_invExt _ _ _ _ _ hInv hAbort
    -- zeta-reduce the two `let`s so the blocking-server match is visible
    simp only [] at hStep
    split at hStep <;>
      · simp only [Except.ok.injEq] at hStep
        subst hStep
        first
          | (apply revertPriorityInheritance_preserves_objects_invExt
             exact wakeThread_preserves_objects_invExt _ _ execCore hInv2)
          | (exact wakeThread_preserves_objects_invExt _ _ execCore hInv2)

/-- WS-SM SM5.D.5 (preservation): `timeoutBlockedThreads` preserves the
object-store invariant — each fold step either keeps the state or applies
`timeoutThread` (which preserves it). -/
theorem timeoutBlockedThreads_preserves_objects_invExt (st : SystemState)
    (scId : SeLe4n.SchedContextId) (execCore : CoreId) (hInv : st.objects.invExt) :
    (timeoutBlockedThreads st scId execCore).1.objects.invExt := by
  unfold timeoutBlockedThreads
  generalize (st.scThreadIndex[scId]?.getD []) = tids
  have hAccInv : ((st, ([] : List (SeLe4n.ThreadId × KernelError)),
      ([] : List (CoreId × SgiKind)))).1.objects.invExt := hInv
  generalize ((st, ([] : List (SeLe4n.ThreadId × KernelError)),
      ([] : List (CoreId × SgiKind)))) = acc at hAccInv ⊢
  induction tids generalizing acc with
  | nil => exact hAccInv
  | cons hd tl ih =>
      rw [List.foldl_cons]
      apply ih
      obtain ⟨st', errs, sgis⟩ := acc
      simp only at hAccInv ⊢
      split
      · rename_i tcb _
        rcases hbi : tcbBlockingInfo tcb with _ | ⟨epId, isRecvQ⟩
        · exact hAccInv
        · dsimp only
          split
          · next r h => exact timeoutThread_preserves_objects_invExt _ _ _ _ _ _ hAccInv h
          · exact hAccInv
      · exact hAccInv

/-- WS-SM SM5.D.5 (preservation): the per-core budget tick preserves the
object-store invariant in every OK branch — each writes only `RHTable.insert`s
(TCB reset / SchedContext budget) plus, in the budget-exhausted branch, the
`timeoutBlockedThreads` call (preserved above). -/
theorem timerTickBudgetOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (b : Bool)
    {sgis : List (CoreId × SgiKind)}
    (hInv : st.objects.invExt)
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b, sgis)) : st'.objects.invExt := by
  unfold timerTickBudgetOnCore at hStep
  split at hStep
  · -- unbound (both time-slice sub-branches: TCB insert)
    split at hStep <;>
      (simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
       obtain ⟨hst, _⟩ := hStep; subst hst
       exact RHTable_insert_preserves_invExt st.objects _ _ hInv)
  all_goals
    -- bound + donated (identical: SchedContext insert, exhausted ⇒ + timeout)
    split at hStep
    · split at hStep
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst
        apply timeoutBlockedThreads_preserves_objects_invExt
        exact RHTable_insert_preserves_invExt st.objects _ _ hInv
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst
        exact RHTable_insert_preserves_invExt st.objects _ _ hInv
    · simp at hStep

/-- WS-SM SM5.D.5: an *unbound* thread whose time-slice has not expired
(`timeSlice > 1`) is **not** preempted by the budget tick. -/
theorem timerTickBudgetOnCore_unbound_not_preempted (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (b : Bool)
    (hUnbound : tcb.schedContextBinding = .unbound) (hSlice : ¬ tcb.timeSlice ≤ 1)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b, sgis)) : b = false := by
  simp only [timerTickBudgetOnCore, hUnbound, if_neg hSlice, Except.ok.injEq,
    Prod.mk.injEq] at hStep
  exact hStep.2.1.symm

/-- WS-SM SM5.D.5: an *unbound* thread whose time-slice has expired
(`timeSlice ≤ 1`) **is** preempted (`wasPreempted = true`) — the per-core
time-slice preemption. -/
theorem timerTickBudgetOnCore_unbound_preempts (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (b : Bool)
    (hUnbound : tcb.schedContextBinding = .unbound) (hSlice : tcb.timeSlice ≤ 1)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b, sgis)) : b = true := by
  simp only [timerTickBudgetOnCore, hUnbound, if_pos hSlice, Except.ok.injEq,
    Prod.mk.injEq] at hStep
  exact hStep.2.1.symm

/-- WS-SM SM5.D.5 / B4: a *bound* thread whose SchedContext budget is exhausted
(`budgetRemaining ≤ 1`) **is** preempted — the per-core CBS budget-exhaustion
preemption (the substantive one, beyond the time-slice case above). -/
theorem timerTickBudgetOnCore_bound_preempts (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (st' : SystemState) (b : Bool)
    (hBound : tcb.schedContextBinding = .bound scId)
    (hSc : st.getSchedContext? scId = some sc) (hBudget : sc.budgetRemaining.val ≤ 1)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b, sgis)) : b = true := by
  simp only [timerTickBudgetOnCore, hBound, hSc, if_pos hBudget, Except.ok.injEq,
    Prod.mk.injEq] at hStep
  exact hStep.2.1.symm

/-- WS-SM SM5.D.5 / B4: a *bound* thread whose SchedContext budget has not expired
(`budgetRemaining > 1`) is **not** preempted (the budget is decremented and the
thread continues). -/
theorem timerTickBudgetOnCore_bound_not_preempted (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (st' : SystemState) (b : Bool)
    (hBound : tcb.schedContextBinding = .bound scId)
    (hSc : st.getSchedContext? scId = some sc) (hBudget : ¬ sc.budgetRemaining.val ≤ 1)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b, sgis)) : b = false := by
  simp only [timerTickBudgetOnCore, hBound, hSc, if_neg hBudget, Except.ok.injEq,
    Prod.mk.injEq] at hStep
  exact hStep.2.1.symm

/-- WS-SM SM5.D.5 / B4: the *donated* SchedContext-binding case — budget exhausted
(`budgetRemaining ≤ 1`) preempts.  (The `.donated scId _` arm of
`timerTickBudgetOnCore` shares the bound-case body.) -/
theorem timerTickBudgetOnCore_donated_preempts (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId) (sc : SchedContext) (st' : SystemState) (b : Bool)
    (hDonated : tcb.schedContextBinding = .donated scId originalOwner)
    (hSc : st.getSchedContext? scId = some sc) (hBudget : sc.budgetRemaining.val ≤ 1)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b, sgis)) : b = true := by
  simp only [timerTickBudgetOnCore, hDonated, hSc, if_pos hBudget, Except.ok.injEq,
    Prod.mk.injEq] at hStep
  exact hStep.2.1.symm

/-- WS-SM SM5.D.5 (local helper): `saveOutgoingContextOnCore` preserves the
object store (its only write is the outgoing TCB's register save — an insert). -/
theorem saveOutgoingContextOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (saveOutgoingContextOnCore st c).objects.invExt := by
  unfold saveOutgoingContextOnCore
  split
  · exact hInv
  · split
    · exact RHTable_insert_preserves_invExt st.objects _ _ hInv
    · exact hInv

/-- WS-SM SM5.D.5 (local helper): `restoreIncomingContext` writes only the machine
register file, so the object store is unchanged. -/
theorem restoreIncomingContext_objects_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).objects = st.objects := by
  unfold restoreIncomingContext; split <;> rfl

-- ============================================================================
-- WS-SM SM5.E (folded idle): `idleFallbackOnCore` invariant lemmas.  These
-- discharge the idle-vs-`none` case analysis **once**, so each
-- `scheduleEffectiveOnCore` establishment proof's `none` case is a clean
-- one-liner.  (Placed before the establishment theorems so they are in scope.)
-- ============================================================================

/-- WS-SM SM5.E: the idle fallback establishes current-thread validity — the idle
arm dispatches the (installed) idle thread; the `none` arm is vacuous. -/
theorem idleFallbackOnCore_establishes_currentThreadValidOnCore (st : SystemState) (c : CoreId) :
    currentThreadValidOnCore (idleFallbackOnCore st c) c := by
  unfold idleFallbackOnCore
  split
  · rename_i hd
    unfold currentThreadValidOnCore
    simp only [dispatchIdleOnCore_currentOnCore, dispatchIdleOnCore_getTcb?]
    unfold idleDispatchableOnCore at hd
    cases hres : st.getTcb? (idleThreadId c) with
    | none => rw [hres] at hd; simp at hd
    | some idleTcb => exact ⟨idleTcb, rfl⟩
  · unfold currentThreadValidOnCore
    simp only [SchedulerState.setCurrentOnCore_currentOnCore_self]

/-- WS-SM SM5.E: the idle fallback establishes dequeue-on-dispatch consistency —
the idle arm dequeues idle before making it current; the `none` arm is vacuous. -/
theorem idleFallbackOnCore_establishes_queueCurrentConsistentOnCore (st : SystemState) (c : CoreId) :
    queueCurrentConsistentOnCore (idleFallbackOnCore st c).scheduler c := by
  unfold idleFallbackOnCore
  split
  · unfold queueCurrentConsistentOnCore
    simp only [dispatchIdleOnCore_currentOnCore, dispatchIdleOnCore_runQueueOnCore]
    exact RunQueue.not_mem_remove_toList _ (idleThreadId c)
  · unfold queueCurrentConsistentOnCore
    simp only [SchedulerState.setCurrentOnCore_currentOnCore_self]

/-- WS-SM SM5.E: the idle fallback establishes current-in-active-domain — the idle
arm's domain matches (the `idleDispatchableOnCore` gate checks it); the `none` arm
is vacuous. -/
theorem idleFallbackOnCore_establishes_currentThreadInActiveDomainOnCore (st : SystemState) (c : CoreId) :
    currentThreadInActiveDomainOnCore (idleFallbackOnCore st c) c := by
  unfold idleFallbackOnCore
  split
  · rename_i hd
    unfold currentThreadInActiveDomainOnCore
    simp only [dispatchIdleOnCore_currentOnCore, dispatchIdleOnCore_getTcb?,
      dispatchIdleOnCore_activeDomainOnCore]
    unfold idleDispatchableOnCore at hd
    cases hres : st.getTcb? (idleThreadId c) with
    | none => rw [hres] at hd; simp at hd
    | some idleTcb => rw [hres] at hd; simp only [Bool.and_eq_true] at hd; simpa using hd.1
  · unfold currentThreadInActiveDomainOnCore
    simp only [SchedulerState.setCurrentOnCore_currentOnCore_self]

/-- WS-SM SM5.E: the idle fallback preserves run-queue well-formedness — the idle
arm only `remove`s the idle thread; the `none` arm leaves the run queue. -/
theorem idleFallbackOnCore_preserves_runQueueOnCoreWellFormed (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed) :
    ((idleFallbackOnCore st c).scheduler.runQueueOnCore c).wellFormed := by
  unfold idleFallbackOnCore
  split
  · rw [dispatchIdleOnCore_runQueueOnCore]
    exact RunQueue.remove_preserves_wellFormed _ hwf _
  · simpa [SchedulerState.setCurrentOnCore_runQueueOnCore] using hwf

/-- WS-SM SM5.I (the register-bank payoff, idle case): dispatching idle
**establishes** `contextMatchesCurrentOnCore` — core `c`'s bank holds the (just
dispatched) idle thread's register context.  The `idleDispatchableOnCore` gate
guarantees the idle thread resolves to a TCB, which the per-core restore writes
into core `c`'s bank. -/
theorem dispatchIdleOnCore_establishes_contextMatchesCurrentOnCore (st : SystemState) (c : CoreId)
    (hd : idleDispatchableOnCore st c = true) :
    contextMatchesCurrentOnCore (dispatchIdleOnCore st c) c := by
  unfold idleDispatchableOnCore at hd
  cases hres : st.getTcb? (idleThreadId c) with
  | none => rw [hres] at hd; simp at hd
  | some idleTcb =>
    unfold contextMatchesCurrentOnCore
    rw [dispatchIdleOnCore_currentOnCore]
    simp only [dispatchIdleOnCore_getTcb?, hres]
    rw [dispatchIdleOnCore_machine_regsOnCore_self st c idleTcb hres]
    exact RegisterFile.beq_self _

/-- WS-SM SM5.I (the register-bank payoff, fallback): the idle fallback
**establishes** `contextMatchesCurrentOnCore` — the idle arm dispatches the
(installed) idle thread into core `c`'s bank, the `none` arm leaves `current =
none` (vacuously matching).  This is the `none`-branch companion of
`switchToThreadOnCore_establishes_contextMatchesCurrentOnCore`. -/
theorem idleFallbackOnCore_establishes_contextMatchesCurrentOnCore (st : SystemState) (c : CoreId) :
    contextMatchesCurrentOnCore (idleFallbackOnCore st c) c := by
  unfold idleFallbackOnCore
  split
  · rename_i hd
    exact dispatchIdleOnCore_establishes_contextMatchesCurrentOnCore st c hd
  · unfold contextMatchesCurrentOnCore
    simp only [SchedulerState.setCurrentOnCore_currentOnCore_self]

/-- WS-SM SM5.D.5 (preservation): the per-core budget-aware reschedule preserves
the object-store invariant (save-outgoing insert + restore-incoming register-only
write). -/
theorem scheduleEffectiveOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') : st'.objects.invExt := by
  unfold scheduleEffectiveOnCore at hStep
  split at hStep
  · simp at hStep
  · -- WS-SM SM5.E (folded idle): the `none` branch dispatches idle if dispatchable;
    -- `idleFallbackOnCore_objects` discharges both arms (idle / `none`) at once.
    simp only [Except.ok.injEq] at hStep; subst hStep
    rw [idleFallbackOnCore_objects]
    exact saveOutgoingContextOnCore_preserves_objects_invExt st c hInv
  · split at hStep
    · split at hStep
      · simp only [Except.ok.injEq] at hStep; subst hStep
        rw [restoreIncomingContextOnCore_objects]
        exact saveOutgoingContextOnCore_preserves_objects_invExt st c hInv
      · simp at hStep
    · simp at hStep

-- ============================================================================
-- §4b  SM5.D.6 — Full per-core domain re-dispatch (`switchDomainOnCore` /
--      `scheduleDomainOnCore`).  These are the domain-*boundary* re-dispatch
--      counterparts of §2's lightweight in-tick `decrementDomainTimeOnCore`.
--      They depend on §4's context save/restore preservation, so they live
--      here rather than in §2.
-- ============================================================================

/-- WS-SM SM5.D.6: in single-domain mode (`domainSchedule = []`) the per-core
domain switch is a no-op. -/
theorem switchDomainOnCore_singleDomain_noop (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule = []) :
    switchDomainOnCore st c = .ok st := by
  unfold switchDomainOnCore; rw [hSched]

/-- WS-SM SM5.D.6 (preservation): `switchDomainOnCore` preserves the RobinHood
object-store invariant.  The empty-schedule case is the identity; the domain-
boundary case writes only the saved register context (`saveOutgoingContextOnCore`,
which preserves `invExt`) plus scheduler-field slots. -/
theorem switchDomainOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : switchDomainOnCore st c = .ok st') : st'.objects.invExt := by
  unfold switchDomainOnCore at hStep
  cases hcase : st.scheduler.domainSchedule with
  | nil => rw [hcase] at hStep; simp only [Except.ok.injEq] at hStep; subst hStep; exact hInv
  | cons hd tl =>
    rw [hcase] at hStep; dsimp only at hStep
    split at hStep
    · simp at hStep
    · simp only [Except.ok.injEq] at hStep; subst hStep
      exact saveOutgoingContextOnCore_preserves_objects_invExt st c hInv

/-- WS-SM SM5.D.6: a successful per-core domain switch on a non-empty schedule
clears `currentOnCore c` (the outgoing thread is preempted and re-enqueued before
the next domain's `chooseThread` selects a fresh current). -/
theorem switchDomainOnCore_sets_currentOnCore_none (st : SystemState) (c : CoreId)
    (st' : SystemState) (hStep : switchDomainOnCore st c = .ok st')
    (hSched : st.scheduler.domainSchedule ≠ []) :
    st'.scheduler.currentOnCore c = none := by
  unfold switchDomainOnCore at hStep
  cases hcase : st.scheduler.domainSchedule with
  | nil => exact absurd hcase hSched
  | cons hd tl =>
    rw [hcase] at hStep; dsimp only at hStep
    split at hStep
    · simp at hStep
    · simp only [Except.ok.injEq] at hStep; subst hStep
      simp [SchedulerState.setDomainScheduleIndexOnCore_currentOnCore,
        SchedulerState.setDomainTimeRemainingOnCore_currentOnCore,
        SchedulerState.setActiveDomainOnCore_currentOnCore,
        SchedulerState.setCurrentOnCore_currentOnCore_self]

/-- WS-SM SM5.D.6: a successful per-core domain switch advances core `c`'s active
domain to the domain of the next schedule entry (the per-core domain rotation
that gives multi-domain SMP scheduling its round-robin shape). -/
theorem switchDomainOnCore_rotates (st : SystemState) (c : CoreId) (st' : SystemState)
    (entry : DomainScheduleEntry)
    (hLookup : st.scheduler.domainSchedule[((st.scheduler.domainScheduleIndexOnCore c) + 1) %
        st.scheduler.domainSchedule.length]? = some entry)
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hStep : switchDomainOnCore st c = .ok st') :
    st'.scheduler.activeDomainOnCore c = DomainScheduleEntry.domain entry := by
  unfold switchDomainOnCore at hStep
  cases hcase : st.scheduler.domainSchedule with
  | nil => exact absurd hcase hSched
  | cons hd tl =>
    rw [hcase] at hStep
    dsimp only at hStep
    simp only [hcase] at hLookup
    rw [hLookup] at hStep
    simp only [Except.ok.injEq] at hStep
    subst hStep
    simp [SchedulerState.setDomainScheduleIndexOnCore_activeDomainOnCore,
      SchedulerState.setDomainTimeRemainingOnCore_activeDomainOnCore,
      SchedulerState.setActiveDomainOnCore_activeDomainOnCore_self]

/-- WS-SM SM5.D.6: with a non-empty domain schedule, before the domain boundary
expires (`domainTimeRemainingOnCore c > 1`), `scheduleDomainOnCore` only
decrements core `c`'s domain time remaining (the lightweight in-domain tick);
it does not rotate or re-dispatch.  (In single-domain mode there is no
accounting at all — `scheduleDomainOnCore_singleDomain_inert`.) -/
theorem scheduleDomainOnCore_decrements (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hle : st.scheduler.domainTimeRemainingOnCore c > 1) :
    ∃ st', scheduleDomainOnCore st c = .ok st' ∧
      st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c - 1 := by
  refine ⟨decrementDomainTimeOnCore st c, ?_, ?_⟩
  · unfold scheduleDomainOnCore
    cases hcase : st.scheduler.domainSchedule with
    | nil => exact absurd hcase hSched
    | cons hd tl => rw [if_neg (by omega)]
  · exact decrementDomainTimeOnCore_decrements st c

/-- WS-SM SM5.D.6 (preservation): `scheduleDomainOnCore` preserves the RobinHood
object-store invariant.  On a domain boundary it composes `switchDomainOnCore`
with the budget-aware `scheduleEffectiveOnCore` (both `invExt`-preserving); the
in-domain tick only writes a scheduler slot. -/
theorem scheduleDomainOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleDomainOnCore st c = .ok st') : st'.objects.invExt := by
  unfold scheduleDomainOnCore at hStep
  split at hStep
  · -- single-domain mode: the domain tick is the identity.
    simp only [Except.ok.injEq] at hStep; subst hStep; exact hInv
  · -- non-empty schedule.
    split at hStep
    · -- boundary: switch then re-dispatch.
      split at hStep
      · simp at hStep
      · rename_i st'' hsw
        exact scheduleEffectiveOnCore_preserves_objects_invExt st'' c st'
          (switchDomainOnCore_preserves_objects_invExt st c st'' hInv hsw) hStep
    · -- non-boundary: pure domain-time decrement.
      simp only [Except.ok.injEq] at hStep; subst hStep; exact hInv

-- ============================================================================
-- §5  SM5.D.2 / .9 — `timerTickOnCore` semantics (idle, no-global-timer-advance,
--      lastTimeoutErrors clearing, the headlines, objects-invExt preservation)
-- ============================================================================

-- ── frame helpers: the per-core tick reads but does not advance the global
--    machine, and clears (never spuriously re-sets) core `c`'s timeout-error
--    diagnostic on the idle path. ──

/-- WS-SM SM5.D.4: `refillSchedContext` writes only the object store, leaving the
scheduler unchanged. -/
@[simp] theorem refillSchedContext_scheduler_eq (st : SystemState)
    (scId : SeLe4n.SchedContextId) (now : Nat) :
    (refillSchedContext st scId now).scheduler = st.scheduler := by
  unfold refillSchedContext; split <;> rfl

/-- WS-SM SM5.D.4: `refillSchedContext` leaves the machine state unchanged. -/
@[simp] theorem refillSchedContext_machine_eq (st : SystemState)
    (scId : SeLe4n.SchedContextId) (now : Nat) :
    (refillSchedContext st scId now).machine = st.machine := by
  unfold refillSchedContext; split <;> rfl

/-- WS-SM SM5.C: `enqueueRunnableOnCore` leaves the machine state unchanged
(it writes only the object store and a run-queue slot). -/
@[simp] theorem enqueueRunnableOnCore_machine_eq (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : (enqueueRunnableOnCore st c tid).machine = st.machine := by
  unfold enqueueRunnableOnCore; split
  · split <;> rfl
  · rfl

/-- WS-SM SM5.C: `enqueueRunnableOnCore` leaves every core's `lastTimeoutErrors`
slot unchanged. -/
theorem enqueueRunnableOnCore_lastTimeoutErrorsOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueRunnableOnCore st c tid).scheduler.lastTimeoutErrorsOnCore c'
      = st.scheduler.lastTimeoutErrorsOnCore c' := by
  unfold enqueueRunnableOnCore; split
  · split
    · rfl
    · simp only [SchedulerState.setRunQueueOnCore_lastTimeoutErrorsOnCore]
  · rfl

/-- WS-SM SM5.D.4: `processOneReplenishmentOnCore` leaves the machine unchanged. -/
theorem processOneReplenishmentOnCore_machine_eq (st : SystemState) (ec : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) :
    (processOneReplenishmentOnCore st ec scId now).1.machine = st.machine := by
  simp only [processOneReplenishmentOnCore]
  split
  · split
    · rw [refillSchedContext_machine_eq]
    · rw [wakeThread_state_eq_enqueue, enqueueRunnableOnCore_machine_eq, refillSchedContext_machine_eq]
  · rw [refillSchedContext_machine_eq]

/-- WS-SM SM5.D.4: `processOneReplenishmentOnCore` leaves every core's
`lastTimeoutErrors` slot unchanged. -/
theorem processOneReplenishmentOnCore_lastTimeoutErrorsOnCore_eq (st : SystemState) (ec : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (c' : CoreId) :
    (processOneReplenishmentOnCore st ec scId now).1.scheduler.lastTimeoutErrorsOnCore c'
      = st.scheduler.lastTimeoutErrorsOnCore c' := by
  simp only [processOneReplenishmentOnCore]
  split
  · split
    · rw [refillSchedContext_scheduler_eq]
    · rw [wakeThread_state_eq_enqueue, enqueueRunnableOnCore_lastTimeoutErrorsOnCore,
        refillSchedContext_scheduler_eq]
  · rw [refillSchedContext_scheduler_eq]

/-- WS-SM SM5.D.4: `processReplenishmentsDueOnCore` leaves the machine unchanged —
the per-core CBS replenishment reads `now := machine.timer` but never advances the
global timer. -/
theorem processReplenishmentsDueOnCore_machine_eq (st : SystemState) (c : CoreId) (now : Nat) :
    (processReplenishmentsDueOnCore st c now).1.machine = st.machine := by
  simp only [processReplenishmentsDueOnCore]
  generalize ((st.scheduler.replenishQueueOnCore c).popDue now).2 = dueIds
  have key : ∀ acc : SystemState × List (CoreId × SgiKind) × Bool,
      (dueIds.foldl (fun acc scId =>
        let r := processOneReplenishmentOnCore acc.1 c scId now
        (r.1, acc.2.1 ++ r.2.1.toList, acc.2.2 || r.2.2)) acc).1.machine = acc.1.machine := by
    intro acc
    induction dueIds generalizing acc with
    | nil => rfl
    | cons hd tl ih => rw [List.foldl_cons, ih]; exact processOneReplenishmentOnCore_machine_eq acc.1 c hd now
  rw [key]

/-- WS-SM SM5.D.4: `processReplenishmentsDueOnCore` leaves every core's
`lastTimeoutErrors` slot unchanged (the `popDue` writes only the replenish-queue
slot; the wakes write run queues / objects). -/
theorem processReplenishmentsDueOnCore_lastTimeoutErrorsOnCore_eq (st : SystemState)
    (c : CoreId) (now : Nat) (c' : CoreId) :
    (processReplenishmentsDueOnCore st c now).1.scheduler.lastTimeoutErrorsOnCore c'
      = st.scheduler.lastTimeoutErrorsOnCore c' := by
  simp only [processReplenishmentsDueOnCore]
  generalize ((st.scheduler.replenishQueueOnCore c).popDue now).2 = dueIds
  have key : ∀ acc : SystemState × List (CoreId × SgiKind) × Bool,
      (dueIds.foldl (fun acc scId =>
        let r := processOneReplenishmentOnCore acc.1 c scId now
        (r.1, acc.2.1 ++ r.2.1.toList, acc.2.2 || r.2.2)) acc).1.scheduler.lastTimeoutErrorsOnCore c'
      = acc.1.scheduler.lastTimeoutErrorsOnCore c' := by
    intro acc
    induction dueIds generalizing acc with
    | nil => rfl
    | cons hd tl ih => rw [List.foldl_cons, ih]
                       exact processOneReplenishmentOnCore_lastTimeoutErrorsOnCore_eq acc.1 c hd now c'
  rw [key]
  simp [SchedulerState.setReplenishQueueOnCore_lastTimeoutErrorsOnCore]

/-- WS-SM SM5.D.4: `processOneReplenishmentOnCore` leaves every core's `current`
slot unchanged — it refills a SchedContext and may *enqueue* a woken thread, but
enqueueing is not dispatching. -/
theorem processOneReplenishmentOnCore_currentOnCore_eq (st : SystemState) (ec : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (c' : CoreId) :
    (processOneReplenishmentOnCore st ec scId now).1.scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  simp only [processOneReplenishmentOnCore]
  split
  · split
    · rw [refillSchedContext_scheduler_eq]
    · rw [wakeThread_state_eq_enqueue, enqueueRunnableOnCore_currentOnCore,
        refillSchedContext_scheduler_eq]
  · rw [refillSchedContext_scheduler_eq]

/-- WS-SM SM8.B (PR #861 review round 17): `processReplenishmentsDueOnCore`
leaves every core's `current` slot unchanged.

This is the load-bearing half of *the timer tick cannot rescue a vacated core*.
`timerTickOnCore_eq_prepared`'s `| none =>` arm — the arm taken exactly when the
core has no current thread — returns `timerTickOnCorePrepared` verbatim, and the
prepared state is the timeout-error clear composed with this replenishment pass.
Neither writes `current`, so a core that entered the tick vacated leaves it
vacated, however many ticks elapse.  Without this the round-17 defect would be a
latency question ("the next tick picks it up"); with it, nothing in the system
dispatches that core until some *other* core happens to poke it. -/
theorem processReplenishmentsDueOnCore_currentOnCore_eq (st : SystemState)
    (c : CoreId) (now : Nat) (c' : CoreId) :
    (processReplenishmentsDueOnCore st c now).1.scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  simp only [processReplenishmentsDueOnCore]
  generalize ((st.scheduler.replenishQueueOnCore c).popDue now).2 = dueIds
  have key : ∀ acc : SystemState × List (CoreId × SgiKind) × Bool,
      (dueIds.foldl (fun acc scId =>
        let r := processOneReplenishmentOnCore acc.1 c scId now
        (r.1, acc.2.1 ++ r.2.1.toList, acc.2.2 || r.2.2)) acc).1.scheduler.currentOnCore c'
      = acc.1.scheduler.currentOnCore c' := by
    intro acc
    induction dueIds generalizing acc with
    | nil => rfl
    | cons hd tl ih => rw [List.foldl_cons, ih]
                       exact processOneReplenishmentOnCore_currentOnCore_eq acc.1 c hd now c'
  rw [key]
  simp [SchedulerState.setReplenishQueueOnCore_currentOnCore]

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` leaves every core's
`lastTimeoutErrors` slot unchanged (it writes only domain slots). -/
theorem decrementDomainTimeOnCore_lastTimeoutErrorsOnCore (st : SystemState) (c c' : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.lastTimeoutErrorsOnCore c'
      = st.scheduler.lastTimeoutErrorsOnCore c' := by
  simp [decrementDomainTimeOnCore, SchedulerState.setDomainTimeRemainingOnCore_lastTimeoutErrorsOnCore]

-- ── the prepared state + the `timerTickOnCore` characterisation ──

/-- WS-SM SM5.D.2: the state `timerTickOnCore` reaches after the SM5.D.9 timeout-
error clear + the SM5.D.4 replenishment, **before** the SM5.D.6 domain accounting —
the post-replenishment state. -/
def timerTickOnCorePreDomain (st : SystemState) (c : CoreId) : SystemState :=
  let st0 := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] }
  (processReplenishmentsDueOnCore st0 c st0.machine.timer).1

/-- WS-SM SM5.D.2: the state-plus-SGIs-plus-local-wake-bit `timerTickOnCore`
reaches after the SM5.D.9 clear + SM5.D.4 replenishment, **before** the SM5.D.5
budget tick / preemption.  Audit-pass-2: the tick does **no** in-tick domain
accounting (rotation is the separate `scheduleDomainOnCore`), so the prepared
state is exactly the post-replenishment state.  Naming it lets the SM5.D
headline theorems characterise `timerTickOnCore`'s behaviour without restating
its internal `let`-chain.  Components: `.1` the post-replenishment state, `.2.1`
the cross-core SGIs to emit, `.2.2` (PR #880 round 7) the local-wake bit the
tick resolves with `handleRescheduleSgiOnCore` when the budget charge did not
already re-dispatch. -/
def timerTickOnCorePrepared (st : SystemState) (c : CoreId) :
    SystemState × List (CoreId × SgiKind) × Bool :=
  let st0 := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] }
  processReplenishmentsDueOnCore st0 c st0.machine.timer

/-- WS-SM SM5.D.2: `timerTickOnCorePrepared`'s state is the post-replenishment
(pre-domain) state — the SM5.D.5 budget step operates on this. -/
theorem timerTickOnCorePrepared_fst_eq (st : SystemState) (c : CoreId) :
    (timerTickOnCorePrepared st c).1 = timerTickOnCorePreDomain st c := rfl

/-- WS-SM SM5.D.2: `timerTickOnCore` is the SM5.D.5 budget tick / preemption —
plus, since PR #880 round 7, the local replenish-wake reschedule decision —
dispatched on the SM5.D.2/.4 prepared state.  `rfl` — the production
`let`-chain *is* this composition.  Every SM5.D.2 headline below is a
corollary. -/
theorem timerTickOnCore_eq_prepared (st : SystemState) (c : CoreId) :
    timerTickOnCore st c =
      (match (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c with
       | none =>
           if (timerTickOnCorePrepared st c).2.2 then
             match handleRescheduleSgiOnCore (timerTickOnCorePrepared st c).1 c with
             | .error e => .error e
             | .ok st2 => .ok (st2, (timerTickOnCorePrepared st c).2.1)
           else .ok ((timerTickOnCorePrepared st c).1, (timerTickOnCorePrepared st c).2.1)
       | some tid =>
           match (timerTickOnCorePrepared st c).1.getTcb? tid with
           | some tcb =>
               match timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb with
               | .error e => .error e
               | .ok (st3, preempted, timeoutSgis) =>
                   if preempted then
                     match scheduleEffectiveOnCore st3 c with
                     | .error e => .error e
                     | .ok st4 => .ok (st4, (timerTickOnCorePrepared st c).2.1 ++ timeoutSgis)
                   else if (timerTickOnCorePrepared st c).2.2 then
                     match handleRescheduleSgiOnCore st3 c with
                     | .error e => .error e
                     | .ok st4 => .ok (st4, (timerTickOnCorePrepared st c).2.1 ++ timeoutSgis)
                   else .ok (st3, (timerTickOnCorePrepared st c).2.1 ++ timeoutSgis)
           | none => .error .schedulerInvariantViolation) := rfl

/-- WS-SM SM5.D.2: the prepared state preserves the machine — the per-core tick
reads `machine.timer` but never advances the global timer. -/
theorem timerTickOnCorePrepared_machine_eq (st : SystemState) (c : CoreId) :
    (timerTickOnCorePrepared st c).1.machine = st.machine := by
  simp only [timerTickOnCorePrepared]
  rw [processReplenishmentsDueOnCore_machine_eq]

/-- WS-SM SM5.D.9: the prepared state has core `c`'s `lastTimeoutErrors` cleared —
the tick clears core `c`'s diagnostic at entry, and the replenishment step never
re-sets it. -/
theorem timerTickOnCorePrepared_lastTimeoutErrors_eq (st : SystemState) (c : CoreId) :
    (timerTickOnCorePrepared st c).1.scheduler.lastTimeoutErrorsOnCore c = [] := by
  simp only [timerTickOnCorePrepared]
  rw [processReplenishmentsDueOnCore_lastTimeoutErrorsOnCore_eq]
  simp [SchedulerState.setLastTimeoutErrorsOnCore_lastTimeoutErrorsOnCore_self]

/-- WS-SM SM8.B (PR #861 review round 17): the prepared state does not dispatch —
it leaves every core's `current` slot exactly as it found it. -/
theorem timerTickOnCorePrepared_currentOnCore_eq (st : SystemState) (c c' : CoreId) :
    (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  simp only [timerTickOnCorePrepared]
  rw [processReplenishmentsDueOnCore_currentOnCore_eq]
  simp [SchedulerState.setLastTimeoutErrorsOnCore_currentOnCore]

/-- WS-SM SM8.B (PR #861 review round 17): **the timer tick cannot rescue a
vacated core.**

A core that enters its tick with no current thread — and whose replenishment
drain wakes nothing local (`hNoWake`) — leaves it with no current thread,
however many ticks elapse, and regardless of what its run queue holds.
`timerTickOnCore` branches on exactly that slot
(`timerTickOnCore_eq_prepared`), and its `none` arm without the local-wake bit
returns the prepared state verbatim: a timeout-error clear and a replenishment
pass, neither of which dispatches.

This is what made the round-17 finding a defect rather than a latency
question: the blocking IPC legs vacate the caller's core, the cross-core SGI
list excludes it by construction (`currentSlotChangeSgis_not_execCore`), and
absent the `scheduleLocalSuccessor` seam nothing dispatches that core until
some *unrelated* transition on *another* core happens to poke it.  **PR #880
round 7 carves out the one event the tick itself produces**: a local
replenish wake (the drain refilled a thread targeting this very core) now
runs the receiver-side reschedule decision — `hNoWake` is what excludes that
arm here, and `timerTickOnCore_idle_local_wake_reschedules` (below) pins the
dispatch it performs.  A thread queued-but-exhausted on a vacated core was
ineligible when `scheduleLocalSuccessor` ran at the vacate seam, so its
refill — which fires no SGI — was otherwise invisible to every scheduling
trigger. -/
theorem timerTickOnCore_cannot_dispatch_vacated_core (st : SystemState) (c : CoreId)
    (res : SystemState × List (CoreId × SgiKind))
    (hIdle : st.scheduler.currentOnCore c = none)
    (hNoWake : (timerTickOnCorePrepared st c).2.2 = false)
    (hTick : timerTickOnCore st c = .ok res) :
    res.1.scheduler.currentOnCore c = none := by
  rw [timerTickOnCore_eq_prepared] at hTick
  rw [timerTickOnCorePrepared_currentOnCore_eq st c c, hIdle, hNoWake] at hTick
  simp only [Bool.false_eq_true, if_false, Except.ok.injEq] at hTick
  have h1 : (timerTickOnCorePrepared st c).1 = res.1 := by rw [← hTick]
  rw [← h1, timerTickOnCorePrepared_currentOnCore_eq, hIdle]

/-- WS-SM SM5.D.2 (preservation): the prepared state preserves the object-store
invariant (the SM5.D.4 replenishment preserves it). -/
theorem timerTickOnCorePrepared_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (timerTickOnCorePrepared st c).1.objects.invExt := by
  simp only [timerTickOnCorePrepared]
  exact processReplenishmentsDueOnCore_preserves_objects_invExt _ c _ hInv

-- ── SM5.D.2 headline theorems ──

/-- WS-SM SM5.D.2: on the quiet idle path (core `c` has no current thread in the
prepared state — e.g. a freshly-booted or freshly-idled core — and the drain
woke nothing local), the tick is exactly the prepared state: the SM5.D.4
replenishment with no budget charge and no dispatch.  With a local replenish
wake the idle arm instead dispatches — see
`timerTickOnCore_idle_local_wake_reschedules` (PR #880 round 7). -/
theorem timerTickOnCore_idle (st : SystemState) (c : CoreId)
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = none)
    (hNoWake : (timerTickOnCorePrepared st c).2.2 = false) :
    timerTickOnCore st c
      = .ok ((timerTickOnCorePrepared st c).1, (timerTickOnCorePrepared st c).2.1) := by
  rw [timerTickOnCore_eq_prepared, hCur, hNoWake]
  rfl

/-- WS-SM (PR #880 round 7): a local replenish wake **dispatches an idle-slot
core**.  When core `c` has no current thread in the prepared state but the
replenishment drain woke a thread targeting core `c` itself (the local-wake
bit), the tick runs the receiver-side reschedule decision
(`handleRescheduleSgiOnCore` — whose gate admits any candidate on an idle
core), so the refilled thread is dispatched by the very tick that made it
eligible instead of stranding until an unrelated cross-core poke. -/
theorem timerTickOnCore_idle_local_wake_reschedules (st : SystemState) (c : CoreId)
    (st2 : SystemState)
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = none)
    (hWake : (timerTickOnCorePrepared st c).2.2 = true)
    (hHandle : handleRescheduleSgiOnCore (timerTickOnCorePrepared st c).1 c = .ok st2) :
    timerTickOnCore st c = .ok (st2, (timerTickOnCorePrepared st c).2.1) := by
  rw [timerTickOnCore_eq_prepared]
  simp only [hCur, hWake, if_true, hHandle]

/-- WS-SM SM5.D.2 (the headline `timerTickOnCore_advances_per_core`, plan §6.1): the
per-core tick **advances core `c`'s local accounting without advancing the global
timer** — `st'.machine = st.machine`.  This is the defining SMP property: each
core's CNTP fires and the tick processes that core's state locally, but the global
monotonic tick counter (`machine.timer`) is owned by a single authority — the
boot core's committed run-loop step (`tickClockedState` in `PerCoreRunLoop.lean`),
mirroring the Rust HAL's primary-owned `TICK_COUNT` (advanced by the boot core's
`per_core_timer_tick_isr` invocation, one site).  Stated on the idle path (where
the tick makes no register-context write, so the *whole* machine is preserved);
the global-timer field specifically is preserved on every path. -/
theorem timerTickOnCore_advances_per_core (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = none)
    (hNoWake : (timerTickOnCorePrepared st c).2.2 = false)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    st'.machine = st.machine := by
  rw [timerTickOnCore_idle st c hCur hNoWake, Except.ok.injEq, Prod.mk.injEq] at hStep
  rw [← hStep.1, timerTickOnCorePrepared_machine_eq]

/-- WS-SM SM5.D.9: on the idle path, the tick leaves core `c`'s `lastTimeoutErrors`
cleared — a stale timeout-error record never survives a tick. -/
theorem timerTickOnCore_clears_lastTimeoutErrors (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = none)
    (hNoWake : (timerTickOnCorePrepared st c).2.2 = false)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    st'.scheduler.lastTimeoutErrorsOnCore c = [] := by
  rw [timerTickOnCore_idle st c hCur hNoWake, Except.ok.injEq, Prod.mk.injEq] at hStep
  rw [← hStep.1, timerTickOnCorePrepared_lastTimeoutErrors_eq]

-- WS-SM SM5.D.6 (audit-pass-2): the per-core *timer tick* deliberately does **no**
-- in-tick domain rotation (the pre-audit-pass-2 `timerTickOnCore_rotates_domain`
-- headline is retired).  Domain rotation is the separate, atomic
-- `scheduleDomainOnCore` transition (its boundary branch is `switchDomainOnCore` +
-- `scheduleEffectiveOnCore`); `switchDomainOnCore_rotates` (§4b) is the rotation
-- witness.  This is exactly the single-core split (`timerTickWithBudget` never
-- rotates; `scheduleDomain` does), and it is what keeps a running thread from
-- outliving its domain (`currentThreadInActiveDomain` faithfulness).

/-- WS-SM SM5.D.5 (the headline `timerTickOnCore_preempts_local`, plan §6.1): when
core `c`'s current thread `tid` (in the prepared state) is preempted by the budget
tick (`timerTickBudgetOnCore … = .ok (st3, true)` — time-slice / budget exhausted),
the tick re-selects and dispatches via the budget-aware `scheduleEffectiveOnCore` —
the per-core local preemption. -/
theorem timerTickOnCore_preempts_local (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st3 st' : SystemState)
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid)
    (hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb)
    {tsgis : List (CoreId × SgiKind)}
    (hBud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, true, tsgis))
    (hSched : scheduleEffectiveOnCore st3 c = .ok st') :
    timerTickOnCore st c = .ok (st', (timerTickOnCorePrepared st c).2.1 ++ tsgis) := by
  rw [timerTickOnCore_eq_prepared]
  simp only [hCur, hTcb, hBud, if_true, hSched]

/-- WS-SM SM5.D.2 (preservation): the per-core timer tick preserves the RobinHood
object-store invariant (`objects.invExt`) through the whole composition — the
SM5.D.9 clear (object-neutral), the SM5.D.4 replenishment (preserves), the SM5.D.6
domain decrement (object-neutral), the SM5.D.5 budget tick (preserves, incl. the
IPC-timeout chain), and the reschedule (preserves).  Matches the SM5.B/C
object-store-invariant parity for the security-critical structural invariant. -/
theorem timerTickOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind)) (hInv : st.objects.invExt)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) : st'.objects.invExt := by
  have hPrep : (timerTickOnCorePrepared st c).1.objects.invExt :=
    timerTickOnCorePrepared_objects_invExt st c hInv
  rw [timerTickOnCore_eq_prepared] at hStep
  split at hStep
  · -- idle arm: the prepared state, or the round-7 local-wake reschedule
    split at hStep
    · -- local replenish wake: handleRescheduleSgiOnCore on the prepared state
      split at hStep
      · simp at hStep
      · rename_i st2 hHandle
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst
        exact handleRescheduleSgiOnCore_preserves_objects_invExt _ c _ hPrep hHandle
    · -- quiet idle: result is the prepared state
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨hst, _⟩ := hStep; rw [← hst]; exact hPrep
  · split at hStep
    · split at hStep
      · -- budget tick `.error` (unreachable: contradicts `.ok`)
        simp at hStep
      · -- budget tick `.ok (st3, preempted)`
        rename_i st3 b tsgis hbud
        have h3 : st3.objects.invExt :=
          timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrep hbud
        split at hStep
        · -- preempted: scheduleEffectiveOnCore
          split at hStep
          · simp at hStep
          · rename_i st4 hsched
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            exact scheduleEffectiveOnCore_preserves_objects_invExt _ c _ h3 hsched
        · -- not preempted: the round-7 local-wake reschedule, or identity
          split at hStep
          · -- local replenish wake: handleRescheduleSgiOnCore on the charged state
            split at hStep
            · simp at hStep
            · rename_i st4 hHandle
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨hst, _⟩ := hStep; subst hst
              exact handleRescheduleSgiOnCore_preserves_objects_invExt _ c _ h3 hHandle
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst; exact h3
    · simp at hStep

-- ============================================================================
-- §6  SM5.D.8 — Tick decidability (for the SM5.D.10 unit tests)
-- ============================================================================

/-- WS-SM SM5.D.8: does the per-core tick succeed (return `.ok`) on `(st, c)`?
Decidable by structural case analysis on the `Except` result (Lean core does not
derive `DecidableEq` on the `SystemState`-carrying `Except`, so the predicate
examines only the constructor).  Lets the SM5.D.10 unit tests `decide` whether a
concrete tick scenario succeeds. -/
def timerTickOnCoreSucceeds (st : SystemState) (c : CoreId) : Prop :=
  match timerTickOnCore st c with
  | .ok _ => True
  | .error _ => False

instance (st : SystemState) (c : CoreId) : Decidable (timerTickOnCoreSucceeds st c) := by
  unfold timerTickOnCoreSucceeds
  cases timerTickOnCore st c <;> simp <;> infer_instance

/-- WS-SM SM5.D.8: does the per-core tick emit at least one cross-core SGI (a
remote-targeted CBS replenish wake)?  Decidable. -/
def timerTickOnCoreEmitsSgi (st : SystemState) (c : CoreId) : Prop :=
  match timerTickOnCore st c with
  | .ok (_, sgis) => sgis ≠ []
  | .error _ => False

instance (st : SystemState) (c : CoreId) : Decidable (timerTickOnCoreEmitsSgi st c) := by
  unfold timerTickOnCoreEmitsSgi
  cases timerTickOnCore st c with
  | error _ => simp; infer_instance
  | ok r => cases r; simp; infer_instance

/-- WS-SM SM5.D.8: does the per-core budget tick preempt the current thread (the
`wasPreempted` flag)?  Decidable. -/
def timerTickBudgetOnCorePreempts (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : Prop :=
  match timerTickBudgetOnCore st c tid tcb with
  | .ok (_, b, _) => b = true
  | .error _ => False

instance (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    Decidable (timerTickBudgetOnCorePreempts st c tid tcb) := by
  unfold timerTickBudgetOnCorePreempts
  cases timerTickBudgetOnCore st c tid tcb with
  | error _ => simp; infer_instance
  | ok r => cases r; simp; infer_instance
-- ============================================================================
-- §7  SM5.D.5/.6 — per-core invariant preservation (the SM5.C-parity coverage)
--
--   The composed `timerTickOnCore` preserves the SM4.C per-core scheduler
--   invariants.  `currentThreadValidOnCore` is preserved UNCONDITIONALLY (the
--   preempted branch re-establishes it via `scheduleEffectiveOnCore`, the
--   not-preempted branch is a clean budget tick that keeps the charged thread a
--   TCB).  `runQueueOnCoreWellFormed` (B2) and `queueCurrentConsistentOnCore` are
--   preserved modulo a single clean hypothesis on the budget tick / prepared
--   state: the *bound-budget-exhausted* timeout branch re-enqueues timed-out
--   threads through the bootCoreId-pinned `ensureRunnable` /
--   `revertPriorityInheritance` (SM5.F per-core PIP migration, tracked debt), so
--   its per-core run-queue effect is not yet provable here.  Every clean path
--   (idle, unbound time-slice, bound budget-not-exhausted, replenishment, domain
--   rotation, reschedule) is discharged unconditionally.
-- ============================================================================

-- ── §7a  `decrementDomainTimeOnCore` (pure domain-slot write) frames the four ──

/-- WS-SM SM5.D.6 (preservation): the per-core domain decrement preserves per-core
current-thread validity — it writes only domain slots, leaving `current` /
`objects` untouched. -/
theorem decrementDomainTimeOnCore_preserves_currentThreadValidOnCore
    (st : SystemState) (c c' : CoreId) (h : currentThreadValidOnCore st c') :
    currentThreadValidOnCore (decrementDomainTimeOnCore st c) c' := by
  unfold currentThreadValidOnCore at h ⊢
  simp only [decrementDomainTimeOnCore_currentOnCore, SystemState.getTcb?,
    decrementDomainTimeOnCore_objects_eq] at h ⊢
  exact h

/-- WS-SM SM5.D.6 (preservation): the per-core domain decrement preserves per-core
dequeue-on-dispatch consistency. -/
theorem decrementDomainTimeOnCore_preserves_queueCurrentConsistentOnCore
    (st : SystemState) (c c' : CoreId) (h : queueCurrentConsistentOnCore st.scheduler c') :
    queueCurrentConsistentOnCore (decrementDomainTimeOnCore st c).scheduler c' := by
  unfold queueCurrentConsistentOnCore at h ⊢
  simp only [decrementDomainTimeOnCore_currentOnCore, decrementDomainTimeOnCore_runQueueOnCore] at h ⊢
  exact h

/-- WS-SM SM5.D.6 (preservation): the per-core domain decrement preserves per-core
runnable-threads-are-TCBs. -/
theorem decrementDomainTimeOnCore_preserves_runnableThreadsAreTCBsOnCore
    (st : SystemState) (c c' : CoreId) (h : runnableThreadsAreTCBsOnCore st c') :
    runnableThreadsAreTCBsOnCore (decrementDomainTimeOnCore st c) c' := by
  unfold runnableThreadsAreTCBsOnCore at h ⊢
  simp only [decrementDomainTimeOnCore_runQueueOnCore, SystemState.getTcb?,
    decrementDomainTimeOnCore_objects_eq] at h ⊢
  exact h

/-- WS-SM SM5.D.6 (preservation, B2): the per-core domain decrement preserves
per-core run-queue well-formedness. -/
theorem decrementDomainTimeOnCore_preserves_runQueueOnCoreWellFormed
    (st : SystemState) (c c' : CoreId) (h : runQueueOnCoreWellFormed st.scheduler c') :
    runQueueOnCoreWellFormed (decrementDomainTimeOnCore st c).scheduler c' := by
  unfold runQueueOnCoreWellFormed at h ⊢
  simp only [decrementDomainTimeOnCore_runQueueOnCore] at h ⊢
  exact h

-- ── §7b  `saveOutgoingContextOnCore` frame lemmas ──

/-- WS-SM SM5.D.5 (frame): the per-core register-context save touches only the
object store; the scheduler is unchanged. -/
theorem saveOutgoingContextOnCore_scheduler_eq (st : SystemState) (c : CoreId) :
    (saveOutgoingContextOnCore st c).scheduler = st.scheduler := by
  simp only [saveOutgoingContextOnCore]
  split
  · rfl
  · split <;> rfl

/-- WS-SM SM5.D.5 (frame): the per-core register-context save preserves
TCB-resolvability of any thread — its only write replaces the outgoing thread's
TCB with the same TCB plus a fresh register context (still a TCB), and any other
key is untouched.  AK7-clean (`.get?` method form). -/
theorem saveOutgoingContextOnCore_getTcb?_isSome (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (h : ∃ t, st.getTcb? tid = some t) :
    ∃ t, (saveOutgoingContextOnCore st c).getTcb? tid = some t := by
  cases hcur : st.scheduler.currentOnCore c with
  | none => rw [show saveOutgoingContextOnCore st c = st from by
      simp only [saveOutgoingContextOnCore, hcur]]; exact h
  | some outTid =>
    cases hout : st.getTcb? outTid with
    | none => rw [show saveOutgoingContextOnCore st c = st from by
        simp only [saveOutgoingContextOnCore, hcur, hout]]; exact h
    | some outTcb =>
      obtain ⟨t, ht⟩ := h
      by_cases hEq : tid = outTid
      · subst hEq
        refine ⟨{ outTcb with registerContext := st.machine.regsOnCore c }, ?_⟩
        simp only [saveOutgoingContextOnCore, hcur, hout]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
      · refine ⟨t, ?_⟩
        have hNeO : ¬ (outTid.toObjId == tid.toObjId) = true := fun he =>
          hEq (ThreadId.toObjId_injective _ _ (by simpa using he)).symm
        simp only [saveOutgoingContextOnCore, hcur, hout]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects outTid.toObjId tid.toObjId
          _ hNeO hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using ht

/-- WS-SM SM5.I (register-bank sibling-frame foundation): `saveOutgoingContextOnCore`
on core `c₀` either leaves a thread's saved register context **unchanged**, or —
when that thread is exactly core `c₀`'s outgoing current — sets it to
`machine.regsOnCore c₀`.  This is the only `registerContext` write any per-core
transition makes; the dispatch sibling `contextMatchesCurrentOnCore` frame uses it
together with the pre-state `contextMatchesCurrentOnCore c₀` to show the write is
`==`-idempotent on a thread (pathologically) current on two cores. -/
theorem saveOutgoingContextOnCore_getTcb?_regContext (st : SystemState) (c₀ : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (htcb : st.getTcb? tid = some tcb) :
    ∃ tcb', (saveOutgoingContextOnCore st c₀).getTcb? tid = some tcb' ∧
      (tcb'.registerContext = tcb.registerContext ∨
        (st.scheduler.currentOnCore c₀ = some tid ∧
          tcb'.registerContext = st.machine.regsOnCore c₀)) := by
  cases hcur : st.scheduler.currentOnCore c₀ with
  | none =>
      refine ⟨tcb, ?_, Or.inl rfl⟩
      rw [show saveOutgoingContextOnCore st c₀ = st from by
        simp only [saveOutgoingContextOnCore, hcur]]; exact htcb
  | some outTid =>
      cases hout : st.getTcb? outTid with
      | none =>
          refine ⟨tcb, ?_, Or.inl rfl⟩
          rw [show saveOutgoingContextOnCore st c₀ = st from by
            simp only [saveOutgoingContextOnCore, hcur, hout]]; exact htcb
      | some outTcb =>
          by_cases hEq : tid = outTid
          · subst hEq
            refine ⟨{ outTcb with registerContext := st.machine.regsOnCore c₀ }, ?_, ?_⟩
            · simp only [saveOutgoingContextOnCore, hcur, hout]
              simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
              rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
            · exact Or.inr ⟨rfl, rfl⟩
          · refine ⟨tcb, ?_, Or.inl rfl⟩
            have hNeO : ¬ (outTid.toObjId == tid.toObjId) = true := fun he =>
              hEq (ThreadId.toObjId_injective _ _ (by simpa using he)).symm
            simp only [saveOutgoingContextOnCore, hcur, hout]
            simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
            rw [RobinHood.RHTable.getElem?_insert_ne st.objects outTid.toObjId tid.toObjId
              _ hNeO hInv]
            simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using htcb

-- ── §7c  `scheduleEffectiveOnCore` preservation / establishment ──

/-- WS-SM SM5.D.5 (object frame): in every OK branch (idle dispatch and
thread dispatch), `scheduleEffectiveOnCore` writes the object store only through
`saveOutgoingContextOnCore` — the dequeue / restore / set-current steps are
object-neutral. -/
theorem scheduleEffectiveOnCore_objects_eq (st : SystemState) (c : CoreId)
    (st' : SystemState) (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.objects = (saveOutgoingContextOnCore st c).objects := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      rw [idleFallbackOnCore_objects]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          simp only [restoreIncomingContextOnCore_objects]
        · simp at hStep

/-- WS-SM SM5.D.5 (frame): `scheduleEffectiveOnCore` preserves TCB-resolvability of
any thread (its only object write is the outgoing register-context save). -/
theorem scheduleEffectiveOnCore_getTcb?_isSome (st : SystemState) (c : CoreId)
    (st' : SystemState) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') (h : ∃ t, st.getTcb? tid = some t) :
    ∃ t, st'.getTcb? tid = some t := by
  have hobj := scheduleEffectiveOnCore_objects_eq st c st' hStep
  have : st'.getTcb? tid = (saveOutgoingContextOnCore st c).getTcb? tid := by
    simp only [SystemState.getTcb?, hobj]
  rw [this]; exact saveOutgoingContextOnCore_getTcb?_isSome st c tid hInv h

/-- WS-SM SM5.D.5 (preservation, B2): `scheduleEffectiveOnCore` preserves per-core
run-queue well-formedness — the dispatch case dequeues (`remove`) the selected
thread (`remove_preserves_wellFormed`); the idle case leaves the run queue. -/
theorem scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed (st : SystemState)
    (c : CoreId) (st' : SystemState) (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hStep : scheduleEffectiveOnCore st c = .ok st') :
    (st'.scheduler.runQueueOnCore c).wellFormed := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      apply idleFallbackOnCore_preserves_runQueueOnCoreWellFormed
      rw [saveOutgoingContextOnCore_scheduler_eq]; exact hwf
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
            restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          rw [saveOutgoingContextOnCore_scheduler_eq]
          exact RunQueue.remove_preserves_wellFormed _ hwf tid
        · simp at hStep

/-- WS-SM SM5.D.5 (invariant established): after a successful per-core reschedule,
core `c` satisfies `currentThreadValidOnCore` — the dispatched thread resolves to a
TCB (the dispatch requires it; the idle case sets `current = none`).  Mirror of
SM5.B's `switchToThreadOnCore_establishes_currentThreadValidOnCore`. -/
theorem scheduleEffectiveOnCore_establishes_currentThreadValidOnCore (st : SystemState)
    (c : CoreId) (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') :
    currentThreadValidOnCore st' c := by
  have hCopy := hStep
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      exact idleFallbackOnCore_establishes_currentThreadValidOnCore _ c
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          unfold currentThreadValidOnCore
          simp only [SchedulerState.setCurrentOnCore_currentOnCore_self]
          exact scheduleEffectiveOnCore_getTcb?_isSome st c _ tid hInv hCopy ⟨tcb, hTcb⟩
        · simp at hStep

/-- WS-SM SM5.D.6 (preservation): `scheduleDomainOnCore` preserves per-core
current-thread validity.  On a domain boundary the re-dispatch *establishes*
validity outright (`scheduleEffectiveOnCore_establishes_currentThreadValidOnCore`,
under `invExt` carried through the switch); the in-domain decrement frames the
current slot and the store
(`decrementDomainTimeOnCore_preserves_currentThreadValidOnCore`).  This is the
composition lemma the live run-loop step (`perCoreTimerTickStep`) consumes now
that the SM5.I run loop genuinely invokes `timerTickOnCore` **then**
`scheduleDomainOnCore`, as the tick's own docstring always required. -/
theorem scheduleDomainOnCore_preserves_currentThreadValidOnCore (st : SystemState)
    (c : CoreId) (st' : SystemState) (hInv : st.objects.invExt)
    (hValid : currentThreadValidOnCore st c)
    (hStep : scheduleDomainOnCore st c = .ok st') :
    currentThreadValidOnCore st' c := by
  unfold scheduleDomainOnCore at hStep
  split at hStep
  · -- single-domain mode: the domain tick is the identity.
    simp only [Except.ok.injEq] at hStep; subst hStep; exact hValid
  · -- non-empty schedule.
    split at hStep
    · -- boundary: the re-dispatch *establishes* validity on the switched state
      -- (whose store is the context-saved one, `invExt`-preserved).
      split at hStep
      · simp at hStep
      · rename_i st'' hsw
        exact scheduleEffectiveOnCore_establishes_currentThreadValidOnCore st'' c st'
          (switchDomainOnCore_preserves_objects_invExt st c st'' hInv hsw) hStep
    · -- non-boundary: pure domain-time decrement.
      simp only [Except.ok.injEq] at hStep; subst hStep
      exact decrementDomainTimeOnCore_preserves_currentThreadValidOnCore st c c hValid

/-- WS-SM SM5.D.5 (invariant established): after a successful per-core reschedule,
core `c` satisfies `queueCurrentConsistentOnCore` — the dispatched thread is
dequeued-on-dispatch (`not_mem_remove_toList`), so it is not in core `c`'s run
queue; the idle case sets `current = none`. -/
theorem scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore (st : SystemState)
    (c : CoreId) (st' : SystemState) (hStep : scheduleEffectiveOnCore st c = .ok st') :
    queueCurrentConsistentOnCore st'.scheduler c := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      exact idleFallbackOnCore_establishes_queueCurrentConsistentOnCore _ c
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          unfold queueCurrentConsistentOnCore
          simp only [SchedulerState.setCurrentOnCore_currentOnCore_self,
            SchedulerState.setCurrentOnCore_runQueueOnCore, restoreIncomingContextOnCore_scheduler,
            SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          rw [saveOutgoingContextOnCore_scheduler_eq]
          exact RunQueue.not_mem_remove_toList _ tid
        · simp at hStep

/-- WS-SM SM5.I (register-bank payoff, dispatch post-state): the canonical
"restore `tid`'s context then set it current" post-state satisfies
`contextMatchesCurrentOnCore` whenever `tid` resolves to a TCB in the (already
context-saved + dequeued) state.  Both the bank value and `getTcb? tid` are read
from the *same* dequeued state via the per-core restore, so they agree by
construction — no `tid ≠ outgoing` side condition is needed (the self-reschedule
case is covered too).  Shared by `switchToThreadOnCore` and
`scheduleEffectiveOnCore`'s dispatch branches. -/
theorem restoreThenSetCurrent_establishes_contextMatchesCurrentOnCore
    (stDeq : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (deqTcb : TCB)
    (hTcb : stDeq.getTcb? tid = some deqTcb) :
    contextMatchesCurrentOnCore
      { restoreIncomingContextOnCore stDeq c tid with
        scheduler :=
          (restoreIncomingContextOnCore stDeq c tid).scheduler.setCurrentOnCore c (some tid) } c := by
  unfold contextMatchesCurrentOnCore
  simp only [SchedulerState.setCurrentOnCore_currentOnCore_self]
  -- `getTcb? tid` is read through the scheduler-only record update + the
  -- object-preserving restore, so it resolves to `deqTcb` (from `hTcb`, typed).
  have hgt : ({ restoreIncomingContextOnCore stDeq c tid with
      scheduler := (restoreIncomingContextOnCore stDeq c tid).scheduler.setCurrentOnCore c
        (some tid) } : SystemState).getTcb? tid = some deqTcb := by
    show (restoreIncomingContextOnCore stDeq c tid).getTcb? tid = some deqTcb
    rw [restoreIncomingContextOnCore_getTcb?]; exact hTcb
  rw [hgt]
  -- the per-core restore wrote core `c`'s bank to `deqTcb.registerContext`.
  have hregs : ({ restoreIncomingContextOnCore stDeq c tid with
      scheduler := (restoreIncomingContextOnCore stDeq c tid).scheduler.setCurrentOnCore c
        (some tid) } : SystemState).machine.regsOnCore c = deqTcb.registerContext := by
    show (restoreIncomingContextOnCore stDeq c tid).machine.regsOnCore c = deqTcb.registerContext
    exact restoreIncomingContextOnCore_regsOnCore_self stDeq c tid deqTcb hTcb
  rw [hregs]
  exact RegisterFile.beq_self _

/-- WS-SM SM5.I (the register-bank payoff, dispatch): a successful per-core
budget-aware reschedule **establishes** `contextMatchesCurrentOnCore` on the
operated core — after the dispatch, core `c`'s register bank holds its new current
thread's context.  This is the dispatch-transition keystone the SM5.I.8
"preservation by every transition" obligation rests on: with the SM4.B per-core
register banks, the per-core dispatch makes the match hold on the dispatched core
*regardless of the other cores*, where a single shared register file admitted the
match on at most one core.  The idle branch is discharged by
`idleFallbackOnCore_establishes_contextMatchesCurrentOnCore`. -/
theorem scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') :
    contextMatchesCurrentOnCore st' c := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      exact idleFallbackOnCore_establishes_contextMatchesCurrentOnCore _ c
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          -- `tid` resolves to a TCB in the context-saved (hence dequeued) state
          -- (typed `getTcb?` form — AK7-clean, no raw `[·]?` derivation needed).
          obtain ⟨deqTcb, hDeqGt⟩ :=
            saveOutgoingContextOnCore_getTcb?_isSome st c tid hInv ⟨tcb, hTcb⟩
          exact restoreThenSetCurrent_establishes_contextMatchesCurrentOnCore _ c tid deqTcb hDeqGt
        · simp at hStep

/-- WS-SM SM5.D.5 (frame): every thread in `scheduleEffectiveOnCore`'s post run
queue was in the pre run queue (the dispatch dequeues, the idle case is the
identity). -/
theorem scheduleEffectiveOnCore_runQueue_toList_subset (st : SystemState) (c : CoreId)
    (st' : SystemState) (hStep : scheduleEffectiveOnCore st c = .ok st')
    (x : SeLe4n.ThreadId) (hx : x ∈ (st'.scheduler.runQueueOnCore c).toList) :
    x ∈ (st.scheduler.runQueueOnCore c).toList := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      rw [RunQueue.mem_toList_iff_mem] at hx ⊢
      have hm := idleFallbackOnCore_runQueueOnCore_mem _ c x hx
      rwa [saveOutgoingContextOnCore_scheduler_eq] at hm
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
            restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at hx
          rw [saveOutgoingContextOnCore_scheduler_eq] at hx
          rw [RunQueue.mem_toList_iff_mem] at hx ⊢
          exact (RunQueue.mem_remove _ tid x |>.mp hx).1
        · simp at hStep

/-- WS-SM SM5.D.5 (preservation): `scheduleEffectiveOnCore` preserves per-core
runnable-threads-are-TCBs — its post run queue is a subset of the pre run queue,
and it preserves TCB-resolvability of every thread. -/
theorem scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore (st : SystemState)
    (c : CoreId) (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st')
    (h : runnableThreadsAreTCBsOnCore st c) :
    runnableThreadsAreTCBsOnCore st' c := by
  intro x hx
  exact scheduleEffectiveOnCore_getTcb?_isSome st c st' x hInv hStep
    (h x (scheduleEffectiveOnCore_runQueue_toList_subset st c st' hStep x hx))

-- ── §7d  `timerTickBudgetOnCore` clean (not-preempted) frame lemmas ──

/-- WS-SM SM5.D.5 (frame): a *not-preempted* budget tick (unbound time-slice not
expired, or bound budget not exhausted) writes only the object store; the
scheduler is unchanged. -/
theorem timerTickBudgetOnCore_notPreempted_scheduler_eq (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', false, sgis)) :
    st'.scheduler = st.scheduler := by
  cases hb : tcb.schedContextBinding with
  | unbound =>
    by_cases hsl : tcb.timeSlice ≤ 1
    · simp only [timerTickBudgetOnCore, hb, if_pos hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      exact absurd hStep.2.1 (by decide)
    · simp only [timerTickBudgetOnCore, hb, if_neg hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      rw [← hStep.1]
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        rw [← hStep.1]
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        rw [← hStep.1]

/-- WS-SM SM5.D.5 (frame): a not-preempted budget tick keeps the charged thread
`tid` a TCB.  Unbound: writes `tid`'s TCB with a decremented time-slice.  Bound:
writes the SchedContext at `scId` — a *different* key from `tid` (both lookups
succeed, so the keys are distinct), leaving `tid`'s TCB untouched.  AK7-clean. -/
theorem timerTickBudgetOnCore_notPreempted_getTcb?_tid (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (hInv : st.objects.invExt)
    (hCur : st.getTcb? tid = some tcb)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', false, sgis)) :
    ∃ t, st'.getTcb? tid = some t := by
  have hDisj : ∀ scId : SeLe4n.SchedContextId, (∃ s, st.getSchedContext? scId = some s) →
      ¬ (scId.toObjId == tid.toObjId) = true := by
    rintro scId ⟨s, hSc⟩ he
    have he' : scId.toObjId = tid.toObjId := by simpa using he
    simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?] at hCur
    simp only [SystemState.getSchedContext?, RHTable_getElem?_eq_get?] at hSc
    rw [he'] at hSc
    revert hCur hSc; cases st.objects.get? tid.toObjId with
    | none => simp
    | some o => cases o <;> simp
  cases hb : tcb.schedContextBinding with
  | unbound =>
    by_cases hsl : tcb.timeSlice ≤ 1
    · simp only [timerTickBudgetOnCore, hb, if_pos hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      exact absurd hStep.2.1 (by decide)
    · simp only [timerTickBudgetOnCore, hb, if_neg hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      rw [← hStep.1]
      simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?,
        RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
      exact ⟨_, rfl⟩
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        refine ⟨tcb, ?_⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hCur
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        refine ⟨tcb, ?_⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hCur

-- ── §7e  Composed `timerTickOnCore` invariant preservation ──

/-- WS-SM SM5.D.5/.6 (the headline B1 preservation): the per-core timer tick
preserves per-core current-thread validity, **UNCONDITIONALLY**.  Three cases:
the idle path leaves `current = none` (vacuously valid); the not-preempted budget
tick keeps the charged current thread a TCB
(`timerTickBudgetOnCore_notPreempted_getTcb?_tid`); the preempted path
re-establishes validity from scratch via
`scheduleEffectiveOnCore_establishes_currentThreadValidOnCore` (needing only the
budget-tick result's object-store `invExt`, which `timerTickBudgetOnCore`
preserves).  The bound-budget-exhausted timeout's effect on the object store is
absorbed by the re-establishment, so no timeout hypothesis is needed here. -/
theorem timerTickOnCore_preserves_currentThreadValidOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind)) (hInv : st.objects.invExt)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    currentThreadValidOnCore st' c := by
  have hPrepInv : (timerTickOnCorePrepared st c).1.objects.invExt :=
    timerTickOnCorePrepared_objects_invExt st c hInv
  rw [timerTickOnCore_eq_prepared] at hStep
  cases hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c with
  | none =>
    simp only [hCur] at hStep
    have hVPrep : currentThreadValidOnCore (timerTickOnCorePrepared st c).1 c := by
      simp [currentThreadValidOnCore, hCur]
    split at hStep
    · -- local replenish wake (PR #880 round 7): handler on the prepared state
      cases hH : handleRescheduleSgiOnCore (timerTickOnCorePrepared st c).1 c with
      | error e => simp [hH] at hStep
      | ok st2 =>
        simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨h1, _⟩ := hStep
        rw [← h1]
        exact handleRescheduleSgiOnCore_preserves_currentThreadValidOnCore _ c st2 hPrepInv hVPrep hH
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨h1, _⟩ := hStep
      rw [← h1]; exact hVPrep
  | some tid =>
    simp only [hCur] at hStep
    cases hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid with
    | none => simp [hTcb] at hStep
    | some tcb =>
      simp only [hTcb] at hStep
      cases hbud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb with
      | error e => simp [hbud] at hStep
      | ok r =>
        obtain ⟨st3, preempted, tsgis⟩ := r
        simp only [hbud] at hStep
        split at hStep
        · -- preempted: re-select + dispatch via scheduleEffectiveOnCore
          cases hsch : scheduleEffectiveOnCore st3 c with
          | error e => simp [hsch] at hStep
          | ok st4 =>
            simp only [hsch, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]
            exact scheduleEffectiveOnCore_establishes_currentThreadValidOnCore st3 c st4
              (timerTickBudgetOnCore_preserves_objects_invExt (timerTickOnCorePrepared st c).1 c tid
                tcb st3 preempted hPrepInv hbud) hsch
        · -- not preempted: the charged thread stays current and a TCB — and the
          -- round-7 local-wake reschedule (when the drain woke locally) preserves
          -- validity through the handler
          rename_i hpre
          have hpf : preempted = false := Bool.not_eq_true _ |>.mp hpre
          subst hpf
          have hV3 : currentThreadValidOnCore st3 c := by
            simp only [currentThreadValidOnCore,
              timerTickBudgetOnCore_notPreempted_scheduler_eq (timerTickOnCorePrepared st c).1 c tid tcb st3 hbud, hCur]
            exact timerTickBudgetOnCore_notPreempted_getTcb?_tid (timerTickOnCorePrepared st c).1 c tid tcb st3 hPrepInv hTcb hbud
          split at hStep
          · cases hH : handleRescheduleSgiOnCore st3 c with
            | error e => simp [hH] at hStep
            | ok st4 =>
              simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨h1, _⟩ := hStep
              rw [← h1]
              exact handleRescheduleSgiOnCore_preserves_currentThreadValidOnCore st3 c st4
                (timerTickBudgetOnCore_preserves_objects_invExt (timerTickOnCorePrepared st c).1 c tid
                  tcb st3 false hPrepInv hbud)
                hV3 hH
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]; exact hV3
/-- WS-SM SM5.D.2 (B2 helper): the prepared state preserves per-core run-queue
well-formedness — the SM5.D.4 replenishment preserves it (wakes `insert`); the tick
does no in-tick domain step (audit-pass-2). -/
theorem timerTickOnCorePrepared_runQueueOnCore_wellFormed (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed) :
    ((timerTickOnCorePrepared st c).1.scheduler.runQueueOnCore c).wellFormed := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_runQueueOnCore_wellFormed
  simpa only [SchedulerState.setLastTimeoutErrorsOnCore_runQueueOnCore] using hwf

-- ── §6c  Prepared-phase (cross-core replenishment-wake) discharge of the
--          per-core invariant conjuncts [SM5.I] — `queueCurrentConsistent` ──

/-- A thread not running on **any** core is not the current thread of any
particular core (the elementwise reading of `runningOnSomeCore = false`). -/
theorem runningOnSomeCore_eq_false_currentOnCore_ne {st : SystemState}
    {tid : SeLe4n.ThreadId} (h : runningOnSomeCore st tid = false) (c : CoreId) :
    st.scheduler.currentOnCore c ≠ some tid := by
  simp only [runningOnSomeCore, SeLe4n.Kernel.Concurrency.allCores, List.any_eq_false] at h
  intro hc
  have hcc := h c (List.mem_finRange c)
  rw [hc] at hcc
  simp at hcc

/-- `processOneReplenishmentOnCore` preserves dequeue-on-dispatch consistency on
**every** core `c'`: the refill frames the scheduler, and the wake fires only when
the woken thread is not running anywhere (so it is not `c'`'s current thread) —
exactly `wakeThread_preserves_queueCurrentConsistentOnCore`'s precondition. -/
theorem processOneReplenishmentOnCore_preserves_queueCurrentConsistentOnCore (st : SystemState)
    (execCore c' : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hcons : queueCurrentConsistentOnCore st.scheduler c') :
    queueCurrentConsistentOnCore (processOneReplenishmentOnCore st execCore scId now).1.scheduler c' := by
  have hRef : queueCurrentConsistentOnCore (refillSchedContext st scId now).scheduler c' := by
    rw [refillSchedContext_scheduler_eq]; exact hcons
  simp only [processOneReplenishmentOnCore]
  split
  next tid _heq =>
    split
    next _hrun => exact hRef
    next hcond =>
      exact wakeThread_preserves_queueCurrentConsistentOnCore (refillSchedContext st scId now)
        tid execCore c'
        (runningOnSomeCore_eq_false_currentOnCore_ne (Bool.not_eq_true _ |>.mp hcond) _) hRef
  next _heq => exact hRef

private theorem foldl_processOneReplenishment_preserves_queueCurrentConsistentOnCore
    (dueIds : List SeLe4n.SchedContextId) (c c' : CoreId) (now : Nat)
    (acc : SystemState × List (CoreId × SgiKind) × Bool)
    (hcons : queueCurrentConsistentOnCore acc.1.scheduler c') :
    queueCurrentConsistentOnCore
      (dueIds.foldl (fun acc scId =>
        let r := processOneReplenishmentOnCore acc.1 c scId now
        (r.1, acc.2.1 ++ r.2.1.toList, acc.2.2 || r.2.2)) acc).1.scheduler c' := by
  induction dueIds generalizing acc with
  | nil => exact hcons
  | cons hd tl ih =>
      rw [List.foldl_cons]
      exact ih _ (processOneReplenishmentOnCore_preserves_queueCurrentConsistentOnCore
        acc.1 c c' hd now hcons)

/-- WS-SM SM5.I.8 (prepared discharge): `processReplenishmentsDueOnCore` preserves
dequeue-on-dispatch consistency on core `c`. -/
theorem processReplenishmentsDueOnCore_preserves_queueCurrentConsistentOnCore (st : SystemState)
    (c : CoreId) (now : Nat) (hcons : queueCurrentConsistentOnCore st.scheduler c) :
    queueCurrentConsistentOnCore (processReplenishmentsDueOnCore st c now).1.scheduler c := by
  simp only [processReplenishmentsDueOnCore]
  apply foldl_processOneReplenishment_preserves_queueCurrentConsistentOnCore
  simpa only [queueCurrentConsistentOnCore, SchedulerState.setReplenishQueueOnCore_currentOnCore,
    SchedulerState.setReplenishQueueOnCore_runQueueOnCore] using hcons

/-- WS-SM SM5.I.8 (prepared discharge): the prepared phase preserves
`queueCurrentConsistentOnCore` — discharges the capstone's `hPrepQcc`. -/
theorem timerTickOnCorePrepared_preserves_queueCurrentConsistentOnCore (st : SystemState)
    (c : CoreId) (hcons : queueCurrentConsistentOnCore st.scheduler c) :
    queueCurrentConsistentOnCore (timerTickOnCorePrepared st c).1.scheduler c := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_queueCurrentConsistentOnCore
  simpa only [queueCurrentConsistentOnCore, SchedulerState.setLastTimeoutErrorsOnCore_currentOnCore,
    SchedulerState.setLastTimeoutErrorsOnCore_runQueueOnCore] using hcons

-- ── §6d  Prepared-phase discharge — `runQueueUnique` (Nodup) ──

/-- `processOneReplenishmentOnCore` preserves run-queue `Nodup` on every core `c'`
(refill frames the scheduler; the wake's `RunQueue.insert` preserves `Nodup`). -/
theorem processOneReplenishmentOnCore_preserves_runQueueUnique (st : SystemState)
    (execCore c' : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hnd : (st.scheduler.runQueueOnCore c').toList.Nodup) :
    ((processOneReplenishmentOnCore st execCore scId now).1.scheduler.runQueueOnCore c').toList.Nodup := by
  have hRef : ((refillSchedContext st scId now).scheduler.runQueueOnCore c').toList.Nodup := by
    rw [refillSchedContext_scheduler_eq]; exact hnd
  simp only [processOneReplenishmentOnCore]
  split
  next tid _heq =>
    split
    next _hrun => exact hRef
    next _hcond =>
      exact wakeThread_preserves_runQueueUniqueOnCore (refillSchedContext st scId now)
        tid execCore c' hRef
  next _heq => exact hRef

private theorem foldl_processOneReplenishment_preserves_runQueueUnique
    (dueIds : List SeLe4n.SchedContextId) (c c' : CoreId) (now : Nat)
    (acc : SystemState × List (CoreId × SgiKind) × Bool)
    (hnd : (acc.1.scheduler.runQueueOnCore c').toList.Nodup) :
    ((dueIds.foldl (fun acc scId =>
        let r := processOneReplenishmentOnCore acc.1 c scId now
        (r.1, acc.2.1 ++ r.2.1.toList, acc.2.2 || r.2.2)) acc).1.scheduler.runQueueOnCore c').toList.Nodup := by
  induction dueIds generalizing acc with
  | nil => exact hnd
  | cons hd tl ih =>
      rw [List.foldl_cons]
      exact ih _ (processOneReplenishmentOnCore_preserves_runQueueUnique acc.1 c c' hd now hnd)

/-- WS-SM SM5.I.8 (prepared discharge): `processReplenishmentsDueOnCore` preserves
run-queue `Nodup` on core `c`. -/
theorem processReplenishmentsDueOnCore_preserves_runQueueUnique (st : SystemState)
    (c : CoreId) (now : Nat) (hnd : (st.scheduler.runQueueOnCore c).toList.Nodup) :
    ((processReplenishmentsDueOnCore st c now).1.scheduler.runQueueOnCore c).toList.Nodup := by
  simp only [processReplenishmentsDueOnCore]
  apply foldl_processOneReplenishment_preserves_runQueueUnique
  simpa only [SchedulerState.setReplenishQueueOnCore_runQueueOnCore] using hnd

/-- WS-SM SM5.I.8 (prepared discharge): the prepared phase preserves run-queue
`Nodup` — discharges the capstone's `hPrepNd`. -/
theorem timerTickOnCorePrepared_preserves_runQueueUnique (st : SystemState) (c : CoreId)
    (hnd : (st.scheduler.runQueueOnCore c).toList.Nodup) :
    ((timerTickOnCorePrepared st c).1.scheduler.runQueueOnCore c).toList.Nodup := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_runQueueUnique
  simpa only [SchedulerState.setLastTimeoutErrorsOnCore_runQueueOnCore] using hnd

/-- WS-SM SM5.D.5 (B2 discharge, clean path): a *not-preempted* budget tick
preserves per-core run-queue well-formedness — its scheduler is unchanged
(`timerTickBudgetOnCore_notPreempted_scheduler_eq`).  This discharges the B2
budget-tick hypothesis on every clean (non-budget-exhausted) path; the
bound-budget-exhausted branch's run-queue effect (the `timeoutBlockedThreads`
re-enqueue through the bootCoreId-pinned `ensureRunnable` /
`revertPriorityInheritance`) is the SM5.F per-core-PIP-migration tracked gap. -/
theorem timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCoreWellFormed
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', false, sgis)) :
    (st'.scheduler.runQueueOnCore c).wellFormed := by
  rw [timerTickBudgetOnCore_notPreempted_scheduler_eq st c tid tcb st' hStep]; exact hwf

/-- WS-SM SM5.D.5/.6 (B2 preservation): the per-core timer tick preserves per-core
run-queue well-formedness, given that the budget tick preserves it
(`hBudgetRqWf`).  The idle path is the prepared state (well-formed via
`timerTickOnCorePrepared_runQueueOnCore_wellFormed`); the not-preempted path is the
budget result; the preempted path dequeues-on-dispatch via
`scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed`.  `hBudgetRqWf` is
discharged unconditionally on every clean path by
`timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCoreWellFormed` (and, for
the unbound time-slice preemption, by `RunQueue.insert_preserves_wellFormed`); the
bound-budget-exhausted preemption's `timeoutBlockedThreads` re-enqueue is the SM5.F
tracked gap (the only case `hBudgetRqWf` is not yet provable here). -/
theorem timerTickOnCore_preserves_runQueueOnCoreWellFormed (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hBudgetRqWf : ∀ tid tcb st3 b sgis,
       (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
       (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb →
       timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b, sgis) →
       (st3.scheduler.runQueueOnCore c).wellFormed)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    (st'.scheduler.runQueueOnCore c).wellFormed := by
  have hPrep := timerTickOnCorePrepared_runQueueOnCore_wellFormed st c hwf
  rw [timerTickOnCore_eq_prepared] at hStep
  cases hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c with
  | none =>
    simp only [hCur] at hStep
    split at hStep
    · cases hH : handleRescheduleSgiOnCore (timerTickOnCorePrepared st c).1 c with
      | error e => simp [hH] at hStep
      | ok st2 =>
        simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨h1, _⟩ := hStep
        rw [← h1]
        exact handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed _ c st2 hPrep hH
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨h1, _⟩ := hStep
      rw [← h1]; exact hPrep
  | some tid =>
    simp only [hCur] at hStep
    cases hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid with
    | none => simp [hTcb] at hStep
    | some tcb =>
      simp only [hTcb] at hStep
      cases hbud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb with
      | error e => simp [hbud] at hStep
      | ok r =>
        obtain ⟨st3, preempted, tsgis⟩ := r
        simp only [hbud] at hStep
        have hst3 : (st3.scheduler.runQueueOnCore c).wellFormed :=
          hBudgetRqWf tid tcb st3 preempted tsgis hCur hTcb hbud
        split at hStep
        · cases hsch : scheduleEffectiveOnCore st3 c with
          | error e => simp [hsch] at hStep
          | ok st4 =>
            simp only [hsch, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]
            exact scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed st3 c st4 hst3 hsch
        · split at hStep
          · cases hH : handleRescheduleSgiOnCore st3 c with
            | error e => simp [hH] at hStep
            | ok st4 =>
              simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨h1, _⟩ := hStep
              rw [← h1]
              exact handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed st3 c st4 hst3 hH
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]; exact hst3

-- ── §7f  runnableThreadsAreTCBs per-core preservation [SM5.I] ──
--
--   The `runnableThreadsAreTCBsOnCore` conjunct.  `scheduleEffectiveOnCore`
--   already preserves it; the missing piece is the not-preempted budget tick,
--   which changes only the object store (the running thread's time-slice, or the
--   bound SchedContext's budget).  A getTcb?-forward frame shows every pre-state
--   TCB stays resolvable across that object write.

/-- A not-preempted budget tick keeps every pre-state TCB resolvable: its only
object write is the running thread's time-slice (a TCB→TCB update) or the bound
SchedContext's budget (a non-TCB slot, distinct from any TCB key). -/
theorem timerTickBudgetOnCore_notPreempted_getTcb?_forward (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (hInv : st.objects.invExt)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', false, sgis))
    (x : SeLe4n.ThreadId) (t : TCB) (hx : st.getTcb? x = some t) :
    ∃ t', st'.getTcb? x = some t' := by
  -- the bound/donated SchedContext key is distinct from any resolvable TCB key
  have hDisj : ∀ scId : SeLe4n.SchedContextId, (∃ s, st.getSchedContext? scId = some s) →
      ¬ (scId.toObjId == x.toObjId) = true := by
    rintro scId ⟨s, hSc⟩ he
    have he' : scId.toObjId = x.toObjId := by simpa using he
    simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?] at hx
    simp only [SystemState.getSchedContext?, RHTable_getElem?_eq_get?] at hSc
    rw [he'] at hSc
    revert hx hSc; cases st.objects.get? x.toObjId with
    | none => simp
    | some o => cases o <;> simp
  cases hb : tcb.schedContextBinding with
  | unbound =>
    by_cases hsl : tcb.timeSlice ≤ 1
    · simp only [timerTickBudgetOnCore, hb, if_pos hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      exact absurd hStep.2.1 (by decide)
    · simp only [timerTickBudgetOnCore, hb, if_neg hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      rw [← hStep.1]
      by_cases hxt : x = tid
      · subst hxt
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?,
          RobinHood.RHTable.getElem?_insert_self st.objects x.toObjId _ hInv]
        exact ⟨_, rfl⟩
      · have hNe : ¬ (tid.toObjId == x.toObjId) = true := fun he =>
          hxt (ThreadId.toObjId_injective _ _ (eq_of_beq he)).symm
        refine ⟨t, ?_⟩
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId x.toObjId _ hNe hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hx
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        refine ⟨t, ?_⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId x.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hx
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        refine ⟨t, ?_⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId x.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hx

/-- A not-preempted budget tick preserves per-core runnable-threads-are-TCBs: the
run queue is unchanged (scheduler frame) and every member stays resolvable. -/
theorem timerTickBudgetOnCore_notPreempted_preserves_runnableThreadsAreTCBsOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hInv : st.objects.invExt) (h : runnableThreadsAreTCBsOnCore st c)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', false, sgis)) :
    runnableThreadsAreTCBsOnCore st' c := by
  intro x hx
  have hsch := timerTickBudgetOnCore_notPreempted_scheduler_eq st c tid tcb st' hStep
  rw [hsch] at hx
  obtain ⟨t, ht⟩ := h x hx
  exact timerTickBudgetOnCore_notPreempted_getTcb?_forward st c tid tcb st' hInv hStep x t ht

/-- WS-SM SM5.I.8: the per-core timer tick preserves `runnableThreadsAreTCBsOnCore`,
given the prepared state satisfies it (`hPrepRat`) and the budget tick preserves it
(`hBudgetRat`).  Idle path = prepared; preempted path via
`scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore` (the dispatched
state's invExt is the budget result's, via `timerTickBudgetOnCore_preserves_objects_invExt`);
not-preempted path = budget result.  `hBudgetRat` is discharged on every clean path
by `timerTickBudgetOnCore_notPreempted_preserves_runnableThreadsAreTCBsOnCore`. -/
theorem timerTickOnCore_preserves_runnableThreadsAreTCBsOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hPrepInv : (timerTickOnCorePrepared st c).1.objects.invExt)
    (hPrepRat : runnableThreadsAreTCBsOnCore (timerTickOnCorePrepared st c).1 c)
    (hBudgetRat : ∀ tid tcb st3 b sgis,
       (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
       (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb →
       timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b, sgis) →
       runnableThreadsAreTCBsOnCore st3 c)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    runnableThreadsAreTCBsOnCore st' c := by
  rw [timerTickOnCore_eq_prepared] at hStep
  cases hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c with
  | none =>
    simp only [hCur] at hStep
    split at hStep
    · cases hH : handleRescheduleSgiOnCore (timerTickOnCorePrepared st c).1 c with
      | error e => simp [hH] at hStep
      | ok st2 =>
        simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨h1, _⟩ := hStep
        rw [← h1]
        exact handleRescheduleSgiOnCore_preserves_runnableThreadsAreTCBsOnCore _ c st2
          hPrepInv hPrepRat (by simp [currentThreadValidOnCore, hCur]) hH
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨h1, _⟩ := hStep
      rw [← h1]; exact hPrepRat
  | some tid =>
    simp only [hCur] at hStep
    cases hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid with
    | none => simp [hTcb] at hStep
    | some tcb =>
      simp only [hTcb] at hStep
      cases hbud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb with
      | error e => simp [hbud] at hStep
      | ok r =>
        obtain ⟨st3, preempted, tsgis⟩ := r
        simp only [hbud] at hStep
        have hst3inv := timerTickBudgetOnCore_preserves_objects_invExt
          (timerTickOnCorePrepared st c).1 c tid tcb st3 preempted hPrepInv hbud
        have hst3rat := hBudgetRat tid tcb st3 preempted tsgis hCur hTcb hbud
        split at hStep
        · cases hsch : scheduleEffectiveOnCore st3 c with
          | error e => simp [hsch] at hStep
          | ok st4 =>
            simp only [hsch, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]
            exact scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore st3 c st4 hst3inv hsch hst3rat
        · rename_i hpre
          have hpf : preempted = false := Bool.not_eq_true _ |>.mp hpre
          subst hpf
          have hV3 : currentThreadValidOnCore st3 c := by
            simp only [currentThreadValidOnCore,
              timerTickBudgetOnCore_notPreempted_scheduler_eq (timerTickOnCorePrepared st c).1 c tid tcb st3 hbud, hCur]
            exact timerTickBudgetOnCore_notPreempted_getTcb?_tid (timerTickOnCorePrepared st c).1 c tid tcb st3 hPrepInv hTcb hbud
          split at hStep
          · cases hH : handleRescheduleSgiOnCore st3 c with
            | error e => simp [hH] at hStep
            | ok st4 =>
              simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨h1, _⟩ := hStep
              rw [← h1]
              exact handleRescheduleSgiOnCore_preserves_runnableThreadsAreTCBsOnCore st3 c st4
                hst3inv hst3rat hV3 hH
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]; exact hst3rat

-- ── §7g  contextMatchesCurrentOnCore per-core preservation [SM5.I] ──
--
--   The register-bank conjunct.  `scheduleEffectiveOnCore` already *establishes*
--   it (the dispatch restores the incoming thread's context into core `c`'s
--   bank); the missing piece is the not-preempted budget tick, which leaves the
--   register bank untouched (`tick` advances only the timer) and the running
--   thread's `registerContext` unchanged (the time-slice / budget write is
--   register-free).

/-- A not-preempted budget tick leaves core `c`'s register bank unchanged
(`tick` advances only `machine.timer`). -/
theorem timerTickBudgetOnCore_notPreempted_regsOnCore_eq (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', false, sgis)) :
    st'.machine.regsOnCore c = st.machine.regsOnCore c := by
  cases hb : tcb.schedContextBinding with
  | unbound =>
    by_cases hsl : tcb.timeSlice ≤ 1
    · simp only [timerTickBudgetOnCore, hb, if_pos hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      exact absurd hStep.2.1 (by decide)
    · simp only [timerTickBudgetOnCore, hb, if_neg hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      rw [← hStep.1]
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        rw [← hStep.1]
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        rw [← hStep.1]

/-- A not-preempted budget tick keeps the running thread resolvable with an
unchanged `registerContext` (the time-slice / budget write is register-free). -/
theorem timerTickBudgetOnCore_notPreempted_getTcb?_tid_reg (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (hInv : st.objects.invExt)
    (hTcb : st.getTcb? tid = some tcb)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', false, sgis)) :
    ∃ t', st'.getTcb? tid = some t' ∧ t'.registerContext = tcb.registerContext := by
  have hDisj : ∀ scId : SeLe4n.SchedContextId, (∃ s, st.getSchedContext? scId = some s) →
      ¬ (scId.toObjId == tid.toObjId) = true := by
    rintro scId ⟨s, hSc⟩ he
    have he' : scId.toObjId = tid.toObjId := by simpa using he
    simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?] at hTcb
    simp only [SystemState.getSchedContext?, RHTable_getElem?_eq_get?] at hSc
    rw [he'] at hSc
    revert hTcb hSc; cases st.objects.get? tid.toObjId with
    | none => simp
    | some o => cases o <;> simp
  cases hb : tcb.schedContextBinding with
  | unbound =>
    by_cases hsl : tcb.timeSlice ≤ 1
    · simp only [timerTickBudgetOnCore, hb, if_pos hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      exact absurd hStep.2.1 (by decide)
    · simp only [timerTickBudgetOnCore, hb, if_neg hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      rw [← hStep.1]
      simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?,
        RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
      exact ⟨_, rfl, rfl⟩
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        refine ⟨tcb, ?_, rfl⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hTcb
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        refine ⟨tcb, ?_, rfl⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hTcb

/-- A not-preempted budget tick preserves `contextMatchesCurrentOnCore`, given the
running thread is core `c`'s current (`hCur` / `hTcb` — true in the tick flow): the
register bank is unchanged and the running thread's `registerContext` is unchanged. -/
theorem timerTickBudgetOnCore_notPreempted_preserves_contextMatchesCurrentOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hInv : st.objects.invExt) (hCur : st.scheduler.currentOnCore c = some tid)
    (hTcb : st.getTcb? tid = some tcb) (h : contextMatchesCurrentOnCore st c)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', false, sgis)) :
    contextMatchesCurrentOnCore st' c := by
  have hsch := timerTickBudgetOnCore_notPreempted_scheduler_eq st c tid tcb st' hStep
  have hregs := timerTickBudgetOnCore_notPreempted_regsOnCore_eq st c tid tcb st' hStep
  obtain ⟨t', ht', htr⟩ :=
    timerTickBudgetOnCore_notPreempted_getTcb?_tid_reg st c tid tcb st' hInv hTcb hStep
  -- the pre-state regs==tcb.reg fact from `h` at current = tid
  simp only [contextMatchesCurrentOnCore, hCur, hTcb] at h
  simp only [contextMatchesCurrentOnCore, hsch, hCur, ht']
  rw [hregs, htr]; exact h

/-- WS-SM SM5.I.8: the per-core timer tick preserves `contextMatchesCurrentOnCore`,
given the prepared state satisfies it (`hPrepCtx`).  Idle path = prepared; preempted
path *re-establishes* it via `scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore`
(no hypothesis); not-preempted path preserves it (register bank + running thread's
`registerContext` unchanged). -/
theorem timerTickOnCore_preserves_contextMatchesCurrentOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hPrepInv : (timerTickOnCorePrepared st c).1.objects.invExt)
    (hPrepCtx : contextMatchesCurrentOnCore (timerTickOnCorePrepared st c).1 c)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    contextMatchesCurrentOnCore st' c := by
  rw [timerTickOnCore_eq_prepared] at hStep
  cases hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c with
  | none =>
    simp only [hCur] at hStep
    split at hStep
    · cases hH : handleRescheduleSgiOnCore (timerTickOnCorePrepared st c).1 c with
      | error e => simp [hH] at hStep
      | ok st2 =>
        simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨h1, _⟩ := hStep
        rw [← h1]
        exact handleRescheduleSgiOnCore_preserves_contextMatchesCurrentOnCore _ c st2
          hPrepInv hPrepCtx hH
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨h1, _⟩ := hStep
      rw [← h1]; exact hPrepCtx
  | some tid =>
    simp only [hCur] at hStep
    cases hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid with
    | none => simp [hTcb] at hStep
    | some tcb =>
      simp only [hTcb] at hStep
      cases hbud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb with
      | error e => simp [hbud] at hStep
      | ok r =>
        obtain ⟨st3, preempted, tsgis⟩ := r
        simp only [hbud] at hStep
        split at hStep
        · cases hsch : scheduleEffectiveOnCore st3 c with
          | error e => simp [hsch] at hStep
          | ok st4 =>
            simp only [hsch, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]
            have hst3inv := timerTickBudgetOnCore_preserves_objects_invExt
              (timerTickOnCorePrepared st c).1 c tid tcb st3 preempted hPrepInv hbud
            exact scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore st3 c st4 hst3inv hsch
        · rename_i hpre
          have hpf : preempted = false := Bool.not_eq_true _ |>.mp hpre
          subst hpf
          have hC3 : contextMatchesCurrentOnCore st3 c :=
            timerTickBudgetOnCore_notPreempted_preserves_contextMatchesCurrentOnCore
              (timerTickOnCorePrepared st c).1 c tid tcb st3 hPrepInv hCur hTcb hPrepCtx hbud
          split at hStep
          · cases hH : handleRescheduleSgiOnCore st3 c with
            | error e => simp [hH] at hStep
            | ok st4 =>
              simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨h1, _⟩ := hStep
              rw [← h1]
              exact handleRescheduleSgiOnCore_preserves_contextMatchesCurrentOnCore st3 c st4
                (timerTickBudgetOnCore_preserves_objects_invExt (timerTickOnCorePrepared st c).1 c tid
                  tcb st3 false hPrepInv hbud)
                hC3 hH
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]; exact hC3

-- ── §7e  Nodup (runQueueUnique) per-core preservation [SM5.I] ──
--
--   The `runQueueUniqueOnCore` (run-queue `toList.Nodup`) conjunct of the SM5.I
--   register-bank+Nodup invariant.  Mirrors the `runQueueOnCoreWellFormed` chain
--   above one-for-one (`RunQueue.remove`/`insert` preserve `toList.Nodup` exactly
--   as they preserve `wellFormed`).  Parameterized by `hPrepNd` (the prepared
--   state's Nodup) like the `queueCurrentConsistent` preservation, since the
--   prepared-phase (cross-core replenishment-wake) Nodup discharger is the SM5
--   cross-core follow-on.

/-- The idle fallback preserves per-core run-queue `Nodup` (idle dispatch only
`remove`s the idle thread; the `current = none` arm leaves the queue unchanged). -/
theorem idleFallbackOnCore_preserves_runQueueOnCore_nodup (st : SystemState) (c : CoreId)
    (hnd : (st.scheduler.runQueueOnCore c).toList.Nodup) :
    ((idleFallbackOnCore st c).scheduler.runQueueOnCore c).toList.Nodup := by
  unfold idleFallbackOnCore
  split
  · rw [dispatchIdleOnCore_runQueueOnCore]
    exact RunQueue.remove_preserves_toList_nodup _ _ hnd
  · simpa [SchedulerState.setCurrentOnCore_runQueueOnCore] using hnd

/-- `scheduleEffectiveOnCore` preserves per-core run-queue `Nodup` — dispatch
dequeues (`remove`), the idle case is the identity. -/
theorem scheduleEffectiveOnCore_preserves_runQueueOnCore_nodup (st : SystemState)
    (c : CoreId) (st' : SystemState) (hnd : (st.scheduler.runQueueOnCore c).toList.Nodup)
    (hStep : scheduleEffectiveOnCore st c = .ok st') :
    (st'.scheduler.runQueueOnCore c).toList.Nodup := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      apply idleFallbackOnCore_preserves_runQueueOnCore_nodup
      rw [saveOutgoingContextOnCore_scheduler_eq]; exact hnd
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
            restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          rw [saveOutgoingContextOnCore_scheduler_eq]
          exact RunQueue.remove_preserves_toList_nodup _ tid hnd
        · simp at hStep

/-- A not-preempted budget tick preserves per-core run-queue `Nodup` — its
scheduler is unchanged (`timerTickBudgetOnCore_notPreempted_scheduler_eq`). -/
theorem timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCore_nodup
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hnd : (st.scheduler.runQueueOnCore c).toList.Nodup)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', false, sgis)) :
    (st'.scheduler.runQueueOnCore c).toList.Nodup := by
  rw [timerTickBudgetOnCore_notPreempted_scheduler_eq st c tid tcb st' hStep]; exact hnd

/-- WS-SM SM5.I.8: the per-core timer tick preserves `runQueueUniqueOnCore`, given
the prepared state is `Nodup` (`hPrepNd`) and the budget tick preserves it
(`hBudgetNd`).  Idle path = prepared; preempted path dequeues-on-dispatch via
`scheduleEffectiveOnCore_preserves_runQueueOnCore_nodup`; not-preempted path leaves
the scheduler unchanged.  `hBudgetNd` is discharged on every clean path by
`timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCore_nodup`. -/
theorem timerTickOnCore_preserves_runQueueUniqueOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hPrepNd : ((timerTickOnCorePrepared st c).1.scheduler.runQueueOnCore c).toList.Nodup)
    (hBudgetNd : ∀ tid tcb st3 b sgis,
       (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
       (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb →
       timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b, sgis) →
       (st3.scheduler.runQueueOnCore c).toList.Nodup)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    runQueueUniqueOnCore st'.scheduler c := by
  rw [timerTickOnCore_eq_prepared] at hStep
  cases hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c with
  | none =>
    simp only [hCur] at hStep
    split at hStep
    · cases hH : handleRescheduleSgiOnCore (timerTickOnCorePrepared st c).1 c with
      | error e => simp [hH] at hStep
      | ok st2 =>
        simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨h1, _⟩ := hStep
        rw [← h1]
        exact handleRescheduleSgiOnCore_preserves_runQueueOnCore_nodup _ c st2 hPrepNd hH
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨h1, _⟩ := hStep
      rw [← h1]; exact hPrepNd
  | some tid =>
    simp only [hCur] at hStep
    cases hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid with
    | none => simp [hTcb] at hStep
    | some tcb =>
      simp only [hTcb] at hStep
      cases hbud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb with
      | error e => simp [hbud] at hStep
      | ok r =>
        obtain ⟨st3, preempted, tsgis⟩ := r
        simp only [hbud] at hStep
        have hst3 := hBudgetNd tid tcb st3 preempted tsgis hCur hTcb hbud
        split at hStep
        · cases hsch : scheduleEffectiveOnCore st3 c with
          | error e => simp [hsch] at hStep
          | ok st4 =>
            simp only [hsch, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]
            exact scheduleEffectiveOnCore_preserves_runQueueOnCore_nodup st3 c st4 hst3 hsch
        · split at hStep
          · cases hH : handleRescheduleSgiOnCore st3 c with
            | error e => simp [hH] at hStep
            | ok st4 =>
              simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨h1, _⟩ := hStep
              rw [← h1]
              exact handleRescheduleSgiOnCore_preserves_runQueueOnCore_nodup st3 c st4 hst3 hH
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]; exact hst3

/-- WS-SM SM5.D.5/.6 (preservation): the per-core timer tick preserves per-core
dequeue-on-dispatch consistency, given that the *prepared* state satisfies it
(`hPrepQcc`).  The idle path is the prepared state; the preempted path
*re-establishes* consistency via
`scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore` (no hypothesis
needed); the not-preempted path leaves the scheduler unchanged
(`timerTickBudgetOnCore_notPreempted_scheduler_eq`), so consistency is inherited
from `hPrepQcc`.  `hPrepQcc` follows from the input `queueCurrentConsistentOnCore`
when the SM5.D.4 replenishment preserves it (the wake's don't-wake-the-running-
thread guard, SM5.C); the SM5.D.6 domain decrement preserves it
(`decrementDomainTimeOnCore_preserves_queueCurrentConsistentOnCore`). -/
theorem timerTickOnCore_preserves_queueCurrentConsistentOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hPrepQcc : queueCurrentConsistentOnCore (timerTickOnCorePrepared st c).1.scheduler c)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    queueCurrentConsistentOnCore st'.scheduler c := by
  rw [timerTickOnCore_eq_prepared] at hStep
  cases hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c with
  | none =>
    simp only [hCur] at hStep
    split at hStep
    · cases hH : handleRescheduleSgiOnCore (timerTickOnCorePrepared st c).1 c with
      | error e => simp [hH] at hStep
      | ok st2 =>
        simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨h1, _⟩ := hStep
        rw [← h1]
        exact handleRescheduleSgiOnCore_preserves_queueCurrentConsistentOnCore _ c st2 hPrepQcc hH
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨h1, _⟩ := hStep
      rw [← h1]; exact hPrepQcc
  | some tid =>
    simp only [hCur] at hStep
    cases hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid with
    | none => simp [hTcb] at hStep
    | some tcb =>
      simp only [hTcb] at hStep
      cases hbud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb with
      | error e => simp [hbud] at hStep
      | ok r =>
        obtain ⟨st3, preempted, tsgis⟩ := r
        simp only [hbud] at hStep
        split at hStep
        · cases hsch : scheduleEffectiveOnCore st3 c with
          | error e => simp [hsch] at hStep
          | ok st4 =>
            simp only [hsch, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]
            exact scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore st3 c st4 hsch
        · rename_i hpre
          have hpf : preempted = false := Bool.not_eq_true _ |>.mp hpre
          subst hpf
          have hQ3 : queueCurrentConsistentOnCore st3.scheduler c := by
            rw [timerTickBudgetOnCore_notPreempted_scheduler_eq (timerTickOnCorePrepared st c).1 c tid tcb st3 hbud]
            exact hPrepQcc
          split at hStep
          · cases hH : handleRescheduleSgiOnCore st3 c with
            | error e => simp [hH] at hStep
            | ok st4 =>
              simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨h1, _⟩ := hStep
              rw [← h1]
              exact handleRescheduleSgiOnCore_preserves_queueCurrentConsistentOnCore st3 c st4 hQ3 hH
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]; exact hQ3

-- ── §7f  Per-core domain-invariant preservation (audit-pass-2 capstone) ──
--
--   The audit-pass-2 fix makes `timerTickOnCore` a pure budget tick (no in-tick
--   domain rotation), so it preserves the SM4.C `currentThreadInActiveDomainOnCore`
--   invariant.  This section *proves* it: `scheduleEffectiveOnCore` dispatches a
--   thread that is in core `c`'s active domain (it checks `tcb.domain = activeDomain`
--   before dispatching); the not-preempted budget tick leaves the scheduler and the
--   charged thread's domain unchanged.  The pre-audit-pass-2 tick (which rotated the
--   domain without re-dispatch) could NOT satisfy this — the missing theorem was the
--   tell.  `timerTickOnCore_preserves_currentThreadInActiveDomainOnCore` is
--   parameterized by `hPrepDom` (the replenishment preserves the domain invariant),
--   discharged on the clean path; the SM5.D.4 wake never touches `current`/domains.

-- saveOutgoing preserves the domain of any resolvable thread.
theorem saveOutgoingContextOnCore_getTcb?_domain (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) (hCur : st.getTcb? tid = some tcb) :
    ∃ tcb', (saveOutgoingContextOnCore st c).getTcb? tid = some tcb' ∧ tcb'.domain = tcb.domain := by
  cases hc : st.scheduler.currentOnCore c with
  | none => exact ⟨tcb, by rw [show saveOutgoingContextOnCore st c = st from by
      simp only [saveOutgoingContextOnCore, hc]]; exact hCur, rfl⟩
  | some outTid =>
    cases ho : st.getTcb? outTid with
    | none => exact ⟨tcb, by rw [show saveOutgoingContextOnCore st c = st from by
        simp only [saveOutgoingContextOnCore, hc, ho]]; exact hCur, rfl⟩
    | some outTcb =>
      by_cases heq : tid = outTid
      · subst heq
        refine ⟨{ outTcb with registerContext := st.machine.regsOnCore c }, ?_, ?_⟩
        · simp only [saveOutgoingContextOnCore, hc, ho]
          simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
          rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
        · rw [hCur] at ho; have he : tcb = outTcb := Option.some.inj ho; rw [he]
      · have hNeO : ¬ (outTid.toObjId == tid.toObjId) = true := fun he =>
          heq (ThreadId.toObjId_injective _ _ (by simpa using he)).symm
        refine ⟨tcb, ?_, rfl⟩
        simp only [saveOutgoingContextOnCore, hc, ho]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects outTid.toObjId tid.toObjId _ hNeO hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hCur


theorem scheduleEffectiveOnCore_getTcb?_domain (st : SystemState) (c : CoreId) (st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') (hres : st.getTcb? tid = some tcb) :
    ∃ tcb', st'.getTcb? tid = some tcb' ∧ tcb'.domain = tcb.domain := by
  have hobj := scheduleEffectiveOnCore_objects_eq st c st' hStep
  obtain ⟨tcb', hg, hdom⟩ := saveOutgoingContextOnCore_getTcb?_domain st c tid tcb hInv hres
  refine ⟨tcb', ?_, hdom⟩
  have hgt : st'.getTcb? tid = (saveOutgoingContextOnCore st c).getTcb? tid := by
    simp only [SystemState.getTcb?, hobj]
  rw [hgt, hg]

theorem scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore (st : SystemState) (c : CoreId) (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') :
    currentThreadInActiveDomainOnCore st' c := by
  have hCopy := hStep
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      exact idleFallbackOnCore_establishes_currentThreadInActiveDomainOnCore _ c
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · rename_i hcond
          simp only [Except.ok.injEq] at hStep
          have hcur : st'.scheduler.currentOnCore c = some tid := by
            rw [← hStep]; simp [SchedulerState.setCurrentOnCore_currentOnCore_self]
          have hact : st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c := by
            rw [← hStep]
            simp only [SchedulerState.setCurrentOnCore_activeDomainOnCore, restoreIncomingContextOnCore_scheduler,
              SchedulerState.setRunQueueOnCore_activeDomainOnCore]
            rw [saveOutgoingContextOnCore_scheduler_eq]
          obtain ⟨tcb', hg, hdom⟩ := scheduleEffectiveOnCore_getTcb?_domain st c st' tid tcb hInv hCopy hTcb
          simp only [currentThreadInActiveDomainOnCore, hcur, hg, hact, hdom]
          exact hcond.2
        · simp at hStep


-- not-preempted budget tick preserves the charged thread's domain.
theorem timerTickBudgetOnCore_notPreempted_getTcb?_domain (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (st' : SystemState) (hInv : st.objects.invExt) (hCur : st.getTcb? tid = some tcb)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', false, sgis)) :
    ∃ t, st'.getTcb? tid = some t ∧ t.domain = tcb.domain := by
  have hDisj : ∀ scId : SeLe4n.SchedContextId, (∃ s, st.getSchedContext? scId = some s) →
      ¬ (scId.toObjId == tid.toObjId) = true := by
    rintro scId ⟨s, hSc⟩ he
    have he' : scId.toObjId = tid.toObjId := by simpa using he
    simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?] at hCur
    simp only [SystemState.getSchedContext?, RHTable_getElem?_eq_get?] at hSc
    rw [he'] at hSc
    revert hCur hSc; cases st.objects.get? tid.toObjId with
    | none => simp
    | some o => cases o <;> simp
  cases hb : tcb.schedContextBinding with
  | unbound =>
    by_cases hsl : tcb.timeSlice ≤ 1
    · simp only [timerTickBudgetOnCore, hb, if_pos hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      exact absurd hStep.2.1 (by decide)
    · simp only [timerTickBudgetOnCore, hb, if_neg hsl, Except.ok.injEq, Prod.mk.injEq] at hStep
      rw [← hStep.1]
      simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?,
        RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
      exact ⟨_, rfl, rfl⟩
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        refine ⟨tcb, ?_, rfl⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hCur
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none => simp only [timerTickBudgetOnCore, hb, hSc] at hStep; exact absurd hStep (by simp)
    | some sc =>
      by_cases hbg : sc.budgetRemaining.val ≤ 1
      · simp only [timerTickBudgetOnCore, hb, hSc, if_pos hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        exact absurd hStep.2.1 (by decide)
      · simp only [timerTickBudgetOnCore, hb, hSc, if_neg hbg, Except.ok.injEq, Prod.mk.injEq] at hStep
        refine ⟨tcb, ?_, rfl⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hCur

-- composed: the tick preserves currentThreadInActiveDomain, parameterized by hPrepDom.
theorem timerTickOnCore_preserves_currentThreadInActiveDomainOnCore (st : SystemState) (c : CoreId) (st' : SystemState)
    (sgis : List (CoreId × SgiKind)) (hInv : st.objects.invExt)
    (hPrepDom : currentThreadInActiveDomainOnCore (timerTickOnCorePrepared st c).1 c)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    currentThreadInActiveDomainOnCore st' c := by
  have hPrepInv : (timerTickOnCorePrepared st c).1.objects.invExt :=
    timerTickOnCorePrepared_objects_invExt st c hInv
  rw [timerTickOnCore_eq_prepared] at hStep
  cases hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c with
  | none =>
    simp only [hCur] at hStep
    split at hStep
    · cases hH : handleRescheduleSgiOnCore (timerTickOnCorePrepared st c).1 c with
      | error e => simp [hH] at hStep
      | ok st2 =>
        simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨h1, _⟩ := hStep
        rw [← h1]
        exact handleRescheduleSgiOnCore_preserves_currentThreadInActiveDomainOnCore _ c st2
          hPrepInv hPrepDom hH
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨h1, _⟩ := hStep
      rw [← h1]; exact hPrepDom
  | some tid =>
    simp only [hCur] at hStep
    cases hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid with
    | none => simp [hTcb] at hStep
    | some tcb =>
      simp only [hTcb] at hStep
      cases hbud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb with
      | error e => simp [hbud] at hStep
      | ok r =>
        obtain ⟨st3, preempted, tsgis⟩ := r
        simp only [hbud] at hStep
        split at hStep
        · cases hsch : scheduleEffectiveOnCore st3 c with
          | error e => simp [hsch] at hStep
          | ok st4 =>
            simp only [hsch, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]
            exact scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore st3 c st4
              (timerTickBudgetOnCore_preserves_objects_invExt (timerTickOnCorePrepared st c).1 c tid
                tcb st3 preempted hPrepInv hbud) hsch
        · rename_i hpre
          have hpf : preempted = false := Bool.not_eq_true _ |>.mp hpre
          subst hpf
          -- not-preempted: scheduler unchanged, current = tid, domain of tid preserved
          have hD3 : currentThreadInActiveDomainOnCore st3 c := by
            obtain ⟨t', hg, hdom⟩ := timerTickBudgetOnCore_notPreempted_getTcb?_domain (timerTickOnCorePrepared st c).1 c tid tcb st3 hPrepInv hTcb hbud
            unfold currentThreadInActiveDomainOnCore at hPrepDom ⊢
            simp only [hCur, hTcb] at hPrepDom
            rw [timerTickBudgetOnCore_notPreempted_scheduler_eq (timerTickOnCorePrepared st c).1 c tid tcb st3 hbud]
            simp only [hCur, hg, hdom]
            exact hPrepDom
          split at hStep
          · cases hH : handleRescheduleSgiOnCore st3 c with
            | error e => simp [hH] at hStep
            | ok st4 =>
              simp only [hH, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨h1, _⟩ := hStep
              rw [← h1]
              exact handleRescheduleSgiOnCore_preserves_currentThreadInActiveDomainOnCore st3 c st4
                (timerTickBudgetOnCore_preserves_objects_invExt (timerTickOnCorePrepared st c).1 c tid
                  tcb st3 false hPrepInv hbud)
                hD3 hH
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨h1, _⟩ := hStep
            rw [← h1]; exact hD3

end SeLe4n.Kernel
