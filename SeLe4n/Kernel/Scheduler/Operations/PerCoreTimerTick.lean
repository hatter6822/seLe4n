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
  over SM5.A's `LockKey` extended with the SM5.D.3 replenish-queue domain:
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
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId allCores SgiKind
  LockKey)

-- ============================================================================
-- §1  SM5.D.3 — Cross-domain lock-set footprint (+ SM5.D.7 WCRT size bound)
-- ============================================================================

/-- WS-SM SM5.D.3 (cross-domain, plan §3.4 / §4.4): the **static** timer-proper
lock-set footprint of `timerTickOnCore c`, over SM5.A's `LockKey` (extended at
SM5.D.3 with the replenish-queue domain).

The tick's *own* writes (the SM5.D.4 replenishment, SM5.D.6 domain accounting,
SM5.D.5 budget tick on its non-timeout branches, and the SM5.D.2 reschedule) touch
three lock domains on core `c`:
* the RobinHood **object store** (write): CBS refills + budget/time-slice writes +
  the context save/restore on preemption all `objects.insert`.  Per SM3.A.10 the
  store is guarded by the single table-level lock (`LockKey.objStore`), in
  **write** mode — which subsumes plan §3.4's "all TCB locks for threads whose
  SchedContext is bound to `c`" (the per-thread set), exactly the SM5.B/C
  table-lock rationale (RHTable structural safety is table-granularity);
* core `c`'s **run-queue** slot (write): re-enqueue on preemption + dispatch
  dequeue; and
* core `c`'s **replenish-queue** slot (write): the head drain + the exhausted-budget
  replenishment insert.

So the static footprint is the three-lock set in plan §4.4 ascending order
(objStore < runQueue < replenishQueue):
`[(objStore, .write), (runQueue c, .write), (replenishQueue c, .write)]`.

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
    List (LockKey × Concurrency.AccessMode) :=
  [ (LockKey.objStore, .write)
  , (LockKey.runQueue c, .write)
  , (LockKey.replenishQueue c, .write) ]

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
    (LockKey.objStore, Concurrency.AccessMode.write)
      ∈ timerTickOnCoreLockSet c := by
  simp [timerTickOnCoreLockSet]

/-- SM5.D.3: core `c`'s run-queue **write** lock is in the tick footprint. -/
theorem timerTickOnCoreLockSet_contains_runQueue_write (c : CoreId) :
    (LockKey.runQueue c, Concurrency.AccessMode.write)
      ∈ timerTickOnCoreLockSet c := by
  simp [timerTickOnCoreLockSet]

/-- SM5.D.3: core `c`'s replenish-queue **write** lock is in the tick footprint. -/
theorem timerTickOnCoreLockSet_contains_replenishQueue_write (c : CoreId) :
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
      ∈ timerTickOnCoreLockSet c := by
  simp [timerTickOnCoreLockSet]

/-- SM5.D.3: the tick footprint's projected keys are duplicate-free (the three
locks are distinct constructors / distinct cores). -/
theorem timerTickOnCoreLockSet_keys_nodup (c : CoreId) :
    ((timerTickOnCoreLockSet c).map (·.1)).Nodup := by
  simp [timerTickOnCoreLockSet]

/-- SM5.D.3 (plan §4.4): the tick footprint's keys form a `LockKey`-ascending
acquisition sequence (`Pairwise (· ≤ ·)`) — object before run-queue before
replenish-queue — so the canonical `withLockSet` acquisition is the list itself
(the tick's contribution to the SM3.D deadlock-freedom ladder). -/
theorem timerTickOnCoreLockSet_pairwise_le (c : CoreId) :
    ((timerTickOnCoreLockSet c).map (·.1)).Pairwise (· ≤ ·) := by
  have hObjRq : LockKey.objStore
      ≤ LockKey.runQueue c :=
    (LockKey.objStore_lt_runQueue _).1
  have hObjRpq : LockKey.objStore
      ≤ LockKey.replenishQueue c :=
    (LockKey.objStore_lt_replenishQueue _).1
  have hRqRpq : LockKey.runQueue c
      ≤ LockKey.replenishQueue c :=
    (LockKey.runQueue_lt_replenishQueue _ _).1
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
def allCoreRunQueueLockSegment : List (LockKey × Concurrency.AccessMode) :=
  allCores.map (fun d => (LockKey.runQueue d, .write))

/-- **WS-RR RR7.39**: the segment's length is the core count. -/
@[simp] theorem allCoreRunQueueLockSegment_length :
    allCoreRunQueueLockSegment.length = numCores := by
  simp [allCoreRunQueueLockSegment, Concurrency.allCores_length]

/-- **WS-RR RR7.39**: every core's run-queue write lock is in the segment. -/
theorem mem_allCoreRunQueueLockSegment (d : CoreId) :
    (LockKey.runQueue d, Concurrency.AccessMode.write)
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
theorem allCoreRunQueueLockSegment_keys_runQueue {k : LockKey}
    (hk : k ∈ allCoreRunQueueLockSegment.map (·.1)) :
    ∃ d : CoreId, k = LockKey.runQueue d := by
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
    List (LockKey × Concurrency.AccessMode) :=
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
    (LockKey.runQueue d, Concurrency.AccessMode.write)
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
    List (LockKey × Concurrency.AccessMode) :=
  (LockKey.objStore, .write) ::
    (allCoreRunQueueLockSegment ++ [(LockKey.replenishQueue c, .write)])

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

`LockKey.objStore` is a single key of the ghost lock table, not a per-core
one — so two ticks on distinct cores exclude each other on it whatever
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
  ⟨(LockKey.objStore, .write),
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
      have hInj : Function.Injective (fun d : CoreId => LockKey.runQueue d) := by
        intro a b hab
        exact LockKey.runQueue.inj hab
      have hKeys : allCoreRunQueueLockSegment.map (·.1)
          = allCores.map (fun d : CoreId => LockKey.runQueue d) := by
        simp [allCoreRunQueueLockSegment, List.map_map, Function.comp]
      rw [hKeys]
      exact List.Pairwise.map _ (fun _ _ h he => h (hInj he)) Concurrency.allCores_nodup
    · intro a ha b hb
      obtain ⟨_, rfl⟩ := allCoreRunQueueLockSegment_keys_runQueue ha
      rw [List.mem_singleton.mp hb]
      simp

/-- SM5.D.3 (plan §4.4): the complete footprint's keys form a
`LockKey`-ascending acquisition sequence — object < every run queue (in
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
      exact (LockKey.objStore_lt_runQueue _).1
    · rw [List.mem_singleton.mp hRep]
      exact (LockKey.objStore_lt_replenishQueue _).1
  · intro a ha b hb
    obtain ⟨_, rfl⟩ := allCoreRunQueueLockSegment_keys_runQueue ha
    rw [List.mem_singleton.mp hb]
    exact (LockKey.runQueue_lt_replenishQueue _ _).1

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
  exact SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv

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

/-- WS-SM SM5.D.4: `refillSchedContext` writes only the object store, leaving the
scheduler unchanged. -/
@[simp] theorem refillSchedContext_scheduler_eq (st : SystemState)
    (scId : SeLe4n.SchedContextId) (now : Nat) :
    (refillSchedContext st scId now).scheduler = st.scheduler := by
  unfold refillSchedContext; exact SystemState.updateSchedContext_scheduler _ _ _

/-- WS-SM SM5.D.4: `refillSchedContext` leaves the machine state unchanged. -/
@[simp] theorem refillSchedContext_machine_eq (st : SystemState)
    (scId : SeLe4n.SchedContextId) (now : Nat) :
    (refillSchedContext st scId now).machine = st.machine := by
  unfold refillSchedContext; exact SystemState.updateSchedContext_machine _ _ _

/-- WS-SM SM5.D.4 (preservation): `processOneReplenishmentOnCore` preserves the
object-store invariant — the state is either the refilled state (refill preserves
`invExt`) or a wake on top of it (`wakeThread` preserves `invExt`), whose
reschedule mark writes no object. -/
theorem processOneReplenishmentOnCore_preserves_objects_invExt (st : SystemState)
    (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hInv : st.objects.invExt) :
    (processOneReplenishmentOnCore st execCore scId now).objects.invExt := by
  have hRef : (refillSchedContext st scId now).objects.invExt :=
    refillSchedContext_preserves_objects_invExt st scId now hInv
  rw [processOneReplenishmentOnCore, markRefillKeyChange_objects]
  simp only [refillWakeOnCore]
  split
  · split
    · exact hRef
    · exact wakeThread_preserves_objects_invExt _ _ execCore hRef
  · exact hRef

/-- WS-SM SM5.D.4 (preservation): `processOneReplenishmentOnCore` preserves
run-queue well-formedness on **every** core `c'` (refill never touches a run
queue; the wake preserves every core's run-queue well-formedness; the mark
writes a flag). -/
theorem processOneReplenishmentOnCore_preserves_runQueueOnCore_wellFormed (st : SystemState)
    (execCore c' : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hwf : (st.scheduler.runQueueOnCore c').wellFormed) :
    ((processOneReplenishmentOnCore st execCore scId now).scheduler.runQueueOnCore c').wellFormed := by
  have hRefRq : (refillSchedContext st scId now).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
    unfold refillSchedContext; rw [SystemState.updateSchedContext_scheduler]
  have hRef : ((refillSchedContext st scId now).scheduler.runQueueOnCore c').wellFormed := by
    rw [hRefRq]; exact hwf
  rw [processOneReplenishmentOnCore, markRefillKeyChange_runQueueOnCore]
  simp only [refillWakeOnCore]
  split
  · split
    · exact hRef
    · exact wakeThread_preserves_runQueueOnCore_wellFormed_anyCore _ _ execCore c' hRef
  · exact hRef

/-- WS-SM SM5.D.4 (preservation): `processReplenishmentsDueOnCore` preserves the
object-store invariant — each refill does, and each re-placement does. -/
theorem processReplenishmentsDueOnCore_preserves_objects_invExt (st : SystemState)
    (c : CoreId) (now : Nat) (hInv : st.objects.invExt) :
    (processReplenishmentsDueOnCore st c now).objects.invExt :=
  processReplenishmentsDueOnCore_induction (fun s => s.objects.invExt) st c now
    (fun s scId h => processOneReplenishmentOnCore_preserves_objects_invExt s c scId now h)
    (fun s scId h => SystemState.releasePlace_objects_invExt s c scId h) hInv

/-- WS-SM SM5.D.4 (preservation): `processReplenishmentsDueOnCore` preserves
run-queue well-formedness on **every** core `c'`. -/
theorem processReplenishmentsDueOnCore_preserves_runQueueOnCore_wellFormed (st : SystemState)
    (c c' : CoreId) (now : Nat)
    (hwf : (st.scheduler.runQueueOnCore c').wellFormed) :
    ((processReplenishmentsDueOnCore st c now).scheduler.runQueueOnCore c').wellFormed :=
  processReplenishmentsDueOnCore_induction (fun s => (s.scheduler.runQueueOnCore c').wellFormed)
    st c now
    (fun s scId h => processOneReplenishmentOnCore_preserves_runQueueOnCore_wellFormed s c c' scId
      now h)
    (fun s scId h => by simpa only [SystemState.releasePlace_runQueueOnCore] using h) hwf

/-- WS-SM SM5.D.4: a replenishment that transitions no thread to runnable is the
refill alone — it wakes nobody and raises no reschedule flag. -/
theorem processOneReplenishmentOnCore_of_no_target (st : SystemState)
    (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hNone : replenishWakeTarget st (refillSchedContext st scId now) scId = none) :
    processOneReplenishmentOnCore st execCore scId now =
      markRefillKeyChange st (refillSchedContext st scId now) scId := by
  simp only [processOneReplenishmentOnCore, refillWakeOnCore, hNone]

/-- WS-ZA ZA6.2: a run-queue placement only raises reschedule flags. -/
theorem enqueueRunnableOnCore_reschedulePendingOnCore_mono (st : SystemState) (c d : CoreId)
    (tid : SeLe4n.ThreadId) (h : st.scheduler.reschedulePendingOnCore d = true) :
    (enqueueRunnableOnCore st c tid).scheduler.reschedulePendingOnCore d = true := by
  unfold enqueueRunnableOnCore
  split
  · split
    · exact h
    · by_cases hcd : c = d
      · subst hcd; simp
      · rw [SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_ne _ _ _ hcd,
          SystemState.runEnqueueAdmitted_reschedulePendingOnCore]
        exact h
  · exact h

/-- WS-ZA ZA6.2: a wake only raises reschedule flags. -/
theorem wakeThread_reschedulePendingOnCore_mono (st : SystemState) (tid : SeLe4n.ThreadId)
    (execCore d : CoreId) (h : st.scheduler.reschedulePendingOnCore d = true) :
    (wakeThread st tid execCore).1.scheduler.reschedulePendingOnCore d = true := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_reschedulePendingOnCore_mono _ _ _ _ h

/-- WS-ZA ZA6.2: a replenishment only raises reschedule flags — it lowers none,
so a flag an earlier step of the drain raised survives the rest of it. -/
theorem processOneReplenishmentOnCore_reschedulePendingOnCore_mono (st : SystemState)
    (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat) (d : CoreId)
    (h : st.scheduler.reschedulePendingOnCore d = true) :
    (processOneReplenishmentOnCore st execCore scId now).scheduler.reschedulePendingOnCore d
      = true := by
  have hRef : (refillSchedContext st scId now).scheduler.reschedulePendingOnCore d = true := by
    rw [refillSchedContext_scheduler_eq]; exact h
  rw [processOneReplenishmentOnCore]
  apply markRefillKeyChange_reschedulePendingOnCore_mono
  simp only [refillWakeOnCore]
  split
  · split
    · exact hRef
    · rename_i tid _ _
      have hW := wakeThread_reschedulePendingOnCore_mono _ tid execCore _ hRef
      by_cases hd : determineTargetCore (refillSchedContext st scId now) tid = d
      · subst hd
        rw [SchedulerState.markReschedulePendingOnCoreIf_reschedulePendingOnCore_self, hW]
        rfl
      · rw [SchedulerState.markReschedulePendingOnCoreIf_reschedulePendingOnCore_ne _ _ _ _ hd]
        exact hW
  · exact hRef

/-- WS-SM SM5.D.4 / WS-ZA ZA6.2 (the headline cross-core wake, plan §6.1
`cbsReplenish_can_wake_remote_core`): when a CBS replenishment transitions a
SchedContext's bound thread `tid` to runnable, `tid` resolves to a TCB and it is
not running on any core, the replenishment raises the reschedule flag of
`tid`'s target core — a remote core's flag going up is the `.reschedule` SGI
the tick's seam fires (`perCoreTimerTickStep_remote_flag_sgi`), the executing
core's is the local decision the tick runs after the charge.  The flag goes up
whether the wake placed `tid` or found it already queued: the refill made a
queued thread eligible, which stales the target core's decision (the case PR
#880 round 7 found, where a thread queued but exhausted on the executing core
had no placement, no SGI and no preemption to make it visible). -/
theorem cbsReplenish_can_wake_remote_core (st : SystemState) (execCore : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTarget : replenishWakeTarget st (refillSchedContext st scId now) scId = some tid)
    (hTcb : (refillSchedContext st scId now).getTcb? tid = some tcb)
    (hNotRunning : runningOnSomeCore (refillSchedContext st scId now) tid = false) :
    (processOneReplenishmentOnCore st execCore scId now).scheduler.reschedulePendingOnCore
      (determineTargetCore (refillSchedContext st scId now) tid) = true := by
  rw [processOneReplenishmentOnCore]
  apply markRefillKeyChange_reschedulePendingOnCore_mono
  simp only [refillWakeOnCore, hTarget, hNotRunning, Bool.false_eq_true,
    if_false, hTcb, Option.isSome_some]
  simp

/-- WS-ZA ZA6.2: the replenishment that wakes `tid` is the wake on the refilled
state with the target core's flag marked when `tid` resolves. -/
theorem processOneReplenishmentOnCore_wake_eq (st : SystemState) (execCore : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (tid : SeLe4n.ThreadId)
    (hTarget : replenishWakeTarget st (refillSchedContext st scId now) scId = some tid)
    (hNotRunning : runningOnSomeCore (refillSchedContext st scId now) tid = false) :
    processOneReplenishmentOnCore st execCore scId now =
      markRefillKeyChange st
        { (wakeThread (refillSchedContext st scId now) tid execCore).1 with scheduler :=
          ((wakeThread (refillSchedContext st scId now) tid execCore).1.scheduler.markReschedulePendingOnCoreIf
            (determineTargetCore (refillSchedContext st scId now) tid)
            ((refillSchedContext st scId now).getTcb? tid).isSome) } scId := by
  simp only [processOneReplenishmentOnCore, refillWakeOnCore, hTarget, hNotRunning,
    Bool.false_eq_true, if_false]

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
-- The timeout wakes are target-aware since PR #880 round 8 (`timeoutThread`
-- wakes through `wakeThread` on the thread's home core), and since WS-ZA ZA6.2
-- each woken thread's home core is flagged (`markRescheduleTargets`), so its
-- `.reschedule` SGI is read off the flags with the drain's.

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
             exact SystemState.unlinkReplyWaiter_objects_invExt _ _ _
               (wakeThread_preserves_objects_invExt _ _ execCore hInv2))
          | (exact wakeThread_preserves_objects_invExt _ _ execCore hInv2)

/-- WS-SM SM5.D.5 (preservation): `timeoutBlockedThreads` preserves the
object-store invariant — each fold step either keeps the state or applies
`timeoutThread` (which preserves it). -/
theorem timeoutBlockedThreads_preserves_objects_invExt (st : SystemState)
    (scId : SeLe4n.SchedContextId) (execCore : CoreId) (hInv : st.objects.invExt) :
    (timeoutBlockedThreads st scId execCore).1.objects.invExt := by
  rw [timeoutBlockedThreads_eq_fold]; delta timeoutBlockedThreadStep
  generalize (schedContextTimeoutThreads st scId) = tids
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
    (hInv : st.objects.invExt)
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', b)) : st'.objects.invExt := by
  unfold timerTickBudgetOnCore at hStep
  dsimp only [SystemState.rewriteObject] at hStep
  split at hStep
  · -- unbound: slice expiry, or the TCB insert of a decremented slice
    split at hStep
    · simp only [Prod.mk.injEq] at hStep
      obtain ⟨hst, _⟩ := hStep; subst hst
      exact sliceExpireOnCore_objects_invExt st c tid tcb hW hInv
    · simp only [Prod.mk.injEq] at hStep
      obtain ⟨hst, _⟩ := hStep; subst hst
      exact RHTable_insert_preserves_invExt st.objects _ _ hInv
  all_goals
    -- bound + donated (identical: SchedContext insert, exhausted ⇒ + timeout);
    -- a context the store does not hold is charged nothing
    split at hStep
    · split at hStep
      · simp only [Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst
        apply timeoutBlockedThreads_preserves_objects_invExt
        rw [markKeyChangeFor_objects]
        exact spendBudgetOnCore_objects_invExt _ _ _ _ _ _ _ _ hInv
      · simp only [Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst
        exact RHTable_insert_preserves_invExt st.objects _ _ hInv
    · simp only [Prod.mk.injEq] at hStep
      obtain ⟨hst, _⟩ := hStep; subst hst
      exact hInv

/-- WS-SM SM5.D.5: an *unbound* thread whose time-slice has not expired
(`timeSlice > 1`) is **not** preempted by the budget tick. -/
theorem timerTickBudgetOnCore_unbound_not_preempted (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (b : Bool)
    (hUnbound : tcb.schedContextBinding = .unbound) (hSlice : ¬ tcb.timeSlice ≤ 1)
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', b)) : b = false := by
  simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hUnbound, if_neg hSlice,
    Prod.mk.injEq] at hStep
  exact hStep.2.symm

/-- WS-SM SM5.D.5: an *unbound* thread whose time-slice has expired
(`timeSlice ≤ 1`) **is** preempted (`wasPreempted = true`) — the per-core
time-slice preemption. -/
theorem timerTickBudgetOnCore_unbound_preempts (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (b : Bool)
    (hUnbound : tcb.schedContextBinding = .unbound) (hSlice : tcb.timeSlice ≤ 1)
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', b)) : b = true := by
  simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hUnbound, if_pos hSlice,
    Prod.mk.injEq] at hStep
  exact hStep.2.symm

/-- WS-SM SM5.D.5 / B4: a *bound* thread whose SchedContext budget is exhausted
(`budgetRemaining ≤ 1`) **is** preempted — the per-core CBS budget-exhaustion
preemption (the substantive one, beyond the time-slice case above). -/
theorem timerTickBudgetOnCore_bound_preempts (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (st' : SystemState) (b : Bool)
    (hBound : tcb.schedContextBinding = .bound scId)
    (hSc : st.getSchedContext? scId = some sc) (hBudget : sc.tickExhausts (st.machine.timer - 1) = true)
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', b)) : b = true := by
  simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hBound, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hBudget,
    Prod.mk.injEq] at hStep
  exact hStep.2.symm

/-- WS-SM SM5.D.5 / B4: a *bound* thread whose SchedContext budget has not expired
(`budgetRemaining > 1`) is **not** preempted (the budget is decremented and the
thread continues). -/
theorem timerTickBudgetOnCore_bound_not_preempted (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (st' : SystemState) (b : Bool)
    (hBound : tcb.schedContextBinding = .bound scId)
    (hSc : st.getSchedContext? scId = some sc) (hBudget : ¬ sc.tickExhausts (st.machine.timer - 1) = true)
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', b)) : b = false := by
  simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hBound, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hBudget,
    Prod.mk.injEq] at hStep
  exact hStep.2.symm

/-- WS-SM SM5.D.5 / B4: the *donated* SchedContext-binding case — budget exhausted
(`budgetRemaining ≤ 1`) preempts.  (The `.donated scId _` arm of
`timerTickBudgetOnCore` shares the bound-case body.) -/
theorem timerTickBudgetOnCore_donated_preempts (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId) (sc : SchedContext) (st' : SystemState) (b : Bool)
    (hDonated : tcb.schedContextBinding = .donated scId originalOwner)
    (hSc : st.getSchedContext? scId = some sc) (hBudget : sc.tickExhausts (st.machine.timer - 1) = true)
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', b)) : b = true := by
  simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hDonated, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hBudget,
    Prod.mk.injEq] at hStep
  exact hStep.2.symm

/-- WS-SM SM5.D.5 (local helper): `saveOutgoingContextOnCore` preserves the
object store (its only write is the outgoing TCB's register save — an insert). -/
theorem saveOutgoingContextOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (saveOutgoingContextOnCore st c).objects.invExt := by
  unfold saveOutgoingContextOnCore
  split
  · exact hInv
  · exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv

/-- WS-ZA ZA4.5: the domain switch's save and re-enqueue preserves the
object-store invariant (the re-enqueue writes run-queue links in place). -/
theorem requeueOutgoingOnCore_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (requeueOutgoingOnCore st c).objects.invExt := by
  have hS := saveOutgoingContextOnCore_preserves_objects_invExt st c hInv
  unfold requeueOutgoingOnCore; dsimp only
  split
  · exact hS
  · split
    · split
      · exact SystemState.runEnqueueAdmitted_objects_invExt _ _ _ _ hS
      · exact hS
    · exact hS

/-- WS-SM SM5.D.5 (local helper): `restoreIncomingContext` writes only the machine
register file, so the object store is unchanged. -/
theorem restoreIncomingContext_objects_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).objects = st.objects := by
  unfold restoreIncomingContext SystemState.getTcb?; split <;> rfl

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
    simp only [dispatchIdleOnCore_currentOnCore]
    unfold idleDispatchableOnCore at hd
    cases hres : st.getTcb? (idleThreadId c) with
    | none => rw [hres] at hd; simp at hd
    | some idleTcb =>
      obtain ⟨t', h', _⟩ := (dispatchIdleOnCore_objectsAgreeOffRunLinks st c).getTcb?_some hres
      exact ⟨t', h'⟩
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
    simp only [dispatchIdleOnCore_currentOnCore, dispatchIdleOnCore_activeDomainOnCore]
    unfold idleDispatchableOnCore at hd
    cases hres : st.getTcb? (idleThreadId c) with
    | none => rw [hres] at hd; simp at hd
    | some idleTcb =>
      obtain ⟨t', h', hE⟩ := (dispatchIdleOnCore_objectsAgreeOffRunLinks st c).getTcb?_some hres
      rw [hres] at hd; simp only [Bool.and_eq_true] at hd
      simp only [h', TCB.proj_eq_of_withoutRunLinks_eq TCB.domain hE]; simpa using hd.1
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
    obtain ⟨t', h', hE⟩ := (dispatchIdleOnCore_objectsAgreeOffRunLinks st c).getTcb?_some hres
    simp only [h', TCB.proj_eq_of_withoutRunLinks_eq TCB.registerContext hE]
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
    -- `idleFallbackOnCore_objects_invExt` discharges both arms (idle / `none`) at once.
    simp only [Except.ok.injEq] at hStep; subst hStep
    rw [SystemState.clearReschedulePendingOnCore_objects]
    exact idleFallbackOnCore_objects_invExt _ c (saveOutgoingContextOnCore_preserves_objects_invExt st c hInv)
  · split at hStep
    · split at hStep
      · simp only [Except.ok.injEq] at hStep; subst hStep
        rw [restoreIncomingContextOnCore_objects]
        exact SystemState.runRemoveOnCore_objects_invExt _ c _
          (saveOutgoingContextOnCore_preserves_objects_invExt st c hInv)
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
      exact requeueOutgoingOnCore_objects_invExt st c hInv

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

/-- WS-SM SM5.C: `enqueueRunnableOnCore` leaves the machine state unchanged
(it writes only the object store and the scheduler). -/
@[simp] theorem enqueueRunnableOnCore_machine_eq (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : (enqueueRunnableOnCore st c tid).machine = st.machine := by
  have h := enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c tid
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

/-- WS-SM SM5.C: `enqueueRunnableOnCore` leaves every core's `lastTimeoutErrors`
slot unchanged. -/
theorem enqueueRunnableOnCore_lastTimeoutErrorsOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueRunnableOnCore st c tid).scheduler.lastTimeoutErrorsOnCore c'
      = st.scheduler.lastTimeoutErrorsOnCore c' := by
  rcases enqueueRunnableOnCore_scheduler_cases st c tid with h | ⟨E, p, h⟩ <;> rw [h]
  simp only [SchedulerState.markReschedulePendingOnCore_lastTimeoutErrorsOnCore,
    SchedulerState.setRunQueueOnCore_lastTimeoutErrorsOnCore,
    SchedulerState.setRunQueueEndsOnCore_lastTimeoutErrorsOnCore]

/-- WS-SM SM5.D.4: `processOneReplenishmentOnCore` leaves the machine unchanged. -/
theorem processOneReplenishmentOnCore_machine_eq (st : SystemState) (ec : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) :
    (processOneReplenishmentOnCore st ec scId now).machine = st.machine := by
  rw [processOneReplenishmentOnCore, markRefillKeyChange_machine]
  simp only [refillWakeOnCore]
  split
  · split
    · rw [refillSchedContext_machine_eq]
    · dsimp only
      rw [wakeThread_state_eq_enqueue, enqueueRunnableOnCore_machine_eq, refillSchedContext_machine_eq]
  · rw [refillSchedContext_machine_eq]

/-- WS-SM SM5.D.4: `processOneReplenishmentOnCore` leaves every core's
`lastTimeoutErrors` slot unchanged. -/
theorem processOneReplenishmentOnCore_lastTimeoutErrorsOnCore_eq (st : SystemState) (ec : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (c' : CoreId) :
    (processOneReplenishmentOnCore st ec scId now).scheduler.lastTimeoutErrorsOnCore c'
      = st.scheduler.lastTimeoutErrorsOnCore c' := by
  rw [processOneReplenishmentOnCore, markRefillKeyChange_lastTimeoutErrorsOnCore]
  simp only [refillWakeOnCore]
  split
  · split
    · rw [refillSchedContext_scheduler_eq]
    · dsimp only
      rw [SchedulerState.markReschedulePendingOnCoreIf_lastTimeoutErrorsOnCore,
        wakeThread_state_eq_enqueue, enqueueRunnableOnCore_lastTimeoutErrorsOnCore,
        refillSchedContext_scheduler_eq]
  · rw [refillSchedContext_scheduler_eq]

/-- WS-SM SM5.D.4: `processReplenishmentsDueOnCore` leaves the machine unchanged —
the per-core CBS replenishment reads `now := machine.timer` but never advances the
global timer. -/
theorem processReplenishmentsDueOnCore_machine_eq (st : SystemState) (c : CoreId) (now : Nat) :
    (processReplenishmentsDueOnCore st c now).machine = st.machine :=
  processReplenishmentsDueOnCore_frame (·.machine) st c now
    (fun s scId => processOneReplenishmentOnCore_machine_eq s c scId now)
    (fun s scId => SystemState.releasePlace_machine s c scId)

/-- WS-SM SM5.D.4: `processReplenishmentsDueOnCore` leaves every core's
`lastTimeoutErrors` slot unchanged (the re-placements write only the release
queues; the wakes write run queues / objects / flags). -/
theorem processReplenishmentsDueOnCore_lastTimeoutErrorsOnCore_eq (st : SystemState)
    (c : CoreId) (now : Nat) (c' : CoreId) :
    (processReplenishmentsDueOnCore st c now).scheduler.lastTimeoutErrorsOnCore c'
      = st.scheduler.lastTimeoutErrorsOnCore c' :=
  processReplenishmentsDueOnCore_frame (·.scheduler.lastTimeoutErrorsOnCore c') st c now
    (fun s scId => processOneReplenishmentOnCore_lastTimeoutErrorsOnCore_eq s c scId now c')
    (fun s scId => SystemState.releasePlace_lastTimeoutErrorsOnCore s c scId c')

/-- WS-SM SM5.D.4: `processOneReplenishmentOnCore` leaves every core's `current`
slot unchanged — it refills a SchedContext and may *enqueue* a woken thread, but
enqueueing is not dispatching. -/
theorem processOneReplenishmentOnCore_currentOnCore_eq (st : SystemState) (ec : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (c' : CoreId) :
    (processOneReplenishmentOnCore st ec scId now).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  rw [processOneReplenishmentOnCore, markRefillKeyChange_currentOnCore]
  simp only [refillWakeOnCore]
  split
  · split
    · rw [refillSchedContext_scheduler_eq]
    · dsimp only
      rw [SchedulerState.markReschedulePendingOnCoreIf_currentOnCore,
        wakeThread_state_eq_enqueue, enqueueRunnableOnCore_currentOnCore,
        refillSchedContext_scheduler_eq]
  · rw [refillSchedContext_scheduler_eq]

/-- WS-SM SM8.B (PR #861 review round 17): `processReplenishmentsDueOnCore`
leaves every core's `current` slot unchanged: the drain refills and enqueues, and
enqueueing is not dispatching.  A core that entered the tick vacated leaves the
drain vacated; since WS-ZA ZA6.2 a drain wake that targets it raises its flag, and
the tick's local decision (`rescheduleIfPendingOnCore`) dispatches it. -/
theorem processReplenishmentsDueOnCore_currentOnCore_eq (st : SystemState)
    (c : CoreId) (now : Nat) (c' : CoreId) :
    (processReplenishmentsDueOnCore st c now).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' :=
  processReplenishmentsDueOnCore_frame (·.scheduler.currentOnCore c') st c now
    (fun s scId => processOneReplenishmentOnCore_currentOnCore_eq s c scId now c')
    (fun s scId => SystemState.releasePlace_currentOnCore s c scId c')

/-- WS-ZA ZA6.2: the drain lowers no reschedule flag. -/
theorem processReplenishmentsDueOnCore_reschedulePendingOnCore_mono (st : SystemState)
    (c : CoreId) (now : Nat) (d : CoreId) (h : st.scheduler.reschedulePendingOnCore d = true) :
    (processReplenishmentsDueOnCore st c now).scheduler.reschedulePendingOnCore d = true :=
  processReplenishmentsDueOnCore_induction (fun s => s.scheduler.reschedulePendingOnCore d = true)
    st c now
    (fun s scId hA => processOneReplenishmentOnCore_reschedulePendingOnCore_mono _ c scId now d hA)
    (fun s scId hA => by simpa only [SystemState.releasePlace_reschedulePendingOnCore] using hA) h

/-- WS-ZA ZA6.3: the states the drain reaches from `st` with `f` heads still to
take, each with the fuel it has left — the loop's trace, as the drain's
statements about a step part way through it read it. -/
inductive DrainReaches (c : CoreId) (now : Nat) (f₀ : Nat) (st : SystemState) :
    Nat → SystemState → Prop
  | start : DrainReaches c now f₀ st f₀ st
  | step {g : Nat} {pre : SystemState} :
      DrainReaches c now f₀ st (g + 1) pre →
      pre.scheduler.releaseHeadOnCore c ≠ 0 →
      pre.releaseAtOn c (ReleaseChain.decode (pre.scheduler.releaseHeadOnCore c)) ≤ now →
      DrainReaches c now f₀ st g
        ((processOneReplenishmentOnCore pre c
          (ReleaseChain.decode (pre.scheduler.releaseHeadOnCore c)) now).releasePlace c
          (ReleaseChain.decode (pre.scheduler.releaseHeadOnCore c)))

/-- The drain from `st` is the drain from any state it reaches, with the fuel
left there. -/
theorem DrainReaches.drain_eq {c : CoreId} {now f₀ : Nat} {st : SystemState} {g : Nat}
    {pre : SystemState} (h : DrainReaches c now f₀ st g pre) :
    drainDueOnCore c now f₀ st = drainDueOnCore c now g pre := by
  induction h with
  | start => rfl
  | step _ hH hD ih =>
    rw [ih, drainDueOnCore.eq_2, if_neg hH, if_pos hD]

/-- WS-ZA ZA6.2 / ZA6.3 (the drain's completeness over the flags): every head the
drain takes whose refill wakes a thread the store holds — whether the wake placed
it or found it already queued — leaves the thread's target core flagged at the
end of the drain.  `pre` is the drain's state when it takes that head, a state
it reaches (`DrainReaches`), and the flag survives the head's re-placement and
the rest of the drain (`processReplenishmentsDueOnCore_reschedulePendingOnCore_mono`). -/
theorem processReplenishmentsDueOnCore_flags_wake_target (st : SystemState) (c : CoreId)
    (now : Nat) (g : Nat) (pre : SystemState)
    (hReach : DrainReaches c now (st.scheduler.releaseCountOnCore c) st (g + 1) pre)
    (hHead : pre.scheduler.releaseHeadOnCore c ≠ 0)
    (hDue : pre.releaseAtOn c (ReleaseChain.decode (pre.scheduler.releaseHeadOnCore c)) ≤ now)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTarget : replenishWakeTarget pre
      (refillSchedContext pre (ReleaseChain.decode (pre.scheduler.releaseHeadOnCore c)) now)
      (ReleaseChain.decode (pre.scheduler.releaseHeadOnCore c)) = some tid)
    (hTcb : (refillSchedContext pre
      (ReleaseChain.decode (pre.scheduler.releaseHeadOnCore c)) now).getTcb? tid = some tcb)
    (hNotRunning : runningOnSomeCore (refillSchedContext pre
      (ReleaseChain.decode (pre.scheduler.releaseHeadOnCore c)) now) tid = false) :
    (processReplenishmentsDueOnCore st c now).scheduler.reschedulePendingOnCore
      (determineTargetCore (refillSchedContext pre
        (ReleaseChain.decode (pre.scheduler.releaseHeadOnCore c)) now) tid) = true := by
  unfold processReplenishmentsDueOnCore
  rw [(hReach.step hHead hDue).drain_eq]
  have hMark := cbsReplenish_can_wake_remote_core pre c _ now tid tcb hTarget hTcb hNotRunning
  generalize determineTargetCore _ tid = d at hMark ⊢
  refine drainDueOnCore_induction (fun s => s.scheduler.reschedulePendingOnCore d = true) c now
    (fun s scId hA => processOneReplenishmentOnCore_reschedulePendingOnCore_mono _ c scId now d hA)
    (fun s scId hA => by simpa only [SystemState.releasePlace_reschedulePendingOnCore] using hA) g _ ?_
  simpa only [SystemState.releasePlace_reschedulePendingOnCore] using hMark

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` leaves every core's
`lastTimeoutErrors` slot unchanged (it writes only domain slots). -/
theorem decrementDomainTimeOnCore_lastTimeoutErrorsOnCore (st : SystemState) (c c' : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.lastTimeoutErrorsOnCore c'
      = st.scheduler.lastTimeoutErrorsOnCore c' := by
  simp [decrementDomainTimeOnCore, SchedulerState.setDomainTimeRemainingOnCore_lastTimeoutErrorsOnCore]

/-- WS-SM SM5.D.2: the prepared state preserves the machine — the per-core tick
reads `machine.timer` but never advances the global timer. -/
theorem timerTickOnCorePrepared_machine_eq (st : SystemState) (c : CoreId) :
    (timerTickOnCorePrepared st c).machine = st.machine := by
  simp only [timerTickOnCorePrepared]
  rw [processReplenishmentsDueOnCore_machine_eq]

/-- WS-SM SM5.D.9: the prepared state has core `c`'s `lastTimeoutErrors` cleared —
the tick clears core `c`'s diagnostic at entry, and the replenishment step never
re-sets it. -/
theorem timerTickOnCorePrepared_lastTimeoutErrors_eq (st : SystemState) (c : CoreId) :
    (timerTickOnCorePrepared st c).scheduler.lastTimeoutErrorsOnCore c = [] := by
  simp only [timerTickOnCorePrepared]
  rw [processReplenishmentsDueOnCore_lastTimeoutErrorsOnCore_eq]
  simp [SchedulerState.setLastTimeoutErrorsOnCore_lastTimeoutErrorsOnCore_self]

/-- WS-SM SM8.B (PR #861 review round 17): the prepared state does not dispatch —
it leaves every core's `current` slot exactly as it found it. -/
theorem timerTickOnCorePrepared_currentOnCore_eq (st : SystemState) (c c' : CoreId) :
    (timerTickOnCorePrepared st c).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  simp only [timerTickOnCorePrepared]
  rw [processReplenishmentsDueOnCore_currentOnCore_eq]
  simp [SchedulerState.setLastTimeoutErrorsOnCore_currentOnCore]

/-- WS-SM SM8.B (PR #861 review round 17): **the timer tick cannot rescue a
vacated core** on its own: a core that enters its tick with no current thread,
and whose reschedule flag is down once the drain has run (`hNoWake`: no drain
wake staled its decision and no earlier entry did), leaves it with no current
thread, regardless of what its run queue holds.

This is what made the round-17 finding a defect rather than a latency
question: the blocking IPC legs vacate the caller's core, and absent the
`scheduleLocalSuccessor` seam nothing dispatches that core until some
*unrelated* transition pokes it.  **The one event the tick itself produces**
(PR #880 round 7) is a drain wake that targets this very core: since WS-ZA
ZA6.2 it raises the core's flag (`cbsReplenish_can_wake_remote_core`), and the
tick's local decision dispatches it — `hNoWake` is what excludes that arm here,
and `timerTickOnCore_idle_local_wake_reschedules` pins the dispatch. -/
theorem timerTickOnCore_cannot_dispatch_vacated_core (st : SystemState) (c : CoreId)
    (hIdle : st.scheduler.currentOnCore c = none)
    (hNoWake : (timerTickOnCorePrepared st c).scheduler.reschedulePendingOnCore c = false) :
    (timerTickOnCore st c).scheduler.currentOnCore c = none := by
  rw [timerTickOnCore_eq_prepared, timerTickOnCorePrepared_currentOnCore_eq st c c, hIdle]
  simp only [rescheduleIfPendingOnCore, hNoWake, Bool.false_eq_true, if_false]
  rw [timerTickOnCorePrepared_currentOnCore_eq, hIdle]

/-- WS-SM SM5.D.2 (preservation): the prepared state preserves the object-store
invariant (the SM5.D.4 replenishment preserves it). -/
theorem timerTickOnCorePrepared_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (timerTickOnCorePrepared st c).objects.invExt := by
  simp only [timerTickOnCorePrepared]
  exact processReplenishmentsDueOnCore_preserves_objects_invExt _ c _ hInv

-- ── SM5.D.2 headline theorems ──

/-- WS-SM SM5.D.2: on the quiet idle path (core `c` has no current thread in the
prepared state — e.g. a freshly-booted or freshly-idled core — and its flag is
down), the tick is exactly the prepared state: the SM5.D.4 replenishment with no
budget charge and no dispatch.  With the flag up the idle arm instead runs the
local decision — see `timerTickOnCore_idle_local_wake_reschedules`. -/
theorem timerTickOnCore_idle (st : SystemState) (c : CoreId)
    (hCur : (timerTickOnCorePrepared st c).scheduler.currentOnCore c = none)
    (hNoWake : (timerTickOnCorePrepared st c).scheduler.reschedulePendingOnCore c = false) :
    timerTickOnCore st c = timerTickOnCorePrepared st c := by
  rw [timerTickOnCore_eq_prepared, hCur]
  simp only [rescheduleIfPendingOnCore, hNoWake, Bool.false_eq_true, if_false]

/-- WS-SM (PR #880 round 7): a local replenish wake **dispatches an idle-slot
core**.  When core `c` has no current thread in the prepared state but its flag
is up — a drain wake targeted core `c` itself — the tick runs the receiver-side
reschedule decision (whose gate admits any candidate on an idle core), so the
refilled thread is dispatched by the very tick that made it eligible instead of
stranding until an unrelated cross-core poke. -/
theorem timerTickOnCore_idle_local_wake_reschedules (st : SystemState) (c : CoreId)
    (hCur : (timerTickOnCorePrepared st c).scheduler.currentOnCore c = none)
    (hWake : (timerTickOnCorePrepared st c).scheduler.reschedulePendingOnCore c = true) :
    timerTickOnCore st c = handleRescheduleOnCoreState (timerTickOnCorePrepared st c) c := by
  rw [timerTickOnCore_eq_prepared, hCur]
  simp only [rescheduleIfPendingOnCore, hWake, if_true]

/-- WS-SM SM5.D.2 (the headline `timerTickOnCore_advances_per_core`, plan §6.1): the
per-core tick **advances core `c`'s local accounting without advancing the global
timer** — `st'.machine = st.machine`.  This is the defining SMP property: each
core's CNTP fires and the tick processes that core's state locally, but the global
monotonic tick counter (`machine.timer`) is owned by a single authority — the
boot core's committed run-loop step (`tickClockedState` in `PerCoreRunLoop.lean`),
mirroring the Rust HAL's primary-owned `TICK_COUNT`.  Stated on the quiet idle
path (where the tick makes no register-context write, so the *whole* machine is
preserved); the global-timer field specifically is preserved on every path. -/
theorem timerTickOnCore_advances_per_core (st : SystemState) (c : CoreId)
    (hCur : (timerTickOnCorePrepared st c).scheduler.currentOnCore c = none)
    (hNoWake : (timerTickOnCorePrepared st c).scheduler.reschedulePendingOnCore c = false) :
    (timerTickOnCore st c).machine = st.machine := by
  rw [timerTickOnCore_idle st c hCur hNoWake, timerTickOnCorePrepared_machine_eq]

/-- WS-SM SM5.D.9: on the quiet idle path, the tick leaves core `c`'s
`lastTimeoutErrors` cleared — a stale timeout-error record never survives a tick. -/
theorem timerTickOnCore_clears_lastTimeoutErrors (st : SystemState) (c : CoreId)
    (hCur : (timerTickOnCorePrepared st c).scheduler.currentOnCore c = none)
    (hNoWake : (timerTickOnCorePrepared st c).scheduler.reschedulePendingOnCore c = false) :
    (timerTickOnCore st c).scheduler.lastTimeoutErrorsOnCore c = [] := by
  rw [timerTickOnCore_idle st c hCur hNoWake, timerTickOnCorePrepared_lastTimeoutErrors_eq]

-- WS-SM SM5.D.6 (audit-pass-2): the per-core *timer tick* deliberately does **no**
-- in-tick domain rotation.  Domain rotation is the separate, atomic
-- `scheduleDomainOnCore` transition (its boundary branch is `switchDomainOnCore` +
-- `scheduleEffectiveOnCore`); `switchDomainOnCore_rotates` (§4b) is the rotation
-- witness.  This is exactly the single-core split (`timerTickWithBudget` never
-- rotates; `scheduleDomain` does), and it is what keeps a running thread from
-- outliving its domain (`currentThreadInActiveDomain` faithfulness).

/-- WS-SM SM5.D.5 (the headline `timerTickOnCore_preempts_local`, plan §6.1): when
core `c`'s current thread `tid` (in the prepared state) is preempted by the budget
tick (`timerTickBudgetOnCore … = (st3, true)` — time-slice / budget exhausted),
the tick re-selects and dispatches via the budget-aware dispatch — the per-core
local preemption. -/
theorem timerTickOnCore_preempts_local (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st3 : SystemState)
    (hCur : (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid)
    (hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb)
    (hBud : timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, true)) :
    timerTickOnCore st c = scheduleEffectiveOnCoreState st3 c := by
  rw [timerTickOnCore_eq_prepared]
  simp only [hCur, timerTickChargeCurrentOnCore_eq hTcb, hBud]

/-- WS-SM SM5.D.2 (preservation): the per-core timer tick preserves the RobinHood
object-store invariant (`objects.invExt`) through the whole composition — the
SM5.D.9 clear (object-neutral), the SM5.D.4 replenishment (preserves), the SM5.D.5
budget tick (preserves, incl. the IPC-timeout chain), the dispatch and the local
decision (preserve). -/
theorem timerTickOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (timerTickOnCore st c).objects.invExt := by
  have hPrep : (timerTickOnCorePrepared st c).objects.invExt :=
    timerTickOnCorePrepared_objects_invExt st c hInv
  have hR : ∀ s, s.objects.invExt → (rescheduleIfPendingOnCore s c).objects.invExt := fun s hs =>
    rescheduleIfPendingOnCore_of (P := fun s => s.objects.invExt) s c hs
      (handleRescheduleSgiOnCore_preserves_objects_invExt _ c _ hs
        (handleRescheduleSgiOnCore_eq_state s c))
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, _, hB, h⟩ |
      ⟨tid, tcb, hTcb, st3, _, hB, h⟩ <;> rw [h]
  · exact hR _ hPrep
  · exact hR _ hPrep
  · exact scheduleEffectiveOnCore_preserves_objects_invExt _ c _
      (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrep hB)
      (scheduleEffectiveOnCore_eq_state st3 c)
  · exact hR _ (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrep hB)

-- ============================================================================
-- §6  SM5.D.8 — Tick decidability (for the SM5.D.10 unit tests)
-- ============================================================================

/-- WS-SM SM5.D.8: does the per-core budget tick preempt the current thread (the
`wasPreempted` flag)?  Decidable.  Stated over the store's own witness that `tid`
resolves to `tcb` (raw-write migration Cut B2), because the tick is. -/
def timerTickBudgetOnCorePreempts (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) : Prop :=
  (timerTickBudgetOnCore st c tid tcb hTcb).2 = true

instance (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) :
    Decidable (timerTickBudgetOnCorePreempts st c tid tcb hTcb) := by
  unfold timerTickBudgetOnCorePreempts; infer_instance

-- ============================================================================
-- §7  SM5.D.5/.6 — per-core invariant preservation (the SM5.C-parity coverage)
--
--   The composed `timerTickOnCore` preserves the SM4.C per-core scheduler
--   invariants.  The tick is total (WS-ZA ZA6.2), so each theorem concludes
--   `P (timerTickOnCore st c)` by casing on `timerTickOnCore_cases`: the idle
--   core and an unresolved current thread end in the local decision on the
--   prepared state, a preempting charge ends in the dispatch (which
--   re-establishes validity, consistency and the context match), and a
--   non-preempting charge ends in the local decision on the charged state.
--   The facts about the prepared phase (`hPrep*`) and about the budget tick's
--   run-queue effect (`hBudget*`) are hypotheses here; `PerCoreInvariantSuite`
--   discharges both, the latter over all four budget outcomes — the exhausted
--   branch's timeout wakes included — through
--   `timerTickBudgetOnCore_preserves_runQueueSafetyOnCore`.
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
  unfold saveOutgoingContextOnCore
  split
  · rfl
  · exact SystemState.updateTcb_scheduler _ _ _

/-- WS-SM SM5.I (frame helper): the idle fallback frames every *sibling* core's
`current` slot — both arms (idle dispatch / `current = none`) write only core
`c`'s slot. -/
theorem idleFallbackOnCore_currentOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (idleFallbackOnCore st c).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  unfold idleFallbackOnCore
  split
  · simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ h,
      restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
      SchedulerState.setRunQueueEndsOnCore_currentOnCore, 
      SchedulerState.setRunQueueOnCore_currentOnCore]
  · simp only [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ h]

/-- WS-SM SM5.I (frame helper): the idle fallback frames every *sibling* core's
run queue. -/
theorem idleFallbackOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (idleFallbackOnCore st c).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold idleFallbackOnCore
  split
  · simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_runQueueOnCore,
      restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
      SchedulerState.setRunQueueEndsOnCore_runQueueOnCore,
      SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ h]
  · simp only [SchedulerState.setCurrentOnCore_runQueueOnCore]

/-- WS-SM SM5.I.8 (other-core frame for the dispatcher): a per-core dispatch on
core `c` leaves every *sibling* core's `current` and `runQueue` slots untouched.
The dispatch's only scheduler writes are core `c`'s `setRunQueueOnCore` (dequeue)
and `setCurrentOnCore`; `saveOutgoingContextOnCore` / `restoreIncomingContext`
leave the scheduler structure intact (they touch only the object store /
`machine.regs`).  Proved over all OK branches (idle fallback + thread dispatch);
the error branch is impossible under `hStep`. -/
theorem scheduleEffectiveOnCore_independent_of_other_core (st : SystemState)
    (c c' : CoreId) (st' : SystemState) (hcc : c ≠ c')
    (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c'
      ∧ st'.scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      refine ⟨?_, ?_⟩
      · rw [SystemState.clearReschedulePendingOnCore_scheduler,
          SchedulerState.clearReschedulePendingOnCore_currentOnCore,
          idleFallbackOnCore_currentOnCore_ne _ c c' hcc, saveOutgoingContextOnCore_scheduler_eq]
      · rw [SystemState.clearReschedulePendingOnCore_scheduler,
          SchedulerState.clearReschedulePendingOnCore_runQueueOnCore,
          idleFallbackOnCore_runQueueOnCore_ne _ c c' hcc, saveOutgoingContextOnCore_scheduler_eq]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          refine ⟨?_, ?_⟩
          · simp only [SchedulerState.clearReschedulePendingOnCore_currentOnCore,
              SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hcc,
              restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
      SchedulerState.setRunQueueEndsOnCore_currentOnCore, 
      SchedulerState.setRunQueueOnCore_currentOnCore,
              saveOutgoingContextOnCore_scheduler_eq]
          · simp only [SchedulerState.clearReschedulePendingOnCore_runQueueOnCore,
              SchedulerState.setCurrentOnCore_runQueueOnCore,
              restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
      SchedulerState.setRunQueueEndsOnCore_runQueueOnCore,
              SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hcc,
              saveOutgoingContextOnCore_scheduler_eq]
        · simp at hStep

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
        simp only [saveOutgoingContextOnCore, hcur, SystemState.updateTcb_eq_self_of_none hout]]; exact h
    | some outTcb =>
      obtain ⟨t, ht⟩ := h
      by_cases hEq : tid = outTid
      · subst hEq
        refine ⟨{ outTcb with registerContext := st.machine.regsOnCore c }, ?_⟩
        simp only [saveOutgoingContextOnCore, hcur, SystemState.updateTcb_eq_of_some hout]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
      · refine ⟨t, ?_⟩
        have hNeO : ¬ (outTid.toObjId == tid.toObjId) = true := fun he =>
          hEq (ThreadId.toObjId_injective _ _ (by simpa using he)).symm
        simp only [saveOutgoingContextOnCore, hcur, SystemState.updateTcb_eq_of_some hout]
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
            simp only [saveOutgoingContextOnCore, hcur, SystemState.updateTcb_eq_self_of_none hout]]; exact htcb
      | some outTcb =>
          by_cases hEq : tid = outTid
          · subst hEq
            refine ⟨{ outTcb with registerContext := st.machine.regsOnCore c₀ }, ?_, ?_⟩
            · simp only [saveOutgoingContextOnCore, hcur, SystemState.updateTcb_eq_of_some hout]
              simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
              rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
            · exact Or.inr ⟨rfl, rfl⟩
          · refine ⟨tcb, ?_, Or.inl rfl⟩
            have hNeO : ¬ (outTid.toObjId == tid.toObjId) = true := fun he =>
              hEq (ThreadId.toObjId_injective _ _ (by simpa using he)).symm
            simp only [saveOutgoingContextOnCore, hcur, SystemState.updateTcb_eq_of_some hout]
            simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
            rw [RobinHood.RHTable.getElem?_insert_ne st.objects outTid.toObjId tid.toObjId
              _ hNeO hInv]
            simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using htcb

-- ── §7c  `scheduleEffectiveOnCore` preservation / establishment ──

/-- WS-SM SM5.D.5 (object frame): in every OK branch (idle dispatch and
thread dispatch), `scheduleEffectiveOnCore` writes the object store only through
`saveOutgoingContextOnCore` past the run-queue links its dequeue rewrites (WS-ZA
ZA4.5) — the restore / set-current steps are object-neutral. -/
theorem scheduleEffectiveOnCore_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (st' : SystemState) (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.objectsAgreeOffRunLinks (saveOutgoingContextOnCore st c) := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      exact .trans (.of_objects_eq (SystemState.clearReschedulePendingOnCore_objects _ _))
        (idleFallbackOnCore_objectsAgreeOffRunLinks _ c)
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep; subst hStep
          exact .trans (.of_objects_eq (restoreIncomingContextOnCore_objects _ _ _))
            (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ c tid)
        · simp at hStep

/-- WS-SM SM5.D.5 (frame): `scheduleEffectiveOnCore` preserves TCB-resolvability of
any thread (its only object write is the outgoing register-context save). -/
theorem scheduleEffectiveOnCore_getTcb?_isSome (st : SystemState) (c : CoreId)
    (st' : SystemState) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') (h : ∃ t, st.getTcb? tid = some t) :
    ∃ t, st'.getTcb? tid = some t := by
  have hA := scheduleEffectiveOnCore_objectsAgreeOffRunLinks st c st' hStep
  obtain ⟨t, ht⟩ := saveOutgoingContextOnCore_getTcb?_isSome st c tid hInv h
  obtain ⟨t', ht', _⟩ := hA.getTcb?_some ht
  exact ⟨t', ht'⟩

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
          simp only [SchedulerState.clearReschedulePendingOnCore_runQueueOnCore,
            SchedulerState.setCurrentOnCore_runQueueOnCore,
            restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
      SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
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
          simp only [SchedulerState.clearReschedulePendingOnCore_currentOnCore,
            SchedulerState.setCurrentOnCore_currentOnCore_self]
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
          simp only [SchedulerState.clearReschedulePendingOnCore_currentOnCore,
            SchedulerState.clearReschedulePendingOnCore_runQueueOnCore,
            SchedulerState.setCurrentOnCore_currentOnCore_self,
            SchedulerState.setCurrentOnCore_runQueueOnCore, restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
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
          obtain ⟨savedTcb, hSaved⟩ :=
            saveOutgoingContextOnCore_getTcb?_isSome st c tid hInv ⟨tcb, hTcb⟩
          obtain ⟨deqTcb, hDeqGt, _⟩ :=
            (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ c tid).getTcb?_some hSaved
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
          simp only [SchedulerState.clearReschedulePendingOnCore_runQueueOnCore,
            SchedulerState.setCurrentOnCore_runQueueOnCore,
            restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
      SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at hx
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
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', false)) :
    st'.scheduler = st.scheduler := by
  cases hb : tcb.schedContextBinding with
  | unbound =>
    by_cases hsl : tcb.timeSlice ≤ 1
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_pos hsl, Prod.mk.injEq] at hStep
      exact absurd hStep.2 (by decide)
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_neg hsl, Prod.mk.injEq] at hStep
      rw [← hStep.1]
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      rfl
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
        rw [← hStep.1]
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      rfl
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
        rw [← hStep.1]

/-- WS-SM SM5.D.5 (frame): a not-preempted budget tick keeps the charged thread
`tid` a TCB.  Unbound: writes `tid`'s TCB with a decremented time-slice.  Bound:
writes the SchedContext at `scId` — a *different* key from `tid` (both lookups
succeed, so the keys are distinct), leaving `tid`'s TCB untouched.  AK7-clean. -/
theorem timerTickBudgetOnCore_notPreempted_getTcb?_tid (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (hInv : st.objects.invExt)
    (hCur : st.getTcb? tid = some tcb)
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', false)) :
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
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_pos hsl, Prod.mk.injEq] at hStep
      exact absurd hStep.2 (by decide)
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_neg hsl, Prod.mk.injEq] at hStep
      rw [← hStep.1]
      simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?,
        RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
      exact ⟨_, rfl⟩
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      exact ⟨tcb, hCur⟩
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
        refine ⟨tcb, ?_⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hCur
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      exact ⟨tcb, hCur⟩
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
        refine ⟨tcb, ?_⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hCur

-- ── §7e  Composed `timerTickOnCore` invariant preservation ──

/-- WS-SM SM5.D.5/.6 (the headline B1 preservation): the per-core timer tick
preserves per-core current-thread validity.  Four cases (`timerTickOnCore_cases`):
the idle path and an unresolved current thread run the local decision on the
prepared state, which keeps validity (`hPrep`, the prepared state's validity —
the drain dispatches nothing and keeps every TCB, discharged in
`PerCoreInvariantSuite.lean`; it is what makes the unresolved arm unreachable,
since the tick charges such a thread nothing); the not-preempted budget tick
keeps the charged current thread a TCB
(`timerTickBudgetOnCore_notPreempted_getTcb?_tid`), and the local decision keeps
it; the preempted path re-establishes validity from scratch via
`scheduleEffectiveOnCore_establishes_currentThreadValidOnCore`. -/
theorem timerTickOnCore_preserves_currentThreadValidOnCore (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt)
    (hPrep : currentThreadValidOnCore (timerTickOnCorePrepared st c) c) :
    currentThreadValidOnCore (timerTickOnCore st c) c := by
  have hPrepInv : (timerTickOnCorePrepared st c).objects.invExt :=
    timerTickOnCorePrepared_objects_invExt st c hInv
  have hR : ∀ s, s.objects.invExt → currentThreadValidOnCore s c →
      currentThreadValidOnCore (rescheduleIfPendingOnCore s c) c := fun s hs hv =>
    rescheduleIfPendingOnCore_of (P := fun s => currentThreadValidOnCore s c) s c hv
      (handleRescheduleSgiOnCore_preserves_currentThreadValidOnCore s c _ hs hv
        (handleRescheduleSgiOnCore_eq_state s c))
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, _, hB, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ <;> rw [h]
  · exact hR _ hPrepInv hPrep
  · exact hR _ hPrepInv hPrep
  · exact scheduleEffectiveOnCore_establishes_currentThreadValidOnCore st3 c _
      (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hB)
      (scheduleEffectiveOnCore_eq_state st3 c)
  · have hV3 : currentThreadValidOnCore st3 c := by
      simp only [currentThreadValidOnCore,
        timerTickBudgetOnCore_notPreempted_scheduler_eq _ c tid tcb st3 hB, hCur]
      exact timerTickBudgetOnCore_notPreempted_getTcb?_tid _ c tid tcb st3 hPrepInv hTcb hB
    exact hR _ (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hB) hV3

/-- WS-SM SM5.D.2 (B2 helper): the prepared state preserves per-core run-queue
well-formedness — the SM5.D.4 replenishment preserves it (wakes `insert`); the tick
does no in-tick domain step (audit-pass-2). -/
theorem timerTickOnCorePrepared_runQueueOnCore_wellFormed (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed) :
    ((timerTickOnCorePrepared st c).scheduler.runQueueOnCore c).wellFormed := by
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

/-- Dequeue-on-dispatch consistency on core `c` reads only `c`'s current slot and
run queue. -/
theorem queueCurrentConsistentOnCore_of_slots {s s' : SchedulerState} {c : CoreId}
    (hCur : s'.currentOnCore c = s.currentOnCore c) (hRq : s'.runQueueOnCore c = s.runQueueOnCore c)
    (h : queueCurrentConsistentOnCore s c) : queueCurrentConsistentOnCore s' c := by
  unfold queueCurrentConsistentOnCore at h ⊢
  rw [hCur, hRq]; exact h

/-- `processOneReplenishmentOnCore` preserves dequeue-on-dispatch consistency on
**every** core `c'`: the refill frames the scheduler, and the wake fires only when
the woken thread is not running anywhere (so it is not `c'`'s current thread) —
exactly `wakeThread_preserves_queueCurrentConsistentOnCore`'s precondition. -/
theorem processOneReplenishmentOnCore_preserves_queueCurrentConsistentOnCore (st : SystemState)
    (execCore c' : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hcons : queueCurrentConsistentOnCore st.scheduler c') :
    queueCurrentConsistentOnCore (processOneReplenishmentOnCore st execCore scId now).scheduler c' := by
  have hRef : queueCurrentConsistentOnCore (refillSchedContext st scId now).scheduler c' := by
    rw [refillSchedContext_scheduler_eq]; exact hcons
  rw [processOneReplenishmentOnCore]
  refine queueCurrentConsistentOnCore_of_slots (markRefillKeyChange_currentOnCore _ _ _ c')
    (markRefillKeyChange_runQueueOnCore _ _ _ c') ?_
  simp only [refillWakeOnCore]
  split
  next tid _heq =>
    split
    next _hrun => exact hRef
    next hcond =>
      have hW := wakeThread_preserves_queueCurrentConsistentOnCore (refillSchedContext st scId now)
        tid execCore c'
        (runningOnSomeCore_eq_false_currentOnCore_ne (Bool.not_eq_true _ |>.mp hcond) _) hRef
      simpa only [queueCurrentConsistentOnCore, SchedulerState.markReschedulePendingOnCoreIf_currentOnCore,
        SchedulerState.markReschedulePendingOnCoreIf_runQueueOnCore] using hW
  next _heq => exact hRef

/-- WS-SM SM5.I.8 (prepared discharge): `processReplenishmentsDueOnCore` preserves
dequeue-on-dispatch consistency on core `c`. -/
theorem processReplenishmentsDueOnCore_preserves_queueCurrentConsistentOnCore (st : SystemState)
    (c : CoreId) (now : Nat) (hcons : queueCurrentConsistentOnCore st.scheduler c) :
    queueCurrentConsistentOnCore (processReplenishmentsDueOnCore st c now).scheduler c :=
  processReplenishmentsDueOnCore_induction (fun s => queueCurrentConsistentOnCore s.scheduler c)
    st c now
    (fun s scId h => processOneReplenishmentOnCore_preserves_queueCurrentConsistentOnCore
      s c c scId now h)
    (fun s scId h => by
      simpa only [queueCurrentConsistentOnCore, SystemState.releasePlace_currentOnCore,
        SystemState.releasePlace_runQueueOnCore] using h) hcons

/-- WS-SM SM5.I.8 (prepared discharge): the prepared phase preserves
`queueCurrentConsistentOnCore` — discharges the capstone's `hPrepQcc`. -/
theorem timerTickOnCorePrepared_preserves_queueCurrentConsistentOnCore (st : SystemState)
    (c : CoreId) (hcons : queueCurrentConsistentOnCore st.scheduler c) :
    queueCurrentConsistentOnCore (timerTickOnCorePrepared st c).scheduler c := by
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
    ((processOneReplenishmentOnCore st execCore scId now).scheduler.runQueueOnCore c').toList.Nodup := by
  have hRef : ((refillSchedContext st scId now).scheduler.runQueueOnCore c').toList.Nodup := by
    rw [refillSchedContext_scheduler_eq]; exact hnd
  rw [processOneReplenishmentOnCore, markRefillKeyChange_runQueueOnCore]
  simp only [refillWakeOnCore]
  split
  next tid _heq =>
    split
    next _hrun => exact hRef
    next _hcond =>
      simpa only [SchedulerState.markReschedulePendingOnCoreIf_runQueueOnCore] using
        wakeThread_preserves_runQueueUniqueOnCore (refillSchedContext st scId now)
          tid execCore c' hRef
  next _heq => exact hRef

/-- WS-SM SM5.I.8 (prepared discharge): `processReplenishmentsDueOnCore` preserves
run-queue `Nodup` on core `c`. -/
theorem processReplenishmentsDueOnCore_preserves_runQueueUnique (st : SystemState)
    (c : CoreId) (now : Nat) (hnd : (st.scheduler.runQueueOnCore c).toList.Nodup) :
    ((processReplenishmentsDueOnCore st c now).scheduler.runQueueOnCore c).toList.Nodup :=
  processReplenishmentsDueOnCore_induction (fun s => (s.scheduler.runQueueOnCore c).toList.Nodup)
    st c now
    (fun s scId h => processOneReplenishmentOnCore_preserves_runQueueUnique s c c scId now h)
    (fun s scId h => by simpa only [SystemState.releasePlace_runQueueOnCore] using h) hnd

/-- WS-SM SM5.I.8 (prepared discharge): the prepared phase preserves run-queue
`Nodup` — discharges the capstone's `hPrepNd`. -/
theorem timerTickOnCorePrepared_preserves_runQueueUnique (st : SystemState) (c : CoreId)
    (hnd : (st.scheduler.runQueueOnCore c).toList.Nodup) :
    ((timerTickOnCorePrepared st c).scheduler.runQueueOnCore c).toList.Nodup := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_runQueueUnique
  simpa only [SchedulerState.setLastTimeoutErrorsOnCore_runQueueOnCore] using hnd

/-- WS-SM SM5.D.5 (B2 discharge, clean path): a *not-preempted* budget tick
preserves per-core run-queue well-formedness — its scheduler is unchanged
(`timerTickBudgetOnCore_notPreempted_scheduler_eq`).  The preempting outcomes,
the exhausted branch's timeout wakes among them, are covered by
`timerTickBudgetOnCore_preserves_runQueueSafetyOnCore` (`PerCoreInvariantSuite`). -/
theorem timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCoreWellFormed
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', false)) :
    (st'.scheduler.runQueueOnCore c).wellFormed := by
  rw [timerTickBudgetOnCore_notPreempted_scheduler_eq st c tid tcb st' hStep]; exact hwf

/-- WS-SM SM5.D.5/.6 (B2 preservation): the per-core timer tick preserves per-core
run-queue well-formedness, given that the budget tick preserves it
(`hBudgetRqWf`).  The idle and unresolved paths are the local decision on the
prepared state (well-formed via `timerTickOnCorePrepared_runQueueOnCore_wellFormed`);
the not-preempted path is the local decision on the budget result; the preempted
path dequeues-on-dispatch via
`scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed`.  `hBudgetRqWf` is
discharged over every budget outcome by
`timerTickBudgetOnCore_preserves_runQueueSafetyOnCore`. -/
theorem timerTickOnCore_preserves_runQueueOnCoreWellFormed (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hBudgetRqWf : ∀ tid tcb st3 b,
       (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid →
       ∀ (hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb),
       timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, b) →
       (st3.scheduler.runQueueOnCore c).wellFormed) :
    ((timerTickOnCore st c).scheduler.runQueueOnCore c).wellFormed := by
  have hPrep := timerTickOnCorePrepared_runQueueOnCore_wellFormed st c hwf
  have hR : ∀ s, (s.scheduler.runQueueOnCore c).wellFormed →
      ((rescheduleIfPendingOnCore s c).scheduler.runQueueOnCore c).wellFormed := fun s hs =>
    rescheduleIfPendingOnCore_of (P := fun s => (s.scheduler.runQueueOnCore c).wellFormed) s c hs
      (handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed s c _ hs
        (handleRescheduleSgiOnCore_eq_state s c))
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ <;> rw [h]
  · exact hR _ hPrep
  · exact hR _ hPrep
  · exact scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed st3 c _
      (hBudgetRqWf tid tcb st3 true hCur hTcb hB) (scheduleEffectiveOnCore_eq_state st3 c)
  · exact hR _ (hBudgetRqWf tid tcb st3 false hCur hTcb hB)

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
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', false))
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
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_pos hsl, Prod.mk.injEq] at hStep
      exact absurd hStep.2 (by decide)
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_neg hsl, Prod.mk.injEq] at hStep
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
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      exact ⟨t, hx⟩
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
        refine ⟨t, ?_⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId x.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hx
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      exact ⟨t, hx⟩
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
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
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', false)) :
    runnableThreadsAreTCBsOnCore st' c := by
  intro x hx
  have hsch := timerTickBudgetOnCore_notPreempted_scheduler_eq st c tid tcb st' hStep
  rw [hsch] at hx
  obtain ⟨t, ht⟩ := h x hx
  exact timerTickBudgetOnCore_notPreempted_getTcb?_forward st c tid tcb st' hInv hStep x t ht

/-- WS-SM SM5.I.8: the per-core timer tick preserves `runnableThreadsAreTCBsOnCore`,
given the prepared state satisfies it (`hPrepRat`) and the budget tick preserves it
(`hBudgetRat`).  Idle path = the local decision on the prepared state; preempted path via
`scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore` (the dispatched
state's invExt is the budget result's, via `timerTickBudgetOnCore_preserves_objects_invExt`);
not-preempted path = budget result.  `hBudgetRat` is discharged on every clean path
by `timerTickBudgetOnCore_notPreempted_preserves_runnableThreadsAreTCBsOnCore`. -/
theorem timerTickOnCore_preserves_runnableThreadsAreTCBsOnCore (st : SystemState) (c : CoreId)
    (hPrepInv : (timerTickOnCorePrepared st c).objects.invExt)
    (hPrepRat : runnableThreadsAreTCBsOnCore (timerTickOnCorePrepared st c) c)
    (hPrepCtv : currentThreadValidOnCore (timerTickOnCorePrepared st c) c)
    (hBudgetRat : ∀ tid tcb st3 b,
       (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid →
       ∀ (hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb),
       timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, b) →
       runnableThreadsAreTCBsOnCore st3 c) :
    runnableThreadsAreTCBsOnCore (timerTickOnCore st c) c := by
  have hR : ∀ s, s.objects.invExt → runnableThreadsAreTCBsOnCore s c →
      currentThreadValidOnCore s c →
      runnableThreadsAreTCBsOnCore (rescheduleIfPendingOnCore s c) c := fun s hs hr hv =>
    rescheduleIfPendingOnCore_of (P := fun s => runnableThreadsAreTCBsOnCore s c) s c hr
      (handleRescheduleSgiOnCore_preserves_runnableThreadsAreTCBsOnCore s c _ hs hr hv
        (handleRescheduleSgiOnCore_eq_state s c))
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ <;> rw [h]
  · exact hR _ hPrepInv hPrepRat hPrepCtv
  · exact hR _ hPrepInv hPrepRat hPrepCtv
  · exact scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore st3 c _
      (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hB)
      (scheduleEffectiveOnCore_eq_state st3 c) (hBudgetRat tid tcb st3 true hCur hTcb hB)
  · have hV3 : currentThreadValidOnCore st3 c := by
      simp only [currentThreadValidOnCore,
        timerTickBudgetOnCore_notPreempted_scheduler_eq _ c tid tcb st3 hB, hCur]
      exact timerTickBudgetOnCore_notPreempted_getTcb?_tid _ c tid tcb st3 hPrepInv hTcb hB
    exact hR _ (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hB)
      (hBudgetRat tid tcb st3 false hCur hTcb hB) hV3

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
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', false)) :
    st'.machine.regsOnCore c = st.machine.regsOnCore c := by
  cases hb : tcb.schedContextBinding with
  | unbound =>
    by_cases hsl : tcb.timeSlice ≤ 1
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_pos hsl, Prod.mk.injEq] at hStep
      exact absurd hStep.2 (by decide)
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_neg hsl, Prod.mk.injEq] at hStep
      rw [← hStep.1]
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      rfl
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
        rw [← hStep.1]
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      rfl
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
        rw [← hStep.1]

/-- A not-preempted budget tick keeps the running thread resolvable with an
unchanged `registerContext` (the time-slice / budget write is register-free). -/
theorem timerTickBudgetOnCore_notPreempted_getTcb?_tid_reg (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (hInv : st.objects.invExt)
    (hTcb : st.getTcb? tid = some tcb)
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', false)) :
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
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_pos hsl, Prod.mk.injEq] at hStep
      exact absurd hStep.2 (by decide)
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_neg hsl, Prod.mk.injEq] at hStep
      rw [← hStep.1]
      simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?,
        RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
      exact ⟨_, rfl, rfl⟩
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      exact ⟨tcb, hTcb, rfl⟩
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
        refine ⟨tcb, ?_, rfl⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hTcb
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      exact ⟨tcb, hTcb, rfl⟩
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
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
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', false)) :
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
given the prepared state satisfies it (`hPrepCtx`).  Idle path = the local decision on the prepared state; preempted
path *re-establishes* it via `scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore`
(no hypothesis); not-preempted path preserves it (register bank + running thread's
`registerContext` unchanged). -/
theorem timerTickOnCore_preserves_contextMatchesCurrentOnCore (st : SystemState) (c : CoreId)
    (hPrepInv : (timerTickOnCorePrepared st c).objects.invExt)
    (hPrepCtx : contextMatchesCurrentOnCore (timerTickOnCorePrepared st c) c) :
    contextMatchesCurrentOnCore (timerTickOnCore st c) c := by
  have hR : ∀ s, s.objects.invExt → contextMatchesCurrentOnCore s c →
      contextMatchesCurrentOnCore (rescheduleIfPendingOnCore s c) c := fun s hs hx =>
    rescheduleIfPendingOnCore_of (P := fun s => contextMatchesCurrentOnCore s c) s c hx
      (handleRescheduleSgiOnCore_preserves_contextMatchesCurrentOnCore s c _ hs hx
        (handleRescheduleSgiOnCore_eq_state s c))
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ <;> rw [h]
  · exact hR _ hPrepInv hPrepCtx
  · exact hR _ hPrepInv hPrepCtx
  · exact scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore st3 c _
      (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hB)
      (scheduleEffectiveOnCore_eq_state st3 c)
  · exact hR _ (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hB)
      (timerTickBudgetOnCore_notPreempted_preserves_contextMatchesCurrentOnCore
        _ c tid tcb st3 hPrepInv hCur hTcb hPrepCtx hB)

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
          simp only [SchedulerState.clearReschedulePendingOnCore_runQueueOnCore,
            SchedulerState.setCurrentOnCore_runQueueOnCore,
            restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
      SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          rw [saveOutgoingContextOnCore_scheduler_eq]
          exact RunQueue.remove_preserves_toList_nodup _ tid hnd
        · simp at hStep

/-- A not-preempted budget tick preserves per-core run-queue `Nodup` — its
scheduler is unchanged (`timerTickBudgetOnCore_notPreempted_scheduler_eq`). -/
theorem timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCore_nodup
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hnd : (st.scheduler.runQueueOnCore c).toList.Nodup)
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', false)) :
    (st'.scheduler.runQueueOnCore c).toList.Nodup := by
  rw [timerTickBudgetOnCore_notPreempted_scheduler_eq st c tid tcb st' hStep]; exact hnd

/-- WS-SM SM5.I.8: the per-core timer tick preserves `runQueueUniqueOnCore`, given
the prepared state is `Nodup` (`hPrepNd`) and the budget tick preserves it
(`hBudgetNd`).  Idle path = the local decision on the prepared state; preempted path dequeues-on-dispatch via
`scheduleEffectiveOnCore_preserves_runQueueOnCore_nodup`; not-preempted path leaves
the scheduler unchanged.  `hBudgetNd` is discharged on every clean path by
`timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCore_nodup`. -/
theorem timerTickOnCore_preserves_runQueueUniqueOnCore (st : SystemState) (c : CoreId)
    (hPrepNd : ((timerTickOnCorePrepared st c).scheduler.runQueueOnCore c).toList.Nodup)
    (hBudgetNd : ∀ tid tcb st3 b,
       (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid →
       ∀ (hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb),
       timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, b) →
       (st3.scheduler.runQueueOnCore c).toList.Nodup) :
    runQueueUniqueOnCore (timerTickOnCore st c).scheduler c := by
  have hR : ∀ s, (s.scheduler.runQueueOnCore c).toList.Nodup →
      runQueueUniqueOnCore (rescheduleIfPendingOnCore s c).scheduler c := fun s hs =>
    rescheduleIfPendingOnCore_of (P := fun s => runQueueUniqueOnCore s.scheduler c) s c hs
      (handleRescheduleSgiOnCore_preserves_runQueueOnCore_nodup s c _ hs
        (handleRescheduleSgiOnCore_eq_state s c))
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ <;> rw [h]
  · exact hR _ hPrepNd
  · exact hR _ hPrepNd
  · exact scheduleEffectiveOnCore_preserves_runQueueOnCore_nodup st3 c _
      (hBudgetNd tid tcb st3 true hCur hTcb hB) (scheduleEffectiveOnCore_eq_state st3 c)
  · exact hR _ (hBudgetNd tid tcb st3 false hCur hTcb hB)

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
    (hPrepQcc : queueCurrentConsistentOnCore (timerTickOnCorePrepared st c).scheduler c) :
    queueCurrentConsistentOnCore (timerTickOnCore st c).scheduler c := by
  have hR : ∀ s, queueCurrentConsistentOnCore s.scheduler c →
      queueCurrentConsistentOnCore (rescheduleIfPendingOnCore s c).scheduler c := fun s hs =>
    rescheduleIfPendingOnCore_of (P := fun s => queueCurrentConsistentOnCore s.scheduler c) s c hs
      (handleRescheduleSgiOnCore_preserves_queueCurrentConsistentOnCore s c _ hs
        (handleRescheduleSgiOnCore_eq_state s c))
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ <;> rw [h]
  · exact hR _ hPrepQcc
  · exact hR _ hPrepQcc
  · exact scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore st3 c _
      (scheduleEffectiveOnCore_eq_state st3 c)
  · apply hR
    rw [timerTickBudgetOnCore_notPreempted_scheduler_eq _ c tid tcb st3 hB]
    exact hPrepQcc

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
        simp only [saveOutgoingContextOnCore, hc, SystemState.updateTcb_eq_self_of_none ho]]; exact hCur, rfl⟩
    | some outTcb =>
      by_cases heq : tid = outTid
      · subst heq
        refine ⟨{ outTcb with registerContext := st.machine.regsOnCore c }, ?_, ?_⟩
        · simp only [saveOutgoingContextOnCore, hc, SystemState.updateTcb_eq_of_some ho]
          simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
          rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
        · rw [hCur] at ho; have he : tcb = outTcb := Option.some.inj ho; rw [he]
      · have hNeO : ¬ (outTid.toObjId == tid.toObjId) = true := fun he =>
          heq (ThreadId.toObjId_injective _ _ (by simpa using he)).symm
        refine ⟨tcb, ?_, rfl⟩
        simp only [saveOutgoingContextOnCore, hc, SystemState.updateTcb_eq_of_some ho]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects outTid.toObjId tid.toObjId _ hNeO hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hCur


theorem scheduleEffectiveOnCore_getTcb?_domain (st : SystemState) (c : CoreId) (st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') (hres : st.getTcb? tid = some tcb) :
    ∃ tcb', st'.getTcb? tid = some tcb' ∧ tcb'.domain = tcb.domain := by
  have hA := scheduleEffectiveOnCore_objectsAgreeOffRunLinks st c st' hStep
  obtain ⟨tcb', hg, hdom⟩ := saveOutgoingContextOnCore_getTcb?_domain st c tid tcb hInv hres
  obtain ⟨t', ht', hE⟩ := hA.getTcb?_some hg
  exact ⟨t', ht', (TCB.proj_eq_of_withoutRunLinks_eq TCB.domain hE).trans hdom⟩

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
            simp only [SchedulerState.clearReschedulePendingOnCore_activeDomainOnCore,
              SchedulerState.setCurrentOnCore_activeDomainOnCore, restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
      SchedulerState.setRunQueueEndsOnCore_activeDomainOnCore,
              SchedulerState.setRunQueueOnCore_activeDomainOnCore]
            rw [saveOutgoingContextOnCore_scheduler_eq]
          obtain ⟨tcb', hg, hdom⟩ := scheduleEffectiveOnCore_getTcb?_domain st c st' tid tcb hInv hCopy hTcb
          simp only [currentThreadInActiveDomainOnCore, hcur, hg, hact, hdom]
          exact hcond
        · simp at hStep


-- not-preempted budget tick preserves the charged thread's domain.
theorem timerTickBudgetOnCore_notPreempted_getTcb?_domain (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (st' : SystemState) (hInv : st.objects.invExt) (hCur : st.getTcb? tid = some tcb)
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', false)) :
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
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_pos hsl, Prod.mk.injEq] at hStep
      exact absurd hStep.2 (by decide)
    · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, if_neg hsl, Prod.mk.injEq] at hStep
      rw [← hStep.1]
      simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?,
        RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
      exact ⟨_, rfl, rfl⟩
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      exact ⟨tcb, hCur, rfl⟩
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
        refine ⟨tcb, ?_, rfl⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hCur
  | donated scId orig =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [timerTickBudgetOnCore, hb, SystemState.getSchedContextWitnessed?_eq_none hSc, Prod.mk.injEq] at hStep
      obtain ⟨hst, -⟩ := hStep; subst hst
      exact ⟨tcb, hCur, rfl⟩
    | some sc =>
      by_cases hbg : sc.tickExhausts (st.machine.timer - 1) = true
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_pos hbg, Prod.mk.injEq] at hStep
        exact absurd hStep.2 (by decide)
      · simp only [timerTickBudgetOnCore, SystemState.rewriteObject, hb, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hbg, Prod.mk.injEq] at hStep
        refine ⟨tcb, ?_, rfl⟩
        rw [← hStep.1]
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (hDisj scId ⟨sc, hSc⟩) hInv]
        simpa only [SystemState.getTcb?, RHTable_getElem?_eq_get?] using hCur

-- composed: the tick preserves currentThreadInActiveDomain, parameterized by hPrepDom.
theorem timerTickOnCore_preserves_currentThreadInActiveDomainOnCore (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt)
    (hPrepDom : currentThreadInActiveDomainOnCore (timerTickOnCorePrepared st c) c) :
    currentThreadInActiveDomainOnCore (timerTickOnCore st c) c := by
  have hPrepInv : (timerTickOnCorePrepared st c).objects.invExt :=
    timerTickOnCorePrepared_objects_invExt st c hInv
  have hR : ∀ s, s.objects.invExt → currentThreadInActiveDomainOnCore s c →
      currentThreadInActiveDomainOnCore (rescheduleIfPendingOnCore s c) c := fun s hs hd =>
    rescheduleIfPendingOnCore_of (P := fun s => currentThreadInActiveDomainOnCore s c) s c hd
      (handleRescheduleSgiOnCore_preserves_currentThreadInActiveDomainOnCore s c _ hs hd
        (handleRescheduleSgiOnCore_eq_state s c))
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ <;> rw [h]
  · exact hR _ hPrepInv hPrepDom
  · exact hR _ hPrepInv hPrepDom
  · exact scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore st3 c _
      (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hB)
      (scheduleEffectiveOnCore_eq_state st3 c)
  · -- not-preempted: scheduler unchanged, current = tid, domain of tid preserved
    have hD3 : currentThreadInActiveDomainOnCore st3 c := by
      obtain ⟨t', hg, hdom⟩ := timerTickBudgetOnCore_notPreempted_getTcb?_domain _ c tid tcb st3
        hPrepInv hTcb hB
      unfold currentThreadInActiveDomainOnCore at hPrepDom ⊢
      simp only [hCur, hTcb] at hPrepDom
      rw [timerTickBudgetOnCore_notPreempted_scheduler_eq _ c tid tcb st3 hB]
      simp only [hCur, hg, hdom]
      exact hPrepDom
    exact hR _ (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hB) hD3

end SeLe4n.Kernel
