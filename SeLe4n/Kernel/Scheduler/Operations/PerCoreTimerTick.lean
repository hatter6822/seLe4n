-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Core
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
* **§2 — SM5.D.6** per-core domain rotation: `decrementDomainTimeOnCore`
  decrement / rotate / single-domain-noop + frame lemmas + the headline
  `timerTickOnCore_rotates_domain`.
* **§3 — SM5.D.4** per-core CBS replenishment + cross-core wake:
  `processOneReplenishmentOnCore` / `processReplenishmentsDueOnCore` semantics +
  preservation + the headline `cbsReplenish_can_wake_remote_core`.
* **§4 — SM5.D.5** per-core budget tick: `timerTickBudgetOnCore` no-timer-advance
  / preemption / preservation + the headline `timerTickOnCore_preempts_local`.
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

/-- WS-SM SM5.D.3 (cross-domain, plan §3.4 / §4.4): the **complete** lock-set
footprint of `timerTickOnCore c`, over SM5.A's `SchedLockId` (extended at SM5.D.3
with the replenish-queue domain).

The tick mutates three lock domains on core `c`:
* the RobinHood **object store** (write): CBS refills + budget/time-slice writes +
  the context save/restore on preemption all `objects.insert`.  Per SM3.A.10 the
  store is guarded by the single table-level lock (`schedObjStoreLockId`), in
  **write** mode — which subsumes plan §3.4's "all TCB locks for threads whose
  SchedContext is bound to `c`" (the dynamic per-thread set), exactly the SM5.B/C
  table-lock rationale (RHTable structural safety is table-granularity);
* core `c`'s **run-queue** slot (write): re-enqueue on preemption + dispatch
  dequeue; and
* core `c`'s **replenish-queue** slot (write): `popDue` + the exhausted-budget
  replenishment insert.

So the footprint is the three-lock set in plan §4.4 ascending order
(object < runQueue < replenishQueue):
`[(object schedObjStoreLockId, .write), (runQueue ⟨c⟩, .write), (replenishQueue ⟨c⟩, .write)]`.
The cross-domain acquisition order is certified by `timerTickOnCoreLockSet_pairwise_le`;
the runtime `withLockSet` acquisition is the SM5.D.1 ISR / SM5.I work. -/
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
-- under the SM3.D `maxLockSetSize` = 8 cap), so the per-tick worst-case lock-wait
-- is bounded by `3 · (numCores − 1) · T_per_lock` (plan §3.9) — the tick fits the
-- WCRT budget.  The size pin (`_length` above) plus this bound are the SM5.D.7
-- surface; the full WCRT integration with SM3.D's `boundedWait_under_2pl` is
-- SM5.J.

/-- WS-SM SM5.D.7 (WCRT bound): the timer-tick lock-set size is within the SM3.D
`maxLockSetSize` (= 8) cap — so a tick's worst-case response time is bounded by
`maxLockSetSize · (numCores − 1) · T_per_lock` (plan §3.9), fitting the 1 ms tick
budget.  A surface witness pinning the tick to the bounded-WCRT class. -/
theorem timerTickOnCoreLockSet_size_le_maxLockSetSize (c : CoreId) :
    (timerTickOnCoreLockSet c).length ≤ 8 := by
  rw [timerTickOnCoreLockSet_length]; decide

-- ============================================================================
-- §2  SM5.D.6 — Per-core domain rotation (`decrementDomainTimeOnCore`)
-- ============================================================================

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` never touches the object store
(both branches mutate only scheduler domain slots). -/
@[simp] theorem decrementDomainTimeOnCore_objects_eq (st : SystemState) (c : CoreId) :
    (decrementDomainTimeOnCore st c).objects = st.objects := by
  simp only [decrementDomainTimeOnCore]
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` never touches the machine state
(the per-core domain accounting reads but does not advance the global timer). -/
@[simp] theorem decrementDomainTimeOnCore_machine_eq (st : SystemState) (c : CoreId) :
    (decrementDomainTimeOnCore st c).machine = st.machine := by
  simp only [decrementDomainTimeOnCore]
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` leaves every core's run queue
unchanged — it writes only the domain slots, never the run-queue slot. -/
@[simp] theorem decrementDomainTimeOnCore_runQueueOnCore (st : SystemState) (c c' : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  simp only [decrementDomainTimeOnCore]
  split
  · split
    · rfl
    · split <;> simp
  · simp

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` leaves every core's current thread
unchanged. -/
@[simp] theorem decrementDomainTimeOnCore_currentOnCore (st : SystemState) (c c' : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  simp only [decrementDomainTimeOnCore]
  split
  · split
    · rfl
    · split <;> simp
  · simp

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` leaves every core's replenish queue
unchanged. -/
@[simp] theorem decrementDomainTimeOnCore_replenishQueueOnCore (st : SystemState) (c c' : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  simp only [decrementDomainTimeOnCore]
  split
  · split
    · rfl
    · split <;> simp
  · simp

/-- WS-SM SM5.D.6 (per-core independence): for a sibling core `c' ≠ c`,
`decrementDomainTimeOnCore st c` leaves core `c'`'s active-domain slot
unchanged — the domain rotation is core-`c`-local. -/
theorem decrementDomainTimeOnCore_activeDomainOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (decrementDomainTimeOnCore st c).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' := by
  simp only [decrementDomainTimeOnCore]
  split
  · split
    · rfl
    · split
      · rfl
      · simp [SchedulerState.setActiveDomainOnCore_activeDomainOnCore_ne _ c c' _ h,
          SchedulerState.setDomainTimeRemainingOnCore_activeDomainOnCore,
          SchedulerState.setDomainScheduleIndexOnCore_activeDomainOnCore]
  · simp [SchedulerState.setDomainTimeRemainingOnCore_activeDomainOnCore]

/-- WS-SM SM5.D.6: when core `c`'s domain has *not* reached its last tick
(`domainTimeRemainingOnCore c > 1`), `decrementDomainTimeOnCore` decrements it by
one — the common-case per-core domain accounting advance. -/
theorem decrementDomainTimeOnCore_decrements (st : SystemState) (c : CoreId)
    (h : 1 < st.scheduler.domainTimeRemainingOnCore c) :
    (decrementDomainTimeOnCore st c).scheduler.domainTimeRemainingOnCore c
      = st.scheduler.domainTimeRemainingOnCore c - 1 := by
  simp only [decrementDomainTimeOnCore]
  rw [if_neg (by omega)]
  simp

/-- WS-SM SM5.D.6: when core `c`'s domain has *not* reached its last tick, the
active domain is unchanged (only the time-remaining counter moves). -/
theorem decrementDomainTimeOnCore_preserves_activeDomain_of_not_expired
    (st : SystemState) (c : CoreId)
    (h : 1 < st.scheduler.domainTimeRemainingOnCore c) :
    (decrementDomainTimeOnCore st c).scheduler.activeDomainOnCore c
      = st.scheduler.activeDomainOnCore c := by
  simp only [decrementDomainTimeOnCore]
  rw [if_neg (by omega)]
  simp [SchedulerState.setDomainTimeRemainingOnCore_activeDomainOnCore]

/-- WS-SM SM5.D.6: in single-domain mode (`domainSchedule = []`), reaching the
domain's last tick (`domainTimeRemainingOnCore c ≤ 1`) is a no-op — no rotation
target exists, so the state is returned unchanged. -/
theorem decrementDomainTimeOnCore_singleDomain_noop (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule = [])
    (hExpired : st.scheduler.domainTimeRemainingOnCore c ≤ 1) :
    decrementDomainTimeOnCore st c = st := by
  simp only [decrementDomainTimeOnCore]
  rw [if_pos hExpired, hSched]

/-- WS-SM SM5.D.6 (the headline rotation theorem, plan §6.1
`timerTickOnCore_rotates_domain`): when core `c`'s domain reaches its last tick
(`domainTimeRemainingOnCore c ≤ 1`) and the (non-empty) domain schedule's next
entry is `entry`, `decrementDomainTimeOnCore` rotates core `c`'s active domain to
`entry`'s domain. -/
theorem decrementDomainTimeOnCore_rotates (st : SystemState) (c : CoreId)
    (entry : DomainScheduleEntry)
    (hExpired : st.scheduler.domainTimeRemainingOnCore c ≤ 1)
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hEntry : st.scheduler.domainSchedule[((st.scheduler.domainScheduleIndexOnCore c) + 1)
        % st.scheduler.domainSchedule.length]? = some entry) :
    (decrementDomainTimeOnCore st c).scheduler.activeDomainOnCore c
      = DomainScheduleEntry.domain entry := by
  -- The equational `rw` (not `simp only`) keeps the `have nextIdx`, so `split`
  -- targets the outer `match domainSchedule` correctly; `dsimp only` then
  -- zeta-reduces the `have` so `rw [hEntry]` can fire on the inner match.
  rw [decrementDomainTimeOnCore, if_pos hExpired]
  split
  · -- domainSchedule = [] : contradicts hSched
    next heq => exact absurd heq hSched
  · -- non-empty: reduce the inner `[nextIdx]?` match via hEntry
    dsimp only
    rw [hEntry]
    simp [SchedulerState.setDomainScheduleIndexOnCore_activeDomainOnCore,
      SchedulerState.setDomainTimeRemainingOnCore_activeDomainOnCore,
      SchedulerState.setActiveDomainOnCore_activeDomainOnCore_self]

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
    (acc : SystemState × List (CoreId × SgiKind)) (hInv : acc.1.objects.invExt) :
    (dueIds.foldl (fun acc scId =>
        let (s, sgi?) := processOneReplenishmentOnCore acc.1 c scId now
        (s, acc.2 ++ sgi?.toList)) acc).1.objects.invExt := by
  induction dueIds generalizing acc with
  | nil => exact hInv
  | cons hd tl ih =>
      rw [List.foldl_cons]
      exact ih _ (processOneReplenishmentOnCore_preserves_objects_invExt acc.1 c hd now hInv)

/-- WS-SM SM5.D.4 (fold preservation helper): the replenishment fold preserves
run-queue well-formedness on **every** core `c'`. -/
private theorem foldl_processOneReplenishment_preserves_runQueueOnCore_wellFormed
    (dueIds : List SeLe4n.SchedContextId) (c c' : CoreId) (now : Nat)
    (acc : SystemState × List (CoreId × SgiKind))
    (hwf : (acc.1.scheduler.runQueueOnCore c').wellFormed) :
    ((dueIds.foldl (fun acc scId =>
        let (s, sgi?) := processOneReplenishmentOnCore acc.1 c scId now
        (s, acc.2 ++ sgi?.toList)) acc).1.scheduler.runQueueOnCore c').wellFormed := by
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
    (processOneReplenishmentOnCore st execCore scId now).2 = none := by
  simp only [processOneReplenishmentOnCore, hNone]

/-- WS-SM SM5.D.4: a wake whose target is the executing core itself emits no SGI
(local enqueue; the local scheduler picks the thread up on its next decision). -/
theorem processOneReplenishmentOnCore_local_no_sgi (st : SystemState)
    (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat) (tid : SeLe4n.ThreadId)
    (hTarget : replenishWakeTarget st (refillSchedContext st scId now) scId = some tid)
    (hLocal : determineTargetCore (refillSchedContext st scId now) tid = execCore) :
    (processOneReplenishmentOnCore st execCore scId now).2 = none := by
  simp only [processOneReplenishmentOnCore, hTarget]
  split
  · rfl
  · exact wakeThread_no_sgi_if_local (refillSchedContext st scId now) tid execCore hLocal

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
    (hNotCur : (refillSchedContext st scId now).scheduler.currentOnCore
        (determineTargetCore (refillSchedContext st scId now) tid) ≠ some tid)
    (hRemote : determineTargetCore (refillSchedContext st scId now) tid ≠ execCore) :
    (processOneReplenishmentOnCore st execCore scId now).2
      = some (determineTargetCore (refillSchedContext st scId now) tid, SgiKind.reschedule) := by
  have hcond : ((refillSchedContext st scId now).scheduler.currentOnCore
      (determineTargetCore (refillSchedContext st scId now) tid) == some tid) = false :=
    beq_eq_false_iff_ne.mpr hNotCur
  simp only [processOneReplenishmentOnCore, hTarget, hcond, Bool.false_eq_true, if_false]
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
-- (Note: `timeoutBlockedThreads` re-enqueues timed-out threads on the **boot
-- core**'s run queue — the IPC-timeout interaction is not yet per-core, an
-- artefact closed by SM5.F per-core PIP.  This does not affect the object-store
-- invariant proven here; the full per-core run-queue interaction of the timeout
-- path is SM5.F / the SM5.I.8 cross-subsystem preservation suite.)

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
    (tid : SeLe4n.ThreadId) (st st' : SystemState) (hInv : st.objects.invExt)
    (hStep : timeoutThread epId isRecvQ tid st = .ok st') : st'.objects.invExt := by
  unfold timeoutThread at hStep
  split at hStep
  · simp at hStep
  · rename_i st1 hEQR
    have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hEQR
    split at hStep
    · simp at hStep
    · rename_i tcb hLook
      simp only [storeObject] at hStep
      split at hStep <;>
        · simp only [Except.ok.injEq] at hStep
          subst hStep
          first
            | (apply revertPriorityInheritance_preserves_objects_invExt
               rw [ensureRunnable_objects_eq_local]
               exact RHTable_insert_preserves_invExt st1.objects _ _ hInv1)
            | (rw [ensureRunnable_objects_eq_local]
               exact RHTable_insert_preserves_invExt st1.objects _ _ hInv1)

/-- WS-SM SM5.D.5 (preservation): `timeoutBlockedThreads` preserves the
object-store invariant — each fold step either keeps the state or applies
`timeoutThread` (which preserves it). -/
theorem timeoutBlockedThreads_preserves_objects_invExt (st : SystemState)
    (scId : SeLe4n.SchedContextId) (hInv : st.objects.invExt) :
    (timeoutBlockedThreads st scId).1.objects.invExt := by
  unfold timeoutBlockedThreads
  generalize (st.scThreadIndex[scId]?.getD []) = tids
  have hAccInv : ((st, ([] : List (SeLe4n.ThreadId × KernelError)))).1.objects.invExt := hInv
  generalize ((st, ([] : List (SeLe4n.ThreadId × KernelError)))) = acc at hAccInv ⊢
  induction tids generalizing acc with
  | nil => exact hAccInv
  | cons hd tl ih =>
      rw [List.foldl_cons]
      apply ih
      obtain ⟨st', errs⟩ := acc
      simp only at hAccInv ⊢
      split
      · rename_i tcb _
        rcases hbi : tcbBlockingInfo tcb with _ | ⟨epId, isRecvQ⟩
        · exact hAccInv
        · dsimp only
          split
          · next st'' h => exact timeoutThread_preserves_objects_invExt _ _ _ _ _ hAccInv h
          · exact hAccInv
      · exact hAccInv

/-- WS-SM SM5.D.5 (preservation): the per-core budget tick preserves the
object-store invariant in every OK branch — each writes only `RHTable.insert`s
(TCB reset / SchedContext budget) plus, in the budget-exhausted branch, the
`timeoutBlockedThreads` call (preserved above). -/
theorem timerTickBudgetOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (b : Bool)
    (hInv : st.objects.invExt)
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b)) : st'.objects.invExt := by
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
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b)) : b = false := by
  simp only [timerTickBudgetOnCore, hUnbound, if_neg hSlice, Except.ok.injEq,
    Prod.mk.injEq] at hStep
  exact hStep.2.symm

/-- WS-SM SM5.D.5: an *unbound* thread whose time-slice has expired
(`timeSlice ≤ 1`) **is** preempted (`wasPreempted = true`) — the per-core
time-slice preemption. -/
theorem timerTickBudgetOnCore_unbound_preempts (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState) (b : Bool)
    (hUnbound : tcb.schedContextBinding = .unbound) (hSlice : tcb.timeSlice ≤ 1)
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b)) : b = true := by
  simp only [timerTickBudgetOnCore, hUnbound, if_pos hSlice, Except.ok.injEq,
    Prod.mk.injEq] at hStep
  exact hStep.2.symm

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

/-- WS-SM SM5.D.5 (preservation): the per-core budget-aware reschedule preserves
the object-store invariant (save-outgoing insert + restore-incoming register-only
write). -/
theorem scheduleEffectiveOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') : st'.objects.invExt := by
  unfold scheduleEffectiveOnCore at hStep
  split at hStep
  · simp at hStep
  · simp only [Except.ok.injEq] at hStep; subst hStep
    exact saveOutgoingContextOnCore_preserves_objects_invExt st c hInv
  · split at hStep
    · split at hStep
      · simp only [Except.ok.injEq] at hStep; subst hStep
        rw [restoreIncomingContext_objects_eq]
        exact saveOutgoingContextOnCore_preserves_objects_invExt st c hInv
      · simp at hStep
    · simp at hStep

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
  have key : ∀ acc : SystemState × List (CoreId × SgiKind),
      (dueIds.foldl (fun acc scId =>
        let (s, sgi?) := processOneReplenishmentOnCore acc.1 c scId now
        (s, acc.2 ++ sgi?.toList)) acc).1.machine = acc.1.machine := by
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
  have key : ∀ acc : SystemState × List (CoreId × SgiKind),
      (dueIds.foldl (fun acc scId =>
        let (s, sgi?) := processOneReplenishmentOnCore acc.1 c scId now
        (s, acc.2 ++ sgi?.toList)) acc).1.scheduler.lastTimeoutErrorsOnCore c'
      = acc.1.scheduler.lastTimeoutErrorsOnCore c' := by
    intro acc
    induction dueIds generalizing acc with
    | nil => rfl
    | cons hd tl ih => rw [List.foldl_cons, ih]
                       exact processOneReplenishmentOnCore_lastTimeoutErrorsOnCore_eq acc.1 c hd now c'
  rw [key]
  simp [SchedulerState.setReplenishQueueOnCore_lastTimeoutErrorsOnCore]

/-- WS-SM SM5.D.6: `decrementDomainTimeOnCore` leaves every core's
`lastTimeoutErrors` slot unchanged (it writes only domain slots). -/
theorem decrementDomainTimeOnCore_lastTimeoutErrorsOnCore (st : SystemState) (c c' : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.lastTimeoutErrorsOnCore c'
      = st.scheduler.lastTimeoutErrorsOnCore c' := by
  simp only [decrementDomainTimeOnCore]
  split
  · split
    · rfl
    · split <;> simp
  · simp

-- ── the prepared state + the `timerTickOnCore` characterisation ──

/-- WS-SM SM5.D.2: the state `timerTickOnCore` reaches after the SM5.D.9 timeout-
error clear + the SM5.D.4 replenishment, **before** the SM5.D.6 domain accounting —
the post-replenishment state. -/
def timerTickOnCorePreDomain (st : SystemState) (c : CoreId) : SystemState :=
  let st0 := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] }
  (processReplenishmentsDueOnCore st0 c st0.machine.timer).1

/-- WS-SM SM5.D.2: the state-plus-SGIs `timerTickOnCore` reaches after the SM5.D.9
clear + SM5.D.4 replenishment + SM5.D.6 domain accounting, **before** the SM5.D.5
budget tick / preemption.  Naming the "prepared" state lets the SM5.D headline
theorems characterise `timerTickOnCore`'s behaviour without restating its internal
`let`-chain. -/
def timerTickOnCorePrepared (st : SystemState) (c : CoreId) :
    SystemState × List (CoreId × SgiKind) :=
  let st0 := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] }
  let (st1, sgis) := processReplenishmentsDueOnCore st0 c st0.machine.timer
  (decrementDomainTimeOnCore st1 c, sgis)

/-- WS-SM SM5.D.2: `timerTickOnCorePrepared`'s state is the domain-decrement of the
pre-domain state (the SM5.D.5 budget step operates on this). -/
theorem timerTickOnCorePrepared_fst_eq (st : SystemState) (c : CoreId) :
    (timerTickOnCorePrepared st c).1
      = decrementDomainTimeOnCore (timerTickOnCorePreDomain st c) c := rfl

/-- WS-SM SM5.D.2: `timerTickOnCore` is the SM5.D.5 budget tick / preemption
dispatched on the SM5.D.2/.4/.6 prepared state.  `rfl` — the production `let`-chain
*is* this composition.  Every SM5.D.2 headline below is a corollary. -/
theorem timerTickOnCore_eq_prepared (st : SystemState) (c : CoreId) :
    timerTickOnCore st c =
      (match (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c with
       | none => .ok (timerTickOnCorePrepared st c)
       | some tid =>
           match (timerTickOnCorePrepared st c).1.getTcb? tid with
           | some tcb =>
               match timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb with
               | .error e => .error e
               | .ok (st3, preempted) =>
                   if preempted then
                     match scheduleEffectiveOnCore st3 c with
                     | .error e => .error e
                     | .ok st4 => .ok (st4, (timerTickOnCorePrepared st c).2)
                   else .ok (st3, (timerTickOnCorePrepared st c).2)
           | none => .error .schedulerInvariantViolation) := rfl

/-- WS-SM SM5.D.2: the prepared state preserves the machine — the per-core tick
reads `machine.timer` but never advances the global timer. -/
theorem timerTickOnCorePrepared_machine_eq (st : SystemState) (c : CoreId) :
    (timerTickOnCorePrepared st c).1.machine = st.machine := by
  simp only [timerTickOnCorePrepared]
  rw [decrementDomainTimeOnCore_machine_eq, processReplenishmentsDueOnCore_machine_eq]

/-- WS-SM SM5.D.9: the prepared state has core `c`'s `lastTimeoutErrors` cleared —
the tick clears core `c`'s diagnostic at entry, and the replenishment / domain
steps never re-set it. -/
theorem timerTickOnCorePrepared_lastTimeoutErrors_eq (st : SystemState) (c : CoreId) :
    (timerTickOnCorePrepared st c).1.scheduler.lastTimeoutErrorsOnCore c = [] := by
  simp only [timerTickOnCorePrepared]
  rw [decrementDomainTimeOnCore_lastTimeoutErrorsOnCore,
    processReplenishmentsDueOnCore_lastTimeoutErrorsOnCore_eq]
  simp [SchedulerState.setLastTimeoutErrorsOnCore_lastTimeoutErrorsOnCore_self]

/-- WS-SM SM5.D.2 (preservation): the prepared state preserves the object-store
invariant (the SM5.D.4 replenishment preserves it; the SM5.D.6 domain decrement is
object-neutral). -/
theorem timerTickOnCorePrepared_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (timerTickOnCorePrepared st c).1.objects.invExt := by
  simp only [timerTickOnCorePrepared]
  rw [decrementDomainTimeOnCore_objects_eq]
  exact processReplenishmentsDueOnCore_preserves_objects_invExt _ c _ hInv

-- ── SM5.D.2 headline theorems ──

/-- WS-SM SM5.D.2: on the idle path (core `c` has no current thread in the prepared
state — e.g. a freshly-booted or freshly-idled core), the tick is exactly the
prepared state: the SM5.D.4 replenishment + SM5.D.6 domain accounting, with no
budget charge. -/
theorem timerTickOnCore_idle (st : SystemState) (c : CoreId)
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = none) :
    timerTickOnCore st c = .ok (timerTickOnCorePrepared st c) := by
  rw [timerTickOnCore_eq_prepared, hCur]

/-- WS-SM SM5.D.2 (the headline `timerTickOnCore_advances_per_core`, plan §6.1): the
per-core tick **advances core `c`'s local accounting without advancing the global
timer** — `st'.machine = st.machine`.  This is the defining SMP property: each
core's CNTV fires and the tick processes that core's state locally, but the global
monotonic tick counter (`machine.timer`) is owned by a single authority (the boot
core / the FFI `ffi_timer_reprogram`), mirroring the Rust HAL's primary-owned
`TICK_COUNT`.  Stated on the idle path (where the tick makes no register-context
write, so the *whole* machine is preserved); the global-timer field specifically is
preserved on every path. -/
theorem timerTickOnCore_advances_per_core (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = none)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    st'.machine = st.machine := by
  rw [timerTickOnCore_idle st c hCur, Except.ok.injEq] at hStep
  have hst : (timerTickOnCorePrepared st c).1 = st' := by rw [hStep]
  rw [← hst, timerTickOnCorePrepared_machine_eq]

/-- WS-SM SM5.D.9: on the idle path, the tick leaves core `c`'s `lastTimeoutErrors`
cleared — a stale timeout-error record never survives a tick. -/
theorem timerTickOnCore_clears_lastTimeoutErrors (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = none)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    st'.scheduler.lastTimeoutErrorsOnCore c = [] := by
  rw [timerTickOnCore_idle st c hCur, Except.ok.injEq] at hStep
  have hst : (timerTickOnCorePrepared st c).1 = st' := by rw [hStep]
  rw [← hst, timerTickOnCorePrepared_lastTimeoutErrors_eq]

/-- WS-SM SM5.D.6 (the headline `timerTickOnCore_rotates_domain`, plan §6.1): when
core `c`'s domain reaches its last tick in the prepared (pre-domain) state and the
non-empty domain schedule's next entry is `entry`, the tick rotates core `c`'s
active domain to `entry`'s domain.  Lifts the SM5.D.6 helper
`decrementDomainTimeOnCore_rotates` through the idle path. -/
theorem timerTickOnCore_rotates_domain (st : SystemState) (c : CoreId)
    (entry : DomainScheduleEntry) (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = none)
    (hStep : timerTickOnCore st c = .ok (st', sgis))
    (hExpired : (timerTickOnCorePreDomain st c).scheduler.domainTimeRemainingOnCore c ≤ 1)
    (hSched : (timerTickOnCorePreDomain st c).scheduler.domainSchedule ≠ [])
    (hEntry : (timerTickOnCorePreDomain st c).scheduler.domainSchedule[
        ((timerTickOnCorePreDomain st c).scheduler.domainScheduleIndexOnCore c + 1)
          % (timerTickOnCorePreDomain st c).scheduler.domainSchedule.length]? = some entry) :
    st'.scheduler.activeDomainOnCore c = DomainScheduleEntry.domain entry := by
  rw [timerTickOnCore_idle st c hCur, Except.ok.injEq] at hStep
  have hst : (timerTickOnCorePrepared st c).1 = st' := by rw [hStep]
  rw [← hst, timerTickOnCorePrepared_fst_eq]
  exact decrementDomainTimeOnCore_rotates (timerTickOnCorePreDomain st c) c entry hExpired hSched hEntry

/-- WS-SM SM5.D.5 (the headline `timerTickOnCore_preempts_local`, plan §6.1): when
core `c`'s current thread `tid` (in the prepared state) is preempted by the budget
tick (`timerTickBudgetOnCore … = .ok (st3, true)` — time-slice / budget exhausted),
the tick re-selects and dispatches via the budget-aware `scheduleEffectiveOnCore` —
the per-core local preemption. -/
theorem timerTickOnCore_preempts_local (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st3 st' : SystemState)
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid)
    (hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb)
    (hBud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, true))
    (hSched : scheduleEffectiveOnCore st3 c = .ok st') :
    timerTickOnCore st c = .ok (st', (timerTickOnCorePrepared st c).2) := by
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
  · -- idle: result is the prepared state
    rw [Except.ok.injEq] at hStep
    have hst : (timerTickOnCorePrepared st c).1 = st' := by rw [hStep]
    rw [← hst]; exact hPrep
  · split at hStep
    · split at hStep
      · -- budget tick `.error` (unreachable: contradicts `.ok`)
        simp at hStep
      · -- budget tick `.ok (st3, preempted)`
        rename_i st3 b hbud
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
  | .ok (_, b) => b = true
  | .error _ => False

instance (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    Decidable (timerTickBudgetOnCorePreempts st c tid tcb) := by
  unfold timerTickBudgetOnCorePreempts
  cases timerTickBudgetOnCore st c tid tcb with
  | error _ => simp; infer_instance
  | ok r => cases r; simp; infer_instance

end SeLe4n.Kernel
