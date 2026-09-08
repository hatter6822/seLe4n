-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR7.40: PRODUCTION.  The PIP chain walk's scheduler-domain footprint —
-- each visited thread's TCB write lock *and* its home core's run-queue write
-- lock, discovered as the walk proceeds.

import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Concurrency.Locks.DynamicChainExtension
import SeLe4n.Kernel.SchedLockBracket

/-!
# WS-RR RR7.40 — the dynamic PIP chain, over a domain that can name its locks

SM3.C.11 built the chain walker and `withDynamicChainExtension`, which acquires
**each chain member's TCB write lock**.  That was every lock the object domain
could name.  What the walk actually writes is more: `updatePipBoostOnCore` writes
the member's TCB *and* migrates its run-queue bucket on **its own home core**, so
the footprint owed a per-member `SchedLockId.runQueue` write lock that `LockSet`
had no constructor for.  That is what `UncoveredLockDomain.dynamicPipChain`
recorded, and RR7.39 removed the obstacle by giving the scheduler domain a
runtime.

## Why two segments rather than hand-over-hand per member

The natural reading of "extend the held set as each member is discovered" is to
take that member's two locks together before moving on.  The `SchedLockId` order
forbids it: it is `object < runQueue < replenishQueue`, so **every** object lock
precedes **every** run-queue lock, and interleaving them per member would walk
the ladder backwards at the second member.  The footprint is therefore two
segments — all TCB locks in `ObjId`-ascending path order, then all home-core
run-queue locks in `CoreId`-ascending order — which is the *only* shape the
ladder admits and is strictly stronger than per-member coupling: the whole chain
is held before any bucket moves.

## Why the run-queue segment is a filter of `allCores`

Two chain members can share a home core, so the segment must be duplicate-free,
and it must be `CoreId`-ascending to be its own acquisition sequence.  Deriving
it as `allCores.filter (…)` gets both from `allCores` being `List.finRange
numCores` — sorted and `Nodup` — rather than from a `dedup` whose ordering would
then need its own proof.  It also bounds the segment by `numCores` without a
separate argument.

## What bounds this footprint

Not `maxLockSetSize`.  That constant is the ceiling on a *declared static*
footprint, and the WCRT surface is stated against it; a walked chain is bounded
by `MAX_PIP_RETRIES` instead, and can be longer.  Saying so is the point — a
reader who assumed the `maxLockSetSize` bound applied here would read the WCRT
figures as covering the PIP walk, which they do not.  `pipChainSchedFootprint`
carries `…_length_le` against the chain length and the core count, which is the
bound it actually has.
-/

namespace SeLe4n.Kernel.PriorityInheritance

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency (CoreId AccessMode allCores numCores LockKind LockId
  runChainExtension runChainExtension_held runChainExtension_refused)

-- ============================================================================
-- §1  The footprint
-- ============================================================================

/-- **WS-RR RR7.40**: the home cores of a chain's members — the cores whose
run-queue buckets the walk can migrate.

`determineTargetCore` at each visited thread, filtered out of `allCores` so the
result is `CoreId`-ascending and duplicate-free by construction (two members may
share a home core, and a chain crossing four cores must still name each once). -/
def pipChainHomeCores (s : SystemState) (visited : List SeLe4n.ThreadId) : List CoreId :=
  allCores.filter (fun c => visited.any (fun t => determineTargetCore s t == c))

/-- **WS-RR RR7.40**: the home-core segment is duplicate-free — it is a sublist
of `allCores`. -/
theorem pipChainHomeCores_nodup (s : SystemState) (visited : List SeLe4n.ThreadId) :
    (pipChainHomeCores s visited).Nodup :=
  List.Pairwise.sublist (List.filter_sublist) Concurrency.allCores_nodup

/-- **WS-RR RR7.40**: every member's home core is in the segment — the coverage
half, and the one a false footprint would fail. -/
theorem mem_pipChainHomeCores (s : SystemState) (visited : List SeLe4n.ThreadId)
    (t : SeLe4n.ThreadId) (ht : t ∈ visited) :
    determineTargetCore s t ∈ pipChainHomeCores s visited := by
  refine List.mem_filter.mpr ⟨Concurrency.mem_allCores _, ?_⟩
  exact List.any_eq_true.mpr ⟨t, ht, by simp⟩

/-- **WS-RR RR7.40**: a core in the segment is some member's home core — the
converse, so the segment names no core the walk cannot touch. -/
theorem pipChainHomeCores_mem (s : SystemState) (visited : List SeLe4n.ThreadId)
    (c : CoreId) (hc : c ∈ pipChainHomeCores s visited) :
    ∃ t ∈ visited, determineTargetCore s t = c := by
  have hAny := (List.mem_filter.mp hc).2
  obtain ⟨t, ht, hEq⟩ := List.any_eq_true.mp hAny
  exact ⟨t, ht, by simpa using hEq⟩

/-- **WS-RR RR7.40**: the segment is bounded by the core count. -/
theorem pipChainHomeCores_length_le (s : SystemState) (visited : List SeLe4n.ThreadId) :
    (pipChainHomeCores s visited).length ≤ numCores := by
  have := List.length_filter_le (fun c => visited.any (fun t => determineTargetCore s t == c))
    allCores
  simpa [pipChainHomeCores, Concurrency.allCores_length] using this

/-- **WS-RR RR7.40**: the PIP chain walk's scheduler-domain footprint.

Two segments in `SchedLockId` order: every visited thread's TCB **write** lock,
then every home core's run-queue **write** lock.  The first covers the boost
itself (`updatePipBoostOnCore` rewrites the member's `pipBoost`), the second the
bucket migration (`setRunQueueOnCore` at that member's home core).

Both are `.write`: the walk reads a member's priority in order to rewrite it, and
a read lock would let a concurrent writer change the value between the read and
the store. -/
def pipChainSchedFootprint (s : SystemState) (visited : List SeLe4n.ThreadId) :
    List (SchedLockId × AccessMode) :=
  visited.map (fun t => (SchedLockId.object ⟨LockKind.tcb, t.toObjId⟩, AccessMode.write))
    ++ (pipChainHomeCores s visited).map
        (fun c => (SchedLockId.runQueue ⟨c⟩, AccessMode.write))

/-- **WS-RR RR7.40**: every lock in the chain footprint is a **write** lock. -/
theorem pipChainSchedFootprint_write_only (s : SystemState) (visited : List SeLe4n.ThreadId) :
    ∀ p ∈ pipChainSchedFootprint s visited, p.2 = AccessMode.write := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h; rfl
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h; rfl

/-- **WS-RR RR7.40**: a visited thread's TCB write lock is in the footprint. -/
theorem mem_pipChainSchedFootprint_tcb (s : SystemState) (visited : List SeLe4n.ThreadId)
    (t : SeLe4n.ThreadId) (ht : t ∈ visited) :
    (SchedLockId.object ⟨LockKind.tcb, t.toObjId⟩, AccessMode.write)
      ∈ pipChainSchedFootprint s visited :=
  List.mem_append_left _ (List.mem_map.mpr ⟨t, ht, rfl⟩)

/-- **WS-RR RR7.40**: a visited thread's **home-core run-queue** write lock is in
the footprint — the member the object domain could not name, and the whole reason
this footprint exists. -/
theorem mem_pipChainSchedFootprint_runQueue (s : SystemState) (visited : List SeLe4n.ThreadId)
    (t : SeLe4n.ThreadId) (ht : t ∈ visited) :
    (SchedLockId.runQueue ⟨determineTargetCore s t⟩, AccessMode.write)
      ∈ pipChainSchedFootprint s visited :=
  List.mem_append_right _
    (List.mem_map.mpr ⟨determineTargetCore s t, mem_pipChainHomeCores s visited t ht, rfl⟩)

/-- **WS-RR RR7.40**: the footprint's length — one lock per visited thread plus
one per distinct home core.

Stated against the chain length and `numCores`, **not** against
`maxLockSetSize`: a walked chain is bounded by `MAX_PIP_RETRIES`, and reading the
static ceiling into it would read the WCRT figures as covering the PIP walk. -/
theorem pipChainSchedFootprint_length (s : SystemState) (visited : List SeLe4n.ThreadId) :
    (pipChainSchedFootprint s visited).length
      ≤ visited.length + numCores := by
  simp only [pipChainSchedFootprint, List.length_append, List.length_map]
  exact Nat.add_le_add_left (pipChainHomeCores_length_le s visited) _

-- ============================================================================
-- §2  Ordering and uniqueness
-- ============================================================================

/-- **WS-RR RR7.40**: a footprint key is either a visited thread's TCB lock or a
home core's run-queue lock — the case analysis every ordering and uniqueness
proof below runs. -/
theorem pipChainSchedFootprint_key_shape {s : SystemState}
    {visited : List SeLe4n.ThreadId} {k : SchedLockId}
    (hk : k ∈ (pipChainSchedFootprint s visited).map (·.1)) :
    (∃ t ∈ visited, k = SchedLockId.object ⟨LockKind.tcb, t.toObjId⟩) ∨
      (∃ c ∈ pipChainHomeCores s visited, k = SchedLockId.runQueue ⟨c⟩) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  rcases List.mem_append.mp hp with h | h
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨t, ht, rfl⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact Or.inr ⟨c, hc, rfl⟩

/-- **WS-RR RR7.40**: the footprint's keys are duplicate-free, given that the
walk visited each thread once.

The `visited.Nodup` hypothesis is the chain's acyclicity, which the walker
establishes by refusing a non-ascending step (`walkStep`'s `next.toNat >
lastTid.toNat` guard).  The run-queue segment needs no hypothesis — it is a
filter of `allCores` — and the two segments are disjoint because their keys are
different `SchedLockId` constructors. -/
theorem pipChainSchedFootprint_keys_nodup (s : SystemState) (visited : List SeLe4n.ThreadId)
    (hNodup : visited.Nodup) :
    ((pipChainSchedFootprint s visited).map (·.1)).Nodup := by
  simp only [pipChainSchedFootprint, List.map_append, List.map_map]
  refine List.nodup_append.2 ⟨?_, ?_, ?_⟩
  · -- the TCB segment: an injective image of a duplicate-free list
    have hInj : ∀ a b : SeLe4n.ThreadId,
        (SchedLockId.object ⟨LockKind.tcb, a.toObjId⟩ : SchedLockId)
          = SchedLockId.object ⟨LockKind.tcb, b.toObjId⟩ → a = b := by
      intro a b hab
      have hOid : a.toObjId = b.toObjId :=
        congrArg Concurrency.LockId.objId (SchedLockId.object.inj hab)
      exact SeLe4n.ThreadId.toObjId_injective a b hOid
    exact List.Pairwise.map _ (fun a b h he => h (hInj a b he)) hNodup
  · -- the run-queue segment: an injective image of a sublist of `allCores`
    have hInj : ∀ a b : CoreId,
        (SchedLockId.runQueue ⟨a⟩ : SchedLockId) = SchedLockId.runQueue ⟨b⟩ → a = b := by
      intro a b hab
      exact congrArg RunQueueLockId.core (SchedLockId.runQueue.inj hab)
    exact List.Pairwise.map _ (fun a b h he => h (hInj a b he))
      (pipChainHomeCores_nodup s visited)
  · -- disjoint: an object key is never a run-queue key
    intro a ha b hb
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
    simp

/-- **WS-RR RR7.40**: the footprint's keys form a `SchedLockId`-ascending
acquisition sequence, given that the walk's path is `ObjId`-ascending.

The `hAsc` hypothesis is exactly what `walkAndAcquire` guarantees on a terminated
walk (`walkAndAcquire_path_ascending_in_ObjId_if_terminated`), so a chain the
walker accepts has an ordered footprint and a chain it refuses declares none.
Across the two segments the ordering is free: `SchedLockId.object_lt_runQueue`
puts every object lock below every run-queue lock, which is why the footprint has
to be two segments rather than per-member pairs. -/
theorem pipChainSchedFootprint_pairwise_le (s : SystemState) (visited : List SeLe4n.ThreadId)
    (hAsc : visited.Pairwise (fun a b => a.toNat < b.toNat)) :
    ((pipChainSchedFootprint s visited).map (·.1)).Pairwise (· ≤ ·) := by
  simp only [pipChainSchedFootprint, List.map_append, List.map_map]
  refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
  · -- within the TCB segment: the SM0.I `LockId` order at equal kind is by ObjId
    refine List.Pairwise.map _ (fun a b hab => ?_) hAsc
    show (SchedLockId.object ⟨LockKind.tcb, a.toObjId⟩ : SchedLockId)
      ≤ SchedLockId.object ⟨LockKind.tcb, b.toObjId⟩
    -- SM0.I's `LockId` order is lexicographic: equal kind, then `objId.val`.
    exact Or.inr ⟨rfl, Nat.le_of_lt hab⟩
  · -- within the run-queue segment: `CoreId`-ascending, from `allCores`
    have hCores : (pipChainHomeCores s visited).Pairwise (fun a b => a.val ≤ b.val) := by
      refine List.Pairwise.sublist (List.filter_sublist) ?_
      show allCores.Pairwise (fun a b : CoreId => a.val ≤ b.val)
      unfold Concurrency.allCores
      decide
    exact List.Pairwise.map _ (fun a b hab => hab) hCores
  · -- across the segments: every object lock precedes every run-queue lock
    intro a ha b hb
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
    exact (SchedLockId.object_lt_runQueue _ _).1


-- ============================================================================
-- §3  The walk visits along the blocking graph
-- ============================================================================

/-- **WS-RR RR7.40**: the threads the cross-core PIP walk visits, at a given
fuel.

Derived from the **same** `blockingServer` recursion `propagatePipChainCrossCore`
runs — a footprint resolved from a different walk would be a footprint for a
different operation, which is the defect the whole declared-footprint family
exists to refuse.

It reads the *initial* state at every step, where the transition threads its own
post-step states.  That is sound rather than approximate: a boost writes
`pipBoost` and a run-queue bucket, never `ipcState`, so
`updatePipBoostOnCore_preserves_blockingServer` says the chain topology the walk
follows is fixed — the same fact `propagatePipChainCrossCore`'s own docstring
relies on when it reads `blockingServer` pre-mutation. -/
def pipChainVisited (s : SystemState) (tid : SeLe4n.ThreadId) : Nat → List SeLe4n.ThreadId
  | 0 => []
  | n + 1 =>
      match blockingServer s tid with
      | some next => tid :: pipChainVisited s next n
      | none => [tid]

@[simp] theorem pipChainVisited_zero (s : SystemState) (tid : SeLe4n.ThreadId) :
    pipChainVisited s tid 0 = [] := rfl

@[simp] theorem pipChainVisited_succ (s : SystemState) (tid : SeLe4n.ThreadId) (n : Nat) :
    pipChainVisited s tid (n + 1) =
      (match blockingServer s tid with
       | some next => tid :: pipChainVisited s next n
       | none => [tid]) := rfl

/-- **WS-RR RR7.40**: the walk visits at most one thread per unit of fuel — the
bound that makes the footprint finite, and the reason `MAX_PIP_RETRIES` rather
than `maxLockSetSize` is what bounds it. -/
theorem pipChainVisited_length_le (s : SystemState) (tid : SeLe4n.ThreadId) (n : Nat) :
    (pipChainVisited s tid n).length ≤ n := by
  induction n generalizing tid with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
      rw [pipChainVisited_succ]
      cases hb : blockingServer s tid with
      | none => simp
      | some next =>
          simp only [List.length_cons]
          exact Nat.succ_le_succ (ih next)

-- ============================================================================
-- §4  The walk's writes are inside the footprint
-- ============================================================================

/-- **WS-RR RR7.40 (one step)**: a single boost writes only the boosted thread's
TCB and its home core's run queue.

The two halves are SM5.F.2's own frames (`updatePipBoostOnCore_objects_ne`,
`updatePipBoostOnCore_runQueueOnCore_ne`); this states them against the footprint
so the chain-level result composes them rather than re-deriving them. -/
theorem pipBoostWithWake_coversWrites (s : SystemState) (tid : SeLe4n.ThreadId)
    (ec : CoreId) (hInv : s.objects.invExt) :
    (∀ oid : SeLe4n.ObjId, ¬(tid.toObjId == oid) = true →
        (pipBoostWithWake s tid ec).1.objects[oid]? = s.objects[oid]?) ∧
      (∀ d : CoreId, determineTargetCore s tid ≠ d →
        (pipBoostWithWake s tid ec).1.scheduler.runQueueOnCore d
          = s.scheduler.runQueueOnCore d) := by
  refine ⟨fun oid hNe => ?_, fun d hNe => ?_⟩
  · exact updatePipBoostOnCore_objects_ne s (determineTargetCore s tid) tid oid hNe hInv
  · exact updatePipBoostOnCore_runQueueOnCore_ne s (determineTargetCore s tid) d tid hNe

/-- **WS-RR RR7.40**: a boost leaves the chain topology and every home core
where it found them, so the tail of the walk visits the same threads and names
the same cores as it would have from the initial state.

This is what lets the footprint be resolved once, from the pre-state, for a walk
whose steps each commit: `updatePipBoostOnCore` writes `pipBoost` and a bucket,
never `ipcState` and never `cpuAffinity`. -/
theorem pipChainVisited_boost_eq (s : SystemState) (tid t : SeLe4n.ThreadId)
    (ec : CoreId) (hInv : s.objects.invExt) (n : Nat) :
    pipChainVisited (pipBoostWithWake s tid ec).1 t n = pipChainVisited s t n := by
  induction n generalizing t with
  | zero => rfl
  | succ m ih =>
      rw [pipChainVisited_succ, pipChainVisited_succ,
        pipBoostWithWake_state s tid ec,
        updatePipBoostOnCore_preserves_blockingServer s (determineTargetCore s tid) tid hInv t]
      cases hb : blockingServer s t with
      | none => rfl
      | some next =>
          simp only
          rw [← pipBoostWithWake_state s tid ec, ih next]

/-- **WS-RR RR7.40 (the payoff)**: the cross-core PIP chain walk writes only
inside the footprint the chain declares.

Every object it rewrites is a visited thread's TCB, and every run queue in which
it migrates a bucket belongs to a visited thread's home core.  So the footprint
the RR7.40 extension acquires is not a *false* one: the exclusion the 2PL
argument rests on is exclusion the walk actually established.

The home cores are read off the **initial** state and stay right across the walk,
because a boost never touches `cpuAffinity`
(`updatePipBoostOnCore_preserves_determineTargetCore`) — the same stability the
footprint's own definition depends on. -/
theorem propagatePipChainCrossCore_coversWrites (s : SystemState)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (n : Nat) (hInv : s.objects.invExt) :
    (∀ oid : SeLe4n.ObjId,
        (∀ t ∈ pipChainVisited s tid n, ¬(t.toObjId == oid) = true) →
        (propagatePipChainCrossCore s tid ec n).1.objects[oid]? = s.objects[oid]?) ∧
      (∀ d : CoreId, d ∉ pipChainHomeCores s (pipChainVisited s tid n) →
        (propagatePipChainCrossCore s tid ec n).1.scheduler.runQueueOnCore d
          = s.scheduler.runQueueOnCore d) := by
  induction n generalizing s tid with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ m ih =>
      have hStep := propagatePipChainCrossCore_step s tid ec m
      have hBoostInv : (pipBoostWithWake s tid ec).1.objects.invExt := by
        rw [pipBoostWithWake_state]
        exact updatePipBoostOnCore_preserves_objects_invExt s (determineTargetCore s tid) tid hInv
      cases hb : blockingServer s tid with
      | none =>
          have hMemHead : tid ∈ pipChainVisited s tid (m + 1) := by
            rw [pipChainVisited_succ, hb]; exact List.mem_singleton.mpr rfl
          refine ⟨fun oid hOid => ?_, fun d hd => ?_⟩
          · rw [hStep]; simp only [hb]
            exact (pipBoostWithWake_coversWrites s tid ec hInv).1 oid (hOid tid hMemHead)
          · rw [hStep]; simp only [hb]
            refine (pipBoostWithWake_coversWrites s tid ec hInv).2 d (fun hEq => hd ?_)
            rw [← hEq]; exact mem_pipChainHomeCores _ _ tid hMemHead
      | some next =>
          have hTailVis : pipChainVisited (pipBoostWithWake s tid ec).1 next m
              = pipChainVisited s next m :=
            pipChainVisited_boost_eq s tid next ec hInv m
          have hDTC : ∀ t : SeLe4n.ThreadId,
              determineTargetCore (pipBoostWithWake s tid ec).1 t = determineTargetCore s t := by
            intro t
            rw [pipBoostWithWake_state]
            exact updatePipBoostOnCore_preserves_determineTargetCore s
              (determineTargetCore s tid) tid t hInv
          have hMemHead : tid ∈ pipChainVisited s tid (m + 1) := by
            rw [pipChainVisited_succ, hb]; exact List.mem_cons_self
          have hMemTail : ∀ t, t ∈ pipChainVisited s next m → t ∈ pipChainVisited s tid (m + 1) := by
            intro t ht
            rw [pipChainVisited_succ, hb]; exact List.mem_cons_of_mem _ ht
          obtain ⟨ihObj, ihRq⟩ := ih (pipBoostWithWake s tid ec).1 next hBoostInv
          refine ⟨fun oid hOid => ?_, fun d hd => ?_⟩
          · rw [hStep]; simp only [hb]
            have hTail := ihObj oid (by
              intro t ht
              exact hOid t (hMemTail t (hTailVis ▸ ht)))
            rw [hTail]
            exact (pipBoostWithWake_coversWrites s tid ec hInv).1 oid (hOid tid hMemHead)
          · rw [hStep]; simp only [hb]
            have hTail := ihRq d (by
              intro hMem
              obtain ⟨t, ht, hEq⟩ :=
                pipChainHomeCores_mem _ _ d hMem
              refine hd ?_
              rw [← hEq, hDTC t]
              exact mem_pipChainHomeCores _ _ t (hMemTail t (hTailVis ▸ ht)))
            rw [hTail]
            refine (pipBoostWithWake_coversWrites s tid ec hInv).2 d (fun hEq => hd ?_)
            rw [← hEq]; exact mem_pipChainHomeCores _ _ tid hMemHead


-- ============================================================================
-- §5  The extension
-- ============================================================================

/-- **WS-RR RR7.40**: run the PIP chain walk inside the footprint the chain
declares.

`runChainExtension` at `schedulerLockBracketDomain` — the *same* definition
`withDynamicChainExtension` runs at the object domain, so "acquire a discovered
chain, act, unwind" has one answer and the two differ only in which locks they
name.  What this one names that the object-domain form could not is each member's
home-core run-queue write lock.

The footprint is resolved from `pipChainVisited` at the pre-state, which is the
walk the transition itself performs; `propagatePipChainCrossCore_coversWrites` is
the proof that the resolution covers what the transition writes.

`SchedLockSet.ofList?` is the fail-closed step: a chain that revisits a thread —
which `blockingAcyclic` forbids — names one lock twice, so no footprint is
declared, and the caller keeps whatever coarser serialisation it already has.
Accepting the duplicated list and acquiring it anyway is the one shape this must
not take: a read-acquire counted twice leaves a reader the symmetric unwind
never removes.

What `ofList?` does **not** check is the order, and it does not need to (PR #892
review round 5): the domain sorts (`SchedLockSet.lockAcquireSequence`), so a
chain resolved in any order is acquired along the SM0.I ladder.  Before that it
did need to, and nothing did — a chain descending in `ObjId`, which is any chain
where a higher-numbered thread blocks on a lower-numbered one, was acquired
backwards. -/
def withPipChainSchedExtension {α : Type} (caller : CoreId)
    (startTid : SeLe4n.ThreadId) (fuel : Nat)
    (action : SystemState → SystemState × α) (fallback : α) (s : SystemState) :
    SystemState × α :=
  match SchedLockSet.ofList? (pipChainSchedFootprint s (pipChainVisited s startTid fuel)) with
  | none => (s, fallback)
  | some S =>
      runChainExtension schedulerLockBracketDomain caller S action fallback s

/-- **WS-RR RR7.40**: with no footprint declared — a chain whose keys repeat —
the extension commits nothing and acquires nothing.

The fail-closed arm, stated so a refactor that started acquiring a duplicated
list has to break it. -/
theorem withPipChainSchedExtension_undeclared {α : Type} (caller : CoreId)
    (startTid : SeLe4n.ThreadId) (fuel : Nat)
    (action : SystemState → SystemState × α) (fallback : α) (s : SystemState)
    (h : SchedLockSet.ofList? (pipChainSchedFootprint s (pipChainVisited s startTid fuel))
          = none) :
    withPipChainSchedExtension caller startTid fuel action fallback s = (s, fallback) := by
  unfold withPipChainSchedExtension
  rw [h]

/-- **WS-RR RR7.40 / PR #892 review round 2**: on a declared footprint the
growing phase **granted**, the extension is acquire / act / unwind over exactly
the chain's locks.

**PR #892 review round 5**: over the chain's locks *in ladder order*.  The
sequence is `S.lockAcquireSequence` — the domain's canonical sort — not the
resolved list, because a blocking chain descends in `ObjId` whenever a
higher-numbered thread blocks on a lower-numbered one and acquiring it as
resolved would walk the SM0.I ladder backwards.  `pipChainSchedExtension_acquires_in_ladder_order`
is what that buys, with no hypothesis on the chain. -/
theorem withPipChainSchedExtension_declared {α : Type} (caller : CoreId)
    (startTid : SeLe4n.ThreadId) (fuel : Nat)
    (action : SystemState → SystemState × α) (fallback : α) (s : SystemState)
    (S : SchedLockSet)
    (h : SchedLockSet.ofList? (pipChainSchedFootprint s (pipChainVisited s startTid fuel))
          = some S)
    (hHeld : schedLockSetHeld caller S (schedAcquireAll caller S.lockAcquireSequence s)) :
    withPipChainSchedExtension caller startTid fuel action fallback s
      = (schedUnwindAll caller S.lockAcquireSequence.reverse
           (action (schedAcquireAll caller S.lockAcquireSequence s)).1,
         (action (schedAcquireAll caller S.lockAcquireSequence s)).2) := by
  unfold withPipChainSchedExtension
  rw [h]
  exact runChainExtension_held schedulerLockBracketDomain caller S action fallback s hHeld

/-- **PR #892 review round 2 (the load-bearing negative)**: a declared footprint
the growing phase did **not** grant is unwound and the action never runs. -/
theorem withPipChainSchedExtension_refused {α : Type} (caller : CoreId)
    (startTid : SeLe4n.ThreadId) (fuel : Nat)
    (action : SystemState → SystemState × α) (fallback : α) (s : SystemState)
    (S : SchedLockSet)
    (h : SchedLockSet.ofList? (pipChainSchedFootprint s (pipChainVisited s startTid fuel))
          = some S)
    (hNot : ¬ schedLockSetHeld caller S (schedAcquireAll caller S.lockAcquireSequence s)) :
    withPipChainSchedExtension caller startTid fuel action fallback s
      = (schedUnwindAll caller S.lockAcquireSequence.reverse
           (schedAcquireAll caller S.lockAcquireSequence s), fallback) := by
  unfold withPipChainSchedExtension
  rw [h]
  exact runChainExtension_refused schedulerLockBracketDomain caller S action fallback s hNot

/-- **PR #892 review round 5 (the payoff)**: the chain extension acquires in
`SchedLockId`-ascending order — the SM0.I ladder — for **every** chain, with no
hypothesis about the order the walk discovered it in.

This is what `pipChainSchedFootprint_pairwise_le` could not say.  That theorem
takes the walk's path being `ObjId`-ascending as a hypothesis, and nothing at
this call site discharged it: `pipChainVisited` follows `blockingServer`
unconditionally, so a chain in which thread 10 blocks on thread 5 resolved to
`[tcb 10, tcb 5]` and `ofList?` accepted it — its check is key-uniqueness, which
that list satisfies.  The acquisition then took `tcb 10` before `tcb 5` while
any other operation naming both takes them the other way round: a lock-order
inversion, and a deadlock.  Sorting in the domain removes the hypothesis
entirely rather than adding a guard that a future resolver has to remember. -/
theorem pipChainSchedExtension_acquires_in_ladder_order (s : SystemState)
    (startTid : SeLe4n.ThreadId) (fuel : Nat) :
    ∀ S ∈ SchedLockSet.ofList? (pipChainSchedFootprint s (pipChainVisited s startTid fuel)),
      (schedulerLockBracketDomain.sequence S).Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst) :=
  fun S _ => schedulerLockBracketDomain_sequence_ordered S

/-- **WS-RR RR7.40 (the declaration resolves for an acyclic chain)**: a walk that
visits each thread once declares a footprint.

The `Nodup` hypothesis is the chain's acyclicity, the property `blockingAcyclic`
maintains — so the fail-closed arm above is reachable only for a chain the
kernel's own invariants already exclude, and the extension acquires on every
well-formed one.

**PR #892 review round 5**: this used to credit `walkStep`'s ascending guard as
well.  That guard belongs to `walkAndAcquire`, the object-domain hand-over-hand
walker, and `pipChainVisited` — the walk this footprint is resolved from — has
none: it follows `blockingServer` wherever the blocking graph goes.  Acyclicity
is what makes the keys distinct; ordering is the domain's, by sorting. -/
theorem withPipChainSchedExtension_resolves (s : SystemState)
    (startTid : SeLe4n.ThreadId) (fuel : Nat)
    (hNodup : (pipChainVisited s startTid fuel).Nodup) :
    (SchedLockSet.ofList? (pipChainSchedFootprint s (pipChainVisited s startTid fuel))).isSome
      = true := by
  rw [SchedLockSet.ofList?_isSome_of_nodup
    (pipChainSchedFootprint_keys_nodup s _ hNodup)]
  rfl

/-- **WS-RR RR7.40 (the extension composes with the declared bracket)**: a
chain extension nested inside `runBracketed` runs on the bracket's acquired
state and returns through the bracket's unwind.

The two are not alternatives.  A declared footprint is resolved before its own
locks are held, so the bracket revalidates; a walked chain is discovered by the
walk's own reads, so it does not.  A caller that needs both — the RR7.12 syscall
seam invoking a PIP walk — takes the declared bracket outside and the chain
extension inside, and this says the composition is the bracket's committed arm
with the extension as its step.

Stated at the generic bracket so it holds at either domain, and so a future
consumer cannot compose them in the other order (a bracket *inside* a chain
extension would acquire a footprint resolved while the chain's locks are already
held, which the ladder forbids). -/
theorem runBracketed_chainExtension_composes {α : Type}
    (D : Concurrency.LockBracketDomain)
    (declared : SystemState → Option D.Footprint) (lockCore : CoreId)
    (chain : D.Footprint) (action : SystemState → SystemState × α) (fallback : α)
    (st : SystemState) (S : D.Footprint)
    (hDecl : declared st = some S)
    (hGuard : declared (D.acquire lockCore (D.sequence S) st) = some S ∧
      D.held lockCore S (D.acquire lockCore (D.sequence S) st)) :
    Concurrency.runBracketed D declared lockCore
        (fun s => let r := runChainExtension D lockCore chain action fallback s; (r.2, r.1)) st
      = .committed
          ((runChainExtension D lockCore chain action fallback
              (D.acquire lockCore (D.sequence S) st)).2,
           D.unwind lockCore (D.sequence S).reverse
             (runChainExtension D lockCore chain action fallback
               (D.acquire lockCore (D.sequence S) st)).1) :=
  Concurrency.runBracketed_committed D declared lockCore _ st S hDecl hGuard

end SeLe4n.Kernel.PriorityInheritance
