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

SM3.C.11 built the chain walker, whose footprint was **each chain member's TCB
write lock** (`chainLockSeq`).  That was every lock the object domain could
name.  What the walk actually writes is more: `updatePipBoostOnCore` writes
the member's TCB *and* migrates its run-queue bucket on **its own home core**, so
the footprint owed a per-member `LockKey.runQueue` write lock that `LockSet`
had no constructor for.  That is what `UncoveredLockDomain.dynamicPipChain`
recorded, and RR7.39 removed the obstacle by giving the scheduler domain a
runtime.

## Why two segments rather than hand-over-hand per member

The natural reading of "extend the held set as each member is discovered" is to
take that member's two locks together before moving on.  The `LockKey` order
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
  LockKey LockSet)

-- ============================================================================
-- §1  The footprint
-- ============================================================================

/-- **WS-RR RR7.40**: the home cores of a chain's members — the cores whose
run-queue buckets the walk can migrate.

`determineTargetCore` at each visited thread, canonicalised through
`Concurrency.canonicalCores`, so the result is `CoreId`-ascending and
duplicate-free by construction (two members may share a home core, and a chain
crossing four cores must still name each once).

**WS-RR RR8.12**: the `allCores.filter` this used to spell inline is that shared
definition now — the same derivation, read from the one place that states it, so
the run-queue segment below and the per-arm syscall-seam segments cannot disagree
about what "the cores, as a list a lock ladder can be walked in" means. -/
def pipChainHomeCores (s : SystemState) (visited : List SeLe4n.ThreadId) : List CoreId :=
  Concurrency.canonicalCores (visited.map (determineTargetCore s))

/-- **WS-RR RR7.40**: the home-core segment is duplicate-free — it is a sublist
of `allCores`. -/
theorem pipChainHomeCores_nodup (s : SystemState) (visited : List SeLe4n.ThreadId) :
    (pipChainHomeCores s visited).Nodup :=
  Concurrency.canonicalCores_nodup _

/-- **WS-RR RR7.40**: every member's home core is in the segment — the coverage
half, and the one a false footprint would fail. -/
theorem mem_pipChainHomeCores (s : SystemState) (visited : List SeLe4n.ThreadId)
    (t : SeLe4n.ThreadId) (ht : t ∈ visited) :
    determineTargetCore s t ∈ pipChainHomeCores s visited :=
  (Concurrency.mem_canonicalCores _ _).mpr (List.mem_map.mpr ⟨t, ht, rfl⟩)

/-- **WS-RR RR7.40**: a core in the segment is some member's home core — the
converse, so the segment names no core the walk cannot touch. -/
theorem pipChainHomeCores_mem (s : SystemState) (visited : List SeLe4n.ThreadId)
    (c : CoreId) (hc : c ∈ pipChainHomeCores s visited) :
    ∃ t ∈ visited, determineTargetCore s t = c := by
  obtain ⟨t, ht, hEq⟩ := List.mem_map.mp ((Concurrency.mem_canonicalCores _ _).mp hc)
  exact ⟨t, ht, hEq⟩

/-- **WS-RR RR7.40**: the segment is bounded by the core count. -/
theorem pipChainHomeCores_length_le (s : SystemState) (visited : List SeLe4n.ThreadId) :
    (pipChainHomeCores s visited).length ≤ numCores :=
  Concurrency.canonicalCores_length_le _

/-- **WS-RR RR7.40**: the PIP chain walk's scheduler-domain footprint.

Two segments in `LockKey` order: every visited thread's TCB **write** lock,
then every home core's run-queue **write** lock.  The first covers the boost
itself (`updatePipBoostOnCore` rewrites the member's `pipBoost`), the second the
bucket migration (`setRunQueueOnCore` at that member's home core).

Both are `.write`: the walk reads a member's priority in order to rewrite it, and
a read lock would let a concurrent writer change the value between the read and
the store. -/
def pipChainSchedFootprint (s : SystemState) (visited : List SeLe4n.ThreadId) :
    List (LockKey × AccessMode) :=
  visited.map (fun t => (LockKey.object ⟨LockKind.tcb, t.toObjId⟩, AccessMode.write))
    ++ schedCoreSegment (fun c => LockKey.runQueue c)
        (visited.map (determineTargetCore s))

/-- **WS-RR RR7.40**: every lock in the chain footprint is a **write** lock. -/
theorem pipChainSchedFootprint_write_only (s : SystemState) (visited : List SeLe4n.ThreadId) :
    ∀ p ∈ pipChainSchedFootprint s visited, p.2 = AccessMode.write := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h; rfl
  · exact schedCoreSegment_write_only _ _ p h

/-- **WS-RR RR7.40**: a visited thread's TCB write lock is in the footprint. -/
theorem mem_pipChainSchedFootprint_tcb (s : SystemState) (visited : List SeLe4n.ThreadId)
    (t : SeLe4n.ThreadId) (ht : t ∈ visited) :
    (LockKey.object ⟨LockKind.tcb, t.toObjId⟩, AccessMode.write)
      ∈ pipChainSchedFootprint s visited :=
  List.mem_append_left _ (List.mem_map.mpr ⟨t, ht, rfl⟩)

/-- **WS-RR RR7.40**: a visited thread's **home-core run-queue** write lock is in
the footprint — the member the object domain could not name, and the whole reason
this footprint exists. -/
theorem mem_pipChainSchedFootprint_runQueue (s : SystemState) (visited : List SeLe4n.ThreadId)
    (t : SeLe4n.ThreadId) (ht : t ∈ visited) :
    (LockKey.runQueue (determineTargetCore s t), AccessMode.write)
      ∈ pipChainSchedFootprint s visited :=
  List.mem_append_right _
    ((mem_schedCoreSegment_iff runQueueLock_injective _ (determineTargetCore s t)).mpr
      (List.mem_map.mpr ⟨t, ht, rfl⟩))

/-- **WS-RR RR7.40**: the footprint's length — one lock per visited thread plus
one per distinct home core.

Stated against the chain length and `numCores`, **not** against
`maxLockSetSize`: a walked chain is bounded by `MAX_PIP_RETRIES`, and reading the
static ceiling into it would read the WCRT figures as covering the PIP walk. -/
theorem pipChainSchedFootprint_length (s : SystemState) (visited : List SeLe4n.ThreadId) :
    (pipChainSchedFootprint s visited).length
      ≤ visited.length + numCores := by
  simp only [pipChainSchedFootprint, List.length_append, List.length_map]
  exact Nat.add_le_add_left
    (schedCoreSegment_length_le (fun c => LockKey.runQueue c) _) _

-- ============================================================================
-- §2  Ordering and uniqueness
-- ============================================================================

/-- **WS-RR RR7.40**: a footprint key is either a visited thread's TCB lock or a
home core's run-queue lock — the case analysis every ordering and uniqueness
proof below runs. -/
theorem pipChainSchedFootprint_key_shape {s : SystemState}
    {visited : List SeLe4n.ThreadId} {k : LockKey}
    (hk : k ∈ (pipChainSchedFootprint s visited).map (·.1)) :
    (∃ t ∈ visited, k = LockKey.object ⟨LockKind.tcb, t.toObjId⟩) ∨
      (∃ c ∈ pipChainHomeCores s visited, k = LockKey.runQueue c) := by
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
different `LockKey` constructors. -/
theorem pipChainSchedFootprint_keys_nodup (s : SystemState) (visited : List SeLe4n.ThreadId)
    (hNodup : visited.Nodup) :
    ((pipChainSchedFootprint s visited).map (·.1)).Nodup := by
  simp only [pipChainSchedFootprint, List.map_append]
  refine List.nodup_append.2 ⟨?_, ?_, ?_⟩
  · -- the TCB segment: an injective image of a duplicate-free list
    rw [List.map_map]
    have hInj : ∀ a b : SeLe4n.ThreadId,
        (LockKey.object ⟨LockKind.tcb, a.toObjId⟩ : LockKey)
          = LockKey.object ⟨LockKind.tcb, b.toObjId⟩ → a = b := by
      intro a b hab
      have hOid : a.toObjId = b.toObjId :=
        congrArg Concurrency.LockId.objId (LockKey.object.inj hab)
      exact SeLe4n.ThreadId.toObjId_injective a b hOid
    exact List.Pairwise.map _ (fun a b h he => h (hInj a b he)) hNodup
  · -- the run-queue segment: the shared segment's own uniqueness (WS-RR RR8.12)
    exact schedCoreSegment_keys_nodup runQueueLock_injective _
  · -- disjoint: an object key is never a run-queue key
    intro a ha b hb
    rw [List.map_map] at ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, _, rfl⟩ := schedCoreSegment_map_fst_mem hb
    simp

/-- **WS-RR RR7.40**: the footprint's keys form a `LockKey`-ascending
acquisition sequence, given that the walk's path is `ObjId`-ascending.

The `hAsc` hypothesis is exactly what `walkAndAcquire` guarantees on a terminated
walk (`walkAndAcquire_path_ascending_in_ObjId_if_terminated`), so a chain the
walker accepts has an ordered footprint and a chain it refuses declares none.
Across the two segments the ordering is free: `LockKey.object_lt_runQueue`
puts every object lock below every run-queue lock, which is why the footprint has
to be two segments rather than per-member pairs. -/
theorem pipChainSchedFootprint_pairwise_le (s : SystemState) (visited : List SeLe4n.ThreadId)
    (hAsc : visited.Pairwise (fun a b => a.toNat < b.toNat)) :
    ((pipChainSchedFootprint s visited).map (·.1)).Pairwise (· ≤ ·) := by
  simp only [pipChainSchedFootprint, List.map_append]
  refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
  · -- within the TCB segment: the SM0.I `LockId` order at equal kind is by ObjId
    rw [List.map_map]
    refine List.Pairwise.map _ (fun a b hab => ?_) hAsc
    show (LockKey.object ⟨LockKind.tcb, a.toObjId⟩ : LockKey)
      ≤ LockKey.object ⟨LockKind.tcb, b.toObjId⟩
    -- SM0.I's `LockId` order is lexicographic: equal kind, then `objId.val`.
    exact Or.inr ⟨rfl, Nat.le_of_lt hab⟩
  · -- within the run-queue segment: `CoreId`-ascending, from `allCores`.
    -- WS-RR RR8.12: the shared segment's own ordering lemma, which routes through
    -- `Concurrency.allCores_pairwise_le` rather than a `decide` at the literal
    -- `numCores` — for the reason `allCores_nodup`'s docstring gives, a `decide`
    -- stops reducing the moment `numCores` is parameterised by
    -- `PlatformBinding.coreCount`.
    exact schedCoreSegment_pairwise_le _ _ (fun c d h => h)
  · -- across the segments: every object lock precedes every run-queue lock
    intro a ha b hb
    rw [List.map_map] at ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, _, rfl⟩ := schedCoreSegment_map_fst_mem hb
    exact (LockKey.object_lt_runQueue _ _).1


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
-- §5  The declaration resolves
-- ============================================================================

/-- **WS-RR RR7.40 (the declaration resolves for an acyclic chain)**: a walk that
visits each thread once declares a footprint.

The `Nodup` hypothesis is the chain's acyclicity, the property `blockingAcyclic`
maintains — so `LockSet.ofList?`'s fail-closed `none` is reachable only for a
chain the kernel's own invariants already exclude, and every well-formed chain
declares.  Ordering is the domain's, by sorting
(`LockSet.lockAcquireSequence`): `pipChainVisited` follows `blockingServer`
wherever the blocking graph goes, so a chain in which thread 10 blocks on
thread 5 resolves to `[tcb 10, tcb 5]`, and it is the sort, not a guard at
this site, that puts the footprint on the SM0.I ladder (PR #892 review round 5).

**WS-LS LS2.4**: the runtime extension that acquired this footprint
(`withPipChainSchedExtension`, over `runChainExtension` at the object domain) is
deleted with the word-level bracket; the footprint is declared statically at
the seams that walk the chain (`SyscallSchedFootprint`), and
`propagatePipChainCrossCore_coversWrites` (§4) is the proof the seam's
`BracketSpec` carries that the walk writes nothing outside it. -/
theorem pipChainSchedFootprint_resolves (s : SystemState)
    (startTid : SeLe4n.ThreadId) (fuel : Nat)
    (hNodup : (pipChainVisited s startTid fuel).Nodup) :
    (LockSet.ofList? (pipChainSchedFootprint s (pipChainVisited s startTid fuel))).isSome
      = true := by
  rw [LockSet.ofList?_isSome_of_nodup
    (pipChainSchedFootprint_keys_nodup s _ hNodup)]
  rfl

end SeLe4n.Kernel.PriorityInheritance
