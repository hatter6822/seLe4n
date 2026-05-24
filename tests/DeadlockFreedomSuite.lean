-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.LockSet
import SeLe4n.Kernel.Concurrency.Locks.Deadlock
import SeLe4n.Kernel.Concurrency.Locks.Sm3DInventory

/-!
# WS-SM SM3.D — Deadlock-freedom regression suite

Tier-2 / Tier-3 surface anchors + decidable examples + runtime
structural assertions for every public symbol introduced by SM3.D
(`Deadlock` / `Sm3DInventory`).

The suite exercises four families of checks:

* **Surface anchors** (§1).  Every public SM3.D symbol is `#check`'d so
  a rename or signature drift fails the suite at elaboration time.

* **Decidable examples** (§2).  Concrete `KernelExecution` fixtures are
  checked at elaboration time via `decide`: a deadlock-free 2-core
  scenario satisfies the hypotheses and `noDeadlock`; a genuine 2-core
  deadlock *necessarily violates* the ordering hypothesis (non-vacuity).

* **Theorem applications** (§3).  Compile-time `example`s instantiate
  the main theorems (`deadlockFreedom_under_2pl_and_ordering`,
  `waitGraph_acyclic_under_2pl`, `boundedWait_under_2pl`,
  `execution_satisfies_hypotheses_of_all_prefix`) on the fixtures,
  proving they are inhabited (not vacuous false-anchors).

* **Runtime assertions** (§4).  The fixtures' decidable properties, the
  bounded-wait arithmetic, and the SM3.D inventory count witnesses run
  at `lake exe deadlock_freedom_suite` and assert via `assertBool`.
-/

namespace SeLe4n.Testing.DeadlockFreedom

open SeLe4n
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1 — Surface anchors
-- ============================================================================

/-! ## SM3.D.1 — KernelExecution model -/

#check @KernelExecution
#check @blockedAt
#check @heldBy

/-! ## SM3.D.4 — Hypotheses + ladder invariant -/

#check @coreFollows2PL
#check @coreAcquiresInOrder
#check @executionFollows2PL
#check @executionAcquiresInLockIdOrder
#check @ladder_of_2pl_and_order

/-! ## SM3.D.3 — Strict-order helpers -/

#check @lockOrder_strict
#check @LockId.lt_irrefl
#check @LockId.lt_trans
#check @LockId.lt_asymm

/-! ## SM3.D.1 / SM3.D.4 — noDeadlock + Theorem 2.1.9 -/

#check @noDeadlock
#check @mutualBlocked
#check @noDeadlockDec
#check @noDeadlock_iff_dec
#check @noDeadlock_definition_decidable
#check @deadlockFreedom_under_2pl_and_ordering

/-! ## SM3.D.5 — Wait-graph acyclicity -/

#check @waitsForCore
#check @blockedWaitsFor
#check @ReachesPlus
#check @Acyclic
#check @waitGraph
#check @blockedWaitsFor_wanted_lt
#check @reachesPlus_wanted_lt
#check @waitGraph_acyclic_under_2pl
#check @noDeadlock_of_waitGraph_acyclic

/-! ## SM3.D.6 — Bounded wait -/

#check @maxLockSetSize
#check @perLockWaitCost
#check @totalWaitCost
#check @sum_const_map
#check @totalWaitCost_eq
#check @boundedWait_under_2pl

/-! ## SM3.D §7 — Grounding bridge -/

#check @acquireOrder_nodup
#check @CorePrefixOf
#check @coreFollows2PL_of_prefix
#check @coreAcquiresInOrder_of_prefix
#check @execution_satisfies_hypotheses_of_all_prefix

/-! ## SM3.D — Inventory aggregator -/

#check @DeadlockCategory
#check @DeadlockTheorem
#check @deadlockTheorems
#check @deadlockTheorems_count
#check @deadlockTheorems_partition_sum
#check @deadlockTheorems_identifiers_nodup
#check @deadlockTheorems_descriptions_nodup

-- ============================================================================
-- §2 — Fixtures
-- ============================================================================

/-- Core 0. -/
def c0 : CoreId := ⟨0, by decide⟩
/-- Core 1. -/
def c1 : CoreId := ⟨1, by decide⟩

/-- A `.tcb` lock at ObjId 5 (lower in the LockId order). -/
def tcb5 : LockId := ⟨.tcb, SeLe4n.ObjId.ofNat 5⟩
/-- A `.tcb` lock at ObjId 7 (higher in the LockId order). -/
def tcb7 : LockId := ⟨.tcb, SeLe4n.ObjId.ofNat 7⟩

/-- **Deadlock-free scenario** (plan §5.4 SM3.D.7): two cores both want
`{tcb5, tcb7}`.  Core 0 holds the lower lock `tcb5` and is blocked on the
higher `tcb7`; core 1 holds nothing and is blocked on `tcb5` (held by
core 0).  Both acquire in ascending order, so there is no cycle: core 0
will acquire `tcb7`, finish, and release, after which core 1 proceeds. -/
def execNoDeadlock : KernelExecution :=
  { held := fun c => if c = c0 then [tcb5] else [],
    blocked := fun c =>
      if c = c0 then some tcb7
      else if c = c1 then some tcb5
      else none }

/-- **Genuine 2-core deadlock** (non-vacuity witness): core 0 holds the
*higher* lock `tcb7` and waits for the *lower* `tcb5`; core 1 holds `tcb5`
and waits for `tcb7`.  This is a real mutual block — and it *necessarily*
violates the `LockId`-ascending ordering hypothesis (core 0 holds `tcb7`
yet blocks on `tcb5 < tcb7`).  Demonstrates the theorem is not vacuous:
every deadlock state falsifies a hypothesis. -/
def execDeadlock : KernelExecution :=
  { held := fun c => if c = c0 then [tcb7] else if c = c1 then [tcb5] else [],
    blocked := fun c =>
      if c = c0 then some tcb5
      else if c = c1 then some tcb7
      else none }

-- ============================================================================
-- §2b — Decidable examples (elaboration-time)
-- ============================================================================

/-! ## SM3.D.3 — Strict order on concrete LockIds -/

example : ¬ (tcb5 < tcb5) := by decide
example : tcb5 < tcb7 := by decide
example : ¬ (tcb7 < tcb5) := by decide

/-! ## SM3.D.4 — Deadlock-free fixture satisfies the hypotheses -/

example : executionFollows2PL execNoDeadlock := by decide
example : executionAcquiresInLockIdOrder execNoDeadlock := by decide
example : noDeadlock execNoDeadlock := by decide

/-! ## SM3.D.4 — Deadlock fixture violates ordering (non-vacuity) -/

example : ¬ noDeadlock execDeadlock := by decide
example : ¬ executionAcquiresInLockIdOrder execDeadlock := by decide
example : mutualBlocked execDeadlock c0 c1 := by decide
example : ¬ mutualBlocked execNoDeadlock c0 c1 := by decide

/-! ## SM3.D.6 — Bounded-wait arithmetic -/

example : maxLockSetSize = 8 := by decide
example : perLockWaitCost 10 = 30 := by decide
-- The `totalWaitCost ≤ …` bound is established via the theorem in §3
-- (`boundedWait_under_2pl`).  Elaboration-time `decide` cannot reduce
-- `lockAcquireSequence`'s `mergeSort` (well-founded recursion does not
-- kernel-reduce); the concrete numeric value is checked at runtime in §5
-- via compiled `decide`.

-- ============================================================================
-- §3 — Theorem applications (compile-time inhabitation witnesses)
-- ============================================================================

/-! The main theorems, instantiated on the deadlock-free fixture, are
inhabited — they are genuine proofs, not vacuous anchors. -/

/-- SM3.D.4 Theorem 2.1.9 on the deadlock-free fixture (hypotheses by
`decide`). -/
example : noDeadlock execNoDeadlock :=
  deadlockFreedom_under_2pl_and_ordering execNoDeadlock (by decide) (by decide)

/-- SM3.D.5 wait-graph acyclicity on the deadlock-free fixture. -/
example : Acyclic (waitGraph execNoDeadlock) :=
  waitGraph_acyclic_under_2pl execNoDeadlock (by decide) (by decide)

/-- SM3.D.5 coherence: acyclicity ⟹ noDeadlock. -/
example : noDeadlock execNoDeadlock :=
  noDeadlock_of_waitGraph_acyclic execNoDeadlock
    (waitGraph_acyclic_under_2pl execNoDeadlock (by decide) (by decide))

/-- SM3.D.6 bounded-wait on a singleton lock set (size 1 ≤ 8). -/
example :
    totalWaitCost (LockSet.singleton tcb5 .write) 10
      ≤ maxLockSetSize * ((numCores - 1) * 10) :=
  boundedWait_under_2pl (LockSet.singleton tcb5 .write) 10 (by decide)

/-- SM3.D §7 grounding: a real `CorePrefixOf` witness on a 2-element lock
set.  `execGrounded` holds the prefix `[tcb5]` of the canonical acquire
order `[tcb5, tcb7]` and is blocked on the next lock `tcb7`. -/
def execGrounded : KernelExecution :=
  { held := fun c => if c = c0 then [tcb5] else [],
    blocked := fun c => if c = c0 then some tcb7 else none }

/-- The 2-element lock set whose canonical acquire order is `[tcb5, tcb7]`. -/
def twoLockSet : LockSet := (LockSet.singleton tcb7 .write).insertOrMerge tcb5 .write

/-- SM3.D §7: `execGrounded`'s core 0 is in the 2PL growing-phase prefix
of `twoLockSet`.  Witnessed by the split `acquireOrder = [tcb5] ++ tcb7 :: []`.

The `acquireOrder` equality is checked with `native_decide` because it
reduces `lockAcquireSequence`'s `mergeSort` (well-founded recursion that
does not kernel-reduce, so plain `decide` cannot discharge it); the
held/blocked equalities reduce structurally under plain `decide`. -/
example : CorePrefixOf execGrounded c0 twoLockSet :=
  ⟨[tcb5], [], tcb7, by native_decide, by decide, by decide⟩

-- ============================================================================
-- §4 — Runtime assertions
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS  {name}"
  else
    IO.eprintln s!"  FAIL  {name}"
    IO.Process.exit 1

private def runStrictOrderChecks : IO Unit := do
  IO.println "--- §1 SM3.D.3 — LockId strict order ---"
  assertBool "¬ (tcb5 < tcb5) [irreflexive]" (decide (¬ (tcb5 < tcb5)))
  assertBool "tcb5 < tcb7 [ascending objId]" (decide (tcb5 < tcb7))
  assertBool "¬ (tcb7 < tcb5) [asymmetric]" (decide (¬ (tcb7 < tcb5)))

private def runHypothesisChecks : IO Unit := do
  IO.println "--- §2 SM3.D.4 — deadlock-free fixture satisfies hypotheses ---"
  assertBool "execNoDeadlock follows 2PL" (decide (executionFollows2PL execNoDeadlock))
  assertBool "execNoDeadlock acquires in LockId order"
    (decide (executionAcquiresInLockIdOrder execNoDeadlock))
  assertBool "execNoDeadlock is deadlock-free" (decide (noDeadlock execNoDeadlock))
  assertBool "execNoDeadlock has no mutual block (c0,c1)"
    (decide (¬ mutualBlocked execNoDeadlock c0 c1))

private def runDeadlockNonVacuityChecks : IO Unit := do
  IO.println "--- §3 SM3.D.4 — genuine deadlock violates ordering (non-vacuity) ---"
  -- execDeadlock IS a deadlock (mutual block).
  assertBool "execDeadlock has mutual block (c0,c1)"
    (decide (mutualBlocked execDeadlock c0 c1))
  assertBool "execDeadlock is NOT deadlock-free" (decide (¬ noDeadlock execDeadlock))
  -- And it necessarily violates the ordering hypothesis (the contrapositive
  -- of deadlockFreedom_under_2pl_and_ordering).
  assertBool "execDeadlock VIOLATES the LockId-ordering hypothesis"
    (decide (¬ executionAcquiresInLockIdOrder execDeadlock))

private def runWaitGraphChecks : IO Unit := do
  IO.println "--- §4 SM3.D.5 — wait-graph edges (decidable) ---"
  -- In execNoDeadlock there is a single edge c1 → c0 (c1 blocked on tcb5
  -- which c0 holds, and c0 is also blocked).  No reverse edge c0 → c1.
  assertBool "execNoDeadlock: c1 blockedWaitsFor c0 (edge present)"
    (decide (blockedWaitsFor execNoDeadlock c1 c0))
  assertBool "execNoDeadlock: ¬ c0 blockedWaitsFor c1 (no reverse edge ⟹ no 2-cycle)"
    (decide (¬ blockedWaitsFor execNoDeadlock c0 c1))
  -- In execDeadlock both edges are present (the 2-cycle the ordering
  -- hypothesis rules out).
  assertBool "execDeadlock: c0 blockedWaitsFor c1 (cycle edge)"
    (decide (blockedWaitsFor execDeadlock c0 c1))
  assertBool "execDeadlock: c1 blockedWaitsFor c0 (cycle edge)"
    (decide (blockedWaitsFor execDeadlock c1 c0))

private def runBoundedWaitChecks : IO Unit := do
  IO.println "--- §5 SM3.D.6 — bounded wait ---"
  assertBool "maxLockSetSize = 8" (decide (maxLockSetSize = 8))
  assertBool "perLockWaitCost 10 = (numCores-1)*10 = 30" (decide (perLockWaitCost 10 = 30))
  -- A singleton lock set: total wait = 1 * (3 * 10) = 30.
  assertBool "totalWaitCost (singleton) 10 = 30"
    (decide (totalWaitCost (LockSet.singleton tcb5 .write) 10 = 30))
  -- Bounded by maxLockSetSize * (numCores-1) * T_cs = 8 * 3 * 10 = 240.
  assertBool "totalWaitCost (singleton) 10 ≤ 8*(3*10)"
    (decide (totalWaitCost (LockSet.singleton tcb5 .write) 10
              ≤ maxLockSetSize * ((numCores - 1) * 10)))
  -- A real 2-element lock set: total wait = 2 * 30 = 60, still ≤ 240.
  assertBool "totalWaitCost (twoLockSet) 10 = 60"
    (decide (totalWaitCost twoLockSet 10 = 60))
  assertBool "twoLockSet.size (= 2) ≤ maxLockSetSize"
    (decide (twoLockSet.size ≤ maxLockSetSize))

private def runGroundingChecks : IO Unit := do
  IO.println "--- §6 SM3.D §7 — grounding bridge ---"
  -- A prefix-shaped execution satisfies BOTH hypotheses (consistent with
  -- execution_satisfies_hypotheses_of_all_prefix).
  assertBool "execGrounded follows 2PL (prefix-shaped)"
    (decide (executionFollows2PL execGrounded))
  assertBool "execGrounded acquires in order (prefix-shaped)"
    (decide (executionAcquiresInLockIdOrder execGrounded))
  -- The canonical acquire order of the 2-element set is [tcb5, tcb7].
  assertBool "acquireOrder twoLockSet = [tcb5, tcb7]"
    (decide (acquireOrder twoLockSet = [tcb5, tcb7]))

private def runInventoryChecks : IO Unit := do
  IO.println "--- §7 SM3.D — inventory aggregator ---"
  assertBool "deadlockTheorems.length = 37" (decide (deadlockTheorems.length = 37))
  assertBool "model count = 3"
    (decide ((deadlockTheorems.filter (fun t => t.category == .model)).length = 3))
  assertBool "hypotheses count = 5"
    (decide ((deadlockTheorems.filter (fun t => t.category == .hypotheses)).length = 5))
  assertBool "order count = 4"
    (decide ((deadlockTheorems.filter (fun t => t.category == .order)).length = 4))
  assertBool "deadlock count = 6"
    (decide ((deadlockTheorems.filter (fun t => t.category == .deadlock)).length = 6))
  assertBool "waitGraph count = 9"
    (decide ((deadlockTheorems.filter (fun t => t.category == .waitGraph)).length = 9))
  assertBool "boundedWait count = 5"
    (decide ((deadlockTheorems.filter (fun t => t.category == .boundedWait)).length = 5))
  assertBool "grounding count = 5"
    (decide ((deadlockTheorems.filter (fun t => t.category == .grounding)).length = 5))
  assertBool "partition sum = total"
    (decide (
      (deadlockTheorems.filter (fun t => t.category == .model)).length +
      (deadlockTheorems.filter (fun t => t.category == .hypotheses)).length +
      (deadlockTheorems.filter (fun t => t.category == .order)).length +
      (deadlockTheorems.filter (fun t => t.category == .deadlock)).length +
      (deadlockTheorems.filter (fun t => t.category == .waitGraph)).length +
      (deadlockTheorems.filter (fun t => t.category == .boundedWait)).length +
      (deadlockTheorems.filter (fun t => t.category == .grounding)).length =
      deadlockTheorems.length))

def runDeadlockFreedomChecks : IO Unit := do
  IO.println "WS-SM SM3.D — deadlock-freedom regression suite"
  IO.println "==============================================="
  runStrictOrderChecks
  runHypothesisChecks
  runDeadlockNonVacuityChecks
  runWaitGraphChecks
  runBoundedWaitChecks
  runGroundingChecks
  runInventoryChecks
  IO.println "==============================================="
  IO.println "All SM3.D deadlock-freedom checks PASS."

end SeLe4n.Testing.DeadlockFreedom

def main : IO Unit :=
  SeLe4n.Testing.DeadlockFreedom.runDeadlockFreedomChecks
