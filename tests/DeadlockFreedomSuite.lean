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
import SeLe4n.Kernel.Concurrency.Locks.DeadlockInventory

/-!
# WS-SM SM3.D — Deadlock-freedom regression suite

Tier-2 / Tier-3 surface anchors + decidable examples + runtime
structural assertions for every public symbol introduced by SM3.D
(`Deadlock` / `DeadlockInventory`).

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

/-! ## SM3.D.3 — Irreflexive / Transitive (plan form) -/

#check @Irreflexive
#check @Transitive
#check @lockOrder_strict_classes

/-! ## SM3.D.5b — Mode-aware (conflict) wait graph -/

#check @ReachesPlus_mono
#check @Acyclic_mono
#check @conflictWaitsFor
#check @conflictWaitsFor_sub_blockedWaitsFor
#check @conflictWaitGraph_acyclic_under_2pl

/-! ## SM3.D.6b — Static lock-set size bounds -/

#check @insertOrMerge_size_le
#check @lockSetOfList_size_le
#check @lockSetExtendOpt_size_le
#check @size_le_1
#check @size_le_2
#check @size_le_3
#check @size_le_4
-- PR #870 round 6: the audit pair join the §6b size family and the §6c
-- aggregate (the plan's SM9.A.12 row claimed both; the landing had neither).
#check @lockSet_auditRead_size_le
#check @lockSet_auditDrain_size_le
#check @lockSetTransitions_within_bound

/-! ## SM3.D.6 — KernelOperation + contention-sensitive WCRT -/

#check @KernelOperation
#check @KernelOperation.ofEndpointCall
#check @KernelOperation.ofReplyRecv
#check @KernelOperation.ofTcbSuspend
#check @otherCores
#check @otherCores_length_eq
#check @contendersAhead
#check @contendersAhead_le
#check @sum_le_length_mul
#check @sum_map_le_sum_map
#check @WCRT
#check @totalWaitCost_le_bound
#check @WCRT_le_totalWaitCost

/-! ## SM3.D §7b/§7c — Model↔kernel bridge + twoCorePathScenario -/

#check @executionOfHeld
#check @executionOfHeld_heldBy
#check @lockSetHeld_realizes_heldBy
#check @twoCorePathScenario

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

-- WS-RR RR7.11: 8 → 9.  WS-OD OD3.5: 9 → 11.  WS-OD OD3.7: 11 → 13.  The widest
-- declared footprint is a `.replyRecv` every time: OD3.5 added the recorded
-- server's TCB and the *second* SchedContext hand-off that arm performs, and
-- OD3.7 added the two objects the donation return reads below the reply-stack
-- head — the Reply one frame down, and that frame's caller's TCB, which is a
-- validate-then-commit and so cannot be read unlocked.  See `maxLockSetSize`'s
-- docstring for why the answer was a wider ceiling rather than a narrower
-- declaration, each time.
example : maxLockSetSize = 13 := by decide
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

/-- SM3.D.6 bounded-wait (full): on the deadlock-free fixture, an
`endpointCall` operation is deadlock-free AND its worst-case response time
is bounded.  `KernelOperation.ofEndpointCall` carries the size proof. -/
example :
    noDeadlock execNoDeadlock ∧
    WCRT execNoDeadlock c0
        (KernelOperation.ofEndpointCall (ThreadId.ofNat 1)
          (SeLe4n.ObjId.ofNat 2) (SeLe4n.ObjId.ofNat 3) none none) 10
      ≤ maxLockSetSize * ((numCores - 1) * 10) :=
  boundedWait_under_2pl execNoDeadlock c0
    (KernelOperation.ofEndpointCall (ThreadId.ofNat 1)
      (SeLe4n.ObjId.ofNat 2) (SeLe4n.ObjId.ofNat 3) none none) 10
    (by decide) (by decide)

/-- SM3.D.6 combinatorial bound on a singleton lock set (size 1 ≤ `maxLockSetSize`). -/
example :
    totalWaitCost (LockSet.singleton tcb5 .write) 10
      ≤ maxLockSetSize * ((numCores - 1) * 10) :=
  totalWaitCost_le_bound (LockSet.singleton tcb5 .write) 10 (by decide)

/-- **Contention fixture** (positive-`WCRT` witness, deadlock-FREE): core 1
holds `tcb5` and is *running* (not blocked); core 0 is blocked waiting for
`tcb5`.  Core 1 will release, so there is no deadlock, and the fixture
satisfies both hypotheses.  Unlike `execNoDeadlock`, here a lock core 0
needs IS held by another core, so `contendersAhead` — and hence `WCRT` —
is positive (≠ 0), exercising the contention-sensitive WCRT model. -/
def execContention : KernelExecution :=
  { held := fun c => if c = c1 then [tcb5] else [],
    blocked := fun c => if c = c0 then some tcb5 else none }

/-- The single-lock operation `{tcb5}` (size 1 ≤ maxLockSetSize). -/
def opTcb5 : KernelOperation := ⟨LockSet.singleton tcb5 .write, by decide⟩

/-- SM3.D.6 (positive WCRT): on `execContention` — deadlock-free, yet core 1
holds the `tcb5` core 0 needs — the bounded-wait theorem gives deadlock-
freedom AND a wait bound.  Here `WCRT` genuinely counts the one contending
core (it is `> 0`, verified at runtime in §10). -/
example :
    noDeadlock execContention ∧
    WCRT execContention c0 opTcb5 10 ≤ maxLockSetSize * ((numCores - 1) * 10) :=
  boundedWait_under_2pl execContention c0 opTcb5 10 (by decide) (by decide)

/-- SM3.D.5b: the mode-aware conflict wait graph of the deadlock-free
fixture is acyclic (for any mode annotation — here all-write). -/
example :
    Acyclic (conflictWaitsFor execNoDeadlock (fun _ => AccessMode.write)
      (fun _ _ => AccessMode.write)) :=
  conflictWaitGraph_acyclic_under_2pl execNoDeadlock _ _ (by decide) (by decide)

/-- SM3.D.6: the `replyRecv` smart constructor (the deepest base-4 footprint)
builds a within-bound `KernelOperation`. -/
example :
    (KernelOperation.ofReplyRecv (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
      (ThreadId.ofNat 3) (SeLe4n.ObjId.ofNat 4) (some (ThreadId.ofNat 5))
      (some ⟨6⟩) (some (ThreadId.ofNat 7))).lockSet.size ≤ maxLockSetSize :=
  (KernelOperation.ofReplyRecv (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (ThreadId.ofNat 3) (SeLe4n.ObjId.ofNat 4) (some (ThreadId.ofNat 5))
    (some ⟨6⟩) (some (ThreadId.ofNat 7))).sizeWithinBound

/-- SM3.D §7b (non-vacuous bridge): after core 0 acquires the table lock on
the default state (SM3.C `acquireLockOnObject`), it genuinely holds the
singleton `{objStore 0}` (SM3.C `lockSetHeld`), so `lockSetHeld_realizes_heldBy`
yields both the concrete `lockHeld` and the abstract `heldBy` for that lock.
This exercises the bridge on a *non-empty, genuinely-held* lock set. -/
example :
    ∀ p ∈ (LockSet.singleton ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write).pairs,
      lockHeld c0 p.fst p.snd
          (acquireLockOnObject (default : SeLe4n.Model.SystemState) c0
            ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write) ∧
      heldBy (executionOfHeld c0
          (LockSet.singleton ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write) none) c0 p.fst :=
  lockSetHeld_realizes_heldBy c0
    (LockSet.singleton ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write)
    (acquireLockOnObject (default : SeLe4n.Model.SystemState) c0
      ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write) none (by decide)

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
  assertBool "maxLockSetSize = 13" (decide (maxLockSetSize = 13))
  assertBool "perLockWaitCost 10 = (numCores-1)*10 = 30" (decide (perLockWaitCost 10 = 30))
  -- A singleton lock set: total wait = 1 * (3 * 10) = 30.
  assertBool "totalWaitCost (singleton) 10 = 30"
    (decide (totalWaitCost (LockSet.singleton tcb5 .write) 10 = 30))
  -- Bounded by maxLockSetSize * (numCores-1) * T_cs, which is 11 * 3 * 10 = 330
  -- at the ceiling WS-OD OD3.5 raised it to.  The assertion names the constant,
  -- so it does not move with the ceiling; only this comment's arithmetic does.
  assertBool "totalWaitCost (singleton) 10 ≤ maxLockSetSize*(3*10)"
    (decide (totalWaitCost (LockSet.singleton tcb5 .write) 10
              ≤ maxLockSetSize * ((numCores - 1) * 10)))
  -- A real 2-element lock set: total wait = 2 * 30 = 60, still inside the
  -- maxLockSetSize * (numCores-1) * T_cs envelope.
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

private def runModeAwareChecks : IO Unit := do
  IO.println "--- §8 SM3.D.5b — mode-aware (conflict) wait graph ---"
  -- Auxiliary mode functions: every core requests write, every held lock is
  -- held in write mode (so all overlaps conflict).
  let wm : CoreId → AccessMode := fun _ => .write
  let hm : CoreId → LockId → AccessMode := fun _ _ => .write
  -- In execDeadlock both write-write edges are present (a genuine conflict).
  assertBool "execDeadlock: c0 conflictWaitsFor c1 (write–write conflict edge)"
    (decide (conflictWaitsFor execDeadlock wm hm c0 c1))
  -- Read–read does NOT conflict: with everyone reading, no conflict edge.
  let rd : CoreId → AccessMode := fun _ => .read
  let rdHeld : CoreId → LockId → AccessMode := fun _ _ => .read
  assertBool "execDeadlock: ¬ c0 conflictWaitsFor c1 under read–read (no conflict)"
    (decide (¬ conflictWaitsFor execDeadlock rd rdHeld c0 c1))
  -- Every conflict edge is a plain blocked-wait edge (subgraph witness).
  assertBool "conflict edge ⟹ blocked-wait edge (subgraph) on execDeadlock"
    (decide (¬ conflictWaitsFor execDeadlock wm hm c0 c1
              ∨ blockedWaitsFor execDeadlock c0 c1))

private def runSizeBoundChecks : IO Unit := do
  IO.println "--- §9 SM3.D.6b — static lock-set size bounds ---"
  -- `tcbSuspend` at every optional: base 3 plus five extensions, eight distinct
  -- locks (WS-SM SM6.E added the reply-link teardown write lock; WS-OD OD3.5
  -- added the SchedContext-index state-level lock).  It was the tree's widest
  -- footprint when `maxLockSetSize` was 8 and this comment claimed it sat *at*
  -- the bound; it no longer does, and the footprint that does is `replyRecv`
  -- below.  The assertion here is the bound, not the equality, so it is the
  -- claim that survives a ceiling change.
  let suspendSet := lockSet_tcbSuspend (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (ThreadId.ofNat 3) (some (SeLe4n.ObjId.ofNat 4)) (some (SeLe4n.ObjId.ofNat 5))
    (some ⟨6⟩) (some (ThreadId.ofNat 7)) (some ⟨8⟩)
  assertBool "lockSet_tcbSuspend (all options) size ≤ maxLockSetSize"
    (decide (suspendSet.size ≤ maxLockSetSize))
  -- replyRecv at **every** optional — base 4 plus five extensions, the widest
  -- footprint the kernel declares and the one `maxLockSetSize` is measured
  -- against (WS-RR RR7.11, WS-OD OD3.5, WS-OD OD3.7).  Taken at distinct threads
  -- and contexts throughout and with the capability install on, so this is the
  -- thirteen-member shape, not a merged one.
  let replySet := lockSet_replyRecv (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (ThreadId.ofNat 3) (SeLe4n.ObjId.ofNat 4) (some (ThreadId.ofNat 5))
    (some ⟨6⟩) (some (ThreadId.ofNat 7)) (some ⟨8⟩) true
    (some (ThreadId.ofNat 9)) (some ⟨10⟩) (some ⟨11⟩) (some (ThreadId.ofNat 12))
  assertBool "lockSet_replyRecv (all options) size ≤ maxLockSetSize"
    (decide (replySet.size ≤ maxLockSetSize))
  assertBool "lockSet_replyRecv (all options) size = maxLockSetSize (the bound, exactly)"
    (decide (replySet.size = maxLockSetSize))
  -- **WS-OD OD3.7 (the sharp bound): how much of the ceiling is slack.**  The
  -- thirteen is the union over ALL argument values; no reachable state supplies
  -- them all distinctly, because the returned donation's owner IS the answered
  -- caller, so those two arguments name one key and `insertOrMerge` lubs the
  -- modes without moving the cardinality.  Executed here at the *same* operands
  -- as the widest shape above with only the owner changed, so the difference is
  -- attributable to that one merge and nothing else.
  let reachableShapeReplyRecv := lockSet_replyRecv (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (ThreadId.ofNat 3) (SeLe4n.ObjId.ofNat 4) (some (ThreadId.ofNat 5))
    (some ⟨6⟩) (some (ThreadId.ofNat 3)) (some ⟨8⟩) true
    (some (ThreadId.ofNat 9)) (some ⟨10⟩) (some ⟨11⟩) (some (ThreadId.ofNat 12))
  assertBool "a .replyRecv whose donation owner is the answered caller declares 12"
    (decide (reachableShapeReplyRecv.size = 12))
  assertBool "…one inside the ceiling, which is the slack the constant carries"
    (decide (reachableShapeReplyRecv.size < maxLockSetSize))
  -- NEGATIVE: and it is exactly one member of slack, not two -- the recorded
  -- server merges with the invoking thread only on a NON-delegated reply, which
  -- is a case split rather than an invariant, so it cannot be taken in a bound.
  -- Keeping the delegated server distinct here is what makes that visible.
  assertBool "NEGATIVE: the sharpening is one member, not two"
    (!decide (reachableShapeReplyRecv.size = 11))
  -- WS-OD OD3.7: and the two below-head reads are each a member of their own —
  -- the reason the ceiling moved 11 → 13.  Stated as the drop, so a merge would
  -- fail here rather than silently make the raise look unnecessary.
  assertBool "…and dropping the two below-head reads drops it by exactly two"
    (decide ((lockSet_replyRecv (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
      (ThreadId.ofNat 3) (SeLe4n.ObjId.ofNat 4) (some (ThreadId.ofNat 5))
      (some ⟨6⟩) (some (ThreadId.ofNat 7)) (some ⟨8⟩) true
      (some (ThreadId.ofNat 9)) (some ⟨10⟩) none none).size = maxLockSetSize - 2))
  -- **The caps flag is a MODE, not a member.**  RR7.11 expressed the receiver's
  -- CSpace-root upgrade as `installsCaps`'s effect on an existing member's
  -- access mode, precisely so the footprint's size and acquisition order do not
  -- move with it — and WS-OD OD3.5 made the state-level member a *disjunction*,
  -- so a donating arm declares it whether or not it installs.  Both together
  -- mean the capless shape here is the same eleven members: the witness asserts
  -- the equality rather than a smaller number, because a size that *did* drop
  -- would mean one of those two design choices had been undone.
  let replySetCapless := lockSet_replyRecv (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (ThreadId.ofNat 3) (SeLe4n.ObjId.ofNat 4) (some (ThreadId.ofNat 5))
    (some ⟨6⟩) (some (ThreadId.ofNat 7)) (some ⟨8⟩) false
    (some (ThreadId.ofNat 9)) (some ⟨10⟩) (some ⟨11⟩) (some (ThreadId.ofNat 12))
  assertBool "lockSet_replyRecv capless size = maxLockSetSize (the caps flag is a mode)"
    (decide (replySetCapless.size = maxLockSetSize))
  assertBool "a capless donating .replyRecv still declares the state-level lock"
    (decide ((stateLevelLock, AccessMode.write) ∈ replySetCapless.pairs))
  -- WS-OD OD3.5: and the two members OD3.5 added are each a member of their own.
  let replySetNoServer := lockSet_replyRecv (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (ThreadId.ofNat 3) (SeLe4n.ObjId.ofNat 4) (some (ThreadId.ofNat 5))
    (some ⟨6⟩) (some (ThreadId.ofNat 7)) (some ⟨8⟩) true
    none (some ⟨10⟩) (some ⟨11⟩) (some (ThreadId.ofNat 12))
  assertBool "lockSet_replyRecv without a distinct recorded server size = 12"
    (decide (replySetNoServer.size = 12))
  let replySetNoRedonation := lockSet_replyRecv (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (ThreadId.ofNat 3) (SeLe4n.ObjId.ofNat 4) (some (ThreadId.ofNat 5))
    (some ⟨6⟩) (some (ThreadId.ofNat 7)) (some ⟨8⟩) true
    (some (ThreadId.ofNat 9)) none (some ⟨11⟩) (some (ThreadId.ofNat 12))
  assertBool "lockSet_replyRecv without the second hand-off size = 12"
    (decide (replySetNoRedonation.size = 12))
  -- The receive arm's caps shape gains the same member: 3 base + sender + reply
  -- + state-level = 6.
  let recvSet := lockSet_endpointReceive (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (SeLe4n.ObjId.ofNat 3) (some (ThreadId.ofNat 4)) (some ⟨5⟩) true none
  assertBool "lockSet_endpointReceive (caps) size = 6"
    (decide (recvSet.size = 6))
  let recvSetCapless := lockSet_endpointReceive (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (SeLe4n.ObjId.ofNat 3) (some (ThreadId.ofNat 4)) (some ⟨5⟩) false none
  assertBool "lockSet_endpointReceive capless size = 5"
    (decide (recvSetCapless.size = 5))
  -- **WS-OD OD3.6**: the widest `.receive` shape — a caps-carrying rendezvous
  -- that also donates: 3 base + sender + reply + donated SC + state-level = 7.
  let recvSetDonating := lockSet_endpointReceive (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (SeLe4n.ObjId.ofNat 3) (some (ThreadId.ofNat 4)) (some ⟨5⟩) true (some ⟨6⟩)
  assertBool "lockSet_endpointReceive (caps + donation) size = 7"
    (decide (recvSetDonating.size = 7))
  -- ...and the passive-server steady state: a donating receive that installs
  -- nothing still declares the state-level lock, because `scThreadIndex` is an
  -- `RHTable`.  3 base + sender + reply + donated SC + state-level = 7 again.
  let recvSetDonatingCapless := lockSet_endpointReceive (ThreadId.ofNat 1)
    (SeLe4n.ObjId.ofNat 2) (SeLe4n.ObjId.ofNat 3) (some (ThreadId.ofNat 4))
    (some ⟨5⟩) false (some ⟨6⟩)
  assertBool "lockSet_endpointReceive (donation, no caps) size = 7"
    (decide (recvSetDonatingCapless.size = 7))
  assertBool "a donating capless .receive still declares the state-level lock"
    (decide ((stateLevelLock, AccessMode.write) ∈ recvSetDonatingCapless.pairs))
  -- A KernelOperation carries its size proof; its lockSet fits by construction.
  let op := KernelOperation.ofTcbSuspend (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (ThreadId.ofNat 3) (some (SeLe4n.ObjId.ofNat 4)) (some (SeLe4n.ObjId.ofNat 5))
    (some ⟨6⟩) (some (ThreadId.ofNat 7))
  assertBool "KernelOperation.ofTcbSuspend lockSet within bound"
    (decide (op.lockSet.size ≤ maxLockSetSize))

/-- **WS-RR RR7.18** (register §6 finding 15): the four footprints
`lockSetTransitions_within_bound` had never reached, and the fifth defect the
census found beneath them.

These are not proofs about a hard case — each is a one-line helper application.
The point is that they *exist*: `boundedWait_under_2pl` and the `KernelOperation`
invariant take the size bound as a premise, so an unbounded footprint is a
transition the WCRT reasoning is **silent** about, which is worse than one it
bounds loosely.

The `endpointReply` check below is the one worth reading.  Its bound was stated
at five arguments while the footprint takes six — the sixth, `replyId`,
defaulted to `none` — so the shape the **live** `.reply` dispatch resolves
(`lockSet_endpointReplyOnCore` reads `target.replyObject`, and a reply always
has one) had no bound at all.  The check therefore takes it at `some`, which is
the case the old statement could not see. -/
private def runNewlyBoundedFootprintChecks : IO Unit := do
  IO.println "--- §9b WS-RR RR7.18 — the footprints the bundle had missed ---"
  -- `mintReplyCap` is `cspaceCopy`'s footprint: caller read + two CNode writes
  -- + the state-level CDT write.
  let mintSet := lockSet_mintReplyCap (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (SeLe4n.ObjId.ofNat 3)
  assertBool "lockSet_mintReplyCap size ≤ maxLockSetSize"
    (decide (mintSet.size ≤ maxLockSetSize))
  assertBool "…and it IS cspaceCopy's footprint, not a second declaration"
    (decide (mintSet = lockSet_cspaceCopy (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
      (SeLe4n.ObjId.ofNat 3)))
  -- Bind / unbind: four distinct objects, no optionals.
  let bindSet := lockSet_tcbBindNotification (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (SeLe4n.ObjId.ofNat 3) (ThreadId.ofNat 4) none
  let unbindSet := lockSet_tcbUnbindNotification (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (SeLe4n.ObjId.ofNat 3) (ThreadId.ofNat 4) none
  assertBool "lockSet_tcbBindNotification size = 4, within the bound"
    (decide (bindSet.size = 4 ∧ bindSet.size ≤ maxLockSetSize))
  assertBool "lockSet_tcbUnbindNotification is the same four members"
    (decide (unbindSet = bindSet))
  -- Affinity: three members plus the bound SchedContext, whose replenishments
  -- migrate with the thread.  Taken at `some`, which is the shape a bound
  -- thread's migration declares.
  let affSet := lockSet_tcbSetAffinity (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (ThreadId.ofNat 3) (some ⟨4⟩) none
  assertBool "lockSet_tcbSetAffinity (bound SC) size = 4, within the bound"
    (decide (affSet.size = 4 ∧ affSet.size ≤ maxLockSetSize))
  assertBool "…and the unbound shape is one member smaller"
    (decide ((lockSet_tcbSetAffinity (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
      (ThreadId.ofNat 3) none none).size = 3))
  -- THE ONE THE CENSUS FOUND: the reply footprint at its sixth argument.
  let replyWithObj := lockSet_endpointReply (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
    (ThreadId.ofNat 3) (some ⟨4⟩) (some (ThreadId.ofNat 5)) (some ⟨6⟩)
    (some ⟨7⟩) (some (ThreadId.ofNat 8))
  assertBool "lockSet_endpointReply WITH a reply object is bounded (the shape the live arm declares)"
    (decide (replyWithObj.size ≤ maxLockSetSize))
  -- WS-OD OD3.5: seven and six — a donating reply also declares the state-level
  -- lock, for the `scThreadIndex` maintenance the donation return performs.
  -- WS-OD OD3.7: nine and eight, with the two below-head reads.  **This arm did
  -- not need the ceiling raise** — only `.replyRecv` did — which is the fact
  -- that keeps the raise honest, so it is asserted here rather than described.
  assertBool "…and it is genuinely wider than the shape the old bound covered"
    (decide (replyWithObj.size = 9 ∧
      (lockSet_endpointReply (ThreadId.ofNat 1) (SeLe4n.ObjId.ofNat 2)
        (ThreadId.ofNat 3) (some ⟨4⟩) (some (ThreadId.ofNat 5)) none
        (some ⟨7⟩) (some (ThreadId.ofNat 8))).size = 8))
  assertBool "the reply arm fits with room to spare; the raise was owed to .replyRecv alone"
    (decide (replyWithObj.size < maxLockSetSize))

private def runWCRTChecks : IO Unit := do
  IO.println "--- §10 SM3.D.6 — contention-sensitive WCRT ---"
  -- contendersAhead ≤ numCores - 1 = 3 on any execution.
  assertBool "contendersAhead execDeadlock c0 tcb5 ≤ numCores - 1"
    (decide (contendersAhead execDeadlock c0 tcb5 ≤ numCores - 1))
  -- otherCores has exactly numCores - 1 = 3 elements.
  assertBool "otherCores c0 has numCores - 1 elements"
    (decide ((otherCores c0).length = numCores - 1))
  -- WCRT on a concrete op and execution is bounded by the static cap.
  let op := KernelOperation.ofEndpointCall (ThreadId.ofNat 1)
    (SeLe4n.ObjId.ofNat 2) (SeLe4n.ObjId.ofNat 3) none none
  assertBool "WCRT execNoDeadlock c0 (endpointCall op) 10 ≤ maxLockSetSize*(3*10)"
    (decide (WCRT execNoDeadlock c0 op 10 ≤ maxLockSetSize * ((numCores - 1) * 10)))
  -- WCRT never exceeds the uniform combinatorial bound.
  assertBool "WCRT ≤ totalWaitCost op.lockSet 10"
    (decide (WCRT execNoDeadlock c0 op 10 ≤ totalWaitCost op.lockSet 10))
  -- POSITIVE contention (non-vacuity): on execContention, core 1 holds tcb5,
  -- so contendersAhead is 1 (not 0) and WCRT is genuinely positive.
  assertBool "contendersAhead execContention c0 tcb5 = 1 (positive)"
    (decide (contendersAhead execContention c0 tcb5 = 1))
  assertBool "WCRT execContention c0 opTcb5 10 = 10 (positive, = 1 contender × T_cs)"
    (decide (WCRT execContention c0 opTcb5 10 = 10))
  assertBool "WCRT execContention c0 opTcb5 10 ≤ maxLockSetSize*(3*10) (bound still holds)"
    (decide (WCRT execContention c0 opTcb5 10 ≤ maxLockSetSize * ((numCores - 1) * 10)))
  -- execContention IS deadlock-free and satisfies both hypotheses.
  assertBool "execContention follows 2PL"
    (decide (executionFollows2PL execContention))
  assertBool "execContention acquires in LockId order"
    (decide (executionAcquiresInLockIdOrder execContention))
  assertBool "execContention is deadlock-free"
    (decide (noDeadlock execContention))

private def runBridgeChecks : IO Unit := do
  IO.println "--- §11 SM3.D §7b/§7c — model↔kernel bridge + twoCorePathScenario ---"
  -- executionOfHeld: the abstract heldBy reflects lock-set membership.
  let S := LockSet.singleton ⟨.tcb, (ThreadId.ofNat 5).toObjId⟩ .write
  let e := executionOfHeld c0 S none
  assertBool "executionOfHeld c0 S: heldBy c0 (tcb 5) holds"
    (decide (heldBy e c0 ⟨.tcb, (ThreadId.ofNat 5).toObjId⟩))
  assertBool "executionOfHeld c0 S: heldBy c0 (tcb 99) does NOT hold"
    (decide (¬ heldBy e c0 ⟨.tcb, (ThreadId.ofNat 99).toObjId⟩))
  -- twoCorePathScenario: the deadlock-free fixture is a canonical two-core path.
  assertBool "execNoDeadlock is a twoCorePathScenario c0 c1 tcb5 tcb7"
    (decide (twoCorePathScenario execNoDeadlock c0 c1 tcb5 tcb7))

private def runInventoryChecks : IO Unit := do
  IO.println "--- §12 SM3.D — inventory aggregator ---"
  assertBool "deadlockTheorems.length = 66" (decide (deadlockTheorems.length = 66))
  assertBool "model count = 3"
    (decide ((deadlockTheorems.filter (fun t => t.category == .model)).length = 3))
  assertBool "hypotheses count = 5"
    (decide ((deadlockTheorems.filter (fun t => t.category == .hypotheses)).length = 5))
  assertBool "order count = 5"
    (decide ((deadlockTheorems.filter (fun t => t.category == .order)).length = 5))
  assertBool "deadlock count = 6"
    (decide ((deadlockTheorems.filter (fun t => t.category == .deadlock)).length = 6))
  assertBool "waitGraph count = 9"
    (decide ((deadlockTheorems.filter (fun t => t.category == .waitGraph)).length = 9))
  assertBool "modeAware count = 5"
    (decide ((deadlockTheorems.filter (fun t => t.category == .modeAware)).length = 5))
  assertBool "sizeBound count = 8"
    (decide ((deadlockTheorems.filter (fun t => t.category == .sizeBound)).length = 8))
  assertBool "boundedWait count = 16"
    (decide ((deadlockTheorems.filter (fun t => t.category == .boundedWait)).length = 16))
  assertBool "grounding count = 9"
    (decide ((deadlockTheorems.filter (fun t => t.category == .grounding)).length = 9))
  assertBool "partition sum = total"
    (decide (
      (deadlockTheorems.filter (fun t => t.category == .model)).length +
      (deadlockTheorems.filter (fun t => t.category == .hypotheses)).length +
      (deadlockTheorems.filter (fun t => t.category == .order)).length +
      (deadlockTheorems.filter (fun t => t.category == .deadlock)).length +
      (deadlockTheorems.filter (fun t => t.category == .waitGraph)).length +
      (deadlockTheorems.filter (fun t => t.category == .modeAware)).length +
      (deadlockTheorems.filter (fun t => t.category == .sizeBound)).length +
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
  runModeAwareChecks
  runSizeBoundChecks
  runNewlyBoundedFootprintChecks
  runWCRTChecks
  runBridgeChecks
  runInventoryChecks
  IO.println "==============================================="
  IO.println "All SM3.D deadlock-freedom checks PASS."

end SeLe4n.Testing.DeadlockFreedom

def main : IO Unit :=
  SeLe4n.Testing.DeadlockFreedom.runDeadlockFreedomChecks
