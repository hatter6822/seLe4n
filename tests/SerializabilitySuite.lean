-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.LockSet
import SeLe4n.Kernel.Concurrency.Locks.Serializability
import SeLe4n.Kernel.Concurrency.Locks.Sm3EInventory

/-!
# WS-SM SM3.E — Serializability regression suite

Tier-2 / Tier-3 surface anchors + decidable examples + theorem-application
witnesses + runtime structural assertions for every public symbol introduced by
SM3.E (`Serializability` / `Sm3EInventory`).

Four families of checks (mirroring `DeadlockFreedomSuite`):

* **Surface anchors** (§1).  Every public SM3.E symbol is `#check`'d so a rename
  or signature drift fails the suite at elaboration time.
* **Decidable examples** (§2).  Concrete `KernelTransitionInstance` fixtures are
  checked at elaboration time via `decide`: conflicting vs non-conflicting pairs,
  the commit-oriented conflict edge, strict-2PL.
* **Theorem applications** (§3).  Compile-time `example`s instantiate the main
  theorems (`serializability_under_2pl`, `serializability_of_readOnly_schedule`,
  `conflictGraph_acyclic`, `singleCore_proof_preservation`,
  `updateObjectAt_objStoreEquiv_comm`) on the fixtures, proving they are
  inhabited (not vacuous false-anchors).
* **Runtime assertions** (§4).  The fixtures' decidable properties, the commit
  sort, the conflict relation, and the SM3.E inventory count witnesses run at
  `lake exe serializability_suite` and assert via `assertBool`.
-/

namespace SeLe4n.Testing.Serializability

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1 — Surface anchors
-- ============================================================================

/-! ## SM3.E.2 — Transition-instance model -/
#check @KernelTransitionInstance
#check @applySequential
#check @applySequential_nil
#check @applySequential_cons
#check @applySequential_append

/-! ## SM3.E.1 — Conflict relation + conflictOrder -/
#check @ktiSharesConflictingLock
#check @ktiConflictsB
#check @ktiConflictsB_iff
#check @ktiSharesConflictingLock_symm
#check @conflictOrder
#check @conflictOrder_sharesConflictingLock
#check @conflictOrder_implies_conflictPrecedes

/-! ## SM3.E.4 — Strict 2PL -/
#check @KernelTransitionInstance.followsStrict2PL
#check @scheduleFollowsStrict2PL
#check @KernelTransitionInstance.ofWithLockSet
#check @strictly_2pl_preserved
#check @scheduleFollowsStrict2PL_of_ofWithLockSet
#check @conflictOrder_commit_le

/-! ## SM3.E.5 — Commutativity -/
#check @KernelTransitionInstance.actionsCommute
#check @KernelTransitionInstance.actionsCommute_symm
#check @KernelTransitionInstance.actionsCommute_of_action_id_left
#check @KernelTransitionInstance.actionsCommute_of_action_id_right
#check @applySequential_swap_adjacent
#check @CommutingReorder
#check @CommutingReorder.cons
#check @applySequential_eq_of_commutingReorder
#check @readOnlyInstance
#check @readOnlyInstance_actionsCommute
#check @readOnlyInstance_actionsCommute_readOnly
#check @setObjStoreLock_setScheduler_commute
#check @disjointField_actionsCommute
#check @objStoreEquiv
#check @objStoreEquiv_refl
#check @objStoreEquiv_symm
#check @objStoreEquiv_trans
#check @updateObjectAt_preserves_invExt
#check @updateObjectAt_get?
#check @updateObjectAt_objStoreEquiv_comm

/-! ## SM3.E.3 — Conflict-graph acyclicity -/
#check @conflictPrecedes
#check @conflictPrecedes_irreflexive
#check @conflictPrecedes_asymm
#check @ConflictReaches
#check @conflictReaches_commitTime_lt
#check @ConflictAcyclic
#check @conflictGraph_acyclic
#check @conflictPrecedes_total_of_distinct_commit
#check @conflictPrecedes_strict_total_of_distinct_commit

/-! ## SM3.E.2 / SM3.E.3 — Serialization order + main theorem -/
#check @insertByCommitTime
#check @commitSort
#check @commitSort_perm
#check @commitSort_sorted
#check @commitSort_commutingReorder
#check @serialEquivalent
#check @serializability_under_2pl
#check @serializability_under_2pl_exists
#check @outOfOrderCommute_of_forall_action_id
#check @serializability_of_readOnly_schedule
#check @commitSorted_respects_conflictPrecedes
#check @commitSorted_respects_conflictOrder
#check @conflictsCommitOrdered
#check @outOfOrderCommute_of_conflictsCommitOrdered
#check @serializability_under_2pl_of_conflicts_ordered

/-! ## SM3.E.6 — Single-core proof preservation -/
#check @singleCore_invariant_preservation
#check @singleCore_proof_preservation
#check @withLockSet_growing_phase_establishes_lockSetHeld
#check @acquireLockOnObject_preserves_objStoreLock_wf
#check @releaseLockOnObject_preserves_objStoreLock_wf
#check @withLockSet_preserves_objStoreLock_wf
#check @releaseLockOnObject_preserves_invExt
#check @updateObjectLockAt_preserves_objectType_at
#check @acquireLockOnObject_preserves_objectType_at
#check @releaseLockOnObject_preserves_objectType_at
#check @withLockSet_preserves_objectType_at

/-! ## SM3.E.2 — Atomicity bridge (applySequential models the withLockSet execution) -/
#check @ActionPiCongr
#check @applySequential_piCongr
#check @withLockSet_observation_eq_action
#check @applySequentialWithLockSet
#check @applySequentialWithLockSet_observation
-- §9b concrete non-vacuity witness (scheduler observer)
#check @acquireLockOnObject_preserves_scheduler
#check @releaseLockOnObject_preserves_scheduler
#check @schedulerObserver_acquireInsensitive
#check @schedulerObserver_releaseInsensitive
#check @withLockSet_observation_scheduler_witness

/-! ## SM3.E.3/E.5 — Observational serializability (covers write/write) -/
#check @ActionObsCongr
#check @ActionPreservesInvExt
#check @KernelTransitionInstance.wellBehavedObs
#check @KernelTransitionInstance.actionsCommuteObs
#check @updateObjectAt_actionObsCongr
#check @updateObjectAt_actionPreservesInvExt
#check @updateObjectAt_wellBehavedObs
#check @applySequential_preservesInvExt
#check @applySequential_obsCongr
#check @applySequential_swap_front_obs
#check @applySequential_cons_obs
#check @outOfOrderCommuteObs
#check @insertByCommitTime_obs
#check @commitSort_obs
#check @serializability_under_2pl_obs
#check @objStoreWriteInstance
#check @objStoreWriteInstance_wellBehavedObs
#check @objStoreWriteInstance_actionsCommuteObs

/-! ## SM3.E inventory -/
#check @SerializabilityCategory
#check @SerializabilityTheorem
#check @serializabilityTheorems
#check @serializabilityTheorems_count
#check @serializabilityTheorems_partition_sum
#check @serializabilityTheorems_identifiers_nodup

-- ============================================================================
-- §2 — Concrete fixtures + decidable examples
-- ============================================================================

/-- Core 0. -/
def c0 : CoreId := ⟨0, by decide⟩

/-- A `.tcb` lock at ObjId 5 (lower in the LockId order). -/
def tcb5 : LockId := ⟨.tcb, SeLe4n.ObjId.ofNat 5⟩
/-- A `.tcb` lock at ObjId 7 (higher in the LockId order). -/
def tcb7 : LockId := ⟨.tcb, SeLe4n.ObjId.ofNat 7⟩

/-- `{tcb5 : write}`. -/
def lsW5 : LockSet := LockSet.singleton tcb5 .write
/-- `{tcb5 : read}`. -/
def lsR5 : LockSet := LockSet.singleton tcb5 .read
/-- `{tcb7 : write}`. -/
def lsW7 : LockSet := LockSet.singleton tcb7 .write

/-- Build a transition instance with `acquireTime ≡ 0` (so strict 2PL holds for
any non-zero commit time) and an arbitrary action. -/
def mkInst (ls : LockSet) (ct : Nat) (act : SystemState → SystemState) :
    KernelTransitionInstance :=
  { lockSet := ls, core := c0, commitTime := ct, acquireTime := fun _ => 0,
    action := act }

/-- A read-only transition (identity action). -/
def mkRead (ls : LockSet) (ct : Nat) : KernelTransitionInstance :=
  readOnlyInstance ls c0 ct (fun _ => 0)

/-- Write tcb5, committing at time 1. -/
def τW5a : KernelTransitionInstance := mkInst lsW5 1 id
/-- Write tcb5, committing at time 2 (conflicts with `τW5a`, commits later). -/
def τW5b : KernelTransitionInstance := mkInst lsW5 2 id
/-- Write tcb7, committing at time 3 (disjoint from the tcb5 transitions). -/
def τW7 : KernelTransitionInstance := mkInst lsW7 3 id
/-- Read tcb5, committing at time 1. -/
def τR5a : KernelTransitionInstance := mkRead lsR5 1
/-- Read tcb5, committing at time 2. -/
def τR5b : KernelTransitionInstance := mkRead lsR5 2

/-- A deliberately commit-unordered read-only schedule: commit times 3, 1, 2. -/
def schedUnsorted : List KernelTransitionInstance :=
  [mkRead lsR5 3, mkRead lsR5 1, mkRead lsR5 2]

/-! ## SM3.E.1 — Conflict relation (decidable) -/

-- Two writes to the same tcb conflict.
example : ktiConflictsB τW5a τW5b = true := by decide
-- Writes to different tcbs do not conflict (disjoint footprints).
example : ktiConflictsB τW5a τW7 = false := by decide
-- Two reads of the same tcb do NOT conflict (read/read).
example : ktiConflictsB τR5a τR5b = false := by decide
-- A read and a write of the same tcb conflict.
example : ktiConflictsB τR5a τW5a = true := by decide
-- Conflict is symmetric (Bool form).
example : ktiConflictsB τR5a τW5a = ktiConflictsB τW5a τR5a := by decide

/-! ## SM3.E.3 — Commit-oriented conflict edge (decidable) -/

-- τW5a (commit 1) conflict-precedes τW5b (commit 2): conflict + 1 < 2.
example : conflictPrecedes τW5a τW5b := by decide
-- Irreflexive: no transition conflict-precedes itself.
example : ¬ conflictPrecedes τW5a τW5a := by decide
-- Asymmetric: the later-committing one does not precede the earlier.
example : ¬ conflictPrecedes τW5b τW5a := by decide
-- Disjoint transitions induce no conflict edge.
example : ¬ conflictPrecedes τW5a τW7 := by decide
-- Two reads induce no conflict edge.
example : ¬ conflictPrecedes τR5a τR5b := by decide

/-! ## SM3.E.4 — Strict 2PL (decidable) -/

example : τW5a.followsStrict2PL := by decide
example : τR5a.followsStrict2PL := by decide
example : (KernelTransitionInstance.ofWithLockSet lsW5 c0 0 5 id).followsStrict2PL := by decide

-- ============================================================================
-- §3 — Theorem applications (compile-time inhabitation witnesses)
-- ============================================================================

/-- Every transition in the read-only schedule has the identity action. -/
theorem schedUnsorted_allRead : ∀ τ ∈ schedUnsorted, τ.action = id := by
  intro τ hτ
  simp only [schedUnsorted, List.mem_cons, List.not_mem_nil, or_false] at hτ
  rcases hτ with rfl | rfl | rfl <;> rfl

/-! ## SM3.E.3 — `serializability_under_2pl` is inhabited on a read-only schedule -/

example (s : SystemState) :
    (commitSort schedUnsorted).Perm schedUnsorted ∧
    (commitSort schedUnsorted).Pairwise (fun a b => a.commitTime ≤ b.commitTime) ∧
    serialEquivalent schedUnsorted (commitSort schedUnsorted) s :=
  serializability_under_2pl schedUnsorted s
    (outOfOrderCommute_of_forall_action_id schedUnsorted schedUnsorted_allRead)

/-! ## SM3.E.3 — unconditional serializability of the read-only schedule -/

example (s : SystemState) :
    serialEquivalent schedUnsorted (commitSort schedUnsorted) s :=
  serializability_of_readOnly_schedule schedUnsorted schedUnsorted_allRead s

/-! ## SM3.E.3 — the conflict graph is acyclic (no parameters) -/

example : ConflictAcyclic conflictPrecedes := conflictGraph_acyclic

/-! ## SM3.E.5 — reads commute; disjoint-subsystem writes commute -/

example : τR5a.actionsCommute τW5b :=
  readOnlyInstance_actionsCommute lsR5 c0 1 (fun _ => 0) τW5b

example (s : SystemState) (f₁ f₂ : KernelObject → KernelObject) (hExt : s.objects.invExt) :
    objStoreEquiv (updateObjectAt (updateObjectAt s tcb5.objId f₁) tcb7.objId f₂)
                  (updateObjectAt (updateObjectAt s tcb7.objId f₂) tcb5.objId f₁) :=
  updateObjectAt_objStoreEquiv_comm s tcb5.objId tcb7.objId f₁ f₂ hExt (by decide)

/-! ## SM3.E.6 — single-core proof preservation on a REAL (non-trivial) invariant -/

-- NON-VACUOUS witness: the genuine `objStoreLock.wf` invariant (a real SM2.C/SM3.C
-- invariant — NOT the trivial `True`) transfers through the 2PL `withLockSet`
-- wrapper, given the action preserves it.  This proves the SM3.E.6 lever is a
-- usable tool, not a vacuous false-anchor.
example (core : CoreId) (op : SystemState → SystemState × Unit) (s : SystemState)
    (hwf : s.objStoreLock.wf)
    (hAction : ∀ s', s'.objStoreLock.wf → (op s').1.objStoreLock.wf) :
    (withLockSet lsW5 core op s).1.objStoreLock.wf :=
  withLockSet_preserves_objStoreLock_wf lsW5 core op s hwf hAction

-- And the underlying lock-insensitivity is genuinely discharged (not assumed):
-- acquiring/releasing any lock preserves objStoreLock.wf.
example (s : SystemState) (core : CoreId) (l : LockId) (m : AccessMode)
    (h : s.objStoreLock.wf) : (acquireLockOnObject s core l m).objStoreLock.wf :=
  acquireLockOnObject_preserves_objStoreLock_wf s core l m h

-- The trivial `True` invariant remains inhabited too (the metatheorem is total).
example (core : CoreId) (op : SystemState → SystemState × Unit) (s : SystemState) :
    (fun _ => True) (withLockSet lsW5 core op s).1 :=
  singleCore_proof_preservation lsW5 core op s (fun _ => True) (fun _ => True)
    trivial (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ _ => trivial)

/-! ## SM3.E.3 — conflict-graph orientation completeness (uses the conflict relation) -/

-- Under distinct commit times, a conflicting pair is comparable (one precedes).
example (τ₁ τ₂ : KernelTransitionInstance)
    (hc : ktiSharesConflictingLock τ₁ τ₂) (hne : τ₁.commitTime ≠ τ₂.commitTime) :
    conflictPrecedes τ₁ τ₂ ∨ conflictPrecedes τ₂ τ₁ :=
  conflictPrecedes_total_of_distinct_commit τ₁ τ₂ hc hne

-- The plan's SM3.E.1 `conflictOrder` is connected to the serialization order:
-- under strict 2PL (+distinct commit times) it IS a `conflictPrecedes` edge, so
-- the commit-sort serialization respects it (`commitSorted_respects_conflictOrder`).
example (τ₁ τ₂ : KernelTransitionInstance) (h2pl : τ₂.followsStrict2PL)
    (h : conflictOrder τ₁ τ₂) (hne : τ₁.commitTime ≠ τ₂.commitTime) :
    conflictPrecedes τ₁ τ₂ :=
  conflictOrder_implies_conflictPrecedes τ₁ τ₂ h2pl h hne

/-! ## SM3.E.3 — grounded serializability (outOfOrderCommute is a 2PL consequence) -/

-- If conflicts are commit-ordered (strict-2PL lock exclusion) and non-conflicting
-- transitions commute, the execution is serial-equivalent to its commit sort.
example (interleaved : List KernelTransitionInstance) (s : SystemState)
    (hnc : ∀ τ₁ τ₂ : KernelTransitionInstance,
      ¬ ktiSharesConflictingLock τ₁ τ₂ → τ₁.actionsCommute τ₂)
    (ho : conflictsCommitOrdered interleaved) :
    serialEquivalent interleaved (commitSort interleaved) s :=
  (serializability_under_2pl_of_conflicts_ordered interleaved s hnc ho).2.2

/-! ## SM3.E.2 — atomicity bridge: applySequential models the withLockSet execution -/

-- A withLockSet-wrapped schedule, observed lock-insensitively (every action a
-- π-congruence), equals the bare applySequential model — the formal grounding
-- that `applySequential` faithfully represents the real `withLockSet` execution.
example (β : Type) (π : SystemState → β)
    (hAcq : ∀ c : CoreId, AcquireInsensitive c π)
    (hRel : ∀ c : CoreId, ReleaseInsensitive c π)
    (sched : List KernelTransitionInstance)
    (hCongr : ∀ τ ∈ sched, ActionPiCongr π τ.action) (s : SystemState) :
    π (applySequentialWithLockSet sched s) = π (applySequential sched s) :=
  applySequentialWithLockSet_observation π hAcq hRel sched hCongr s

-- §9b NON-VACUITY: the scheduler projection is a CONCRETE non-trivial observer
-- that discharges both insensitivity hypotheses — so the bridge above is not
-- vacuous.  A scheduler write wrapped in the full withLockSet 2PL machinery has
-- its effect (= sch) correctly observed, the lock folds invisible.
example (S : LockSet) (core : CoreId) (sch : SchedulerState) (s : SystemState) :
    (withLockSet S core (fun st => (setSchedulerAction sch st, ())) s).1.scheduler = sch :=
  withLockSet_observation_scheduler_witness S core sch s

example (core : CoreId) : AcquireInsensitive core (fun s => s.scheduler) :=
  schedulerObserver_acquireInsensitive core

/-! ## SM3.E.3/E.5 — OBSERVATIONAL serializability on a real write/write schedule -/

-- Two object-store WRITES to DIFFERENT objects (tcb5, tcb7), out of commit order
-- (commit 2 then 1), are observationally serial-equivalent to their commit sort.
-- This is the realistic write-heavy case the structural theorem cannot cover.
private def wA : KernelTransitionInstance :=
  objStoreWriteInstance lsW5 c0 2 (fun _ => 0) tcb5.objId id
private def wB : KernelTransitionInstance :=
  objStoreWriteInstance lsW7 c0 1 (fun _ => 0) tcb7.objId id

theorem writeWriteSched_wellBehavedObs :
    ∀ τ ∈ [wA, wB], KernelTransitionInstance.wellBehavedObs τ := by
  intro τ hτ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
  rcases hτ with rfl | rfl <;>
    exact objStoreWriteInstance_wellBehavedObs _ _ _ _ _ _

theorem writeWriteSched_outOfOrderCommuteObs : outOfOrderCommuteObs [wA, wB] := by
  rw [outOfOrderCommuteObs_cons, outOfOrderCommuteObs_cons]
  refine ⟨fun x hx _ => ?_, fun x hx _ => ?_, trivial⟩
  · -- x ∈ [wB]: wA commutes-obs with wB (writes to distinct objects tcb5 ≠ tcb7)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact objStoreWriteInstance_actionsCommuteObs lsW5 lsW7 c0 c0 2 1 _ _
      tcb5.objId tcb7.objId id id (by decide)
  · exact absurd hx List.not_mem_nil

-- The headline observational serializability on the concrete write/write schedule.
example (s : SystemState) (hExt : s.objects.invExt) :
    objStoreEquiv (applySequential [wA, wB] s) (applySequential (commitSort [wA, wB]) s) :=
  (serializability_under_2pl_obs [wA, wB] s hExt
    writeWriteSched_wellBehavedObs writeWriteSched_outOfOrderCommuteObs).2.2

/-! ## SM3.E.6 — second real-invariant witness: the kind-discipline (objectType) invariant -/

-- The kind-discipline invariant (every object's objectType tag preserved relative
-- to s₀) survives the withLockSet wrapper when the action preserves it — a real,
-- invExt-dependent invariant class (NOT the trivial True).
example (core : CoreId) (op : SystemState → SystemState × Unit) (s s₀ : SystemState)
    (hInv : s.objects.invExt ∧
      ∀ k, Option.map KernelObject.objectType (s.objects.get? k)
        = Option.map KernelObject.objectType (s₀.objects.get? k))
    (hAction : ∀ s',
      (s'.objects.invExt ∧ ∀ k, Option.map KernelObject.objectType (s'.objects.get? k)
        = Option.map KernelObject.objectType (s₀.objects.get? k)) →
      ((op s').1.objects.invExt ∧ ∀ k, Option.map KernelObject.objectType ((op s').1.objects.get? k)
        = Option.map KernelObject.objectType (s₀.objects.get? k))) :
    (withLockSet lsW5 core op s).1.objects.invExt ∧
    ∀ k, Option.map KernelObject.objectType ((withLockSet lsW5 core op s).1.objects.get? k)
      = Option.map KernelObject.objectType (s₀.objects.get? k) :=
  withLockSet_preserves_objectType_at lsW5 core op s s₀ hInv hAction

-- ============================================================================
-- §4 — Runtime assertions
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS  {name}"
  else
    IO.eprintln s!"  FAIL  {name}"
    IO.Process.exit 1

private def runConflictChecks : IO Unit := do
  IO.println "--- §1 SM3.E.1 — conflict relation ---"
  assertBool "write/write same tcb conflicts" (ktiConflictsB τW5a τW5b)
  assertBool "write/write different tcb does NOT conflict" (! ktiConflictsB τW5a τW7)
  assertBool "read/read same tcb does NOT conflict" (! ktiConflictsB τR5a τR5b)
  assertBool "read/write same tcb conflicts" (ktiConflictsB τR5a τW5a)
  assertBool "conflict is symmetric"
    (ktiConflictsB τR5a τW5a == ktiConflictsB τW5a τR5a)

private def runConflictPrecedesChecks : IO Unit := do
  IO.println "--- §2 SM3.E.3 — commit-oriented conflict edge ---"
  assertBool "τW5a (c=1) conflict-precedes τW5b (c=2)" (decide (conflictPrecedes τW5a τW5b))
  assertBool "irreflexive: ¬ conflictPrecedes τW5a τW5a"
    (decide (¬ conflictPrecedes τW5a τW5a))
  assertBool "asymmetric: ¬ conflictPrecedes τW5b τW5a"
    (decide (¬ conflictPrecedes τW5b τW5a))
  assertBool "disjoint: ¬ conflictPrecedes τW5a τW7"
    (decide (¬ conflictPrecedes τW5a τW7))

private def runStrict2PLChecks : IO Unit := do
  IO.println "--- §3 SM3.E.4 — strict 2PL ---"
  assertBool "τW5a follows strict 2PL" (decide τW5a.followsStrict2PL)
  assertBool "ofWithLockSet (acquire 0 ≤ commit 5) follows strict 2PL"
    (decide (KernelTransitionInstance.ofWithLockSet lsW5 c0 0 5 id).followsStrict2PL)

private def runGroundingChecks : IO Unit := do
  IO.println "--- §3b SM3.E.3 — strict-2PL grounding (conflictsCommitOrdered) ---"
  -- A read-only schedule has no conflicts ⟹ conflictsCommitOrdered holds (vacuous).
  assertBool "read-only schedule is conflictsCommitOrdered"
    (decide (conflictsCommitOrdered schedUnsorted))
  -- Conflicting writes IN commit order [τW5a(c=1), τW5b(c=2)] ⟹ conflictsCommitOrdered.
  assertBool "conflicting writes in commit order ARE conflictsCommitOrdered"
    (decide (conflictsCommitOrdered [τW5a, τW5b]))
  -- Conflicting writes OUT of commit order [τW5b(c=2), τW5a(c=1)] ⟹ NOT (the
  -- lock-exclusion property the predicate captures — strict 2PL forbids this).
  assertBool "conflicting writes OUT of commit order are NOT conflictsCommitOrdered"
    (decide (¬ conflictsCommitOrdered [τW5b, τW5a]))

private def runCommitSortChecks : IO Unit := do
  IO.println "--- §4 SM3.E.3 — commit-sort serialization order ---"
  -- commitSort reorders the commit-unordered schedule into ascending commit time.
  assertBool "commitSort orders [3,1,2] into [1,2,3]"
    (decide ((commitSort schedUnsorted).map (·.commitTime) = [1, 2, 3]))
  -- commitSort preserves length (no transition lost).
  assertBool "commitSort preserves length"
    (decide ((commitSort schedUnsorted).length = schedUnsorted.length))
  -- An already-sorted singleton/empty schedule is fixed.
  assertBool "commitSort [] = []" (decide ((commitSort ([] : List KernelTransitionInstance)).length = 0))

private def runInventoryChecks : IO Unit := do
  IO.println "--- §5 SM3.E — inventory counts ---"
  assertBool "serializabilityTheorems.length = 111"
    (decide (serializabilityTheorems.length = 111))
  assertBool "model count = 5"
    (decide ((serializabilityTheorems.filter (fun t => t.category == .model)).length = 5))
  assertBool "conflict count = 7"
    (decide ((serializabilityTheorems.filter (fun t => t.category == .conflict)).length = 7))
  assertBool "strict2pl count = 6"
    (decide ((serializabilityTheorems.filter (fun t => t.category == .strict2pl)).length = 6))
  assertBool "commutativity count = 23"
    (decide ((serializabilityTheorems.filter (fun t => t.category == .commutativity)).length = 23))
  assertBool "acyclicity count = 9"
    (decide ((serializabilityTheorems.filter (fun t => t.category == .acyclicity)).length = 9))
  assertBool "serializability count = 22"
    (decide ((serializabilityTheorems.filter (fun t => t.category == .serializability)).length = 22))
  assertBool "preservation count = 11"
    (decide ((serializabilityTheorems.filter (fun t => t.category == .preservation)).length = 11))
  assertBool "atomicityBridge count = 10"
    (decide ((serializabilityTheorems.filter (fun t => t.category == .atomicityBridge)).length = 10))
  assertBool "observational count = 18"
    (decide ((serializabilityTheorems.filter (fun t => t.category == .observational)).length = 18))

def runSerializabilityChecks : IO Unit := do
  IO.println "WS-SM SM3.E — serializability regression suite"
  IO.println "==============================================="
  runConflictChecks
  runConflictPrecedesChecks
  runStrict2PLChecks
  runGroundingChecks
  runCommitSortChecks
  runInventoryChecks
  IO.println "==============================================="
  IO.println "All SM3.E serializability checks PASS."

end SeLe4n.Testing.Serializability

def main : IO Unit :=
  SeLe4n.Testing.Serializability.runSerializabilityChecks
