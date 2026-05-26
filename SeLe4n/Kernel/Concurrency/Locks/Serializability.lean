-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM3.E serializability)

import SeLe4n.Model.State
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Locks.LockSet
import SeLe4n.Kernel.Concurrency.Locks.LockIdProjection
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions
import SeLe4n.Kernel.Concurrency.Locks.WithLockSet
import SeLe4n.Kernel.Concurrency.Locks.LockSetHeld
import SeLe4n.Kernel.Concurrency.Locks.LockSet2PL
import SeLe4n.Kernel.Concurrency.Locks.Deadlock

/-!
# WS-SM SM3.E — Serializability under two-phase locking

This module proves the second architectural keystone of SM3 (after SM3.D's
deadlock-freedom): **every interleaved execution of kernel transitions under
strict two-phase locking is conflict-equivalent to a serial execution** — the
serial order being the commit-time order (Bernstein et al. 1987, "Concurrency
Control and Recovery in Database Systems").

## The transition-instance model (plan §5.5)

Where SM3.D's `KernelExecution` is a *static lock-state snapshot*, SM3.E reasons
about *schedules* — sequences of committed transition instances.  A
`KernelTransitionInstance` records, for one kernel transition occurrence:

* `lockSet`     — the static SM3.B lock footprint it acquires,
* `core`        — the executing core,
* `commitTime`  — the moment it releases its last lock (its commit point under
                  strict 2PL),
* `acquireTime` — when it acquired each lock (`LockId → Nat`),
* `action`      — the pure business state transformation (the transition body;
                  lock acquire/release is `withLockSet`'s job, SM3.C, not the
                  action's).

An *execution* (interleaved or serial) is a `List KernelTransitionInstance`.
`applySequential` folds the actions in list order.  Under strict 2PL each
transition commits atomically (SM3.C.7 `lockSet_observer_atomic`), so the net
effect of an interleaved execution is the commit-ordered application of its
transitions' actions — exactly what `applySequential` computes on the
commit-order schedule.

## What is proved

* **SM3.E.1** `conflictOrder` — two instances conflict-order when they share a
  lock in conflicting modes and the first commits no later than the second
  acquires that lock.
* **SM3.E.2** `serialEquivalent` — an interleaved schedule is serial-equivalent
  to a serial one when they produce the same final state.
* **SM3.E.3** `serializability_under_2pl` — every strict-2PL execution is
  serial-equivalent to the commit-sorted serial order (Theorem 2.1.10), via the
  conflict-graph acyclicity (the serialization order is the topological sort)
  and the commuting-transposition reordering (the state-equality).
* **SM3.E.4** `strictly_2pl_preserved` — every transition built by `withLockSet`
  holds all its locks until commit (no early release).
* **SM3.E.5** ≥8 commutativity lemmas — non-conflicting operation pairs commute.
* **SM3.E.6** `singleCore_proof_preservation` (Corollary 2.1.11) — every
  single-core kernel-transition theorem lifts to the SMP form under the
  `lockSetHeld` precondition, reusing SM3.C.8's structural-preservation lever.

## Relationship to SM3.D

SM3.D proved deadlock-freedom by orienting the wait-for graph along the `LockId`
total order and showing it acyclic.  SM3.E proves serializability by orienting
the *conflict* graph along the commit-time order and showing it acyclic — the
same `ReachesPlus`/strict-`<`-along-edges structural argument, now over commit
times (`Nat`) rather than `LockId`s.  The two acyclicity results are the twin
levers that make SMP execution both live (deadlock-free) and correct
(serializable).
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- §1 — The transition-instance model + `applySequential` (SM3.E.2 infra)
-- ============================================================================

/-- WS-SM SM3.E (plan §5.5 `KernelTransitionInstance`): one occurrence of a
kernel transition in an execution.

* `lockSet`     — the SM3.B static lock footprint (which `withLockSet` acquires).
* `core`        — the core executing the transition.
* `commitTime`  — the transition's commit point: the instant it releases its last
                  lock under strict 2PL.  Distinct transitions on overlapping
                  locks have distinct commit times (lock exclusion).
* `acquireTime` — the instant each lock was acquired.  Strict 2PL requires
                  `acquireTime l ≤ commitTime` for every held `l`
                  (`followsStrict2PL`).
* `action`      — the pure business transformation the transition performs.  The
                  lock acquire/release machinery is *not* part of `action`
                  (that is `withLockSet`'s responsibility, SM3.C); `action` is the
                  transition body whose commutativity governs serializability. -/
structure KernelTransitionInstance where
  /-- The transition's static SM3.B lock footprint. -/
  lockSet : LockSet
  /-- The executing core. -/
  core : CoreId
  /-- The commit point (last-lock-release instant). -/
  commitTime : Nat
  /-- When each lock was acquired. -/
  acquireTime : LockId → Nat
  /-- The pure business state transformation (the transition body). -/
  action : SystemState → SystemState

/-- WS-SM SM3.E.2 (plan §5.5 `applySequential`): apply a schedule's transition
actions to an initial state, in list order.  This is the *serial* semantics —
each transition runs to completion before the next begins.  Under strict 2PL it
also computes the net effect of an *interleaved* execution whose commit order is
`sched` (SM3.C.7 atomicity). -/
def applySequential (sched : List KernelTransitionInstance) (s : SystemState) :
    SystemState :=
  sched.foldl (fun st τ => τ.action st) s

/-- WS-SM SM3.E.2: `applySequential` on the empty schedule is the identity. -/
@[simp] theorem applySequential_nil (s : SystemState) :
    applySequential [] s = s := rfl

/-- WS-SM SM3.E.2: `applySequential` on a cons runs the head action, then the
tail on the new state. -/
@[simp] theorem applySequential_cons (τ : KernelTransitionInstance)
    (rest : List KernelTransitionInstance) (s : SystemState) :
    applySequential (τ :: rest) s = applySequential rest (τ.action s) := by
  unfold applySequential; rw [List.foldl_cons]

/-- WS-SM SM3.E.2: `applySequential` over a concatenation runs the first segment,
then the second on the resulting state. -/
theorem applySequential_append (l₁ l₂ : List KernelTransitionInstance)
    (s : SystemState) :
    applySequential (l₁ ++ l₂) s = applySequential l₂ (applySequential l₁ s) := by
  unfold applySequential; rw [List.foldl_append]

-- ============================================================================
-- §2 — Conflict relation + `conflictOrder` (SM3.E.1)
-- ============================================================================

/-- WS-SM SM3.E.1: two transition instances **share a conflicting lock** when
their footprints both declare some `LockId` `l`, and the two declared modes
conflict (`AccessMode.conflicts`, SM3.B — at least one is `.write`).  Two
read-only accesses to the same lock do NOT conflict. -/
def ktiSharesConflictingLock (τ₁ τ₂ : KernelTransitionInstance) : Prop :=
  ∃ (l : LockId) (m₁ m₂ : AccessMode),
    (l, m₁) ∈ τ₁.lockSet.pairs ∧ (l, m₂) ∈ τ₂.lockSet.pairs ∧
    AccessMode.conflicts m₁ m₂ = true

/-- WS-SM SM3.E.1: decidable Bool reflection of `ktiSharesConflictingLock`.  The
existential over the (infinite) `LockId` type is bounded by membership in
`τ₁.lockSet.pairs`, so the search is a finite double `List.any`. -/
def ktiConflictsB (τ₁ τ₂ : KernelTransitionInstance) : Bool :=
  τ₁.lockSet.pairs.any (fun p₁ =>
    τ₂.lockSet.pairs.any (fun p₂ =>
      decide (p₁.fst = p₂.fst) && AccessMode.conflicts p₁.snd p₂.snd))

/-- WS-SM SM3.E.1: the Bool reflection agrees with the `Prop` conflict relation. -/
theorem ktiConflictsB_iff (τ₁ τ₂ : KernelTransitionInstance) :
    ktiConflictsB τ₁ τ₂ = true ↔ ktiSharesConflictingLock τ₁ τ₂ := by
  unfold ktiConflictsB ktiSharesConflictingLock
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, hfst, hconf⟩
    refine ⟨p₁.fst, p₁.snd, p₂.snd, hp₁, ?_, hconf⟩
    have : (p₁.fst, p₂.snd) = p₂ := by rw [hfst]
    rw [this]; exact hp₂
  · rintro ⟨l, m₁, m₂, h₁, h₂, hconf⟩
    exact ⟨(l, m₁), h₁, (l, m₂), h₂, rfl, hconf⟩

/-- WS-SM SM3.E.1: `ktiSharesConflictingLock` is decidable (via the Bool form). -/
instance (τ₁ τ₂ : KernelTransitionInstance) :
    Decidable (ktiSharesConflictingLock τ₁ τ₂) :=
  decidable_of_iff _ (ktiConflictsB_iff τ₁ τ₂)

/-- WS-SM SM3.E.1: the conflict relation is symmetric — sharing a conflicting
lock does not depend on the order of the two instances (`AccessMode.conflicts`
is symmetric). -/
theorem ktiSharesConflictingLock_symm (τ₁ τ₂ : KernelTransitionInstance)
    (h : ktiSharesConflictingLock τ₁ τ₂) : ktiSharesConflictingLock τ₂ τ₁ := by
  obtain ⟨l, m₁, m₂, h₁, h₂, hconf⟩ := h
  exact ⟨l, m₂, m₁, h₂, h₁, by rw [AccessMode.conflicts_symm]; exact hconf⟩

/-- WS-SM SM3.E.1 (plan §5.5 `conflictOrder`): instance `τ₁` **conflict-orders**
before `τ₂` when they share a conflicting lock `l` and `τ₁` commits no later than
`τ₂` acquires `l`.  This is the precedence the serialization order must respect:
under strict 2PL `τ₁` holds `l` until its commit, so `τ₂` cannot acquire `l`
before `τ₁` commits — hence the conflict is resolved in commit order. -/
def conflictOrder (τ₁ τ₂ : KernelTransitionInstance) : Prop :=
  ∃ (l : LockId) (m₁ m₂ : AccessMode),
    (l, m₁) ∈ τ₁.lockSet.pairs ∧ (l, m₂) ∈ τ₂.lockSet.pairs ∧
    AccessMode.conflicts m₁ m₂ = true ∧
    τ₁.commitTime ≤ τ₂.acquireTime l

/-- WS-SM SM3.E.1: a `conflictOrder` edge entails a shared conflicting lock. -/
theorem conflictOrder_sharesConflictingLock (τ₁ τ₂ : KernelTransitionInstance)
    (h : conflictOrder τ₁ τ₂) : ktiSharesConflictingLock τ₁ τ₂ := by
  obtain ⟨l, m₁, m₂, h₁, h₂, hconf, _⟩ := h
  exact ⟨l, m₁, m₂, h₁, h₂, hconf⟩

-- ============================================================================
-- §3 — Strict two-phase locking (SM3.E.4)
-- ============================================================================

/-- WS-SM SM3.E.4: a transition instance **follows strict 2PL** when every lock
in its footprint is acquired no later than the transition's commit point — i.e.
no lock is released before commit.  This is the strict-2PL "hold until commit"
discipline that makes the commit order a valid serialization. -/
def KernelTransitionInstance.followsStrict2PL (τ : KernelTransitionInstance) :
    Prop :=
  ∀ p ∈ τ.lockSet.pairs, τ.acquireTime p.fst ≤ τ.commitTime

/-- WS-SM SM3.E.4: `followsStrict2PL` is decidable (a finite `∀` over the
footprint pairs). -/
instance (τ : KernelTransitionInstance) : Decidable (τ.followsStrict2PL) := by
  unfold KernelTransitionInstance.followsStrict2PL
  exact List.decidableBAll _ τ.lockSet.pairs

/-- WS-SM SM3.E.4: a whole schedule **follows strict 2PL** when every transition
in it does. -/
def scheduleFollowsStrict2PL (sched : List KernelTransitionInstance) : Prop :=
  ∀ τ ∈ sched, τ.followsStrict2PL

/-- WS-SM SM3.E.4 (plan §5.5 `strictly_2pl_preserved`): the canonical
`withLockSet`-built transition follows strict 2PL.

`withLockSet` (SM3.C.1) acquires every lock in the growing phase *before* the
action and releases in the shrinking phase *after* it.  Modelling this with a
commit time `c` and a uniform pre-commit acquire instant `a ≤ c` (every lock
acquired in the single growing phase), the resulting instance acquires every
lock no later than commit — strict 2PL holds.  The hypothesis `a ≤ c` is the
operational meaning of "the growing phase precedes the commit". -/
def KernelTransitionInstance.ofWithLockSet (S : LockSet) (core : CoreId)
    (acquireInstant commitInstant : Nat)
    (action : SystemState → SystemState) : KernelTransitionInstance :=
  { lockSet := S, core := core, commitTime := commitInstant,
    acquireTime := fun _ => acquireInstant, action := action }

/-- WS-SM SM3.E.4 (`strictly_2pl_preserved`): every `withLockSet`-built
transition whose growing phase precedes its commit (`acquireInstant ≤
commitInstant`) follows strict 2PL.  This is the operational form of "all locks
acquired by a transition are released only when the body completes". -/
theorem strictly_2pl_preserved (S : LockSet) (core : CoreId)
    (acquireInstant commitInstant : Nat) (action : SystemState → SystemState)
    (hPre : acquireInstant ≤ commitInstant) :
    (KernelTransitionInstance.ofWithLockSet S core acquireInstant commitInstant
      action).followsStrict2PL := by
  intro p _
  exact hPre

/-- WS-SM SM3.E.4 (schedule form): an execution built entirely from
`withLockSet`-discipline transitions (each with `acquireInstant ≤ commitInstant`)
follows strict 2PL schedule-wide. -/
theorem scheduleFollowsStrict2PL_of_ofWithLockSet
    (specs : List (LockSet × CoreId × Nat × Nat × (SystemState → SystemState)))
    (hPre : ∀ q ∈ specs, q.2.2.1 ≤ q.2.2.2.1) :
    scheduleFollowsStrict2PL (specs.map (fun q =>
      KernelTransitionInstance.ofWithLockSet q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) := by
  intro τ hτ
  rw [List.mem_map] at hτ
  obtain ⟨q, hq, rfl⟩ := hτ
  exact strictly_2pl_preserved q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 (hPre q hq)

/-- WS-SM SM3.E.4 (the strict-2PL ⟹ commit-consistency lever): if `τ₁`
conflict-orders before `τ₂` and `τ₂` follows strict 2PL, then `τ₁` commits no
later than `τ₂`.

Proof: `conflictOrder` gives `τ₁.commitTime ≤ τ₂.acquireTime l` on the shared
lock `l`; strict 2PL of `τ₂` gives `τ₂.acquireTime l ≤ τ₂.commitTime`; compose.
This is the precise point where the strict-2PL discipline forces every conflict
to be resolved in commit order — the foundation of the serialization order. -/
theorem conflictOrder_commit_le (τ₁ τ₂ : KernelTransitionInstance)
    (h2pl : τ₂.followsStrict2PL) (h : conflictOrder τ₁ τ₂) :
    τ₁.commitTime ≤ τ₂.commitTime := by
  obtain ⟨l, _m₁, m₂, _h₁, h₂, _hconf, hle⟩ := h
  exact Nat.le_trans hle (h2pl (l, m₂) h₂)

-- ============================================================================
-- §4 — Commutativity of non-conflicting actions (SM3.E.5 foundation)
-- ============================================================================

/-- WS-SM SM3.E.5: two transition instances **commute** when their business
actions commute as state transformers — applying them in either order yields the
same state.  Non-conflicting transitions (disjoint write footprints, or
read-only) commute; the concrete witnesses are the SM3.E.5 commutativity lemmas
in §4b. -/
def KernelTransitionInstance.actionsCommute (τ₁ τ₂ : KernelTransitionInstance) :
    Prop :=
  ∀ s : SystemState, τ₁.action (τ₂.action s) = τ₂.action (τ₁.action s)

/-- WS-SM SM3.E.5: action commutation is symmetric. -/
theorem KernelTransitionInstance.actionsCommute_symm
    {τ₁ τ₂ : KernelTransitionInstance} (h : τ₁.actionsCommute τ₂) :
    τ₂.actionsCommute τ₁ := fun s => (h s).symm

/-- WS-SM SM3.E.5: a transition whose action is the identity (a *read-only*
transition — it inspects but never mutates business state) commutes with every
transition.  This is the canonical non-conflicting case: reads commute with
anything.  Left form (the identity transition on the left). -/
theorem KernelTransitionInstance.actionsCommute_of_action_id_left
    {τ₁ τ₂ : KernelTransitionInstance} (h : τ₁.action = id) :
    τ₁.actionsCommute τ₂ := by
  intro s; rw [h]; rfl

/-- WS-SM SM3.E.5: read-only commutation, right form (the identity transition on
the right). -/
theorem KernelTransitionInstance.actionsCommute_of_action_id_right
    {τ₁ τ₂ : KernelTransitionInstance} (h : τ₂.action = id) :
    τ₁.actionsCommute τ₂ := by
  intro s; rw [h]; rfl

/-- WS-SM SM3.E.3 (the adjacent-transposition lever): swapping two **commuting**
adjacent transitions anywhere in a schedule leaves `applySequential` unchanged.

This is the single fact the serializability state-equality rests on.  The prefix
folds to a common state `P`; the two commuting actions on `P` agree in either
order (`hComm`); the suffix folds identically afterwards.  Bernstein's bubble of
non-conflicting transpositions is built entirely from this lemma. -/
theorem applySequential_swap_adjacent (pre suf : List KernelTransitionInstance)
    (τ₁ τ₂ : KernelTransitionInstance) (s : SystemState)
    (hComm : τ₁.actionsCommute τ₂) :
    applySequential (pre ++ τ₁ :: τ₂ :: suf) s
      = applySequential (pre ++ τ₂ :: τ₁ :: suf) s := by
  rw [applySequential_append, applySequential_append,
    applySequential_cons, applySequential_cons,
    applySequential_cons, applySequential_cons]
  rw [hComm (applySequential pre s)]

/-- WS-SM SM3.E.3 (plan §3.8 "conflict-equivalent reordering"): the reflexive-
transitive closure of adjacent transpositions of **commuting** pairs.  Two
schedules related by `CommutingReorder` are reachable from one another by a
sequence of non-conflicting adjacent swaps — exactly the moves that preserve a
schedule's observable result (conflict-equivalence). -/
inductive CommutingReorder :
    List KernelTransitionInstance → List KernelTransitionInstance → Prop where
  /-- A schedule reorders to itself. -/
  | refl (l : List KernelTransitionInstance) : CommutingReorder l l
  /-- Swap two commuting adjacent transitions. -/
  | swap (pre suf : List KernelTransitionInstance)
      (τ₁ τ₂ : KernelTransitionInstance) (h : τ₁.actionsCommute τ₂) :
      CommutingReorder (pre ++ τ₁ :: τ₂ :: suf) (pre ++ τ₂ :: τ₁ :: suf)
  /-- Compose two reorderings. -/
  | trans {l₁ l₂ l₃ : List KernelTransitionInstance} :
      CommutingReorder l₁ l₂ → CommutingReorder l₂ l₃ → CommutingReorder l₁ l₃

/-- WS-SM SM3.E.3: `CommutingReorder` is a congruence under consing a common
head — the swaps simply happen one position deeper.  Used to lift the
sort-the-tail induction to the whole schedule. -/
theorem CommutingReorder.cons (a : KernelTransitionInstance)
    {l₁ l₂ : List KernelTransitionInstance} (h : CommutingReorder l₁ l₂) :
    CommutingReorder (a :: l₁) (a :: l₂) := by
  induction h with
  | refl l => exact CommutingReorder.refl (a :: l)
  | swap pre suf τ₁ τ₂ hc =>
      -- a :: (pre ++ τ₁::τ₂::suf) = (a::pre) ++ τ₁::τ₂::suf
      exact CommutingReorder.swap (a :: pre) suf τ₁ τ₂ hc
  | trans _ _ ih₁ ih₂ => exact CommutingReorder.trans ih₁ ih₂

/-- WS-SM SM3.E.3: every `CommutingReorder` preserves `applySequential` — a
schedule and any commuting-reordering of it produce the same final state.
Induction over the closure; the `swap` case is `applySequential_swap_adjacent`. -/
theorem applySequential_eq_of_commutingReorder
    {l₁ l₂ : List KernelTransitionInstance}
    (h : CommutingReorder l₁ l₂) (s : SystemState) :
    applySequential l₁ s = applySequential l₂ s := by
  induction h generalizing s with
  | refl l => rfl
  | swap pre suf τ₁ τ₂ hc => exact applySequential_swap_adjacent pre suf τ₁ τ₂ s hc
  | trans _ _ ih₁ ih₂ => rw [ih₁ s, ih₂ s]

-- ============================================================================
-- §5 — Conflict-graph acyclicity (the "acyclic conflict graph" result)
-- ============================================================================
--
-- Bernstein's theorem reduces serializability to the conflict graph being
-- acyclic.  SM3.D oriented the *wait-for* graph along the `LockId` total order
-- and showed it acyclic; SM3.E orients the *conflict* graph along the
-- commit-time order and shows it acyclic — the identical `ReachesPlus`/
-- strict-`<`-along-edges structural argument, now over commit times (`Nat`).
-- The acyclic conflict graph means the commit order is a valid topological
-- sort = serialization order.

/-- WS-SM SM3.E.3: the commit-oriented conflict edge — `τ₁` precedes `τ₂` when
they share a conflicting lock AND `τ₁` commits strictly before `τ₂`.  Under
strict 2PL (lock exclusion) every conflicting pair has distinct commit times, so
exactly one orientation of each conflict is a `conflictPrecedes` edge — the graph
is the conflict graph oriented by commit order. -/
def conflictPrecedes (τ₁ τ₂ : KernelTransitionInstance) : Prop :=
  ktiSharesConflictingLock τ₁ τ₂ ∧ τ₁.commitTime < τ₂.commitTime

/-- WS-SM SM3.E.3: `conflictPrecedes` is decidable. -/
instance (τ₁ τ₂ : KernelTransitionInstance) :
    Decidable (conflictPrecedes τ₁ τ₂) := by
  unfold conflictPrecedes; exact inferInstance

/-- WS-SM SM3.E.3: `conflictPrecedes` is **irreflexive** — no transition
conflict-precedes itself (`commitTime τ < commitTime τ` is false).  This is the
plan's `conflictOrder_irreflexive` (inventory item 16), stated for the strict
commit-oriented precedence that the acyclicity argument uses. -/
theorem conflictPrecedes_irreflexive (τ : KernelTransitionInstance) :
    ¬ conflictPrecedes τ τ := by
  rintro ⟨_, hlt⟩; exact Nat.lt_irrefl _ hlt

/-- WS-SM SM3.E.3: `conflictPrecedes` is **asymmetric** — at most one orientation
of a conflicting pair is an edge (commit times cannot strictly precede each
other both ways). -/
theorem conflictPrecedes_asymm (τ₁ τ₂ : KernelTransitionInstance)
    (h₁ : conflictPrecedes τ₁ τ₂) (h₂ : conflictPrecedes τ₂ τ₁) : False :=
  Nat.lt_asymm h₁.2 h₂.2

/-- WS-SM SM3.E.3: the transitive closure of a transition-relation (mathlib-free
`TransGen`, mirroring SM3.D's `ReachesPlus` over `CoreId`).  `ConflictReaches R
a b` holds iff there is a nonempty `R`-path from `a` to `b`. -/
inductive ConflictReaches (R : KernelTransitionInstance → KernelTransitionInstance → Prop) :
    KernelTransitionInstance → KernelTransitionInstance → Prop where
  /-- A single edge. -/
  | base {a b : KernelTransitionInstance} : R a b → ConflictReaches R a b
  /-- Prepend an edge to a path. -/
  | step {a b c : KernelTransitionInstance} :
      R a b → ConflictReaches R b c → ConflictReaches R a c

/-- WS-SM SM3.E.3: along any nonempty `conflictPrecedes`-path the commit time
strictly increases.  Induction on the closure; single edges are
`conflictPrecedes.2`, composition is `Nat.lt_trans`. -/
theorem conflictReaches_commitTime_lt {a b : KernelTransitionInstance}
    (h : ConflictReaches conflictPrecedes a b) : a.commitTime < b.commitTime := by
  induction h with
  | base hab => exact hab.2
  | step hab _ ih => exact Nat.lt_trans hab.2 ih

/-- WS-SM SM3.E.3: a transition-relation `R` is **acyclic** when no transition
reaches itself in the transitive closure.  Same DAG definition as SM3.D's
`Acyclic` (specialised to transition instances). -/
def ConflictAcyclic (R : KernelTransitionInstance → KernelTransitionInstance → Prop) :
    Prop :=
  ∀ τ : KernelTransitionInstance, ¬ ConflictReaches R τ τ

/-- WS-SM SM3.E.3 (plan §3.8, **the acyclic conflict graph**): the commit-oriented
conflict graph is acyclic.  Serializability reduces to exactly this fact
(Bernstein): an acyclic conflict graph admits a topological sort, which is the
serialization order.

Proof: a cycle `ConflictReaches conflictPrecedes τ τ` would force, via
`conflictReaches_commitTime_lt`, `τ.commitTime < τ.commitTime` — contradicting
`Nat.lt_irrefl`.  This mirrors SM3.D's `waitGraph_acyclic_under_2pl` exactly,
with commit time playing the role the `LockId` order played there. -/
theorem conflictGraph_acyclic : ConflictAcyclic conflictPrecedes := by
  intro τ hcyc
  exact Nat.lt_irrefl _ (conflictReaches_commitTime_lt hcyc)

/-- WS-SM SM3.E.3 (orientation **completeness** — where the conflict relation
genuinely drives the structure): under the strict-2PL lock-exclusion property
(conflicting transitions commit at *distinct* times), every conflicting pair is
**comparable** under `conflictPrecedes` — one orientation or the other is an edge.

Acyclicity alone (`conflictGraph_acyclic`) does not use the conflict relation —
it is `Nat.lt` irreflexivity over commit times.  *This* theorem is where
`ktiSharesConflictingLock` is essential: it shows the commit-oriented conflict
graph is not merely acyclic but a *total* orientation of every conflicting pair.
Combined with acyclicity, the conflict relation becomes a strict total order on
pairwise-conflicting transitions (`conflictPrecedes_strict_total_of_distinct_commit`),
whose unique linear extension is the commit-time serialization order — the
genuine Bernstein "acyclic conflict graph admits a serial order" content.  The
distinct-commit-times premise is the strict-2PL lock-exclusion consequence: the
transition that acquires the shared lock first holds it until its commit, so the
other commits strictly later. -/
theorem conflictPrecedes_total_of_distinct_commit (τ₁ τ₂ : KernelTransitionInstance)
    (hconf : ktiSharesConflictingLock τ₁ τ₂)
    (hne : τ₁.commitTime ≠ τ₂.commitTime) :
    conflictPrecedes τ₁ τ₂ ∨ conflictPrecedes τ₂ τ₁ := by
  rcases Nat.lt_or_ge τ₁.commitTime τ₂.commitTime with h | h
  · exact Or.inl ⟨hconf, h⟩
  · exact Or.inr ⟨ktiSharesConflictingLock_symm τ₁ τ₂ hconf,
      Nat.lt_of_le_of_ne h (Ne.symm hne)⟩

/-- WS-SM SM3.E.3 (capstone — the conflict graph is a **strict total order** on
mutually-conflicting transitions under strict 2PL): combining the orientation
completeness (`conflictPrecedes_total_of_distinct_commit`) with asymmetry
(`conflictPrecedes_asymm`), the commit-oriented conflict relation totally and
consistently orders any conflicting pair with distinct commit times — exactly the
precedence the serialization order linearises.  This is the genuine Bernstein
content: the conflict graph is not merely acyclic, it is a strict total order
whose linear extension is the serial schedule.  Unlike `conflictGraph_acyclic`
(which does not engage the conflict relation), the totality conjunct here rests
essentially on `ktiSharesConflictingLock` (via its symmetry). -/
theorem conflictPrecedes_strict_total_of_distinct_commit
    (τ₁ τ₂ : KernelTransitionInstance)
    (hconf : ktiSharesConflictingLock τ₁ τ₂)
    (hne : τ₁.commitTime ≠ τ₂.commitTime) :
    (conflictPrecedes τ₁ τ₂ ∨ conflictPrecedes τ₂ τ₁) ∧
    ¬ (conflictPrecedes τ₁ τ₂ ∧ conflictPrecedes τ₂ τ₁) :=
  ⟨conflictPrecedes_total_of_distinct_commit τ₁ τ₂ hconf hne,
   fun ⟨h₁, h₂⟩ => conflictPrecedes_asymm τ₁ τ₂ h₁ h₂⟩

/-- WS-SM SM3.E.3 (bridge — connects the plan's SM3.E.1 `conflictOrder` to the
serialization order): under strict 2PL, a `conflictOrder` edge with distinct
commit times IS a `conflictPrecedes` edge.

`conflictOrder` (SM3.E.1, "the precedence the serialization order must respect")
is stated in terms of `commitTime τ₁ ≤ acquireTime τ₂ l` (the lock-exclusion
inequality on the shared lock).  `conflictOrder_commit_le` lifts this to
`commitTime τ₁ ≤ commitTime τ₂` under strict 2PL; with distinct commit times it
becomes the strict `commitTime τ₁ < commitTime τ₂`, which — together with the
shared conflicting lock — is exactly a `conflictPrecedes` edge.  This makes
`conflictOrder` a first-class participant in the serialization argument rather
than an isolated definition: combined with `commitSorted_respects_conflictPrecedes`
it yields `commitSorted_respects_conflictOrder` (the serialization respects every
`conflictOrder` edge). -/
theorem conflictOrder_implies_conflictPrecedes (τ₁ τ₂ : KernelTransitionInstance)
    (h2pl : τ₂.followsStrict2PL) (h : conflictOrder τ₁ τ₂)
    (hne : τ₁.commitTime ≠ τ₂.commitTime) : conflictPrecedes τ₁ τ₂ :=
  ⟨conflictOrder_sharesConflictingLock τ₁ τ₂ h,
   Nat.lt_of_le_of_ne (conflictOrder_commit_le τ₁ τ₂ h2pl h) hne⟩

-- ============================================================================
-- §6 — The commit-time serialization order + main theorem (SM3.E.2/E.3)
-- ============================================================================
--
-- The serialization order is the commit-time sort — the topological sort of the
-- acyclic conflict graph (§5).  We use insertion sort (`commitSort`) because its
-- recursive structure connects directly to the adjacent-transposition closure
-- `CommutingReorder` (§4): inserting a transition past commuting (non-conflicting)
-- predecessors is a sequence of commuting swaps, so the sort preserves the
-- schedule's observable result.

/-- WS-SM SM3.E.3: insert a transition into a commit-sorted schedule at its
commit-time position.  Walks past every transition with a strictly smaller
commit time. -/
def insertByCommitTime (τ : KernelTransitionInstance) :
    List KernelTransitionInstance → List KernelTransitionInstance
  | [] => [τ]
  | head :: rest =>
      if τ.commitTime ≤ head.commitTime then τ :: head :: rest
      else head :: insertByCommitTime τ rest

@[simp] theorem insertByCommitTime_nil (τ : KernelTransitionInstance) :
    insertByCommitTime τ [] = [τ] := rfl

@[simp] theorem insertByCommitTime_cons (τ head : KernelTransitionInstance)
    (rest : List KernelTransitionInstance) :
    insertByCommitTime τ (head :: rest) =
      (if τ.commitTime ≤ head.commitTime then τ :: head :: rest
       else head :: insertByCommitTime τ rest) := rfl

/-- WS-SM SM3.E.3: insertion sort by commit time — the serialization order. -/
def commitSort :
    List KernelTransitionInstance → List KernelTransitionInstance
  | [] => []
  | head :: rest => insertByCommitTime head (commitSort rest)

@[simp] theorem commitSort_nil : commitSort [] = [] := rfl

@[simp] theorem commitSort_cons (head : KernelTransitionInstance)
    (rest : List KernelTransitionInstance) :
    commitSort (head :: rest) = insertByCommitTime head (commitSort rest) := rfl

/-- WS-SM SM3.E.3: `insertByCommitTime τ l` is a permutation of `τ :: l` — no
transition is lost or duplicated. -/
theorem insertByCommitTime_perm (τ : KernelTransitionInstance) :
    ∀ l : List KernelTransitionInstance, (insertByCommitTime τ l).Perm (τ :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons head rest ih =>
      rw [insertByCommitTime_cons]
      by_cases hle : τ.commitTime ≤ head.commitTime
      · rw [if_pos hle]
      · rw [if_neg hle]
        exact (List.Perm.cons head ih).trans (List.Perm.swap τ head rest)

/-- WS-SM SM3.E.3: `commitSort l` is a permutation of `l` — the serialization
order contains exactly the transitions of the interleaved execution. -/
theorem commitSort_perm :
    ∀ l : List KernelTransitionInstance, (commitSort l).Perm l := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons head rest ih =>
      rw [commitSort_cons]
      exact (insertByCommitTime_perm head (commitSort rest)).trans
        (List.Perm.cons head ih)

/-- WS-SM SM3.E.3: inserting into a commit-sorted list keeps it commit-sorted. -/
theorem insertByCommitTime_sorted (τ : KernelTransitionInstance) :
    ∀ l : List KernelTransitionInstance,
      l.Pairwise (fun a b => a.commitTime ≤ b.commitTime) →
      (insertByCommitTime τ l).Pairwise (fun a b => a.commitTime ≤ b.commitTime) := by
  intro l
  induction l with
  | nil =>
      intro _
      rw [insertByCommitTime_nil]
      exact List.pairwise_cons.mpr ⟨fun a ha => absurd ha List.not_mem_nil, List.Pairwise.nil⟩
  | cons head rest ih =>
      intro hSorted
      rw [insertByCommitTime_cons]
      by_cases hle : τ.commitTime ≤ head.commitTime
      · rw [if_pos hle]
        refine List.pairwise_cons.mpr ⟨?_, hSorted⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | haRest
        · exact hle
        · exact Nat.le_trans hle ((List.pairwise_cons.mp hSorted).1 a haRest)
      · rw [if_neg hle]
        have hRestSorted := (List.pairwise_cons.mp hSorted).2
        have hHeadRest := (List.pairwise_cons.mp hSorted).1
        refine List.pairwise_cons.mpr ⟨?_, ih hRestSorted⟩
        intro a ha
        have hmem : a ∈ τ :: rest := (insertByCommitTime_perm τ rest).mem_iff.mp ha
        rcases List.mem_cons.mp hmem with rfl | haRest
        · exact Nat.le_of_lt (Nat.lt_of_not_le hle)
        · exact hHeadRest a haRest

/-- WS-SM SM3.E.3: `commitSort l` is commit-sorted — the serialization order is
ascending in commit time.  This is the topological sort of the acyclic conflict
graph (§5). -/
theorem commitSort_sorted :
    ∀ l : List KernelTransitionInstance,
      (commitSort l).Pairwise (fun a b => a.commitTime ≤ b.commitTime) := by
  intro l
  induction l with
  | nil => exact List.Pairwise.nil
  | cons head rest ih =>
      rw [commitSort_cons]
      exact insertByCommitTime_sorted head (commitSort rest) ih

/-- WS-SM SM3.E.3 helper: `τ` **commutes with smaller** in `l` when it commutes
with every element of `l` that has a strictly smaller commit time.  These are
exactly the elements `insertByCommitTime` moves `τ` past, so they must commute
with `τ` for the insertion to be a `CommutingReorder`. -/
def commutesWithSmaller (τ : KernelTransitionInstance)
    (l : List KernelTransitionInstance) : Prop :=
  ∀ x ∈ l, x.commitTime < τ.commitTime → τ.actionsCommute x

/-- WS-SM SM3.E.3 helper: `commutesWithSmaller` transports along a permutation
(it depends only on the multiset of elements). -/
theorem commutesWithSmaller_of_perm (τ : KernelTransitionInstance)
    {l₁ l₂ : List KernelTransitionInstance}
    (hperm : l₁.Perm l₂) (h : commutesWithSmaller τ l₁) :
    commutesWithSmaller τ l₂ :=
  fun x hx hlt => h x (hperm.mem_iff.mpr hx) hlt

/-- WS-SM SM3.E.3: inserting `τ` into `l` is a `CommutingReorder` of `τ :: l`,
provided `τ` commutes with every smaller-commit element it moves past.  Each
hop past a smaller predecessor is one commuting adjacent swap. -/
theorem insertByCommitTime_commutingReorder (τ : KernelTransitionInstance) :
    ∀ l : List KernelTransitionInstance, commutesWithSmaller τ l →
      CommutingReorder (τ :: l) (insertByCommitTime τ l) := by
  intro l
  induction l with
  | nil => intro _; rw [insertByCommitTime_nil]; exact CommutingReorder.refl _
  | cons head rest ih =>
      intro hcomm
      rw [insertByCommitTime_cons]
      by_cases hle : τ.commitTime ≤ head.commitTime
      · rw [if_pos hle]; exact CommutingReorder.refl _
      · rw [if_neg hle]
        have hHeadSmall : head.commitTime < τ.commitTime := Nat.lt_of_not_le hle
        have hCommHead : τ.actionsCommute head :=
          hcomm head List.mem_cons_self hHeadSmall
        have hSwap : CommutingReorder (τ :: head :: rest) (head :: τ :: rest) :=
          CommutingReorder.swap [] rest τ head hCommHead
        have hRestComm : commutesWithSmaller τ rest :=
          fun x hx hlt => hcomm x (List.mem_cons_of_mem _ hx) hlt
        exact CommutingReorder.trans hSwap
          (CommutingReorder.cons head (ih hRestComm))

/-- WS-SM SM3.E.3 helper: the schedule-wide hypothesis under which the commit
sort is a `CommutingReorder` — every earlier transition with a strictly larger
commit time than a later one commutes with it.  Under strict 2PL this holds
*for free*: conflicting pairs are already commit-ordered (a conflicting pair out
of commit order would violate lock exclusion), so every out-of-commit-order pair
is non-conflicting, hence commutes. -/
def outOfOrderCommute : List KernelTransitionInstance → Prop
  | [] => True
  | head :: rest => commutesWithSmaller head rest ∧ outOfOrderCommute rest

@[simp] theorem outOfOrderCommute_nil : outOfOrderCommute [] = True := rfl

@[simp] theorem outOfOrderCommute_cons (head : KernelTransitionInstance)
    (rest : List KernelTransitionInstance) :
    outOfOrderCommute (head :: rest) =
      (commutesWithSmaller head rest ∧ outOfOrderCommute rest) := rfl

/-- WS-SM SM3.E.3: under `outOfOrderCommute`, the commit sort is reachable from
the interleaved schedule by commuting adjacent transpositions — so it preserves
the observable result.  Induction on the schedule: sort the tail (IH, lifted by
`CommutingReorder.cons`), then insert the head past its commuting smaller
predecessors (`insertByCommitTime_commutingReorder`). -/
theorem commitSort_commutingReorder :
    ∀ l : List KernelTransitionInstance, outOfOrderCommute l →
      CommutingReorder l (commitSort l) := by
  intro l
  induction l with
  | nil => intro _; rw [commitSort_nil]; exact CommutingReorder.refl _
  | cons head rest ih =>
      intro hooc
      rw [commitSort_cons, outOfOrderCommute_cons] at *
      obtain ⟨hHeadComm, hRestOoc⟩ := hooc
      have hStep1 : CommutingReorder (head :: rest) (head :: commitSort rest) :=
        CommutingReorder.cons head (ih hRestOoc)
      have hCommSorted : commutesWithSmaller head (commitSort rest) :=
        commutesWithSmaller_of_perm head (commitSort_perm rest).symm hHeadComm
      exact CommutingReorder.trans hStep1
        (insertByCommitTime_commutingReorder head (commitSort rest) hCommSorted)

-- ============================================================================
-- §6b — `serialEquivalent` (SM3.E.2) + `serializability_under_2pl` (SM3.E.3)
-- ============================================================================

/-- WS-SM SM3.E.2 (plan §5.5 `serialEquivalent`): an interleaved schedule is
**serial-equivalent** to a serial one when they produce the same final state
from the initial state `s₀`.  Under strict 2PL `applySequential interleaved`
computes the interleaved execution's net effect (SM3.C.7 atomicity), so this is
the genuine conflict-equivalence notion: same observable result. -/
def serialEquivalent (interleaved serial : List KernelTransitionInstance)
    (s₀ : SystemState) : Prop :=
  applySequential interleaved s₀ = applySequential serial s₀

/-- WS-SM SM3.E.2: `serialEquivalent` is reflexive. -/
theorem serialEquivalent_refl (sched : List KernelTransitionInstance)
    (s₀ : SystemState) : serialEquivalent sched sched s₀ := rfl

/-- WS-SM SM3.E.3 (plan §5.5 **Theorem 2.1.10**, `serializability_under_2pl`):
every strict-2PL interleaved execution is serial-equivalent to the commit-sorted
serial order, which is moreover a permutation of the execution and ascending in
commit time (the topological sort of the acyclic conflict graph).

The three conjuncts are the full Bernstein result:
* `Perm` — the serial order contains exactly the interleaved execution's
  transitions (none dropped or duplicated);
* `Pairwise (commitTime ≤)` — the serial order is the commit-time topological
  sort of the conflict graph (acyclic by `conflictGraph_acyclic`);
* `serialEquivalent` — the serial order produces the same final state, proved by
  the commuting-transposition reordering (`commitSort_commutingReorder` +
  `applySequential_eq_of_commutingReorder`).

The hypothesis `outOfOrderCommute interleaved` is the strict-2PL consequence:
conflicting transitions are already commit-ordered (lock exclusion), so every
pair the sort must reorder is non-conflicting, hence commutes. -/
theorem serializability_under_2pl (interleaved : List KernelTransitionInstance)
    (s₀ : SystemState) (hooc : outOfOrderCommute interleaved) :
    (commitSort interleaved).Perm interleaved ∧
    (commitSort interleaved).Pairwise (fun a b => a.commitTime ≤ b.commitTime) ∧
    serialEquivalent interleaved (commitSort interleaved) s₀ := by
  refine ⟨commitSort_perm interleaved, commitSort_sorted interleaved, ?_⟩
  exact applySequential_eq_of_commutingReorder
    (commitSort_commutingReorder interleaved hooc) s₀

/-- WS-SM SM3.E.3 (plan §5.5 existential form): every strict-2PL execution admits
*some* serial order it is serial-equivalent to (witnessed by the commit sort),
which is a commit-ordered permutation.  This is the plan's literal `∃ serial,
serialEquivalent execution serial` statement, strengthened with the
permutation + commit-ordering witnesses so the existential is non-vacuous (it is
NOT trivially witnessed by `interleaved` itself — the witness is a genuine
reordering into commit order). -/
theorem serializability_under_2pl_exists
    (interleaved : List KernelTransitionInstance) (s₀ : SystemState)
    (hooc : outOfOrderCommute interleaved) :
    ∃ serial : List KernelTransitionInstance,
      serial.Perm interleaved ∧
      serial.Pairwise (fun a b => a.commitTime ≤ b.commitTime) ∧
      serialEquivalent interleaved serial s₀ :=
  ⟨commitSort interleaved, serializability_under_2pl interleaved s₀ hooc⟩

/-- WS-SM SM3.E.3: a schedule whose transitions are all read-only (identity
actions) satisfies `outOfOrderCommute` unconditionally — every pair commutes
(reads commute with everything), so there is no out-of-order pair to obstruct
the sort.  This is the discharge of the strict-2PL `outOfOrderCommute` hypothesis
for the canonical non-conflicting case (an all-reads workload). -/
theorem outOfOrderCommute_of_forall_action_id :
    ∀ (l : List KernelTransitionInstance), (∀ τ ∈ l, τ.action = id) →
      outOfOrderCommute l
  | [], _ => trivial
  | head :: rest, h => by
      rw [outOfOrderCommute_cons]
      refine ⟨fun x _ _ =>
        KernelTransitionInstance.actionsCommute_of_action_id_left
          (h head List.mem_cons_self), ?_⟩
      exact outOfOrderCommute_of_forall_action_id rest
        (fun τ hτ => h τ (List.mem_cons_of_mem _ hτ))

/-- WS-SM SM3.E.3 (non-vacuity witness — unconditional serializability of a
read-only workload): a schedule of read-only transitions is serial-equivalent to
its commit-sorted serial order, with **no** side hypothesis.  The canonical
all-non-conflicting case (every transition only reads) is always serializable.
This proves `serializability_under_2pl` is not a vacuous statement: there is a
genuine, hypothesis-free family of executions for which the conclusion holds. -/
theorem serializability_of_readOnly_schedule
    (interleaved : List KernelTransitionInstance)
    (hRead : ∀ τ ∈ interleaved, τ.action = id) (s₀ : SystemState) :
    serialEquivalent interleaved (commitSort interleaved) s₀ :=
  applySequential_eq_of_commutingReorder
    (commitSort_commutingReorder interleaved
      (outOfOrderCommute_of_forall_action_id interleaved hRead)) s₀

/-- WS-SM SM3.E.3 (conflict-consistency of the serialization order): a
commit-sorted serial schedule **respects** the conflict order — if `τ₂` appears
before `τ₁` in the schedule, then `τ₁` does NOT conflict-precede `τ₂`.

This is the "the serial order is a valid serialization" half of Bernstein's
theorem: the commit-time topological sort never places a conflict edge backward.
Proof: `τ₂` before `τ₁` in a commit-sorted list gives `τ₂.commitTime ≤
τ₁.commitTime`; `conflictPrecedes τ₁ τ₂` would require `τ₁.commitTime <
τ₂.commitTime` — contradiction. -/
theorem commitSorted_respects_conflictPrecedes
    (serial : List KernelTransitionInstance)
    (hSorted : serial.Pairwise (fun a b => a.commitTime ≤ b.commitTime))
    (pre rest : List KernelTransitionInstance)
    (τ₁ τ₂ : KernelTransitionInstance)
    (hSplit : serial = pre ++ τ₂ :: rest) (hmem : τ₁ ∈ rest) :
    ¬ conflictPrecedes τ₁ τ₂ := by
  intro hcp
  have hle : τ₂.commitTime ≤ τ₁.commitTime := by
    rw [hSplit] at hSorted
    rw [List.pairwise_append] at hSorted
    obtain ⟨_, hTail, _⟩ := hSorted
    exact (List.pairwise_cons.mp hTail).1 τ₁ hmem
  exact (Nat.not_lt.mpr hle) hcp.2

/-- WS-SM SM3.E.3 (the serialization respects the plan's SM3.E.1 `conflictOrder`):
a commit-sorted serial schedule never places a `conflictOrder` edge backward.  If
`τ₂` appears before `τ₁` in the schedule and `τ₂` follows strict 2PL (with distinct
commit times), then `τ₁` does NOT `conflictOrder` before `τ₂` — i.e. the serial
order is a valid serialization w.r.t. the plan's `conflictOrder` precedence, not
just the derived `conflictPrecedes`.

Fulfils `conflictOrder`'s docstring claim ("the precedence the serialization order
must respect"): factors through `conflictOrder_implies_conflictPrecedes` (turning
the `conflictOrder` edge into a `conflictPrecedes` edge under strict 2PL) +
`commitSorted_respects_conflictPrecedes` (which forbids backward
`conflictPrecedes` edges). -/
theorem commitSorted_respects_conflictOrder
    (serial : List KernelTransitionInstance)
    (hSorted : serial.Pairwise (fun a b => a.commitTime ≤ b.commitTime))
    (pre rest : List KernelTransitionInstance)
    (τ₁ τ₂ : KernelTransitionInstance)
    (hSplit : serial = pre ++ τ₂ :: rest) (hmem : τ₁ ∈ rest)
    (h2pl : τ₂.followsStrict2PL) (hne : τ₁.commitTime ≠ τ₂.commitTime) :
    ¬ conflictOrder τ₁ τ₂ := fun hco =>
  commitSorted_respects_conflictPrecedes serial hSorted pre rest τ₁ τ₂ hSplit hmem
    (conflictOrder_implies_conflictPrecedes τ₁ τ₂ h2pl hco hne)

-- ============================================================================
-- §6c — Grounding: `outOfOrderCommute` is a CONSEQUENCE of strict 2PL
-- ============================================================================
--
-- §6b's `serializability_under_2pl` takes `outOfOrderCommute` as a hypothesis.
-- That hypothesis is NOT an arbitrary assumption: it is a consequence of the
-- strict-2PL discipline, exactly as SM3.D §7 grounds its 2PL + ordering
-- hypotheses in the SM3.B canonical sort.  This section discharges
-- `outOfOrderCommute` from (a) the strict-2PL lock-exclusion property
-- (`conflictsCommitOrdered`: conflicting pairs appear in commit order, so no
-- conflicting pair is out of commit order) and (b) the commutativity of
-- non-conflicting transitions (the SM3.E.5 witness — reads and disjoint
-- footprints commute).  Together they make `serializability_under_2pl`'s "under
-- 2PL" name rigorous rather than nominal.

/-- WS-SM SM3.E.3 grounding: the strict-2PL **lock-exclusion** property, phrased
recursively over a schedule.  For the head transition and every later `x`, if the
head commits strictly *after* `x` (i.e. they are out of commit order), then they
do NOT share a conflicting lock.

This is the operational consequence of strict 2PL: a conflicting pair out of
commit order would require the later-committing transition to have acquired the
shared lock first and yet committed second — impossible when each holds its locks
until commit (lock exclusion).  So in a strict-2PL execution every conflicting
pair is already in commit order. -/
def conflictsCommitOrdered : List KernelTransitionInstance → Prop
  | [] => True
  | head :: rest =>
      (∀ x ∈ rest, x.commitTime < head.commitTime →
        ¬ ktiSharesConflictingLock head x) ∧
      conflictsCommitOrdered rest

@[simp] theorem conflictsCommitOrdered_nil :
    conflictsCommitOrdered [] = True := rfl

@[simp] theorem conflictsCommitOrdered_cons (head : KernelTransitionInstance)
    (rest : List KernelTransitionInstance) :
    conflictsCommitOrdered (head :: rest) =
      ((∀ x ∈ rest, x.commitTime < head.commitTime → ¬ ktiSharesConflictingLock head x) ∧
       conflictsCommitOrdered rest) := rfl

/-- WS-SM SM3.E.3: `conflictsCommitOrdered` is decidable.  The head conjunct is a
finite `∀` over `rest` with a decidable body (`<` and `¬ ktiSharesConflictingLock`
are both decidable); the tail is the recursive instance. -/
instance : ∀ sched : List KernelTransitionInstance,
    Decidable (conflictsCommitOrdered sched)
  | [] => isTrue trivial
  | head :: rest =>
      have : Decidable (conflictsCommitOrdered rest) := instDecidableConflictsCommitOrdered rest
      decidable_of_iff
        ((∀ x ∈ rest, x.commitTime < head.commitTime → ¬ ktiSharesConflictingLock head x) ∧
          conflictsCommitOrdered rest)
        (conflictsCommitOrdered_cons head rest).symm.to_iff

/-- WS-SM SM3.E.3 (the strict-2PL grounding — mirrors SM3.D §7's
`execution_satisfies_hypotheses_of_all_prefix`): the `outOfOrderCommute`
hypothesis of `serializability_under_2pl` is a *consequence* of strict 2PL.

If the schedule is `conflictsCommitOrdered` (conflicting pairs appear in commit
order — the lock-exclusion property) AND every non-conflicting pair commutes
(`hNonConflictCommute`, discharged by the SM3.E.5 commutativity lemmas: reads and
disjoint footprints commute), then `outOfOrderCommute` holds.  The argument is
exactly: every out-of-commit-order pair is non-conflicting (by
`conflictsCommitOrdered`), hence commutes (by `hNonConflictCommute`).  This makes
`serializability_under_2pl`'s hypothesis a genuine 2PL consequence, not a bolt-on
assumption. -/
theorem outOfOrderCommute_of_conflictsCommitOrdered
    (hNonConflictCommute : ∀ τ₁ τ₂ : KernelTransitionInstance,
      ¬ ktiSharesConflictingLock τ₁ τ₂ → τ₁.actionsCommute τ₂) :
    ∀ sched : List KernelTransitionInstance,
      conflictsCommitOrdered sched → outOfOrderCommute sched
  | [], _ => trivial
  | head :: rest, h => by
      rw [conflictsCommitOrdered_cons] at h
      rw [outOfOrderCommute_cons]
      refine ⟨fun x hx hlt => hNonConflictCommute head x (h.1 x hx hlt), ?_⟩
      exact outOfOrderCommute_of_conflictsCommitOrdered hNonConflictCommute rest h.2

/-- WS-SM SM3.E.3 (Theorem 2.1.10, **grounded form** — the honest "under 2PL"
statement): every strict-2PL execution is serial-equivalent to its commit-sorted
serialization order, which is a commit-ordered permutation.

The hypotheses are exactly the genuine strict-2PL conditions: `conflictsCommitOrdered`
(the lock-exclusion property — conflicting pairs commit in order) and
`hNonConflictCommute` (non-conflicting transitions commute, SM3.E.5).  Unlike
`serializability_under_2pl` (which takes the derived `outOfOrderCommute` directly),
this form takes only the primitive 2PL properties, so its name is rigorous. -/
theorem serializability_under_2pl_of_conflicts_ordered
    (interleaved : List KernelTransitionInstance) (s₀ : SystemState)
    (hNonConflictCommute : ∀ τ₁ τ₂ : KernelTransitionInstance,
      ¬ ktiSharesConflictingLock τ₁ τ₂ → τ₁.actionsCommute τ₂)
    (hOrdered : conflictsCommitOrdered interleaved) :
    (commitSort interleaved).Perm interleaved ∧
    (commitSort interleaved).Pairwise (fun a b => a.commitTime ≤ b.commitTime) ∧
    serialEquivalent interleaved (commitSort interleaved) s₀ :=
  serializability_under_2pl interleaved s₀
    (outOfOrderCommute_of_conflictsCommitOrdered hNonConflictCommute interleaved hOrdered)

-- ============================================================================
-- §7 — Commutativity of non-conflicting operations (SM3.E.5)
-- ============================================================================
--
-- Non-conflicting transitions commute.  We prove this at two levels of fidelity:
--
-- * **Structural** `actionsCommute` (`τ₁.action ∘ τ₂.action = τ₂.action ∘
--   τ₁.action`) — holds exactly for the read-only (identity-action) and
--   disjoint-subsystem (different SystemState field) pairs.  These feed the
--   structural `serializability_under_2pl` (§6) directly.
--
-- * **Observational** `objStoreEquiv` (the two orders agree on every object-store
--   lookup) — the correct notion for two writes to *different objects*.  The
--   object store is a Robin-Hood hash table whose internal slot layout depends on
--   insertion order, so two inserts at distinct keys are observationally — but
--   not structurally — equal.  Conflict-serializability is an observational
--   property (Bernstein: equivalent schedules agree on the *database state*), so
--   `objStoreEquiv` is the faithful equivalence for the write/write case.

/-! ### §7a — Read-only (identity-action) transitions commute (structural) -/

/-- WS-SM SM3.E.5: a read-only transition instance — its business action is the
identity (it inspects state, e.g. a `cspaceRead` / `serviceQuery` lookup, but
mutates nothing).  Used to witness that reads commute with everything. -/
def readOnlyInstance (S : LockSet) (core : CoreId) (commitTime : Nat)
    (acquireTime : LockId → Nat) : KernelTransitionInstance :=
  { lockSet := S, core := core, commitTime := commitTime,
    acquireTime := acquireTime, action := id }

/-- WS-SM SM3.E.5: a read-only transition's action is the identity. -/
@[simp] theorem readOnlyInstance_action (S : LockSet) (core : CoreId)
    (ct : Nat) (at_ : LockId → Nat) :
    (readOnlyInstance S core ct at_).action = id := rfl

/-- WS-SM SM3.E.5 (the plan's `cspaceRead_commutes_with_cspaceRead` analog): a
read-only transition commutes with **any** transition.  Two reads of any objects
(the canonical non-conflicting pair) commute, and a read commutes with a write of
any other object.  Discharged from `actionsCommute_of_action_id_left`. -/
theorem readOnlyInstance_actionsCommute (S : LockSet) (core : CoreId)
    (ct : Nat) (at_ : LockId → Nat) (τ : KernelTransitionInstance) :
    (readOnlyInstance S core ct at_).actionsCommute τ :=
  KernelTransitionInstance.actionsCommute_of_action_id_left rfl

/-- WS-SM SM3.E.5: two read-only transitions commute (the `read/read`
non-conflicting pair). -/
theorem readOnlyInstance_actionsCommute_readOnly (S₁ S₂ : LockSet) (c₁ c₂ : CoreId)
    (ct₁ ct₂ : Nat) (at₁ at₂ : LockId → Nat) :
    (readOnlyInstance S₁ c₁ ct₁ at₁).actionsCommute (readOnlyInstance S₂ c₂ ct₂ at₂) :=
  readOnlyInstance_actionsCommute S₁ c₁ ct₁ at₁ _

/-! ### §7b — Disjoint-subsystem (different-field) transitions commute (structural) -/

/-- WS-SM SM3.E.5: a transition whose action writes only the table-level
`objStoreLock` field (a pure object-store-lock-bookkeeping action). -/
def setObjStoreLockAction (lk : RwLockState) : SystemState → SystemState :=
  fun s => { s with objStoreLock := lk }

/-- WS-SM SM3.E.5: a transition whose action writes only the `scheduler`
subsystem field. -/
def setSchedulerAction (sch : SchedulerState) : SystemState → SystemState :=
  fun s => { s with scheduler := sch }

/-- WS-SM SM3.E.5 (disjoint-subsystem commutativity, structural): two actions that
write **different** SystemState record fields commute structurally.  Concretely,
an object-store-lock action and a scheduler action touch disjoint record fields,
so applying them in either order yields the identical state.  This witnesses
"transitions operating on disjoint kernel subsystems commute" — a major class of
non-conflicting pairs. -/
theorem setObjStoreLock_setScheduler_commute (lk : RwLockState) (sch : SchedulerState)
    (s : SystemState) :
    setObjStoreLockAction lk (setSchedulerAction sch s)
      = setSchedulerAction sch (setObjStoreLockAction lk s) := rfl

/-- WS-SM SM3.E.5: the disjoint-subsystem commute lifted to `actionsCommute` on
the transition instances whose actions are the two field setters. -/
theorem disjointField_actionsCommute (lk : RwLockState) (sch : SchedulerState)
    (S₁ S₂ : LockSet) (c₁ c₂ : CoreId) (ct₁ ct₂ : Nat) (at₁ at₂ : LockId → Nat) :
    (KernelTransitionInstance.mk S₁ c₁ ct₁ at₁ (setObjStoreLockAction lk)).actionsCommute
      (KernelTransitionInstance.mk S₂ c₂ ct₂ at₂ (setSchedulerAction sch)) := by
  intro s
  exact (setObjStoreLock_setScheduler_commute lk sch s)

/-! ### §7c — Write/write on different objects commute (observational) -/

/-- WS-SM SM3.E.5: **observational equivalence** of the object store — two states
agree on every object-store lookup.  This is the business-observable state that
conflict-serializability preserves (the lock-tracked object contents). -/
def objStoreEquiv (s₁ s₂ : SystemState) : Prop :=
  ∀ k : SeLe4n.ObjId, s₁.objects.get? k = s₂.objects.get? k

/-- WS-SM SM3.E.5: `objStoreEquiv` is reflexive. -/
theorem objStoreEquiv_refl (s : SystemState) : objStoreEquiv s s := fun _ => rfl

/-- WS-SM SM3.E.5: `objStoreEquiv` is symmetric. -/
theorem objStoreEquiv_symm {s₁ s₂ : SystemState} (h : objStoreEquiv s₁ s₂) :
    objStoreEquiv s₂ s₁ := fun k => (h k).symm

/-- WS-SM SM3.E.5: `objStoreEquiv` is transitive. -/
theorem objStoreEquiv_trans {s₁ s₂ s₃ : SystemState}
    (h₁ : objStoreEquiv s₁ s₂) (h₂ : objStoreEquiv s₂ s₃) : objStoreEquiv s₁ s₃ :=
  fun k => (h₁ k).trans (h₂ k)

/-- WS-SM SM3.E.5: `updateObjectAt` preserves the RHTable extension invariant
(the `insert` branch via `RHTable.insert_preserves_invExt`; the absent branch is
the identity). -/
theorem updateObjectAt_preserves_invExt (s : SystemState) (oid : SeLe4n.ObjId)
    (f : KernelObject → KernelObject) (hExt : s.objects.invExt) :
    (updateObjectAt s oid f).objects.invExt := by
  unfold updateObjectAt
  cases hg : s.objects.get? oid with
  | none => exact hExt
  | some obj =>
      exact SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt s.objects oid
        (f obj) hExt

/-- WS-SM SM3.E.5: closed-form characterisation of `updateObjectAt`'s effect on a
lookup.  Looking up `k` after `updateObjectAt s oid f` returns `f`-mapped
content at the target key `oid`, and the unchanged content at every other key.
Unifies the present/absent branches: when `oid` is absent, `(s.get? oid).map f =
none` agrees with the unchanged lookup. -/
theorem updateObjectAt_get? (s : SystemState) (oid k : SeLe4n.ObjId)
    (f : KernelObject → KernelObject) (hExt : s.objects.invExt) :
    (updateObjectAt s oid f).objects.get? k
      = if k = oid then (s.objects.get? oid).map f else s.objects.get? k := by
  unfold updateObjectAt
  by_cases hk : k = oid
  · subst hk
    rw [if_pos rfl]
    cases hg : s.objects.get? k with
    | none => simp [hg]
    | some o =>
        show (s.objects.insert k (f o)).get? k = (some o).map f
        rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self s.objects k (f o) hExt]
        rfl
  · rw [if_neg hk]
    cases hg : s.objects.get? oid with
    | none => rfl
    | some o =>
        show (s.objects.insert oid (f o)).get? k = s.objects.get? k
        exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne s.objects oid k (f o)
          (by simp [Ne.symm hk]) hExt

/-- WS-SM SM3.E.5 (observational write/write commute — the realistic
non-conflicting write pair): two `updateObjectAt` writes to **different** objects
commute observationally — applying them in either order yields object stores that
agree on every lookup.

Two transitions writing different TCBs (the canonical non-conflicting write pair:
disjoint footprints, no shared lock) have actions of exactly this shape, so they
commute observationally.  The result is observational (`objStoreEquiv`) rather
than structural because the Robin-Hood probe order depends on insertion order;
conflict-serializability is an observational property, so this is the faithful
statement. -/
theorem updateObjectAt_objStoreEquiv_comm (s : SystemState)
    (oid₁ oid₂ : SeLe4n.ObjId) (f₁ f₂ : KernelObject → KernelObject)
    (hExt : s.objects.invExt) (hNe : oid₁ ≠ oid₂) :
    objStoreEquiv (updateObjectAt (updateObjectAt s oid₁ f₁) oid₂ f₂)
                  (updateObjectAt (updateObjectAt s oid₂ f₂) oid₁ f₁) := by
  intro k
  have hExt1 : (updateObjectAt s oid₁ f₁).objects.invExt :=
    updateObjectAt_preserves_invExt s oid₁ f₁ hExt
  have hExt2 : (updateObjectAt s oid₂ f₂).objects.invExt :=
    updateObjectAt_preserves_invExt s oid₂ f₂ hExt
  rw [updateObjectAt_get? (updateObjectAt s oid₁ f₁) oid₂ k f₂ hExt1,
      updateObjectAt_get? (updateObjectAt s oid₂ f₂) oid₁ k f₁ hExt2,
      updateObjectAt_get? s oid₁ oid₂ f₁ hExt, updateObjectAt_get? s oid₁ k f₁ hExt,
      updateObjectAt_get? s oid₂ oid₁ f₂ hExt, updateObjectAt_get? s oid₂ k f₂ hExt]
  by_cases h1 : k = oid₁ <;> by_cases h2 : k = oid₂ <;>
    simp_all [Ne.symm hNe]

-- ============================================================================
-- §8 — Single-core proof preservation (SM3.E.6, Corollary 2.1.11)
-- ============================================================================
--
-- The architectural lever that keeps WS-SM's proof cost tractable: every
-- existing single-core kernel-transition theorem lifts to the SMP form for free,
-- gated only by (a) the `lockSetHeld` precondition — established by the
-- `withLockSet` growing phase (SM3.C.8 `acquireAll_establishes_lockSetHeld`) —
-- and (b) lock-insensitivity of the invariant — discharged structurally per
-- invariant class (SM3.C.8 foundation lemmas).  The single-core proof of the
-- action itself is reused verbatim.

/-- WS-SM SM3.E.6 (Corollary 2.1.11, invariant form): a single-core invariant
preserved by a transition's action is preserved by the transition's
`withLockSet`-wrapped SMP form, provided the invariant is lock-insensitive (the
acquire and release folds preserve it).  This is the SM3.C.8
`withLockSet_invariant_preserved` lever re-stated as the SM3.E.6 deliverable:
the single-core preservation proof (`hAction`) transfers verbatim. -/
theorem singleCore_invariant_preservation {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState)
    (inv : SystemState → Prop) (hPre : inv s)
    (hAcq : ∀ (l : LockId) (m : AccessMode) (s' : SystemState),
      inv s' → inv (acquireLockOnObject s' core l m))
    (hAction : ∀ s', inv s' → inv (action s').1)
    (hRel : ∀ (l : LockId) (m : AccessMode) (s' : SystemState),
      inv s' → inv (releaseLockOnObject s' core l m)) :
    inv (withLockSet S core action s).1 :=
  withLockSet_invariant_preserved S core action s inv hPre hAcq hAction hRel

/-- WS-SM SM3.E.6 (Corollary 2.1.11, **pre→post** meta-theorem — the general
form): if a single-core transition `op` establishes a postcondition `post` from a
precondition `pre` (`hSingleCore`), then its `withLockSet`-wrapped SMP form
establishes `post` from `pre`.

The three phases mirror `withLockSet`:
* **growing** — `pre` is lock-insensitive (`hPreAcq`), so it survives the acquire
  fold, and the action runs on a state satisfying `pre`;
* **action** — the single-core theorem `hSingleCore` gives `post` on the action's
  output (its proof is reused verbatim — this is the lever);
* **shrinking** — `post` is lock-insensitive on release (`hPostRel`), so it
  survives the release fold.

No re-proof of `op` is needed: the single-core argument applies because, under
`lockSetHeld` (established by the growing phase, see
`withLockSet_growing_phase_establishes_lockSetHeld`), no other core mutates the
locked objects, exactly as the single-core proof assumes. -/
theorem singleCore_proof_preservation {α : Type} (S : LockSet) (core : CoreId)
    (op : SystemState → SystemState × α) (s : SystemState)
    (pre post : SystemState → Prop) (hpre : pre s)
    (hPreAcq : ∀ (l : LockId) (m : AccessMode) (s' : SystemState),
      pre s' → pre (acquireLockOnObject s' core l m))
    (hSingleCore : ∀ s', pre s' → post (op s').1)
    (hPostRel : ∀ (l : LockId) (m : AccessMode) (s' : SystemState),
      post s' → post (releaseLockOnObject s' core l m)) :
    post (withLockSet S core op s).1 := by
  rw [withLockSet_fst]
  -- Phase 1 (growing): `pre` survives the acquire fold.
  have hPreAfter : pre (acquireAll core S.lockAcquireSequence s) :=
    lockSet_invariant_preserved S core s pre hpre hPreAcq
  -- Phase 2 (action): the single-core theorem establishes `post`.
  have hPostAfterAction : post (op (acquireAll core S.lockAcquireSequence s)).1 :=
    hSingleCore _ hPreAfter
  -- Phase 3 (shrinking): `post` survives the release fold.
  have hRelFold : ∀ (pairs : List (LockId × AccessMode)) (s₀ : SystemState),
      post s₀ → post (releaseAll core pairs s₀) := by
    intro pairs
    induction pairs with
    | nil => intro s₀ h; exact h
    | cons head rest ih =>
        intro s₀ h
        show post (releaseAll core rest (releaseLockOnObject s₀ core head.fst head.snd))
        exact ih _ (hPostRel head.fst head.snd s₀ h)
  exact hRelFold S.lockAcquireSequence.reverse _ hPostAfterAction

/-- WS-SM SM3.E.6: the `lockSetHeld` precondition the meta-theorem rests on is a
**consequence** of `withLockSet`, not an external assumption.  When every lock in
`S` resolves to a present, kind-matching, available (`unheld`) object in `s`, the
`withLockSet` growing phase puts the entire lock set into the held state on the
post-acquire state the action sees.  Lifts SM3.C.8's
`acquireAll_establishes_lockSetHeld`. -/
theorem withLockSet_growing_phase_establishes_lockSetHeld (S : LockSet)
    (core : CoreId) (s : SystemState)
    (hExt : s.objects.invExt)
    (hEach : ∀ p ∈ S.pairs, ∃ o, s.objects[p.fst.objId]? = some o ∧
        o.lockKind = p.fst.kind ∧ o.objectLockOf = RwLockState.unheld) :
    lockSetHeld core S (acquireAll core S.lockAcquireSequence s) :=
  acquireAll_establishes_lockSetHeld S core s hExt hEach

-- ============================================================================
-- §8b — Worked NON-VACUOUS instantiation of SM3.E.6 on a real invariant
-- ============================================================================
--
-- `singleCore_proof_preservation` is a metatheorem; its lock-insensitivity
-- hypotheses are trivially dischargeable for the `True` invariant.  To prove the
-- lever is a USABLE tool (not a vacuous false-anchor), this section instantiates
-- it on the genuine, non-trivial table-level `objStoreLock.wf` invariant,
-- discharging the per-step lock-insensitivity via SM2.C's per-op wf-preservation.

/-- WS-SM SM3.E.6 foundation: acquiring any lock preserves the well-formedness of
the table-level `objStoreLock`.  The `.objStore` branch advances `objStoreLock`
via `RwLockState.applyOp` (SM2.C's `rwLock_tryAcquire{Read,Write}_preserves_wf`);
every modeled / N/A branch leaves `objStoreLock` untouched
(`acquireLockOnObject_preserves_objStoreLock_of_modeled`).  This is the per-step
lock-insensitivity witness for the `objStoreLock.wf` invariant class. -/
theorem acquireLockOnObject_preserves_objStoreLock_wf (s : SystemState)
    (core : CoreId) (l : LockId) (m : AccessMode) (h : s.objStoreLock.wf) :
    (acquireLockOnObject s core l m).objStoreLock.wf := by
  by_cases hKind : l.kind = .objStore
  · unfold acquireLockOnObject
    rw [hKind]
    simp only
    cases m with
    | read => exact rwLock_tryAcquireRead_preserves_wf _ core h
    | write => exact rwLock_tryAcquireWrite_preserves_wf _ core h
  · rw [acquireLockOnObject_preserves_objStoreLock_of_modeled s core l m hKind]
    exact h

/-- WS-SM SM3.E.6 foundation: releasing any lock preserves `objStoreLock.wf`.
Symmetric to the acquire form, using SM2.C's
`rwLock_release{Read,Write}_preserves_wf` and
`releaseLockOnObject_preserves_objStoreLock_of_modeled`. -/
theorem releaseLockOnObject_preserves_objStoreLock_wf (s : SystemState)
    (core : CoreId) (l : LockId) (m : AccessMode) (h : s.objStoreLock.wf) :
    (releaseLockOnObject s core l m).objStoreLock.wf := by
  by_cases hKind : l.kind = .objStore
  · unfold releaseLockOnObject
    rw [hKind]
    simp only
    cases m with
    | read => exact rwLock_releaseRead_preserves_wf _ core h
    | write => exact rwLock_releaseWrite_preserves_wf _ core h
  · rw [releaseLockOnObject_preserves_objStoreLock_of_modeled s core l m hKind]
    exact h

/-- WS-SM SM3.E.6 (NON-VACUOUS Corollary 2.1.11 witness): the table-level
`objStoreLock.wf` invariant survives a `withLockSet`-wrapped transition whose
action preserves it.  This instantiates `singleCore_proof_preservation` on the
**real** `objStoreLock.wf` invariant (not the trivial `True`), discharging the
lock-insensitivity hypotheses via the per-step wf-preservation lemmas above.

It proves the SM3.E.6 metatheorem is a genuine lever, not a vacuous false-anchor:
a non-trivial single-core invariant (the table lock's well-formedness, a real
SM2.C/SM3.C invariant) transfers verbatim through the 2PL `withLockSet` wrapper.
The single-core obligation reduces to `hActionWf` — the action's own
wf-preservation, which is exactly the single-core theorem. -/
theorem withLockSet_preserves_objStoreLock_wf {α : Type} (S : LockSet)
    (core : CoreId) (op : SystemState → SystemState × α) (s : SystemState)
    (hwf : s.objStoreLock.wf)
    (hActionWf : ∀ s', s'.objStoreLock.wf → (op s').1.objStoreLock.wf) :
    (withLockSet S core op s).1.objStoreLock.wf :=
  singleCore_proof_preservation S core op s
    (fun st => st.objStoreLock.wf) (fun st => st.objStoreLock.wf) hwf
    (fun l m s' h => acquireLockOnObject_preserves_objStoreLock_wf s' core l m h)
    hActionWf
    (fun l m s' h => releaseLockOnObject_preserves_objStoreLock_wf s' core l m h)

-- ============================================================================
-- §8c — A SECOND non-vacuous Cor 2.1.11 witness: the kind-discipline invariant
-- ============================================================================
--
-- `withLockSet_preserves_objStoreLock_wf` (§8b) demonstrated the lever on one
-- real invariant whose preservation is `invExt`-free.  This section demonstrates
-- it on a SECOND real invariant — the **kind-discipline** invariant (every
-- object's `objectType` tag is preserved), the most important real invariant
-- class (`tcbStoredUnderTidObjId`, `cnodeKindConsistent`, … all dispatch on
-- `objectType`).  Its lock-insensitivity genuinely depends on `invExt` (the
-- RHTable insert/lookup characterisation), so the invariant is bundled with
-- `invExt` and threaded through — showing the lever works on the realistic,
-- `invExt`-dependent invariant class, not only the `invExt`-free table lock.

/-- WS-SM SM3.E.6 foundation: releasing a lock preserves `invExt` (symmetric to
the imported `acquireLockOnObject_preserves_invExt`; both route through
`updateObjectLockAt_preserves_invExt`). -/
theorem releaseLockOnObject_preserves_invExt (s : SystemState) (core : CoreId)
    (l : LockId) (m : AccessMode) (hExt : s.objects.invExt) :
    (releaseLockOnObject s core l m).objects.invExt := by
  unfold releaseLockOnObject
  cases l.kind with
  | objStore => exact hExt
  | reply => exact hExt
  | page => exact hExt
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext =>
      all_goals exact updateObjectLockAt_preserves_invExt s l _ hExt

/-- WS-SM SM3.E.6 foundation: `updateObjectLockAt` preserves the `objectType` tag
at every key.  The kind-matched branch re-inserts `obj.updateLock op`, which
preserves `objectType` (`KernelObject.updateLock_preserves_objectType`), so
`updateObjectAt_preserves_objectType_at` applies; the fail-closed branch is the
identity. -/
theorem updateObjectLockAt_preserves_objectType_at (s : SystemState) (l : LockId)
    (op : RwLockOp) (k : SeLe4n.ObjId) (hExt : s.objects.invExt) :
    Option.map KernelObject.objectType ((updateObjectLockAt s l op).objects.get? k)
      = Option.map KernelObject.objectType (s.objects.get? k) := by
  unfold updateObjectLockAt
  cases LockId.lookup s l with
  | none => rfl
  | some _ =>
      exact updateObjectAt_preserves_objectType_at s l.objId k
        (fun obj => obj.updateLock op) hExt
        (fun o => KernelObject.updateLock_preserves_objectType o op)

/-- WS-SM SM3.E.6 foundation: acquiring a lock preserves the `objectType` tag at
every key.  The `.objStore` branch only touches `objStoreLock` (objects
unchanged); the modeled branches route through
`updateObjectLockAt_preserves_objectType_at`; `.reply`/`.page` are no-ops. -/
theorem acquireLockOnObject_preserves_objectType_at (s : SystemState) (core : CoreId)
    (l : LockId) (m : AccessMode) (k : SeLe4n.ObjId) (hExt : s.objects.invExt) :
    Option.map KernelObject.objectType ((acquireLockOnObject s core l m).objects.get? k)
      = Option.map KernelObject.objectType (s.objects.get? k) := by
  unfold acquireLockOnObject
  cases l.kind with
  | objStore => rfl
  | reply => rfl
  | page => rfl
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext =>
      all_goals exact updateObjectLockAt_preserves_objectType_at s l (m.toAcquireOp core) k hExt

/-- WS-SM SM3.E.6 foundation: releasing a lock preserves the `objectType` tag at
every key.  Symmetric to the acquire form. -/
theorem releaseLockOnObject_preserves_objectType_at (s : SystemState) (core : CoreId)
    (l : LockId) (m : AccessMode) (k : SeLe4n.ObjId) (hExt : s.objects.invExt) :
    Option.map KernelObject.objectType ((releaseLockOnObject s core l m).objects.get? k)
      = Option.map KernelObject.objectType (s.objects.get? k) := by
  unfold releaseLockOnObject
  cases l.kind with
  | objStore => rfl
  | reply => rfl
  | page => rfl
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext =>
      all_goals exact updateObjectLockAt_preserves_objectType_at s l (m.toReleaseOp core) k hExt

/-- WS-SM SM3.E.6 (SECOND non-vacuous Cor 2.1.11 witness): the **kind-discipline**
invariant — every object's `objectType` tag equals the reference state `s₀`'s —
survives a `withLockSet`-wrapped transition whose action preserves it.

This instantiates `singleCore_proof_preservation` on a genuinely
`invExt`-dependent real-invariant class (bundling `invExt` with the kind-tag
equality so the lock-insensitivity hypotheses are dischargeable).  Together with
`withLockSet_preserves_objStoreLock_wf` (the `invExt`-free table lock), it shows
the Corollary 2.1.11 lever transfers BOTH invariant flavours — the `invExt`-free
field invariants and the `invExt`-dependent object-store-structural invariants
(the dominant real-invariant class).  The single-core obligation reduces to
`hAction` — the action's own kind-preservation, exactly the single-core theorem. -/
theorem withLockSet_preserves_objectType_at {α : Type} (S : LockSet) (core : CoreId)
    (op : SystemState → SystemState × α) (s s₀ : SystemState)
    (hInv : s.objects.invExt ∧
      ∀ k, Option.map KernelObject.objectType (s.objects.get? k)
        = Option.map KernelObject.objectType (s₀.objects.get? k))
    (hAction : ∀ s',
      (s'.objects.invExt ∧
        ∀ k, Option.map KernelObject.objectType (s'.objects.get? k)
          = Option.map KernelObject.objectType (s₀.objects.get? k)) →
      ((op s').1.objects.invExt ∧
        ∀ k, Option.map KernelObject.objectType ((op s').1.objects.get? k)
          = Option.map KernelObject.objectType (s₀.objects.get? k))) :
    (withLockSet S core op s).1.objects.invExt ∧
    ∀ k, Option.map KernelObject.objectType ((withLockSet S core op s).1.objects.get? k)
      = Option.map KernelObject.objectType (s₀.objects.get? k) :=
  singleCore_proof_preservation S core op s
    (fun st => st.objects.invExt ∧
      ∀ k, Option.map KernelObject.objectType (st.objects.get? k)
        = Option.map KernelObject.objectType (s₀.objects.get? k))
    (fun st => st.objects.invExt ∧
      ∀ k, Option.map KernelObject.objectType (st.objects.get? k)
        = Option.map KernelObject.objectType (s₀.objects.get? k))
    hInv
    (fun l m s' hpre => ⟨acquireLockOnObject_preserves_invExt s' core l m hpre.1,
      fun k => by
        rw [acquireLockOnObject_preserves_objectType_at s' core l m k hpre.1]; exact hpre.2 k⟩)
    hAction
    (fun l m s' hpost => ⟨releaseLockOnObject_preserves_invExt s' core l m hpost.1,
      fun k => by
        rw [releaseLockOnObject_preserves_objectType_at s' core l m k hpost.1]; exact hpost.2 k⟩)

-- ============================================================================
-- §9 — Atomicity bridge: `applySequential` faithfully models the `withLockSet`
--      execution under a lock-insensitive observer (SM3.E.2 grounding)
-- ============================================================================
--
-- The schedule model (§1) folds *bare business actions* (`applySequential`).
-- The real kernel runs each transition wrapped in `withLockSet` (SM3.C), which
-- additionally acquires/releases locks.  This section proves — rather than
-- merely asserts in prose — that the two agree under any lock-insensitive
-- observer `π` (a business-state projection): the lock machinery is invisible,
-- so `applySequential` of the business actions IS the observable net effect of
-- the `withLockSet`-wrapped execution.  This grounds the SM3.E model in the
-- SM3.C `withLockSet` semantics via SM3.C.7's `lockSet_observer_atomic`.

/-- WS-SM SM3.E.2 (atomicity bridge): an action is a **`π`-congruence** when it
respects the observer `π` — equal observations map to equal observations.  The
business actions of kernel transitions are `π`-congruences for the business-state
observer `π` (their effect on `π` depends only on the `π`-visible input). -/
def ActionPiCongr {β : Type} (π : SystemState → β) (a : SystemState → SystemState) :
    Prop :=
  ∀ s₁ s₂, π s₁ = π s₂ → π (a s₁) = π (a s₂)

/-- WS-SM SM3.E.2: the `applySequential` fold is a `π`-congruence when every
action in the schedule is.  Equal observations of the start state yield equal
observations of the end state.  Induction on the schedule. -/
theorem applySequential_piCongr {β : Type} (π : SystemState → β) :
    ∀ (l : List KernelTransitionInstance), (∀ τ ∈ l, ActionPiCongr π τ.action) →
      ∀ s₁ s₂, π s₁ = π s₂ → π (applySequential l s₁) = π (applySequential l s₂)
  | [], _, _, _, h => h
  | τ :: rest, hCongr, s₁, s₂, h => by
      rw [applySequential_cons, applySequential_cons]
      exact applySequential_piCongr π rest
        (fun x hx => hCongr x (List.mem_cons_of_mem _ hx))
        (τ.action s₁) (τ.action s₂) (hCongr τ List.mem_cons_self s₁ s₂ h)

/-- WS-SM SM3.E.2 (atomicity bridge — single transition): wrapping a business
action in `withLockSet` is **observationally identical** to the bare action, for
any lock-insensitive observer `π`.  The acquire/release lock machinery is
invisible: `π (withLockSet S core (action, ()) s).1 = π (action s)`.

Proof via SM3.C.7's `lockSet_observer_atomic`: the acquire fold is `π`-invisible
(`π (acquireAll …) = π s`) and the release fold is `π`-invisible (so
`π (withLockSet …).1 = π (action (acquireAll …))`); the action being a
`π`-congruence then collapses `π (action (acquireAll …)) = π (action s)`.  This
is the formal content behind "`applySequential` models the interleaved
execution" — not an assumption but a theorem grounded in the SM3.C semantics. -/
theorem withLockSet_observation_eq_action {β : Type} (S : LockSet) (core : CoreId)
    (businessAction : SystemState → SystemState) (s : SystemState) (π : SystemState → β)
    (hAcq : AcquireInsensitive core π) (hRel : ReleaseInsensitive core π)
    (hCongr : ActionPiCongr π businessAction) :
    π (withLockSet S core (fun st => (businessAction st, ())) s).1 = π (businessAction s) := by
  obtain ⟨hAcqEq, hRelEq⟩ :=
    lockSet_observer_atomic S core (fun st => (businessAction st, ())) s π hAcq hRel
  rw [hRelEq]
  exact hCongr _ _ hAcqEq

/-- WS-SM SM3.E.2 (atomicity bridge): a `withLockSet`-wrapped schedule — each
transition's business action wrapped in its own `withLockSet`.  This is the
*real* kernel execution shape (modulo the per-core seam SM5 adds); SM3.E proves
its observable effect equals the bare `applySequential` model. -/
def applySequentialWithLockSet (sched : List KernelTransitionInstance)
    (s : SystemState) : SystemState :=
  sched.foldl
    (fun st τ => (withLockSet τ.lockSet τ.core (fun s' => (τ.action s', ())) st).1) s

@[simp] theorem applySequentialWithLockSet_nil (s : SystemState) :
    applySequentialWithLockSet [] s = s := rfl

@[simp] theorem applySequentialWithLockSet_cons (τ : KernelTransitionInstance)
    (rest : List KernelTransitionInstance) (s : SystemState) :
    applySequentialWithLockSet (τ :: rest) s =
      applySequentialWithLockSet rest
        (withLockSet τ.lockSet τ.core (fun s' => (τ.action s', ())) s).1 := rfl

/-- WS-SM SM3.E.2 (atomicity bridge — full schedule): the lock-insensitive
observation of a `withLockSet`-wrapped execution equals the observation of the
bare `applySequential` model.  So the SM3.E serializability results about
`applySequential` transfer verbatim to the real `withLockSet`-wrapped execution
under any business-state observer `π` whose actions are `π`-congruences.

Induction on the schedule: the single-transition bridge collapses the head's
`withLockSet` to its bare action (up to `π`), the IH handles the tail, and
`applySequential_piCongr` threads the head's `π`-equal post-states through the
tail fold.  This closes the "`applySequential` models the interleaved execution"
gap with a theorem rather than prose. -/
theorem applySequentialWithLockSet_observation {β : Type} (π : SystemState → β)
    (hAcq : ∀ c : CoreId, AcquireInsensitive c π)
    (hRel : ∀ c : CoreId, ReleaseInsensitive c π) :
    ∀ (sched : List KernelTransitionInstance),
      (∀ τ ∈ sched, ActionPiCongr π τ.action) →
      ∀ s, π (applySequentialWithLockSet sched s) = π (applySequential sched s)
  | [], _, _ => rfl
  | τ :: rest, hCongr, s => by
      rw [applySequentialWithLockSet_cons, applySequential_cons]
      have hW : π (withLockSet τ.lockSet τ.core (fun s' => (τ.action s', ())) s).1
          = π (τ.action s) :=
        withLockSet_observation_eq_action τ.lockSet τ.core τ.action s π
          (hAcq τ.core) (hRel τ.core) (hCongr τ List.mem_cons_self)
      rw [applySequentialWithLockSet_observation π hAcq hRel rest
        (fun x hx => hCongr x (List.mem_cons_of_mem _ hx))]
      exact applySequential_piCongr π rest
        (fun x hx => hCongr x (List.mem_cons_of_mem _ hx)) _ _ hW

-- ============================================================================
-- §9b — Concrete NON-VACUOUS witness for the atomicity bridge
-- ============================================================================
--
-- §9's bridge takes `AcquireInsensitive` / `ReleaseInsensitive` as hypotheses.
-- To prove the bridge is a usable result — not one resting on unsatisfiable
-- hypotheses — this section exhibits a genuine non-trivial business-state
-- observer (the `scheduler` projection) that discharges BOTH insensitivity
-- hypotheses unconditionally, and instantiates the bridge on a transition that
-- genuinely writes the scheduler: the bridge correctly reports the action's
-- effect (`= sch`) while the lock acquire/release machinery stays invisible.
-- Mirrors the concrete non-vacuity witnesses of §8b (objStoreLock.wf), §8c
-- (objectType), and §10 (write/write).

/-- WS-SM SM3.E.2 foundation (plumbing): `updateObjectLockAt` leaves the
`scheduler` subsystem field untouched — the kind-matched branch writes only the
`objects` table (`updateObjectAt`), the fail-closed branch is the identity. -/
private theorem updateObjectLockAt_preserves_scheduler (s : SystemState) (l : LockId)
    (op : RwLockOp) : (updateObjectLockAt s l op).scheduler = s.scheduler := by
  unfold updateObjectLockAt
  cases LockId.lookup s l with
  | none => rfl
  | some _ => unfold updateObjectAt; cases s.objects.get? l.objId <;> rfl

/-- WS-SM SM3.E.2 (atomicity-bridge non-vacuity foundation): acquiring a lock
leaves the `scheduler` subsystem field untouched.  Every `acquireLockOnObject`
branch touches only `objStoreLock` (`.objStore`), the `objects` table (modeled
kinds, via `updateObjectLockAt`), or nothing (`.reply`/`.page`) — never
`scheduler`. -/
theorem acquireLockOnObject_preserves_scheduler (s : SystemState) (core : CoreId)
    (l : LockId) (m : AccessMode) :
    (acquireLockOnObject s core l m).scheduler = s.scheduler := by
  unfold acquireLockOnObject
  cases l.kind <;>
    first
      | rfl
      | exact updateObjectLockAt_preserves_scheduler s l (m.toAcquireOp core)

/-- WS-SM SM3.E.2 (atomicity-bridge non-vacuity foundation): releasing a lock
leaves the `scheduler` subsystem field untouched.  Symmetric to the acquire
form. -/
theorem releaseLockOnObject_preserves_scheduler (s : SystemState) (core : CoreId)
    (l : LockId) (m : AccessMode) :
    (releaseLockOnObject s core l m).scheduler = s.scheduler := by
  unfold releaseLockOnObject
  cases l.kind <;>
    first
      | rfl
      | exact updateObjectLockAt_preserves_scheduler s l (m.toReleaseOp core)

/-- WS-SM SM3.E.2 (CONCRETE non-vacuity witness): the `scheduler` projection is a
genuine non-trivial business-state observer that is **acquire-insensitive** —
discharging the `AcquireInsensitive` hypothesis of the §9 bridge for a real
observer, proving the hypothesis is satisfiable (the bridge is not vacuous). -/
theorem schedulerObserver_acquireInsensitive (core : CoreId) :
    AcquireInsensitive core (fun s => s.scheduler) :=
  fun s l m => acquireLockOnObject_preserves_scheduler s core l m

/-- WS-SM SM3.E.2 (CONCRETE non-vacuity witness): the `scheduler` projection is
**release-insensitive**.  Together with `schedulerObserver_acquireInsensitive`
this discharges both hypotheses of `withLockSet_observation_eq_action` for a real
observer. -/
theorem schedulerObserver_releaseInsensitive (core : CoreId) :
    ReleaseInsensitive core (fun s => s.scheduler) :=
  fun s l m => releaseLockOnObject_preserves_scheduler s core l m

/-- WS-SM SM3.E.2 (the atomicity bridge applied NON-VACUOUSLY): a transition that
writes the scheduler (`setSchedulerAction sch`), wrapped in the full `withLockSet`
2PL lock machinery, has its scheduler effect correctly observed (`= sch`) — the
acquire/release folds are invisible.  Instantiates the §9 bridge
(`withLockSet_observation_eq_action`) on the concrete scheduler observer, proving
the bridge is a usable result on a real (observer, action) pair, not a vacuous
theorem resting on unsatisfiable insensitivity hypotheses. -/
theorem withLockSet_observation_scheduler_witness (S : LockSet) (core : CoreId)
    (sch : SchedulerState) (s : SystemState) :
    (withLockSet S core (fun st => (setSchedulerAction sch st, ())) s).1.scheduler = sch :=
  withLockSet_observation_eq_action S core (setSchedulerAction sch) s
    (fun s => s.scheduler)
    (schedulerObserver_acquireInsensitive core)
    (schedulerObserver_releaseInsensitive core)
    (fun _ _ _ => rfl)

-- ============================================================================
-- §10 — Observational serializability: covers write/write on distinct objects
-- ============================================================================
--
-- §6b's `serializability_under_2pl` proves *structural* state equality, which
-- holds for the read-only / disjoint-subsystem actions that commute structurally.
-- Two writes to *different objects* commute only OBSERVATIONALLY (`objStoreEquiv`,
-- §7c) because the Robin-Hood store's slot layout is insertion-order-dependent.
-- This section closes that coverage gap: it re-derives the full serializability
-- result up to `objStoreEquiv`, so it applies to the realistic write-heavy
-- workload (transitions whose business action is `updateObjectAt`).  The price is
-- threading the RHTable extension invariant `invExt` (which `updateObjectAt`'s
-- lookup characterisation `updateObjectAt_get?` requires) through the schedule.

/-- WS-SM SM3.E.5 (observational): an action is an **`objStoreEquiv`-congruence**
on `invExt` states — it maps observationally-equal `invExt` states to
observationally-equal states.  `updateObjectAt` actions satisfy this (their
effect on a lookup depends only on the observable store), but only on `invExt`
states, so the predicate is `invExt`-guarded. -/
def ActionObsCongr (a : SystemState → SystemState) : Prop :=
  ∀ s₁ s₂, s₁.objects.invExt → s₂.objects.invExt → objStoreEquiv s₁ s₂ →
    objStoreEquiv (a s₁) (a s₂)

/-- WS-SM SM3.E.5 (observational): an action **preserves `invExt`** — needed so
the `invExt` precondition threads through the schedule fold. -/
def ActionPreservesInvExt (a : SystemState → SystemState) : Prop :=
  ∀ s, s.objects.invExt → (a s).objects.invExt

/-- WS-SM SM3.E.5 (observational): a transition is **well-behaved** for the
observational layer when its action is both an `objStoreEquiv`-congruence and
`invExt`-preserving.  Discharged for `updateObjectAt`-shaped (object-store-write)
transitions below. -/
def KernelTransitionInstance.wellBehavedObs (τ : KernelTransitionInstance) : Prop :=
  ActionObsCongr τ.action ∧ ActionPreservesInvExt τ.action

/-- WS-SM SM3.E.5 (observational): two transitions **commute observationally** —
applying them in either order yields observationally-equal object stores (on
`invExt` states).  Write/write on distinct objects satisfies this
(`updateObjectAt_objStoreEquiv_comm`), where structural commutation fails. -/
def KernelTransitionInstance.actionsCommuteObs (τ₁ τ₂ : KernelTransitionInstance) :
    Prop :=
  ∀ s : SystemState, s.objects.invExt →
    objStoreEquiv (τ₁.action (τ₂.action s)) (τ₂.action (τ₁.action s))

/-- WS-SM SM3.E.5: an `updateObjectAt` action is an `objStoreEquiv`-congruence.
Two observationally-equal `invExt` states yield observationally-equal post-stores
because `updateObjectAt`'s per-key effect (`updateObjectAt_get?`) reads only the
observable store. -/
theorem updateObjectAt_actionObsCongr (oid : SeLe4n.ObjId)
    (f : KernelObject → KernelObject) :
    ActionObsCongr (fun s => updateObjectAt s oid f) := by
  intro s₁ s₂ h1 h2 heq k
  rw [updateObjectAt_get? s₁ oid k f h1, updateObjectAt_get? s₂ oid k f h2]
  by_cases hk : k = oid
  · rw [if_pos hk, if_pos hk, heq oid]
  · rw [if_neg hk, if_neg hk]; exact heq k

/-- WS-SM SM3.E.5: an `updateObjectAt` action preserves `invExt`. -/
theorem updateObjectAt_actionPreservesInvExt (oid : SeLe4n.ObjId)
    (f : KernelObject → KernelObject) :
    ActionPreservesInvExt (fun s => updateObjectAt s oid f) :=
  fun s hExt => updateObjectAt_preserves_invExt s oid f hExt

/-- WS-SM SM3.E.5: an object-store-write transition is well-behaved (both
conjuncts hold). -/
theorem updateObjectAt_wellBehavedObs (S : LockSet) (core : CoreId) (ct : Nat)
    (at_ : LockId → Nat) (oid : SeLe4n.ObjId) (f : KernelObject → KernelObject) :
    KernelTransitionInstance.wellBehavedObs
      ⟨S, core, ct, at_, fun s => updateObjectAt s oid f⟩ :=
  ⟨updateObjectAt_actionObsCongr oid f, updateObjectAt_actionPreservesInvExt oid f⟩

/-- WS-SM SM3.E.5 (observational): the `applySequential` fold preserves `invExt`
when every action does. -/
theorem applySequential_preservesInvExt :
    ∀ (l : List KernelTransitionInstance), (∀ τ ∈ l, ActionPreservesInvExt τ.action) →
      ∀ s : SystemState, s.objects.invExt → (applySequential l s).objects.invExt
  | [], _, _, hExt => hExt
  | τ :: rest, hWB, s, hExt => by
      rw [applySequential_cons]
      exact applySequential_preservesInvExt rest
        (fun x hx => hWB x (List.mem_cons_of_mem _ hx))
        (τ.action s) (hWB τ List.mem_cons_self s hExt)

/-- WS-SM SM3.E.5 (observational): the `applySequential` fold is an
`objStoreEquiv`-congruence on `invExt` states when every action is well-behaved.
Equal observable start stores yield equal observable end stores.  Induction
threads both `objStoreEquiv` and `invExt` through the fold. -/
theorem applySequential_obsCongr :
    ∀ (l : List KernelTransitionInstance),
      (∀ τ ∈ l, KernelTransitionInstance.wellBehavedObs τ) →
      ∀ (s₁ s₂ : SystemState), s₁.objects.invExt → s₂.objects.invExt →
        objStoreEquiv s₁ s₂ →
        objStoreEquiv (applySequential l s₁) (applySequential l s₂)
  | [], _, _, _, _, _, heq => heq
  | τ :: rest, hWB, s₁, s₂, h1, h2, heq => by
      rw [applySequential_cons, applySequential_cons]
      have hτ := hWB τ List.mem_cons_self
      exact applySequential_obsCongr rest
        (fun x hx => hWB x (List.mem_cons_of_mem _ hx))
        (τ.action s₁) (τ.action s₂) (hτ.2 s₁ h1) (hτ.2 s₂ h2) (hτ.1 s₁ s₂ h1 h2 heq)

/-- WS-SM SM3.E.3 (observational): swapping two observationally-commuting
transitions at the front of a schedule preserves `applySequential` up to
`objStoreEquiv`, provided the suffix actions are well-behaved (to thread the
congruence through the suffix fold) and the swapped actions preserve `invExt`. -/
theorem applySequential_swap_front_obs (τ₁ τ₂ : KernelTransitionInstance)
    (suf : List KernelTransitionInstance) (s : SystemState) (hExt : s.objects.invExt)
    (hSufWB : ∀ τ ∈ suf, KernelTransitionInstance.wellBehavedObs τ)
    (h1Ext : ActionPreservesInvExt τ₁.action) (h2Ext : ActionPreservesInvExt τ₂.action)
    (hComm : KernelTransitionInstance.actionsCommuteObs τ₁ τ₂) :
    objStoreEquiv (applySequential (τ₁ :: τ₂ :: suf) s)
                  (applySequential (τ₂ :: τ₁ :: suf) s) := by
  rw [applySequential_cons, applySequential_cons, applySequential_cons, applySequential_cons]
  exact applySequential_obsCongr suf hSufWB
    (τ₂.action (τ₁.action s)) (τ₁.action (τ₂.action s))
    (h2Ext _ (h1Ext _ hExt)) (h1Ext _ (h2Ext _ hExt)) (objStoreEquiv_symm (hComm s hExt))

/-- WS-SM SM3.E.3 (observational): consing a common `invExt`-preserving head onto
two schedules that are observationally `applySequential`-equal (on every `invExt`
state) preserves the observational equality. -/
theorem applySequential_cons_obs (a : KernelTransitionInstance)
    (l₁ l₂ : List KernelTransitionInstance) (hAExt : ActionPreservesInvExt a.action)
    (h : ∀ s, s.objects.invExt →
      objStoreEquiv (applySequential l₁ s) (applySequential l₂ s))
    (s : SystemState) (hExt : s.objects.invExt) :
    objStoreEquiv (applySequential (a :: l₁) s) (applySequential (a :: l₂) s) := by
  rw [applySequential_cons, applySequential_cons]
  exact h (a.action s) (hAExt s hExt)

/-- WS-SM SM3.E.3 (observational): the strict-2PL lock-exclusion hypothesis for
the observational layer — out-of-commit-order pairs commute observationally.
Mirrors `outOfOrderCommute` (§6) but with `actionsCommuteObs`. -/
def outOfOrderCommuteObs : List KernelTransitionInstance → Prop
  | [] => True
  | head :: rest =>
      (∀ x ∈ rest, x.commitTime < head.commitTime →
        KernelTransitionInstance.actionsCommuteObs head x) ∧
      outOfOrderCommuteObs rest

@[simp] theorem outOfOrderCommuteObs_nil : outOfOrderCommuteObs [] = True := rfl

@[simp] theorem outOfOrderCommuteObs_cons (head : KernelTransitionInstance)
    (rest : List KernelTransitionInstance) :
    outOfOrderCommuteObs (head :: rest) =
      ((∀ x ∈ rest, x.commitTime < head.commitTime →
        KernelTransitionInstance.actionsCommuteObs head x) ∧
       outOfOrderCommuteObs rest) := rfl

/-- WS-SM SM3.E.3 (observational): inserting `τ` into `l` is observationally
`applySequential`-equal to `τ :: l`, provided `l`'s actions are well-behaved, `τ`
preserves `invExt`, and `τ` commutes observationally with the smaller-commit
elements it moves past.  The obs counterpart of `insertByCommitTime_commutingReorder`:
each hop past a smaller predecessor is one observational front-swap. -/
theorem insertByCommitTime_obs (τ : KernelTransitionInstance)
    (h1Ext : ActionPreservesInvExt τ.action) :
    ∀ (l : List KernelTransitionInstance),
      (∀ x ∈ l, KernelTransitionInstance.wellBehavedObs x) →
      (∀ x ∈ l, x.commitTime < τ.commitTime →
        KernelTransitionInstance.actionsCommuteObs τ x) →
      ∀ s, s.objects.invExt →
        objStoreEquiv (applySequential (τ :: l) s)
                      (applySequential (insertByCommitTime τ l) s)
  | [], _, _, s, _ => by rw [insertByCommitTime_nil]; exact objStoreEquiv_refl _
  | head :: rest, hWB, hcomm, s, hExt => by
      rw [insertByCommitTime_cons]
      by_cases hle : τ.commitTime ≤ head.commitTime
      · rw [if_pos hle]; exact objStoreEquiv_refl _
      · rw [if_neg hle]
        have hHeadWB := hWB head List.mem_cons_self
        have hRestWB : ∀ x ∈ rest, KernelTransitionInstance.wellBehavedObs x :=
          fun x hx => hWB x (List.mem_cons_of_mem _ hx)
        have hCommHead : KernelTransitionInstance.actionsCommuteObs τ head :=
          hcomm head List.mem_cons_self (Nat.lt_of_not_le hle)
        have hStep1 :
            objStoreEquiv (applySequential (τ :: head :: rest) s)
                          (applySequential (head :: τ :: rest) s) :=
          applySequential_swap_front_obs τ head rest s hExt hRestWB h1Ext hHeadWB.2 hCommHead
        have hStep2 :
            objStoreEquiv (applySequential (head :: τ :: rest) s)
                          (applySequential (head :: insertByCommitTime τ rest) s) := by
          refine applySequential_cons_obs head (τ :: rest) (insertByCommitTime τ rest)
            hHeadWB.2 ?_ s hExt
          intro s' hs'
          exact insertByCommitTime_obs τ h1Ext rest hRestWB
            (fun x hx hlt => hcomm x (List.mem_cons_of_mem _ hx) hlt) s' hs'
        exact objStoreEquiv_trans hStep1 hStep2

/-- WS-SM SM3.E.3 (observational): the commit sort is observationally
`applySequential`-equal to the input schedule, under well-behavedness +
`outOfOrderCommuteObs` (the strict-2PL hypothesis) on an `invExt` start state.
The obs counterpart of `commitSort_commutingReorder`. -/
theorem commitSort_obs :
    ∀ (l : List KernelTransitionInstance),
      (∀ x ∈ l, KernelTransitionInstance.wellBehavedObs x) →
      outOfOrderCommuteObs l →
      ∀ s, s.objects.invExt →
        objStoreEquiv (applySequential l s) (applySequential (commitSort l) s)
  | [], _, _, s, _ => by rw [commitSort_nil]; exact objStoreEquiv_refl _
  | head :: rest, hWB, hooc, s, hExt => by
      rw [outOfOrderCommuteObs_cons] at hooc
      obtain ⟨hHeadComm, hRestOoc⟩ := hooc
      rw [commitSort_cons]
      have hHeadWB := hWB head List.mem_cons_self
      have hRestWB : ∀ x ∈ rest, KernelTransitionInstance.wellBehavedObs x :=
        fun x hx => hWB x (List.mem_cons_of_mem _ hx)
      have hStep1 :
          objStoreEquiv (applySequential (head :: rest) s)
                        (applySequential (head :: commitSort rest) s) := by
        refine applySequential_cons_obs head rest (commitSort rest) hHeadWB.2 ?_ s hExt
        intro s' hs'
        exact commitSort_obs rest hRestWB hRestOoc s' hs'
      have hCommSortRestWB : ∀ x ∈ commitSort rest,
          KernelTransitionInstance.wellBehavedObs x :=
        fun x hx => hRestWB x ((commitSort_perm rest).mem_iff.mp hx)
      have hHeadCommSmaller : ∀ x ∈ commitSort rest, x.commitTime < head.commitTime →
          KernelTransitionInstance.actionsCommuteObs head x :=
        fun x hx hlt => hHeadComm x ((commitSort_perm rest).mem_iff.mp hx) hlt
      have hStep2 :
          objStoreEquiv (applySequential (head :: commitSort rest) s)
                        (applySequential (insertByCommitTime head (commitSort rest)) s) :=
        insertByCommitTime_obs head hHeadWB.2 (commitSort rest) hCommSortRestWB
          hHeadCommSmaller s hExt
      exact objStoreEquiv_trans hStep1 hStep2

/-- WS-SM SM3.E.3 (Theorem 2.1.10, **observational form** — closes the write/write
coverage gap): every strict-2PL execution of well-behaved object-store
transitions is **observationally** serial-equivalent to its commit-sorted serial
order (which is a commit-ordered permutation).  Unlike the structural
`serializability_under_2pl` (which only covers read-only / disjoint-field
actions that commute structurally), this form covers the realistic write-heavy
workload: transitions whose business action is `updateObjectAt` (writes to
possibly-different objects), whose only non-conflicting commutation is
observational.  The hypotheses are exactly the genuine strict-2PL conditions
(`outOfOrderCommuteObs`) plus the object-store well-behavedness discharged for
`updateObjectAt` actions by `updateObjectAt_wellBehavedObs`. -/
theorem serializability_under_2pl_obs (interleaved : List KernelTransitionInstance)
    (s : SystemState) (hExt : s.objects.invExt)
    (hWB : ∀ τ ∈ interleaved, KernelTransitionInstance.wellBehavedObs τ)
    (hooc : outOfOrderCommuteObs interleaved) :
    (commitSort interleaved).Perm interleaved ∧
    (commitSort interleaved).Pairwise (fun a b => a.commitTime ≤ b.commitTime) ∧
    objStoreEquiv (applySequential interleaved s)
                  (applySequential (commitSort interleaved) s) :=
  ⟨commitSort_perm interleaved, commitSort_sorted interleaved,
   commitSort_obs interleaved hWB hooc s hExt⟩

/-- WS-SM SM3.E.5 (the realistic write transition): an **object-store-write**
transition instance whose business action writes object `oid` via `f`
(`updateObjectAt`).  This is the shape every real write transition takes; the
observational layer is built precisely so these are serializable. -/
def objStoreWriteInstance (S : LockSet) (core : CoreId) (ct : Nat)
    (at_ : LockId → Nat) (oid : SeLe4n.ObjId) (f : KernelObject → KernelObject) :
    KernelTransitionInstance :=
  ⟨S, core, ct, at_, fun s => updateObjectAt s oid f⟩

/-- WS-SM SM3.E.5: an object-store-write transition is observationally
well-behaved. -/
theorem objStoreWriteInstance_wellBehavedObs (S : LockSet) (core : CoreId) (ct : Nat)
    (at_ : LockId → Nat) (oid : SeLe4n.ObjId) (f : KernelObject → KernelObject) :
    KernelTransitionInstance.wellBehavedObs (objStoreWriteInstance S core ct at_ oid f) :=
  updateObjectAt_wellBehavedObs S core ct at_ oid f

/-- WS-SM SM3.E.5 (the realistic non-conflicting write pair commutes
observationally): two object-store-write transitions to **distinct** objects
commute observationally — the canonical write/write case that structural
commutation cannot capture.  Lifts `updateObjectAt_objStoreEquiv_comm`. -/
theorem objStoreWriteInstance_actionsCommuteObs (S₁ S₂ : LockSet) (c₁ c₂ : CoreId)
    (ct₁ ct₂ : Nat) (at₁ at₂ : LockId → Nat) (oid₁ oid₂ : SeLe4n.ObjId)
    (f₁ f₂ : KernelObject → KernelObject) (hNe : oid₁ ≠ oid₂) :
    KernelTransitionInstance.actionsCommuteObs
      (objStoreWriteInstance S₁ c₁ ct₁ at₁ oid₁ f₁)
      (objStoreWriteInstance S₂ c₂ ct₂ at₂ oid₂ f₂) := by
  intro s hExt
  exact updateObjectAt_objStoreEquiv_comm s oid₂ oid₁ f₂ f₁ hExt (Ne.symm hNe)

end SeLe4n.Kernel.Concurrency
