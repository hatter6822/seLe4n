-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM3.D deadlock-freedom)

import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Locks.LockSet
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions
import SeLe4n.Kernel.Concurrency.Locks.LockSet2PL
import SeLe4n.Kernel.Concurrency.Locks.LockSetHeld

/-!
# WS-SM SM3.D — Deadlock-freedom under two-phase locking + lock ordering

This module proves the architectural keystone of SM3: **no execution of
the verified microkernel can deadlock**, given that every kernel
transition (a) acquires its locks under the two-phase-locking discipline
(`withLockSet`, SM3.C) and (b) acquires them in the SM0.I `LockId`
total order (`lockAcquireSequence`, SM3.B).

## The abstract execution model (plan §5.4 `KernelExecution`)

`KernelExecution` is the abstract per-core lock-state snapshot that the
deadlock-freedom theorems reason about.  For each `CoreId` it records:

* `held c`     — the list of `LockId`s the core currently holds, and
* `blocked c`  — the `LockId` the core is currently blocked waiting for
                 (`none` if the core is running, not blocked).

`blockedAt` and `heldBy` (plan §5.4 SM3.D.1) lift these fields to
predicates.  The model is deliberately *minimal*: it captures exactly
the wait-for relationship needed to state and prove deadlock-freedom,
without committing to a particular scheduler or interleaving semantics.
SM3.D §7 grounds the abstract model in the concrete SM3.B/SM3.C
`lockAcquireSequence` discipline (see `CorePrefixOf`).

## The two hypotheses (plan §5.4 SM3.D.4)

The main theorem takes two hypotheses, each carrying *distinct,
non-redundant* content:

* `executionAcquiresInLockIdOrder` — a blocked core's held locks are all
  `≤` (in the `LockId` total order) the lock it is blocked on.  This is
  the operational meaning of "acquires in `LockId` order": a core only
  ever reaches for a lock ranked at-or-above everything it already holds
  (it acquired a prefix of its ascending sequence and is reaching for the
  next element).

* `executionFollows2PL` — a blocked core does **not** already hold the
  lock it is blocked on.  This is the two-phase-locking *growing-phase*
  property: in the growing phase a core only requests *new* locks; it
  never re-requests a lock it already holds.

Neither hypothesis alone suffices.  Ordering gives `held ≤ wanted`; 2PL
upgrades that to the *strict* `held < wanted` (since `wanted ∉ held`
rules out equality).  The strictness is what closes the deadlock cycle.
SM3.D §7 (`execution_satisfies_hypotheses_of_all_prefix`) discharges both
hypotheses from the SM3.B canonical-sort discipline, so they are
*consequences* of `withLockSet`, not arbitrary assumptions.

## What is proved

* **SM3.D.3** `lockOrder_strict` — the `LockId` strict order is
  irreflexive and transitive (the engine of every cycle contradiction).
* **SM3.D.4** `deadlockFreedom_under_2pl_and_ordering` (Theorem 2.1.9) —
  no two cores can be mutually blocked.
* **SM3.D.5** `waitGraph_acyclic_under_2pl` — the dual, N-core form: the
  wait-for graph among blocked cores is acyclic (a DAG).  This subsumes
  the two-core theorem (`noDeadlock_of_waitGraph_acyclic`).
* **SM3.D.6** `boundedWait_under_2pl` — the worst-case wait of a
  transition holding lock-set `S` is bounded by
  `maxLockSetSize · (numCores − 1) · T_cs`.

## Relationship to SM3.C

SM3.C's `DynamicChainExtension` proved a *special case* — two cores
walking PIP blocking chains cannot mutually wait
(`dynamic_chain_no_mutual_wait`), using the `ObjId.val` order on the
all-`.tcb` chain locks.  SM3.D generalises to **arbitrary lock sets** and
**arbitrary numbers of cores**, using the full `LockId` total order
(kind-level lexicographic, SM0.I).  The dynamic-chain result is the
TCB-only instance of SM3.D's general theorem.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- §1 — The abstract `KernelExecution` model (plan §5.4 SM3.D.1)
-- ============================================================================

/-- WS-SM SM3.D.1 (plan §5.4): an abstract per-core lock-state snapshot.

The deadlock-freedom theorems are stated and proved over this model.
For each core it records the locks the core currently holds (`held`) and
the lock it is currently blocked waiting for (`blocked`, `none` when the
core is running).

The model is intentionally minimal: it captures exactly the wait-for
relationship the deadlock argument needs.  It is grounded in the concrete
SM3.B/SM3.C lock discipline by §7 (`CorePrefixOf`). -/
structure KernelExecution where
  /-- The locks each core currently holds. -/
  held : CoreId → List LockId
  /-- The lock each core is currently blocked waiting for (`none` if the
      core is not blocked). -/
  blocked : CoreId → Option LockId

/-- WS-SM SM3.D.1 (plan §5.4): core `c` is **blocked at** lock `l`. -/
def blockedAt (e : KernelExecution) (c : CoreId) (l : LockId) : Prop :=
  e.blocked c = some l

/-- WS-SM SM3.D.1 (plan §5.4): lock `l` is **held by** core `c`. -/
def heldBy (e : KernelExecution) (c : CoreId) (l : LockId) : Prop :=
  l ∈ e.held c

/-- WS-SM SM3.D.1: `blockedAt` is decidable (`Option` equality). -/
instance (e : KernelExecution) (c : CoreId) (l : LockId) :
    Decidable (blockedAt e c l) := by unfold blockedAt; exact inferInstance

/-- WS-SM SM3.D.1: `heldBy` is decidable (`List` membership). -/
instance (e : KernelExecution) (c : CoreId) (l : LockId) :
    Decidable (heldBy e c l) := by unfold heldBy; exact inferInstance

-- ============================================================================
-- §2 — The 2PL + ordering hypotheses + the ladder invariant (plan §5.4)
-- ============================================================================

/-- WS-SM SM3.D.4 helper: the per-core two-phase-locking property — if `c`
is blocked on a lock `w`, then `c` does not already hold `w`.

This is the growing-phase discipline: a core requests only *new* locks in
its growing phase, never re-requesting a lock it holds.  Factored into a
per-core predicate so the decidability instance and the proofs both stay
match-on-one-`Option` simple. -/
def coreFollows2PL (e : KernelExecution) (c : CoreId) : Prop :=
  match e.blocked c with
  | some w => w ∉ e.held c
  | none => True

/-- WS-SM SM3.D.4 helper: the per-core lock-ordering property — if `c` is
blocked on `w`, every lock `c` holds is `≤ w` in the `LockId` total order.

This is the operational meaning of "acquires in `LockId` order": the held
locks are an ascending prefix and `w` is the next (≥) lock requested. -/
def coreAcquiresInOrder (e : KernelExecution) (c : CoreId) : Prop :=
  match e.blocked c with
  | some w => ∀ l ∈ e.held c, l ≤ w
  | none => True

/-- WS-SM SM3.D.4: `coreFollows2PL` is decidable. -/
instance (e : KernelExecution) (c : CoreId) : Decidable (coreFollows2PL e c) := by
  unfold coreFollows2PL; cases e.blocked c <;> exact inferInstance

/-- WS-SM SM3.D.4: `coreAcquiresInOrder` is decidable. -/
instance (e : KernelExecution) (c : CoreId) : Decidable (coreAcquiresInOrder e c) := by
  unfold coreAcquiresInOrder; cases e.blocked c <;> exact inferInstance

/-- WS-SM SM3.D.4 (plan §5.4): the execution follows the two-phase-locking
discipline — no core blocks on a lock it already holds. -/
def executionFollows2PL (e : KernelExecution) : Prop :=
  ∀ c : CoreId, coreFollows2PL e c

/-- WS-SM SM3.D.4 (plan §5.4): the execution acquires locks in `LockId`
ascending order — every blocked core's held locks are `≤` its wanted lock. -/
def executionAcquiresInLockIdOrder (e : KernelExecution) : Prop :=
  ∀ c : CoreId, coreAcquiresInOrder e c

/-- WS-SM SM3.D.4: `executionFollows2PL` is decidable (finite `∀` over
`CoreId = Fin numCores`, decidable per-core body). -/
instance (e : KernelExecution) : Decidable (executionFollows2PL e) :=
  inferInstanceAs (Decidable (∀ c : CoreId, coreFollows2PL e c))

/-- WS-SM SM3.D.4: `executionAcquiresInLockIdOrder` is decidable. -/
instance (e : KernelExecution) : Decidable (executionAcquiresInLockIdOrder e) :=
  inferInstanceAs (Decidable (∀ c : CoreId, coreAcquiresInOrder e c))

/-- WS-SM SM3.D.4 (the **ladder invariant** — plan §3.7 "all locks in
`H_c` have `LockId < l₁`"): under 2PL + ordering, every lock a blocked
core holds is *strictly* below the lock it is blocked on.

This is the single fact every deadlock-freedom theorem below rests on.
Its proof is the precise point where the two hypotheses combine:
ordering gives `l ≤ w`; 2PL gives `w ∉ held`, hence `l ≠ w` (because
`l ∈ held`); together `l < w`. -/
theorem ladder_of_2pl_and_order (e : KernelExecution)
    (h2pl : executionFollows2PL e)
    (hOrder : executionAcquiresInLockIdOrder e)
    (c : CoreId) (w : LockId) (hBlocked : e.blocked c = some w)
    (l : LockId) (hHeld : l ∈ e.held c) : l < w := by
  have h2c := h2pl c
  have hoc := hOrder c
  unfold coreFollows2PL at h2c
  unfold coreAcquiresInOrder at hoc
  rw [hBlocked] at h2c hoc
  -- h2c : w ∉ e.held c ;  hoc : ∀ l ∈ e.held c, l ≤ w
  exact ⟨hoc l hHeld, fun hEq => h2c (hEq ▸ hHeld)⟩

-- ============================================================================
-- §3 — SM3.D.3 — `lockOrder_strict`
-- ============================================================================

/-- WS-SM SM3.D.3 (plan §5.4): the `LockId` strict order is irreflexive
and transitive.  Both halves are proved in `Kind.lean`
(`LockId.lt_irrefl`, `LockId.lt_trans`) from the lexicographic-order
properties; this bundles them as the single SM3.D.3 deliverable.

(`Irreflexive` / `Transitive` are mathlib typeclasses unavailable in the
core-only seLe4n toolchain, so the conjuncts are stated with explicit
`∀`.) -/
theorem lockOrder_strict :
    (∀ l : LockId, ¬ (l < l)) ∧
    (∀ l₁ l₂ l₃ : LockId, l₁ < l₂ → l₂ < l₃ → l₁ < l₃) :=
  ⟨LockId.lt_irrefl, LockId.lt_trans⟩

/-- WS-SM SM3.D.3: a binary relation is irreflexive when no element relates
to itself.  seLe4n is mathlib-free, so the `Irreflexive` order-class the
plan §5.4 quotes does not exist in the core toolchain; this namespaced
abbreviation reproduces its meaning so `lockOrder_strict_classes` can state
the SM3.D.3 deliverable in the plan's exact `Irreflexive ∧ Transitive`
form. -/
abbrev Irreflexive {α : Type _} (r : α → α → Prop) : Prop := ∀ a, ¬ r a a

/-- WS-SM SM3.D.3: a binary relation is transitive when it composes.
Mathlib-free counterpart of the plan's `Transitive` order-class. -/
abbrev Transitive {α : Type _} (r : α → α → Prop) : Prop :=
  ∀ {a b c}, r a b → r b c → r a c

/-- WS-SM SM3.D.3 (plan §5.4, exact `Irreflexive ∧ Transitive` form):
restatement of `lockOrder_strict` in the plan's quoted notation, using the
namespaced `Irreflexive` / `Transitive` abbreviations above.  Definitionally
the same content as `lockOrder_strict`; provided so a reader matching the
plan text finds the literal signature. -/
theorem lockOrder_strict_classes :
    Irreflexive (· < · : LockId → LockId → Prop) ∧
    Transitive (· < · : LockId → LockId → Prop) :=
  ⟨LockId.lt_irrefl, fun h₁ h₂ => LockId.lt_trans _ _ _ h₁ h₂⟩

-- ============================================================================
-- §4 — SM3.D.1 `noDeadlock` + SM3.D.4 main theorem (Theorem 2.1.9)
-- ============================================================================

/-- WS-SM SM3.D.1 (plan §5.4): the deadlock-freedom predicate — there is
no pair of distinct cores that are mutually blocked (each blocked on a
lock the *other* holds).  This is the two-core deadlock cycle, the
smallest possible deadlock. -/
def noDeadlock (e : KernelExecution) : Prop :=
  ¬ (∃ (c₁ c₂ : CoreId) (l₁ l₂ : LockId),
      c₁ ≠ c₂ ∧
      blockedAt e c₁ l₁ ∧
      blockedAt e c₂ l₂ ∧
      heldBy e c₂ l₁ ∧
      heldBy e c₁ l₂)

/-- WS-SM SM3.D.1 helper: per-pair mutual-block test.  Decidable because
both locks are pinned by the `blocked` fields (no free existential over
the infinite `LockId` type). -/
def mutualBlocked (e : KernelExecution) (c₁ c₂ : CoreId) : Prop :=
  match e.blocked c₁, e.blocked c₂ with
  | some l₁, some l₂ => l₁ ∈ e.held c₂ ∧ l₂ ∈ e.held c₁
  | _, _ => False

/-- WS-SM SM3.D.1: `mutualBlocked` is decidable. -/
instance (e : KernelExecution) (c₁ c₂ : CoreId) :
    Decidable (mutualBlocked e c₁ c₂) := by
  unfold mutualBlocked
  cases e.blocked c₁ <;> cases e.blocked c₂ <;> exact inferInstance

/-- WS-SM SM3.D.1: a finite, decidable reformulation of `noDeadlock` — no
distinct pair of cores is mutually blocked.  Equivalent to `noDeadlock`
(`noDeadlock_iff_dec`); used to derive the `Decidable (noDeadlock e)`
instance. -/
def noDeadlockDec (e : KernelExecution) : Prop :=
  ∀ c₁ c₂ : CoreId, c₁ ≠ c₂ → ¬ mutualBlocked e c₁ c₂

/-- WS-SM SM3.D.1: `noDeadlockDec` is decidable (finite `∀` over `CoreId`
pairs, decidable per-pair body). -/
instance (e : KernelExecution) : Decidable (noDeadlockDec e) :=
  inferInstanceAs (Decidable (∀ _ _ : CoreId, _))

/-- WS-SM SM3.D.1: the spec form `noDeadlock` and the decidable form
`noDeadlockDec` agree.  The existential's `l₁ l₂` are pinned by the
`blocked` fields, so the `∃ l₁ l₂ : LockId` collapses to the `match` in
`mutualBlocked`. -/
theorem noDeadlock_iff_dec (e : KernelExecution) :
    noDeadlock e ↔ noDeadlockDec e := by
  unfold noDeadlock noDeadlockDec mutualBlocked blockedAt heldBy
  constructor
  · intro h c₁ c₂ hne hmb
    apply h
    revert hmb
    cases hb1 : e.blocked c₁ with
    | none => intro hmb; exact hmb.elim
    | some l₁ =>
      cases hb2 : e.blocked c₂ with
      | none => intro hmb; exact hmb.elim
      | some l₂ =>
        intro hmb
        exact ⟨c₁, c₂, l₁, l₂, hne, hb1, hb2, hmb.1, hmb.2⟩
  · intro h ⟨c₁, c₂, l₁, l₂, hne, hb1, hb2, hm1, hm2⟩
    apply h c₁ c₂ hne
    rw [hb1, hb2]
    exact ⟨hm1, hm2⟩

/-- WS-SM SM3.D.1 (inventory item 11 `noDeadlock_definition_decidable`):
`noDeadlock` is decidable, via the finite reformulation. -/
instance noDeadlock_definition_decidable (e : KernelExecution) :
    Decidable (noDeadlock e) :=
  decidable_of_iff _ (noDeadlock_iff_dec e).symm

/-- WS-SM SM3.D.4 (plan §5.4, **Theorem 2.1.9**):
`deadlockFreedom_under_2pl_and_ordering`.  No execution that follows 2PL
and acquires in `LockId` order can reach a two-core deadlock.

Proof (plan §3.7): suppose `c₁ ≠ c₂` are mutually blocked — `c₁` blocked
at `l₁` while holding `l₂`, `c₂` blocked at `l₂` while holding `l₁`.  The
ladder invariant on `c₁` (blocked at `l₁`, holds `l₂`) gives `l₂ < l₁`;
on `c₂` (blocked at `l₂`, holds `l₁`) gives `l₁ < l₂`.  By asymmetry of
the `LockId` strict order, `l₂ < l₁` and `l₁ < l₂` is impossible. -/
theorem deadlockFreedom_under_2pl_and_ordering (e : KernelExecution)
    (h2pl : executionFollows2PL e)
    (hOrder : executionAcquiresInLockIdOrder e) :
    noDeadlock e := by
  rintro ⟨c₁, c₂, l₁, l₂, _hne, hb₁, hb₂, hh₂, hh₁⟩
  -- hb₁ : blockedAt e c₁ l₁ ; hh₁ : heldBy e c₁ l₂ ⟹ l₂ < l₁.
  have hA : l₂ < l₁ := ladder_of_2pl_and_order e h2pl hOrder c₁ l₁ hb₁ l₂ hh₁
  -- hb₂ : blockedAt e c₂ l₂ ; hh₂ : heldBy e c₂ l₁ ⟹ l₁ < l₂.
  have hB : l₁ < l₂ := ladder_of_2pl_and_order e h2pl hOrder c₂ l₂ hb₂ l₁ hh₂
  exact LockId.lt_asymm _ _ hA hB

-- ============================================================================
-- §5 — SM3.D.5 — Wait-graph acyclicity (the N-core dual form)
-- ============================================================================

/-- WS-SM SM3.D.5: core `c` **waits for** core `c'` — `c` is blocked on a
lock that `c'` holds.  The directed edge of the wait-for graph. -/
def waitsForCore (e : KernelExecution) (c c' : CoreId) : Prop :=
  ∃ l, e.blocked c = some l ∧ l ∈ e.held c'

/-- WS-SM SM3.D.5: the **blocked** wait-for edge — `c` waits for `c'` and
`c'` is *also* blocked.  Only blocked cores can be part of a deadlock
cycle: a running core that holds a contended lock will release it.  This
is the edge relation of the deadlock-relevant wait graph. -/
def blockedWaitsFor (e : KernelExecution) (c c' : CoreId) : Prop :=
  (e.blocked c').isSome = true ∧ waitsForCore e c c'

/-- WS-SM SM3.D.5: `waitsForCore` is decidable. -/
instance (e : KernelExecution) (c c' : CoreId) :
    Decidable (waitsForCore e c c') := by
  unfold waitsForCore
  cases hb : e.blocked c with
  | none => exact isFalse (by rintro ⟨l, hl, _⟩; simp at hl)
  | some l =>
      by_cases hmem : l ∈ e.held c'
      · exact isTrue ⟨l, rfl, hmem⟩
      · exact isFalse (by
          rintro ⟨l', hl', hmem'⟩
          injection hl' with hEq
          rw [hEq] at hmem
          exact hmem hmem')

/-- WS-SM SM3.D.5: `blockedWaitsFor` is decidable. -/
instance (e : KernelExecution) (c c' : CoreId) :
    Decidable (blockedWaitsFor e c c') := by
  unfold blockedWaitsFor; exact inferInstance

/-- WS-SM SM3.D.5: the transitive closure of a core-relation.  A
mathlib-free `TransGen`: `ReachesPlus R c c'` holds iff there is a
nonempty `R`-path from `c` to `c'`. -/
inductive ReachesPlus (R : CoreId → CoreId → Prop) : CoreId → CoreId → Prop where
  /-- A single edge. -/
  | base {a b : CoreId} : R a b → ReachesPlus R a b
  /-- Prepend an edge to a path. -/
  | step {a b c : CoreId} : R a b → ReachesPlus R b c → ReachesPlus R a c

/-- WS-SM SM3.D.5: a core-relation `R` is **acyclic** when no core reaches
itself in the transitive closure.  Standard DAG definition. -/
def Acyclic (R : CoreId → CoreId → Prop) : Prop :=
  ∀ c : CoreId, ¬ ReachesPlus R c c

/-- WS-SM SM3.D.5 (plan §5.4): the **wait graph** of an execution — the
directed graph whose edges are the blocked wait-for relation. -/
def waitGraph (e : KernelExecution) : CoreId → CoreId → Prop :=
  blockedWaitsFor e

/-- WS-SM SM3.D.5 helper: a single blocked wait-for edge strictly
increases the wanted lock.  If `c` (blocked at `lc`) waits for `c'`
(blocked at `lc'`), then `lc < lc'`: `c` holds nothing above `lc` is
false — rather, `lc ∈ held c'` and `c'`'s ladder gives `lc < lc'`. -/
theorem blockedWaitsFor_wanted_lt (e : KernelExecution)
    (h2pl : executionFollows2PL e) (hOrder : executionAcquiresInLockIdOrder e)
    {c c' : CoreId} (h : blockedWaitsFor e c c') :
    ∃ lc lc', e.blocked c = some lc ∧ e.blocked c' = some lc' ∧ lc < lc' := by
  obtain ⟨hc'some, l, hbl, hmem⟩ := h
  obtain ⟨lc', hbc'⟩ := Option.isSome_iff_exists.mp hc'some
  -- c blocked at l, l ∈ held c', c' blocked at lc' ⟹ l < lc' (ladder on c').
  exact ⟨l, lc', hbl, hbc', ladder_of_2pl_and_order e h2pl hOrder c' lc' hbc' l hmem⟩

/-- WS-SM SM3.D.5 helper: along any nonempty path in the wait graph the
wanted lock strictly increases (both endpoints are blocked, and the
end's wanted lock is `>` the start's).  Induction on the closure;
single steps use `blockedWaitsFor_wanted_lt`, composition uses
`LockId.lt_trans`. -/
theorem reachesPlus_wanted_lt (e : KernelExecution)
    (h2pl : executionFollows2PL e) (hOrder : executionAcquiresInLockIdOrder e)
    {c c' : CoreId} (h : ReachesPlus (waitGraph e) c c') :
    ∃ lc lc', e.blocked c = some lc ∧ e.blocked c' = some lc' ∧ lc < lc' := by
  induction h with
  | base hb => exact blockedWaitsFor_wanted_lt e h2pl hOrder hb
  | step hb _ ih =>
      obtain ⟨lc, lmid, hbc, hbmid, hlt⟩ := blockedWaitsFor_wanted_lt e h2pl hOrder hb
      obtain ⟨lmid', lc', hbmid', hbc', hlt'⟩ := ih
      -- hbmid : blocked b = some lmid ; hbmid' : blocked b = some lmid' ⟹ lmid = lmid'.
      rw [hbmid'] at hbmid
      injection hbmid with hEq
      subst hEq
      exact ⟨lc, lc', hbc, hbc', LockId.lt_trans _ _ _ hlt hlt'⟩

/-- WS-SM SM3.D.5 (plan §5.4): `waitGraph_acyclic_under_2pl`.  The wait
graph of any 2PL + ordered execution is acyclic — the dual, N-core form
of deadlock-freedom.

Proof: a cycle `ReachesPlus (waitGraph e) c c` would force the wanted
lock of `c` strictly below itself (`reachesPlus_wanted_lt` gives
`lc < lc'` with `lc = lc'` both equal to `e.blocked c`), contradicting
`LockId.lt_irrefl`. -/
theorem waitGraph_acyclic_under_2pl (e : KernelExecution)
    (h2pl : executionFollows2PL e)
    (hOrder : executionAcquiresInLockIdOrder e) :
    Acyclic (waitGraph e) := by
  intro c hCycle
  obtain ⟨lc, lc', hb, hb', hlt⟩ := reachesPlus_wanted_lt e h2pl hOrder hCycle
  rw [hb] at hb'
  injection hb' with hEq
  subst hEq
  exact LockId.lt_irrefl lc hlt

/-- WS-SM SM3.D.5 (coherence corollary): wait-graph acyclicity implies the
two-core `noDeadlock`.  A mutual block between `c₁` and `c₂` would close a
2-cycle `c₁ → c₂ → c₁` in the wait graph.

This witnesses that SM3.D.4 (`deadlockFreedom_under_2pl_and_ordering`) and
SM3.D.5 (`waitGraph_acyclic_under_2pl`) are consistent: the small (2-core)
theorem follows from the general (N-core) one.  Both are also proved
directly from the ladder invariant. -/
theorem noDeadlock_of_waitGraph_acyclic (e : KernelExecution)
    (hAcyclic : Acyclic (waitGraph e)) : noDeadlock e := by
  rintro ⟨c₁, c₂, l₁, l₂, hne, hb₁, hb₂, hh₂, hh₁⟩
  -- Edge c₁ → c₂: c₁ blocked at l₁, l₁ ∈ held c₂, c₂ blocked at l₂.
  have hEdge₁₂ : waitGraph e c₁ c₂ :=
    ⟨by rw [hb₂]; rfl, l₁, hb₁, hh₂⟩
  -- Edge c₂ → c₁: c₂ blocked at l₂, l₂ ∈ held c₁, c₁ blocked at l₁.
  have hEdge₂₁ : waitGraph e c₂ c₁ :=
    ⟨by rw [hb₁]; rfl, l₂, hb₂, hh₁⟩
  -- Compose into a self-cycle c₁ → c₂ → c₁.
  exact hAcyclic c₁ (ReachesPlus.step hEdge₁₂ (ReachesPlus.base hEdge₂₁))

-- ============================================================================
-- §5b — Mode-aware (conflict) wait graph (incorporates AccessMode.conflicts)
-- ============================================================================
--
-- §5's `blockedWaitsFor` treats ANY held-lock overlap as a wait edge,
-- regardless of access mode.  That is a *conservative over-approximation*:
-- two cores both holding a lock in READ mode do not actually block each
-- other (`AccessMode.conflicts .read .read = false`).  This section adds the
-- realistic, mode-aware wait edge `conflictWaitsFor`, which only fires when
-- the requested mode genuinely conflicts with a held mode (SM3.B's
-- `AccessMode.conflicts`).  Since every conflict edge is also a plain
-- `blockedWaitsFor` edge, the conflict-aware wait graph is a *subgraph* of
-- the plain one, so its acyclicity follows from `waitGraph_acyclic_under_2pl`
-- by monotonicity (`Acyclic_mono`).  This proves deadlock-freedom for the
-- faithful, mode-distinguishing wait graph without weakening any result.
--
-- The per-lock modes are supplied as auxiliary functions (`wantMode`,
-- `heldMode`) rather than carried inside `KernelExecution`, so the
-- plan-signature `noDeadlock` / `blockedAt` / `heldBy` (SM3.D.1, bare
-- `LockId`) and the §4/§5 theorems remain exactly as the plan specifies.

/-- WS-SM SM3.D.5: `ReachesPlus` is monotone in its edge relation — a path
under `R` is a path under any `R'` that contains every `R`-edge. -/
theorem ReachesPlus_mono {R R' : CoreId → CoreId → Prop}
    (h : ∀ a b, R a b → R' a b) {a b : CoreId}
    (hr : ReachesPlus R a b) : ReachesPlus R' a b := by
  induction hr with
  | base hab => exact ReachesPlus.base (h _ _ hab)
  | step hab _ ih => exact ReachesPlus.step (h _ _ hab) ih

/-- WS-SM SM3.D.5: acyclicity is **anti-monotone** in the edge relation —
removing edges cannot create a cycle.  If `R ⊆ R'` and the larger graph
`R'` is acyclic, the smaller graph `R` is acyclic too.  This is the lever
that lifts `waitGraph_acyclic_under_2pl` to every sub-relation of the wait
graph (in particular, the mode-aware conflict graph). -/
theorem Acyclic_mono {R R' : CoreId → CoreId → Prop}
    (hsub : ∀ a b, R a b → R' a b) (h : Acyclic R') : Acyclic R :=
  fun c hc => h c (ReachesPlus_mono hsub hc)

/-- WS-SM SM3.D.5b: the **mode-aware** wait edge.  Core `c` (requesting lock
`l` in mode `wantMode c`) waits for core `c'` only when `c'` is also blocked
AND holds `l` in a mode `heldMode c' l` that *conflicts* with `c`'s
request (SM3.B `AccessMode.conflicts`).  Two concurrent readers of `l` do
NOT induce an edge (`conflicts .read .read = false`), so this is the
realistic deadlock-relevant wait relation. -/
def conflictWaitsFor (e : KernelExecution)
    (wantMode : CoreId → AccessMode) (heldMode : CoreId → LockId → AccessMode)
    (c c' : CoreId) : Prop :=
  (e.blocked c').isSome = true ∧
  ∃ l, e.blocked c = some l ∧ l ∈ e.held c' ∧
    AccessMode.conflicts (wantMode c) (heldMode c' l) = true

/-- WS-SM SM3.D.5b: `conflictWaitsFor` is decidable.  The existential lock
is pinned by `e.blocked c`, so the `∃ l : LockId` collapses to a decidable
per-state test (no unbounded search). -/
instance (e : KernelExecution) (wm : CoreId → AccessMode)
    (hm : CoreId → LockId → AccessMode) (c c' : CoreId) :
    Decidable (conflictWaitsFor e wm hm c c') := by
  unfold conflictWaitsFor
  cases hb : e.blocked c with
  | none => exact isFalse (by rintro ⟨_, l, hl, _, _⟩; simp at hl)
  | some lc =>
      refine
        if hsome : (e.blocked c').isSome = true then
          if hmem : lc ∈ e.held c' then
            if hconf : AccessMode.conflicts (wm c) (hm c' lc) = true then
              isTrue ⟨hsome, lc, rfl, hmem, hconf⟩
            else isFalse ?_
          else isFalse ?_
        else isFalse ?_
      · rintro ⟨_, l, hl, _, hc⟩; injection hl with h; subst h; exact hconf hc
      · rintro ⟨_, l, hl, hm', _⟩; injection hl with h; subst h; exact hmem hm'
      · rintro ⟨hs, _⟩; exact hsome hs

/-- WS-SM SM3.D.5b: every mode-aware conflict edge is a plain
`blockedWaitsFor` edge — the conflict graph is a subgraph of the wait graph
(it just drops the `AccessMode.conflicts` conjunct). -/
theorem conflictWaitsFor_sub_blockedWaitsFor (e : KernelExecution)
    (wm : CoreId → AccessMode) (hm : CoreId → LockId → AccessMode) (c c' : CoreId) :
    conflictWaitsFor e wm hm c c' → blockedWaitsFor e c c' := by
  rintro ⟨hsome, l, hbl, hmem, _hconf⟩
  exact ⟨hsome, l, hbl, hmem⟩

/-- WS-SM SM3.D.5b (mode-aware deadlock-freedom): the **conflict** wait graph
of any 2PL + ordered execution is acyclic.  This is the realistic,
mode-distinguishing form of `waitGraph_acyclic_under_2pl` — it accounts for
`AccessMode.conflicts` (read–read overlaps create no edge).  Proved by
`Acyclic_mono`: the conflict graph is a subgraph of the plain wait graph
(`conflictWaitsFor_sub_blockedWaitsFor`), which is already acyclic. -/
theorem conflictWaitGraph_acyclic_under_2pl (e : KernelExecution)
    (wm : CoreId → AccessMode) (hm : CoreId → LockId → AccessMode)
    (h2pl : executionFollows2PL e)
    (hOrder : executionAcquiresInLockIdOrder e) :
    Acyclic (conflictWaitsFor e wm hm) :=
  Acyclic_mono (fun a b => conflictWaitsFor_sub_blockedWaitsFor e wm hm a b)
    (waitGraph_acyclic_under_2pl e h2pl hOrder)

-- ============================================================================
-- §6 — SM3.D.6 — Bounded-wait corollary
-- ============================================================================

/-- WS-SM SM3.D.6 (plan §5.4): the static worst-case lock-set size.  Per
plan §5.4, most transitions touch ≤ 4 locks; the worst-case IPC paths
(call/reply with donation) stay ≤ 8.  Every SM3.B `lockSet_<τ>`
declaration respects this bound (exercised in `DeadlockFreedomSuite`). -/
def maxLockSetSize : Nat := 8

/-- WS-SM SM3.D.6: per-lock worst-case wait.  Under FIFO RwLock fairness
(SM2.C) each lock is contended by at most `numCores − 1` other cores,
each for one critical section of cost `tCs`. -/
def perLockWaitCost (tCs : Nat) : Nat := (numCores - 1) * tCs

/-- WS-SM SM3.D.6: total worst-case wait for a transition holding lock-set
`S` — the sum, over the canonical acquisition sequence, of the per-lock
wait.  Modelled as a sum (rather than a bare product) so the bound has
genuine combinatorial content: it accumulates one `perLockWaitCost` per
lock actually acquired. -/
def totalWaitCost (S : LockSet) (tCs : Nat) : Nat :=
  (S.lockAcquireSequence.map (fun _ => perLockWaitCost tCs)).sum

/-- WS-SM SM3.D.6 helper: summing a constant over a list yields
`length · constant`. -/
theorem sum_const_map {α : Type _} (l : List α) (k : Nat) :
    (l.map (fun _ => k)).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons _ t ih => simp [List.map_cons, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

/-- WS-SM SM3.D.6: the total wait of lock-set `S` is exactly
`|S| · (numCores − 1) · T_cs`.  Collapses the sum-of-constants to the
product the plan quotes. -/
theorem totalWaitCost_eq (S : LockSet) (tCs : Nat) :
    totalWaitCost S tCs = S.size * ((numCores - 1) * tCs) := by
  unfold totalWaitCost perLockWaitCost
  rw [sum_const_map, LockSet.lockAcquireSequence_length]

/-- WS-SM SM3.D.6: the *combinatorial* worst-case bound — total wait of a
lock-set of size `≤ maxLockSetSize` is `≤ maxLockSetSize · (numCores−1) · T_cs`.
This is the uniform (contention-agnostic) bound; the contention-sensitive
`WCRT` below refines it (`WCRT_le_totalWaitCost`) and `boundedWait_under_2pl`
bounds `WCRT` directly. -/
theorem totalWaitCost_le_bound (S : LockSet) (tCs : Nat)
    (hSize : S.size ≤ maxLockSetSize) :
    totalWaitCost S tCs ≤ maxLockSetSize * ((numCores - 1) * tCs) := by
  rw [totalWaitCost_eq]
  exact Nat.mul_le_mul_right _ hSize

-- ============================================================================
-- §6b — Static lock-set size bounds (discharges the `maxLockSetSize` premise)
-- ============================================================================
--
-- The `maxLockSetSize` premise of `boundedWait_under_2pl` / the
-- `KernelOperation` invariant is not an assumption: every one of the 25
-- SM3.B per-transition `lockSet_<τ>` declarations is proved here to have
-- size ≤ `maxLockSetSize` (= 8).  The bounds factor through three generic
-- size lemmas about the SM3.B `LockSet` builders plus four "shape" helpers
-- (`size_le_1..4`) for the nested-`extendOpt` forms.

/-- WS-SM SM3.D.6b: `insertOrMerge` grows the lock-set size by at most 1
(the merge branch keeps the length; the prepend branch adds one key). -/
theorem insertOrMerge_size_le (S : LockSet) (l : LockId) (m : AccessMode) :
    (S.insertOrMerge l m).size ≤ S.size + 1 := by
  unfold LockSet.insertOrMerge LockSet.size
  split
  · simp [List.length_map]
  · simp

/-- WS-SM SM3.D.6b: `lockSetOfList` has size at most the length of its
source list (the fold of `insertOrMerge` over the empty set grows by ≤ 1
per element). -/
theorem lockSetOfList_size_le (pairs : List (LockId × AccessMode)) :
    (lockSetOfList pairs).size ≤ pairs.length := by
  unfold lockSetOfList
  have hgen : ∀ (ps : List (LockId × AccessMode)) (acc : LockSet),
      (ps.foldl (fun a p => a.insertOrMerge p.fst p.snd) acc).size
        ≤ acc.size + ps.length := by
    intro ps
    induction ps with
    | nil => intro acc; simp
    | cons p rest ih =>
        intro acc
        simp only [List.foldl_cons, List.length_cons]
        have h1 := ih (acc.insertOrMerge p.fst p.snd)
        have h2 := insertOrMerge_size_le acc p.fst p.snd
        omega
  have := hgen pairs LockSet.empty
  simpa [LockSet.size] using this

/-- WS-SM SM3.D.6b: `lockSetExtendOpt` grows the size by at most 1. -/
theorem lockSetExtendOpt_size_le (S : LockSet) (opt : Option (LockId × AccessMode)) :
    (lockSetExtendOpt S opt).size ≤ S.size + 1 := by
  cases opt with
  | none => exact Nat.le_succ _
  | some p => exact insertOrMerge_size_le S p.fst p.snd

/-- WS-SM SM3.D.6b shape helper: one optional extension over a base list. -/
theorem size_le_1 (L : List (LockId × AccessMode)) (o₁ : Option (LockId × AccessMode)) :
    (lockSetExtendOpt (lockSetOfList L) o₁).size ≤ L.length + 1 :=
  Nat.le_trans (lockSetExtendOpt_size_le _ _)
    (Nat.add_le_add_right (lockSetOfList_size_le _) 1)

/-- WS-SM SM3.D.6b shape helper: two optional extensions over a base list. -/
theorem size_le_2 (L : List (LockId × AccessMode))
    (o₁ o₂ : Option (LockId × AccessMode)) :
    (lockSetExtendOpt (lockSetExtendOpt (lockSetOfList L) o₁) o₂).size ≤ L.length + 2 := by
  refine Nat.le_trans (lockSetExtendOpt_size_le _ _) ?_
  refine Nat.le_trans (Nat.add_le_add_right (size_le_1 L o₁) 1) ?_
  omega

/-- WS-SM SM3.D.6b shape helper: three optional extensions over a base list. -/
theorem size_le_3 (L : List (LockId × AccessMode))
    (o₁ o₂ o₃ : Option (LockId × AccessMode)) :
    (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetOfList L) o₁) o₂) o₃).size
      ≤ L.length + 3 := by
  refine Nat.le_trans (lockSetExtendOpt_size_le _ _) ?_
  refine Nat.le_trans (Nat.add_le_add_right (size_le_2 L o₁ o₂) 1) ?_
  omega

/-- WS-SM SM3.D.6b shape helper: four optional extensions over a base list. -/
theorem size_le_4 (L : List (LockId × AccessMode))
    (o₁ o₂ o₃ o₄ : Option (LockId × AccessMode)) :
    (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
      (lockSetExtendOpt (lockSetOfList L) o₁) o₂) o₃) o₄).size ≤ L.length + 4 := by
  refine Nat.le_trans (lockSetExtendOpt_size_le _ _) ?_
  refine Nat.le_trans (Nat.add_le_add_right (size_le_3 L o₁ o₂ o₃) 1) ?_
  omega

/-- Local tactic shorthand: reduce a concrete `[…].length (+k)` to a numeral
and discharge the `≤ maxLockSetSize` goal. -/
local macro "size_bound" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_nil]; omega))

-- The 25 per-transition size bounds (one per SyscallId variant).
theorem lockSet_endpointSend_size_le (a : ThreadId) (b c : ObjId) (d : Option ThreadId) :
    (lockSet_endpointSend a b c d).size ≤ maxLockSetSize := by
  unfold lockSet_endpointSend maxLockSetSize
  exact Nat.le_trans (size_le_1 _ _) (by size_bound)

theorem lockSet_endpointReceive_size_le (a : ThreadId) (b c : ObjId) (d : Option ThreadId) :
    (lockSet_endpointReceive a b c d).size ≤ maxLockSetSize := by
  unfold lockSet_endpointReceive maxLockSetSize
  exact Nat.le_trans (size_le_1 _ _) (by size_bound)

theorem lockSet_endpointCall_size_le (a : ThreadId) (b c : ObjId)
    (d : Option ThreadId) (e : Option SchedContextId)
    (f : Option ReplyId := none) :
    (lockSet_endpointCall a b c d e f).size ≤ maxLockSetSize := by
  unfold lockSet_endpointCall maxLockSetSize
  -- PR #822 review: the server-first stashed reply is folded in as the outermost
  -- (third) optional, so the bound is the three-extension form (as `replyRecv`).
  exact Nat.le_trans (size_le_3 _ _ _ _) (by size_bound)

theorem lockSet_endpointReply_size_le (a : ThreadId) (b : ObjId) (c : ThreadId)
    (d : Option SchedContextId) (e : Option ThreadId) :
    (lockSet_endpointReply a b c d e).size ≤ maxLockSetSize := by
  unfold lockSet_endpointReply maxLockSetSize
  exact Nat.le_trans (size_le_2 _ _ _) (by size_bound)

theorem lockSet_replyRecv_size_le (a : ThreadId) (b : ObjId) (c : ThreadId)
    (d : ObjId) (e : Option ThreadId) (f : Option SchedContextId) (g : Option ThreadId) :
    (lockSet_replyRecv a b c d e f g).size ≤ maxLockSetSize := by
  unfold lockSet_replyRecv maxLockSetSize
  exact Nat.le_trans (size_le_3 _ _ _ _) (by size_bound)

theorem lockSet_notificationSignal_size_le (a : ThreadId) (b c : ObjId) (d : Option ThreadId) :
    (lockSet_notificationSignal a b c d).size ≤ maxLockSetSize := by
  unfold lockSet_notificationSignal maxLockSetSize
  exact Nat.le_trans (size_le_1 _ _) (by size_bound)

theorem lockSet_notificationWait_size_le (a : ThreadId) (b c : ObjId) :
    (lockSet_notificationWait a b c).size ≤ maxLockSetSize := by
  unfold lockSet_notificationWait maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_cspaceMint_size_le (a : ThreadId) (b c : ObjId) :
    (lockSet_cspaceMint a b c).size ≤ maxLockSetSize := by
  unfold lockSet_cspaceMint maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_cspaceCopy_size_le (a : ThreadId) (b c : ObjId) :
    (lockSet_cspaceCopy a b c).size ≤ maxLockSetSize := by
  unfold lockSet_cspaceCopy maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_cspaceMove_size_le (a : ThreadId) (b c : ObjId) :
    (lockSet_cspaceMove a b c).size ≤ maxLockSetSize := by
  unfold lockSet_cspaceMove maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_cspaceDelete_size_le (a : ThreadId) (b c : ObjId) :
    (lockSet_cspaceDelete a b c).size ≤ maxLockSetSize := by
  unfold lockSet_cspaceDelete maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_lifecycleRetype_size_le (a : ThreadId) (b c d : ObjId) :
    (lockSet_lifecycleRetype a b c d).size ≤ maxLockSetSize := by
  unfold lockSet_lifecycleRetype maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_vspaceMap_size_le (a : ThreadId) (b c : ObjId) :
    (lockSet_vspaceMap a b c).size ≤ maxLockSetSize := by
  unfold lockSet_vspaceMap maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_vspaceUnmap_size_le (a : ThreadId) (b c : ObjId) :
    (lockSet_vspaceUnmap a b c).size ≤ maxLockSetSize := by
  unfold lockSet_vspaceUnmap maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_serviceRegister_size_le (a : ThreadId) (b c : ObjId) :
    (lockSet_serviceRegister a b c).size ≤ maxLockSetSize := by
  unfold lockSet_serviceRegister maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_serviceRevoke_size_le (a : ThreadId) (b : ObjId) :
    (lockSet_serviceRevoke a b).size ≤ maxLockSetSize := by
  unfold lockSet_serviceRevoke maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_serviceQuery_size_le (a : ThreadId) (b : ObjId) :
    (lockSet_serviceQuery a b).size ≤ maxLockSetSize := by
  unfold lockSet_serviceQuery maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_schedContextConfigure_size_le (a : ThreadId) (b : ObjId)
    (c : SchedContextId) (d : Option ThreadId) :
    (lockSet_schedContextConfigure a b c d).size ≤ maxLockSetSize := by
  unfold lockSet_schedContextConfigure maxLockSetSize
  exact Nat.le_trans (size_le_1 _ _) (by size_bound)

theorem lockSet_schedContextBind_size_le (a : ThreadId) (b : ObjId)
    (c : SchedContextId) (d : ThreadId) :
    (lockSet_schedContextBind a b c d).size ≤ maxLockSetSize := by
  unfold lockSet_schedContextBind maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_schedContextUnbind_size_le (a : ThreadId) (b : ObjId)
    (c : SchedContextId) (d : ThreadId) :
    (lockSet_schedContextUnbind a b c d).size ≤ maxLockSetSize := by
  unfold lockSet_schedContextUnbind maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_tcbSuspend_size_le (a : ThreadId) (b : ObjId) (c : ThreadId)
    (d e : Option ObjId) (f : Option SchedContextId) (g : Option ThreadId) :
    (lockSet_tcbSuspend a b c d e f g).size ≤ maxLockSetSize := by
  unfold lockSet_tcbSuspend maxLockSetSize
  exact Nat.le_trans (size_le_4 _ _ _ _ _) (by size_bound)

theorem lockSet_tcbResume_size_le (a : ThreadId) (b : ObjId) (c : ThreadId) :
    (lockSet_tcbResume a b c).size ≤ maxLockSetSize := by
  unfold lockSet_tcbResume maxLockSetSize
  exact Nat.le_trans (lockSetOfList_size_le _) (by size_bound)

theorem lockSet_tcbSetPriority_size_le (a : ThreadId) (b : ObjId) (c : ThreadId)
    (d : Option SchedContextId) :
    (lockSet_tcbSetPriority a b c d).size ≤ maxLockSetSize := by
  unfold lockSet_tcbSetPriority maxLockSetSize
  exact Nat.le_trans (size_le_1 _ _) (by size_bound)

theorem lockSet_tcbSetMCPriority_size_le (a : ThreadId) (b : ObjId) (c : ThreadId)
    (d : Option SchedContextId) :
    (lockSet_tcbSetMCPriority a b c d).size ≤ maxLockSetSize := by
  unfold lockSet_tcbSetMCPriority maxLockSetSize
  exact Nat.le_trans (size_le_1 _ _) (by size_bound)

theorem lockSet_tcbSetIPCBuffer_size_le (a : ThreadId) (b : ObjId) (c : ThreadId)
    (d : Option ObjId) :
    (lockSet_tcbSetIPCBuffer a b c d).size ≤ maxLockSetSize := by
  unfold lockSet_tcbSetIPCBuffer maxLockSetSize
  exact Nat.le_trans (size_le_1 _ _) (by size_bound)

/-- WS-SM SM3.D.6b (aggregate): **every** one of the 25 SM3.B per-transition
`lockSet_<τ>` declarations has size `≤ maxLockSetSize`, for all arguments.
This discharges, once and for all, the size premise of
`boundedWait_under_2pl` / the `KernelOperation` invariant for the real
kernel transition surface — the bound is never vacuous. -/
theorem lockSetTransitions_within_bound :
    (∀ a b c d, (lockSet_endpointSend a b c d).size ≤ maxLockSetSize) ∧
    (∀ a b c d, (lockSet_endpointReceive a b c d).size ≤ maxLockSetSize) ∧
    (∀ a b c d e, (lockSet_endpointCall a b c d e).size ≤ maxLockSetSize) ∧
    (∀ a b c d e, (lockSet_endpointReply a b c d e).size ≤ maxLockSetSize) ∧
    (∀ a b c d e f g, (lockSet_replyRecv a b c d e f g).size ≤ maxLockSetSize) ∧
    (∀ a b c d, (lockSet_notificationSignal a b c d).size ≤ maxLockSetSize) ∧
    (∀ a b c, (lockSet_notificationWait a b c).size ≤ maxLockSetSize) ∧
    (∀ a b c, (lockSet_cspaceMint a b c).size ≤ maxLockSetSize) ∧
    (∀ a b c, (lockSet_cspaceCopy a b c).size ≤ maxLockSetSize) ∧
    (∀ a b c, (lockSet_cspaceMove a b c).size ≤ maxLockSetSize) ∧
    (∀ a b c, (lockSet_cspaceDelete a b c).size ≤ maxLockSetSize) ∧
    (∀ a b c d, (lockSet_lifecycleRetype a b c d).size ≤ maxLockSetSize) ∧
    (∀ a b c, (lockSet_vspaceMap a b c).size ≤ maxLockSetSize) ∧
    (∀ a b c, (lockSet_vspaceUnmap a b c).size ≤ maxLockSetSize) ∧
    (∀ a b c, (lockSet_serviceRegister a b c).size ≤ maxLockSetSize) ∧
    (∀ a b, (lockSet_serviceRevoke a b).size ≤ maxLockSetSize) ∧
    (∀ a b, (lockSet_serviceQuery a b).size ≤ maxLockSetSize) ∧
    (∀ a b c d, (lockSet_schedContextConfigure a b c d).size ≤ maxLockSetSize) ∧
    (∀ a b c d, (lockSet_schedContextBind a b c d).size ≤ maxLockSetSize) ∧
    (∀ a b c d, (lockSet_schedContextUnbind a b c d).size ≤ maxLockSetSize) ∧
    (∀ a b c d e f g, (lockSet_tcbSuspend a b c d e f g).size ≤ maxLockSetSize) ∧
    (∀ a b c, (lockSet_tcbResume a b c).size ≤ maxLockSetSize) ∧
    (∀ a b c d, (lockSet_tcbSetPriority a b c d).size ≤ maxLockSetSize) ∧
    (∀ a b c d, (lockSet_tcbSetMCPriority a b c d).size ≤ maxLockSetSize) ∧
    (∀ a b c d, (lockSet_tcbSetIPCBuffer a b c d).size ≤ maxLockSetSize) :=
  ⟨lockSet_endpointSend_size_le, lockSet_endpointReceive_size_le,
   lockSet_endpointCall_size_le, lockSet_endpointReply_size_le,
   lockSet_replyRecv_size_le, lockSet_notificationSignal_size_le,
   lockSet_notificationWait_size_le, lockSet_cspaceMint_size_le,
   lockSet_cspaceCopy_size_le, lockSet_cspaceMove_size_le,
   lockSet_cspaceDelete_size_le, lockSet_lifecycleRetype_size_le,
   lockSet_vspaceMap_size_le, lockSet_vspaceUnmap_size_le,
   lockSet_serviceRegister_size_le, lockSet_serviceRevoke_size_le,
   lockSet_serviceQuery_size_le, lockSet_schedContextConfigure_size_le,
   lockSet_schedContextBind_size_le, lockSet_schedContextUnbind_size_le,
   lockSet_tcbSuspend_size_le, lockSet_tcbResume_size_le,
   lockSet_tcbSetPriority_size_le, lockSet_tcbSetMCPriority_size_le,
   lockSet_tcbSetIPCBuffer_size_le⟩

-- ============================================================================
-- §6c — `KernelOperation` (a transition's lock footprint, size-bounded)
-- ============================================================================

/-- WS-SM SM3.D.6 (plan §5.4 `KernelOperation`): a kernel operation, modelled
by its static lock-set footprint together with a proof that the footprint
respects `maxLockSetSize`.  The size invariant is carried in the structure
so `WCRT` is bounded by construction; the §6b per-transition bounds are the
constructors' justification.  `lockSet_<τ>_size_le` smart constructors build
a `KernelOperation` from any real transition. -/
structure KernelOperation where
  /-- The transition's declared lock-set footprint (SM3.B). -/
  lockSet : LockSet
  /-- The footprint respects the static size bound (discharged per-transition
      in §6b). -/
  sizeWithinBound : lockSet.size ≤ maxLockSetSize

/-- WS-SM SM3.D.6: build the `KernelOperation` for an `endpointCall`.  The optional
`f` (PR #822 review) is the server-first stashed reply object the rendezvous links
(`linkServerFirstCaller`), so the deadlock/WCRT footprint accounts for the per-object
reply write-lock on a server-first `Call`. -/
def KernelOperation.ofEndpointCall (a : ThreadId) (b c : ObjId)
    (d : Option ThreadId) (e : Option SchedContextId)
    (f : Option ReplyId := none) : KernelOperation :=
  ⟨lockSet_endpointCall a b c d e f, lockSet_endpointCall_size_le a b c d e f⟩

/-- WS-SM SM3.D.6: build the `KernelOperation` for a `replyRecv` (a 7-arg,
3-extension transition — the deepest static footprint). -/
def KernelOperation.ofReplyRecv (a : ThreadId) (b : ObjId) (c : ThreadId)
    (d : ObjId) (e : Option ThreadId) (f : Option SchedContextId) (g : Option ThreadId) :
    KernelOperation :=
  ⟨lockSet_replyRecv a b c d e f g, lockSet_replyRecv_size_le a b c d e f g⟩

/-- WS-SM SM3.D.6: build the `KernelOperation` for a `tcbSuspend` (the
4-extension transition). -/
def KernelOperation.ofTcbSuspend (a : ThreadId) (b : ObjId) (c : ThreadId)
    (d e : Option ObjId) (f : Option SchedContextId) (g : Option ThreadId) :
    KernelOperation :=
  ⟨lockSet_tcbSuspend a b c d e f g, lockSet_tcbSuspend_size_le a b c d e f g⟩

-- ============================================================================
-- §6d — Worst-case response time (contention-sensitive)
-- ============================================================================

/-- WS-SM SM3.D.6: the cores other than `c`.  `otherCores_length_eq` proves
this has exactly `numCores − 1` elements (`allCores` is `Nodup` and contains
`c` exactly once). -/
def otherCores (c : CoreId) : List CoreId := allCores.filter (fun c' => decide (c' ≠ c))

/-- WS-SM SM3.D.6: `otherCores c` has `numCores − 1` elements.  Discharged by
`decide` over the finite `CoreId = Fin numCores`. -/
theorem otherCores_length_eq : ∀ c : CoreId, (otherCores c).length = numCores - 1 := by decide

/-- WS-SM SM3.D.6: the number of cores *other than* `c` that currently hold
lock `l` in execution `e` — the contention `c` faces for `l`.  This makes
`WCRT` genuinely depend on the execution's contention and on the requesting
core. -/
def contendersAhead (e : KernelExecution) (c : CoreId) (l : LockId) : Nat :=
  (otherCores c).countP (fun c' => decide (heldBy e c' l))

/-- WS-SM SM3.D.6: at most `numCores − 1` cores contend for any lock (only
the other cores can hold it).  `countP ≤ length = numCores − 1`. -/
theorem contendersAhead_le (e : KernelExecution) (c : CoreId) (l : LockId) :
    contendersAhead e c l ≤ numCores - 1 := by
  unfold contendersAhead
  rw [← otherCores_length_eq c]
  exact List.countP_le_length

/-- WS-SM SM3.D.6 helper: summing `f` over a list where each value is `≤ K`
is bounded by `length · K`. -/
theorem sum_le_length_mul {α : Type _} (L : List α) (f : α → Nat) (K : Nat)
    (h : ∀ x ∈ L, f x ≤ K) : (L.map f).sum ≤ L.length * K := by
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      have hhead := h a List.mem_cons_self
      have htail := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      omega

/-- WS-SM SM3.D.6 helper: pointwise-`≤` maps have `≤` sums. -/
theorem sum_map_le_sum_map {α : Type _} (L : List α) (f g : α → Nat)
    (h : ∀ x ∈ L, f x ≤ g x) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      have hhead := h a List.mem_cons_self
      have htail := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      omega

/-- WS-SM SM3.D.6 (plan §5.4 `WCRT`): the worst-case response time of
operation `op` on core `c` in execution `e` (in units where one critical
section costs `tCs`).  For each lock in `op`'s footprint, `c` waits behind
the cores currently contending for it (`contendersAhead`), each for one
critical section.  This genuinely depends on the execution `e` (contention)
and the core `c`. -/
def WCRT (e : KernelExecution) (c : CoreId) (op : KernelOperation) (tCs : Nat) : Nat :=
  (op.lockSet.lockAcquireSequence.map (fun p => contendersAhead e c p.fst * tCs)).sum

/-- WS-SM SM3.D.6 (plan §5.4, **full** `boundedWait_under_2pl`): under 2PL +
`LockId`-order acquisition, an execution is deadlock-free AND every kernel
operation's worst-case response time is bounded by
`maxLockSetSize · (numCores − 1) · T_cs`.

Both conjuncts are substantive and use distinct hypotheses:
* `noDeadlock e` follows from the 2PL + ordering hypotheses
  (`deadlockFreedom_under_2pl_and_ordering`) — without deadlock-freedom the
  wait would be unbounded (a deadlocked core waits forever), so this is the
  precondition that makes the WCRT bound *meaningful*;
* `WCRT e c op tCs ≤ …` follows from the per-lock contention bound
  (`contendersAhead_le`: ≤ `numCores − 1` per lock) summed over the
  footprint, capped by `op.sizeWithinBound` (≤ `maxLockSetSize` locks). -/
theorem boundedWait_under_2pl (e : KernelExecution) (c : CoreId)
    (op : KernelOperation) (tCs : Nat)
    (h2pl : executionFollows2PL e)
    (hOrder : executionAcquiresInLockIdOrder e) :
    noDeadlock e ∧ WCRT e c op tCs ≤ maxLockSetSize * ((numCores - 1) * tCs) := by
  refine ⟨deadlockFreedom_under_2pl_and_ordering e h2pl hOrder, ?_⟩
  unfold WCRT
  have hbound : (op.lockSet.lockAcquireSequence.map
      (fun p => contendersAhead e c p.fst * tCs)).sum
      ≤ op.lockSet.lockAcquireSequence.length * ((numCores - 1) * tCs) := by
    apply sum_le_length_mul
    intro p _
    exact Nat.mul_le_mul_right tCs (contendersAhead_le e c p.fst)
  rw [LockSet.lockAcquireSequence_length] at hbound
  exact Nat.le_trans hbound (Nat.mul_le_mul_right _ op.sizeWithinBound)

/-- WS-SM SM3.D.6: the contention-sensitive `WCRT` never exceeds the uniform
combinatorial `totalWaitCost` bound (each lock's actual contention is `≤
numCores − 1 = perLockWaitCost / tCs`).  Bridges the two bounded-wait models. -/
theorem WCRT_le_totalWaitCost (e : KernelExecution) (c : CoreId)
    (op : KernelOperation) (tCs : Nat) :
    WCRT e c op tCs ≤ totalWaitCost op.lockSet tCs := by
  unfold WCRT totalWaitCost perLockWaitCost
  apply sum_map_le_sum_map
  intro p _
  exact Nat.mul_le_mul_right tCs (contendersAhead_le e c p.fst)

-- ============================================================================
-- §7 — Grounding: the hypotheses are CONSEQUENCES of the SM3.B/C discipline
-- ============================================================================
--
-- §2's hypotheses (`executionFollows2PL`, `executionAcquiresInLockIdOrder`)
-- are not arbitrary assumptions.  This section discharges them from the
-- concrete SM3.B `lockAcquireSequence` canonical sort, realising the plan
-- §3.7 step "By 2PL, H_c is the prefix of c's lockAcquireSequence(S_c)
-- that has been acquired so far".  A core in the growing phase of
-- `withLockSet` holds a prefix of its transition's ascending acquisition
-- order and (if blocked) waits on the next lock — and that structure alone
-- forces both hypotheses.

/-- WS-SM SM3.D §7 helper: the projected acquisition order
(`acquireOrder S`, SM3.C.5) has no duplicate `LockId`s — it is a
permutation of `S.pairs.map (·.fst)`, which `S.hUniqueKeys` proves
`Nodup`. -/
theorem acquireOrder_nodup (S : LockSet) : (acquireOrder S).Nodup := by
  unfold acquireOrder
  exact ((LockSet.lockAcquireSequence_perm S).map _).nodup_iff.mpr S.hUniqueKeys

/-- WS-SM SM3.D §7 (plan §3.7 "H_c is the prefix"): a core is in the
**2PL growing-phase prefix** of `S` when its held set is exactly a prefix
of `S`'s canonical (`LockId`-ascending) acquisition order and it is
blocked on the next lock in that order.

`acquireOrder S = pre ++ w :: suf` splits the canonical order into the
acquired prefix `pre = held`, the next (blocked-on) lock `w`, and the
not-yet-acquired remainder `suf`. -/
def CorePrefixOf (e : KernelExecution) (c : CoreId) (S : LockSet) : Prop :=
  ∃ (pre suf : List LockId) (w : LockId),
    acquireOrder S = pre ++ w :: suf ∧
    e.held c = pre ∧
    e.blocked c = some w

/-- WS-SM SM3.D §7: a growing-phase prefix satisfies the per-core 2PL
property.  The blocked-on lock `w` is the splitting element of a `Nodup`
sequence, so `w ∉ pre = held`. -/
theorem coreFollows2PL_of_prefix (e : KernelExecution) (c : CoreId)
    (S : LockSet) (h : CorePrefixOf e c S) : coreFollows2PL e c := by
  obtain ⟨pre, suf, w, hSplit, hHeld, hBlocked⟩ := h
  unfold coreFollows2PL
  rw [hBlocked, hHeld]
  -- Goal (definitionally): w ∉ pre.
  have hND := acquireOrder_nodup S
  rw [hSplit, List.nodup_append] at hND
  obtain ⟨_, _, hDisj⟩ := hND
  intro hwpre
  exact (hDisj w hwpre w List.mem_cons_self) rfl

/-- WS-SM SM3.D §7: a growing-phase prefix satisfies the per-core ordering
property.  Every held lock precedes the blocked-on lock `w` in the
canonically-sorted sequence (`lockSet_acquired_in_order`, SM3.C.5), so
each is `≤ w`. -/
theorem coreAcquiresInOrder_of_prefix (e : KernelExecution) (c : CoreId)
    (S : LockSet) (h : CorePrefixOf e c S) : coreAcquiresInOrder e c := by
  obtain ⟨pre, suf, w, hSplit, hHeld, hBlocked⟩ := h
  unfold coreAcquiresInOrder
  rw [hBlocked, hHeld]
  -- Goal (definitionally): ∀ l ∈ pre, l ≤ w.
  have hPW := lockSet_acquired_in_order S
  rw [hSplit, List.pairwise_append] at hPW
  obtain ⟨_, _, hCross⟩ := hPW
  intro l hl
  exact hCross l hl w List.mem_cons_self

/-- WS-SM SM3.D §7 (the grounding theorem): if every blocked core is in a
2PL growing-phase prefix of *some* lock set, then the whole execution
satisfies both deadlock-freedom hypotheses.

This closes the loop: the abstract `executionFollows2PL` /
`executionAcquiresInLockIdOrder` hypotheses of SM3.D.4/D.5 are genuine
consequences of `withLockSet`'s 2PL discipline over the SM3.B canonical
sort — not assumptions bolted on for the proof.  A non-blocked core
trivially satisfies both per-core predicates (the `none` branch). -/
theorem execution_satisfies_hypotheses_of_all_prefix (e : KernelExecution)
    (h : ∀ c : CoreId, (e.blocked c).isSome = true → ∃ S, CorePrefixOf e c S) :
    executionFollows2PL e ∧ executionAcquiresInLockIdOrder e := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · -- 2PL: blocked ⟹ prefix ⟹ coreFollows2PL; not blocked ⟹ vacuous.
    cases hb : e.blocked c with
    | none => unfold coreFollows2PL; rw [hb]; trivial
    | some w =>
        obtain ⟨S, hPre⟩ := h c (by rw [hb]; rfl)
        exact coreFollows2PL_of_prefix e c S hPre
  · cases hb : e.blocked c with
    | none => unfold coreAcquiresInOrder; rw [hb]; trivial
    | some w =>
        obtain ⟨S, hPre⟩ := h c (by rw [hb]; rfl)
        exact coreAcquiresInOrder_of_prefix e c S hPre

-- ============================================================================
-- §7b — Bridge: the abstract `held` model ↔ the SM3.C concrete lock state
-- ============================================================================
--
-- §7 grounds the *hypotheses* in the SM3.B `lockAcquireSequence` discipline.
-- This section grounds the *model itself*: it connects the abstract
-- `heldBy` / `KernelExecution` to SM3.C's concrete `lockSetHeld` / `lockHeld`
-- (which read the actual per-object `RwLockState` of a `SystemState`).
-- `executionOfHeld` materialises the `KernelExecution` of a single core that
-- holds a lock set `S` and is blocked on `blk`; `lockSetHeld_realizes_heldBy`
-- proves that when the core *genuinely* holds `S` on a concrete state `s`
-- (SM3.C `lockSetHeld`), the abstract `heldBy` agrees and each declared lock
-- is concretely held (`lockHeld`).  This closes the abstract-model ↔
-- concrete-kernel gap for the holding side.  (The *blocked* side has no
-- concrete counterpart until SM5+ adds per-core blocked tracking to the
-- kernel state; `blk` is supplied externally as the next-to-acquire lock.)

/-- WS-SM SM3.D §7b: the `KernelExecution` of a single core `c` that holds
exactly the lock set `S` (its `held` is `S`'s canonical `LockId` sequence)
and is blocked on `blk`; all other cores are idle. -/
def executionOfHeld (c : CoreId) (S : LockSet) (blk : Option LockId) : KernelExecution :=
  { held := fun c' => if c' = c then acquireOrder S else [],
    blocked := fun c' => if c' = c then blk else none }

/-- WS-SM SM3.D §7b: in `executionOfHeld c S blk`, core `c` (abstractly)
holds exactly the `LockId`s of `S`. -/
theorem executionOfHeld_heldBy (c : CoreId) (S : LockSet) (blk : Option LockId)
    (l : LockId) :
    heldBy (executionOfHeld c S blk) c l ↔ l ∈ acquireOrder S := by
  unfold heldBy executionOfHeld
  simp

/-- WS-SM SM3.D §7b (the model↔kernel bridge): if core `c` genuinely holds
the lock set `S` on the concrete state `s` (SM3.C `lockSetHeld`), then for
every declared `(l, m) ∈ S`:
* the **concrete** lock is held — `lockHeld c l m s` (SM3.C, reads the actual
  per-object `RwLockState`), and
* the **abstract** model agrees — `heldBy (executionOfHeld c S blk) c l`.

This is the missing connection between the abstract `KernelExecution` the
deadlock theorems reason about and the concrete kernel lock state: a
deadlock-relevant "held" edge in the abstract model is realised by a genuine
`RwLockState` holding in the kernel. -/
theorem lockSetHeld_realizes_heldBy (c : CoreId) (S : LockSet)
    (s : SeLe4n.Model.SystemState) (blk : Option LockId)
    (hHeld : lockSetHeld c S s) :
    ∀ p ∈ S.pairs, lockHeld c p.fst p.snd s ∧ heldBy (executionOfHeld c S blk) c p.fst := by
  intro p hp
  refine ⟨hHeld p hp, ?_⟩
  rw [executionOfHeld_heldBy]
  unfold acquireOrder
  exact List.mem_map.mpr
    ⟨p, (LockSet.lockAcquireSequence_complete S p).mp ((LockSet.mem_def p S).mpr hp), rfl⟩

-- ============================================================================
-- §7c — `twoCorePathScenario` (plan §5.4 SM3.D.7)
-- ============================================================================

/-- WS-SM SM3.D.7 (plan §5.4): the canonical "two cores acquiring `{lo, hi}`"
scenario.  Two distinct cores both want the ordered pair `lo < hi`: core
`c₁` holds the lower lock `lo` and is blocked on `hi`; core `c₂` holds
nothing and is blocked on `lo`.  Under ascending acquisition this is the
deadlock-free interleaving — `c₁` will acquire `hi`, finish, and release,
after which `c₂` proceeds.  The plan's SM3.D.7 example existentially
witnesses such a scenario satisfying the 2PL + ordering hypotheses (see
`DeadlockFreedomSuite`). -/
def twoCorePathScenario (e : KernelExecution) (c₁ c₂ : CoreId) (lo hi : LockId) : Prop :=
  c₁ ≠ c₂ ∧ lo < hi ∧
  e.held c₁ = [lo] ∧ e.blocked c₁ = some hi ∧
  e.held c₂ = [] ∧ e.blocked c₂ = some lo

/-- WS-SM SM3.D.7: `twoCorePathScenario` is decidable. -/
instance (e : KernelExecution) (c₁ c₂ : CoreId) (lo hi : LockId) :
    Decidable (twoCorePathScenario e c₁ c₂ lo hi) := by
  unfold twoCorePathScenario; exact inferInstance

end SeLe4n.Kernel.Concurrency
