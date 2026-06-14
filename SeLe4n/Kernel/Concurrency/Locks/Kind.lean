-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.A: PRODUCTION (LANDED).  The SM0.I LockKind + LockId total order
-- entered the production import closure when the live `.call` dispatch was wired
-- through the cross-core call (`API.dispatchWithCap{,Checked}` →
-- `endpointCallCrossCoreDispatch`), which acquires the per-object lock-set under
-- this hierarchy.  (Former "STATUS: staged" marker replaced with this landing
-- note per the implement-the-improvement rule.)

import SeLe4n.Prelude

/-!
# WS-SM SM0.I — LockKind, LockId, and the lock-acquisition total order

The deadlock-freedom theorem for SM3 (`per-object fine locks`) requires
a **total order** on the set of all lock identifiers so that a thread
acquiring multiple locks always grabs them in a strictly-increasing
sequence.  Wait-for cycles cannot form when every cycle would imply a
strict-decrease somewhere on the lock ladder.

`LockKind` partitions the lock universe into ten kinds in a fixed
hierarchical order (lower level = acquired first).  `LockId` pairs a
kind with the identifier of the locked object.  The lexicographic
order on `(kind.level, objId.val)` is total, decidable, reflexive,
transitive, and antisymmetric — the four order properties downstream
SM3 lemmas appeal to.

This module is foundational and depends only on `SeLe4n.Prelude` (for
`ObjId`); SM3 lock primitive theorems extend it with acquisition
predicates and ladder enforcement.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM0.I.1 — LockKind hierarchy (10-level total order)
-- ============================================================================

/-- WS-SM SM0.I: lock kinds partitioning the set of kernel locks into
ten layers in a fixed hierarchical order.

The ordering reflects *acquisition discipline*: a thread holding a
lock at level `k` may only request locks at level `> k`.  Level 0
(`objStore`) is the coarsest lock — the RobinHood object store
itself.  Level 9 (`page`) is the finest — individual page frames.

The ten kinds enumerate every fine-grained kernel resource that
SM3..SM7 will protect: capability nodes, thread control blocks,
endpoints, notifications, replies, scheduling contexts, VSpace
roots, and page frames.

The ordering is intentionally **not alphabetical**: it is the
acquisition discipline downstream proofs require.  Adding a new lock
kind in a future workstream requires:

1. Inserting it at the correct level (preserving the existing
   strict-monotone ordering — the gap between two adjacent existing
   levels can be closed, but inserting at level `n` must shift every
   subsequent kind's level up by 1).
2. Re-deriving `level_strictMono`, `level_surjective`, and
   `level_bounded` (each reduces to a `decide` after the level
   function is updated).
3. Updating downstream SM3 ladder-acquisition theorems that pattern-
   match on `LockKind`. -/
inductive LockKind where
  | objStore         -- the RobinHood hash table (level 0, coarsest)
  | untyped          -- Untyped memory regions   (level 1)
  | cnode            -- Capability nodes         (level 2)
  | tcb              -- Thread control blocks    (level 3)
  | endpoint         -- IPC endpoints            (level 4)
  | notification     -- Notification objects     (level 5)
  | reply            -- Reply objects            (level 6)
  | schedContext     -- Scheduling contexts      (level 7)
  | vspaceRoot       -- VSpace roots / ASIDs     (level 8)
  | page             -- Page frames              (level 9, finest)
  deriving DecidableEq, Repr, Inhabited

/-- WS-SM SM0.I: extract the numeric level of a lock kind for the
lexicographic order.  Strict-monotone (`level_strictMono`) so the
order on `LockKind` lifts to a strict order on levels. -/
def LockKind.level : LockKind → Nat
  | .objStore       => 0
  | .untyped        => 1
  | .cnode          => 2
  | .tcb            => 3
  | .endpoint       => 4
  | .notification   => 5
  | .reply          => 6
  | .schedContext   => 7
  | .vspaceRoot     => 8
  | .page           => 9

/-- WS-SM SM0.I: distinct kinds have distinct levels.  Pairwise
distinctness via 10-way `cases` analysis discharged by `decide` on
the resulting numeric inequalities. -/
theorem LockKind.level_strictMono :
    ∀ k₁ k₂ : LockKind, k₁ ≠ k₂ → k₁.level ≠ k₂.level := by
  intro k₁ k₂ h
  cases k₁ <;> cases k₂ <;> simp_all <;> decide

/-- WS-SM SM0.I: every level `0..9` is realised by some kind.
Surjectivity is the second half of the bijection between
`LockKind` and `Fin 10` (the first half being `level_bounded`).

Proof by direct `match` on the natural number plus its bound — the
ten in-range cases each give an existential witness; the
`n + 10` case is excluded by `omega` from the `< 10` hypothesis. -/
theorem LockKind.level_surjective :
    ∀ n : Nat, n < 10 → ∃ k : LockKind, k.level = n := by
  intro n hn
  match n, hn with
  | 0, _ => exact ⟨.objStore, rfl⟩
  | 1, _ => exact ⟨.untyped, rfl⟩
  | 2, _ => exact ⟨.cnode, rfl⟩
  | 3, _ => exact ⟨.tcb, rfl⟩
  | 4, _ => exact ⟨.endpoint, rfl⟩
  | 5, _ => exact ⟨.notification, rfl⟩
  | 6, _ => exact ⟨.reply, rfl⟩
  | 7, _ => exact ⟨.schedContext, rfl⟩
  | 8, _ => exact ⟨.vspaceRoot, rfl⟩
  | 9, _ => exact ⟨.page, rfl⟩
  | n + 10, h => exact absurd h (by omega)

/-- WS-SM SM0.I: every kind's level is `< 10`.  Discharged by case
analysis on `LockKind`. -/
theorem LockKind.level_bounded :
    ∀ k : LockKind, k.level < 10 := by
  intro k; cases k <;> decide

/-- WS-SM SM0.I: lift a kind to a `Fin 10` index.  Bundles `level`
with its `level_bounded` witness so consumers obtain a structurally
in-range index. -/
def LockKind.toFin (k : LockKind) : Fin 10 := ⟨k.level, k.level_bounded⟩

/-- WS-SM SM0.I: `toFin` agrees with `level` on the underlying value. -/
theorem LockKind.toFin_val (k : LockKind) : k.toFin.val = k.level := rfl

-- ============================================================================
-- SM0.I.2 — LockId and lexicographic total order
-- ============================================================================

/-- WS-SM SM0.I: identifier for a single lockable kernel object.
Pairs the kind (which determines the level for the lexicographic
order) with the `ObjId` of the underlying object.

The lexicographic order on `(kind.level, objId.val)` makes every
pair of `LockId`s comparable, so SM3's deadlock-freedom proof can
appeal to a single total order without per-kind branching. -/
structure LockId where
  kind  : LockKind
  objId : SeLe4n.ObjId
  deriving DecidableEq, Repr, Inhabited

/-- WS-SM SM0.I: lexicographic less-than-or-equal on `LockId`.
Compare by `kind.level` first, breaking ties by `objId.val`. -/
instance : LE LockId where
  le l₁ l₂ :=
    l₁.kind.level < l₂.kind.level ∨
    (l₁.kind.level = l₂.kind.level ∧ l₁.objId.val ≤ l₂.objId.val)

/-- WS-SM SM0.I: strict less-than derived from the `LE` instance. -/
instance : LT LockId where
  lt l₁ l₂ := l₁ ≤ l₂ ∧ l₁ ≠ l₂

/-- WS-SM SM0.I: the `LE` instance is decidable.  Lifts the
underlying `Nat` decidability to the lexicographic shape. -/
instance LockId.decLE (l₁ l₂ : LockId) : Decidable (l₁ ≤ l₂) := by
  show Decidable (l₁.kind.level < l₂.kind.level ∨
    (l₁.kind.level = l₂.kind.level ∧ l₁.objId.val ≤ l₂.objId.val))
  exact inferInstance

/-- WS-SM SM0.I: the `LT` instance is decidable. -/
instance LockId.decLT (l₁ l₂ : LockId) : Decidable (l₁ < l₂) := by
  show Decidable (l₁ ≤ l₂ ∧ l₁ ≠ l₂)
  exact inferInstance

/-- WS-SM SM0.I: every pair of `LockId`s is comparable.  This is the
totality property SM3's ladder-acquisition argument requires:
acquiring two locks `l₁` and `l₂` always proceeds in the order given
by `≤`, never stalled by an "incomparable" verdict. -/
theorem LockId.le_total : ∀ l₁ l₂ : LockId, l₁ ≤ l₂ ∨ l₂ ≤ l₁ := by
  intro l₁ l₂
  by_cases h₁ : l₁.kind.level < l₂.kind.level
  · exact Or.inl (Or.inl h₁)
  · by_cases h₂ : l₂.kind.level < l₁.kind.level
    · exact Or.inr (Or.inl h₂)
    · -- Levels are equal — break the tie with `objId.val`.
      have hkind : l₁.kind.level = l₂.kind.level :=
        Nat.le_antisymm (Nat.le_of_not_lt h₂) (Nat.le_of_not_lt h₁)
      by_cases hobj : l₁.objId.val ≤ l₂.objId.val
      · exact Or.inl (Or.inr ⟨hkind, hobj⟩)
      · exact Or.inr (Or.inr ⟨hkind.symm, Nat.le_of_lt (Nat.lt_of_not_le hobj)⟩)

/-- WS-SM SM0.I: reflexivity — every `LockId` is `≤` itself. -/
theorem LockId.le_refl : ∀ l : LockId, l ≤ l := by
  intro l
  exact Or.inr ⟨rfl, Nat.le_refl _⟩

/-- WS-SM SM0.I: transitivity of the lexicographic order.  Case
analysis on the disjunction structure of the two hypotheses (4
cases): both strict-level, h₁ strict + h₂ tied, h₁ tied + h₂ strict,
both tied. -/
theorem LockId.le_trans :
    ∀ l₁ l₂ l₃ : LockId, l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃ := by
  intro l₁ l₂ l₃ h₁ h₂
  rcases h₁ with hLt₁ | ⟨hEq₁, hObj₁⟩
  · -- l₁.level < l₂.level
    rcases h₂ with hLt₂ | ⟨hEq₂, _hObj₂⟩
    · -- < then < ⇒ <
      exact Or.inl (Nat.lt_trans hLt₁ hLt₂)
    · -- < then = ⇒ <
      exact Or.inl (hEq₂ ▸ hLt₁)
  · -- l₁.level = l₂.level, l₁.objId ≤ l₂.objId
    rcases h₂ with hLt₂ | ⟨hEq₂, hObj₂⟩
    · -- = then < ⇒ <
      exact Or.inl (hEq₁ ▸ hLt₂)
    · -- = then = ⇒ = and obj transitive
      exact Or.inr ⟨hEq₁.trans hEq₂, Nat.le_trans hObj₁ hObj₂⟩

/-- WS-SM SM0.I: antisymmetry of the lexicographic order — if
`l₁ ≤ l₂` and `l₂ ≤ l₁` both hold, then `l₁ = l₂`.

Proof outline: from each `≤` we either get a strict-level inequality
or an equality plus an `objId.val` inequality.  The two strict-level
inequalities `l₁.level < l₂.level` and `l₂.level < l₁.level` cannot
both hold (`Nat.lt_irrefl` after combination), so both hypotheses
must be in the tied-level branch.  That gives `l₁.level = l₂.level`
and `l₁.objId.val = l₂.objId.val` (by `Nat.le_antisymm`).  The level
equality lifts to `l₁.kind = l₂.kind` via `level_strictMono`'s
contrapositive; combined with `objId.val` equality and `ObjId`
extensionality, we conclude `l₁ = l₂`. -/
theorem LockId.le_antisymm :
    ∀ l₁ l₂ : LockId, l₁ ≤ l₂ → l₂ ≤ l₁ → l₁ = l₂ := by
  intro l₁ l₂ h₁ h₂
  -- Reject the two strict-level disjuncts: they would yield
  -- `l₁.level < l₂.level ∧ l₂.level < l₁.level`, contradiction.
  rcases h₁ with hLt₁ | ⟨hEq₁, hObj₁⟩
  · rcases h₂ with hLt₂ | ⟨hEq₂, _⟩
    · exact absurd (Nat.lt_trans hLt₁ hLt₂) (Nat.lt_irrefl _)
    · exact absurd (hEq₂ ▸ hLt₁) (Nat.lt_irrefl _)
  · rcases h₂ with hLt₂ | ⟨hEq₂, hObj₂⟩
    · exact absurd (hEq₁ ▸ hLt₂) (Nat.lt_irrefl _)
    · -- Both tied: levels equal, objIds equal.
      have hKindLevel : l₁.kind.level = l₂.kind.level := hEq₁
      have hObjEq : l₁.objId.val = l₂.objId.val := Nat.le_antisymm hObj₁ hObj₂
      -- Lift level equality to kind equality via the strict-monotone
      -- contrapositive: distinct kinds → distinct levels.  Lean 4.28
      -- exposes the contradiction-from-decidable bridge as
      -- `Decidable.byContradiction`; `LockKind` is `DecidableEq` via
      -- `deriving`, so the instance resolves automatically.
      have hKindEq : l₁.kind = l₂.kind := by
        apply Decidable.byContradiction
        intro hNe
        exact LockKind.level_strictMono _ _ hNe hKindLevel
      -- Lift objId.val equality to ObjId equality via the
      -- `ofNat_toNat` round-trip (`@[inline] ofNat n := ⟨n⟩`,
      -- `toNat id := id.val`).  Rewriting both sides through
      -- `ofNat ∘ toNat = id` reduces the goal to `ofNat a = ofNat b`,
      -- which `congr` resolves from `a = b`.
      have hObjIdEq : l₁.objId = l₂.objId := by
        have h1 : l₁.objId = SeLe4n.ObjId.ofNat l₁.objId.val :=
          (SeLe4n.ObjId.ofNat_toNat l₁.objId).symm
        have h2 : l₂.objId = SeLe4n.ObjId.ofNat l₂.objId.val :=
          (SeLe4n.ObjId.ofNat_toNat l₂.objId).symm
        rw [h1, h2, hObjEq]
      -- Conclude by `LockId` extensionality on the two field equalities.
      -- Manual expansion avoids `simp_all`'s recursion-depth blow-up
      -- on the destructured form.
      obtain ⟨k₁, o₁⟩ := l₁
      obtain ⟨k₂, o₂⟩ := l₂
      simp only at hKindEq hObjIdEq
      subst hKindEq
      subst hObjIdEq
      rfl

/-- WS-SM SM0.I: smart constructor — build a `LockId` from a kind
and an ObjId without raw record syntax. -/
def LockId.mk' (k : LockKind) (o : SeLe4n.ObjId) : LockId :=
  { kind := k, objId := o }

/-- WS-SM SM0.I / SM3.D.3: irreflexivity of the strict order — no
`LockId` is strictly below itself.  Immediate from the `LT` definition
(`l₁ < l₂ := l₁ ≤ l₂ ∧ l₁ ≠ l₂`): `l < l` would require `l ≠ l`.

This is the half of `lockOrder_strict` (SM3.D.3) that closes the
deadlock-freedom cycle: a wait-for cycle forces some lock strictly
below itself, contradicting this. -/
theorem LockId.lt_irrefl (l : LockId) : ¬ (l < l) := fun h => h.2 rfl

/-- WS-SM SM0.I / SM3.D.3: transitivity of the strict order.

`l₁ < l₂` and `l₂ < l₃` give `l₁ ≤ l₃` by `le_trans`; the distinctness
`l₁ ≠ l₃` follows because `l₁ = l₃` would force `l₁ = l₂` (via
`le_antisymm` on `l₁ ≤ l₂` and `l₂ ≤ l₃ = l₁`), contradicting `l₁ ≠ l₂`.

This is the second half of `lockOrder_strict` (SM3.D.3) and the engine
of the N-core wait-graph acyclicity proof (`waitGraph_acyclic_under_2pl`):
the wanted-lock measure strictly increases along every wait edge, so a
closed walk would chain `w < w` by transitivity. -/
theorem LockId.lt_trans (l₁ l₂ l₃ : LockId) (h₁ : l₁ < l₂) (h₂ : l₂ < l₃) :
    l₁ < l₃ :=
  ⟨LockId.le_trans _ _ _ h₁.1 h₂.1,
   fun hEq => h₁.2 (LockId.le_antisymm _ _ h₁.1 (hEq ▸ h₂.1))⟩

/-- WS-SM SM0.I / SM3.D.3: asymmetry of the strict order — `l₁ < l₂`
rules out `l₂ < l₁`.  Derived from irreflexivity + transitivity.  This
is the form the two-core deadlock-freedom theorem
(`deadlockFreedom_under_2pl_and_ordering`) applies directly to the two
mutually-blocked cores. -/
theorem LockId.lt_asymm (l₁ l₂ : LockId) (h : l₁ < l₂) : ¬ (l₂ < l₁) :=
  fun h' => LockId.lt_irrefl l₁ (LockId.lt_trans _ _ _ h h')

/-- WS-SM SM0.I: trichotomy — for any two `LockId`s, exactly one of
`l₁ < l₂`, `l₁ = l₂`, or `l₂ < l₁` holds.  Useful for SM3 ladder
arguments that case-split on the relative position of two locks. -/
theorem LockId.lt_trichotomy : ∀ l₁ l₂ : LockId, l₁ < l₂ ∨ l₁ = l₂ ∨ l₂ < l₁ := by
  intro l₁ l₂
  by_cases hEq : l₁ = l₂
  · exact Or.inr (Or.inl hEq)
  · rcases LockId.le_total l₁ l₂ with hLe | hLe
    · exact Or.inl ⟨hLe, hEq⟩
    · refine Or.inr (Or.inr ⟨hLe, ?_⟩)
      intro h; exact hEq h.symm

end SeLe4n.Kernel.Concurrency
