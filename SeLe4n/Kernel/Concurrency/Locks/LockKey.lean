-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Locks.RwLockState

/-!
# WS-LS LS1.1/LS1.2 — `LockKey`: every lock a bracket can declare, and its order

One key type for the table lock, the per-object locks (by `LockId`) and the
per-core scheduler queue locks; one total order over it, extending the SM0.I
`LockId` order and placing every object lock before every scheduler lock (as
`LockKey`'s did until LS1.2 retired it into this type); and the one sort,
`lockAcquireSequence`, a bracket acquires a footprint in.  `LockSet` is keyed
by it (LS1.2) and the ghost `LockState` (`Locks/LockState.lean`) is indexed by
it.  Foundational: it depends on `Kind` (for `LockId`) and `RwLockState` (for
`AccessMode`) only.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  The key
-- ============================================================================

/-- **WS-LS LS1.1**: every lock a bracket can declare.

`object` carries an SM0.I `LockId` of a *modeled* kind; the table lock is its
own constructor because it is one word however it was spelled
(`LockKey.ofLockId` folds every `.objStore`-kind `LockId` onto it).  The two
scheduler arms are the per-core run-queue and replenish-queue locks that
`LockKey` named until this row; they take the core directly. -/
inductive LockKey where
  /-- The object store's table lock — SM0.I level 0, acquired before every
  object lock. -/
  | objStore
  /-- A per-object lock, keyed by `(LockKind, ObjId)`. -/
  | object (l : LockId)
  /-- Core `c`'s run-queue lock. -/
  | runQueue (c : CoreId)
  /-- Core `c`'s replenish-queue lock. -/
  | replenishQueue (c : CoreId)
  deriving DecidableEq, Repr, Inhabited

namespace LockKey

/-- **LS1.1**: the acquisition order.  The table lock first; object locks by
the SM0.I lexicographic order; then the run-queue locks by core, then the
replenish-queue locks by core — every object lock before every scheduler lock,
as `LockKey.le` had it. -/
protected def le : LockKey → LockKey → Prop
  | .objStore,          _                  => True
  | .object _,          .objStore          => False
  | .object l₁,         .object l₂         => l₁ ≤ l₂
  | .object _,          .runQueue _        => True
  | .object _,          .replenishQueue _  => True
  | .runQueue _,        .objStore          => False
  | .runQueue _,        .object _          => False
  | .runQueue c₁,       .runQueue c₂       => c₁.val ≤ c₂.val
  | .runQueue _,        .replenishQueue _  => True
  | .replenishQueue _,  .objStore          => False
  | .replenishQueue _,  .object _          => False
  | .replenishQueue _,  .runQueue _        => False
  | .replenishQueue c₁, .replenishQueue c₂ => c₁.val ≤ c₂.val

/-- **LS1.2**: the kind of the lock a key names — the SM0.I ladder level it
sits at.  The permitted-kinds consistency layer (`LockSetTransitions.lean`
§`permittedKinds`) reads it; with the two scheduler kinds on the ladder it is
total. -/
def kind : LockKey → LockKind
  | .objStore => .objStore
  | .object l => l.kind
  | .runQueue _ => .runQueue
  | .replenishQueue _ => .replenishQueue

@[simp] theorem kind_objStore : LockKey.objStore.kind = LockKind.objStore := rfl
@[simp] theorem kind_object (l : LockId) : (LockKey.object l).kind = l.kind := rfl
@[simp] theorem kind_runQueue (c : CoreId) : (LockKey.runQueue c).kind = LockKind.runQueue := rfl
@[simp] theorem kind_replenishQueue (c : CoreId) :
    (LockKey.replenishQueue c).kind = LockKind.replenishQueue := rfl

/-- **LS1.2**: the object a key's lock lives on, when it lives on one.  Two
object keys at one `ObjId` that both resolve to a stored object resolve to the
same object, which is what the per-object establishment theorems
(`LockSetHeld.lean` §4) rule out by distinctness of this projection. -/
def objId? : LockKey → Option SeLe4n.ObjId
  | .object l => some l.objId
  | _ => none

@[simp] theorem objId?_objStore : LockKey.objStore.objId? = none := rfl
@[simp] theorem objId?_object (l : LockId) : (LockKey.object l).objId? = some l.objId := rfl
@[simp] theorem objId?_runQueue (c : CoreId) : (LockKey.runQueue c).objId? = none := rfl
@[simp] theorem objId?_replenishQueue (c : CoreId) :
    (LockKey.replenishQueue c).objId? = none := rfl

instance decLe (a b : LockKey) : Decidable (LockKey.le a b) := by
  cases a <;> cases b <;> simp only [LockKey.le] <;> infer_instance

instance : LE LockKey := ⟨LockKey.le⟩
instance : LT LockKey := ⟨fun a b => a ≤ b ∧ a ≠ b⟩
instance (a b : LockKey) : Decidable (a ≤ b) := decLe a b
instance (a b : LockKey) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a ≤ b ∧ a ≠ b))

/-- **LS1.1**: reflexivity, from each arm's own. -/
protected theorem le_refl (k : LockKey) : k ≤ k := by
  cases k with
  | objStore => exact True.intro
  | object l => exact LockId.le_refl l
  | runQueue c => exact Nat.le_refl c.val
  | replenishQueue c => exact Nat.le_refl c.val

/-- **LS1.1**: transitivity.  Every cross-arm edge points the same way
(table, objects, run queues, replenish queues), so no chain can turn back. -/
protected theorem le_trans {a b c : LockKey} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;>
    first
      | exact True.intro
      | exact (h₁ : False).elim
      | exact (h₂ : False).elim
      | exact LockId.le_trans _ _ _ h₁ h₂
      | exact Nat.le_trans h₁ h₂

/-- **LS1.1**: antisymmetry.  The cross-arm edges are strict, so two keys
below each other share an arm, where the arm's own antisymmetry applies. -/
protected theorem le_antisymm {a b : LockKey} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  cases a <;> cases b <;>
    first
      | rfl
      | exact (h₁ : False).elim
      | exact (h₂ : False).elim
      | exact congrArg LockKey.object (LockId.le_antisymm _ _ h₁ h₂)
      | exact congrArg LockKey.runQueue (Fin.ext (Nat.le_antisymm h₁ h₂))
      | exact congrArg LockKey.replenishQueue (Fin.ext (Nat.le_antisymm h₁ h₂))

/-- **LS1.1**: totality — the property the ladder argument needs: two keys
are always acquired in a definite order. -/
protected theorem le_total (a b : LockKey) : a ≤ b ∨ b ≤ a := by
  cases a <;> cases b <;>
    first
      | exact Or.inl True.intro
      | exact Or.inr True.intro
      | exact LockId.le_total _ _
      | exact Nat.le_total _ _

/-- **LS1.1**: strictness of `<` is decidable irreflexivity — stated as the
`lt` the sorts and the 2PL theorems use. -/
theorem lt_iff (a b : LockKey) : a < b ↔ a ≤ b ∧ a ≠ b := Iff.rfl

/-- **LS1.2**: the strict order is irreflexive, transitive and asymmetric —
`LockId.lt_irrefl` / `lt_trans` / `lt_asymm` for keys, which is what the
deadlock-freedom ladder (`Deadlock.lean`) reads once executions hold keys. -/
theorem lt_irrefl (k : LockKey) : ¬ (k < k) := fun h => h.2 rfl

theorem lt_trans (a b c : LockKey) (h₁ : a < b) (h₂ : b < c) : a < c :=
  ⟨LockKey.le_trans h₁.1 h₂.1,
   fun hEq => h₁.2 (LockKey.le_antisymm h₁.1 (hEq ▸ h₂.1))⟩

theorem lt_asymm (a b : LockKey) (h₁ : a < b) (h₂ : b < a) : False :=
  LockKey.lt_irrefl a (LockKey.lt_trans a b a h₁ h₂)

/-- **LS1.2**: the cross-arm edges of the ladder, in the strict form the
scheduler footprints' ordering proofs read: the table lock precedes every other
key, every object lock precedes every scheduler lock, and every run-queue lock
precedes every replenish-queue lock (`LockKey.object_lt_runQueue` and its
siblings until this row). -/
theorem objStore_lt_object (l : LockId) : LockKey.objStore < LockKey.object l :=
  ⟨True.intro, LockKey.noConfusion⟩

theorem objStore_lt_runQueue (c : CoreId) : LockKey.objStore < LockKey.runQueue c :=
  ⟨True.intro, LockKey.noConfusion⟩

theorem objStore_lt_replenishQueue (c : CoreId) :
    LockKey.objStore < LockKey.replenishQueue c :=
  ⟨True.intro, LockKey.noConfusion⟩

theorem object_lt_runQueue (l : LockId) (c : CoreId) : LockKey.object l < LockKey.runQueue c :=
  ⟨True.intro, LockKey.noConfusion⟩

theorem object_lt_replenishQueue (l : LockId) (c : CoreId) :
    LockKey.object l < LockKey.replenishQueue c :=
  ⟨True.intro, LockKey.noConfusion⟩

theorem runQueue_lt_replenishQueue (c d : CoreId) :
    LockKey.runQueue c < LockKey.replenishQueue d :=
  ⟨True.intro, LockKey.noConfusion⟩

/-- **LS1.2**: within one scheduler arm the order is the core order. -/
@[simp] theorem runQueue_le_runQueue_iff (c d : CoreId) :
    LockKey.runQueue c ≤ LockKey.runQueue d ↔ c.val ≤ d.val := Iff.rfl

@[simp] theorem replenishQueue_le_replenishQueue_iff (c d : CoreId) :
    LockKey.replenishQueue c ≤ LockKey.replenishQueue d ↔ c.val ≤ d.val := Iff.rfl

-- ----------------------------------------------------------------------------
-- The embedding of the object domain
-- ----------------------------------------------------------------------------

/-- **LS1.1**: the key a `LockId` names.  A `.objStore`-kind `LockId` is the
table lock whatever `ObjId` it carried — `SystemState.objStoreLock` is one
word and `lockHeld` routes every such id to it — so here it is one key.  This
is what LS1.2 retired `canonicalSchedLockOfObject` into: the canonical form
made a constructor, which is what lets a key have exactly one spelling. -/
def ofLockId (l : LockId) : LockKey :=
  if l.kind = LockKind.objStore then .objStore else .object l

@[simp] theorem ofLockId_objStore (oid : SeLe4n.ObjId) :
    ofLockId ⟨LockKind.objStore, oid⟩ = .objStore := by
  unfold ofLockId; rw [if_pos rfl]

@[simp] theorem ofLockId_of_ne (l : LockId) (h : l.kind ≠ LockKind.objStore) :
    ofLockId l = .object l := by
  unfold ofLockId; rw [if_neg h]

/-- A kind at level 0 is the table lock: the contrapositive of
`LockKind.level_strictMono` at the bottom of the ladder. -/
theorem _root_.SeLe4n.Kernel.Concurrency.LockKind.eq_objStore_of_level_eq_zero
    (k : LockKind) (h : k.level = 0) : k = LockKind.objStore := by
  cases k <;> first | rfl | exact absurd h (by decide)

/-- **LS1.1**: the embedding is monotone, so `LockKey`'s order *extends*
`LockId`'s: a footprint the object domain declared in ladder order is in
ladder order here too, and the table lock — level 0 — stays first. -/
theorem ofLockId_le_of_le {l₁ l₂ : LockId} (h : l₁ ≤ l₂) : ofLockId l₁ ≤ ofLockId l₂ := by
  by_cases h₁ : l₁.kind = LockKind.objStore
  · rw [show ofLockId l₁ = .objStore from by unfold ofLockId; rw [if_pos h₁]]
    exact True.intro
  · rw [ofLockId_of_ne l₁ h₁]
    by_cases h₂ : l₂.kind = LockKind.objStore
    · exfalso
      have hz : l₂.kind.level = 0 := by rw [h₂]; rfl
      rcases h with hLt | ⟨hEq, _⟩
      · rw [hz] at hLt; exact Nat.not_lt_zero _ hLt
      · exact h₁ (LockKind.eq_objStore_of_level_eq_zero _ (hEq.trans hz))
    · rw [ofLockId_of_ne l₂ h₂]
      exact h

/-- **LS1.1**: the embedding is injective off the table lock, which is all
the uniqueness a footprint's keys need: two modeled `LockId`s that map to one
key are one `LockId`. -/
theorem ofLockId_inj {l₁ l₂ : LockId} (h₁ : l₁.kind ≠ LockKind.objStore)
    (h : ofLockId l₁ = ofLockId l₂) : l₁ = l₂ := by
  rw [ofLockId_of_ne l₁ h₁] at h
  by_cases h₂ : l₂.kind = LockKind.objStore
  · rw [show ofLockId l₂ = .objStore from by unfold ofLockId; rw [if_pos h₂]] at h
    exact absurd h (by simp)
  · rw [ofLockId_of_ne l₂ h₂] at h
    exact LockKey.object.inj h

end LockKey

-- ============================================================================
-- §2  The acquisition sequence
-- ============================================================================

/-- **LS1.1**: the order a bracket acquires a footprint in — `LockKey`
ascending, whatever order it was declared or resolved in.  The one sort
`LockSet.lockAcquireSequence` and `LockSet.lockAcquireSequence` each
spelled for their own key; LS1.2 points both at it. -/
def lockAcquireSequence (pairs : List (LockKey × AccessMode)) :
    List (LockKey × AccessMode) :=
  pairs.mergeSort (fun p₁ p₂ => decide (p₁.fst ≤ p₂.fst))

private theorem leKey_bool_trans (a b c : LockKey × AccessMode) :
    decide (a.fst ≤ b.fst) = true → decide (b.fst ≤ c.fst) = true →
    decide (a.fst ≤ c.fst) = true := fun hab hbc =>
  decide_eq_true (LockKey.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))

private theorem leKey_bool_total (a b : LockKey × AccessMode) :
    (decide (a.fst ≤ b.fst) || decide (b.fst ≤ a.fst)) = true := by
  rcases LockKey.le_total a.fst b.fst with h | h
  · simp [decide_eq_true h]
  · simp [decide_eq_true h]

/-- **LS1.1**: the sequence is ascending — the ladder, for every footprint. -/
theorem lockAcquireSequence_ordered (pairs : List (LockKey × AccessMode)) :
    (lockAcquireSequence pairs).Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst) :=
  (List.pairwise_mergeSort (le := fun p₁ p₂ => decide (p₁.fst ≤ p₂.fst))
    leKey_bool_trans leKey_bool_total pairs).imp (fun h => of_decide_eq_true h)

/-- **LS1.1**: and a permutation of the declaration — the bracket acquires
exactly what was declared. -/
theorem lockAcquireSequence_perm (pairs : List (LockKey × AccessMode)) :
    (lockAcquireSequence pairs).Perm pairs :=
  List.mergeSort_perm pairs _

@[simp] theorem mem_lockAcquireSequence (pairs : List (LockKey × AccessMode))
    (p : LockKey × AccessMode) : p ∈ lockAcquireSequence pairs ↔ p ∈ pairs := by
  simp only [lockAcquireSequence, List.mem_mergeSort]

/-- **LS1.2**: a declaration already in ascending order is its own sequence —
what makes the sort transparent for every statically declared footprint, each
of which carries a `_pairwise_le` theorem.  Only a footprint resolved out of
ladder order (the PIP chain walk) is acquired in an order other than the one
it lists. -/
theorem lockAcquireSequence_eq_of_pairwise_le (pairs : List (LockKey × AccessMode))
    (h : (pairs.map (·.fst)).Pairwise (· ≤ ·)) :
    lockAcquireSequence pairs = pairs := by
  refine List.mergeSort_of_pairwise ?_
  exact (List.pairwise_map.mp h).imp (fun hle => decide_eq_true hle)

/-- Sorting keeps the keys distinct: the sequence of a duplicate-free footprint
is duplicate-free, which `acquireAll_unheld_held` needs of what it folds. -/
theorem lockAcquireSequence_nodup_keys (pairs : List (LockKey × AccessMode))
    (h : (pairs.map (·.fst)).Nodup) :
    ((lockAcquireSequence pairs).map (·.fst)).Nodup :=
  ((lockAcquireSequence_perm pairs).map (·.fst)).nodup_iff.mpr h

end SeLe4n.Kernel.Concurrency
