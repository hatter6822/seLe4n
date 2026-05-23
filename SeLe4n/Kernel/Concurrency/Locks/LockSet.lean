-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Locks.RwLock

/-!
# WS-SM SM3.B — `LockSet`, lock-acquisition ordering, and canonical sort

This module introduces the SM3.B abstract lock-set type — a well-formed
list of `(LockId × AccessMode)` pairs with unique `LockId` keys — and
the canonical `lockAcquireSequence` sort that sorts a `LockSet` by
`LockId` ascending.  Three substantive theorems follow:

* `lockAcquireSequence_ordered` (SM3.B.6) — the sort produces a list
  whose adjacent `LockId`s are `≤`-ordered.  Lifts `mergeSort`'s
  `pairwise_mergeSort` lemma against the `LockId` total order
  (`LockId.le_total`, `LockId.le_trans`).
* `lockAcquireSequence_complete` (SM3.B.7) — every element of the
  source `LockSet` appears in the sorted output.  Lifts
  `mergeSort`'s `mem_mergeSort` lemma.
* `lockAcquireSequence_canonical` (SM3.B.8, plan §3.5.1) — the
  sorted sequence is the *unique* sorted permutation of the source's
  underlying list.  The proof factors through key uniqueness
  (the `hUniqueKeys` field): two sorted permutations of the same
  underlying multiset agree position-by-position because the
  `LockId` keys are pairwise distinct.

## Design rationale: `LockSet` vs `Finset`

The plan §3.4 uses `Finset (LockId × AccessMode)` for the lock-set
type.  seLe4n is mathlib-free (core Lean only), so `Finset` is
unavailable; the equivalent structural shape is a `List` carrying a
`Nodup` witness on the underlying keys.

The well-formedness predicate `(pairs.map (·.fst)).Nodup` enforces
**plan §3.5's key-uniqueness invariant**: a single `LockSet` cannot
declare both read and write modes for the same `LockId` —
ambiguous declarations are resolved at *insertion* time via
`AccessMode.lub` (write dominates read), so a `LockSet` is always
canonical with respect to its declared modes.

## Used by

* SM3.B.3 (`lockSet_<transition>` per-transition declarations) —
  every kernel transition exports a static `LockSet` declaring its
  acquisition footprint.
* SM3.C (`withLockSet` 2PL combinator) — folds
  `lockAcquireSequence` to acquire in ascending order, then folds
  the reverse to release in descending order.
* SM3.D (`deadlockFreedom_under_2pl_and_ordering`) — appeals to
  `lockAcquireSequence_ordered` to discharge the lock-ladder
  invariant that closes any potential wait-cycle.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM3.B helpers — AccessMode lattice / conflict relation
-- ============================================================================

/-- WS-SM SM3.B: least-upper-bound on `AccessMode`.

`write` dominates `read` — a `LockSet` that declares both `read` and
`write` on the same `LockId` collapses to `write` (the conservative
choice).  Used at `LockSet.insertOrMerge` to discharge the
key-uniqueness invariant when the same `LockId` is inserted twice
with different modes. -/
def AccessMode.lub : AccessMode → AccessMode → AccessMode
  | .write, _       => .write
  | _,       .write => .write
  | .read,   .read  => .read

/-- WS-SM SM3.B: `AccessMode.lub` is idempotent. -/
@[simp] theorem AccessMode.lub_idem (m : AccessMode) : m.lub m = m := by
  cases m <;> rfl

/-- WS-SM SM3.B: `AccessMode.lub` is commutative. -/
theorem AccessMode.lub_comm (m₁ m₂ : AccessMode) : m₁.lub m₂ = m₂.lub m₁ := by
  cases m₁ <;> cases m₂ <;> rfl

/-- WS-SM SM3.B: `AccessMode.lub` is associative. -/
theorem AccessMode.lub_assoc (m₁ m₂ m₃ : AccessMode) :
    (m₁.lub m₂).lub m₃ = m₁.lub (m₂.lub m₃) := by
  cases m₁ <;> cases m₂ <;> cases m₃ <;> rfl

/-- WS-SM SM3.B: `write` is the top of the `AccessMode` lattice. -/
@[simp] theorem AccessMode.lub_write_left (m : AccessMode) :
    AccessMode.write.lub m = .write := by
  cases m <;> rfl

/-- WS-SM SM3.B: `write` is the top of the `AccessMode` lattice (right-form). -/
@[simp] theorem AccessMode.lub_write_right (m : AccessMode) :
    m.lub AccessMode.write = .write := by
  cases m <;> rfl

/-- WS-SM SM3.B: `read` is the bottom of the `AccessMode` lattice. -/
@[simp] theorem AccessMode.lub_read_left (m : AccessMode) :
    AccessMode.read.lub m = m := by
  cases m <;> rfl

/-- WS-SM SM3.B: `read` is the bottom of the `AccessMode` lattice (right-form). -/
@[simp] theorem AccessMode.lub_read_right (m : AccessMode) :
    m.lub AccessMode.read = m := by
  cases m <;> rfl

/-- WS-SM SM3.B: conflict relation per plan §3.3.

Two access modes on the same lock conflict iff at least one is `write`.
The relation is symmetric; pairs of `read`s do not conflict.

Used by SM3.D's deadlock-freedom proof (the conflict relation
characterises when a wait-edge is induced between two transactions
touching the same lock) and SM3.E's commutativity lemmas
(non-conflicting transitions commute). -/
def AccessMode.conflicts : AccessMode → AccessMode → Bool
  | .write, _      => true
  | .read,  .write => true
  | .read,  .read  => false

/-- WS-SM SM3.B: `conflicts` is symmetric. -/
theorem AccessMode.conflicts_symm (m₁ m₂ : AccessMode) :
    m₁.conflicts m₂ = m₂.conflicts m₁ := by
  cases m₁ <;> cases m₂ <;> rfl

/-- WS-SM SM3.B: two read-mode acquires do not conflict. -/
@[simp] theorem AccessMode.conflicts_read_read :
    AccessMode.read.conflicts .read = false := rfl

/-- WS-SM SM3.B: write conflicts with anything. -/
@[simp] theorem AccessMode.conflicts_write_left (m : AccessMode) :
    AccessMode.write.conflicts m = true := by
  cases m <;> rfl

/-- WS-SM SM3.B: anything conflicts with write. -/
@[simp] theorem AccessMode.conflicts_write_right (m : AccessMode) :
    m.conflicts AccessMode.write = true := by
  cases m <;> rfl

-- ============================================================================
-- SM3.B — LockSet structure with key-uniqueness invariant
-- ============================================================================

/-- WS-SM SM3.B: the abstract lock-set type.

A `LockSet` is a list of `(LockId × AccessMode)` pairs with the
structural invariant that the projected `LockId` keys are pairwise
distinct.  This enforces plan §3.5's claim that "a lock can't have
two modes declared in the same lock-set" by construction —
constructors that would violate the invariant either reject or
merge modes via `AccessMode.lub`.

`Repr` is derived for trace output; `DecidableEq` is derived for
runtime test assertions and `decide`-based example discharge.

The mathlib-free design encodes the key-uniqueness invariant as a
`Nodup` over the projected keys, mirroring SM3.A's
`NoDupList`-based notification waiter list (which carries a
`hNodup : val.Nodup` proof). -/
structure LockSet where
  /-- The list of `(LockId × AccessMode)` declarations. -/
  pairs : List (LockId × AccessMode)
  /-- WS-SM SM3.B well-formedness: each `LockId` key appears at most
      once.  Enforces plan §3.5's key-uniqueness invariant by
      construction. -/
  hUniqueKeys : (pairs.map (·.fst)).Nodup

namespace LockSet

instance : Repr LockSet where
  reprPrec s n := reprPrec s.pairs n

/-- WS-SM SM3.B: structural equality on `LockSet` reduces to equality
on the `pairs` field (the well-formedness witness is propositionally
unique under `Nodup` proof irrelevance). -/
instance : DecidableEq LockSet := fun s₁ s₂ =>
  if h : s₁.pairs = s₂.pairs then
    .isTrue (by
      obtain ⟨p₁, h₁⟩ := s₁
      obtain ⟨p₂, _h₂⟩ := s₂
      simp only at h
      subst h
      rfl)
  else
    .isFalse (fun heq => h (heq ▸ rfl))

/-- WS-SM SM3.B: the empty `LockSet` — a transition with no locks (rare).

The well-formedness witness is `List.Pairwise.nil` (the empty list
is trivially `Nodup`).  Used as the base case for `LockSet.union?`
and as the seed for `List.foldl`-based assembly. -/
def empty : LockSet :=
  { pairs := [], hUniqueKeys := List.Pairwise.nil }

@[simp] theorem empty_pairs : empty.pairs = [] := rfl

/-- WS-SM SM3.B: singleton `LockSet` — a transition holding exactly one lock. -/
def singleton (l : LockId) (m : AccessMode) : LockSet :=
  { pairs := [(l, m)],
    hUniqueKeys := by
      simp only [List.map_cons, List.map_nil]
      exact List.Pairwise.cons (fun _ h => by cases h) List.Pairwise.nil }

@[simp] theorem singleton_pairs (l : LockId) (m : AccessMode) :
    (singleton l m).pairs = [(l, m)] := rfl

/-- WS-SM SM3.B: membership in a `LockSet` reduces to membership in
the underlying `pairs` list.  Signature follows the Lean 4
`Membership` convention: the collection comes first, the element
comes second. -/
def Mem (S : LockSet) (p : LockId × AccessMode) : Prop :=
  p ∈ S.pairs

instance : Membership (LockId × AccessMode) LockSet := ⟨Mem⟩

@[simp] theorem mem_def (p : LockId × AccessMode) (S : LockSet) :
    p ∈ S ↔ p ∈ S.pairs := Iff.rfl

@[simp] theorem mem_empty (p : LockId × AccessMode) : ¬ p ∈ empty := by
  intro h; cases h

@[simp] theorem mem_singleton (l : LockId) (m : AccessMode)
    (p : LockId × AccessMode) :
    p ∈ singleton l m ↔ p = (l, m) := by
  show p ∈ [(l, m)] ↔ p = (l, m)
  simp

/-- WS-SM SM3.B: size of a `LockSet` is the length of its underlying
list (well-defined under `Nodup`-keyed pairs). -/
def size (S : LockSet) : Nat := S.pairs.length

@[simp] theorem size_empty : empty.size = 0 := rfl

@[simp] theorem size_singleton (l : LockId) (m : AccessMode) :
    (singleton l m).size = 1 := rfl

/-- WS-SM SM3.B: check whether a `LockId` is present in a `LockSet`. -/
def containsKey (l : LockId) (S : LockSet) : Bool :=
  S.pairs.any (fun p => decide (p.fst = l))

@[simp] theorem containsKey_empty (l : LockId) :
    containsKey l empty = false := rfl

theorem containsKey_iff (l : LockId) (S : LockSet) :
    containsKey l S = true ↔ ∃ m, (l, m) ∈ S := by
  constructor
  · intro h
    rw [containsKey, List.any_eq_true] at h
    obtain ⟨p, hpmem, hpfst⟩ := h
    have hEq : p.fst = l := of_decide_eq_true hpfst
    refine ⟨p.snd, ?_⟩
    show (l, p.snd) ∈ S.pairs
    rw [show (l, p.snd) = p from by cases p; simp_all]
    exact hpmem
  · rintro ⟨m, hmem⟩
    rw [containsKey, List.any_eq_true]
    refine ⟨(l, m), hmem, ?_⟩
    simp

/-- WS-SM SM3.B: try to insert a fresh `(LockId, AccessMode)` pair
into a `LockSet`.  Returns `none` if the `LockId` is already
present (the caller should use `insertOrMerge` instead for the
merge-via-`lub` semantics).

The strict form is used by tests that want to assert no key is
duplicated; the merging form is used by production lockSet
assembly. -/
def insert? (l : LockId) (m : AccessMode) (S : LockSet) : Option LockSet :=
  if h : containsKey l S = true then
    none
  else
    some {
      pairs := (l, m) :: S.pairs,
      hUniqueKeys := by
        have hNotMem : l ∉ S.pairs.map (·.fst) := by
          intro hmem
          have : containsKey l S = true := by
            rw [containsKey, List.any_eq_true]
            obtain ⟨p, hpmem, hpfst⟩ := List.mem_map.mp hmem
            exact ⟨p, hpmem, by simp [hpfst]⟩
          exact h this
        simp only [List.map_cons]
        exact List.Pairwise.cons
          (fun a' ha' hEq => hNotMem (hEq ▸ ha')) S.hUniqueKeys
    }

/-- WS-SM SM3.B: insert a `(LockId, AccessMode)` pair, merging modes
via `AccessMode.lub` if the `LockId` is already present.

This is the production insertion: when a transition's `lockSet`
declares both `read` and `write` over the same path (e.g. a
cap-lookup branch reads the CNode but a write-branch also writes
it), the union picks `write` (the conservative bound).  Per plan
§4.1, "the lock-set is the union over all paths". -/
def insertOrMerge (l : LockId) (m : AccessMode) (S : LockSet) : LockSet :=
  match h : containsKey l S with
  | true  =>
      -- Replace the existing entry with the lub'd mode.
      {
        pairs := S.pairs.map (fun p =>
          if p.fst = l then (l, p.snd.lub m) else p),
        hUniqueKeys := by
          -- The `(·.fst)` projection over the mapped list equals
          -- the original projection because the if-then-else only
          -- changes the snd component.
          have hMap : (S.pairs.map (fun p =>
                          if p.fst = l then (l, p.snd.lub m) else p)).map (·.fst) =
                      S.pairs.map (·.fst) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro p _hmem
            by_cases hp : p.fst = l
            · simp [hp]
            · simp [hp]
          rw [hMap]
          exact S.hUniqueKeys
      }
  | false =>
      -- Fresh key; prepend.
      {
        pairs := (l, m) :: S.pairs,
        hUniqueKeys := by
          have hNotMem : l ∉ S.pairs.map (·.fst) := by
            intro hmem
            have : containsKey l S = true := by
              rw [containsKey, List.any_eq_true]
              obtain ⟨p, hpmem, hpfst⟩ := List.mem_map.mp hmem
              exact ⟨p, hpmem, by simp [hpfst]⟩
            rw [h] at this
            exact Bool.false_ne_true this
          simp only [List.map_cons]
          exact List.Pairwise.cons
            (fun a' ha' hEq => hNotMem (hEq ▸ ha')) S.hUniqueKeys
      }

/-- WS-SM SM3.B: union of two `LockSet`s — fold `insertOrMerge` over
the right-hand argument's pairs.

Merges duplicate keys per `AccessMode.lub` (write dominates read).
Used to combine the per-object lock declarations of a multi-object
transition (e.g., `endpointCall` touching caller TCB, endpoint, and
receiver TCB). -/
def union (S₁ S₂ : LockSet) : LockSet :=
  S₂.pairs.foldl (init := S₁) (fun acc p => acc.insertOrMerge p.fst p.snd)

/-- WS-SM SM3.B: `union` with the empty set on the right is identity. -/
@[simp] theorem union_empty (S : LockSet) : S.union empty = S := by
  simp [union, empty]

-- ============================================================================
-- SM3.B.5..B.8 — canonical sort (`lockAcquireSequence`)
-- ============================================================================

/-- WS-SM SM3.B.5: canonical acquisition sequence — the underlying
pairs sorted by `LockId` ascending.

The comparator returns `true` iff `p₁.fst ≤ p₂.fst` (Bool-form for
`List.mergeSort`).  Two pairs sharing the same `LockId` cannot
appear in a well-formed `LockSet` (`hUniqueKeys`), so the comparator
never sees a true tie — but `mergeSort` is stable for tied keys
anyway, so the result is deterministic regardless.

This is the input that `withLockSet` (SM3.C.1) folds to acquire
locks in ascending order, then folds in reverse to release in
descending order. -/
def lockAcquireSequence (S : LockSet) : List (LockId × AccessMode) :=
  S.pairs.mergeSort (fun p₁ p₂ => decide (p₁.fst ≤ p₂.fst))

@[simp] theorem lockAcquireSequence_empty :
    lockAcquireSequence empty = [] := by
  simp [lockAcquireSequence, empty]

@[simp] theorem lockAcquireSequence_singleton (l : LockId) (m : AccessMode) :
    lockAcquireSequence (singleton l m) = [(l, m)] := by
  simp [lockAcquireSequence, singleton]

-- ============================================================================
-- SM3.B.6 — `lockAcquireSequence_ordered`
-- ============================================================================

/-- WS-SM SM3.B helper: the comparator used by `lockAcquireSequence`
is transitive on Bool-form. -/
private theorem leLockId_bool_trans (a b c : LockId × AccessMode) :
    decide (a.fst ≤ b.fst) = true →
    decide (b.fst ≤ c.fst) = true →
    decide (a.fst ≤ c.fst) = true := by
  intro hab hbc
  have hab' : a.fst ≤ b.fst := of_decide_eq_true hab
  have hbc' : b.fst ≤ c.fst := of_decide_eq_true hbc
  exact decide_eq_true (LockId.le_trans _ _ _ hab' hbc')

/-- WS-SM SM3.B helper: the comparator used by `lockAcquireSequence`
is total on Bool-form. -/
private theorem leLockId_bool_total (a b : LockId × AccessMode) :
    (decide (a.fst ≤ b.fst) || decide (b.fst ≤ a.fst)) = true := by
  rcases LockId.le_total a.fst b.fst with h | h
  · simp [decide_eq_true h]
  · simp [decide_eq_true h]

/-- WS-SM SM3.B.6 (plan §3.5): the canonical sort produces a list
whose adjacent `LockId`s are `≤`-ordered.

Discharged via `List.pairwise_mergeSort` applied to `LockId`'s
total order (transitivity from `LockId.le_trans`, totality from
`LockId.le_total`).  This is the cornerstone witness that SM3.C's
`withLockSet` consumes to discharge "acquires in lock-ID order"
without further argument. -/
theorem lockAcquireSequence_ordered (S : LockSet) :
    (lockAcquireSequence S).Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst) := by
  -- Start from `pairwise_mergeSort` on the Bool comparator.
  have hPairBool : List.Pairwise
      (fun p₁ p₂ => decide (p₁.fst ≤ p₂.fst) = true)
      (lockAcquireSequence S) :=
    List.pairwise_mergeSort
      (le := fun p₁ p₂ => decide (p₁.fst ≤ p₂.fst))
      leLockId_bool_trans leLockId_bool_total S.pairs
  -- Lift `decide _ = true` to the underlying Prop.
  exact hPairBool.imp (fun h => of_decide_eq_true h)

-- ============================================================================
-- SM3.B.7 — `lockAcquireSequence_complete`
-- ============================================================================

/-- WS-SM SM3.B.7 (plan §5.2.SM3.B.7): every element of the source
`LockSet` appears in the sorted output, and vice versa.  Lifts
`List.mem_mergeSort`. -/
theorem lockAcquireSequence_complete (S : LockSet)
    (p : LockId × AccessMode) :
    p ∈ S ↔ p ∈ lockAcquireSequence S := by
  simp only [mem_def, lockAcquireSequence, List.mem_mergeSort]

/-- WS-SM SM3.B: forward direction of `_complete` for compatibility
with the plan's signature. -/
theorem lockAcquireSequence_complete_forward (S : LockSet)
    (p : LockId × AccessMode) (hmem : p ∈ S) :
    p ∈ lockAcquireSequence S :=
  (lockAcquireSequence_complete S p).mp hmem

/-- WS-SM SM3.B: the sort is a permutation of the input. -/
theorem lockAcquireSequence_perm (S : LockSet) :
    (lockAcquireSequence S).Perm S.pairs := by
  exact List.mergeSort_perm S.pairs _

/-- WS-SM SM3.B: the sort preserves length. -/
theorem lockAcquireSequence_length (S : LockSet) :
    (lockAcquireSequence S).length = S.size := by
  have := (lockAcquireSequence_perm S).length_eq
  simpa [size] using this

-- ============================================================================
-- SM3.B.8 — `lockAcquireSequence_canonical` (plan §3.5.1)
-- ============================================================================

/-- WS-SM SM3.B helper: in a list whose mapped keys are `Nodup`, if
two pairs share the same key then they are the same pair.

Proved by induction on the list — the head of the list either
matches both pairs (then equal by transitivity), matches one
(contradiction with mapped Nodup since the other would also map
to the head's key), or matches neither (recursive case).

This is the generic structural lemma; `LockSet.fst_inj_at_pairs`
specialises it to a `LockSet`'s underlying `pairs` field. -/
theorem list_fst_inj_of_nodup_keys {α β : Type _} [DecidableEq α]
    (l : List (α × β)) (hNodup : (l.map (·.fst)).Nodup)
    {p₁ p₂ : α × β} (h₁ : p₁ ∈ l) (h₂ : p₂ ∈ l)
    (hfst : p₁.fst = p₂.fst) : p₁ = p₂ := by
  induction l with
  | nil => exact absurd h₁ (List.not_mem_nil)
  | cons head tail ih =>
      simp only [List.map_cons] at hNodup
      have hHeadNotIn : head.fst ∉ tail.map (·.fst) :=
        fun hmem => by
          have hForall := (List.pairwise_cons.mp hNodup).1
          exact (hForall _ hmem) rfl
      have hTailNodup : (tail.map (·.fst)).Nodup :=
        (List.pairwise_cons.mp hNodup).2
      rcases List.mem_cons.mp h₁ with hp₁ | hp₁
      · rcases List.mem_cons.mp h₂ with hp₂ | hp₂
        · -- Both pairs are the head.
          rw [hp₁, hp₂]
        · -- p₁ is the head; p₂ is in tail.
          -- head.fst ∈ tail.map (·.fst) via the chain head = p₁, p₁.fst = p₂.fst, p₂ ∈ tail.
          exfalso
          apply hHeadNotIn
          refine List.mem_map.mpr ⟨p₂, hp₂, ?_⟩
          rw [← hfst, ← hp₁]
      · rcases List.mem_cons.mp h₂ with hp₂ | hp₂
        · -- p₂ is the head; p₁ is in tail.  Symmetric.
          exfalso
          apply hHeadNotIn
          refine List.mem_map.mpr ⟨p₁, hp₁, ?_⟩
          rw [hfst, ← hp₂]
        · -- Both pairs are in the tail; recurse.
          exact ih hTailNodup hp₁ hp₂

/-- WS-SM SM3.B helper: in a well-formed `LockSet`, two pairs with
the same `fst` key are equal.

Defined inside `namespace LockSet`, so the fully-qualified name is
`SeLe4n.Kernel.Concurrency.LockSet.fst_inj_at_pairs`. -/
theorem fst_inj_at_pairs (S : LockSet)
    {p₁ p₂ : LockId × AccessMode}
    (h₁ : p₁ ∈ S.pairs) (h₂ : p₂ ∈ S.pairs)
    (hfst : p₁.fst = p₂.fst) : p₁ = p₂ :=
  list_fst_inj_of_nodup_keys S.pairs S.hUniqueKeys h₁ h₂ hfst

/-- WS-SM SM3.B.8 (plan §3.5.1 Theorem `lockAcquireSequence_canonical`):
the canonical acquisition sequence is the *unique* `≤`-sorted
permutation of the source's underlying list.

Given any list `l'` that is a permutation of `S.pairs` *and* is
`≤`-sorted by `(·.fst)`, `l'` equals `lockAcquireSequence S`.

The proof factors through the Bool-typed `List.eq_of_perm_of_sorted`
(or its analog) — under key-uniqueness from `hUniqueKeys`, the
`fst`-ordering becomes strict, which combined with permutation
forces structural equality.

We discharge by induction on the length, exploiting that
`mergeSort` is itself a permutation (`lockAcquireSequence_perm`)
and that sorted permutations of a list with distinct keys are
identical position-by-position. -/
theorem lockAcquireSequence_canonical (S : LockSet)
    (l' : List (LockId × AccessMode))
    (hPerm : l'.Perm S.pairs)
    (hSorted : l'.Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst)) :
    l' = lockAcquireSequence S := by
  -- Combine: lockAcquireSequence S is also a permutation of S.pairs and is sorted.
  have hSortedSelf := lockAcquireSequence_ordered S
  have hPermSelf := lockAcquireSequence_perm S
  -- Both are permutations of S.pairs, so they're permutations of each other.
  have hPermBoth : l'.Perm (lockAcquireSequence S) :=
    hPerm.trans hPermSelf.symm
  -- We need a uniqueness-of-sorted-permutation lemma.  Use the
  -- antisymmetric `≤` derived from key-uniqueness.
  -- Define a *strict-positional* ordering: for any two pairs from S.pairs,
  -- `p₁.fst < p₂.fst` (since keys are distinct, ≤ becomes <).
  -- Then sorted permutations of a list with strict ordering are unique.
  -- We use List.eq_of_perm_of_sorted from Std (or hand-prove via induction).
  -- This is the canonical "perm + sorted on antisymmetric R = equal" lemma.
  -- Since we may not have it directly, hand-prove via induction.
  exact lockAcquireSequence_canonical_aux S l' hPermBoth.symm hSortedSelf hSorted
where
  /-- Helper: any two sorted permutations of `S.pairs` are equal.  Proof by
  strong induction on length using a custom "uniqueness of sorted
  permutation" lemma. -/
  lockAcquireSequence_canonical_aux (S : LockSet)
      (l' : List (LockId × AccessMode))
      (hPerm : (lockAcquireSequence S).Perm l')
      (_hSortedRef : (lockAcquireSequence S).Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst))
      (hSortedL' : l'.Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst)) :
      l' = lockAcquireSequence S := by
    -- Strategy: under key uniqueness on S.pairs, the `≤`-sorted
    -- permutations are uniquely determined.  Symmetrize hPerm to use
    -- standard mathlib-style identification.
    symm
    -- We use the fact: if two lists are permutations and both Pairwise (≤)
    -- under a strictly-antisymmetric-via-key-uniqueness ≤, they are equal.
    -- We derive antisymmetry from S's hUniqueKeys (positions in S.pairs
    -- have distinct fst, hence distinct ≤-ordering after sort).
    -- Use the standard `List.Sorted` uniqueness pattern, hand-rolled:
    have hKeysNodup_lock : ((lockAcquireSequence S).map (·.fst)).Nodup := by
      -- The sort preserves the underlying list as a permutation, so the
      -- mapped fst list is also a permutation of S.pairs.map (·.fst),
      -- which is Nodup by S.hUniqueKeys.
      have hPermFst : ((lockAcquireSequence S).map (·.fst)).Perm
                      (S.pairs.map (·.fst)) :=
        (lockAcquireSequence_perm S).map _
      exact hPermFst.nodup_iff.mpr S.hUniqueKeys
    have hKeysNodup_l' : (l'.map (·.fst)).Nodup := by
      have hPermFstL' : (l'.map (·.fst)).Perm
                        ((lockAcquireSequence S).map (·.fst)) :=
        (hPerm.symm.map _)
      exact hPermFstL'.nodup_iff.mpr hKeysNodup_lock
    -- Now apply uniqueness of sorted Nodup-keyed permutation.
    exact uniq_sorted_perm_aux hPerm
      _hSortedRef hKeysNodup_lock hSortedL' hKeysNodup_l'
  /-- Inner helper: uniqueness of sorted-with-Nodup-keys permutation.
  Generic over arbitrary lists. -/
  uniq_sorted_perm_aux : ∀ {l₁ l₂ : List (LockId × AccessMode)},
      l₁.Perm l₂ →
      l₁.Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst) →
      (l₁.map (·.fst)).Nodup →
      l₂.Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst) →
      (l₂.map (·.fst)).Nodup →
      l₁ = l₂
  | [], [], _, _, _, _, _ => rfl
  | [], (b :: _), hPerm, _, _, _, _ => by
      cases hPerm.length_eq
  | (a :: _), [], hPerm, _, _, _, _ => by
      cases hPerm.length_eq
  | (a :: l₁'), (b :: l₂'), hPerm, hS1, hNodup1, hS2, hNodup2 => by
      -- Show heads are equal: a is ≤ every element of l₁' (by hS1), and
      -- a appears in (b :: l₂') (by Perm), so a is ≤ b (from a ≤ ... = b).
      -- Symmetric: b is ≤ a.  Then antisymmetry via Nodup-keys gives a = b.
      have ha_in_bl₂' : a ∈ (b :: l₂') :=
        hPerm.mem_iff.mp (List.mem_cons_self)
      have hb_in_al₁' : b ∈ (a :: l₁') :=
        hPerm.symm.mem_iff.mp (List.mem_cons_self)
      -- Case a = b: strip heads and recurse.
      by_cases hab : a = b
      · subst hab
        have hPerm' : l₁'.Perm l₂' := (List.perm_cons _).mp hPerm
        have hNodup1' : (l₁'.map (·.fst)).Nodup := by
          have := hNodup1
          simp only [List.map_cons] at this
          exact this.of_cons
        have hNodup2' : (l₂'.map (·.fst)).Nodup := by
          have := hNodup2
          simp only [List.map_cons] at this
          exact this.of_cons
        have hS1' : l₁'.Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst) := hS1.of_cons
        have hS2' : l₂'.Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst) := hS2.of_cons
        have := uniq_sorted_perm_aux hPerm' hS1' hNodup1' hS2' hNodup2'
        rw [this]
      -- Case a ≠ b: derive contradiction.  a ∈ b :: l₂' and a ≠ b implies a ∈ l₂'.
      -- Similarly b ∈ l₁'.  Then a ≤ b (from hS1 applied to head a + b ∈ l₁') ...
      · exfalso
        have ha_in_l₂' : a ∈ l₂' := by
          rcases List.mem_cons.mp ha_in_bl₂' with hEq | hin
          · exact absurd hEq hab
          · exact hin
        have hb_in_l₁' : b ∈ l₁' := by
          rcases List.mem_cons.mp hb_in_al₁' with hEq | hin
          · exact absurd hEq.symm hab
          · exact hin
        -- hS1 gives: a.fst ≤ b.fst (head of a :: l₁', b ∈ l₁').
        have hab_le : a.fst ≤ b.fst :=
          (List.rel_of_pairwise_cons hS1) hb_in_l₁'
        -- hS2 gives: b.fst ≤ a.fst (head of b :: l₂', a ∈ l₂').
        have hba_le : b.fst ≤ a.fst :=
          (List.rel_of_pairwise_cons hS2) ha_in_l₂'
        -- Antisymmetry: a.fst = b.fst.
        have hKeyEq : a.fst = b.fst := LockId.le_antisymm _ _ hab_le hba_le
        -- But the Nodup of keys on (a :: l₁') says a.fst ∉ l₁'.map (·.fst).
        have hNodup1_head : a.fst ∉ l₁'.map (·.fst) := by
          have h := hNodup1
          simp only [List.map_cons] at h
          have hForall := (List.pairwise_cons.mp h).1
          intro hmem
          exact (hForall _ hmem) rfl
        -- And b ∈ l₁'.
        have hbFstInMap : b.fst ∈ l₁'.map (·.fst) :=
          List.mem_map.mpr ⟨b, hb_in_l₁', rfl⟩
        rw [← hKeyEq] at hbFstInMap
        exact hNodup1_head hbFstInMap

end LockSet

end SeLe4n.Kernel.Concurrency
