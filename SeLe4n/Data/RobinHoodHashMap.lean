/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import Std.Data.HashMap
import Std.Data.HashSet

/-! # WS-N1: Robin Hood HashMap — Foundation with machine-checked bridge lemmas

This module defines `RobinHoodHashMap` and `RobinHoodHashSet` as drop-in
replacements for `Std.HashMap` and `Std.HashSet` with machine-checked bridge
lemmas (zero proof gaps or unproven assumptions).

## Architecture

The implementation uses a **refinement-model** approach:

- **Phase 1 (this file)**: The `RobinHoodHashMap` structure wraps `Std.HashMap`
  internally, providing all 14 HashMap and 5 HashSet bridge lemmas with
  complete machine-checked proofs. This establishes the correctness contract
  that the rest of the kernel proof surface depends on.

- **Phase 3 (WS-N3)**: The internal representation will be swapped to a flat
  `Array`-based Robin Hood open-addressing layout for ARM64 cache locality.
  The bridge lemma signatures are unchanged — only the internal proofs are
  updated. All downstream proofs remain valid.

## Design rationale

Lean 4's `Std.HashMap` uses separate chaining (array of `AssocList` buckets).
Robin Hood hashing stores entries **inline** in a flat `Array`, eliminating
pointer chasing. This module lays the foundation: bridge lemmas first,
performance optimization second. This ordering ensures the kernel proof surface
is never broken during the migration.

## Bridge lemmas provided

**HashMap (14)**: `get?_insert`, `get?_empty`, `get?_erase`,
`getElem?_insert`, `getElem?_empty`, `getElem?_erase`,
`getElem?_eq_get?`, `get?_eq_getElem?`, `fold_eq_foldl_toList`,
`filter_preserves_key`, `filter_filter_getElem?`, `size_erase_le`,
`mem_iff_isSome_getElem?`, `getKey_beq`.

**HashSet (6)**: `contains_empty`, `contains_insert_self`, `contains_insert`,
`contains_insert_iff`, `not_contains_insert`, `contains_erase`.
-/

namespace SeLe4n.Data

-- ============================================================================
-- N1-A: Core data structure — refinement model
-- ============================================================================

/-- Robin Hood HashMap foundation. Wraps `Std.HashMap` with identical
semantics and machine-checked bridge lemmas. The internal representation
will be upgraded to flat open-addressing in WS-N3. -/
structure RobinHoodHashMap (α : Type) (β : Type) [BEq α] [Hashable α] where
  /-- Internal hash map providing both storage and proof delegation. -/
  inner : Std.HashMap α β

-- ============================================================================
-- N1-B: Constructors and instances
-- ============================================================================

/-- Default initial capacity. -/
def defaultCapacity : Nat := 16

variable {α : Type} {β : Type} [BEq α] [Hashable α]

/-- Create an empty Robin Hood HashMap. -/
def RobinHoodHashMap.mk' (_cap : Nat := defaultCapacity) :
    RobinHoodHashMap α β :=
  ⟨∅⟩

instance : EmptyCollection (RobinHoodHashMap α β) :=
  ⟨RobinHoodHashMap.mk'⟩

instance : Inhabited (RobinHoodHashMap α β) :=
  ⟨RobinHoodHashMap.mk'⟩

namespace RobinHoodHashMap

-- ============================================================================
-- N1-C: Core operations
-- ============================================================================

/-- Look up a key in the hash map. Returns `none` if not found. -/
@[inline] def get? (m : RobinHoodHashMap α β) (k : α) : Option β :=
  m.inner.get? k

/-- Check if a key exists in the map. -/
@[inline] def contains (m : RobinHoodHashMap α β) (k : α) : Bool :=
  m.inner.contains k

/-- Number of entries in the map. -/
@[inline] def size (m : RobinHoodHashMap α β) : Nat :=
  m.inner.size

-- ============================================================================
-- N1-D: Insert
-- ============================================================================

/-- Insert a key-value pair. If the key already exists, update its value. -/
def insert (m : RobinHoodHashMap α β) (k : α) (v : β) :
    RobinHoodHashMap α β :=
  ⟨m.inner.insert k v⟩

-- ============================================================================
-- N1-E: Erase
-- ============================================================================

/-- Remove a key from the map. -/
def erase (m : RobinHoodHashMap α β) (k : α) : RobinHoodHashMap α β :=
  ⟨m.inner.erase k⟩

-- ============================================================================
-- N1-F: Fold, toList, filter, isEmpty
-- ============================================================================

/-- Fold over all key-value pairs in iteration order. -/
def fold {γ : Type _} (m : RobinHoodHashMap α β) (init : γ)
    (f : γ → α → β → γ) : γ :=
  m.inner.fold (init := init) f

/-- Extract all key-value pairs as a list. -/
def toList (m : RobinHoodHashMap α β) : List (α × β) :=
  m.inner.toList

/-- The association list representation of the map's contents. -/
def toAssocList (m : RobinHoodHashMap α β) : List (α × β) := m.toList

/-- Filter entries by predicate. -/
def filter (m : RobinHoodHashMap α β) (f : α → β → Bool) :
    RobinHoodHashMap α β :=
  ⟨m.inner.filter f⟩

/-- Is the map empty? -/
@[inline] def isEmpty (m : RobinHoodHashMap α β) : Bool :=
  m.inner.isEmpty

-- ============================================================================
-- N1-F2: Membership and getElem? instances
-- ============================================================================

instance : Membership α (RobinHoodHashMap α β) :=
  ⟨fun (m : RobinHoodHashMap α β) (k : α) => m.contains k⟩

instance : GetElem? (RobinHoodHashMap α β) α β (fun m k => m.contains k) where
  getElem m k h := m.inner[k]'(by simp only [contains] at h; exact h)
  getElem? m k := m.inner[k]?

-- ============================================================================
-- N1-G: Bridge lemmas — HashMap (14 required)
-- ============================================================================

-- All bridge lemmas are proved by delegation to `Std.HashMap`/`Std.DHashMap`
-- proofs. Since our operations are defined as wrappers around `Std.HashMap`,
-- the proofs are direct rewrites.

/-- An empty map contains no keys. -/
theorem get?_empty (k : α) (cap : Nat) :
    (RobinHoodHashMap.mk' (α := α) (β := β) cap).get? k = none := by
  simp [get?, mk']

/-- Lookup on an empty map returns `none`. -/
theorem get?_emptyCollection (k : α) :
    (∅ : RobinHoodHashMap α β).get? k = none :=
  get?_empty k _

/-- After inserting `(k, v)`, looking up `k` returns `some v`. -/
theorem get?_insert_self [LawfulBEq α] (m : RobinHoodHashMap α β)
    (k : α) (v : β) :
    (m.insert k v).get? k = some v := by
  show (m.inner.insert k v).get? k = some v
  simp only [Std.HashMap.get?, Std.HashMap.insert]
  exact Std.DHashMap.Const.get?_insert_self

/-- After inserting `(k, v)`, looking up a different key `a ≠ k` returns
the same result as before the insert. -/
theorem get?_insert_ne [LawfulBEq α] (m : RobinHoodHashMap α β)
    (k a : α) (v : β) (hne : (k == a) = false) :
    (m.insert k v).get? a = m.get? a := by
  show (m.inner.insert k v).get? a = m.inner.get? a
  simp only [Std.HashMap.get?, Std.HashMap.insert]
  rw [Std.DHashMap.Const.get?_insert]
  simp [hne]

/-- Combined insert bridge lemma matching `Std.HashMap.get?_insert`. -/
theorem get?_insert [LawfulBEq α] (m : RobinHoodHashMap α β)
    {k a : α} {v : β} :
    (m.insert k v).get? a = if k == a then some v else m.get? a := by
  split
  · rename_i h; have := eq_of_beq h; subst this; exact get?_insert_self m k v
  · rename_i h
    exact get?_insert_ne m k a v (by cases hb : (k == a) <;> simp_all)

/-- After erasing `k`, looking up `k` returns `none`. -/
theorem get?_erase_self [LawfulBEq α] (m : RobinHoodHashMap α β) (k : α) :
    (m.erase k).get? k = none := by
  show (m.inner.erase k).get? k = none
  simp only [Std.HashMap.get?, Std.HashMap.erase]
  exact Std.DHashMap.Const.get?_erase_self

/-- After erasing `k`, looking up a different key `a ≠ k` returns
the same result as before the erase. -/
theorem get?_erase_ne [LawfulBEq α] (m : RobinHoodHashMap α β)
    (k a : α) (hne : (k == a) = false) :
    (m.erase k).get? a = m.get? a := by
  show (m.inner.erase k).get? a = m.inner.get? a
  simp only [Std.HashMap.get?, Std.HashMap.erase]
  rw [Std.DHashMap.Const.get?_erase]
  simp [hne]

/-- Combined erase bridge lemma matching `Std.HashMap.get?_erase`. -/
theorem get?_erase [LawfulBEq α] (m : RobinHoodHashMap α β) {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a := by
  split
  · rename_i h
    have : k = a := eq_of_beq h
    subst this
    exact get?_erase_self m k
  · rename_i h
    have hf : (k == a) = false := by cases hb : (k == a) <;> simp_all
    exact get?_erase_ne m k a hf

/-- `getElem?` after insert. -/
theorem getElem?_insert [LawfulBEq α] (m : RobinHoodHashMap α β)
    {k a : α} {v : β} :
    (m.insert k v)[a]? = if k == a then some v else m[a]? :=
  get?_insert m

/-- `getElem?` on empty. -/
theorem getElem?_empty (a : α) :
    (∅ : RobinHoodHashMap α β)[a]? = none :=
  get?_emptyCollection a

/-- `getElem?` after erase. -/
theorem getElem?_erase [LawfulBEq α] (m : RobinHoodHashMap α β)
    {k a : α} :
    (m.erase k)[a]? = if k == a then none else m[a]? :=
  get?_erase m

/-- `getElem?` equals `get?`. -/
theorem getElem?_eq_get? (m : RobinHoodHashMap α β) (k : α) :
    m[k]? = m.get? k := by
  rfl

/-- `get?` equals `getElem?`. -/
theorem get?_eq_getElem? (m : RobinHoodHashMap α β) (k : α) :
    m.get? k = m[k]? := by
  rfl

/-- `fold` is equivalent to `List.foldl` on `toList`. -/
theorem fold_eq_foldl_toList {γ : Type _} (m : RobinHoodHashMap α β)
    (init : γ) (f : γ → α → β → γ) :
    m.fold init f = m.toList.foldl (fun acc (p : α × β) => f acc p.1 p.2) init := by
  simp only [fold, toList]
  exact Std.HashMap.fold_eq_foldl_toList

/-- The size of `erase` is at most the original size. -/
theorem size_erase_le [LawfulBEq α] (m : RobinHoodHashMap α β) (k : α) :
    (m.erase k).size ≤ m.size := by
  simp only [size, erase]
  exact Std.HashMap.size_erase_le

/-- Membership is equivalent to `getElem?` returning `some`. -/
theorem mem_iff_isSome_getElem? [LawfulBEq α] (m : RobinHoodHashMap α β) (k : α) :
    m.contains k = true ↔ (m[k]?).isSome = true := by
  simp only [contains]
  exact Std.HashMap.mem_iff_isSome_getElem?

/-- Retrieve the stored key matching `k` by `BEq`. -/
@[inline] def getKey (m : RobinHoodHashMap α β) (k : α)
    (h : m.contains k = true) : α :=
  m.inner.getKey k (by simp only [contains] at h; exact h)

/-- The stored key is `BEq`-equivalent to the lookup key. -/
theorem getKey_beq [LawfulBEq α] (m : RobinHoodHashMap α β) (k : α)
    (h : m.contains k = true) :
    (m.getKey k h == k) = true := by
  simp only [getKey]
  exact Std.HashMap.getKey_beq (by simp only [contains] at h; exact h)

/-- Filtering with a predicate that holds for `k` preserves `k`'s entry. -/
theorem filter_preserves_key [EquivBEq α] [LawfulHashable α]
    (m : RobinHoodHashMap α β) (f : α → β → Bool) (k : α)
    (hTrue : ∀ (k' : α) (v : β), (k' == k) = true → f k' v = true) :
    (m.filter f)[k]? = m[k]? := by
  -- Delegate to Std.HashMap proof via the inner map
  show (m.inner.filter f)[k]? = m.inner[k]?
  simp only [Std.HashMap.getElem?_filter]
  suffices h : ∀ (o : Option β) (p : (a : β) → o = some a → Bool),
      (∀ a (h : o = some a), p a h = true) → o.pfilter p = o by
    apply h
    intro a ha
    have hMem : k ∈ m.inner := Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [ha])
    exact hTrue _ _ (Std.HashMap.getKey_beq hMem)
  intro o p hp
  cases o with
  | none => rfl
  | some v => simp [hp]

/-- Double-filtering is lookup-equivalent to single-filtering. -/
theorem filter_filter_getElem? [EquivBEq α] [LawfulHashable α]
    (m : RobinHoodHashMap α β) (f : α → β → Bool) (k : α) :
    ((m.filter f).filter f)[k]? = (m.filter f)[k]? := by
  show ((m.inner.filter f).filter f)[k]? = (m.inner.filter f)[k]?
  by_cases hMem : k ∈ m.inner.filter f
  · have ⟨_, hF⟩ := Std.HashMap.mem_filter.mp hMem
    have hMemFF : k ∈ (m.inner.filter f).filter f := by
      rw [Std.HashMap.mem_filter]
      refine ⟨hMem, ?_⟩
      rw [Std.HashMap.getKey_filter]
      rw [Std.HashMap.getElem_filter]
      exact hF
    have h1 := Std.HashMap.getElem?_eq_some_getElem hMemFF
    have h2 := Std.HashMap.getElem?_eq_some_getElem hMem
    have h3 : ((m.inner.filter f).filter f)[k] = (m.inner.filter f)[k] :=
      Std.HashMap.getElem_filter
    rw [h1, h2, h3]
  · have hNotMemFF : k ∉ (m.inner.filter f).filter f :=
      fun h => hMem (Std.HashMap.mem_of_mem_filter h)
    rw [Std.HashMap.getElem?_eq_none hNotMemFF,
        Std.HashMap.getElem?_eq_none hMem]

-- ============================================================================
-- N1-H: HashSet — thin wrapper
-- ============================================================================

end RobinHoodHashMap

/-- Robin Hood HashSet: thin wrapper over `RobinHoodHashMap α Unit`. -/
structure RobinHoodHashSet (α : Type) [BEq α] [Hashable α] where
  inner : RobinHoodHashMap α Unit

namespace RobinHoodHashSet

variable {α : Type} [BEq α] [Hashable α]

def mk' (cap : Nat := defaultCapacity) : RobinHoodHashSet α :=
  ⟨RobinHoodHashMap.mk' cap⟩

instance : EmptyCollection (RobinHoodHashSet α) := ⟨mk'⟩
instance : Inhabited (RobinHoodHashSet α) := ⟨mk'⟩

def insert (s : RobinHoodHashSet α) (a : α) : RobinHoodHashSet α :=
  ⟨s.inner.insert a ()⟩

@[inline] def contains (s : RobinHoodHashSet α) (a : α) : Bool :=
  s.inner.contains a

def erase (s : RobinHoodHashSet α) (a : α) : RobinHoodHashSet α :=
  ⟨s.inner.erase a⟩

@[inline] def size (s : RobinHoodHashSet α) : Nat := s.inner.size

def toList (s : RobinHoodHashSet α) : List α :=
  s.inner.toList.map Prod.fst

def fold {γ : Type _} (s : RobinHoodHashSet α) (init : γ)
    (f : γ → α → γ) : γ :=
  s.inner.fold init fun acc k _ => f acc k

-- ============================================================================
-- HashSet bridge lemmas (5 required)
-- ============================================================================

theorem contains_empty (a : α) :
    (∅ : RobinHoodHashSet α).contains a = false := by
  show (∅ : Std.HashMap α Unit).contains a = false
  exact Std.HashMap.contains_empty

theorem contains_insert_self [LawfulBEq α] (s : RobinHoodHashSet α) (a : α) :
    (s.insert a).contains a = true := by
  show (s.inner.inner.insert a ()).contains a = true
  simp [Std.HashMap.contains_insert]

theorem contains_insert [LawfulBEq α] (s : RobinHoodHashSet α)
    (a b : α) :
    (s.insert a).contains b = (a == b || s.contains b) := by
  show (s.inner.inner.insert a ()).contains b = (a == b || s.inner.inner.contains b)
  simp [Std.HashMap.contains_insert]

theorem contains_insert_iff [LawfulBEq α] (s : RobinHoodHashSet α)
    (a b : α) :
    (s.insert a).contains b = true ↔ b = a ∨ s.contains b = true := by
  rw [contains_insert]
  constructor
  · intro h
    cases hba : (a == b) with
    | true =>
      left
      exact (@eq_of_beq α _ _ a b (by rw [hba])).symm
    | false => simp [hba] at h; right; exact h
  · intro h
    cases h with
    | inl h => subst h; simp
    | inr h => simp [h]

theorem not_contains_insert [LawfulBEq α] (s : RobinHoodHashSet α)
    (a b : α) :
    (s.insert a).contains b = false ↔ b ≠ a ∧ s.contains b = false := by
  rw [contains_insert]
  constructor
  · intro h
    simp [Bool.or_eq_false_iff] at h
    constructor
    · intro hab; subst hab; simp at h
    · exact h.2
  · intro ⟨hne, hc⟩
    simp [hc]
    cases hab : (a == b) with
    | true =>
      exfalso; apply hne
      exact (@eq_of_beq α _ _ a b (by rw [hab])).symm
    | false =>
      intro hab2; subst hab2; simp at hab

theorem contains_erase [LawfulBEq α] (s : RobinHoodHashSet α)
    (a b : α) :
    (s.erase a).contains b = (!(a == b) && s.contains b) := by
  show (s.inner.inner.erase a).contains b = (!(a == b) && s.inner.inner.contains b)
  simp [Std.HashMap.contains_erase]

end RobinHoodHashSet

end SeLe4n.Data
