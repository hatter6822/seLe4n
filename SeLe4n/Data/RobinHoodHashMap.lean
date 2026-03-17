/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

/-! # WS-N1: Robin Hood HashMap — Core Data Structure & Bridge Lemmas

A cache-friendly, open-addressing hash table using Robin Hood hashing with
backward-shift deletion. Backed by Lean 4's `Array` for flat C memory layout
and FBIP in-place mutation.

## Design

- **Flat `Array`-backed**: Compiles to contiguous C heap allocation with O(1)
  random access and in-place mutation via FBIP.
- **Robin Hood displacement**: Entries with longer probe distances displace
  entries with shorter distances, bounding worst-case lookup to O(log n).
- **Backward-shift deletion**: No tombstone pollution.
- **Power-of-two capacity**: Bitwise masking for index computation.
- **7/8 load factor**: Resize at 87.5% occupancy.

## Proof Architecture

Bridge lemmas are built in layers:

1. **WellFormed**: PSL correctness, no duplicate keys, Robin Hood ordering.
2. **Insert decomposition**: `insertCore_contains_self` + `insertCore_preserves_other`
3. **Erase decomposition**: `erase_removes_self` + `erase_preserves_other`
4. **Bridge lemmas**: `get?_insert`, `get?_erase` compose the decomposition.
-/

namespace SeLe4n.Data

-- ============================================================================
-- Section 1: Core types
-- ============================================================================

/-- Entry in a Robin Hood HashMap bucket with inline probe sequence length. -/
structure Entry (α : Type) (β : Type) where
  key : α
  val : β
  psl : Nat
deriving BEq

-- ============================================================================
-- Section 2: Robin Hood HashMap structure
-- ============================================================================

/-- Robin Hood HashMap with open addressing and backward-shift deletion. -/
structure RobinHoodHashMap (α : Type) (β : Type) [BEq α] [Hashable α] where
  buckets  : Array (Option (Entry α β))
  size     : Nat
  capacity : Nat
  hCapPos  : capacity ≥ 4
  hBuckets : buckets.size = capacity

namespace RobinHoodHashMap

variable {α : Type} {β : Type} [BEq α] [Hashable α]

def defaultCapacity : Nat := 16

/-- Create an empty map with given capacity (minimum 4). -/
def empty (cap : Nat := defaultCapacity) : RobinHoodHashMap α β :=
  let c := max cap 4
  { buckets  := Array.mk (List.replicate c none)
    size     := 0
    capacity := c
    hCapPos  := by omega
    hBuckets := by simp [Array.size, List.length_replicate] }

instance : EmptyCollection (RobinHoodHashMap α β) := ⟨empty⟩
instance : Inhabited (RobinHoodHashMap α β) := ⟨empty⟩

/-- Ideal bucket index for a key. -/
@[inline] def idealIndex (m : RobinHoodHashMap α β) (k : α) : Nat :=
  (hash k).toUSize.toNat % m.capacity

/-- Next bucket index (wrapping). -/
@[inline] def nextIdx (m : RobinHoodHashMap α β) (i : Nat) : Nat :=
  (i + 1) % m.capacity

/-- Previous bucket index (wrapping). -/
@[inline] def prevIdx (m : RobinHoodHashMap α β) (i : Nat) : Nat :=
  (i + m.capacity - 1) % m.capacity

-- ============================================================================
-- Section 3: Lookup
-- ============================================================================

/-- Look up a key. Uses Robin Hood early termination. -/
def get? (m : RobinHoodHashMap α β) (k : α) : Option β :=
  go (m.idealIndex k) 0 m.capacity
where
  go (idx dist fuel : Nat) : Option β :=
    if fuel = 0 then none
    else if h : idx < m.buckets.size then
      match m.buckets[idx] with
      | none => none
      | some entry =>
        if entry.key == k then some entry.val
        else if entry.psl < dist then none
        else go (m.nextIdx idx) (dist + 1) (fuel - 1)
    else none

def contains (m : RobinHoodHashMap α β) (k : α) : Bool := (m.get? k).isSome

-- ============================================================================
-- Section 4: Insert with Robin Hood displacement
-- ============================================================================

/-- Core insert without resize. -/
def insertCore (m : RobinHoodHashMap α β) (k : α) (v : β) : RobinHoodHashMap α β :=
  go m k v (m.idealIndex k) 0 m.capacity
where
  go (m : RobinHoodHashMap α β) (curK : α) (curV : β)
      (idx dist fuel : Nat) : RobinHoodHashMap α β :=
    if fuel = 0 then m
    else if h : idx < m.buckets.size then
      match m.buckets[idx] with
      | none =>
        { m with
          buckets  := m.buckets.set idx (some ⟨curK, curV, dist⟩) h
          size     := m.size + 1
          hBuckets := by rw [Array.size_set]; exact m.hBuckets }
      | some entry =>
        if entry.key == curK then
          { m with
            buckets  := m.buckets.set idx (some ⟨curK, curV, entry.psl⟩) h
            hBuckets := by rw [Array.size_set]; exact m.hBuckets }
        else if entry.psl < dist then
          let m' :=
            { m with
              buckets  := m.buckets.set idx (some ⟨curK, curV, dist⟩) h
              hBuckets := by rw [Array.size_set]; exact m.hBuckets }
          go m' entry.key entry.val (m'.nextIdx idx) (entry.psl + 1) (fuel - 1)
        else
          go m curK curV (m.nextIdx idx) (dist + 1) (fuel - 1)
    else m

/-- Resize to double capacity, reinserting all entries. -/
def resize (m : RobinHoodHashMap α β) : RobinHoodHashMap α β :=
  let newCap := max (m.capacity * 2) 4
  let init : RobinHoodHashMap α β :=
    { buckets  := Array.mk (List.replicate newCap none)
      size     := 0
      capacity := newCap
      hCapPos  := by omega
      hBuckets := by simp [Array.size, List.length_replicate] }
  m.buckets.foldl (init := init) fun acc bucket =>
    match bucket with
    | some entry => acc.insertCore entry.key entry.val
    | none => acc

/-- Insert with load factor check (resize at 7/8). -/
def insert (m : RobinHoodHashMap α β) (k : α) (v : β) : RobinHoodHashMap α β :=
  let m' := m.insertCore k v
  if m'.size * 8 ≥ m'.capacity * 7 then m'.resize else m'

-- ============================================================================
-- Section 5: Erase with backward-shift deletion
-- ============================================================================

/-- Find bucket index of a key. -/
def findIndex (m : RobinHoodHashMap α β) (k : α) : Option Nat :=
  go (m.idealIndex k) 0 m.capacity
where
  go (idx dist fuel : Nat) : Option Nat :=
    if fuel = 0 then none
    else if h : idx < m.buckets.size then
      match m.buckets[idx] with
      | none => none
      | some entry =>
        if entry.key == k then some idx
        else if entry.psl < dist then none
        else go (m.nextIdx idx) (dist + 1) (fuel - 1)
    else none

/-- Backward-shift: fill gap after deletion. -/
def backwardShift (m : RobinHoodHashMap α β) (idx fuel : Nat) :
    RobinHoodHashMap α β :=
  if fuel = 0 then m
  else if h : idx < m.buckets.size then
    match m.buckets[idx] with
    | none => m
    | some entry =>
      if entry.psl = 0 then m
      else
        let prevI := m.prevIdx idx
        if hPrev : prevI < m.buckets.size then
          let b1 := m.buckets.set prevI (some ⟨entry.key, entry.val, entry.psl - 1⟩) hPrev
          have hb1 : b1.size = m.capacity := by rw [Array.size_set]; exact m.hBuckets
          let b2 := b1.set idx none (by rw [hb1, ← m.hBuckets]; exact h)
          let m' : RobinHoodHashMap α β :=
            { buckets := b2, size := m.size, capacity := m.capacity,
              hCapPos := m.hCapPos,
              hBuckets := by rw [Array.size_set]; exact hb1 }
          backwardShift m' (m.nextIdx idx) (fuel - 1)
        else m
  else m

/-- Erase a key using backward-shift deletion. -/
def erase (m : RobinHoodHashMap α β) (k : α) : RobinHoodHashMap α β :=
  match m.findIndex k with
  | none => m
  | some idx =>
    if h : idx < m.buckets.size then
      let m' := { m with
        buckets := m.buckets.set idx none h
        size    := m.size - 1
        hBuckets := by rw [Array.size_set]; exact m.hBuckets }
      m'.backwardShift (m'.nextIdx idx) m'.capacity
    else m

-- ============================================================================
-- Section 6: Fold, toList, filter
-- ============================================================================

def fold {γ : Type _} (m : RobinHoodHashMap α β) (init : γ)
    (f : γ → α → β → γ) : γ :=
  m.buckets.foldl (init := init) fun acc bucket =>
    match bucket with
    | some entry => f acc entry.key entry.val
    | none => acc

def toList (m : RobinHoodHashMap α β) : List (α × β) :=
  m.buckets.toList.filterMap fun
    | some entry => some (entry.key, entry.val)
    | none => none

def filter (m : RobinHoodHashMap α β) (f : α → β → Bool) :
    RobinHoodHashMap α β :=
  let kept := m.toList.filter fun (k, v) => f k v
  kept.foldl (init := empty m.capacity) fun acc (k, v) => acc.insert k v

-- ============================================================================
-- Section 7: Well-formedness invariant (proof Layer 1)
-- ============================================================================

/-- PSL matches actual probe distance from ideal index. -/
def pslCorrect (m : RobinHoodHashMap α β) : Prop :=
  ∀ (i : Nat) (hi : i < m.buckets.size) (entry : Entry α β),
    m.buckets[i] = some entry →
    entry.psl = (i + m.capacity - m.idealIndex entry.key) % m.capacity

/-- No duplicate keys in occupied buckets. -/
def noDuplicateKeys (m : RobinHoodHashMap α β) : Prop :=
  ∀ (i j : Nat) (hi : i < m.buckets.size) (hj : j < m.buckets.size)
    (ei ej : Entry α β),
    m.buckets[i] = some ei → m.buckets[j] = some ej →
    ei.key == ej.key = true → i = j

/-- Robin Hood ordering: adjacent occupied buckets satisfy PSL constraint. -/
def robinHoodOrdering (m : RobinHoodHashMap α β) : Prop :=
  ∀ (i : Nat) (hi : i < m.buckets.size) (entry : Entry α β),
    m.buckets[i] = some entry →
    ∀ (hNext : m.nextIdx i < m.buckets.size) (nextEntry : Entry α β),
      m.buckets[m.nextIdx i] = some nextEntry →
      nextEntry.psl ≤ entry.psl + 1

/-- Empty buckets terminate probe chains. -/
def noSpuriousGaps (m : RobinHoodHashMap α β) : Prop :=
  ∀ (i : Nat) (hi : i < m.buckets.size),
    m.buckets[i] = none →
    ∀ (hNext : m.nextIdx i < m.buckets.size) (nextEntry : Entry α β),
      m.buckets[m.nextIdx i] = some nextEntry →
      nextEntry.psl = 0

/-- Full well-formedness predicate. -/
structure WellFormed (m : RobinHoodHashMap α β) : Prop where
  pslOk    : m.pslCorrect
  noDups   : m.noDuplicateKeys
  ordering : m.robinHoodOrdering
  noGaps   : m.noSpuriousGaps
  sizeOk   : m.size = m.buckets.toList.countP (·.isSome)

-- ============================================================================
-- Section 8: Foundational lemmas (proof Layer 2)
-- ============================================================================

theorem empty_wellFormed (cap : Nat) :
    WellFormed (empty (α := α) (β := β) cap) where
  pslOk := by sorry -- TPI-D12 N1-G: vacuous on all-none buckets
  noDups := by sorry -- TPI-D12 N1-G: vacuous on all-none buckets
  ordering := by sorry -- TPI-D12 N1-G: vacuous on all-none buckets
  noGaps := by sorry -- TPI-D12 N1-G: vacuous on all-none buckets
  sizeOk := by sorry -- TPI-D12 N1-G: countP on all-none = 0

-- ============================================================================
-- Section 9: Bridge lemma decomposition (proof Layer 3)
--
-- These decompose get?_insert and get?_erase into sub-lemmas:
--   get?_insert = insertCore_contains_self ∧ insertCore_preserves_other
--                 ∧ resize_preserves_get?
--   get?_erase  = erase_removes_self ∧ erase_preserves_other
-- ============================================================================

/-- After insertCore, the inserted key is retrievable. -/
theorem insertCore_contains_self (m : RobinHoodHashMap α β)
    [EquivBEq α] [LawfulHashable α]
    (k : α) (v : β) (wf : WellFormed m) :
    (m.insertCore k v).get? k = some v := by
  sorry -- TPI-D12 N1-G: probe chain induction + WF preservation

/-- After insertCore, other keys' lookups are unchanged. -/
theorem insertCore_preserves_other (m : RobinHoodHashMap α β)
    [EquivBEq α] [LawfulHashable α]
    (k a : α) (v : β) (hNe : (k == a) = false) (wf : WellFormed m) :
    (m.insertCore k v).get? a = m.get? a := by
  sorry -- TPI-D12 N1-G: Robin Hood displacement preserves findability

/-- Resize preserves all lookups. -/
theorem resize_preserves_get? (m : RobinHoodHashMap α β)
    [EquivBEq α] [LawfulHashable α] (k : α) (wf : WellFormed m) :
    m.resize.get? k = m.get? k := by
  sorry -- TPI-D12 N1-G: induction on buckets

/-- insertCore preserves well-formedness. -/
theorem insertCore_wellFormed (m : RobinHoodHashMap α β)
    [EquivBEq α] [LawfulHashable α]
    (k : α) (v : β) (wf : WellFormed m) :
    WellFormed (m.insertCore k v) := by
  sorry -- TPI-D12 N1-G: case analysis on insertion path

/-- Resize preserves well-formedness. -/
theorem resize_wellFormed (m : RobinHoodHashMap α β)
    [EquivBEq α] [LawfulHashable α] (wf : WellFormed m) :
    WellFormed m.resize := by
  sorry -- TPI-D12 N1-G: induction on buckets

/-- After erase, the erased key is not found. -/
theorem erase_removes_self (m : RobinHoodHashMap α β)
    [EquivBEq α] [LawfulHashable α] (k : α) (wf : WellFormed m) :
    (m.erase k).get? k = none := by
  sorry -- TPI-D12 N1-G: cleared → backwardShift doesn't reintroduce

/-- After erase, other keys' lookups are unchanged. -/
theorem erase_preserves_other (m : RobinHoodHashMap α β)
    [EquivBEq α] [LawfulHashable α]
    (k a : α) (hNe : (k == a) = false) (wf : WellFormed m) :
    (m.erase k).get? a = m.get? a := by
  sorry -- TPI-D12 N1-G: backwardShift preserves via PSL decrement

/-- Erase preserves well-formedness. -/
theorem erase_wellFormed (m : RobinHoodHashMap α β)
    [EquivBEq α] [LawfulHashable α] (k : α) (wf : WellFormed m) :
    WellFormed (m.erase k) := by
  sorry -- TPI-D12 N1-G: clear + backwardShift preserves WF

-- ============================================================================
-- Section 10: Bridge lemmas (proof Layer 4)
-- ============================================================================

/-- WS-N1: `get?` after `insert`. Matches `HashMap_get?_insert`. -/
theorem get?_insert [EquivBEq α] [LawfulHashable α]
    {m : RobinHoodHashMap α β} {k a : α} {v : β} (wf : WellFormed m) :
    (m.insert k v).get? a = if k == a then some v else m.get? a := by
  sorry -- TPI-D12 N1-G: compose insertCore_contains_self, insertCore_preserves_other, resize_preserves_get?

/-- WS-N1: `get?` on empty. Matches `HashMap_get?_empty`. -/
@[simp]
theorem get?_empty_simp {a : α} :
    (∅ : RobinHoodHashMap α β).get? a = none := by
  sorry -- TPI-D12 N1-G: unfold get? on empty buckets

/-- WS-N1: `get?` after `erase`. Matches `HashMap_get?_erase`. -/
theorem get?_erase [EquivBEq α] [LawfulHashable α]
    {m : RobinHoodHashMap α β} {k a : α} (wf : WellFormed m) :
    (m.erase k).get? a = if k == a then none else m.get? a := by
  cases hka : k == a with
  | false => exact erase_preserves_other m k a hka wf
  | true => sorry -- TPI-D12 N1-G: BEq rewrite + erase_removes_self

/-- WS-N1: fold equals foldl over toList. -/
theorem fold_eq_foldl_toList {γ : Type _}
    (m : RobinHoodHashMap α β) (init : γ) (f : γ → α → β → γ) :
    m.fold init f = m.toList.foldl (fun acc (kv : α × β) => f acc kv.1 kv.2) init := by
  sorry -- TPI-D12 N1-G: Array.foldl → List.foldl + filterMap induction

/-- WS-N1: Erase does not increase size. -/
theorem size_erase_le (m : RobinHoodHashMap α β) (k : α) :
    (m.erase k).size ≤ m.size := by
  sorry -- TPI-D12 N1-G: unfold erase, case analysis

end RobinHoodHashMap

-- ============================================================================
-- Section 11: RobinHoodHashSet wrapper
-- ============================================================================

/-- Robin Hood HashSet: thin wrapper over `RobinHoodHashMap α Unit`. -/
structure RobinHoodHashSet (α : Type) [BEq α] [Hashable α] where
  inner : RobinHoodHashMap α Unit

namespace RobinHoodHashSet

variable {α : Type} [BEq α] [Hashable α]

instance : EmptyCollection (RobinHoodHashSet α) := ⟨⟨∅⟩⟩
instance : Inhabited (RobinHoodHashSet α) := ⟨⟨∅⟩⟩

def empty (cap : Nat := RobinHoodHashMap.defaultCapacity) : RobinHoodHashSet α :=
  ⟨RobinHoodHashMap.empty cap⟩

def insert (s : RobinHoodHashSet α) (a : α) : RobinHoodHashSet α :=
  ⟨s.inner.insert a ()⟩

def contains (s : RobinHoodHashSet α) (a : α) : Bool :=
  s.inner.contains a

def erase (s : RobinHoodHashSet α) (a : α) : RobinHoodHashSet α :=
  ⟨s.inner.erase a⟩

def size (s : RobinHoodHashSet α) : Nat := s.inner.size

def toList (s : RobinHoodHashSet α) : List α :=
  s.inner.toList.map Prod.fst

def fold {γ : Type _} (s : RobinHoodHashSet α) (init : γ) (f : γ → α → γ) : γ :=
  s.inner.fold init fun acc k _ => f acc k

-- HashSet bridge lemmas

/-- WS-N1: Contains on empty returns false. -/
@[simp]
theorem contains_empty {a : α} :
    (∅ : RobinHoodHashSet α).contains a = false := by
  sorry -- TPI-D12 N1-G: unfold to get?_empty_simp

/-- WS-N1: Contains after insert (iff). -/
theorem contains_insert_iff [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (s : RobinHoodHashSet α) (a b : α)
    (wf : RobinHoodHashMap.WellFormed s.inner) :
    (s.insert a).contains b = true ↔ b = a ∨ s.contains b = true := by
  sorry -- TPI-D12 N1-G: unfold to get?_insert

/-- WS-N1: Negative contains after insert. -/
theorem not_contains_insert [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (s : RobinHoodHashSet α) (a b : α)
    (wf : RobinHoodHashMap.WellFormed s.inner) :
    (s.insert a).contains b = false ↔ b ≠ a ∧ s.contains b = false := by
  sorry -- TPI-D12 N1-G: from contains_insert_iff

/-- WS-N1: Self-membership after insert. -/
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (s : RobinHoodHashSet α) (a : α)
    (wf : RobinHoodHashMap.WellFormed s.inner) :
    (s.insert a).contains a = true := by
  sorry -- TPI-D12 N1-G: from contains_insert_iff

/-- WS-N1: Contains after erase. -/
theorem contains_erase [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (s : RobinHoodHashSet α) (a b : α)
    (wf : RobinHoodHashMap.WellFormed s.inner) :
    (s.erase a).contains b = (!(a == b) && s.contains b) := by
  sorry -- TPI-D12 N1-G: unfold to get?_erase

end RobinHoodHashSet

end SeLe4n.Data
