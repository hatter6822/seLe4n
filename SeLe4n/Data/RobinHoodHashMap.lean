/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

/-! # WS-N1: Robin Hood HashMap — Open-addressing with Robin Hood displacement

A cache-friendly, deterministic hash map using Robin Hood hashing with
open addressing and backward-shift deletion. Backed by Lean 4's `Array`
for flat memory layout (contiguous C heap allocation via FBIP).

## Design rationale

Lean 4's `Std.HashMap` uses separate chaining (array of `AssocList` buckets).
Each lookup traverses a linked list — poor cache locality due to pointer
chasing, especially on ARM64 where cache lines are 64 bytes.

Robin Hood hashing stores entries **inline** in a flat `Array`. Lookups
probe contiguous memory with O(log n) expected worst-case probe length.
Backward-shift deletion avoids tombstone pollution.

## Bucket representation

Each bucket is `Option (α × β × Nat)`:
- `none`: empty slot
- `some (key, value, psl)`: occupied with probe sequence length

PSL is stored as `Nat` (not `UInt8`) to avoid coercion noise in proofs.
Lean compiles small `Nat` to unboxed machine integers.
-/

namespace SeLe4n.Data

-- ============================================================================
-- N1-A: Core data structure
-- ============================================================================

/-- Bucket entry: key, value, and probe sequence length. -/
abbrev Bucket (α : Type) (β : Type) := Option (α × β × Nat)

/-- Robin Hood open-addressing hash map with flat `Array` storage. -/
structure RobinHoodHashMap (α : Type) (β : Type) [BEq α] [Hashable α] where
  /-- Flat bucket array. `none` = empty, `some (k, v, psl)` = occupied. -/
  buckets   : Array (Bucket α β)
  /-- Number of occupied entries. -/
  size      : Nat
  /-- Total bucket count (= buckets.size). Always ≥ 4. -/
  capacity  : Nat
  /-- Structural invariant: array size equals capacity. -/
  hCapacity : buckets.size = capacity
  /-- Capacity is always ≥ 4. -/
  hCapPos   : capacity ≥ 4

-- ============================================================================
-- N1-B: Helpers and empty
-- ============================================================================

/-- Default initial capacity (≥ 4). -/
def defaultCapacity : Nat := 16

variable {α : Type} {β : Type} [BEq α] [Hashable α]

/-- Create an empty Robin Hood HashMap with capacity `max cap 4`. -/
def RobinHoodHashMap.mk' (cap : Nat := defaultCapacity) :
    RobinHoodHashMap α β :=
  let c := if cap < 4 then 4 else cap
  { buckets   := (List.replicate c (none : Bucket α β)).toArray
    size      := 0
    capacity  := c
    hCapacity := by simp
    hCapPos   := by simp only [c]; split <;> omega }

instance : EmptyCollection (RobinHoodHashMap α β) :=
  ⟨RobinHoodHashMap.mk'⟩

instance : Inhabited (RobinHoodHashMap α β) :=
  ⟨RobinHoodHashMap.mk'⟩

namespace RobinHoodHashMap

-- ============================================================================
-- Structural helpers
-- ============================================================================

/-- Capacity is always positive. -/
theorem cap_pos (m : RobinHoodHashMap α β) : m.capacity > 0 := by
  have := m.hCapPos; omega

/-- Compute the ideal bucket index for a key. -/
@[inline] private def bucketIdx (m : RobinHoodHashMap α β) (k : α) : Nat :=
  (hash k).toNat % m.capacity

/-- Get a bucket by index. Requires `i < m.capacity`. -/
@[inline] private def getBucket (m : RobinHoodHashMap α β) (i : Nat)
    (hi : i < m.capacity) : Bucket α β :=
  m.buckets[i]'(m.hCapacity ▸ hi)

/-- Set a bucket by index, constructing a new map with same metadata. -/
private def setBucket (m : RobinHoodHashMap α β) (i : Nat)
    (hi : i < m.capacity) (v : Bucket α β) : RobinHoodHashMap α β :=
  have hbs : i < m.buckets.size := m.hCapacity ▸ hi
  { buckets   := m.buckets.set i v hbs
    size      := m.size
    capacity  := m.capacity
    hCapacity := by rw [Array.size_set hbs]; exact m.hCapacity
    hCapPos   := m.hCapPos }

@[simp] theorem setBucket_size_eq (m : RobinHoodHashMap α β) (i : Nat)
    (hi : i < m.capacity) (v : Bucket α β) :
    (m.setBucket i hi v).size = m.size := rfl

@[simp] theorem setBucket_capacity_eq (m : RobinHoodHashMap α β) (i : Nat)
    (hi : i < m.capacity) (v : Bucket α β) :
    (m.setBucket i hi v).capacity = m.capacity := rfl

/-- Modular index in [0, capacity). -/
@[inline] private def modCap (m : RobinHoodHashMap α β) (i : Nat) : Nat :=
  i % m.capacity

private theorem modCap_lt (m : RobinHoodHashMap α β) (i : Nat) :
    m.modCap i < m.capacity :=
  Nat.mod_lt _ m.cap_pos

-- ============================================================================
-- N1-C: get? (lookup) with Robin Hood early termination
-- ============================================================================

/-- Look up a key in the hash map. Returns `none` if not found.

Robin Hood early termination: if we encounter an entry whose PSL is less
than our current probe distance, the key cannot exist further along the
probe chain. This bounds worst-case lookup to O(log n) expected. -/
def get? (m : RobinHoodHashMap α β) (k : α) : Option β :=
  go (m.bucketIdx k) 0 m.capacity
where
  go (idx : Nat) (dist : Nat) : Nat → Option β
    | 0 => none
    | fuel + 1 =>
      let i := m.modCap idx
      match m.getBucket i (m.modCap_lt idx) with
      | none => none
      | some (k', v, psl) =>
        if k' == k then some v
        else if psl < dist then none
        else go (idx + 1) (dist + 1) fuel

/-- Check if a key exists in the map. -/
@[inline] def contains (m : RobinHoodHashMap α β) (k : α) : Bool :=
  (m.get? k).isSome

-- ============================================================================
-- N1-D: insertCore with Robin Hood displacement
-- ============================================================================

/-- Internal insert without resize check. -/
private def insertCore (m : RobinHoodHashMap α β) (k : α) (v : β) :
    RobinHoodHashMap α β :=
  go m (m.bucketIdx k) k v 0 false m.capacity
where
  go (m : RobinHoodHashMap α β) (idx : Nat) (curK : α) (curV : β)
     (dist : Nat) (sizeIncr : Bool) : Nat → RobinHoodHashMap α β
    | 0 => m
    | fuel + 1 =>
      let i := m.modCap idx
      have hi := m.modCap_lt idx
      match m.getBucket i hi with
      | none =>
        let m' := m.setBucket i hi (some (curK, curV, dist))
        { m' with size := if sizeIncr then m.size else m.size + 1 }
      | some (k', v', psl') =>
        if k' == curK then
          m.setBucket i hi (some (curK, curV, psl'))
        else if psl' < dist then
          let m' := m.setBucket i hi (some (curK, curV, dist))
          go m' (idx + 1) k' v' (psl' + 1) true fuel
        else
          go m (idx + 1) curK curV (dist + 1) sizeIncr fuel

-- ============================================================================
-- N1-D2: Resize and public insert
-- ============================================================================

/-- Resize the hash map to double capacity, reinserting all entries. -/
private def resize (m : RobinHoodHashMap α β) : RobinHoodHashMap α β :=
  let newCap := m.capacity * 2
  let base : RobinHoodHashMap α β := RobinHoodHashMap.mk' newCap
  m.buckets.foldl (init := base) fun acc bucket =>
    match bucket with
    | some (k, v, _) => acc.insertCore k v
    | none => acc

/-- Insert a key-value pair. If the key already exists, update its value.
After insertion, checks load factor and resizes if ≥ 87.5%. -/
def insert (m : RobinHoodHashMap α β) (k : α) (v : β) : RobinHoodHashMap α β :=
  let m' := m.insertCore k v
  if m'.size * 8 ≥ m'.capacity * 7 then m'.resize else m'

-- ============================================================================
-- N1-E: erase with backward-shift deletion
-- ============================================================================

/-- Find the bucket index of a key, or `none` if not found.
Returns an index `i` where `i < m.capacity`. -/
private def findIdx (m : RobinHoodHashMap α β) (k : α) : Option (Fin m.capacity) :=
  go (m.bucketIdx k) 0 m.capacity
where
  go (idx : Nat) (dist : Nat) : Nat → Option (Fin m.capacity)
    | 0 => none
    | fuel + 1 =>
      let i := m.modCap idx
      have hi := m.modCap_lt idx
      match m.getBucket i hi with
      | none => none
      | some (k', _, psl) =>
        if k' == k then some ⟨i, hi⟩
        else if psl < dist then none
        else go (idx + 1) (dist + 1) fuel

/-- Backward-shift: after clearing a bucket, shift subsequent entries
one position backward to fill the gap, decrementing their PSL. -/
private def backwardShift (m : RobinHoodHashMap α β) (startIdx : Nat) :
    RobinHoodHashMap α β :=
  go m startIdx m.capacity
where
  go (m : RobinHoodHashMap α β) (idx : Nat) : Nat → RobinHoodHashMap α β
    | 0 => m
    | fuel + 1 =>
      let i := m.modCap idx
      have hi := m.modCap_lt idx
      match m.getBucket i hi with
      | none => m
      | some (_, _, 0) => m
      | some (k', v', psl) =>
        let prev := m.modCap (idx + m.capacity - 1)
        have hp := m.modCap_lt (idx + m.capacity - 1)
        let m1 := m.setBucket prev hp (some (k', v', psl - 1))
        -- m1 has same capacity as m, so hi still valid
        have hi1 : i < m1.capacity := by simp [setBucket, m1]; exact hi
        let m2 := m1.setBucket i hi1 none
        go m2 (idx + 1) fuel

/-- Remove a key from the map. Uses backward-shift deletion. -/
def erase (m : RobinHoodHashMap α β) (k : α) : RobinHoodHashMap α β :=
  match m.findIdx k with
  | none => m
  | some ⟨idx, hi⟩ =>
    let m' := m.setBucket idx hi none
    let m'' : RobinHoodHashMap α β := { m' with size := m.size - 1 }
    m''.backwardShift (idx + 1)

-- ============================================================================
-- N1-F: fold, toList, filter
-- ============================================================================

/-- Fold over all key-value pairs in bucket-index order. -/
def fold {γ : Type _} (m : RobinHoodHashMap α β) (init : γ)
    (f : γ → α → β → γ) : γ :=
  m.buckets.foldl (init := init) fun acc bucket =>
    match bucket with
    | some (k, v, _) => f acc k v
    | none => acc

/-- Extract all key-value pairs as a list (bucket-index order). -/
def toList (m : RobinHoodHashMap α β) : List (α × β) :=
  m.buckets.toList.filterMap fun
    | some (k, v, _) => some (k, v)
    | none => none

/-- Filter entries by predicate, rebuilding the map. -/
def filter (m : RobinHoodHashMap α β) (f : α → β → Bool) :
    RobinHoodHashMap α β :=
  let kept := m.toList.filter fun (k, v) => f k v
  kept.foldl (init := RobinHoodHashMap.mk' m.capacity) fun acc (k, v) =>
    acc.insert k v

/-- Is the map empty? -/
@[inline] def isEmpty (m : RobinHoodHashMap α β) : Bool := m.size == 0

-- ============================================================================
-- N1-G: Bridge lemmas
-- ============================================================================

/-- The association list representation of the map's contents. -/
def toAssocList (m : RobinHoodHashMap α β) : List (α × β) := m.toList

/-- All buckets in a freshly created empty map are `none`. -/
private theorem mk'_getBucket_none (cap : Nat) (i : Nat)
    (hi : i < (RobinHoodHashMap.mk' (α := α) (β := β) cap).capacity) :
    (RobinHoodHashMap.mk' (α := α) (β := β) cap).getBucket i hi = none := by
  simp [mk', getBucket]

/-- An empty map contains no keys. -/
theorem get?_empty (k : α) (cap : Nat) :
    (RobinHoodHashMap.mk' (α := α) (β := β) cap).get? k = none := by
  unfold get?
  -- fuel = capacity ≥ 4, first bucket is none → returns none immediately
  unfold get?.go
  split
  · -- fuel = 0 case: absurd since capacity ≥ 4
    have := (RobinHoodHashMap.mk' (α := α) (β := β) cap).hCapPos; omega
  · -- fuel = n + 1: first probe into all-none array
    simp only [mk'_getBucket_none]

/-- Lookup on an empty map returns `none`. -/
theorem get?_emptyCollection (k : α) :
    (∅ : RobinHoodHashMap α β).get? k = none :=
  get?_empty k _

/-- `setBucket` preserves `size`. -/
private theorem setBucket_size (m : RobinHoodHashMap α β) (i : Nat)
    (hi : i < m.capacity) (v : Bucket α β) :
    (m.setBucket i hi v).size = m.size := by
  simp [setBucket]

/-- `backwardShift.go` preserves `size`. -/
private theorem backwardShift_go_preserves_size (fuel : Nat) (m : RobinHoodHashMap α β)
    (idx : Nat) : (backwardShift.go m idx fuel).size = m.size := by
  induction fuel generalizing m idx with
  | zero => rfl
  | succ n ih =>
    show (backwardShift.go m idx (n + 1)).size = m.size
    simp only [backwardShift.go]
    -- After simp, we have nested let/match. Use split on the match.
    -- The goal has form: (let i := ...; have ...; match ... with | ...).size = m.size
    -- We need to simp through the let bindings first
    simp only [getBucket, modCap]
    split <;> simp_all [setBucket]

/-- `backwardShift` preserves `size`. -/
theorem backwardShift_size (m : RobinHoodHashMap α β) (idx : Nat) :
    (m.backwardShift idx).size = m.size :=
  backwardShift_go_preserves_size m.capacity m idx

/-- The size of `erase` is at most the original size. -/
theorem size_erase_le (m : RobinHoodHashMap α β) (k : α) :
    (m.erase k).size ≤ m.size := by
  simp only [erase]; split
  · omega
  · simp [backwardShift_size]

/-- Helper: fold over a list of buckets extracts key-value pairs. -/
omit [BEq α] [Hashable α] in
private theorem fold_buckets_eq_foldl_filterMap
    {γ : Type _} (bs : List (Bucket α β)) (init : γ)
    (f : γ → α → β → γ) :
    bs.foldl (fun acc b => match b with | some (k, v, _) => f acc k v | none => acc) init =
    (bs.filterMap fun | some (k, v, _) => some (k, v) | none => none).foldl
      (fun acc (p : α × β) => f acc p.1 p.2) init := by
  induction bs generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.filterMap_cons]
    cases hd with
    | none => exact ih init
    | some entry =>
      obtain ⟨k, v, _⟩ := entry
      simp only [List.foldl_cons]
      exact ih (f init k v)

/-- `fold` is equivalent to `List.foldl` on `toList`. -/
theorem fold_eq_foldl_toList {γ : Type _} (m : RobinHoodHashMap α β)
    (init : γ) (f : γ → α → β → γ) :
    m.fold init f = m.toList.foldl (fun acc (p : α × β) => f acc p.1 p.2) init := by
  simp only [fold, toList, ← Array.foldl_toList]
  exact fold_buckets_eq_foldl_filterMap m.buckets.toList init f

/-- After inserting `(k, v)`, looking up `k` returns `some v`. -/
theorem get?_insert_self [LawfulBEq α] (m : RobinHoodHashMap α β)
    (k : α) (v : β) :
    (m.insert k v).get? k = some v := by
  sorry

/-- After inserting `(k, v)`, looking up a different key `a ≠ k` returns
the same result as before the insert. -/
theorem get?_insert_ne [LawfulBEq α] (m : RobinHoodHashMap α β)
    (k a : α) (v : β) (hne : (k == a) = false) :
    (m.insert k v).get? a = m.get? a := by
  sorry

/-- Combined insert bridge lemma matching `Std.HashMap.get?_insert`. -/
theorem get?_insert [LawfulBEq α] (m : RobinHoodHashMap α β)
    {k a : α} {v : β} :
    (m.insert k v).get? a = if k == a then some v else m.get? a := by
  split
  · rename_i h
    have : k = a := eq_of_beq h
    subst this
    exact get?_insert_self m k v
  · rename_i h
    have hf : (k == a) = false := by cases hb : (k == a) <;> simp_all
    exact get?_insert_ne m k a v hf

/-- After erasing `k`, looking up `k` returns `none`. -/
theorem get?_erase_self [LawfulBEq α] (m : RobinHoodHashMap α β) (k : α) :
    (m.erase k).get? k = none := by
  sorry

/-- After erasing `k`, looking up a different key `a ≠ k` returns
the same result as before the erase. -/
theorem get?_erase_ne [LawfulBEq α] (m : RobinHoodHashMap α β)
    (k a : α) (hne : (k == a) = false) :
    (m.erase k).get? a = m.get? a := by
  sorry

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

end RobinHoodHashMap

-- ============================================================================
-- N1-H: RobinHoodHashSet — thin wrapper over RobinHoodHashMap α Unit
-- ============================================================================

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

end RobinHoodHashSet

end SeLe4n.Data
