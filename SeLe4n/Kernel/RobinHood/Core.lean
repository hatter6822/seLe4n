-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

/-!
# Robin Hood Hash Table — Core Types and Operations

V7-C: All public `RHTable` operations (`get?`, `contains`, `insert`, `erase`,
`filter`, `resize`, `ofList`, `toList`) require `[LawfulBEq α]` as an explicit
API-level constraint. This ensures that key equality is propositionally sound
(i.e., `a == b = true → a = b`), which is necessary for the correctness proofs
in `Invariant/` and `Bridge.lean`. All kernel identifier types (`ObjId`,
`ThreadId`, `Priority`, `Slot`, `CPtr`, `Irq`, etc.) satisfy `LawfulBEq`
via their `Nat`-wrapper `BEq` instances.
-/

namespace SeLe4n.Kernel.RobinHood

-- ============================================================================
-- N1-A: Core Data Types
-- ============================================================================

/-- An entry in a Robin Hood hash table, storing key, value, and probe distance
    from the entry's ideal (home) position. -/
structure RHEntry (α : Type) (β : Type) where
  key   : α
  value : β
  dist  : Nat
  deriving Repr

/-- A Robin Hood hash table with open addressing, linear probing, and
    Robin Hood displacement.  Single-representation architecture:
    one `Array (Option (RHEntry α β))` — no split arrays. -/
structure RHTable (α : Type) (β : Type) where
  slots     : Array (Option (RHEntry α β))
  size      : Nat
  capacity  : Nat
  -- AE2-A (U-28): Enforce minimum capacity of 4 to guarantee the
  -- insert-size guard (`insert_size_lt_capacity`) holds for all tables.
  -- Tables with capacity 1–3 bypassed the guard because `invExtK` requires
  -- `4 ≤ capacity` but the old `0 < capacity` did not.
  hCapGe4   : 4 ≤ capacity
  hSlotsLen : slots.size = capacity

/-- AE2-A: Backward-compatible accessor — `4 ≤ capacity` implies `0 < capacity`. -/
theorem RHTable.hCapPos (t : RHTable α β) : 0 < t.capacity := by
  have := t.hCapGe4; omega

instance [Repr α] [Repr β] : Repr (RHTable α β) where
  reprPrec t _ :=
    f!"RHTable(size={t.size}, capacity={t.capacity}, slots={repr t.slots})"

-- ============================================================================
-- N1-A3: Index functions
-- ============================================================================

/-- Compute the ideal (home) slot index for a key via modular hashing. -/
@[inline] def idealIndex [Hashable α] (k : α) (capacity : Nat)
    (_hCapPos : 0 < capacity) : Nat :=
  (hash k).toNat % capacity

/-- Advance to the next slot index with wrap-around. -/
@[inline] def nextIndex (i : Nat) (capacity : Nat) : Nat :=
  (i + 1) % capacity

-- ============================================================================
-- N1-A4: Index bound proofs
-- ============================================================================

theorem idealIndex_lt [Hashable α] (k : α) (capacity : Nat)
    (hCapPos : 0 < capacity) :
    idealIndex k capacity hCapPos < capacity :=
  Nat.mod_lt _ hCapPos

theorem nextIndex_lt (i : Nat) (capacity : Nat) (hCapPos : 0 < capacity) :
    nextIndex i capacity < capacity :=
  Nat.mod_lt _ hCapPos

-- ============================================================================
-- N1-B: Empty Table Constructor
-- ============================================================================

/-- Count occupied (non-none) slots in an array. -/
def countOccupied (slots : Array (Option (RHEntry α β))) : Nat :=
  slots.toList.countP (·.isSome)

/-- Well-formedness predicate for Robin Hood tables. -/
structure RHTable.WF [BEq α] [Hashable α] (t : RHTable α β) : Prop where
  slotsLen   : t.slots.size = t.capacity
  capPos     : 0 < t.capacity
  sizeCount  : t.size = countOccupied t.slots
  sizeBound  : t.size ≤ t.capacity

/-- Create an empty Robin Hood hash table with the given capacity.
    AE2-A (U-28): Requires `4 ≤ cap` to guarantee the insert-size guard
    (`insert_size_lt_capacity`) holds without caller-side obligations. -/
def RHTable.empty (cap : Nat) (hCapGe4 : 4 ≤ cap := by omega) : RHTable α β :=
  { slots     := ⟨List.replicate cap none⟩
    size      := 0
    capacity  := cap
    hCapGe4   := hCapGe4
    hSlotsLen := by simp [Array.size] }

/-- N1-B2: The empty table is well-formed (all 4 WF conjuncts). -/
theorem RHTable.empty_wf [BEq α] [Hashable α] (cap : Nat) (hCapGe4 : 4 ≤ cap) :
    (RHTable.empty cap hCapGe4 : RHTable α β).WF where
  slotsLen  := by simp [RHTable.empty, Array.size]
  capPos    := by simp [RHTable.empty]; omega
  sizeCount := by simp [RHTable.empty, countOccupied, List.countP_replicate]
  sizeBound := Nat.zero_le _

-- ============================================================================
-- N1-C: Bounded Insertion Loop
-- ============================================================================

/-- N1-C1–C5: Fuel-bounded insertion loop with Robin Hood displacement.
    Returns `(slots', isNew)` where `isNew = true` when a fresh key was added.

    Operational behavior per slot inspection:
    1. Empty slot → place entry, return `(slots', true)`
    2. Key match  → update value in place, return `(slots', false)`
    3. Robin Hood swap (`resident.dist < d`) → displace resident, continue
    4. Continue probing (`resident.dist ≥ d`) → advance index, increment dist
    5. Fuel exhausted → return `(slots, false)` (table full) -/
def insertLoop [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (v : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity)
    : Array (Option (RHEntry α β)) × Bool :=
  match fuel with
  -- AUDIT-NOTE: D-RH02 / LOW-06 — Fuel exhaustion cannot occur under maintained
  -- invariants. The caller (`insert`) passes `fuel = capacity`, and the `invExtK`
  -- bundle guarantees the load factor remains below 1.0, ensuring at least one
  -- empty slot exists. The maximum probe distance is therefore bounded by
  -- `capacity - 1`, and fuel always exceeds this bound. The `false` return flag
  -- is the only signal of incomplete insertion — callers should treat it as a
  -- table-full condition.
  -- CONSEQUENCE if reached: no mutation — `(slots, false)` returned unchanged.
  -- WF PROPERTY: `invExtK` → `size < capacity` → at least one empty slot.
  | 0 => (slots, false)
  | fuel' + 1 =>
    let i := idx % capacity
    have hIdx : i < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    match slots[i] with
    | none =>
      (slots.set i (some ⟨k, v, d⟩), true)
    | some e =>
      if e.key == k then
        (slots.set i (some { e with value := v }), false)
      else if e.dist < d then
        let slots' := slots.set i (some ⟨k, v, d⟩)
        insertLoop fuel' (i + 1) e.key e.value (e.dist + 1)
          slots' capacity (by rw [Array.size_set]; exact hLen) hCapPos
      else
        insertLoop fuel' (i + 1) k v (d + 1) slots capacity hLen hCapPos

/-- N1-D2: `insertLoop` preserves array size. -/
theorem insertLoop_preserves_len [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (v : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity) :
    (insertLoop fuel idx k v d slots capacity hLen hCapPos).1.size = slots.size := by
  induction fuel generalizing idx k v d slots hLen with
  | zero => simp [insertLoop]
  | succ n ih =>
    unfold insertLoop
    simp only []
    split
    · simp [Array.size_set]
    · next e =>
      split
      · simp [Array.size_set]
      · split
        · rw [ih]; simp [Array.size_set]
        · exact ih ..

-- ============================================================================
-- N1-E: Bounded Lookup Loop
-- ============================================================================

/-- N1-E1: Fuel-bounded lookup loop.  Uses Robin Hood early termination:
    - Empty slot → key absent
    - Resident dist < search dist → key absent (Robin Hood property)
    - Key match → return value -/
def getLoop [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity)
    : Option β :=
  match fuel with
  -- AUDIT-NOTE: D-RH02 — Fuel exhaustion cannot occur under maintained
  -- invariants. The caller (`get?`) passes `fuel = capacity`. Robin Hood
  -- early termination (empty slot or dist < search dist) is guaranteed to
  -- trigger within `capacity` steps because at least one slot is empty
  -- under `invExtK` (`size < capacity`).
  -- CONSEQUENCE if reached: `none` returned — correct "key absent" semantics.
  -- WF PROPERTY: `invExtK` → at least one empty slot within probe chain.
  | 0 => none
  | fuel' + 1 =>
    let i := idx % capacity
    have hIdx : i < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    match slots[i] with
    | none => none
    | some e =>
      if e.key == k then some e.value
      else if e.dist < d then none
      else getLoop fuel' (i + 1) k (d + 1) slots capacity hLen hCapPos

/-- N1-E2: Top-level lookup returning the value associated with a key. -/
def RHTable.get? [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) (k : α) : Option β :=
  let start := idealIndex k t.capacity t.hCapPos
  getLoop t.capacity start k 0 t.slots t.capacity t.hSlotsLen t.hCapPos

/-- N1-E3: Membership test. -/
def RHTable.contains [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) (k : α) : Bool :=
  (t.get? k).isSome

-- ============================================================================
-- N1-F: Bounded Erasure (find + backshift)
-- ============================================================================

/-- N1-F1: Fuel-bounded find loop — locate the slot containing a key.
    Uses same early-termination rules as getLoop. -/
def findLoop [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity)
    : Option Nat :=
  match fuel with
  -- AUDIT-NOTE: D-RH02 — Same fuel-safety argument as `getLoop`. Caller
  -- (`erase`) passes `fuel = capacity`. Robin Hood early termination
  -- guarantees triggering within capacity steps under `invExtK`.
  -- CONSEQUENCE if reached: `none` returned — no slot found, erase is no-op.
  -- WF PROPERTY: `invExtK` → at least one empty slot within probe chain.
  | 0 => none
  | fuel' + 1 =>
    let i := idx % capacity
    have hIdx : i < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    match slots[i] with
    | none => none
    | some e =>
      if e.key == k then some i
      else if e.dist < d then none
      else findLoop fuel' (i + 1) k (d + 1) slots capacity hLen hCapPos

/-- N1-F2: Fuel-bounded backward-shift loop.  After clearing a slot,
    shift subsequent entries backward (decrementing dist) until we hit
    an empty slot or an entry at its ideal position (dist = 0). -/
def backshiftLoop
    (fuel : Nat) (gapIdx : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity)
    : Array (Option (RHEntry α β)) :=
  match fuel with
  -- AUDIT-NOTE: D-RH02 / LOW-06 — Fuel exhaustion cannot occur under maintained
  -- invariants. The caller (`erase`) passes `fuel = capacity`, and the `invExtK`
  -- bundle guarantees at least one empty slot exists (load < 1.0). Backshift
  -- terminates at the first empty slot or an entry at its ideal position
  -- (dist = 0), both of which are guaranteed to occur within `capacity` steps.
  -- CONSEQUENCE if reached: unchanged `slots` returned — no backshift applied.
  -- WF PROPERTY: `invExtK` → `size < capacity` → empty slot within chain.
  | 0 => slots
  | fuel' + 1 =>
    let nextI := (gapIdx + 1) % capacity
    have hNext : nextI < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    match slots[nextI] with
    | none => slots
    | some e =>
      if e.dist == 0 then slots
      else
        have hGap : gapIdx % capacity < slots.size := by
          rw [hLen]; exact Nat.mod_lt _ hCapPos
        let slots' := slots.set (gapIdx % capacity) (some { e with dist := e.dist - 1 })
          hGap
        let slots'' := slots'.set nextI none (by rw [Array.size_set]; exact hNext)
        backshiftLoop fuel' nextI slots'' capacity
          (by rw [Array.size_set, Array.size_set]; exact hLen) hCapPos

/-- N1-F4: `backshiftLoop` preserves array size. -/
theorem backshiftLoop_preserves_len
    (fuel : Nat) (gapIdx : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity) :
    (backshiftLoop fuel gapIdx slots capacity hLen hCapPos).size = slots.size := by
  induction fuel generalizing gapIdx slots hLen with
  | zero => simp [backshiftLoop]
  | succ n ih =>
    unfold backshiftLoop
    simp only []
    split
    · rfl
    · next e =>
      split
      · rfl
      · rw [ih]; simp [Array.size_set]

/-- N1-F3: Top-level erase.  Two-phase: find the key, then backshift.

**V7-H: Size decrement safety.** The `size - 1` in the `some` branch is safe
(never underflows to wrap-around) because this branch is only reached when
`findLoop` locates the key in the table. Under `invExt` (specifically the `WF`
sub-invariant), `size = countOccupied slots`, which guarantees `size > 0` when
at least one entry is present. The `none` branch returns the table unchanged,
so `size - 1` is never applied to an empty table. Nat subtraction in Lean
saturates at 0, so even without `invExt` there is no arithmetic panic — but
the invariant ensures the decrement is semantically correct. -/
def RHTable.erase [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) (k : α) : RHTable α β :=
  let start := idealIndex k t.capacity t.hCapPos
  match findLoop t.capacity start k 0 t.slots t.capacity t.hSlotsLen t.hCapPos with
  | none => t
  | some idx =>
    have hIdx : idx % t.capacity < t.slots.size := by
      rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
    let slots' := t.slots.set (idx % t.capacity) none hIdx
    have hLen' : slots'.size = t.capacity := by rw [Array.size_set]; exact t.hSlotsLen
    let slots'' := backshiftLoop t.capacity idx slots' t.capacity hLen' t.hCapPos
    { slots     := slots''
      size      := t.size - 1
      capacity  := t.capacity
      hCapGe4   := t.hCapGe4
      hSlotsLen := by
        rw [backshiftLoop_preserves_len]; rw [Array.size_set]; exact t.hSlotsLen }

-- ============================================================================
-- N1-G: Fold, Resize, and Utility Operations
-- ============================================================================

/-- N1-G1: Fold over all occupied entries in the table. -/
def RHTable.fold (t : RHTable α β) (init : γ) (f : γ → α → β → γ) : γ :=
  t.slots.foldl (fun acc slot =>
    match slot with
    | none => acc
    | some e => f acc e.key e.value) init

/-- N1-G2: Collect all key-value pairs into a list. -/
def RHTable.toList [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) : List (α × β) :=
  t.fold [] (fun acc k v => (k, v) :: acc)

/-- Internal insert without resize check — used by `resize` to avoid circularity.
    Composes `insertLoop` with table metadata bookkeeping. -/
protected def RHTable.insertNoResize [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) : RHTable α β :=
  let start := idealIndex k t.capacity t.hCapPos
  let result := insertLoop t.capacity start k v 0
    t.slots t.capacity t.hSlotsLen t.hCapPos
  { slots     := result.1
    size      := if result.2 then t.size + 1 else t.size
    capacity  := t.capacity
    hCapGe4   := t.hCapGe4
    hSlotsLen := by
      show (insertLoop t.capacity start k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos).1.size
           = t.capacity
      rw [insertLoop_preserves_len]; exact t.hSlotsLen }

/-- `insertNoResize` preserves capacity (definitional). -/
protected theorem RHTable.insertNoResize_capacity [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) :
    (t.insertNoResize k v).capacity = t.capacity := rfl

/-- N1-G3: Resize the table by doubling capacity and re-inserting all entries. -/
def RHTable.resize [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) : RHTable α β :=
  let newCap := t.capacity * 2
  have hNewGe4 : 4 ≤ newCap := by have := t.hCapGe4; omega
  let empty : RHTable α β := RHTable.empty newCap hNewGe4
  t.fold empty (fun acc k v => acc.insertNoResize k v)

/-- The fold step used by resize preserves capacity.
    Proved via `Array.foldl_induction`. -/
protected theorem RHTable.resize_fold_capacity [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) :
    (t.resize).capacity = t.capacity * 2 := by
  unfold resize fold
  have hStep : ∀ (i : Fin t.slots.size) (acc : RHTable α β),
      acc.capacity = t.capacity * 2 →
      (match t.slots[i] with
       | none => acc
       | some e => acc.insertNoResize e.key e.value).capacity = t.capacity * 2 := by
    intro i acc hAcc
    split
    · exact hAcc
    · rw [RHTable.insertNoResize_capacity]; exact hAcc
  exact Array.foldl_induction
    (motive := fun _ (acc : RHTable α β) => acc.capacity = t.capacity * 2)
    (by simp [RHTable.empty])
    hStep

/-- N1-G4: After resize, slots array has the doubled capacity. -/
theorem RHTable.resize_preserves_len [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) :
    (t.resize).slots.size = t.capacity * 2 := by
  rw [← t.resize_fold_capacity]; exact (t.resize).hSlotsLen

-- ============================================================================
-- N1-D: Top-Level Insert with Resize
-- ============================================================================

/-- N1-D1: Top-level insert — checks load factor (75%) and resizes if needed,
    then delegates to `insertLoop`. -/
def RHTable.insert [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) (k : α) (v : β)
    : RHTable α β :=
  let t' := if t.size * 4 ≥ t.capacity * 3 then t.resize else t
  t'.insertNoResize k v

/-- N1-D3: `insertNoResize` increases size by at most 1. -/
theorem RHTable.insertNoResize_size_le [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) :
    (t.insertNoResize k v).size ≤ t.size + 1 := by
  unfold RHTable.insertNoResize
  dsimp only []
  split <;> omega

-- ============================================================================
-- N1-G (continued): Instances
-- ============================================================================

instance {κ : Type} {ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] :
    Membership κ (RHTable κ ν) where
  mem t k := t.contains k = true

/-- GetElem instance for proof-bounded access (required by GetElem?). -/
instance {κ : Type} {ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] :
    GetElem (RHTable κ ν) κ ν (fun t k => (t.get? k).isSome) where
  getElem t k h := (t.get? k).get h

/-- GetElem? instance enabling `t[k]?` bracket notation.
V7-C: `LawfulBEq` is an explicit API-level requirement — all kernel
identifier types (`ObjId`, `ThreadId`, `Priority`, `Slot`, etc.) satisfy
`LawfulBEq` via their `Nat`-based `BEq` instances. -/
instance {κ : Type} {ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] :
    GetElem? (RHTable κ ν) κ ν (fun t k => (t.get? k).isSome) where
  getElem? t k := t.get? k
  getElem! t k := (t.get? k).getD default

end SeLe4n.Kernel.RobinHood
