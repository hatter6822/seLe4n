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

/-- The lookup loop of `getLoop`, returning the slot that holds `k` as the
table stores it rather than a fresh `some` around its value.  Compiled, the
result is the array's own cell under a reference-count increment, so a lookup
allocates nothing; `RHTable.get?` is compiled through it (`get?_eq_getByEntry`).
Proofs reason about `getLoop`. -/
def getEntryLoop [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity)
    : Option (RHEntry α β) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let i := idx % capacity
    have hIdx : i < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    match slots[i] with
    | none => none
    | some e =>
      if e.key == k then slots[i]
      else if e.dist < d then none
      else getEntryLoop fuel' (i + 1) k (d + 1) slots capacity hLen hCapPos

theorem getLoop_eq_getEntryLoop [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity) :
    getLoop fuel idx k d slots capacity hLen hCapPos =
      (getEntryLoop fuel idx k d slots capacity hLen hCapPos).map RHEntry.value := by
  induction fuel generalizing idx d with
  | zero => rfl
  | succ fuel ih =>
    simp only [getLoop, getEntryLoop]
    split <;> rename_i h
    · simp
    · rw [h]
      split
      · rfl
      · split
        · rfl
        · exact ih ..

/-- The stored entry for `k`, if any: `getEntryLoop` from `k`'s ideal slot. -/
def RHTable.getEntry? [BEq α] [Hashable α] (t : RHTable α β) (k : α) :
    Option (RHEntry α β) :=
  getEntryLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
    t.capacity t.hSlotsLen t.hCapPos

theorem RHTable.get?_eq_getEntry?_map [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) :
    t.get? k = (t.getEntry? k).map RHEntry.value := by
  simp only [RHTable.get?, RHTable.getEntry?, getLoop_eq_getEntryLoop]

/-- `RHTable.get?` as the kernel runs it: the slot lookup, then its value.
Inlined, the `some` it builds meets the caller's `match` and is never
allocated. -/
@[inline] def RHTable.getByEntry [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) : Option β :=
  match getEntryLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
      t.capacity t.hSlotsLen t.hCapPos with
  | some e => some e.value
  | none => none

@[csimp] theorem RHTable.get?_eq_getByEntry :
    @RHTable.get? = @RHTable.getByEntry := by
  funext α β _ _ _ t k
  simp only [RHTable.get?, RHTable.getByEntry, getLoop_eq_getEntryLoop]
  cases getEntryLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
      t.capacity t.hSlotsLen t.hCapPos <;> rfl

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

/-- WS-ZA ZA1.2: the slot of `k` on its probe chain, as a bare index — the
same walk as `findLoop`, answering `capacity` (never a valid index) where
`findLoop` answers `none`, so it allocates nothing.  `insertLoop` reaches the
same slot without writing anything before it (`insertLoop_of_findIdxLoop_lt`). -/
def findIdxLoop [BEq α] (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity) : Nat :=
  match fuel with
  | 0 => capacity
  | fuel' + 1 =>
    let i := idx % capacity
    have hIdx : i < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    match slots[i] with
    | none => capacity
    | some e =>
      if e.key == k then i
      else if e.dist < d then capacity
      else findIdxLoop fuel' (i + 1) k (d + 1) slots capacity hLen hCapPos

/-- WS-ZA ZA1.2: the entry update `insertLoop` performs on a present key. -/
@[inline] def RHEntry.withValue (v : β) : Option (RHEntry α β) → Option (RHEntry α β)
  | some e => some { e with value := v }
  | none => none

/-- WS-ZA ZA1.2: when the probe finds `k`, `insertLoop` is an in-place update of
that one slot and reports no new key — on every table, well-formed or not. -/
theorem insertLoop_of_findIdxLoop_lt [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (v : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (h : findIdxLoop fuel idx k d slots capacity hLen hCapPos < capacity) :
    insertLoop fuel idx k v d slots capacity hLen hCapPos =
      (slots.modify (findIdxLoop fuel idx k d slots capacity hLen hCapPos)
        (RHEntry.withValue v), false) := by
  induction fuel generalizing idx d with
  | zero => simp [findIdxLoop] at h
  | succ n ih =>
    unfold findIdxLoop at h ⊢
    unfold insertLoop
    dsimp only at h ⊢
    split at h
    · next => simp at h
    · next e hSome =>
      by_cases hk : (e.key == k) = true
      · simp only [hk, ↓reduceIte]
        refine Prod.ext ?_ rfl
        apply Array.ext
        · simp
        · intro j h1 h2
          simp only [Array.getElem_modify, Array.getElem_set]
          split
          · next hj => subst hj; simp [hSome, RHEntry.withValue]
          · rfl
      · simp only [hk, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hd : e.dist < d
        · simp [hd] at h
        · simp only [hd, ↓reduceIte] at h ⊢
          exact ih _ _ h


/-- WS-ZA ZA1.2: the compiled `insertNoResize`.  A present key is updated in its
slot through `Array.modify`, which takes the entry out of the array before
rebuilding it, so on an exclusively owned table the slot, its `some` and the
table record are all reused in place and nothing is allocated; an absent key
runs the specification's loop.  The absent branch spells that loop out rather
than calling `insertNoResize`, which this definition replaces in compiled code. -/
def RHTable.insertNoResizeImpl [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) : RHTable α β :=
  let start := idealIndex k t.capacity t.hCapPos
  let i := findIdxLoop t.capacity start k 0 t.slots t.capacity t.hSlotsLen t.hCapPos
  if i < t.capacity then
    { t with
        slots     := t.slots.modify i (RHEntry.withValue v)
        hSlotsLen := by rw [Array.size_modify]; exact t.hSlotsLen }
  else
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

@[csimp] theorem RHTable.insertNoResize_eq_impl :
    @RHTable.insertNoResize = @RHTable.insertNoResizeImpl := by
  funext α β _ _ _ t k v
  unfold RHTable.insertNoResize RHTable.insertNoResizeImpl
  dsimp only
  by_cases h : findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
      t.capacity t.hSlotsLen t.hCapPos < t.capacity
  · rw [if_pos h]
    simp only [insertLoop_of_findIdxLoop_lt _ _ k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos h,
      Bool.false_eq_true, ↓reduceIte]
  · rw [if_neg h]

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

/-- WS-ZA ZA1.4: the lookup is the probe's slot, read: `findIdxLoop` answers
`capacity`, past the array, exactly where `getLoop` answers `none`. -/
theorem getLoop_eq_findIdxLoop [BEq α] [Hashable α]
    (fuel idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity) :
    getLoop fuel idx k d slots capacity hLen hCapPos =
      (slots[findIdxLoop fuel idx k d slots capacity hLen hCapPos]?).join.map RHEntry.value := by
  induction fuel generalizing idx d with
  | zero => simp [findIdxLoop, getLoop, hLen]
  | succ n ih =>
    unfold findIdxLoop getLoop
    dsimp only
    split
    · next hNone => simp [hLen]
    · next e hSome =>
      by_cases hk : (e.key == k) = true
      · simp only [hk, ↓reduceIte]
        rw [Array.getElem?_eq_getElem (by rw [hLen]; exact Nat.mod_lt _ hCapPos), hSome]
        rfl
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]
        by_cases hd : e.dist < d
        · simp [hd, hLen]
        · simp only [hd, ↓reduceIte]
          exact ih _ _

/-- WS-ZA ZA1.4: `k` already holds `v` and the table is below its resize
threshold, so inserting `v` at `k` changes nothing (`insert_eq_self_of_holds`).
One probe, the slot read in place: it allocates nothing. -/
def RHTable.holds [BEq α] [Hashable α] [BEq β] (t : RHTable α β) (k : α) (v : β) : Bool :=
  if t.size * 4 ≥ t.capacity * 3 then false
  else
    let i := findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
      t.capacity t.hSlotsLen t.hCapPos
    if h : i < t.slots.size then
      match t.slots[i] with
      | some e => e.value == v
      | none => false
    else false

/-- WS-ZA ZA1.4: an insert of what the table already holds is the table. -/
theorem RHTable.insert_eq_self_of_holds [BEq α] [Hashable α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (t : RHTable α β) (k : α) (v : β) (h : t.holds k v = true) : t.insert k v = t := by
  unfold RHTable.holds at h
  split at h
  · simp at h
  · next hNo =>
    unfold RHTable.insert
    rw [if_neg hNo, RHTable.insertNoResize_eq_impl]
    unfold RHTable.insertNoResizeImpl
    dsimp only at h ⊢
    split at h
    · next hi =>
      rw [if_pos (by have := t.hSlotsLen; omega)]
      split at h
      · next e he =>
        have hv : e.value = v := by simpa using h
        have hs : t.slots.modify (findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
            t.slots t.capacity t.hSlotsLen t.hCapPos) (RHEntry.withValue v) = t.slots := by
          apply Array.ext
          · simp
          · intro j h1 h2
            simp only [Array.getElem_modify]
            split
            · next hj => subst hj; simp [he, RHEntry.withValue, ← hv]
            · rfl
        cases t
        simp only [RHTable.mk.injEq] at hs ⊢
        exact ⟨hs, trivial, trivial⟩
      · simp at h
    · simp at h

/-- WS-ZA ZA1.4: a key that holds a value is present. -/
theorem RHTable.contains_of_holds [BEq α] [Hashable α] [LawfulBEq α] [BEq β]
    (t : RHTable α β) (k : α) (v : β) (h : t.holds k v = true) : t.contains k = true := by
  unfold RHTable.holds at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · next hi =>
      unfold RHTable.contains RHTable.get?
      rw [getLoop_eq_findIdxLoop, Array.getElem?_eq_getElem hi]
      split at h
      · next e he => rw [he]; rfl
      · simp at h
    · simp at h

/-- WS-ZA ZA1.6: **update the value at `k` in place.**  The specification is the
lookup then the insert; compiled (`modify_eq_impl`), a table below its resize
threshold takes the entry out of its slot with `Array.modify`, applies `f` and
puts it back, so on an exclusively owned table the slot's `some`, the entry and
the value `f` receives are all exclusive: an `f` that rebuilds its argument's
constructor reuses it, and nothing is allocated. -/
def RHTable.modify [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) (k : α)
    (f : β → β) : RHTable α β :=
  match t.get? k with
  | some v => t.insert k (f v)
  | none => t

/-- WS-ZA ZA1.6: the entry update `RHTable.modify` performs. -/
@[inline] def RHEntry.mapValue (f : β → β) : Option (RHEntry α β) → Option (RHEntry α β)
  | some e => some { e with value := f e.value }
  | none => none

/-- WS-ZA ZA1.6: the compiled `RHTable.modify`. -/
def RHTable.modifyImpl [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) (k : α)
    (f : β → β) : RHTable α β :=
  if t.size * 4 ≥ t.capacity * 3 then
    match t.get? k with
    | some v => t.insert k (f v)
    | none => t
  else
    let i := findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
      t.capacity t.hSlotsLen t.hCapPos
    if i < t.capacity then
      { t with
          slots     := t.slots.modify i (RHEntry.mapValue f)
          hSlotsLen := by rw [Array.size_modify]; exact t.hSlotsLen }
    else t

@[csimp] theorem RHTable.modify_eq_impl :
    @RHTable.modify = @RHTable.modifyImpl := by
  funext α β _ _ _ t k f
  unfold RHTable.modify RHTable.modifyImpl
  by_cases hNo : t.size * 4 ≥ t.capacity * 3
  · rw [if_pos hNo]
  · rw [if_neg hNo]
    dsimp only
    have hGet : t.get? k = (t.slots[findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
        t.slots t.capacity t.hSlotsLen t.hCapPos]?).join.map RHEntry.value :=
      getLoop_eq_findIdxLoop _ _ _ _ _ _ _ _
    by_cases hi : findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
          t.slots t.capacity t.hSlotsLen t.hCapPos < t.capacity
    · rw [if_pos hi]
      have hi' : findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
          t.slots t.capacity t.hSlotsLen t.hCapPos < t.slots.size := by
        rw [t.hSlotsLen]; exact hi
      rw [Array.getElem?_eq_getElem hi'] at hGet
      rcases hE : t.slots[findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
          t.slots t.capacity t.hSlotsLen t.hCapPos] with _ | e
      · rw [hE] at hGet
        simp at hGet
        simp only [hGet]
        have hs : t.slots.modify (findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
            t.slots t.capacity t.hSlotsLen t.hCapPos) (RHEntry.mapValue f) = t.slots := by
          apply Array.ext
          · simp
          · intro j h1 h2
            simp only [Array.getElem_modify]
            split
            · next hj => subst hj; simp [hE, RHEntry.mapValue]
            · rfl
        cases t
        simp only at hs ⊢
        simp only [hs]
      · rw [hE] at hGet
        simp at hGet
        simp only [hGet]
        unfold RHTable.insert
        rw [if_neg hNo, RHTable.insertNoResize_eq_impl]
        unfold RHTable.insertNoResizeImpl
        dsimp only
        rw [if_pos hi]
        have hs : t.slots.modify (findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
            t.slots t.capacity t.hSlotsLen t.hCapPos) (RHEntry.withValue (f e.value)) =
            t.slots.modify (findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
            t.slots t.capacity t.hSlotsLen t.hCapPos) (RHEntry.mapValue f) := by
          apply Array.ext
          · simp
          · intro j h1 h2
            simp only [Array.getElem_modify]
            split
            · next hj => subst hj; simp [hE, RHEntry.mapValue, RHEntry.withValue]
            · rfl
        cases t
        simp only [RHTable.mk.injEq] at hs ⊢
        exact ⟨hs, trivial, trivial⟩
    · rw [if_neg hi]
      have hNone : t.slots[findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
          t.slots t.capacity t.hSlotsLen t.hCapPos]? = none :=
        Array.getElem?_eq_none (by rw [t.hSlotsLen]; omega)
      rw [hNone] at hGet
      simp at hGet
      simp only [hGet]

/-- WS-ZA ZA1.6: `modify` of a present key is the insert of its new value. -/
theorem RHTable.modify_of_get? [BEq α] [Hashable α] [LawfulBEq α] {t : RHTable α β} {k : α}
    {v : β} (h : t.get? k = some v) (f : β → β) : t.modify k f = t.insert k (f v) := by
  unfold RHTable.modify; rw [h]


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
