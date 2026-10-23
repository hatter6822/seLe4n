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

/-- WS-ZA ZA5.3: the compiled `idealIndex`, reduced in machine words.  A hash at
or above `2 ^ 63` is a big number once it is a `Nat`, so `(hash k).toNat` built
one on every insert and lookup of a key with a mixed hash (`SlotRef`); a word
`%` by a capacity below `2 ^ 64` leaves only the index, a small number.  A call,
specialised to the key's hash: inlined, its two arms split the caller's probe
into a join point, and an in-place table update (`RHTable.modifyImpl`) then
rebuilt the table record instead of reusing it. -/
@[noinline, specialize] def idealIndexImpl [Hashable α] (k : α) (capacity : Nat)
    (_hCapPos : 0 < capacity) : Nat :=
  if capacity < UInt64.size then (hash k % capacity.toUInt64).toNat
  else (hash k).toNat % capacity

@[csimp] theorem idealIndex_eq_impl : @idealIndex = @idealIndexImpl := by
  funext α _ k capacity h
  unfold idealIndex idealIndexImpl
  split
  · next hc => rw [UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' hc]
  · rfl

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

/-- A slot's cell moved one slot back on its probe chain: its entry's distance
one less.  Out of line, so the cell is handed over whole and, when exclusively
owned, rewritten in place, its `some` first and then its entry. -/
@[noinline] def RHEntry.shiftedBack : Option (RHEntry α β) → Option (RHEntry α β)
  | some e => some { e with dist := e.dist - 1 }
  | none => none

/-- `backshiftLoop` as compiled: the next slot's cell is taken out of the array
before the shifted entry is built from it, so on an exclusively owned array the
cell and its entry are rewritten in place rather than copied
(`backshiftLoop_eq_impl`).  A one-slot table, whose gap and next slot coincide,
takes the specification's step. -/
def backshiftLoopImpl
    (fuel : Nat) (gapIdx : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity)
    : Array (Option (RHEntry α β)) :=
  match fuel with
  | 0 => slots
  | fuel' + 1 =>
    let nextI := (gapIdx + 1) % capacity
    have hNext : nextI < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hGap : gapIdx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    if gapIdx % capacity = nextI then
      backshiftLoop (fuel' + 1) gapIdx slots capacity hLen hCapPos
    else
      let v := slots[nextI]
      let slots1 := slots.set nextI none hNext
      match v with
      | none => slots1
      | some e =>
        if e.dist == 0 then slots1.set nextI (some e) (by rw [Array.size_set]; exact hNext)
        else
          backshiftLoopImpl fuel' nextI
            (slots1.set (gapIdx % capacity) (RHEntry.shiftedBack (some e))
              (by rw [Array.size_set]; exact hGap))
            capacity (by rw [Array.size_set, Array.size_set]; exact hLen) hCapPos

@[csimp] theorem backshiftLoop_eq_impl : @backshiftLoop = @backshiftLoopImpl := by
  funext α β fuel
  induction fuel with
  | zero => funext gapIdx slots capacity hLen hCapPos; rfl
  | succ n ih =>
    funext gapIdx slots capacity hLen hCapPos
    have hNext : (gapIdx + 1) % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hGap : gapIdx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    unfold backshiftLoopImpl
    dsimp only
    by_cases hEq : gapIdx % capacity = (gapIdx + 1) % capacity
    · rw [if_pos hEq]
    · rw [if_neg hEq]
      unfold backshiftLoop
      dsimp only
      cases hv : slots[(gapIdx + 1) % capacity] with
      | none =>
        dsimp only
        rw [← hv, Array.set_getElem_self]
      | some e =>
        dsimp only
        by_cases hd : (e.dist == 0) = true
        · rw [if_pos hd, if_pos hd, Array.set_set, ← hv, Array.set_getElem_self]
        · rw [if_neg hd, if_neg hd, ih]
          simp only [RHEntry.shiftedBack]
          congr 1
          apply Array.ext
          · simp
          · intro j h1 h2
            simp only [Array.getElem_set]
            split <;> split <;> simp_all

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

/-- N1-G1: Fold over all occupied entries in the table.  Inlined so a fold's
body is specialised in rather than passed as a closure (WS-ZA ZA4.7). -/
@[inline] def RHTable.fold (t : RHTable α β) (init : γ) (f : γ → α → β → γ) : γ :=
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

/-- WS-ZA ZA4.7: `Array.modify` with the slot holding `fill` while `g` runs, so
`g` receives the element's only reference on an exclusively owned array.  Unlike
`Array.modify` (whose `modifyM` builds a monadic closure around `g`), it is
inlined to the call site with `g` applied directly, so a `g` that captures
values allocates no closure (`arrayModifyFill_eq`). -/
@[inline] def arrayModifyFill (a : Array γ) (i : Nat) (fill : γ) (g : γ → γ) : Array γ :=
  if h : i < a.size then
    let v := a[i]
    (a.set i fill h).set i (g v) (by simp [h])
  else a

theorem arrayModifyFill_eq (a : Array γ) (i : Nat) (fill : γ) (g : γ → γ) :
    arrayModifyFill a i fill g = a.modify i g := by
  unfold arrayModifyFill
  split
  · next h =>
    apply Array.ext
    · simp
    · intro j h1 h2
      simp only [Array.getElem_set, Array.getElem_modify]
      split <;> simp_all
  · next h =>
    apply Array.ext
    · simp
    · intro j h1 h2
      simp only [Array.getElem_modify]
      split
      · omega
      · rfl

/-- WS-ZA ZA4.7: a table's slot array with slot `i` rewritten by `g` — the
specification is `Array.modify`; compiled, `arrayModifyFill` with `none` held
in the slot meanwhile (`modifySlotAt_eq_impl`). -/
def modifySlotAt (s : Array (Option (RHEntry α β))) (i : Nat)
    (g : Option (RHEntry α β) → Option (RHEntry α β)) : Array (Option (RHEntry α β)) :=
  s.modify i g

/-- WS-ZA ZA4.7: the compiled `modifySlotAt`. -/
@[inline] def modifySlotAtImpl (s : Array (Option (RHEntry α β))) (i : Nat)
    (g : Option (RHEntry α β) → Option (RHEntry α β)) : Array (Option (RHEntry α β)) :=
  arrayModifyFill s i none g

@[csimp] theorem modifySlotAt_eq_impl :
    @modifySlotAt = @modifySlotAtImpl := by
  funext α β s i g
  unfold modifySlotAt modifySlotAtImpl
  rw [arrayModifyFill_eq]

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


/-- WS-ZA ZA5.4: whether `insertLoop` places its entry in an empty slot (the
flag it returns), read without writing anything: the same probe, with each
displaced resident carried on.  Over a probe no longer than the table it reads
the slots `insertLoop` reads before it writes them (`insertLoop_snd_eq_places`),
so the insert can learn its flag first and return its array alone. -/
def insertPlacesLoop [BEq α] (fuel idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β))) (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    let i := idx % capacity
    have hIdx : i < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    match slots[i] with
    | none => true
    | some e =>
      if e.key == k then false
      else if e.dist < d then
        insertPlacesLoop fuel' (i + 1) e.key (e.dist + 1) slots capacity hLen hCapPos
      else insertPlacesLoop fuel' (i + 1) k (d + 1) slots capacity hLen hCapPos

private theorem mod_succ_add_ne {capacity a j : Nat} (ha : a < capacity) (hj : j + 1 < capacity) :
    (a + 1 + j) % capacity ≠ a := by
  by_cases h : a + 1 + j < capacity
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

private theorem mod_succ_add_eq (idx capacity j : Nat) :
    (idx % capacity + 1 + j) % capacity = (idx + (j + 1)) % capacity := by
  rw [show idx % capacity + 1 + j = idx % capacity + (j + 1) by omega, Nat.mod_add_mod]

/-- WS-ZA ZA5.4: `insertLoop`'s flag is `insertPlacesLoop` over any array that
agrees with the one it is handed on the slots its probe visits, for a probe no
longer than the table (so it never comes back to a slot it wrote). -/
theorem insertLoop_snd_eq_places [BEq α] [Hashable α] (capacity : Nat) (hCapPos : 0 < capacity)
    (slots0 : Array (Option (RHEntry α β))) (hLen0 : slots0.size = capacity) :
    ∀ (fuel idx : Nat) (k : α) (v : β) (d : Nat) (slots : Array (Option (RHEntry α β)))
      (hLen : slots.size = capacity), fuel ≤ capacity →
      (∀ j, j < fuel → slots[(idx + j) % capacity]? = slots0[(idx + j) % capacity]?) →
      (insertLoop fuel idx k v d slots capacity hLen hCapPos).2 =
        insertPlacesLoop fuel idx k d slots0 capacity hLen0 hCapPos
  | 0, _, _, _, _, _, _, _, _ => rfl
  | fuel' + 1, idx, k, v, d, slots, hLen, hF, hA => by
    have hi : idx % capacity < capacity := Nat.mod_lt _ hCapPos
    have h0 := hA 0 (Nat.succ_pos _)
    rw [Nat.add_zero, Array.getElem?_eq_getElem (by omega),
      Array.getElem?_eq_getElem (by omega)] at h0
    have hAgree : ∀ j, j < fuel' →
        slots[(idx % capacity + 1 + j) % capacity]? =
          slots0[(idx % capacity + 1 + j) % capacity]? := by
      intro j hj
      rw [mod_succ_add_eq]; exact hA (j + 1) (by omega)
    unfold insertLoop insertPlacesLoop
    dsimp only
    rw [Option.some.inj h0]
    cases slots0[idx % capacity] with
    | none => rfl
    | some e =>
      dsimp only
      by_cases hk : (e.key == k) = true
      · simp only [hk, ↓reduceIte]
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]
        by_cases hd : e.dist < d
        · simp only [hd, ↓reduceIte]
          refine insertLoop_snd_eq_places capacity hCapPos slots0 hLen0 fuel' _ _ _ _ _ _
            (by omega) (fun j hj => ?_)
          rw [Array.getElem?_set_ne (by omega) (Ne.symm (mod_succ_add_ne hi (by omega)))]
          exact hAgree j hj
        · simp only [hd, ↓reduceIte]
          exact insertLoop_snd_eq_places capacity hCapPos slots0 hLen0 fuel' _ _ _ _ _ _
            (by omega) hAgree

/-- WS-ZA ZA5.4: what the insert probe does at a slot holding `o`, for the
entry it carries (key `k`, distance `d`), as a code: `0` place it, `1`
overwrite the matching key's value, `2` displace the resident, `3` move on. -/
@[inline] def insertStepCode [BEq α] (o : Option (RHEntry α β)) (k : α) (d : Nat) : UInt8 :=
  match o with
  | none => 0
  | some e => if e.key == k then 1 else if e.dist < d then 2 else 3

/-- WS-ZA ZA5.4: the cell `c` with its entry's distance advanced, in place when
`c` is exclusive. -/
@[inline] def RHEntry.bumpDist : Option (RHEntry α β) → Option (RHEntry α β)
  | some e => some { e with dist := e.dist + 1 }
  | none => none

/-- WS-ZA ZA5.4: the value the cell `c` carries, written over a slot's entry. -/
@[inline] def RHEntry.withValueOf (c : Option (RHEntry α β)) :
    Option (RHEntry α β) → Option (RHEntry α β)
  | some e => match c with
    | some ce => some { e with value := ce.value }
    | none => some e
  | none => none

/-- WS-ZA ZA5.4: `insertLoop`'s array, carrying the entry being placed as its
own cell `c` (the `some` and the entry; its key `k` and distance `d` passed
beside it): an empty slot takes `c` itself, a displaced resident's cell is
carried on with its distance advanced, and moving on advances `c`'s distance in
place.  A displaced resident is read before its slot is written and matched
after, so its cell is the probe's alone by then: on an exclusively owned table
nothing is allocated (`insertCellLoop_eq`). -/
def insertCellLoop [BEq α] (fuel idx : Nat) (k : α) (d : Nat) (c : Option (RHEntry α β))
    (slots : Array (Option (RHEntry α β))) (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity) : Array (Option (RHEntry α β)) :=
  match fuel with
  | 0 => slots
  | fuel' + 1 =>
    let i := idx % capacity
    have hIdx : i < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    let code := insertStepCode slots[i] k d
    if code == 0 then slots.set i c
    else if code == 1 then modifySlotAt slots i (RHEntry.withValueOf c)
    else if code == 2 then
      let old := slots[i]
      let slots' := slots.set i c
      match old with
      | some e =>
        insertCellLoop fuel' (i + 1) e.key (e.dist + 1) (some { e with dist := e.dist + 1 })
          slots' capacity (by rw [Array.size_set]; exact hLen) hCapPos
      | none => slots'
    else
      insertCellLoop fuel' (i + 1) k (d + 1) (RHEntry.bumpDist c) slots capacity hLen hCapPos

theorem insertCellLoop_eq [BEq α] [Hashable α] (capacity : Nat) (hCapPos : 0 < capacity) :
    ∀ (fuel idx : Nat) (k : α) (v : β) (d : Nat) (slots : Array (Option (RHEntry α β)))
      (hLen : slots.size = capacity),
      insertCellLoop fuel idx k d (some ⟨k, v, d⟩) slots capacity hLen hCapPos =
        (insertLoop fuel idx k v d slots capacity hLen hCapPos).1
  | 0, _, _, _, _, _, _ => rfl
  | fuel' + 1, idx, k, v, d, slots, hLen => by
    have hI : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have c10 : ((1 : UInt8) == 0) = false := by decide
    have c20 : ((2 : UInt8) == 0) = false := by decide
    have c21 : ((2 : UInt8) == 1) = false := by decide
    have c30 : ((3 : UInt8) == 0) = false := by decide
    have c31 : ((3 : UInt8) == 1) = false := by decide
    have c32 : ((3 : UInt8) == 2) = false := by decide
    unfold insertCellLoop insertLoop
    dsimp only
    cases hs : slots[idx % capacity]'hI with
    | none => simp [insertStepCode]
    | some e =>
      by_cases hk : (e.key == k) = true
      · simp only [insertStepCode, hk, ↓reduceIte, c10, Bool.false_eq_true, beq_self_eq_true]
        unfold modifySlotAt
        apply Array.ext
        · simp
        · intro j h1 h2
          simp only [Array.getElem_modify, Array.getElem_set]
          split
          · next hj => subst hj; simp [hs, RHEntry.withValueOf]
          · rfl
      · by_cases hd : e.dist < d
        · simp only [insertStepCode, hk, hd, Bool.false_eq_true, ↓reduceIte, c20, c21,
            beq_self_eq_true]
          exact insertCellLoop_eq capacity hCapPos fuel' _ e.key e.value (e.dist + 1) _ _
        · simp only [insertStepCode, hk, hd, Bool.false_eq_true, ↓reduceIte, c30, c31, c32,
            RHEntry.bumpDist]
          exact insertCellLoop_eq capacity hCapPos fuel' _ k v (d + 1) _ _

/-- WS-ZA ZA5.4: the absent-key half of `insertNoResize`, placing the entry's
own cell `c` (its key, value and distance `0`): the insert's flag is read before
the array is written (`insertPlacesLoop`) and `c` itself is placed
(`insertCellLoop`), so on an exclusively owned table nothing beyond `c` is used
and no result pair is built (`insertAbsentCell_eq`). -/
def RHTable.insertAbsentCell [BEq α] [Hashable α] (t : RHTable α β)
    (c : Option (RHEntry α β)) : RHTable α β :=
  match hc : c with
  | none => t
  | some ce =>
    let start := idealIndex ce.key t.capacity t.hCapPos
    have hLen : (insertCellLoop t.capacity start ce.key ce.dist c t.slots t.capacity
        t.hSlotsLen t.hCapPos).size = t.capacity := by
      rw [hc, show (some ce) = some ⟨ce.key, ce.value, ce.dist⟩ from rfl, insertCellLoop_eq,
        insertLoop_preserves_len]
      exact t.hSlotsLen
    if insertPlacesLoop t.capacity start ce.key ce.dist t.slots t.capacity t.hSlotsLen
        t.hCapPos then
      { t with
          slots     := insertCellLoop t.capacity start ce.key ce.dist c t.slots t.capacity
            t.hSlotsLen t.hCapPos
          size      := t.size + 1
          hSlotsLen := hLen }
    else
      { t with
          slots     := insertCellLoop t.capacity start ce.key ce.dist c t.slots t.capacity
            t.hSlotsLen t.hCapPos
          hSlotsLen := hLen }

theorem RHTable.insertAbsentCell_eq [BEq α] [Hashable α] (t : RHTable α β) (k : α) (v : β) :
    t.insertAbsentCell (some ⟨k, v, 0⟩) =
      { slots     := (insertLoop t.capacity (idealIndex k t.capacity t.hCapPos) k v 0
                       t.slots t.capacity t.hSlotsLen t.hCapPos).1
        size      := if (insertLoop t.capacity (idealIndex k t.capacity t.hCapPos) k v 0
                       t.slots t.capacity t.hSlotsLen t.hCapPos).2 then t.size + 1 else t.size
        capacity  := t.capacity
        hCapGe4   := t.hCapGe4
        hSlotsLen := by rw [insertLoop_preserves_len]; exact t.hSlotsLen } := by
  unfold RHTable.insertAbsentCell
  dsimp only
  have hF := insertLoop_snd_eq_places t.capacity t.hCapPos t.slots t.hSlotsLen t.capacity
    (idealIndex k t.capacity t.hCapPos) k v 0 t.slots t.hSlotsLen (Nat.le_refl _)
    (fun _ _ => rfl)
  rw [← hF]
  split <;> simp only [insertCellLoop_eq]

/-- WS-ZA ZA5.4: `insertNoResize` with the new entry's cell `c` supplied (its
key, value and distance `0`): a present key has its value written in its slot,
an absent one is `insertAbsentCell` (`insertNoResizeCell_eq`). -/
def RHTable.insertNoResizeCell [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β)
    (c : Option (RHEntry α β)) : RHTable α β :=
  match c with
  | none => t
  | some ce =>
    let i := findIdxLoop t.capacity (idealIndex ce.key t.capacity t.hCapPos) ce.key 0 t.slots
      t.capacity t.hSlotsLen t.hCapPos
    if i < t.capacity then
      { t with
          slots     := modifySlotAt t.slots i (RHEntry.withValue ce.value)
          hSlotsLen := by rw [modifySlotAt, Array.size_modify]; exact t.hSlotsLen }
    else t.insertAbsentCell (some ce)

/-- WS-ZA ZA1.2: the compiled `insertNoResize`.  A present key is updated in its
slot through `Array.modify`, which takes the entry out of the array before
rebuilding it, so on an exclusively owned table the slot, its `some` and the
table record are all reused in place and nothing is allocated; an absent key
builds its entry's cell and places that cell itself (`insertAbsentCell`), so no
result pair is built. -/
def RHTable.insertNoResizeImpl [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) : RHTable α β :=
  let start := idealIndex k t.capacity t.hCapPos
  let i := findIdxLoop t.capacity start k 0 t.slots t.capacity t.hSlotsLen t.hCapPos
  if i < t.capacity then
    { t with
        slots     := modifySlotAt t.slots i (RHEntry.withValue v)
        hSlotsLen := by rw [modifySlotAt, Array.size_modify]; exact t.hSlotsLen }
  else t.insertAbsentCell (some ⟨k, v, 0⟩)

@[csimp] theorem RHTable.insertNoResize_eq_impl :
    @RHTable.insertNoResize = @RHTable.insertNoResizeImpl := by
  funext α β _ _ _ t k v
  unfold RHTable.insertNoResize RHTable.insertNoResizeImpl
  dsimp only
  simp only [modifySlotAt]
  by_cases h : findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
      t.capacity t.hSlotsLen t.hCapPos < t.capacity
  · rw [if_pos h]
    simp only [insertLoop_of_findIdxLoop_lt _ _ k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos h,
      Bool.false_eq_true, ↓reduceIte]
  · rw [if_neg h, RHTable.insertAbsentCell_eq]

theorem RHTable.insertNoResizeCell_eq [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β)
    (k : α) (v : β) :
    t.insertNoResizeCell (some ⟨k, v, 0⟩) = t.insertNoResize k v := by
  rw [RHTable.insertNoResize_eq_impl]
  rfl

/-- WS-ZA ZA5.4: `findLoop` answers the slot `findIdxLoop` names, as an
`Option`: `findIdxLoop`'s `capacity` is `findLoop`'s `none`. -/
theorem findLoop_eq_findIdxLoop [BEq α] [Hashable α] (capacity : Nat) (hCapPos : 0 < capacity) :
    ∀ (fuel idx : Nat) (k : α) (d : Nat) (slots : Array (Option (RHEntry α β)))
      (hLen : slots.size = capacity),
      findLoop fuel idx k d slots capacity hLen hCapPos =
        if findIdxLoop fuel idx k d slots capacity hLen hCapPos < capacity then
          some (findIdxLoop fuel idx k d slots capacity hLen hCapPos)
        else none
  | 0, _, _, _, _, _ => by simp [findLoop, findIdxLoop]
  | fuel' + 1, idx, k, d, slots, hLen => by
    have hi : idx % capacity < capacity := Nat.mod_lt _ hCapPos
    unfold findLoop findIdxLoop
    dsimp only
    split
    · simp
    · split
      · simp
      · split
        · simp
        · exact findLoop_eq_findIdxLoop capacity hCapPos fuel' _ k _ slots hLen

/-- WS-ZA ZA5.4: `erase` at the slot `i` the probe found: the slot cleared, the
entries after it shifted back, one entry fewer. -/
def RHTable.eraseAt (t : RHTable α β) (i : Nat) (hi : i < t.capacity) : RHTable α β :=
  have hIdx : i < t.slots.size := by rw [t.hSlotsLen]; exact hi
  let slots' := t.slots.set i none hIdx
  have hLen' : slots'.size = t.capacity := by rw [Array.size_set]; exact t.hSlotsLen
  { slots     := backshiftLoop t.capacity i slots' t.capacity hLen' t.hCapPos
    size      := t.size - 1
    capacity  := t.capacity
    hCapGe4   := t.hCapGe4
    hSlotsLen := by rw [backshiftLoop_preserves_len]; exact hLen' }

/-- WS-ZA ZA5.4: `erase` is the probe for the key's slot as a bare index, then
`eraseAt` there, so no slot `Option` is built. -/
theorem RHTable.erase_eq_eraseAt [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) (k : α) :
    t.erase k =
      if h : findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots t.capacity
          t.hSlotsLen t.hCapPos < t.capacity then
        t.eraseAt _ h
      else t := by
  unfold RHTable.erase
  dsimp only
  rw [findLoop_eq_findIdxLoop]
  by_cases h : findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots t.capacity
      t.hSlotsLen t.hCapPos < t.capacity
  · rw [if_pos h, dif_pos h]
    simp only [RHTable.eraseAt, Nat.mod_eq_of_lt h]
  · rw [if_neg h, dif_neg h]

/-- `erase` as compiled: the probe's slot as a bare index (`findIdxLoop`), then
`eraseAt` there, so no `Option` of the index is built (`RHTable.erase_eq_impl`). -/
@[inline] def RHTable.eraseImpl [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) (k : α) :
    RHTable α β :=
  if h : findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots t.capacity
      t.hSlotsLen t.hCapPos < t.capacity then
    t.eraseAt _ h
  else t

@[csimp] theorem RHTable.erase_eq_impl : @RHTable.erase = @RHTable.eraseImpl := by
  funext α β _ _ _ t k
  exact RHTable.erase_eq_eraseAt t k

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

/-- WS-ZA ZA5.4: `insert` with the new entry's cell supplied (`insertNoResizeCell`
after the resize check). -/
def RHTable.insertCell [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β)
    (c : Option (RHEntry α β)) : RHTable α β :=
  let t' := if t.size * 4 ≥ t.capacity * 3 then t.resize else t
  t'.insertNoResizeCell c

theorem RHTable.insertCell_eq [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β)
    (k : α) (v : β) : t.insertCell (some ⟨k, v, 0⟩) = t.insert k v := by
  unfold RHTable.insertCell RHTable.insert
  exact RHTable.insertNoResizeCell_eq _ k v

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

/-- WS-ZA ZA5.4: a key that holds a value looks it up. -/
theorem RHTable.get?_of_holds [BEq α] [Hashable α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (t : RHTable α β) (k : α) (v : β) (h : t.holds k v = true) : t.get? k = some v := by
  unfold RHTable.holds at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · next hi =>
      unfold RHTable.get?
      rw [getLoop_eq_findIdxLoop, Array.getElem?_eq_getElem hi]
      split at h
      · next e he =>
        rw [he]
        show (some e).map RHEntry.value = some v
        rw [Option.map_some, eq_of_beq h]
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

/-- WS-ZA ZA1.6: the compiled `RHTable.modify`, specialised so the update `f`
is compiled in at each call site rather than passed as a closure.  A call, not
inlined: the caller releases the record it projected the table from before the
call, so the table arrives exclusive (inlined, the branch that answers the table
unchanged kept that record alive across the write). -/
@[specialize] def RHTable.modifyImpl [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) (k : α)
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
          slots     := modifySlotAt t.slots i (RHEntry.mapValue f)
          hSlotsLen := by rw [modifySlotAt, Array.size_modify]; exact t.hSlotsLen }
    else t

@[csimp] theorem RHTable.modify_eq_impl :
    @RHTable.modify = @RHTable.modifyImpl := by
  funext α β _ _ _ t k f
  unfold RHTable.modify RHTable.modifyImpl
  by_cases hNo : t.size * 4 ≥ t.capacity * 3
  · rw [if_pos hNo]
  · rw [if_neg hNo]
    dsimp only
    simp only [modifySlotAt]
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

/-- WS-ZA ZA5.4: **an update that changes nothing a theorem reads, written in
the key's slot when the key is found there and skipped otherwise.**  For an `f`
that is the identity (`modifyInPlace_of_id`) — a write of a `Squash` field, the
hand-over of a spare cell from one object to another — skipping the write is
the same table, so the update never inserts, never resizes and needs no
invariant; compiled, the slot's `some`, its entry and the value are exclusive
on an exclusively owned table, as in `modifyImpl`. -/
@[specialize] def RHTable.modifyInPlace [BEq α] [Hashable α] (t : RHTable α β) (k : α)
    (f : β → β) : RHTable α β :=
  let i := findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
    t.capacity t.hSlotsLen t.hCapPos
  if i < t.capacity then
    { t with
        slots     := modifySlotAt t.slots i (RHEntry.mapValue f)
        hSlotsLen := by rw [modifySlotAt, Array.size_modify]; exact t.hSlotsLen }
  else t

theorem RHTable.modifyInPlace_of_id [BEq α] [Hashable α] (t : RHTable α β) (k : α)
    (f : β → β) (hf : ∀ b, f b = b) : t.modifyInPlace k f = t := by
  unfold RHTable.modifyInPlace
  dsimp only
  split
  · have hs : modifySlotAt t.slots (findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
        t.slots t.capacity t.hSlotsLen t.hCapPos) (RHEntry.mapValue f) = t.slots := by
      unfold modifySlotAt
      apply Array.ext
      · simp
      · intro j h1 h2
        simp only [Array.getElem_modify]
        split
        · unfold RHEntry.mapValue
          split <;> simp_all
        · rfl
    cases t
    simp only [RHTable.mk.injEq] at hs ⊢
    exact ⟨hs, trivial, trivial⟩
  · rfl

/-- WS-ZA ZA1.6: `modify` of a present key is the insert of its new value. -/
theorem RHTable.modify_of_get? [BEq α] [Hashable α] [LawfulBEq α] {t : RHTable α β} {k : α}
    {v : β} (h : t.get? k = some v) (f : β → β) : t.modify k f = t.insert k (f v) := by
  unfold RHTable.modify; rw [h]

/-- WS-ZA ZA4: `findIdxLoop` reads a slot only through its key and distance. -/
theorem findIdxLoop_congr [BEq α] (fuel idx : Nat) (k : α) (d : Nat)
    (s s' : Array (Option (RHEntry α β))) (capacity : Nat)
    (hLen : s.size = capacity) (hLen' : s'.size = capacity) (hCapPos : 0 < capacity)
    (h : ∀ j (h1 : j < s.size) (h2 : j < s'.size),
      s[j].map (fun e => (e.key, e.dist)) = s'[j].map (fun e => (e.key, e.dist))) :
    findIdxLoop fuel idx k d s capacity hLen hCapPos =
      findIdxLoop fuel idx k d s' capacity hLen' hCapPos := by
  induction fuel generalizing idx d with
  | zero => rfl
  | succ n ih =>
    unfold findIdxLoop
    dsimp only
    have h1 : idx % capacity < s.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have h2 : idx % capacity < s'.size := by rw [hLen']; exact Nat.mod_lt _ hCapPos
    have hj := h (idx % capacity) h1 h2
    revert hj
    cases hA : s[idx % capacity] <;> cases hB : s'[idx % capacity] <;> intro hj
    · rfl
    · simp at hj
    · simp at hj
    · next e e' =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hj
      simp only [hj.1, hj.2]
      split
      · rfl
      · split
        · rfl
        · exact ih _ _

/-- WS-ZA ZA4: the slot `findIdxLoop` lands on holds the key it probed for. -/
theorem findIdxLoop_key [BEq α] (fuel idx : Nat) (k : α) (d : Nat)
    (s : Array (Option (RHEntry α β))) (capacity : Nat)
    (hLen : s.size = capacity) (hCapPos : 0 < capacity)
    (h : findIdxLoop fuel idx k d s capacity hLen hCapPos < capacity) :
    ∃ e, s[findIdxLoop fuel idx k d s capacity hLen hCapPos]? = some (some e) ∧
      (e.key == k) = true := by
  induction fuel generalizing idx d with
  | zero => simp [findIdxLoop] at h
  | succ n ih =>
    have h1 : idx % capacity < s.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    unfold findIdxLoop at h ⊢
    dsimp only at h ⊢
    revert h
    cases hA : s[idx % capacity] <;> intro h
    · simp at h
    · next e =>
      by_cases hk : (e.key == k) = true
      · simp only [hk, ↓reduceIte]
        exact ⟨e, by rw [Array.getElem?_eq_getElem h1, hA], hk⟩
      · simp only [hk, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hd : e.dist < d
        · simp [hd] at h
        · simp only [hd, ↓reduceIte] at h ⊢
          exact ih _ _ h

/-- WS-ZA ZA4: rewriting one slot's value leaves every probe where it was. -/
theorem findIdxLoop_modify_withValue [BEq α] (fuel idx : Nat) (k : α) (d : Nat)
    (s : Array (Option (RHEntry α β))) (i : Nat) (v : β) (capacity : Nat)
    (hLen' : (s.modify i (RHEntry.withValue v)).size = capacity)
    (hCapPos : 0 < capacity) :
    findIdxLoop fuel idx k d (s.modify i (RHEntry.withValue v)) capacity hLen' hCapPos =
      findIdxLoop fuel idx k d s capacity (by rw [← hLen', Array.size_modify]) hCapPos :=
  findIdxLoop_congr _ _ _ _ _ _ _ _ _ _ (by
    intro j h1 h2
    simp only [Array.getElem_modify]
    split
    · next hj => subst hj; cases s[i] <;> rfl
    · rfl)

/-- WS-ZA ZA4: **an insert that rewrites its key where it stands**: no resize
is due and the probe finds `k`, so the insert changes that one slot's value
(`insertLoop_of_findIdxLoop_lt`), on every table, well-formed or not. -/
def RHTable.findsInPlace [BEq α] [Hashable α] (t : RHTable α β) (k : α) : Bool :=
  !decide (t.size * 4 ≥ t.capacity * 3) &&
  decide (findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
    t.capacity t.hSlotsLen t.hCapPos < t.capacity)

/-- WS-ZA ZA4: an insert that rewrites its key in place leaves every other key's
lookup as it was.  No `invExt`: only the one slot's value moves, and a probe
reads slots through their keys and distances. -/
theorem RHTable.get?_insert_ne_of_findsInPlace [BEq α] [Hashable α] [LawfulBEq α]
    {t : RHTable α β} {k : α} (k' : α) (v : β) (h : t.findsInPlace k = true)
    (hNe : k ≠ k') : (t.insert k v).get? k' = t.get? k' := by
  unfold RHTable.findsInPlace at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  obtain ⟨hNo, hFound⟩ := h
  obtain ⟨e, he, hek⟩ := findIdxLoop_key _ _ _ _ _ _ _ _ hFound
  unfold RHTable.insert
  rw [if_neg hNo, RHTable.insertNoResize_eq_impl]
  unfold RHTable.insertNoResizeImpl modifySlotAt
  dsimp only
  rw [if_pos hFound]
  unfold RHTable.get?
  simp only [getLoop_eq_findIdxLoop]
  rw [findIdxLoop_modify_withValue]
  by_cases hji : findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
      t.capacity t.hSlotsLen t.hCapPos = findIdxLoop t.capacity (idealIndex k' t.capacity t.hCapPos)
      k' 0 t.slots t.capacity t.hSlotsLen t.hCapPos
  · obtain ⟨e', he', hek'⟩ := findIdxLoop_key _ _ _ _ _ _ _ _ (hji ▸ hFound)
    rw [← hji, he] at he'
    cases he'
    exact absurd ((beq_iff_eq.1 hek).symm.trans (beq_iff_eq.1 hek')) hNe
  · rw [Array.getElem?_modify, if_neg hji]


/-- WS-ZA ZA4.4: an insert that rewrites its key in place leaves every key's
in-place question as it was: the size, the capacity and every slot's key and
distance are unchanged, so a chain of in-place writes can be asked about up
front, on the table it starts from. -/
theorem RHTable.findsInPlace_insert_of_findsInPlace [BEq α] [Hashable α] [LawfulBEq α]
    {t : RHTable α β} {k : α} (k' : α) (v : β) (h : t.findsInPlace k = true) :
    (t.insert k v).findsInPlace k' = t.findsInPlace k' := by
  have h' := h
  unfold RHTable.findsInPlace at h'
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h'
  obtain ⟨hNo, hFound⟩ := h'
  unfold RHTable.insert
  rw [if_neg hNo, RHTable.insertNoResize_eq_impl]
  unfold RHTable.insertNoResizeImpl modifySlotAt
  dsimp only
  rw [if_pos hFound]
  unfold RHTable.findsInPlace
  dsimp only
  rw [findIdxLoop_modify_withValue]

/-- WS-ZA ZA4.4: an insert that rewrites its key in place reads back what it
wrote, on every table, well-formed or not. -/
theorem RHTable.get?_insert_self_of_findsInPlace [BEq α] [Hashable α] [LawfulBEq α]
    {t : RHTable α β} {k : α} (v : β) (h : t.findsInPlace k = true) :
    (t.insert k v).get? k = some v := by
  unfold RHTable.findsInPlace at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  obtain ⟨hNo, hFound⟩ := h
  obtain ⟨e, he, hek⟩ := findIdxLoop_key _ _ _ _ _ _ _ _ hFound
  unfold RHTable.insert
  rw [if_neg hNo, RHTable.insertNoResize_eq_impl]
  unfold RHTable.insertNoResizeImpl modifySlotAt
  dsimp only
  rw [if_pos hFound]
  unfold RHTable.get?
  simp only [getLoop_eq_findIdxLoop]
  rw [findIdxLoop_modify_withValue, Array.getElem?_modify, if_pos rfl, he]
  simp [RHEntry.withValue]

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
