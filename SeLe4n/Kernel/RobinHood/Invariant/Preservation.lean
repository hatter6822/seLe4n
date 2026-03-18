/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RobinHood.Invariant.Defs

namespace SeLe4n.Kernel.RobinHood

-- ============================================================================
-- Section 1: List.countP helper lemmas
-- ============================================================================

private theorem List.countP_set_of_same {p : α → Bool}
    (l : List α) (i : Nat) (v : α) (hi : i < l.length)
    (hSame : p (l[i]'hi) = p v) :
    (l.set i v).countP p = l.countP p := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.countP_cons]
      simp only [List.getElem_cons_zero] at hSame; rw [hSame]
    | succ n =>
      simp only [List.set_cons_succ, List.countP_cons]
      have hn : n < tl.length := by simp [List.length_cons] at hi; omega
      rw [ih n hn (by simpa [List.getElem_cons_succ] using hSame)]

private theorem List.countP_set_of_false_to_true {p : α → Bool}
    (l : List α) (i : Nat) (v : α) (hi : i < l.length)
    (hOld : p (l[i]'hi) = false) (hNew : p v = true) :
    (l.set i v).countP p = l.countP p + 1 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.countP_cons, List.getElem_cons_zero] at *
      rw [hNew, hOld]; simp
    | succ n =>
      simp only [List.set_cons_succ, List.countP_cons]
      have hn : n < tl.length := by simp [List.length_cons] at hi; omega
      rw [ih n hn (by simpa [List.getElem_cons_succ] using hOld)]; omega

private theorem List.countP_set_of_true_to_false {p : α → Bool}
    (l : List α) (i : Nat) (v : α) (hi : i < l.length)
    (hOld : p (l[i]'hi) = true) (hNew : p v = false) :
    (l.set i v).countP p + 1 = l.countP p := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.countP_cons, List.getElem_cons_zero] at *
      rw [hNew, hOld]; simp
    | succ n =>
      simp only [List.set_cons_succ, List.countP_cons]
      have hn : n < tl.length := by simp [List.length_cons] at hi; omega
      have := ih n hn (by simpa [List.getElem_cons_succ] using hOld); omega

-- ============================================================================
-- Section 2: countOccupied helpers for Array.set
-- ============================================================================

theorem countOccupied_set_none_to_some
    (slots : Array (Option (RHEntry α β)))
    (i : Nat) (hi : i < slots.size) (e : RHEntry α β)
    (hNone : slots[i] = none) :
    countOccupied (slots.set i (some e)) = countOccupied slots + 1 := by
  unfold countOccupied; rw [Array.toList_set]
  refine List.countP_set_of_false_to_true _ _ _ (by rwa [Array.length_toList]) ?_ (by simp)
  simp [hNone]

theorem countOccupied_set_some_to_some
    (slots : Array (Option (RHEntry α β)))
    (i : Nat) (hi : i < slots.size) (e e' : RHEntry α β)
    (hSome : slots[i] = some e') :
    countOccupied (slots.set i (some e)) = countOccupied slots := by
  unfold countOccupied; rw [Array.toList_set]
  refine List.countP_set_of_same _ _ _ (by rwa [Array.length_toList]) ?_
  simp [hSome]

theorem countOccupied_set_some_to_none
    (slots : Array (Option (RHEntry α β)))
    (i : Nat) (hi : i < slots.size) (e : RHEntry α β)
    (hSome : slots[i] = some e) :
    countOccupied (slots.set i none) + 1 = countOccupied slots := by
  unfold countOccupied; rw [Array.toList_set]
  refine List.countP_set_of_true_to_false _ _ _ (by rwa [Array.length_toList]) ?_ (by simp)
  simp [hSome]

-- ============================================================================
-- Section 3: insertLoop countOccupied relationship (N2-A2)
-- ============================================================================

/-- N2-A2: `insertLoop` changes `countOccupied` by exactly `isNew ? 1 : 0`. -/
theorem insertLoop_countOccupied [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (v : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity) :
    let result := insertLoop fuel idx k v d slots capacity hLen hCapPos
    countOccupied result.1 =
      countOccupied slots + if result.2 then 1 else 0 := by
  induction fuel generalizing idx k v d slots hLen with
  | zero => simp [insertLoop]
  | succ n ih =>
    unfold insertLoop; simp only []
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    split
    · -- Empty slot → place entry
      rename_i hNone; simp only [ite_true]
      exact countOccupied_set_none_to_some slots _ hIdx _ hNone
    · -- Occupied slot
      rename_i e hSome; split
      · -- Key match → update
        simp only []
        exact countOccupied_set_some_to_some slots _ hIdx { e with value := v } e hSome
      · split
        · -- Robin Hood swap
          rename_i _ hRH
          have hLen' : (slots.set (idx % capacity) (some ⟨k, v, d⟩)).size = capacity := by
            rw [Array.size_set]; exact hLen
          specialize ih (idx % capacity + 1) e.key e.value (e.dist + 1)
            (slots.set (idx % capacity) (some ⟨k, v, d⟩)) hLen'
          rw [ih, countOccupied_set_some_to_some slots _ hIdx ⟨k, v, d⟩ e hSome]
        · -- Continue probing
          exact ih (idx % capacity + 1) k v (d + 1) slots hLen

-- ============================================================================
-- Section 4: backshiftLoop countOccupied (N2-A6)
-- ============================================================================

/-- N2-A6: `backshiftLoop` preserves `countOccupied` when the gap position
    is initially empty. This precondition is satisfied by `erase`. -/
theorem backshiftLoop_countOccupied
    (fuel : Nat) (gapIdx : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hGapNone : slots[gapIdx % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none) :
    countOccupied (backshiftLoop fuel gapIdx slots capacity hLen hCapPos) =
      countOccupied slots := by
  induction fuel generalizing gapIdx slots hLen with
  | zero => simp [backshiftLoop]
  | succ n ih =>
    unfold backshiftLoop; simp only []
    have hGapI : gapIdx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hNextI : (gapIdx + 1) % capacity < slots.size := by
      rw [hLen]; exact Nat.mod_lt _ hCapPos
    split
    · rfl
    · rename_i e hNext; split
      · rfl
      · -- backward shift
        have hNe : gapIdx % capacity ≠ (gapIdx + 1) % capacity := by
          intro hEq
          have : slots[(gapIdx + 1) % capacity]'hNextI = none := by
            have : slots[(gapIdx + 1) % capacity]'hNextI =
              slots[gapIdx % capacity]'hGapI := by congr 1; exact hEq.symm
            rw [this]; exact hGapNone
          simp [this] at hNext
        -- Build intermediate arrays
        have hSizeS1 : (slots.set (gapIdx % capacity)
            (some { e with dist := e.dist - 1 }) hGapI).size = capacity := by
          rw [Array.size_set]; exact hLen
        -- Count: gap none→some (+1), next some→none (-1), net 0
        have h1 := countOccupied_set_none_to_some slots _ hGapI
          { e with dist := e.dist - 1 } hGapNone
        have hNextUnchanged : (slots.set (gapIdx % capacity)
            (some { e with dist := e.dist - 1 }) hGapI)[(gapIdx + 1) % capacity]'(by
              rw [hSizeS1]; exact Nat.mod_lt _ hCapPos) = some e := by
          simp [Array.getElem_set, hNe]; exact hNext
        have h2 := countOccupied_set_some_to_none
          (slots.set (gapIdx % capacity) (some { e with dist := e.dist - 1 }) hGapI)
          ((gapIdx + 1) % capacity) (by rw [hSizeS1]; exact Nat.mod_lt _ hCapPos)
          e hNextUnchanged
        -- Apply IH: need gap-none for slots₂ at ((gapIdx+1) % cap) % cap
        have hIH := ih ((gapIdx + 1) % capacity)
          ((slots.set (gapIdx % capacity) (some { e with dist := e.dist - 1 }) hGapI).set
            ((gapIdx + 1) % capacity) none (by rw [hSizeS1]; exact Nat.mod_lt _ hCapPos))
          (by simp [Array.size_set]; exact hLen)
          (by simp [Nat.mod_eq_of_lt (Nat.mod_lt _ hCapPos)])
        omega

-- ============================================================================
-- Section 5: countOccupied bound
-- ============================================================================

/-- countP never exceeds list length. -/
private theorem List.countP_le_len {p : α → Bool} :
    ∀ (l : List α), l.countP p ≤ l.length := by
  intro l; induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.countP_cons, List.length_cons]
    split <;> omega

/-- countOccupied never exceeds array size. -/
theorem countOccupied_le_size (slots : Array (Option (RHEntry α β))) :
    countOccupied slots ≤ slots.size := by
  unfold countOccupied
  have := List.countP_le_len (p := (·.isSome)) (l := slots.toList)
  rwa [Array.length_toList] at this

-- ============================================================================
-- Section 6: WF Preservation (N2-A3, N2-A4, N2-A5)
-- ============================================================================

/-- N2-A3: `insertNoResize` preserves well-formedness. -/
theorem RHTable.insertNoResize_preserves_wf [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) (v : β) (hwf : t.WF) :
    (t.insertNoResize k v).WF where
  slotsLen := by
    show (insertLoop t.capacity _ k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos).1.size
         = t.capacity
    rw [insertLoop_preserves_len]; exact t.hSlotsLen
  capPos := t.hCapPos
  sizeCount := by
    show (if (insertLoop t.capacity _ k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos).2
          then t.size + 1 else t.size) =
         countOccupied (insertLoop t.capacity _ k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos).1
    have hC := insertLoop_countOccupied t.capacity (idealIndex k t.capacity t.hCapPos)
      k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos
    rw [hwf.sizeCount]; split <;> simp_all <;> omega
  sizeBound := by
    show (if (insertLoop t.capacity _ k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos).2
          then t.size + 1 else t.size) ≤ t.capacity
    split
    · -- isNew = true: countOccupied increased by 1, but ≤ capacity
      rename_i hNew
      have hCnt := insertLoop_countOccupied t.capacity (idealIndex k t.capacity t.hCapPos)
        k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos
      have hBound := countOccupied_le_size
        (insertLoop t.capacity (idealIndex k t.capacity t.hCapPos)
          k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos).1
      rw [insertLoop_preserves_len, t.hSlotsLen] at hBound
      simp [hNew] at hCnt
      rw [hwf.sizeCount]; omega
    · exact hwf.sizeBound

/-- N2-A3: `insert` preserves well-formedness. -/
theorem RHTable.insert_preserves_wf [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) (v : β) (hwf : t.WF) :
    (t.insert k v).WF := by
  unfold RHTable.insert
  split
  · -- resize path
    exact (t.resize).insertNoResize_preserves_wf k v (by
      -- resize preserves WF (proved via fold induction)
      unfold RHTable.resize RHTable.fold
      exact Array.foldl_induction
        (motive := fun _ (acc : RHTable α β) => acc.WF)
        (RHTable.empty_wf _ _)
        (fun i acc hAcc => by
          split
          · exact hAcc
          · exact acc.insertNoResize_preserves_wf _ _ hAcc))
  · -- no resize
    exact t.insertNoResize_preserves_wf k v hwf

/-- N2-A5: `resize` preserves well-formedness. -/
theorem RHTable.resize_preserves_wf [BEq α] [Hashable α]
    (t : RHTable α β) : (t.resize).WF := by
  unfold RHTable.resize RHTable.fold
  exact Array.foldl_induction
    (motive := fun _ (acc : RHTable α β) => acc.WF)
    (RHTable.empty_wf _ _)
    (fun i acc hAcc => by
      split
      · exact hAcc
      · exact acc.insertNoResize_preserves_wf _ _ hAcc)

-- ============================================================================
-- Section 7: findLoop validity (for erase)
-- ============================================================================

/-- `findLoop` returns a position < capacity when it succeeds. -/
theorem findLoop_lt [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (p : Nat) (hFound : findLoop fuel idx k d slots capacity hLen hCapPos = some p) :
    p < capacity := by
  induction fuel generalizing idx d with
  | zero => simp [findLoop] at hFound
  | succ n ih =>
    unfold findLoop at hFound; simp only [] at hFound
    split at hFound
    · simp at hFound
    · rename_i e hSlot
      split at hFound
      · -- key match: p = idx % capacity
        simp at hFound; rw [← hFound]; exact Nat.mod_lt _ hCapPos
      · split at hFound
        · simp at hFound
        · exact ih (idx % capacity + 1) (d + 1) hFound

/-- `findLoop` returns a position where the key exists. -/
theorem findLoop_correct [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (p : Nat) (hFound : findLoop fuel idx k d slots capacity hLen hCapPos = some p) :
    ∃ e, slots[p]'(by rw [hLen]; exact findLoop_lt fuel idx k d slots capacity hLen hCapPos p hFound) = some e
       ∧ (e.key == k) = true := by
  induction fuel generalizing idx d with
  | zero => simp [findLoop] at hFound
  | succ n ih =>
    unfold findLoop at hFound; simp only [] at hFound
    split at hFound
    · simp at hFound
    · rename_i e hSlot
      split at hFound
      · -- key match: p = idx % capacity
        rename_i hKey
        have hp : p = idx % capacity := by simp at hFound; exact hFound.symm
        subst hp
        exact ⟨e, hSlot, hKey⟩
      · split at hFound
        · simp at hFound
        · exact ih (idx % capacity + 1) (d + 1) hFound

-- ============================================================================
-- Section 8: erase preserves WF (N2-A4)
-- ============================================================================

/-- N2-A4: `erase` preserves well-formedness. -/
theorem RHTable.erase_preserves_wf [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) (hwf : t.WF) :
    (t.erase k).WF := by
  simp only [RHTable.erase]
  split
  · exact hwf  -- key not found
  · -- key found at position idx
    rename_i idx hFound
    have hIdxLt := findLoop_lt t.capacity _ k 0 t.slots t.capacity t.hSlotsLen t.hCapPos
      idx hFound
    have ⟨e, hSlot, _⟩ := findLoop_correct t.capacity _ k 0 t.slots t.capacity t.hSlotsLen
      t.hCapPos idx hFound
    have hIdxS : idx % t.capacity < t.slots.size := by
      rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
    constructor
    · -- slotsLen
      show (backshiftLoop _ _ _ _ _ _).size = t.capacity
      rw [backshiftLoop_preserves_len, Array.size_set]; exact t.hSlotsLen
    · exact t.hCapPos
    · -- sizeCount
      have hLen' : (t.slots.set (idx % t.capacity) none hIdxS).size = t.capacity := by
        rw [Array.size_set]; exact t.hSlotsLen
      have hGapNone : (t.slots.set (idx % t.capacity) none hIdxS)[idx % t.capacity]'(by
          rw [hLen']; exact Nat.mod_lt _ t.hCapPos) = none := by
        simp [Array.getElem_set, Nat.mod_eq_of_lt (Nat.mod_lt _ t.hCapPos)]
      have hBS := backshiftLoop_countOccupied t.capacity idx _ _ hLen' t.hCapPos hGapNone
      have hSlot' : t.slots[idx % t.capacity]'hIdxS = some e := by
        simp [Nat.mod_eq_of_lt hIdxLt]; exact hSlot
      have hDrop := countOccupied_set_some_to_none t.slots (idx % t.capacity) hIdxS e hSlot'
      show t.size - 1 = countOccupied (backshiftLoop t.capacity idx
          (t.slots.set (idx % t.capacity) none hIdxS) t.capacity hLen' t.hCapPos)
      rw [hBS, hwf.sizeCount]; omega
    · show t.size - 1 ≤ t.capacity; have := hwf.sizeBound; omega

-- ============================================================================
-- Section 9: Modular arithmetic helper
-- ============================================================================

/-- Key modular arithmetic: incrementing displacement by 1 when advancing
    to the next probe position. Used in distCorrect preservation proofs. -/
private theorem mod_succ_eq (x n : Nat) (hn : 0 < n) (hBound : x % n + 1 < n) :
    x % n + 1 = (x + 1) % n := by
  have hDiv := Nat.div_add_mod x n
  have hDecomp : x + 1 = (x % n + 1) + n * (x / n) := by omega
  show x % n + 1 = (x + 1) % n
  rw [show x + 1 = (x % n + 1) + n * (x / n) from hDecomp]
  rw [Nat.add_mul_mod_self_left (x % n + 1) n (x / n)]
  exact (Nat.mod_eq_of_lt hBound).symm

/-- Displacement at position (i+1)%cap equals displacement at i plus 1,
    modulo capacity, when the displacement is below cap-1. -/
private theorem dist_step_mod (i h cap : Nat) (hCapPos : 0 < cap)
    (hi : i < cap) (hh : h < cap) (d : Nat)
    (hD : d = (i + cap - h) % cap) (hSmall : d + 1 < cap) :
    d + 1 = ((i + 1) % cap + cap - h) % cap := by
  subst hD
  -- Key: (i + cap - h) % cap + 1 = ((i + 1) % cap + cap - h) % cap
  -- By mod_succ_eq: (i + cap - h) % cap + 1 = (i + cap - h + 1) % cap
  rw [mod_succ_eq _ _ hCapPos hSmall]
  -- Now: (i + cap - h + 1) % cap = ((i + 1) % cap + cap - h) % cap
  -- i + cap - h + 1 = (i + 1) + cap - h
  -- (i+1) = (i+1) % cap + cap * ((i+1) / cap)
  -- So i + cap - h + 1 = (i+1) % cap + cap * ((i+1) / cap) + cap - h
  --                     = ((i+1) % cap + cap - h) + cap * ((i+1) / cap)
  -- Therefore (i + cap - h + 1) % cap = ((i+1) % cap + cap - h) % cap
  have hDiv := Nat.div_add_mod (i + 1) cap
  -- (i+1) / cap * cap + (i+1) % cap = i + 1
  -- So i + 1 = (i+1) / cap * cap + (i+1) % cap
  have hMod_lt : (i + 1) % cap < cap := Nat.mod_lt _ hCapPos
  have hDiv_le : (i + 1) / cap ≤ 1 := by
    by_cases h1 : i + 1 < cap
    · rw [Nat.div_eq_of_lt h1]; omega
    · have : i + 1 = cap := by omega
      rw [this, Nat.div_self hCapPos]; omega
  -- i + cap - h + 1 = (i + 1) % cap + cap - h + cap * ((i + 1) / cap)
  have key : i + cap - h + 1 = ((i + 1) % cap + cap - h) + cap * ((i + 1) / cap) := by omega
  rw [key, Nat.add_mul_mod_self_left]

-- ============================================================================
-- Section 9a: Probe-chain dominant invariant
-- ============================================================================

/-- Probe-chain dominant (slot-level): for every occupied slot at position `p`,
    every position in its probe chain `(idealIndex e.key + d) % cap` for
    `d < e.dist` is occupied by an entry with `dist ≥ d`.

    This prevents insertLoop from Robin-Hood-swapping a key into a
    position when the same key already exists further along the chain,
    which would create duplicate keys. It also enables getLoop's early
    termination. -/
def probeChainDominant [Hashable α]
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    : Prop :=
  ∀ (p : Nat) (hp : p < capacity) (e : RHEntry α β),
    slots[p]'(by rw [hLen]; exact hp) = some e →
    ∀ (d : Nat), d < e.dist →
      ∃ e', slots[(idealIndex e.key capacity hCapPos + d) % capacity]'(by
        rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' ∧ e'.dist ≥ d

/-- Table-level probe-chain dominant. -/
def RHTable.probeChainDominant [Hashable α] (t : RHTable α β) : Prop :=
  SeLe4n.Kernel.RobinHood.probeChainDominant t.slots t.capacity t.hSlotsLen t.hCapPos

/-- Empty tables trivially satisfy probe-chain dominant. -/
theorem RHTable.empty_probeChainDominant [Hashable α] (cap : Nat) (hPos : 0 < cap) :
    (RHTable.empty cap hPos : RHTable α β).probeChainDominant := by
  intro p hp e hSlot
  simp [RHTable.empty] at hSlot

/-- Extended invariant: the operational invariant that ALL operations
    preserve, including erase. Uses probeChainDominant instead of
    robinHoodOrdered (which is NOT preserved by backshift-on-erase).

    This is the primary invariant bundle for reasoning about sequences
    of operations. -/
def RHTable.invExt [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
  t.WF ∧ t.distCorrect ∧ t.noDupKeys ∧ t.probeChainDominant

/-- Empty tables satisfy the extended invariant. -/
theorem RHTable.empty_invExt [BEq α] [Hashable α] (cap : Nat) (hPos : 0 < cap) :
    (RHTable.empty cap hPos : RHTable α β).invExt :=
  ⟨RHTable.empty_wf cap hPos,
   RHTable.empty_distCorrect cap hPos,
   RHTable.empty_noDupKeys cap hPos,
   RHTable.empty_probeChainDominant cap hPos⟩

-- ============================================================================
-- Section 9b: Modular arithmetic displacement helpers
-- ============================================================================

/-- If `d = (idx%cap + cap - h) % cap` then `(h + d) % cap = idx % cap`. -/
private theorem displacement_roundtrip
    (idx h cap : Nat) (hCapPos : 0 < cap) (hh : h < cap)
    (d : Nat) (hD : d = (idx % cap + cap - h) % cap) (hd : d < cap) :
    (h + d) % cap = idx % cap := by
  subst hD
  have hMod := Nat.mod_lt idx hCapPos
  by_cases hge : idx % cap ≥ h
  · have hval : (idx % cap + cap - h) % cap = idx % cap - h := by
      have : idx % cap + cap - h = (idx % cap - h) + cap := by omega
      rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    rw [hval]
    have : h + (idx % cap - h) = idx % cap := by omega
    rw [this, Nat.mod_eq_of_lt hMod]
  · have hlt := Nat.lt_of_not_le hge
    have hval : (idx % cap + cap - h) % cap = idx % cap + cap - h := by
      exact Nat.mod_eq_of_lt (by omega)
    rw [hval]
    have : h + (idx % cap + cap - h) = idx % cap + cap := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hMod]

/-- Two positions with the same displacement from a base are equal. -/
private theorem same_displacement_eq
    (i j h cap : Nat) (hCapPos : 0 < cap) (hi : i < cap) (hj : j < cap)
    (hh : h < cap)
    (hEq : (i + cap - h) % cap = (j + cap - h) % cap) :
    i = j := by
  by_cases hige : i ≥ h
  · by_cases hjge : j ≥ h
    · have h1 : (i + cap - h) % cap = i - h := by
        have : i + cap - h = (i - h) + cap := by omega
        rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
      have h2 : (j + cap - h) % cap = j - h := by
        have : j + cap - h = (j - h) + cap := by omega
        rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
      rw [h1, h2] at hEq; omega
    · have hjlt := Nat.lt_of_not_le hjge
      have h1 : (i + cap - h) % cap = i - h := by
        have : i + cap - h = (i - h) + cap := by omega
        rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
      have h2 : (j + cap - h) % cap = j + cap - h := by
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1, h2] at hEq; omega
  · have hilt := Nat.lt_of_not_le hige
    by_cases hjge : j ≥ h
    · have h1 : (i + cap - h) % cap = i + cap - h := by
        exact Nat.mod_eq_of_lt (by omega)
      have h2 : (j + cap - h) % cap = j - h := by
        have : j + cap - h = (j - h) + cap := by omega
        rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
      rw [h1, h2] at hEq; omega
    · have hjlt := Nat.lt_of_not_le hjge
      have h1 : (i + cap - h) % cap = i + cap - h := by
        exact Nat.mod_eq_of_lt (by omega)
      have h2 : (j + cap - h) % cap = j + cap - h := by
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1, h2] at hEq; omega

-- ============================================================================
-- Section 10: insertLoop preserves distCorrect (N2-B2)
-- ============================================================================

/-- N2-B2: `insertLoop` preserves distance correctness at all slots. -/
theorem insertLoop_preserves_distCorrect [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (v : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hDist : ∀ (j : Nat) (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity)
    (hD : d = (idx % capacity + capacity - idealIndex k capacity hCapPos) % capacity)
    (hBound : d + fuel ≤ capacity) :
    ∀ (j : Nat) (hj : j < capacity) (e : RHEntry α β),
      (insertLoop fuel idx k v d slots capacity hLen hCapPos).1[j]'(by
        rw [insertLoop_preserves_len]; rw [hLen]; exact hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity := by
  induction fuel generalizing idx k v d slots hLen with
  | zero => simp [insertLoop]; exact hDist
  | succ n ih =>
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    -- Use a local helper for array set distCorrect transfer
    have set_dist (val : RHEntry α β)
        (hVal : val.dist = (idx % capacity + capacity -
          idealIndex val.key capacity hCapPos) % capacity) :
        ∀ j (hj : j < capacity) e',
          (slots.set (idx % capacity) (some val) hIdx)[j]'(by
            rw [Array.size_set, hLen]; exact hj) = some e' →
          e'.dist = (j + capacity - idealIndex e'.key capacity hCapPos) % capacity := by
      intro j hj e' hSlot
      simp only [Array.getElem_set] at hSlot
      if h : idx % capacity = j then
        subst h; simp at hSlot; obtain rfl := hSlot; exact hVal
      else
        simp [h] at hSlot; exact hDist j hj e' hSlot
    -- Case split on slot value, then simplify insertLoop with the result
    intro j hj e' hSlot
    cases hSlotCase : slots[idx % capacity]'hIdx with
    | none =>
      simp only [insertLoop, hSlotCase] at hSlot
      exact set_dist ⟨k, v, d⟩ hD j hj e' hSlot
    | some e =>
      have hDltCap : d < capacity := by omega
      simp only [insertLoop, hSlotCase] at hSlot
      if hKey : e.key == k then
        simp only [hKey, ite_true] at hSlot
        have hEd := hDist (idx % capacity) (Nat.mod_lt _ hCapPos) e hSlotCase
        exact set_dist { e with value := v } (by simp [hEd]) j hj e' hSlot
      else
        simp only [hKey, ite_false] at hSlot
        if hRH : e.dist < d then
          simp only [hRH, ite_true] at hSlot
          have hLen' : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx).size
              = capacity := by rw [Array.size_set]; exact hLen
          have hDist' := set_dist ⟨k, v, d⟩ hD
          have hEdist := hDist _ (Nat.mod_lt _ hCapPos) e hSlotCase
          have hSmall : e.dist + 1 < capacity := by omega
          have hD' := dist_step_mod _ _ _ hCapPos (Nat.mod_lt _ hCapPos)
            (idealIndex_lt e.key capacity hCapPos) e.dist hEdist hSmall
          exact ih _ e.key e.value (e.dist + 1) _ hLen' hDist' hD'
            (by omega) j hj e' hSlot
        else
          simp only [hRH, ite_false] at hSlot
          -- When n = 0 (fuel = 1), the recursive call returns (slots, false)
          -- and hDist applies directly
          match n, ih with
          | 0, _ =>
            simp [insertLoop] at hSlot
            exact hDist j hj e' hSlot
          | n' + 1, ih =>
            have hSmall : d + 1 < capacity := by omega
            have hD' := dist_step_mod _ _ _ hCapPos (Nat.mod_lt _ hCapPos)
              (idealIndex_lt k capacity hCapPos) d hD hSmall
            exact ih _ k v (d + 1) slots hLen hDist hD' (by omega) j hj e' hSlot

-- ============================================================================
-- Section 11: Lift to table-level + resize/erase
-- ============================================================================

/-- N2-B: `insertNoResize` preserves distance correctness. -/
theorem RHTable.insertNoResize_preserves_distCorrect [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) (v : β) (hDist : t.distCorrect) :
    (t.insertNoResize k v).distCorrect := by
  intro j hj e hSlot
  have := insertLoop_preserves_distCorrect t.capacity (idealIndex k t.capacity t.hCapPos)
    k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos hDist
    (by simp [Nat.mod_eq_of_lt (idealIndex_lt k t.capacity t.hCapPos)]) (by omega)
  exact this j hj e hSlot

/-- N2-B: `resize` preserves distance correctness. -/
theorem RHTable.resize_preserves_distCorrect [BEq α] [Hashable α]
    (t : RHTable α β) :
    (t.resize).distCorrect := by
  unfold RHTable.resize RHTable.fold
  exact Array.foldl_induction
    (motive := fun _ (acc : RHTable α β) => acc.distCorrect)
    (RHTable.empty_distCorrect _ _)
    (fun i acc hAcc => by
      split
      · exact hAcc
      · exact acc.insertNoResize_preserves_distCorrect _ _ hAcc)

/-- N2-B: `insert` preserves distance correctness. -/
theorem RHTable.insert_preserves_distCorrect [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) (v : β) (hDist : t.distCorrect) :
    (t.insert k v).distCorrect := by
  unfold RHTable.insert; split
  · exact (t.resize).insertNoResize_preserves_distCorrect k v
      (t.resize_preserves_distCorrect)
  · exact t.insertNoResize_preserves_distCorrect k v hDist

/-- N2-C: `insertNoResize` preserves no-duplicate-keys.
    Requires the extended invariant (probeChainDominant) to ensure insertLoop
    finds existing keys before performing Robin Hood swaps. -/
theorem RHTable.insertNoResize_preserves_noDupKeys [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insertNoResize k v).noDupKeys := by
  sorry -- TPI-D1 insertLoop noDupKeys induction (probeChainDominant prevents swap past existing key)

-- Note: `insertNoResize_preserves_robinHoodOrdered` is provable for insert
-- (unlike erase) but is not required for the operational invariant bundle
-- `invExt`. It is retained as a structural property available for future use
-- in a subsequent workstream phase.

/-- `insertNoResize` preserves probeChainDominant. -/
theorem RHTable.insertNoResize_preserves_probeChainDominant [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insertNoResize k v).probeChainDominant := by
  sorry -- TPI-D2 insertLoop probeChainDominant induction (placed entry's chain is occupied)

/-- `insertNoResize` preserves the extended invariant. -/
theorem RHTable.insertNoResize_preserves_invExt [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insertNoResize k v).invExt :=
  ⟨t.insertNoResize_preserves_wf k v hExt.1,
   t.insertNoResize_preserves_distCorrect k v hExt.2.1,
   t.insertNoResize_preserves_noDupKeys k v hExt,
   t.insertNoResize_preserves_probeChainDominant k v hExt⟩

/-- N2-C: `resize` preserves no-duplicate-keys. -/
theorem RHTable.resize_preserves_noDupKeys [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) :
    (t.resize).noDupKeys := by
  unfold RHTable.resize RHTable.fold
  exact (Array.foldl_induction
    (motive := fun _ (acc : RHTable α β) => acc.invExt)
    (RHTable.empty_invExt _ _)
    (fun i acc hAcc => by
      cases t.slots[i] with
      | none => exact hAcc
      | some e => exact acc.insertNoResize_preserves_invExt _ _ hAcc)).2.2.1

/-- `resize` preserves probeChainDominant. -/
theorem RHTable.resize_preserves_probeChainDominant [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) :
    (t.resize).probeChainDominant := by
  unfold RHTable.resize RHTable.fold
  exact (Array.foldl_induction
    (motive := fun _ (acc : RHTable α β) => acc.invExt)
    (RHTable.empty_invExt _ _)
    (fun i acc hAcc => by
      cases t.slots[i] with
      | none => exact hAcc
      | some e => exact acc.insertNoResize_preserves_invExt _ _ hAcc)).2.2.2

/-- `resize` preserves the extended invariant. -/
theorem RHTable.resize_preserves_invExt [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) :
    (t.resize).invExt :=
  ⟨t.resize_preserves_wf, t.resize_preserves_distCorrect,
   t.resize_preserves_noDupKeys, t.resize_preserves_probeChainDominant⟩

/-- N2-C: `insert` preserves no-duplicate-keys. -/
theorem RHTable.insert_preserves_noDupKeys [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insert k v).noDupKeys := by
  unfold RHTable.insert; split
  · exact (t.resize).insertNoResize_preserves_noDupKeys k v t.resize_preserves_invExt
  · exact t.insertNoResize_preserves_noDupKeys k v hExt

/-- `insert` preserves probeChainDominant. -/
theorem RHTable.insert_preserves_probeChainDominant [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insert k v).probeChainDominant := by
  unfold RHTable.insert; split
  · exact (t.resize).insertNoResize_preserves_probeChainDominant k v t.resize_preserves_invExt
  · exact t.insertNoResize_preserves_probeChainDominant k v hExt

-- ============================================================================
-- Section 11a: Backshift invariant helpers (for erase proofs)
-- ============================================================================

/-- Clearing a slot preserves noDupKeys. -/
private theorem noDupKeys_after_clear [BEq α]
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (idx : Nat) (hIdx : idx < slots.size)
    (hNoDup : ∀ (i j : Nat) (hi : i < capacity) (hj : j < capacity)
      (ei ej : RHEntry α β),
      slots[i]'(by rw [hLen]; exact hi) = some ei →
      slots[j]'(by rw [hLen]; exact hj) = some ej →
      (ei.key == ej.key) = true → i = j) :
    ∀ (i j : Nat) (hi : i < capacity) (hj : j < capacity)
      (ei ej : RHEntry α β),
      (slots.set idx none hIdx)[i]'(by rw [Array.size_set, hLen]; exact hi) = some ei →
      (slots.set idx none hIdx)[j]'(by rw [Array.size_set, hLen]; exact hj) = some ej →
      (ei.key == ej.key) = true → i = j := by
  intro i j hi hj ei ej hI hJ hKeyEq
  simp only [Array.getElem_set] at hI hJ
  split at hI
  · simp at hI
  · split at hJ
    · simp at hJ
    · exact hNoDup i j hi hj ei ej hI hJ hKeyEq

/-- backshiftLoop preserves noDupKeys when the gap is initially empty. -/
theorem backshiftLoop_preserves_noDupKeys [BEq α]
    (fuel : Nat) (gapIdx : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hGapNone : slots[gapIdx % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none)
    (hNoDup : ∀ (i j : Nat) (hi : i < capacity) (hj : j < capacity)
      (ei ej : RHEntry α β),
      slots[i]'(by rw [hLen]; exact hi) = some ei →
      slots[j]'(by rw [hLen]; exact hj) = some ej →
      (ei.key == ej.key) = true → i = j) :
    ∀ (i j : Nat) (hi : i < capacity) (hj : j < capacity)
      (ei ej : RHEntry α β),
      (backshiftLoop fuel gapIdx slots capacity hLen hCapPos)[i]'(by
        rw [backshiftLoop_preserves_len, hLen]; exact hi) = some ei →
      (backshiftLoop fuel gapIdx slots capacity hLen hCapPos)[j]'(by
        rw [backshiftLoop_preserves_len, hLen]; exact hj) = some ej →
      (ei.key == ej.key) = true → i = j := by
  induction fuel generalizing gapIdx slots hLen with
  | zero => simp [backshiftLoop]; exact hNoDup
  | succ n ih =>
    have hGapI : gapIdx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hNextI : (gapIdx + 1) % capacity < slots.size := by
      rw [hLen]; exact Nat.mod_lt _ hCapPos
    intro i j hi hj ei ej hI hJ hKeyEq
    -- Case split on the next slot value
    match hSlot : slots[(gapIdx + 1) % capacity]'hNextI with
    | none =>
      simp [backshiftLoop, hSlot] at hI hJ
      exact hNoDup i j hi hj ei ej hI hJ hKeyEq
    | some nextE =>
      if hDist : nextE.dist == 0 then
        simp [backshiftLoop, hSlot, hDist] at hI hJ
        exact hNoDup i j hi hj ei ej hI hJ hKeyEq
      else
        -- backward shift
        have hNe : gapIdx % capacity ≠ (gapIdx + 1) % capacity := by
          intro hEq
          have hSame : slots[gapIdx % capacity]'hGapI =
              slots[(gapIdx + 1) % capacity]'hNextI := by congr 1
          rw [hGapNone, hSlot] at hSame; injection hSame
        -- Simplify backshiftLoop to the recursive call
        have hDistF : (nextE.dist == 0) = false := by
          cases h : nextE.dist == 0 <;> simp_all
        simp only [backshiftLoop, hSlot, hDistF, ↓reduceIte] at hI hJ
        -- Clean up remaining if false = true
        simp only [show (false = true) ↔ False from ⟨Bool.noConfusion, False.elim⟩,
          ite_false] at hI hJ
        -- noDupKeys for intermediate array
        have hNoDup2 : ∀ (a b : Nat) (ha : a < capacity) (hb : b < capacity)
            (ea eb : RHEntry α β),
            ((slots.set (gapIdx % capacity) (some { nextE with dist := nextE.dist - 1 })
              hGapI).set ((gapIdx + 1) % capacity) none
              (by rw [Array.size_set]; exact hNextI))[a]'(by
                rw [Array.size_set, Array.size_set, hLen]; exact ha) = some ea →
            ((slots.set (gapIdx % capacity) (some { nextE with dist := nextE.dist - 1 })
              hGapI).set ((gapIdx + 1) % capacity) none
              (by rw [Array.size_set]; exact hNextI))[b]'(by
                rw [Array.size_set, Array.size_set, hLen]; exact hb) = some eb →
            (ea.key == eb.key) = true → a = b := by
          intro a b ha hb ea eb hA hB hK
          simp only [Array.getElem_set] at hA hB
          split at hA
          · simp at hA
          · rename_i haNe
            split at hB
            · simp at hB
            · rename_i hbNe
              split at hA
              · rename_i haGap
                split at hB
                · rename_i hbGap; exact haGap ▸ hbGap ▸ rfl
                · rename_i hbNG
                  have : ea.key = nextE.key := by
                    have := Option.some.inj hA; rw [← this]
                  rw [this] at hK
                  exact absurd (hNoDup _ b (Nat.mod_lt _ hCapPos) hb nextE eb hSlot hB hK) hbNe
              · rename_i haNG
                split at hB
                · rename_i hbGap
                  have : eb.key = nextE.key := by
                    have := Option.some.inj hB; rw [← this]
                  rw [this] at hK
                  exact absurd (hNoDup a _ ha (Nat.mod_lt _ hCapPos) ea nextE hA hSlot hK)
                    (Ne.symm haNe)
                · exact hNoDup a b ha hb ea eb hA hB hK
        have hLen2 : ((slots.set (gapIdx % capacity)
            (some { nextE with dist := nextE.dist - 1 }) hGapI).set
            ((gapIdx + 1) % capacity) none
            (by rw [Array.size_set]; exact hNextI)).size = capacity := by
          rw [Array.size_set, Array.size_set]; exact hLen
        have hNewGap : ((slots.set (gapIdx % capacity)
            (some { nextE with dist := nextE.dist - 1 }) hGapI).set
            ((gapIdx + 1) % capacity) none
            (by rw [Array.size_set]; exact hNextI))[((gapIdx + 1) % capacity) % capacity]'(by
              rw [hLen2]; exact Nat.mod_lt _ hCapPos) = none := by
          have hMod : ((gapIdx + 1) % capacity) % capacity = (gapIdx + 1) % capacity :=
            Nat.mod_eq_of_lt (Nat.mod_lt _ hCapPos)
          simp_all [Array.getElem_set]
        exact ih ((gapIdx + 1) % capacity) _ hLen2 hNewGap hNoDup2 i j hi hj ei ej hI hJ hKeyEq

/-- Displacement step backward: moving entry from (g+1)%cap to g%cap decrements
    displacement by 1. -/
private theorem displacement_backward [Hashable α]
    (g cap : Nat) (hCapPos : 0 < cap) (k : α)
    (d : Nat) (hd : d = ((g + 1) % cap + cap - idealIndex k cap hCapPos) % cap)
    (hd_pos : 0 < d) :
    d - 1 = (g % cap + cap - idealIndex k cap hCapPos) % cap := by
  have hh := idealIndex_lt k cap hCapPos
  have hgm := Nat.mod_lt g hCapPos
  -- Use dist_step_mod in reverse: show d' + 1 = d where d' is the backward displacement
  -- First show d' + 1 < cap
  suffices hMain : (g % cap + cap - idealIndex k cap hCapPos) % cap + 1 =
      ((g + 1) % cap + cap - idealIndex k cap hCapPos) % cap by omega
  -- Prove via dist_step_mod: d + 1 = ((i+1)%cap + cap - h) % cap given d = (i + cap - h) % cap
  -- with i = g % cap, h = idealIndex, d = (g%cap + cap - ideal) % cap
  -- Need: d + 1 < cap (where d = (g%cap + cap - ideal) % cap)
  -- Prove d + 1 < cap indirectly: if d = cap - 1, then d + 1 = cap and by dist_step_mod
  -- the RHS would equal cap which is 0 mod cap. But d > 0 implies hMain holds trivially
  -- if d + 1 = cap since both sides would differ.
  -- Actually, let's just apply dist_step_mod and handle the cap-1 case separately.
  by_cases hSmall : (g % cap + cap - idealIndex k cap hCapPos) % cap + 1 < cap
  · -- Normal case: apply dist_step_mod
    have hStep := dist_step_mod (g % cap) (idealIndex k cap hCapPos) cap hCapPos
      (Nat.mod_lt _ hCapPos) hh
      ((g % cap + cap - idealIndex k cap hCapPos) % cap) rfl hSmall
    -- hStep: d' + 1 = ((g%cap + 1) % cap + cap - ideal) % cap
    -- Need: ((g%cap + 1) % cap + cap - ideal) % cap = ((g+1) % cap + cap - ideal) % cap
    have : (g % cap + 1) % cap = (g + 1) % cap := by
      have hDiv := Nat.div_add_mod g cap
      rw [show g + 1 = g % cap + 1 + cap * (g / cap) from by omega,
        Nat.add_mul_mod_self_left]
    rw [this] at hStep; exact hStep
  · -- Edge case: d' = cap - 1 → d = 0, contradicting hd_pos
    exfalso
    have hd'_eq : (g % cap + cap - idealIndex k cap hCapPos) % cap = cap - 1 := by
      have := Nat.mod_lt (g % cap + cap - idealIndex k cap hCapPos) hCapPos; omega
    -- If d' = cap-1, show d = 0
    -- d' = cap-1 means displacement at g%cap is cap-1
    -- At the next position (g+1)%cap, displacement wraps to 0
    -- Case split on whether g%cap + 1 wraps
    by_cases hCase : g % cap + cap - idealIndex k cap hCapPos < cap
    · -- g%cap < ideal: d' = g%cap + cap - ideal = cap - 1, so g%cap = ideal - 1
      have hEqSimp := Nat.mod_eq_of_lt hCase
      have hgVal : g % cap = idealIndex k cap hCapPos - 1 := by omega
      -- (g+1) % cap = ideal (no wrap since g%cap+1 = ideal ≤ cap-1 < cap, or wrap)
      by_cases hw : g % cap + 1 < cap
      · have h1 : (g + 1) % cap = idealIndex k cap hCapPos := by
          have hDiv := Nat.div_add_mod g cap
          rw [show g + 1 = g % cap + 1 + cap * (g / cap) from by omega,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]; omega
        rw [h1, show idealIndex k cap hCapPos + cap - idealIndex k cap hCapPos = cap
          from by omega, Nat.mod_self] at hd; omega
      · -- g%cap + 1 = cap: g%cap = cap-1, ideal = cap. But ideal < cap. Contradiction.
        omega
    · -- g%cap ≥ ideal: d' = g%cap - ideal = cap-1
      have hge : g % cap + cap - idealIndex k cap hCapPos ≥ cap := by omega
      have : (g % cap + cap - idealIndex k cap hCapPos) % cap =
          g % cap - idealIndex k cap hCapPos := by
        rw [show g % cap + cap - idealIndex k cap hCapPos =
          (g % cap - idealIndex k cap hCapPos) + cap from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      -- g%cap - ideal = cap - 1, so g%cap = ideal + cap - 1
      -- g%cap < cap and ideal ≥ 0, so ideal = 0 and g%cap = cap - 1
      have hIdealZ : idealIndex k cap hCapPos = 0 := by omega
      have hgCap : g % cap = cap - 1 := by omega
      have h1 : (g + 1) % cap = 0 := by
        rw [show g + 1 = (g % cap + 1) + cap * (g / cap) from by have := Nat.div_add_mod g cap; omega, hgCap,
          show cap - 1 + 1 = cap from by omega, Nat.add_mul_mod_self_left]; simp
      rw [h1, hIdealZ, show 0 + cap - 0 = cap from by omega, Nat.mod_self] at hd; omega

/-- backshiftLoop preserves distCorrect. -/
theorem backshiftLoop_preserves_distCorrect [Hashable α]
    (fuel : Nat) (gapIdx : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hGapNone : slots[gapIdx % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none)
    (hDist : ∀ (j : Nat) (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity) :
    ∀ (j : Nat) (hj : j < capacity) (e : RHEntry α β),
      (backshiftLoop fuel gapIdx slots capacity hLen hCapPos)[j]'(by
        rw [backshiftLoop_preserves_len, hLen]; exact hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity := by
  induction fuel generalizing gapIdx slots hLen with
  | zero => simp [backshiftLoop]; exact hDist
  | succ n ih =>
    have hGapI : gapIdx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hNextI : (gapIdx + 1) % capacity < slots.size := by
      rw [hLen]; exact Nat.mod_lt _ hCapPos
    intro j hj e hSlot
    match hSlotCase : slots[(gapIdx + 1) % capacity]'hNextI with
    | none =>
      simp [backshiftLoop, hSlotCase] at hSlot
      exact hDist j hj e hSlot
    | some nextE =>
      if hDistEq : nextE.dist == 0 then
        simp [backshiftLoop, hSlotCase, hDistEq] at hSlot
        exact hDist j hj e hSlot
      else
        have hDistF : (nextE.dist == 0) = false := by
          cases h : nextE.dist == 0 <;> simp_all
        simp only [backshiftLoop, hSlotCase, hDistF, ↓reduceIte] at hSlot
        simp only [show (false = true) ↔ False from ⟨Bool.noConfusion, False.elim⟩,
          ite_false] at hSlot
        have hNe : gapIdx % capacity ≠ (gapIdx + 1) % capacity := by
          intro hEq
          have hSame : slots[gapIdx % capacity]'hGapI =
              slots[(gapIdx + 1) % capacity]'hNextI := by congr 1
          rw [hGapNone, hSlotCase] at hSame; injection hSame
        -- distCorrect for intermediate array
        have hDist2 : ∀ (p : Nat) (hp : p < capacity) (e' : RHEntry α β),
            ((slots.set (gapIdx % capacity) (some { nextE with dist := nextE.dist - 1 })
              hGapI).set ((gapIdx + 1) % capacity) none
              (by rw [Array.size_set]; exact hNextI))[p]'(by
                rw [Array.size_set, Array.size_set, hLen]; exact hp) = some e' →
            e'.dist = (p + capacity - idealIndex e'.key capacity hCapPos) % capacity := by
          intro p hp e' hSlot'
          simp only [Array.getElem_set] at hSlot'
          split at hSlot'
          · simp at hSlot'
          · rename_i hpNe
            split at hSlot'
            · rename_i hpGap
              have hE' : e' = { nextE with dist := nextE.dist - 1 } := by
                cases hSlot'; rfl
              rw [hE']
              simp only []
              have hDistOrig := hDist ((gapIdx + 1) % capacity) (Nat.mod_lt _ hCapPos)
                nextE hSlotCase
              have hPos : 0 < nextE.dist := by
                cases h : nextE.dist with
                | zero => simp [h] at hDistEq
                | succ n => omega
              exact displacement_backward gapIdx capacity hCapPos nextE.key nextE.dist
                hDistOrig hPos ▸ (by rw [← hpGap])
            · exact hDist p hp e' hSlot'
        -- New gap
        have hLen2 : ((slots.set (gapIdx % capacity)
            (some { nextE with dist := nextE.dist - 1 }) hGapI).set
            ((gapIdx + 1) % capacity) none
            (by rw [Array.size_set]; exact hNextI)).size = capacity := by
          rw [Array.size_set, Array.size_set]; exact hLen
        have hNewGap : ((slots.set (gapIdx % capacity)
            (some { nextE with dist := nextE.dist - 1 }) hGapI).set
            ((gapIdx + 1) % capacity) none
            (by rw [Array.size_set]; exact hNextI))[((gapIdx + 1) % capacity) % capacity]'(by
              rw [hLen2]; exact Nat.mod_lt _ hCapPos) = none := by
          have hMod : ((gapIdx + 1) % capacity) % capacity = (gapIdx + 1) % capacity :=
            Nat.mod_eq_of_lt (Nat.mod_lt _ hCapPos)
          simp_all [Array.getElem_set]
        exact ih ((gapIdx + 1) % capacity) _ hLen2 hNewGap hDist2 j hj e hSlot

/-- N2-B: `erase` preserves distance correctness. -/
theorem RHTable.erase_preserves_distCorrect [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) :
    (t.erase k).distCorrect := by
  simp only [RHTable.erase]
  split
  · exact hExt.2.1
  · rename_i idx hFound
    have hIdxS : idx % t.capacity < t.slots.size := by
      rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
    have hLen' : (t.slots.set (idx % t.capacity) none hIdxS).size = t.capacity := by
      rw [Array.size_set]; exact t.hSlotsLen
    -- distCorrect for cleared array
    have hDist' : ∀ (j : Nat) (hj : j < t.capacity) (e : RHEntry α β),
        (t.slots.set (idx % t.capacity) none hIdxS)[j]'(by
          rw [hLen']; exact hj) = some e →
        e.dist = (j + t.capacity - idealIndex e.key t.capacity t.hCapPos) % t.capacity := by
      intro j hj e hSlot
      simp only [Array.getElem_set] at hSlot
      split at hSlot
      · simp at hSlot
      · exact hExt.2.1 j hj e hSlot
    have hGap : (t.slots.set (idx % t.capacity) none hIdxS)[idx % t.capacity]'(by
        rw [hLen']; exact Nat.mod_lt _ t.hCapPos) = none := by
      simp [Array.getElem_set]
    intro j hj e hSlot
    exact backshiftLoop_preserves_distCorrect t.capacity idx _ _ hLen' t.hCapPos
      hGap hDist' j hj e hSlot

/-- N2-C: `erase` preserves no-duplicate-keys. -/
theorem RHTable.erase_preserves_noDupKeys [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) :
    (t.erase k).noDupKeys := by
  simp only [RHTable.erase]
  split
  · exact hExt.2.2.1  -- key not found, table unchanged
  · -- key found at idx, clear + backshift
    rename_i idx hFound
    have hIdxLt := findLoop_lt t.capacity _ k 0 t.slots t.capacity t.hSlotsLen t.hCapPos idx hFound
    have hIdxS : idx % t.capacity < t.slots.size := by
      rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
    have hLen' : (t.slots.set (idx % t.capacity) none hIdxS).size = t.capacity := by
      rw [Array.size_set]; exact t.hSlotsLen
    -- noDupKeys for cleared array
    have hND' := noDupKeys_after_clear t.slots t.capacity t.hSlotsLen t.hCapPos
      (idx % t.capacity) hIdxS hExt.2.2.1
    -- gap is none in cleared array
    have hGap : (t.slots.set (idx % t.capacity) none hIdxS)[idx % t.capacity]'(by
        rw [hLen']; exact Nat.mod_lt _ t.hCapPos) = none := by
      simp [Array.getElem_set]
    -- Apply backshiftLoop_preserves_noDupKeys
    intro i j hi hj ei ej hI hJ hKeyEq
    exact backshiftLoop_preserves_noDupKeys t.capacity idx _ _ hLen' t.hCapPos
      hGap hND' i j hi hj ei ej hI hJ hKeyEq

-- Note: `erase_preserves_robinHoodOrdered` is NOT provable.
-- The standard backshift-on-erase algorithm does NOT preserve non-decreasing
-- dist within clusters (counterexample: consecutive entries with equal dist,
-- erasing a middle entry shifts the next entry backward, breaking ordering).
-- This is a well-known property of Robin Hood erase: `robinHoodOrdered` is
-- preserved by insert/resize but NOT by erase. The `probeChainDominant`
-- property (which IS preserved) suffices for lookup correctness.

/-- `erase` preserves probeChainDominant. -/
theorem RHTable.erase_preserves_probeChainDominant [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) :
    (t.erase k).probeChainDominant := by
  sorry -- TPI-D3 backshiftLoop probeChainDominant induction (gap filled maintains chains)

-- ============================================================================
-- Section 12: Composite invariant bundle preservation
-- ============================================================================

/-- `insert` preserves the extended invariant (the operational invariant). -/
theorem RHTable.insert_preserves_invExt [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insert k v).invExt :=
  ⟨t.insert_preserves_wf k v hExt.1,
   t.insert_preserves_distCorrect k v hExt.2.1,
   t.insert_preserves_noDupKeys k v hExt,
   t.insert_preserves_probeChainDominant k v hExt⟩

/-- `erase` preserves the extended invariant (the operational invariant). -/
theorem RHTable.erase_preserves_invExt [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) :
    (t.erase k).invExt :=
  ⟨t.erase_preserves_wf k hExt.1,
   t.erase_preserves_distCorrect k hExt,
   t.erase_preserves_noDupKeys k hExt,
   t.erase_preserves_probeChainDominant k hExt⟩

/-- `resize` preserves the extended invariant. -/
theorem RHTable.resize_preserves_invariant [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) :
    (t.resize).invExt :=
  ⟨t.resize_preserves_wf,
   t.resize_preserves_distCorrect,
   t.resize_preserves_noDupKeys,
   t.resize_preserves_probeChainDominant⟩

end SeLe4n.Kernel.RobinHood
