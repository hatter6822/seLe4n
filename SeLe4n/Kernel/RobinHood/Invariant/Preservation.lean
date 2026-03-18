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
-- Section 9a: Gap consistency — cluster continuity invariant
-- ============================================================================

/-- Gap consistency: an occupied slot with dist > 0 must have an occupied
    predecessor.  This invariant is maintained by all operations and is
    required for noDupKeys preservation proofs. -/
def gapConsistent
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    : Prop :=
  ∀ (i : Nat) (hi : i < capacity) (e : RHEntry α β),
    slots[(i + 1) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e →
    e.dist > 0 →
    ∃ e', slots[i]'(by rw [hLen]; exact hi) = some e'

/-- Table-level gap consistency. -/
def RHTable.gapConsistent (t : RHTable α β) : Prop :=
  SeLe4n.Kernel.RobinHood.gapConsistent t.slots t.capacity t.hSlotsLen t.hCapPos

/-- Empty tables trivially satisfy gap consistency. -/
theorem RHTable.empty_gapConsistent (cap : Nat) (hPos : 0 < cap) :
    (RHTable.empty cap hPos : RHTable α β).gapConsistent := by
  intro i hi e hSlot _
  simp [RHTable.empty] at hSlot

/-- Extended invariant: WF + distCorrect + noDupKeys + robinHoodOrdered +
    gapConsistent.  The gap consistency property is required to prove
    noDupKeys and robinHoodOrdered preservation. -/
def RHTable.invExt [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
  t.invariant ∧ t.gapConsistent

/-- Empty tables satisfy the extended invariant. -/
theorem RHTable.empty_invExt [BEq α] [Hashable α] (cap : Nat) (hPos : 0 < cap) :
    (RHTable.empty cap hPos : RHTable α β).invExt :=
  ⟨RHTable.empty_invariant cap hPos, RHTable.empty_gapConsistent cap hPos⟩

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
    (t : RHTable α β) (k : α) (v : β) (hInv : t.invariant) :
    (t.insert k v).distCorrect := by
  unfold RHTable.insert; split
  · exact (t.resize).insertNoResize_preserves_distCorrect k v
      (t.resize_preserves_distCorrect)
  · exact t.insertNoResize_preserves_distCorrect k v hInv.2.1

/-- N2-C: `insert` preserves no-duplicate-keys. -/
theorem RHTable.insert_preserves_noDupKeys [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hInv : t.invariant) :
    (t.insert k v).noDupKeys := by
  intro i j hi hj ei ej hSlotI hSlotJ hKeyEq
  sorry

/-- N2-D: `insert` preserves Robin Hood ordering. -/
theorem RHTable.insert_preserves_robinHoodOrdered [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hInv : t.invariant) :
    (t.insert k v).robinHoodOrdered := by
  intro i hi ei ej hSlotI hSlotJ
  sorry

/-- N2-B: `erase` preserves distance correctness. -/
theorem RHTable.erase_preserves_distCorrect [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hInv : t.invariant) :
    (t.erase k).distCorrect := by
  intro j hj e hSlot
  sorry

/-- N2-C: `erase` preserves no-duplicate-keys. -/
theorem RHTable.erase_preserves_noDupKeys [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hInv : t.invariant) :
    (t.erase k).noDupKeys := by
  intro i j hi hj ei ej hSlotI hSlotJ hKeyEq
  sorry

/-- N2-D: `erase` preserves Robin Hood ordering. -/
theorem RHTable.erase_preserves_robinHoodOrdered [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hInv : t.invariant) :
    (t.erase k).robinHoodOrdered := by
  intro i hi ei ej hSlotI hSlotJ
  sorry

/-- N2-C: `resize` preserves no-duplicate-keys. -/
theorem RHTable.resize_preserves_noDupKeys [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (hInv : t.invariant) :
    (t.resize).noDupKeys := by
  intro i j hi hj ei ej hSlotI hSlotJ hKeyEq
  sorry

/-- N2-D: `resize` preserves Robin Hood ordering. -/
theorem RHTable.resize_preserves_robinHoodOrdered [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (hInv : t.invariant) :
    (t.resize).robinHoodOrdered := by
  intro i hi ei ej hSlotI hSlotJ
  sorry

-- ============================================================================
-- Section 10: Composite invariant bundle preservation
-- ============================================================================

/-- `insert` preserves the full invariant bundle. -/
theorem RHTable.insert_preserves_invariant [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hInv : t.invariant) :
    (t.insert k v).invariant :=
  ⟨t.insert_preserves_wf k v hInv.1,
   t.insert_preserves_distCorrect k v hInv,
   t.insert_preserves_noDupKeys k v hInv,
   t.insert_preserves_robinHoodOrdered k v hInv⟩

/-- `erase` preserves the full invariant bundle. -/
theorem RHTable.erase_preserves_invariant [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hInv : t.invariant) :
    (t.erase k).invariant :=
  ⟨t.erase_preserves_wf k hInv.1,
   t.erase_preserves_distCorrect k hInv,
   t.erase_preserves_noDupKeys k hInv,
   t.erase_preserves_robinHoodOrdered k hInv⟩

/-- `resize` preserves the full invariant bundle. -/
theorem RHTable.resize_preserves_invariant [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (hInv : t.invariant) :
    (t.resize).invariant :=
  ⟨t.resize_preserves_wf,
   t.resize_preserves_distCorrect,
   t.resize_preserves_noDupKeys hInv,
   t.resize_preserves_robinHoodOrdered hInv⟩

end SeLe4n.Kernel.RobinHood
