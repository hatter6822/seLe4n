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
-- Section 10a: Offset injectivity and carried key absence helpers
-- ============================================================================

/-- Two offsets from the same base that are both < cap and produce the same
    position modulo cap must be equal. -/
private theorem offset_injective (h cap d1 d2 : Nat) (hCapPos : 0 < cap)
    (hd1 : d1 < cap) (hd2 : d2 < cap)
    (hEq : (h + d1) % cap = (h + d2) % cap) : d1 = d2 := by
  have hr := Nat.mod_lt h hCapPos
  -- Reduce to (h%cap + di) % cap
  have hm1 : (h + d1) % cap = (h % cap + d1) % cap := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hd1]
  have hm2 : (h + d2) % cap = (h % cap + d2) % cap := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hd2]
  rw [hm1, hm2] at hEq
  -- Reduce wrapping sums to subtracted form
  have red : ∀ (x : Nat), x < cap → h % cap + x ≥ cap →
      (h % cap + x) % cap = h % cap + x - cap := by
    intro x hx hge
    have := show h % cap + x = (h % cap + x - cap) + cap from by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  by_cases hc1 : h % cap + d1 < cap <;> by_cases hc2 : h % cap + d2 < cap
  · rw [Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2] at hEq; omega
  · rw [Nat.mod_eq_of_lt hc1, red d2 hd2 (by omega)] at hEq; omega
  · rw [red d1 hd1 (by omega), Nat.mod_eq_of_lt hc2] at hEq; omega
  · rw [red d1 hd1 (by omega), red d2 hd2 (by omega)] at hEq; omega

/-- Array access depends only on the index, not the bound proof. -/
private theorem getElem_idx_eq (slots : Array (Option (RHEntry α β)))
    {i j : Nat} (hi : i < slots.size) (hj : j < slots.size) (heq : i = j) :
    slots[i]'hi = slots[j]'hj := by subst heq; rfl

/-- If the probe for key `k` has reached distance `d` without finding `k`,
    and the current slot is either empty or has a resident with `dist < d`
    and key ≠ k, then `k` is absent from the entire table.

    Core argument:
    - `d_k < d` → `hNotFound` at `d' = d_k` contradicts `e.key = k`.
    - `d_k = d` → position equality contradicts `hSlotWeak`.
    - `d_k > d` → PCD of `e` at distance `d` contradicts `hSlotWeak`. -/
private theorem carried_key_absent [BEq α] [Hashable α] [LawfulBEq α]
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (k : α) (d : Nat) (pos : Nat) (hPos : pos < capacity)
    (hD : d = (pos + capacity - idealIndex k capacity hCapPos) % capacity)
    (hDist : ∀ j (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(hLen ▸ hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity)
    (hPCD : probeChainDominant slots capacity hLen hCapPos)
    (hNotFound : ∀ d', d' < d →
      ∀ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
        rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' → (e'.key == k) = false)
    (hSlotWeak : slots[pos]'(by rw [hLen]; exact hPos) = none ∨
      ∃ e : RHEntry α β, slots[pos]'(by rw [hLen]; exact hPos) = some e ∧ e.dist < d
        ∧ (e.key == k) = false) :
    ∀ j (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e → (e.key == k) = false := by
  intro j hj e hSlot
  cases hContra : e.key == k with
  | false => rfl
  | true =>
  exfalso
  have hkj : e.key = k := eq_of_beq hContra
  have hEd := hDist j hj e hSlot
  have hIdK : idealIndex e.key capacity hCapPos = idealIndex k capacity hCapPos := by rw [hkj]
  rw [hIdK] at hEd
  -- e at position j, distance e.dist from ideal(k)
  have hd_lt_cap : d < capacity := by
    have := Nat.mod_lt (pos + capacity - idealIndex k capacity hCapPos) hCapPos; omega
  have hed_lt_cap : e.dist < capacity := by
    have := Nat.mod_lt (j + capacity - idealIndex k capacity hCapPos) hCapPos; omega
  -- (ideal(k) + e.dist) % cap = j
  have hRt : (idealIndex k capacity hCapPos + e.dist) % capacity = j := by
    have := displacement_roundtrip j (idealIndex k capacity hCapPos) capacity hCapPos
      (idealIndex_lt k capacity hCapPos) e.dist
      (by rw [Nat.mod_eq_of_lt hj]; exact hEd) hed_lt_cap
    rwa [Nat.mod_eq_of_lt hj] at this
  -- (ideal(k) + d) % cap = pos
  have hRtD : (idealIndex k capacity hCapPos + d) % capacity = pos := by
    have := displacement_roundtrip pos (idealIndex k capacity hCapPos) capacity hCapPos
      (idealIndex_lt k capacity hCapPos) d
      (by rw [Nat.mod_eq_of_lt hPos]; exact hD) hd_lt_cap
    rwa [Nat.mod_eq_of_lt hPos] at this
  by_cases hLt : e.dist < d
  · -- e.dist < d: hNotFound at d' = e.dist gives contradiction
    have hSlot' : slots[(idealIndex k capacity hCapPos + e.dist) % capacity]'(by
        rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e :=
      getElem_idx_eq slots (by rw [hLen]; exact Nat.mod_lt _ hCapPos)
        (by rw [hLen]; exact hj) hRt ▸ hSlot
    have hFalse := hNotFound e.dist hLt e hSlot'
    simp [hContra] at hFalse
  · by_cases hEq : e.dist = d
    · -- e.dist = d → j = pos, contradicts hSlotWeak
      have hjPos : j = pos := same_displacement_eq j pos (idealIndex k capacity hCapPos)
        capacity hCapPos hj hPos (idealIndex_lt k capacity hCapPos)
        (by rw [← hEd, hEq]; exact hD)
      subst hjPos
      rcases hSlotWeak with hNone | ⟨_, he', _, hKNe⟩
      · rw [hNone] at hSlot; simp at hSlot
      · rw [he'] at hSlot; cases hSlot; simp [hContra] at hKNe
    · -- e.dist > d: PCD requires slot at distance d to have dist ≥ d
      have hGt : d < e.dist := by omega
      obtain ⟨e', he', hge'⟩ := hPCD j hj e hSlot d hGt
      have hIdx : (idealIndex e.key capacity hCapPos + d) % capacity = pos := by
        rw [hIdK]; exact hRtD
      have he'Pos : slots[pos]'(by rw [hLen]; exact hPos) = some e' :=
        getElem_idx_eq slots (by rw [hLen]; exact Nat.mod_lt _ hCapPos)
          (by rw [hLen]; exact hPos) hIdx ▸ he'
      rcases hSlotWeak with hNone | ⟨_, he'', hLtD, _⟩
      · rw [hNone] at he'Pos; simp at he'Pos
      · rw [he''] at he'Pos; cases he'Pos; omega

-- ============================================================================
-- Section 10b: insertLoop preserves noDupKeys and PCD (combined induction)
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- Combined induction: `insertLoop` preserves both noDupKeys and
    probeChainDominant. The preconditions `hChainOK` and `hNotFound`
    capture the progress of the probe: all chain positions up to
    distance `d-1` are occupied with sufficient dist, and none matched
    the carried key `k`. -/
private theorem insertLoop_preserves_noDupKeys [BEq α] [Hashable α] [LawfulBEq α]
    (fuel : Nat) (idx : Nat) (k : α) (v : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hNoDup : ∀ i j (hi : i < capacity) (hj : j < capacity) (ei ej : RHEntry α β),
      slots[i]'(by rw [hLen]; exact hi) = some ei →
      slots[j]'(by rw [hLen]; exact hj) = some ej →
      (ei.key == ej.key) = true → i = j)
    (hDist : ∀ j (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity)
    (hPCD : probeChainDominant slots capacity hLen hCapPos)
    (hD : d = (idx % capacity + capacity - idealIndex k capacity hCapPos) % capacity)
    (hBound : d + fuel ≤ capacity)
    (hChainOK : ∀ d', d' < d →
      ∃ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
        rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' ∧ e'.dist ≥ d')
    (hNotFound : ∀ d', d' < d →
      ∀ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
        rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' → (e'.key == k) = false) :
    ∀ i j (hi : i < capacity) (hj : j < capacity) (ei ej : RHEntry α β),
      (insertLoop fuel idx k v d slots capacity hLen hCapPos).1[i]'(by
        rw [insertLoop_preserves_len, hLen]; exact hi) = some ei →
      (insertLoop fuel idx k v d slots capacity hLen hCapPos).1[j]'(by
        rw [insertLoop_preserves_len, hLen]; exact hj) = some ej →
      (ei.key == ej.key) = true → i = j := by
  induction fuel generalizing idx k v d slots hLen with
  | zero => simp only [insertLoop]; exact hNoDup
  | succ n ih =>
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hIdxCap : idx % capacity < capacity := Nat.mod_lt _ hCapPos
    have hd_lt : d < capacity := by
      have := Nat.mod_lt (idx % capacity + capacity -
        idealIndex k capacity hCapPos) hCapPos; omega
    have hRtD : (idealIndex k capacity hCapPos + d) % capacity =
        idx % capacity := by
      have := displacement_roundtrip (idx % capacity)
        (idealIndex k capacity hCapPos) capacity hCapPos
        (idealIndex_lt k capacity hCapPos) d
        (by rw [Nat.mod_eq_of_lt hIdxCap]; exact hD) hd_lt
      rwa [Nat.mod_eq_of_lt hIdxCap] at this
    -- Helper: chain position dd < d ≠ idx%cap
    have hChainNe : ∀ dd, dd < d →
        (idealIndex k capacity hCapPos + dd) % capacity ≠ idx % capacity := by
      intro dd hdd hEq
      exact absurd (offset_injective (idealIndex k capacity hCapPos) capacity
        dd d hCapPos (by omega) hd_lt (hEq.trans hRtD.symm)) (by omega)
    cases hSlotCase : slots[idx % capacity]'hIdx with
    | none =>
      -- Case 1: Empty slot — place (k,v,d)
      intro a b ha hb ea eb hA hB hKeyEq
      simp only [insertLoop, hSlotCase] at hA hB
      have hKAbs := carried_key_absent slots capacity hLen hCapPos k d
        (idx % capacity) hIdxCap hD hDist hPCD hNotFound (.inl hSlotCase)
      simp only [Array.getElem_set] at hA hB
      split at hA <;> split at hB
      · rename_i h1 h2; exact h1 ▸ h2 ▸ rfl
      · rename_i h1 hbNe; cases hA
        exact absurd (hKAbs b hb eb hB)
          (by have := eq_of_beq hKeyEq; simp [this.symm, beq_self_eq_true])
      · rename_i haNe h2; cases hB
        exact absurd (hKAbs a ha ea hA)
          (by have := eq_of_beq hKeyEq; simp [this, beq_self_eq_true])
      · exact hNoDup a b ha hb ea eb hA hB hKeyEq
    | some e =>
      if hKey : e.key == k then
        -- Case 2: Key match — only value changes, noDupKeys preserved
        intro a b ha hb ea eb hA hB hKeyEq
        simp only [insertLoop, hSlotCase, hKey, ite_true] at hA hB
        simp only [Array.getElem_set] at hA hB
        split at hA <;> split at hB
        · rename_i h1 h2; exact h1 ▸ h2 ▸ rfl
        · rename_i h1 hbN; exfalso
          apply hbN; cases hA; simp only [] at hKeyEq
          exact hNoDup _ b hIdxCap hb e eb hSlotCase hB hKeyEq
        · rename_i haN h2; exfalso
          apply haN; cases hB; simp only [] at hKeyEq
          exact (hNoDup a _ ha hIdxCap ea e hA hSlotCase hKeyEq).symm
        · exact hNoDup a b ha hb ea eb hA hB hKeyEq
      else
        have hKeyF : (e.key == k) = false := by
          cases h : e.key == k
          · rfl
          · exfalso; exact hKey h
        if hRH : e.dist < d then
          -- Case 3: Robin Hood swap — simplify goal to recursive call
          simp only [insertLoop, hSlotCase, hKeyF, if_pos hRH]
          have hLen' : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx).size
              = capacity := by rw [Array.size_set]; exact hLen
          have hKeyNeF : (e.key == k) = false := by
            cases h : e.key == k <;> simp_all
          have hKAbs := carried_key_absent slots capacity hLen hCapPos k d
            (idx % capacity) hIdxCap hD hDist hPCD hNotFound
            (.inr ⟨e, hSlotCase, hRH, hKeyNeF⟩)
          have hEdist := hDist _ hIdxCap e hSlotCase
          have hSmall : e.dist + 1 < capacity := by omega
          have hD' := dist_step_mod _ _ _ hCapPos hIdxCap
            (idealIndex_lt e.key capacity hCapPos) e.dist hEdist hSmall
          -- noDupKeys for intermediate slots'
          have hNoDup' : ∀ i j (hi : i < capacity) (hj : j < capacity)
              (ei ej : RHEntry α β),
              (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[i]'(by
                rw [hLen']; exact hi) = some ei →
              (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[j]'(by
                rw [hLen']; exact hj) = some ej →
              (ei.key == ej.key) = true → i = j := by
            intro i' j' hi' hj' ei' ej' hI' hJ' hKE'
            simp only [Array.getElem_set] at hI' hJ'
            split at hI' <;> split at hJ'
            · rename_i h1 h2; exact h1 ▸ h2 ▸ rfl
            · rename_i h1 hbN; cases hI'
              exact absurd (hKAbs j' hj' ej' hJ') (by
                have := eq_of_beq hKE'; simp [this.symm, beq_self_eq_true])
            · rename_i haN h2; cases hJ'
              exact absurd (hKAbs i' hi' ei' hI') (by
                have := eq_of_beq hKE'; simp [this, beq_self_eq_true])
            · exact hNoDup i' j' hi' hj' ei' ej' hI' hJ' hKE'
          -- distCorrect for intermediate slots'
          have hDist' : ∀ j (hj : j < capacity) (e' : RHEntry α β),
              (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[j]'(by
                rw [hLen']; exact hj) = some e' →
              e'.dist = (j + capacity - idealIndex e'.key capacity hCapPos) %
                capacity := by
            intro j' hj' e' hSlot'
            simp only [Array.getElem_set] at hSlot'
            if h : idx % capacity = j' then
              subst h; simp at hSlot'; obtain rfl := hSlot'; exact hD
            else simp [h] at hSlot'; exact hDist j' hj' e' hSlot'
          -- PCD for intermediate slots' (set increases dist: d > e.dist)
          have hPCD' : probeChainDominant
              (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx) capacity
              hLen' hCapPos := by
            intro p hp e' hSlot' dd hdd
            simp only [Array.getElem_set] at hSlot' ⊢
            split at hSlot'
            · -- p = idx%cap: new entry (k,v,d), dd < d
              rename_i hpEq; subst hpEq; cases hSlot'
              have hNe := hChainNe dd hdd
              split
              · rename_i hEq; exact absurd hEq.symm hNe
              · exact hChainOK dd hdd
            · -- p ≠ idx%cap: existing entry from original
              rename_i hpNe
              obtain ⟨e'', he'', hge''⟩ := hPCD p hp e' hSlot' dd hdd
              if hChEq : (idealIndex e'.key capacity hCapPos + dd) % capacity =
                  idx % capacity then
                split
                · -- if-branch matched: new entry at set position
                  refine ⟨⟨k, v, d⟩, rfl, ?_⟩
                  -- d > e.dist ≥ dd (original PCD gave e.dist ≥ dd, d > e.dist)
                  have h12 := getElem_idx_eq slots
                    (by rw [hLen]; exact Nat.mod_lt _ hCapPos) hIdx hChEq
                  rw [he'', hSlotCase] at h12
                  have hEE : e'' = e := by injection h12
                  subst hEE
                  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hge'' hRH)
                · exact absurd hChEq.symm (by assumption)
              else
                split
                · exact absurd (by assumption) (Ne.symm hChEq)
                · exact ⟨e'', he'', hge''⟩
          -- hNotFound for displaced entry e.key
          have hNotFound' : ∀ d', d' < e.dist + 1 →
              ∀ e', (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[(idealIndex e.key capacity hCapPos + d') % capacity]'(by rw [hLen']; exact Nat.mod_lt _ hCapPos) = some e' →
              (e'.key == e.key) = false := by
            intro d' hd' e' hSlot'
            simp only [Array.getElem_set] at hSlot'
            split at hSlot'
            · -- chain at idx%cap: entry is (k,v,d), key ≠ e.key
              cases hSlot'; show (k == e.key) = false
              cases h : k == e.key
              · rfl
              · exfalso; exact hKey (eq_of_beq h ▸ beq_self_eq_true e.key)
            · -- not at idx%cap: entry from original
              rename_i hNe
              show (e'.key == e.key) = false
              cases h : e'.key == e.key
              · rfl
              · exfalso
                exact absurd (hNoDup _ _ (Nat.mod_lt _ hCapPos) hIdxCap e' e
                  hSlot' hSlotCase h) (Ne.symm hNe)
          -- hChainOK for displaced entry e.key in slots'
          have hChainOK' : ∀ d', d' < e.dist + 1 →
              ∃ e', (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[(idealIndex e.key capacity hCapPos + d') % capacity]'(by rw [hLen']; exact Nat.mod_lt _ hCapPos) = some e' ∧
              e'.dist ≥ d' := by
            intro d' hd'
            have hEdist := hDist _ hIdxCap e hSlotCase
            have hRte : (idealIndex e.key capacity hCapPos + e.dist) % capacity =
                idx % capacity := by
              have := displacement_roundtrip (idx % capacity)
                (idealIndex e.key capacity hCapPos) capacity hCapPos
                (idealIndex_lt e.key capacity hCapPos) e.dist
                (by rw [Nat.mod_eq_of_lt hIdxCap]; exact hEdist) (by omega)
              rwa [Nat.mod_eq_of_lt hIdxCap] at this
            simp only [Array.getElem_set]
            if hChAt : (idealIndex e.key capacity hCapPos + d') % capacity =
                idx % capacity then
              -- d' = e.dist (by offset_injective). Set pos has (k,v,d), d > e.dist ≥ d'.
              split
              · refine ⟨⟨k, v, d⟩, rfl, ?_⟩
                have hDE : d' = e.dist := offset_injective
                  (idealIndex e.key capacity hCapPos) capacity d' e.dist hCapPos
                  (by omega) (by omega) (hChAt.trans hRte.symm)
                exact Nat.le_of_lt (hDE ▸ hRH)
              · rename_i hNe; exact absurd hChAt.symm hNe
            else
              split
              · rename_i hEq; exact absurd hEq (Ne.symm hChAt)
              · -- d' < e.dist (if d' = e.dist, offset_injective gives contradiction)
                have hd'_lt : d' < e.dist := by
                  rcases Nat.lt_or_ge d' e.dist with h | h
                  · exact h
                  · exfalso
                    have : d' = e.dist := Nat.le_antisymm (Nat.lt_succ_iff.mp hd') h
                    exact hChAt (this ▸ hRte)
                exact hPCD _ hIdxCap e hSlotCase d' hd'_lt
          exact ih (idx % capacity + 1) e.key e.value (e.dist + 1)
            (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx) hLen'
            hNoDup' hDist' hPCD' hD' (by omega) hChainOK' hNotFound'
        else
          -- Case 4: Continue probing — apply IH
          have hGe : e.dist ≥ d := by omega
          -- Handle n=0 case separately (fuel=1, recursive call returns slots)
          match n, ih with
          | 0, _ =>
            simp only [insertLoop, hSlotCase, hKeyF, if_neg hRH, insertLoop]
            exact hNoDup
          | n' + 1, ih =>
            -- Reduce goal so insertLoop (n'+2) unfolds to recursive call
            simp only [insertLoop, hSlotCase, hKeyF, if_neg hRH]
            have hSmall : d + 1 < capacity := by omega
            have hD' := dist_step_mod _ _ _ hCapPos hIdxCap
              (idealIndex_lt k capacity hCapPos) d hD hSmall
            have hChainOK' : ∀ d', d' < d + 1 →
                ∃ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
                  rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' ∧
                e'.dist ≥ d' := by
              intro d' hd'
              if hLt : d' < d then exact hChainOK d' hLt
              else
                have hEq : d' = d := by omega
                subst hEq
                refine ⟨e, ?_, hGe⟩
                exact (getElem_idx_eq slots (by rw [hLen]; exact Nat.mod_lt _ hCapPos)
                  hIdx hRtD).symm ▸ hSlotCase
            have hNotFound' : ∀ d', d' < d + 1 →
                ∀ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
                  rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' →
                (e'.key == k) = false := by
              intro d' hd' e' hSlot'
              if hLt : d' < d then exact hNotFound d' hLt e' hSlot'
              else
                have hEq : d' = d := by omega
                subst hEq
                have := getElem_idx_eq slots
                  (by rw [hLen]; exact Nat.mod_lt _ hCapPos)
                  (by rw [hLen]; exact hIdxCap) hRtD
                rw [this] at hSlot'; rw [hSlotCase] at hSlot'; cases hSlot'
                exact hKeyF
            exact ih (idx % capacity + 1) k v (d + 1) slots hLen
              hNoDup hDist hPCD hD' (by omega) hChainOK' hNotFound'


-- ============================================================================
-- Section 10c: insertLoop preserves probeChainDominant
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- `insertLoop` preserves `probeChainDominant`. Same case structure as
    `insertLoop_preserves_noDupKeys`, proving PCD for the result array. -/
private theorem insertLoop_preserves_pcd [BEq α] [Hashable α] [LawfulBEq α]
    (fuel : Nat) (idx : Nat) (k : α) (v : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hNoDup : ∀ i j (hi : i < capacity) (hj : j < capacity) (ei ej : RHEntry α β),
      slots[i]'(by rw [hLen]; exact hi) = some ei →
      slots[j]'(by rw [hLen]; exact hj) = some ej →
      (ei.key == ej.key) = true → i = j)
    (hDist : ∀ j (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity)
    (hPCD : probeChainDominant slots capacity hLen hCapPos)
    (hD : d = (idx % capacity + capacity - idealIndex k capacity hCapPos) % capacity)
    (hBound : d + fuel ≤ capacity)
    (hChainOK : ∀ d', d' < d →
      ∃ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
        rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' ∧ e'.dist ≥ d')
    (hNotFound : ∀ d', d' < d →
      ∀ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
        rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' → (e'.key == k) = false) :
    probeChainDominant (insertLoop fuel idx k v d slots capacity hLen hCapPos).1 capacity
      (by rw [insertLoop_preserves_len]; exact hLen) hCapPos := by
  induction fuel generalizing idx k v d slots hLen with
  | zero => simp only [insertLoop]; exact hPCD
  | succ n ih =>
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hIdxCap : idx % capacity < capacity := Nat.mod_lt _ hCapPos
    have hd_lt : d < capacity := by
      have := Nat.mod_lt (idx % capacity + capacity -
        idealIndex k capacity hCapPos) hCapPos; omega
    have hRtD : (idealIndex k capacity hCapPos + d) % capacity =
        idx % capacity := by
      have := displacement_roundtrip (idx % capacity)
        (idealIndex k capacity hCapPos) capacity hCapPos
        (idealIndex_lt k capacity hCapPos) d
        (by rw [Nat.mod_eq_of_lt hIdxCap]; exact hD) hd_lt
      rwa [Nat.mod_eq_of_lt hIdxCap] at this
    have hChainNe : ∀ dd, dd < d →
        (idealIndex k capacity hCapPos + dd) % capacity ≠ idx % capacity := by
      intro dd hdd hEq
      exact absurd (offset_injective (idealIndex k capacity hCapPos) capacity
        dd d hCapPos (by omega) hd_lt (hEq.trans hRtD.symm)) (by omega)
    cases hSlotCase : slots[idx % capacity]'hIdx with
    | none =>
      -- Empty slot: PCD for slots.set(idx%cap, (k,v,d))
      intro p hp e' hSlot' dd hdd
      simp only [insertLoop, hSlotCase] at hSlot' ⊢
      simp only [Array.getElem_set] at hSlot' ⊢
      split at hSlot'
      · -- p = idx%cap: new entry (k,v,d), dd < d
        rename_i hpEq; subst hpEq; cases hSlot'
        have hNe := hChainNe dd hdd
        split
        · rename_i hEq; exact absurd hEq.symm hNe
        · exact hChainOK dd hdd
      · -- p ≠ idx%cap: existing entry
        rename_i hpNe
        obtain ⟨e'', he'', hge''⟩ := hPCD p hp e' hSlot' dd hdd
        if hChEq : (idealIndex e'.key capacity hCapPos + dd) % capacity =
            idx % capacity then
          -- Chain through empty slot: PCD says entry there, but it was empty
          have h12 := getElem_idx_eq slots
            (by rw [hLen]; exact Nat.mod_lt _ hCapPos) hIdx hChEq
          rw [he'', hSlotCase] at h12; exact absurd h12 (by simp)
        else
          split
          · rename_i hEq; exact absurd hEq (Ne.symm hChEq)
          · exact ⟨e'', he'', hge''⟩
    | some e =>
      if hKey : e.key == k then
        -- Key match: PCD for slots.set(idx%cap, {e with value := v})
        intro p hp e' hSlot' dd hdd
        simp only [insertLoop, hSlotCase, hKey, ite_true] at hSlot' ⊢
        simp only [Array.getElem_set] at hSlot' ⊢
        split at hSlot'
        · rename_i hpEq; subst hpEq; cases hSlot'; simp only []
          have ⟨e'', he'', hge''⟩ := hPCD _ hIdxCap e hSlotCase dd hdd
          if hChEq : (idealIndex e.key capacity hCapPos + dd) % capacity =
              idx % capacity then
            have h12 := getElem_idx_eq slots
              (by rw [hLen]; exact Nat.mod_lt _ hCapPos) hIdx hChEq
            rw [he'', hSlotCase] at h12
            split
            · exact ⟨{e with value := v}, rfl, by
                have : e'' = e := by injection h12
                rw [this] at hge''; exact hge''⟩
            · rename_i hNe; exact absurd hChEq.symm hNe
          else
            split
            · rename_i hEq; exact absurd hEq (Ne.symm hChEq)
            · exact ⟨e'', he'', hge''⟩
        · rename_i hpNe
          have ⟨e'', he'', hge''⟩ := hPCD p hp e' hSlot' dd hdd
          if hChEq : (idealIndex e'.key capacity hCapPos + dd) % capacity =
              idx % capacity then
            have h12 := getElem_idx_eq slots
              (by rw [hLen]; exact Nat.mod_lt _ hCapPos) hIdx hChEq
            rw [he'', hSlotCase] at h12
            split
            · exact ⟨{e with value := v}, rfl, by
                have : e'' = e := by injection h12
                rw [this] at hge''; exact hge''⟩
            · rename_i hNe; exact absurd hChEq.symm hNe
          else
            split
            · rename_i hEq; exact absurd hEq (Ne.symm hChEq)
            · exact ⟨e'', he'', hge''⟩
      else
        have hKeyF : (e.key == k) = false := by
          cases h : e.key == k
          · rfl
          · exfalso; exact hKey h
        if hRH : e.dist < d then
          -- Robin Hood swap: PCD for recursive call
          simp only [insertLoop, hSlotCase, hKeyF, if_pos hRH]
          have hLen' : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx).size
              = capacity := by rw [Array.size_set]; exact hLen
          have hKeyNeF : (e.key == k) = false := hKeyF
          have hKAbs := carried_key_absent slots capacity hLen hCapPos k d
            (idx % capacity) hIdxCap hD hDist hPCD hNotFound
            (.inr ⟨e, hSlotCase, hRH, hKeyNeF⟩)
          have hEdist := hDist _ hIdxCap e hSlotCase
          have hSmall : e.dist + 1 < capacity := by omega
          have hD' := dist_step_mod _ _ _ hCapPos hIdxCap
            (idealIndex_lt e.key capacity hCapPos) e.dist hEdist hSmall
          -- All intermediate invariants (same as in D1 proof)
          have hNoDup' : ∀ i j (hi : i < capacity) (hj : j < capacity)
              (ei ej : RHEntry α β),
              (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[i]'(by
                rw [hLen']; exact hi) = some ei →
              (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[j]'(by
                rw [hLen']; exact hj) = some ej →
              (ei.key == ej.key) = true → i = j := by
            intro i' j' hi' hj' ei' ej' hI' hJ' hKE'
            simp only [Array.getElem_set] at hI' hJ'
            split at hI' <;> split at hJ'
            · rename_i h1 h2; exact h1 ▸ h2 ▸ rfl
            · rename_i h1 hbN; cases hI'
              exact absurd (hKAbs j' hj' ej' hJ') (by
                have := eq_of_beq hKE'; simp [this.symm, beq_self_eq_true])
            · rename_i haN h2; cases hJ'
              exact absurd (hKAbs i' hi' ei' hI') (by
                have := eq_of_beq hKE'; simp [this, beq_self_eq_true])
            · exact hNoDup i' j' hi' hj' ei' ej' hI' hJ' hKE'
          have hDist' : ∀ j (hj : j < capacity) (e' : RHEntry α β),
              (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[j]'(by
                rw [hLen']; exact hj) = some e' →
              e'.dist = (j + capacity - idealIndex e'.key capacity hCapPos) %
                capacity := by
            intro j' hj' e' hSlot'
            simp only [Array.getElem_set] at hSlot'
            if h : idx % capacity = j' then
              subst h; simp at hSlot'; obtain rfl := hSlot'; exact hD
            else simp [h] at hSlot'; exact hDist j' hj' e' hSlot'
          have hPCD' : probeChainDominant
              (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx) capacity
              hLen' hCapPos := by
            intro p hp e' hSlot' dd hdd
            simp only [Array.getElem_set] at hSlot' ⊢
            split at hSlot'
            · rename_i hpEq; subst hpEq; cases hSlot'
              have hNe := hChainNe dd hdd
              split
              · rename_i hEq; exact absurd hEq.symm hNe
              · exact hChainOK dd hdd
            · rename_i hpNe
              obtain ⟨e'', he'', hge''⟩ := hPCD p hp e' hSlot' dd hdd
              if hChEq : (idealIndex e'.key capacity hCapPos + dd) % capacity =
                  idx % capacity then
                split
                · refine ⟨⟨k, v, d⟩, rfl, ?_⟩
                  have h12 := getElem_idx_eq slots
                    (by rw [hLen]; exact Nat.mod_lt _ hCapPos) hIdx hChEq
                  rw [he'', hSlotCase] at h12
                  have hEE : e'' = e := by injection h12
                  subst hEE
                  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hge'' hRH)
                · exact absurd hChEq.symm (by assumption)
              else
                split
                · exact absurd (by assumption) (Ne.symm hChEq)
                · exact ⟨e'', he'', hge''⟩
          have hNotFound' : ∀ d', d' < e.dist + 1 →
              ∀ e', (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[(idealIndex e.key capacity hCapPos + d') % capacity]'(by rw [hLen']; exact Nat.mod_lt _ hCapPos) = some e' →
              (e'.key == e.key) = false := by
            intro d' hd' e' hSlot'
            simp only [Array.getElem_set] at hSlot'
            split at hSlot'
            · cases hSlot'; show (k == e.key) = false
              cases h : k == e.key
              · rfl
              · exfalso; exact hKey (eq_of_beq h ▸ beq_self_eq_true e.key)
            · rename_i hNe
              show (e'.key == e.key) = false
              cases h : e'.key == e.key
              · rfl
              · exfalso
                exact absurd (hNoDup _ _ (Nat.mod_lt _ hCapPos) hIdxCap e' e
                  hSlot' hSlotCase h) (Ne.symm hNe)
          have hChainOK' : ∀ d', d' < e.dist + 1 →
              ∃ e', (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[(idealIndex e.key capacity hCapPos + d') % capacity]'(by rw [hLen']; exact Nat.mod_lt _ hCapPos) = some e' ∧
              e'.dist ≥ d' := by
            intro d' hd'
            have hEdist2 := hDist _ hIdxCap e hSlotCase
            have hRte : (idealIndex e.key capacity hCapPos + e.dist) % capacity =
                idx % capacity := by
              have := displacement_roundtrip (idx % capacity)
                (idealIndex e.key capacity hCapPos) capacity hCapPos
                (idealIndex_lt e.key capacity hCapPos) e.dist
                (by rw [Nat.mod_eq_of_lt hIdxCap]; exact hEdist2) (by omega)
              rwa [Nat.mod_eq_of_lt hIdxCap] at this
            simp only [Array.getElem_set]
            if hChAt : (idealIndex e.key capacity hCapPos + d') % capacity =
                idx % capacity then
              split
              · refine ⟨⟨k, v, d⟩, rfl, ?_⟩
                have hDE : d' = e.dist := offset_injective
                  (idealIndex e.key capacity hCapPos) capacity d' e.dist hCapPos
                  (by omega) (by omega) (hChAt.trans hRte.symm)
                exact Nat.le_of_lt (hDE ▸ hRH)
              · rename_i hNe; exact absurd hChAt.symm hNe
            else
              split
              · rename_i hEq; exact absurd hEq (Ne.symm hChAt)
              · have hd'_lt : d' < e.dist := by
                  rcases Nat.lt_or_ge d' e.dist with h | h
                  · exact h
                  · exfalso
                    have : d' = e.dist := Nat.le_antisymm (Nat.lt_succ_iff.mp hd') h
                    exact hChAt (this ▸ hRte)
                exact hPCD _ hIdxCap e hSlotCase d' hd'_lt
          exact ih (idx % capacity + 1) e.key e.value (e.dist + 1)
            (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx) hLen'
            hNoDup' hDist' hPCD' hD' (by omega) hChainOK' hNotFound'
        else
          -- Continue probing: PCD via IH
          have hGe : e.dist ≥ d := by omega
          match n, ih with
          | 0, _ =>
            simp only [insertLoop, hSlotCase, hKeyF, if_neg hRH, insertLoop]
            exact hPCD
          | n' + 1, ih =>
            simp only [insertLoop, hSlotCase, hKeyF, if_neg hRH]
            have hSmall : d + 1 < capacity := by omega
            have hD' := dist_step_mod _ _ _ hCapPos hIdxCap
              (idealIndex_lt k capacity hCapPos) d hD hSmall
            have hChainOK' : ∀ d', d' < d + 1 →
                ∃ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
                  rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' ∧
                e'.dist ≥ d' := by
              intro d' hd'
              if hLt : d' < d then exact hChainOK d' hLt
              else
                have hEq : d' = d := by omega
                subst hEq
                refine ⟨e, ?_, hGe⟩
                exact (getElem_idx_eq slots (by rw [hLen]; exact Nat.mod_lt _ hCapPos)
                  hIdx hRtD).symm ▸ hSlotCase
            have hNotFound' : ∀ d', d' < d + 1 →
                ∀ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
                  rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' →
                (e'.key == k) = false := by
              intro d' hd' e' hSlot'
              if hLt : d' < d then exact hNotFound d' hLt e' hSlot'
              else
                have hEq : d' = d := by omega
                subst hEq
                have := getElem_idx_eq slots
                  (by rw [hLen]; exact Nat.mod_lt _ hCapPos)
                  (by rw [hLen]; exact hIdxCap) hRtD
                rw [this] at hSlot'
                rw [hSlotCase] at hSlot'; cases hSlot'; exact hKeyF
            exact ih (idx % capacity + 1) k v (d + 1) slots hLen
              hNoDup hDist hPCD hD' (by omega) hChainOK' hNotFound'

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
  exact insertLoop_preserves_noDupKeys t.capacity (idealIndex k t.capacity t.hCapPos)
    k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos hExt.2.2.1 hExt.2.1
    hExt.2.2.2 (by simp [Nat.mod_eq_of_lt (idealIndex_lt k t.capacity t.hCapPos)])
    (by omega) (by intro d' hd'; omega) (by intro d' hd'; omega)

-- Note: `insertNoResize_preserves_robinHoodOrdered` is provable for insert
-- (unlike erase) but is not required for the operational invariant bundle
-- `invExt`. It is retained as a structural property available for future use
-- in a subsequent workstream phase.

/-- `insertNoResize` preserves probeChainDominant.
    Follows the same induction structure as `insertLoop_preserves_noDupKeys`.
    Each case proves PCD for the result array. -/
theorem RHTable.insertNoResize_preserves_probeChainDominant [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insertNoResize k v).probeChainDominant := by
  -- PCD preservation follows from noDupKeys preservation + structural argument:
  -- the noDupKeys loop lemma maintains PCD as a PRECONDITION through the
  -- induction (hPCD' is proven at each swap step). The result PCD follows
  -- because the loop lemma's IH establishes PCD for recursive calls, and
  -- base cases (empty/match) have explicit PCD proofs.
  exact insertLoop_preserves_pcd t.capacity (idealIndex k t.capacity t.hCapPos)
    k v 0 t.slots t.capacity t.hSlotsLen t.hCapPos hExt.2.2.1 hExt.2.1
    hExt.2.2.2 (by simp [Nat.mod_eq_of_lt (idealIndex_lt k t.capacity t.hCapPos)])
    (by omega) (by intro d' hd'; omega) (by intro d' hd'; omega)

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

/-- Relaxed PCD: like probeChainDominant but excuses one gap position. -/
private def relaxedPCD [Hashable α]
    (gap : Nat) (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity) : Prop :=
  ∀ (p : Nat) (hp : p < capacity) (e : RHEntry α β),
    slots[p]'(by rw [hLen]; exact hp) = some e →
    ∀ (d : Nat), d < e.dist →
      (idealIndex e.key capacity hCapPos + d) % capacity = gap ∨
      ∃ e', slots[(idealIndex e.key capacity hCapPos + d) % capacity]'(by
        rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' ∧ e'.dist ≥ d

/-- When the gap and its next slot are both "inactive" (next is none or dist=0),
    relaxedPCD collapses to full PCD. The gap excuse is vacuous because any chain
    passing through the gap would need a witness at the next slot too, but the next
    slot either doesn't exist or has dist=0 which can't provide a sufficient witness. -/
private theorem relaxedPCD_to_pcd_at_termination [Hashable α]
    (gap : Nat) (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hGapNone : slots[gap % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none)
    (hGapLt : gap % capacity < capacity)
    (hNextInactive : slots[(gap + 1) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none ∨
      ∃ ne, slots[(gap + 1) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = some ne ∧
        ne.dist = 0)
    (hDist : ∀ (j : Nat) (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity)
    (hRelaxed : relaxedPCD (gap % capacity) slots capacity hLen hCapPos) :
    probeChainDominant slots capacity hLen hCapPos := by
  intro p hp e hSlot d hd
  have hR := hRelaxed p hp e hSlot d hd
  cases hR with
  | inr h => exact h
  | inl hWitGap =>
    -- The witness position = gap%cap. Show this is impossible.
    exfalso
    -- Entry at p has ideal h, dist = (p + cap - h) % cap, and d < dist.
    -- Witness position (h + d) % cap = gap % cap.
    -- If d + 1 < e.dist, consider d+1: by relaxedPCD, (h + d + 1) % cap = gap%cap
    -- or witness exists at (h+d+1)%cap = (gap+1)%cap.
    -- (h+d+1)%cap = (gap+1)%cap (since (h+d)%cap = gap%cap, adding 1 mod cap).
    -- But (gap+1)%cap either has none or dist=0, and the gap excuse requires
    -- (gap+1)%cap = gap%cap which is false for cap > 1.
    have hGapM : gap % capacity = (idealIndex e.key capacity hCapPos + d) % capacity := hWitGap.symm
    -- Case: is d + 1 < e.dist?
    by_cases hd1 : d + 1 < e.dist
    · -- Consider chain witness at d+1
      have hR2 := hRelaxed p hp e hSlot (d + 1) hd1
      -- (idealIndex e.key cap hCapPos + (d+1)) % cap = (gap + 1) % cap
      have hWitNext : (idealIndex e.key capacity hCapPos + (d + 1)) % capacity =
          (gap + 1) % capacity := by
        rw [show idealIndex e.key capacity hCapPos + (d + 1) =
            (idealIndex e.key capacity hCapPos + d) + 1 from by omega]
        have hME : (idealIndex e.key capacity hCapPos + d) % capacity =
            gap % capacity := hGapM.symm
        calc ((idealIndex e.key capacity hCapPos + d) + 1) % capacity
            = ((idealIndex e.key capacity hCapPos + d) % capacity +
                1 % capacity) % capacity := Nat.add_mod _ 1 _
          _ = (gap % capacity + 1 % capacity) % capacity := by rw [hME]
          _ = (gap + 1) % capacity := (Nat.add_mod gap 1 capacity).symm
      rcases hR2 with hGap2 | ⟨e', he', hge'⟩
      · -- (h+d+1)%cap = gap%cap but should be (gap+1)%cap
        rw [hWitNext] at hGap2
        by_cases hCap1 : capacity = 1
        · subst hCap1; have := hDist p hp e hSlot; simp [Nat.mod_one] at this; omega
        · by_cases hw : gap % capacity + 1 < capacity
          · have : (gap + 1) % capacity = gap % capacity + 1 := by
              rw [show gap + 1 = gap % capacity + 1 + capacity * (gap / capacity) from by
                have := Nat.div_add_mod gap capacity; omega,
                Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]
            omega
          · have hEqM : gap % capacity = capacity - 1 := by
              have := Nat.mod_lt gap hCapPos; omega
            have : (gap + 1) % capacity = 0 := by
              rw [show gap + 1 = gap % capacity + 1 + capacity * (gap / capacity) from by
                have := Nat.div_add_mod gap capacity; omega,
                hEqM, show capacity - 1 + 1 = capacity from by omega,
                Nat.add_mul_mod_self_left, Nat.mod_self]
            omega
      · -- Witness at (gap+1)%cap with dist >= d+1
        have he'2 : slots[(gap + 1) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos)
            = some e' := by
          have : (idealIndex e.key capacity hCapPos + (d + 1)) % capacity =
              (gap + 1) % capacity := hWitNext
          simp only [this] at he'; exact he'
        rcases hNextInactive with hNone | ⟨ne, hne, hne0⟩
        · rw [hNone] at he'2; exact absurd he'2 (by simp)
        · rw [hne] at he'2; have := Option.some.inj he'2; subst this; omega
    · -- d + 1 >= e.dist, so d = e.dist - 1 (since d < e.dist)
      have hd_eq : d = e.dist - 1 := by omega
      -- Entry at p: (h + dist) % cap = p (by distCorrect roundtrip)
      -- (h + d) % cap = gap % cap, d = dist - 1
      -- So (h + dist) % cap = (gap + 1) % cap, meaning p = (gap + 1) % cap
      have hEDist := hDist p hp e hSlot
      have hPEq : p = (idealIndex e.key capacity hCapPos + e.dist) % capacity := by
        have hpMod : p % capacity = p := Nat.mod_eq_of_lt hp
        have hEDist' : e.dist = (p % capacity + capacity -
            idealIndex e.key capacity hCapPos) % capacity := by
          rw [hpMod]; exact hEDist
        have hdr := displacement_roundtrip p (idealIndex e.key capacity hCapPos) capacity
          hCapPos (idealIndex_lt e.key capacity hCapPos) e.dist hEDist'
          (by rw [hEDist']; exact Nat.mod_lt _ hCapPos)
        rw [hpMod] at hdr; exact hdr.symm
      have hStep : (idealIndex e.key capacity hCapPos + e.dist) % capacity =
          (gap + 1) % capacity := by
        rw [show idealIndex e.key capacity hCapPos + e.dist =
            (idealIndex e.key capacity hCapPos + d) + 1 from by omega]
        have hME : (idealIndex e.key capacity hCapPos + d) % capacity =
            gap % capacity := hGapM.symm
        calc ((idealIndex e.key capacity hCapPos + d) + 1) % capacity
            = ((idealIndex e.key capacity hCapPos + d) % capacity +
                1 % capacity) % capacity := Nat.add_mod _ 1 _
          _ = (gap % capacity + 1 % capacity) % capacity := by rw [hME]
          _ = (gap + 1) % capacity := (Nat.add_mod gap 1 capacity).symm
      -- p = (gap+1) % cap, so slots[(gap+1)%cap] = some e
      have hSlot2 : slots[(gap + 1) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos)
          = some e := by
        have : p = (gap + 1) % capacity := by rw [hPEq, hStep]
        simp only [this] at hSlot; exact hSlot
      rcases hNextInactive with hNone | ⟨ne, hne, hne0⟩
      · rw [hNone] at hSlot2; exact absurd hSlot2 (by simp)
      · rw [hne] at hSlot2
        have := Option.some.inj hSlot2; subst this; omega

/-- Clearing a slot in a PCD table yields relaxedPCD at the cleared position. -/
private theorem pcd_to_relaxedPCD_after_clear [Hashable α]
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (idx : Nat) (hIdx : idx < slots.size)
    (hPCD : probeChainDominant slots capacity hLen hCapPos) :
    relaxedPCD (idx) (slots.set idx none hIdx) capacity
      (by rw [Array.size_set]; exact hLen) hCapPos := by
  intro p hp e hSlot d hd
  simp only [Array.getElem_set] at hSlot
  split at hSlot
  · simp at hSlot
  · rename_i hpNe
    have hOrig : slots[p]'(by rw [hLen]; exact hp) = some e := hSlot
    have hW := hPCD p hp e hOrig d hd
    obtain ⟨e', he', hge'⟩ := hW
    let w := (idealIndex e.key capacity hCapPos + d) % capacity
    by_cases hWIdx : w = idx
    · left; exact hWIdx
    · right
      refine ⟨e', ?_, hge'⟩
      simp only [Array.getElem_set]
      split
      · rename_i hEq; exact absurd hEq hWIdx
      · exact he'

/-- One backshift step transforms relaxedPCD(gap%cap) to relaxedPCD((gap+1)%cap). -/
private theorem backshiftStep_relaxedPCD [Hashable α]
    (gap : Nat) (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (nextE : RHEntry α β)
    (hGapNone : slots[gap % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none)
    (hNextSome : slots[(gap + 1) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = some nextE)
    (hNextDist : 0 < nextE.dist)
    (hDist : ∀ (j : Nat) (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity)
    (hNe : gap % capacity ≠ (gap + 1) % capacity)
    (hRelaxed : relaxedPCD (gap % capacity) slots capacity hLen hCapPos) :
    let hGapI := by rw [hLen]; exact Nat.mod_lt gap hCapPos
    let hNextI := by rw [hLen]; exact Nat.mod_lt (gap + 1) hCapPos
    let slots' := (slots.set (gap % capacity) (some { nextE with dist := nextE.dist - 1 })
      hGapI).set ((gap + 1) % capacity) none (by rw [Array.size_set]; exact hNextI)
    relaxedPCD ((gap + 1) % capacity) slots' capacity
      (by rw [Array.size_set, Array.size_set]; exact hLen) hCapPos := by
  intro p hp e hSlot d hd
  have hGapI : gap % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
  have hNextI : (gap + 1) % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
  simp only [Array.getElem_set] at hSlot
  split at hSlot
  · simp at hSlot
  · rename_i hpNeNext
    split at hSlot
    · rename_i hpGap
      -- p = gap%cap: entry is { nextE with dist := nextE.dist - 1 }
      have hEDef : e = { nextE with dist := nextE.dist - 1 } := by cases hSlot; rfl
      let w := (idealIndex e.key capacity hCapPos + d) % capacity
      by_cases hwNext : w = (gap + 1) % capacity
      · left; exact hwNext
      · by_cases hwGap : w = gap % capacity
        · right
          refine ⟨e, ?_, ?_⟩
          · simp only [Array.getElem_set]; split
            · simp at hwNext
            · split; · exact hSlot; · exact absurd hwGap (by assumption)
          · rw [hEDef]; simp; omega
        · right
          have hd' : d < nextE.dist := by rw [hEDef] at hd; simp at hd; omega
          have hR := hRelaxed ((gap + 1) % capacity) (Nat.mod_lt _ hCapPos)
            nextE hNextSome d hd'
          rcases hR with hExc | ⟨e', he', hge'⟩
          · rw [hEDef] at *; simp at *; exact absurd hExc hwGap
          · refine ⟨e', ?_, hge'⟩
            simp only [Array.getElem_set]
            split
            · exact absurd (by assumption) hwNext
            · split
              · rename_i hq; exact absurd hq hwGap
              · exact he'
    · rename_i hpNeGap
      -- p is neither gap nor gap+1: entry from original slots
      have hOrig : slots[p]'(by rw [hLen]; exact hp) = some e := hSlot
      let w := (idealIndex e.key capacity hCapPos + d) % capacity
      by_cases hwNext : w = (gap + 1) % capacity
      · left; exact hwNext
      · by_cases hwGap : w = gap % capacity
        · right
          by_cases hd1 : d + 1 < e.dist
          · have hR2 := hRelaxed p hp e hOrig (d + 1) hd1
            have hWitNext : (idealIndex e.key capacity hCapPos + (d + 1)) % capacity =
                (gap + 1) % capacity := by
              rw [show idealIndex e.key capacity hCapPos + (d + 1) =
                  (idealIndex e.key capacity hCapPos + d) + 1 from by omega]
              calc ((idealIndex e.key capacity hCapPos + d) + 1) % capacity
                  = ((idealIndex e.key capacity hCapPos + d) % capacity +
                      1 % capacity) % capacity := Nat.add_mod _ 1 _
                _ = (gap % capacity + 1 % capacity) % capacity := by rw [hwGap]
                _ = (gap + 1) % capacity := (Nat.add_mod gap 1 capacity).symm
            rcases hR2 with hExc2 | ⟨e2, he2, hge2⟩
            · rw [hWitNext] at hExc2; exact absurd hExc2 hNe
            · have he2Eq : e2 = nextE := by
                rw [hWitNext] at he2; exact Option.some.inj he2
              rw [he2Eq] at hge2
              refine ⟨{ nextE with dist := nextE.dist - 1 }, ?_, by simp; omega⟩
              simp only [Array.getElem_set]
              split
              · exact absurd hwGap (by omega)
              · split; · rfl; · exact absurd (by assumption) hpNeGap
          · exfalso
            have hdeq : d = e.dist - 1 := by omega
            have hEDist := hDist p hp e hOrig
            have hPEq : p = (idealIndex e.key capacity hCapPos + e.dist) % capacity := by
              have hpMod : p % capacity = p := Nat.mod_eq_of_lt hp
              have hEDist' : e.dist = (p % capacity + capacity -
                  idealIndex e.key capacity hCapPos) % capacity := by
                rw [hpMod]; exact hEDist
              have hdr := displacement_roundtrip p (idealIndex e.key capacity hCapPos) capacity
                hCapPos (idealIndex_lt e.key capacity hCapPos) e.dist hEDist'
                (by rw [hEDist']; exact Nat.mod_lt _ hCapPos)
              rw [hpMod] at hdr; exact hdr.symm
            have hStep : (idealIndex e.key capacity hCapPos + e.dist) % capacity =
                (gap + 1) % capacity := by
              rw [show idealIndex e.key capacity hCapPos + e.dist =
                  (idealIndex e.key capacity hCapPos + d) + 1 from by omega]
              calc ((idealIndex e.key capacity hCapPos + d) + 1) % capacity
                  = ((idealIndex e.key capacity hCapPos + d) % capacity +
                      1 % capacity) % capacity := Nat.add_mod _ 1 _
                _ = (gap % capacity + 1 % capacity) % capacity := by rw [hwGap]
                _ = (gap + 1) % capacity := (Nat.add_mod gap 1 capacity).symm
            rw [hPEq, hStep] at hpNeNext
            exact hpNeNext rfl
        · right
          have hR := hRelaxed p hp e hOrig d hd
          rcases hR with hExc | ⟨e', he', hge'⟩
          · exact absurd hExc hwGap
          · refine ⟨e', ?_, hge'⟩
            simp only [Array.getElem_set]
            split
            · exact absurd (by assumption) hwNext
            · split
              · rename_i hq; exact absurd hq hwGap
              · exact he'

-- ============================================================================
-- Section 11c: backshiftLoop PCD preservation
-- ============================================================================

-- Note: `erase_preserves_robinHoodOrdered` is NOT provable.
-- The standard backshift-on-erase algorithm does NOT preserve non-decreasing
-- dist within clusters (counterexample: consecutive entries with equal dist,
-- erasing a middle entry shifts the next entry backward, breaking ordering).
-- This is a well-known property of Robin Hood erase: `robinHoodOrdered` is
-- preserved by insert/resize but NOT by erase. The `probeChainDominant`
-- property (which IS preserved) suffices for lookup correctness.

/-- Modular arithmetic identity: `(a % n + b) % n = (a + b) % n`. -/
private theorem mod_add_mod (a b n : Nat) (hn : 0 < n) :
    (a % n + b) % n = (a + b) % n := by
  conv_rhs => rw [show a = a % n + n * (a / n) from by omega]
  rw [Nat.add_assoc, Nat.add_comm (n * (a / n)) b, ← Nat.add_assoc,
      Nat.add_mul_mod_self_left]

/-- backshiftLoop preserves PCD given relaxedPCD + distCorrect + natural termination.
    The `hTerminate` hypothesis states there exists a position within `fuel` steps
    that terminates the loop (none or dist=0). This is guaranteed by `size < capacity`
    at the call site. -/
private theorem backshiftLoop_preserves_pcd [Hashable α]
    (fuel : Nat) (gapIdx : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hGapNone : slots[gapIdx % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none)
    (hDist : ∀ (j : Nat) (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity)
    (hRelaxed : relaxedPCD (gapIdx % capacity) slots capacity hLen hCapPos)
    (hTerminate : ∃ j, j < fuel ∧
      (gapIdx + 1 + j) % capacity ≠ gapIdx % capacity ∧
      (slots[(gapIdx + 1 + j) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none ∨
       ∃ ne, slots[(gapIdx + 1 + j) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = some ne ∧ ne.dist = 0)) :
    probeChainDominant (backshiftLoop fuel gapIdx slots capacity hLen hCapPos)
      capacity (by rw [backshiftLoop_preserves_len]; exact hLen) hCapPos := by
  induction fuel generalizing gapIdx slots hLen with
  | zero =>
    obtain ⟨j, hj, _⟩ := hTerminate; omega
  | succ n ih =>
    have hGapI : gapIdx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hNextI : (gapIdx + 1) % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    match hSlot : slots[(gapIdx + 1) % capacity]'hNextI with
    | none =>
      simp [backshiftLoop, hSlot]
      exact relaxedPCD_to_pcd_at_termination gapIdx slots capacity hLen hCapPos
        hGapNone (Nat.mod_lt _ hCapPos) (Or.inl hSlot) hDist hRelaxed
    | some nextE =>
      if hDistEq : nextE.dist == 0 then
        simp [backshiftLoop, hSlot, hDistEq]
        have hD0 : nextE.dist = 0 := by cases h : nextE.dist == 0 <;> simp_all
        exact relaxedPCD_to_pcd_at_termination gapIdx slots capacity hLen hCapPos
          hGapNone (Nat.mod_lt _ hCapPos) (Or.inr ⟨nextE, hSlot, hD0⟩) hDist hRelaxed
      else
        have hNextDist : 0 < nextE.dist := by
          cases h : nextE.dist with
          | zero => simp [h] at hDistEq
          | succ n => omega
        have hDistF : (nextE.dist == 0) = false := by
          cases h : nextE.dist == 0 <;> simp_all
        have hNe : gapIdx % capacity ≠ (gapIdx + 1) % capacity := by
          intro hEq
          have hSame : slots[gapIdx % capacity]'hGapI =
              slots[(gapIdx + 1) % capacity]'hNextI := by congr 1
          rw [hGapNone, hSlot] at hSame; injection hSame
        simp only [backshiftLoop, hSlot, hDistF, ↓reduceIte]
        simp only [show (false = true) ↔ False from ⟨Bool.noConfusion, False.elim⟩, ite_false]
        -- Build intermediate array
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
          simp [Array.getElem_set, Nat.mod_eq_of_lt (Nat.mod_lt _ hCapPos)]
        -- relaxedPCD step
        have hRelaxed2 := backshiftStep_relaxedPCD gapIdx slots capacity hLen hCapPos
          nextE hGapNone hSlot hNextDist hDist hNe hRelaxed
        -- distCorrect for intermediate array
        have hDist2 : ∀ (p : Nat) (hp : p < capacity) (e' : RHEntry α β),
            ((slots.set (gapIdx % capacity)
              (some { nextE with dist := nextE.dist - 1 }) hGapI).set
              ((gapIdx + 1) % capacity) none
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
              have hE' : e' = { nextE with dist := nextE.dist - 1 } := by cases hSlot'; rfl
              rw [hE']; simp only []
              exact displacement_backward gapIdx capacity hCapPos nextE.key nextE.dist
                (hDist _ (Nat.mod_lt _ hCapPos) _ hSlot) hNextDist ▸ (by rw [← hpGap])
            · exact hDist p hp e' hSlot'
        -- Termination witness for recursive call
        obtain ⟨j, hjFuel, hjNeGap, hjTerm⟩ := hTerminate
        have hj0 : j ≠ 0 := by
          intro hj0; subst hj0; simp at hjTerm
          rcases hjTerm with hNone | ⟨ne, hne, hne0⟩
          · rw [hSlot] at hNone; exact absurd hNone (by simp)
          · rw [hSlot] at hne; have := Option.some.inj hne; subst this
            simp at hne0; exact absurd hne0 (by omega)
        -- Position identity: ((gapIdx+1)%cap + 1 + (j-1)) % cap = (gapIdx + 1 + j) % cap
        have hPosEq : ((gapIdx + 1) % capacity + 1 + (j - 1)) % capacity =
            (gapIdx + 1 + j) % capacity := by
          rw [mod_add_mod (gapIdx + 1) (1 + (j - 1)) capacity hCapPos]
          congr 1; omega
        -- The position is not (gapIdx+1)%cap (the new gap after modding)
        have hjNeNext : (gapIdx + 1 + j) % capacity ≠ (gapIdx + 1) % capacity := by
          intro hEq
          -- (gapIdx + 1 + j) % cap = (gapIdx + 1) % cap implies j % cap = 0
          -- j ≥ 1 and j < n+1 ≤ capacity, so j cannot be 0 or capacity
          have : (gapIdx + 1 + j) % capacity = (gapIdx + 1 + 0) % capacity := by
            simp; exact hEq
          have : j % capacity = 0 := by
            have hM := Nat.add_mod (gapIdx + 1) j capacity
            have hM0 := Nat.add_mod (gapIdx + 1) 0 capacity
            simp at hM0; rw [hEq] at hM
            have := hM.symm.trans hM0
            omega
          have : j = 0 ∨ j = capacity := by
            have hjlt : j < capacity := by omega
            have := Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero this) hjlt
            left; exact this
          rcases this with rfl | rfl
          · exact hj0 rfl
          · omega
        -- The position is not gapIdx%cap (preserved from hypothesis)
        -- Slot at this position in slots' = slot in original slots
        -- (because it's neither gapIdx%cap nor (gapIdx+1)%cap)
        have hSlotPreserved :
            ((slots.set (gapIdx % capacity)
              (some { nextE with dist := nextE.dist - 1 }) hGapI).set
              ((gapIdx + 1) % capacity) none
              (by rw [Array.size_set]; exact hNextI))[(gapIdx + 1 + j) % capacity]'(by
                rw [Array.size_set, Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos) =
            slots[(gapIdx + 1 + j) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) := by
          simp only [Array.getElem_set]
          split
          · exact absurd (by assumption) hjNeNext
          · split
            · exact absurd (by assumption) hjNeGap
            · rfl
        have hTerminate2 : ∃ j', j' < n ∧
            ((gapIdx + 1) % capacity + 1 + j') % capacity ≠ (gapIdx + 1) % capacity ∧
            (((slots.set (gapIdx % capacity)
                (some { nextE with dist := nextE.dist - 1 }) hGapI).set
                ((gapIdx + 1) % capacity) none
                (by rw [Array.size_set]; exact hNextI))[((gapIdx + 1) % capacity + 1 + j') % capacity]'(by
                  rw [hLen2]; exact Nat.mod_lt _ hCapPos) = none ∨
             ∃ ne, ((slots.set (gapIdx % capacity)
                (some { nextE with dist := nextE.dist - 1 }) hGapI).set
                ((gapIdx + 1) % capacity) none
                (by rw [Array.size_set]; exact hNextI))[((gapIdx + 1) % capacity + 1 + j') % capacity]'(by
                  rw [hLen2]; exact Nat.mod_lt _ hCapPos) = some ne ∧ ne.dist = 0)) := by
          refine ⟨j - 1, by omega, ?_, ?_⟩
          · rw [hPosEq]; exact hjNeNext
          · rw [hPosEq, hSlotPreserved]; exact hjTerm
        exact ih ((gapIdx + 1) % capacity) _ hLen2 hNewGap hDist2 hRelaxed2 hTerminate2

/-- If countP isSome on a list is less than length, there exists an index with value
    that is not isSome (i.e., none). -/
private theorem List.exists_none_of_countP_lt {l : List (Option γ)}
    (h : l.countP (·.isSome) < l.length) :
    ∃ i (hi : i < l.length), l[i] = none := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    cases hd with
    | none => exact ⟨0, by simp, rfl⟩
    | some v =>
      simp only [List.countP_cons, Option.isSome, List.length_cons,
        decide_true, ite_true] at h
      have htl := ih (by omega)
      obtain ⟨i, hi, hv⟩ := htl
      exact ⟨i + 1, by omega, by simpa [List.getElem_cons_succ]⟩

/-- If countOccupied < size, there exists a none slot. -/
private theorem exists_none_of_countOccupied_lt
    (slots : Array (Option (RHEntry α β)))
    (h : countOccupied slots < slots.size) :
    ∃ i (hi : i < slots.size), slots[i]'hi = none := by
  unfold countOccupied at h
  have hList := List.exists_none_of_countP_lt (l := slots.toList) (by simp [Array.size] at h ⊢; exact h)
  obtain ⟨i, hi, hv⟩ := hList
  refine ⟨i, by simp [Array.size]; exact hi, ?_⟩
  simp [Array.getElem_eq_toList_getElem]; exact hv

/-- `erase` preserves probeChainDominant when the table is not full. -/
theorem RHTable.erase_preserves_probeChainDominant [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) (hSize : t.size < t.capacity) :
    (t.erase k).probeChainDominant := by
  simp only [RHTable.erase]
  split
  · exact hExt.2.2.2  -- key not found, table unchanged
  · -- key found at idx
    rename_i idx hFound
    have hIdxLt := findLoop_lt t.capacity _ k 0 t.slots t.capacity t.hSlotsLen t.hCapPos idx hFound
    have ⟨foundE, hFoundSlot, _⟩ := findLoop_correct t.capacity _ k 0 t.slots t.capacity
      t.hSlotsLen t.hCapPos idx hFound
    -- idx < capacity, so idx % capacity = idx
    have hIdxMod : idx % t.capacity = idx := Nat.mod_eq_of_lt hIdxLt
    have hIdxS : idx % t.capacity < t.slots.size := by
      rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
    have hLen' : (t.slots.set (idx % t.capacity) none hIdxS).size = t.capacity := by
      rw [Array.size_set]; exact t.hSlotsLen
    -- Gap is none in cleared array
    have hGap : (t.slots.set (idx % t.capacity) none hIdxS)[idx % t.capacity]'(by
        rw [hLen']; exact Nat.mod_lt _ t.hCapPos) = none := by
      simp [Array.getElem_set]
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
    -- relaxedPCD for cleared array (from pcd_to_relaxedPCD_after_clear)
    have hRelaxed : relaxedPCD (idx % t.capacity) (t.slots.set (idx % t.capacity) none hIdxS)
        t.capacity hLen' t.hCapPos :=
      pcd_to_relaxedPCD_after_clear t.slots t.capacity t.hSlotsLen t.hCapPos
        (idx % t.capacity) hIdxS hExt.2.2.2
    -- Termination witness: find a none entry in original slots at q ≠ idx
    -- size < capacity and size = countOccupied, so countOccupied < capacity
    have hOccLt : countOccupied t.slots < t.capacity := by
      rw [← hExt.1.sizeCount]; exact hSize
    -- Original slots have a none entry
    have ⟨q, hq, hqNone⟩ := exists_none_of_countOccupied_lt t.slots (by rw [t.hSlotsLen]; exact hOccLt)
    have hqCap : q < t.capacity := by rw [← t.hSlotsLen]; exact hq
    -- q ≠ idx because slots[idx] = some foundE
    have hqNeIdx : q ≠ idx := by
      intro heq; subst heq; rw [hIdxMod] at hFoundSlot; rw [hqNone] at hFoundSlot; simp at hFoundSlot
    -- q ≠ idx % capacity
    have hqNeIdxMod : q ≠ idx % t.capacity := by rw [hIdxMod]; exact hqNeIdx
    -- q is still none in the cleared array
    have hqNoneClear : (t.slots.set (idx % t.capacity) none hIdxS)[q]'(by
        rw [hLen']; exact hqCap) = none := by
      simp only [Array.getElem_set]
      split
      · rfl
      · exact hqNone
    -- Express q as (idx + 1 + j) % capacity for some j
    -- j = (q + capacity - (idx + 1) % capacity) % capacity
    let j := (q + t.capacity - (idx + 1) % t.capacity) % t.capacity
    have hjLt : j < t.capacity := Nat.mod_lt _ t.hCapPos
    have hjPos : (idx + 1 + j) % t.capacity = q := by
      simp only [j]
      rw [mod_add_mod (idx + 1) ((q + t.capacity - (idx + 1) % t.capacity) % t.capacity) t.capacity t.hCapPos]
      rw [show idx + 1 + (q + t.capacity - (idx + 1) % t.capacity) % t.capacity =
          idx + 1 + (q + t.capacity - (idx + 1) % t.capacity) % t.capacity from rfl]
      rw [mod_add_mod (idx + 1) (q + t.capacity - (idx + 1) % t.capacity) t.capacity t.hCapPos]
      have hMod := Nat.mod_lt (idx + 1) t.hCapPos
      rw [show idx + 1 + (q + t.capacity - (idx + 1) % t.capacity) =
          q + t.capacity + (idx + 1 - (idx + 1) % t.capacity) from by omega]
      rw [show idx + 1 - (idx + 1) % t.capacity = t.capacity * ((idx + 1) / t.capacity) from by
        have := Nat.div_add_mod (idx + 1) t.capacity; omega]
      rw [Nat.add_assoc, Nat.add_mul_mod_self_left]
      rw [show q + t.capacity = q + 1 * t.capacity from by omega, Nat.add_mul_mod_self]
      exact Nat.mod_eq_of_lt hqCap
    -- (idx + 1 + j) % cap = q ≠ idx % cap
    have hjNeGap : (idx + 1 + j) % t.capacity ≠ idx % t.capacity := by
      rw [hjPos]; exact hqNeIdxMod
    -- Termination condition
    have hTerminate : ∃ j', j' < t.capacity ∧
        (idx + 1 + j') % t.capacity ≠ idx % t.capacity ∧
        ((t.slots.set (idx % t.capacity) none hIdxS)[(idx + 1 + j') % t.capacity]'(by
          rw [hLen']; exact Nat.mod_lt _ t.hCapPos) = none ∨
         ∃ ne, (t.slots.set (idx % t.capacity) none hIdxS)[(idx + 1 + j') % t.capacity]'(by
          rw [hLen']; exact Nat.mod_lt _ t.hCapPos) = some ne ∧ ne.dist = 0) := by
      refine ⟨j, hjLt, hjNeGap, Or.inl ?_⟩
      rw [hjPos]; exact hqNoneClear
    exact backshiftLoop_preserves_pcd t.capacity idx _ t.capacity hLen' t.hCapPos
      hGap hDist' hRelaxed hTerminate

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

/-- `erase` preserves the extended invariant (the operational invariant).
    Requires `t.size < t.capacity` because probeChainDominant preservation
    needs natural loop termination (not fuel exhaustion). This holds for all
    reachable states: `insert` resizes at 75% load. -/
theorem RHTable.erase_preserves_invExt [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) (hSize : t.size < t.capacity) :
    (t.erase k).invExt :=
  ⟨t.erase_preserves_wf k hExt.1,
   t.erase_preserves_distCorrect k hExt,
   t.erase_preserves_noDupKeys k hExt,
   t.erase_preserves_probeChainDominant k hExt hSize⟩

/-- `resize` preserves the extended invariant. -/
theorem RHTable.resize_preserves_invariant [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) :
    (t.resize).invExt :=
  ⟨t.resize_preserves_wf,
   t.resize_preserves_distCorrect,
   t.resize_preserves_noDupKeys,
   t.resize_preserves_probeChainDominant⟩

end SeLe4n.Kernel.RobinHood
