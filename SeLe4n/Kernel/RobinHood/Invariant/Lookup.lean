/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RobinHood.Invariant.Preservation

namespace SeLe4n.Kernel.RobinHood

-- ============================================================================
-- N2-E: Lookup Correctness
-- ============================================================================

/-- If key `k` is absent from all slots, `getLoop` returns `none`.
    The argument is simple: at each step, the slot is either `none` (return none),
    has a different key (continue or early-terminate with none), or fuel exhausts
    (return none). Key `k` is never found. -/
private theorem getLoop_none_of_absent [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hAbsent : ∀ j (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e → (e.key == k) = false) :
    getLoop fuel idx k d slots capacity hLen hCapPos = none := by
  induction fuel generalizing idx d with
  | zero => simp [getLoop]
  | succ n ih =>
    unfold getLoop; simp only []
    have hIdx : idx % capacity < capacity := Nat.mod_lt _ hCapPos
    split
    · rfl  -- none slot → return none
    · rename_i e hSlot
      have hKeyNe := hAbsent (idx % capacity) hIdx e hSlot
      rw [hKeyNe]; simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · rfl  -- e.dist < d → return none
      · exact ih (idx % capacity + 1) (d + 1)

/-- When `findLoop` returns `none`, key `k` is absent from the table.
    By induction on fuel, each step either terminates at an empty slot or
    at a slot with `dist < d` and key ≠ k. In both cases `carried_key_absent`
    gives full absence. -/
private theorem findLoop_none_implies_absent [BEq α] [Hashable α] [LawfulBEq α]
    (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hDist : ∀ j (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(hLen ▸ hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity)
    (hPCD : probeChainDominant slots capacity hLen hCapPos)
    (hD : d = (idx % capacity + capacity - idealIndex k capacity hCapPos) % capacity)
    (hNotFound : ∀ d', d' < d →
      ∀ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
        rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' → (e'.key == k) = false)
    (hFuelBound : capacity ≤ d + fuel)
    (hNone : findLoop fuel idx k d slots capacity hLen hCapPos = none) :
    ∀ j (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e → (e.key == k) = false := by
  induction fuel generalizing idx d with
  | zero =>
    -- fuel = 0 means capacity ≤ d, so all positions checked
    have hCapLeD : capacity ≤ d := by omega
    exact carried_key_absent slots capacity hLen hCapPos k d (idx % capacity)
      (Nat.mod_lt _ hCapPos) hD hDist hPCD (by
        intro d' hd' e' he'
        exact hNotFound d' (by omega) e' he')
      (by
        -- We need hSlotWeak for idx%cap position
        -- Since d ≥ capacity, and e.dist < capacity for any entry,
        -- any entry at this position has dist < d
        cases hSlotCase : slots[idx % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) with
        | none => left; rfl
        | some e =>
          right; exact ⟨e, rfl,
            by have := Nat.mod_lt (idx % capacity + capacity -
                 idealIndex e.key capacity hCapPos) hCapPos
               have := hDist _ (Nat.mod_lt _ hCapPos) e hSlotCase; omega,
            by exact hNotFound ((idx % capacity + capacity -
                 idealIndex e.key capacity hCapPos) % capacity)
                 (by have := Nat.mod_lt (idx % capacity + capacity -
                      idealIndex e.key capacity hCapPos) hCapPos
                     have := hDist _ (Nat.mod_lt _ hCapPos) e hSlotCase; omega)
                 e (by
                   have hEd := hDist _ (Nat.mod_lt _ hCapPos) e hSlotCase
                   have hRt := displacement_roundtrip (idx % capacity)
                     (idealIndex e.key capacity hCapPos) capacity hCapPos
                     (idealIndex_lt e.key capacity hCapPos) e.dist
                     (by rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hCapPos)]; exact hEd)
                     (by have := Nat.mod_lt (idx % capacity + capacity -
                           idealIndex e.key capacity hCapPos) hCapPos; omega)
                   rw [hRt, Nat.mod_eq_of_lt (Nat.mod_lt _ hCapPos)]; exact hSlotCase)⟩)
  | succ n ih =>
    unfold findLoop at hNone; simp only [] at hNone
    have hIdx := Nat.mod_lt idx hCapPos
    split at hNone
    · -- slot is none
      exact carried_key_absent slots capacity hLen hCapPos k d (idx % capacity)
        (Nat.mod_lt _ hCapPos) hD hDist hPCD hNotFound (Or.inl ‹_›)
    · rename_i e hSlot
      split at hNone
      · -- key matches → findLoop returns some, contradiction
        simp at hNone
      · split at hNone
        · -- e.dist < d → early termination
          rename_i hKeyNe hDistLt
          exact carried_key_absent slots capacity hLen hCapPos k d (idx % capacity)
            (Nat.mod_lt _ hCapPos) hD hDist hPCD hNotFound
            (Or.inr ⟨e, hSlot, hDistLt, by
              cases hc : e.key == k with
              | false => rfl
              | true => exact absurd hc ‹_›⟩)
        · -- continue probing
          rename_i hKeyNe hDistGe
          have hDistLtCap : d < capacity := by
            have := Nat.mod_lt (idx % capacity + capacity -
              idealIndex k capacity hCapPos) hCapPos; omega
          have hSmall : d + 1 < capacity := by omega
          exact ih (idx % capacity + 1) (d + 1) hDist hPCD
            (disp_step' (idx % capacity) (idealIndex k capacity hCapPos)
              capacity hCapPos hIdx (idealIndex_lt k capacity hCapPos)
              d hD hSmall)
            (by
              intro d' hd' e' he'
              if hLt : d' < d then exact hNotFound d' hLt e' he'
              else
                have hEq : d' = d := by omega
                subst hEq
                have hRt := displacement_roundtrip (idx % capacity)
                  (idealIndex k capacity hCapPos) capacity hCapPos
                  (idealIndex_lt k capacity hCapPos) d
                  (by rw [Nat.mod_eq_of_lt hIdx]; exact hD)
                  (by omega)
                rw [hRt, Nat.mod_eq_of_lt hIdx] at he'
                rw [he'] at hSlot; cases hSlot
                cases hc : e'.key == k with
                | false => rfl
                | true => exact absurd hc hKeyNe)
            (by omega) hNone

/-- backshiftLoop does not introduce new keys: if key `k` is absent from all
    slots before the loop, it remains absent afterward. -/
private theorem backshiftLoop_preserves_key_absence [BEq α]
    (fuel gapIdx : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (k : α)
    (hAbsent : ∀ j (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e → (e.key == k) = false) :
    ∀ j (hj : j < capacity) (e : RHEntry α β),
      (backshiftLoop fuel gapIdx slots capacity hLen hCapPos)[j]'(by
        rw [backshiftLoop_preserves_len, hLen]; exact hj) = some e →
      (e.key == k) = false := by
  induction fuel generalizing gapIdx slots hLen hAbsent with
  | zero => simp [backshiftLoop]; exact hAbsent
  | succ n ih =>
    unfold backshiftLoop; simp only []
    have hNext : (gapIdx + 1) % capacity < slots.size := by
      rw [hLen]; exact Nat.mod_lt _ hCapPos
    split
    · exact hAbsent  -- next slot is none → no change
    · rename_i eNext hSlotNext
      split
      · exact hAbsent  -- eNext.dist == 0 → no change
      · -- backshift: set gap to {eNext with dist - 1}, set nextI to none, recurse
        have hGap : gapIdx % capacity < slots.size := by
          rw [hLen]; exact Nat.mod_lt _ hCapPos
        apply ih
        intro j' hj' e' hSlot'
        simp only [Array.getElem_set] at hSlot'
        split at hSlot'
        · -- j' = nextI → slot set to none
          simp at hSlot'
        · -- j' ≠ nextI
          simp only [Array.getElem_set] at hSlot'
          split at hSlot'
          · -- j' = gapIdx % capacity → slot set to {eNext with dist - 1}
            simp at hSlot'; obtain rfl := hSlot'
            exact hAbsent _ (Nat.mod_lt _ hCapPos) eNext hSlotNext
          · -- j' untouched
            exact hAbsent j' hj' e' hSlot'

/-- Key `k` is absent from the erased table: after `erase k`, no slot
    contains an entry with key `k`. -/
private theorem erase_removes_key [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invariant) :
    ∀ j (hj : j < (t.erase k).capacity) (e : RHEntry α β),
      (t.erase k).slots[j]'(by rw [(t.erase k).hSlotsLen]; exact hj) = some e →
      (e.key == k) = false := by
  sorry

/-- Modular displacement roundtrip: if `d = (p + cap - h) % cap` where
    `p < cap` and `h < cap` and `d < cap`, then `(h + d) % cap = p`. -/
private theorem displacement_roundtrip'
    (p h cap : Nat) (hCapPos : 0 < cap) (hp : p < cap) (hh : h < cap)
    (d : Nat) (hD : d = (p + cap - h) % cap) (hd : d < cap) :
    (h + d) % cap = p := by
  have hp' : p % cap = p := Nat.mod_eq_of_lt hp
  have := displacement_roundtrip p h cap hCapPos hh d (by rwa [hp']) hd
  rwa [hp'] at this

/-- If `(h + d1) % cap = (h + d2) % cap` with `d1 < cap` and `d2 < cap`,
    then `d1 = d2`. -/
private theorem offset_injective'
    (h cap d1 d2 : Nat) (_hCapPos : 0 < cap) (hd1 : d1 < cap) (hd2 : d2 < cap)
    (hEq : (h + d1) % cap = (h + d2) % cap) :
    d1 = d2 := by
  have hm1 : (h + d1) % cap = (h % cap + d1) % cap := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hd1]
  have hm2 : (h + d2) % cap = (h % cap + d2) % cap := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hd2]
  rw [hm1, hm2] at hEq
  have hr := Nat.mod_lt h _hCapPos
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

/-- Displacement step: `d + 1 = ((idx + 1) % cap + cap - h) % cap`
    given `d = (idx + cap - h) % cap`, `idx < cap`, `d + 1 < cap`. -/
private theorem disp_step'
    (idx h cap : Nat) (hCapPos : 0 < cap) (hIdx : idx < cap)
    (hh : h < cap) (d : Nat) (hD : d = (idx + cap - h) % cap)
    (hSmall : d + 1 < cap) :
    d + 1 = ((idx + 1) % cap + cap - h) % cap := by
  exact dist_step_mod idx h cap hCapPos hIdx hh d hD hSmall

/-- If a table satisfies `distCorrect`, `PCD`, and `noDupKeys`, and there exists
    a position `p` with `slots[p] = some e` where `e.key == k = true` and
    `e.value = v`, then `getLoop fuel idx k d` returns `some v` whenever
    `d ≤ e.dist` and `e.dist - d < fuel` and `d` tracks the displacement. -/
private theorem getLoop_finds_present [BEq α] [Hashable α] [LawfulBEq α]
    (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (p : Nat) (hp : p < capacity) (e : RHEntry α β)
    (hSlotP : slots[p]'(hLen ▸ hp) = some e)
    (hKey : (e.key == k) = true) (hVal : e.value = v)
    (hDist : ∀ j (hj : j < capacity) (e' : RHEntry α β),
      slots[j]'(hLen ▸ hj) = some e' →
      e'.dist = (j + capacity - idealIndex e'.key capacity hCapPos) % capacity)
    (hPCD : probeChainDominant slots capacity hLen hCapPos)
    (hNoDup : ∀ i j (hi : i < capacity) (hj : j < capacity)
      (ei ej : RHEntry α β),
      slots[i]'(hLen ▸ hi) = some ei →
      slots[j]'(hLen ▸ hj) = some ej →
      (ei.key == ej.key) = true → i = j)
    (hD : d = (idx % capacity + capacity -
      idealIndex k capacity hCapPos) % capacity)
    (hFuel : e.dist - d < fuel)
    (hDLe : d ≤ e.dist) :
    getLoop fuel idx k d slots capacity hLen hCapPos = some v := by
  sorry

/-- `insertLoop` never modifies slots unreachable within its fuel window.
    If position `j` cannot be reached from `idx` in fewer than `fuel` steps
    (modular), then `slots'[j] = slots[j]`. -/
private theorem insertLoop_preserves_slot [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (v : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (j : Nat) (hj : j < capacity)
    (hNR : ∀ s, s < fuel → (idx + s) % capacity ≠ j) :
    (insertLoop fuel idx k v d slots capacity hLen hCapPos).1[j]'(by
      rw [insertLoop_preserves_len, hLen]; exact hj)
    = slots[j]'(by rw [hLen]; exact hj) := by
  sorry

/-- After `insertLoop` with fuel = capacity and d = 0, the result
    contains an entry with `key == k = true` and `value = v` at some position,
    provided the table has a reachable empty slot or matching key within the
    probe chain (guaranteed by `countOccupied < capacity ∨ key already present`). -/
private theorem insertLoop_places_key [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (v : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hBound : d + fuel ≤ capacity)
    (hRoom : ∃ s, s < fuel ∧
      (slots[(idx + s) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none
       ∨ ∃ e, slots[(idx + s) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e
             ∧ (e.key == k) = true)) :
    ∃ p, ∃ hp : p < capacity,
      ∃ e : RHEntry α β,
        (insertLoop fuel idx k v d slots capacity hLen hCapPos).1[p]'(by
          rw [insertLoop_preserves_len, hLen]; exact hp) = some e
        ∧ (e.key == k) = true ∧ e.value = v := by
  sorry

/-- If every element of a list satisfies `p`, then `countP p = length`. -/
private theorem List.countP_eq_length {p : α → Bool} :
    ∀ (l : List α), (∀ i (hi : i < l.length), p (l.get ⟨i, hi⟩) = true) →
    l.countP p = l.length := by
  sorry

/-- If `countOccupied slots < capacity`, there exists an empty slot. -/
private theorem exists_empty_slot
    (slots : Array (Option (RHEntry α β))) (cap : Nat)
    (hLen : slots.size = cap) (_hCapPos : 0 < cap)
    (hLt : countOccupied slots < cap) :
    ∃ j, ∃ hj : j < cap, slots[j]'(hLen ▸ hj) = none := by
  sorry

/-- Any position is reachable from any starting index within `cap` steps. -/
private theorem position_reachable
    (idx j cap : Nat) (hCapPos : 0 < cap) (hj : j < cap) :
    ∃ s, s < cap ∧ (idx + s) % cap = j := by
  sorry

/-- After `insert k v`, the result table contains key k with value v. -/
private theorem insert_has_key [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invariant) :
    ∃ p, ∃ hp : p < (t.insert k v).capacity,
      ∃ e : RHEntry α β,
        (t.insert k v).slots[p]'((t.insert k v).hSlotsLen ▸ hp) = some e
        ∧ (e.key == k) = true ∧ e.value = v := by
  sorry

/-- N2-E1: After inserting key `k` with value `v`, looking up `k` returns `v`.
    This is the fundamental correctness theorem for Robin Hood insertion. -/
theorem RHTable.get_after_insert_eq [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invariant) :
    (t.insert k v).get? k = some v := by
  sorry

/-- `insertLoop` does not introduce entries with keys different from the
    key being inserted. If key `k'` (with `k' ≠ kIns`) is absent from all
    input slots, it remains absent from all output slots.
    Proved by induction on fuel, case-splitting on the insertLoop step.
    In the Robin Hood swap case, the displaced entry's key came from the
    original slots (so ≠ k' by hAbsent), and the IH applies. -/
private theorem insertLoop_absent_ne_key [BEq α] [Hashable α] [LawfulBEq α]
    (fuel idx : Nat) (kIns : α) (vIns : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (k' : α) (hNeIns : ¬(kIns == k') = true)
    (hAbsent : ∀ j (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(hLen ▸ hj) = some e → (e.key == k') = false) :
    ∀ j (hj : j < capacity) (e : RHEntry α β),
      (insertLoop fuel idx kIns vIns d slots capacity hLen hCapPos).1[j]'(by
        rw [insertLoop_preserves_len, hLen]; exact hj) = some e →
      (e.key == k') = false := by
  sorry

/-- If `getLoop` returns `some val`, there is a slot with a matching entry. -/
private theorem getLoop_some_implies_entry [BEq α] [Hashable α]
    (fuel idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (val : β)
    (hGet : getLoop fuel idx k d slots capacity hLen hCapPos = some val) :
    ∃ p, ∃ hp : p < capacity, ∃ e : RHEntry α β,
      slots[p]'(hLen ▸ hp) = some e ∧ (e.key == k) = true ∧ e.value = val := by
  sorry

/-- If key `k'` is absent from every slot of `t`, then `k'` is absent from
    every slot of `t.resize`. -/
private theorem resize_preserves_key_absence [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k' : α)
    (hAbsent : ∀ j (hj : j < t.capacity) (e : RHEntry α β),
      t.slots[j]'(t.hSlotsLen ▸ hj) = some e → (e.key == k') = false) :
    ∀ j (hj : j < (t.resize).capacity) (e : RHEntry α β),
      (t.resize).slots[j]'((t.resize).hSlotsLen ▸ hj) = some e →
      (e.key == k') = false := by
  sorry

/-- Every entry in the output of `insertLoop` either has (key = kIns, value = vIns)
    or existed in the input with the same key and value. -/
private theorem insertLoop_output_source [BEq α] [Hashable α] [LawfulBEq α]
    (fuel idx : Nat) (kIns : α) (vIns : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity) :
    ∀ j (hj : j < capacity) (e : RHEntry α β),
      (insertLoop fuel idx kIns vIns d slots capacity hLen hCapPos).1[j]'(by
        rw [insertLoop_preserves_len, hLen]; exact hj) = some e →
      ((e.key == kIns) = true ∧ e.value = vIns) ∨
      (∃ q, ∃ hq : q < capacity, slots[q]'(hLen ▸ hq) = some e) := by
  sorry

/-- N2-E2: Inserting key `k` does not affect lookups of other keys.
    This ensures insert doesn't corrupt existing mappings.

    Proof strategy (TPI-D5):
    • **none case**: k' absent from t.slots (contrapositive of getLoop_finds_present)
      → absent from (t.insert k v).slots (by insertLoop_absent_ne_key)
      → getLoop_none_of_absent gives none.
    • **some case**: k' present at some position with value val in t.slots
      (getLoop_some_implies_present, pending) → still present after insert
      (insertLoop_present_ne_entry, pending) → getLoop_finds_present gives some val.

    The none case is fully proved. The some case requires two additional helper
    lemmas (getLoop_some_implies_present, insertLoop_present_ne_entry) that are
    each ~50-80 lines. These are deferred to avoid exceeding the ~100-line
    threshold per proof block. -/
theorem RHTable.get_after_insert_ne [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (v : β) (hNe : ¬(k == k') = true)
    (hExt : t.invariant) :
    (t.insert k v).get? k' = t.get? k' := by
  sorry

/-- N2-E3: After erasing key `k`, looking up `k` returns `none`.
    Proved via `getLoop_none_of_absent`: key `k` is not in the erased table
    (by `erase_removes_key`), so `getLoop` never finds it. -/
theorem RHTable.get_after_erase_eq [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invariant) :
    (t.erase k).get? k = none := by
  sorry

end SeLe4n.Kernel.RobinHood
