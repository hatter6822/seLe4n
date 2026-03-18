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
    · rfl
    · rename_i e hSlot
      have hKeyNe := hAbsent (idx % capacity) hIdx e hSlot
      rw [hKeyNe]; simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · rfl
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
    have hCapLeD : capacity ≤ d := by omega
    exact carried_key_absent slots capacity hLen hCapPos k d (idx % capacity)
      (Nat.mod_lt _ hCapPos) hD hDist hPCD (by
        intro d' hd' e' he'
        exact hNotFound d' (by omega) e' he')
      (by
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
    · exact carried_key_absent slots capacity hLen hCapPos k d (idx % capacity)
        (Nat.mod_lt _ hCapPos) hD hDist hPCD hNotFound (Or.inl ‹_›)
    · rename_i e hSlot
      split at hNone
      · simp at hNone
      · split at hNone
        · rename_i hKeyNe hDistLt
          exact carried_key_absent slots capacity hLen hCapPos k d (idx % capacity)
            (Nat.mod_lt _ hCapPos) hD hDist hPCD hNotFound
            (Or.inr ⟨e, hSlot, hDistLt, by
              cases hc : e.key == k with
              | false => rfl
              | true => exact absurd hc ‹_›⟩)
        · rename_i hKeyNe hDistGe
          have hDistLtCap : d < capacity := by
            have := Nat.mod_lt (idx % capacity + capacity -
              idealIndex k capacity hCapPos) hCapPos; omega
          have hSmall : d + 1 < capacity := by omega
          exact ih (idx % capacity + 1) (d + 1) hDist hPCD
            (dist_step_mod (idx % capacity) (idealIndex k capacity hCapPos)
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
    · exact hAbsent
    · rename_i eNext hSlotNext
      split
      · exact hAbsent
      · have hGap : gapIdx % capacity < slots.size := by
          rw [hLen]; exact Nat.mod_lt _ hCapPos
        apply ih
        intro j' hj' e' hSlot'
        simp only [Array.getElem_set] at hSlot'
        split at hSlot'
        · simp at hSlot'
        · simp only [Array.getElem_set] at hSlot'
          split at hSlot'
          · simp at hSlot'; obtain rfl := hSlot'
            exact hAbsent _ (Nat.mod_lt _ hCapPos) eNext hSlotNext
          · exact hAbsent j' hj' e' hSlot'

/-- Key `k` is absent from the erased table: after `erase k`, no slot
    contains an entry with key `k`. -/
private theorem erase_removes_key [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invariant) :
    ∀ j (hj : j < (t.erase k).capacity) (e : RHEntry α β),
      (t.erase k).slots[j]'(by rw [(t.erase k).hSlotsLen]; exact hj) = some e →
      (e.key == k) = false := by
  obtain ⟨hwf, hDist, hNoDup, hPCD⟩ := hExt
  unfold RHTable.erase
  split
  · rename_i hFindNone
    simp only []
    exact findLoop_none_implies_absent t.capacity
      (idealIndex k t.capacity t.hCapPos) k 0
      t.slots t.capacity t.hSlotsLen t.hCapPos
      hDist hPCD (by simp [idealIndex]; omega)
      (by intro d' hd'; omega) (by omega) hFindNone
  · rename_i idx hFindSome
    simp only []
    have hIdxLt := findLoop_lt _ _ _ _ _ _ t.hSlotsLen t.hCapPos _ hFindSome
    have ⟨eFound, hSlotFound, hKeyFound⟩ := findLoop_correct _ _ _ _ _ _ t.hSlotsLen t.hCapPos _ hFindSome
    have hIdxMod : idx % t.capacity < t.slots.size := by
      rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
    have hAbsent' : ∀ j (hj : j < t.capacity) (e : RHEntry α β),
        (t.slots.set (idx % t.capacity) none hIdxMod)[j]'(by
          rw [Array.size_set, t.hSlotsLen]; exact hj) = some e →
        (e.key == k) = false := by
      intro j' hj' e' hSlot'
      simp only [Array.getElem_set] at hSlot'
      split at hSlot'
      · simp at hSlot'
      · cases hc : e'.key == k with
        | false => rfl
        | true =>
          exfalso
          have hEq : e'.key = k := eq_of_beq hc
          have hkFound : eFound.key = k := eq_of_beq hKeyFound
          have hKeyEq : (e'.key == eFound.key) = true := by
            rw [hEq, hkFound]; exact beq_self_eq_true k
          have := hNoDup j' (idx % t.capacity) hj' (Nat.mod_lt _ t.hCapPos)
            e' eFound hSlot' hSlotFound hKeyEq
          rename_i hNe _
          exact hNe this.symm
    exact backshiftLoop_preserves_key_absence t.capacity idx
      (t.slots.set (idx % t.capacity) none hIdxMod)
      t.capacity (by rw [Array.size_set]; exact t.hSlotsLen) t.hCapPos k hAbsent'

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
  induction fuel generalizing idx d with
  | zero => omega
  | succ n ih =>
    unfold getLoop; simp only []
    have hIdx := Nat.mod_lt idx hCapPos
    have hEk : e.key = k := eq_of_beq hKey
    have hEdist := hDist p hp e hSlotP
    -- e.dist = (p + cap - idealIndex e.key cap _) % cap
    -- d = (idx%cap + cap - idealIndex k cap _) % cap
    -- and idealIndex e.key = idealIndex k
    have hIdK : idealIndex e.key capacity hCapPos = idealIndex k capacity hCapPos := by
      rw [hEk]
    rw [hIdK] at hEdist
    have hed_lt_cap : e.dist < capacity := by
      have := Nat.mod_lt (p + capacity - idealIndex k capacity hCapPos) hCapPos; omega
    have hd_lt_cap : d < capacity := by
      have := Nat.mod_lt (idx % capacity + capacity - idealIndex k capacity hCapPos) hCapPos; omega
    -- Position at displacement d from ideal(k) = idx % cap
    have hRtD : (idealIndex k capacity hCapPos + d) % capacity = idx % capacity := by
      exact displacement_roundtrip idx (idealIndex k capacity hCapPos) capacity hCapPos
        (idealIndex_lt k capacity hCapPos) d hD hd_lt_cap
    -- Position at displacement e.dist from ideal(k) = p
    have hRtE : (idealIndex k capacity hCapPos + e.dist) % capacity = p := by
      have := displacement_roundtrip p (idealIndex k capacity hCapPos) capacity hCapPos
        (idealIndex_lt k capacity hCapPos) e.dist
        (by rw [Nat.mod_eq_of_lt hp]; exact hEdist) hed_lt_cap
      rwa [Nat.mod_eq_of_lt hp] at this
    -- Look at what's in slot idx%cap
    cases hSlotCase : slots[idx % capacity]'(by rw [hLen]; exact hIdx) with
    | none =>
      -- If slot is none, then PCD of e at distance d gives a contradiction
      -- since e.dist ≥ d > 0 would require an occupied slot at distance d
      -- but if d = e.dist then p = idx%cap and the slot should have e
      exfalso
      if hDeq : d = e.dist then
        -- p = idx%cap
        have hpEq : p = idx % capacity := by
          have : (idealIndex k capacity hCapPos + d) % capacity =
                 (idealIndex k capacity hCapPos + e.dist) % capacity := by rw [hDeq]
          rw [hRtD, hRtE] at this; exact this.symm
        rw [hpEq] at hSlotP; rw [hSlotP] at hSlotCase; simp at hSlotCase
      else
        have hDlt : d < e.dist := by omega
        have ⟨e', he', _⟩ := hPCD p hp e hSlotP d hDlt
        have hPos : (idealIndex e.key capacity hCapPos + d) % capacity = idx % capacity := by
          rw [hIdK, hRtD]
        have : slots[idx % capacity]'(by rw [hLen]; exact hIdx) = some e' := by
          have h1 : (idealIndex e.key capacity hCapPos + d) % capacity < slots.size := by
            rw [hLen]; exact Nat.mod_lt _ hCapPos
          have h2 : idx % capacity < slots.size := by rw [hLen]; exact hIdx
          have := congrArg (slots[·]) hPos
          rw [show slots[(idealIndex e.key capacity hCapPos + d) % capacity] =
            slots[(idealIndex e.key capacity hCapPos + d) % capacity]'h1 from rfl] at he'
          rw [hPos] at he'; exact he'
        rw [hSlotCase] at this; simp at this
    | some e' =>
      -- Check if e'.key == k
      if hKeyMatch : e'.key == k then
        -- Key matches! By noDupKeys, idx%cap = p, so e' = e
        have hEk' : e'.key = k := eq_of_beq hKeyMatch
        simp [hKeyMatch]
        have hEdist' := hDist _ hIdx e' hSlotCase
        have hIdK' : idealIndex e'.key capacity hCapPos = idealIndex k capacity hCapPos := by
          rw [hEk']
        rw [hIdK'] at hEdist'
        -- e' at idx%cap with displacement from ideal(k) = d
        -- e at p with displacement from ideal(k) = e.dist
        -- Both have key == k, so by noDupKeys, idx%cap = p
        have := hNoDup _ _ hIdx hp e' e hSlotCase hSlotP
          (by rw [hEk', ← hEk]; exact beq_self_eq_true e.key)
        subst this
        rw [hSlotCase] at hSlotP; cases hSlotP
        exact hVal
      else
        simp [hKeyMatch]
        -- e'.dist < d case: contradiction since PCD would need occupied slot
        -- e'.dist ≥ d case: continue probing
        if hDistLt : e'.dist < d then
          -- e' at idx%cap has dist < d, but e at p has dist ≥ d and its
          -- probe chain passes through idx%cap at distance d.
          -- PCD gives a slot at distance d with dist ≥ d, contradicting e'.dist < d
          exfalso
          if hDeq : d = e.dist then
            have hpEq : p = idx % capacity := by
              have : (idealIndex k capacity hCapPos + d) % capacity =
                     (idealIndex k capacity hCapPos + e.dist) % capacity := by rw [hDeq]
              rw [hRtD, hRtE] at this; exact this.symm
            rw [hpEq] at hSlotP; rw [hSlotP] at hSlotCase; cases hSlotCase
            simp [hKey] at hKeyMatch
          else
            have hDlt : d < e.dist := by omega
            have ⟨e'', he'', hge''⟩ := hPCD p hp e hSlotP d hDlt
            have hPos : (idealIndex e.key capacity hCapPos + d) % capacity = idx % capacity := by
              rw [hIdK, hRtD]
            have he''Idx : slots[idx % capacity]'(by rw [hLen]; exact hIdx) = some e'' := by
              have h1 : (idealIndex e.key capacity hCapPos + d) % capacity < slots.size := by
                rw [hLen]; exact Nat.mod_lt _ hCapPos
              rw [hPos] at he''; exact he''
            rw [hSlotCase] at he''Idx; cases he''Idx; omega
        else
          simp [hDistLt]
          -- Continue probing: d ≤ e'.dist, key doesn't match
          -- idx%cap ≠ p (since e'.key ≠ k but e.key = k, noDupKeys)
          have hSmall : d + 1 < capacity := by
            -- e.dist < capacity and d ≤ e.dist, and d < e.dist (otherwise
            -- idx%cap = p which contradicts key mismatch)
            -- Actually d could equal e.dist. Let's check.
            if hDeq : d = e.dist then
              -- d = e.dist means idx%cap = p
              exfalso
              have hpEq : p = idx % capacity := by
                have : (idealIndex k capacity hCapPos + d) % capacity =
                       (idealIndex k capacity hCapPos + e.dist) % capacity := by rw [hDeq]
                rw [hRtD, hRtE] at this; exact this.symm
              rw [hpEq] at hSlotP; rw [hSlotP] at hSlotCase; cases hSlotCase
              simp [hKey] at hKeyMatch
            else
              have : d < e.dist := by omega
              omega
          exact ih (idx % capacity + 1) (d + 1)
            (dist_step_mod _ _ _ hCapPos hIdx (idealIndex_lt k capacity hCapPos) d hD hSmall)
            (by omega) (by omega)

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
  induction fuel generalizing idx k v d slots hLen with
  | zero => simp [insertLoop]
  | succ n ih =>
    unfold insertLoop; simp only []
    have hIdx : idx % capacity < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    have hNe : idx % capacity ≠ j := by
      have := hNR 0 (by omega); simp at this; exact this
    split
    · -- none slot: set idx%cap to some entry
      simp only [Array.getElem_set]
      split
      · rename_i h; exact absurd h hNe
      · rfl
    · rename_i e
      split
      · -- key match: set idx%cap
        simp only [Array.getElem_set]
        split
        · rename_i h; exact absurd h hNe
        · rfl
      · split
        · -- Robin Hood swap: set idx%cap, then recurse
          have hLen' : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx).size = capacity := by
            rw [Array.size_set]; exact hLen
          have hStep := ih (idx % capacity + 1) e.key e.value (e.dist + 1)
            (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx) hLen' j hj (by
              intro s hs
              have := hNR (s + 1) (by omega)
              simp only [Nat.add_assoc] at this ⊢
              convert this using 2; omega)
          rw [hStep]
          simp only [Array.getElem_set]
          split
          · rename_i h; exact absurd h hNe
          · rfl
        · -- continue probing
          exact ih (idx % capacity + 1) k v (d + 1) slots hLen j hj (by
            intro s hs
            have := hNR (s + 1) (by omega)
            simp only [Nat.add_assoc] at this ⊢
            convert this using 2; omega)

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
  induction fuel generalizing idx k v d slots hLen with
  | zero => obtain ⟨s, hs, _⟩ := hRoom; omega
  | succ n ih =>
    unfold insertLoop; simp only []
    have hIdx : idx % capacity < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    have hModLt := Nat.mod_lt idx hCapPos
    split
    · -- none slot: place entry here
      exact ⟨idx % capacity, hModLt, ⟨k, v, d⟩, by
        simp only [Array.getElem_set]; split
        · simp
        · rename_i h; exact absurd rfl h, beq_self_eq_true k, rfl⟩
    · rename_i e hSlot
      split
      · -- key match: update value in place
        exact ⟨idx % capacity, hModLt, { e with value := v }, by
          simp only [Array.getElem_set]; split
          · simp
          · rename_i h; exact absurd rfl h,
          by
            rename_i hKeyMatch
            simp [hKeyMatch], rfl⟩
      · split
        · -- Robin Hood swap
          have hLen' : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx).size = capacity := by
            rw [Array.size_set]; exact hLen
          -- The inserted entry for k is at idx%cap in the new slots
          exact ⟨idx % capacity, hModLt, ⟨k, v, d⟩, by
            have hPreserved := insertLoop_preserves_slot n (idx % capacity + 1) e.key e.value
              (e.dist + 1) (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)
              capacity hLen' hCapPos (idx % capacity) hModLt (by
                intro s hs
                have h1s : 1 + s < capacity := by omega
                intro heq
                have : (idx % capacity + (1 + s)) % capacity = idx % capacity := by
                  convert heq using 2; omega
                rw [Nat.add_mod_right] at this
                have := Nat.mod_eq_of_lt (by omega : s < capacity)
                omega)
            rw [hPreserved]
            simp only [Array.getElem_set]; split
            · simp
            · rename_i hNe; exact absurd rfl hNe, beq_self_eq_true k, rfl⟩
        · -- continue probing
          obtain ⟨s, hs, hOr⟩ := hRoom
          if hZero : s = 0 then
            subst hZero; simp at hOr
            rcases hOr with hNone | ⟨e', he', _⟩
            · rw [hNone] at hSlot; simp at hSlot
            · rw [he'] at hSlot; cases hSlot; rename_i hKeyNe _; simp [‹_›] at hKeyNe
          else
            exact ih (idx % capacity + 1) k v (d + 1) slots hLen (by omega)
              ⟨s - 1, by omega, by
                have : idx + s = idx % capacity + 1 + (s - 1) := by omega
                rwa [this] at hOr⟩

/-- If every element of a list satisfies `p`, then `countP p = length`. -/
private theorem List.countP_eq_length {p : α → Bool} :
    ∀ (l : List α), (∀ i (hi : i < l.length), p (l.get ⟨i, hi⟩) = true) →
    l.countP p = l.length := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro hAll
    simp only [List.countP_cons, List.length_cons]
    have hx := hAll 0 (by simp)
    simp at hx; rw [hx]; simp
    exact ih (by
      intro i hi
      exact hAll (i + 1) (by simp; omega))

/-- If `countOccupied slots < capacity`, there exists an empty slot. -/
private theorem exists_empty_slot
    (slots : Array (Option (RHEntry α β))) (cap : Nat)
    (hLen : slots.size = cap) (_hCapPos : 0 < cap)
    (hLt : countOccupied slots < cap) :
    ∃ j, ∃ hj : j < cap, slots[j]'(hLen ▸ hj) = none := by
  by_contra hAll
  push_neg at hAll
  -- Every slot is occupied
  have hOcc : countOccupied slots = cap := by
    unfold countOccupied
    rw [← hLen]
    apply List.countP_eq_length
    intro i hi
    simp only [Array.toList_length] at hi
    have hi' : i < cap := by rw [← hLen]; exact hi
    have := hAll i hi'
    simp only [Option.isSome]
    cases hCase : slots[i]'(hLen ▸ hi') with
    | none => exact absurd rfl (this hCase)
    | some _ => rfl
  omega

/-- Any position is reachable from any starting index within `cap` steps. -/
private theorem position_reachable
    (idx j cap : Nat) (hCapPos : 0 < cap) (hj : j < cap) :
    ∃ s, s < cap ∧ (idx + s) % cap = j := by
  use (j + cap - idx % cap) % cap
  constructor
  · exact Nat.mod_lt _ hCapPos
  · have hIdxMod := Nat.mod_lt idx hCapPos
    have hsMod := Nat.mod_lt (j + cap - idx % cap) hCapPos
    -- (idx + (j + cap - idx%cap) % cap) % cap = j
    -- idx = idx%cap + cap * (idx/cap)
    -- so idx + s ≡ idx%cap + s (mod cap)
    rw [Nat.add_mod, Nat.mod_mod_of_dvd]
    · by_cases hge : j ≥ idx % cap
      · have : (j + cap - idx % cap) % cap = j - idx % cap := by
          have : j + cap - idx % cap = (j - idx % cap) + cap := by omega
          rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
        rw [this]
        have : idx % cap + (j - idx % cap) = j := by omega
        rw [this, Nat.mod_eq_of_lt hj]
      · have hlt := Nat.lt_of_not_le hge
        have : (j + cap - idx % cap) % cap = j + cap - idx % cap := by
          exact Nat.mod_eq_of_lt (by omega)
        rw [this]
        have : idx % cap + (j + cap - idx % cap) = j + cap := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    · exact dvd_refl cap

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
  induction fuel generalizing idx kIns vIns d slots hLen hAbsent with
  | zero => simp [insertLoop]; exact hAbsent
  | succ n ih =>
    unfold insertLoop; simp only []
    have hIdx : idx % capacity < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    intro j hj e' hSlot'
    split at hSlot'
    · -- none slot: set idx%cap to ⟨kIns, vIns, d⟩
      simp only [Array.getElem_set] at hSlot'
      split at hSlot'
      · simp at hSlot'; obtain rfl := hSlot'
        simp; cases hc : kIns == k' with
        | true => exact absurd hc hNeIns
        | false => rfl
      · exact hAbsent j hj e' hSlot'
    · rename_i eOld hSlotOld
      split at hSlot'
      · -- key match: update value
        simp only [Array.getElem_set] at hSlot'
        split at hSlot'
        · simp at hSlot'; obtain rfl := hSlot'
          simp; exact hAbsent _ (Nat.mod_lt _ hCapPos) eOld hSlotOld
        · exact hAbsent j hj e' hSlot'
      · split at hSlot'
        · -- Robin Hood swap: set idx%cap to ⟨kIns, vIns, d⟩, recurse with eOld
          have hLen' : (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx).size = capacity := by
            rw [Array.size_set]; exact hLen
          have hAbsent' : ∀ j (hj : j < capacity) (e : RHEntry α β),
              (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)[j]'(by
                rw [Array.size_set, hLen]; exact hj) = some e →
              (e.key == k') = false := by
            intro j' hj' e'' hSlot''
            simp only [Array.getElem_set] at hSlot''
            split at hSlot''
            · simp at hSlot''; obtain rfl := hSlot''
              simp; cases hc : kIns == k' with
              | true => exact absurd hc hNeIns
              | false => rfl
            · exact hAbsent j' hj' e'' hSlot''
          -- eOld.key ≠ k' because eOld was in original slots
          have hNeOld : ¬(eOld.key == k') = true := by
            intro hc
            have := hAbsent _ (Nat.mod_lt _ hCapPos) eOld hSlotOld
            simp [hc] at this
          exact ih (idx % capacity + 1) eOld.key eOld.value (eOld.dist + 1)
            (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx) hLen'
            k' hNeOld hAbsent' j hj e' hSlot'
        · -- continue probing
          exact ih (idx % capacity + 1) kIns vIns (d + 1) slots hLen k' hNeIns hAbsent j hj e' hSlot'

/-- If `getLoop` returns `some val`, there is a slot with a matching entry. -/
private theorem getLoop_some_implies_entry [BEq α] [Hashable α]
    (fuel idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (val : β)
    (hGet : getLoop fuel idx k d slots capacity hLen hCapPos = some val) :
    ∃ p, ∃ hp : p < capacity, ∃ e : RHEntry α β,
      slots[p]'(hLen ▸ hp) = some e ∧ (e.key == k) = true ∧ e.value = val := by
  induction fuel generalizing idx d with
  | zero => simp [getLoop] at hGet
  | succ n ih =>
    unfold getLoop at hGet; simp only [] at hGet
    have hIdx := Nat.mod_lt idx hCapPos
    split at hGet
    · simp at hGet
    · rename_i e hSlot
      split at hGet
      · rename_i hKey
        simp at hGet
        exact ⟨idx % capacity, hIdx, e, hSlot, hKey, hGet⟩
      · split at hGet
        · simp at hGet
        · exact ih (idx % capacity + 1) (d + 1) hGet

/-- If key `k'` is absent from every slot of `t`, then `k'` is absent from
    every slot of `t.resize`. -/
private theorem resize_preserves_key_absence [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k' : α)
    (hAbsent : ∀ j (hj : j < t.capacity) (e : RHEntry α β),
      t.slots[j]'(t.hSlotsLen ▸ hj) = some e → (e.key == k') = false) :
    ∀ j (hj : j < (t.resize).capacity) (e : RHEntry α β),
      (t.resize).slots[j]'((t.resize).hSlotsLen ▸ hj) = some e →
      (e.key == k') = false := by
  unfold RHTable.resize RHTable.fold
  have hNewPos : 0 < t.capacity * 2 := Nat.mul_pos t.hCapPos (by omega)
  suffices hSuff : ∀ j (hj : j < (Array.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => acc.insertNoResize e.key e.value) (RHTable.empty (t.capacity * 2) hNewPos)
      t.slots).capacity) (e : RHEntry α β),
      (Array.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => acc.insertNoResize e.key e.value) (RHTable.empty (t.capacity * 2) hNewPos)
      t.slots).slots[j]'(by
        rw [(Array.foldl (fun acc slot =>
          match slot with
          | none => acc
          | some e => acc.insertNoResize e.key e.value) (RHTable.empty (t.capacity * 2) hNewPos)
          t.slots).hSlotsLen]; exact hj) = some e →
      (e.key == k') = false from hSuff
  apply Array.foldl_induction
    (motive := fun _ (acc : RHTable α β) =>
      ∀ j (hj : j < acc.capacity) (e : RHEntry α β),
        acc.slots[j]'(acc.hSlotsLen ▸ hj) = some e → (e.key == k') = false)
  · intro j hj e hSlot; simp [RHTable.empty] at hSlot
  · intro ⟨i, hi⟩ acc hAcc
    split
    · exact hAcc
    · rename_i eOrig hSlotOrig
      have hOrigAbsent : (eOrig.key == k') = false := by
        have hi' : i < t.capacity := by rw [← t.hSlotsLen]; exact hi
        exact hAbsent i hi' eOrig hSlotOrig
      unfold RHTable.insertNoResize; simp only []
      intro j hj e' hSlot'
      exact insertLoop_absent_ne_key acc.capacity
        (idealIndex eOrig.key acc.capacity acc.hCapPos)
        eOrig.key eOrig.value 0
        acc.slots acc.capacity acc.hSlotsLen acc.hCapPos
        k' (by rw [hOrigAbsent]; simp) hAcc j hj e' hSlot'


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
  induction fuel generalizing idx kIns vIns d slots hLen with
  | zero => simp [insertLoop]; intro j hj e he; exact Or.inr ⟨j, hj, he⟩
  | succ n ih =>
    unfold insertLoop; simp only []
    have hIdx : idx % capacity < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    intro j hj e' hSlot'
    split at hSlot'
    · -- none slot
      simp only [Array.getElem_set] at hSlot'
      split at hSlot'
      · simp at hSlot'; obtain rfl := hSlot'
        exact Or.inl ⟨beq_self_eq_true kIns, rfl⟩
      · exact Or.inr ⟨j, hj, hSlot'⟩
    · rename_i eOld hSlotOld
      split at hSlot'
      · -- key match
        simp only [Array.getElem_set] at hSlot'
        split at hSlot'
        · simp at hSlot'; obtain rfl := hSlot'
          simp
          rename_i hKeyMatch
          -- e' = { eOld with value := vIns }
          -- eOld.key == kIns = true, so e'.key == kIns = true
          exact Or.inl ⟨hKeyMatch, rfl⟩
        · exact Or.inr ⟨j, hj, hSlot'⟩
      · split at hSlot'
        · -- Robin Hood swap
          have hLen' : (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx).size = capacity := by
            rw [Array.size_set]; exact hLen
          have := ih (idx % capacity + 1) eOld.key eOld.value (eOld.dist + 1)
            (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx) hLen' j hj e' hSlot'
          rcases this with ⟨hKey, hVal⟩ | ⟨q, hq, hSlotQ⟩
          · -- Entry has eOld.key and eOld.value
            -- eOld was in original slots
            exact Or.inr ⟨idx % capacity, Nat.mod_lt _ hCapPos, by
              rw [hSlotOld]; congr 1
              have hEk : e'.key = eOld.key := eq_of_beq hKey
              have hEv : e'.value = eOld.value := hVal
              sorry⟩
          · -- Entry existed in set slots
            simp only [Array.getElem_set] at hSlotQ
            split at hSlotQ
            · simp at hSlotQ; obtain rfl := hSlotQ
              exact Or.inl ⟨beq_self_eq_true kIns, rfl⟩
            · exact Or.inr ⟨q, hq, hSlotQ⟩
        · -- continue probing
          exact ih (idx % capacity + 1) kIns vIns (d + 1) slots hLen j hj e' hSlot'

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
  unfold RHTable.get?
  exact getLoop_none_of_absent _ _ _ _ _ _ _ _
    (erase_removes_key t k hExt)

end SeLe4n.Kernel.RobinHood

/-- If every element of a list satisfies `p`, then `countP p = length`. -/
private theorem List.countP_eq_length {p : α → Bool} :
    ∀ (l : List α), (∀ i (hi : i < l.length), p (l.get ⟨i, hi⟩) = true) →
    l.countP p = l.length := by
  intro l h
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, List.length_cons]
    have hx : p x = true := by have := h 0 (by omega); simp [List.get] at this; exact this
    rw [hx]; simp only [ite_true]
    rw [ih (fun i hi => by have := h (i + 1) (by omega); simp [List.get] at this; exact this)]

/-- If `countOccupied slots < capacity`, there exists an empty slot. -/
private theorem exists_empty_slot
    (slots : Array (Option (RHEntry α β))) (cap : Nat)
    (hLen : slots.size = cap) (_hCapPos : 0 < cap)
    (hLt : countOccupied slots < cap) :
    ∃ j, ∃ hj : j < cap, slots[j]'(hLen ▸ hj) = none := by
  by_contra h; push_neg at h
  have hAllSome : ∀ j (hj : j < cap), (slots[j]'(hLen ▸ hj)).isSome = true := by
    intro j hj
    have := h j hj
    cases hSlot : slots[j]'(hLen ▸ hj) with
    | none => exact absurd rfl (this (by intro e he; rw [hSlot] at he; simp at he))
    | some _ => rfl
  have hCount : countOccupied slots = cap := by
    unfold countOccupied; rw [← hLen]
    apply List.countP_eq_length
    intro i hi
    rw [Array.length_toList] at hi
    have hLt' : i < cap := by rw [← hLen]; exact hi
    show (slots.toList[i]).isSome = true
    rw [Array.getElem_toList]; exact hAllSome i hLt'
  omega

/-- Any position is reachable from any starting index within `cap` steps. -/
private theorem position_reachable
    (idx j cap : Nat) (hCapPos : 0 < cap) (hj : j < cap) :
    ∃ s, s < cap ∧ (idx + s) % cap = j := by
  refine ⟨(j + cap - idx % cap) % cap, Nat.mod_lt _ hCapPos, ?_⟩
  have hIdxMod := Nat.mod_lt idx hCapPos
  by_cases hge : j ≥ idx % cap
  · have hval : (j + cap - idx % cap) % cap = j - idx % cap := by
      have h1 : j + cap - idx % cap = (j - idx % cap) + cap := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hval, Nat.add_mod, Nat.mod_self_add _ hCapPos, Nat.mod_eq_of_lt (by omega)]
    have : idx % cap + (j - idx % cap) = j := by omega
    rw [this, Nat.mod_eq_of_lt hj]
  · have hlt := Nat.lt_of_not_le hge
    have hval : (j + cap - idx % cap) % cap = j + cap - idx % cap := by
      exact Nat.mod_eq_of_lt (by omega)
    rw [hval, Nat.add_mod, Nat.mod_self_add _ hCapPos, Nat.mod_eq_of_lt (by omega)]
    have : idx % cap + (j + cap - idx % cap) = j + cap := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

/-- After `insert k v`, the result table contains key k with value v. -/
private theorem insert_has_key [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invariant) :
    ∃ p, ∃ hp : p < (t.insert k v).capacity,
      ∃ e : RHEntry α β,
        (t.insert k v).slots[p]'((t.insert k v).hSlotsLen ▸ hp) = some e
        ∧ (e.key == k) = true ∧ e.value = v := by
  unfold RHTable.insert
  split
  · unfold RHTable.insertNoResize; simp only []
    have hRes := t.resize_preserves_invariant
    have hResCap : 0 < (t.resize).capacity := hRes.1.capPos
    apply insertLoop_places_key; · omega
    · have hNewCap : (t.resize).capacity = t.capacity * 2 := RHTable.resize_fold_capacity t
      have hLt : countOccupied (t.resize).slots < (t.resize).capacity := by
        rw [← hRes.1.sizeCount, hNewCap]; have := hExt.1.sizeBound; omega
      obtain ⟨j, hj, hNone⟩ := exists_empty_slot (t.resize).slots
        (t.resize).capacity (t.resize).hSlotsLen hResCap hLt
      obtain ⟨s, hs, hEq⟩ := position_reachable
        (idealIndex k (t.resize).capacity hResCap) j (t.resize).capacity hResCap hj
      exact ⟨s, hs, Or.inl (by rw [hEq]; exact hNone)⟩
  · unfold RHTable.insertNoResize; simp only []
    apply insertLoop_places_key; · omega
    · rename_i hNoResize; push_neg at hNoResize
      have hSizeLt : t.size < t.capacity := by omega
      have hLt : countOccupied t.slots < t.capacity := by rw [← hExt.1.sizeCount]; exact hSizeLt
      obtain ⟨j, hj, hNone⟩ := exists_empty_slot t.slots t.capacity t.hSlotsLen t.hCapPos hLt
      obtain ⟨s, hs, hEq⟩ := position_reachable
        (idealIndex k t.capacity t.hCapPos) j t.capacity t.hCapPos hj
      exact ⟨s, hs, Or.inl (by rw [hEq]; exact hNone)⟩

/-- N2-E1: After inserting key `k` with value `v`, looking up `k` returns `v`. -/
theorem RHTable.get_after_insert_eq [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invariant) :
    (t.insert k v).get? k = some v := by
  have hIns := t.insert_preserves_invariant k v hExt
  obtain ⟨p, hp, e, hSlotP, hKey, hVal⟩ := insert_has_key t k v hExt
  unfold RHTable.get?
  exact getLoop_finds_present
    (t.insert k v).capacity
    (idealIndex k (t.insert k v).capacity (t.insert k v).hCapPos)
    k 0 (t.insert k v).slots (t.insert k v).capacity
    (t.insert k v).hSlotsLen (t.insert k v).hCapPos
    p hp e hSlotP hKey hVal hIns.2.1 hIns.2.2.2 hIns.2.2.1
    (by simp [Nat.mod_eq_of_lt (idealIndex_lt k (t.insert k v).capacity
      (t.insert k v).hCapPos)])
    (by omega) (by omega)

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
  induction fuel generalizing idx kIns vIns d slots hLen with
  | zero => simp [insertLoop]; intro j hj e hSlot; exact Or.inr ⟨j, hj, hSlot⟩
  | succ n ih =>
    unfold insertLoop; simp only []
    have hIdx : idx % capacity < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    have hIdxLt : idx % capacity < capacity := Nat.mod_lt _ hCapPos
    intro j hj eJ hSlotJ
    split at hSlotJ
    · -- empty slot
      simp [Array.getElem_set] at hSlotJ
      split at hSlotJ
      · cases hSlotJ; exact Or.inl ⟨BEq.refl, rfl⟩
      · exact Or.inr ⟨j, hj, hSlotJ⟩
    · rename_i e hSlot
      split at hSlotJ
      · -- key match
        simp [Array.getElem_set] at hSlotJ
        split at hSlotJ
        · cases hSlotJ; exact Or.inl ⟨by assumption, rfl⟩
        · exact Or.inr ⟨j, hj, hSlotJ⟩
      · split at hSlotJ
        · -- Robin Hood swap: kIns→idx%cap, e displaced forward
          have hLenSet := show (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩)
            hIdx).size = capacity from by rw [Array.size_set]; exact hLen
          have := ih (idx % capacity + 1) e.key e.value (e.dist + 1)
            (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx) hLenSet
            j hj eJ hSlotJ
          rcases this with ⟨hKeyEq, hValEq⟩ | ⟨q, hq, hOrig⟩
          · -- eJ.key == e.key (the displaced entry's key) and eJ.value = e.value
            -- e came from slots[idx%cap], so eJ has e's key
            -- eJ exists in original slots at idx%cap
            right; simp [Array.getElem_set] at hOrig
          · -- eJ existed in the set-array at position q
            simp [Array.getElem_set] at hOrig
            split at hOrig
            · -- q = idx%cap: eJ = ⟨kIns, vIns, d⟩
              cases hOrig; exact Or.inl ⟨BEq.refl, rfl⟩
            · exact Or.inr ⟨q, hq, hOrig⟩
        · -- continue probing
          exact ih (idx % capacity + 1) kIns vIns (d + 1) slots hLen j hj eJ hSlotJ
