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

/-- `(a % n + b) % n = (a + b) % n` — modular addition absorbs inner mod. -/
private theorem mod_add_mod_eq (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  conv => lhs; rw [Nat.add_mod]
  conv => rhs; rw [Nat.add_mod]
  rw [Nat.mod_mod]

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
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    split
    · -- none: return none
      rfl
    · -- some e: key ≠ k (by hAbsent)
      rename_i e hSlot
      have hKNe := hAbsent (idx % capacity) (Nat.mod_lt _ hCapPos) e hSlot
      if hDist : e.dist < d then
        simp [getLoop, hSlot, hKNe, hDist]
      else
        simp only [getLoop, hSlot, hKNe, hDist, ite_false, ite_true]
        exact ih (idx % capacity + 1) (d + 1)

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
    (hFuel : d + fuel ≥ capacity)
    (hNone : findLoop fuel idx k d slots capacity hLen hCapPos = none) :
    ∀ j (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(hLen ▸ hj) = some e → (e.key == k) = false := by
  revert idx d hD hNotFound hFuel hNone
  induction fuel with
  | zero =>
    intro idx d hD hNotFound hFuel hNone
    -- fuel = 0 and d + 0 ≥ capacity → d ≥ capacity
    have hd : d ≥ capacity := by omega
    intro j hj e hSlot
    cases hContra : e.key == k with
    | false => rfl
    | true =>
      exfalso
      have hkj : e.key = k := eq_of_beq hContra
      have hEd := hDist j hj e hSlot
      have hIdK : idealIndex e.key capacity hCapPos = idealIndex k capacity hCapPos := by
        rw [hkj]
      rw [hIdK] at hEd
      have hed_lt : e.dist < capacity := by
        have := Nat.mod_lt (j + capacity - idealIndex k capacity hCapPos) hCapPos; omega
      have hFalse := hNotFound e.dist (by omega) e (by
        have hRt : (idealIndex k capacity hCapPos + e.dist) % capacity = j := by
          have := displacement_roundtrip j (idealIndex k capacity hCapPos) capacity hCapPos
            (idealIndex_lt k capacity hCapPos) e.dist
            (by rw [Nat.mod_eq_of_lt hj]; exact hEd) hed_lt
          rwa [Nat.mod_eq_of_lt hj] at this
        simp only [hRt]; exact hSlot)
      simp [hContra] at hFalse
  | succ n ih =>
    intro idx d hD hNotFound hFuel hNone
    unfold findLoop at hNone; simp only [] at hNone
    have hPos : idx % capacity < capacity := Nat.mod_lt _ hCapPos
    split at hNone
    · -- Slot at idx % cap is none → carried_key_absent (empty slot)
      rename_i hSlotNone
      exact carried_key_absent slots capacity hLen hCapPos k d (idx % capacity) hPos
        hD hDist hPCD hNotFound (Or.inl hSlotNone)
    · -- Slot at idx % cap is some e
      rename_i e hSlot
      split at hNone
      · -- Key match → findLoop returns some, contradicts hNone
        simp at hNone
      · split at hNone
        · -- e.dist < d and key ≠ k → carried_key_absent (dist too small)
          rename_i hKeyNe hDistLt
          have hKeyF : (e.key == k) = false := by cases h : e.key == k <;> simp_all
          exact carried_key_absent slots capacity hLen hCapPos k d (idx % capacity) hPos
            hD hDist hPCD hNotFound (Or.inr ⟨e, hSlot, hDistLt, hKeyF⟩)
        · -- Continue probing: key ≠ k, e.dist ≥ d → recurse
          rename_i hKeyNe hDistGe
          have hKeyF : (e.key == k) = false := by cases h : e.key == k <;> simp_all
          have hDistGe' : ¬ e.dist < d := hDistGe
          have hd_lt : d < capacity := by
            have := Nat.mod_lt (idx % capacity + capacity -
              idealIndex k capacity hCapPos) hCapPos; omega
          -- Helper: displacement_roundtrip from d' = d
          have hDispRt : ∀ d', d' = d → (idealIndex k capacity hCapPos + d') % capacity =
              idx % capacity := by
            intro d' hd'_eq; rw [hd'_eq]
            have := displacement_roundtrip (idx % capacity)
              (idealIndex k capacity hCapPos) capacity hCapPos
              (idealIndex_lt k capacity hCapPos) d
              (by rw [Nat.mod_eq_of_lt hPos]; exact hD) hd_lt
            rwa [Nat.mod_eq_of_lt hPos] at this
          -- Helper: slot at position d has key ≠ k
          have hSlotD : ∀ d', d' = d →
              ∀ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
                rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' →
              (e'.key == k) = false := by
            intro d' hd'_eq e' hSlot'
            have hSlotE : slots[idx % capacity]'(by rw [hLen]; exact hPos) = some e' := by
              simp only [hDispRt d' hd'_eq] at hSlot'; exact hSlot'
            have : e' = e := Option.some.inj (hSlotE.symm.trans hSlot)
            subst this; exact hKeyF
          by_cases hSmall : d + 1 < capacity
          · -- Recurse
            have hD' : d + 1 = ((idx % capacity + 1) % capacity + capacity -
                idealIndex k capacity hCapPos) % capacity := by
              have hEd := hDist (idx % capacity) hPos e hSlot
              have := dist_step_mod (idx % capacity) (idealIndex k capacity hCapPos)
                capacity hCapPos hPos (idealIndex_lt k capacity hCapPos) d hD hSmall
              omega
            have hNotFound' : ∀ d', d' < d + 1 →
                ∀ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
                  rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' →
                (e'.key == k) = false := by
              intro d' hd' e' hSlot'
              by_cases hd'_lt : d' < d
              · exact hNotFound d' hd'_lt e' hSlot'
              · exact hSlotD d' (by omega) e' hSlot'
            exact ih (idx % capacity + 1) (d + 1) hD' hNotFound' (by omega) hNone
          · -- d + 1 ≥ capacity: all positions covered directly
            have hFullCov : ∀ d', d' < capacity →
                ∀ e', slots[(idealIndex k capacity hCapPos + d') % capacity]'(by
                  rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' →
                (e'.key == k) = false := by
              intro d' hd' e' hSlot'
              by_cases hd'_lt : d' < d
              · exact hNotFound d' hd'_lt e' hSlot'
              · exact hSlotD d' (by omega) e' hSlot'
            intro j hj eJ hSlotJ
            cases hContraJ : eJ.key == k with
            | false => rfl
            | true =>
              exfalso
              have hkj : eJ.key = k := eq_of_beq hContraJ
              have hEdJ := hDist j hj eJ hSlotJ
              rw [show idealIndex eJ.key capacity hCapPos =
                  idealIndex k capacity hCapPos from by rw [hkj]] at hEdJ
              have hed_lt : eJ.dist < capacity := by
                have := Nat.mod_lt (j + capacity - idealIndex k capacity hCapPos) hCapPos; omega
              have hRtJ : (idealIndex k capacity hCapPos + eJ.dist) % capacity = j := by
                have := displacement_roundtrip j (idealIndex k capacity hCapPos) capacity hCapPos
                  (idealIndex_lt k capacity hCapPos) eJ.dist
                  (by rw [Nat.mod_eq_of_lt hj]; exact hEdJ) hed_lt
                rwa [Nat.mod_eq_of_lt hj] at this
              have hSlotAtIdeal : slots[(idealIndex k capacity hCapPos + eJ.dist) % capacity]'(by
                  rw [hLen]; exact Nat.mod_lt _ hCapPos) = some eJ := by
                simp only [hRtJ]; exact hSlotJ
              have := hFullCov eJ.dist hed_lt eJ hSlotAtIdeal
              simp [hContraJ] at this

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
  induction fuel generalizing gapIdx slots hLen with
  | zero => simp [backshiftLoop]; exact hAbsent
  | succ n ih =>
    have hGapI : gapIdx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hNextI : (gapIdx + 1) % capacity < slots.size := by
      rw [hLen]; exact Nat.mod_lt _ hCapPos
    intro j hj e hSlot
    match hNext : slots[(gapIdx + 1) % capacity]'hNextI with
    | none =>
      simp [backshiftLoop, hNext] at hSlot
      exact hAbsent j hj e hSlot
    | some nextE =>
      if hDist : nextE.dist == 0 then
        simp [backshiftLoop, hNext, hDist] at hSlot
        exact hAbsent j hj e hSlot
      else
        -- Backward shift: entry moved from (gapIdx+1)%cap to gapIdx%cap
        -- with dist decremented. The key is preserved (same nextE.key).
        have hDistF : (nextE.dist == 0) = false := by
          cases h : nextE.dist == 0 <;> simp_all
        simp only [backshiftLoop, hNext, hDistF, ↓reduceIte] at hSlot
        simp only [show (false = true) ↔ False from ⟨Bool.noConfusion, False.elim⟩,
          ite_false] at hSlot
        -- The intermediate array has the same keys (nextE.key moved, nextI cleared)
        have hLen2 : ((slots.set (gapIdx % capacity)
            (some { nextE with dist := nextE.dist - 1 }) hGapI).set
            ((gapIdx + 1) % capacity) none
            (by rw [Array.size_set]; exact hNextI)).size = capacity := by
          rw [Array.size_set, Array.size_set]; exact hLen
        have hAbsent2 : ∀ j (hj : j < capacity) (e : RHEntry α β),
            ((slots.set (gapIdx % capacity)
              (some { nextE with dist := nextE.dist - 1 }) hGapI).set
              ((gapIdx + 1) % capacity) none
              (by rw [Array.size_set]; exact hNextI))[j]'(by
                rw [Array.size_set, Array.size_set, hLen]; exact hj) = some e →
            (e.key == k) = false := by
          intro a ha ea hA
          simp only [Array.getElem_set] at hA
          split at hA
          · simp at hA  -- nextI set to none
          · split at hA
            · -- gapIdx set to {nextE with dist := nextE.dist - 1}
              have : ea = { nextE with dist := nextE.dist - 1 } := Option.some.inj hA.symm
              rw [this]; simp only
              -- nextE.key was in the original table at (gapIdx+1) % cap
              exact hAbsent ((gapIdx + 1) % capacity) (Nat.mod_lt _ hCapPos) nextE hNext
            · exact hAbsent a ha ea hA
        exact ih ((gapIdx + 1) % capacity) _ hLen2 hAbsent2 j hj e hSlot

/-- Key `k` is absent from the erased table: after `erase k`, no slot
    contains an entry with key `k`. -/
private theorem erase_removes_key [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) :
    ∀ j (hj : j < (t.erase k).capacity) (e : RHEntry α β),
      (t.erase k).slots[j]'(by rw [(t.erase k).hSlotsLen]; exact hj) = some e →
      (e.key == k) = false := by
  simp only [RHTable.erase]
  generalize hFind : findLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
    t.slots t.capacity t.hSlotsLen t.hCapPos = result
  cases result with
  | none =>
    -- Key not found: table unchanged. findLoop none → k absent via carried_key_absent.
    simp only []
    exact findLoop_none_implies_absent t.capacity _ k 0 t.slots t.capacity
      t.hSlotsLen t.hCapPos hExt.2.1 hExt.2.2.2
      (by simp [idealIndex])
      (by intro d' hd'; omega)
      (by omega)
      hFind
  | some idx =>
    -- Key found at idx: clear + backshift
    simp only []
    have hFound := hFind
    intro j hj e hSlot
    have hIdxS : idx % t.capacity < t.slots.size := by
      rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
    have hLen' : (t.slots.set (idx % t.capacity) none hIdxS).size = t.capacity := by
      rw [Array.size_set]; exact t.hSlotsLen
    -- After clearing idx % cap, key k is absent (it was only at idx by noDupKeys,
    -- and that slot is now none).
    have ⟨eFound, hSlotFound, hKeyFound⟩ := findLoop_correct t.capacity _ k 0
      t.slots t.capacity t.hSlotsLen t.hCapPos idx hFound
    have hIdxLt := findLoop_lt t.capacity _ k 0 t.slots t.capacity t.hSlotsLen
      t.hCapPos idx hFound
    have hAbsentCleared : ∀ a (ha : a < t.capacity) (ea : RHEntry α β),
        (t.slots.set (idx % t.capacity) none hIdxS)[a]'(by
          rw [Array.size_set, t.hSlotsLen]; exact ha) = some ea →
        (ea.key == k) = false := by
      intro a ha ea hA
      simp only [Array.getElem_set] at hA
      split at hA
      · simp at hA  -- cleared slot is none
      · -- a ≠ idx % cap, so slot unchanged from original
        rename_i haNe
        cases hContra : ea.key == k with
        | false => rfl
        | true =>
          exfalso
          -- ea has key k at position a ≠ idx % cap
          -- But noDupKeys says the only position with key k is idx % cap
          -- (since eFound at idx % cap also has key == k)
          have : a = idx % t.capacity :=
            hExt.2.2.1 a (idx % t.capacity) ha (Nat.mod_lt _ t.hCapPos) ea eFound hA
              hSlotFound (by rw [hContra]; exact hKeyFound)
          exact haNe this
    -- backshiftLoop preserves key absence
    exact backshiftLoop_preserves_key_absence t.capacity idx
      (t.slots.set (idx % t.capacity) none hIdxS) t.capacity hLen' t.hCapPos k
      hAbsentCleared j hj e hSlot

/-- Modular displacement roundtrip: if `d = (p + cap - h) % cap` where
    `p < cap` and `h < cap` and `d < cap`, then `(h + d) % cap = p`. -/
private theorem displacement_roundtrip'
    (p h cap : Nat) (hCapPos : 0 < cap) (hp : p < cap) (hh : h < cap)
    (d : Nat) (hD : d = (p + cap - h) % cap) (hd : d < cap) :
    (h + d) % cap = p := by
  subst hD
  by_cases hge : p ≥ h
  · have hval : (p + cap - h) % cap = p - h := by
      rw [show p + cap - h = (p - h) + cap from by omega,
          Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hval, show h + (p - h) = p from by omega, Nat.mod_eq_of_lt hp]
  · simp only [Nat.not_le] at hge
    have hval : (p + cap - h) % cap = p + cap - h :=
      Nat.mod_eq_of_lt (by omega)
    rw [hval, show h + (p + cap - h) = p + cap from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hp]

/-- If `(h + d1) % cap = (h + d2) % cap` with `d1 < cap` and `d2 < cap`,
    then `d1 = d2`. -/
private theorem offset_injective'
    (h cap d1 d2 : Nat) (_hCapPos : 0 < cap) (hd1 : d1 < cap) (hd2 : d2 < cap)
    (hEq : (h + d1) % cap = (h + d2) % cap) :
    d1 = d2 := by
  have hm : h % cap < cap := Nat.mod_lt h _hCapPos
  conv at hEq => lhs; rw [Nat.add_mod, Nat.mod_eq_of_lt hd1]
  conv at hEq => rhs; rw [Nat.add_mod, Nat.mod_eq_of_lt hd2]
  by_cases h1 : h % cap + d1 < cap <;> by_cases h2 : h % cap + d2 < cap
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hEq; omega
  · simp only [Nat.not_lt] at h2
    have hb : h % cap + d2 - cap < cap := by omega
    rw [Nat.mod_eq_of_lt h1,
        show h % cap + d2 = (h % cap + d2 - cap) + cap from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hb] at hEq; omega
  · simp only [Nat.not_lt] at h1
    have hb : h % cap + d1 - cap < cap := by omega
    rw [Nat.mod_eq_of_lt h2,
        show h % cap + d1 = (h % cap + d1 - cap) + cap from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hb] at hEq; omega
  · simp only [Nat.not_lt] at h1 h2
    have hb1 : h % cap + d1 - cap < cap := by omega
    have hb2 : h % cap + d2 - cap < cap := by omega
    rw [show h % cap + d1 = (h % cap + d1 - cap) + cap from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hb1,
        show h % cap + d2 = (h % cap + d2 - cap) + cap from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hb2] at hEq; omega

/-- Displacement step: `d + 1 = ((idx + 1) % cap + cap - h) % cap`
    given `d = (idx + cap - h) % cap`, `idx < cap`, `d + 1 < cap`. -/
private theorem disp_step'
    (idx h cap : Nat) (hCapPos : 0 < cap) (hIdx : idx < cap)
    (hh : h < cap) (d : Nat) (hD : d = (idx + cap - h) % cap)
    (hSmall : d + 1 < cap) :
    d + 1 = ((idx + 1) % cap + cap - h) % cap := by
  -- Key idea: (h + d) % cap = idx (by roundtrip), so (h + (d+1)) % cap = (idx+1) % cap
  -- and d+1 < cap, so d+1 is the unique displacement from h to (idx+1)%cap.
  have hRound := displacement_roundtrip' idx h cap hCapPos hIdx hh d hD (by omega)
  -- We need: d + 1 = ((idx+1)%cap + cap - h) % cap
  -- Equivalently: (h + (d+1)) % cap = (idx+1) % cap  (and d+1 < cap)
  -- This follows from: (h + (d+1)) = (h + d) + 1, and (h + d) % cap = idx
  suffices hGoal : (h + (d + 1)) % cap = (idx + 1) % cap by
    -- Now we have (h + (d+1)) % cap = (idx+1) % cap
    -- and d+1 < cap. We need d+1 = ((idx+1)%cap + cap - h) % cap.
    -- This is the "inverse" of displacement_roundtrip', i.e.,
    -- if (h + x) % cap = y % cap and x < cap, then x = (y%cap + cap - h) % cap.
    have hNxt := Nat.mod_lt (idx + 1) hCapPos
    by_cases hge : (idx + 1) % cap ≥ h
    · have hb1 : (idx + 1) % cap - h < cap := by omega
      rw [show (idx + 1) % cap + cap - h = ((idx + 1) % cap - h) + cap from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hb1]
      by_cases hlt : h + (d + 1) < cap
      · rw [Nat.mod_eq_of_lt hlt] at hGoal; omega
      · simp only [Nat.not_lt] at hlt
        have hb2 : h + (d + 1) - cap < cap := by omega
        rw [show h + (d + 1) = (h + (d + 1) - cap) + cap from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hb2] at hGoal; omega
    · simp only [Nat.not_le] at hge
      have hb1 : (idx + 1) % cap + cap - h < cap := by omega
      rw [Nat.mod_eq_of_lt hb1]
      by_cases hlt : h + (d + 1) < cap
      · rw [Nat.mod_eq_of_lt hlt] at hGoal; omega
      · simp only [Nat.not_lt] at hlt
        have hb2 : h + (d + 1) - cap < cap := by omega
        rw [show h + (d + 1) = (h + (d + 1) - cap) + cap from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hb2] at hGoal; omega
  conv => lhs; rw [show h + (d + 1) = (h + d) + 1 from by omega, Nat.add_mod, hRound]
  conv => rhs; rw [Nat.add_mod, Nat.mod_eq_of_lt hIdx]

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
  | zero => simp [getLoop] at hFuel hDLe ⊢ <;> omega
  | succ n ih =>
    unfold getLoop; simp only []
    have hIdxMod : idx % capacity < capacity := Nat.mod_lt _ hCapPos
    have hIdxS : idx % capacity < slots.size := by rw [hLen]; exact hIdxMod
    have hd_lt_cap : d < capacity := by
      have := Nat.mod_lt (idx % capacity + capacity -
        idealIndex k capacity hCapPos) hCapPos; omega
    -- e.dist is the displacement of the target from ideal(k)
    have hKeyEq : idealIndex e.key capacity hCapPos = idealIndex k capacity hCapPos := by
      rw [eq_of_beq hKey]
    have hEDist := hDist p hp e hSlotP
    rw [hKeyEq] at hEDist
    have hdk_lt : e.dist < capacity := by
      have := Nat.mod_lt (p + capacity - idealIndex k capacity hCapPos) hCapPos; omega
    -- (ideal(k) + d) % cap = idx % cap
    have hRound : (idealIndex k capacity hCapPos + d) % capacity = idx % capacity :=
      displacement_roundtrip' (idx % capacity) (idealIndex k capacity hCapPos) capacity
        hCapPos hIdxMod (idealIndex_lt k capacity hCapPos) d hD hd_lt_cap
    -- (ideal(k) + e.dist) % cap = p
    have hpRound : (idealIndex k capacity hCapPos + e.dist) % capacity = p :=
      displacement_roundtrip' p (idealIndex k capacity hCapPos) capacity
        hCapPos hp (idealIndex_lt k capacity hCapPos) e.dist hEDist hdk_lt
    by_cases hDeq : d = e.dist
    · -- At the target: idx % cap = p
      have hIdxP : idx % capacity = p := by rw [← hRound, hDeq, hpRound]
      have hSlotP' : slots[idx % capacity]'hIdxS = some e := by
        simp only [hIdxP]; exact hSlotP
      rw [hSlotP']; simp [hKey, hVal]
    · -- d < e.dist: not at target yet
      have hDLt : d < e.dist := by omega
      -- PCD at distance d from ideal(e.key)
      obtain ⟨e', he', hge'⟩ := hPCD p hp e hSlotP d hDLt
      rw [hKeyEq] at he'
      -- e' at (ideal(k) + d) % cap = idx % cap
      have he'Pos : slots[idx % capacity]'hIdxS = some e' := by
        simp only [show idx % capacity = (idealIndex k capacity hCapPos + d) % capacity from
          hRound.symm]; exact he'
      rw [he'Pos]
      -- e'.key ≠ k: if e'.key == k, noDupKeys gives (ideal(k)+d)%cap = p,
      -- then d = e.dist by offset_injective', contradicting d < e.dist.
      have hKeyNe : (e'.key == k) = false := by
        by_contra hContra; simp only [Bool.not_eq_false] at hContra
        have := hNoDup (idx % capacity) p hIdxMod hp e' e he'Pos hSlotP
          (by rw [hContra]; exact hKey)
        -- idx % cap = p → (ideal(k)+d)%cap = p = (ideal(k)+e.dist)%cap
        rw [this] at hRound
        exact absurd (offset_injective' (idealIndex k capacity hCapPos) capacity
          d e.dist hCapPos hd_lt_cap hdk_lt (hRound.trans hpRound.symm)) (by omega)
      simp [hKeyNe]
      -- e'.dist ≥ d, so no early termination
      have : ¬(e'.dist < d) := by omega
      simp [this]
      -- Recurse at d+1
      have hD' : d + 1 = ((idx % capacity + 1) % capacity + capacity -
          idealIndex k capacity hCapPos) % capacity :=
        disp_step' (idx % capacity) (idealIndex k capacity hCapPos) capacity
          hCapPos hIdxMod (idealIndex_lt k capacity hCapPos) d
          hD (by omega)
      exact ih (idx % capacity + 1) (d + 1) hD' (by omega) (by omega)

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
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hjNe : idx % capacity ≠ j := by
      have := hNR 0 (by omega); simp at this; exact this
    cases hSlot : slots[idx % capacity]'hIdx with
    | none =>
      simp only [insertLoop, hSlot]
      rw [Array.getElem_set]; simp [hjNe]
    | some e =>
      unfold insertLoop; simp only []; simp only [hSlot]
      if hKey : e.key == k then
        simp only [hKey, ite_true]
        rw [Array.getElem_set]; simp [hjNe]
      else if hRH : e.dist < d then
        simp only [hKey, ite_false, hRH, ite_true]
        have hLen' : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx).size = capacity := by
          rw [Array.size_set]; exact hLen
        have hNR' : ∀ s, s < n → (idx % capacity + 1 + s) % capacity ≠ j := by
          intro s hs
          have h := hNR (s + 1) (by omega)
          rw [show idx % capacity + 1 + s = idx % capacity + (s + 1) from by omega,
              mod_add_mod_eq]; exact h
        have hIH := ih (idx % capacity + 1) e.key e.value (e.dist + 1) _ hLen' hNR'
        rw [hIH, Array.getElem_set]; simp [hjNe]
      else
        simp only [hKey, ite_false, hRH, ite_false]
        have hNR' : ∀ s, s < n → (idx % capacity + 1 + s) % capacity ≠ j := by
          intro s hs
          have h := hNR (s + 1) (by omega)
          rw [show idx % capacity + 1 + s = idx % capacity + (s + 1) from by omega,
              mod_add_mod_eq]; exact h
        exact ih (idx % capacity + 1) k v (d + 1) slots hLen hNR'

/-- After `insertLoop` with fuel = capacity and d = 0, the result
    contains an entry with `key == k = true` and `value = v` at some position,
    provided the table has a reachable empty slot or matching key within the
    probe chain (guaranteed by `countOccupied < capacity ∨ key already present`). -/
private theorem insertLoop_places_key [BEq α] [Hashable α] [LawfulBEq α]
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
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hIdxCap : idx % capacity < capacity := Nat.mod_lt _ hCapPos
    cases hSlot : slots[idx % capacity]'hIdx with
    | none =>
      unfold insertLoop; simp only []; simp only [hSlot]
      exact ⟨idx % capacity, hIdxCap, ⟨k, v, d⟩,
        by simp [Array.getElem_set], BEq.refl k, rfl⟩
    | some e =>
      simp only [insertLoop, hSlot]
      split
      · -- e.key == k = true: update in place
        rename_i hKey
        exact ⟨idx % capacity, hIdxCap, { e with value := v },
          by simp [Array.getElem_set], hKey, rfl⟩
      · -- e.key == k = false
        rename_i hKey
        split
        · -- e.dist < d: Robin Hood swap
          rename_i hRH
          have hLen' : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx).size = capacity := by
            rw [Array.size_set]; exact hLen
          have hn_lt : n < capacity := by omega
          have hPreserved := insertLoop_preserves_slot n (idx % capacity + 1) e.key e.value
            (e.dist + 1) (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx) capacity hLen'
            hCapPos (idx % capacity) hIdxCap
            (by intro s hs
                by_contra hEq
                have : (idx % capacity + 1 + s) % capacity = idx % capacity := hEq
                have h1s : 1 + s < capacity := by omega
                rw [show idx % capacity + 1 + s = idx % capacity + (1 + s) from by omega,
                    Nat.add_mod, Nat.mod_eq_of_lt hIdxCap, Nat.mod_eq_of_lt h1s] at this
                by_cases hlt : idx % capacity + (1 + s) < capacity
                · rw [Nat.mod_eq_of_lt hlt] at this; omega
                · simp only [Nat.not_lt] at hlt
                  have hb : idx % capacity + (1 + s) - capacity < capacity := by omega
                  rw [show idx % capacity + (1 + s) = (idx % capacity + (1 + s) - capacity) +
                    capacity from by omega, Nat.add_mod_right,
                    Nat.mod_eq_of_lt hb] at this; omega)
          have hSlotKV : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[idx % capacity]'(by
              rw [Array.size_set]; exact hIdx) = some ⟨k, v, d⟩ := by
            simp [Array.getElem_set]
          rw [hSlotKV] at hPreserved
          exact ⟨idx % capacity, hIdxCap, ⟨k, v, d⟩,
            hPreserved.symm, BEq.refl k, rfl⟩
      · -- e.dist ≥ d: continue probing
        rename_i hRH
        -- Continue probing: need to show room still exists for recursive call
        obtain ⟨s, hs, hSlotS⟩ := hRoom
        have hRoom' : ∃ s', s' < n ∧
            (slots[(idx % capacity + 1 + s') % capacity]'(by
              rw [hLen]; exact Nat.mod_lt _ hCapPos) = none
             ∨ ∃ e', slots[(idx % capacity + 1 + s') % capacity]'(by
              rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e'
                    ∧ (e'.key == k) = true) := by
          -- s = 0 case: slot at idx%cap has e with key ≠ k and is not empty → s ≠ 0
          by_cases hs0 : s = 0
          · subst hs0; simp at hSlotS
            rcases hSlotS with hNone | ⟨e', he', hKeyE⟩
            · -- slot at (idx+0)%cap = idx%cap is none, contradicts hSlot
              rw [show (idx + 0) % capacity = idx % capacity from by simp] at hNone
              rw [hNone] at hSlot; exact absurd hSlot (by simp)
            · -- slot at idx%cap has entry with key == k, contradicts hKey
              rw [show (idx + 0) % capacity = idx % capacity from by simp] at he'
              rw [he'] at hSlot; cases hSlot
              exact absurd hKeyE (by simp [hKey])
          · -- s > 0: use s - 1 for the recursive call
            refine ⟨s - 1, by omega, ?_⟩
            rw [show idx % capacity + 1 + (s - 1) = idx + s from by omega]
            exact hSlotS
        exact ih (idx % capacity + 1) k v (d + 1) slots hLen (by omega) hRoom'

/-- If every element of a list satisfies `p`, then `countP p = length`. -/
private theorem List.countP_eq_length {p : α → Bool} :
    ∀ (l : List α), (∀ i (hi : i < l.length), p (l.get ⟨i, hi⟩) = true) →
    l.countP p = l.length
  | [], _ => rfl
  | hd :: tl, hAll => by
    simp only [List.countP_cons, List.length_cons]
    have hhd := hAll 0 (by simp)
    simp at hhd; rw [hhd]; simp
    exact List.countP_eq_length tl (fun i hi => by
      have := hAll (i + 1) (by simp; omega)
      simpa using this)

/-- If `countOccupied slots < capacity`, there exists an empty slot. -/
private theorem exists_empty_slot
    (slots : Array (Option (RHEntry α β))) (cap : Nat)
    (hLen : slots.size = cap) (_hCapPos : 0 < cap)
    (hLt : countOccupied slots < cap) :
    ∃ j, ∃ hj : j < cap, slots[j]'(hLen ▸ hj) = none := by
  by_contra hAll; simp only [not_exists] at hAll
  -- Every slot is some
  have hOcc : ∀ j (hj : j < cap), (slots[j]'(hLen ▸ hj)).isSome = true := by
    intro j hj
    have := hAll j hj
    match h : slots[j]'(hLen ▸ hj) with
    | none => exact absurd h this
    | some _ => rfl
  -- countOccupied = cap
  have : countOccupied slots = cap := by
    unfold countOccupied
    rw [← hLen]
    rw [show slots.size = slots.toList.length from Array.length_toList _]
    exact List.countP_eq_length slots.toList (fun i hi => by
      have hi' : i < cap := by rwa [Array.length_toList, hLen] at hi
      have : (slots.toList.get ⟨i, hi⟩).isSome = true := by
        rw [show slots.toList.get ⟨i, hi⟩ = slots[i]'(by rw [hLen]; exact hi') from by
          simp [Array.getElem_eq_toList_get]]
        exact hOcc i hi'
      exact this)
  omega

/-- Any position is reachable from any starting index within `cap` steps. -/
private theorem position_reachable
    (idx j cap : Nat) (hCapPos : 0 < cap) (hj : j < cap) :
    ∃ s, s < cap ∧ (idx + s) % cap = j := by
  -- s = (j + cap - idx % cap) % cap works
  refine ⟨(j + cap - idx % cap) % cap, Nat.mod_lt _ hCapPos, ?_⟩
  have hm := Nat.mod_lt idx hCapPos
  by_cases hge : j ≥ idx % cap
  · have hb1 : j - idx % cap < cap := by omega
    have hb2 : idx % cap + (j - idx % cap) < cap := by omega
    rw [show j + cap - idx % cap = (j - idx % cap) + cap from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hb1]
    rw [Nat.add_mod, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hb2]
    rw [show idx % cap + (j - idx % cap) = j from by omega, Nat.mod_eq_of_lt hj]
  · simp only [Nat.not_le] at hge
    have hb1 : j + cap - idx % cap < cap := by omega
    rw [Nat.mod_eq_of_lt hb1]
    rw [Nat.add_mod, Nat.mod_eq_of_lt hm]
    by_cases hlt : idx % cap + (j + cap - idx % cap) < cap
    · omega
    · simp only [Nat.not_lt] at hlt
      have hb2 : idx % cap + (j + cap - idx % cap) - cap < cap := by omega
      rw [show idx % cap + (j + cap - idx % cap) =
        (idx % cap + (j + cap - idx % cap) - cap) + cap from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hb2]
      omega

/-- After `insert k v`, the result table contains key k with value v. -/
private theorem insert_has_key [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    ∃ p, ∃ hp : p < (t.insert k v).capacity,
      ∃ e : RHEntry α β,
        (t.insert k v).slots[p]'((t.insert k v).hSlotsLen ▸ hp) = some e
        ∧ (e.key == k) = true ∧ e.value = v := by
  -- Unfold insert: t.insert k v = t'.insertNoResize k v where t' may be resized
  unfold RHTable.insert
  -- Case split on whether resize happens
  split
  · -- Resize case: t' = t.resize
    rename_i hResize
    let t' := t.resize
    have ht'_def : t' = t.resize := rfl
    -- t'.invExt holds
    have hExt' := t.resize_preserves_invExt
    rw [← ht'_def] at hExt'
    -- t' has size ≤ old capacity < 2 * old capacity = t'.capacity
    have hSizeLt : t'.size < t'.capacity := by
      have hSB := hExt'.1.sizeBound
      have hResizeCap : t'.capacity = t.capacity * 2 := t.resize_fold_capacity
      rw [ht'_def, hResizeCap]
      have := hExt.1.sizeBound
      -- After resize, size ≤ old size ≤ old capacity < 2 * old capacity
      -- Actually, resize rebuilds with fold, so size = countOccupied of result
      -- which equals the original count. But we know size ≤ capacity (from sizeBound).
      -- And t'.capacity = 2 * t.capacity. So t'.size ≤ t'.capacity = 2*t.capacity,
      -- but we need strict <. Since t.capacity > 0, 2*t.capacity > t.capacity ≥ t.size ≥ t'.size...
      -- Actually resize changes size too. The fold re-inserts all entries.
      -- t'.size = countOccupied of the resized table = number of entries.
      -- Since all original entries are re-inserted, t'.size = t.size (if no duplicates,
      -- which is guaranteed by noDupKeys).
      -- So t'.size = t.size ≤ t.capacity < 2 * t.capacity = t'.capacity.
      omega
    -- There exists an empty slot in t'
    have ⟨j, hj, hjNone⟩ := exists_empty_slot t'.slots t'.capacity t'.hSlotsLen t'.hCapPos
      (by rw [← hExt'.1.sizeCount]; exact hSizeLt)
    -- That slot is reachable from idealIndex k within capacity steps
    have ⟨s, hs, hsEq⟩ := position_reachable (idealIndex k t'.capacity t'.hCapPos) j
      t'.capacity t'.hCapPos hj
    -- Build hRoom for insertLoop_places_key
    have hRoom : ∃ s, s < t'.capacity ∧
        (t'.slots[(idealIndex k t'.capacity t'.hCapPos + s) % t'.capacity]'(by
          rw [t'.hSlotsLen]; exact Nat.mod_lt _ t'.hCapPos) = none
         ∨ ∃ e, t'.slots[(idealIndex k t'.capacity t'.hCapPos + s) % t'.capacity]'(by
          rw [t'.hSlotsLen]; exact Nat.mod_lt _ t'.hCapPos) = some e
               ∧ (e.key == k) = true) :=
      ⟨s, hs, Or.inl (by rw [hsEq]; exact hjNone)⟩
    -- Apply insertLoop_places_key
    unfold RHTable.insertNoResize
    simp only []
    have hResult := insertLoop_places_key t'.capacity
      (idealIndex k t'.capacity t'.hCapPos) k v 0
      t'.slots t'.capacity t'.hSlotsLen t'.hCapPos
      (by omega) hRoom
    obtain ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := hResult
    exact ⟨p, hp, e, hSlotP, hKeyE, hValE⟩
  · -- No resize case: t' = t
    rename_i hNoResize
    simp only [Nat.not_le] at hNoResize
    -- t.size * 4 < t.capacity * 3, so t.size < t.capacity
    have hSizeLt : t.size < t.capacity := by
      have := hExt.1.sizeBound; omega
    have ⟨j, hj, hjNone⟩ := exists_empty_slot t.slots t.capacity t.hSlotsLen t.hCapPos
      (by rw [← hExt.1.sizeCount]; exact hSizeLt)
    have ⟨s, hs, hsEq⟩ := position_reachable (idealIndex k t.capacity t.hCapPos) j
      t.capacity t.hCapPos hj
    have hRoom : ∃ s, s < t.capacity ∧
        (t.slots[(idealIndex k t.capacity t.hCapPos + s) % t.capacity]'(by
          rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos) = none
         ∨ ∃ e, t.slots[(idealIndex k t.capacity t.hCapPos + s) % t.capacity]'(by
          rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos) = some e
               ∧ (e.key == k) = true) :=
      ⟨s, hs, Or.inl (by rw [hsEq]; exact hjNone)⟩
    unfold RHTable.insertNoResize
    simp only []
    have hResult := insertLoop_places_key t.capacity
      (idealIndex k t.capacity t.hCapPos) k v 0
      t.slots t.capacity t.hSlotsLen t.hCapPos
      (by omega) hRoom
    obtain ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := hResult
    exact ⟨p, hp, e, hSlotP, hKeyE, hValE⟩

/-- N2-E1: After inserting key `k` with value `v`, looking up `k` returns `v`.
    This is the fundamental correctness theorem for Robin Hood insertion. -/
theorem RHTable.get_after_insert_eq [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insert k v).get? k = some v := by
  -- The result table satisfies invExt
  have hInsExt := t.insert_preserves_invExt k v hExt
  -- Key k, value v exists in the result table (via insert_has_key below)
  have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := insert_has_key t k v hExt
  -- Unfold get? and apply getLoop_finds_present
  unfold RHTable.get?
  have hDistE := hInsExt.2.1 p hp e hSlotP
  have hKeyEq : idealIndex e.key (t.insert k v).capacity (t.insert k v).hCapPos
      = idealIndex k (t.insert k v).capacity (t.insert k v).hCapPos := by
    rw [eq_of_beq hKeyE]
  rw [hKeyEq] at hDistE
  have hdk_lt : e.dist < (t.insert k v).capacity := by
    have := Nat.mod_lt (p + (t.insert k v).capacity -
      idealIndex k (t.insert k v).capacity (t.insert k v).hCapPos) (t.insert k v).hCapPos
    omega
  exact getLoop_finds_present (t.insert k v).capacity
    (idealIndex k (t.insert k v).capacity (t.insert k v).hCapPos)
    k 0 (t.insert k v).slots (t.insert k v).capacity
    (t.insert k v).hSlotsLen (t.insert k v).hCapPos
    p hp e hSlotP hKeyE hValE
    hInsExt.2.1 hInsExt.2.2.2 hInsExt.2.2.1
    (by simp [Nat.mod_eq_of_lt (idealIndex_lt k _ _)])
    (by omega) (by omega)

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
  induction fuel generalizing idx kIns vIns d slots hLen with
  | zero => intro j hj e hSlot; simp [insertLoop] at hSlot; exact hAbsent j hj e hSlot
  | succ n ih =>
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    intro j hj e hSlot
    cases hSlotCase : slots[idx % capacity]'hIdx with
    | none =>
      simp only [insertLoop, hSlotCase] at hSlot
      simp only [Array.getElem_set] at hSlot
      split at hSlot
      · cases hSlot; simp only
        cases h : kIns == k' with
        | false => rfl
        | true => exact absurd h hNeIns
      · exact hAbsent j hj e hSlot
    | some eOld =>
      simp only [insertLoop, hSlotCase] at hSlot
      if hKey : eOld.key == kIns then
        simp only [hKey, ite_true] at hSlot
        simp only [Array.getElem_set] at hSlot
        split at hSlot
        · cases hSlot; simp only
          exact hAbsent (idx % capacity) (Nat.mod_lt _ hCapPos) eOld hSlotCase
        · exact hAbsent j hj e hSlot
      else if hRH : eOld.dist < d then
        simp only [hKey, ite_false, hRH, ite_true] at hSlot
        have hLen' : (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx).size
            = capacity := by rw [Array.size_set]; exact hLen
        have hAbsent' : ∀ a (ha : a < capacity) (ea : RHEntry α β),
            (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)[a]'(by
              rw [Array.size_set, hLen]; exact ha) = some ea →
            (ea.key == k') = false := by
          intro a ha ea hA
          simp only [Array.getElem_set] at hA
          split at hA
          · cases hA; simp only
            cases h : kIns == k' with
            | false => rfl
            | true => exact absurd h hNeIns
          · exact hAbsent a ha ea hA
        have hOldNeK' : ¬(eOld.key == k') = true := by
          intro hContra
          have := hAbsent (idx % capacity) (Nat.mod_lt _ hCapPos) eOld hSlotCase
          rw [hContra] at this; exact Bool.noConfusion this
        exact ih (idx % capacity + 1) eOld.key eOld.value (eOld.dist + 1) _ hLen'
          hOldNeK' hAbsent' j hj e hSlot
      else
        simp only [hKey, ite_false, hRH, ite_false] at hSlot
        exact ih (idx % capacity + 1) kIns vIns (d + 1) slots hLen
          hNeIns hAbsent j hj e hSlot

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
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    split at hGet
    · simp at hGet
    · rename_i e hSlot
      if hKey : e.key == k then
        simp [hKey] at hGet
        exact ⟨idx % capacity, Nat.mod_lt _ hCapPos, e, hSlot, hKey, hGet⟩
      else if hDist : e.dist < d then
        simp [hKey, hDist] at hGet
      else
        simp only [hKey, ite_false, hDist, ite_false] at hGet
        exact ih (idx % capacity + 1) (d + 1) hGet

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
  exact Array.foldl_induction
    (motive := fun _ (acc : RHTable α β) =>
      ∀ j (hj : j < acc.capacity) (e : RHEntry α β),
        acc.slots[j]'(by rw [acc.hSlotsLen]; exact hj) = some e → (e.key == k') = false)
    (by intro j hj e hSlot; simp [RHTable.empty] at hSlot)
    (fun i acc hAcc => by
      match hSlotI : t.slots[i] with
      | none => exact hAcc
      | some eOrig =>
        have hi : (i : Nat) < t.capacity := by rw [← t.hSlotsLen]; exact i.isLt
        have hOrigAbs : ¬(eOrig.key == k') = true := by
          have := hAbsent i hi eOrig (by
            show t.slots[(i : Nat)]'(by rw [t.hSlotsLen]; exact hi) = some eOrig
            exact hSlotI)
          simp [this]
        show ∀ j hj e, (acc.insertNoResize eOrig.key eOrig.value).slots[j]'(by
          rw [(acc.insertNoResize eOrig.key eOrig.value).hSlotsLen]; exact hj) = some e →
          (e.key == k') = false
        intro j hj e hSlot
        unfold RHTable.insertNoResize at hSlot hj; simp only [] at hSlot hj
        exact insertLoop_absent_ne_key acc.capacity
          (idealIndex eOrig.key acc.capacity acc.hCapPos) eOrig.key eOrig.value 0
          acc.slots acc.capacity acc.hSlotsLen acc.hCapPos k' hOrigAbs hAcc j hj e hSlot)

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
  | zero =>
    intro j hj e hSlot; simp [insertLoop] at hSlot
    exact Or.inr ⟨j, hj, hSlot⟩
  | succ n ih =>
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    intro j hj e hSlotR
    cases hSlot : slots[idx % capacity]'hIdx with
    | none =>
      simp only [insertLoop, hSlot] at hSlotR
      simp only [Array.getElem_set] at hSlotR
      split at hSlotR
      · cases hSlotR; exact Or.inl ⟨BEq.refl kIns, rfl⟩
      · exact Or.inr ⟨j, hj, hSlotR⟩
    | some eOld =>
      simp only [insertLoop, hSlot] at hSlotR
      if hKey : eOld.key == kIns then
        simp only [hKey, ite_true] at hSlotR
        simp only [Array.getElem_set] at hSlotR
        split at hSlotR
        · -- Updated entry: key = eOld.key (== kIns), value = vIns
          cases hSlotR
          exact Or.inl ⟨hKey, rfl⟩
        · exact Or.inr ⟨j, hj, hSlotR⟩
      else if hRH : eOld.dist < d then
        simp only [hKey, ite_false, hRH, ite_true] at hSlotR
        have hLen' : (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx).size
            = capacity := by rw [Array.size_set]; exact hLen
        have hIH := ih (idx % capacity + 1) eOld.key eOld.value (eOld.dist + 1)
          (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx) hLen' hCapPos
          j hj e hSlotR
        rcases hIH with ⟨hKeyE, hValE⟩ | ⟨q, hq, hSlotQ⟩
        · -- Entry has key == eOld.key and value == eOld.value.
          -- eOld was in original slots at idx%cap.
          exact Or.inr ⟨idx % capacity, Nat.mod_lt _ hCapPos, by
            rw [hValE]; show slots[idx % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) =
              some { eOld with value := eOld.value }
            simp; exact hSlot⟩
        · -- Entry from slots' (set array). Check if q = idx%cap.
          simp only [Array.getElem_set] at hSlotQ
          split at hSlotQ
          · -- q = idx%cap: e = ⟨kIns, vIns, d⟩
            cases hSlotQ; exact Or.inl ⟨BEq.refl kIns, rfl⟩
          · -- q ≠ idx%cap: e from original slots
            exact Or.inr ⟨q, hq, hSlotQ⟩
      else
        simp only [hKey, ite_false, hRH, ite_false] at hSlotR
        exact ih (idx % capacity + 1) kIns vIns (d + 1) slots hLen j hj e hSlotR

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
    (hExt : t.invExt) :
    (t.insert k v).get? k' = t.get? k' := by
  have hInsExt := t.insert_preserves_invExt k v hExt
  cases hGet : t.get? k' with
  | none =>
    -- k' absent from t.slots (contrapositive of getLoop_finds_present)
    have hAbsOrig : ∀ j (hj : j < t.capacity) (e : RHEntry α β),
        t.slots[j]'(t.hSlotsLen ▸ hj) = some e → (e.key == k') = false := by
      intro j hj e hSlot
      cases hKE : e.key == k' with
      | false => rfl
      | true =>
        exfalso
        have hDist := hExt.2.1 j hj e hSlot
        have hKeyEq : idealIndex e.key t.capacity t.hCapPos
            = idealIndex k' t.capacity t.hCapPos := by rw [eq_of_beq hKE]
        rw [hKeyEq] at hDist
        have hdk_lt : e.dist < t.capacity := by
          have := Nat.mod_lt (j + t.capacity -
            idealIndex k' t.capacity t.hCapPos) t.hCapPos; omega
        have hFound := getLoop_finds_present t.capacity
          (idealIndex k' t.capacity t.hCapPos) k' 0 t.slots t.capacity
          t.hSlotsLen t.hCapPos j hj e hSlot hKE rfl
          hExt.2.1 hExt.2.2.2 hExt.2.2.1
          (by simp [Nat.mod_eq_of_lt (idealIndex_lt k' _ _)])
          (by omega) (by omega)
        unfold RHTable.get? at hGet; rw [hFound] at hGet; simp at hGet
    -- k' absent from (t.insert k v).slots via insertLoop_absent_ne_key
    have hAbsIns : ∀ j (hj : j < (t.insert k v).capacity) (e : RHEntry α β),
        (t.insert k v).slots[j]'((t.insert k v).hSlotsLen ▸ hj) = some e →
        (e.key == k') = false := by
      unfold RHTable.insert RHTable.insertNoResize; simp only []
      split
      · -- Resize case: k' absent from t.resize via resize_preserves_key_absence
        intro j hj e hSlot
        exact insertLoop_absent_ne_key (t.resize).capacity
          (idealIndex k (t.resize).capacity (t.resize).hCapPos) k v 0
          (t.resize).slots (t.resize).capacity (t.resize).hSlotsLen (t.resize).hCapPos
          k' hNe (resize_preserves_key_absence t k' hAbsOrig) j hj e hSlot
      · -- No resize case: direct application
        intro j hj e hSlot
        exact insertLoop_absent_ne_key t.capacity
          (idealIndex k t.capacity t.hCapPos) k v 0
          t.slots t.capacity t.hSlotsLen t.hCapPos
          k' hNe hAbsOrig j hj e hSlot
    unfold RHTable.get?
    exact getLoop_none_of_absent _ _ _ _ _ _ _ _ hAbsIns
  | some val =>
    -- Step 1: extract witness from t.get? k' = some val
    obtain ⟨p, hp, eP, hSlotP, hKeyP, hValP⟩ :=
      getLoop_some_implies_entry t.capacity _ k' 0 t.slots t.capacity t.hSlotsLen t.hCapPos val
        (by unfold RHTable.get? at hGet; exact hGet)
    -- Step 2: k' exists in result (by insertLoop_absent_ne_key contrapositive)
    have hPresent : ∃ p', ∃ hp' : p' < (t.insert k v).capacity, ∃ e' : RHEntry α β,
        (t.insert k v).slots[p']'((t.insert k v).hSlotsLen ▸ hp') = some e' ∧
        (e'.key == k') = true := by
      by_contra hAll; simp only [not_exists, not_and] at hAll
      -- k' would be absent from result → get? k' = none → contradicts hGet
      have hAbs : ∀ j (hj : j < (t.insert k v).capacity) (e : RHEntry α β),
          (t.insert k v).slots[j]'((t.insert k v).hSlotsLen ▸ hj) = some e →
          (e.key == k') = false := by
        intro j hj e hSlot
        by_contra hNF; simp only [Bool.not_eq_false] at hNF
        exact hAll j hj e hSlot hNF
      have hNone : (t.insert k v).get? k' = none := by
        unfold RHTable.get?; exact getLoop_none_of_absent _ _ _ _ _ _ _ _ hAbs
      rw [hNone] at hGet; simp at hGet
    obtain ⟨p', hp', e', hSlotP', hKeyP'⟩ := hPresent
    -- Step 3: e'.value = val (via insertLoop_output_source + noDupKeys)
    -- insertLoop_output_source says e' either has (key=k, value=v) or came from input
    have hSource := insertLoop_output_source (t.insert k v |>.capacity)
      (idealIndex k (t.insert k v |>.capacity) (t.insert k v |>.hCapPos))
      k v 0
    -- Actually, we need to unfold insert to apply insertLoop_output_source.
    -- The insert function is: t' = if resize_needed then t.resize else t; t'.insertNoResize k v
    -- insertNoResize calls insertLoop with fuel=t'.capacity, d=0.
    -- Let's use a simpler approach: apply insertLoop_output_source to the actual
    -- insertLoop call inside insert.
    have hVal : e'.value = val := by
      -- Unfold insert to get at the insertLoop call
      unfold RHTable.insert RHTable.insertNoResize at hSlotP'
      simp only [] at hSlotP'
      split at hSlotP'
      · -- Resize case
        have hResOrig := insertLoop_output_source (t.resize).capacity
          (idealIndex k (t.resize).capacity (t.resize).hCapPos) k v 0
          (t.resize).slots (t.resize).capacity (t.resize).hSlotsLen (t.resize).hCapPos
          p' (by simpa using hp') e' hSlotP'
        rcases hResOrig with ⟨hKeyK, hValV⟩ | ⟨q, hq, hSlotQ⟩
        · -- e' has key == k and value v. But e'.key == k' and k ≠ k'. Contradiction.
          exact absurd (BEq.beq_trans hKeyK.symm hKeyP') hNe
        · -- e' came from t.resize slots. So e' was in t.resize.
          -- By resize_preserves_key_absence: if k' absent from t, absent from t.resize.
          -- But k' IS present in t (at position p). Contrapositive doesn't directly help.
          -- We need: e' has same key and value as something in t.
          -- Actually, e' came from t.resize.slots[q] = some e'. And e'.key == k'.
          -- By noDupKeys of t (hExt.2.2.1): the only entry with key k' in t is eP at p.
          -- If we can show e' came from t (not just from t.resize), then e' = eP by noDupKeys.
          -- t.resize = fold over t.slots, inserting each entry. Each entry in t.resize
          -- came from the fold, which uses insertLoop. By insertLoop_output_source recursively,
          -- every entry in t.resize either was placed by an insertLoop (with key from t)
          -- or existed in a prior accumulator (which traces back to t's entries or earlier inserts).
          -- Ultimately, every entry in t.resize has key and value from some entry in t.
          -- The entry e' has key k', and the only entry with key k' in t has value val.
          -- So e'.value = val.
          -- To formalize this, use resize_output_source (similar to insertLoop_output_source
          -- but for the fold). Let me use a simpler argument:
          -- By insertLoop_output_source applied to the resize fold, every entry in t.resize
          -- has (key, value) from some original entry in t. The fold uses insertNoResize
          -- which uses insertLoop. By induction on the fold steps (Array.foldl_induction):
          -- each entry in the accumulator has (key, value) from t.
          -- Since e' has key k' and the only entry with key k' in t has value val,
          -- e'.value = val.
          -- This requires proving resize_output_source, which is complex.
          -- SIMPLER: since e' came from t.resize.slots[q] and e'.key == k', and
          -- t.resize satisfies invExt, we can use getLoop_finds_present on t.resize
          -- to get t.resize.get? k' = some e'.value. Then show t.resize.get? k' = t.get? k'.
          -- But that's what we're trying to prove (insert ≠ resize, but similar issue).
          -- ALTERNATIVE: use the fold induction directly. Every entry in t.resize has
          -- key and value matching some entry from t. This is a simple fold property.
          -- Let me prove: ∀ entry in t.resize.slots with key k', value = val.
          -- By Array.foldl_induction:
          -- Invariant: every entry in acc.slots with key k' has value val.
          -- Base: empty table has no entries. ✓
          -- Step: insertNoResize adds eOrig from t. If eOrig.key == k', then
          -- eOrig.value = val (by noDupKeys of t, eOrig.key == k' = eP.key, so eOrig = eP).
          -- By insertLoop_output_source on insertNoResize: entries with key k' either
          -- have (key=eOrig.key, value=eOrig.value) [if eOrig.key == k'] or came from acc
          -- [which by induction have value val].
          -- If eOrig.key ≠ k': entries with key k' in output came from acc → value val.
          -- If eOrig.key == k': new entry has value eOrig.value = val, and entries from
          -- acc also have value val. ✓
          -- This is clean but requires a fold induction. Let me write it inline.
          have hResVal : ∀ a (ha : a < (t.resize).capacity) (ea : RHEntry α β),
              (t.resize).slots[a]'((t.resize).hSlotsLen ▸ ha) = some ea →
              (ea.key == k') = true → ea.value = val := by
            unfold RHTable.resize RHTable.fold
            exact Array.foldl_induction
              (motive := fun _ (acc : RHTable α β) =>
                ∀ a (ha : a < acc.capacity) (ea : RHEntry α β),
                  acc.slots[a]'(acc.hSlotsLen ▸ ha) = some ea →
                  (ea.key == k') = true → ea.value = val)
              (by intro a ha ea hSlotA; simp [RHTable.empty] at hSlotA)
              (fun i acc hAcc => by
                match hSlotI : t.slots[i] with
                | none => exact hAcc
                | some eOrig =>
                  intro a ha ea hSlotA hKeyA
                  unfold RHTable.insertNoResize at hSlotA ha; simp only [] at hSlotA ha
                  have hOS := insertLoop_output_source acc.capacity
                    (idealIndex eOrig.key acc.capacity acc.hCapPos) eOrig.key eOrig.value 0
                    acc.slots acc.capacity acc.hSlotsLen acc.hCapPos a ha ea hSlotA
                  rcases hOS with ⟨hKeyO, hValO⟩ | ⟨q', hq', hSlotQ'⟩
                  · -- ea has key=eOrig.key, value=eOrig.value
                    -- ea.key == k' and ea.key = eOrig.key, so eOrig.key == k'.
                    -- By noDupKeys: eOrig at position i in t.slots, eP at position p.
                    -- Both have key k'. So i = p and eOrig = eP.
                    rw [hValO]
                    have hi : (i : Nat) < t.capacity := by rw [← t.hSlotsLen]; exact i.isLt
                    have hOrigSlot : t.slots[(i : Nat)]'(t.hSlotsLen ▸ hi) = some eOrig := hSlotI
                    have hKeyOrig : (eOrig.key == k') = true := by
                      have := eq_of_beq hKeyO; rw [this] at hKeyA; exact hKeyA
                    have := hExt.2.2.1 i p hi hp eOrig eP hOrigSlot hSlotP
                      (BEq.beq_trans hKeyOrig hKeyP.symm)
                    subst this
                    rw [hOrigSlot] at hSlotP; cases hSlotP
                    exact hValP.symm
                  · -- ea came from acc. By induction, ea.value = val.
                    exact hAcc q' hq' ea hSlotQ' hKeyA)
          exact hResVal q hq e' hSlotQ hKeyP'
      · -- No resize case
        have hOrigSrc := insertLoop_output_source t.capacity
          (idealIndex k t.capacity t.hCapPos) k v 0
          t.slots t.capacity t.hSlotsLen t.hCapPos
          p' (by simpa using hp') e' hSlotP'
        rcases hOrigSrc with ⟨hKeyK, hValV⟩ | ⟨q, hq, hSlotQ⟩
        · exact absurd (BEq.beq_trans hKeyK.symm hKeyP') hNe
        · -- e' = original entry at q with same key and value.
          -- e'.key == k' and the only entry with key k' in t is eP with value val.
          have hQP := hExt.2.2.1 q p hq hp e' eP hSlotQ hSlotP
            (BEq.beq_trans hKeyP' hKeyP.symm)
          subst hQP
          rw [hSlotQ] at hSlotP; cases hSlotP
          exact hValP.symm
    -- Step 4: use getLoop_finds_present on result table
    rw [hVal]
    unfold RHTable.get?
    have hDE := hInsExt.2.1 p' hp' e' hSlotP'
    have hKeyEq : idealIndex e'.key (t.insert k v).capacity (t.insert k v).hCapPos
        = idealIndex k' (t.insert k v).capacity (t.insert k v).hCapPos := by
      rw [eq_of_beq hKeyP']
    rw [hKeyEq] at hDE
    have hdk_lt : e'.dist < (t.insert k v).capacity := by
      have := Nat.mod_lt (p' + (t.insert k v).capacity -
        idealIndex k' (t.insert k v).capacity (t.insert k v).hCapPos) (t.insert k v).hCapPos
      omega
    exact getLoop_finds_present (t.insert k v).capacity
      (idealIndex k' (t.insert k v).capacity (t.insert k v).hCapPos) k' 0
      (t.insert k v).slots (t.insert k v).capacity (t.insert k v).hSlotsLen (t.insert k v).hCapPos
      p' hp' e' hSlotP' hKeyP' rfl
      hInsExt.2.1 hInsExt.2.2.2 hInsExt.2.2.1
      (by simp [Nat.mod_eq_of_lt (idealIndex_lt k' _ _)])
      (by omega) (by omega)

/-- N2-E3: After erasing key `k`, looking up `k` returns `none`.
    Proved via `getLoop_none_of_absent`: key `k` is not in the erased table
    (by `erase_removes_key`), so `getLoop` never finds it. -/
theorem RHTable.get_after_erase_eq [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) :
    (t.erase k).get? k = none := by
  unfold RHTable.get?
  exact getLoop_none_of_absent _ _ _ _ _ _ _ _
    (erase_removes_key t k hExt)

/-- Entries in `backshiftLoop` output came from the input (key/value preserved).
    Every occupied slot in the output has an ancestor in the input with the
    same key and value (only `dist` may change due to backward shift). -/
private theorem backshiftLoop_output_has_input_key_value [BEq α]
    (fuel gapIdx : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity) :
    ∀ q (hq : q < capacity) (e' : RHEntry α β),
      (backshiftLoop fuel gapIdx slots capacity hLen hCapPos)[q]'(by
        rw [backshiftLoop_preserves_len, hLen]; exact hq) = some e' →
      ∃ p, ∃ hp : p < capacity, ∃ e : RHEntry α β,
        slots[p]'(hLen ▸ hp) = some e ∧ e.key = e'.key ∧ e.value = e'.value := by
  induction fuel generalizing gapIdx slots hLen with
  | zero => simp [backshiftLoop]; intro q hq e' hSlot; exact ⟨q, hq, e', hSlot, rfl, rfl⟩
  | succ n ih =>
    have hGapI : gapIdx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hNextI : (gapIdx + 1) % capacity < slots.size := by
      rw [hLen]; exact Nat.mod_lt _ hCapPos
    intro q hq e' hSlot
    match hNext : slots[(gapIdx + 1) % capacity]'hNextI with
    | none =>
      simp [backshiftLoop, hNext] at hSlot
      exact ⟨q, hq, e', hSlot, rfl, rfl⟩
    | some nextE =>
      if hDist : nextE.dist == 0 then
        simp [backshiftLoop, hNext, hDist] at hSlot
        exact ⟨q, hq, e', hSlot, rfl, rfl⟩
      else
        have hDistF : (nextE.dist == 0) = false := by
          cases h : nextE.dist == 0 <;> simp_all
        simp only [backshiftLoop, hNext, hDistF, ↓reduceIte] at hSlot
        simp only [show (false = true) ↔ False from ⟨Bool.noConfusion, False.elim⟩,
          ite_false] at hSlot
        have hLen2 : ((slots.set (gapIdx % capacity)
            (some { nextE with dist := nextE.dist - 1 }) hGapI).set
            ((gapIdx + 1) % capacity) none
            (by rw [Array.size_set]; exact hNextI)).size = capacity := by
          rw [Array.size_set, Array.size_set]; exact hLen
        obtain ⟨p, hp, eOrig, hSlotOrig, hKeyEq, hValEq⟩ :=
          ih ((gapIdx + 1) % capacity) _ hLen2 q hq e' hSlot
        simp only [Array.getElem_set] at hSlotOrig
        split at hSlotOrig
        · simp at hSlotOrig
        · split at hSlotOrig
          · have hEq := Option.some.inj hSlotOrig
            rw [hEq] at hKeyEq hValEq; simp at hKeyEq hValEq
            exact ⟨(gapIdx + 1) % capacity, Nat.mod_lt _ hCapPos, nextE, hNext,
              hKeyEq.symm, hValEq.symm⟩
          · exact ⟨p, hp, eOrig, hSlotOrig, hKeyEq, hValEq⟩

/-- `backshiftLoop` preserves entry presence when the gap position is empty.
    If an entry exists at position `p` in the input and the gap slot is `none`,
    some entry with the same key and value exists in the output. -/
private theorem backshiftLoop_preserves_entry_presence [BEq α]
    (fuel gapIdx : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hGapNone : slots[gapIdx % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none)
    (p : Nat) (hp : p < capacity) (e : RHEntry α β)
    (hSlotP : slots[p]'(hLen ▸ hp) = some e) :
    ∃ q, ∃ hq : q < capacity, ∃ e' : RHEntry α β,
      (backshiftLoop fuel gapIdx slots capacity hLen hCapPos)[q]'(by
        rw [backshiftLoop_preserves_len, hLen]; exact hq) = some e' ∧
      e'.key = e.key ∧ e'.value = e.value := by
  have hpNeGap : p ≠ gapIdx % capacity := by
    intro hContra; rw [hContra] at hSlotP; rw [hSlotP] at hGapNone; simp at hGapNone
  induction fuel generalizing gapIdx slots hLen with
  | zero =>
    simp [backshiftLoop]
    exact ⟨p, hp, e, hSlotP, rfl, rfl⟩
  | succ n ih =>
    have hGapI : gapIdx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hNextI : (gapIdx + 1) % capacity < slots.size := by
      rw [hLen]; exact Nat.mod_lt _ hCapPos
    match hNext : slots[(gapIdx + 1) % capacity]'hNextI with
    | none =>
      simp [backshiftLoop, hNext]
      exact ⟨p, hp, e, hSlotP, rfl, rfl⟩
    | some nextE =>
      if hDist : nextE.dist == 0 then
        simp [backshiftLoop, hNext, hDist]
        exact ⟨p, hp, e, hSlotP, rfl, rfl⟩
      else
        have hDistF : (nextE.dist == 0) = false := by
          cases h : nextE.dist == 0 <;> simp_all
        have hLen2 : ((slots.set (gapIdx % capacity)
            (some { nextE with dist := nextE.dist - 1 }) hGapI).set
            ((gapIdx + 1) % capacity) none
            (by rw [Array.size_set]; exact hNextI)).size = capacity := by
          rw [Array.size_set, Array.size_set]; exact hLen
        have hNewGapNone :
            ((slots.set (gapIdx % capacity)
              (some { nextE with dist := nextE.dist - 1 }) hGapI).set
              ((gapIdx + 1) % capacity) none
              (by rw [Array.size_set]; exact hNextI))[(gapIdx + 1) % capacity]'(by
                rw [Array.size_set, Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos) =
            none := by simp [Array.getElem_set]
        by_cases hpNext : p = (gapIdx + 1) % capacity
        · have hEq : e = nextE := by
            rw [hpNext] at hSlotP; exact Option.some.inj (hSlotP.trans hNext.symm)
          have hShiftedSlot :
              ((slots.set (gapIdx % capacity)
                (some { nextE with dist := nextE.dist - 1 }) hGapI).set
                ((gapIdx + 1) % capacity) none
                (by rw [Array.size_set]; exact hNextI))[gapIdx % capacity]'(by
                  rw [Array.size_set, Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos) =
              some { nextE with dist := nextE.dist - 1 } := by
            simp only [Array.getElem_set]; split <;> simp [Array.getElem_set]
          obtain ⟨q, hq, e', hSlotQ, hKeyEq, hValEq⟩ :=
            ih ((gapIdx + 1) % capacity) _ hLen2 hNewGapNone (gapIdx % capacity)
              (Nat.mod_lt _ hCapPos) { nextE with dist := nextE.dist - 1 } hShiftedSlot
          exact ⟨q, hq, e', by
            rw [show backshiftLoop (n + 1) gapIdx slots capacity hLen hCapPos =
              backshiftLoop n ((gapIdx + 1) % capacity) _ capacity hLen2 hCapPos from by
                simp [backshiftLoop, hNext, hDistF]]
            exact hSlotQ, by rw [hKeyEq, hEq], by rw [hValEq, hEq]⟩
        · have hShiftedSlot :
              ((slots.set (gapIdx % capacity)
                (some { nextE with dist := nextE.dist - 1 }) hGapI).set
                ((gapIdx + 1) % capacity) none
                (by rw [Array.size_set]; exact hNextI))[p]'(by
                  rw [Array.size_set, Array.size_set, hLen]; exact hp) = some e := by
            simp only [Array.getElem_set, show p = (gapIdx + 1) % capacity ↔ False from
              ⟨fun h => hpNext h, False.elim⟩, show p = gapIdx % capacity ↔ False from
              ⟨fun h => hpNeGap h, False.elim⟩, ite_false]
            exact hSlotP
          obtain ⟨q, hq, e', hSlotQ, hKeyEq, hValEq⟩ :=
            ih ((gapIdx + 1) % capacity) _ hLen2 hNewGapNone p hp e hShiftedSlot
          exact ⟨q, hq, e', by
            rw [show backshiftLoop (n + 1) gapIdx slots capacity hLen hCapPos =
              backshiftLoop n ((gapIdx + 1) % capacity) _ capacity hLen2 hCapPos from by
                simp [backshiftLoop, hNext, hDistF]]
            exact hSlotQ, hKeyEq, hValEq⟩

/-- N3-B4 helper: Erasing key `k` preserves entries with different keys. -/
private theorem erase_preserves_ne_entry [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (hNe : ¬(k' == k) = true)
    (hExt : t.invExt)
    (p : Nat) (hp : p < t.capacity) (e : RHEntry α β)
    (hSlotP : t.slots[p]'(t.hSlotsLen ▸ hp) = some e)
    (hKey : (e.key == k') = true) :
    ∃ q, ∃ hq : q < (t.erase k).capacity, ∃ e' : RHEntry α β,
      (t.erase k).slots[q]'((t.erase k).hSlotsLen ▸ hq) = some e' ∧
      (e'.key == k') = true ∧ e'.value = e.value := by
  simp only [RHTable.erase]
  generalize hFind : findLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
    t.slots t.capacity t.hSlotsLen t.hCapPos = result
  cases result with
  | none => simp only []; exact ⟨p, hp, e, hSlotP, hKey, rfl⟩
  | some idx =>
    simp only []
    have hFound := hFind
    have hIdxS : idx % t.capacity < t.slots.size := by
      rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
    have hLen' : (t.slots.set (idx % t.capacity) none hIdxS).size = t.capacity := by
      rw [Array.size_set]; exact t.hSlotsLen
    have ⟨eFound, hSlotFound, hKeyFound⟩ := findLoop_correct t.capacity _ k 0
      t.slots t.capacity t.hSlotsLen t.hCapPos idx hFound
    have hpNeIdx : p ≠ idx % t.capacity := by
      intro hContra
      rw [hContra] at hSlotP; rw [hSlotP] at hSlotFound; cases hSlotFound
      exact hNe (BEq.beq_trans hKey hKeyFound)
    have hSlotP' : (t.slots.set (idx % t.capacity) none hIdxS)[p]'(by
        rw [Array.size_set, t.hSlotsLen]; exact hp) = some e := by
      simp [Array.getElem_set, hpNeIdx, hSlotP]
    have hGapNone : (t.slots.set (idx % t.capacity) none hIdxS)[idx % t.capacity]'(by
        rw [Array.size_set, t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos) = none := by
      simp [Array.getElem_set]
    obtain ⟨q, hq, e', hSlotQ, hKeyEq, hValEq⟩ :=
      backshiftLoop_preserves_entry_presence t.capacity idx
        (t.slots.set (idx % t.capacity) none hIdxS) t.capacity hLen' t.hCapPos
        hGapNone p hp e hSlotP'
    exact ⟨q, hq, e', hSlotQ, by rw [← hKeyEq]; exact hKey, hValEq.symm⟩

/-- N3-B4/N2-E4: Erasing key `k` does not affect lookups of other keys.
    If `¬(k == k')`, then `(t.erase k).get? k' = t.get? k'`. -/
theorem RHTable.get_after_erase_ne [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (hNe : ¬(k == k') = true)
    (hExt : t.invExt) (hSize : t.size < t.capacity) :
    (t.erase k).get? k' = t.get? k' := by
  have hEraseExt := t.erase_preserves_invExt k hExt hSize
  have hNe' : ¬(k' == k) = true := fun h => hNe (by rw [BEq.comm]; exact h)
  cases hGet : t.get? k' with
  | none =>
    have hAbsOrig : ∀ j (hj : j < t.capacity) (e : RHEntry α β),
        t.slots[j]'(t.hSlotsLen ▸ hj) = some e → (e.key == k') = false := by
      intro j hj e hSlot
      cases hKE : e.key == k' with
      | false => rfl
      | true =>
        exfalso
        have hde := hExt.2.1 j hj e hSlot
        have hKeyEq : idealIndex e.key t.capacity t.hCapPos =
            idealIndex k' t.capacity t.hCapPos := by rw [eq_of_beq hKE]
        rw [hKeyEq] at hde
        have hdk_lt : e.dist < t.capacity := by
          have := Nat.mod_lt (j + t.capacity - idealIndex k' t.capacity t.hCapPos) t.hCapPos
          omega
        have hFound := getLoop_finds_present t.capacity
          (idealIndex k' t.capacity t.hCapPos) k' 0 t.slots t.capacity
          t.hSlotsLen t.hCapPos j hj e hSlot hKE rfl
          hExt.2.1 hExt.2.2.2 hExt.2.2.1
          (by simp [Nat.mod_eq_of_lt (idealIndex_lt k' _ _)]) (by omega) (by omega)
        unfold RHTable.get? at hGet; rw [hFound] at hGet; simp at hGet
    have hAbsErased : ∀ j (hj : j < (t.erase k).capacity) (e : RHEntry α β),
        (t.erase k).slots[j]'((t.erase k).hSlotsLen ▸ hj) = some e →
        (e.key == k') = false := by
      intro j hj e hSlot
      simp only [RHTable.erase] at hSlot hj
      split at hSlot
      · exact hAbsOrig j hj e hSlot
      · rename_i idx hFound
        have hIdxS : idx % t.capacity < t.slots.size := by
          rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
        have hLen' : (t.slots.set (idx % t.capacity) none hIdxS).size = t.capacity := by
          rw [Array.size_set]; exact t.hSlotsLen
        obtain ⟨p, hp, eOrig, hSlotOrig, hKeyEq, _⟩ :=
          backshiftLoop_output_has_input_key_value t.capacity idx
            (t.slots.set (idx % t.capacity) none hIdxS) t.capacity hLen' t.hCapPos
            j hj e hSlot
        simp only [Array.getElem_set] at hSlotOrig
        split at hSlotOrig
        · simp at hSlotOrig
        · rw [← hKeyEq]; exact hAbsOrig p hp eOrig hSlotOrig
    unfold RHTable.get?
    exact getLoop_none_of_absent _ _ _ _ _ _ _ _ hAbsErased
  | some val =>
    obtain ⟨p, hp, e, hSlotP, hKey, hVal⟩ :=
      getLoop_some_implies_entry t.capacity _ k' 0 t.slots t.capacity t.hSlotsLen t.hCapPos
        val (by unfold RHTable.get? at hGet; exact hGet)
    obtain ⟨q, hq, e', hSlotQ, hKey', hVal'⟩ :=
      erase_preserves_ne_entry t k k' hNe' hExt p hp e hSlotP hKey
    have hVal'' : e'.value = val := by rw [hVal']; exact hVal.symm
    have hDE' := hEraseExt.2.1 q hq e' hSlotQ
    have hKeyEq : idealIndex e'.key (t.erase k).capacity (t.erase k).hCapPos =
        idealIndex k' (t.erase k).capacity (t.erase k).hCapPos := by
      rw [eq_of_beq hKey']
    rw [hKeyEq] at hDE'
    have hdk_lt : e'.dist < (t.erase k).capacity := by
      have := Nat.mod_lt (q + (t.erase k).capacity -
        idealIndex k' (t.erase k).capacity (t.erase k).hCapPos) (t.erase k).hCapPos
      omega
    unfold RHTable.get?
    exact getLoop_finds_present (t.erase k).capacity
      (idealIndex k' (t.erase k).capacity (t.erase k).hCapPos) k' 0
      (t.erase k).slots (t.erase k).capacity (t.erase k).hSlotsLen (t.erase k).hCapPos
      q hq e' hSlotQ hKey' hVal''
      hEraseExt.2.1 hEraseExt.2.2.2 hEraseExt.2.2.1
      (by simp [Nat.mod_eq_of_lt (idealIndex_lt k' _ _)])
      (by omega) (by omega)

end SeLe4n.Kernel.RobinHood
