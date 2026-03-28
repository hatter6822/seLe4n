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

/-- Array access depends only on the index, not the bound proof. -/
private theorem getElem_idx_eq (slots : Array (Option (RHEntry α β)))
    {i j : Nat} (hi : i < slots.size) (hj : j < slots.size) (heq : i = j) :
    slots[i]'hi = slots[j]'hj := by subst heq; rfl

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
private theorem getLoop_none_of_absent [BEq α] [Hashable α] [LawfulBEq α]
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
        simp [hKNe, hDist]
      else
        simp only [hKNe, hDist, ite_false]
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
        simp only [backshiftLoop, hNext, hDistF] at hSlot
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

/-- If `findLoop` returns `some idx`, then `slots[idx%cap]` has an entry
    with `key == k`. Proved by fuel induction. -/
private theorem findLoop_some_has_key [BEq α] [Hashable α] [LawfulBEq α]
    (fuel idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (result : Nat)
    (hResult : findLoop fuel idx k d slots capacity hLen hCapPos = some result) :
    ∃ e : RHEntry α β,
      slots[result % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e ∧
      (e.key == k) = true := by
  induction fuel generalizing idx d with
  | zero => simp [findLoop] at hResult
  | succ n ih =>
    unfold findLoop at hResult; simp only [] at hResult
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    split at hResult
    · -- none: findLoop returns none, contradicts hResult
      simp at hResult
    · rename_i e hSlot
      split at hResult
      · -- Key match: result = idx%cap, entry is e with e.key == k
        rename_i hKeyMatch
        have hRes : result = idx % capacity := Option.some.inj hResult.symm
        have hModEq : result % capacity = idx % capacity := by
          rw [hRes, Nat.mod_eq_of_lt (Nat.mod_lt _ hCapPos)]
        have hSlotEq := getElem_idx_eq slots
          (by rw [hLen]; exact Nat.mod_lt _ hCapPos) hIdx hModEq
        exact ⟨e, hSlotEq ▸ hSlot, hKeyMatch⟩
      · split at hResult
        · -- e.dist < d: findLoop returns none, contradicts hResult
          simp at hResult
        · -- Continue: recurse
          exact ih (idx % capacity + 1) (d + 1) hResult

/-- Key `k` is absent from the erased table: after `erase k`, no slot
    contains an entry with key `k`. -/
private theorem erase_removes_key [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) :
    ∀ j (hj : j < (t.erase k).capacity) (e : RHEntry α β),
      (t.erase k).slots[j]'(by rw [(t.erase k).hSlotsLen]; exact hj) = some e →
      (e.key == k) = false := by
  intro j hj e hSlot
  -- Unfold erase and case-split on findLoop result
  unfold RHTable.erase at hSlot hj
  simp only [] at hSlot hj
  -- let start := idealIndex k t.capacity t.hCapPos
  match hFind : findLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
      t.slots t.capacity t.hSlotsLen t.hCapPos with
  | none =>
    -- erase returns t unchanged; key k was already absent
    simp only [hFind] at hSlot hj
    have hAbsent := findLoop_none_implies_absent t.capacity
      (idealIndex k t.capacity t.hCapPos) k 0
      t.slots t.capacity t.hSlotsLen t.hCapPos
      hExt.2.1 hExt.2.2.2
      (by simp [idealIndex]) (by intro d' hd'; omega) (by omega) hFind
    exact hAbsent j hj e hSlot
  | some idx =>
    simp only [hFind] at hSlot hj
    -- findLoop found key k at idx; slots[idx%cap] has entry with key == k
    have ⟨eFound, hSlotFound, hKeyFound⟩ := findLoop_some_has_key t.capacity
      (idealIndex k t.capacity t.hCapPos) k 0
      t.slots t.capacity t.hSlotsLen t.hCapPos idx hFind
    have hIdxI : idx % t.capacity < t.slots.size := by
      rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
    -- Key k is absent from slots.set(idx%cap, none): the only slot with key k was idx%cap
    -- (by noDupKeys), and that slot is now none.
    have hLen' : (t.slots.set (idx % t.capacity) none hIdxI).size = t.capacity := by
      rw [Array.size_set]; exact t.hSlotsLen
    have hAbsent' : ∀ a (ha : a < t.capacity) (ea : RHEntry α β),
        (t.slots.set (idx % t.capacity) none hIdxI)[a]'(by rw [hLen']; exact ha) = some ea →
        (ea.key == k) = false := by
      intro a ha ea hA
      simp only [Array.getElem_set] at hA
      split at hA
      · simp at hA  -- slot set to none, contradiction
      · -- a ≠ idx%cap: ea from original slots
        rename_i hNeq
        cases hc : ea.key == k with
        | false => rfl
        | true =>
          exfalso
          -- ea.key == k and eFound.key == k, so ea.key == eFound.key
          have hBoth : (ea.key == eFound.key) = true := by
            rw [eq_of_beq hc, eq_of_beq hKeyFound]; exact BEq.refl k
          have := hExt.2.2.1 a (idx % t.capacity) ha (Nat.mod_lt _ t.hCapPos)
            ea eFound hA hSlotFound hBoth
          exact hNeq this.symm
    -- backshiftLoop preserves key absence
    exact backshiftLoop_preserves_key_absence t.capacity idx
      (t.slots.set (idx % t.capacity) none hIdxI) t.capacity hLen' t.hCapPos
      k hAbsent' j hj e hSlot

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
  | zero => simp at hFuel hDLe ⊢ <;> omega
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
    · -- At the target: idx % cap = p, so slots[idx%cap] = slots[p] = some e
      have hIdxP : idx % capacity = p := by
        have : (idealIndex k capacity hCapPos + d) % capacity =
               (idealIndex k capacity hCapPos + e.dist) % capacity := by rw [hDeq]
        rw [hRound, hpRound] at this; exact this
      have hSlotEq := getElem_idx_eq slots hIdxS (hLen ▸ hp) hIdxP
      rw [hSlotEq, hSlotP]; simp only [hKey, ite_true, hVal]
    · -- d < e.dist: PCD gives occupied slot at idx%cap with dist ≥ d
      have hDLt : d < e.dist := by omega
      have ⟨e', he', hge'⟩ := hPCD p hp e hSlotP d hDLt
      have hPosEq : (idealIndex e.key capacity hCapPos + d) % capacity = idx % capacity := by
        rw [hKeyEq]; exact hRound
      have he'Idx := getElem_idx_eq slots
        (by rw [hLen]; exact Nat.mod_lt _ hCapPos) hIdxS hPosEq
      rw [he'Idx] at he'
      -- slots[idx%cap] = some e' with e'.dist ≥ d; resolve the match
      rw [he']
      -- e'.key ≠ k (otherwise idx%cap = p → d = e.dist, contradiction)
      have hKeyNe : (e'.key == k) = false := by
        cases hc : e'.key == k with
        | false => rfl
        | true =>
          exfalso
          have hBothK : (e'.key == e.key) = true := by
            rw [eq_of_beq hc, eq_of_beq hKey]; exact BEq.refl k
          have hIdxEqP := hNoDup (idx % capacity) p hIdxMod hp e' e he' hSlotP hBothK
          rw [hIdxEqP] at hD; exact hDeq (hD.trans hEDist.symm)
      simp only [hKeyNe]
      -- e'.dist ≥ d so the dist < d branch is false
      have hDistGe : ¬(e'.dist < d) := by omega
      simp only [hDistGe, ite_false]
      -- Recursive case with advanced position
      have hD' : d + 1 = ((idx % capacity + 1) % capacity + capacity -
          idealIndex k capacity hCapPos) % capacity :=
        disp_step' (idx % capacity) (idealIndex k capacity hCapPos) capacity
          hCapPos hIdxMod (idealIndex_lt k capacity hCapPos) d hD (by omega)
      exact ih (idx % capacity + 1) (d + 1) hD' (by omega) (by omega)

/-- `insertLoop` never modifies slots unreachable within its fuel window.
    If position `j` cannot be reached from `idx` in fewer than `fuel` steps
    (modular), then `slots'[j] = slots[j]`. -/
private theorem insertLoop_preserves_slot [BEq α] [Hashable α] [LawfulBEq α]
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
        simp only [hKey, hRH, ite_true]
        have hLen' : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx).size = capacity := by
          rw [Array.size_set]; exact hLen
        have hNR' : ∀ s, s < n → (idx % capacity + 1 + s) % capacity ≠ j := by
          intro s hs
          have h := hNR (s + 1) (by omega)
          rw [show idx % capacity + 1 + s = idx % capacity + (s + 1) from by omega,
              mod_add_mod_eq]; exact h
        exact (ih (idx % capacity + 1) e.key e.value (e.dist + 1) _ hLen' hNR').trans
          (by rw [Array.getElem_set]; simp [hjNe])
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
    provided the table has a reachable empty slot within the probe window. -/
private theorem insertLoop_places_key [BEq α] [Hashable α] [LawfulBEq α]
    (fuel : Nat) (idx : Nat) (k : α) (v : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hBound : d + fuel ≤ capacity)
    (hRoom : ∃ s, s < fuel ∧
      slots[(idx + s) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none) :
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
        by simp, BEq.refl k, rfl⟩
    | some e =>
      simp only [insertLoop, hSlot]
      by_cases hKey : e.key == k
      · simp only [hKey, ite_true]
        exact ⟨idx % capacity, hIdxCap, { e with value := v },
          by simp, hKey, rfl⟩
      · simp only [show (e.key == k) = false from by simp [hKey]]
        -- Room at (idx+s)%cap is none. s ≥ 1 since idx%cap is some e (not none).
        obtain ⟨s, hs, hRoomNone⟩ := hRoom
        have hs_pos : 1 ≤ s := by
          by_cases h0 : s = 0
          · exfalso; subst h0
            have hEq : (idx + 0) % capacity = idx % capacity := by simp
            have := getElem_idx_eq slots (by rw [hLen]; exact Nat.mod_lt _ hCapPos) hIdx hEq
            rw [this] at hRoomNone; rw [hSlot] at hRoomNone; exact absurd hRoomNone (by simp)
          · omega
        -- Position (idx+s)%cap ≠ idx%cap since 1 ≤ s < capacity
        have hNeq : (idx + s) % capacity ≠ idx % capacity := by
          intro heq
          have hIdxM := Nat.mod_lt idx hCapPos
          have hsMod : s % capacity = s := Nat.mod_eq_of_lt (by omega)
          -- (idx + s) % cap = idx % cap. Rewrite using mod_add_mod_eq:
          -- (idx%cap + s) % cap = (idx + s) % cap = idx % cap
          have h1 : (idx % capacity + s) % capacity = idx % capacity := by
            rw [mod_add_mod_eq]; exact heq
          by_cases hWrap : idx % capacity + s < capacity
          · rw [Nat.mod_eq_of_lt hWrap] at h1; omega
          · rw [show idx % capacity + s = (idx % capacity + s - capacity) + capacity
              from by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega : idx % capacity + s - capacity < capacity)] at h1
            omega
        by_cases hRH : e.dist < d
        · simp only [if_pos hRH]
          -- Robin Hood swap: insert displaced e into set array
          have hLen' : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx).size =
              capacity := by rw [Array.size_set]; exact hLen
          -- Room for IH: at (idx%cap+1+(s-1))%cap in the set array = none
          have hPosEq : (idx % capacity + 1 + (s - 1)) % capacity =
              (idx + s) % capacity := by
            rw [show idx % capacity + 1 + (s - 1) = idx % capacity + s from by omega]
            rw [mod_add_mod_eq]
          have hRoomIH : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[
              (idx % capacity + 1 + (s - 1)) % capacity]'(by
                rw [Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos)
              = none := by
            have hEq := getElem_idx_eq
              (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)
              (by rw [Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos)
              (by rw [Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos)
              hPosEq
            rw [hEq]; simp only [Array.getElem_set]
            split
            · rename_i hAbs; exact absurd hAbs.symm hNeq
            · exact hRoomNone
          -- The entry ⟨k, v, d⟩ is at idx%cap in the set array.
          -- It survives the recursive insertLoop (starts at idx%cap+1, can't reach idx%cap).
          have hNR : ∀ s', s' < n → (idx % capacity + 1 + s') % capacity ≠ idx % capacity := by
            intro s' hs'
            intro heq'
            -- (idx%cap + 1 + s') % cap = idx%cap → (1 + s') % cap = 0
            have h1 : (idx % capacity + (1 + s')) % capacity = idx % capacity := by
              rw [show idx % capacity + 1 + s' = idx % capacity + (1 + s') from by omega] at heq'
              exact heq'
            have hIdxM := Nat.mod_lt idx hCapPos
            have hSmall : 1 + s' < capacity := by omega
            rw [show idx % capacity + (1 + s') = idx % capacity + (1 + s') from rfl] at h1
            by_cases hW : idx % capacity + (1 + s') < capacity
            · rw [Nat.mod_eq_of_lt hW] at h1; omega
            · rw [show idx % capacity + (1 + s') =
                (idx % capacity + (1 + s') - capacity) + capacity from by omega,
                Nat.add_mod_right,
                Nat.mod_eq_of_lt (by omega)] at h1; omega
          have hPreserved := insertLoop_preserves_slot n
            (idx % capacity + 1) e.key e.value (e.dist + 1)
            (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)
            capacity hLen' hCapPos (idx % capacity) hIdxCap hNR
          -- Set array has ⟨k, v, d⟩ at idx%cap
          have hSetEntry : (slots.set (idx % capacity) (some ⟨k, v, d⟩) hIdx)[
              idx % capacity]'(by rw [Array.size_set]; exact hIdx) =
              some ⟨k, v, d⟩ := by simp
          -- After insertLoop, still there
          refine ⟨idx % capacity, hIdxCap, ⟨k, v, d⟩, ?_, BEq.refl k, rfl⟩
          -- Simplify remaining if-then-else from key check
          simp only [Bool.false_eq_true, ite_false]
          rw [hPreserved]; exact hSetEntry
        · simp only [if_neg hRH]
          -- Continue probing: same array, advance position
          have hPosEq : (idx % capacity + 1 + (s - 1)) % capacity =
              (idx + s) % capacity := by
            rw [show idx % capacity + 1 + (s - 1) = idx % capacity + s from by omega]
            rw [mod_add_mod_eq]
          have hRoomIH : slots[(idx % capacity + 1 + (s - 1)) % capacity]'(by
              rw [hLen]; exact Nat.mod_lt _ hCapPos) = none := by
            rw [getElem_idx_eq slots
              (by rw [hLen]; exact Nat.mod_lt _ hCapPos)
              (by rw [hLen]; exact Nat.mod_lt _ hCapPos)
              hPosEq]
            exact hRoomNone
          exact ih (idx % capacity + 1) k v (d + 1) slots hLen (by omega)
            ⟨s - 1, by omega, hRoomIH⟩

/-- If every element of a list satisfies `p`, then `countP p = length`. -/
private theorem List.countP_eq_length {p : α → Bool} :
    ∀ (l : List α), (∀ i (hi : i < l.length), p (l.get ⟨i, hi⟩) = true) →
    l.countP p = l.length
  | [], _ => rfl
  | hd :: tl, hAll => by
    simp only [List.countP_cons, List.length_cons]
    have hhd := hAll 0 (by simp)
    simp at hhd; rw [hhd]; simp only [ite_true]
    have hTail := List.countP_eq_length tl (fun i hi => by
      have := hAll (i + 1) (by simp; omega)
      simpa using this)
    omega

/-- If `countP isSome < length`, some element is `none`. -/
private theorem list_exists_none_of_countP_lt :
    ∀ (l : List (Option γ)),
    l.countP (·.isSome) < l.length →
    ∃ i, ∃ hi : i < l.length, l.get ⟨i, hi⟩ = none
  | [], h => by simp at h
  | none :: _, _ => ⟨0, by simp, rfl⟩
  | some a :: tl, h => by
    have hLen : (some a :: tl).length = tl.length + 1 := rfl
    have hCnt : (some a :: tl).countP (·.isSome) = tl.countP (·.isSome) + 1 := by
      simp
    rw [hLen, hCnt] at h
    have hTl : tl.countP (·.isSome) < tl.length := by omega
    have ⟨i, hi, hNone⟩ := list_exists_none_of_countP_lt tl hTl
    exact ⟨i + 1, by omega, by simp only [List.get_cons_succ]; exact hNone⟩

/-- If `countOccupied slots < capacity`, there exists an empty slot. -/
private theorem exists_empty_slot
    (slots : Array (Option (RHEntry α β))) (cap : Nat)
    (hLen : slots.size = cap) (_hCapPos : 0 < cap)
    (hLt : countOccupied slots < cap) :
    ∃ j, ∃ hj : j < cap, slots[j]'(hLen ▸ hj) = none := by
  have hLL : slots.toList.length = cap := by rw [Array.length_toList, hLen]
  have hCntLt : slots.toList.countP (·.isSome) < slots.toList.length := by
    unfold countOccupied at hLt; rw [hLL]; exact hLt
  have ⟨i, hi, hNone⟩ := list_exists_none_of_countP_lt slots.toList hCntLt
  have hI : i < cap := hLL ▸ hi
  have hIS : i < slots.size := hLen ▸ hI
  refine ⟨i, hI, ?_⟩
  have : slots.toList.get ⟨i, hi⟩ = slots[i]'hIS := by
    simp [Array.getElem_toList]
  rwa [this] at hNone

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
    rw [← mod_add_mod_eq, show idx % cap + (j - idx % cap) = j from by omega,
        Nat.mod_eq_of_lt hj]
  · simp only [Nat.not_le] at hge
    have hb1 : j + cap - idx % cap < cap := by omega
    rw [Nat.mod_eq_of_lt hb1, ← mod_add_mod_eq]
    by_cases hlt : idx % cap + (j + cap - idx % cap) < cap
    · omega
    · simp only [Nat.not_lt] at hlt
      have hb2 : idx % cap + (j + cap - idx % cap) - cap < cap := by omega
      rw [show idx % cap + (j + cap - idx % cap) =
        (idx % cap + (j + cap - idx % cap) - cap) + cap from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hb2]
      omega

/-- Resize size is bounded by the number of slots processed (≤ t.capacity). -/
private theorem resize_size_le_capacity [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) : t.resize.size ≤ t.capacity :=
  t.hSlotsLen ▸ (show t.resize.size ≤ t.slots.size from by
    unfold RHTable.resize RHTable.fold
    exact Array.foldl_induction
      (motive := fun (idx : Nat) (acc : RHTable α β) => acc.size ≤ idx)
      (Nat.le_refl 0)
      (fun i acc hAcc => by
        split
        · exact Nat.le_succ_of_le hAcc
        · exact Nat.le_trans (acc.insertNoResize_size_le _ _)
            (Nat.succ_le_succ hAcc)))

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
      have hRSL := resize_size_le_capacity t
      have hCP := t.hCapPos
      -- t.resize.size ≤ t.capacity < 2 * t.capacity (since capacity > 0)
      omega
    -- There exists an empty slot in t'
    have ⟨j, hj, hjNone⟩ := exists_empty_slot t'.slots t'.capacity t'.hSlotsLen t'.hCapPos
      (by rw [← hExt'.1.sizeCount]; exact hSizeLt)
    -- That slot is reachable from idealIndex k within capacity steps
    have ⟨s, hs, hsEq⟩ := position_reachable (idealIndex k t'.capacity t'.hCapPos) j
      t'.capacity t'.hCapPos hj
    -- Build hRoom for insertLoop_places_key
    have hRoom : ∃ s, s < t'.capacity ∧
        t'.slots[(idealIndex k t'.capacity t'.hCapPos + s) % t'.capacity]'(by
          rw [t'.hSlotsLen]; exact Nat.mod_lt _ t'.hCapPos) = none :=
      ⟨s, hs, by simp only [hsEq]; exact hjNone⟩
    -- Apply insertLoop_places_key
    unfold RHTable.insertNoResize; simp only []
    exact insertLoop_places_key t'.capacity
      (idealIndex k t'.capacity t'.hCapPos) k v 0
      t'.slots t'.capacity t'.hSlotsLen t'.hCapPos
      (by omega) hRoom
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
        t.slots[(idealIndex k t.capacity t.hCapPos + s) % t.capacity]'(by
          rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos) = none :=
      ⟨s, hs, by simp only [hsEq]; exact hjNone⟩
    unfold RHTable.insertNoResize; simp only []
    exact insertLoop_places_key t.capacity
      (idealIndex k t.capacity t.hCapPos) k v 0
      t.slots t.capacity t.hSlotsLen t.hCapPos
      (by omega) hRoom

/-- N2-E1: After inserting key `k` with value `v`, looking up `k` returns `v`.
    This is the fundamental correctness theorem for Robin Hood insertion.

    **U8-E/U-M35: Hash collision assumption.** This theorem (and its companion
    `get_after_erase_eq`) rely on `LawfulBEq α`, which ensures that `BEq`
    agrees with propositional equality. The proofs do NOT assume absence of
    hash collisions — Robin Hood open addressing handles collisions correctly
    via probe-chain displacement. However, the `Hashable` instance is assumed
    to be deterministic (same key always produces the same hash). Hash
    collision resistance is not formally modeled because the kernel uses typed
    identifiers (`ObjId`, `ThreadId`, `SlotRef`, etc.) as keys, which are
    system-assigned monotonic IDs — not adversary-controlled inputs. For
    adversarial key sets, a collision-resistant hash function would be needed,
    but this is outside the kernel's threat model. -/
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
        simp only [hKey, hRH, ite_true] at hSlot
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
private theorem getLoop_some_implies_entry [BEq α] [Hashable α] [LawfulBEq α]
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
          have := hAbsent i hi eOrig hSlotI
          simp [this]
        intro j hj e hSlot
        have hSlot' := hSlot
        have hj' := hj
        unfold RHTable.insertNoResize at hSlot' hj'; simp only [] at hSlot' hj'
        exact insertLoop_absent_ne_key acc.capacity
          (idealIndex eOrig.key acc.capacity acc.hCapPos) eOrig.key eOrig.value 0
          acc.slots acc.capacity acc.hSlotsLen acc.hCapPos k' hOrigAbs hAcc j hj' e hSlot')

/-- Every entry in the output of `insertLoop` either has (key = kIns, value = vIns)
    or has the same key and value as some entry in the input slots.
    (The `dist` field may differ due to Robin Hood displacement.) -/
private theorem insertLoop_output_source [BEq α] [Hashable α] [LawfulBEq α]
    (fuel idx : Nat) (kIns : α) (vIns : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity) :
    ∀ j (hj : j < capacity) (e : RHEntry α β),
      (insertLoop fuel idx kIns vIns d slots capacity hLen hCapPos).1[j]'(by
        rw [insertLoop_preserves_len, hLen]; exact hj) = some e →
      ((e.key == kIns) = true ∧ e.value = vIns) ∨
      (∃ q, ∃ hq : q < capacity, ∃ eOrig : RHEntry α β,
        slots[q]'(hLen ▸ hq) = some eOrig ∧ eOrig.key = e.key ∧ eOrig.value = e.value) := by
  induction fuel generalizing idx kIns vIns d slots hLen with
  | zero =>
    intro j hj e hSlot; simp [insertLoop] at hSlot
    exact Or.inr ⟨j, hj, e, hSlot, rfl, rfl⟩
  | succ n ih =>
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    intro j hj e hSlotR
    cases hSlot : slots[idx % capacity]'hIdx with
    | none =>
      simp only [insertLoop, hSlot] at hSlotR
      simp only [Array.getElem_set] at hSlotR
      split at hSlotR
      · cases hSlotR; exact Or.inl ⟨BEq.refl kIns, rfl⟩
      · exact Or.inr ⟨j, hj, e, hSlotR, rfl, rfl⟩
    | some eOld =>
      simp only [insertLoop, hSlot] at hSlotR
      if hKey : eOld.key == kIns then
        simp only [hKey, ite_true] at hSlotR
        simp only [Array.getElem_set] at hSlotR
        split at hSlotR
        · -- Updated entry: key = eOld.key (== kIns), value = vIns
          cases hSlotR
          exact Or.inl ⟨hKey, rfl⟩
        · exact Or.inr ⟨j, hj, e, hSlotR, rfl, rfl⟩
      else if hRH : eOld.dist < d then
        simp only [hKey, hRH, ite_true] at hSlotR
        have hLen' : (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx).size
            = capacity := by rw [Array.size_set]; exact hLen
        have hIH := ih (idx % capacity + 1) eOld.key eOld.value (eOld.dist + 1)
          (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx) hLen'
          j hj e hSlotR
        rcases hIH with ⟨hKeyE, hValE⟩ | ⟨q, hq, eOrig, hSlotQ, hKeyOrig, hValOrig⟩
        · -- Entry has key == eOld.key and value == eOld.value.
          -- eOld was in original slots at idx%cap — witness it.
          exact Or.inr ⟨idx % capacity, Nat.mod_lt _ hCapPos, eOld, hSlot,
            eq_of_beq hKeyE ▸ rfl, hValE ▸ rfl⟩
        · -- Entry from slots' (set array). Check if q = idx%cap.
          simp only [Array.getElem_set] at hSlotQ
          split at hSlotQ
          · -- q = idx%cap: eOrig = ⟨kIns, vIns, d⟩
            cases hSlotQ; exact Or.inl ⟨hKeyOrig ▸ BEq.refl kIns, hValOrig ▸ rfl⟩
          · -- q ≠ idx%cap: eOrig from original slots
            exact Or.inr ⟨q, hq, eOrig, hSlotQ, hKeyOrig, hValOrig⟩
      else
        simp only [hKey, ite_false, hRH, ite_false] at hSlotR
        exact ih (idx % capacity + 1) kIns vIns (d + 1) slots hLen j hj e hSlotR

/-- If `get? k = none` under `invExt`, then key `k` is absent from all slots.
    Contrapositive: if any slot had `e.key == k`, then `getLoop_finds_present`
    would return `some`, contradicting `none`. -/
private theorem get_none_implies_absent [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) (hNone : t.get? k = none) :
    ∀ j (hj : j < t.capacity) (e : RHEntry α β),
      t.slots[j]'(t.hSlotsLen ▸ hj) = some e → (e.key == k) = false := by
  intro j hj e hSlot
  cases hc : e.key == k with
  | false => rfl
  | true =>
    exfalso
    -- e at position j has key == k. getLoop_finds_present should give some.
    have hDist := hExt.2.1 j hj e hSlot
    have hKeyEq : idealIndex e.key t.capacity t.hCapPos = idealIndex k t.capacity t.hCapPos := by
      rw [eq_of_beq hc]
    rw [hKeyEq] at hDist
    have hdk_lt : e.dist < t.capacity := by
      have := Nat.mod_lt (j + t.capacity - idealIndex k t.capacity t.hCapPos) t.hCapPos; omega
    unfold RHTable.get? at hNone
    have hSome := getLoop_finds_present t.capacity
      (idealIndex k t.capacity t.hCapPos) k 0
      t.slots t.capacity t.hSlotsLen t.hCapPos
      j hj e hSlot hc rfl hExt.2.1 hExt.2.2.2 hExt.2.2.1
      (by simp [Nat.mod_eq_of_lt (idealIndex_lt k _ _)])
      (by omega) (by omega)
    rw [hSome] at hNone; exact absurd hNone (by simp)

/-- `insertNoResize` preserves key absence for different keys. -/
private theorem insertNoResize_absent_ne_key [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (k' : α) (hNe : ¬(k == k') = true)
    (hAbsent : ∀ j (hj : j < t.capacity) (e : RHEntry α β),
      t.slots[j]'(t.hSlotsLen ▸ hj) = some e → (e.key == k') = false) :
    ∀ j (hj : j < (t.insertNoResize k v).capacity) (e : RHEntry α β),
      (t.insertNoResize k v).slots[j]'((t.insertNoResize k v).hSlotsLen ▸ hj) = some e →
      (e.key == k') = false := by
  unfold RHTable.insertNoResize; simp only []
  exact insertLoop_absent_ne_key t.capacity
    (idealIndex k t.capacity t.hCapPos) k v 0
    t.slots t.capacity t.hSlotsLen t.hCapPos k' hNe hAbsent

/-- `insert` preserves key absence for different keys. -/
private theorem insert_absent_ne_key [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (k' : α) (hNe : ¬(k == k') = true)
    (hAbsent : ∀ j (hj : j < t.capacity) (e : RHEntry α β),
      t.slots[j]'(t.hSlotsLen ▸ hj) = some e → (e.key == k') = false) :
    ∀ j (hj : j < (t.insert k v).capacity) (e : RHEntry α β),
      (t.insert k v).slots[j]'((t.insert k v).hSlotsLen ▸ hj) = some e →
      (e.key == k') = false := by
  unfold RHTable.insert; simp only []
  split
  · -- Resize case
    exact insertNoResize_absent_ne_key t.resize k v k' hNe
      (resize_preserves_key_absence t k' hAbsent)
  · -- No resize case
    exact insertNoResize_absent_ne_key t k v k' hNe hAbsent


private theorem insertLoop_preserves_ne_entry_new [BEq α] [Hashable α] [LawfulBEq α]
    (fuel : Nat) (idx : Nat) (kIns : α) (vIns : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity) (hCapPos : 0 < capacity)
    (hNoDup : ∀ i j (hi : i < capacity) (hj : j < capacity) (ei ej : RHEntry α β),
      slots[i]'(by rw [hLen]; exact hi) = some ei →
      slots[j]'(by rw [hLen]; exact hj) = some ej →
      (ei.key == ej.key) = true → i = j)
    (hDistC : ∀ j (hj : j < capacity) (e : RHEntry α β),
      slots[j]'(by rw [hLen]; exact hj) = some e →
      e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity)
    (hPCD : probeChainDominant slots capacity hLen hCapPos)
    (hD : d = (idx % capacity + capacity - idealIndex kIns capacity hCapPos) % capacity)
    (hBound : d + fuel ≤ capacity)
    (hChainOK : ∀ d', d' < d →
      ∃ e', slots[(idealIndex kIns capacity hCapPos + d') % capacity]'(by
        rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' ∧ e'.dist ≥ d')
    (hNotFound : ∀ d', d' < d →
      ∀ e', slots[(idealIndex kIns capacity hCapPos + d') % capacity]'(by
        rw [hLen]; exact Nat.mod_lt _ hCapPos) = some e' → (e'.key == kIns) = false)
    (hRoom : ∃ s, s < fuel ∧
      slots[(idx + s) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos) = none)
    (k' : α) (hNeIns : ¬(kIns == k') = true)
    (p' : Nat) (hp' : p' < capacity) (e' : RHEntry α β)
    (hSlotP' : slots[p']'(by rw [hLen]; exact hp') = some e')
    (hKey' : (e'.key == k') = true) :
    ∃ q, ∃ hq : q < capacity, ∃ e'' : RHEntry α β,
      (insertLoop fuel idx kIns vIns d slots capacity hLen hCapPos).1[q]'(by
        rw [insertLoop_preserves_len, hLen]; exact hq) = some e'' ∧
      (e''.key == k') = true ∧ e''.value = e'.value := by
  induction fuel generalizing idx kIns vIns d slots hLen with
  | zero => exact ⟨p', hp', e', hSlotP', hKey', rfl⟩
  | succ n ih =>
    have hIdx : idx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hIdxCap : idx % capacity < capacity := Nat.mod_lt _ hCapPos
    have hRtD : (idealIndex kIns capacity hCapPos + d) % capacity = idx % capacity :=
      displacement_roundtrip' (idx % capacity) (idealIndex kIns capacity hCapPos) capacity
        hCapPos hIdxCap (idealIndex_lt kIns capacity hCapPos) d hD (by omega)
    cases hSlotCase : slots[idx % capacity]'hIdx with
    | none =>
      simp only [insertLoop, hSlotCase]
      have hNeP : p' ≠ idx % capacity := by
        intro h
        have h1 := getElem_idx_eq slots (by rw [hLen]; exact hp') hIdx h
        rw [hSlotP'] at h1; rw [hSlotCase] at h1; exact absurd h1 (by simp)
      have hNeP2 : ¬(idx % capacity = p') := fun h => hNeP h.symm
      refine ⟨p', hp', e', ?_, hKey', rfl⟩
      show (slots.set _ _ _)[p']'_ = some e'
      simp only [Array.getElem_set, hNeP2, ite_false]; exact hSlotP'
    | some eOld =>
      if hKey : eOld.key == kIns then
        simp only [insertLoop, hSlotCase, hKey, ite_true]
        have hNeP : p' ≠ idx % capacity := by
          intro h
          have h1 := getElem_idx_eq slots (by rw [hLen]; exact hp') hIdx h
          have h2 : some eOld = some e' := hSlotCase.symm.trans (h1.symm.trans hSlotP')
          have : eOld = e' := Option.some.inj h2
          rw [this] at hKey
          exact hNeIns (by rw [← eq_of_beq hKey', ← eq_of_beq hKey]; exact beq_self_eq_true e'.key)
        have hNeP2 : ¬(idx % capacity = p') := fun h => hNeP h.symm
        refine ⟨p', hp', e', ?_, hKey', rfl⟩
        show (slots.set _ _ _)[p']'_ = some e'
        simp only [Array.getElem_set, hNeP2, ite_false]; exact hSlotP'
      else
        have hKeyF : (eOld.key == kIns) = false := Bool.eq_false_iff.mpr hKey
        if hRH : eOld.dist < d then
          simp only [insertLoop, hSlotCase, hKeyF, Bool.false_eq_true, ↓reduceIte, if_pos hRH]
          have hLen' : (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx).size
              = capacity := by rw [Array.size_set]; exact hLen
          by_cases hpEq : p' = idx % capacity
          · -- p' = idx%cap: e' = eOld, Robin Hood re-places it
            have hEO : eOld = e' := by
              have h1 : slots[p']'(by rw [hLen]; exact hp') = slots[idx % capacity]'hIdx :=
                getElem_idx_eq slots (by rw [hLen]; exact hp') hIdx hpEq
              have h2 : some eOld = some e' := hSlotCase.symm.trans (h1.symm.trans hSlotP')
              exact Option.some.inj h2
            -- eOld gets re-inserted by the recursive insertLoop call
            obtain ⟨s, hs, hRoomNone⟩ := hRoom
            have hs_pos : 1 ≤ s := by
              by_cases hs0 : s = 0
              · exfalso; subst hs0; simp only [Nat.add_zero] at hRoomNone
                rw [hSlotCase] at hRoomNone; exact absurd hRoomNone (by simp)
              · omega
            have hPosEq : (idx % capacity + 1 + (s - 1)) % capacity = (idx + s) % capacity := by
              rw [show idx % capacity + 1 + (s - 1) = idx % capacity + s from by omega]
              rw [mod_add_mod_eq]
            have hNeq : (idx + s) % capacity ≠ idx % capacity := by
              intro heq
              have h1 : (idx % capacity + s) % capacity = idx % capacity := by
                rw [mod_add_mod_eq]; exact heq
              by_cases hW : idx % capacity + s < capacity
              · rw [Nat.mod_eq_of_lt hW] at h1; omega
              · rw [show idx % capacity + s = (idx % capacity + s - capacity) + capacity
                  from by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h1; omega
            have hRoomSet : (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)[
                (idx % capacity + 1 + (s - 1)) % capacity]'(by
                  rw [Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos) = none := by
              rw [getElem_idx_eq (slots.set _ _ _)
                (by rw [Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos)
                (by rw [Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos) hPosEq]
              simp only [Array.getElem_set]; split
              · rename_i hAbs; exact absurd hAbs (Ne.symm hNeq)
              · exact hRoomNone
            have ⟨q, hqC, eR, hSlotR, hKeyR, hValR⟩ := insertLoop_places_key n
              (idx % capacity + 1) eOld.key eOld.value (eOld.dist + 1)
              (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)
              capacity hLen' hCapPos (by omega) ⟨s - 1, by omega, hRoomSet⟩
            exact ⟨q, hqC, eR, hSlotR,
              by rw [eq_of_beq hKeyR, hEO, eq_of_beq hKey']; exact beq_self_eq_true k',
              by rw [hValR, hEO]⟩
          · -- p' ≠ idx%cap: entry survives in set array, apply IH
            have hSlotP'Set : (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)[p']'(by
                rw [Array.size_set, hLen]; exact hp') = some e' := by
              simp only [Array.getElem_set]
              have hNeP2 : ¬(idx % capacity = p') := fun h => hpEq h.symm
              simp only [hNeP2, ite_false]; exact hSlotP'
            have hOldNeK' : ¬(eOld.key == k') = true := by
              intro hContra
              exact hpEq (hNoDup (idx % capacity) p' hIdxCap hp' eOld e' hSlotCase hSlotP'
                (by rw [eq_of_beq hContra, eq_of_beq hKey']; exact BEq.refl k')).symm
            -- noDupKeys for set array
            have hKAbs := carried_key_absent slots capacity hLen hCapPos kIns d
              (idx % capacity) hIdxCap hD hDistC hPCD hNotFound
              (.inr ⟨eOld, hSlotCase, hRH, hKeyF⟩)
            have hNoDup' : ∀ i j (hi : i < capacity) (hj : j < capacity) (ei ej : RHEntry α β),
                (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)[i]'(by rw [hLen']; exact hi) = some ei →
                (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)[j]'(by rw [hLen']; exact hj) = some ej →
                (ei.key == ej.key) = true → i = j := by
              intro i' j' hi' hj' ei' ej' hI' hJ' hKE'
              simp only [Array.getElem_set] at hI' hJ'
              split at hI' <;> split at hJ'
              · rename_i h1 h2; exact h1 ▸ h2 ▸ rfl
              · rename_i h1 hbN; cases hI'
                exact absurd (hKAbs j' hj' ej' hJ')
                  (by have := eq_of_beq hKE'; simp [this.symm])
              · rename_i haN h2; cases hJ'
                exact absurd (hKAbs i' hi' ei' hI')
                  (by have := eq_of_beq hKE'; simp [this])
              · exact hNoDup i' j' hi' hj' ei' ej' hI' hJ' hKE'
            -- distCorrect for set array
            have hDistC' : ∀ j (hj : j < capacity) (e : RHEntry α β),
                (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)[j]'(by rw [hLen']; exact hj) = some e →
                e.dist = (j + capacity - idealIndex e.key capacity hCapPos) % capacity := by
              intro j' hj' eJ hSlotJ
              simp only [Array.getElem_set] at hSlotJ
              split at hSlotJ
              · rename_i hEq; cases hSlotJ; rw [← hEq]; exact hD
              · exact hDistC j' hj' eJ hSlotJ
            -- PCD for set array
            have hChainNe : ∀ dd', dd' < d →
                (idealIndex kIns capacity hCapPos + dd') % capacity ≠ idx % capacity := by
              intro dd' hdd' hEq'
              exact absurd (offset_injective' (idealIndex kIns capacity hCapPos) capacity
                dd' d hCapPos (by omega) (by omega) (hEq'.trans hRtD.symm)) (by omega)
            have hPCD' : probeChainDominant
                (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx) capacity hLen' hCapPos := by
              intro p hp eP hSlotP dd hdd
              simp only [Array.getElem_set] at hSlotP ⊢
              split at hSlotP
              · rename_i hpEq'; cases hSlotP
                have hNe' := hChainNe dd hdd
                split
                · rename_i hEq'; exact absurd hEq'.symm hNe'
                · exact hChainOK dd hdd
              · obtain ⟨e'', he'', hge''⟩ := hPCD p hp eP hSlotP dd hdd
                if hChEq : (idealIndex eP.key capacity hCapPos + dd) % capacity = idx % capacity then
                  split
                  · refine ⟨⟨kIns, vIns, d⟩, rfl, ?_⟩
                    have h12 := getElem_idx_eq slots
                      (by rw [hLen]; exact Nat.mod_lt _ hCapPos) hIdx hChEq
                    have h13 : some e'' = some eOld := (he''.symm.trans h12).trans hSlotCase
                    rw [Option.some.inj h13] at hge''
                    exact Nat.le_of_lt (Nat.lt_of_le_of_lt hge'' hRH)
                  · exact absurd hChEq.symm (by assumption)
                else
                  split
                  · exact absurd (by assumption) (Ne.symm hChEq)
                  · exact ⟨e'', he'', hge''⟩
            -- hD' for displaced entry
            have hEdist := hDistC _ hIdxCap eOld hSlotCase
            have hSmall : eOld.dist + 1 < capacity := by omega
            have hD' := disp_step' _ _ _ hCapPos hIdxCap
              (idealIndex_lt eOld.key capacity hCapPos) eOld.dist hEdist hSmall
            -- hNotFound' for displaced entry
            have hNotFound' : ∀ d', d' < eOld.dist + 1 →
                ∀ eF, (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)[
                  (idealIndex eOld.key capacity hCapPos + d') % capacity]'(by
                    rw [hLen']; exact Nat.mod_lt _ hCapPos) = some eF →
                (eF.key == eOld.key) = false := by
              intro d' hd' eF hSlotF
              simp only [Array.getElem_set] at hSlotF
              split at hSlotF
              · cases hSlotF; show (kIns == eOld.key) = false
                exact Bool.eq_false_iff.mpr (fun h => hKey (eq_of_beq h ▸ beq_self_eq_true eOld.key))
              · show (eF.key == eOld.key) = false
                exact Bool.eq_false_iff.mpr (fun h =>
                  absurd (hNoDup _ _ (Nat.mod_lt _ hCapPos) hIdxCap eF eOld hSlotF hSlotCase h)
                    (Ne.symm (by assumption)))
            -- hChainOK' for displaced entry
            have hChainOK' : ∀ d', d' < eOld.dist + 1 →
                ∃ eC, (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)[
                  (idealIndex eOld.key capacity hCapPos + d') % capacity]'(by
                    rw [hLen']; exact Nat.mod_lt _ hCapPos) = some eC ∧ eC.dist ≥ d' := by
              intro d' hd'
              by_cases hd'lt : d' < eOld.dist
              · obtain ⟨eC, heC, hgeC⟩ := hPCD _ hIdxCap eOld hSlotCase d' hd'lt
                simp only [Array.getElem_set]
                have hd'_lt_d : d' < d := Nat.lt_trans hd'lt hRH
                if hEq : (idealIndex eOld.key capacity hCapPos + d') % capacity = idx % capacity then
                  split
                  · exact ⟨⟨kIns, vIns, d⟩, rfl, Nat.le_of_lt hd'_lt_d⟩
                  · rename_i hNe; exact absurd hEq.symm hNe
                else
                  split
                  · rename_i hEq2; exact absurd hEq2 (Ne.symm hEq)
                  · exact ⟨eC, heC, hgeC⟩
              · -- d' = eOld.dist: the entry itself at idx%cap (now replaced with kIns)
                have hd'eq : d' = eOld.dist := by omega
                rw [hd'eq]
                simp only [Array.getElem_set]
                have hRtE : (idealIndex eOld.key capacity hCapPos + eOld.dist) % capacity =
                    idx % capacity := by
                  exact displacement_roundtrip' (idx % capacity) (idealIndex eOld.key capacity hCapPos)
                    capacity hCapPos hIdxCap (idealIndex_lt eOld.key capacity hCapPos) eOld.dist
                    hEdist (by omega)
                split
                · exact ⟨⟨kIns, vIns, d⟩, rfl, Nat.le_of_lt hRH⟩
                · rename_i hNe; exact absurd hRtE.symm hNe
            -- hRoom' for recursive call
            obtain ⟨s, hs, hRoomNone⟩ := hRoom
            have hs_pos : 1 ≤ s := by
              by_cases hs0 : s = 0
              · exfalso; subst hs0; simp only [Nat.add_zero] at hRoomNone
                rw [hSlotCase] at hRoomNone; exact absurd hRoomNone (by simp)
              · omega
            have hPosEqR : (idx % capacity + 1 + (s - 1)) % capacity = (idx + s) % capacity := by
              rw [show idx % capacity + 1 + (s - 1) = idx % capacity + s from by omega]
              rw [mod_add_mod_eq]
            have hNeqR : (idx + s) % capacity ≠ idx % capacity := by
              intro heq
              have h1 : (idx % capacity + s) % capacity = idx % capacity := by
                rw [mod_add_mod_eq]; exact heq
              by_cases hW : idx % capacity + s < capacity
              · rw [Nat.mod_eq_of_lt hW] at h1; omega
              · rw [show idx % capacity + s = (idx % capacity + s - capacity) + capacity
                  from by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h1; omega
            have hRoomSet' : (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)[
                (idx % capacity + 1 + (s - 1)) % capacity]'(by
                  rw [Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos) = none := by
              rw [getElem_idx_eq (slots.set _ _ _)
                (by rw [Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos)
                (by rw [Array.size_set, hLen]; exact Nat.mod_lt _ hCapPos) hPosEqR]
              simp only [Array.getElem_set]; split
              · exact absurd (by assumption) (Ne.symm hNeqR)
              · exact hRoomNone
            have hBoundRH : (eOld.dist + 1) + n ≤ capacity := by omega
            have hRoomRH : ∃ s, s < n ∧
                (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx)[
                  (idx % capacity + 1 + s) % capacity]'(by rw [hLen']; exact Nat.mod_lt _ hCapPos)
                = none := ⟨s - 1, by omega, hRoomSet'⟩
            exact ih (idx % capacity + 1) eOld.key eOld.value (eOld.dist + 1)
              (slots.set (idx % capacity) (some ⟨kIns, vIns, d⟩) hIdx) hLen'
              hNoDup' hDistC' hPCD' hD' hBoundRH hChainOK' hNotFound' hRoomRH
              hOldNeK' hSlotP'Set
        else
          -- Continue probing: same array, advance position
          simp only [insertLoop, hSlotCase, hKeyF, Bool.false_eq_true, ↓reduceIte, if_neg hRH]
          obtain ⟨s, hs, hRoomNone⟩ := hRoom
          have hs_pos : 1 ≤ s := by
            by_cases hs0 : s = 0
            · exfalso; subst hs0
              simp only [Nat.add_zero] at hRoomNone
              rw [hSlotCase] at hRoomNone; exact absurd hRoomNone (by simp)
            · omega
          have hPosEq' : (idx % capacity + 1 + (s - 1)) % capacity = (idx + s) % capacity := by
            rw [show idx % capacity + 1 + (s - 1) = idx % capacity + s from by omega]
            rw [mod_add_mod_eq]
          have hRoomIH : slots[(idx % capacity + 1 + (s - 1)) % capacity]'(by
              rw [hLen]; exact Nat.mod_lt _ hCapPos) = none := by
            rw [getElem_idx_eq slots
              (by rw [hLen]; exact Nat.mod_lt _ hCapPos)
              (by rw [hLen]; exact Nat.mod_lt _ hCapPos)
              hPosEq']
            exact hRoomNone
          have hSmallC : d + 1 < capacity := by
            have : ¬ eOld.dist < d := hRH; have := hDistC _ hIdxCap eOld hSlotCase; omega
          have hD'C := disp_step' _ _ _ hCapPos hIdxCap
            (idealIndex_lt kIns capacity hCapPos) d hD hSmallC
          have hChainOK'C : ∀ d', d' < d + 1 →
              ∃ eC, slots[(idealIndex kIns capacity hCapPos + d') % capacity]'(by
                rw [hLen]; exact Nat.mod_lt _ hCapPos) = some eC ∧ eC.dist ≥ d' := by
            intro d' hd'
            by_cases hd'_lt : d' < d
            · exact hChainOK d' hd'_lt
            · have hd'_eq : d' = d := by omega
              rw [hd'_eq]
              refine ⟨eOld, ?_, by omega⟩
              have h1 := getElem_idx_eq slots (by rw [hLen]; exact Nat.mod_lt _ hCapPos) hIdx hRtD
              rw [h1]; exact hSlotCase
          have hNotFound'C : ∀ d', d' < d + 1 →
              ∀ eF, slots[(idealIndex kIns capacity hCapPos + d') % capacity]'(by
                rw [hLen]; exact Nat.mod_lt _ hCapPos) = some eF → (eF.key == kIns) = false := by
            intro d' hd' eF hSlotF
            by_cases hd'_lt : d' < d
            · exact hNotFound d' hd'_lt eF hSlotF
            · have hd'_eq : d' = d := by omega
              rw [hd'_eq] at hSlotF
              have h1 := getElem_idx_eq slots (by rw [hLen]; exact Nat.mod_lt _ hCapPos) hIdx hRtD
              have hSlotEq : some eF = some eOld := (hSlotF.symm.trans h1).trans hSlotCase
              rw [Option.some.inj hSlotEq]; exact hKeyF
          have hBound' : (d + 1) + n ≤ capacity := by omega
          have hSm1 : s - 1 < n := by omega
          have hRoom' : ∃ s, s < n ∧
              slots[(idx % capacity + 1 + s) % capacity]'(by rw [hLen]; exact Nat.mod_lt _ hCapPos)
              = none := ⟨s - 1, hSm1, hRoomIH⟩
          exact ih (idx % capacity + 1) kIns vIns (d + 1) slots hLen
            hNoDup hDistC hPCD hD'C hBound' hChainOK'C hNotFound'C hRoom'
            hNeIns hSlotP'


private theorem resize_preserves_entry [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k' : α) (v' : β)
    (p : Nat) (hp : p < t.capacity) (e : RHEntry α β)
    (hSlotP : t.slots[p]'(t.hSlotsLen ▸ hp) = some e)
    (hKey : (e.key == k') = true) (hVal : e.value = v')
    (hExt : t.invExt) :
    ∃ q, ∃ hq : q < t.resize.capacity, ∃ e' : RHEntry α β,
      t.resize.slots[q]'(t.resize.hSlotsLen ▸ hq) = some e' ∧
      (e'.key == k') = true ∧ e'.value = v' := by
  unfold RHTable.resize RHTable.fold
  exact (Array.foldl_induction
    (motive := fun (i : Nat) (acc : RHTable α β) =>
      acc.invExt ∧ acc.size ≤ i ∧ acc.capacity = t.capacity * 2 ∧
      (p < i → ∃ q, ∃ hq : q < acc.capacity, ∃ e' : RHEntry α β,
        acc.slots[q]'(acc.hSlotsLen ▸ hq) = some e' ∧
        (e'.key == k') = true ∧ e'.value = v'))
    ⟨RHTable.empty_invExt _ _, Nat.le_refl 0, by simp [RHTable.empty], fun h => absurd h (by omega)⟩
    (fun i acc ⟨hAccExt, hAccSize, hAccCap, hAccEntry⟩ => by
      have hi : (i : Nat) < t.capacity := by rw [← t.hSlotsLen]; exact i.isLt
      have hAccSizeLt : acc.size < acc.capacity := by
        rw [hAccCap]; have := hAccSize; have := hi; have := t.hCapPos; omega
      match hSlotI : t.slots[i] with
      | none =>
        refine ⟨hAccExt, Nat.le_succ_of_le hAccSize, hAccCap, fun h => ?_⟩
        have hpNe : p ≠ (i : Nat) := by
          intro hpeq
          have h1 := getElem_idx_eq t.slots i.isLt (t.hSlotsLen ▸ hp) hpeq.symm
          have h2 : none = some e := (hSlotI.symm.trans h1).trans hSlotP
          exact absurd h2 (by simp)
        exact hAccEntry (by omega)
      | some eOrig =>
        have hAccExt' := acc.insertNoResize_preserves_invExt eOrig.key eOrig.value hAccExt
        have hAccSize' : (acc.insertNoResize eOrig.key eOrig.value).size ≤ i.val + 1 :=
          Nat.le_trans (acc.insertNoResize_size_le _ _) (Nat.succ_le_succ hAccSize)
        have hAccCap' : (acc.insertNoResize eOrig.key eOrig.value).capacity =
            t.capacity * 2 := by rw [RHTable.insertNoResize_capacity]; exact hAccCap
        refine ⟨hAccExt', hAccSize', hAccCap', fun hpLt => ?_⟩
        by_cases hpi : p = (i : Nat)
        · -- This step inserts the target entry
          have hEOrig : eOrig = e := by
            have h1 := getElem_idx_eq t.slots i.isLt (t.hSlotsLen ▸ hp) hpi.symm
            have h2 : some eOrig = some e := (hSlotI.symm.trans h1).trans hSlotP
            exact Option.some.inj h2
          rw [hEOrig]
          -- insertNoResize places the entry
          have ⟨j, hj, hjNone⟩ := exists_empty_slot acc.slots acc.capacity
            acc.hSlotsLen acc.hCapPos (by rw [← hAccExt.1.sizeCount]; exact hAccSizeLt)
          have ⟨sR, hsR, hsREq⟩ := position_reachable
            (idealIndex e.key acc.capacity acc.hCapPos) j acc.capacity acc.hCapPos hj
          unfold RHTable.insertNoResize; simp only []
          have ⟨q, hq, eR, hSlotR, hKeyR, hValR⟩ := insertLoop_places_key acc.capacity
            (idealIndex e.key acc.capacity acc.hCapPos) e.key e.value 0
            acc.slots acc.capacity acc.hSlotsLen acc.hCapPos (by omega)
            ⟨sR, hsR, by simp only [hsREq]; exact hjNone⟩
          exact ⟨q, hq, eR, hSlotR,
            by rw [eq_of_beq hKeyR, eq_of_beq hKey]; exact beq_self_eq_true k',
            hValR ▸ hVal⟩
        · -- Entry already in acc, show it survives insertNoResize
          have hpLtI : p < i.val := by omega
          obtain ⟨q, hq, eQ, hSlotQ, hKeyQ, hValQ⟩ := hAccEntry hpLtI
          have hOrigNeK' : ¬(eOrig.key == k') = true := by
            intro hContra
            -- Use noDupKeys to show i = p, contradicting hpi
            exact hpi (hExt.2.2.1 (i : Nat) p hi hp eOrig e hSlotI hSlotP
              (by rw [eq_of_beq hContra, eq_of_beq hKey]; exact BEq.refl k')).symm
          -- Use insertLoop_preserves_ne_entry_new to show the entry survives
          have ⟨jE, hjE, hjENone⟩ := exists_empty_slot acc.slots acc.capacity
            acc.hSlotsLen acc.hCapPos (by rw [← hAccExt.1.sizeCount]; exact hAccSizeLt)
          have ⟨sE, hsE, hsEEq⟩ := position_reachable
            (idealIndex eOrig.key acc.capacity acc.hCapPos) jE acc.capacity acc.hCapPos hjE
          unfold RHTable.insertNoResize; simp only []
          have hD0 : 0 = (idealIndex eOrig.key acc.capacity acc.hCapPos % acc.capacity +
              acc.capacity - idealIndex eOrig.key acc.capacity acc.hCapPos) % acc.capacity := by
            simp [Nat.mod_eq_of_lt (idealIndex_lt eOrig.key _ _)]
          have hRoom0 : ∃ sR, sR < acc.capacity ∧
              acc.slots[(idealIndex eOrig.key acc.capacity acc.hCapPos + sR) % acc.capacity]'(by
                rw [acc.hSlotsLen]; exact Nat.mod_lt _ acc.hCapPos) = none :=
            ⟨sE, hsE, by simp only [hsEEq]; exact hjENone⟩
          have ⟨q2, hq2, e2, hSlot2, hKey2, hVal2⟩ :=
            insertLoop_preserves_ne_entry_new acc.capacity
              (idealIndex eOrig.key acc.capacity acc.hCapPos) eOrig.key eOrig.value 0
              acc.slots acc.capacity acc.hSlotsLen acc.hCapPos
              hAccExt.2.2.1 hAccExt.2.1 hAccExt.2.2.2
              hD0 (by omega)
              (by intro d' hd'; omega) (by intro d' hd'; omega)
              hRoom0
              k' hOrigNeK' q hq eQ hSlotQ hKeyQ
          exact ⟨q2, hq2, e2, hSlot2, hKey2, hVal2.trans hValQ⟩)
    ).2.2.2 (by rw [t.hSlotsLen]; exact hp)

/-- `insert` preserves entries with different keys at the table level. -/
private theorem insert_preserves_ne_entry [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (v : β) (hNe : ¬(k == k') = true)
    (hExt : t.invExt)
    (p : Nat) (hp : p < t.capacity) (e : RHEntry α β)
    (hSlotP : t.slots[p]'(t.hSlotsLen ▸ hp) = some e)
    (hKey : (e.key == k') = true) :
    ∃ q, ∃ hq : q < (t.insert k v).capacity, ∃ e' : RHEntry α β,
      (t.insert k v).slots[q]'((t.insert k v).hSlotsLen ▸ hq) = some e' ∧
      (e'.key == k') = true ∧ e'.value = e.value := by
  -- Strategy: insertLoop either doesn't reach position p (entry unchanged via
  -- insertLoop_preserves_slot) or reaches it and displaces e (entry placed
  -- via insertLoop_places_key). Both paths preserve key k' with value e.value.
  --
  -- At the top level, insert = (resize_or_not).insertNoResize k v.
  -- insertNoResize calls insertLoop with fuel = capacity and start = idealIndex k.
  -- The probe window starts at idealIndex(k) and advances. Position p is either
  -- in the probe window or not.
  --
  -- If p NOT in probe window: insertLoop_preserves_slot gives slots[p] unchanged.
  -- If p IN probe window: the entry at p is either:
  --   (a) key match (e.key == k) — but e.key == k' ≠ k, contradiction
  --   (b) Robin Hood displaced — insertLoop_places_key gives the displaced entry
  --       (with key == e.key == k') somewhere in the output
  --   (c) skipped (e.dist ≥ d) — entry unchanged at p
  --
  -- The detailed proof requires unfolding insert and tracking the probe path.
  -- Use insert_has_key to get invExt-derived facts, then insertLoop_output_source
  -- to identify which case applies.
  --
  -- SIMPLEST APPROACH: use the output table's invExt. Since the output has invExt
  -- and insertLoop_output_source tells us every output entry has key==k or key/value
  -- from input, we need to show k' EXISTS in output. We use a slot-counting argument:
  -- insertLoop produces at least as many occupied slots as the input (it only adds
  -- or updates, never removes). Combined with noDupKeys, if k' were absent, we'd
  -- have fewer unique non-k keys than the input, but the same or more total entries.
  -- Since noDupKeys bounds entries ≤ unique keys, this gives a contradiction.
  --
  -- Actually, the simplest path: use the already-proved fact that insertLoop
  -- ONLY modifies slots within its probe window (insertLoop_preserves_slot).
  -- If p is outside the window, the entry is trivially preserved.
  -- If p is inside the window, the entry is displaced and re-inserted via
  -- insertLoop_places_key.
  --
  -- Prove: entry at p with key k' survives insert. Two cases based on whether
  -- the insertLoop probe touches position p.
  -- e.key ≠ k
  have hNeK : ¬(e.key == k) = true := by
    intro hc; exact hNe (by rw [← eq_of_beq hKey, ← eq_of_beq hc]; exact BEq.refl e.key)
  -- Factor: suffices for any table t' with invExt containing entry with key k'
  -- at position p, t'.insertNoResize k v preserves it.
  -- Helper: for a table with invExt + size < capacity, insertNoResize preserves ne entry.
  suffices hHelper : ∀ (t' : RHTable α β) (hExt' : t'.invExt)
      (hSizeLt : t'.size < t'.capacity)
      (p' : Nat) (hp' : p' < t'.capacity) (e' : RHEntry α β)
      (hSlotP' : t'.slots[p']'(t'.hSlotsLen ▸ hp') = some e')
      (hKey' : (e'.key == k') = true),
      ∃ q, ∃ hq : q < (t'.insertNoResize k v).capacity, ∃ e'' : RHEntry α β,
        (t'.insertNoResize k v).slots[q]'((t'.insertNoResize k v).hSlotsLen ▸ hq) = some e'' ∧
        (e''.key == k') = true ∧ e''.value = e'.value by
    unfold RHTable.insert; simp only []
    split
    · -- Resize case
      rename_i hResize
      -- t.resize has invExt
      have hResExt := t.resize_preserves_invExt (α := α) (β := β)
      -- t.resize.size < t.resize.capacity (resize doubles capacity)
      have hResSizeLt : t.resize.size < t.resize.capacity := by
        have hSB := hResExt.1.sizeBound
        have hResizeCap := t.resize_fold_capacity
        have hRSL := resize_size_le_capacity t
        have hCP := t.hCapPos; omega
      -- Entry with key k' exists in t.resize (by resize re-inserting all entries)
      -- resize = fold over t.slots, inserting each entry into empty table
      -- The entry e with key k' at position p gets re-inserted during fold.
      -- By insertLoop_output_source on the resize's insertNoResize calls,
      -- the entry survives. But proving this requires tracking through the fold.
      -- Use a simpler argument: by resize_preserves_key_absence (contrapositive),
      -- if k' present in t, it's present in resize. But we need the positive direction.
      -- Actually: resize_preserves_key_absence says absent→absent. We need present→present.
      -- This faces the SAME problem as the main theorem.
      -- However, resize is already proved to preserve invExt, and we can use
      -- Use resize_preserves_entry to show entry survives resize, then hHelper
      have ⟨qR, hqR, eR, hSlotR, hKeyR, hValR⟩ :=
        resize_preserves_entry t k' e.value p hp e hSlotP hKey rfl hExt
      have ⟨q2, hq2, e2, hSlot2, hKey2, hVal2⟩ :=
        hHelper t.resize hResExt hResSizeLt qR hqR eR hSlotR hKeyR
      exact ⟨q2, hq2, e2, hSlot2, hKey2, hVal2.trans hValR⟩
    · -- No resize case
      rename_i hNoResize
      simp only [Nat.not_le] at hNoResize
      have hSizeLt : t.size < t.capacity := by have := hExt.1.sizeBound; omega
      exact hHelper t hExt hSizeLt p hp e hSlotP hKey
  -- Prove the helper: insertNoResize preserves ne entry using insertLoop_preserves_ne_entry_new
  intro t' hExt' hSizeLt p' hp' e' hSlotP' hKey'
  unfold RHTable.insertNoResize; simp only []
  have ⟨j, hj, hjNone⟩ := exists_empty_slot t'.slots t'.capacity t'.hSlotsLen t'.hCapPos
    (by rw [← hExt'.1.sizeCount]; exact hSizeLt)
  have ⟨s, hs, hsEq⟩ := position_reachable (idealIndex k t'.capacity t'.hCapPos) j
    t'.capacity t'.hCapPos hj
  have hRoom : ∃ s, s < t'.capacity ∧
      t'.slots[(idealIndex k t'.capacity t'.hCapPos + s) % t'.capacity]'(by
        rw [t'.hSlotsLen]; exact Nat.mod_lt _ t'.hCapPos) = none :=
    ⟨s, hs, by simp only [hsEq]; exact hjNone⟩
  exact insertLoop_preserves_ne_entry_new t'.capacity
    (idealIndex k t'.capacity t'.hCapPos) k v 0
    t'.slots t'.capacity t'.hSlotsLen t'.hCapPos
    hExt'.2.2.1 hExt'.2.1 hExt'.2.2.2
    (by simp [Nat.mod_eq_of_lt (idealIndex_lt k _ _)])
    (by omega)
    (by intro d' hd'; omega) (by intro d' hd'; omega)
    hRoom k' hNe p' hp' e' hSlotP' hKey'

/-- N2-E2: Inserting key `k` does not affect lookups of other keys.
    This ensures insert doesn't corrupt existing mappings. -/
theorem RHTable.get_after_insert_ne [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (v : β) (hNe : ¬(k == k') = true)
    (hExt : t.invExt) :
    (t.insert k v).get? k' = t.get? k' := by
  -- Case split on t.get? k'
  cases hGet : t.get? k' with
  | none =>
    -- k' absent from original → absent from insert → getLoop returns none
    have hAbsent := get_none_implies_absent t k' hExt hGet
    have hAbsent' := insert_absent_ne_key t k v k' hNe hAbsent
    unfold RHTable.get?
    exact getLoop_none_of_absent _ _ _ _ _ _ _ _ hAbsent'
  | some val =>
    -- k' present at some slot in original
    have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := getLoop_some_implies_entry
      t.capacity (idealIndex k' t.capacity t.hCapPos) k' 0
      t.slots t.capacity t.hSlotsLen t.hCapPos val (by unfold RHTable.get? at hGet; exact hGet)
    -- Entry survives insert
    have ⟨q, hq, e', hSlotQ, hKeyQ, hValQ⟩ := insert_preserves_ne_entry t k k' v hNe hExt
      p hp e hSlotP hKeyE
    -- The output table satisfies invExt
    have hInsExt := t.insert_preserves_invExt k v hExt
    -- getLoop_finds_present on the output table
    unfold RHTable.get?
    exact getLoop_finds_present (t.insert k v).capacity
      (idealIndex k' (t.insert k v).capacity (t.insert k v).hCapPos)
      k' 0 (t.insert k v).slots (t.insert k v).capacity
      (t.insert k v).hSlotsLen (t.insert k v).hCapPos
      q hq e' hSlotQ hKeyQ (hValQ.trans hValE)
      hInsExt.2.1 hInsExt.2.2.2 hInsExt.2.2.1
      (by simp [Nat.mod_eq_of_lt (idealIndex_lt k' _ _)])
      (by
        have hd := hInsExt.2.1 q hq e' hSlotQ
        have hKeyEq : idealIndex e'.key (t.insert k v).capacity (t.insert k v).hCapPos =
            idealIndex k' (t.insert k v).capacity (t.insert k v).hCapPos := by
          rw [eq_of_beq hKeyQ]
        rw [hKeyEq] at hd
        have := Nat.mod_lt (q + (t.insert k v).capacity -
          idealIndex k' (t.insert k v).capacity (t.insert k v).hCapPos) (t.insert k v).hCapPos
        omega)
      (by omega)

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
  | zero =>
    -- fuel = 0: backshiftLoop returns slots unchanged
    simp [backshiftLoop]
    intro q hq e' hSlot
    exact ⟨q, hq, e', hSlot, rfl, rfl⟩
  | succ n ih =>
    have hGapI : gapIdx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hNextI : (gapIdx + 1) % capacity < slots.size := by
      rw [hLen]; exact Nat.mod_lt _ hCapPos
    intro q hq e'
    match hNext : slots[(gapIdx + 1) % capacity]'hNextI with
    | none =>
      simp [backshiftLoop, hNext]
      intro hSlot; exact ⟨q, hq, e', hSlot, rfl, rfl⟩
    | some nextE =>
      if hDist : nextE.dist == 0 then
        simp [backshiftLoop, hNext, hDist]
        intro hSlot; exact ⟨q, hq, e', hSlot, rfl, rfl⟩
      else
        have hDistF : (nextE.dist == 0) = false := by cases h : nextE.dist == 0 <;> simp_all
        simp only [backshiftLoop, hNext, hDistF]
        simp only [show (false = true) ↔ False from ⟨Bool.noConfusion, False.elim⟩,
          ite_false]
        have hLen2 : ((slots.set (gapIdx % capacity)
            (some { nextE with dist := nextE.dist - 1 }) hGapI).set
            ((gapIdx + 1) % capacity) none
            (by rw [Array.size_set]; exact hNextI)).size = capacity := by
          rw [Array.size_set, Array.size_set]; exact hLen
        intro hSlot
        -- By IH: e' came from the double-set array
        have ⟨p', hp', eM, hSlotM, hKeyM, hValM⟩ := ih ((gapIdx + 1) % capacity)
          _ hLen2 q hq e' hSlot
        -- Track eM back to original slots through two sets
        simp only [Array.getElem_set] at hSlotM
        split at hSlotM
        · simp at hSlotM  -- p' = nextI: set to none, contradiction
        · -- p' ≠ nextI: hSlotM is about inner set
          split at hSlotM
          · rename_i hEqGap; cases hSlotM
            exact ⟨(gapIdx + 1) % capacity, Nat.mod_lt _ hCapPos, nextE,
              hNext, by rw [← hKeyM], by rw [← hValM]⟩
          · exact ⟨p', hp', eM, hSlotM, hKeyM, hValM⟩

/-- If an entry exists in the pre-backshift slots, then after backshift,
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
  induction fuel generalizing gapIdx slots hLen p e with
  | zero =>
    simp [backshiftLoop]; exact ⟨p, hp, e, hSlotP, rfl, rfl⟩
  | succ n ih =>
    have hGapI : gapIdx % capacity < slots.size := by rw [hLen]; exact Nat.mod_lt _ hCapPos
    have hNextI : (gapIdx + 1) % capacity < slots.size := by
      rw [hLen]; exact Nat.mod_lt _ hCapPos
    -- p ≠ gapIdx%cap (gap is none, but slots[p] = some e)
    have hpNeGap : p ≠ gapIdx % capacity := by
      intro heq
      have h1 := getElem_idx_eq slots (hLen ▸ hp) hGapI heq
      have : some e = none := (hSlotP.symm.trans h1).trans hGapNone
      exact absurd this (by simp)
    match hNext : slots[(gapIdx + 1) % capacity]'hNextI with
    | none =>
      simp [backshiftLoop, hNext]; exact ⟨p, hp, e, hSlotP, rfl, rfl⟩
    | some nextE =>
      if hDist : nextE.dist == 0 then
        simp [backshiftLoop, hNext, hDist]; exact ⟨p, hp, e, hSlotP, rfl, rfl⟩
      else
        have hDistF : (nextE.dist == 0) = false := by cases h : nextE.dist == 0 <;> simp_all
        simp only [backshiftLoop, hNext, hDistF]
        simp only [show (false = true) ↔ False from ⟨Bool.noConfusion, False.elim⟩, ite_false]
        -- Double-set: set gapIdx%cap to {nextE with dist-1}, set (gapIdx+1)%cap to none
        have hLen2 : ((slots.set (gapIdx % capacity)
            (some { nextE with dist := nextE.dist - 1 }) hGapI).set
            ((gapIdx + 1) % capacity) none
            (by rw [Array.size_set]; exact hNextI)).size = capacity := by
          rw [Array.size_set, Array.size_set]; exact hLen
        -- New gap is at (gapIdx+1)%cap which is set to none
        have hNewGap : ((slots.set (gapIdx % capacity)
            (some { nextE with dist := nextE.dist - 1 }) hGapI).set
            ((gapIdx + 1) % capacity) none
            (by rw [Array.size_set]; exact hNextI))[(gapIdx + 1) % capacity]'(by
              rw [hLen2]; exact Nat.mod_lt _ hCapPos) = none := by
          simp only [Array.getElem_set, ite_true]
        -- (gapIdx+1)%cap ≠ gapIdx%cap (otherwise gap has entry AND is none — contradiction)
        have hGapNeNext : (gapIdx + 1) % capacity ≠ gapIdx % capacity := by
          intro heq
          have h1 := getElem_idx_eq slots hNextI hGapI heq
          have : some nextE = none := (hNext.symm.trans h1).trans hGapNone
          exact absurd this (by simp)
        by_cases hpEqNext : p = (gapIdx + 1) % capacity
        · -- Entry e is at the position being cleared → it's nextE, moved to gapIdx%cap
          have heEqNext : e = nextE := by
            have h1 := getElem_idx_eq slots (hLen ▸ hp) hNextI hpEqNext
            exact Option.some.inj ((hSlotP.symm.trans h1).trans hNext)
          -- In double-set array, gapIdx%cap has {nextE with dist-1} = entry with same key/value
          have hMoved : ((slots.set (gapIdx % capacity)
              (some { nextE with dist := nextE.dist - 1 }) hGapI).set
              ((gapIdx + 1) % capacity) none
              (by rw [Array.size_set]; exact hNextI))[gapIdx % capacity]'(by
                rw [hLen2]; exact Nat.mod_lt _ hCapPos) =
              some { nextE with dist := nextE.dist - 1 } := by
            have hNeq1 : ¬ gapIdx % capacity = (gapIdx + 1) % capacity :=
              fun h => hGapNeNext h.symm
            have hNeq2 : ¬ (gapIdx + 1) % capacity = gapIdx % capacity :=
              fun h => hGapNeNext h
            simp only [Array.getElem_set, hNeq2, ite_false, ite_true]
          -- Adapt hNewGap: IH wants [(gapIdx+1)%cap % cap] but hNewGap has [(gapIdx+1)%cap]
          have hModIdem : ((gapIdx + 1) % capacity) % capacity = (gapIdx + 1) % capacity :=
            Nat.mod_eq_of_lt (Nat.mod_lt _ hCapPos)
          have hNewGap' : ((slots.set (gapIdx % capacity)
              (some { nextE with dist := nextE.dist - 1 }) hGapI).set
              ((gapIdx + 1) % capacity) none
              (by rw [Array.size_set]; exact hNextI))[((gapIdx + 1) % capacity) % capacity]'(by
                rw [hLen2]; rw [hModIdem]; exact Nat.mod_lt _ hCapPos) = none := by
            have := getElem_idx_eq
              ((slots.set (gapIdx % capacity) (some { nextE with dist := nextE.dist - 1 }) hGapI).set
                ((gapIdx + 1) % capacity) none (by rw [Array.size_set]; exact hNextI))
              (by rw [hLen2]; rw [hModIdem]; exact Nat.mod_lt _ hCapPos)
              (by rw [hLen2]; exact Nat.mod_lt _ hCapPos)
              hModIdem
            rw [this]; exact hNewGap
          have ⟨q, hq, e', h1, h2, h3⟩ := ih ((gapIdx + 1) % capacity) _ hLen2 hNewGap'
            (gapIdx % capacity) (Nat.mod_lt _ hCapPos)
            { nextE with dist := nextE.dist - 1 } hMoved
          exact ⟨q, hq, e', h1, heEqNext ▸ h2, heEqNext ▸ h3⟩
        · -- Entry e is NOT at (gapIdx+1)%cap: unchanged by double-set
          have hModIdem : ((gapIdx + 1) % capacity) % capacity = (gapIdx + 1) % capacity :=
            Nat.mod_eq_of_lt (Nat.mod_lt _ hCapPos)
          have hSlotDS : ((slots.set (gapIdx % capacity)
              (some { nextE with dist := nextE.dist - 1 }) hGapI).set
              ((gapIdx + 1) % capacity) none
              (by rw [Array.size_set]; exact hNextI))[p]'(by rw [hLen2]; exact hp) =
              some e := by
            have hNeN1 : ¬ p = (gapIdx + 1) % capacity := hpEqNext
            have hNeN2 : ¬ (gapIdx + 1) % capacity = p := fun h => hpEqNext h.symm
            have hNeG1 : ¬ p = gapIdx % capacity := hpNeGap
            have hNeG2 : ¬ gapIdx % capacity = p := fun h => hpNeGap h.symm
            simp only [Array.getElem_set, hNeN2, hNeG2, ite_false, hSlotP]
          have hNewGap' : ((slots.set (gapIdx % capacity)
              (some { nextE with dist := nextE.dist - 1 }) hGapI).set
              ((gapIdx + 1) % capacity) none
              (by rw [Array.size_set]; exact hNextI))[((gapIdx + 1) % capacity) % capacity]'(by
                rw [hLen2]; rw [hModIdem]; exact Nat.mod_lt _ hCapPos) = none := by
            have := getElem_idx_eq
              ((slots.set (gapIdx % capacity) (some { nextE with dist := nextE.dist - 1 }) hGapI).set
                ((gapIdx + 1) % capacity) none (by rw [Array.size_set]; exact hNextI))
              (by rw [hLen2]; rw [hModIdem]; exact Nat.mod_lt _ hCapPos)
              (by rw [hLen2]; exact Nat.mod_lt _ hCapPos)
              hModIdem
            rw [this]; exact hNewGap
          exact ih ((gapIdx + 1) % capacity) _ hLen2 hNewGap' p hp e hSlotDS
/-- N3-B4 helper: Erasing key `k` preserves entries with different keys. -/
private theorem erase_preserves_ne_entry [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (hNe : ¬(k' == k) = true)
    (_hExt : t.invExt)
    (p : Nat) (hp : p < t.capacity) (e : RHEntry α β)
    (hSlotP : t.slots[p]'(t.hSlotsLen ▸ hp) = some e)
    (hKey : (e.key == k') = true) :
    ∃ q, ∃ hq : q < (t.erase k).capacity, ∃ e' : RHEntry α β,
      (t.erase k).slots[q]'((t.erase k).hSlotsLen ▸ hq) = some e' ∧
      (e'.key == k') = true ∧ e'.value = e.value := by
  -- Introduce j, hj, e, hSlot by working with the erased table's hypotheses
  -- Unfold erase in the conclusion via intro + rewrite
  -- Case split on findLoop
  match hFind : findLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
      t.slots t.capacity t.hSlotsLen t.hCapPos with
  | none =>
    -- erase returns t unchanged
    have hEraseEq : t.erase k = t := by unfold RHTable.erase; simp only [hFind]
    simp only [hEraseEq]; exact ⟨p, hp, e, hSlotP, hKey, rfl⟩
  | some idx =>
    have ⟨eFound, hSlotFound, hKeyFound⟩ := findLoop_some_has_key t.capacity
      (idealIndex k t.capacity t.hCapPos) k 0
      t.slots t.capacity t.hSlotsLen t.hCapPos idx hFind
    have hIdxI : idx % t.capacity < t.slots.size := by
      rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
    have hpNeIdx : p ≠ idx % t.capacity := by
      intro heq
      have h1 := getElem_idx_eq t.slots (t.hSlotsLen ▸ hp) hIdxI heq
      have heEq : e = eFound := Option.some.inj ((hSlotP.symm.trans h1).trans hSlotFound)
      have hKeyK : (e.key == k) = true := heEq ▸ hKeyFound
      have : (k' == k) = true := by
        rw [← eq_of_beq hKey, ← eq_of_beq hKeyK]; exact BEq.refl e.key
      exact hNe this
    have hLen' : (t.slots.set (idx % t.capacity) none hIdxI).size = t.capacity := by
      rw [Array.size_set]; exact t.hSlotsLen
    have hSlotP' : (t.slots.set (idx % t.capacity) none hIdxI)[p]'(by
        rw [hLen']; exact hp) = some e := by
      have hNe2 : ¬ idx % t.capacity = p := fun h => hpNeIdx h.symm
      simp only [Array.getElem_set, hNe2, ite_false, hSlotP]
    have hGapNone : (t.slots.set (idx % t.capacity) none hIdxI)[idx % t.capacity]'(by
        rw [hLen']; exact Nat.mod_lt _ t.hCapPos) = none := by
      simp only [Array.getElem_set, ite_true]
    have ⟨q, hq, e', hSlotQ, hKeyQ, hValQ⟩ := backshiftLoop_preserves_entry_presence
      t.capacity idx
      (t.slots.set (idx % t.capacity) none hIdxI) t.capacity hLen' t.hCapPos
      hGapNone p hp e hSlotP'
    have hKey' : (e'.key == k') = true := by rw [hKeyQ]; exact hKey
    -- Show (t.erase k) has capacity = t.capacity and slots = backshiftLoop result
    -- Use show to convert goal type
    show ∃ q, ∃ hq : q < (t.erase k).capacity, ∃ e' : RHEntry α β,
      (t.erase k).slots[q]'((t.erase k).hSlotsLen ▸ hq) = some e' ∧
      (e'.key == k') = true ∧ e'.value = e.value
    have hCapEq : (t.erase k).capacity = t.capacity := by
      unfold RHTable.erase; simp only [hFind]
    refine ⟨q, hCapEq ▸ hq, e', ?_, hKey', hValQ⟩
    -- Need: (t.erase k).slots[q] = some e'
    -- We have hSlotQ about backshiftLoop output. Connect via erase's definition.
    have : (t.erase k).slots = backshiftLoop t.capacity idx
        (t.slots.set (idx % t.capacity) none hIdxI) t.capacity hLen' t.hCapPos := by
      unfold RHTable.erase; simp only [hFind]
    simp only [this]; exact hSlotQ
/-- N3-B4/N2-E4: Erasing key `k` does not affect lookups of other keys.
    If `¬(k == k')`, then `(t.erase k).get? k' = t.get? k'`. -/
theorem RHTable.get_after_erase_ne [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (hNe : ¬(k == k') = true)
    (hExt : t.invExt) (hSize : t.size < t.capacity) :
    (t.erase k).get? k' = t.get? k' := by
  -- The erased table satisfies invExt
  have hEraseExt := t.erase_preserves_invExt k hExt hSize
  cases hGet : t.get? k' with
  | none =>
    -- k' absent from original → absent from erased → getLoop returns none
    have hAbsent := get_none_implies_absent t k' hExt hGet
    -- Every entry in erased table came from original (by backshiftLoop_output_has_input_key_value)
    -- So k' absent from erased table
    have hAbsentE : ∀ j (hj : j < (t.erase k).capacity) (e : RHEntry α β),
        (t.erase k).slots[j]'(by rw [(t.erase k).hSlotsLen]; exact hj) = some e →
        (e.key == k') = false := by
      intro j hj e hSlot
      -- Unfold erase at hSlot to track back to original slots
      unfold RHTable.erase at hSlot hj; simp only [] at hSlot hj
      match hFind : findLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0
          t.slots t.capacity t.hSlotsLen t.hCapPos with
      | none =>
        simp only [hFind] at hSlot hj
        exact hAbsent j hj e hSlot
      | some idx =>
        simp only [hFind] at hSlot hj
        -- Entry e came from backshiftLoop output → came from set array → came from original
        have hIdxI : idx % t.capacity < t.slots.size := by
          rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos
        have hLen' : (t.slots.set (idx % t.capacity) none hIdxI).size = t.capacity := by
          rw [Array.size_set]; exact t.hSlotsLen
        have ⟨p, hp, eOrig, hSlotP, hKeyP, hValP⟩ :=
          backshiftLoop_output_has_input_key_value t.capacity idx
            (t.slots.set (idx % t.capacity) none hIdxI) t.capacity hLen' t.hCapPos
            j hj e hSlot
        -- eOrig is from the set array; trace back to original
        simp only [Array.getElem_set] at hSlotP
        split at hSlotP
        · simp at hSlotP -- set position is none, contradiction
        · -- eOrig from original slots
          have hOrigAbs := hAbsent p hp eOrig hSlotP
          -- e.key = eOrig.key (from backshiftLoop), and eOrig.key ≠ k'
          cases hc : e.key == k' with
          | false => rfl
          | true =>
            exfalso
            have : eOrig.key = e.key := hKeyP
            rw [this] at hOrigAbs
            rw [hc] at hOrigAbs; exact absurd hOrigAbs (by simp)
    unfold RHTable.get?
    exact getLoop_none_of_absent _ _ _ _ _ _ _ _ hAbsentE
  | some val =>
    -- k' present in original, entry survives erase
    have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := getLoop_some_implies_entry
      t.capacity (idealIndex k' t.capacity t.hCapPos) k' 0
      t.slots t.capacity t.hSlotsLen t.hCapPos val (by unfold RHTable.get? at hGet; exact hGet)
    -- k' ≠ k (swap direction of hNe)
    have hNeSwap : ¬(k' == k) = true := by
      intro hc; exact hNe (by rw [eq_of_beq hc]; exact BEq.refl k)
    have ⟨q, hq, e', hSlotQ, hKeyQ, hValQ⟩ := erase_preserves_ne_entry t k k' hNeSwap hExt
      p hp e hSlotP hKeyE
    -- getLoop_finds_present on the erased table
    unfold RHTable.get?
    exact getLoop_finds_present (t.erase k).capacity
      (idealIndex k' (t.erase k).capacity (t.erase k).hCapPos)
      k' 0 (t.erase k).slots (t.erase k).capacity
      (t.erase k).hSlotsLen (t.erase k).hCapPos
      q hq e' hSlotQ hKeyQ (hValQ.trans hValE)
      hEraseExt.2.1 hEraseExt.2.2.2 hEraseExt.2.2.1
      (by simp [Nat.mod_eq_of_lt (idealIndex_lt k' _ _)])
      (by
        have hd := hEraseExt.2.1 q hq e' hSlotQ
        have hKeyEq : idealIndex e'.key (t.erase k).capacity (t.erase k).hCapPos =
            idealIndex k' (t.erase k).capacity (t.erase k).hCapPos := by
          rw [eq_of_beq hKeyQ]
        rw [hKeyEq] at hd
        have := Nat.mod_lt (q + (t.erase k).capacity -
          idealIndex k' (t.erase k).capacity (t.erase k).hCapPos) (t.erase k).hCapPos
        omega)
      (by omega)

-- ============================================================================
-- N4: Public lookup infrastructure (for Bridge.lean filter proof)
-- ============================================================================

-- If get? returns none, no slot has a matching key.
theorem RHTable.get_none_no_matching_entry [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) (hNone : t.get? k = none) :
    ∀ j (hj : j < t.capacity) (e : RHEntry α β),
      t.slots[j]'(t.hSlotsLen ▸ hj) = some e → (e.key == k) = false :=
  get_none_implies_absent t k hExt hNone

-- If get? returns some, there is a slot with a matching entry.
theorem RHTable.get_some_slot_entry [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hGet : t.get? k = some v) :
    ∃ p, ∃ hp : p < t.capacity, ∃ e : RHEntry α β,
      t.slots[p]'(t.hSlotsLen ▸ hp) = some e ∧ (e.key == k) = true ∧ e.value = v := by
  unfold RHTable.get? at hGet
  exact getLoop_some_implies_entry t.capacity
    (idealIndex k t.capacity t.hCapPos) k 0
    t.slots t.capacity t.hSlotsLen t.hCapPos v hGet

theorem RHTable.insertNoResize_get_eq [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β)
    (hExt : t.invExt) (hSizeLt : t.size < t.capacity) :
    (t.insertNoResize k v).get? k = some v := by
  have ⟨j, hj, hjNone⟩ := exists_empty_slot t.slots t.capacity t.hSlotsLen t.hCapPos
    (by rw [← hExt.1.sizeCount]; exact hSizeLt)
  have ⟨s, hs, hsEq⟩ := position_reachable (idealIndex k t.capacity t.hCapPos) j
    t.capacity t.hCapPos hj
  have hRoom : ∃ s, s < t.capacity ∧
      t.slots[(idealIndex k t.capacity t.hCapPos + s) % t.capacity]'(by
        rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos) = none :=
    ⟨s, hs, by simp only [hsEq]; exact hjNone⟩
  have hHasKey : ∃ p, ∃ hp : p < (t.insertNoResize k v).capacity,
      ∃ e : RHEntry α β,
        (t.insertNoResize k v).slots[p]'((t.insertNoResize k v).hSlotsLen ▸ hp) = some e
        ∧ (e.key == k) = true ∧ e.value = v := by
    unfold RHTable.insertNoResize; simp only []
    exact insertLoop_places_key t.capacity
      (idealIndex k t.capacity t.hCapPos) k v 0
      t.slots t.capacity t.hSlotsLen t.hCapPos
      (by omega) hRoom
  have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := hHasKey
  have hInsExt := t.insertNoResize_preserves_invExt k v hExt
  unfold RHTable.get?
  have hDistE := hInsExt.2.1 p hp e hSlotP
  have hKeyEq : idealIndex e.key (t.insertNoResize k v).capacity
      (t.insertNoResize k v).hCapPos =
      idealIndex k (t.insertNoResize k v).capacity
      (t.insertNoResize k v).hCapPos := by
    rw [eq_of_beq hKeyE]
  rw [hKeyEq] at hDistE
  exact getLoop_finds_present (t.insertNoResize k v).capacity
    (idealIndex k (t.insertNoResize k v).capacity
      (t.insertNoResize k v).hCapPos) k 0
    (t.insertNoResize k v).slots (t.insertNoResize k v).capacity
    (t.insertNoResize k v).hSlotsLen (t.insertNoResize k v).hCapPos
    p hp e hSlotP hKeyE hValE
    hInsExt.2.1 hInsExt.2.2.2 hInsExt.2.2.1
    (by simp [Nat.mod_eq_of_lt (idealIndex_lt k _ _)])
    (by
      have := Nat.mod_lt (p + (t.insertNoResize k v).capacity -
        idealIndex k (t.insertNoResize k v).capacity
        (t.insertNoResize k v).hCapPos) (t.insertNoResize k v).hCapPos
      omega)
    (by omega)

theorem RHTable.insertNoResize_get_ne [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (v : β) (hNe : ¬(k' == k) = true)
    (hExt : t.invExt) (hSizeLt : t.size < t.capacity) :
    (t.insertNoResize k' v).get? k = t.get? k := by
  have hInsExt := t.insertNoResize_preserves_invExt k' v hExt
  cases hGet : t.get? k with
  | none =>
    have hAbsent := get_none_implies_absent t k hExt hGet
    have hNe' : ¬(k' == k) = true := hNe
    have hAbsent' := insertNoResize_absent_ne_key t k' v k hNe' hAbsent
    unfold RHTable.get?
    exact getLoop_none_of_absent _ _ _ _ _ _ _ _ hAbsent'
  | some val =>
    have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := getLoop_some_implies_entry
      t.capacity (idealIndex k t.capacity t.hCapPos) k 0
      t.slots t.capacity t.hSlotsLen t.hCapPos val
      (by unfold RHTable.get? at hGet; exact hGet)
    -- Entry survives insertNoResize via insertLoop_preserves_ne_entry_new
    have ⟨j2, hj2, hjNone⟩ := exists_empty_slot t.slots t.capacity t.hSlotsLen
      t.hCapPos (by rw [← hExt.1.sizeCount]; exact hSizeLt)
    have ⟨s2, hs2, hsEq2⟩ := position_reachable
      (idealIndex k' t.capacity t.hCapPos) j2 t.capacity t.hCapPos hj2
    have hRoom : ∃ s, s < t.capacity ∧
        t.slots[(idealIndex k' t.capacity t.hCapPos + s) % t.capacity]'(by
          rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos) = none :=
      ⟨s2, hs2, by simp only [hsEq2]; exact hjNone⟩
    have ⟨q, hq, e', hSlotQ, hKeyQ, hValQ⟩ :
        ∃ q, ∃ hq : q < (t.insertNoResize k' v).capacity, ∃ e' : RHEntry α β,
          (t.insertNoResize k' v).slots[q]'((t.insertNoResize k' v).hSlotsLen ▸ hq) =
            some e' ∧
          (e'.key == k) = true ∧ e'.value = e.value := by
      unfold RHTable.insertNoResize; simp only []
      exact insertLoop_preserves_ne_entry_new t.capacity
        (idealIndex k' t.capacity t.hCapPos) k' v 0
        t.slots t.capacity t.hSlotsLen t.hCapPos
        hExt.2.2.1 hExt.2.1 hExt.2.2.2
        (by simp [Nat.mod_eq_of_lt (idealIndex_lt k' _ _)])
        (by omega)
        (by intro d' hd'; omega) (by intro d' hd'; omega)
        hRoom k hNe p hp e hSlotP hKeyE
    unfold RHTable.get?
    exact getLoop_finds_present (t.insertNoResize k' v).capacity
      (idealIndex k (t.insertNoResize k' v).capacity
        (t.insertNoResize k' v).hCapPos)
      k 0 (t.insertNoResize k' v).slots (t.insertNoResize k' v).capacity
      (t.insertNoResize k' v).hSlotsLen (t.insertNoResize k' v).hCapPos
      q hq e' hSlotQ hKeyQ (hValQ.trans hValE)
      hInsExt.2.1 hInsExt.2.2.2 hInsExt.2.2.1
      (by simp [Nat.mod_eq_of_lt (idealIndex_lt k _ _)])
      (by
        have hd := hInsExt.2.1 q hq e' hSlotQ
        have hKeyEq2 : idealIndex e'.key (t.insertNoResize k' v).capacity
            (t.insertNoResize k' v).hCapPos =
            idealIndex k (t.insertNoResize k' v).capacity
            (t.insertNoResize k' v).hCapPos := by
          rw [eq_of_beq hKeyQ]
        rw [hKeyEq2] at hd
        have := Nat.mod_lt (q + (t.insertNoResize k' v).capacity -
          idealIndex k (t.insertNoResize k' v).capacity
          (t.insertNoResize k' v).hCapPos) (t.insertNoResize k' v).hCapPos
        omega)
      (by omega)

end SeLe4n.Kernel.RobinHood
