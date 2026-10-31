-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Types

/-! # The refill engine — seL4-MCS's sporadic-server refills

A scheduling context's budget is held as seL4-MCS holds it (`sc_refills`), as a
list of refills, each an amount released at a time:

- the **head**, the refill being consumed: `budgetRemaining` is its amount and
  `periodStart` its release time, present while the amount is positive;
- the **pending** refills behind it (`SchedContext.replenishments`, held in the
  context's own fields), each released at its `eligibleAt`.

A context whose head is used up holds `budgetRemaining = 0`, and its next refill
is the first pending one; the release queue holds it at that refill's time
(`SchedContext.releaseKey?`) and the drain makes it the head when it is released
(`releaseReadyHead`, seL4's `awaken`).

The operations, each seL4-MCS's (WS-ZA ZA6.4):

- `refillNew` (`refill_new`) and `refillUpdate` (`refill_update`): configure,
  head-only — the budget in one refill, or the head kept and trimmed to it;
- `refillBudgetCheck` (`refill_budget_check`) with `scheduleUsed`
  (`schedule_used`): the charge — the used amount scheduled one period after its
  head's release, merged into the last refill when it overlaps or when the
  refills are at capacity, so no budget is dropped;
- `refillUnblockCheck` (`refill_unblock_check`): a ready head is moved to the
  charge's start and the refills it overlaps merged into it;
- `releaseReadyHead`: a used-up head is replaced by the first pending refill once
  that is released.

Every operation keeps the context's total: the head plus the pending refills
equals the configured budget (`Invariant/Defs.lean`, `refillsConserved`), and a
context never runs more than its budget in any window of one period
(`refill_window_bound`).
-/

namespace SeLe4n.Kernel

-- ============================================================================
-- Budget exhaustion and the refill sum
-- ============================================================================

/-- A SchedContext's budget is exhausted when `budgetRemaining` is zero. -/
@[inline] def isBudgetExhausted (sc : SchedContext) : Bool :=
  sc.budgetRemaining.isZero

/-- Sum the budget amounts of all replenishment entries. -/
def sumReplenishments : List ReplenishmentEntry → Nat
  | [] => 0
  | r :: rs => r.amount.val + sumReplenishments rs

theorem sumReplenishments_nil : sumReplenishments [] = 0 := rfl

theorem sumReplenishments_cons (r : ReplenishmentEntry)
    (rs : List ReplenishmentEntry) :
    sumReplenishments (r :: rs) = r.amount.val + sumReplenishments rs := rfl

theorem sumReplenishments_append (l₁ l₂ : List ReplenishmentEntry) :
    sumReplenishments (l₁ ++ l₂) = sumReplenishments l₁ + sumReplenishments l₂ := by
  induction l₁ with
  | nil => simp [sumReplenishments]
  | cons r rs ih => simp only [List.cons_append, sumReplenishments, ih]; omega

-- ============================================================================
-- The pending refills' storage: slot readers and writers
-- ============================================================================

/-- WS-ZA ZA6.3: a slot's amount, read as its field. -/
@[inline] def SchedContext.tailSlotAmount (sc : SchedContext) : Nat → Nat
  | 0 => sc.refillSlot1Amount | 1 => sc.refillSlot2Amount | 2 => sc.refillSlot3Amount
  | 3 => sc.refillSlot4Amount | 4 => sc.refillSlot5Amount | 5 => sc.refillSlot6Amount
  | 6 => sc.refillSlot7Amount | _ => 0

/-- WS-ZA ZA6.3: a slot's release time, read as its field. -/
@[inline] def SchedContext.tailSlotEligibleAt (sc : SchedContext) : Nat → Nat
  | 0 => sc.refillSlot1EligibleAt | 1 => sc.refillSlot2EligibleAt | 2 => sc.refillSlot3EligibleAt
  | 3 => sc.refillSlot4EligibleAt | 4 => sc.refillSlot5EligibleAt | 5 => sc.refillSlot6EligibleAt
  | 6 => sc.refillSlot7EligibleAt | _ => 0

theorem SchedContext.tailSlot_eq (sc : SchedContext) (i : Nat) :
    sc.tailSlot i = { amount := ⟨sc.tailSlotAmount i⟩, eligibleAt := sc.tailSlotEligibleAt i } := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => rfl

/-- WS-ZA ZA6.3: a tail slot's field after a write of `v` into slot `i`: `v` in
slot `k = i`, its old value `old` in every other.  A call, so the record update
that applies it to each slot is straight-line. -/
@[noinline] def tailSlotWrite (old k i v : Nat) : Nat := if k = i then v else old

/-- WS-ZA ZA6.3: a refill of `amount` released at `eligibleAt` written into tail
slot `n`, the pending count set to `n + 1`, as one straight-line record update
over every slot (`tailSlotWrite`). -/
@[inline] def SchedContext.appendTailRecord (sc : SchedContext) (n amount eligibleAt : Nat) :
    SchedContext :=
  { sc with
    refillSlot1Amount := tailSlotWrite sc.refillSlot1Amount 0 n amount
    refillSlot1EligibleAt := tailSlotWrite sc.refillSlot1EligibleAt 0 n eligibleAt
    refillSlot2Amount := tailSlotWrite sc.refillSlot2Amount 1 n amount
    refillSlot2EligibleAt := tailSlotWrite sc.refillSlot2EligibleAt 1 n eligibleAt
    refillSlot3Amount := tailSlotWrite sc.refillSlot3Amount 2 n amount
    refillSlot3EligibleAt := tailSlotWrite sc.refillSlot3EligibleAt 2 n eligibleAt
    refillSlot4Amount := tailSlotWrite sc.refillSlot4Amount 3 n amount
    refillSlot4EligibleAt := tailSlotWrite sc.refillSlot4EligibleAt 3 n eligibleAt
    refillSlot5Amount := tailSlotWrite sc.refillSlot5Amount 4 n amount
    refillSlot5EligibleAt := tailSlotWrite sc.refillSlot5EligibleAt 4 n eligibleAt
    refillSlot6Amount := tailSlotWrite sc.refillSlot6Amount 5 n amount
    refillSlot6EligibleAt := tailSlotWrite sc.refillSlot6EligibleAt 5 n eligibleAt
    refillSlot7Amount := tailSlotWrite sc.refillSlot7Amount 6 n amount
    refillSlot7EligibleAt := tailSlotWrite sc.refillSlot7EligibleAt 6 n eligibleAt
    refillTailCount := n + 1 }

theorem SchedContext.appendTailRecord_tailSlot (sc : SchedContext) (n a t j : Nat) :
    (sc.appendTailRecord n a t).tailSlot j =
      if j = n ∧ j < refillTailCapacity then { amount := ⟨a⟩, eligibleAt := t } else sc.tailSlot j := by
  unfold refillTailCapacity maxReplenishments
  have key : ∀ (k : Nat), k < 7 → (sc.appendTailRecord n a t).tailSlot k =
      if k = n then { amount := ⟨a⟩, eligibleAt := t } else sc.tailSlot k := by
    intro k hk
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ =>
      simp only [SchedContext.appendTailRecord, SchedContext.tailSlot, tailSlotWrite]
      split <;> simp_all
  by_cases hj : j < 7
  · rw [key j hj]; by_cases h : j = n
    · subst h; simp [hj]
    · simp [h]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 7 := ⟨j - 7, by omega⟩
    simp only [SchedContext.tailSlot]
    rw [if_neg (by omega)]

/-- WS-ZA ZA6.4: the number of slots in use behind the first pending refill. -/
@[inline] def SchedContext.tailUsed (sc : SchedContext) : Nat :=
  min sc.refillTailCount refillTailCapacity

theorem SchedContext.tailUsed_le (sc : SchedContext) : sc.tailUsed ≤ refillTailCapacity :=
  Nat.min_le_right _ _

theorem SchedContext.refillTail_eq_tailUsed (sc : SchedContext) :
    sc.refillTail = (List.range sc.tailUsed).map sc.tailSlot := rfl

/-- The tail read through slots that agree below `k`. -/
theorem refillTail_congr {sc sc' : SchedContext} {k : Nat}
    (hk : sc.tailUsed = k) (hk' : sc'.tailUsed = k)
    (h : ∀ j, j < k → sc'.tailSlot j = sc.tailSlot j) : sc'.refillTail = sc.refillTail := by
  rw [SchedContext.refillTail_eq_tailUsed, SchedContext.refillTail_eq_tailUsed, hk, hk']
  apply List.ext_getElem (by simp)
  intro j h1 _
  simp only [List.getElem_map, List.getElem_range]
  exact h j (by simpa using h1)

-- ============================================================================
-- The pending refills' edits, each a record update of the context's fields
-- ============================================================================

/-- WS-ZA ZA6.4: the pending refills dropped (seL4's list truncated to its head). -/
@[inline] def SchedContext.refillClear (sc : SchedContext) : SchedContext :=
  { sc with refillHeadPresent := false, refillTailCount := 0 }

/-- WS-ZA ZA6.4: a refill of `a` released at `t` added behind the pending ones
(seL4's `refill_add_tail`): the first pending refill's fields when there is
none, the next slot otherwise.  The storage holds `maxReplenishments`; a caller
adds one only below that (`refillPush_replenishments`). -/
@[inline] def SchedContext.refillPush (sc : SchedContext) (a t : Nat) : SchedContext :=
  if sc.refillHeadPresent then
    if sc.tailUsed < refillTailCapacity then sc.appendTailRecord sc.tailUsed a t else sc
  else
    { sc with
      refillHeadPresent := true
      refillHeadAmount := a
      refillHeadEligibleAt := t
      refillTailCount := 0 }

/-- WS-ZA ZA6.4: the last pending refill rewritten as `a` released at `t` (seL4's
`refill_tail` written in place). -/
@[inline] def SchedContext.refillSetLast (sc : SchedContext) (a t : Nat) : SchedContext :=
  if sc.refillHeadPresent then
    if sc.tailUsed = 0 then
      { sc with refillHeadAmount := a, refillHeadEligibleAt := t, refillTailCount := 0 }
    else sc.appendTailRecord (sc.tailUsed - 1) a t
  else sc

/-- WS-ZA ZA6.4: the first pending refill taken off (seL4's `refill_pop_head`):
the slots move up one, as one straight-line record update. -/
@[inline] def SchedContext.refillPop (sc : SchedContext) : SchedContext :=
  if sc.refillHeadPresent && decide (0 < sc.tailUsed) then
    { sc with
      refillHeadAmount := sc.refillSlot1Amount
      refillHeadEligibleAt := sc.refillSlot1EligibleAt
      refillSlot1Amount := sc.refillSlot2Amount
      refillSlot1EligibleAt := sc.refillSlot2EligibleAt
      refillSlot2Amount := sc.refillSlot3Amount
      refillSlot2EligibleAt := sc.refillSlot3EligibleAt
      refillSlot3Amount := sc.refillSlot4Amount
      refillSlot3EligibleAt := sc.refillSlot4EligibleAt
      refillSlot4Amount := sc.refillSlot5Amount
      refillSlot4EligibleAt := sc.refillSlot5EligibleAt
      refillSlot5Amount := sc.refillSlot6Amount
      refillSlot5EligibleAt := sc.refillSlot6EligibleAt
      refillSlot6Amount := sc.refillSlot7Amount
      refillSlot6EligibleAt := sc.refillSlot7EligibleAt
      refillTailCount := sc.tailUsed - 1 }
  else { sc with refillHeadPresent := false, refillTailCount := 0 }

/-- WS-ZA ZA6.4: the last pending refill's amount (0 when none). -/
@[noinline] def SchedContext.lastRefillAmount (sc : SchedContext) : Nat :=
  if sc.tailUsed = 0 then sc.refillHeadAmount else sc.tailSlotAmount (sc.tailUsed - 1)

/-- WS-ZA ZA6.4: the last pending refill's release time. -/
@[noinline] def SchedContext.lastRefillAt (sc : SchedContext) : Nat :=
  if sc.tailUsed = 0 then sc.refillHeadEligibleAt else sc.tailSlotEligibleAt (sc.tailUsed - 1)

/-- WS-ZA ZA6.4: how many refills the context holds, its head among them (seL4's
`refill_size`). -/
@[inline] def SchedContext.refillSize (sc : SchedContext) : Nat :=
  (if 0 < sc.budgetRemaining.val then 1 else 0) +
    (if sc.refillHeadPresent then sc.tailUsed + 1 else 0)

/-- WS-ZA ZA6.4: the refills are at capacity (seL4's `refill_full`). -/
@[inline] def SchedContext.refillFull (sc : SchedContext) : Bool :=
  decide (maxReplenishments ≤ sc.refillSize)

-- ============================================================================
-- What the edits do to the pending refills
-- ============================================================================

theorem SchedContext.replenishments_eq (sc : SchedContext) :
    sc.replenishments = if sc.refillHeadPresent then
      { amount := ⟨sc.refillHeadAmount⟩, eligibleAt := sc.refillHeadEligibleAt } ::
        (List.range sc.tailUsed).map sc.tailSlot else [] := rfl

theorem SchedContext.replenishments_length (sc : SchedContext) :
    sc.replenishments.length = if sc.refillHeadPresent then sc.tailUsed + 1 else 0 := by
  rw [SchedContext.replenishments_eq]; split <;> simp

theorem SchedContext.refillSize_eq (sc : SchedContext) :
    sc.refillSize = (if 0 < sc.budgetRemaining.val then 1 else 0) + sc.replenishments.length := by
  rw [SchedContext.replenishments_length]; rfl

@[simp] theorem SchedContext.refillClear_replenishments (sc : SchedContext) :
    sc.refillClear.replenishments = [] := rfl

/-- The pending refills of a context holding a first one, read from its
fields: the first, then `L` when the slots in use hold `L`. -/
theorem SchedContext.replenishments_of_slots {sc : SchedContext}
    (hp : sc.refillHeadPresent = true) (L : List ReplenishmentEntry) (hlen : sc.tailUsed = L.length)
    (hslot : ∀ j (h : j < L.length), sc.tailSlot j = L[j]) :
    sc.replenishments =
      { amount := ⟨sc.refillHeadAmount⟩, eligibleAt := sc.refillHeadEligibleAt } :: L := by
  rw [SchedContext.replenishments_eq, if_pos hp, hlen]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 _
  simp only [List.getElem_map, List.getElem_range]
  exact hslot j (by simpa using h1)

theorem SchedContext.refillTail_getElem (sc : SchedContext) (j : Nat)
    (h : j < sc.refillTail.length) : sc.refillTail[j] = sc.tailSlot j := by
  simp [SchedContext.refillTail]

theorem SchedContext.refillTail_length' (sc : SchedContext) :
    sc.refillTail.length = sc.tailUsed := by simp [SchedContext.refillTail, SchedContext.tailUsed]

theorem SchedContext.replenishments_of_present' {sc : SchedContext}
    (hp : sc.refillHeadPresent = true) :
    sc.replenishments =
      { amount := ⟨sc.refillHeadAmount⟩, eligibleAt := sc.refillHeadEligibleAt } :: sc.refillTail := by
  simp [SchedContext.replenishments, hp]

theorem SchedContext.refillPush_replenishments (sc : SchedContext) (a t : Nat)
    (h : sc.replenishments.length < maxReplenishments) :
    (sc.refillPush a t).replenishments =
      sc.replenishments ++ [{ amount := ⟨a⟩, eligibleAt := t }] := by
  rw [SchedContext.replenishments_length] at h
  unfold SchedContext.refillPush
  by_cases hP : sc.refillHeadPresent = true
  · have hu : sc.tailUsed < refillTailCapacity := by
      rw [if_pos hP] at h; unfold refillTailCapacity; omega
    rw [if_pos hP, if_pos hu, SchedContext.replenishments_of_present' hP, List.cons_append]
    have hk : (sc.appendTailRecord sc.tailUsed a t).tailUsed = sc.tailUsed + 1 := by
      simp only [SchedContext.tailUsed, SchedContext.appendTailRecord]
      unfold SchedContext.tailUsed at hu; omega
    refine SchedContext.replenishments_of_slots (sc := sc.appendTailRecord sc.tailUsed a t) hP
      (sc.refillTail ++ [{ amount := ⟨a⟩, eligibleAt := t }])
      (hk.trans (by simp [sc.refillTail_length'])) ?_
    intro j hj
    rw [SchedContext.appendTailRecord_tailSlot]
    simp only [List.length_append, List.length_singleton, sc.refillTail_length'] at hj
    by_cases hjn : j = sc.tailUsed
    · subst hjn; rw [if_pos ⟨rfl, hu⟩]; simp [sc.refillTail_length']
    · rw [if_neg (fun h => hjn h.1), List.getElem_append_left (by rw [sc.refillTail_length']; omega),
        sc.refillTail_getElem]
  · simp only [Bool.not_eq_true] at hP
    rw [if_neg (by simp [hP])]
    simp [hP]

theorem SchedContext.refillSetLast_replenishments (sc : SchedContext) (a t : Nat) :
    (sc.refillSetLast a t).replenishments =
      if sc.replenishments = [] then []
      else sc.replenishments.dropLast ++ [{ amount := ⟨a⟩, eligibleAt := t }] := by
  unfold SchedContext.refillSetLast
  by_cases hP : sc.refillHeadPresent = true
  · rw [if_pos hP, SchedContext.replenishments_of_present' hP,
      if_neg (List.cons_ne_nil _ _)]
    by_cases h0 : sc.tailUsed = 0
    · rw [if_pos h0]
      have hT : sc.refillTail = [] := by
        rw [← List.length_eq_zero_iff, sc.refillTail_length', h0]
      rw [hT]
      simp [SchedContext.replenishments_eq, hP, SchedContext.tailUsed]
    · rw [if_neg h0]
      have hk : (sc.appendTailRecord (sc.tailUsed - 1) a t).tailUsed = sc.tailUsed := by
        have := sc.tailUsed_le
        simp only [SchedContext.tailUsed, SchedContext.appendTailRecord] at this h0 ⊢; omega
      obtain ⟨L, e, hL⟩ : ∃ L e, sc.refillTail = L ++ [e] := by
        refine ⟨sc.refillTail.dropLast, sc.refillTail.getLast (by
          rw [← List.length_pos_iff, sc.refillTail_length']; omega), ?_⟩
        exact (List.dropLast_concat_getLast _).symm
      have hLlen : L.length + 1 = sc.tailUsed := by
        have := congrArg List.length hL; rw [sc.refillTail_length'] at this; simp at this; omega
      rw [hL, ← List.cons_append, List.dropLast_concat, List.cons_append]
      refine SchedContext.replenishments_of_slots (sc := sc.appendTailRecord (sc.tailUsed - 1) a t) hP
        (L ++ [{ amount := ⟨a⟩, eligibleAt := t }])
        (hk.trans (by rw [List.length_append, List.length_singleton]; omega)) ?_
      intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      rw [SchedContext.appendTailRecord_tailSlot]
      by_cases hjn : j = sc.tailUsed - 1
      · rw [if_pos ⟨hjn, by have := sc.tailUsed_le; omega⟩]
        have hjL : j = L.length := by omega
        subst hjL; simp
      · rw [if_neg (fun h => hjn h.1), List.getElem_append_left (by omega)]
        have hj' : j < sc.refillTail.length := by rw [sc.refillTail_length']; omega
        rw [← sc.refillTail_getElem j hj']
        simp only [hL, List.getElem_append_left (show j < L.length by omega)]
  · simp only [Bool.not_eq_true] at hP
    simp [hP, SchedContext.replenishments_eq]

theorem SchedContext.refillPop_replenishments (sc : SchedContext) :
    sc.refillPop.replenishments = sc.replenishments.tail := by
  unfold SchedContext.refillPop
  by_cases h : sc.refillHeadPresent = true ∧ 0 < sc.tailUsed
  · obtain ⟨hP, hk⟩ := h
    rw [if_pos (by simp [hP, hk]), SchedContext.replenishments_of_present' hP, List.tail_cons]
    obtain ⟨k, hk'⟩ : ∃ k, sc.tailUsed = k + 1 := ⟨sc.tailUsed - 1, by omega⟩
    have hT : sc.refillTail = sc.tailSlot 0 :: (List.range k).map (fun j => sc.tailSlot (j + 1)) := by
      rw [SchedContext.refillTail_eq_tailUsed, hk', List.range_succ_eq_map]; simp
    rw [hT, sc.tailSlot_eq 0]
    refine SchedContext.replenishments_of_slots (L := (List.range k).map (fun j => sc.tailSlot (j + 1)))
      (by simp [hP]) (by
        have := sc.tailUsed_le
        simp only [SchedContext.tailUsed] at hk' this ⊢; simp; omega) ?_
    intro j hj
    simp only [List.length_map, List.length_range] at hj
    have hj6 : j < 6 := by have := sc.tailUsed_le; unfold refillTailCapacity maxReplenishments at this; omega
    simp only [List.getElem_map, List.getElem_range]
    match j, hj6 with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl
  · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact h)]
    by_cases hP : sc.refillHeadPresent = true
    · have hk : sc.tailUsed = 0 := by
        exact Classical.byContradiction fun hc => h ⟨hP, Nat.pos_of_ne_zero hc⟩
      rw [SchedContext.replenishments_of_present' hP]
      have hT : sc.refillTail = [] := by rw [← List.length_eq_zero_iff, sc.refillTail_length', hk]
      simp [hT, SchedContext.replenishments]
    · simp only [Bool.not_eq_true] at hP
      simp [SchedContext.replenishments, hP]

theorem SchedContext.lastRefill_eq (sc : SchedContext) (r : ReplenishmentEntry)
    (h : sc.replenishments.getLast? = some r) :
    r.amount.val = sc.lastRefillAmount ∧ r.eligibleAt = sc.lastRefillAt := by
  by_cases hP : sc.refillHeadPresent = true
  · rw [SchedContext.replenishments_of_present' hP] at h
    unfold SchedContext.lastRefillAmount SchedContext.lastRefillAt
    by_cases h0 : sc.tailUsed = 0
    · have hT : sc.refillTail = [] := by rw [← List.length_eq_zero_iff, sc.refillTail_length', h0]
      rw [hT] at h; simp at h; subst h; simp [h0]
    · rw [if_neg h0, if_neg h0]
      have hne : sc.refillTail ≠ [] := by
        rw [← List.length_pos_iff, sc.refillTail_length']; omega
      rw [List.getLast?_cons, List.getLast?_eq_some_getLast hne] at h
      simp only [Option.getD_some, Option.some.injEq] at h
      subst h
      rw [List.getLast_eq_getElem, sc.refillTail_getElem, sc.tailSlot_eq]
      simp [sc.refillTail_length']
  · simp only [Bool.not_eq_true] at hP
    simp [SchedContext.replenishments_eq, hP] at h

/-- WS-ZA ZA6.4: a context with its pending refills erased: every field the
pending refills' edits leave alone. -/
@[inline] def SchedContext.pendingErased (sc : SchedContext) : SchedContext :=
  { sc with
    refillHeadPresent := false, refillHeadAmount := 0, refillHeadEligibleAt := 0,
    refillTailCount := 0,
    refillSlot1Amount := 0, refillSlot1EligibleAt := 0, refillSlot2Amount := 0,
    refillSlot2EligibleAt := 0, refillSlot3Amount := 0, refillSlot3EligibleAt := 0,
    refillSlot4Amount := 0, refillSlot4EligibleAt := 0, refillSlot5Amount := 0,
    refillSlot5EligibleAt := 0, refillSlot6Amount := 0, refillSlot6EligibleAt := 0,
    refillSlot7Amount := 0, refillSlot7EligibleAt := 0 }

@[simp] theorem SchedContext.refillClear_pendingErased (sc : SchedContext) :
    sc.refillClear.pendingErased = sc.pendingErased := rfl

@[simp] theorem SchedContext.appendTailRecord_pendingErased (sc : SchedContext) (n a t : Nat) :
    (sc.appendTailRecord n a t).pendingErased = sc.pendingErased := rfl

@[simp] theorem SchedContext.refillPush_pendingErased (sc : SchedContext) (a t : Nat) :
    (sc.refillPush a t).pendingErased = sc.pendingErased := by
  unfold SchedContext.refillPush; split
  · split <;> rfl
  · rfl

@[simp] theorem SchedContext.refillSetLast_pendingErased (sc : SchedContext) (a t : Nat) :
    (sc.refillSetLast a t).pendingErased = sc.pendingErased := by
  unfold SchedContext.refillSetLast; split
  · split <;> rfl
  · rfl

@[simp] theorem SchedContext.refillPop_pendingErased (sc : SchedContext) :
    sc.refillPop.pendingErased = sc.pendingErased := by
  unfold SchedContext.refillPop; split <;> rfl

/-- The fields the pending refills' edits leave alone, read through the
erasure. -/
theorem SchedContext.fields_of_pendingErased {sc sc' : SchedContext}
    (h : sc'.pendingErased = sc.pendingErased) :
    sc'.scId = sc.scId ∧ sc'.budget = sc.budget ∧ sc'.period = sc.period ∧
      sc'.priority = sc.priority ∧ sc'.deadline = sc.deadline ∧ sc'.domain = sc.domain ∧
      sc'.budgetRemaining = sc.budgetRemaining ∧ sc'.periodStart = sc.periodStart ∧
      sc'.boundThreadCode = sc.boundThreadCode ∧ sc'.scReply = sc.scReply ∧
      sc'.donationOrigin = sc.donationOrigin ∧ sc'.isActive = sc.isActive ∧
      sc'.releaseNextCode = sc.releaseNextCode ∧ sc'.releaseCoreCode = sc.releaseCoreCode ∧
      sc'.releaseAt = sc.releaseAt := by
  have f : ∀ {α : Type} (g : SchedContext → α), (∀ s, g s.pendingErased = g s) →
      g sc' = g sc := fun g hg => by rw [← hg sc', h, hg]
  exact ⟨f (·.scId) (fun _ => rfl), f (·.budget) (fun _ => rfl), f (·.period) (fun _ => rfl),
    f (·.priority) (fun _ => rfl), f (·.deadline) (fun _ => rfl), f (·.domain) (fun _ => rfl),
    f (·.budgetRemaining) (fun _ => rfl), f (·.periodStart) (fun _ => rfl),
    f (·.boundThreadCode) (fun _ => rfl), f (·.scReply) (fun _ => rfl),
    f (·.donationOrigin) (fun _ => rfl), f (·.isActive) (fun _ => rfl),
    f (·.releaseNextCode) (fun _ => rfl), f (·.releaseCoreCode) (fun _ => rfl),
    f (·.releaseAt) (fun _ => rfl)⟩

-- ============================================================================
-- seL4-MCS's `schedule_used`
-- ============================================================================

/-- WS-ZA ZA6.4: seL4-MCS's `schedule_used` over the pending refills: the used
refill `u` is merged into the last pending one when it overlaps or touches it;
it is added behind the last when the refills are not at capacity; and at
capacity it is merged into the last, which moves later so the two are adjacent
(`tail.rTime = new.rTime - tail.rAmount`).  No amount is dropped. -/
def scheduleUsedList (full : Bool) (u : ReplenishmentEntry) (P : List ReplenishmentEntry) :
    List ReplenishmentEntry :=
  match P.getLast? with
  | none => [u]
  | some l =>
    if u.eligibleAt ≤ l.eligibleAt + l.amount.val then
      P.dropLast ++ [{ amount := ⟨l.amount.val + u.amount.val⟩, eligibleAt := l.eligibleAt }]
    else if full then
      P.dropLast ++
        [{ amount := ⟨l.amount.val + u.amount.val⟩, eligibleAt := u.eligibleAt - l.amount.val }]
    else P ++ [u]

/-- WS-ZA ZA6.4: `schedule_used` on the context's own fields: `a` used, its
refill released at `t` (`scheduleUsedList`, `scheduleUsed_replenishments`). -/
@[inline] def SchedContext.scheduleUsed (sc : SchedContext) (a t : Nat) : SchedContext :=
  if sc.refillHeadPresent then
    let la := sc.lastRefillAmount
    let lt := sc.lastRefillAt
    if t ≤ lt + la then sc.refillSetLast (la + a) lt
    else if sc.refillFull then sc.refillSetLast (la + a) (t - la)
    else sc.refillPush a t
  else sc.refillPush a t

@[simp] theorem SchedContext.scheduleUsed_pendingErased (sc : SchedContext) (a t : Nat) :
    (sc.scheduleUsed a t).pendingErased = sc.pendingErased := by
  unfold SchedContext.scheduleUsed; split
  · dsimp only; split
    · simp
    · split <;> simp
  · simp

theorem SchedContext.scheduleUsed_replenishments (sc : SchedContext) (a t : Nat) :
    (sc.scheduleUsed a t).replenishments =
      scheduleUsedList sc.refillFull { amount := ⟨a⟩, eligibleAt := t } sc.replenishments := by
  have hNotFull : sc.refillFull = false → sc.replenishments.length < maxReplenishments := by
    intro h
    simp only [SchedContext.refillFull, decide_eq_false_iff_not, SchedContext.refillSize_eq] at h
    omega
  unfold SchedContext.scheduleUsed scheduleUsedList
  by_cases hP : sc.refillHeadPresent = true
  · rw [if_pos hP]
    have hne : sc.replenishments ≠ [] := by rw [sc.replenishments_of_present' hP]; simp
    obtain ⟨l, hl⟩ : ∃ l, sc.replenishments.getLast? = some l :=
      ⟨_, List.getLast?_eq_some_getLast hne⟩
    obtain ⟨hla, hlt⟩ := sc.lastRefill_eq l hl
    rw [hl]
    dsimp only
    rw [← hla, ← hlt]
    split
    · rw [SchedContext.refillSetLast_replenishments, if_neg hne]
    · split
      · rw [SchedContext.refillSetLast_replenishments, if_neg hne]
      · rename_i hF
        rw [SchedContext.refillPush_replenishments _ _ _ (hNotFull (by simpa using hF))]
  · simp only [Bool.not_eq_true] at hP
    rw [if_neg (by simp [hP])]
    have h0 : sc.replenishments = [] := by simp [SchedContext.replenishments, hP]
    rw [SchedContext.refillPush_replenishments _ _ _ (by rw [h0]; decide), h0]
    rfl

/-- `schedule_used` adds exactly the used amount to the pending refills. -/
theorem sumReplenishments_scheduleUsedList (full : Bool) (u : ReplenishmentEntry)
    (P : List ReplenishmentEntry) :
    sumReplenishments (scheduleUsedList full u P) = sumReplenishments P + u.amount.val := by
  unfold scheduleUsedList
  cases hl : P.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hl; subst hl; simp [sumReplenishments]
  | some l =>
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
    dsimp only
    split
    · simp [sumReplenishments_append, sumReplenishments]; omega
    · split <;> simp [sumReplenishments_append, sumReplenishments] <;> omega

/-- `schedule_used` keeps every pending amount positive when the used one is. -/
theorem scheduleUsedList_pos (full : Bool) (u : ReplenishmentEntry) (P : List ReplenishmentEntry)
    (hP : ∀ r ∈ P, 0 < r.amount.val) (hu : 0 < u.amount.val) :
    ∀ r ∈ scheduleUsedList full u P, 0 < r.amount.val := by
  unfold scheduleUsedList
  cases hl : P.getLast? with
  | none => simp only [List.mem_singleton]; rintro r rfl; exact hu
  | some l =>
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
    dsimp only
    have hys : ∀ r ∈ ys, 0 < r.amount.val := fun r hr => hP r (List.mem_append_left _ hr)
    split
    · simp only [List.dropLast_concat, List.mem_append, List.mem_singleton]
      rintro r (hr | rfl)
      · exact hys r hr
      · simp only; omega
    · split
      · simp only [List.dropLast_concat, List.mem_append, List.mem_singleton]
        rintro r (hr | rfl)
        · exact hys r hr
        · simp only; omega
      · simp only [List.mem_append, List.mem_singleton]
        rintro r ((hr | hr) | rfl)
        · exact hys r hr
        · exact hP r (by simp [hr])
        · exact hu

/-- `schedule_used` adds a refill only when the refills are not at capacity. -/
theorem scheduleUsedList_length (full : Bool) (u : ReplenishmentEntry) (P : List ReplenishmentEntry) :
    (scheduleUsedList full u P).length = P.length ∨
      (full = false ∧ (scheduleUsedList full u P).length = P.length + 1) ∨
      (P = [] ∧ (scheduleUsedList full u P).length = 1) := by
  unfold scheduleUsedList
  cases hl : P.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hl; subst hl; simp
  | some l =>
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
    dsimp only
    split
    · left; simp
    · split
      · left; simp
      · rename_i hF; right; left; exact ⟨by simpa using hF, by simp⟩

-- ============================================================================
-- seL4-MCS's `refill_budget_check`, `refill_unblock_check` and the release
-- ============================================================================

/-- WS-ZA ZA6.4: seL4-MCS's `refill_budget_check`: `usage` charged against the
head refill.  A head used up is taken off (its whole amount scheduled one period
after its release, `schedule_used`) and `budgetRemaining` reads 0; a head used in
part keeps the rest, released `usage` later, and the used part is scheduled one
period after the head's release.  A charge of 0, or of a context with no head,
writes nothing.  Callers charge at most the head (the tick charges one unit to a
head of at least one; the yield charges the whole head). -/
@[inline] def SchedContext.refillBudgetCheck (sc : SchedContext) (usage : Nat) : SchedContext :=
  let b := sc.budgetRemaining.val
  let used := sc.periodStart + sc.period.val
  if usage = 0 ∨ b = 0 then sc
  else if b ≤ usage then
    ({ sc with budgetRemaining := ⟨0⟩, isActive := false } : SchedContext).scheduleUsed b used
  else
    ({ sc with
        budgetRemaining := ⟨b - usage⟩
        periodStart := sc.periodStart + usage
        isActive := true } : SchedContext).scheduleUsed usage used

/-- WS-ZA ZA6.4: one release of a used-up head: when `budgetRemaining` is 0 and
the first pending refill is released by `now`, it becomes the head (seL4-MCS's
head refill, made ready, which `awaken` releases).  Otherwise nothing changes. -/
@[inline] def SchedContext.releaseOne (sc : SchedContext) (now : Nat) : SchedContext :=
  if sc.budgetRemaining.val = 0 ∧ sc.refillHeadPresent = true ∧ sc.refillHeadEligibleAt ≤ now then
    let a := sc.refillHeadAmount
    let t := sc.refillHeadEligibleAt
    { sc.refillPop with budgetRemaining := ⟨a⟩, periodStart := t, isActive := decide (0 < a) }
  else sc

/-- Whether a pop takes a pending refill into the head: the head is present and
a slot behind it is in use.  A scalar helper kept out of line so that the
compiled release is one straight-line record update. -/
@[noinline] def refillPopTakes (present : Bool) (count : Nat) : Bool :=
  present && decide (0 < min count refillTailCapacity)

/-- The slots in use behind the head after a pop that takes one. -/
@[noinline] def refillPopCount (count : Nat) : Nat := min count refillTailCapacity - 1

/-- One of two slot values, chosen by `c`. -/
@[noinline] def refillSlotSelect (c : Bool) (a b : Nat) : Nat := if c then a else b

/-- The compiled `SchedContext.releaseOne`: the pop's choice is made per field
by the scalar helpers above, so the update has no branch inside it and Lean
writes the context in place when it holds the only reference (a branch inside
the update makes a join point that drops the reuse and allocates a context
on every release). -/
@[inline] def SchedContext.releaseOneImpl (sc : SchedContext) (now : Nat) : SchedContext :=
  if sc.budgetRemaining.val = 0 ∧ sc.refillHeadPresent = true ∧ sc.refillHeadEligibleAt ≤ now then
    let a := sc.refillHeadAmount
    let t := sc.refillHeadEligibleAt
    let c := refillPopTakes sc.refillHeadPresent sc.refillTailCount
    { sc with
      refillHeadPresent := c
      refillHeadAmount := refillSlotSelect c sc.refillSlot1Amount sc.refillHeadAmount
      refillHeadEligibleAt := refillSlotSelect c sc.refillSlot1EligibleAt sc.refillHeadEligibleAt
      refillSlot1Amount := refillSlotSelect c sc.refillSlot2Amount sc.refillSlot1Amount
      refillSlot1EligibleAt := refillSlotSelect c sc.refillSlot2EligibleAt sc.refillSlot1EligibleAt
      refillSlot2Amount := refillSlotSelect c sc.refillSlot3Amount sc.refillSlot2Amount
      refillSlot2EligibleAt := refillSlotSelect c sc.refillSlot3EligibleAt sc.refillSlot2EligibleAt
      refillSlot3Amount := refillSlotSelect c sc.refillSlot4Amount sc.refillSlot3Amount
      refillSlot3EligibleAt := refillSlotSelect c sc.refillSlot4EligibleAt sc.refillSlot3EligibleAt
      refillSlot4Amount := refillSlotSelect c sc.refillSlot5Amount sc.refillSlot4Amount
      refillSlot4EligibleAt := refillSlotSelect c sc.refillSlot5EligibleAt sc.refillSlot4EligibleAt
      refillSlot5Amount := refillSlotSelect c sc.refillSlot6Amount sc.refillSlot5Amount
      refillSlot5EligibleAt := refillSlotSelect c sc.refillSlot6EligibleAt sc.refillSlot5EligibleAt
      refillSlot6Amount := refillSlotSelect c sc.refillSlot7Amount sc.refillSlot6Amount
      refillSlot6EligibleAt := refillSlotSelect c sc.refillSlot7EligibleAt sc.refillSlot6EligibleAt
      refillTailCount := refillSlotSelect c (refillPopCount sc.refillTailCount) 0
      budgetRemaining := ⟨a⟩, periodStart := t, isActive := decide (0 < a) }
  else sc

/-- The compiled release is the release. -/
@[csimp] theorem SchedContext.releaseOne_eq_impl :
    @SchedContext.releaseOne = @SchedContext.releaseOneImpl := by
  funext sc now
  unfold SchedContext.releaseOne SchedContext.releaseOneImpl SchedContext.refillPop
    refillPopTakes refillPopCount refillSlotSelect SchedContext.tailUsed
  split
  · rename_i h
    obtain ⟨-, hP, -⟩ := h
    by_cases hc : 0 < min sc.refillTailCount refillTailCapacity <;> simp [hP, hc]
  · rfl

/-- WS-ZA ZA6.4: whether a release has a refill to take. -/
@[inline] def SchedContext.releaseDue (sc : SchedContext) (now : Nat) : Bool :=
  sc.budgetRemaining.val == 0 && sc.refillHeadPresent && decide (sc.refillHeadEligibleAt ≤ now)

/-- WS-ZA ZA6.4: the releases of a used-up head, at most `n`: while the head is
used up and the first pending refill is released by `now`, it becomes the head. -/
def SchedContext.releaseReadyHeadN : Nat → SchedContext → Nat → SchedContext
  | 0, sc, _ => sc
  | n + 1, sc, now =>
    if sc.releaseDue now then SchedContext.releaseReadyHeadN n (sc.releaseOne now) now else sc

/-- WS-ZA ZA6.4: the release of a used-up head (seL4-MCS's `awaken` of a context
whose head refill is ready): the head is replaced by the pending refills released
by `now`, one at a time, until one holds budget or none is released. -/
@[inline] def SchedContext.releaseReadyHead (sc : SchedContext) (now : Nat) : SchedContext :=
  SchedContext.releaseReadyHeadN maxReplenishments sc now

/-- **A property every release keeps holds after the releases.** -/
theorem SchedContext.releaseReadyHeadN_induction (Q : SchedContext → Prop) (now : Nat)
    (hstep : ∀ s, Q s → Q (s.releaseOne now)) :
    ∀ (n : Nat) (s : SchedContext), Q s → Q (SchedContext.releaseReadyHeadN n s now)
  | 0, _, h => h
  | n + 1, s, h => by
    unfold SchedContext.releaseReadyHeadN
    split
    · exact SchedContext.releaseReadyHeadN_induction Q now hstep n _ (hstep s h)
    · exact h

/-- WS-ZA ZA6.4: `refill_unblock_check`'s merge: while the first pending refill
is released by the head's end, it joins the head (at most `n` merges). -/
def SchedContext.mergeOverlapping : Nat → SchedContext → SchedContext
  | 0, sc => sc
  | n + 1, sc =>
    if sc.refillHeadPresent = true ∧
        sc.refillHeadEligibleAt ≤ sc.periodStart + sc.budgetRemaining.val then
      let b := sc.budgetRemaining.val + sc.refillHeadAmount
      SchedContext.mergeOverlapping n { sc.refillPop with budgetRemaining := ⟨b⟩ }
    else sc

/-- WS-ZA ZA6.4: seL4-MCS's `refill_unblock_check`: a head released by `t` is
moved to `t`, and the pending refills it now overlaps merge into it. -/
@[inline] def SchedContext.refillUnblockCheck (sc : SchedContext) (t : Nat) : SchedContext :=
  if 0 < sc.budgetRemaining.val ∧ sc.periodStart ≤ t then
    SchedContext.mergeOverlapping maxReplenishments { sc with periodStart := t }
  else sc

/-- WS-ZA ZA6.4: the charge: `usage` run from `start` to `now`.  The head is
made ready at the run's start (`refill_unblock_check`, as seL4-MCS runs it when
the context is switched to), charged (`refill_budget_check`), and, when used up,
replaced by a pending refill released by `now`.

WS-ZA ZA6.5: the time run, `now - start`, is added to the context's consumed
time (seL4-MCS's `chargeBudget`: `sc->scConsumed += consumed`).  It is the time
that passed, not the refill charge: the tick charges the unit it ran, `now - 1`
to `now`, and adds that unit; the yield charges the whole head from `now`
(`refill_budget_check` of the head's amount) and adds nothing, as seL4-MCS's
`handleYield` sets `scConsumed` back to the time actually consumed
(`scConsumed + ksConsumed`), and this kernel charges every unit at the tick
that ends it, so none is left uncharged at a yield. -/
@[inline] def SchedContext.chargeBudget (sc : SchedContext) (start usage now : Nat) :
    SchedContext :=
  (((sc.refillUnblockCheck start).refillBudgetCheck usage).releaseReadyHead now).addConsumed
    (now - start)

/-- WS-ZA ZA6.4: seL4-MCS's `refill_new`: the budget in one refill, released now.
-/
@[inline] def SchedContext.refillNew (sc : SchedContext) (budget now : Nat) : SchedContext :=
  { sc.refillClear with
    budgetRemaining := ⟨budget⟩
    periodStart := now
    isActive := decide (0 < budget) }

/-- WS-ZA ZA6.4: seL4-MCS's `refill_update`, from a head of `ha` released at
`ht`: the head alone is kept, moved to `now` when released, trimmed to the new
budget `nb` or followed by the rest of it one new period `np` later. -/
@[inline] def SchedContext.refillUpdateFrom (sc : SchedContext) (ha ht nb np now : Nat) :
    SchedContext :=
  if ht ≤ now then
    let s : SchedContext := { sc.refillClear with
      budgetRemaining := ⟨min ha nb⟩
      periodStart := now
      isActive := decide (0 < min ha nb) }
    if ha < nb then s.refillPush (nb - ha) (now + np) else s
  else
    let s : SchedContext := ({ sc.refillClear with
      budgetRemaining := ⟨0⟩
      periodStart := ht
      isActive := false } : SchedContext).refillPush (min ha nb) ht
    if ha < nb then s.refillPush (nb - ha) (ht + np) else s

/-- WS-ZA ZA6.4: seL4-MCS's `refill_update` on the context: its head is the
refill being consumed, or the first pending one when that is used up; a context
with neither takes `refill_new`. -/
@[inline] def SchedContext.refillUpdate (sc : SchedContext) (nb np now : Nat) : SchedContext :=
  if 0 < sc.budgetRemaining.val then
    sc.refillUpdateFrom sc.budgetRemaining.val sc.periodStart nb np now
  else if sc.refillHeadPresent then
    sc.refillUpdateFrom sc.refillHeadAmount sc.refillHeadEligibleAt nb np now
  else sc.refillNew nb now

-- ============================================================================
-- The refill operations write the refills alone
-- ============================================================================

/-- WS-ZA ZA6.4: a context with its refills erased — the head (`budgetRemaining`,
`periodStart`, `isActive`) and the pending refills: every field the refill
operations leave alone.  WS-ZA ZA6.5: and the consumed time, which the charge
adds to (`SchedContext.chargeBudget`). -/
@[inline] def SchedContext.refillsErased (sc : SchedContext) : SchedContext :=
  { sc.pendingErased with
    budgetRemaining := ⟨0⟩
    periodStart := 0
    isActive := false
    consumed := 0 }

/-- WS-ZA ZA6.5: the consumed time is erased with the refills. -/
@[simp] theorem SchedContext.addConsumed_refillsErased (sc : SchedContext) (t : Nat) :
    (sc.addConsumed t).refillsErased = sc.refillsErased := rfl

theorem SchedContext.refillsErased_of_pendingErased {sc sc' : SchedContext}
    (h : sc'.pendingErased = sc.pendingErased) : sc'.refillsErased = sc.refillsErased := by
  unfold SchedContext.refillsErased; rw [h]

@[simp] theorem SchedContext.refillsErased_head (sc : SchedContext) (b : Budget) (t : Nat)
    (a : Bool) :
    ({ sc with budgetRemaining := b, periodStart := t, isActive := a } : SchedContext).refillsErased =
      sc.refillsErased := rfl

/-- The fields the refill operations leave alone, read through the erasure. -/
theorem SchedContext.fields_of_refillsErased {sc sc' : SchedContext}
    (h : sc'.refillsErased = sc.refillsErased) :
    sc'.scId = sc.scId ∧ sc'.budget = sc.budget ∧ sc'.period = sc.period ∧
      sc'.priority = sc.priority ∧ sc'.deadline = sc.deadline ∧ sc'.domain = sc.domain ∧
      sc'.boundThreadCode = sc.boundThreadCode ∧ sc'.scReply = sc.scReply ∧
      sc'.donationOrigin = sc.donationOrigin ∧
      sc'.releaseNextCode = sc.releaseNextCode ∧ sc'.releaseCoreCode = sc.releaseCoreCode ∧
      sc'.releaseAt = sc.releaseAt := by
  have f : ∀ {α : Type} (g : SchedContext → α), (∀ s, g s.refillsErased = g s) →
      g sc' = g sc := fun g hg => by rw [← hg sc', h, hg]
  exact ⟨f (·.scId) (fun _ => rfl), f (·.budget) (fun _ => rfl), f (·.period) (fun _ => rfl),
    f (·.priority) (fun _ => rfl), f (·.deadline) (fun _ => rfl), f (·.domain) (fun _ => rfl),
    f (·.boundThreadCode) (fun _ => rfl), f (·.scReply) (fun _ => rfl),
    f (·.donationOrigin) (fun _ => rfl),
    f (·.releaseNextCode) (fun _ => rfl), f (·.releaseCoreCode) (fun _ => rfl),
    f (·.releaseAt) (fun _ => rfl)⟩

/-- The bound thread, read through the erasure. -/
theorem SchedContext.boundThread_of_refillsErased {sc sc' : SchedContext}
    (h : sc'.refillsErased = sc.refillsErased) : sc'.boundThread = sc.boundThread := by
  unfold SchedContext.boundThread
  rw [(SchedContext.fields_of_refillsErased h).2.2.2.2.2.2.1]

/-- WS-ZA ZA6.6: the yield-from code, read through the erasure. -/
theorem SchedContext.yieldFromCode_of_refillsErased {sc sc' : SchedContext}
    (h : sc'.refillsErased = sc.refillsErased) : sc'.yieldFromCode = sc.yieldFromCode := by
  have e := congrArg SchedContext.yieldFromCode h
  exact e

theorem SchedContext.scheduleUsed_refillsErased (sc : SchedContext) (a t : Nat) :
    (sc.scheduleUsed a t).refillsErased = sc.refillsErased :=
  SchedContext.refillsErased_of_pendingErased (sc.scheduleUsed_pendingErased a t)

theorem SchedContext.refillBudgetCheck_refillsErased (sc : SchedContext) (u : Nat) :
    (sc.refillBudgetCheck u).refillsErased = sc.refillsErased := by
  unfold SchedContext.refillBudgetCheck
  dsimp only
  split
  · rfl
  · split
    · rw [SchedContext.scheduleUsed_refillsErased]; rfl
    · rw [SchedContext.scheduleUsed_refillsErased]; rfl

theorem SchedContext.releaseOne_refillsErased (sc : SchedContext) (now : Nat) :
    (sc.releaseOne now).refillsErased = sc.refillsErased := by
  unfold SchedContext.releaseOne
  split
  · show ({ sc.refillPop with budgetRemaining := _, periodStart := _, isActive := _ } :
      SchedContext).refillsErased = _
    rw [SchedContext.refillsErased_head]
    exact SchedContext.refillsErased_of_pendingErased (sc' := sc.refillPop) sc.refillPop_pendingErased
  · rfl

theorem SchedContext.releaseReadyHead_refillsErased (sc : SchedContext) (now : Nat) :
    (sc.releaseReadyHead now).refillsErased = sc.refillsErased :=
  SchedContext.releaseReadyHeadN_induction (fun s => s.refillsErased = sc.refillsErased) now
    (fun s h => (s.releaseOne_refillsErased now).trans h) _ sc rfl

theorem SchedContext.mergeOverlapping_refillsErased :
    ∀ (n : Nat) (sc : SchedContext),
      (SchedContext.mergeOverlapping n sc).refillsErased = sc.refillsErased
  | 0, _ => rfl
  | n + 1, sc => by
    unfold SchedContext.mergeOverlapping
    split
    · rw [SchedContext.mergeOverlapping_refillsErased n]
      exact SchedContext.refillsErased_of_pendingErased (sc' := sc.refillPop) sc.refillPop_pendingErased
    · rfl

theorem SchedContext.refillUnblockCheck_refillsErased (sc : SchedContext) (t : Nat) :
    (sc.refillUnblockCheck t).refillsErased = sc.refillsErased := by
  unfold SchedContext.refillUnblockCheck
  split
  · rw [SchedContext.mergeOverlapping_refillsErased]; rfl
  · rfl

/-- **The charge writes the refills alone.** -/
theorem SchedContext.chargeBudget_refillsErased (sc : SchedContext) (start usage now : Nat) :
    (sc.chargeBudget start usage now).refillsErased = sc.refillsErased := by
  unfold SchedContext.chargeBudget
  rw [SchedContext.addConsumed_refillsErased, SchedContext.releaseReadyHead_refillsErased, SchedContext.refillBudgetCheck_refillsErased,
    SchedContext.refillUnblockCheck_refillsErased]

-- ============================================================================
-- WS-ZA ZA6.5: the consumed time every charge adds
-- ============================================================================

/-- The consumed time reads through the pending refills' erasure. -/
theorem SchedContext.consumed_of_pendingErased {sc sc' : SchedContext}
    (h : sc'.pendingErased = sc.pendingErased) : sc'.consumed = sc.consumed := by
  have e := congrArg (fun s : SchedContext => s.consumed) h
  exact e

theorem SchedContext.refillBudgetCheck_consumed (sc : SchedContext) (u : Nat) :
    (sc.refillBudgetCheck u).consumed = sc.consumed := by
  unfold SchedContext.refillBudgetCheck
  dsimp only
  split
  · rfl
  · split
    · exact (SchedContext.consumed_of_pendingErased (SchedContext.scheduleUsed_pendingErased _ _ _)).trans rfl
    · exact (SchedContext.consumed_of_pendingErased (SchedContext.scheduleUsed_pendingErased _ _ _)).trans rfl

theorem SchedContext.releaseOne_consumed (sc : SchedContext) (now : Nat) :
    (sc.releaseOne now).consumed = sc.consumed := by
  unfold SchedContext.releaseOne
  split
  · exact (SchedContext.consumed_of_pendingErased (sc' := sc.refillPop) sc.refillPop_pendingErased :)
  · rfl

theorem SchedContext.releaseReadyHead_consumed (sc : SchedContext) (now : Nat) :
    (sc.releaseReadyHead now).consumed = sc.consumed :=
  SchedContext.releaseReadyHeadN_induction (fun s => s.consumed = sc.consumed) now
    (fun s h => (s.releaseOne_consumed now).trans h) _ sc rfl

theorem SchedContext.mergeOverlapping_consumed :
    ∀ (n : Nat) (sc : SchedContext), (SchedContext.mergeOverlapping n sc).consumed = sc.consumed
  | 0, _ => rfl
  | n + 1, sc => by
    unfold SchedContext.mergeOverlapping
    split
    · rw [SchedContext.mergeOverlapping_consumed n]
      exact (SchedContext.consumed_of_pendingErased (sc' := sc.refillPop) sc.refillPop_pendingErased :)
    · rfl

theorem SchedContext.refillUnblockCheck_consumed (sc : SchedContext) (t : Nat) :
    (sc.refillUnblockCheck t).consumed = sc.consumed := by
  unfold SchedContext.refillUnblockCheck
  split
  · rw [SchedContext.mergeOverlapping_consumed]
  · rfl

/-- **The charge adds the time run to the consumed count** (seL4-MCS's
`chargeBudget`: `sc->scConsumed += consumed`). -/
theorem SchedContext.chargeBudget_consumed (sc : SchedContext) (start usage now : Nat) :
    (sc.chargeBudget start usage now).consumed = sc.consumed + (now - start) := by
  unfold SchedContext.chargeBudget SchedContext.addConsumed
  dsimp only
  rw [SchedContext.releaseReadyHead_consumed, SchedContext.refillBudgetCheck_consumed,
    SchedContext.refillUnblockCheck_consumed]

/-- The timer tick's charge (the unit run from `now - 1`, charged by `now`) adds
that unit. -/
theorem SchedContext.chargeBudget_tick_consumed (sc : SchedContext) (now : Nat) (h : 1 ≤ now) :
    (sc.chargeBudget (now - 1) 1 now).consumed = sc.consumed + 1 := by
  rw [SchedContext.chargeBudget_consumed]; omega

/-- The yield's charge (the whole head, from `now`) adds nothing: seL4-MCS's
`handleYield` keeps the consumed count at the time actually run, and this kernel
has charged every unit run by `now` at the tick that ended it. -/
theorem SchedContext.chargeBudget_forfeit_consumed (sc : SchedContext) (usage now : Nat) :
    (sc.chargeBudget now usage now).consumed = sc.consumed := by
  rw [SchedContext.chargeBudget_consumed, Nat.sub_self, Nat.add_zero]

theorem SchedContext.refillNew_refillsErased (sc : SchedContext) (budget now : Nat) :
    (sc.refillNew budget now).refillsErased = sc.refillsErased := rfl

theorem SchedContext.refillUpdateFrom_refillsErased (sc : SchedContext) (ha ht nb np now : Nat) :
    (sc.refillUpdateFrom ha ht nb np now).refillsErased = sc.refillsErased := by
  unfold SchedContext.refillUpdateFrom
  split
  · dsimp only
    split
    · rw [SchedContext.refillsErased_of_pendingErased (SchedContext.refillPush_pendingErased _ _ _)]
      rfl
    · rfl
  · dsimp only
    split
    · rw [SchedContext.refillsErased_of_pendingErased (SchedContext.refillPush_pendingErased _ _ _),
        SchedContext.refillsErased_of_pendingErased (SchedContext.refillPush_pendingErased _ _ _)]
      rfl
    · rw [SchedContext.refillsErased_of_pendingErased (SchedContext.refillPush_pendingErased _ _ _)]
      rfl

/-- **Configure's refills write the refills alone.** -/
theorem SchedContext.refillUpdate_refillsErased (sc : SchedContext) (nb np now : Nat) :
    (sc.refillUpdate nb np now).refillsErased = sc.refillsErased := by
  unfold SchedContext.refillUpdate
  split
  · exact sc.refillUpdateFrom_refillsErased _ _ _ _ _
  · split
    · exact sc.refillUpdateFrom_refillsErased _ _ _ _ _
    · exact sc.refillNew_refillsErased _ _

-- ============================================================================
-- Conservation: the head plus the pending refills is the budget
-- ============================================================================

/-- WS-ZA ZA6.4: the context's refills in total: the head's amount and every
pending refill's.  Configure sets it to the budget and every other operation
keeps it (`Invariant/Defs.lean`, `refillsConserved`). -/
@[inline] def SchedContext.refillTotal (sc : SchedContext) : Nat :=
  sc.budgetRemaining.val + sumReplenishments sc.replenishments

/-- The pending refills' edits leave the head. -/
theorem SchedContext.budgetRemaining_of_pendingErased {sc sc' : SchedContext}
    (h : sc'.pendingErased = sc.pendingErased) : sc'.budgetRemaining = sc.budgetRemaining :=
  (SchedContext.fields_of_pendingErased h).2.2.2.2.2.2.1

theorem SchedContext.scheduleUsed_refillTotal (sc : SchedContext) (a t : Nat) :
    (sc.scheduleUsed a t).refillTotal = sc.refillTotal + a := by
  unfold SchedContext.refillTotal
  rw [SchedContext.budgetRemaining_of_pendingErased (sc.scheduleUsed_pendingErased a t),
    sc.scheduleUsed_replenishments, sumReplenishments_scheduleUsedList]
  simp only; omega

theorem SchedContext.refillBudgetCheck_refillTotal (sc : SchedContext) (usage : Nat) :
    (sc.refillBudgetCheck usage).refillTotal = sc.refillTotal := by
  unfold SchedContext.refillBudgetCheck
  dsimp only
  split
  · rfl
  · rename_i h0
    split
    · rw [SchedContext.scheduleUsed_refillTotal]
      unfold SchedContext.refillTotal; simp only [SchedContext.replenishments_mk_self]; omega
    · rw [SchedContext.scheduleUsed_refillTotal]
      unfold SchedContext.refillTotal; simp only [SchedContext.replenishments_mk_self]; omega

theorem SchedContext.releaseOne_refillTotal (sc : SchedContext) (now : Nat) :
    (sc.releaseOne now).refillTotal = sc.refillTotal := by
  unfold SchedContext.releaseOne
  split
  · rename_i h
    obtain ⟨hB, hP, -⟩ := h
    unfold SchedContext.refillTotal
    show sc.refillHeadAmount + sumReplenishments sc.refillPop.replenishments = _
    rw [sc.refillPop_replenishments, sc.replenishments_of_present' hP, hB]
    simp [sumReplenishments]
  · rfl

theorem SchedContext.releaseReadyHead_refillTotal (sc : SchedContext) (now : Nat) :
    (sc.releaseReadyHead now).refillTotal = sc.refillTotal :=
  SchedContext.releaseReadyHeadN_induction (fun s => s.refillTotal = sc.refillTotal) now
    (fun s h => (s.releaseOne_refillTotal now).trans h) _ sc rfl

theorem SchedContext.mergeOverlapping_refillTotal :
    ∀ (n : Nat) (sc : SchedContext), (SchedContext.mergeOverlapping n sc).refillTotal = sc.refillTotal
  | 0, _ => rfl
  | n + 1, sc => by
    unfold SchedContext.mergeOverlapping
    split
    · rename_i h
      rw [SchedContext.mergeOverlapping_refillTotal n]
      unfold SchedContext.refillTotal
      show sc.budgetRemaining.val + sc.refillHeadAmount +
        sumReplenishments sc.refillPop.replenishments = _
      rw [sc.refillPop_replenishments, sc.replenishments_of_present' h.1]
      simp [sumReplenishments]; omega
    · rfl

theorem SchedContext.refillUnblockCheck_refillTotal (sc : SchedContext) (t : Nat) :
    (sc.refillUnblockCheck t).refillTotal = sc.refillTotal := by
  unfold SchedContext.refillUnblockCheck
  split
  · rw [SchedContext.mergeOverlapping_refillTotal]; rfl
  · rfl

/-- WS-ZA ZA6.5: the consumed time holds no budget. -/
@[simp] theorem SchedContext.addConsumed_refillTotal (sc : SchedContext) (t : Nat) :
    (sc.addConsumed t).refillTotal = sc.refillTotal := rfl

/-- **The charge keeps the total**: what it takes off the head it schedules as
a refill, and the merges and the release move amounts between refills. -/
theorem SchedContext.chargeBudget_refillTotal (sc : SchedContext) (start usage now : Nat) :
    (sc.chargeBudget start usage now).refillTotal = sc.refillTotal := by
  unfold SchedContext.chargeBudget
  rw [SchedContext.addConsumed_refillTotal, SchedContext.releaseReadyHead_refillTotal, SchedContext.refillBudgetCheck_refillTotal,
    SchedContext.refillUnblockCheck_refillTotal]

theorem SchedContext.refillNew_refillTotal (sc : SchedContext) (budget now : Nat) :
    (sc.refillNew budget now).refillTotal = budget := by
  simp [SchedContext.refillNew, SchedContext.refillTotal, SchedContext.refillClear,
    SchedContext.replenishments, sumReplenishments]

@[simp] theorem SchedContext.refillClear_refillHeadPresent (sc : SchedContext) :
    sc.refillClear.refillHeadPresent = false := rfl

/-- A push onto no pending refill is the one pending refill. -/
theorem SchedContext.refillPush_replenishments_of_empty (s : SchedContext) (a t : Nat)
    (h : s.refillHeadPresent = false) :
    (s.refillPush a t).replenishments = [{ amount := ⟨a⟩, eligibleAt := t }] := by
  have hc : s.replenishments = [] := by simp [SchedContext.replenishments, h]
  rw [SchedContext.refillPush_replenishments _ _ _ (by simp [hc, maxReplenishments]), hc]; rfl

/-- Two pushes onto no pending refill are the two. -/
theorem SchedContext.refillPush_refillPush_replenishments_of_empty (s : SchedContext)
    (a t a' t' : Nat) (h : s.refillHeadPresent = false) :
    ((s.refillPush a t).refillPush a' t').replenishments =
      [{ amount := ⟨a⟩, eligibleAt := t }, { amount := ⟨a'⟩, eligibleAt := t' }] := by
  have h1 := s.refillPush_replenishments_of_empty a t h
  rw [SchedContext.refillPush_replenishments _ _ _ (by simp [h1, maxReplenishments]), h1]; rfl

theorem SchedContext.refillPush_budgetRemaining (s : SchedContext) (a t : Nat) :
    (s.refillPush a t).budgetRemaining = s.budgetRemaining :=
  SchedContext.budgetRemaining_of_pendingErased (s.refillPush_pendingErased a t)

theorem SchedContext.refillUpdateFrom_refillTotal (sc : SchedContext) (ha ht nb np now : Nat) :
    (sc.refillUpdateFrom ha ht nb np now).refillTotal = nb := by
  unfold SchedContext.refillUpdateFrom SchedContext.refillTotal
  split
  · dsimp only
    split
    · simp only [SchedContext.refillPush_budgetRemaining]
      rw [SchedContext.refillPush_replenishments_of_empty _ _ _ rfl]
      simp [sumReplenishments]; omega
    · simp [SchedContext.replenishments, sumReplenishments]; omega
  · dsimp only
    split
    · simp only [SchedContext.refillPush_budgetRemaining]
      rw [SchedContext.refillPush_refillPush_replenishments_of_empty _ _ _ _ _ rfl]
      simp [sumReplenishments]; omega
    · simp only [SchedContext.refillPush_budgetRemaining]
      rw [SchedContext.refillPush_replenishments_of_empty _ _ _ rfl]
      simp [sumReplenishments]; omega

theorem SchedContext.refillUpdate_refillTotal (sc : SchedContext) (nb np now : Nat) :
    (sc.refillUpdate nb np now).refillTotal = nb := by
  unfold SchedContext.refillUpdate
  split
  · exact SchedContext.refillUpdateFrom_refillTotal ..
  · split
    · exact SchedContext.refillUpdateFrom_refillTotal ..
    · exact SchedContext.refillNew_refillTotal ..

-- ============================================================================
-- The refills stay positive and within capacity
-- ============================================================================

/-- WS-ZA ZA6.4: every pending refill holds a positive amount. -/
def SchedContext.refillsPositive (sc : SchedContext) : Prop :=
  ∀ r ∈ sc.replenishments, 0 < r.amount.val

/-- WS-ZA ZA6.4: the refills, the head among them, fit the context's storage
(seL4's `refill_size ≤ refill_max`). -/
def SchedContext.refillsFit (sc : SchedContext) : Prop :=
  sc.refillSize ≤ maxReplenishments

theorem SchedContext.refillsPositive_of_replenishments {sc sc' : SchedContext}
    (h : sc'.replenishments = sc.replenishments) (hp : sc.refillsPositive) : sc'.refillsPositive :=
  fun r hr => hp r (h ▸ hr)

theorem SchedContext.refillsPositive_tail {sc sc' : SchedContext}
    (h : sc'.replenishments = sc.replenishments.tail) (hp : sc.refillsPositive) :
    sc'.refillsPositive :=
  fun r hr => hp r (List.mem_of_mem_tail (h ▸ hr))

theorem SchedContext.scheduleUsed_refillsPositive (sc : SchedContext) (a t : Nat)
    (hp : sc.refillsPositive) (ha : 0 < a) : (sc.scheduleUsed a t).refillsPositive := by
  intro r hr
  rw [sc.scheduleUsed_replenishments] at hr
  exact scheduleUsedList_pos _ _ _ hp ha r hr

theorem SchedContext.scheduleUsed_refillSize_le (sc : SchedContext) (a t : Nat)
    (h : sc.refillSize ≤ maxReplenishments) (hB : sc.budgetRemaining.val = 0 ∨ sc.refillSize < maxReplenishments ∨
      sc.replenishments ≠ []) :
    (sc.scheduleUsed a t).refillSize ≤ maxReplenishments := by
  have hB' := SchedContext.budgetRemaining_of_pendingErased (sc.scheduleUsed_pendingErased a t)
  rw [SchedContext.refillSize_eq, hB', sc.scheduleUsed_replenishments]
  rw [SchedContext.refillSize_eq] at h hB
  rcases scheduleUsedList_length sc.refillFull { amount := ⟨a⟩, eligibleAt := t } sc.replenishments
    with h1 | ⟨hF, h1⟩ | ⟨h0, h1⟩
  · omega
  · simp only [SchedContext.refillFull, decide_eq_false_iff_not, SchedContext.refillSize_eq] at hF
    omega
  · rw [h1]; rw [h0] at hB h; simp at hB h ⊢; unfold maxReplenishments; split <;> omega

theorem SchedContext.refillBudgetCheck_refillsPositive (sc : SchedContext) (usage : Nat)
    (hp : sc.refillsPositive) : (sc.refillBudgetCheck usage).refillsPositive := by
  unfold SchedContext.refillBudgetCheck
  dsimp only
  split
  · exact hp
  · rename_i h0
    split
    · exact SchedContext.scheduleUsed_refillsPositive _ _ _ hp (by omega)
    · exact SchedContext.scheduleUsed_refillsPositive _ _ _ hp (by omega)

theorem SchedContext.refillBudgetCheck_refillsFit (sc : SchedContext) (usage : Nat)
    (hf : sc.refillsFit) : (sc.refillBudgetCheck usage).refillsFit := by
  unfold SchedContext.refillBudgetCheck SchedContext.refillsFit at *
  dsimp only
  split
  · exact hf
  · rename_i h0
    split
    · apply SchedContext.scheduleUsed_refillSize_le
      · rw [SchedContext.refillSize_eq] at hf ⊢
        simp only [SchedContext.replenishments_mk_self] at *; split at hf <;> simp <;> omega
      · left; rfl
    · apply SchedContext.scheduleUsed_refillSize_le
      · rw [SchedContext.refillSize_eq] at hf ⊢
        simp only [SchedContext.replenishments_mk_self] at *
        rw [if_pos (by omega)] at hf; rw [if_pos (show 0 < sc.budgetRemaining.val - usage by omega)]
        exact hf
      · rw [SchedContext.refillSize_eq] at hf
        simp only [SchedContext.replenishments_mk_self]
        by_cases hE : sc.replenishments = []
        · right; left; rw [SchedContext.refillSize_eq]; simp only [SchedContext.replenishments_mk_self, hE]
          simp [maxReplenishments]; split <;> omega
        · right; right; exact hE

theorem SchedContext.releaseOne_refillsPositive (sc : SchedContext) (now : Nat)
    (hp : sc.refillsPositive) : (sc.releaseOne now).refillsPositive := by
  unfold SchedContext.releaseOne
  split
  · exact SchedContext.refillsPositive_tail (sc.refillPop_replenishments) hp
  · exact hp

theorem SchedContext.releaseReadyHead_refillsPositive (sc : SchedContext) (now : Nat)
    (hp : sc.refillsPositive) : (sc.releaseReadyHead now).refillsPositive :=
  SchedContext.releaseReadyHeadN_induction (fun s => s.refillsPositive) now
    (fun s h => s.releaseOne_refillsPositive now h) _ sc hp

theorem SchedContext.releaseOne_refillsFit (sc : SchedContext) (now : Nat)
    (hf : sc.refillsFit) : (sc.releaseOne now).refillsFit := by
  unfold SchedContext.releaseOne SchedContext.refillsFit at *
  split
  · rename_i h
    obtain ⟨hB, hP, -⟩ := h
    rw [SchedContext.refillSize_eq] at hf ⊢
    show _ + sc.refillPop.replenishments.length ≤ _
    rw [sc.refillPop_replenishments, sc.replenishments_of_present' hP] at *
    rw [hB] at hf; simp at hf ⊢; split <;> omega
  · exact hf

theorem SchedContext.releaseReadyHead_refillsFit (sc : SchedContext) (now : Nat)
    (hf : sc.refillsFit) : (sc.releaseReadyHead now).refillsFit :=
  SchedContext.releaseReadyHeadN_induction (fun s => s.refillsFit) now
    (fun s h => s.releaseOne_refillsFit now h) _ sc hf

/-- After the release, a used-up head means the first pending refill is not yet
released: the release queue keys the context after `now`. -/
theorem SchedContext.releaseDue_iff (sc : SchedContext) (now : Nat) :
    sc.releaseDue now = true ↔
      (sc.budgetRemaining.val = 0 ∧ sc.refillHeadPresent = true ∧ sc.refillHeadEligibleAt ≤ now) := by
  simp [SchedContext.releaseDue, and_assoc]

theorem SchedContext.releaseOne_replenishments_of_due (sc : SchedContext) (now : Nat)
    (h : sc.releaseDue now = true) : (sc.releaseOne now).replenishments = sc.replenishments.tail := by
  unfold SchedContext.releaseOne
  rw [if_pos ((sc.releaseDue_iff now).mp h)]
  exact sc.refillPop_replenishments

/-- **After the releases, a used-up head means the first pending refill is not
yet released**: the release queue keys the context after `now`. -/
theorem SchedContext.releaseReadyHeadN_pending_after (now : Nat) :
    ∀ (n : Nat) (s : SchedContext), s.replenishments.length ≤ n →
      (SchedContext.releaseReadyHeadN n s now).budgetRemaining.val = 0 →
      (SchedContext.releaseReadyHeadN n s now).refillHeadPresent = true →
      now < (SchedContext.releaseReadyHeadN n s now).refillHeadEligibleAt
  | 0, s, hl, _, hP => by
    rw [SchedContext.replenishments_length] at hl
    simp only [SchedContext.releaseReadyHeadN] at hP ⊢
    rw [if_pos hP] at hl; omega
  | n + 1, s, hl, hB, hP => by
    unfold SchedContext.releaseReadyHeadN at *
    split at hB
    · rename_i hd
      rw [if_pos hd] at hP ⊢
      refine SchedContext.releaseReadyHeadN_pending_after now n _ ?_ hB hP
      rw [s.releaseOne_replenishments_of_due now hd, List.length_tail]; omega
    · rename_i hd
      rw [if_neg hd] at hP ⊢
      exact Nat.lt_of_not_le fun hle => hd ((s.releaseDue_iff now).mpr ⟨hB, hP, hle⟩)

theorem SchedContext.releaseReadyHead_pending_after (sc : SchedContext) (now : Nat)
    (hB : (sc.releaseReadyHead now).budgetRemaining.val = 0)
    (hP : (sc.releaseReadyHead now).refillHeadPresent = true) :
    now < (sc.releaseReadyHead now).refillHeadEligibleAt :=
  SchedContext.releaseReadyHeadN_pending_after now _ sc sc.replenishments_length_le hB hP

theorem SchedContext.mergeOverlapping_refillsPositive :
    ∀ (n : Nat) (sc : SchedContext), sc.refillsPositive →
      (SchedContext.mergeOverlapping n sc).refillsPositive
  | 0, _, hp => hp
  | n + 1, sc, hp => by
    unfold SchedContext.mergeOverlapping
    split
    · exact SchedContext.mergeOverlapping_refillsPositive n _
        (SchedContext.refillsPositive_tail (sc.refillPop_replenishments) hp)
    · exact hp

theorem SchedContext.mergeOverlapping_refillsFit :
    ∀ (n : Nat) (sc : SchedContext), 0 < sc.budgetRemaining.val → sc.refillsFit →
      (SchedContext.mergeOverlapping n sc).refillsFit ∧
        0 < (SchedContext.mergeOverlapping n sc).budgetRemaining.val
  | 0, _, hB, hf => ⟨hf, hB⟩
  | n + 1, sc, hB, hf => by
    unfold SchedContext.mergeOverlapping
    split
    · rename_i h
      refine SchedContext.mergeOverlapping_refillsFit n _ (by simp only []; omega) ?_
      unfold SchedContext.refillsFit at hf ⊢
      rw [SchedContext.refillSize_eq] at hf ⊢
      show _ + sc.refillPop.replenishments.length ≤ _
      rw [sc.refillPop_replenishments, sc.replenishments_of_present' h.1] at *
      simp at hf ⊢; rw [if_pos hB] at hf; rw [if_pos (by omega)]; omega
    · exact ⟨hf, hB⟩

theorem SchedContext.refillUnblockCheck_refillsPositive (sc : SchedContext) (t : Nat)
    (hp : sc.refillsPositive) : (sc.refillUnblockCheck t).refillsPositive := by
  unfold SchedContext.refillUnblockCheck
  split
  · exact SchedContext.mergeOverlapping_refillsPositive _ _ hp
  · exact hp

theorem SchedContext.refillUnblockCheck_refillsFit (sc : SchedContext) (t : Nat)
    (hf : sc.refillsFit) : (sc.refillUnblockCheck t).refillsFit := by
  unfold SchedContext.refillUnblockCheck
  split
  · rename_i h
    exact (SchedContext.mergeOverlapping_refillsFit _ { sc with periodStart := t } h.1 hf).1
  · exact hf

theorem SchedContext.chargeBudget_refillsPositive (sc : SchedContext) (start usage now : Nat)
    (hp : sc.refillsPositive) : (sc.chargeBudget start usage now).refillsPositive :=
  SchedContext.releaseReadyHead_refillsPositive _ _
    (SchedContext.refillBudgetCheck_refillsPositive _ _
      (SchedContext.refillUnblockCheck_refillsPositive _ _ hp))

theorem SchedContext.chargeBudget_refillsFit (sc : SchedContext) (start usage now : Nat)
    (hf : sc.refillsFit) : (sc.chargeBudget start usage now).refillsFit :=
  SchedContext.releaseReadyHead_refillsFit _ _
    (SchedContext.refillBudgetCheck_refillsFit _ _
      (SchedContext.refillUnblockCheck_refillsFit _ _ hf))

-- ============================================================================
-- The sliding window: a context runs at most its budget in any period
-- ============================================================================

/-! A refill of `a` released at `t` is `a` units of time the context may run,
the `k`-th of them from `t + k` on.  `refillTokens x r` counts the units of `r`
released before `x`; `SchedContext.tokensBefore sc x` counts the head's (from
`periodStart`) and every pending refill's.  Each charged unit takes the head's
first unit and schedules it again one period after that unit's release
(`refill_budget_check`); the merges and the head's move to the charge's start
only release units later.  So over a window `[w, w + period)` the units run plus
the units still released before the window's end never grow, and they start at
most at the budget (`refill_window_bound`). -/

/-- The units of refill `r` released before `x`. -/
@[inline] def refillTokens (x : Nat) (r : ReplenishmentEntry) : Nat :=
  min r.amount.val (x - r.eligibleAt)

/-- The units of the refills `P` released before `x`. -/
def refillsTokens (x : Nat) : List ReplenishmentEntry → Nat
  | [] => 0
  | r :: rs => refillTokens x r + refillsTokens x rs

theorem refillsTokens_append (x : Nat) (l₁ l₂ : List ReplenishmentEntry) :
    refillsTokens x (l₁ ++ l₂) = refillsTokens x l₁ + refillsTokens x l₂ := by
  induction l₁ with
  | nil => simp [refillsTokens]
  | cons r rs ih => simp only [List.cons_append, refillsTokens, ih]; omega

/-- The context's units released before `x`: its head's, from `periodStart`,
and every pending refill's. -/
def SchedContext.tokensBefore (sc : SchedContext) (x : Nat) : Nat :=
  min sc.budgetRemaining.val (x - sc.periodStart) + refillsTokens x sc.replenishments

/-- Every unit is a unit of the total. -/
theorem refillsTokens_le_sum (x : Nat) :
    ∀ P : List ReplenishmentEntry, refillsTokens x P ≤ sumReplenishments P
  | [] => Nat.le_refl _
  | r :: rs => by
    have := refillsTokens_le_sum x rs
    simp only [refillsTokens, sumReplenishments, refillTokens]; omega

theorem SchedContext.tokensBefore_le_refillTotal (sc : SchedContext) (x : Nat) :
    sc.tokensBefore x ≤ sc.refillTotal := by
  have := refillsTokens_le_sum x sc.replenishments
  unfold SchedContext.tokensBefore SchedContext.refillTotal; omega

/-- `schedule_used` releases no unit earlier than adding the used refill as it
is would. -/
theorem refillsTokens_scheduleUsedList (x : Nat) (full : Bool) (u : ReplenishmentEntry)
    (P : List ReplenishmentEntry) :
    refillsTokens x (scheduleUsedList full u P) ≤ refillsTokens x P + refillTokens x u := by
  unfold scheduleUsedList
  cases hl : P.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hl; subst hl; simp [refillsTokens]
  | some l =>
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
    dsimp only
    split
    · rename_i h
      simp only [List.dropLast_concat, refillsTokens_append, refillsTokens, refillTokens]; omega
    · rename_i h
      split
      · simp only [List.dropLast_concat, refillsTokens_append, refillsTokens, refillTokens]; omega
      · simp only [refillsTokens_append, refillsTokens]; omega

theorem SchedContext.scheduleUsed_tokensBefore (sc : SchedContext) (a t x : Nat) :
    (sc.scheduleUsed a t).tokensBefore x ≤ sc.tokensBefore x + min a (x - t) := by
  obtain ⟨-, -, -, -, -, -, hB, hT, -⟩ := SchedContext.fields_of_pendingErased
    (sc.scheduleUsed_pendingErased a t)
  unfold SchedContext.tokensBefore
  rw [hB, hT, sc.scheduleUsed_replenishments]
  have := refillsTokens_scheduleUsedList x sc.refillFull { amount := ⟨a⟩, eligibleAt := t }
    sc.replenishments
  simp only [refillTokens] at this; omega

/-- **One charge of `u` against a head released at `periodStart`**: the units it
takes off the head before `x` are rescheduled one period later. -/
theorem SchedContext.refillBudgetCheck_tokensBefore (sc : SchedContext) (u x : Nat) :
    (sc.refillBudgetCheck u).tokensBefore x + min (min u sc.budgetRemaining.val) (x - sc.periodStart) ≤
      sc.tokensBefore x +
        min (min u sc.budgetRemaining.val) (x - (sc.periodStart + sc.period.val)) := by
  unfold SchedContext.refillBudgetCheck
  dsimp only
  split
  · rename_i h0
    rcases h0 with h0 | h0 <;> simp [h0]
  · rename_i h0
    split
    · rename_i hle
      have := SchedContext.scheduleUsed_tokensBefore
        ({ sc with budgetRemaining := ⟨0⟩, isActive := false } : SchedContext)
        sc.budgetRemaining.val (sc.periodStart + sc.period.val) x
      have hr : ({ sc with budgetRemaining := ⟨0⟩, isActive := false } : SchedContext).replenishments =
          sc.replenishments := rfl
      unfold SchedContext.tokensBefore at this ⊢
      rw [hr] at this
      rw [Nat.min_eq_right hle]; simp only [Nat.zero_min, Nat.zero_add] at this; omega
    · rename_i hle
      have := SchedContext.scheduleUsed_tokensBefore
        ({ sc with
            budgetRemaining := ⟨sc.budgetRemaining.val - u⟩
            periodStart := sc.periodStart + u
            isActive := true } : SchedContext)
        u (sc.periodStart + sc.period.val) x
      have hr : ({ sc with
            budgetRemaining := ⟨sc.budgetRemaining.val - u⟩
            periodStart := sc.periodStart + u
            isActive := true } : SchedContext).replenishments = sc.replenishments := rfl
      unfold SchedContext.tokensBefore at this ⊢
      rw [hr] at this
      rw [Nat.min_eq_left (show u ≤ sc.budgetRemaining.val by omega)]
      simp only [] at this; omega

/-- The release moves the first pending refill to the head: the same units. -/
theorem SchedContext.releaseOne_tokensBefore (sc : SchedContext) (now x : Nat) :
    (sc.releaseOne now).tokensBefore x = sc.tokensBefore x := by
  unfold SchedContext.releaseOne
  split
  · rename_i h
    obtain ⟨hB, hP, -⟩ := h
    unfold SchedContext.tokensBefore
    show min sc.refillHeadAmount (x - sc.refillHeadEligibleAt) +
      refillsTokens x sc.refillPop.replenishments = _
    rw [sc.refillPop_replenishments, sc.replenishments_of_present' hP, hB]
    simp [refillsTokens, refillTokens]
  · rfl

theorem SchedContext.releaseReadyHead_tokensBefore (sc : SchedContext) (now x : Nat) :
    (sc.releaseReadyHead now).tokensBefore x = sc.tokensBefore x :=
  SchedContext.releaseReadyHeadN_induction (fun s => s.tokensBefore x = sc.tokensBefore x) now
    (fun s h => (s.releaseOne_tokensBefore now x).trans h) _ sc rfl

theorem SchedContext.mergeOverlapping_tokensBefore :
    ∀ (n : Nat) (sc : SchedContext) (x : Nat),
      (SchedContext.mergeOverlapping n sc).tokensBefore x ≤ sc.tokensBefore x
  | 0, _, _ => Nat.le_refl _
  | n + 1, sc, x => by
    unfold SchedContext.mergeOverlapping
    split
    · rename_i h
      refine Nat.le_trans (SchedContext.mergeOverlapping_tokensBefore n _ x) ?_
      unfold SchedContext.tokensBefore
      show min (sc.budgetRemaining.val + sc.refillHeadAmount) (x - sc.refillPop.periodStart) +
        refillsTokens x sc.refillPop.replenishments ≤ _
      obtain ⟨-, -, -, -, -, -, -, hT, -⟩ := SchedContext.fields_of_pendingErased
        sc.refillPop_pendingErased
      rw [hT, sc.refillPop_replenishments, sc.replenishments_of_present' h.1]
      have := h.2
      simp only [List.tail_cons, refillsTokens, refillTokens]; omega
    · exact Nat.le_refl _

theorem SchedContext.refillUnblockCheck_tokensBefore (sc : SchedContext) (t x : Nat) :
    (sc.refillUnblockCheck t).tokensBefore x ≤ sc.tokensBefore x := by
  unfold SchedContext.refillUnblockCheck
  split
  · rename_i h
    refine Nat.le_trans (SchedContext.mergeOverlapping_tokensBefore _ _ x) ?_
    unfold SchedContext.tokensBefore
    simp only [SchedContext.replenishments_mk_self]
    have := h.2; omega
  · exact Nat.le_refl _

/-- The merge keeps the head's release, the period and the budget, and only
adds to the head. -/
theorem SchedContext.mergeOverlapping_fields :
    ∀ (n : Nat) (sc : SchedContext),
      (SchedContext.mergeOverlapping n sc).periodStart = sc.periodStart ∧
        (SchedContext.mergeOverlapping n sc).period = sc.period ∧
        (SchedContext.mergeOverlapping n sc).budget = sc.budget ∧
        sc.budgetRemaining.val ≤ (SchedContext.mergeOverlapping n sc).budgetRemaining.val
  | 0, _ => ⟨rfl, rfl, rfl, Nat.le_refl _⟩
  | n + 1, sc => by
    unfold SchedContext.mergeOverlapping
    split
    · obtain ⟨h1, h2, h3, h4⟩ := SchedContext.mergeOverlapping_fields n
        { sc.refillPop with budgetRemaining := ⟨sc.budgetRemaining.val + sc.refillHeadAmount⟩ }
      obtain ⟨-, hb, hp, -, -, -, -, hT, -⟩ := SchedContext.fields_of_pendingErased
        sc.refillPop_pendingErased
      refine ⟨h1.trans hT, h2.trans hp, h3.trans hb, Nat.le_trans ?_ h4⟩
      show sc.budgetRemaining.val ≤ sc.budgetRemaining.val + sc.refillHeadAmount
      omega
    · exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩

/-- A head made ready at `t` is released at `t`, and only grows. -/
theorem SchedContext.refillUnblockCheck_head (sc : SchedContext) (t : Nat)
    (hB : 0 < sc.budgetRemaining.val) (hT : sc.periodStart ≤ t) :
    (sc.refillUnblockCheck t).periodStart = t ∧ (sc.refillUnblockCheck t).period = sc.period ∧
      (sc.refillUnblockCheck t).budget = sc.budget ∧
      sc.budgetRemaining.val ≤ (sc.refillUnblockCheck t).budgetRemaining.val := by
  unfold SchedContext.refillUnblockCheck
  rw [if_pos ⟨hB, hT⟩]
  exact SchedContext.mergeOverlapping_fields _ { sc with periodStart := t }

theorem SchedContext.refillUnblockCheck_period (sc : SchedContext) (t : Nat) :
    (sc.refillUnblockCheck t).period = sc.period ∧ (sc.refillUnblockCheck t).budget = sc.budget := by
  unfold SchedContext.refillUnblockCheck
  split
  · obtain ⟨-, h2, h3, -⟩ := SchedContext.mergeOverlapping_fields _ { sc with periodStart := t }
    exact ⟨h2, h3⟩
  · exact ⟨rfl, rfl⟩

theorem SchedContext.scheduleUsed_head (sc : SchedContext) (a t : Nat) :
    (sc.scheduleUsed a t).budgetRemaining = sc.budgetRemaining ∧
      (sc.scheduleUsed a t).periodStart = sc.periodStart ∧
      (sc.scheduleUsed a t).period = sc.period ∧ (sc.scheduleUsed a t).budget = sc.budget := by
  obtain ⟨-, hb, hp, -, -, -, hB, hT, -⟩ := SchedContext.fields_of_pendingErased
    (sc.scheduleUsed_pendingErased a t)
  exact ⟨hB, hT, hp, hb⟩

theorem SchedContext.refillBudgetCheck_period (sc : SchedContext) (u : Nat) :
    (sc.refillBudgetCheck u).period = sc.period ∧ (sc.refillBudgetCheck u).budget = sc.budget := by
  unfold SchedContext.refillBudgetCheck
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split
    · obtain ⟨-, -, h1, h2⟩ := SchedContext.scheduleUsed_head
        ({ sc with budgetRemaining := ⟨0⟩, isActive := false } : SchedContext) _ _
      exact ⟨h1, h2⟩
    · obtain ⟨-, -, h1, h2⟩ := SchedContext.scheduleUsed_head
        ({ sc with
            budgetRemaining := ⟨sc.budgetRemaining.val - u⟩
            periodStart := sc.periodStart + u
            isActive := true } : SchedContext) _ _
      exact ⟨h1, h2⟩

theorem SchedContext.releaseOne_period (sc : SchedContext) (now : Nat) :
    (sc.releaseOne now).period = sc.period ∧ (sc.releaseOne now).budget = sc.budget := by
  unfold SchedContext.releaseOne
  split
  · obtain ⟨-, hb, hp, -⟩ := SchedContext.fields_of_pendingErased sc.refillPop_pendingErased
    exact ⟨hp, hb⟩
  · exact ⟨rfl, rfl⟩

theorem SchedContext.releaseReadyHead_period (sc : SchedContext) (now : Nat) :
    (sc.releaseReadyHead now).period = sc.period ∧ (sc.releaseReadyHead now).budget = sc.budget :=
  SchedContext.releaseReadyHeadN_induction (fun s => s.period = sc.period ∧ s.budget = sc.budget) now
    (fun s h => ⟨(s.releaseOne_period now).1.trans h.1, (s.releaseOne_period now).2.trans h.2⟩)
    _ sc ⟨rfl, rfl⟩

/-- **The charge keeps the period and the budget.** -/
theorem SchedContext.chargeBudget_period (sc : SchedContext) (start usage now : Nat) :
    (sc.chargeBudget start usage now).period = sc.period ∧
      (sc.chargeBudget start usage now).budget = sc.budget := by
  unfold SchedContext.chargeBudget
  obtain ⟨a1, a2⟩ := SchedContext.releaseReadyHead_period
    ((sc.refillUnblockCheck start).refillBudgetCheck usage) now
  obtain ⟨b1, b2⟩ := SchedContext.refillBudgetCheck_period (sc.refillUnblockCheck start) usage
  obtain ⟨c1, c2⟩ := SchedContext.refillUnblockCheck_period sc start
  exact ⟨a1.trans (b1.trans c1), a2.trans (b2.trans c2)⟩

/-- WS-ZA ZA6.5: the consumed time releases no unit. -/
@[simp] theorem SchedContext.addConsumed_tokensBefore (sc : SchedContext) (t x : Nat) :
    (sc.addConsumed t).tokensBefore x = sc.tokensBefore x := rfl

/-- **No charge releases a unit earlier.** -/
theorem SchedContext.chargeBudget_tokensBefore (sc : SchedContext) (start usage now x : Nat) :
    (sc.chargeBudget start usage now).tokensBefore x ≤ sc.tokensBefore x := by
  unfold SchedContext.chargeBudget
  rw [SchedContext.addConsumed_tokensBefore, SchedContext.releaseReadyHead_tokensBefore]
  have h1 := SchedContext.refillUnblockCheck_tokensBefore sc start x
  have h2 := SchedContext.refillBudgetCheck_tokensBefore (sc.refillUnblockCheck start) usage x
  have : x - ((sc.refillUnblockCheck start).periodStart + (sc.refillUnblockCheck start).period.val) ≤
      x - (sc.refillUnblockCheck start).periodStart := by omega
  have : min (min usage (sc.refillUnblockCheck start).budgetRemaining.val)
      (x - ((sc.refillUnblockCheck start).periodStart + (sc.refillUnblockCheck start).period.val)) ≤
      min (min usage (sc.refillUnblockCheck start).budgetRemaining.val)
        (x - (sc.refillUnblockCheck start).periodStart) := by omega
  omega

/-- **A unit run at `τ` from a ready head**: its unit before `x` is released
again one period later. -/
theorem SchedContext.chargeBudget_run_tokensBefore (sc : SchedContext) (τ x : Nat)
    (hB : 0 < sc.budgetRemaining.val) (hT : sc.periodStart ≤ τ) :
    (sc.chargeBudget τ 1 (τ + 1)).tokensBefore x + min 1 (x - τ) ≤
      sc.tokensBefore x + min 1 (x - (τ + sc.period.val)) := by
  unfold SchedContext.chargeBudget
  rw [SchedContext.addConsumed_tokensBefore, SchedContext.releaseReadyHead_tokensBefore]
  obtain ⟨hT1, hP1, -, hB1⟩ := SchedContext.refillUnblockCheck_head sc τ hB hT
  have h1 := SchedContext.refillUnblockCheck_tokensBefore sc τ x
  have h2 := SchedContext.refillBudgetCheck_tokensBefore (sc.refillUnblockCheck τ) 1 x
  rw [hT1, hP1, Nat.min_eq_left (show 1 ≤ (sc.refillUnblockCheck τ).budgetRemaining.val by omega)]
    at h2
  omega

/-- The release leaves a ready head ready, or makes one ready by `now`. -/
theorem SchedContext.releaseOne_ready (sc : SchedContext) (now c : Nat)
    (h : 0 < sc.budgetRemaining.val → sc.periodStart ≤ c) (hc : c ≤ now) :
    0 < (sc.releaseOne now).budgetRemaining.val →
      (sc.releaseOne now).periodStart ≤ now := by
  unfold SchedContext.releaseOne
  split
  · rename_i hh; intro _; exact hh.2.2
  · intro hB; exact Nat.le_trans (h hB) hc

theorem SchedContext.releaseReadyHead_ready (sc : SchedContext) (now c : Nat)
    (h : 0 < sc.budgetRemaining.val → sc.periodStart ≤ c) (hc : c ≤ now) :
    0 < (sc.releaseReadyHead now).budgetRemaining.val →
      (sc.releaseReadyHead now).periodStart ≤ now := by
  have key : ∀ (n : Nat) (s : SchedContext), (0 < s.budgetRemaining.val → s.periodStart ≤ now) →
      0 < (SchedContext.releaseReadyHeadN n s now).budgetRemaining.val →
        (SchedContext.releaseReadyHeadN n s now).periodStart ≤ now :=
    SchedContext.releaseReadyHeadN_induction
      (fun s => 0 < s.budgetRemaining.val → s.periodStart ≤ now) now
      (fun s hs => s.releaseOne_ready now now hs (Nat.le_refl _))
  exact key _ sc (fun hB => Nat.le_trans (h hB) hc)

theorem SchedContext.refillBudgetCheck_ready (sc : SchedContext) (u : Nat) :
    0 < (sc.refillBudgetCheck u).budgetRemaining.val →
      (sc.refillBudgetCheck u).periodStart ≤ sc.periodStart + u := by
  unfold SchedContext.refillBudgetCheck
  dsimp only
  split
  · intro _; omega
  · split
    · rw [(SchedContext.scheduleUsed_head _ _ _).1]; intro h; simp at h
    · rw [(SchedContext.scheduleUsed_head _ _ _).2.1]; intro _; exact Nat.le_refl _

theorem SchedContext.refillBudgetCheck_spent (sc : SchedContext) (u : Nat)
    (h : sc.budgetRemaining.val ≤ u) : (sc.refillBudgetCheck u).budgetRemaining.val = 0 := by
  unfold SchedContext.refillBudgetCheck
  dsimp only
  split
  · rename_i h0; rcases h0 with h0 | h0 <;> omega
  · rw [(SchedContext.scheduleUsed_head _ _ _).1]

/-- WS-ZA ZA6.4: what happens to a context between two configures: a unit run
from `τ` (the timer tick's charge at `τ + 1`, `chargeBudget τ 1 (τ + 1)`), the
head forfeited at `t` (the yield's charge, `chargeBudget t budget t`), and the
release of a used-up head at `t` (the drain's, `releaseReadyHead t`). -/
inductive RefillEvent where
  | run (τ : Nat)
  | forfeit (t : Nat)
  | release (t : Nat)

/-- When the event starts. -/
def RefillEvent.start : RefillEvent → Nat
  | .run τ => τ
  | .forfeit t => t
  | .release t => t

/-- When the event ends: a run takes one unit. -/
def RefillEvent.finish : RefillEvent → Nat
  | .run τ => τ + 1
  | .forfeit t => t
  | .release t => t

/-- The context after the event. -/
def RefillEvent.apply (sc : SchedContext) : RefillEvent → SchedContext
  | .run τ => sc.chargeBudget τ 1 (τ + 1)
  | .forfeit t => sc.chargeBudget t sc.budget.val t
  | .release t => sc.releaseReadyHead t

/-- The units the event runs in the window `[w, w + period)`: one for a run
of a context holding budget that starts inside it. -/
def RefillEvent.runIn (sc : SchedContext) (w : Nat) : RefillEvent → Nat
  | .run τ => if 0 < sc.budgetRemaining.val ∧ w ≤ τ ∧ τ < w + sc.period.val then 1 else 0
  | .forfeit _ => 0
  | .release _ => 0

/-- The units a sequence of events runs in the window `[w, w + period)`. -/
def refillWindowRuns (w : Nat) : SchedContext → List RefillEvent → Nat
  | _, [] => 0
  | sc, e :: es => e.runIn sc w + refillWindowRuns w (e.apply sc) es

/-- Events in time order from `c`: each starts no earlier than the last ended. -/
def refillEventsOrdered : Nat → List RefillEvent → Prop
  | _, [] => True
  | c, e :: es => c ≤ e.start ∧ refillEventsOrdered e.finish es

/-- One event: what it runs in the window and the units it leaves released
before the window's end are at most the units released before it; and it keeps
the total, the budget, the period and a ready head. -/
theorem RefillEvent.step (sc : SchedContext) (e : RefillEvent) (w c : Nat)
    (hTot : sc.refillTotal = sc.budget.val)
    (hReady : 0 < sc.budgetRemaining.val → sc.periodStart ≤ c) (hc : c ≤ e.start) :
    e.runIn sc w + (e.apply sc).tokensBefore (w + sc.period.val) ≤
        sc.tokensBefore (w + sc.period.val) ∧
      (e.apply sc).refillTotal = (e.apply sc).budget.val ∧
      (e.apply sc).period = sc.period ∧
      (0 < (e.apply sc).budgetRemaining.val → (e.apply sc).periodStart ≤ e.finish) := by
  cases e with
  | run τ =>
    simp only [RefillEvent.apply, RefillEvent.runIn, RefillEvent.start, RefillEvent.finish] at hc ⊢
    obtain ⟨hp, hb⟩ := SchedContext.chargeBudget_period sc τ 1 (τ + 1)
    refine ⟨?_, by rw [SchedContext.chargeBudget_refillTotal, hb, hTot], hp, ?_⟩
    · by_cases hB : 0 < sc.budgetRemaining.val
      · have := SchedContext.chargeBudget_run_tokensBefore sc τ (w + sc.period.val) hB
          (Nat.le_trans (hReady hB) hc)
        split
        · rename_i hw; omega
        · rename_i hw
          have : ¬ (w ≤ τ ∧ τ < w + sc.period.val) := fun h => hw ⟨hB, h⟩
          by_cases hτ : τ < w <;> omega
      · rw [if_neg (fun h => hB h.1), Nat.zero_add]
        exact SchedContext.chargeBudget_tokensBefore _ _ _ _ _
    · unfold SchedContext.chargeBudget
      apply SchedContext.releaseReadyHead_ready _ _ (τ + 1) _ (Nat.le_refl _)
      intro hB2
      refine Nat.le_trans (SchedContext.refillBudgetCheck_ready _ 1 hB2) ?_
      by_cases hB : 0 < sc.budgetRemaining.val
      · rw [(SchedContext.refillUnblockCheck_head sc τ hB (Nat.le_trans (hReady hB) hc)).1]
        exact Nat.le_refl _
      · have h0 : sc.budgetRemaining.val = 0 := by omega
        have hu : sc.refillUnblockCheck τ = sc := by
          unfold SchedContext.refillUnblockCheck; rw [if_neg (fun h => hB h.1)]
        rw [hu] at hB2 ⊢
        rw [SchedContext.refillBudgetCheck_spent _ _ (by omega)] at hB2
        exact absurd hB2 (by decide)
  | forfeit t =>
    simp only [RefillEvent.apply, RefillEvent.runIn, RefillEvent.start, RefillEvent.finish] at hc ⊢
    obtain ⟨hp, hb⟩ := SchedContext.chargeBudget_period sc t sc.budget.val t
    refine ⟨by rw [Nat.zero_add]; exact SchedContext.chargeBudget_tokensBefore _ _ _ _ _,
      by rw [SchedContext.chargeBudget_refillTotal, hb, hTot], hp, ?_⟩
    unfold SchedContext.chargeBudget
    apply SchedContext.releaseReadyHead_ready _ _ t _ (Nat.le_refl _)
    intro hB2
    have hle : (sc.refillUnblockCheck t).budgetRemaining.val ≤ sc.budget.val := by
      have := SchedContext.refillUnblockCheck_refillTotal sc t
      unfold SchedContext.refillTotal at this hTot; omega
    rw [SchedContext.refillBudgetCheck_spent _ _ hle] at hB2
    exact absurd hB2 (by decide)
  | release t =>
    simp only [RefillEvent.apply, RefillEvent.runIn, RefillEvent.start, RefillEvent.finish] at hc ⊢
    obtain ⟨hp, hb⟩ := SchedContext.releaseReadyHead_period sc t
    refine ⟨by rw [Nat.zero_add, SchedContext.releaseReadyHead_tokensBefore]; exact Nat.le_refl _,
      by rw [SchedContext.releaseReadyHead_refillTotal, hb, hTot], hp,
      SchedContext.releaseReadyHead_ready _ _ c hReady hc⟩

theorem refillWindowRuns_le_tokens (w : Nat) :
    ∀ (es : List RefillEvent) (sc : SchedContext) (c : Nat),
      sc.refillTotal = sc.budget.val → (0 < sc.budgetRemaining.val → sc.periodStart ≤ c) →
      refillEventsOrdered c es →
      refillWindowRuns w sc es ≤ sc.tokensBefore (w + sc.period.val)
  | [], _, _, _, _, _ => Nat.zero_le _
  | e :: es, sc, c, hTot, hReady, hOrd => by
    obtain ⟨hc, hOrd'⟩ := hOrd
    obtain ⟨h1, h2, h3, h4⟩ := RefillEvent.step sc e w c hTot hReady hc
    have ih := refillWindowRuns_le_tokens w es (e.apply sc) e.finish h2 h4 hOrd'
    rw [h3] at ih
    simp only [refillWindowRuns]; omega

/-- **WS-ZA ZA6.4 — a context never runs more than its budget in any window of
one period.**  From a context whose refills total its budget and whose head is
ready by `c`, over any time-ordered sequence of runs, forfeits and releases
after `c` (everything that happens to a context between two configures), the
units it runs in any window `[w, w + period)` number at most its budget.  This
is seL4-MCS's sliding-window guarantee for sporadic servers, and the
charging's whole point: the refills hold the budget once (conservation), each
charged unit is scheduled again one period after its release, and nothing is
released earlier than that. -/
theorem refill_window_bound (sc : SchedContext) (es : List RefillEvent) (w c : Nat)
    (hTot : sc.refillTotal = sc.budget.val)
    (hReady : 0 < sc.budgetRemaining.val → sc.periodStart ≤ c)
    (hOrd : refillEventsOrdered c es) :
    refillWindowRuns w sc es ≤ sc.budget.val :=
  Nat.le_trans (refillWindowRuns_le_tokens w es sc c hTot hReady hOrd)
    (hTot ▸ sc.tokensBefore_le_refillTotal _)

-- ============================================================================
-- The timer tick's charge
-- ============================================================================

/-- WS-ZA ZA6.4: whether the tick's charge of one unit run from `start` uses the
head up: it holds at most the unit and `refill_unblock_check` merges no pending
refill holding budget into it (seL4-MCS ends the timeslice when the charged
head no longer holds the next unit, `refill_sufficient`).  Read off the
context's fields, so no context is built to decide it. -/
@[inline] def SchedContext.tickExhausts (sc : SchedContext) (start : Nat) : Bool :=
  decide (sc.budgetRemaining.val ≤ 1) &&
    !(decide (0 < sc.budgetRemaining.val) && decide (sc.periodStart ≤ start) &&
      sc.refillHeadPresent && decide (sc.refillHeadEligibleAt ≤ start + sc.budgetRemaining.val) &&
      decide (0 < sc.refillHeadAmount))

/-- Nothing due, nothing released. -/
theorem SchedContext.releaseReadyHead_of_not_due (sc : SchedContext) (now : Nat)
    (h : sc.releaseDue now = false) : sc.releaseReadyHead now = sc := by
  show SchedContext.releaseReadyHeadN 8 sc now = sc
  unfold SchedContext.releaseReadyHeadN
  rw [h]; rfl

/-- A head holding budget is not released again. -/
theorem SchedContext.releaseReadyHead_of_pos (sc : SchedContext) (now : Nat)
    (h : 0 < sc.budgetRemaining.val) : sc.releaseReadyHead now = sc := by
  have hd : sc.releaseDue now = false := by
    cases e : sc.releaseDue now with
    | false => rfl
    | true => have := ((sc.releaseDue_iff now).mp e).1; omega
  show SchedContext.releaseReadyHeadN 8 sc now = sc
  unfold SchedContext.releaseReadyHeadN
  rw [hd]; rfl

/-- A charge less than the head leaves the rest of it. -/
theorem SchedContext.refillBudgetCheck_partial (sc : SchedContext) (u : Nat)
    (hu : 0 < u) (h : u < sc.budgetRemaining.val) :
    (sc.refillBudgetCheck u).budgetRemaining.val = sc.budgetRemaining.val - u := by
  unfold SchedContext.refillBudgetCheck
  dsimp only
  rw [if_neg (by omega), if_neg (by omega), (SchedContext.scheduleUsed_head _ _ _).1]

/-- **A tick that does not exhaust charges a head holding budget.** -/
theorem SchedContext.tickExhausts_false_pos (sc : SchedContext) (start : Nat)
    (h : sc.tickExhausts start = false) : 0 < sc.budgetRemaining.val := by
  unfold SchedContext.tickExhausts at h
  by_cases hB : sc.budgetRemaining.val ≤ 1
  · simp only [hB, decide_true, Bool.true_and, Bool.not_eq_false', Bool.and_eq_true,
      decide_eq_true_eq] at h
    exact h.1.1.1.1
  · omega

/-- **A tick that does not use the head up leaves it holding budget**: the
context is not exhausted, so it is placed on no release queue. -/
theorem SchedContext.chargeBudget_tick_pos (sc : SchedContext) (start now : Nat)
    (h : sc.tickExhausts start = false) :
    0 < (sc.chargeBudget start 1 now).budgetRemaining.val := by
  have hu : 1 < (sc.refillUnblockCheck start).budgetRemaining.val := by
    unfold SchedContext.tickExhausts at h
    by_cases hB : sc.budgetRemaining.val ≤ 1
    · simp only [hB, decide_true, Bool.true_and, Bool.not_eq_false', Bool.and_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hB0, hT⟩, hP⟩, hE⟩, hA⟩ := h
      unfold SchedContext.refillUnblockCheck
      rw [if_pos ⟨hB0, hT⟩]
      show 1 < (SchedContext.mergeOverlapping 8 { sc with periodStart := start }).budgetRemaining.val
      unfold SchedContext.mergeOverlapping
      rw [if_pos ⟨hP, hE⟩]
      have := (SchedContext.mergeOverlapping_fields 7
        { ({ sc with periodStart := start } : SchedContext).refillPop with
          budgetRemaining := ⟨sc.budgetRemaining.val + sc.refillHeadAmount⟩ }).2.2.2
      exact Nat.lt_of_lt_of_le (show 1 < sc.budgetRemaining.val + sc.refillHeadAmount by omega) this
    · by_cases hc : 0 < sc.budgetRemaining.val ∧ sc.periodStart ≤ start
      · exact Nat.lt_of_lt_of_le (by omega) (sc.refillUnblockCheck_head start hc.1 hc.2).2.2.2
      · unfold SchedContext.refillUnblockCheck; rw [if_neg hc]; omega
  unfold SchedContext.chargeBudget
  show 0 < (SchedContext.releaseReadyHead _ _).budgetRemaining.val
  rw [SchedContext.releaseReadyHead_of_pos _ _ (by
    rw [SchedContext.refillBudgetCheck_partial _ 1 (by decide) hu]; omega),
    SchedContext.refillBudgetCheck_partial _ 1 (by decide) hu]
  omega


-- ============================================================================
-- Configure's refills
-- ============================================================================

theorem SchedContext.refillNew_replenishments (sc : SchedContext) (budget now : Nat) :
    (sc.refillNew budget now).replenishments = [] := by
  simp [SchedContext.refillNew, SchedContext.replenishments, SchedContext.refillClear]

theorem SchedContext.refillNew_budgetRemaining (sc : SchedContext) (budget now : Nat) :
    (sc.refillNew budget now).budgetRemaining = ⟨budget⟩ ∧ (sc.refillNew budget now).periodStart = now :=
  ⟨rfl, rfl⟩

/-- The refills `refill_update` leaves, as a list: the head kept (made ready at
`now` when released, trimmed to `nb`), and the rest of `nb` one period on. -/
theorem SchedContext.refillUpdateFrom_parts (sc : SchedContext) (ha ht nb np now : Nat) :
    let s := sc.refillUpdateFrom ha ht nb np now
    (ht ≤ now → s.budgetRemaining.val = min ha nb ∧ s.periodStart = now ∧
        s.replenishments = (if ha < nb then [{ amount := ⟨nb - ha⟩, eligibleAt := now + np }] else [])) ∧
      (¬ ht ≤ now → s.budgetRemaining.val = 0 ∧
        s.replenishments = { amount := ⟨min ha nb⟩, eligibleAt := ht } ::
          (if ha < nb then [{ amount := ⟨nb - ha⟩, eligibleAt := ht + np }] else [])) := by
  intro s
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [s, SchedContext.refillUpdateFrom, if_pos h]
    split
    · refine ⟨by simp [SchedContext.refillPush_budgetRemaining],
        (SchedContext.fields_of_pendingErased (SchedContext.refillPush_pendingErased _ _ _)).2.2.2.2.2.2.2.1, ?_⟩
      rw [SchedContext.refillPush_replenishments_of_empty _ _ _ rfl]
    · exact ⟨rfl, rfl, by simp [SchedContext.replenishments]⟩
  · simp only [s, SchedContext.refillUpdateFrom, if_neg h]
    split
    · refine ⟨by simp [SchedContext.refillPush_budgetRemaining], ?_⟩
      rw [SchedContext.refillPush_refillPush_replenishments_of_empty _ _ _ _ _ rfl]
    · exact ⟨by simp [SchedContext.refillPush_budgetRemaining],
        SchedContext.refillPush_replenishments_of_empty _ _ _ rfl⟩

theorem SchedContext.refillUpdateFrom_refillsPositive (sc : SchedContext) (ha ht nb np now : Nat)
    (ha0 : 0 < ha) (hnb : 0 < nb) : (sc.refillUpdateFrom ha ht nb np now).refillsPositive := by
  obtain ⟨h1, h2⟩ := SchedContext.refillUpdateFrom_parts sc ha ht nb np now
  intro r hr
  by_cases h : ht ≤ now
  · rw [(h1 h).2.2] at hr; split at hr
    · simp at hr; subst hr; simp only; omega
    · simp at hr
  · rw [(h2 h).2] at hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · simp only; omega
    · split at hr
      · simp at hr; subst hr; simp only; omega
      · simp at hr

theorem SchedContext.refillUpdateFrom_refillsFit (sc : SchedContext) (ha ht nb np now : Nat) :
    (sc.refillUpdateFrom ha ht nb np now).refillsFit := by
  obtain ⟨h1, h2⟩ := SchedContext.refillUpdateFrom_parts sc ha ht nb np now
  unfold SchedContext.refillsFit
  rw [SchedContext.refillSize_eq]
  have hl : ∀ (b : Prop) [Decidable b] (e : ReplenishmentEntry),
      (if b then [e] else ([] : List ReplenishmentEntry)).length ≤ 1 := by
    intro b _ e; split <;> simp
  by_cases h : ht ≤ now
  · rw [(h1 h).2.2]
    have := hl (ha < nb) { amount := ⟨nb - ha⟩, eligibleAt := now + np }
    unfold maxReplenishments; split <;> omega
  · rw [(h2 h).1, (h2 h).2]
    have := hl (ha < nb) { amount := ⟨nb - ha⟩, eligibleAt := ht + np }
    simp only [List.length_cons, Nat.lt_irrefl, if_false]; unfold maxReplenishments; omega

/-- After `refill_update`, a used-up head means its refill is not yet released,
and a head holding budget is released by `now`. -/
theorem SchedContext.refillUpdateFrom_ready (sc : SchedContext) (ha ht nb np now : Nat)
    (ha0 : 0 < ha) (hnb : 0 < nb) :
    let s := sc.refillUpdateFrom ha ht nb np now
    (0 < s.budgetRemaining.val → s.periodStart ≤ now) ∧
      (s.budgetRemaining.val = 0 → ∀ r, s.replenishments.head? = some r → now < r.eligibleAt) := by
  intro s
  obtain ⟨h1, h2⟩ := SchedContext.refillUpdateFrom_parts sc ha ht nb np now
  by_cases h : ht ≤ now
  · obtain ⟨hB, hT, -⟩ := h1 h
    refine ⟨fun _ => by simp only [s, hT]; exact Nat.le_refl _, fun h0 => ?_⟩
    simp only [s] at h0; rw [hB] at h0; omega
  · obtain ⟨hB, hR⟩ := h2 h
    refine ⟨fun hp => by simp only [s] at hp; rw [hB] at hp; omega, fun _ r hr => ?_⟩
    simp only [s] at hr; rw [hR] at hr; simp at hr; subst hr; simp only; omega

-- ============================================================================
-- The CBS deadline rule
-- ============================================================================

/-- CBS deadline assignment rule. When a SchedContext is replenished after
exhaustion, set deadline to `currentTime + period`. If budget was not exhausted
(continuing execution), deadline is unchanged. -/
def cbsUpdateDeadline (sc : SchedContext) (currentTime : Nat)
    (wasExhausted : Bool) : SchedContext :=
  if wasExhausted && sc.budgetRemaining.isPositive then
    { sc with deadline := ⟨currentTime + sc.period.val⟩ }
  else
    sc

/-- WS-ZA ZA6.3: the deadline rule writes none of the context's release-queue
fields. -/
theorem cbsUpdateDeadline_release (sc : SchedContext) (currentTime : Nat) (wasExhausted : Bool) :
    (cbsUpdateDeadline sc currentTime wasExhausted).releaseNextCode = sc.releaseNextCode ∧
      (cbsUpdateDeadline sc currentTime wasExhausted).releaseCoreCode = sc.releaseCoreCode ∧
      (cbsUpdateDeadline sc currentTime wasExhausted).releaseAt = sc.releaseAt := by
  unfold cbsUpdateDeadline; split <;> exact ⟨rfl, rfl, rfl⟩

/-- The deadline rule writes only the deadline: the refills read the same. -/
theorem cbsUpdateDeadline_refills (sc : SchedContext) (currentTime : Nat) (wasExhausted : Bool) :
    (cbsUpdateDeadline sc currentTime wasExhausted).budgetRemaining = sc.budgetRemaining ∧
      (cbsUpdateDeadline sc currentTime wasExhausted).periodStart = sc.periodStart ∧
      (cbsUpdateDeadline sc currentTime wasExhausted).replenishments = sc.replenishments ∧
      (cbsUpdateDeadline sc currentTime wasExhausted).budget = sc.budget ∧
      (cbsUpdateDeadline sc currentTime wasExhausted).period = sc.period ∧
      (cbsUpdateDeadline sc currentTime wasExhausted).boundThreadCode = sc.boundThreadCode := by
  unfold cbsUpdateDeadline; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- WS-ZA ZA6.3/ZA6.4: the deadline rule after an operation that writes the
refills alone writes none of the context's release-queue fields. -/
theorem cbsUpdateDeadline_release_of_refillsErased {sc x : SchedContext}
    (h : x.refillsErased = sc.refillsErased) (now : Nat) (b : Bool) :
    (cbsUpdateDeadline x now b).releaseNextCode = sc.releaseNextCode ∧
      (cbsUpdateDeadline x now b).releaseCoreCode = sc.releaseCoreCode ∧
      (cbsUpdateDeadline x now b).releaseAt = sc.releaseAt := by
  obtain ⟨h1, h2, h3⟩ := cbsUpdateDeadline_release x now b
  obtain ⟨-, -, -, -, -, -, -, -, -, h4, h5, h6⟩ := SchedContext.fields_of_refillsErased h
  exact ⟨h1.trans h4, h2.trans h5, h3.trans h6⟩

/-! WS-ZA ZA6.6: the refill operations and the deadline rule keep the context's
end of the yield link. -/

@[simp] theorem SchedContext.releaseReadyHead_yieldFromCode (sc : SchedContext) (now : Nat) :
    (sc.releaseReadyHead now).yieldFromCode = sc.yieldFromCode :=
  SchedContext.yieldFromCode_of_refillsErased (sc.releaseReadyHead_refillsErased now)

@[simp] theorem SchedContext.releaseOne_yieldFromCode (sc : SchedContext) (now : Nat) :
    (sc.releaseOne now).yieldFromCode = sc.yieldFromCode :=
  SchedContext.yieldFromCode_of_refillsErased (sc.releaseOne_refillsErased now)

@[simp] theorem SchedContext.refillNew_yieldFromCode (sc : SchedContext) (b now : Nat) :
    (sc.refillNew b now).yieldFromCode = sc.yieldFromCode :=
  SchedContext.yieldFromCode_of_refillsErased (sc.refillNew_refillsErased b now)

@[simp] theorem SchedContext.refillUpdate_yieldFromCode (sc : SchedContext) (nb np now : Nat) :
    (sc.refillUpdate nb np now).yieldFromCode = sc.yieldFromCode :=
  SchedContext.yieldFromCode_of_refillsErased (sc.refillUpdate_refillsErased nb np now)

@[simp] theorem SchedContext.refillBudgetCheck_yieldFromCode (sc : SchedContext) (u : Nat) :
    (sc.refillBudgetCheck u).yieldFromCode = sc.yieldFromCode :=
  SchedContext.yieldFromCode_of_refillsErased (sc.refillBudgetCheck_refillsErased u)

@[simp] theorem SchedContext.refillUnblockCheck_yieldFromCode (sc : SchedContext) (t : Nat) :
    (sc.refillUnblockCheck t).yieldFromCode = sc.yieldFromCode :=
  SchedContext.yieldFromCode_of_refillsErased (sc.refillUnblockCheck_refillsErased t)

@[simp] theorem SchedContext.chargeBudget_yieldFromCode (sc : SchedContext) (a u now : Nat) :
    (sc.chargeBudget a u now).yieldFromCode = sc.yieldFromCode :=
  SchedContext.yieldFromCode_of_refillsErased (sc.chargeBudget_refillsErased a u now)

@[simp] theorem cbsUpdateDeadline_yieldFromCode (sc : SchedContext) (now : Nat) (b : Bool) :
    (cbsUpdateDeadline sc now b).yieldFromCode = sc.yieldFromCode := by
  unfold cbsUpdateDeadline; split <;> rfl

/-- WS-ZA ZA6.3: the budget spend's record (the charge, then the deadline rule)
writes none of the context's release-queue fields. -/
theorem spendRecord_release (sc : SchedContext) (start ticks now : Nat) :
    (cbsUpdateDeadline (sc.chargeBudget start ticks now) now true).releaseNextCode =
        sc.releaseNextCode ∧
      (cbsUpdateDeadline (sc.chargeBudget start ticks now) now true).releaseCoreCode =
        sc.releaseCoreCode ∧
      (cbsUpdateDeadline (sc.chargeBudget start ticks now) now true).releaseAt = sc.releaseAt :=
  cbsUpdateDeadline_release_of_refillsErased (sc.chargeBudget_refillsErased start ticks now) now true

/-- WS-ZA ZA6.3: the drain's refill record (the release, then the deadline rule)
writes none of the context's release-queue fields. -/
theorem refillRecord_release (sc : SchedContext) (now : Nat) :
    (cbsUpdateDeadline (sc.releaseReadyHead now) now true).releaseNextCode = sc.releaseNextCode ∧
      (cbsUpdateDeadline (sc.releaseReadyHead now) now true).releaseCoreCode =
        sc.releaseCoreCode ∧
      (cbsUpdateDeadline (sc.releaseReadyHead now) now true).releaseAt = sc.releaseAt :=
  cbsUpdateDeadline_release_of_refillsErased (sc.releaseReadyHead_refillsErased now) now true

-- ============================================================================
-- Admission
-- ============================================================================

/-- CBS admission control. Checks whether adding `candidate` to the set of
existing SchedContexts would exceed total utilization of 1000 per-mille
(100% bandwidth). Uses integer arithmetic only.

**AK2-E (S-M03) — ceiling-round admission**: `utilizationPerMille` uses
ceiling-round division `(budget * 1000 + period - 1) / period`, an
over-estimate of each context's true utilization, so admission never accepts a
workload that would actually exceed 100% bandwidth. -/
def admissionCheck (existing : List SchedContext) (candidate : SchedContext)
    : Bool :=
  let existingUtil := existing.foldl (fun acc sc => acc + sc.utilizationPerMille) 0
  let candidateUtil := candidate.utilizationPerMille
  existingUtil + candidateUtil ≤ 1000

end SeLe4n.Kernel
