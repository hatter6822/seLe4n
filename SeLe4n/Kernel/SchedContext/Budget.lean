-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Types

/-! # CBS Budget Engine — WS-Z Phase Z2

Pure-function CBS (Constant Bandwidth Server) budget management operations.
All operations are total, deterministic, and produce `SchedContext` values
suitable for machine-checked invariant proofs.

## Operations:
- `consumeBudget`: Saturating budget decrement per tick
- `isBudgetExhausted`: Budget exhaustion predicate
- `mkReplenishmentEntry` / `truncateReplenishments` / `scheduleReplenishment`: CBS replenishment scheduling
- `partitionEligible` / `sumReplenishments` / `applyRefill` / `processReplenishments`: CBS replenishment processing
- `cbsUpdateDeadline`: CBS deadline assignment rule
- `cbsBudgetCheck`: Combined per-tick budget accounting entry point
- `admissionCheck`: CBS admission control predicate
-/

namespace SeLe4n.Kernel

-- ============================================================================
-- Z2-A: consumeBudget operation
-- ============================================================================

/-- Decrement a SchedContext's remaining budget by `ticks`, saturating at 0.
After decrement, `isActive` reflects whether budget remains. -/
def consumeBudget (sc : SchedContext) (ticks : Nat := 1) : SchedContext :=
  let newRemaining := sc.budgetRemaining.decrement ticks
  { sc with
    budgetRemaining := newRemaining
    isActive := newRemaining.isPositive }

/-- `consumeBudget` never increases `budgetRemaining`. -/
theorem consumeBudget_budgetRemaining_le (sc : SchedContext) (ticks : Nat) :
    (consumeBudget sc ticks).budgetRemaining.val ≤ sc.budgetRemaining.val := by
  simp [consumeBudget, Budget.decrement]

-- ============================================================================
-- Z2-B: isBudgetExhausted predicate
-- ============================================================================

/-- A SchedContext's budget is exhausted when `budgetRemaining` is zero. -/
@[inline] def isBudgetExhausted (sc : SchedContext) : Bool :=
  sc.budgetRemaining.isZero

-- ============================================================================
-- Z2-C1: mkReplenishmentEntry constructor
-- ============================================================================

/-- Create a replenishment entry for consumed budget. The entry becomes eligible
at `currentTime + period.val` — one full period from now. -/
@[inline] def mkReplenishmentEntry (consumed : Budget) (currentTime : Nat)
    (period : Period) : ReplenishmentEntry :=
  { amount := consumed, eligibleAt := currentTime + period.val }

/-- The amount in a constructed entry equals the consumed budget. -/
theorem mkReplenishmentEntry_amount_eq (consumed : Budget) (currentTime : Nat)
    (period : Period) :
    (mkReplenishmentEntry consumed currentTime period).amount = consumed := by
  rfl

-- ============================================================================
-- Z2-C2: truncateReplenishments helper
-- ============================================================================

/-- Truncate a replenishment list to at most `maxReplenishments` entries,
dropping the oldest (head) entries as needed. -/
def truncateReplenishments (rs : List ReplenishmentEntry) : List ReplenishmentEntry :=
  rs.drop (rs.length - maxReplenishments)

/-- `truncateReplenishments` produces a list within the bound. -/
@[simp] theorem truncateReplenishments_length_le (rs : List ReplenishmentEntry) :
    (truncateReplenishments rs).length ≤ maxReplenishments := by
  simp [truncateReplenishments, List.length_drop]
  omega

-- ============================================================================
-- Z2-C3: scheduleReplenishment (compose C1+C2)
-- ============================================================================

/-- Schedule a replenishment for consumed budget. Creates an entry eligible one
period from `currentTime`, appends to the replenishment list, and truncates
to the bound. Only called when `consumed > 0` (budget was actually used). -/
def scheduleReplenishment (sc : SchedContext) (currentTime : Nat)
    (consumed : Budget) : SchedContext :=
  let entry := mkReplenishmentEntry consumed currentTime sc.period
  let newList := sc.replenishments ++ [entry]
  sc.withReplenishments (truncateReplenishments newList)

/-- WS-ZA ZA6.3: a tail slot's field after a write of `v` into slot `i`: `v` in
slot `k = i`, its old value `old` in every other.  A call, so the record update
that applies it to each slot is straight-line. -/
@[noinline] def tailSlotWrite (old k i v : Nat) : Nat := if k = i then v else old

/-- WS-ZA ZA6.3: a refill of `amount` released at `eligibleAt` appended behind
the context's first, into tail slot `n`, as one straight-line record update over
every slot (`tailSlotWrite`): the slot match writes the slot in one of seven
arms, and the compiler joins the arms before the count's update, which then
builds a new context. -/
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

theorem SchedContext.appendTailRecord_eq (sc : SchedContext) (n : Nat) (e : ReplenishmentEntry)
    (h : n < refillTailCapacity) (hP : sc.refillHeadPresent = true) :
    sc.appendTailRecord n e.amount.val e.eligibleAt =
      { sc.setTailSlot n e with
        refillHeadPresent := true
        refillHeadAmount := sc.refillHeadAmount
        refillHeadEligibleAt := sc.refillHeadEligibleAt
        refillTailCount := n + 1 } := by
  unfold refillTailCapacity maxReplenishments at h
  match n, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ =>
    simp [SchedContext.appendTailRecord, SchedContext.setTailSlot, tailSlotWrite, ← hP]

/-- WS-ZA ZA6.3: the compiled `scheduleReplenishment`.  The specification
reads the refills as a list, appends the new one and writes the list back, a
cell and an entry per refill; seL4-MCS writes the new refill into the next
slot of the context's own storage (`refill_add_tail`).  A context with no
refill takes the new one as its first, and one with a free slot takes it in
the next slot, each a record update of the context's own fields; a context
whose slots are full (the specification drops its oldest refill) runs the
specification.  Proven equal (`scheduleReplenishment_eq_impl`). -/
@[inline] def scheduleReplenishmentImpl (sc : SchedContext) (currentTime : Nat)
    (consumed : Budget) : SchedContext :=
  let eligibleAt := currentTime + sc.period.val
  if sc.refillHeadPresent then
    if sc.refillTailCount < refillTailCapacity then
      sc.appendTailRecord sc.refillTailCount consumed.val eligibleAt
    else scheduleReplenishment sc currentTime consumed
  else
    { sc with
      refillHeadPresent := true
      refillHeadAmount := consumed.val
      refillHeadEligibleAt := eligibleAt
      refillTailCount := 0 }

@[csimp] theorem scheduleReplenishment_eq_impl :
    @scheduleReplenishment = @scheduleReplenishmentImpl := by
  funext sc t consumed
  unfold scheduleReplenishmentImpl
  split
  · rename_i hP
    split
    · rename_i hN
      rw [SchedContext.appendTailRecord_eq sc _ { amount := consumed, eligibleAt := _ } hN hP]
      have hTail : sc.refillTail.length = sc.refillTailCount := by
        rw [SchedContext.refillTail_length]; omega
      have hR : sc.replenishments =
          { amount := ⟨sc.refillHeadAmount⟩, eligibleAt := sc.refillHeadEligibleAt } ::
            sc.refillTail := by
        simp [SchedContext.replenishments, hP]
      have hLen : (sc.replenishments ++ [mkReplenishmentEntry consumed t sc.period]).length ≤
          maxReplenishments := by
        rw [hR]; simp only [List.length_append, List.length_cons, List.length_nil, hTail]
        unfold refillTailCapacity at hN; unfold maxReplenishments at hN ⊢; omega
      unfold scheduleReplenishment truncateReplenishments
      dsimp only
      rw [Nat.sub_eq_zero_of_le hLen, List.drop_zero, hR]
      simp only [List.cons_append, SchedContext.withReplenishments, List.isEmpty_cons,
        Bool.not_false, List.tail_cons, SchedContext.writeTail_append,
        SchedContext.writeTail_refillTail, List.length_append, List.length_cons,
        List.length_nil, hTail, Nat.zero_add, SchedContext.writeTail, mkReplenishmentEntry]
    · rfl
  · rename_i hP
    have hR : sc.replenishments = [] := by simp [SchedContext.replenishments, hP]
    unfold scheduleReplenishment truncateReplenishments
    rw [hR]
    simp [SchedContext.withReplenishments, SchedContext.writeTail, mkReplenishmentEntry,
      maxReplenishments]

-- ============================================================================
-- Z2-D1: partitionEligible helper
-- ============================================================================

/-- Partition replenishment entries into (eligible, not-yet-eligible) based on
`eligibleAt ≤ currentTime`. -/
def partitionEligible (rs : List ReplenishmentEntry) (currentTime : Nat)
    : List ReplenishmentEntry × List ReplenishmentEntry :=
  rs.partition (fun r => r.isEligible currentTime)

/-- The eligible partition is a sublist of the original. -/
theorem partitionEligible_eligible_sublist (rs : List ReplenishmentEntry) (ct : Nat) :
    (partitionEligible rs ct).1.length ≤ rs.length := by
  simp [partitionEligible]
  exact List.length_filter_le _ rs

-- ============================================================================
-- Z2-D2: sumReplenishments helper
-- ============================================================================

/-- Sum the budget amounts of all replenishment entries. -/
def sumReplenishments : List ReplenishmentEntry → Nat
  | [] => 0
  | r :: rs => r.amount.val + sumReplenishments rs

theorem sumReplenishments_nil : sumReplenishments [] = 0 := rfl

theorem sumReplenishments_cons (r : ReplenishmentEntry)
    (rs : List ReplenishmentEntry) :
    sumReplenishments (r :: rs) = r.amount.val + sumReplenishments rs := rfl

-- ============================================================================
-- Z2-D3: applyRefill helper
-- ============================================================================

/-- Add `refillAmount` to `budgetRemaining`, capped at the configured `budget`
ceiling. This ensures the CBS invariant `budgetRemaining ≤ budget`.
Also updates `isActive` to reflect whether budget is now positive. -/
def applyRefill (sc : SchedContext) (refillAmount : Nat) : SchedContext :=
  let newRemaining : Budget := ⟨min (sc.budgetRemaining.val + refillAmount) sc.budget.val⟩
  { sc with
    budgetRemaining := newRemaining
    isActive := newRemaining.isPositive }

/-- After refill, `budgetRemaining` never exceeds `budget`. -/
theorem applyRefill_le_budget (sc : SchedContext) (refillAmount : Nat) :
    (applyRefill sc refillAmount).budgetRemaining.val ≤ sc.budget.val := by
  simp [applyRefill]
  omega

-- ============================================================================
-- Z2-D4: processReplenishments (compose D1+D2+D3)
-- ============================================================================

/-- Process all eligible replenishments: partition the list, sum eligible
amounts, apply the refill (capped at budget ceiling), keep remaining entries. -/
def processReplenishments (sc : SchedContext) (currentTime : Nat) : SchedContext :=
  let (eligible, remaining) := partitionEligible sc.replenishments currentTime
  let refillAmount := sumReplenishments eligible
  let refilled := applyRefill sc refillAmount
  refilled.withReplenishments remaining

/-- Whether every entry of `rs` is due at `currentTime`: a walk with no closure,
so the compiled refill below reads it in place. -/
def allReplenishmentsEligible (currentTime : Nat) : List ReplenishmentEntry → Bool
  | [] => true
  | r :: rs => r.isEligible currentTime && allReplenishmentsEligible currentTime rs

theorem partition_of_allReplenishmentsEligible (currentTime : Nat) :
    ∀ rs : List ReplenishmentEntry, allReplenishmentsEligible currentTime rs = true →
      rs.partition (fun r => r.isEligible currentTime) = (rs, [])
  | [], _ => rfl
  | r :: rs, h => by
    simp only [allReplenishmentsEligible, Bool.and_eq_true] at h
    have ih := partition_of_allReplenishmentsEligible currentTime rs h.2
    rw [List.partition_eq_filter_filter] at ih ⊢
    simp only [Prod.mk.injEq] at ih ⊢
    simp [List.filter_cons, h.1, ih.1, ih.2]

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

/-- WS-ZA ZA6.3: whether the `k` slots from `i` are all due, read from the
fields. -/
def SchedContext.tailAllEligibleFrom (sc : SchedContext) (currentTime : Nat) (i : Nat) :
    Nat → Bool
  | 0 => true
  | k + 1 => decide (sc.tailSlotEligibleAt i ≤ currentTime) &&
      sc.tailAllEligibleFrom currentTime (i + 1) k

/-- WS-ZA ZA6.3: the `k` slots' amounts from `i`, read from the fields. -/
def SchedContext.tailSumFrom (sc : SchedContext) (i : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sc.tailSlotAmount i + sc.tailSumFrom (i + 1) k

/-- WS-ZA ZA6.3: whether every replenishment after the first is due, with no
list built. -/
@[inline] def SchedContext.tailAllEligible (sc : SchedContext) (currentTime : Nat) : Bool :=
  sc.tailAllEligibleFrom currentTime 0 (min sc.refillTailCount refillTailCapacity)

/-- WS-ZA ZA6.3: the amounts of the replenishments after the first, with no
list built. -/
@[inline] def SchedContext.tailSum (sc : SchedContext) : Nat :=
  sc.tailSumFrom 0 (min sc.refillTailCount refillTailCapacity)

theorem SchedContext.tailAllEligibleFrom_eq (sc : SchedContext) (t : Nat) :
    ∀ i k, sc.tailAllEligibleFrom t i k =
      allReplenishmentsEligible t ((List.range' i k).map sc.tailSlot)
  | _, 0 => rfl
  | i, k + 1 => by
    simp only [SchedContext.tailAllEligibleFrom, List.range'_succ, List.map_cons,
      allReplenishmentsEligible, SchedContext.tailAllEligibleFrom_eq sc t (i + 1) k,
      SchedContext.tailSlot_eq, ReplenishmentEntry.isEligible]

theorem SchedContext.tailSumFrom_eq (sc : SchedContext) :
    ∀ i k, sc.tailSumFrom i k = sumReplenishments ((List.range' i k).map sc.tailSlot)
  | _, 0 => rfl
  | i, k + 1 => by
    simp only [SchedContext.tailSumFrom, List.range'_succ, List.map_cons, sumReplenishments,
      SchedContext.tailSumFrom_eq sc (i + 1) k, SchedContext.tailSlot_eq]

theorem SchedContext.tailAllEligible_eq (sc : SchedContext) (t : Nat) :
    sc.tailAllEligible t = allReplenishmentsEligible t sc.refillTail := by
  rw [SchedContext.tailAllEligible, SchedContext.tailAllEligibleFrom_eq, SchedContext.refillTail,
    List.range_eq_range']

theorem SchedContext.tailSum_eq (sc : SchedContext) :
    sc.tailSum = sumReplenishments sc.refillTail := by
  rw [SchedContext.tailSum, SchedContext.tailSumFrom_eq, SchedContext.refillTail,
    List.range_eq_range']

/-- WS-ZA ZA6.2: the compiled `processReplenishments`.  The refills are held as
the context's own fields (`refillHeadPresent`, `refillHeadAmount`,
`refillHeadEligibleAt`) and a tail, and the specification reads them as a list
and partitions it, a cell per refill and a pair.  Two cases take the refill in
the context's fields with no list built: every pending refill due (their
amounts added to the remaining budget, capped at the budget, and the refills
cleared), which is the drain's case, as seL4's `refill_unblock_check` merges
every ready refill into the head; and no pending refill (the remaining budget
re-capped).  A context with a refill not yet due runs the specification.
Proven equal (`processReplenishments_eq_impl`). -/
@[inline] def processReplenishmentsImpl (sc : SchedContext) (currentTime : Nat) : SchedContext :=
  if sc.refillHeadPresent then
    if decide (sc.refillHeadEligibleAt ≤ currentTime) && sc.tailAllEligible currentTime then
      let newRemaining : Budget :=
        ⟨min (sc.budgetRemaining.val + (sc.refillHeadAmount + sc.tailSum)) sc.budget.val⟩
      { sc with
        budgetRemaining := newRemaining
        isActive := newRemaining.isPositive
        refillHeadPresent := false
        refillTailCount := 0 }
    else processReplenishments sc currentTime
  else
    let newRemaining : Budget := ⟨min sc.budgetRemaining.val sc.budget.val⟩
    { sc with
      budgetRemaining := newRemaining
      isActive := newRemaining.isPositive
      refillTailCount := 0 }

@[csimp] theorem processReplenishments_eq_impl :
    @processReplenishments = @processReplenishmentsImpl := by
  funext sc t
  unfold processReplenishmentsImpl
  split
  · rename_i hP
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq, SchedContext.tailAllEligible_eq] at h
      obtain ⟨hE, hT⟩ := h
      have hR : sc.replenishments =
          { amount := ⟨sc.refillHeadAmount⟩, eligibleAt := sc.refillHeadEligibleAt } ::
            sc.refillTail := by
        simp [SchedContext.replenishments, hP]
      have hAll : allReplenishmentsEligible t sc.replenishments = true := by
        rw [hR]
        simp [allReplenishmentsEligible, ReplenishmentEntry.isEligible, hE, hT]
      simp only [processReplenishments, partitionEligible,
        partition_of_allReplenishmentsEligible t _ hAll]
      rw [hR]
      simp [sumReplenishments, applyRefill, SchedContext.withReplenishments,
        SchedContext.tailSum_eq, SchedContext.writeTail]
    · rfl
  · rename_i hP
    have hR : sc.replenishments = [] := by simp [SchedContext.replenishments, hP]
    simp [processReplenishments, partitionEligible, hR, sumReplenishments, applyRefill,
      SchedContext.withReplenishments, SchedContext.writeTail, hP]

-- ============================================================================
-- Z2-E: cbsUpdateDeadline operation
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

/-- WS-ZA ZA6.3: the budget spend's record (charge, refill scheduled, deadline
rule) writes none of the context's release-queue fields. -/
theorem spendRecord_release (sc : SchedContext) (ticks now : Nat) :
    (cbsUpdateDeadline (scheduleReplenishment (consumeBudget sc ticks) now ⟨sc.budgetRemaining.val⟩)
        now true).releaseNextCode = sc.releaseNextCode ∧
      (cbsUpdateDeadline (scheduleReplenishment (consumeBudget sc ticks) now
        ⟨sc.budgetRemaining.val⟩) now true).releaseCoreCode = sc.releaseCoreCode ∧
      (cbsUpdateDeadline (scheduleReplenishment (consumeBudget sc ticks) now
        ⟨sc.budgetRemaining.val⟩) now true).releaseAt = sc.releaseAt := by
  obtain ⟨h1, h2, h3⟩ := cbsUpdateDeadline_release
    (scheduleReplenishment (consumeBudget sc ticks) now ⟨sc.budgetRemaining.val⟩) now true
  rw [h1, h2, h3]
  simp [scheduleReplenishment, consumeBudget]

/-- WS-ZA ZA6.3: the drain's refill record writes none of the context's
release-queue fields. -/
theorem refillRecord_release (sc : SchedContext) (now : Nat) :
    (cbsUpdateDeadline (processReplenishments sc now) now true).releaseNextCode = sc.releaseNextCode ∧
      (cbsUpdateDeadline (processReplenishments sc now) now true).releaseCoreCode =
        sc.releaseCoreCode ∧
      (cbsUpdateDeadline (processReplenishments sc now) now true).releaseAt = sc.releaseAt := by
  obtain ⟨h1, h2, h3⟩ := cbsUpdateDeadline_release (processReplenishments sc now) now true
  rw [h1, h2, h3]
  simp [processReplenishments, applyRefill]

/-- WS-ZA ZA6.2: whether the drain's refill of `sc` (`processReplenishments`,
then `cbsUpdateDeadline` as an exhausted context) is the one record update
`refillRecord`: no pending refill, or every pending refill due. -/
@[inline] def refillInPlace (sc : SchedContext) (currentTime : Nat) : Bool :=
  !sc.refillHeadPresent ||
    (decide (sc.refillHeadEligibleAt ≤ currentTime) && sc.tailAllEligible currentTime)

/-- WS-ZA ZA6.2: the amount the drain's refill adds: every pending refill's,
when all are due (`refillInPlace`). -/
@[noinline] def refillDueAmount (sc : SchedContext) : Nat :=
  if sc.refillHeadPresent then sc.refillHeadAmount + sc.tailSum else 0

/-- WS-ZA ZA6.2: the deadline after the drain's refill: a period on when the
budget is now positive (`cbsUpdateDeadline` for an exhausted context). -/
@[noinline] def refillDeadline (sc : SchedContext) (currentTime : Nat) (remaining : Budget) :
    SeLe4n.Deadline :=
  if remaining.isPositive then ⟨currentTime + sc.period.val⟩ else sc.deadline

/-- WS-ZA ZA6.2: the drain's refill as one record update over the context's
own fields: every due amount added (capped at the budget), the refills
cleared and, when the budget is now positive, the deadline a period on.  Its
values are read through calls (`refillDueAmount`, `refillDeadline`), so the
update is straight-line and the compiled write reuses the context's cell
(`refillRecord_eq`). -/
@[inline] def refillRecord (sc : SchedContext) (currentTime : Nat) : SchedContext :=
  let newRemaining : Budget := ⟨min (sc.budgetRemaining.val + refillDueAmount sc) sc.budget.val⟩
  { sc with
    deadline := refillDeadline sc currentTime newRemaining
    budgetRemaining := newRemaining
    isActive := newRemaining.isPositive
    refillHeadPresent := false
    refillTailCount := 0 }

theorem refillRecord_eq (sc : SchedContext) (currentTime : Nat)
    (h : refillInPlace sc currentTime = true) :
    cbsUpdateDeadline (processReplenishments sc currentTime) currentTime true =
      refillRecord sc currentTime := by
  rw [processReplenishments_eq_impl]
  unfold processReplenishmentsImpl refillRecord refillDueAmount refillDeadline
  unfold refillInPlace at h
  by_cases hP : sc.refillHeadPresent = true
  · simp only [hP, Bool.not_true, Bool.false_or] at h
    rw [if_pos hP, if_pos h, if_pos hP]
    unfold cbsUpdateDeadline
    split <;> simp_all
  · simp only [Bool.not_eq_true] at hP
    rw [if_neg (by simp [hP]), if_neg (by simp [hP])]
    unfold cbsUpdateDeadline
    split <;> simp_all

-- ============================================================================
-- Z2-F: cbsBudgetCheck combined operation
-- ============================================================================

/-- Combined per-tick CBS budget accounting. Returns `(updatedSc, wasPreempted)`.
1. Consume `ticksConsumed` from budget.
2. If budget exhausted: schedule replenishment, process pending replenishments,
   update deadline if refilled. Preemption = true.
3. If budget remains: just process any pending replenishments. No preemption. -/
def cbsBudgetCheck (sc : SchedContext) (currentTime : Nat)
    (ticksConsumed : Nat := 1) : SchedContext × Bool :=
  let consumed := consumeBudget sc ticksConsumed
  if isBudgetExhausted consumed then
    -- Budget exhausted: schedule replenishment for consumed amount
    let consumedAmount : Budget := ⟨sc.budgetRemaining.val⟩
    let withReplenishment := scheduleReplenishment consumed currentTime consumedAmount
    -- Process any now-eligible replenishments
    let processed := processReplenishments withReplenishment currentTime
    -- Update deadline if we were refilled
    let final := cbsUpdateDeadline processed currentTime true
    (final, true)
  else
    -- Budget remains: just check for pending replenishments
    let processed := processReplenishments consumed currentTime
    (processed, false)

-- ============================================================================
-- Z2-G: admissionCheck predicate
-- ============================================================================

/-- CBS admission control. Checks whether adding `candidate` to the set of
existing SchedContexts would exceed total utilization of 1000 per-mille
(100% bandwidth). Uses integer arithmetic only.

**AK2-E (S-M03) — ceiling-round admission**: `utilizationPerMille` now uses
ceiling-round division `(budget * 1000 + period - 1) / period`. This provides
an over-estimate of each context's true utilization, ensuring admission never
accepts a workload that would actually exceed 100% bandwidth.

The prior truncation-down approach admitted up to ~6.4% aggregate over-
utilization at 64 contexts, which is unacceptable for safety-critical RT
workloads. Ceiling-round trades near-boundary rejections (admitting at most
~99.9% utilization instead of exactly 100%) for a hard upper bound, matching
the CBS isolation guarantee expected by `cbs_bandwidth_bounded`.

Per-context budget bounds (`budgetWithinBounds`) hold independently of
admission precision. See `docs/spec/SELE4N_SPEC.md` §5.4 for details. -/
def admissionCheck (existing : List SchedContext) (candidate : SchedContext)
    : Bool :=
  let existingUtil := existing.foldl (fun acc sc => acc + sc.utilizationPerMille) 0
  let candidateUtil := candidate.utilizationPerMille
  existingUtil + candidateUtil ≤ 1000

end SeLe4n.Kernel
