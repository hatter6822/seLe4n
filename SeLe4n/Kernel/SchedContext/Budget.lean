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
theorem truncateReplenishments_length_le (rs : List ReplenishmentEntry) :
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
    if decide (sc.refillHeadEligibleAt ≤ currentTime) &&
        allReplenishmentsEligible currentTime sc.refillTail then
      let newRemaining : Budget :=
        ⟨min (sc.budgetRemaining.val + (sc.refillHeadAmount + sumReplenishments sc.refillTail))
          sc.budget.val⟩
      { sc with
        budgetRemaining := newRemaining
        isActive := newRemaining.isPositive
        refillHeadPresent := false
        refillTail := [] }
    else processReplenishments sc currentTime
  else
    let newRemaining : Budget := ⟨min sc.budgetRemaining.val sc.budget.val⟩
    { sc with
      budgetRemaining := newRemaining
      isActive := newRemaining.isPositive
      refillTail := [] }

@[csimp] theorem processReplenishments_eq_impl :
    @processReplenishments = @processReplenishmentsImpl := by
  funext sc t
  unfold processReplenishmentsImpl
  split
  · rename_i hP
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
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
      simp [sumReplenishments, applyRefill, SchedContext.withReplenishments]
    · rfl
  · rename_i hP
    have hR : sc.replenishments = [] := by simp [SchedContext.replenishments, hP]
    simp [processReplenishments, partitionEligible, hR, sumReplenishments, applyRefill,
      SchedContext.withReplenishments, hP]

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

/-- WS-ZA ZA6.2: whether the drain's refill of `sc` (`processReplenishments`,
then `cbsUpdateDeadline` as an exhausted context) is the one record update
`refillRecord`: no pending refill, or every pending refill due. -/
@[inline] def refillInPlace (sc : SchedContext) (currentTime : Nat) : Bool :=
  !sc.refillHeadPresent ||
    (decide (sc.refillHeadEligibleAt ≤ currentTime) &&
      allReplenishmentsEligible currentTime sc.refillTail)

/-- WS-ZA ZA6.2: the amount the drain's refill adds: every pending refill's,
when all are due (`refillInPlace`). -/
@[noinline] def refillDueAmount (sc : SchedContext) : Nat :=
  if sc.refillHeadPresent then sc.refillHeadAmount + sumReplenishments sc.refillTail else 0

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
    refillTail := [] }

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
