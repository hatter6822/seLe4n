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
  { sc with replenishments := truncateReplenishments newList }

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
  { refilled with replenishments := remaining }

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

**L-17 truncation tolerance**: `utilizationPerMille` uses integer division
(`budget * 1000 / period`), which truncates down. Each context's utilization
is underestimated by at most 1 per-mille (~0.1%). With `n` active contexts,
the aggregate error is at most `n` per-mille. The worst-case over-admission
is ~6.25% (1/16) when many small-budget contexts accumulate rounding errors.

**RPi5 impact**: At 54 MHz with typical periods (1–100 ms), the per-context
admission error is at most `period / 1000` time units (≤ 0.1 ms per context).
For practical deployments with ≤ 64 contexts, the total over-admission is
bounded by 64 per-mille (6.4%), well within the standard CBS tolerance.
Per-context budget bounds (`budgetWithinBounds`) hold regardless of admission
control precision, so marginal over-admission cannot cause budget overrun.

**Design choice**: Rounding up (`(budget * 1000 + period - 1) / period`)
would eliminate under-counting but may over-reject near-capacity workloads.
The current truncation-down approach is standard CBS practice, matching the
seL4 MCS kernel behavior and preferring admission over rejection at the margin. -/
def admissionCheck (existing : List SchedContext) (candidate : SchedContext)
    : Bool :=
  let existingUtil := existing.foldl (fun acc sc => acc + sc.utilizationPerMille) 0
  let candidateUtil := candidate.utilizationPerMille
  existingUtil + candidateUtil ≤ 1000

end SeLe4n.Kernel
