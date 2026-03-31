/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Budget

/-! # SchedContext Invariant Definitions — WS-Z Phase Z2

Per-object invariants for SchedContext and machine-checked proofs that CBS
budget operations preserve them.

## Invariants:
- `budgetWithinBounds`: remaining ≤ configured ≤ period
- `replenishmentListWellFormed`: bounded list, no zero-amount entries
- `replenishmentAmountsBounded`: each entry's amount ≤ configured budget
- `schedContextWellFormed`: 4-conjunct bundle (wellFormed ∧ budgetWithinBounds
  ∧ replenishmentListWellFormed ∧ replenishmentAmountsBounded)

## Preservation theorems (16 per-operation + 2 composite):
- `consumeBudget` preserves all 4 sub-invariants
- `processReplenishments` preserves all 4 sub-invariants
- `scheduleReplenishment` preserves all 4 sub-invariants
- `cbsUpdateDeadline` preserves all 4 sub-invariants
- `cbsBudgetCheck_preserves_schedContextWellFormed` — full bundle composite
- `cbsBudgetCheck_preserves_replenishmentAmountsBounded` — standalone

## Bandwidth theorems:
- `cbs_single_period_bound` — single-period consumption bound
- `cbs_bandwidth_bounded` — multi-period CBS bandwidth isolation
-/

namespace SeLe4n.Kernel

-- ============================================================================
-- Z2-H: budgetWithinBounds invariant
-- ============================================================================

/-- The fundamental CBS bandwidth constraint: remaining budget never exceeds
configured budget, and configured budget never exceeds the period. -/
def budgetWithinBounds (sc : SchedContext) : Prop :=
  sc.budgetRemaining.val ≤ sc.budget.val ∧
  sc.budget.val ≤ sc.period.val

-- ============================================================================
-- Z2-I: replenishmentListWellFormed invariant
-- ============================================================================

/-- Replenishment list structural invariant: bounded length, no zero-amount
entries. Zero-amount entries would be no-ops that waste queue slots. -/
def replenishmentListWellFormed (sc : SchedContext) : Prop :=
  sc.replenishments.length ≤ maxReplenishments ∧
  ∀ r ∈ sc.replenishments, r.amount.val > 0

-- ============================================================================
-- Z2-I2: replenishmentAmountsBounded invariant
-- ============================================================================

/-- Replenishment entry amounts are bounded by the configured budget.
This invariant holds because each replenishment entry is created from
`budgetRemaining` which satisfies `budgetRemaining ≤ budget`. -/
def replenishmentAmountsBounded (sc : SchedContext) : Prop :=
  ∀ r ∈ sc.replenishments, r.amount.val ≤ sc.budget.val

-- ============================================================================
-- Z2-J: schedContextWellFormed bundle
-- ============================================================================

/-- Full per-object SchedContext invariant: structural well-formedness from Z1,
CBS budget bounds, replenishment list well-formedness, and replenishment
entry amount bounds. The fourth conjunct ensures that every replenishment
entry's amount is ≤ the configured budget — required by the CBS bandwidth
isolation theorems (`cbs_single_period_bound`, `cbs_bandwidth_bounded`). -/
def schedContextWellFormed (sc : SchedContext) : Prop :=
  sc.wellFormed ∧ budgetWithinBounds sc ∧
  replenishmentListWellFormed sc ∧ replenishmentAmountsBounded sc

-- ============================================================================
-- Z2-K: consumeBudget preserves budgetWithinBounds
-- ============================================================================

/-- Budget consumption preserves the upper bound: decrementing remaining budget
keeps it ≤ configured budget (since it was already ≤ and can only decrease). -/
theorem consumeBudget_preserves_budgetWithinBounds (sc : SchedContext)
    (ticks : Nat) (h : budgetWithinBounds sc) :
    budgetWithinBounds (consumeBudget sc ticks) := by
  obtain ⟨hrem, hbp⟩ := h
  constructor
  · -- budgetRemaining ≤ budget
    simp [consumeBudget, Budget.decrement]
    omega
  · -- budget ≤ period (unchanged)
    exact hbp

-- ============================================================================
-- Z2-L: processReplenishments preserves budgetWithinBounds
-- ============================================================================

/-- Replenishment processing preserves budget bounds: `applyRefill` caps at
the configured budget via `min`, so `budgetRemaining ≤ budget` is maintained. -/
theorem processReplenishments_preserves_budgetWithinBounds (sc : SchedContext)
    (currentTime : Nat) (h : budgetWithinBounds sc) :
    budgetWithinBounds (processReplenishments sc currentTime) := by
  simp [processReplenishments, budgetWithinBounds]
  constructor
  · simp [applyRefill]
    omega
  · exact h.2

-- ============================================================================
-- Z2-M: scheduleReplenishment preserves replenishmentListWellFormed
-- ============================================================================

/-- Scheduling a replenishment with positive consumed budget preserves
replenishment list well-formedness: the new entry has `amount > 0` and the
list is truncated to the bound. -/
theorem scheduleReplenishment_preserves_replenishmentListWellFormed
    (sc : SchedContext) (currentTime : Nat) (consumed : Budget)
    (hsc : replenishmentListWellFormed sc) (hpos : consumed.val > 0) :
    replenishmentListWellFormed (scheduleReplenishment sc currentTime consumed) := by
  simp [replenishmentListWellFormed, scheduleReplenishment]
  constructor
  · -- Length bounded by truncation
    exact truncateReplenishments_length_le _
  · -- All entries have positive amount
    intro r hr
    simp [truncateReplenishments] at hr
    have hmem : r ∈ sc.replenishments ++ [mkReplenishmentEntry consumed currentTime sc.period] := by
      exact List.mem_of_mem_drop hr
    simp [List.mem_append] at hmem
    cases hmem with
    | inl h => exact hsc.2 r h
    | inr h => rw [h]; simp [mkReplenishmentEntry]; exact hpos

-- ============================================================================
-- Auxiliary: consumeBudget preserves wellFormed
-- ============================================================================

/-- `consumeBudget` preserves `SchedContext.wellFormed`: period, budget, and
replenishment list are unchanged; budgetRemaining can only decrease. -/
theorem consumeBudget_preserves_wellFormed (sc : SchedContext)
    (ticks : Nat) (h : sc.wellFormed) :
    (consumeBudget sc ticks).wellFormed := by
  simp [SchedContext.wellFormed, consumeBudget, Budget.decrement, Budget.isPositive]
  obtain ⟨hp, hbp, hrb, hrl⟩ := h
  exact ⟨hp, hbp, by omega, hrl⟩

/-- `consumeBudget` preserves `replenishmentListWellFormed`: the replenishment
list is unchanged by budget consumption. -/
theorem consumeBudget_preserves_replenishmentListWellFormed (sc : SchedContext)
    (ticks : Nat) (h : replenishmentListWellFormed sc) :
    replenishmentListWellFormed (consumeBudget sc ticks) := by
  simp [replenishmentListWellFormed, consumeBudget]
  exact h

-- ============================================================================
-- Auxiliary: processReplenishments preserves wellFormed
-- ============================================================================

/-- `processReplenishments` preserves `SchedContext.wellFormed`. -/
theorem processReplenishments_preserves_wellFormed (sc : SchedContext)
    (currentTime : Nat) (h : sc.wellFormed) :
    (processReplenishments sc currentTime).wellFormed := by
  simp [SchedContext.wellFormed, processReplenishments, applyRefill, partitionEligible]
  obtain ⟨hp, hbp, hrb, hrl⟩ := h
  refine ⟨hp, hbp, ?_, ?_⟩
  · omega
  · exact Nat.le_trans (List.length_filter_le _ _) hrl

/-- `processReplenishments` preserves `replenishmentListWellFormed` when
the source has well-formed replenishments (remaining entries are a sublist). -/
private theorem filter_mem_of_mem {α : Type} {p : α → Bool} {l : List α} {x : α}
    (h : x ∈ l.filter p) : x ∈ l := by
  induction l with
  | nil => simp [List.filter] at h
  | cons hd tl ih =>
    simp only [List.filter] at h
    split at h
    · simp only [List.mem_cons] at h ⊢
      cases h with
      | inl heq => left; exact heq
      | inr htl => right; exact ih htl
    · simp only [List.mem_cons] at h ⊢
      right; exact ih h

theorem processReplenishments_preserves_replenishmentListWellFormed
    (sc : SchedContext) (currentTime : Nat)
    (h : replenishmentListWellFormed sc) :
    replenishmentListWellFormed (processReplenishments sc currentTime) := by
  constructor
  · -- Length: filter result ≤ original ≤ maxReplenishments
    simp [processReplenishments, partitionEligible]
    exact Nat.le_trans (List.length_filter_le _ _) h.1
  · -- All entries have positive amount
    simp [processReplenishments, partitionEligible]
    intro r hr _
    exact h.2 r hr

-- ============================================================================
-- Auxiliary: cbsUpdateDeadline preserves everything
-- ============================================================================

/-- `cbsUpdateDeadline` preserves `budgetWithinBounds` (only changes deadline). -/
theorem cbsUpdateDeadline_preserves_budgetWithinBounds (sc : SchedContext)
    (currentTime : Nat) (wasExhausted : Bool) (h : budgetWithinBounds sc) :
    budgetWithinBounds (cbsUpdateDeadline sc currentTime wasExhausted) := by
  simp [cbsUpdateDeadline, budgetWithinBounds]
  split <;> exact h

/-- `cbsUpdateDeadline` preserves `SchedContext.wellFormed`. -/
theorem cbsUpdateDeadline_preserves_wellFormed (sc : SchedContext)
    (currentTime : Nat) (wasExhausted : Bool) (h : sc.wellFormed) :
    (cbsUpdateDeadline sc currentTime wasExhausted).wellFormed := by
  simp [cbsUpdateDeadline, SchedContext.wellFormed]
  split <;> exact h

/-- `cbsUpdateDeadline` preserves `replenishmentListWellFormed`. -/
theorem cbsUpdateDeadline_preserves_replenishmentListWellFormed (sc : SchedContext)
    (currentTime : Nat) (wasExhausted : Bool)
    (h : replenishmentListWellFormed sc) :
    replenishmentListWellFormed (cbsUpdateDeadline sc currentTime wasExhausted) := by
  simp [cbsUpdateDeadline, replenishmentListWellFormed]
  split <;> exact h

-- ============================================================================
-- Auxiliary: scheduleReplenishment preserves wellFormed
-- ============================================================================

/-- `scheduleReplenishment` preserves `SchedContext.wellFormed`. -/
theorem scheduleReplenishment_preserves_wellFormed (sc : SchedContext)
    (currentTime : Nat) (consumed : Budget) (h : sc.wellFormed) :
    (scheduleReplenishment sc currentTime consumed).wellFormed := by
  simp [SchedContext.wellFormed, scheduleReplenishment]
  obtain ⟨hp, hbp, hrb, _⟩ := h
  exact ⟨hp, hbp, hrb, truncateReplenishments_length_le _⟩

/-- `scheduleReplenishment` preserves `budgetWithinBounds` (only changes replenishments). -/
theorem scheduleReplenishment_preserves_budgetWithinBounds (sc : SchedContext)
    (currentTime : Nat) (consumed : Budget) (h : budgetWithinBounds sc) :
    budgetWithinBounds (scheduleReplenishment sc currentTime consumed) := by
  simp [scheduleReplenishment, budgetWithinBounds]
  exact h

-- ============================================================================
-- Z2-M2: replenishmentAmountsBounded preservation
-- ============================================================================

/-- `consumeBudget` preserves `replenishmentAmountsBounded`: the replenishment
list and budget ceiling are unchanged by consumption. -/
theorem consumeBudget_preserves_replenishmentAmountsBounded (sc : SchedContext)
    (ticks : Nat) (h : replenishmentAmountsBounded sc) :
    replenishmentAmountsBounded (consumeBudget sc ticks) := by
  simp [replenishmentAmountsBounded, consumeBudget]
  exact h

/-- `processReplenishments` preserves `replenishmentAmountsBounded`: the
remaining entries are a subset of the original list with the same budget. -/
theorem processReplenishments_preserves_replenishmentAmountsBounded
    (sc : SchedContext) (currentTime : Nat)
    (h : replenishmentAmountsBounded sc) :
    replenishmentAmountsBounded (processReplenishments sc currentTime) := by
  simp [replenishmentAmountsBounded, processReplenishments, partitionEligible]
  intro r hr _
  exact h r hr

/-- `scheduleReplenishment` preserves `replenishmentAmountsBounded` when the
consumed amount ≤ budget (which holds when `budgetWithinBounds` is satisfied,
since consumed = budgetRemaining ≤ budget). -/
theorem scheduleReplenishment_preserves_replenishmentAmountsBounded
    (sc : SchedContext) (currentTime : Nat) (consumed : Budget)
    (h : replenishmentAmountsBounded sc) (hle : consumed.val ≤ sc.budget.val) :
    replenishmentAmountsBounded (scheduleReplenishment sc currentTime consumed) := by
  simp [replenishmentAmountsBounded, scheduleReplenishment, truncateReplenishments]
  intro r hr
  have hmem : r ∈ sc.replenishments ++ [mkReplenishmentEntry consumed currentTime sc.period] :=
    List.mem_of_mem_drop hr
  simp [List.mem_append] at hmem
  cases hmem with
  | inl hmem => exact h r hmem
  | inr heq => rw [heq]; simp [mkReplenishmentEntry]; exact hle

/-- `cbsUpdateDeadline` preserves `replenishmentAmountsBounded` (only changes
deadline, not replenishments or budget). -/
theorem cbsUpdateDeadline_preserves_replenishmentAmountsBounded
    (sc : SchedContext) (currentTime : Nat) (wasExhausted : Bool)
    (h : replenishmentAmountsBounded sc) :
    replenishmentAmountsBounded (cbsUpdateDeadline sc currentTime wasExhausted) := by
  simp [cbsUpdateDeadline, replenishmentAmountsBounded]
  split <;> exact h

-- ============================================================================
-- Z2-N: cbsBudgetCheck preserves schedContextWellFormed
-- ============================================================================

/-- The combined per-tick budget check preserves the full SchedContext invariant
bundle. This composes the individual preservation theorems for each sub-operation
(consume, schedule replenishment, process replenishments, update deadline). -/
theorem cbsBudgetCheck_preserves_schedContextWellFormed (sc : SchedContext)
    (currentTime : Nat) (ticksConsumed : Nat)
    (h : schedContextWellFormed sc)
    (hbudgetPos : sc.budgetRemaining.val > 0) :
    schedContextWellFormed (cbsBudgetCheck sc currentTime ticksConsumed).1 := by
  obtain ⟨hwf, hbounds, hrepl, hamounts⟩ := h
  simp [schedContextWellFormed, cbsBudgetCheck]
  split
  · -- Budget exhausted branch
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- wellFormed
      apply cbsUpdateDeadline_preserves_wellFormed
      apply processReplenishments_preserves_wellFormed
      apply scheduleReplenishment_preserves_wellFormed
      exact consumeBudget_preserves_wellFormed sc ticksConsumed hwf
    · -- budgetWithinBounds
      apply cbsUpdateDeadline_preserves_budgetWithinBounds
      apply processReplenishments_preserves_budgetWithinBounds
      apply scheduleReplenishment_preserves_budgetWithinBounds
      exact consumeBudget_preserves_budgetWithinBounds sc ticksConsumed hbounds
    · -- replenishmentListWellFormed
      apply cbsUpdateDeadline_preserves_replenishmentListWellFormed
      apply processReplenishments_preserves_replenishmentListWellFormed
      apply scheduleReplenishment_preserves_replenishmentListWellFormed
      · exact consumeBudget_preserves_replenishmentListWellFormed sc ticksConsumed hrepl
      · -- consumed amount > 0: we know budgetRemaining was > 0
        exact hbudgetPos
    · -- replenishmentAmountsBounded
      apply cbsUpdateDeadline_preserves_replenishmentAmountsBounded
      apply processReplenishments_preserves_replenishmentAmountsBounded
      apply scheduleReplenishment_preserves_replenishmentAmountsBounded
      · exact consumeBudget_preserves_replenishmentAmountsBounded sc ticksConsumed hamounts
      · exact hbounds.1
  · -- Budget not exhausted branch
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply processReplenishments_preserves_wellFormed
      exact consumeBudget_preserves_wellFormed sc ticksConsumed hwf
    · apply processReplenishments_preserves_budgetWithinBounds
      exact consumeBudget_preserves_budgetWithinBounds sc ticksConsumed hbounds
    · apply processReplenishments_preserves_replenishmentListWellFormed
      exact consumeBudget_preserves_replenishmentListWellFormed sc ticksConsumed hrepl
    · apply processReplenishments_preserves_replenishmentAmountsBounded
      exact consumeBudget_preserves_replenishmentAmountsBounded sc ticksConsumed hamounts

-- ============================================================================
-- Z2-O1: totalConsumed accumulator
-- ============================================================================

/-- Compute the total ticks consumed by a SchedContext within a time window,
measured by summing replenishment amounts whose eligibility falls within
`[windowStart, windowStart + window)`. This models the CBS accounting identity:
consumed ticks are eventually scheduled for replenishment. -/
def totalConsumed (sc : SchedContext) (windowStart : Nat) (window : Nat) : Nat :=
  let relevant := sc.replenishments.filter (fun r =>
    r.eligibleAt ≥ windowStart && r.eligibleAt < windowStart + window)
  sumReplenishments relevant

/-- `cbsBudgetCheck` preserves `replenishmentAmountsBounded`. The key insight
is that the consumed amount equals `sc.budgetRemaining.val` which is ≤
`sc.budget.val` by `budgetWithinBounds`. -/
theorem cbsBudgetCheck_preserves_replenishmentAmountsBounded (sc : SchedContext)
    (currentTime : Nat) (ticksConsumed : Nat)
    (h : replenishmentAmountsBounded sc)
    (hbounds : budgetWithinBounds sc) :
    replenishmentAmountsBounded (cbsBudgetCheck sc currentTime ticksConsumed).1 := by
  simp [cbsBudgetCheck]
  split
  · -- Budget exhausted branch
    apply cbsUpdateDeadline_preserves_replenishmentAmountsBounded
    apply processReplenishments_preserves_replenishmentAmountsBounded
    apply scheduleReplenishment_preserves_replenishmentAmountsBounded
    · exact consumeBudget_preserves_replenishmentAmountsBounded sc ticksConsumed h
    · -- consumed.val = sc.budgetRemaining.val ≤ sc.budget.val
      exact hbounds.1
  · -- Budget not exhausted branch
    apply processReplenishments_preserves_replenishmentAmountsBounded
    exact consumeBudget_preserves_replenishmentAmountsBounded sc ticksConsumed h

-- ============================================================================
-- Z2-O2: Single-period bandwidth bound
-- ============================================================================

/-- Helper: sum of filtered list ≤ sum of original list. -/
private theorem sumReplenishments_filter_le (p : ReplenishmentEntry → Bool)
    (rs : List ReplenishmentEntry) :
    sumReplenishments (rs.filter p) ≤ sumReplenishments rs := by
  induction rs with
  | nil => simp [List.filter, sumReplenishments]
  | cons hd tl ih =>
    simp only [List.filter]
    split
    · simp [sumReplenishments]; omega
    · simp [sumReplenishments]; omega

/-- Helper: sum of replenishments bounded by count * max entry. -/
private theorem sumReplenishments_le_count_mul_max
    (rs : List ReplenishmentEntry) (bound : Nat)
    (h : ∀ r ∈ rs, r.amount.val ≤ bound) :
    sumReplenishments rs ≤ rs.length * bound := by
  induction rs with
  | nil => simp [sumReplenishments]
  | cons hd tl ih =>
    simp only [sumReplenishments, List.length_cons]
    have hhd : hd.amount.val ≤ bound := h hd (by simp)
    have htl : sumReplenishments tl ≤ tl.length * bound :=
      ih (fun r hr => h r (by simp [hr]))
    have : (tl.length + 1) * bound = bound + tl.length * bound := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [this]
    exact Nat.add_le_add hhd htl

/-- Core CBS consumption bound: total consumption from the replenishment list
(over any window) is bounded by `maxReplenishments × budget`. This follows from
two invariants: (1) list length ≤ `maxReplenishments`, (2) each entry's amount ≤
budget. -/
private theorem totalConsumed_le_max_budget (sc : SchedContext)
    (windowStart : Nat) (window : Nat)
    (hamounts : replenishmentAmountsBounded sc)
    (hwf : sc.wellFormed) :
    totalConsumed sc windowStart window ≤
      maxReplenishments * sc.budget.val := by
  simp [totalConsumed]
  calc sumReplenishments (sc.replenishments.filter _)
      ≤ sumReplenishments sc.replenishments :=
        sumReplenishments_filter_le _ _
    _ ≤ sc.replenishments.length * sc.budget.val :=
        sumReplenishments_le_count_mul_max sc.replenishments sc.budget.val hamounts
    _ ≤ maxReplenishments * sc.budget.val :=
        Nat.mul_le_mul_right _ hwf.2.2.2

/-- Within a single period, a well-formed SchedContext's consumption is bounded
by `maxReplenishments × budget`. This is an upper bound on the total CBS
consumption observable via the replenishment list during one period.

**Design note**: The tighter bound `totalConsumed ≤ budget` (one budget per
period) holds under the CBS scheduling discipline (which ensures at most one
full budget is consumed per period), but proving it requires tracking the
temporal ordering of consume/replenish operations across scheduler ticks.
The weaker bound proven here suffices for admission control and is
fully machine-checked. -/
theorem cbs_single_period_bound (sc : SchedContext)
    (windowStart : Nat)
    (hamounts : replenishmentAmountsBounded sc)
    (hwf : sc.wellFormed) :
    totalConsumed sc windowStart sc.period.val ≤
      maxReplenishments * sc.budget.val :=
  totalConsumed_le_max_budget sc windowStart sc.period.val hamounts hwf

-- ============================================================================
-- Z2-O3: CBS bandwidth isolation theorem (multi-period)
-- ============================================================================

/-- Over any time window, a well-formed SchedContext's total consumption is
bounded by `maxReplenishments × budget`. This is the fundamental CBS bandwidth
isolation guarantee: the replenishment list is bounded in length (`≤ 8`), and
each entry's amount is bounded by the configured budget, giving an absolute
consumption ceiling of `8 × budget` ticks.

Combined with the CBS scheduling discipline (which limits per-period consumption
to budget), the effective runtime bound is `budget × ⌈window / period⌉`, but
that tighter bound requires tracking temporal consume/replenish ordering across
scheduler integration (Z4). This static bound from list structure alone is
sufficient for admission control and type-level CBS correctness. -/
theorem cbs_bandwidth_bounded (sc : SchedContext)
    (windowStart : Nat) (window : Nat)
    (hamounts : replenishmentAmountsBounded sc)
    (hwf : sc.wellFormed) :
    totalConsumed sc windowStart window ≤
      maxReplenishments * sc.budget.val :=
  totalConsumed_le_max_budget sc windowStart window hamounts hwf

end SeLe4n.Kernel
