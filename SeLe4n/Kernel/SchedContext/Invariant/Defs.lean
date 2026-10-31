-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Budget

/-! # SchedContext Invariant Definitions

Per-object invariants for SchedContext and the machine-checked proofs that the
refill engine (`Budget.lean`, seL4-MCS's refills) keeps them.

## Invariants:
- `budgetWithinBounds`: remaining ≤ configured ≤ period
- `replenishmentListWellFormed`: bounded list, no zero-amount entries
- `replenishmentAmountsBounded`: each entry's amount ≤ configured budget
- `refillsConserved` (WS-ZA ZA6.4): the head plus the pending refills equals
  the configured budget, and the refills fit the context's storage
- `schedContextWellFormed`: the 5-conjunct bundle

## Preservation:
- `chargeBudget_preserves_schedContextWellFormed`: the charge (the tick's and the
  yield's)
- `releaseReadyHead_preserves_schedContextWellFormed`: the drain's release
- `cbsUpdateDeadline_preserves_schedContextWellFormed`: the deadline rule
- `refillNew_schedContextWellFormed` / `refillUpdate_schedContextWellFormed`:
  configure's refills, at valid parameters

## Bandwidth:
- `refill_window_bound` (`Budget.lean`): a context never runs more than its
  budget in any window of one period
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

-- ============================================================================
-- WS-ZA ZA6.4: refillsConserved invariant
-- ============================================================================

/-- WS-ZA ZA6.4: the context's refills hold its budget exactly once — the head's
amount plus every pending refill's is the configured budget — and they fit its
storage (`maxReplenishments`, the head among them).  seL4-MCS's refill list
keeps the same sum (`refill_sum = budget`), and the sliding-window bound
(`refill_window_bound`) rests on it. -/
def refillsConserved (sc : SchedContext) : Prop :=
  sc.refillTotal = sc.budget.val ∧ sc.refillsFit

-- ============================================================================
-- Z2-J: schedContextWellFormed bundle
-- ============================================================================

/-- Full per-object SchedContext invariant: structural well-formedness, CBS
budget bounds, replenishment list well-formedness, replenishment amounts
bounded by the budget, and (WS-ZA ZA6.4) the refills conserved: the head and the
pending refills sum to the budget and fit the context's storage.

Conservation is what makes the bandwidth bound exact: a context never runs more
than its budget in any window of one period (`refill_window_bound`), where the
bound proven before ZA6.4 was eight budgets, one per refill slot, because the
charging then neither conserved budget nor merged at capacity. -/
def schedContextWellFormed (sc : SchedContext) : Prop :=
  sc.wellFormed ∧ budgetWithinBounds sc ∧
  replenishmentListWellFormed sc ∧ replenishmentAmountsBounded sc ∧ refillsConserved sc

-- ============================================================================
-- The bundle from its parts
-- ============================================================================

/-- Every pending amount is at most the sum of all of them. -/
theorem le_sumReplenishments_of_mem {r : ReplenishmentEntry} :
    ∀ {P : List ReplenishmentEntry}, r ∈ P → r.amount.val ≤ sumReplenishments P
  | _ :: rs, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [sumReplenishments]; omega
    · have := le_sumReplenishments_of_mem h; simp only [sumReplenishments]; omega

/-- **The bundle from the refills**: a context with a positive period and a
budget within it, whose refills are positive, conserved and fit, is well
formed — the other bounds follow from conservation. -/
theorem schedContextWellFormed_of_refills (sc : SchedContext)
    (hP : sc.period.isPositive = true) (hBP : sc.budget.val ≤ sc.period.val)
    (hPos : sc.refillsPositive) (hC : refillsConserved sc) : schedContextWellFormed sc := by
  obtain ⟨hTot, hFit⟩ := hC
  unfold SchedContext.refillTotal at hTot
  have hB : sc.budgetRemaining.val ≤ sc.budget.val := by omega
  refine ⟨⟨hP, hBP, hB, sc.replenishments_length_le⟩, ⟨hB, hBP⟩,
    ⟨sc.replenishments_length_le, fun r hr => hPos r hr⟩, fun r hr => ?_, ⟨by
      unfold SchedContext.refillTotal; omega, hFit⟩⟩
  have := le_sumReplenishments_of_mem hr; omega

theorem schedContextWellFormed_refillsPositive {sc : SchedContext}
    (h : schedContextWellFormed sc) : sc.refillsPositive := fun r hr => h.2.2.1.2 r hr

theorem schedContextWellFormed_refillsConserved {sc : SchedContext}
    (h : schedContextWellFormed sc) : refillsConserved sc := h.2.2.2.2

-- ============================================================================
-- Preservation by the refill engine
-- ============================================================================

/-- **The charge keeps the bundle**: the tick's charge and the yield's. -/
theorem chargeBudget_preserves_schedContextWellFormed (sc : SchedContext) (start usage now : Nat)
    (h : schedContextWellFormed sc) :
    schedContextWellFormed (sc.chargeBudget start usage now) := by
  obtain ⟨hp, hb⟩ := SchedContext.chargeBudget_period sc start usage now
  refine schedContextWellFormed_of_refills _ (by rw [hp]; exact h.1.1) (by rw [hp, hb]; exact h.1.2.1)
    (SchedContext.chargeBudget_refillsPositive _ _ _ _ (schedContextWellFormed_refillsPositive h))
    ⟨by rw [SchedContext.chargeBudget_refillTotal, hb]; exact h.2.2.2.2.1,
      SchedContext.chargeBudget_refillsFit _ _ _ _ h.2.2.2.2.2⟩

/-- **The release keeps the bundle**: the drain's. -/
theorem releaseReadyHead_preserves_schedContextWellFormed (sc : SchedContext) (now : Nat)
    (h : schedContextWellFormed sc) :
    schedContextWellFormed (sc.releaseReadyHead now) := by
  obtain ⟨hp, hb⟩ := SchedContext.releaseReadyHead_period sc now
  refine schedContextWellFormed_of_refills _ (by rw [hp]; exact h.1.1) (by rw [hp, hb]; exact h.1.2.1)
    (SchedContext.releaseReadyHead_refillsPositive _ _ (schedContextWellFormed_refillsPositive h))
    ⟨by rw [SchedContext.releaseReadyHead_refillTotal, hb]; exact h.2.2.2.2.1,
      SchedContext.releaseReadyHead_refillsFit _ _ h.2.2.2.2.2⟩

/-- The deadline rule keeps the bundle: it writes only the deadline. -/
theorem cbsUpdateDeadline_preserves_schedContextWellFormed (sc : SchedContext) (t : Nat) (b : Bool)
    (h : schedContextWellFormed sc) : schedContextWellFormed (cbsUpdateDeadline sc t b) := by
  unfold cbsUpdateDeadline; split
  · exact h
  · exact h

/-- **`refill_new` at valid parameters is well formed**: the budget in one
refill, none pending. -/
theorem refillNew_schedContextWellFormed (sc : SchedContext) (now : Nat)
    (hP : 0 < sc.period.val) (hBP : sc.budget.val ≤ sc.period.val) :
    schedContextWellFormed (sc.refillNew sc.budget.val now) := by
  refine schedContextWellFormed_of_refills _ (by simp [Period.isPositive]; exact hP) hBP ?_ ⟨?_, ?_⟩
  · intro r hr
    rw [SchedContext.refillNew_replenishments] at hr
    simp at hr
  · exact SchedContext.refillNew_refillTotal _ _ _
  · unfold SchedContext.refillsFit
    rw [SchedContext.refillSize_eq, SchedContext.refillNew_replenishments]
    simp [SchedContext.refillNew, maxReplenishments]; split <;> omega

/-- **`refill_update` at valid parameters is well formed**, from a context whose
pending refills are positive. -/
theorem refillUpdate_schedContextWellFormed (sc : SchedContext) (now : Nat)
    (hP : 0 < sc.period.val) (hBP : sc.budget.val ≤ sc.period.val) (h0 : 0 < sc.budget.val)
    (hPos : sc.refillsPositive) :
    schedContextWellFormed (sc.refillUpdate sc.budget.val sc.period.val now) := by
  obtain ⟨-, hb, hp, -⟩ := SchedContext.fields_of_refillsErased
    (SchedContext.refillUpdate_refillsErased sc sc.budget.val sc.period.val now)
  have hPos' : (sc.refillUpdate sc.budget.val sc.period.val now).refillsPositive ∧
      (sc.refillUpdate sc.budget.val sc.period.val now).refillsFit := by
    unfold SchedContext.refillUpdate
    split
    · rename_i hb
      exact ⟨SchedContext.refillUpdateFrom_refillsPositive _ _ _ _ _ _ hb h0,
        SchedContext.refillUpdateFrom_refillsFit _ _ _ _ _ _⟩
    · split
      · rename_i _ hp
        have := hPos _ (by rw [sc.replenishments_of_present' hp]; exact List.mem_cons_self ..)
        exact ⟨SchedContext.refillUpdateFrom_refillsPositive _ _ _ _ _ _ this h0,
          SchedContext.refillUpdateFrom_refillsFit _ _ _ _ _ _⟩
      · refine ⟨fun r hr => by rw [SchedContext.refillNew_replenishments] at hr; simp at hr, ?_⟩
        unfold SchedContext.refillsFit
        rw [SchedContext.refillSize_eq, SchedContext.refillNew_replenishments]
        simp [SchedContext.refillNew, maxReplenishments]; split <;> omega
  refine schedContextWellFormed_of_refills _ (by rw [hp]; simp [Period.isPositive]; exact hP)
    (by rw [hp, hb]; exact hBP) hPos'.1 ⟨?_, hPos'.2⟩
  rw [SchedContext.refillUpdate_refillTotal, hb]

end SeLe4n.Kernel
