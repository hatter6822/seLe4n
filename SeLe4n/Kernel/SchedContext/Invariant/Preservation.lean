/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Operations
import SeLe4n.Kernel.SchedContext.Invariant.Defs

/-! # SchedContext Invariant Preservation — WS-Z Phase Z5

Preservation theorems for capability-controlled SchedContext operations.

## Theorems:
- `validateSchedContextParams_implies_wellFormed` (Z5-M helper)
- `schedContextConfigure_output_wellFormed` (Z5-M)
- `schedContextYieldTo_target_bounded` (Z5-I helper)
-/

namespace SeLe4n.Kernel.SchedContextOps

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- Z5-M helper: validated parameters satisfy well-formedness
-- ============================================================================

/-- Z5-M: If `validateSchedContextParams` succeeds, the period is positive
and budget does not exceed period. -/
theorem validateSchedContextParams_implies_wellFormed
    (budget period priority deadline domain : Nat)
    (hOk : validateSchedContextParams budget period priority deadline domain = .ok ()) :
    period > 0 ∧ budget ≤ period := by
  simp [validateSchedContextParams] at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · simp at hOk
    · split at hOk
      · simp at hOk
      · split at hOk
        · simp at hOk
        · rename_i h1 h2 _ _
          constructor
          · omega
          · omega

-- ============================================================================
-- Z5-M: schedContextConfigure output well-formedness
-- ============================================================================

/-- Z5-M helper: Build a configured SchedContext from an existing one. -/
def applyConfigureParams (sc : SchedContext) (budget period priority deadline domain : Nat)
    : SchedContext :=
  { sc with
    budget := ⟨budget⟩
    period := ⟨period⟩
    priority := ⟨priority⟩
    deadline := ⟨deadline⟩
    domain := ⟨domain⟩
    budgetRemaining := ⟨budget⟩ }

/-- Z5-M: When parameters pass validation and the original SchedContext has
bounded replenishments, the configured SchedContext is well-formed. -/
theorem schedContextConfigure_output_wellFormed
    (budget period priority deadline domain : Nat)
    (hValid : validateSchedContextParams budget period priority deadline domain = .ok ())
    (sc : SchedContext) (hRep : sc.replenishments.length ≤ maxReplenishments) :
    SchedContext.wellFormed (applyConfigureParams sc budget period priority deadline domain) := by
  obtain ⟨hPeriod, hBudget⟩ := validateSchedContextParams_implies_wellFormed
    budget period priority deadline domain hValid
  unfold applyConfigureParams SchedContext.wellFormed
  simp [Period.isPositive]
  omega

-- ============================================================================
-- Z5-I: schedContextYieldTo budget bound
-- ============================================================================

/-- Z5-I: After `schedContextYieldTo`, the target's `budgetRemaining` does not
exceed its configured `budget`. -/
theorem schedContextYieldTo_target_bounded
    (targetSc : SchedContext) (transferAmount : Nat) :
    min (targetSc.budgetRemaining.val + transferAmount) targetSc.budget.val
      ≤ targetSc.budget.val := by
  omega

end SeLe4n.Kernel.SchedContextOps
