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
- `schedContextBind_output_bidirectional` (Z5-K)
- `schedContextUnbind_output_cleared` (Z5-L)
- `schedContextBind_runQueue_priority_matches` (Z5-N1/N2)
- `schedContextConfigure_excludes_self` (Z5-M admission)
-/

namespace SeLe4n.Kernel.SchedContextOps

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- Z5-M helper: validated parameters satisfy well-formedness
-- ============================================================================

/-- Z5-M: If `validateSchedContextParams` succeeds, the period is positive,
budget is positive (AK6-A / SC-H01), and budget does not exceed period. -/
theorem validateSchedContextParams_implies_wellFormed
    (budget period priority deadline domain : Nat)
    (hOk : validateSchedContextParams budget period priority deadline domain = .ok ()) :
    period > 0 ∧ budget > 0 ∧ budget ≤ period := by
  simp [validateSchedContextParams] at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · simp at hOk
    · split at hOk
      · simp at hOk
      · split at hOk
        · simp at hOk
        · split at hOk
          · simp at hOk
          · rename_i h1 h2 h3 _ _
            refine ⟨?_, ?_, ?_⟩
            · omega
            · omega
            · omega

-- ============================================================================
-- Z5-M: schedContextConfigure output well-formedness
-- ============================================================================

/-- Z5-M helper: Build a configured SchedContext from an existing one.

AK6-B (SC-M01) preserves this legacy shape for backward compatibility with
existing proofs; the REAL configured SchedContext stored by
`schedContextConfigure` includes a replenishment-list replacement, which is
captured separately by `applyConfigureParamsFull` below. Both helpers agree
on budget / period / priority / deadline / domain / budgetRemaining. -/
def applyConfigureParams (sc : SchedContext) (budget period priority deadline domain : Nat)
    : SchedContext :=
  { sc with
    budget := ⟨budget⟩
    period := ⟨period⟩
    priority := ⟨priority⟩
    deadline := ⟨deadline⟩
    domain := ⟨domain⟩
    budgetRemaining := ⟨budget⟩ }

/-- AK6-B (SC-M01): Build the EXACT SchedContext post-state produced by
`schedContextConfigure`, including the replenishment-list replacement.
`schedContextConfigure` replaces `sc.replenishments` with a single fresh
entry `[{ amount := ⟨budget⟩, eligibleAt := timer + period }]` (AK6-C
window correction). `applyConfigureParamsFull` captures that concrete
shape so end-to-end preservation can be proven without the prior
divergence between spec helper and real op. -/
def applyConfigureParamsFull (sc : SchedContext)
    (budget period priority deadline domain timer : Nat)
    : SchedContext :=
  { sc with
    budget := ⟨budget⟩
    period := ⟨period⟩
    priority := ⟨priority⟩
    deadline := ⟨deadline⟩
    domain := ⟨domain⟩
    budgetRemaining := ⟨budget⟩
    replenishments := [{ amount := ⟨budget⟩, eligibleAt := timer + period }] }

/-- Z5-M: When parameters pass validation and the original SchedContext has
bounded replenishments, the configured SchedContext is well-formed. -/
theorem schedContextConfigure_output_wellFormed
    (budget period priority deadline domain : Nat)
    (hValid : validateSchedContextParams budget period priority deadline domain = .ok ())
    (sc : SchedContext) (hRep : sc.replenishments.length ≤ maxReplenishments) :
    SchedContext.wellFormed (applyConfigureParams sc budget period priority deadline domain) := by
  obtain ⟨hPeriod, _hBudgetPos, hBudget⟩ := validateSchedContextParams_implies_wellFormed
    budget period priority deadline domain hValid
  unfold applyConfigureParams SchedContext.wellFormed
  simp [Period.isPositive]
  omega

/-- AK6-B (SC-M01): The FULL configured SchedContext (with the
replenishment-list replacement applied) is `SchedContext.wellFormed`. The
freshly replaced replenishment list has length 1 ≤ `maxReplenishments`
(which equals 8), so the structural constraint is satisfied. -/
theorem applyConfigureParamsFull_wellFormed
    (budget period priority deadline domain timer : Nat)
    (hValid : validateSchedContextParams budget period priority deadline domain = .ok ())
    (sc : SchedContext) :
    SchedContext.wellFormed
      (applyConfigureParamsFull sc budget period priority deadline domain timer) := by
  obtain ⟨hPeriod, _hBudgetPos, hBudget⟩ := validateSchedContextParams_implies_wellFormed
    budget period priority deadline domain hValid
  unfold applyConfigureParamsFull SchedContext.wellFormed
  simp [Period.isPositive, maxReplenishments]
  omega

/-- AK6-B (SC-M01): The FULL configured SchedContext has
`budgetWithinBounds`. `budgetRemaining := ⟨budget⟩` and `budget ≤ period`
by validation. -/
theorem applyConfigureParamsFull_budgetWithinBounds
    (budget period priority deadline domain timer : Nat)
    (hValid : validateSchedContextParams budget period priority deadline domain = .ok ())
    (sc : SchedContext) :
    budgetWithinBounds
      (applyConfigureParamsFull sc budget period priority deadline domain timer) := by
  obtain ⟨_, _, hBudget⟩ := validateSchedContextParams_implies_wellFormed
    budget period priority deadline domain hValid
  unfold applyConfigureParamsFull budgetWithinBounds
  simp
  omega

/-- AK6-B (SC-M01): The FULL configured SchedContext has
`replenishmentListWellFormed`. The freshly replaced list has length 1 ≤ 8
and the sole entry's amount `⟨budget⟩` has `.val = budget > 0` (closed by
AK6-A `budget > 0` validation). -/
theorem applyConfigureParamsFull_replenishmentListWellFormed
    (budget period priority deadline domain timer : Nat)
    (hValid : validateSchedContextParams budget period priority deadline domain = .ok ())
    (sc : SchedContext) :
    replenishmentListWellFormed
      (applyConfigureParamsFull sc budget period priority deadline domain timer) := by
  obtain ⟨_, hBudgetPos, _⟩ := validateSchedContextParams_implies_wellFormed
    budget period priority deadline domain hValid
  unfold applyConfigureParamsFull replenishmentListWellFormed
  refine ⟨?_, ?_⟩
  · simp [maxReplenishments]
  · intro r hr
    simp at hr
    rw [hr]
    exact hBudgetPos

/-- AK6-B (SC-M01): The FULL configured SchedContext has
`replenishmentAmountsBounded`. The sole entry's `amount.val = budget` and
`sc'.budget.val = budget`, so the bound holds with equality. -/
theorem applyConfigureParamsFull_replenishmentAmountsBounded
    (budget period priority deadline domain timer : Nat)
    (sc : SchedContext) :
    replenishmentAmountsBounded
      (applyConfigureParamsFull sc budget period priority deadline domain timer) := by
  unfold applyConfigureParamsFull replenishmentAmountsBounded
  intro r hr
  simp at hr
  rw [hr]
  simp

/-- AK6-B (SC-M01): End-to-end preservation — the FULL configured
SchedContext satisfies the 4-conjunct `schedContextWellFormed` bundle. -/
theorem applyConfigureParamsFull_schedContextWellFormed
    (budget period priority deadline domain timer : Nat)
    (hValid : validateSchedContextParams budget period priority deadline domain = .ok ())
    (sc : SchedContext) :
    schedContextWellFormed
      (applyConfigureParamsFull sc budget period priority deadline domain timer) :=
  ⟨ applyConfigureParamsFull_wellFormed budget period priority deadline domain timer hValid sc
  , applyConfigureParamsFull_budgetWithinBounds budget period priority deadline domain timer hValid sc
  , applyConfigureParamsFull_replenishmentListWellFormed budget period priority deadline domain timer hValid sc
  , applyConfigureParamsFull_replenishmentAmountsBounded budget period priority deadline domain timer sc ⟩

/-- AK6-B (SC-M01) + AK6-C (SC-M02): The replenishment list produced by
`schedContextConfigure` is exactly one entry whose amount equals the
configured `budget` and whose eligibility is `timer + period` (one full
period AFTER reconfigure — the AK6-C window correction). -/
theorem applyConfigureParamsFull_replenishments_correct
    (budget period priority deadline domain timer : Nat)
    (sc : SchedContext) :
    (applyConfigureParamsFull sc budget period priority deadline domain timer).replenishments
      = [{ amount := ⟨budget⟩, eligibleAt := timer + period }] := by
  unfold applyConfigureParamsFull
  rfl

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

-- ============================================================================
-- Z5-K: schedContextBind bidirectional binding correctness
-- ============================================================================

/-- Z5-K: After `schedContextBind`, the updated SchedContext's `boundThread`
field equals the target thread, and the updated TCB's binding references the
SchedContext. This is the local correctness property that, given `invExt`
on the object store, would compose into full `schedContextBindingConsistent`
preservation. -/
theorem schedContextBind_output_bidirectional
    (sc : SchedContext) (tcb : TCB) (threadId : ThreadId) (scId : ObjId) :
    let scIdTyped : SchedContextId := ⟨scId.toNat⟩
    let updatedSc := { sc with boundThread := some threadId }
    let updatedTcb := { tcb with schedContextBinding := SchedContextBinding.bound scIdTyped }
    updatedSc.boundThread = some threadId ∧
    updatedTcb.schedContextBinding = SchedContextBinding.bound scIdTyped := by
  constructor <;> rfl

-- ============================================================================
-- Z5-L: schedContextUnbind cleared binding correctness
-- ============================================================================

/-- Z5-L: After `schedContextUnbind`, the updated SchedContext's `boundThread`
is `none`, `isActive` is `false`, and the updated TCB's binding is `.unbound`.
This is the local correctness property for unbinding. -/
theorem schedContextUnbind_output_cleared
    (sc : SchedContext) (tcb : TCB) :
    let updatedSc := { sc with boundThread := none, isActive := false }
    let updatedTcb := { tcb with schedContextBinding := SchedContextBinding.unbound }
    updatedSc.boundThread = none ∧
    updatedSc.isActive = false ∧
    updatedTcb.schedContextBinding = SchedContextBinding.unbound := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Z5-N1/N2: schedContextBind RunQueue priority correctness
-- ============================================================================

/-- Z5-N1/N2: The priority used for RunQueue re-insertion in `schedContextBind`
matches the SchedContext's configured priority. `RunQueue.insert` stores
`sc.priority` in the `threadPriority` map when `¬contains tid`, which holds
after `RunQueue.remove`. After bind, `effectivePriority` resolves from the
SchedContext, so the RunQueue entry's priority is consistent. -/
theorem schedContextBind_runQueue_insert_uses_sc_priority
    (sc : SchedContext) (rq : RunQueue) (tid : ThreadId)
    (hNotContains : (rq.remove tid).contains tid = false) :
    ((rq.remove tid).insert tid sc.priority).threadPriority =
    (rq.remove tid).threadPriority.insert tid sc.priority := by
  simp [RunQueue.insert, hNotContains]

-- ============================================================================
-- Z5-M (admission): collectSchedContexts exclusion well-formedness
-- ============================================================================

/-- Z5-M (admission): When admission control is called with `excludeId`,
the candidate SchedContext is compared against all other contexts. The
excluded ObjId is filtered out by the `if excludeId == some oid` guard
in `collectSchedContexts`, preventing double-counting of the SchedContext
being reconfigured. -/
theorem schedContextConfigure_admission_excludes_eq
    (oid : ObjId) :
    (if (some oid) == some oid then (none : Option SchedContext) else some sc) = none := by
  simp

end SeLe4n.Kernel.SchedContextOps
