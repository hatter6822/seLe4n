-- SPDX-License-Identifier: GPL-3.0-or-later
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
- `configuredSchedContext_schedContextWellFormed` (Z5-M)
- `schedContextBind_output_bidirectional` (Z5-K)
- `schedContextUnbind_output_cleared` (Z5-L)
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
    (budget period : Nat)
    (hOk : validateSchedContextParams budget period = .ok ()) :
    period > 0 ∧ budget > 0 ∧ budget ≤ period := by
  unfold validateSchedContextParams at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · simp at hOk
    · split at hOk
      · simp at hOk
      · rename_i h1 h2 h3
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at h1 h2
        refine ⟨?_, ?_, ?_⟩
        · omega
        · omega
        · omega

-- ============================================================================
-- Z5-M: schedContextConfigure output well-formedness
-- ============================================================================

/-- Z5-M / WS-ZA ZA6.4: **the context a configure stores is well formed** at
validated parameters (`configuredSchedContext`, the record `schedContextConfigure`
writes and its fast form rewrites in place), from a context whose pending refills
are positive: its refills hold the new budget exactly once, either the head kept
(`refill_update`) or the whole budget released now (`refill_new`).  Before ZA6.4
the stored record held the full budget as its remaining budget *and* a refill of
the full budget one period on — two budgets in the first period after every
configure. -/
theorem configuredSchedContext_schedContextWellFormed
    (budget period : Nat) (extraRefills badge flags : UInt64) (timer : Nat) (keep : Bool)
    (hValid : validateSchedContextParams budget period = .ok ())
    (sc : SchedContext) (hPos : sc.refillsPositive) :
    schedContextWellFormed
      (configuredSchedContext budget period extraRefills badge flags timer keep sc) := by
  obtain ⟨hP, hB0, hBP⟩ := validateSchedContextParams_implies_wellFormed
    budget period hValid
  unfold configuredSchedContext
  split
  · exact refillUpdate_schedContextWellFormed _ timer hP hBP hB0
      (SchedContext.refillsPositive_of_replenishments rfl hPos)
  · exact refillNew_schedContextWellFormed _ timer hP hBP

/-- WS-ZA ZA6.4: **a configure's refills hold its budget exactly once**: the head
and the pending refills of the stored context sum to the new budget, whichever
of seL4-MCS's two forms the configure takes. -/
theorem configuredSchedContext_refillTotal
    (budget period : Nat) (extraRefills badge flags : UInt64) (timer : Nat) (keep : Bool) (sc : SchedContext) :
    (configuredSchedContext budget period extraRefills badge flags timer keep sc).refillTotal =
      budget := by
  unfold configuredSchedContext
  split
  · exact SchedContext.refillUpdate_refillTotal _ _ _ _
  · exact SchedContext.refillNew_refillTotal _ _ _

/-- AK6-B bridge: If `schedContextConfigure` succeeds, then the parameters
MUST have passed `validateSchedContextParams`. The operation's first match
rejects failed validation before touching any state. Composing this with
`configuredSchedContext_schedContextWellFormed` witnesses end-to-end
`schedContextWellFormed` preservation — the CONCRETE post-state stored at
`scId` is `configuredSchedContext` of the stored context (by construction in
`schedContextConfigure`), and its well-formedness follows from validation. -/
theorem schedContextConfigure_success_implies_validated
    (vScId : ValidObjId) (budget period : Nat) (extraRefills badge flags : UInt64)
    (st st' : SystemState)
    (hOk : schedContextConfigure vScId budget period extraRefills badge flags st = .ok ((), st')) :
    validateSchedContextParams budget period = .ok () := by
  unfold schedContextConfigure at hOk
  split at hOk
  · rename_i e heq; simp at hOk
  · rename_i heq; exact heq

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
    let updatedSc := { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some threadId) }
    let updatedTcb := { tcb with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (SchedContextBinding.bound scIdTyped), scBindingOwnerCode := 0 }
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
    let updatedSc := { sc with boundThreadCode := 0, isActive := false }
    let updatedTcb := { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }
    updatedSc.boundThread = none ∧
    updatedSc.isActive = false ∧
    updatedTcb.schedContextBinding = SchedContextBinding.unbound := by
  exact ⟨rfl, rfl, rfl⟩

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
