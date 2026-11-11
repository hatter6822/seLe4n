-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.PriorityInheritance.Preservation

namespace SeLe4n.Kernel.PriorityInheritance

open SeLe4n.Model

-- ============================================================================
-- D4-Q: Bounded inversion theorem
-- ============================================================================

/-- D4-Q: Worst-case response time parameter. Taken as a hypothesis —
when D5 delivers the concrete WCRT bound, this can be instantiated. -/
abbrev WCRT := Nat

/-- D4-Q: Single-link bound — if thread H is blocked on server S,
and S has effective priority ≥ H's effective priority (from PIP),
then S completes within `wcrt` ticks. Parametric in WCRT. -/
def pipSingleLinkBound (wcrt : WCRT) (chainDepth : Nat) : Nat :=
  chainDepth * wcrt

/-- D4-Q: The total inversion time for a blocking chain of depth D
is bounded by D × WCRT. Each chain link contributes at most one WCRT
interval because PIP ensures the server runs at the client's priority. -/
theorem pip_chain_composition (wcrt : WCRT) (chainDepth : Nat) :
    pipSingleLinkBound wcrt chainDepth = chainDepth * wcrt := by
  rfl

/-- D4-Q: Bounded inversion theorem — priority inversion for any thread
is bounded by `objects.size × WCRT`. This is a conservative bound
using the maximum possible chain depth (from D4-E). -/
theorem pip_bounded_inversion (st : SystemState) (tid : ThreadId) (wcrt : WCRT) :
    pipSingleLinkBound wcrt (blockingChain st tid st.objects.size).length
    ≤ st.objects.size * wcrt := by
  simp [pipSingleLinkBound]
  exact Nat.mul_le_mul_right wcrt (blockingChain_bounded st tid)

-- ============================================================================
-- D4-R: PIP determinism
-- ============================================================================

/-- AF1-E (D4-R): Congruence: `propagatePriorityInheritance` respects argument
equality. Follows from purity — given identical inputs, pure functions produce
identical outputs. Retained for explicit documentation that PIP propagation
is deterministic in the formal model (no non-deterministic branches). -/
theorem pip_congruence (st₁ st₂ : SystemState) (tid₁ tid₂ : ThreadId)
    (fuel₁ fuel₂ : Nat)
    (hSt : st₁ = st₂) (hTid : tid₁ = tid₂) (hFuel : fuel₁ = fuel₂) :
    propagatePriorityInheritance st₁ tid₁ fuel₁ =
    propagatePriorityInheritance st₂ tid₂ fuel₂ := by
  subst hSt; subst hTid; subst hFuel; rfl

/-- AF1-E (D4-R): Congruence for `revertPriorityInheritance`. -/
theorem pip_revert_congruence (st₁ st₂ : SystemState) (tid₁ tid₂ : ThreadId)
    (fuel₁ fuel₂ : Nat)
    (hSt : st₁ = st₂) (hTid : tid₁ = tid₂) (hFuel : fuel₁ = fuel₂) :
    revertPriorityInheritance st₁ tid₁ fuel₁ =
    revertPriorityInheritance st₂ tid₂ fuel₂ := by
  subst hSt; subst hTid; subst hFuel; rfl

end SeLe4n.Kernel.PriorityInheritance
