-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM0.I BklState anchor)

import SeLe4n.Kernel.Concurrency.Types

/-!
# WS-SM SM0.I — Big-Kernel-Lock state and per-object lock anchor

`BklState` captures the legacy "Big Kernel Lock" view that v1.0.0
retains as a coarse monitoring abstraction.  When SM3 lands the
per-object fine-lock discipline (`Concurrency/Locks/Kind.lean` plus
the SM3 acquisition machinery), the Big Lock becomes an entry-point
gate rather than the only atomicity mechanism: it is held while a
core enters the kernel and released after the per-object locks
have been acquired in `LockId` order.

The state has two constructors:

* `.unheld` — the kernel is quiescent; no core is inside a kernel
  transition.
* `.held c` — a single core `c : CoreId` is currently inside a kernel
  transition.

`bklState_unique_owner` formalises the invariant that two different
cores cannot simultaneously claim the lock — direct from the
constructor's `injection` rule.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM0.I.3 — BklState
-- ============================================================================

/-- WS-SM SM0.I: Big-Kernel-Lock state, retained at v1.0.0 as a
typed anchor that distinguishes "kernel is currently being entered
by core `c`" (`.held c`) from "kernel is quiescent" (`.unheld`).

With per-object fine locks (SM3), this becomes a coarser monitoring
abstraction: the BKL is acquired at kernel entry, released after
fine-lock acquisition completes, and re-acquired only at
trap-return for the `currentThread` swap.  The legacy "single Big
Lock for all kernel state" semantics no longer holds at SM3+, but
the type stays as the primary sequencing-event marker for the
trace harness. -/
inductive BklState where
  | unheld
  | held (owner : CoreId)
  deriving DecidableEq, Repr, Inhabited

/-- WS-SM SM0.I: BKL ownership predicate — does core `c` currently
hold the BKL? -/
def bklHeldBy (b : BklState) (c : CoreId) : Prop :=
  b = .held c

/-- WS-SM SM0.I: `bklHeldBy` is decidable — the test reduces to
constructor equality on `BklState`, which is `DecidableEq` via
`deriving`. -/
instance (b : BklState) (c : CoreId) : Decidable (bklHeldBy b c) := by
  unfold bklHeldBy
  exact inferInstance

/-- WS-SM SM0.I: well-formedness invariant — the BKL admits at most
one owner.  If `b = .held c₁` and `b = .held c₂`, then `c₁ = c₂`.
Discharged by transitive equality on the held-arm constructor.

This is the foundational non-overlap property the SM3 deadlock-
freedom proof appeals to when ruling out two concurrent kernel
entries by distinct cores. -/
theorem bklState_unique_owner :
    ∀ (b : BklState) (c₁ c₂ : CoreId),
      b = .held c₁ → b = .held c₂ → c₁ = c₂ := by
  intro b c₁ c₂ h₁ h₂
  rw [h₁] at h₂
  injection h₂

/-- WS-SM SM0.I: the unheld state is owned by no core. -/
theorem bklUnheld_no_owner :
    ∀ c : CoreId, ¬ bklHeldBy .unheld c := by
  intro c h
  unfold bklHeldBy at h
  exact BklState.noConfusion h

/-- WS-SM SM0.I: smart constructor for the held state. -/
def bklAcquire (c : CoreId) : BklState := .held c

/-- WS-SM SM0.I: `bklAcquire c` is held by `c`. -/
theorem bklAcquire_held (c : CoreId) : bklHeldBy (bklAcquire c) c := rfl

/-- WS-SM SM0.I: smart constructor for the unheld state. -/
def bklRelease : BklState := .unheld

/-- WS-SM SM0.I: `bklRelease` is unheld. -/
theorem bklRelease_unheld : bklRelease = BklState.unheld := rfl

end SeLe4n.Kernel.Concurrency
