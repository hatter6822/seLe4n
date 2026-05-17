-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Locks.TicketLock
import SeLe4n.Kernel.Concurrency.Types

/-!
# WS-SM SM2.B (tests) — TicketLock test suite

Tier-3 surface anchors plus decidable examples for every public
symbol introduced in WS-SM Phase 2.B.  This file is the canonical
regression gate that catches:

* Renames or signature drift on the SM2.B.1..B.5 data types
  (`#check` of every public symbol).
* Decidability regressions on `TicketLockState.wf`.
* Behavioural regressions on the operational semantics
  (`captureTicket`, `observeServing`, `applyOp`, `promotePending`,
  `releaseAndPromote`).
* The substantive theorem surface (mutex, wf preservation, FIFO,
  bounded wait, RA pairing, reachability, determinism, closure-form
  aliases).

The suite is a runnable executable (`lake exe ticket_lock_suite`)
that performs every decidable check at runtime as well — every
`example : ... := by decide` is also asserted as a runtime property
inside `runTicketLockChecks`, so the assertions surface in the
`run` output if they ever silently regress.

## Coverage

The suite carries:

* **§1: Surface anchors** — 70+ `#check` lines covering every
  public symbol exported by `TicketLock.lean`.
* **§2: Decidable examples** — 25+ `example : ... := by decide` /
  `rfl` examples covering the data-type constructors, the
  `unheld` initial state, the wf predicate's decide-time behavior
  on small concrete states, and operational-semantics behaviour
  on canonical examples (fast-path acquire, slow-path acquire,
  release-and-promote).
* **§3: Runtime assertion suite** — `runTicketLockChecks`
  exercises every decidable example at runtime via an
  `assertBool` helper that prints PASS / FAIL.
-/

open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1 — Surface anchors: every SM2.B.* public symbol resolves at elaboration
-- ============================================================================

/-! ## SM2.B.1 — TicketLockState -/
#check @SeLe4n.Kernel.Concurrency.TicketLockState
#check @SeLe4n.Kernel.Concurrency.TicketLockState.nextTicket
#check @SeLe4n.Kernel.Concurrency.TicketLockState.serving
#check @SeLe4n.Kernel.Concurrency.TicketLockState.pending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.held

/-! ## SM2.B.2 — unheld + witnesses -/
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld_nextTicket
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld_serving
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld_pending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld_held

/-! ## SM2.B.3 — wf + Bool helpers -/
#check @SeLe4n.Kernel.Concurrency.TicketLockState.pendingInRange
#check @SeLe4n.Kernel.Concurrency.TicketLockState.heldCount
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderTicketIsServing
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderTicketDisjointFromPending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderCoreDisjointFromPending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf
#check @SeLe4n.Kernel.Concurrency.TicketLockState.pendingInRange_iff
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderTicketIsServing_iff
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderTicketDisjointFromPending_iff
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderCoreDisjointFromPending_iff

/-! ## SM2.B.4 — Decidable + unheld_wf -/
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld_wf

/-! ## SM2.B.5 — TicketLockOp -/
#check @SeLe4n.Kernel.Concurrency.TicketLockOp
#check @SeLe4n.Kernel.Concurrency.TicketLockOp.tryAcquire
#check @SeLe4n.Kernel.Concurrency.TicketLockOp.release
#check @SeLe4n.Kernel.Concurrency.TicketLockOp.observeServing

/-! ## SM2.B.6 — Operations -/
#check @SeLe4n.Kernel.Concurrency.TicketLockState.captureTicket
#check @SeLe4n.Kernel.Concurrency.TicketLockState.observeServing
#check @SeLe4n.Kernel.Concurrency.TicketLockState.applyOp

/-! ## SM2.B.7 — promotePending + releaseAndPromote -/
#check @SeLe4n.Kernel.Concurrency.TicketLockState.promotePending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.releaseAndPromote

/-! ## SM2.B.8 — mutex -/
#check @SeLe4n.Kernel.Concurrency.ticketLock_mutex

/-! ## SM2.B.9 — wf extractor lemmas (helpers) -/
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_servingLeNextTicket
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_pendingInRange
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_holderTicketIsServing
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_pendingTicketsNodup
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_holderTicketNotInPending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_pendingCoresNodup
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_holderCoreNotInPending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_countParity
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_serving_lt_nextTicket_of_held
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_serving_lt_nextTicket_of_pending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_pending_ticket_lt
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_pending_ticket_gt
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf_nextTicket_not_in_pending

/-! ## SM2.B.9 — wf preservation theorems -/
#check @SeLe4n.Kernel.Concurrency.TicketLockState.applyOp_release_cases
#check @SeLe4n.Kernel.Concurrency.ticketLock_observeServing_preserves_wf
#check @SeLe4n.Kernel.Concurrency.ticketLock_release_preserves_partial_wf
#check @SeLe4n.Kernel.Concurrency.ticketLock_tryAcquire_preserves_wf
#check @SeLe4n.Kernel.Concurrency.ticketLock_releaseAndPromote_preserves_wf
#check @SeLe4n.Kernel.Concurrency.ticketLock_wf_invariant

/-! ## SM2.B.10 — FIFO -/
#check @SeLe4n.Kernel.Concurrency.TicketLockState.applyOp_nextTicket_monotone
#check @SeLe4n.Kernel.Concurrency.TicketLockState.applyOp_release_nextTicket_eq
#check @SeLe4n.Kernel.Concurrency.TicketLockState.promotePending_nextTicket_eq
#check @SeLe4n.Kernel.Concurrency.TicketLockState.releaseAndPromote_nextTicket_eq
#check @SeLe4n.Kernel.Concurrency.TicketLockState.applyOp_tryAcquire_captures
#check @SeLe4n.Kernel.Concurrency.ticketLock_fifo
#check @SeLe4n.Kernel.Concurrency.ticketLock_fifo_trace

/-! ## SM2.B.11 — bounded wait -/
#check @SeLe4n.Kernel.Concurrency.ticketLock_bounded_wait

/-! ## SM2.B.12 — release-acquire pairing -/
#check @SeLe4n.Kernel.Concurrency.ticketLock_release_acquire_pairing
#check @SeLe4n.Kernel.Concurrency.ticketLock_release_acquire_happensBefore

/-! ## SM2.B.13 — reachability -/
#check @SeLe4n.Kernel.Concurrency.KernelStep
#check @SeLe4n.Kernel.Concurrency.KernelStep.acquire
#check @SeLe4n.Kernel.Concurrency.KernelStep.release
#check @SeLe4n.Kernel.Concurrency.KernelStep.observe
#check @SeLe4n.Kernel.Concurrency.Reachable
#check @SeLe4n.Kernel.Concurrency.Reachable.base
#check @SeLe4n.Kernel.Concurrency.Reachable.step
#check @SeLe4n.Kernel.Concurrency.ticketLock_reachability

/-! ## SM2.B.14 — determinism -/
#check @SeLe4n.Kernel.Concurrency.ticketLock_applyOp_deterministic
#check @SeLe4n.Kernel.Concurrency.ticketLock_promotePending_deterministic

/-! ## SM2.B.15 — closure-form aliases -/
#check @SeLe4n.Kernel.Concurrency.ticketLock_acquire_preserves_wf
#check @SeLe4n.Kernel.Concurrency.ticketLock_release_preserves_wf

-- ============================================================================
-- §2 — Decidable examples: behavioural pinning for canonical states
-- ============================================================================

/-! ## §2.1 — unheld state shape -/

example : (TicketLockState.unheld).nextTicket = 0 := rfl
example : (TicketLockState.unheld).serving = 0 := rfl
example : (TicketLockState.unheld).pending = [] := rfl
example : (TicketLockState.unheld).held = (none : Option (CoreId × Nat)) := rfl

/-- The unheld state is wf. -/
example : TicketLockState.unheld.wf := by decide

/-! ## §2.2 — Bool encoding witnesses on unheld -/

example : TicketLockState.unheld.heldCount = 0 := rfl
example : TicketLockState.unheld.pendingInRange = true := by decide
example : TicketLockState.unheld.holderTicketIsServing = true := by decide
example : TicketLockState.unheld.holderTicketDisjointFromPending = true := by decide
example : TicketLockState.unheld.holderCoreDisjointFromPending = true := by decide

/-! ## §2.3 — First tryAcquire from unheld (fast-path immediate promote) -/

/-- From unheld, tryAcquire of core 0 takes the fast path: serving = nextTicket = 0
and held = none, so the captured ticket = 0 is immediately promoted to held. -/
example :
    (TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)).nextTicket = 1 := by decide

example :
    (TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)).serving = 0 := by decide

example :
    (TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)).pending = [] := by decide

example :
    (TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)).held = some (bootCoreId, 0) := by
  decide

/-- The post-acquire state is wf. -/
example :
    (TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)).wf := by decide

/-! ## §2.4 — Second tryAcquire (slow-path: append to pending) -/

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := s.applyOp (.tryAcquire ⟨1, by decide⟩)
    s'.nextTicket = 2 := by decide

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := s.applyOp (.tryAcquire ⟨1, by decide⟩)
    s'.serving = 0 := by decide

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := s.applyOp (.tryAcquire ⟨1, by decide⟩)
    s'.pending = [(⟨1, by decide⟩, 1)] := by decide

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := s.applyOp (.tryAcquire ⟨1, by decide⟩)
    s'.held = some (bootCoreId, 0) := by decide

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := s.applyOp (.tryAcquire ⟨1, by decide⟩)
    s'.wf := by decide

/-! ## §2.5 — Release-and-promote chains -/

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := s.applyOp (.tryAcquire ⟨1, by decide⟩)
    let s'' := s'.releaseAndPromote bootCoreId
    s''.nextTicket = 2 := by decide

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := s.applyOp (.tryAcquire ⟨1, by decide⟩)
    let s'' := s'.releaseAndPromote bootCoreId
    s''.serving = 1 := by decide

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := s.applyOp (.tryAcquire ⟨1, by decide⟩)
    let s'' := s'.releaseAndPromote bootCoreId
    s''.pending = [] := by decide

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := s.applyOp (.tryAcquire ⟨1, by decide⟩)
    let s'' := s'.releaseAndPromote bootCoreId
    s''.held = some (⟨1, by decide⟩, 1) := by decide

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := s.applyOp (.tryAcquire ⟨1, by decide⟩)
    let s'' := s'.releaseAndPromote bootCoreId
    s''.wf := by decide

/-! ## §2.6 — observeServing is identity -/

example :
    (TicketLockState.unheld.applyOp (.observeServing bootCoreId 0)).nextTicket = 0 := rfl

example :
    TicketLockState.unheld.applyOp (.observeServing bootCoreId 0)
    = TicketLockState.unheld := rfl

/-! ## §2.7 — No-op tryAcquire (already-pending core) -/

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := s.applyOp (.tryAcquire ⟨1, by decide⟩)
    -- Now core 1 is pending.  Re-acquiring is a no-op.
    s'.applyOp (.tryAcquire ⟨1, by decide⟩) = s' := by decide

/-! ## §2.8 — Determinism (rfl-trivial) -/

example :
    let s := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    let s' := TicketLockState.unheld.applyOp (.tryAcquire bootCoreId)
    s = s' := rfl

-- ============================================================================
-- §3 — Runtime assertions: every above example also runs in `main`
-- ============================================================================

namespace SeLe4n.Testing.TicketLockSuite

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

private def runUnheldChecks : IO Unit := do
  IO.println "--- §3.1 unheld state shape ---"
  assertBool "unheld.nextTicket = 0"
    (decide (SeLe4n.Kernel.Concurrency.TicketLockState.unheld.nextTicket = 0))
  assertBool "unheld.serving = 0"
    (decide (SeLe4n.Kernel.Concurrency.TicketLockState.unheld.serving = 0))
  assertBool "unheld.pending = []"
    (decide (SeLe4n.Kernel.Concurrency.TicketLockState.unheld.pending = []))
  assertBool "unheld.held = none"
    (decide (SeLe4n.Kernel.Concurrency.TicketLockState.unheld.held = none))
  assertBool "unheld.wf"
    (decide SeLe4n.Kernel.Concurrency.TicketLockState.unheld.wf)
  assertBool "unheld.heldCount = 0"
    (decide (SeLe4n.Kernel.Concurrency.TicketLockState.unheld.heldCount = 0))
  assertBool "unheld.pendingInRange"
    (decide (SeLe4n.Kernel.Concurrency.TicketLockState.unheld.pendingInRange = true))
  assertBool "unheld.holderTicketIsServing"
    (decide (SeLe4n.Kernel.Concurrency.TicketLockState.unheld.holderTicketIsServing = true))
  assertBool "unheld.holderTicketDisjointFromPending"
    (decide (SeLe4n.Kernel.Concurrency.TicketLockState.unheld.holderTicketDisjointFromPending = true))
  assertBool "unheld.holderCoreDisjointFromPending"
    (decide (SeLe4n.Kernel.Concurrency.TicketLockState.unheld.holderCoreDisjointFromPending = true))

private def runFastPathAcquireChecks : IO Unit := do
  IO.println "--- §3.2 fast-path acquire (unheld → held by core 0) ---"
  let s := SeLe4n.Kernel.Concurrency.TicketLockState.unheld.applyOp
            (.tryAcquire SeLe4n.Kernel.Concurrency.bootCoreId)
  assertBool "fast-path: nextTicket = 1"
    (decide (s.nextTicket = 1))
  assertBool "fast-path: serving = 0"
    (decide (s.serving = 0))
  assertBool "fast-path: pending = []"
    (decide (s.pending = []))
  assertBool "fast-path: held = some (boot, 0)"
    (decide (s.held = some (SeLe4n.Kernel.Concurrency.bootCoreId, 0)))
  assertBool "fast-path: wf"
    (decide s.wf)

private def runSlowPathAcquireChecks : IO Unit := do
  IO.println "--- §3.3 slow-path acquire (second tryAcquire appends to pending) ---"
  let s := SeLe4n.Kernel.Concurrency.TicketLockState.unheld.applyOp
            (.tryAcquire SeLe4n.Kernel.Concurrency.bootCoreId)
  let c1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  let s' := s.applyOp (.tryAcquire c1)
  assertBool "slow-path: nextTicket = 2"
    (decide (s'.nextTicket = 2))
  assertBool "slow-path: serving = 0"
    (decide (s'.serving = 0))
  assertBool "slow-path: pending = [(c1, 1)]"
    (decide (s'.pending = [(c1, 1)]))
  assertBool "slow-path: held = some (boot, 0)"
    (decide (s'.held = some (SeLe4n.Kernel.Concurrency.bootCoreId, 0)))
  assertBool "slow-path: wf"
    (decide s'.wf)

private def runReleaseAndPromoteChecks : IO Unit := do
  IO.println "--- §3.4 release-and-promote (boot releases; c1 promoted) ---"
  let s := SeLe4n.Kernel.Concurrency.TicketLockState.unheld.applyOp
            (.tryAcquire SeLe4n.Kernel.Concurrency.bootCoreId)
  let c1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  let s' := s.applyOp (.tryAcquire c1)
  let s'' := s'.releaseAndPromote SeLe4n.Kernel.Concurrency.bootCoreId
  assertBool "release+promote: nextTicket = 2"
    (decide (s''.nextTicket = 2))
  assertBool "release+promote: serving = 1"
    (decide (s''.serving = 1))
  assertBool "release+promote: pending = []"
    (decide (s''.pending = []))
  assertBool "release+promote: held = some (c1, 1)"
    (decide (s''.held = some (c1, 1)))
  assertBool "release+promote: wf"
    (decide s''.wf)

private def runObserveServingChecks : IO Unit := do
  IO.println "--- §3.5 observeServing is identity ---"
  let s := SeLe4n.Kernel.Concurrency.TicketLockState.unheld
  let s' := s.applyOp (.observeServing SeLe4n.Kernel.Concurrency.bootCoreId 0)
  assertBool "observeServing leaves state unchanged"
    (decide (s = s'))

private def runNoOpTryAcquireChecks : IO Unit := do
  IO.println "--- §3.6 no-op tryAcquire (already-pending) ---"
  let s := SeLe4n.Kernel.Concurrency.TicketLockState.unheld.applyOp
            (.tryAcquire SeLe4n.Kernel.Concurrency.bootCoreId)
  let c1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  let s' := s.applyOp (.tryAcquire c1)
  let s'' := s'.applyOp (.tryAcquire c1)
  assertBool "re-acquiring already-pending core is a no-op"
    (decide (s' = s''))

private def runDeterminismChecks : IO Unit := do
  IO.println "--- §3.7 determinism (applyOp is a function) ---"
  let s := SeLe4n.Kernel.Concurrency.TicketLockState.unheld
  let s1 := s.applyOp (.tryAcquire SeLe4n.Kernel.Concurrency.bootCoreId)
  let s2 := s.applyOp (.tryAcquire SeLe4n.Kernel.Concurrency.bootCoreId)
  assertBool "two identical applyOp invocations produce equal states"
    (decide (s1 = s2))

private def runReachabilityShapeChecks : IO Unit := do
  IO.println "--- §3.8 reachability shape (Reachable inhabits unheld) ---"
  -- The Reachable predicate is a Prop, not Bool, so we can't directly
  -- run decide on its inhabitation.  We check that the structural
  -- witnesses (KernelStep + Reachable constructors) exist.
  -- The ticketLock_reachability theorem itself is verified at
  -- elaboration via the `#check` line in §1.
  IO.println "  PASS: Reachable surface anchors verified at elaboration"

private def runBoundedWaitShapeChecks : IO Unit := do
  IO.println "--- §3.9 bounded wait (nextTicket ≤ serving + numCores for unheld) ---"
  let s := SeLe4n.Kernel.Concurrency.TicketLockState.unheld
  assertBool "unheld: nextTicket = 0 ≤ serving + numCores = 0 + 4 = 4"
    (decide (s.nextTicket ≤ s.serving + SeLe4n.Kernel.Concurrency.numCores))

private def runFifoChainChecks : IO Unit := do
  IO.println "--- §3.10 FIFO chain (3 acquires produce tickets 0, 1, 2) ---"
  let s := SeLe4n.Kernel.Concurrency.TicketLockState.unheld
  let s1 := s.applyOp (.tryAcquire SeLe4n.Kernel.Concurrency.bootCoreId)
  -- After fast-path acquire: nextTicket = 1, captured = 0.
  assertBool "first acquire captures ticket 0 (nextTicket-1)"
    (decide (s1.nextTicket - 1 = 0))
  -- Second acquire (different core) appends to pending.
  let c1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  let s2 := s1.applyOp (.tryAcquire c1)
  assertBool "second acquire grows nextTicket to 2"
    (decide (s2.nextTicket = 2))
  -- Third acquire (third core).
  let c2 : SeLe4n.Kernel.Concurrency.CoreId := ⟨2, by decide⟩
  let s3 := s2.applyOp (.tryAcquire c2)
  assertBool "third acquire grows nextTicket to 3"
    (decide (s3.nextTicket = 3))
  -- FIFO: each acquire grows nextTicket by 1.
  assertBool "FIFO: nextTicket strictly increased across the chain"
    (decide (s.nextTicket < s1.nextTicket ∧
             s1.nextTicket < s2.nextTicket ∧
             s2.nextTicket < s3.nextTicket))

def runTicketLockChecks : IO Unit := do
  IO.println "WS-SM SM2.B — TicketLock test suite"
  IO.println "==================================="
  runUnheldChecks
  runFastPathAcquireChecks
  runSlowPathAcquireChecks
  runReleaseAndPromoteChecks
  runObserveServingChecks
  runNoOpTryAcquireChecks
  runDeterminismChecks
  runReachabilityShapeChecks
  runBoundedWaitShapeChecks
  runFifoChainChecks
  IO.println "==================================="
  IO.println "All SM2.B TicketLock checks PASS."

end SeLe4n.Testing.TicketLockSuite

def main : IO Unit :=
  SeLe4n.Testing.TicketLockSuite.runTicketLockChecks
