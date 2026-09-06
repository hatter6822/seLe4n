-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR7.39: PRODUCTION.  The revalidating two-phase-locking bracket, once,
-- for every lock domain that has one.  `SeLe4n/Kernel/SyscallLockBracket.lean`
-- instantiates it at the object domain and `SeLe4n/Kernel/SchedLockBracket.lean`
-- at the scheduler domain.

import SeLe4n.Kernel.Concurrency.Locks.LockSetHeld

/-!
# WS-RR RR7.39 — one bracket, two domains

RR7.12 built the revalidating bracket the live syscall seam runs: resolve the
declared footprint, acquire it, **re-resolve at the state the growing phase
ended in**, refuse on any change, and otherwise run the step from that state and
unwind.  RR7.39 needs the same discipline at the per-core scheduler entries, over
a different lock domain (`SchedLockId`, which spans the object store, the
per-core run queues and the per-core replenishment queues).

Writing it twice is the shape this project's key conventions name explicitly:
*one question answered in two places will diverge*.  "What does a revalidating
2PL bracket do?" is one question — the two domains differ only in which
primitives advance which words.  So the bracket is parameterised over a
**domain record** carrying exactly those primitives, and each domain supplies
one.

## What a domain must provide

`LockBracketDomain` names five things: the footprint type, the key type its
acquisition sequence is a list of, the sequence itself, the growing-phase fold,
the shrinking-phase fold (`unwind`, not `release` — WS-LC LC4), and the
held-predicate with its decidability.  Nothing about *which* words those folds
advance appears here, which is the point: the bracket's correctness argument
does not depend on it.

## What is deliberately **not** here

The bracket does not know whether a footprint is well-formed, sorted, or within
`maxLockSetSize`.  Those are the domain's own theorems, stated where the
footprints are, and a bracket that re-checked them would be a second answer to a
question already answered.  What the bracket *does* check — and what no
footprint-level theorem can — is that the resolution has not moved and that the
growing phase actually **granted** the set rather than queueing on it.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n.Model

/-- **WS-RR RR7.39**: what a bracketed step can do.

Three outcomes, because they oblige the caller differently and collapsing any
two of them loses something.  `undeclared` did not acquire and has nothing to
release — the caller keeps its coarser serialisation, which is always sound.
`refused` **did** acquire, so it carries the state with the footprint unwound;
returning a refusal without the unwinding would strand the footprint on
`lockCore` and block every later user of those objects.  `committed` ran the
step from the state the growing phase ended in and released after it. -/
inductive LockBracketOutcome (α : Type) where
  /-- No footprint is declared for this operation; the step ran unbracketed. -/
  | undeclared (result : α × SystemState)
  /-- A footprint was acquired and the guard then refused; the state carries the
  footprint **unwound** — released where it was granted, withdrawn where it was
  only queued. -/
  | refused (unwound : SystemState)
  /-- The guard passed; the step ran under the footprint, which was then
  released. -/
  | committed (result : α × SystemState)

/-- **WS-RR RR7.39**: the primitives a lock domain supplies to the bracket.

Five fields and no more.  A domain that needed a sixth would be telling the
bracket something about its own words, which is exactly what this record exists
to keep out of the bracket's argument. -/
structure LockBracketDomain where
  /-- The footprint type — `LockSet` at the object domain, the `SchedLockId`
  footprint at the scheduler domain. -/
  Footprint : Type
  /-- The key type the acquisition sequence is a list of. -/
  Key : Type
  /-- Decidable equality on footprints, so the revalidation can compare the
  re-resolved footprint against the acquired one. -/
  decEqFootprint : DecidableEq Footprint
  /-- The footprint's acquisition sequence, in the domain's own lock order.  The
  shrinking phase walks its reverse. -/
  sequence : Footprint → List Key
  /-- The growing phase: fold the domain's acquire primitive over a sequence. -/
  acquire : CoreId → List Key → SystemState → SystemState
  /-- The shrinking phase: withdraw then release, in one pass (WS-LC LC4). -/
  unwind : CoreId → List Key → SystemState → SystemState
  /-- Core `c` holds every lock the footprint declares, at the declared mode. -/
  held : CoreId → Footprint → SystemState → Prop
  /-- …decidably, so the bracket's guard is an `if`. -/
  heldDec : ∀ c S s, Decidable (held c S s)

attribute [instance] LockBracketDomain.decEqFootprint LockBracketDomain.heldDec

/-- **WS-RR RR7.39**: run a step inside its declared footprint, revalidating.

Resolve, acquire, **re-resolve at the state the growing phase ended in**, and
refuse on any change; on a match run the step from that state and unwind.

Two conditions, both necessary.  The resolution must not have moved — a
footprint's own read locks are members of the set it returns, so they are
acquired strictly after the reads they protect, and another core could replace
what those reads saw in between.  And the acquired state must actually **hold**
the footprint: the growing phase runs whether or not the set was granted, so a
step that ran on a contended footprint would have no exclusion at all.

The step runs from `acquired`, not from `st` — re-running it from `st` would
discard exactly the growing phase whose grant the guard just checked.

The shrinking phase is `unwind`, never a release-only fold (WS-LC LC4): a
release is the identity for a non-holder, so a release-only unwind leaves every
*contended* member of the footprint still queued on `lockCore`. -/
def runBracketed {α : Type} (D : LockBracketDomain)
    (declared : SystemState → Option D.Footprint)
    (lockCore : CoreId) (step : SystemState → α × SystemState) (st : SystemState) :
    LockBracketOutcome α :=
  match declared st with
  | none => .undeclared (step st)
  | some S =>
    let acquired := D.acquire lockCore (D.sequence S) st
    if declared acquired = some S ∧ D.held lockCore S acquired then
      let (v, post) := step acquired
      .committed (v, D.unwind lockCore (D.sequence S).reverse post)
    else
      .refused (D.unwind lockCore (D.sequence S).reverse acquired)

/-- **WS-RR RR7.39 (the fallback is exactly the unbracketed step)**: with no
footprint declared, the bracket is the bare step.

This is what makes installing a bracket safe ahead of the declarations it does
not yet have: every operation whose footprint is still `none` runs
bit-identically to the pre-bracket seam, on the pre-state, with no lock written.
Definitional, so a refactor that starts acquiring *something* on the undeclared
path stops this elaborating. -/
@[simp] theorem runBracketed_undeclared {α : Type} (D : LockBracketDomain)
    (declared : SystemState → Option D.Footprint) (lockCore : CoreId)
    (step : SystemState → α × SystemState) (st : SystemState)
    (h : declared st = none) :
    runBracketed D declared lockCore step st = .undeclared (step st) := by
  unfold runBracketed
  rw [h]

/-- **WS-RR RR7.39**: on the committed arm the step ran from the **acquired**
state and the returned state is that step's post-state, unwound. -/
theorem runBracketed_committed {α : Type} (D : LockBracketDomain)
    (declared : SystemState → Option D.Footprint) (lockCore : CoreId)
    (step : SystemState → α × SystemState) (st : SystemState) (S : D.Footprint)
    (hDecl : declared st = some S)
    (hGuard : declared (D.acquire lockCore (D.sequence S) st) = some S ∧
      D.held lockCore S (D.acquire lockCore (D.sequence S) st)) :
    runBracketed D declared lockCore step st
      = .committed ((step (D.acquire lockCore (D.sequence S) st)).1,
          D.unwind lockCore (D.sequence S).reverse
            (step (D.acquire lockCore (D.sequence S) st)).2) := by
  unfold runBracketed
  rw [hDecl]
  simp only [if_pos hGuard]

/-- **WS-RR RR7.39 (a refusal commits nothing but the unwinding)**: the state a
refusal carries is the pre-state with the footprint acquired and then unwound —
the step never ran, so no transition was committed.

The load-bearing negative.  A guard that refused *after* running the step would
be worse than no guard at all: the operation would have committed on a
resolution the guard judged stale. -/
theorem runBracketed_refused {α : Type} (D : LockBracketDomain)
    (declared : SystemState → Option D.Footprint) (lockCore : CoreId)
    (step : SystemState → α × SystemState) (st : SystemState) (S : D.Footprint)
    (hDecl : declared st = some S)
    (hGuard : ¬ (declared (D.acquire lockCore (D.sequence S) st) = some S ∧
      D.held lockCore S (D.acquire lockCore (D.sequence S) st))) :
    runBracketed D declared lockCore step st
      = .refused (D.unwind lockCore (D.sequence S).reverse
          (D.acquire lockCore (D.sequence S) st)) := by
  unfold runBracketed
  rw [hDecl]
  simp only [if_neg hGuard]

/-- **WS-RR RR7.39**: the state a bracket commits, as a function — the value the
three arms agree to return.

Named because every consumer of the bracket has to project a `SystemState` out
of the outcome (a kernel entry commits *a state*, not an outcome), and a
consumer that wrote its own `match` would be free to disagree with the next one
about what a refusal returns. -/
def LockBracketOutcome.state {α : Type} : LockBracketOutcome α → SystemState
  | .undeclared (_, s) => s
  | .refused s => s
  | .committed (_, s) => s

/-- **WS-RR RR7.39**: the value a bracket produced, where it ran the step.

`none` on a refusal, because a refused bracket did not run the step and has no
value to report — the honest answer, rather than a default the caller would
mistake for a result. -/
def LockBracketOutcome.value? {α : Type} : LockBracketOutcome α → Option α
  | .undeclared (v, _) => some v
  | .refused _ => none
  | .committed (v, _) => some v

@[simp] theorem LockBracketOutcome.state_undeclared {α : Type} (r : α × SystemState) :
    (LockBracketOutcome.undeclared r).state = r.2 := rfl

@[simp] theorem LockBracketOutcome.state_refused {α : Type} (s : SystemState) :
    (LockBracketOutcome.refused (α := α) s).state = s := rfl

@[simp] theorem LockBracketOutcome.state_committed {α : Type} (r : α × SystemState) :
    (LockBracketOutcome.committed r).state = r.2 := rfl

@[simp] theorem LockBracketOutcome.value?_undeclared {α : Type} (r : α × SystemState) :
    (LockBracketOutcome.undeclared r).value? = some r.1 := rfl

@[simp] theorem LockBracketOutcome.value?_refused {α : Type} (s : SystemState) :
    (LockBracketOutcome.refused (α := α) s).value? = none := rfl

@[simp] theorem LockBracketOutcome.value?_committed {α : Type} (r : α × SystemState) :
    (LockBracketOutcome.committed r).value? = some r.1 := rfl

/-- **WS-RR RR7.39**: with no footprint declared, the bracket's committed state
**is** the unbracketed step's — the projection-level form of
`runBracketed_undeclared`, which is what a kernel entry actually consumes. -/
theorem runBracketed_undeclared_state {α : Type} (D : LockBracketDomain)
    (declared : SystemState → Option D.Footprint) (lockCore : CoreId)
    (step : SystemState → α × SystemState) (st : SystemState)
    (h : declared st = none) :
    (runBracketed D declared lockCore step st).state = (step st).2 := by
  rw [runBracketed_undeclared D declared lockCore step st h]
  rfl

-- ============================================================================
-- §2  The object domain
-- ============================================================================

/-- **WS-RR RR7.39**: the SM0.I object domain as a bracket domain — `LockSet`
over `LockId`, with SM3.C's own acquire / unwind folds and `lockSetHeld`.

This is the domain RR7.12's syscall seam runs.  It is stated here rather than
beside the seam so the scheduler domain's instance sits next to it and a reader
can see that the two differ in exactly five primitives. -/
def objectLockBracketDomain : LockBracketDomain where
  Footprint := LockSet
  Key := LockId × AccessMode
  decEqFootprint := inferInstance
  sequence := LockSet.lockAcquireSequence
  acquire := acquireAll
  unwind := unwindAll
  held := lockSetHeld
  heldDec := fun c S s => lockSetHeld_decidable c S s

@[simp] theorem objectLockBracketDomain_sequence (S : LockSet) :
    objectLockBracketDomain.sequence S = S.lockAcquireSequence := rfl

@[simp] theorem objectLockBracketDomain_acquire (c : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState) :
    objectLockBracketDomain.acquire c pairs s = acquireAll c pairs s := rfl

@[simp] theorem objectLockBracketDomain_unwind (c : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState) :
    objectLockBracketDomain.unwind c pairs s = unwindAll c pairs s := rfl

@[simp] theorem objectLockBracketDomain_held (c : CoreId) (S : LockSet)
    (s : SystemState) :
    objectLockBracketDomain.held c S s = lockSetHeld c S s := rfl

end SeLe4n.Kernel.Concurrency
