-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Locks.TicketLockRefinement
import SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement
import SeLe4n.Kernel.Concurrency.Locks.QueuedRwLockRefinement

/-!
# WS-RR RR7.24 — the lock-refinement methodology, in one place

The panic-hang plan's Stream A named a `Locks/Refinement.lean` methodology hub
and two Tier-3 anchors on it.  Neither landed, so the plan carried an internal
reference to a file that does not exist, and each bridge kept its own copy of
the same prose in isolation.

This is that hub, and it is not only prose: the **block fold** every bridge is
built on is defined once here, and each bridge's own fold is pinned to it by
`rfl`.  A hub that merely described the method would be a fourth statement of
it; one that *is* the method has something to fail when a bridge drifts.

## The method

A refinement bridge in this tree relates a **concrete** state — the machine
words a Rust lock actually holds — to an **abstract** one — the `LockState` the
specification reasons about — and shows that every concrete execution the
implementation can perform maps onto a specification execution.  Three moving
parts, in every bridge:

1. **A simulation relation.**  `ticketLockSim`, `rwLockSim`, `queuedSim`.  It
   says what the concrete words mean.  Its conjuncts are the honest content of
   the bridge: `rwLockSim` deliberately does *not* represent the abstract
   `waiters` field, and says so, because the CAS-retry lock has no queue —
   which is why a FIFO claim goes through `queuedSim` and not through it.

2. **A block decomposition.**  One abstract operation is many concrete
   instructions, so the bridge folds a *list* of concrete operations and relates
   the endpoints.  That fold is `foldBlock` below; the per-bridge folds
   (`ticketFoldBlock`, `concreteFoldBlock`, `queuedFoldBlock`) are its
   instances, pinned as such in §3.

3. **A trace lifting.**  A list of blocks, related pairwise, lifts to a whole
   execution.  Each bridge states this as an inductive relation over lists
   (`ListTicketBlocks`, `ListBlockBisim`, the queued sibling) and a capstone
   over it.

## The two rules a bridge must not break

**A bridge may not assume its own conclusion.**  `rust_rwLock_refines_lean`
takes `ListBlockBisim` — which is the per-block form of what it concludes — so
it is kept only as the general form; the results that *assert* something are
the `_honest` ones, derived from the trace-shape predicate `honestBlock`.  A
new bridge states its capstone so that the hypothesis is a property of the
trace, not a per-block instance of the conclusion.

**A block shape may not exist for a call the code does not make.**  A `[]`
block for an operation the implementation performs atomically is a fiction, and
it was one: the CAS-retry lock's four `_noop` constructors and the ticket lock's
two claimed no-op blocks for calls that really do touch memory, and they were
deleted (PR #890 review rounds 2 and 4) rather than kept as harmless.  The
deployed `QueuedRwLock` is the only lock whose no-ops are real, because it
carries a per-core `held` word and branches on it; the others state their caller
contract instead (`TicketLockState.callerContract`,
`rw_lock.rs`'s module docs).
-/

namespace SeLe4n.Kernel.Concurrency.Refinement

-- ============================================================================
-- §1  The block fold, once
-- ============================================================================

/-- WS-RR RR7.24: apply a block of concrete operations in order.

The one definition all three bridges' folds are instances of. -/
def foldBlock {S Op : Type} (step : S → Op → S) (s : S) (ops : List Op) : S :=
  ops.foldl step s

@[simp] theorem foldBlock_nil {S Op : Type} (step : S → Op → S) (s : S) :
    foldBlock step s [] = s := rfl

@[simp] theorem foldBlock_cons {S Op : Type} (step : S → Op → S) (s : S)
    (op : Op) (ops : List Op) :
    foldBlock step s (op :: ops) = foldBlock step (step s op) ops := rfl

/-- WS-RR RR7.24: blocks compose.  Every bridge proves this for its own fold;
here it is proved once. -/
theorem foldBlock_append {S Op : Type} (step : S → Op → S) (s : S)
    (a b : List Op) :
    foldBlock step s (a ++ b) = foldBlock step (foldBlock step s a) b := by
  unfold foldBlock
  exact List.foldl_append

/-- WS-RR RR7.24: an operation that leaves the concrete state alone.

`isObservation` in each bridge; the property it must have is this one, and
`foldBlock_stutter` is what that property buys. -/
def StepPreserves {S Op : Type} (step : S → Op → S) (obs : Op → Bool) : Prop :=
  ∀ (s : S) (op : Op), obs op = true → step s op = s

/-- WS-RR RR7.24: a block of observations is a stutter — the concrete state at
the end is the state at the start.

Each bridge states this for its own fold (`ticketFoldBlock_stutter`,
`queuedFoldBlock_stutter`, and the CAS-retry lock's noop chain); the argument is
an induction on the list and does not depend on the lock. -/
theorem foldBlock_stutter {S Op : Type} (step : S → Op → S) (obs : Op → Bool)
    (hStep : StepPreserves step obs) (s : S) (ops : List Op)
    (hAll : ∀ op ∈ ops, obs op = true) :
    foldBlock step s ops = s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
    rw [foldBlock_cons, hStep s op (hAll op (List.mem_cons_self ..))]
    exact ih s (fun o ho => hAll o (List.mem_cons_of_mem op ho))

-- ============================================================================
-- §2  A stutter cannot be a whole bridge
-- ============================================================================

/-- WS-RR RR7.24: **the negative the method needs.**

If every operation in a block were an observation, the bridge would relate the
abstract step to a concrete block that changes nothing — the `[]`-block fiction
in list form.  This is the statement that such a block cannot witness a *state
change*, so a bridge claiming one has to exhibit a non-observation.

Stated because the two deleted no-op families were exactly this shape, and a
scanner cannot tell a legitimate observation block (a poll loop) from an
illegitimate one (an acquisition claimed to touch nothing).

Stated as the refusal rather than as an existential: constructively, "not every
operation here is an observation" is what the hypothesis yields, and the
existential form would need a classical step to say no more. -/
theorem foldBlock_changes_state_needs_a_write {S Op : Type} (step : S → Op → S)
    (obs : Op → Bool) (hStep : StepPreserves step obs) (s : S) (ops : List Op)
    (hChanged : foldBlock step s ops ≠ s) :
    ¬ (∀ op ∈ ops, obs op = true) :=
  fun hAll => hChanged (foldBlock_stutter step obs hStep s ops hAll)

-- ============================================================================
-- §3  The three bridges' folds *are* this fold
-- ============================================================================

open SeLe4n.Kernel.Concurrency in
/-- WS-RR RR7.24: the ticket lock's block fold is the generic one. -/
theorem ticketFoldBlock_eq_foldBlock (conc : TicketLockConcrete)
    (blk : List ConcreteTicketLockOp) :
    ticketFoldBlock conc blk = foldBlock TicketLockConcrete.applyOp conc blk := rfl

open SeLe4n.Kernel.Concurrency in
/-- WS-RR RR7.24: the CAS-retry lock's block fold is the generic one. -/
theorem concreteFoldBlock_eq_foldBlock (conc : UInt64)
    (blk : List ConcreteRwLockOp) :
    concreteFoldBlock conc blk
      = foldBlock (fun s op => (concreteApplyOp s op).1) conc blk := rfl

open SeLe4n.Kernel.Concurrency in
/-- WS-RR RR7.24: the deployed ticket-FIFO lock's block fold is the generic
one. -/
theorem queuedFoldBlock_eq_foldBlock (conc : QueuedRwLockConcrete)
    (blk : List QueuedRwLockOp) :
    queuedFoldBlock conc blk
      = foldBlock (fun s op => (s.applyOp op).1) conc blk := rfl

end SeLe4n.Kernel.Concurrency.Refinement
