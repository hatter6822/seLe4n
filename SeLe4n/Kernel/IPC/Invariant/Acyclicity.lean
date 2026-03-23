/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-! # TCB Queue Chain Acyclicity

Machine-checked proof that intrusive TCB queue chains (via `queueNext` links)
are acyclic. This prevents degenerate states such as self-loops, 2-cycles,
and N-cycles in the doubly-linked intrusive queue infrastructure.

The proofs follow the pattern established by `Service/Invariant/Acyclicity.lean`:
- **Layer 0:** Declarative definitions (edges, nontrivial paths, acyclicity).
- **Layer 1:** Structural lemmas (transitivity, edge lifting, cycle consequences).

Preservation proofs (Layer 2) live in `Structural.lean` alongside the existing
`tcbQueueLinkIntegrity` preservation theorems, since they share the same
state-threading infrastructure.

This invariant is added as a conjunct of `dualQueueSystemInvariant` and
enables the `prevTid ≠ nextTid` derivation needed for
`endpointQueueRemoveDual_preserves_dualQueueSystemInvariant` (T4-D). -/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- Layer 0: Declarative definitions
-- ============================================================================

/-- Direct edge in the TCB queue-next chain: thread `a` has `queueNext = some b`. -/
def tcbQueueNextEdge (st : SystemState) (a b : SeLe4n.ThreadId) : Prop :=
  ∃ tcbA, st.objects[a.toObjId]? = some (.tcb tcbA) ∧ tcbA.queueNext = some b

/-- Nontrivial path (length ≥ 1) in the TCB queue-next chain. A sequence of
one or more `tcbQueueNextEdge` steps from `a` to `b`. -/
inductive tcbQueueNontrivialPath (st : SystemState) : SeLe4n.ThreadId → SeLe4n.ThreadId → Prop where
  | single : tcbQueueNextEdge st a b → tcbQueueNontrivialPath st a b
  | cons   : tcbQueueNextEdge st a b → tcbQueueNontrivialPath st b c →
             tcbQueueNontrivialPath st a c

/-- The TCB queue-next chain is acyclic: no thread can reach itself via one
or more `queueNext` steps. This prevents self-loops (a→a), 2-cycles (a→b→a),
and cycles of any length. -/
def tcbQueueChainAcyclic (st : SystemState) : Prop :=
  ∀ tid, ¬ tcbQueueNontrivialPath st tid tid

-- ============================================================================
-- Layer 1: Structural lemmas
-- ============================================================================

/-- A single edge is a nontrivial path. -/
theorem tcbQueueNontrivialPath_of_edge {st : SystemState} {a b : SeLe4n.ThreadId}
    (h : tcbQueueNextEdge st a b) : tcbQueueNontrivialPath st a b :=
  .single h

/-- Nontrivial paths compose: if a→⁺b and b→⁺c, then a→⁺c. -/
theorem tcbQueueNontrivialPath_trans {st : SystemState} {a b c : SeLe4n.ThreadId}
    (hab : tcbQueueNontrivialPath st a b) (hbc : tcbQueueNontrivialPath st b c) :
    tcbQueueNontrivialPath st a c := by
  induction hab with
  | single hedge => exact .cons hedge hbc
  | cons hedge _ ih => exact .cons hedge (ih hbc)

/-- Acyclicity implies no self-loop: a thread's queueNext cannot point to itself. -/
theorem acyclic_no_self_loop {st : SystemState}
    (hAcyclic : tcbQueueChainAcyclic st)
    (a : SeLe4n.ThreadId) (tcbA : TCB)
    (hA : st.objects[a.toObjId]? = some (.tcb tcbA)) :
    tcbA.queueNext ≠ some a := by
  intro h
  exact hAcyclic a (.single ⟨tcbA, hA, h⟩)

/-- Acyclicity implies no 2-cycle: if a.next=some b, then b.next ≠ some a. -/
theorem acyclic_no_two_cycle {st : SystemState}
    (hAcyclic : tcbQueueChainAcyclic st)
    (a b : SeLe4n.ThreadId) (tcbA tcbB : TCB)
    (hA : st.objects[a.toObjId]? = some (.tcb tcbA))
    (hB : st.objects[b.toObjId]? = some (.tcb tcbB))
    (hAB : tcbA.queueNext = some b) :
    tcbB.queueNext ≠ some a := by
  intro hBA
  exact hAcyclic a (.cons ⟨tcbA, hA, hAB⟩ (.single ⟨tcbB, hB, hBA⟩))

end SeLe4n.Kernel
