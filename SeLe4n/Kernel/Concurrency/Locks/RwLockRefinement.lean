-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM2.C.20 RwLock refinement bridge).

import SeLe4n.Kernel.Concurrency.Locks.RwLock

/-!
# WS-SM SM2.C.20 — RwLock refinement bridge

This module documents the operational refinement relation between the
Lean abstract `RwLockState` (in `Locks/RwLock.lean`) and the Rust impl
(in `rust/sele4n-hal/src/rw_lock.rs`).

## Refinement summary

The refinement φ relates a Lean `RwLockState` to a Rust `AtomicU64` state
value via the bit-packed encoding:

    φ(abstract, concrete) ↔
      concrete = encodeRwLock abstract.writerHeld.isSome abstract.readers.length

* abstract.writerHeld.isSome corresponds to bit 63 of concrete (the writer bit).
* abstract.readers.length corresponds to bits 0..62 of concrete (the reader count).
* abstract.waiters is **NOT represented** in the concrete state.  The Rust
  impl uses CAS-retry with WFE for waiters; the queue is implicit through
  the order in which threads observe the state.

## FIFO divergence

The Lean spec's `rwLock_fifo_admission` theorem states that earlier
waiters are admitted before later waiters.  The Rust impl does NOT
satisfy this property: a thread that just called `acquire_read` on a
contended lock may observe the writer-bit clear and CAS-acquire BEFORE
an earlier-arrived writer that's still parked on WFE.

The mutex and exclusion invariants (`rwLock_writer_readers_exclusion`)
ARE satisfied by the Rust impl, because the CAS-retry ensures only one
core can claim the writer bit at a time, and the same-state CAS ensures
readers don't admit while writer-bit is set.

## What SM3 must verify

SM3 (per-object locks) consumes the RwLock primitive for protecting
shared kernel objects.  Per-object lock proofs cite:

* `rwLock_writer_readers_exclusion` — for state-visibility lemmas:
  writer-protected fields are not concurrently observable by readers.
* `rwLock_release_acquire_pairing_read/write` — for happens-before
  edges across release-acquire boundaries.
* `rwLock_bounded_wait_read/write` — for WCRT analysis.

SM3 does NOT rely on `rwLock_fifo_admission`.  Kernel paths that require
strict FIFO writer admission (e.g., for response-time analysis under
heavy reader contention) are flagged at SM3 review time.  If any are
found, SM2.C.20 will be extended with a queued RwLock variant.

## Simulation φ (informal)

A formal bisimulation between the Lean operational `applyOp` and the
Rust CAS-retry loop is a substantial proof that goes through:

1. At each operational step, the Rust state's bit-packed encoding equals
   `encodeRwLock(abstract.writerHeld.isSome, abstract.readers.length)`.
2. The Rust CAS-retry loop's progress condition matches the Lean spec's
   acquire branch condition.
3. The Rust release path's atomic decrement / store matches the Lean
   spec's `applyOp .releaseRead/releaseWrite` + promote step.

We do not encode this bisimulation formally at v1.0.0; instead, the
refinement is reviewed at per-PR level (each Rust function's docstring
references the corresponding Lean operation).  The cargo unit tests
exercise the round-trip encoding (`encoding_round_trip`) so the
bit-level correspondence is mechanically verified.

## Why not a full bisimulation proof?

Per decision #10 in the SM2 plan, the lock primitives are "verification-
quality elevated" — the Lean spec is the source of truth.  A full
formal bisimulation between the spec and impl would require:

* A FFI-level model of the Rust atomic operations (LDAR, STLR, CAS).
* A trace-based equivalence proof at the operational-semantics level.
* Mechanically checked code generation from the Lean spec to Rust.

The first two are tractable but expensive (estimated 5-10 weeks for
RwLock alone).  The third is research-grade infrastructure.

At v1.0.0, we accept the simulation as a per-PR review obligation.  The
refinement is "live": every Rust function references its Lean
counterpart in a docstring; every Lean theorem cites the corresponding
ARM instruction in its docstring; the cargo round-trip tests verify the
bit-level encoding mechanically.  This is "weak refinement with strong
spec" — the spec is verified end-to-end; the impl correspondence is
reviewer-checked at the operational level.

Post-1.0 work (SM2.C.20.a) will introduce a stricter bisimulation
checker if SM3 surfaces correspondence bugs.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM2.C.20 — Refinement φ between abstract and concrete state
-- ============================================================================

/-- **WS-SM SM2.C.20**: the refinement relation between the Lean
abstract `RwLockState` and the Rust impl's bit-packed `state : AtomicU64`.

The relation is structural:
* The concrete state equals `encodeRwLock(writerHeld.isSome, readers.length)`.
* The abstract `waiters` field is NOT represented in the concrete state
  (the Rust impl uses CAS-retry instead of an explicit queue, weakening
  FIFO admission).

The `RwLockEncoded` value is the abstraction of the Rust `AtomicU64.load(...)`
result; bit operations on it correspond to bit operations on the Rust value. -/
def rwLockSim (abstract : RwLockState) (concrete : RwLockEncoded) : Prop :=
  concrete = encodeRwLock abstract.writerHeld.isSome abstract.readers.length

/-- **WS-SM SM2.C.20**: `rwLockSim` is decidable. -/
instance decidableRwLockSim (abstract : RwLockState) (concrete : RwLockEncoded) :
    Decidable (rwLockSim abstract concrete) := by
  unfold rwLockSim
  exact inferInstance

/-- **Witness**: the unheld abstract state corresponds to concrete state 0. -/
theorem rwLockSim_unheld : rwLockSim RwLockState.unheld 0 := by
  unfold rwLockSim encodeRwLock RwLockState.unheld
  simp

/-- **Witness**: an abstract state with a writer and no readers corresponds
to concrete state `writerBit`. -/
theorem rwLockSim_writer_only (c : CoreId) :
    rwLockSim { writerHeld := some c, readers := [], waiters := [] }
              writerBit := by
  unfold rwLockSim encodeRwLock
  simp

/-- **Witness**: an abstract state with N readers corresponds to concrete
state N.

(Audit pass-3 LOW-3 fix: removed the unused `readers.Nodup` hypothesis.
The simulation relation depends only on the list LENGTH, not on whether
the list is Nodup.  Callers that need Nodup for the state to be `wf`
can prove that separately.) -/
theorem rwLockSim_readers_only (readers : List CoreId) :
    rwLockSim { writerHeld := none, readers := readers, waiters := [] }
              readers.length := by
  unfold rwLockSim encodeRwLock
  simp

/-- **Surface anchor**: the refinement relation respects the writer bit.

If the concrete state has bit 63 set, then the abstract state has a
writer held (the simulation φ requires writerHeld.isSome ↔ bit 63 set). -/
theorem rwLockSim_writer_bit_iff
    (abstract : RwLockState) (concrete : RwLockEncoded)
    (h_sim : rwLockSim abstract concrete)
    (h_count_bound : abstract.readers.length < writerBit) :
    concrete ≥ writerBit ↔ abstract.writerHeld.isSome := by
  unfold rwLockSim at h_sim
  rw [h_sim]
  constructor
  · -- encodeRwLock w c ≥ writerBit → w = true.
    intro h_ge
    cases h_some : abstract.writerHeld.isSome with
    | true => rfl
    | false =>
      -- writerHeld.isSome = false → encodeRwLock false c = c < writerBit.
      exfalso
      rw [h_some] at h_ge
      unfold encodeRwLock at h_ge
      have h_simp : (if (false : Bool) then writerBit else 0) + abstract.readers.length
                  = abstract.readers.length := by simp
      rw [h_simp] at h_ge
      exact absurd h_ge (Nat.not_le_of_lt h_count_bound)
  · -- writerHeld.isSome → encodeRwLock true c ≥ writerBit.
    intro h_is_some
    unfold encodeRwLock
    rw [h_is_some]
    show (if (true : Bool) then writerBit else 0) + abstract.readers.length ≥ writerBit
    simp

/-- **Surface anchor**: the refinement preserves reader count when no
writer is held.

If writer is not held, the concrete state equals the reader count exactly. -/
theorem rwLockSim_reader_count_iff
    (abstract : RwLockState) (concrete : RwLockEncoded)
    (h_sim : rwLockSim abstract concrete)
    (h_no_writer : abstract.writerHeld = none) :
    concrete = abstract.readers.length := by
  unfold rwLockSim at h_sim
  rw [h_sim]
  unfold encodeRwLock
  rw [h_no_writer]
  simp

-- ============================================================================
-- SM2.C.20 — Refinement preservation theorems
-- ============================================================================

/-- **Theorem (SM2.C.20): refinement is preserved by no-op transitions.**

If an abstract operation is a no-op on the abstract state, then the
simulation relation is preserved (the concrete state, which doesn't
change in the no-op case at the Rust impl level either, still relates
to the post-state).

This is the substantive base case of the full bisimulation: every
no-op in the abstract layer corresponds to a no-op in the concrete
layer (no atomic operations are performed in either case), so
`rwLockSim` is trivially preserved.

(Audit pass-3 LOW-2 fix: replaces the prior `True := trivial`
placeholder with this substantive partial result.) -/
theorem rwLock_refinement_preservation_noop
    (abstract : RwLockState) (concrete : RwLockEncoded)
    (h_sim : rwLockSim abstract concrete)
    (op : RwLockOp)
    (h_noop : abstract.applyOp op = abstract) :
    rwLockSim (abstract.applyOp op) concrete := by
  rw [h_noop]
  exact h_sim

/-- **Theorem (SM2.C.20): full bisimulation deferred to post-1.0.**

The full bisimulation theorem requires modeling the Rust impl's
atomic-operation step function in Lean (encoded against a memory-event
trace).  At v1.0.0, we do NOT do this; the refinement between the
abstract Lean spec and the Rust impl is reviewed per-PR via the
operational-mapping table in `rust/sele4n-hal/src/rw_lock.rs`'s module
header.

A future post-1.0 phase (tentatively SM2.C.20.a) could introduce a
trace-based refinement using SM2.A's `MemoryTrace`.  The interface
shape would be:

    theorem rwLockRefinement_full :
      ∀ (impl_trace : MemoryTrace) (lean_trace : List RwLockOp),
        impl_trace.wellFormed →
        rustImplementsRwLock impl_trace lean_trace →
        rwLockSim (lean_trace.foldl applyOp .unheld)
                  (impl_state_from_trace impl_trace)

where `rustImplementsRwLock` is a structural correspondence predicate
and `impl_state_from_trace` extracts the latest `state` value from
the memory trace.  Neither helper is implemented at v1.0.0.

This `example` block documents the deferred work without inflating
the proof surface with a `True := trivial` theorem. -/
example : True := trivial

-- ============================================================================
-- SM2.C-defer D-4 — Bisimulation refinement (rwLockSim-aware)
-- ============================================================================

/-- **WS-SM SM2.C-defer D-4.6 (rwLockSim-aware)**: under the simulation
relation, an abstract state with a reader corresponds to a concrete
state ≥ 1, so `fetch_sub(1)` does not underflow.

Bridges `encodeRwLock_at_least_one_when_reader` (in `RwLock.lean`) into
the `rwLockSim` predicate.  Used by D-4.5 to discharge the underflow
precondition of `concreteApplyOp .fetchSubRead`. -/
theorem concreteApplyOp_fetch_sub_no_underflow
    (abstract : RwLockState) (concrete : RwLockEncoded) (c : CoreId)
    (h_sim : rwLockSim abstract concrete)
    (h_holder : c ∈ abstract.readers) :
    concrete ≥ 1 := by
  unfold rwLockSim at h_sim
  rw [h_sim]
  exact encodeRwLock_at_least_one_when_reader abstract c h_holder

/-- **WS-SM SM2.C-defer D-4.3 (helper inductive)**: pointwise
correspondence between an abstract op-list and a list of concrete blocks.

Both lists must have the same length, and at each position the
abstract op corresponds to its concrete block via `opCorresponds`. -/
inductive ListCorresponds :
    List RwLockOp → List (List ConcreteRwLockOp) → Prop where
  | nil : ListCorresponds [] []
  | cons : ∀ {a as b bs},
      opCorresponds a b →
      ListCorresponds as bs →
      ListCorresponds (a :: as) (b :: bs)

/-- **WS-SM SM2.C-defer D-4.3 (corresponds predicate)**: a Rust concrete
op-sequence implements a Lean abstract op-list iff the concrete sequence
can be split into per-abstract-op blocks, each admissible by
`opCorresponds`. -/
def rustImplementsRwLock
    (conc : List ConcreteRwLockOp) (abs : List RwLockOp) : Prop :=
  ∃ (blocks : List (List ConcreteRwLockOp)),
    blocks.flatten = conc ∧ ListCorresponds abs blocks

/-- **WS-SM SM2.C-defer D-4 (no-op base case)**: an empty concrete trace
implements an empty abstract trace; the refinement φ is preserved. -/
theorem rust_rwLock_refines_lean_nil
    (initial_abs : RwLockState) (initial_conc : RwLockEncoded)
    (h_sim_init : rwLockSim initial_abs initial_conc) :
    rwLockSim (([] : List RwLockOp).foldl RwLockState.applyOp initial_abs) initial_conc := by
  simp; exact h_sim_init

/-- **WS-SM SM2.C-defer D-4 (state-preserving sub-ops)**: load, wfeWait,
and sev all preserve concrete state.

These are the "observation" ops in `opCorresponds` — they appear at
the head of CAS-retry / park-retry sequences before the state-changing
CAS or fetch_*.  Their state-preservation underpins the inductive
bisimulation: a long CAS-retry prefix preserves both abstract and
concrete states, so the simulation φ is preserved across the prefix. -/
theorem concreteApplyOp_load_preserves_state (state : UInt64) (c : CoreId) :
    (concreteApplyOp state (.load c)).1 = state := by
  unfold concreteApplyOp; rfl

theorem concreteApplyOp_wfeWait_preserves_state (state : UInt64) (c : CoreId) :
    (concreteApplyOp state (.wfeWait c)).1 = state := by
  unfold concreteApplyOp; rfl

theorem concreteApplyOp_sev_preserves_state (state : UInt64) (c : CoreId) :
    (concreteApplyOp state (.sev c)).1 = state := by
  unfold concreteApplyOp; rfl

/-- **WS-SM SM2.C-defer D-4 (simulation preservation under state-preserving ops)**:
a state-preserving concrete op preserves the simulation relation.

For an abstract no-op and any of the three state-preserving concrete
ops (load / wfeWait / sev), the simulation φ is preserved. -/
theorem rwLockSim_preserved_by_load
    (abstract : RwLockState) (concrete : RwLockEncoded) (_c : CoreId)
    (h_sim : rwLockSim abstract concrete) :
    rwLockSim abstract concrete := h_sim

/-- **WS-SM SM2.C-defer D-4.5 (abstract acquire-direct shape ⇒ encoded
form)**: when the abstract state transitions via direct-acquire-read,
the encoded post-state equals the encoded pre-state plus 1.

This is the foundational identity for the bisimulation: the abstract
`applyOp .tryAcquireRead` (direct branch) corresponds to the concrete
`casAcquireRead` (success branch) at the encoded level. -/
theorem rwLockSim_preserved_by_direct_acquire_read
    (abstract : RwLockState) (c : CoreId)
    (h_not_inv : ¬ abstract.coreInvolved c)
    (h_no_writer : abstract.writerHeld = none)
    (h_waiters_empty : abstract.waiters = []) :
    let post := abstract.applyOp (.tryAcquireRead c)
    encodeRwLock post.writerHeld.isSome post.readers.length =
      encodeRwLock abstract.writerHeld.isSome abstract.readers.length + 1 := by
  have h_shape := tryAcquireRead_direct_acquire_shape abstract c h_not_inv h_no_writer
    h_waiters_empty
  show encodeRwLock _ _ = encodeRwLock _ _ + 1
  rw [h_shape.1, h_shape.2.1]
  -- post.readers = c :: abstract.readers; post.writerHeld = abstract.writerHeld.
  unfold encodeRwLock
  rw [List.length_cons]
  -- Goal: (if w then writerBit else 0) + (abstract.readers.length + 1)
  --     = (if w then writerBit else 0) + abstract.readers.length + 1
  -- Both sides are `Nat`; use Nat.add_assoc.
  exact Nat.add_assoc _ _ 1 |>.symm

/-- **WS-SM SM2.C-defer D-4.7 (abstract acquire-direct write shape ⇒
encoded form)**: when the abstract state transitions via direct-acquire-
write, the encoded post-state has the writer bit set.

This is the foundational identity for the writer-side bisimulation. -/
theorem rwLockSim_preserved_by_direct_acquire_write
    (abstract : RwLockState) (c : CoreId)
    (h_not_inv : ¬ abstract.coreInvolved c)
    (h_no_writer : abstract.writerHeld = none)
    (h_no_readers : abstract.readers = [])
    (h_no_waiters : abstract.waiters = []) :
    let post := abstract.applyOp (.tryAcquireWrite c)
    encodeRwLock post.writerHeld.isSome post.readers.length = writerBit := by
  have h_shape := tryAcquireWrite_direct_acquire_shape abstract c h_not_inv h_no_writer
    h_no_readers h_no_waiters
  show encodeRwLock _ _ = writerBit
  rw [h_shape.1, h_shape.2.1, h_no_readers]
  unfold encodeRwLock
  simp

/-- **WS-SM SM2.C-defer D-4 (no-op fold preserves)**: a list of no-op
abstract operations preserves the simulation.

This is the structural form that the full bisimulation `rust_rwLock_refines_lean`
will eventually use: a chain of no-op abstract operations corresponds
to a chain of state-preserving concrete operations, so the simulation
holds at every position. -/
theorem rwLockSim_preserved_by_noop_chain
    (abstract : RwLockState) (concrete : RwLockEncoded)
    (h_sim : rwLockSim abstract concrete)
    (ops : List RwLockOp)
    (h_all_noop : ∀ op ∈ ops, abstract.applyOp op = abstract) :
    rwLockSim (ops.foldl RwLockState.applyOp abstract) concrete := by
  induction ops with
  | nil => simp; exact h_sim
  | cons head tail ih =>
    -- applyOp on head is a no-op, so folding tail from abstract.applyOp head
    -- equals folding tail from abstract.
    have h_head : abstract.applyOp head = abstract := h_all_noop head (List.mem_cons_self)
    rw [List.foldl_cons, h_head]
    apply ih
    intro op h_in
    exact h_all_noop op (List.mem_cons_of_mem _ h_in)

-- ============================================================================
-- SM2.C-defer D-4.9 — Full bisimulation main theorem
-- ============================================================================

/-- **WS-SM SM2.C-defer D-4.9 (concrete state-fold)**: fold
`concreteApplyOp` over a block of concrete operations, returning the
final UInt64 state.

This is the canonical "execute the Rust trace" semantics.  The bisim
relates the abstract `applyOp` fold to this concrete fold via
`rwLockSim` after a `.toNat` conversion (UInt64 → Nat). -/
def concreteFoldBlock (initial_conc : UInt64)
    (conc_block : List ConcreteRwLockOp) : UInt64 :=
  conc_block.foldl (fun s op => (concreteApplyOp s op).1) initial_conc

theorem concreteFoldBlock_append (conc : UInt64) (a b : List ConcreteRwLockOp) :
    concreteFoldBlock conc (a ++ b)
      = concreteFoldBlock (concreteFoldBlock conc a) b := by
  unfold concreteFoldBlock; rw [List.foldl_append]

/-- **WS-SM SM2.C-defer D-4.9 (block bisim)**: per-block bisim
obligation — after applying `abs_op` to `abs` and folding `conc_block`
over `conc`, the resulting states are sim-related (via the
UInt64.toNat bridge).

This is the per-block obligation that an honest Rust trace satisfies
by construction (the impl loads-then-CAS-with-loaded-value, so the
CAS parameters always match the current state).  We make the
consistency explicit in the bisim theorem rather than baking it into
`opCorresponds` (avoiding a breaking refactor of the existing
inductive). -/
def blockBisim (abs : RwLockState) (conc : UInt64)
    (abs_op : RwLockOp) (conc_block : List ConcreteRwLockOp) : Prop :=
  rwLockSim (abs.applyOp abs_op) (concreteFoldBlock conc conc_block).toNat

/-- **WS-SM SM2.C-defer D-4.9 (list bisim consistency)**: every block
in a `ListCorresponds` chain satisfies the per-block bisim obligation
at its respective state.

This is the explicit consistency hypothesis that `rust_rwLock_refines_lean`
takes.  An honest Rust trace discharges it block-by-block via the
discharge lemmas (`blockBisim_of_noop`, `blockBisim_tryRead_success`,
etc.). -/
inductive ListBlockBisim :
    RwLockState → UInt64 → List RwLockOp → List (List ConcreteRwLockOp) → Prop where
  | nil (abs : RwLockState) (conc : UInt64) :
      ListBlockBisim abs conc [] []
  | cons (abs : RwLockState) (conc : UInt64) (a : RwLockOp) (b : List ConcreteRwLockOp)
         (as : List RwLockOp) (bs : List (List ConcreteRwLockOp)) :
      blockBisim abs conc a b →
      ListBlockBisim (abs.applyOp a) (concreteFoldBlock conc b) as bs →
      ListBlockBisim abs conc (a :: as) (b :: bs)

/-- **WS-SM SM2.C-defer D-4.9 (FULL MAIN THEOREM)**: bisimulation.

For an abstract trace and its corresponding concrete trace (via
`rustImplementsRwLock`-style `ListCorresponds`), if the trace's
per-block bisim obligations are discharged (via `ListBlockBisim`),
then the abstract `applyOp` fold and the concrete `concreteApplyOp`
fold produce sim-related states.

**Why the explicit `ListBlockBisim` hypothesis**: the bare
`opCorresponds` inductive in `RwLock.lean` permits CAS constructors
with arbitrary `expected` / `new` parameters (e.g., the `tryRead_success`
constructor is `(e n : UInt64) → opCorresponds ...`).  Without
state-awareness, the bisim is unsound: a trace with `tryRead_success c
999 999` would have the abstract direct-acquire but the concrete CAS
fail.  `ListBlockBisim` makes the state-consistency explicit at each
block; an honest Rust trace satisfies it by construction (the impl's
load-then-CAS-with-loaded-value protocol ensures `e = state`).

**Composition with existing partial forms**: the per-block obligations
(`blockBisim abs conc abs_op conc_block`) can be discharged via the
existing `rwLockSim_preserved_by_direct_acquire_read/write`,
`rwLockSim_preserved_by_noop_chain`, and state-preservation lemmas
(`concreteApplyOp_load_preserves_state`, etc.).

**Proof**: by induction on `ListBlockBisim`.  The `nil` case is
immediate.  The `cons` case unfolds one step: the abstract fold
extends by one op, the concrete fold extends by one block; the
per-block hypothesis discharges the simulation extension; the
inductive hypothesis discharges the remaining chain. -/
theorem rust_rwLock_refines_lean
    (initial_abs : RwLockState) (initial_conc : UInt64)
    (h_sim_init : rwLockSim initial_abs initial_conc.toNat)
    (abs_ops : List RwLockOp)
    (conc_blocks : List (List ConcreteRwLockOp))
    (h_blocks_bisim : ListBlockBisim initial_abs initial_conc abs_ops conc_blocks) :
    rwLockSim
      (abs_ops.foldl RwLockState.applyOp initial_abs)
      (concreteFoldBlock initial_conc conc_blocks.flatten).toNat := by
  -- Induction on h_blocks_bisim's structure.
  induction h_blocks_bisim with
  | nil _ _ =>
    -- Empty: both folds return initial states; sim from h_sim_init.
    simp [concreteFoldBlock]
    exact h_sim_init
  | cons abs conc a b as bs h_block _h_rest ih =>
    -- One step: the abstract fold becomes (a :: as).foldl = (as.foldl applied to applyOp a abs).
    -- The concrete fold becomes (b :: bs).flatten.foldl = bs.flatten.foldl applied to
    --   (b.foldl ... conc) = (concreteFoldBlock conc b).
    -- h_block discharges the single-step sim extension; ih discharges the rest.
    show rwLockSim
      ((a :: as).foldl RwLockState.applyOp abs)
      (concreteFoldBlock conc ((b :: bs).flatten)).toNat
    -- Simplify the folds.
    rw [List.foldl_cons]
    have h_flatten : (b :: bs).flatten = b ++ bs.flatten := by
      simp [List.flatten_cons]
    rw [h_flatten]
    -- concreteFoldBlock over (b ++ bs.flatten) = concreteFoldBlock (concreteFoldBlock conc b) bs.flatten.
    have h_fold_append : concreteFoldBlock conc (b ++ bs.flatten) =
        concreteFoldBlock (concreteFoldBlock conc b) bs.flatten := by
      unfold concreteFoldBlock
      rw [List.foldl_append]
    rw [h_fold_append]
    -- Use ih.
    exact ih h_block

/-- **WS-SM SM2.C-defer D-4.9 (corollary — via rustImplementsRwLock)**:
the bisim theorem stated using the structural `rustImplementsRwLock`
predicate.

This is the form that matches the plan's §5.4 statement.  The
`ListBlockBisim` consistency is still needed as an explicit precondition
(see the main theorem's docstring for the rationale). -/
theorem rust_rwLock_refines_lean_via_rustImplementsRwLock
    (initial_abs : RwLockState) (initial_conc : UInt64)
    (h_sim_init : rwLockSim initial_abs initial_conc.toNat)
    (abs_ops : List RwLockOp)
    (conc_ops : List ConcreteRwLockOp)
    (_h_corresponds : rustImplementsRwLock conc_ops abs_ops)
    (h_blocks_bisim : ∃ blocks : List (List ConcreteRwLockOp),
        blocks.flatten = conc_ops ∧
        ListCorresponds abs_ops blocks ∧
        ListBlockBisim initial_abs initial_conc abs_ops blocks) :
    rwLockSim
      (abs_ops.foldl RwLockState.applyOp initial_abs)
      (concreteFoldBlock initial_conc conc_ops).toNat := by
  obtain ⟨blocks, h_flatten, _h_list_corr, h_block_bisim⟩ := h_blocks_bisim
  rw [← h_flatten]
  exact rust_rwLock_refines_lean initial_abs initial_conc h_sim_init abs_ops blocks
    h_block_bisim

-- ============================================================================
-- SM2.C-defer D-4.9 — Per-block bisim discharge lemmas
-- ============================================================================

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — load-only)**: a
single `[.load c]` concrete block always preserves concrete state. -/
theorem concreteFoldBlock_load (conc : UInt64) (c : CoreId) :
    concreteFoldBlock conc [.load c] = conc := by
  unfold concreteFoldBlock; simp [concreteApplyOp]

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — wfeWait-only)**: a
single `[.wfeWait c]` concrete block always preserves concrete state. -/
theorem concreteFoldBlock_wfe (conc : UInt64) (c : CoreId) :
    concreteFoldBlock conc [.wfeWait c] = conc := by
  unfold concreteFoldBlock; simp [concreteApplyOp]

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — sev-only)**: a
single `[.sev c]` concrete block always preserves concrete state. -/
theorem concreteFoldBlock_sev (conc : UInt64) (c : CoreId) :
    concreteFoldBlock conc [.sev c] = conc := by
  unfold concreteFoldBlock; simp [concreteApplyOp]

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — abstract no-op)**:
if the abstract op is a no-op AND the concrete block preserves state,
then the block bisim holds. -/
theorem blockBisim_of_noop
    (abs : RwLockState) (conc : UInt64)
    (h_sim : rwLockSim abs conc.toNat)
    (abs_op : RwLockOp)
    (conc_block : List ConcreteRwLockOp)
    (h_abs_noop : abs.applyOp abs_op = abs)
    (h_conc_noop : concreteFoldBlock conc conc_block = conc) :
    blockBisim abs conc abs_op conc_block := by
  unfold blockBisim
  rw [h_abs_noop, h_conc_noop]
  exact h_sim

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — tryRead_success)**:
when the abstract is in direct-acquire-read shape AND the CAS values
in the concrete block are consistent with the current state, the block
bisim holds.

Consistency conditions:
* `e = conc` (CAS expected = current concrete state, so CAS succeeds).
* `n.toNat = conc.toNat + 1` (CAS new = state + 1, matching the
  abstract direct-acquire-read's reader-count increment).

The Rust impl's `acquire_read` satisfies these by construction (load
returns conc; CAS uses loaded value as expected and loaded+1 as new). -/
theorem blockBisim_tryRead_success
    (abs : RwLockState) (conc : UInt64)
    (h_sim : rwLockSim abs conc.toNat)
    (c : CoreId)
    (h_not_inv : ¬ abs.coreInvolved c)
    (h_no_writer : abs.writerHeld = none)
    (h_no_waiters : abs.waiters = [])
    (e n : UInt64)
    (h_cas_expected : e = conc)
    (h_cas_new : n.toNat = conc.toNat + 1) :
    blockBisim abs conc (.tryAcquireRead c) [.load c, .casAcquireRead c e n] := by
  unfold blockBisim concreteFoldBlock
  -- Reduce the fold: load doesn't change state, CAS-success returns n.
  simp only [List.foldl_cons, List.foldl_nil]
  have h_load : (concreteApplyOp conc (.load c)).1 = conc := by simp [concreteApplyOp]
  rw [h_load]
  -- Apply CAS: state = e → result = n.
  have h_cas : (concreteApplyOp conc (.casAcquireRead c e n)).1 = n := by
    unfold concreteApplyOp
    simp [h_cas_expected]
  rw [h_cas]
  -- Now show rwLockSim (abs.applyOp (.tryAcquireRead c)) n.toNat.
  -- Use h_cas_new: n.toNat = conc.toNat + 1.
  rw [h_cas_new]
  -- Now show rwLockSim (abs.applyOp ...) (conc.toNat + 1).
  -- By rwLockSim_preserved_by_direct_acquire_read, the encoded post = encoded pre + 1.
  -- h_sim says conc.toNat = encoded pre.  So conc.toNat + 1 = encoded post.
  unfold rwLockSim at h_sim ⊢
  have h_step := rwLockSim_preserved_by_direct_acquire_read abs c h_not_inv h_no_writer h_no_waiters
  -- h_step : encodeRwLock (post.writerHeld.isSome) (post.readers.length) =
  --          encodeRwLock (abs.writerHeld.isSome) (abs.readers.length) + 1.
  rw [h_step]
  rw [h_sim]

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — tryRead CAS-retry)**:
when the CAS fails (state ≠ expected), the block reduces to the no-op
case structurally.

Used in the inductive `tryRead_cas_retry` opCorresponds constructor:
the block is [load, casFail] ++ tail, where casFail leaves state
unchanged.  Recursing on `tail` requires `blockBisim` on the same abs
state but with conc unchanged. -/
theorem blockBisim_tryRead_cas_fail_chain
    (abs : RwLockState) (conc : UInt64)
    (abs_op : RwLockOp)
    (c : CoreId) (e n : UInt64) (tail : List ConcreteRwLockOp)
    (h_cas_fails : conc ≠ e)
    (h_tail_bisim : blockBisim abs conc abs_op tail) :
    blockBisim abs conc abs_op ([.load c, .casAcquireRead c e n] ++ tail) := by
  unfold blockBisim concreteFoldBlock at h_tail_bisim ⊢
  -- The prefix [load, casFail] preserves state; reduce to the tail.
  simp only [List.cons_append, List.nil_append, List.foldl_cons]
  have h_load : (concreteApplyOp conc (.load c)).1 = conc := by simp [concreteApplyOp]
  rw [h_load]
  have h_cas : (concreteApplyOp conc (.casAcquireRead c e n)).1 = conc := by
    unfold concreteApplyOp
    simp [h_cas_fails]
  rw [h_cas]
  exact h_tail_bisim

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — tryRead park-retry)**:
when the block prefix is [load, wfeWait] (both state-preserving), the
block reduces to the no-op case structurally. -/
theorem blockBisim_tryRead_park_retry_chain
    (abs : RwLockState) (conc : UInt64)
    (abs_op : RwLockOp)
    (c : CoreId) (tail : List ConcreteRwLockOp)
    (h_tail_bisim : blockBisim abs conc abs_op tail) :
    blockBisim abs conc abs_op ([.load c, .wfeWait c] ++ tail) := by
  unfold blockBisim concreteFoldBlock at h_tail_bisim ⊢
  simp only [List.cons_append, List.nil_append, List.foldl_cons]
  have h_load : (concreteApplyOp conc (.load c)).1 = conc := by simp [concreteApplyOp]
  rw [h_load]
  have h_wfe : (concreteApplyOp conc (.wfeWait c)).1 = conc := by simp [concreteApplyOp]
  rw [h_wfe]
  exact h_tail_bisim

/-- **WS-SM SM2.C-defer D-4.9 (helper)**: UInt64 subtraction by 1 is
the Nat subtraction by 1 when the input is ≥ 1.

Standard fact about UInt64.toNat: for `x : UInt64` with `x.toNat ≥ 1`,
`(x - 1).toNat = x.toNat - 1`.  Above 0, UInt64 subtraction is exact
(no wrap). -/
private theorem uInt64_sub_one_toNat
    (x : UInt64) (h : x.toNat ≥ 1) : (x - 1).toNat = x.toNat - 1 := by
  have h_le : (1 : UInt64) ≤ x := by
    rw [UInt64.le_iff_toNat_le]
    show (1 : UInt64).toNat ≤ x.toNat
    have : (1 : UInt64).toNat = 1 := by decide
    omega
  rw [UInt64.toNat_sub_of_le _ _ h_le]
  show x.toNat - (1 : UInt64).toNat = x.toNat - 1
  have : (1 : UInt64).toNat = 1 := by decide
  rw [this]

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — releaseRead
no-promote)**: under wf + `c ∈ readers` + `readers.length ≥ 2`, the
`releaseRead c` abstract op + `[.fetchSubRead c]` concrete block
preserves the bisim.

The Nodup hypothesis (from wf) ensures `readers.filter (· ≠ c)` has
length `readers.length - 1` (exactly one occurrence of c).  The
`readers.length ≥ 2` ensures the post-filter has length ≥ 1, so
`promoteWaitersIfReadersEmpty` doesn't fire (returns intermediate
unchanged).

**Proof strategy**: derive the structural form of the abstract
post-state directly via `releaseRead_effective_post` + manual
characterization of the promote being a no-op (since filter is
non-empty); then use the Nat arithmetic identity
`conc.toNat - 1 = (writerBitOn + abs.readers.length) - 1 =
writerBitOn + (abs.readers.length - 1) = writerBitOn + filter.length`. -/
theorem blockBisim_releaseRead_no_promote
    (abs : RwLockState) (conc : UInt64)
    (h_sim : rwLockSim abs conc.toNat)
    (h_wf : abs.wf)
    (c : CoreId)
    (h_holder : c ∈ abs.readers)
    (h_readers_size_ge_two : abs.readers.length ≥ 2) :
    blockBisim abs conc (.releaseRead c) [.fetchSubRead c] := by
  unfold blockBisim concreteFoldBlock
  simp only [List.foldl_cons, List.foldl_nil]
  have h_fetch : (concreteApplyOp conc (.fetchSubRead c)).1 = conc - 1 := by
    simp [concreteApplyOp]
  rw [h_fetch]
  have h_readers_nodup : abs.readers.Nodup := h_wf.2.1
  have h_filter_len_eq := filter_ne_length_of_nodup abs.readers h_readers_nodup c h_holder
  have h_readers_len_ge_one : abs.readers.length ≥ 1 := by omega
  -- Characterize the post-state directly using induction-style proof
  -- without going through promoteWaitersIfReadersEmpty's match.
  have h_filter_len_concrete : (abs.readers.filter (· ≠ c)).length = abs.readers.length - 1 := by
    omega
  have h_filter_ne_nil : abs.readers.filter (· ≠ c) ≠ [] := by
    intro h_eq
    have h_len_zero : (abs.readers.filter (· ≠ c)).length = 0 := by rw [h_eq]; simp
    omega
  -- Show the filter is non-empty by exhibiting an element ≠ c.
  -- readers.length ≥ 2 + Nodup ⇒ at least 2 distinct elements; at most one is c, so at least one ≠ c.
  have h_exists_ne_c : ∃ x ∈ abs.readers, x ≠ c := by
    -- If NOT, then ∀ x ∈ readers, x = c.  Combined with Nodup, length ≤ 1.  Contradicts.
    apply Decidable.byContradiction
    intro h_no
    have h_all_c : ∀ x ∈ abs.readers, x = c := by
      intro x hx
      apply Decidable.byContradiction
      intro h_ne
      exact h_no ⟨x, hx, h_ne⟩
    -- Nodup + all_c ⇒ length ≤ 1.  Induction on readers.
    have h_len_le_one : abs.readers.length ≤ 1 := by
      cases h_eq : abs.readers with
      | nil => simp
      | cons head rest =>
        -- head = c (from h_all_c).
        have h_head_eq : head = c := h_all_c head (by rw [h_eq]; exact List.mem_cons_self)
        rw [h_eq] at h_readers_nodup
        rw [List.nodup_cons] at h_readers_nodup
        obtain ⟨h_head_not_in, _⟩ := h_readers_nodup
        -- rest is empty (all rest elements would be c, but head=c ∉ rest).
        cases h_eq_rest : rest with
        | nil => simp
        | cons r1 _ =>
          -- r1 ∈ rest, r1 = c (from h_all_c).
          have h_r1_in : r1 ∈ abs.readers := by rw [h_eq, h_eq_rest]; simp
          have h_r1_eq : r1 = c := h_all_c r1 h_r1_in
          have h_r1_in_rest : r1 ∈ rest := by rw [h_eq_rest]; exact List.mem_cons_self
          -- head = c = r1, so c ∈ rest contradicts h_head_not_in.
          apply absurd h_r1_in_rest
          rw [h_r1_eq, ← h_head_eq]
          exact h_head_not_in
    omega
  -- The abstract applyOp for releaseRead with c ∈ readers AND filter non-empty:
  -- post.readers = filter (· ≠ c), post.writerHeld = abs.writerHeld, post.waiters = abs.waiters.
  have h_filter_isEmpty_false : (abs.readers.filter (· ≠ c)).isEmpty = false := by
    have h_in_filter : ∃ x, x ∈ abs.readers.filter (· ≠ c) := by
      obtain ⟨x, h_x_in, h_x_ne⟩ := h_exists_ne_c
      exact ⟨x, List.mem_filter.mpr ⟨h_x_in, by simp [h_x_ne]⟩⟩
    obtain ⟨x, h_x_in⟩ := h_in_filter
    cases h_e : (abs.readers.filter (· ≠ c)).isEmpty with
    | true =>
      exfalso
      rw [List.isEmpty_iff] at h_e
      rw [h_e] at h_x_in
      exact absurd h_x_in List.not_mem_nil
    | false => rfl
  have h_post_readers : (abs.applyOp (.releaseRead c)).readers = abs.readers.filter (· ≠ c) := by
    unfold RwLockState.applyOp
    have h_not_in_neg : ¬ c ∉ abs.readers := fun h => h h_holder
    simp only [h_not_in_neg, ↓reduceIte]
    unfold RwLockState.promoteWaitersIfReadersEmpty
    simp [h_exists_ne_c]
  have h_post_writer : (abs.applyOp (.releaseRead c)).writerHeld = abs.writerHeld := by
    unfold RwLockState.applyOp
    have h_not_in_neg : ¬ c ∉ abs.readers := fun h => h h_holder
    simp only [h_not_in_neg, ↓reduceIte]
    unfold RwLockState.promoteWaitersIfReadersEmpty
    simp [h_exists_ne_c]
  -- Now reduce the bisim equality.
  unfold rwLockSim at h_sim ⊢
  have h_conc_ge_one : conc.toNat ≥ 1 := by
    rw [h_sim]; exact encodeRwLock_at_least_one_when_reader abs c h_holder
  have h_sub := uInt64_sub_one_toNat conc h_conc_ge_one
  rw [h_sub, h_post_readers, h_post_writer]
  unfold encodeRwLock
  rw [h_filter_len_concrete]
  by_cases h_w : abs.writerHeld.isSome
  · simp only [h_w, ↓reduceIte]
    have h_sim_unfold : conc.toNat = writerBit + abs.readers.length := by
      rw [h_sim]; unfold encodeRwLock; simp [h_w]
    rw [h_sim_unfold]
    rw [Nat.add_sub_assoc h_readers_len_ge_one]
  · simp only [h_w, Bool.false_eq_true, ↓reduceIte]
    have h_sim_unfold : conc.toNat = abs.readers.length := by
      rw [h_sim]; unfold encodeRwLock; simp [h_w]
    -- Goal: conc.toNat - 1 = 0 + (abs.readers.length - 1).
    rw [h_sim_unfold]
    simp

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — releaseRead
no-promote + SEV)**: the SEV-emitted variant adds a state-preserving
`.sev c` op to the end; the rest of the block discharge is identical
to `blockBisim_releaseRead_no_promote`. -/
theorem blockBisim_releaseRead_no_promote_with_sev
    (abs : RwLockState) (conc : UInt64)
    (h_sim : rwLockSim abs conc.toNat)
    (h_wf : abs.wf)
    (c : CoreId)
    (h_holder : c ∈ abs.readers)
    (h_readers_size_ge_two : abs.readers.length ≥ 2) :
    blockBisim abs conc (.releaseRead c) [.fetchSubRead c, .sev c] := by
  -- Equivalent to no-sev: sev is state-preserving.
  have h_base := blockBisim_releaseRead_no_promote abs conc h_sim h_wf c h_holder h_readers_size_ge_two
  unfold blockBisim concreteFoldBlock at h_base ⊢
  simp only [List.foldl_cons, List.foldl_nil] at h_base ⊢
  have h_sev : (concreteApplyOp (concreteApplyOp conc (.fetchSubRead c)).1 (.sev c)).1 =
               (concreteApplyOp conc (.fetchSubRead c)).1 := by
    simp [concreteApplyOp]
  rw [h_sev]
  exact h_base

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — tryWrite_success)**:
when the abstract is in direct-acquire-write shape AND CAS expected = 0
(matching writer-acquire) AND state = 0 at CAS time, the block bisim
holds. -/
theorem blockBisim_tryWrite_success
    (abs : RwLockState) (conc : UInt64)
    (c : CoreId)
    (h_not_inv : ¬ abs.coreInvolved c)
    (h_no_writer : abs.writerHeld = none)
    (h_no_readers : abs.readers = [])
    (h_no_waiters : abs.waiters = [])
    (h_state_zero : conc = 0) :
    blockBisim abs conc (.tryAcquireWrite c) [.load c, .casAcquireWrite c] := by
  unfold blockBisim concreteFoldBlock
  simp only [List.foldl_cons, List.foldl_nil]
  have h_load : (concreteApplyOp conc (.load c)).1 = conc := by simp [concreteApplyOp]
  rw [h_load]
  have h_cas : (concreteApplyOp conc (.casAcquireWrite c)).1 = writerBit.toUInt64 := by
    unfold concreteApplyOp
    simp [h_state_zero]
  rw [h_cas]
  -- Show rwLockSim (abs.applyOp .tryAcquireWrite c) writerBit.toUInt64.toNat
  -- By tryAcquireWrite_direct_acquire_shape, post-state = writerHeld := some c, readers = [].
  -- encodeRwLock true 0 = writerBit.
  -- We need writerBit.toUInt64.toNat = writerBit (Nat).
  unfold rwLockSim
  have h_step := rwLockSim_preserved_by_direct_acquire_write abs c h_not_inv h_no_writer
    h_no_readers h_no_waiters
  -- h_step : encodeRwLock post.writerHeld.isSome post.readers.length = writerBit.
  rw [h_step]
  -- Need: writerBit.toUInt64.toNat = writerBit.
  -- writerBit = 2^63.  UInt64 fits 0..2^64-1, so 2^63.toUInt64.toNat = 2^63 = writerBit. ✓
  show writerBit.toUInt64.toNat = writerBit
  decide

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — releaseWrite
empty-queue)**: under `writerHeld = some c` AND `readers = []`
AND `waiters = []`, the `releaseWrite c` op clears writerHeld and
the queue stays empty.  Concrete `[.fetchAndWrite c]` produces
`state &&& readerMask = 0` (writer bit cleared, readers bit was 0). -/
theorem blockBisim_releaseWrite_no_sev_empty_queue
    (abs : RwLockState) (conc : UInt64)
    (h_sim : rwLockSim abs conc.toNat)
    (c : CoreId)
    (h_writer : abs.writerHeld = some c)
    (h_no_readers : abs.readers = [])
    (h_no_waiters : abs.waiters = []) :
    blockBisim abs conc (.releaseWrite c) [.fetchAndWrite c] := by
  unfold blockBisim concreteFoldBlock
  simp only [List.foldl_cons, List.foldl_nil]
  -- concreteApplyOp .fetchAndWrite: state &&& readerMask.
  have h_fetch_eq : (concreteApplyOp conc (.fetchAndWrite c)).1 = conc &&& readerMask.toUInt64 := by
    simp [concreteApplyOp]
  rw [h_fetch_eq]
  -- abs.applyOp .releaseWrite c with writerHeld = some c:
  -- intermediate: writerHeld = none, readers = [], waiters = [].
  -- promoteWaitersOnWriterRelease: waiters = [] case, returns intermediate.
  have h_post_eq : abs.applyOp (.releaseWrite c) =
      { writerHeld := none, readers := abs.readers, waiters := abs.waiters } := by
    unfold RwLockState.applyOp
    have h_ne_neg : ¬ abs.writerHeld ≠ some c := fun h => h h_writer
    simp only [h_ne_neg, ↓reduceIte]
    unfold RwLockState.promoteWaitersOnWriterRelease
    rw [h_no_waiters]
  rw [h_post_eq]
  -- Now show rwLockSim { writerHeld := none, ... } (conc &&& readerMask).toNat.
  unfold rwLockSim at h_sim ⊢
  unfold encodeRwLock
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  rw [h_no_readers]
  -- From h_sim: conc.toNat = encodeRwLock (some c).isSome [].length = writerBit + 0 = writerBit.
  have h_sim_unfold : conc.toNat = writerBit := by
    rw [h_sim, h_writer]
    unfold encodeRwLock
    rw [h_no_readers]
    simp
  -- writerBit & readerMask = 0 (writerBit has only bit 63 set; readerMask has bits 0..62).
  have h_conc_eq : conc = writerBit.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [h_sim_unfold]
    decide
  rw [h_conc_eq]
  decide

/-- **WS-SM SM2.C-defer D-4.9 (per-block discharge — releaseWrite
empty-queue + SEV)**: SEV-emitted variant. -/
theorem blockBisim_releaseWrite_with_sev_empty_queue
    (abs : RwLockState) (conc : UInt64)
    (h_sim : rwLockSim abs conc.toNat)
    (c : CoreId)
    (h_writer : abs.writerHeld = some c)
    (h_no_readers : abs.readers = [])
    (h_no_waiters : abs.waiters = []) :
    blockBisim abs conc (.releaseWrite c) [.fetchAndWrite c, .sev c] := by
  have h_base := blockBisim_releaseWrite_no_sev_empty_queue abs conc h_sim c h_writer
    h_no_readers h_no_waiters
  unfold blockBisim concreteFoldBlock at h_base ⊢
  simp only [List.foldl_cons, List.foldl_nil] at h_base ⊢
  have h_sev : (concreteApplyOp (concreteApplyOp conc (.fetchAndWrite c)).1 (.sev c)).1 =
               (concreteApplyOp conc (.fetchAndWrite c)).1 := by
    simp [concreteApplyOp]
  rw [h_sev]
  exact h_base

-- ============================================================================
-- WS-RR RR6.15 … RR6.19 — Closing D-4: an honest trace, a promoting release,
-- total discharges, and a main theorem that no longer assumes its conclusion
-- ============================================================================
--
-- What was open, and why each piece exists:
--
-- * `rust_rwLock_refines_lean` above takes `ListBlockBisim` as a hypothesis —
--   the per-block simulation obligation — and concludes the trace-level
--   simulation.  That is the conclusion assumed block by block: an "honest
--   Rust trace satisfies it by construction", as its docstring says, but
--   nothing in the tree said what an honest trace *is*.  RR6.15 says it.
--
-- * `opCorresponds` parameterizes `tryRead_success` by arbitrary CAS
--   operands, so the bare inductive admits `tryRead_success c 999 999` — an
--   abstract direct-acquire whose concrete CAS fails.  The honest predicate
--   pins the operands to the state the block starts in.
--
-- * The four release discharges carry `_no_promote` / `_empty_queue` side
--   conditions, which dodge the only interesting case: the abstract release
--   *promotes*.  RR6.16 extends the block contract with the admission tail
--   and discharges the promoting case over it.
--
-- * `tryWrite_cas_retry` and `tryWrite_park_retry` are named by none of the
--   nine `blockBisim_*` lemmas, so a case analysis over the inductive could
--   not close whatever the trace shape.  RR6.17's coverage theorem is a case
--   analysis over the honest predicate's own constructors, so a shape added
--   later is a missing case rather than a silent gap.

-- ----------------------------------------------------------------------------
-- RR6.16 — the promotion block and its fold
-- ----------------------------------------------------------------------------

/-- **WS-RR RR6.16**: the concrete ops a promoted run of readers
performs as it re-acquires — one `[load, CAS]` pair per admitted core,
each CAS taking the state the previous one left. -/
def casPromoteReaderOps (conc : UInt64) : List CoreId → List ConcreteRwLockOp
  | [] => []
  | c :: rest =>
      [.load c, .casAcquireRead c conc (conc + 1)] ++ casPromoteReaderOps (conc + 1) rest

/-- **WS-RR RR6.16**: the concrete ops that carry out the abstract
promotion, mirroring `promoteWaitersOnWriterRelease`'s three cases —
nothing queued, a writer at the head admitted alone, or a contiguous run
of readers admitted together. -/
def casPromoteOps (conc : UInt64) (waiters : List (CoreId × AccessMode)) :
    List ConcreteRwLockOp :=
  match waiters with
  | [] => []
  | (w, .write) :: _ => [.load w, .casAcquireWrite w]
  | (_, .read) :: _ =>
      casPromoteReaderOps conc ((waiters.takeWhile (fun x => x.2 = .read)).map Prod.fst)

/-- **WS-RR RR6.16**: the packed word after a run of `n` admissions
from `conc`.  Written as a recursion so the no-wrap side condition is
discharged where it is needed rather than assumed in the statement. -/
def casPromotePost (conc : UInt64) : Nat → UInt64
  | 0 => conc
  | n + 1 => casPromotePost (conc + 1) n

theorem concreteFoldBlock_casPromoteReaderOps (conc : UInt64) (cores : List CoreId) :
    concreteFoldBlock conc (casPromoteReaderOps conc cores)
      = casPromotePost conc cores.length := by
  induction cores generalizing conc with
  | nil => rfl
  | cons c rest ih =>
    rw [casPromoteReaderOps, concreteFoldBlock, List.foldl_append]
    have hHead : ([ConcreteRwLockOp.load c, .casAcquireRead c conc (conc + 1)].foldl
        (fun s op => (concreteApplyOp s op).1) conc) = conc + 1 := by
      simp [concreteApplyOp]
    rw [hHead]
    have hTail := ih (conc + 1)
    rw [concreteFoldBlock] at hTail
    rw [hTail]
    rfl

/-- **Helper**: `UInt64` increment is `Nat` increment below the wrap
boundary.  The side condition is stated over `UInt64.size` rather than
its numeral so callers can discharge it from a hypothesis in the same
form — `omega` treats the two as unrelated atoms. -/
private theorem uInt64_add_one_toNat (x : UInt64) (h : x.toNat + 1 < UInt64.size) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add]
  have hOne : (1 : UInt64).toNat = 1 := by decide
  rw [hOne, Nat.mod_eq_of_lt h]

theorem casPromotePost_toNat (conc : UInt64) (n : Nat)
    (h : conc.toNat + n < UInt64.size) :
    (casPromotePost conc n).toNat = conc.toNat + n := by
  induction n generalizing conc with
  | zero => simp [casPromotePost]
  | succ k ih =>
    have hStep : (conc + 1).toNat = conc.toNat + 1 :=
      uInt64_add_one_toNat conc (by omega)
    have hRec : (casPromotePost (conc + 1) k).toNat = (conc + 1).toNat + k :=
      ih (conc + 1) (by rw [hStep]; omega)
    show (casPromotePost (conc + 1) k).toNat = conc.toNat + (k + 1)
    rw [hRec, hStep]
    omega

/-- **WS-RR RR6.16 (the promoting release, discharged)**: from a
quiescent sim-related pair, the promotion block reaches the state the
abstract promotion produces.

This is the case the four pre-existing release discharges exclude with
their `_no_promote` / `_empty_queue` side conditions, and the reason the
composition provably could not close over them: the abstract release
admits the head of the queue and a block that stops at `fetch_sub` /
`fetch_and` has not. -/
theorem casPromoteOps_preserves_rwLockSim
    {abs : RwLockState} {conc : UInt64}
    (hSim : rwLockSim abs conc.toNat)
    (hBound : abs.waiters.length ≤ numCores)
    (hW : abs.writerHeld = none) (hR : abs.readers = []) :
    rwLockSim abs.promoteWaitersOnWriterRelease
      (concreteFoldBlock conc (casPromoteOps conc abs.waiters)).toNat := by
  have hZero : conc = 0 := by
    apply UInt64.toNat_inj.mp
    unfold rwLockSim at hSim
    rw [hSim, hW, hR]
    simp [encodeRwLock]
  cases hQ : abs.waiters with
  | nil =>
    rw [promote_noop_on_empty_waiters abs hQ, ← hQ]
    have hOps : casPromoteOps conc abs.waiters = [] := by rw [hQ]; rfl
    rw [hOps]
    simpa [concreteFoldBlock] using hSim
  | cons hd tl =>
    obtain ⟨c, m⟩ := hd
    cases m with
    | write =>
      rw [← hQ]
      have hPromote : abs.promoteWaitersOnWriterRelease
          = { abs with writerHeld := some c, waiters := tl } := by
        unfold RwLockState.promoteWaitersOnWriterRelease; rw [hQ]
      have hOps : casPromoteOps conc abs.waiters
          = [ConcreteRwLockOp.load c, .casAcquireWrite c] := by rw [hQ]; rfl
      rw [hPromote, hOps]
      have hFold : concreteFoldBlock conc [ConcreteRwLockOp.load c, .casAcquireWrite c]
          = writerBit.toUInt64 := by
        simp [concreteFoldBlock, concreteApplyOp, hZero]
      rw [hFold]
      unfold rwLockSim encodeRwLock
      show (writerBit.toUInt64).toNat = _
      simp only [Option.isSome_some, if_true]
      rw [hR]
      simp only [List.length_nil, Nat.add_zero]
      decide
    | read =>
      rw [← hQ]
      have hPromote : abs.promoteWaitersOnWriterRelease
          = { abs with
                readers := (abs.waiters.takeWhile (fun w => w.2 = .read)).map Prod.fst
                  ++ abs.readers
                waiters := abs.waiters.dropWhile (fun w => w.2 = .read) } := by
        unfold RwLockState.promoteWaitersOnWriterRelease; rw [hQ]
      have hOps : casPromoteOps conc abs.waiters
          = casPromoteReaderOps conc
              ((abs.waiters.takeWhile (fun w => w.2 = .read)).map Prod.fst) := by
        rw [hQ]; rfl
      rw [hPromote, hOps, concreteFoldBlock_casPromoteReaderOps]
      have hSplit : (abs.waiters.takeWhile (fun w => w.2 = .read))
          ++ (abs.waiters.dropWhile (fun w => w.2 = .read)) = abs.waiters :=
        List.takeWhile_append_dropWhile
      have hKle : (abs.waiters.takeWhile (fun w => w.2 = .read)).length
          ≤ abs.waiters.length := by
        have := congrArg List.length hSplit
        simp only [List.length_append] at this
        omega
      have hSizeBound : (numCores : Nat) < UInt64.size := by decide
      have hZeroNat : conc.toNat = 0 := by rw [hZero]; rfl
      rw [casPromotePost_toNat _ _ (by rw [hZeroNat]; simp; omega)]
      unfold rwLockSim encodeRwLock
      rw [hZeroNat, hW, hR]
      simp

/-- **WS-RR RR6.16**: a promotion block is an admission sequence, so it
is the tail `opCorresponds`'s promoting release constructors accept. -/
theorem casPromoteReaderOps_admissionSequence (conc : UInt64) (cores : List CoreId) :
    AdmissionSequence (casPromoteReaderOps conc cores) := by
  induction cores generalizing conc with
  | nil => exact .nil
  | cons c rest ih => exact .reader c conc (conc + 1) _ (ih (conc + 1))

theorem casPromoteOps_admissionSequence (conc : UInt64)
    (waiters : List (CoreId × AccessMode)) :
    AdmissionSequence (casPromoteOps conc waiters) := by
  unfold casPromoteOps
  match waiters with
  | [] => exact .nil
  | (_, .write) :: _ => exact .writer _ [] .nil
  | (_, .read) :: _ => exact casPromoteReaderOps_admissionSequence _ _

-- ----------------------------------------------------------------------------
-- RR6.15 — the honest-trace predicate
-- ----------------------------------------------------------------------------

/-- **WS-RR RR6.15**: an *honest* concrete block for an abstract
operation, indexed on **both** pre-states.

This is the trace-shape predicate D-4 was missing.  `opCorresponds`
alone parameterizes `tryRead_success` by arbitrary `(e n : UInt64)`, so
the bare inductive admits `tryRead_success c 999 999` — an abstract
direct-acquire whose concrete CAS *fails* — and any composition over it
is unsound.  Honesty pins each CAS to the state the block starts in:
a **succeeding** CAS carries `expected = conc` and the `new` the
implementation computes from it, and a **failing** CAS (the contention
retry) is required to actually fail.  Which of the two a block is comes
from the abstract branch, which is why the predicate is indexed on the
abstract state as well.

The blocks also cover the abstract outcomes `opCorresponds`'s original
ten could not express — the no-ops and the enqueues (WS-RR RR6.16) —
and the release blocks carry the promotion (RR6.16), without which the
composition provably cannot close. -/
inductive honestBlock :
    RwLockState → UInt64 → RwLockOp → List ConcreteRwLockOp → Prop where
  /-- A core already involved re-acquiring: the spec no-ops and the
  implementation performs no atomic access. -/
  | acquireRead_noop (abs : RwLockState) (conc : UInt64) (c : CoreId) :
      abs.coreInvolved c → honestBlock abs conc (.tryAcquireRead c) []
  /-- Direct acquire: load, then CAS `conc → conc + 1`.  The operands
  are the state the block starts in, which is what makes the CAS
  succeed — the pinning RR6.15 exists for. -/
  | acquireRead_success (abs : RwLockState) (conc : UInt64) (c : CoreId) :
      ¬ abs.coreInvolved c → abs.writerHeld = none → abs.waiters = [] →
      honestBlock abs conc (.tryAcquireRead c)
        [.load c, .casAcquireRead c conc (conc + 1)]
  /-- Enqueue: the reader parks and the block ends there.  The spec
  appends to `waiters` and no atomic access moves the packed word. -/
  | acquireRead_enqueue (abs : RwLockState) (conc : UInt64) (c : CoreId) :
      ¬ abs.coreInvolved c → (abs.writerHeld.isSome ∨ abs.waiters ≠ []) →
      honestBlock abs conc (.tryAcquireRead c) [.load c, .wfeWait c]
  /-- CAS-retry under contention: the CAS **fails**, which is the
  honest reading of "another core moved the state between the load and
  the CAS".  A failing CAS is a no-op whatever its operands, so the
  block continues with any honest block for the same operation. -/
  | acquireRead_cas_retry (abs : RwLockState) (conc : UInt64) (c : CoreId)
      (e n : UInt64) (tail : List ConcreteRwLockOp) :
      conc ≠ e → honestBlock abs conc (.tryAcquireRead c) tail →
      honestBlock abs conc (.tryAcquireRead c)
        ([.load c, .casAcquireRead c e n] ++ tail)
  /-- Park-retry: load, park, retry. -/
  | acquireRead_park_retry (abs : RwLockState) (conc : UInt64) (c : CoreId)
      (tail : List ConcreteRwLockOp) :
      honestBlock abs conc (.tryAcquireRead c) tail →
      honestBlock abs conc (.tryAcquireRead c) ([.load c, .wfeWait c] ++ tail)
  /-- Spec no-op for a core already involved. -/
  | acquireWrite_noop (abs : RwLockState) (conc : UInt64) (c : CoreId) :
      abs.coreInvolved c → honestBlock abs conc (.tryAcquireWrite c) []
  /-- Direct acquire: load, then CAS from exactly `0`. -/
  | acquireWrite_success (abs : RwLockState) (conc : UInt64) (c : CoreId) :
      ¬ abs.coreInvolved c → abs.writerHeld = none → abs.readers = [] →
      abs.waiters = [] →
      honestBlock abs conc (.tryAcquireWrite c) [.load c, .casAcquireWrite c]
  /-- Enqueue: the writer parks. -/
  | acquireWrite_enqueue (abs : RwLockState) (conc : UInt64) (c : CoreId) :
      ¬ abs.coreInvolved c →
      (abs.writerHeld.isSome ∨ abs.readers ≠ [] ∨ abs.waiters ≠ []) →
      honestBlock abs conc (.tryAcquireWrite c) [.load c, .wfeWait c]
  /-- **WS-RR RR6.17**: the writer CAS-retry, which no `blockBisim_*`
  lemma named.  Honest exactly when the state is not `0`, which is what
  makes the CAS fail. -/
  | acquireWrite_cas_retry (abs : RwLockState) (conc : UInt64) (c : CoreId)
      (tail : List ConcreteRwLockOp) :
      conc ≠ 0 → honestBlock abs conc (.tryAcquireWrite c) tail →
      honestBlock abs conc (.tryAcquireWrite c)
        ([.load c, .casAcquireWrite c] ++ tail)
  /-- **WS-RR RR6.17**: the writer park-retry, likewise. -/
  | acquireWrite_park_retry (abs : RwLockState) (conc : UInt64) (c : CoreId)
      (tail : List ConcreteRwLockOp) :
      honestBlock abs conc (.tryAcquireWrite c) tail →
      honestBlock abs conc (.tryAcquireWrite c) ([.load c, .wfeWait c] ++ tail)
  /-- Releasing a read lock one does not hold: spec no-op. -/
  | releaseRead_noop (abs : RwLockState) (conc : UInt64) (c : CoreId) :
      c ∉ abs.readers → honestBlock abs conc (.releaseRead c) []
  /-- `release_read` leaving holders behind: the count drops and nobody
  is promoted. -/
  | releaseRead_noPromote (abs : RwLockState) (conc : UInt64) (c : CoreId) :
      c ∈ abs.readers →
      (abs.readers.filter (· ≠ c) ≠ [] ∨ abs.writerHeld.isSome) →
      honestBlock abs conc (.releaseRead c) [.fetchSubRead c, .sev c]
  /-- **WS-RR RR6.16**: `release_read` draining the lock, with the
  promotion the spec performs carried in the block. -/
  | releaseRead_promote (abs : RwLockState) (conc : UInt64) (c : CoreId) :
      c ∈ abs.readers → abs.readers.filter (· ≠ c) = [] → abs.writerHeld = none →
      honestBlock abs conc (.releaseRead c)
        ([.fetchSubRead c, .sev c] ++ casPromoteOps (conc - 1) abs.waiters)
  /-- Releasing a write lock one does not hold: spec no-op. -/
  | releaseWrite_noop (abs : RwLockState) (conc : UInt64) (c : CoreId) :
      abs.writerHeld ≠ some c → honestBlock abs conc (.releaseWrite c) []
  /-- **WS-RR RR6.16**: `release_write`, with the promotion carried. -/
  | releaseWrite_effective (abs : RwLockState) (conc : UInt64) (c : CoreId) :
      abs.writerHeld = some c →
      honestBlock abs conc (.releaseWrite c)
        ([.fetchAndWrite c, .sev c]
          ++ casPromoteOps (conc &&& readerMask.toUInt64) abs.waiters)

/-- **WS-RR RR6.17 (coverage)**: every honest block is an admissible
`opCorresponds` block.

A case analysis over `honestBlock`'s own constructors, so the coverage
is derived from the inventory rather than from a hand-kept list: a
shape added to `honestBlock` later is a missing case here, not a silent
gap.  This is what the `tryWrite_cas_retry` / `tryWrite_park_retry`
constructors lacked — nine `blockBisim_*` lemmas named eight of the ten
`opCorresponds` shapes and nothing said the family was complete. -/
theorem honestBlock_opCorresponds
    {abs : RwLockState} {conc : UInt64} {op : RwLockOp}
    {blk : List ConcreteRwLockOp} (h : honestBlock abs conc op blk) :
    opCorresponds op blk := by
  induction h with
  | acquireRead_noop c _ => exact .noop _
  | acquireRead_success c _ _ _ => exact .tryRead_success c _ _
  | acquireRead_enqueue c _ _ => exact .tryRead_enqueue c
  | acquireRead_cas_retry c e n tail _ _ ih => exact .tryRead_cas_retry c e n tail ih
  | acquireRead_park_retry c tail _ ih => exact .tryRead_park_retry c tail ih
  | acquireWrite_noop c _ => exact .noop _
  | acquireWrite_success c _ _ _ _ => exact .tryWrite_success c
  | acquireWrite_enqueue c _ _ => exact .tryWrite_enqueue c
  | acquireWrite_cas_retry c tail _ _ ih => exact .tryWrite_cas_retry c tail ih
  | acquireWrite_park_retry c tail _ ih => exact .tryWrite_park_retry c tail ih
  | releaseRead_noop c _ => exact .noop _
  | releaseRead_noPromote c _ _ => exact .releaseRead_with_sev c
  | releaseRead_promote c _ _ _ =>
      exact .releaseRead_promoting c _ (casPromoteOps_admissionSequence _ _)
  | releaseWrite_noop c _ => exact .noop _
  | releaseWrite_effective c _ =>
      exact .releaseWrite_promoting c _ (casPromoteOps_admissionSequence _ _)

-- ----------------------------------------------------------------------------
-- RR6.16 / RR6.17 — the discharge family, now total over the honest shapes
-- ----------------------------------------------------------------------------

/-- A failing read CAS is a no-op, so a retry prefix leaves the fold
where it started. -/
private theorem concreteFoldBlock_failed_read_cas (conc e n : UInt64) (c : CoreId)
    (h : conc ≠ e) (tail : List ConcreteRwLockOp) :
    concreteFoldBlock conc ([.load c, .casAcquireRead c e n] ++ tail)
      = concreteFoldBlock conc tail := by
  unfold concreteFoldBlock
  rw [List.foldl_append]
  simp [concreteApplyOp, h]

/-- A failing write CAS is a no-op, likewise. -/
private theorem concreteFoldBlock_failed_write_cas (conc : UInt64) (c : CoreId)
    (h : conc ≠ 0) (tail : List ConcreteRwLockOp) :
    concreteFoldBlock conc ([.load c, .casAcquireWrite c] ++ tail)
      = concreteFoldBlock conc tail := by
  unfold concreteFoldBlock
  rw [List.foldl_append]
  simp [concreteApplyOp, h]

/-- A park prefix is a no-op. -/
private theorem concreteFoldBlock_park (conc : UInt64) (c : CoreId)
    (tail : List ConcreteRwLockOp) :
    concreteFoldBlock conc ([.load c, .wfeWait c] ++ tail)
      = concreteFoldBlock conc tail := by
  unfold concreteFoldBlock
  rw [List.foldl_append]
  simp [concreteApplyOp]

/-- **WS-RR RR6.16 / RR6.17 (the discharge family, total)**: every
honest block satisfies the per-block simulation obligation.

An induction over `honestBlock`'s constructors, so the family is total
by construction: the two write-retry shapes that no `blockBisim_*`
lemma named are cases here, and a shape added later is a missing case
rather than a gap.  The promoting release cases are discharged over the
admission tail (RR6.16), which is what the pre-existing
`_no_promote` / `_empty_queue` discharges excluded. -/
theorem honestBlock_blockBisim
    {abs : RwLockState} {conc : UInt64} {op : RwLockOp} {blk : List ConcreteRwLockOp}
    (hSim : rwLockSim abs conc.toNat) (hWfAbs : abs.wf)
    (hHonest : honestBlock abs conc op blk) :
    blockBisim abs conc op blk := by
  have hReadersBound : abs.readers.length ≤ numCores := by
    have := rwLock_bounded_wait_read abs hWfAbs; omega
  have hWaitersBound : abs.waiters.length ≤ numCores := by
    have := rwLock_bounded_wait_read abs hWfAbs; omega
  induction hHonest with
  | acquireRead_noop c hInv =>
    unfold blockBisim
    rw [RwLockState.applyOp_noop_acquireRead hInv]
    simpa [concreteFoldBlock] using hSim
  | acquireRead_success c hNotInv hW hQ =>
    have hShape := tryAcquireRead_direct_acquire_shape abs c hNotInv hW hQ
    have hStateNat : conc.toNat = abs.readers.length := by
      unfold rwLockSim at hSim; rw [hSim, hW]; simp [encodeRwLock]
    have hNoWrap : conc.toNat + 1 < UInt64.size := by
      have : (numCores : Nat) + 1 < UInt64.size := by decide
      omega
    unfold blockBisim rwLockSim
    have hFold : concreteFoldBlock conc
        [ConcreteRwLockOp.load c, .casAcquireRead c conc (conc + 1)] = conc + 1 := by
      simp [concreteFoldBlock, concreteApplyOp]
    rw [hFold, hShape.1, hShape.2.1, hW, uInt64_add_one_toNat _ hNoWrap, hStateNat]
    simp [encodeRwLock]
  | acquireRead_enqueue c hNotInv hBusy =>
    have hPost : abs.applyOp (.tryAcquireRead c)
        = { abs with waiters := abs.waiters ++ [(c, AccessMode.read)] } := by
      unfold RwLockState.applyOp
      simp only [hNotInv, ↓reduceIte]
      have : (abs.writerHeld.isSome = true ∨ abs.waiters ≠ []) := hBusy
      simp [this]
    unfold blockBisim
    rw [hPost]
    have hFold : concreteFoldBlock conc [ConcreteRwLockOp.load c, .wfeWait c] = conc := by
      simp [concreteFoldBlock, concreteApplyOp]
    rw [hFold]
    exact hSim
  | acquireRead_cas_retry c e n tail hNe _ ih =>
    unfold blockBisim at ih ⊢
    rw [concreteFoldBlock_failed_read_cas conc e n c hNe tail]
    exact ih
  | acquireRead_park_retry c tail _ ih =>
    unfold blockBisim at ih ⊢
    rw [concreteFoldBlock_park conc c tail]
    exact ih
  | acquireWrite_noop c hInv =>
    unfold blockBisim
    rw [RwLockState.applyOp_noop_acquireWrite hInv]
    simpa [concreteFoldBlock] using hSim
  | acquireWrite_success c hNotInv hW hR hQ =>
    have hZero : conc = 0 := by
      apply UInt64.toNat_inj.mp
      unfold rwLockSim at hSim
      rw [hSim, hW, hR]; simp [encodeRwLock]
    have hShape := tryAcquireWrite_direct_acquire_shape abs c hNotInv hW hR hQ
    unfold blockBisim rwLockSim
    have hFold : concreteFoldBlock conc
        [ConcreteRwLockOp.load c, .casAcquireWrite c] = writerBit.toUInt64 := by
      simp [concreteFoldBlock, concreteApplyOp, hZero]
    rw [hFold, hShape.1, hShape.2.1, hR]
    simp only [Option.isSome_some, encodeRwLock, if_true, List.length_nil, Nat.add_zero]
    decide
  | acquireWrite_enqueue c hNotInv hBusy =>
    have hPost : abs.applyOp (.tryAcquireWrite c)
        = { abs with waiters := abs.waiters ++ [(c, AccessMode.write)] } := by
      unfold RwLockState.applyOp
      simp only [hNotInv, ↓reduceIte]
      have : (abs.writerHeld.isSome = true ∨ abs.readers ≠ [] ∨ abs.waiters ≠ []) := hBusy
      simp [this]
    unfold blockBisim
    rw [hPost]
    have hFold : concreteFoldBlock conc [ConcreteRwLockOp.load c, .wfeWait c] = conc := by
      simp [concreteFoldBlock, concreteApplyOp]
    rw [hFold]
    exact hSim
  | acquireWrite_cas_retry c tail hNe _ ih =>
    unfold blockBisim at ih ⊢
    rw [concreteFoldBlock_failed_write_cas conc c hNe tail]
    exact ih
  | acquireWrite_park_retry c tail _ ih =>
    unfold blockBisim at ih ⊢
    rw [concreteFoldBlock_park conc c tail]
    exact ih
  | releaseRead_noop c hNotHolder =>
    unfold blockBisim
    rw [RwLockState.applyOp_noop_releaseRead hNotHolder]
    simpa [concreteFoldBlock] using hSim
  | releaseRead_noPromote c hHolder hNoPromote =>
    have hLenStep := filter_ne_length_of_nodup abs.readers hWfAbs.2.1 c hHolder
    have hFilterLen : (abs.readers.filter (· ≠ c)).length = abs.readers.length - 1 := by
      rw [← hLenStep]; omega
    have hPos : 1 ≤ abs.readers.length := by rw [← hLenStep]; omega
    have hPost : abs.applyOp (.releaseRead c)
        = ({ writerHeld := abs.writerHeld, readers := abs.readers.filter (· ≠ c),
             waiters := abs.waiters } : RwLockState) := by
      rw [releaseRead_effective_post abs c hHolder]
      exact promoteWaitersIfReadersEmpty_noop _ hNoPromote
    have hGe : 1 ≤ conc.toNat := by
      unfold rwLockSim at hSim
      rw [hSim]; exact encodeRwLock_at_least_one_when_reader abs c hHolder
    have hFold : concreteFoldBlock conc [ConcreteRwLockOp.fetchSubRead c, .sev c]
        = conc - 1 := by simp [concreteFoldBlock, concreteApplyOp]
    -- Rewrite the post-state's *projections* rather than the state
    -- itself: `rw [hPost]` would leave `{ … }.writerHeld` — a record
    -- projection that is definitionally `abs.writerHeld` but not
    -- syntactically, so `omega` would abstract the two writer-bit terms
    -- to different atoms and fail on an identity.
    have hPostW : (abs.applyOp (.releaseRead c)).writerHeld = abs.writerHeld := by
      rw [hPost]
    have hPostR : (abs.applyOp (.releaseRead c)).readers
        = abs.readers.filter (· ≠ c) := by rw [hPost]
    unfold blockBisim
    rw [hFold]
    unfold rwLockSim at hSim ⊢
    rw [uInt64_sub_one_toNat _ hGe, hSim, hPostW, hPostR, hFilterLen]
    -- Both sides now carry the same writer-bit term.  Generalise it —
    -- `writerBit` is `2 ^ writerBitPos`, which `omega` will not abstract
    -- on its own — leaving `w + n - 1 = w + (n - 1)` under `1 ≤ n`.
    unfold encodeRwLock
    exact Nat.add_sub_assoc hPos _
  | releaseRead_promote c hHolder hFilterNil hW =>
    have hLenStep := filter_ne_length_of_nodup abs.readers hWfAbs.2.1 c hHolder
    have hOne : abs.readers.length = 1 := by
      rw [hFilterNil] at hLenStep; simpa using hLenStep.symm
    have hStateOne : conc.toNat = 1 := by
      unfold rwLockSim at hSim; rw [hSim, hW, hOne]; simp [encodeRwLock]
    have hPost : abs.applyOp (.releaseRead c)
        = ({ writerHeld := abs.writerHeld, readers := [], waiters := abs.waiters }
            : RwLockState).promoteWaitersOnWriterRelease := by
      rw [releaseRead_effective_post abs c hHolder, hFilterNil]
      exact promoteIfReadersEmpty_eq_onWriterRelease _ rfl hW
    have hFold : concreteFoldBlock conc [ConcreteRwLockOp.fetchSubRead c, .sev c]
        = conc - 1 := by simp [concreteFoldBlock, concreteApplyOp]
    unfold blockBisim
    rw [hPost, concreteFoldBlock_append, hFold]
    refine casPromoteOps_preserves_rwLockSim ?_ hWaitersBound hW rfl
    show rwLockSim _ (conc - 1).toNat
    unfold rwLockSim
    rw [uInt64_sub_one_toNat _ (by omega), hStateOne, hW]
    simp [encodeRwLock]
  | releaseWrite_noop c hNotWriter =>
    unfold blockBisim
    rw [RwLockState.applyOp_noop_releaseWrite hNotWriter]
    simpa [concreteFoldBlock] using hSim
  | releaseWrite_effective c hW =>
    have hNoReaders : abs.readers = [] := RwLockState.wf_writerReadersExclusion hWfAbs c hW
    have hSimUnfold : conc.toNat = writerBit := by
      unfold rwLockSim at hSim
      rw [hSim, hW, hNoReaders]
      simp [encodeRwLock]
    have hStateW : conc = writerBit.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [hSimUnfold]
      decide
    have hPost : abs.applyOp (.releaseWrite c)
        = ({ writerHeld := none, readers := abs.readers, waiters := abs.waiters }
            : RwLockState).promoteWaitersOnWriterRelease := by
      unfold RwLockState.applyOp
      have hNe : ¬ (abs.writerHeld ≠ some c) := fun h => h hW
      simp only [hNe, ↓reduceIte]
    have hFold : concreteFoldBlock conc [ConcreteRwLockOp.fetchAndWrite c, .sev c]
        = conc &&& readerMask.toUInt64 := by simp [concreteFoldBlock, concreteApplyOp]
    unfold blockBisim
    rw [hPost, concreteFoldBlock_append, hFold]
    refine casPromoteOps_preserves_rwLockSim ?_ hWaitersBound rfl hNoReaders
    show rwLockSim _ (conc &&& readerMask.toUInt64).toNat
    unfold rwLockSim
    rw [hStateW, hNoReaders]
    have hMask : writerBit.toUInt64 &&& readerMask.toUInt64 = 0 := by decide
    rw [hMask]
    simp [encodeRwLock]

-- ----------------------------------------------------------------------------
-- RR6.18 — the composition, and RR6.19 — the hypothesis retired
-- ----------------------------------------------------------------------------

/-- **WS-RR RR6.15**: an abstract op-list paired with its concrete block
list, every block honest at the state pair it executes in.

This is `ListCorresponds` with the trace shape: `honestBlock_opCorresponds`
shows each block is an admissible `opCorresponds` block, and the
state indices pin the CAS operands the bare inductive left free. -/
inductive ListHonestBlocks :
    RwLockState → UInt64 → List RwLockOp → List (List ConcreteRwLockOp) → Prop where
  | nil (abs : RwLockState) (conc : UInt64) : ListHonestBlocks abs conc [] []
  | cons (abs : RwLockState) (conc : UInt64) (a : RwLockOp) (b : List ConcreteRwLockOp)
      (as : List RwLockOp) (bs : List (List ConcreteRwLockOp)) :
      honestBlock abs conc a b →
      ListHonestBlocks (abs.applyOp a) (concreteFoldBlock conc b) as bs →
      ListHonestBlocks abs conc (a :: as) (b :: bs)

/-- **WS-RR RR6.18 (the composition)**: an honest trace **implies** the
per-block bisimulation obligation.

This is the step that turns the discharge lemmas from a collection into
a proof.  `ListBlockBisim` — the hypothesis `rust_rwLock_refines_lean`
took — is now a *consequence* of the trace's shape rather than something
a caller must supply, which is what WS-RR RR6.19 needs to retire it. -/
theorem listHonestBlocks_listBlockBisim
    {abs : RwLockState} {conc : UInt64}
    {ops : List RwLockOp} {blocks : List (List ConcreteRwLockOp)}
    (hSim : rwLockSim abs conc.toNat) (hWfAbs : abs.wf)
    (hChain : ListHonestBlocks abs conc ops blocks) :
    ListBlockBisim abs conc ops blocks := by
  induction hChain with
  | nil a c => exact .nil a c
  | cons a c op blk restOps restBlocks hBlk _hRest ih =>
    have hStep := honestBlock_blockBisim hSim hWfAbs hBlk
    refine .cons a c op blk restOps restBlocks hStep ?_
    exact ih hStep (RwLockState.applyOp_preserves_wf hWfAbs op)

/-- **WS-RR RR6.18 (coverage of the shape inductive)**: an honest trace
is a corresponding trace.

Together with `listHonestBlocks_listBlockBisim` this is the plan's
`ListCorresponds` + trace shape ⇒ `ListBlockBisim`: honesty is a
*restriction* of the shape inductive, not a replacement for it. -/
theorem listHonestBlocks_listCorresponds
    {abs : RwLockState} {conc : UInt64}
    {ops : List RwLockOp} {blocks : List (List ConcreteRwLockOp)}
    (hChain : ListHonestBlocks abs conc ops blocks) :
    ListCorresponds ops blocks := by
  induction hChain with
  | nil _ _ => exact .nil
  | cons _ _ op blk _ _ hBlk _ ih =>
    exact .cons (honestBlock_opCorresponds hBlk) ih

/-- **WS-RR RR6.19 (the hypothesis retired)**: for an honest trace, the
abstract fold and the concrete fold end sim-related — with **no**
per-block obligation assumed.

`rust_rwLock_refines_lean` above takes `ListBlockBisim` as a hypothesis,
i.e. assumes the simulation block by block and concludes it for the
trace.  Here the only hypotheses are the initial simulation, the
abstract well-formedness, and the trace's *shape*; the per-block
obligation is discharged by `listHonestBlocks_listBlockBisim`.

The assumed form is kept (it is a true statement, and a caller with a
block-by-block obligation from some other source may still use it), but
it is no longer what the refinement rests on, and the SM2.D.7 inventory
registers this one. -/
theorem rust_rwLock_refines_lean_honest
    {initial_abs : RwLockState} {initial_conc : UInt64}
    (h_sim_init : rwLockSim initial_abs initial_conc.toNat)
    (h_wf : initial_abs.wf)
    (abs_ops : List RwLockOp)
    (conc_blocks : List (List ConcreteRwLockOp))
    (h_honest : ListHonestBlocks initial_abs initial_conc abs_ops conc_blocks) :
    rwLockSim
      (abs_ops.foldl RwLockState.applyOp initial_abs)
      (concreteFoldBlock initial_conc conc_blocks.flatten).toNat :=
  rust_rwLock_refines_lean initial_abs initial_conc h_sim_init abs_ops conc_blocks
    (listHonestBlocks_listBlockBisim h_sim_init h_wf h_honest)

/-- **WS-RR RR6.19 (corollary — via `rustImplementsRwLock`)**: the same,
stated through the structural correspondence predicate the plan's §5.4
uses.

The `ListBlockBisim` precondition the previous corollary carried is
gone: `listHonestBlocks_listCorresponds` supplies the `ListCorresponds`
half from the honest trace, and `listHonestBlocks_listBlockBisim`
supplies the simulation half. -/
theorem rust_rwLock_refines_lean_via_rustImplementsRwLock_honest
    {initial_abs : RwLockState} {initial_conc : UInt64}
    (h_sim_init : rwLockSim initial_abs initial_conc.toNat)
    (h_wf : initial_abs.wf)
    (abs_ops : List RwLockOp)
    (conc_ops : List ConcreteRwLockOp)
    (h_honest : ∃ blocks : List (List ConcreteRwLockOp),
        blocks.flatten = conc_ops ∧
        ListHonestBlocks initial_abs initial_conc abs_ops blocks) :
    rustImplementsRwLock conc_ops abs_ops ∧
    rwLockSim
      (abs_ops.foldl RwLockState.applyOp initial_abs)
      (concreteFoldBlock initial_conc conc_ops).toNat := by
  obtain ⟨blocks, hFlatten, hChain⟩ := h_honest
  refine ⟨⟨blocks, hFlatten, listHonestBlocks_listCorresponds hChain⟩, ?_⟩
  rw [← hFlatten]
  exact rust_rwLock_refines_lean_honest h_sim_init h_wf abs_ops blocks hChain

/-- **WS-RR RR6.19 (the end-to-end statement)**: from the
implementations' initial states — `RwLock::new` and
`RwLockState.unheld` — every honest trace ends sim-related.

No hypothesis beyond the trace's shape. -/
theorem rust_rwLock_refines_lean_from_unheld
    (abs_ops : List RwLockOp) (conc_blocks : List (List ConcreteRwLockOp))
    (h_honest : ListHonestBlocks RwLockState.unheld 0 abs_ops conc_blocks) :
    rwLockSim
      (abs_ops.foldl RwLockState.applyOp RwLockState.unheld)
      (concreteFoldBlock 0 conc_blocks.flatten).toNat :=
  rust_rwLock_refines_lean_honest
    (by show (0 : UInt64).toNat = _; exact rwLockSim_unheld)
    RwLockState.unheld_wf abs_ops conc_blocks h_honest

end SeLe4n.Kernel.Concurrency
