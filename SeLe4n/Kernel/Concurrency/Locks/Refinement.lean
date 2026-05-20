-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM2.E.5 unified refinement-proof methodology;
-- documentation hub that re-exports the two per-lock refinement bridges
-- and pins the methodology with marker theorems at the module level).

import SeLe4n.Kernel.Concurrency.Locks.TicketLockRefinement
import SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement

/-!
# WS-SM SM2.E.5 — Refinement-proof methodology

This module is the **canonical documentation hub** for the operational
refinement between the Lean lock specs and the Rust HAL implementations.
It does not introduce new theorems beyond two marker witnesses; instead
it cross-references the two per-lock bridges and documents the uniform
methodology a future SM3+ contributor must follow when adding a new
verified lock primitive.

## What "refinement" means in SM2

For each verified lock primitive `L` (currently `TicketLock` and
`RwLock`), SM2 establishes an **operational simulation** φ between:

* the abstract Lean state (a pure value of type `L.State`), and
* the concrete Rust state (the observable view of the impl's atomic
  fields, modelled in Lean as a pure value of type `L.Concrete`).

The simulation φ relates the two sides at every step of the
operation sequence.  Concretely:

    φ : L.State → L.Concrete → Prop

with:

1. **Initial-state correspondence**: φ holds for the canonical
   unheld pair: `φ L.State.unheld L.Concrete.unheld`.
2. **Per-operation preservation**: for every Op constructor `op`,
   φ is preserved by the parallel Lean / Rust step:

       φ s c → φ (s.applyOp op) (c.applyConcrete op)

   where `c.applyConcrete op` is the Lean-level model of the
   atomic-operation effects the Rust impl executes for that op.

## Per-step bisimulation vs full reachability

The v1.0.0 cut establishes the **per-step bisimulation** form: an
inductive invariant on adjacent (Lean, Rust) state pairs.  It does
NOT prove the full reachability-closure form:

    ∀ (lean_ops : List Op),
      φ (foldl applyOp .unheld lean_ops)
        (foldl applyConcrete .unheld lean_ops)

The two forms are related: full reachability closure follows from
per-step preservation by induction on the length of the operation
sequence.  We defer the reachability-closure aggregator past v1.0.0
because:

* Per-step preservation is **sufficient** for every SM3+ consumer.
  SM3 critical sections execute a single atomic operation between
  consecutive Lean-side state observations, so the per-step form
  applies directly without unfolding `foldl`.
* The reachability-closure form would require carrying an extra
  recursion principle through the operation index — pure proof
  infrastructure overhead with no kernel-correctness improvement.
* Full bisimulation between the Rust CAS-retry loop and the
  per-Op transition of the spec requires modelling the bounded
  WFE timeout, which is a liveness concern rather than a
  correctness one (the Lean spec assumes scheduling fairness;
  the Rust impl achieves it via WFE-bounded backoff).

The per-step bisimulation is captured by the `*_preserved_by_*`
theorems in `Locks/TicketLockRefinement.lean` and
`Locks/RwLockRefinement.lean` (plus the SM2.C-defer D-4 extensions
in `RwLockRefinement.lean`).

## Methodology — six structural steps for a new lock primitive

When SM3+ or any post-1.0 work adds a new verified lock primitive,
the refinement bridge follows this uniform shape (worked examples in
`Locks/TicketLockRefinement.lean` and `Locks/RwLockRefinement.lean`):

### Step 1 — Concrete state

Define a `*Concrete` structure mirroring the Rust impl's observable
atomic-state shape.  Use `UInt64` (not `Nat`) for fields that
correspond to `AtomicU64` so the abstract / concrete sides agree
on overflow semantics.

  ```
  structure TicketLockConcrete where
    nextTicket : UInt64
    serving    : UInt64
    deriving Repr, DecidableEq, Inhabited
  ```

### Step 2 — Initial state

Define `*Concrete.unheld` matching the Rust `*::new()` const
constructor — typically all-zeros for atomic-counter locks or
the empty pool for bit-packed locks.

  ```
  def TicketLockConcrete.unheld : TicketLockConcrete :=
    { nextTicket := 0, serving := 0 }
  ```

### Step 3 — Simulation relation φ

Define `*Sim : Abstract → Concrete → Prop` as a small conjunction
relating each abstract field to the corresponding concrete
observation.  Use `.toNat` for the bridge from `UInt64` to `Nat`;
use explicit bit-extraction helpers for bit-packed encodings.

The simulation must be **decidable** so test fixtures can
construct (Lean state, Rust state) pairs and `decide` φ:

  ```
  def ticketLockSim
      (abs : TicketLockState) (conc : TicketLockConcrete) : Prop :=
    conc.nextTicket.toNat = abs.nextTicket ∧
    conc.serving.toNat = abs.serving
  ```

### Step 4 — Initial-state correspondence

Prove `*Sim Abstract.unheld Concrete.unheld`.  This is typically
`rfl` (when both sides agree on field defaults) or `decide` (when
the relation has additional conjuncts).

  ```
  theorem ticketLockSim_unheld :
      ticketLockSim TicketLockState.unheld TicketLockConcrete.unheld := by
    decide
  ```

### Step 5 — Per-operation preservation

For every `Op` constructor, prove

    *Sim s c → *Sim (s.applyOp op) (c.applyConcrete op)

The proof is structural: each Rust atomic operation produces a
concrete-state delta that φ relates to the abstract-state delta
from `applyOp`.  Use `unfold` to expose the field updates on both
sides, then `decide` or `omega` to close the arithmetic goals.

  ```
  theorem ticketLockSim_preserved_by_tryAcquire
      (s : TicketLockState) (c : TicketLockConcrete) (core : CoreId) :
      ticketLockSim s c →
      ticketLockSim (s.applyOp (.tryAcquire core))
                    (c.applyConcrete (.tryAcquire core)) := by
    -- ...field-by-field arithmetic, typically 20-50 LoC per Op...
  ```

### Step 6 — Aggregator F-theorem

Bundle the per-step witnesses into a single aggregator theorem
`rust_*_refines_lean` and add it to the `lockPrimitives` inventory
in `LockPrimitives.lean` under the `.refinement` category.

  ```
  theorem rust_ticketLock_refines_lean :
      (∃ φ : TicketLockState → TicketLockConcrete → Prop,
        φ TicketLockState.unheld TicketLockConcrete.unheld ∧
        ∀ s c op, φ s c → φ (s.applyOp op) (c.applyConcrete op)) := by
    refine ⟨ticketLockSim, ?_, ?_⟩
    · exact ticketLockSim_unheld
    · intro s c op h; cases op <;>
        exact (per-op-preservation theorems)
  ```

## Documented divergences

Not every Rust impl matches its Lean spec at every property.  Where
divergences exist, they MUST be explicitly documented in the
refinement bridge's docstring and acknowledged in the F-theorem's
statement.  Currently exactly **one** divergence is documented:

* **FIFO admission** (RwLock — `Locks/RwLockRefinement.lean` F-02):
  the Lean spec's `rwLock_fifo_admission` theorem states that
  earlier-arriving waiters are admitted before later-arriving
  waiters.  The Rust `rust/sele4n-hal/src/rw_lock.rs` impl uses
  CAS-retry without an explicit waiter queue, so a thread that
  CAS-acquires immediately after a writer release may admit
  AHEAD of an earlier-arrived writer parked on WFE.  The mutex
  and exclusion invariants
  (`rwLock_writer_readers_exclusion`) ARE satisfied; only FIFO
  diverges.  Kernel paths that require strict FIFO writer
  admission (a handful of SchedContext budget update paths at
  SM3 review time) consume the SM2.C-defer D-5 queued variant
  in `queued_rw_lock.rs` instead.

The TicketLock impl satisfies every theorem of its spec —
no divergence.

## Test discipline

Each refinement bridge ships with a Lean test suite that exercises
φ at decidable instances:

* `tests/TicketLockSuite.lean` — surface anchors on
  `ticketLockSim_*` theorems.
* `tests/RwLockSuite.lean` — surface anchors on `rwLockSim_*`
  theorems plus bit-packing round-trip tests.
* `tests/SmpSurfaceAnchors.lean` — top-level surface anchors for
  the F-01 / F-02 aggregator theorems.

The Rust side has unit tests (`cargo test ticket_lock`,
`cargo test rw_lock`) that exercise the impl directly; the
correspondence between Rust unit-test traces and Lean spec
operation sequences is reviewed per-PR but not encoded as a
running test fixture (the Tier-5 cross-language correspondence
script for the RwLock — `scripts/test_tier5_cross_language.sh`
— provides one concrete worked example).

## Reachability

`SeLe4n.Kernel.Concurrency.Locks.Refinement` (this module) is
reachable in the kernel's production import closure via
`SeLe4n/Platform/Staged.lean`.  It imports both per-lock
refinement bridges (`TicketLockRefinement`, `RwLockRefinement`)
transitively so consumers can import this single methodology
module without listing the two bridges separately.
-/

namespace SeLe4n.Kernel.Concurrency

/-- **WS-SM SM2.E.5**: methodology marker — anchors the
    refinement-proof methodology at the type level.

    Any module that follows the six-step methodology described in
    this file's docstring (`Locks/Refinement.lean`) and provides an
    F-theorem in the form expected by `LockPrimitives.lean`'s
    `.refinement` category can be cross-referenced through this
    marker.

    The marker is a `Unit`-typed definition rather than a theorem
    because the methodology itself is documentation, not a logical
    claim.  The marker's job is to prevent the methodology
    documentation from being accidentally deleted: two layered
    gates protect it:

    1. **Tier-3 surface anchor** in
       `scripts/test_tier3_invariant_surface.sh` — every CI run
       does `#check @SeLe4n.Kernel.Concurrency.refinementMethodologyMarker`,
       which fails to elaborate if this declaration is removed.
    2. **Staged-module allowlist** in
       `scripts/staged_module_allowlist.txt` — the module is
       listed there and is reached from `SeLe4n/Platform/Staged.lean`,
       so a removal that doesn't update the allowlist fails the
       Tier-0 production/staged partition gate. -/
def refinementMethodologyMarker : Unit := ()

/-- **WS-SM SM2.E.5**: every refinement bridge currently in the
    SM2 inventory follows the six-step methodology.

    This theorem references both F-theorems
    (`rust_ticketLock_refines_lean`, `rust_rwLock_refines_lean`)
    by name so a single Tier-3 surface anchor on this aggregator
    fails to elaborate if either F-theorem is removed or renamed.

    The two F-theorems have different parameter shapes — F-01 is
    a closed conjunction over `ticketLockSim`, while F-02
    (`rust_rwLock_refines_lean`) takes an initial-state pair and
    a block-bisimulation hypothesis as parameters — so we cannot
    directly conjoin their statements.  Instead, we package them
    as **name references** inside the proof term: if either
    F-theorem is removed, this theorem fails to elaborate at
    `lake build` time, exactly matching the docstring's claim of
    "single anchor scans both refinement bridges from one site". -/
theorem refinementMethodology_covers_sm2_inventory :
    refinementMethodologyMarker = refinementMethodologyMarker := by
  -- Reference F-01 (`rust_ticketLock_refines_lean`) by name.  Lean
  -- infers the full type at elaboration; if the theorem is removed
  -- or renamed, this `let` binding fails to elaborate.
  let _f01 := rust_ticketLock_refines_lean
  -- Reference F-02 (`rust_rwLock_refines_lean`) by name via `@`
  -- syntax (it is parameterised; `@` exposes the full signature
  -- for the elaboration check).
  let _f02 := @rust_rwLock_refines_lean
  rfl

end SeLe4n.Kernel.Concurrency
