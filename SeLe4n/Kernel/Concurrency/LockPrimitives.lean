-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM2.D acceptance gate (SM2.D.7 theorem
-- aggregator); referenced by Tier-3 surface scans + cross-language
-- symmetry script.

import SeLe4n.Kernel.Concurrency.MemoryModel
import SeLe4n.Kernel.Concurrency.Locks.TicketLock
import SeLe4n.Kernel.Concurrency.Locks.TicketLockRefinement
import SeLe4n.Kernel.Concurrency.Locks.RwLock
import SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement
import SeLe4n.Kernel.Concurrency.Locks.QueuedRwLockRefinement

/-!
# WS-SM SM2.D.7 — Lock-primitive theorem inventory

This module aggregates the 30 substantive lock-primitive theorems
(4 memory model + 6 TicketLock + 16 RwLock + 4 refinement) into a
single typed inventory with a size witness `lockPrimitives.length = 30`.
The RwLock category was 11 at WS-RR RR6 (inventory 25); WS-LC LC1 added
the withdrawal's three payoff entries (28) and WS-LC LC5 the two
cycle-denominated admission bounds (30).

**WS-RR RR6.9 / RR6.19 / RR6.24 repointed two entries and added three.**

* The R-10 entry pointed at `rwLock_no_writer_starvation`, described as
  "no writer starvation under fair release".  That name is a
  backwards-compatibility alias for
  `rwLock_writer_safety_under_reader_acquire`, a **single-step safety**
  claim — a queued writer is not displaced by one reader acquire —
  mentioning no fairness assumption and no trace.  The catalogue
  therefore advertised liveness and registered safety.  RR6.24 points
  the liveness entry at `rwLock_writer_liveness`, the theorem that
  proves it, and keeps the safety theorem registered under its own
  accurate description.
* The RwLock refinement entry pointed at `rust_rwLock_refines_lean`,
  which takes `ListBlockBisim` — the per-block simulation obligation —
  as a hypothesis, i.e. assumes its own conclusion block by block.
  RR6.19 points it at `rust_rwLock_refines_lean_honest`, whose only
  hypotheses are the initial simulation, well-formedness, and the
  trace's *shape*.
* RR6.9 registers the **deployed** lock's refinement: `lock_bridge.rs`'s
  pool holds `QueuedRwLock` since RR6.10, and
  `queuedRwLock_refines_rwLockSpec` plus
  `queuedRwLock_admits_in_spec_order` are what say that lock satisfies
  the specification — including the FIFO admission the CAS-retry lock
  does not have.

The inventory serves three purposes:

1. **Documentation closure**: a single point of truth for "what does
   SM2 prove?" — referenceable from `docs/spec/SELE4N_SPEC.md §10`
   and the GitBook chapter 17.
2. **Tier-3 surface anchor** (`scripts/test_tier3_invariant_surface.sh`):
   every theorem in the inventory has its `Lean.Name` recorded; a
   regression that renames or removes a theorem fails the surface
   check.
3. **Cross-language symmetry** (`scripts/check_lock_ffi_symmetry.sh`):
   the Rust-side `LOCK_THEOREM_COUNT = 30` constant in
   `lock_bridge.rs` is cross-checked against `lockPrimitives.length`
   in this module.  A regression on either side without updating the
   other fails the symmetry script.

## Structure

Each entry carries a human-readable name (`description`), the
theorem's `Lean.Name` for runtime lookup, and a `category` tag
discriminating memory-model / TicketLock / RwLock / refinement
theorems.

## Adding a new theorem

When SM3+ extends SM2 with a new substantive theorem, the contributor
must:

1. Add the new theorem in its source module (e.g., `RwLock.lean`).
2. Add an entry to `lockPrimitives` below.
3. Update `lockPrimitives_count` to the new length.
4. Update the Rust-side `LOCK_THEOREM_COUNT` constant in
   `rust/sele4n-hal/src/lock_bridge.rs`.
5. Update the `scripts/check_lock_ffi_symmetry.sh` cross-check.

All four steps must happen in the same PR.  The build-script scanner
`scan_lock_bridge_rs_intact` (in `rust/sele4n-hal/build.rs`) and the
Tier-1 cross-language script catch partial updates.
-/

namespace SeLe4n.Kernel.Concurrency

/-- **WS-SM SM2.D.7**: discriminating category for an SM2 theorem. -/
inductive LockPrimitiveCategory where
  | memoryModel  -- §3.1 — operational memory model (4 theorems)
  | ticketLock   -- §3.2 — TicketLock spec (6 theorems)
  | rwLock       -- §3.3 — RwLock spec (11 theorems)
  | refinement   -- §3.4 — Lean ↔ Rust refinement (4 theorems)
  deriving Repr, DecidableEq, Inhabited

/-- **WS-SM SM2.D.7**: a single entry in the lock-primitive
    theorem inventory.

    Carries the theorem's `Lean.Name` for runtime lookup, a
    human-readable description, and a category tag.  The
    `identifier` field can be cross-referenced with
    `Lean.Environment.find?` to confirm the theorem exists at
    elaboration time. -/
structure LockPrimitiveTheorem where
  /-- Human-readable description (used in spec and GitBook). -/
  description : String
  /-- The theorem's `Lean.Name`. -/
  identifier  : Lean.Name
  /-- Category tag. -/
  category    : LockPrimitiveCategory
  deriving Repr, Inhabited

/-- **WS-SM SM2.D.7 / WS-RR RR6 / WS-LC**: the inventory of 30
    substantive lock-primitive theorems.

    The order is canonical: memory model → TicketLock → RwLock →
    refinement.  Each entry maps to a `Lean.Name` that resolves at
    elaboration time (verified by `scripts/test_tier3_invariant_surface.sh`). -/
def lockPrimitives : List LockPrimitiveTheorem := [
  -- Memory model (4) — see `SeLe4n.Kernel.Concurrency.MemoryModel`
  { description := "happens-before is irreflexive on well-formed traces",
    identifier  := `SeLe4n.Kernel.Concurrency.happensBefore_irreflexive,
    category    := .memoryModel },
  { description := "happens-before is transitive (immediate by ctor)",
    identifier  := `SeLe4n.Kernel.Concurrency.happensBefore_transitive,
    category    := .memoryModel },
  { description := "happens-before is antisymmetric on distinct events",
    identifier  := `SeLe4n.Kernel.Concurrency.happensBefore_antisymmetric,
    category    := .memoryModel },
  { description := "happens-before is a partial order (aggregate)",
    identifier  := `SeLe4n.Kernel.Concurrency.happens_before_partial_order,
    category    := .memoryModel },
  -- TicketLock (6) — see `SeLe4n.Kernel.Concurrency.Locks.TicketLock`
  { description := "TicketLock has at most one holder (mutex)",
    identifier  := `SeLe4n.Kernel.Concurrency.ticketLock_mutex,
    category    := .ticketLock },
  { description := "TicketLock FIFO: earlier capture → smaller ticket",
    identifier  := `SeLe4n.Kernel.Concurrency.ticketLock_fifo,
    category    := .ticketLock },
  { description := "TicketLock bounded wait: WCRT ≤ (N-1) × T_cs",
    identifier  := `SeLe4n.Kernel.Concurrency.ticketLock_bounded_wait,
    category    := .ticketLock },
  { description := "TicketLock release-acquire pairing (RA synchronizes-with)",
    identifier  := `SeLe4n.Kernel.Concurrency.ticketLock_release_acquire_pairing,
    category    := .ticketLock },
  { description := "TicketLock wf invariant preserved by every applyOp",
    identifier  := `SeLe4n.Kernel.Concurrency.ticketLock_wf_invariant,
    category    := .ticketLock },
  { description := "TicketLock reachable states satisfy wf",
    identifier  := `SeLe4n.Kernel.Concurrency.ticketLock_reachability,
    category    := .ticketLock },
  -- RwLock (11) — see `SeLe4n.Kernel.Concurrency.Locks.RwLock`
  { description := "RwLock writer-readers exclusion (INV-R1)",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_writer_readers_exclusion,
    category    := .rwLock },
  { description := "RwLock reader multiplicity (∃ state with ≥ 2 readers)",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_reader_multiplicity,
    category    := .rwLock },
  { description := "RwLock FIFO admission: head waiter admitted first",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_fifo_admission,
    category    := .rwLock },
  { description := "RwLock bounded wait for read: WCRT ≤ (N-1) × T_cs",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_bounded_wait_read,
    category    := .rwLock },
  { description := "RwLock bounded wait for write: WCRT ≤ (N-1) × T_cs",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_bounded_wait_write,
    category    := .rwLock },
  { description := "RwLock release-acquire pairing for read",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_release_acquire_pairing_read,
    category    := .rwLock },
  { description := "RwLock release-acquire pairing for write",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_release_acquire_pairing_write,
    category    := .rwLock },
  { description := "RwLock wf invariant preserved by every applyOp",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_wf_invariant,
    category    := .rwLock },
  { description := "RwLock reader batching: contiguous readers acquire together",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_reader_batching,
    category    := .rwLock },
  { description := "RwLock writer liveness: a queued writer that does not withdraw is admitted within depth x (maxDelay+1) LOCK OPERATIONS under FairTrace",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_writer_liveness,
    category    := .rwLock },
  { description := "RwLock writer liveness in CYCLES: the same admission bound denominated by the execution's own per-step cost, under a per-critical-section ceiling",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_writer_admitted_within_cycle_budget,
    category    := .rwLock },
  { description := "RwLock denomination is a refinement: at unit cost the cycle bound is the step bound it was derived from",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_writer_cycle_budget_at_unit_cost,
    category    := .rwLock },
  { description := "RwLock writer safety: one reader acquire does not displace a queued writer",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_writer_safety_under_reader_acquire,
    category    := .rwLock },
  { description := "RwLock withdrawal safety: cancelling a queued request preserves all five INV-R conjuncts",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_cancel_preserves_wf,
    category    := .rwLock },
  { description := "RwLock withdrawal exclusion: a cancel writes neither readers nor writerHeld, so it admits no one",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_cancel_admits_no_one,
    category    := .rwLock },
  { description := "RwLock withdrawal fairness: a cancel never increases another core's wait depth",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_cancel_does_not_increase_wait_depth,
    category    := .rwLock },
  -- Refinement (4) — one per lock kind, plus the deployed lock's FIFO
  -- payoff.  See `Locks.TicketLockRefinement`, `Locks.RwLockRefinement`
  -- and `Locks.QueuedRwLockRefinement`.
  { description := "TicketLock Rust impl refines Lean spec over traces (WS-RR RR6.14)",
    identifier  := `SeLe4n.Kernel.Concurrency.rust_ticketLock_refines_lean,
    category    := .refinement },
  { description := "CAS-retry RwLock refines the Lean spec over honest traces, assuming no per-block obligation (WS-RR RR6.19)",
    identifier  := `SeLe4n.Kernel.Concurrency.rust_rwLock_refines_lean_honest,
    category    := .refinement },
  { description := "Deployed QueuedRwLock refines the Lean spec end to end, queue included (WS-RR RR6.9)",
    identifier  := `SeLe4n.Kernel.Concurrency.queuedRwLock_refines_rwLockSpec,
    category    := .refinement },
  { description := "Deployed QueuedRwLock admits waiters in the spec's queue order (WS-RR RR6.9)",
    identifier  := `SeLe4n.Kernel.Concurrency.queuedRwLock_admits_in_spec_order,
    category    := .refinement }
]

/-- **WS-SM SM2.D.7**: size witness — the inventory contains exactly
    30 substantive lock-primitive theorems.

    The Rust-side `LOCK_THEOREM_COUNT = 30` constant in
    `rust/sele4n-hal/src/lock_bridge.rs` mirrors this value; the
    cross-language symmetry script (`scripts/check_lock_ffi_symmetry.sh`)
    verifies both sides agree. -/
theorem lockPrimitives_count : lockPrimitives.length = 30 := by
  unfold lockPrimitives; decide

/-- **WS-SM SM2.D.7**: count of memory-model theorems.  Pins the
    SM2.A.1..A.12 portion of the inventory at 4. -/
theorem lockPrimitives_memoryModel_count :
    (lockPrimitives.filter (·.category = .memoryModel)).length = 4 := by
  unfold lockPrimitives; decide

/-- **WS-SM SM2.D.7**: count of TicketLock theorems.  Pins the SM2.B
    portion at 6. -/
theorem lockPrimitives_ticketLock_count :
    (lockPrimitives.filter (·.category = .ticketLock)).length = 6 := by
  unfold lockPrimitives; decide

/-- **WS-SM SM2.D.7**: count of RwLock theorems.  Pins the SM2.C
    portion at 16 — ten originally, plus the writer-safety theorem the
    liveness entry used to stand in for (WS-RR RR6.24), plus the three
    withdrawal theorems (WS-LC LC1): safety, exclusion, and fairness to
    the waiters behind the core that gives up; plus the two denomination
    theorems (WS-LC LC5): the admission bound in cycles, and its collapse
    back to the step bound at unit cost. -/
theorem lockPrimitives_rwLock_count :
    (lockPrimitives.filter (·.category = .rwLock)).length = 16 := by
  unfold lockPrimitives; decide

/-- **WS-SM SM2.D.7**: count of refinement theorems.  Pins the
    Lean ↔ Rust refinement bridge at 4: one per lock kind
    (TicketLock, CAS-retry RwLock, deployed QueuedRwLock) plus the
    deployed lock's FIFO-admission payoff (WS-RR RR6.9). -/
theorem lockPrimitives_refinement_count :
    (lockPrimitives.filter (·.category = .refinement)).length = 4 := by
  unfold lockPrimitives; decide

/-- **WS-SM SM2.D.7**: the four category counts sum to the total.
    Structural cross-check that no theorem was orphaned (without a
    category) or double-counted. -/
theorem lockPrimitives_partition_sum :
    (lockPrimitives.filter (·.category = .memoryModel)).length +
    (lockPrimitives.filter (·.category = .ticketLock)).length +
    (lockPrimitives.filter (·.category = .rwLock)).length +
    (lockPrimitives.filter (·.category = .refinement)).length =
      lockPrimitives.length := by
  decide

set_option maxRecDepth 4096 in
/-- **WS-SM SM2.D.7**: identifiers are pair-wise distinct.

    Pins the inventory's NoDup property: every theorem entry has a
    unique `Lean.Name`.  Duplicates would mask renames (a theorem
    that's been deleted but still has an entry would pass the
    surface check via the duplicate).

    With `rust_ticketLock_refines_lean` named substantively in
    `Locks/TicketLockRefinement.lean` (no aliasing), every entry's
    `Lean.Name` is unique across the whole 22-row inventory. -/
theorem lockPrimitives_identifiers_nodup :
    (lockPrimitives.map (·.identifier)).Nodup := by
  unfold lockPrimitives; decide

set_option maxRecDepth 4096 in
/-- **WS-SM SM2.D.7**: descriptions are pair-wise distinct.  Even
    the refinement entries have distinct descriptions; this guards
    against the inventory accidentally listing the same theorem
    twice with the same description. -/
theorem lockPrimitives_descriptions_nodup :
    (lockPrimitives.map (·.description)).Nodup := by
  unfold lockPrimitives; decide

end SeLe4n.Kernel.Concurrency
