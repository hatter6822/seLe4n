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

/-!
# WS-SM SM2.D.7 — Lock-primitive theorem inventory

This module aggregates the 22 substantive SM2 theorems (4 memory
model + 6 TicketLock + 10 RwLock + 2 refinement) into a single
typed inventory with a size witness `lockPrimitives.length = 22`.

The inventory serves three purposes:

1. **Documentation closure**: a single point of truth for "what does
   SM2 prove?" — referenceable from `docs/spec/SELE4N_SPEC.md §10`
   and the GitBook chapter 17.
2. **Tier-3 surface anchor** (`scripts/test_tier3_invariant_surface.sh`):
   every theorem in the inventory has its `Lean.Name` recorded; a
   regression that renames or removes a theorem fails the surface
   check.
3. **Cross-language symmetry** (`scripts/check_lock_ffi_symmetry.sh`):
   the Rust-side `SM2_THEOREM_COUNT = 22` constant in
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
4. Update the Rust-side `SM2_THEOREM_COUNT` constant in
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
  | rwLock       -- §3.3 — RwLock spec (10 theorems)
  | refinement   -- §3.4 — Lean ↔ Rust refinement (2 theorems)
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

/-- **WS-SM SM2.D.7**: the inventory of 22 substantive SM2 theorems.

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
  -- RwLock (10) — see `SeLe4n.Kernel.Concurrency.Locks.RwLock`
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
  { description := "RwLock no writer starvation under fair release",
    identifier  := `SeLe4n.Kernel.Concurrency.rwLock_no_writer_starvation,
    category    := .rwLock },
  -- Refinement (2) — see `SeLe4n.Kernel.Concurrency.Locks.TicketLockRefinement`
  -- and `SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement`.  Both
  -- substantive `rust_*_refines_lean` theorems exist as named
  -- structural witnesses; aliasing is intentional and the entries
  -- are distinct (different `Lean.Name`s).
  { description := "TicketLock Rust impl refines Lean spec (operational simulation)",
    identifier  := `SeLe4n.Kernel.Concurrency.rust_ticketLock_refines_lean,
    category    := .refinement },
  { description := "RwLock Rust impl refines Lean spec (with documented FIFO divergence; SM2.C-defer D-4.9)",
    identifier  := `SeLe4n.Kernel.Concurrency.rust_rwLock_refines_lean,
    category    := .refinement }
]

/-- **WS-SM SM2.D.7**: size witness — the inventory contains exactly
    22 substantive SM2 theorems.

    The Rust-side `SM2_THEOREM_COUNT = 22` constant in
    `rust/sele4n-hal/src/lock_bridge.rs` mirrors this value; the
    cross-language symmetry script (`scripts/check_lock_ffi_symmetry.sh`)
    verifies both sides agree. -/
theorem lockPrimitives_count : lockPrimitives.length = 22 := by
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
    portion at 10. -/
theorem lockPrimitives_rwLock_count :
    (lockPrimitives.filter (·.category = .rwLock)).length = 10 := by
  unfold lockPrimitives; decide

/-- **WS-SM SM2.D.7**: count of refinement theorems.  Pins the
    Lean ↔ Rust refinement bridge at 2 (one per lock kind). -/
theorem lockPrimitives_refinement_count :
    (lockPrimitives.filter (·.category = .refinement)).length = 2 := by
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

/-- **WS-SM SM2.D.7**: identifiers are pair-wise distinct.

    Pins the inventory's NoDup property: every theorem entry has a
    unique `Lean.Name`.  Duplicates would mask renames (a theorem
    that's been deleted but still has an entry would pass the
    surface check via the duplicate).

    Audit-pass-1 strengthening: after `rust_ticketLock_refines_lean`
    was added in `Locks/TicketLockRefinement.lean`, every entry's
    `Lean.Name` is unique across the whole 22-row inventory.  The
    NoDup check now covers ALL identifiers (no exemption for the
    refinement category). -/
theorem lockPrimitives_identifiers_nodup :
    (lockPrimitives.map (·.identifier)).Nodup := by
  unfold lockPrimitives; decide

/-- **WS-SM SM2.D.7** (alias): kept for backwards-compat with the
    audit-pass-0 landing.  Equivalent to
    `lockPrimitives_identifiers_nodup` restricted to the substantive
    (non-refinement) entries. -/
theorem lockPrimitives_substantive_identifiers_nodup :
    ((lockPrimitives.filter (·.category ≠ .refinement)).map (·.identifier)).Nodup := by
  unfold lockPrimitives; decide

/-- **WS-SM SM2.D.7**: descriptions are pair-wise distinct.  Even
    the refinement entries have distinct descriptions; this guards
    against the inventory accidentally listing the same theorem
    twice with the same description. -/
theorem lockPrimitives_descriptions_nodup :
    (lockPrimitives.map (·.description)).Nodup := by
  unfold lockPrimitives; decide

end SeLe4n.Kernel.Concurrency
