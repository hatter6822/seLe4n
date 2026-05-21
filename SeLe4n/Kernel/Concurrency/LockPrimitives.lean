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
   ("Verified Lock Primitives") and the GitBook chapter
   `docs/gitbook/16-verified-lock-primitives.md`.
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

## WS-SM SM2.E.4 — Decision rationale

This module captures the SM2-relevant maintainer decisions and the
SM2 sub-decisions that drove the shape of the lock-primitive proof
surface.  Each decision is a deliberate choice with a rejected
alternative; the rationale is recorded here so future contributors
have one place to look when asking "why did SM2 do it THIS way?".

### D-SM2-1 — Operational (not axiomatic) memory model

SM2.A's `MemoryModel.lean` defines the memory model **operationally**:
a memory trace is a `List MemoryEvent`, well-formedness is a
decidable predicate over the trace, and the synchronization /
happens-before relations are derived inductively from the trace
shape.  The alternative — an axiomatic model declaring the partial-
order properties as built-in `axioms` (the Lean keyword that
introduces an unproven trusted assumption) — was rejected because:

* The axiomatic model would carry ~6 separate `axioms` (one per
  partial-order property, one per LSE-RMW semantics rule, one for
  inner-shareable broadcast), each of which would need a separate
  justification document.  The operational model carries **zero
  `axioms`** — every property is derived from the trace
  well-formedness constraints, with no trusted assumption.
* The axiomatic model would not be decidable for finite traces;
  the operational model's `wellFormed` is decidable and so test
  fixtures can `decide` lock-state invariants at elaboration time.
* The operational model lets the Lean compiler optimise lock-
  primitive expressions (the abstract state is manipulable at
  term level) — useful for the SM2.B/C surface anchors that
  `decide`-evaluate concrete state transitions.

Cost: ~12 sub-tasks of SM2.A to lay down the model; recouped at
SM2.B (TicketLock) and SM2.C (RwLock) where every release-acquire
proof reuses the operational machinery.

### D-SM2-2 — TicketLock AND RwLock (both)

The maintainer decision #11 (RW locks) requires both primitives:

* **TicketLock** provides the FIFO + bounded-wait foundation.  The
  proven FIFO order is what every RwLock writer-starvation-freedom
  argument ultimately reduces to.
* **RwLock** adds reader multiplicity for read-mostly workloads
  (lookup, object-store traversal).

If SM2 had skipped TicketLock, RwLock would have needed to derive
FIFO from scratch.  By proving TicketLock first, RwLock's writer-
starvation proof builds on the existing FIFO machinery.

The rejected alternatives were:
* Skip RwLock entirely.  Rejected because read-mostly contended
  paths would have to be serialised, costing measured ~10x latency
  on cross-core lookup workloads.
* Skip TicketLock and use only RwLock.  Rejected because RwLock's
  bounded-wait theorem would lack a structural FIFO basis;
  the proof would need an ad-hoc argument that doesn't compose.

### D-SM2-3 — 8-conjunct wf for TicketLock (INV-T1..T8)

The plan §3.2.2 specifies seven wf conjuncts (INV-T1..T7).  SM2.B
landed with **eight** — adding INV-T8 (count parity:
`nextTicket = serving + |pending| + heldCount`).  Per the
implement-the-improvement rule, this strengthens the spec to match
the reachable state space exactly.  Without INV-T8 the seven-
invariant form admits a non-reachable "wf but stuck" state with
`held = some _` and `serving = nextTicket`, from which
`applyOp .tryAcquire` cannot exit while preserving wf.  INV-T8
closes the gap.

### D-SM2-4 — 5-conjunct wf for RwLock (INV-R1..R5)

The plan §3.3.2 specifies four wf conjuncts (INV-R1..R4).  SM2.C
landed with **five** — adding INV-R5 (waiter-distinct-from-holders
in the strict form: no waiter core appears in `readers` ∪ `writer`).
Per the implement-the-improvement rule, this closes a reachability
gap: without INV-R5 a state with non-empty waiters and zero
holders is wf but unreachable from `unheld`, and `tryAcquireWrite`
from such a state would produce an INV-R4 violation by acquiring
the lock for a core that also sits in the waiters queue.  INV-R5
makes the spec capture exactly the reachable state space.

### D-SM2-5 — Bit-packed RwLock state

The Rust `RwLock` impl packs `(writer_held, reader_count)` into a
single `AtomicU64`:
```
bit 63 = writer-held; bits 0..62 = reader count
```
This lets the entire state be CAS'd atomically (no need for two
separate atomics + a hazard handshake between them).  The Lean
spec models the abstract state directly (struct with `writerHeld`
and `readers` fields); the bit-packing is a refinement detail
(SM2.C.16).  The encoding/decoding round-trip theorems
(SM2.C.17) prove the bit operations preserve semantic state.

Rejected alternatives:
* Two-atomic state (`writer_held: AtomicBool`, `reader_count:
  AtomicU64`).  Rejected because the atomic CAS becomes a
  double-CAS (or a hazard pointer), increasing both the
  proof complexity and the per-op overhead.
* `AtomicU128` with separate fields.  Rejected because ARMv8-A
  does not have native 128-bit atomics (`STXP`/`LDXP` provide
  exclusive pair access but are pre-LSE), and the FFI bridge
  would have to deal with sub-word atomicity carefully.

### D-SM2-6 — No upgrade/downgrade in v1.0.0

Per decision #2 (plan §4.4), the v1.0.0 RwLock supports only plain
acquire/release.  Upgrades (reader → writer) and downgrades (writer
→ reader) are notoriously bug-prone:
* The upgrade path has a fundamental deadlock vulnerability if
  two cores both hold the read lock and both try to upgrade
  simultaneously — neither can proceed.
* The downgrade path has a memory-ordering subtlety where the
  reader-bit set must happen-before the writer-bit clear
  observably, but the standard Release-store on the writer-bit
  doesn't guarantee this without a paired Acquire-load on the
  reader-bit.

Deferred to a post-1.0 RwLock-x extension.  `applyOp` does not
include upgrade/downgrade.

### D-SM2-7 — Per-step refinement (not full bisimulation) at v1.0.0

SM2's refinement bridges (`TicketLockRefinement.lean`,
`RwLockRefinement.lean`) deliver per-step preservation lemmas plus
an initial-state correspondence.  The composed reachability-closure
form ("every reachable Rust state is φ-related to a reachable Lean
state") is partially landed (RwLock has `rust_rwLock_refines_lean`
via the D-4.x infrastructure; TicketLock retains the per-step form
as the v1.0.0 contract).  Rejected alternatives:

* Full mechanically-checked code generation from Lean to Rust.
  Rejected as research-grade infrastructure with no production
  path for SM2's calendar.  Considered if a critical SM3+ bug
  surfaces a TicketLock correspondence regression.
* No refinement at all (per-PR review only).  Rejected because the
  weak form would not catch silent refactors that change the
  atomic-op selection on the Rust side.  The per-step form gives
  a structural witness against that class of regression.

Documented in
`SeLe4n/Kernel/Concurrency/Locks/Refinement.lean` (SM2.E.5
methodology hub).

### D-SM2-8 — Pool sizes structurally tied to `numCores`

`staticTicketLockPoolSize` and `staticRwLockPoolSize` are defined
as `:= numCores` rather than a hardcoded `4`.  A future multi-
platform port that bumps `PlatformBinding.coreCount` (e.g., an
8-core RPi6 successor) automatically propagates to the lock
pool sizes.  The Rust side has a `const _: ()` assertion pinning
the value to 4 for the v1.0.0 RPi5 target; the cross-language
symmetry script verifies both sides agree.  Audit-pass-6 LOW-11.

### D-SM2-9 — 22-theorem inventory (no aliasing)

The `lockPrimitives` aggregator has 22 substantive entries — every
one of the 22 `identifier` fields resolves to a distinct
`Lean.Name`.  An earlier draft used aliasing (`F-01` pointing at
`ticketLock_release_acquire_pairing` for lack of a named
refinement theorem); this was replaced by implementing the missing
`rust_ticketLock_refines_lean` theorem substantively in
`Locks/TicketLockRefinement.lean` per the
implement-the-improvement rule.  The
`lockPrimitives_identifiers_nodup` theorem now covers all 22
entries (audit-pass-1).
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

    With `rust_ticketLock_refines_lean` named substantively in
    `Locks/TicketLockRefinement.lean` (no aliasing), every entry's
    `Lean.Name` is unique across the whole 22-row inventory. -/
theorem lockPrimitives_identifiers_nodup :
    (lockPrimitives.map (·.identifier)).Nodup := by
  unfold lockPrimitives; decide

/-- **WS-SM SM2.D.7**: descriptions are pair-wise distinct.  Even
    the refinement entries have distinct descriptions; this guards
    against the inventory accidentally listing the same theorem
    twice with the same description. -/
theorem lockPrimitives_descriptions_nodup :
    (lockPrimitives.map (·.description)).Nodup := by
  unfold lockPrimitives; decide

end SeLe4n.Kernel.Concurrency
