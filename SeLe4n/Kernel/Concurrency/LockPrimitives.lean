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

## SM2.E.4 — Decision rationale

The four binding maintainer decisions driving SM2's shape (from the
master overview `SMP_MULTICORE_COMPLETION_PLAN.md` §10) are recorded
here so future contributors can locate the rationale next to the
inventory it produced rather than chasing it through planning docs.

### Decision #1, #10 — per-object fine locks (not Big Kernel Lock)

* **Choice**: each kernel object (TCB, CNode, Endpoint, Notification,
  Reply, SchedContext, VSpaceRoot, Page, plus the global ObjStore /
  Untyped tables) carries a private lock field; cross-object
  operations acquire locks in a `LockKind.level` order defined at
  SM0.I.
* **Alternative rejected**: a single Big Kernel Lock (BKL) covering
  the entire `KernelState` (the seL4-mainline approach).  The BKL
  serialises every syscall through one critical section and caps
  the throughput at single-core levels regardless of how many cores
  the kernel runs on.
* **Rationale**: SMP value proposition is throughput; the BKL voids
  it entirely.  The per-object discipline also matches the
  capability-derivation tree's locality: most syscalls touch a small
  set of objects whose lock-graph closure is bounded.  The
  hierarchy (SM0.I `LockKind` 0..9 levels with strict <) eliminates
  the classical "fine-grained locking → ad-hoc deadlock" failure
  mode by construction.

### Decision #11 — reader-writer locks (not exclusive-only)

* **Choice**: lookup-heavy objects (CSpace radix tree, ASID table,
  scheduler RunQueue snapshot) use the verified `RwLock`; write-
  heavy paths (capability transfer, mintage) use `TicketLock`.
* **Alternative rejected**: exclusive-only locks everywhere (one
  primitive, simpler verification surface).
* **Rationale**: capability lookups dominate by call frequency in
  every real microkernel workload (90%+ of syscalls perform at
  least one capability dereference).  Letting readers parallelise
  is the single highest-leverage performance win available.  The
  cost is a second primitive in the verified inventory (10 RwLock
  theorems instead of 6); the benefit is two orders of magnitude
  scaling on read-heavy workloads.  The documented FIFO divergence
  (`rust_rwLock_refines_lean`'s F-02 caveat) is acceptable because
  the kernel paths that depend on strict FIFO are very few
  (writer-precedence on a few SchedContext budget updates) and
  receive runtime audit (SM2.C-defer D-5's queued variant
  available for those paths).

### Decision #13 — verify the lock primitives themselves

* **Choice**: the primitives (`TicketLock`, `RwLock`) are first-class
  verified artefacts.  Both have abstract operational specs in Lean
  with substantive theorems (mutex, FIFO, bounded wait, release-
  acquire pairing, wf preservation, reader multiplicity, etc.); the
  Rust impls refine the specs via documented operational simulation
  bridges (`TicketLockRefinement.lean` F-01,
  `RwLockRefinement.lean` F-02).
* **Alternative rejected**: assume the lock primitives are correct
  (the seL4 mainline approach — the C-level spinlock is in the
  trusted computing base).
* **Rationale**: this is the **verification-quality elevation** that
  distinguishes seLe4n from seL4.  Lock primitives are notorious for
  subtle bugs at exactly the operations the kernel performs most
  frequently; treating them as unverified trusted code defeats the
  rest of the proof effort.  The cost (16-22 weeks calendar; ~3,500
  LoC of Lean spec + proofs; ~1,500 LoC of Rust impl) is amortised
  across every kernel object that uses a lock — the v1.0.0 kernel
  has ~50 distinct critical sections that all benefit.  The
  alternative would have required moving the BKL into the TCB and
  trusting it, then proving everything else above it; the per-
  primitive verification approach gives a smaller TCB and a more
  composable proof structure.

### Decision #2 (carry-over) — no upgrade/downgrade in v1.0.0

* **Choice**: the v1.0.0 `RwLock` supports only plain
  acquire/release.  Reader → writer upgrades and writer → reader
  downgrades are explicitly not in `RwLockOp`.
* **Alternative rejected**: include upgrade/downgrade as primitive
  operations from day one.
* **Rationale**: RwLock upgrade/downgrade is notoriously bug-prone
  (the "deadlock when two readers upgrade concurrently" class of
  bugs).  The verified spec for upgrade/downgrade would require a
  fairness-with-progress assumption that v1.0.0's bounded-wait
  reasoning does not yet support cleanly.  Deferring to a post-1.0
  RwLock-x extension lets v1.0.0 ship with a smaller verified
  surface; kernel paths that genuinely need upgrade semantics
  release-and-reacquire instead, paying one extra release-acquire
  pair (~25 ns on the RPi5 target) for vastly simpler proofs.

These decisions are **binding** for v1.0.0.  Future deviations
require maintainer-led re-decisioning recorded in errata per the
master overview §10.

## SM2.E.5 — Refinement-proof methodology

The refinement bridges (`TicketLockRefinement.lean` F-01,
`RwLockRefinement.lean` F-02) follow a uniform structure that future
SM3+ extensions and any post-1.0 lock primitive must reproduce.  See
`Locks/Refinement.lean` for the full methodology document with
worked examples; the short form is:

1. **Concrete state**: define a `*Concrete` structure mirroring the
   Rust impl's observable atomic-state shape (e.g.,
   `TicketLockConcrete` carries two `UInt64` counters matching the
   Rust `(next_ticket: AtomicU64, serving: AtomicU64)`).
2. **Initial state**: define `*Concrete.unheld` matching the Rust
   `*::new()` const constructor.
3. **Simulation relation φ**: define `*Sim : Abstract → Concrete →
   Prop` as a small conjunction relating each abstract field to the
   corresponding concrete observation (typically via `.toNat` or
   bit-extraction helpers).
4. **Initial-state correspondence**: prove `*Sim Abstract.unheld
   Concrete.unheld` — trivial via `rfl` or `decide` once both
   sides agree on field defaults.
5. **Per-operation preservation**: for every `Op` constructor,
   prove `*Sim s c → *Sim (applyOp s op) (concreteApply c op)`.
   The proof is structural — each Rust atomic operation produces
   a concrete-state delta that φ relates to the abstract-state
   delta from `applyOp`.
6. **Aggregator**: bundle the four (TicketLock) or five (RwLock)
   per-step witnesses into the F-01/F-02 refinement theorem.

The methodology gives a **per-step bisimulation** (not full
reachability closure).  The trade-off is documented in each
refinement bridge's module header: the per-step form is sufficient
for SM3+ consumers (which only ever execute one atomic operation
between consecutive Lean-side state observations) and is much
cheaper to prove than full reachability.

## SM2.E.6 — Hardware-discipline limits

The lock-primitive theorems are sound under the following
hardware-discipline preconditions.  Violation puts the system
outside the verified envelope; the spec offers no guarantees
about behaviour past these limits.

1. **Single-cluster, inner-shareable domain**.  Both `TicketLock`
   and `RwLock` use `Release`/`Acquire` orderings, which on
   ARMv8.1-A are valid within a single inner-shareable (`ISH`)
   domain.  The RPi5 BCM2712 is single-cluster (one ISH domain
   covering all four cores) so `Concurrency.Types.SharingDomain`
   is `.inner`.  A future multi-cluster port must switch to
   `dsbForSharing .outer` and the corresponding `OS`-variant
   TLBI primitives (SM1.E.2).
2. **No mixed-shareability accesses to the lock state**.  The
   Rust impls declare lock state with default cache attributes
   (Normal Memory, Write-Back, Read/Write-Allocate, ISH).  Any
   page-table mapping that downgrades the cacheability or
   shareability of the lock-memory region invalidates the
   acquire/release semantics (the `Release`-store no longer
   broadcasts to other PEs' caches).
3. **Bounded critical sections (`T_cs`)**.  The bounded-wait
   theorems quantify "within (N-1) × T_cs operations" — they
   assume every holder releases within `T_cs` operations.  Code
   that loops indefinitely under a held lock voids the WCRT
   bound (the safety properties — mutex, FIFO order — still hold;
   liveness does not).
4. **No external preemption of the locking PE**.  ARM hypervisors,
   secure-world traps, and NMI-style interrupts can preempt a
   PE that holds a lock for an unbounded duration.  v1.0.0
   does not run under a hypervisor and does not enter secure
   world at runtime; SError-class interrupts are kept masked
   over critical sections per the kernel's existing IRQ-mask
   policy (`Architecture.exceptionLevel`).
5. **No DMA into lock state**.  The lock-state regions are
   declared `cacheable` and are not exposed in the kernel's
   `iommu`/`smmu` configuration; DMA writes from a device into
   a lock counter would silently corrupt state.  No production
   path can produce this configuration (kernel-only memory is
   not DMA-mapped); a third-party port that DMA-mapped kernel
   memory would void the verified envelope.

These limits are **structural** — they describe configurations the
verified spec is sound for, not behavioural constraints on
correct callers.  Each limit is enforced by a kernel-side gate
(SM0/SM1 type-level pinning of `PlatformBinding.coreCount`,
`PlatformBinding.sharingDomain`; SM1.D cmdline guards) or by the
kernel's exclusive ownership of its memory regions.
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
