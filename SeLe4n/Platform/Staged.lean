-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Sim.Contract
import SeLe4n.Platform.FFI
import SeLe4n.Platform.RPi5.Contract
import SeLe4n.Platform.RPi5.VSpaceBoot
import SeLe4n.Kernel.Architecture.CacheModel
import SeLe4n.Kernel.Architecture.ExceptionModel
import SeLe4n.Kernel.Architecture.TimerModel
-- AN9-C / AN9-A / AN9-B: hardware-binding closure modules
import SeLe4n.Kernel.Architecture.BarrierComposition
import SeLe4n.Kernel.Architecture.TlbCacheComposition
-- AN12-B (Theme 4.4): SMP-latent single-core assumption inventory
import SeLe4n.Kernel.Concurrency.Assumptions
-- WS-SM SM0.C (closes SMP-H3): build-time `@`-references for every
-- `smpLatentInventory` entry's `identifier` and `sourceTheorem` so a
-- renamed underlying symbol fails the build instead of silently
-- leaving a dangling inventory entry.  This is the post-AN12-B
-- "audit-by-source-read" pattern's structural replacement.
import SeLe4n.Kernel.Concurrency.Anchors
-- WS-SM SM0.E/SM0.F/SM0.H/SM0.I: foundational typed-identifier modules
-- pulled into Staged so the SM0 build closure is one unit.  No runtime
-- behavior change at SM0; SM1..SM9 wire these into kernel transitions.
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Concurrency.Locks
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Sgi
-- WS-SM SM1.B.5: typed FFI wrapper for `ffi_current_core_id`.  Pulled
-- into Staged so CI builds the bridge (CoreId-typed wrapper around the
-- Rust per-CPU base) on every push.  Reachability: production import
-- closure runs through here even before per-core scheduler state lands
-- at SM5.
import SeLe4n.Kernel.Concurrency.Runtime
-- WS-SM SM1.C.6: secondary-core kernel-entry placeholder.  Pulled into
-- Staged so CI verifies the `@[export lean_secondary_kernel_main]`
-- attribute keeps emitting a C-callable wrapper that the Rust HAL's
-- `rust_secondary_main` (smp.rs Step 6) resolves at link time.  At
-- SM1.C the body is `pure ()`; SM5 replaces it with the per-core
-- scheduler entry.
import SeLe4n.Kernel.SecondaryEntry
-- WS-SM SM1.E.4: typed `tlbiForSharing` FFI wrapper.  Pulled into
-- Staged so CI builds the typed wrapper around the Rust
-- `ffi_tlbi_for_sharing` dispatcher on every push.  Reachability:
-- staged at SM1.E; SM7 (TLB shootdown) is the first runtime exerciser.
import SeLe4n.Kernel.Architecture.TlbiForSharing
-- WS-SM SM2.A: abstract memory model for verified lock primitives.
-- Pulled into Staged so CI builds the operational ARMv8.1-A LSE memory
-- model (MemoryOrder, MemoryEvent, MemoryTrace, synchronizesWith,
-- happensBefore + partial-order theorems) on every push.  Reachability:
-- staged at SM2.A; SM2.B (TicketLock) and SM2.C (RwLock) are the first
-- runtime exercisers.
import SeLe4n.Kernel.Concurrency.MemoryModel
-- WS-SM SM2.B: abstract TicketLock specification.  Pulled into Staged so
-- CI builds the operational TicketLock spec (TicketLockState, applyOp,
-- promotePending, releaseAndPromote, the 8-conjunct wf invariant, plus
-- the substantive theorems mutex / FIFO / bounded-wait / RA-pairing /
-- reachability / determinism / wf-preservation closure-form) on every
-- push.  Reachability: staged at SM2.B; SM3 per-object lock proofs are
-- the first runtime exercisers.
import SeLe4n.Kernel.Concurrency.Locks.TicketLock
-- WS-SM SM2.C: abstract RwLock specification.  Pulled into Staged so CI
-- builds the operational RwLock spec (RwLockState, AccessMode, RwLockOp,
-- applyOp, promoteWaitersOnWriterRelease, promoteWaitersIfReadersEmpty,
-- the 5-conjunct wf invariant, plus the substantive theorems writer-
-- readers-exclusion / reader-multiplicity / FIFO admission / bounded-
-- wait / RA-pairing / reader-batching / no-writer-starvation / wf-
-- preservation / determinism / closure-form / bit-packed encoding).
-- Reachability: staged at SM2.C; SM3 per-object lock proofs are the
-- first runtime exercisers.
import SeLe4n.Kernel.Concurrency.Locks.RwLock
-- WS-SM SM2.C.20: RwLock refinement bridge between the Lean abstract
-- state and the Rust bit-packed AtomicU64 representation.  Documents
-- the FIFO divergence and exports the simulation φ (`rwLockSim`).
import SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement
-- WS-SM SM2.D: typed lock FFI wrappers + RAII combinators.  Wraps the
-- raw `Platform.FFI.ffi*` lock declarations into typed Lean APIs
-- (`TicketLockHandle`, `RwLockHandle`, `withTicketLock`, `withReadLock`,
-- `withWriteLock`).  Reachability: staged at SM2.D; SM3+ per-object
-- locks are the first runtime exercisers.
import SeLe4n.Kernel.Concurrency.LockBridge
-- WS-SM SM2.D.7: lock-primitive theorem inventory.  Aggregates the
-- 22 substantive SM2 theorems (4 memory-model + 6 TicketLock + 10
-- RwLock + 2 refinement) with a `lockPrimitives.length = 22` size
-- witness.  Used by the cross-language symmetry script
-- `scripts/check_lock_ffi_symmetry.sh`.
import SeLe4n.Kernel.Concurrency.LockPrimitives

/-!
# AN7-D.6 (PLT-M07) — Staged-modules build graph

This meta-module pulls seven platform-binding-adjacent modules into the
dependency graph so that `lake build SeLe4n.Platform.Staged` (and, via
`scripts/test_tier1_build.sh`, every CI run) forces each one to compile.
Without this wiring, the seven modules are orphans — they are not reached
from `Main.lean` or from any production kernel chain, so a regression that
breaks them would go undetected until the H3 hardware-binding workstream
reaches them.

The staged modules are:

1. `SeLe4n.Platform.Sim.Contract`              — Sim platform contract
2. `SeLe4n.Platform.FFI`                       — Lean @[extern] FFI declarations
3. `SeLe4n.Platform.RPi5.Contract`             — RPi5 platform contract
4. `SeLe4n.Platform.RPi5.VSpaceBoot`           — AN7-D.2 RPi5 boot VSpaceRoot
5. `SeLe4n.Kernel.Architecture.CacheModel`     — Cache coherency model
6. `SeLe4n.Kernel.Architecture.ExceptionModel` — ARM64 exception model
7. `SeLe4n.Kernel.Architecture.TimerModel`     — ARM generic timer model
8. `SeLe4n.Kernel.Architecture.BarrierComposition` — AN9-C BarrierKind algebra
9. `SeLe4n.Kernel.Architecture.TlbCacheComposition` — AN9-A page-table coherency
10. `SeLe4n.Kernel.Concurrency.Assumptions`    — AN12-B SMP-latent inventory
11. `SeLe4n.Kernel.Concurrency.Anchors`        — WS-SM SM0.C inventory build anchor (SMP-H3)
12. `SeLe4n.Kernel.Concurrency.Types`          — WS-SM SM0.E/SM0.F CoreId + SharingDomain
13. `SeLe4n.Kernel.Concurrency.Locks`          — WS-SM SM0.I BklState
14. `SeLe4n.Kernel.Concurrency.Locks.Kind`     — WS-SM SM0.I LockKind + LockId
15. `SeLe4n.Kernel.Concurrency.Sgi`            — WS-SM SM0.H SgiKind
16. `SeLe4n.Kernel.Concurrency.Runtime`        — WS-SM SM1.B.5 currentCoreId FFI wrapper
17. `SeLe4n.Kernel.SecondaryEntry`             — WS-SM SM1.C.6 secondary-core kernel-entry placeholder
18. `SeLe4n.Kernel.Architecture.TlbiForSharing` — WS-SM SM1.E.4 typed TLBI FFI dispatcher
19. `SeLe4n.Kernel.Concurrency.MemoryModel`     — WS-SM SM2.A abstract memory model
20. `SeLe4n.Kernel.Concurrency.Locks.TicketLock` — WS-SM SM2.B abstract TicketLock spec
21. `SeLe4n.Kernel.Concurrency.Locks.RwLock`    — WS-SM SM2.C abstract RwLock spec
22. `SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement` — WS-SM SM2.C.20 refinement bridge

Per the plan (AN9-J will transition most of these from "SMP-latent" to
"SMP-implemented, runtime-gated by smp_enabled=false at v1.0.0"), the
module remains present as a confirmation inventory rather than a
pending-work surface.  See `docs/spec/SELE4N_SPEC.md` §8.15 for the
activation roadmap.

Every imported module carries its own
`-- STATUS: staged for H3 hardware binding` header comment at the top of
its file (PLT-M07 requirement); this module plus the CI hygiene check
guarantees they all continue to compile.
-/

namespace SeLe4n.Platform.Staged

/-- AN7-D.6 anchor: a dummy definition whose mere presence forces Lean to
    link the seven imported modules into this compilation unit.  `lake
    build SeLe4n.Platform.Staged` will fail loudly if any of those modules
    acquires a broken proof. -/
def stagedBuildAnchor : Unit := ()

end SeLe4n.Platform.Staged
