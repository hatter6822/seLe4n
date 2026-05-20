<!-- WS-SM SM2.E.2: Verified Lock Primitives GitBook chapter. -->
<!-- Canonical normative source: docs/spec/SELE4N_SPEC.md §10. -->

# 16 — Verified Lock Primitives (WS-SM Phase SM2)

This chapter is the **handbook companion** to the normative spec
section [`docs/spec/SELE4N_SPEC.md` §10](../spec/SELE4N_SPEC.md).
The spec is authoritative for theorem statements, axiom budget, and
hardware-discipline limits; this chapter expands the prose with
worked examples, pointers into the Lean / Rust source, and the
intuition behind each architectural choice.

## Overview

WS-SM Phase SM2 elevates the lock primitives from
*unverified trusted code* (the seL4-mainline approach, where the
C-level spinlock lives in the trusted computing base) to
**first-class verified artefacts**: both `TicketLock` and `RwLock`
have abstract operational specifications in Lean with substantive
correctness theorems, and the Rust implementations refine those
specifications via documented operational simulation bridges.

The verified surface comprises **22 substantive theorems**:

| Category | Count | Theorems |
|----------|------:|----------|
| Abstract memory model (SM2.A) | 4 | M-01..M-04 |
| TicketLock spec (SM2.B) | 6 | T-01..T-06 |
| RwLock spec (SM2.C) | 10 | R-01..R-10 |
| Refinement bridges (SM2.D) | 2 | F-01..F-02 |

The full catalogue with statement summaries is in
[`docs/spec/SELE4N_SPEC.md` §10.1](../spec/SELE4N_SPEC.md);
the typed inventory is `SeLe4n.Kernel.Concurrency.lockPrimitives`
in `SeLe4n/Kernel/Concurrency/LockPrimitives.lean`, with a size
witness `lockPrimitives.length = 22`.

## Why verify the lock primitives?

In a microkernel, the lock primitive is *the* highest-frequency
piece of code: every kernel entry acquires at least one lock,
many syscalls acquire several.  Unverified lock code is a textbook
example of a place where the cost of a bug is concentrated and the
cost of verification is amortised across every kernel object that
uses it.

The seL4 mainline ships unverified C-level spinlocks as part of
its trusted computing base.  This is a deliberate trade-off: their
verification effort goes into the syscall logic above the lock
layer, taking the lock primitive as an assumption.  seLe4n reaches
the opposite trade-off: by verifying the primitives, we reduce
the TCB at the lock-primitive layer to zero unverified code.

The cost is calendar time (~16-22 weeks across the four SM2
sub-phases A → B → C → D).  The benefit accrues to every kernel
path that consumes a lock — and at v1.0.0 that's every syscall.

## Architecture summary

The two verified primitives serve disjoint roles:

| | TicketLock | RwLock |
|-|------------|--------|
| **Used for** | Write-heavy paths, mintage, capability transfer | Lookup-heavy paths: CSpace radix tree, ASID table, scheduler RunQueue snapshot |
| **Concrete state** | 2× `AtomicU64` (next_ticket, serving) | 1× `AtomicU64` (bit-packed: bit 63 = writer, bits 0..62 = reader count) |
| **Acquisition primitive** | LDADDA (LSE) | CAS-retry with WFE backoff |
| **FIFO order** | Yes (by ticket value) | Spec yes, impl no (documented divergence) |
| **Lean spec LoC** | ~1,900 | ~6,600 |
| **Rust impl LoC** | ~500 | ~500 |
| **Substantive theorems** | 6 (T-01..T-06) | 10 (R-01..R-10) |

Kernel paths that need strict FIFO writer admission (a handful of
SchedContext budget update paths) use the SM2.C-defer D-5 queued
variant in `rust/sele4n-hal/src/queued_rw_lock.rs` instead of the
mainline `RwLock`.  Both variants share the same Lean spec; only
the Rust impl differs.

## Module map

The verified surface is organised across nine Lean modules and
three Rust modules:

```
Lean (production-staged via SeLe4n/Platform/Staged.lean):
  SeLe4n/Kernel/Concurrency/
    MemoryModel.lean                 -- SM2.A: abstract memory model
    Locks/
      TicketLock.lean                 -- SM2.B: TicketLock spec
      RwLock.lean                     -- SM2.C: RwLock spec
      TicketLockRefinement.lean       -- SM2.D F-01: refinement bridge
      RwLockRefinement.lean           -- SM2.C.20 F-02: refinement bridge
      Refinement.lean                 -- SM2.E.5: methodology hub
    LockBridge.lean                   -- SM2.D: typed FFI + RAII combinators
    LockPrimitives.lean               -- SM2.D.7: 22-theorem inventory

Rust (in rust/sele4n-hal/src/):
  ticket_lock.rs                      -- SM2.B.16: TicketLock impl
  rw_lock.rs                          -- SM2.C.19: RwLock impl
  lock_bridge.rs                      -- SM2.D: FFI exports + static pools
  queued_rw_lock.rs                   -- SM2.C-defer D-5: queued variant
```

## Memory model — the foundation (SM2.A)

The abstract memory model lives in
`SeLe4n/Kernel/Concurrency/MemoryModel.lean` and captures
*operationally* (no `axiom` declarations) the parts of ARMv8.1-A
LSE atomic semantics the lock proofs depend on:

* **`MemoryOrder`** — five-constructor inductive
  (`.relaxed`, `.acquire`, `.release`, `.acqRel`, `.seqCst`)
  mapping to ARM ARM B2.3.7 release/acquire semantics.
* **`AtomicLocation`** — opaque single-`Nat` ID with three
  concrete helpers (`nextTicketOf`, `servingOf`, `rwLockStateOf`)
  reserving slots per lock instance.
* **`MemoryEvent`** — 6-field structure: which core, which
  location, isWrite, memory-order tag, value, per-core seqNum.
* **`MemoryTrace`** — event list with `wellFormed` predicate
  (events Nodup + per-core Pairwise seqNum monotonicity).
* **`synchronizesWith`** — 9-conjunct relation encoding ARM ARM
  B2.3.7: a Release-store on L synchronises-with the next
  Acquire-load on L that reads the released value.
* **`happensBefore`** — three-constructor inductive: `.seq`
  (per-core sequencing), `.sync` (lifts `synchronizesWith`),
  `.trans` (closure).

The four canonical theorems (`happensBefore_irreflexive`,
`_transitive`, `_antisymmetric`, and the
`happens_before_partial_order` aggregate) prove `happensBefore` is
a partial order on the events of a wellFormed trace.  These four
are the foundation every release-acquire pairing theorem rests on.

**ARM ARM citation map** (full version in
`MemoryModel.lean`'s module docstring,
[SM2.E.3](../spec/SELE4N_SPEC.md#105-arm-arm-citation-map-sm2e3)):

* Ordering and synchronisation surface — B2.3.3 / B2.3.5 / B2.3.7
  / K11.2 / K11.3
* LSE atomic instruction surface — C6.2.116 (`LDADD`), C6.2.50
  (`CAS`), C6.2.103 (`LDCLR`), C6.2.135 (`LDXR`/`LDAXR`),
  C6.2.323 (`STXR`/`STLXR`), C6.2.142 (`LDAR`)
* Memory barriers — C6.2.94 (`DMB`), C6.2.97 (`DSB`), C6.2.183
  (`ISB`)
* Wait-event coordination — B2.10 (local event register),
  C6.2.353 (`WFE`), C6.2.243 (`SEV`), C6.2.244 (`SEVL`)

A single ARM ARM revision (DDI 0487K.a, July 2024) is the
authoritative source for every section above.

## TicketLock — FIFO spinlock with bounded wait (SM2.B)

`SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean` defines the
abstract `TicketLockState`:

```lean
structure TicketLockState where
  nextTicket : Nat                       -- monotone counter
  serving    : Nat                       -- monotone counter
  pending    : List (CoreId × Nat)       -- (core, captured ticket)
  held       : Option (CoreId × Nat)     -- current holder
```

The well-formedness invariant carries **eight conjuncts**
(INV-T1..T8 — improvement over the plan's seven, closing a
reachability gap at INV-T8 *count parity*:
`nextTicket = serving + |pending| + heldCount`).  The six
substantive theorems prove:

* **T-01 `ticketLock_mutex`**: at most one holder; immediate from
  `Option` injection.
* **T-02 `ticketLock_fifo`**: earlier `tryAcquire` calls capture
  strictly smaller tickets.  Foundation for SM3 ladder-acquisition
  lemmas.
* **T-03 `ticketLock_bounded_wait`**: `nextTicket ≤ serving +
  numCores`.  WCRT bound the RwLock writer-starvation freedom
  derives from.
* **T-04 `ticketLock_release_acquire_pairing`**: a release-store
  on `serving` synchronises-with the next acquire-load that
  observes the released value.  Lifts to `happensBefore` via the
  partial order from SM2.A.
* **T-05 `ticketLock_wf_invariant`**: every `applyOp` preserves
  all eight conjuncts.
* **T-06 `ticketLock_reachability`**: every state reachable from
  `unheld` by a finite operation sequence satisfies wf.

The Rust impl (`rust/sele4n-hal/src/ticket_lock.rs`) is
cache-line-aligned (`#[repr(C, align(64))]`) and uses:

* `LDADDA` (ARM ARM C6.2.116) for `next_ticket.fetch_add(1,
  Acquire)` to capture a ticket.
* `LDAR` (ARM ARM C6.2.142) for `serving.load(Acquire)` in the
  WFE spin loop.
* `LDADDL` (ARM ARM C6.2.116) for `serving.fetch_add(1, Release)`
  on release.
* `SEV` (ARM ARM C6.2.243) to wake waiting cores.

## RwLock — reader-writer lock with bit-packed state (SM2.C)

`SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` defines the
abstract `RwLockState`:

```lean
structure RwLockState where
  writerHeld : Option CoreId
  readers    : List CoreId
  waiters    : List (CoreId × AccessMode)
```

The well-formedness invariant carries **five conjuncts**
(INV-R1..R5 — improvement over the plan's four, closing a
reachability gap at INV-R5 *FIFO admission discipline*:
`waiters ≠ [] → writerHeld.isSome ∨ readers ≠ []`).

The ten substantive theorems (R-01..R-10) cover writer-readers
exclusion, reader multiplicity, FIFO admission, bounded wait
(read/write), release-acquire pairing (read/write), wf invariant
preservation, reader batching, and no-writer-starvation.

The Rust impl bit-packs `(writerHeld, readers)` into a single
`AtomicU64`:

* Bit 63 = writer-held flag.
* Bits 0..62 = reader count (max 2^63 readers; far above the
  `numCores ≤ 1024` upper bound on realistic hardware).

Acquisition uses CAS-retry with `WFE` backoff; release uses
`LDADDL` (for reader release) and `LDCLRL` (for writer release —
clears the writer bit while preserving any reader bits, which
under wf must be zero but the impl never silently overwrites).

**Documented FIFO divergence** (the only one in v1.0.0):
the Lean spec's `rwLock_fifo_admission` (R-03) states that
earlier-arriving waiters are admitted before later-arriving
waiters.  The Rust CAS-retry impl satisfies mutex and exclusion
(R-01) but does NOT satisfy FIFO: a thread that CAS-acquires
immediately after a writer release may admit AHEAD of an
earlier-arrived writer parked on WFE.  Kernel paths that require
strict FIFO consume the queued variant in `queued_rw_lock.rs`.

## Refinement bridges (SM2.D F-01, SM2.C.20 F-02)

Each verified lock primitive ships with an **operational
simulation** φ between the abstract Lean state and a Lean-modelled
view of the Rust impl's observable atomic-field shape.

For TicketLock (`Locks/TicketLockRefinement.lean`):

```lean
def ticketLockSim
    (abs : TicketLockState) (conc : TicketLockConcrete) : Prop :=
  conc.nextTicket.toNat = abs.nextTicket ∧
  conc.serving.toNat = abs.serving
```

Per-step preservation theorems
(`ticketLockSim_preserved_by_tryAcquire`, `..._by_release`,
`..._by_observeServing`) prove φ is maintained by every
`applyOp`.  The aggregator `rust_ticketLock_refines_lean` (F-01)
bundles initial-state correspondence and the three per-step
witnesses.

For RwLock (`Locks/RwLockRefinement.lean`), the simulation
relates the bit-packed `AtomicU64` to the abstract state via
`encodeRwLock` / `decodeRwLock` round-trip lemmas; F-02 is the
aggregator, with the FIFO divergence documented in its
docstring.

The methodology is documented in
`Locks/Refinement.lean` (SM2.E.5) as a uniform 6-step recipe
future SM3+ contributors must follow when adding new verified
lock primitives.

## FFI bridge and RAII combinators (SM2.D)

`SeLe4n/Kernel/Concurrency/LockBridge.lean` provides the Lean-side
typed FFI surface:

* **`TicketLockHandle`** / **`RwLockHandle`** — typed handles
  carrying structural bound proofs (`raw.toNat <
  staticTicketLockPoolSize`).
* **`mkTicketLockHandle`** / **`mkRwLockHandle`** — smart
  constructors taking a typed `Fin staticTicketLockPoolSize`.
* **`acquireTicketLock`**, **`releaseTicketLock`**,
  **`acquireReadLock`**, **`releaseReadLock`**, etc. — typed
  FFI wrappers.
* **`withTicketLock`**, **`withReadLock`**, **`withWriteLock`** —
  RAII combinators bracketing a `BaseIO α` action with
  acquire/release.

The Rust side (`rust/sele4n-hal/src/lock_bridge.rs`) exports 16
`#[no_mangle] pub extern "C"` symbols and maintains two static
lock pools (`STATIC_TICKET_LOCK_POOL: [TicketLock; 4]`,
`STATIC_RW_LOCK_POOL: [RwLock; 4]`) sized to
`PlatformBinding.coreCount = 4`.

## Cross-language symmetry

The Lean `lockPrimitives.length = 22` size witness mirrors the
Rust `SM2_THEOREM_COUNT = 22` constant in `lock_bridge.rs`.  The
script `scripts/check_lock_ffi_symmetry.sh` (wired into Tier 0
hygiene) enforces:

1. Every expected FFI symbol is declared on the Lean side
   (`@[extern "ffi_*"]`).
2. Every expected FFI symbol is exported on the Rust side
   (`#[no_mangle] pub extern "C"`).
3. Every expected FFI symbol has a corresponding helper in
   `lock_bridge.rs`.
4. The Lean `lockPrimitives_count` value matches the Rust
   `SM2_THEOREM_COUNT` constant.
5. & 6. Bidirectional orphan detection.

## Axiom budget — zero

All SM2 modules carry **zero `axiom` declarations** and **zero
`sorry`** placeholders.  Hardware semantics enter operationally
through the memory-trace shape; refinement is a structural
per-step bisimulation, not an axiomatic claim.

## Test infrastructure

Six Lean test executables exercise the SM2 surface:

| Executable | Test file | Surface |
|------------|-----------|---------|
| `memory_model_suite` | `tests/MemoryModelSuite.lean` | SM2.A memory model |
| `ticket_lock_suite` | `tests/TicketLockSuite.lean` | SM2.B TicketLock |
| `rw_lock_suite` | `tests/RwLockSuite.lean` | SM2.C RwLock |
| `rw_lock_deferred_suite` | `tests/RwLockDeferredSuite.lean` | SM2.C-defer D-1..D-4 |
| `smp_surface_anchors` | `tests/SmpSurfaceAnchors.lean` | SM2.D.6 inventory |
| `lock_bridge_suite` | `tests/LockBridgeSuite.lean` | SM2.D.3 RAII |

Plus Rust unit tests (`cargo test` in `rust/sele4n-hal/`) and the
Tier-5 cross-language correspondence harness
(`scripts/test_tier5_cross_language.sh`, SM2.C-defer D-6).

## SMP-H4 closure

WS-SM Phase SM2 closes the SMP-H4 audit finding ("lock primitives
unverified") **foundationally** — the primitives exist and are
proven correct.  Their *integration* into kernel paths
(per-object lock fields, the acquisition discipline at syscall
entry, the cross-object acquire-order proofs) happens in SM3 and
consumes the verified artefacts SM2 ships.

## See also

* **Normative spec**: [`docs/spec/SELE4N_SPEC.md` §10](../spec/SELE4N_SPEC.md)
  (theorem catalogue, hardware-discipline limits, axiom budget)
* **Plan record**:
  [`docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](../planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
  (audit/landing record for each sub-phase)
* **Master overview**:
  [`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](../planning/SMP_MULTICORE_COMPLETION_PLAN.md)
  (binding maintainer decisions; v1.0.0 release path)
* **Proof and invariant map**:
  [`docs/gitbook/12-proof-and-invariant-map.md`](12-proof-and-invariant-map.md)
  (full theorem index across all subsystems)
