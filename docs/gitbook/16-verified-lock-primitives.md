# Verified Lock Primitives (WS-SM Phase SM2)

This chapter is the handbook entry point for SM2 — the verification-quality
elevation that distinguishes seLe4n from seL4. SM2 makes the kernel's lock
primitives **first-class proven artefacts** instead of trusted-but-unverified
C code.

Canonical spec: [`docs/spec/SELE4N_SPEC.md` §10](../spec/SELE4N_SPEC.md). The
chapter below is a handbook mirror, summarising the spec and pointing into
the per-module proof sources where applicable.

## Status

* **SM2.A** (Abstract memory model) — LANDED at v0.31.9.
* **SM2.B** (TicketLock spec + Rust impl) — LANDED post-v0.31.9.
* **SM2.C** (RwLock spec + Rust impl) — LANDED post-v0.31.9 (CAS-based
  v1.0.0 path + queued MCS-RW lock for FIFO-strict paths).
* **SM2.D** (FFI bridge + integration) — LANDED post-v0.31.9.
* **SM2.E** (Documentation + assertion sites) — LANDED at the
  documentation cut after SM2.D (this chapter is the SM2.E.2 artefact).

## What SM2 proves

22 substantive theorems aggregated in
[`SeLe4n/Kernel/Concurrency/LockPrimitives.lean`](../../SeLe4n/Kernel/Concurrency/LockPrimitives.lean)
under `lockPrimitives` with the size witness `lockPrimitives.length = 22`.

| Category | Count | Highlights |
|----------|-------|-----------|
| Memory model | 4 | `happensBefore_irreflexive`, `_transitive`, `_antisymmetric`, `happens_before_partial_order` |
| TicketLock | 6 | `mutex`, `fifo`, `bounded_wait`, `release_acquire_pairing`, `wf_invariant`, `reachability` |
| RwLock | 10 | `writer_readers_exclusion`, `reader_multiplicity`, `fifo_admission`, 2× `bounded_wait_*`, 2× `release_acquire_pairing_*`, `wf_invariant`, `reader_batching`, `no_writer_starvation` |
| Refinement | 2 | `rust_ticketLock_refines_lean` (F-01), `rust_rwLock_refines_lean` (F-02) |

The Rust-side `SM2_THEOREM_COUNT = 22` constant in `lock_bridge.rs` is
cross-checked against the Lean inventory by
`scripts/check_lock_ffi_symmetry.sh` (Tier 0 hygiene).

## Why SM2 matters

seL4 ships with C-level lock primitives that are NOT in its proof surface.
Capability-based isolation, scheduling invariants, and IPC correctness all
rest on the assumption that the C locks work. If a lock bug were to land,
the formal verification would silently lose its meaning.

seLe4n flips this: lock primitives are now Lean specifications, the Rust
impl is a refinement, and every theorem about kernel-state safety
discharges the lock-correctness obligation **mechanically**. The TCB
shrinks; the assurance surface grows.

## Architecture

The four-layer stack:

```
┌──────────────────────────────────────────────────────────────┐
│ SM2.E — Documentation (this chapter, §10, methodology hub)    │
├──────────────────────────────────────────────────────────────┤
│ SM2.D — FFI bridge: typed Lean handles + RAII combinators    │
│         ↕ cross-language symmetry script ↕                   │
│         Rust-side `lock_bridge.rs` static pools + counters   │
├──────────────────────────────────────────────────────────────┤
│ SM2.B — TicketLock spec    │ SM2.C — RwLock spec             │
│   `TicketLock.lean`         │   `RwLock.lean`                 │
│   `TicketLockRefinement.lean` │ `RwLockRefinement.lean`       │
│   `ticket_lock.rs`          │   `rw_lock.rs` (CAS-based)      │
│                             │   `queued_rw_lock.rs` (FIFO)    │
├──────────────────────────────────────────────────────────────┤
│ SM2.A — Abstract memory model (`MemoryModel.lean`)            │
│         ARMv8.1-A LSE operational semantics                  │
│         happens-before partial order                          │
└──────────────────────────────────────────────────────────────┘
```

## SM2.A — Abstract memory model

Source: [`SeLe4n/Kernel/Concurrency/MemoryModel.lean`](../../SeLe4n/Kernel/Concurrency/MemoryModel.lean).

The memory model captures, **operationally**, just enough of the ARMv8.1-A
hardware semantics to make the lock primitives provable:

* `MemoryOrder` — 5-variant enum tagging every atomic op
  (`.relaxed`, `.acquire`, `.release`, `.acqRel`, `.seqCst`).
* `MemoryEvent` — `(core, loc, isWrite, order, value, seqNum)` tuple.
* `MemoryTrace` — `List MemoryEvent` with `wellFormed` decidable predicate
  (Nodup + per-core Pairwise monotonicity).
* `synchronizesWith` — release-store on L → matching acquire-load on L
  (9-conjunct predicate; per ARM ARM B2.3.7).
* `sequencedBefore` — per-core program order on smaller `seqNum`.
* `happensBefore` — inductive transitive closure (3 ctors: `.seq`, `.sync`,
  `.trans`).

The four substantive theorems form the **happens-before partial order**:

```
theorem happens_before_partial_order (t : MemoryTrace) (h_wf : t.wellFormed) :
    (∀ e ∈ t.events, ¬ happensBefore t e e) ∧                          -- irreflexive
    (∀ e₁ e₂ e₃, happensBefore t e₁ e₂ → happensBefore t e₂ e₃ →
        happensBefore t e₁ e₃) ∧                                       -- transitive
    (∀ e₁ e₂, e₁ ∈ t.events → e₂ ∈ t.events → e₁ ≠ e₂ →
        ¬ (happensBefore t e₁ e₂ ∧ happensBefore t e₂ e₁))             -- antisymmetric
```

These three properties are the inductive invariant that drives every SM2.B
(TicketLock) and SM2.C (RwLock) release-acquire pairing proof.

**Axiom budget: zero**. All hardware semantics enter as operational
constraints on the trace shape; no `axiom` declarations.

For the full ARM ARM citation map (which architectural property maps to
which Lean construct), see the SM2.E.3 docstring in `MemoryModel.lean`
under "ARM ARM citation map (SM2.E.3)".

## SM2.B — TicketLock

Source: [`SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean`](../../SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean)
(~1900 LoC including proofs) + [`rust/sele4n-hal/src/ticket_lock.rs`](../../rust/sele4n-hal/src/ticket_lock.rs)
(~540 LoC including tests).

A FIFO spinlock with bounded wait. Abstract state:

```
structure TicketLockState where
  nextTicket : Nat
  serving    : Nat
  pending    : List (CoreId × Nat)
  held       : Option (CoreId × Nat)
```

The well-formedness invariant has **eight** conjuncts (INV-T1..T8). INV-T8
("count parity": `nextTicket = serving + |pending| + heldCount`) is a
spec-strengthening over the plan's 7-invariant form, closing a
reachability gap where the 7-form admits a non-reachable "wf but stuck"
state. See `LockPrimitives.lean` §"Decision rationale" D-SM2-3 for the
counter-example.

The 6 substantive theorems (T-01..T-06):

| # | Theorem | Statement |
|---|---------|-----------|
| T-01 | `ticketLock_mutex` | At most one holder at any time |
| T-02 | `ticketLock_fifo` | Earlier `tryAcquire` → smaller ticket |
| T-03 | `ticketLock_bounded_wait` | `nextTicket ≤ serving + numCores` |
| T-04 | `ticketLock_release_acquire_pairing` | Release-store sync-with acquire-load |
| T-05 | `ticketLock_wf_invariant` | wf preserved by every `applyOp` |
| T-06 | `ticketLock_reachability` | Every reachable state satisfies wf |

The Rust impl uses `LDADDA` (Acquire) for `acquire` and `LDADDL` (Release)
for `release`, with `WFE`/`SEV` for low-power waiting and CAS-based
contention resolution. The refinement bridge (F-01,
`rust_ticketLock_refines_lean`) discharges per-step preservation between
the abstract `TicketLockState` and the Rust two-`AtomicU64` representation.

## SM2.C — RwLock

Source: [`SeLe4n/Kernel/Concurrency/Locks/RwLock.lean`](../../SeLe4n/Kernel/Concurrency/Locks/RwLock.lean)
(~6600 LoC) + [`rust/sele4n-hal/src/rw_lock.rs`](../../rust/sele4n-hal/src/rw_lock.rs)
(CAS-based) + [`rust/sele4n-hal/src/queued_rw_lock.rs`](../../rust/sele4n-hal/src/queued_rw_lock.rs)
(queued MCS-RW for FIFO-strict paths).

A reader-writer lock with FIFO writer admission (in the abstract spec).
Abstract state:

```
structure RwLockState where
  writerHeld : Option CoreId
  readers    : List CoreId
  waiters    : List (CoreId × AccessMode)
```

The well-formedness invariant has **five** conjuncts (INV-R1..R5). INV-R5
("waiter-distinct-from-holders strict form") is a spec-strengthening over
the plan's 4-invariant form, closing the analogous reachability gap that
SM2.B's INV-T8 closes.

The 10 substantive theorems are listed in §10.1 of the spec (R-01..R-10).

### FIFO divergence between spec and CAS-based impl

The Lean spec's `rwLock_fifo_admission` theorem (R-03) states earlier
waiters are admitted before later ones. The **CAS-based** Rust impl
(`rust/sele4n-hal/src/rw_lock.rs`) does NOT satisfy this property — a
thread that just called `acquire_read` on a contended lock may observe the
writer-bit clear and CAS-acquire BEFORE an earlier-arrived writer that is
still parked on `wfe`.

The **mutex** (R-01) and **exclusion** invariants ARE satisfied by the
CAS-based impl. Kernel paths that require strict FIFO writer admission
must instead use the **queued MCS-RW lock** at
[`rust/sele4n-hal/src/queued_rw_lock.rs`](../../rust/sele4n-hal/src/queued_rw_lock.rs),
which provides the stronger ordering via a per-core waiter queue with a
four-state mode-encoded parked machine (closed by the SM2.E Panic-Hang
Remediation cut).

The refinement bridge `rust_rwLock_refines_lean` explicitly documents
this divergence — the abstract Lean spec is **stronger** than the
CAS-based impl on FIFO ordering, and the refinement φ does not claim
FIFO equivalence.

## SM2.D — FFI bridge

Source: [`SeLe4n/Kernel/Concurrency/LockBridge.lean`](../../SeLe4n/Kernel/Concurrency/LockBridge.lean)
+ [`rust/sele4n-hal/src/lock_bridge.rs`](../../rust/sele4n-hal/src/lock_bridge.rs).

SM2.D wires the verified lock primitives into the Lean kernel via:

* **16 `@[extern]` declarations** in `SeLe4n/Platform/FFI.lean` (6
  TicketLock + 10 RwLock operations).
* **Typed handles** (`TicketLockHandle`, `RwLockHandle`) with structural
  bound proofs (`raw.toNat < staticPoolSize`).
* **Smart constructors** taking a `Fin` argument so a well-formed Lean
  caller cannot construct a handle that the FFI's fail-closed bound check
  would reject.
* **RAII combinators** (`withTicketLock`, `withReadLock`, `withWriteLock`)
  that bracket BaseIO actions with acquire/release.
* **Static pools** (`STATIC_TICKET_LOCK_POOL[4]`, `STATIC_RW_LOCK_POOL[4]`,
  one slot per RPi5 core) for SM3+ per-object lock attachment.
* **Per-pool-slot counters** (6 × 4 = 24 Relaxed `AtomicU64`s) for
  SM2.D.8 cross-core test verification.

The cross-language symmetry script
[`scripts/check_lock_ffi_symmetry.sh`](../../scripts/check_lock_ffi_symmetry.sh)
verifies the Lean `@[extern]` declarations, Rust `pub extern "C"` exports,
and the `SM2_THEOREM_COUNT = 22` constant all agree.

## SM2.E — Documentation (the SM2 closure)

SM2.E lands the documentation surface that pins SM2 as a publicly
referenceable contract. Seven sub-tasks:

| Sub | What it lands |
|-----|---------------|
| SM2.E.1 | `docs/spec/SELE4N_SPEC.md §10` "Verified Lock Primitives" |
| SM2.E.2 | This GitBook chapter |
| SM2.E.3 | Expanded ARM ARM citation map in `MemoryModel.lean` |
| SM2.E.4 | Decision rationale block in `LockPrimitives.lean` |
| SM2.E.5 | Refinement-proof methodology hub at `Locks/Refinement.lean` |
| SM2.E.6 | Hardware-discipline limits (in `Refinement.lean` §3 + spec §10.7) |
| SM2.E.7 | CHANGELOG entry |

The methodology hub is the canonical entry for understanding "how do the
two refinement bridges relate to each other, and what do they jointly
prove?". See
[`SeLe4n/Kernel/Concurrency/Locks/Refinement.lean`](../../SeLe4n/Kernel/Concurrency/Locks/Refinement.lean).

## Hardware-discipline limits

The SM2.A operational memory model intentionally captures a **bounded
subset** of ARMv8.1-A hardware behaviour. The §10.7 sub-section of the
spec enumerates what is in scope (acquire/release/seqCst ordering,
per-core program order, synchronizes-with, happens-before, RMW pairing,
IS-domain SEV broadcast) and what is out of scope (page-table walk
ordering, cache coherence protocol details, prefetch effects,
exception-side memory access, DMA, self-modifying code).

A kernel critical section protected by an SM2 lock primitive inherits:

1. **Mutual exclusion** of its protected state (TicketLock / RwLock writer
   or RwLock reader-shared).
2. **Cross-core visibility** of every write performed inside the critical
   section AFTER the release-acquire bracket.
3. **Bounded wait** to acquire (modulo the CAS-RwLock FIFO carve-out).

It does NOT inherit any guarantee about speculative reads outside the
critical section, out-of-order completion of TLB walks, or hardware-error
recovery — these are out-of-scope hardware concerns.

## Decision rationale (highlights)

Full rationale lives in `LockPrimitives.lean` §"Decision rationale".
Highlights:

* **D-SM2-1**: Operational (not axiomatic) memory model — zero axioms,
  decidable wellFormed for test fixtures.
* **D-SM2-2**: Both TicketLock and RwLock — FIFO + read-multiplicity
  composition.
* **D-SM2-3**: 8-conjunct wf for TicketLock — INV-T8 count parity closes
  reachability gap.
* **D-SM2-4**: 5-conjunct wf for RwLock — INV-R5 strict-form closes
  analogous gap.
* **D-SM2-5**: Bit-packed RwLock state — single `AtomicU64` CAS instead of
  two atomics.
* **D-SM2-6**: No upgrade/downgrade at v1.0.0 — deferred to post-1.0
  RwLock-x extension.
* **D-SM2-7**: Per-step refinement (not full bisimulation) for TicketLock;
  reachability-closure form for RwLock.
* **D-SM2-8**: Pool sizes structurally tied to `numCores` for
  multi-platform forward-compat.
* **D-SM2-9**: 22-theorem inventory (no aliasing) — every `identifier`
  resolves to a distinct `Lean.Name`.

## Verification command matrix

```bash
source ~/.elan/env

# Module builds
lake build SeLe4n.Kernel.Concurrency.MemoryModel
lake build SeLe4n.Kernel.Concurrency.Locks.TicketLock
lake build SeLe4n.Kernel.Concurrency.Locks.RwLock
lake build SeLe4n.Kernel.Concurrency.Locks.TicketLockRefinement
lake build SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement
lake build SeLe4n.Kernel.Concurrency.Locks.Refinement
lake build SeLe4n.Kernel.Concurrency.LockBridge
lake build SeLe4n.Kernel.Concurrency.LockPrimitives

# Lean test suites
lake exe memory_model_suite
lake exe ticket_lock_suite
lake exe rw_lock_suite
lake exe lock_bridge_suite
lake exe smp_surface_anchors
lake exe lock_refinement_suite

# Cargo (Rust impl verification)
cargo test -p sele4n-hal --lib ticket_lock
cargo test -p sele4n-hal --lib rw_lock
cargo test -p sele4n-hal --lib queued_rw_lock
cargo test -p sele4n-hal --lib lock_bridge

# Cross-language symmetry
./scripts/check_lock_ffi_symmetry.sh

# Full tier set
./scripts/test_smoke.sh       # Tier 0+1+2
./scripts/test_full.sh        # Tier 0+1+2+3
```

## Verification evidence

| Artifact | Path |
|----------|------|
| Abstract memory model | [`SeLe4n/Kernel/Concurrency/MemoryModel.lean`](../../SeLe4n/Kernel/Concurrency/MemoryModel.lean) |
| TicketLock spec | [`SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean`](../../SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean) |
| TicketLock refinement | [`SeLe4n/Kernel/Concurrency/Locks/TicketLockRefinement.lean`](../../SeLe4n/Kernel/Concurrency/Locks/TicketLockRefinement.lean) |
| RwLock spec | [`SeLe4n/Kernel/Concurrency/Locks/RwLock.lean`](../../SeLe4n/Kernel/Concurrency/Locks/RwLock.lean) |
| RwLock refinement | [`SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean`](../../SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean) |
| SM2.E.5 methodology hub | [`SeLe4n/Kernel/Concurrency/Locks/Refinement.lean`](../../SeLe4n/Kernel/Concurrency/Locks/Refinement.lean) |
| FFI bridge (Lean) | [`SeLe4n/Kernel/Concurrency/LockBridge.lean`](../../SeLe4n/Kernel/Concurrency/LockBridge.lean) |
| 22-theorem aggregator | [`SeLe4n/Kernel/Concurrency/LockPrimitives.lean`](../../SeLe4n/Kernel/Concurrency/LockPrimitives.lean) |
| FFI bridge (Rust) | [`rust/sele4n-hal/src/lock_bridge.rs`](../../rust/sele4n-hal/src/lock_bridge.rs) |
| TicketLock impl (Rust) | [`rust/sele4n-hal/src/ticket_lock.rs`](../../rust/sele4n-hal/src/ticket_lock.rs) |
| RwLock impl (Rust, CAS) | [`rust/sele4n-hal/src/rw_lock.rs`](../../rust/sele4n-hal/src/rw_lock.rs) |
| RwLock impl (Rust, queued MCS) | [`rust/sele4n-hal/src/queued_rw_lock.rs`](../../rust/sele4n-hal/src/queued_rw_lock.rs) |
| Plan | [`docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](../planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md) |

### Related

- [Proof and Invariant Map](12-proof-and-invariant-map.md) — invariant-bundle composition
- [Architecture & Module Map](03-architecture-and-module-map.md) — module overview
- [Path to Real Hardware (Raspberry Pi 5)](10-path-to-real-hardware-mobile-first.md) — hardware-binding context
