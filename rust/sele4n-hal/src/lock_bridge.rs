// SPDX-License-Identifier: GPL-3.0-or-later
//! Lock-bridge — Static lock pools + FFI helpers for SM2.D.
//!
//! **WS-SM SM2.D** (FFI bridge + integration): bridges the verified Lean lock
//! specifications (`SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean` and
//! `RwLock.lean`) and the Rust implementations (`ticket_lock.rs`,
//! `queued_rw_lock.rs`) into a stable C-callable surface that the Lean kernel
//! can consume via `@[extern]` declarations.
//!
//! ## Which reader-writer lock this pool holds (WS-RR RR6.10)
//!
//! `STATIC_RW_LOCK_POOL` holds [`QueuedRwLock`](crate::queued_rw_lock::QueuedRwLock),
//! the **ticket FIFO** lock — not `rw_lock::RwLock`, the CAS-retry one it
//! held through v0.34.48.
//!
//! The Lean specification this pool is claimed to satisfy was tightened to
//! strict FIFO admission at SM2.C-defer D-3, and the CAS-retry lock does not
//! satisfy it: a reader that arrives while a writer is queued can be admitted
//! ahead of that writer, because there is no queue in the concrete state to
//! order them.  `rwLockSim`, the CAS-retry lock's simulation relation, says
//! so in as many words — the abstract `waiters` field is **not represented**.
//! So the deployed lock was not the lock the spec described.
//!
//! `QueuedRwLock` is.  Its refinement —
//! `SeLe4n/Kernel/Concurrency/Locks/QueuedRwLockRefinement.lean` — relates
//! the abstract `waiters` queue to the half-open ticket interval
//! `[now_serving, next_ticket)`, in order, so FIFO admission is a theorem
//! (`queuedRwLock_admits_in_spec_order`) rather than a documented
//! divergence.  It was proved before this switch, so no version ships a
//! deployed lock with no refinement to its own specification.
//!
//! `rw_lock::RwLock` is **retained** (WS-RR RR6.11): it is the second
//! implementation the Tier-5 oracle checks the ticket lock against
//! (`src/bin/rw_lock_oracle.rs` drives both and fails on any disagreement),
//! and its own D-4 refinement is completed rather than deleted.  Two
//! independent algorithms refining one specification and agreeing word for
//! word on every generated trace is worth more than one algorithm agreeing
//! with itself.
//!
//! ## The `core_id` the queued entry points take
//!
//! `QueuedRwLock`'s entry points take the executing PE's id; the FFI's
//! `u64` handle carries none, and adding one would let a caller name a PE it
//! is not running on.  The bridge therefore reads it from the hardware —
//! `per_cpu::current_core_id_from_tpidr()`, whose documented range invariant
//! is `core_id < PlatformBinding.coreCount` — which is the same
//! executing-PE discipline the readiness gate requires of `lean_ready`'s
//! argument.  The id **decides**: the lock's withdrawal slot (WS-LC LC3)
//! and its held word (PR #890 review round 2) are indexed by it, so a
//! wrong id would let one PE release another's hold, or turn a real
//! acquisition into the no-op the lock reserves for a holder re-acquiring
//! — which is why it is read from the hardware at the call and never taken
//! from a caller.  On the host every std thread reads the boot core's slot
//! unless a test adopts another PE's identity for it
//! (`per_cpu::HostCoreIdentity`); the cross-thread tests below do, because
//! several threads under one id are one PE issuing overlapping
//! acquisitions, and the first host lane after the held word landed hung
//! in exactly that shape.
//!
//! ## Architecture
//!
//! At SM2.D the Lean kernel does not yet allocate locks dynamically — SM3+
//! per-object locks will introduce that.  For SM2.D we expose a small
//! **static pool** of locks (4 TicketLocks + 4 RwLocks) addressable by
//! a single `u64` **handle** that the FFI carries.  At SM5 the handle
//! encoding will extend to per-object locks via a high-bit discriminator
//! tag; the SM2.D-reserved low values (0..3 for each pool) remain
//! source-compatible.
//!
//! The pool is intentionally small (4 entries per kind) because:
//!
//! * It mirrors `PlatformBinding.coreCount = 4` on RPi5, so cross-core
//!   tests can exercise one lock per core.
//! * Each `TicketLock` / `QueuedRwLock` is `#[repr(C, align(64))]` (one cache
//!   line); 4 instances per pool = 256 bytes total.  Static allocation
//!   keeps the kernel's BSS footprint flat.
//! * Larger pools at SM2.D would imply we expect Lean callers to want
//!   many locks before SM5 lands — which would be premature.
//!
//! ## Handle encoding (SM2.D version)
//!
//! At SM2.D the handle is simply the pool index reinterpreted as `u64`.
//! Valid values: `0..STATIC_*_POOL_SIZE` (= `0..4` at SM2.D).  Every
//! other value is rejected by the decoder — including handles where
//! high bits are non-zero but the low 2 bits happen to lie in 0..3.
//!
//! Concretely the decoder checks `handle < POOL_SIZE`, so high bits
//! MUST be zero today.  A future SM5+ encoding may use the high bits
//! to discriminate `static_pool` / `object_lock`; the SM2.D-reserved
//! low values (0..3) will remain source-compatible by staying in the
//! `static_pool` discriminator space.
//!
//! The decoder is fail-closed: any handle that doesn't decode to a
//! valid pool index panics rather than silently aliasing to a
//! different lock.
//!
//! ## Tracing (SM2.D.4)
//!
//! Each lock instance in the pool carries a pair of Relaxed `AtomicU64`
//! counters tracking total acquire / release calls.  The counters are
//! always-on and wait-free; they cost one atomic increment per FFI
//! call.  They are exposed via dedicated FFI accessors so the cross-
//! core test (SM2.D.8) can verify FFI calls actually serialise — if N
//! threads each call `acquire`-`release` once on the same lock, the
//! final counter values must equal N (no lost updates, no double
//! increments).  In a future SM3+ kernel the counters would also feed
//! a per-lock contention metric for diagnostic dashboards; that is out
//! of scope for SM2.D.
//!
//! ## ARM ARM citations
//!
//! All counter increments use `Ordering::Relaxed` per the ARM ARM B2.3.5
//! "Memory model" definition: Relaxed atomics provide atomicity but not
//! synchronisation, which is exactly what we want for wait-free
//! diagnostic counters that must NOT participate in the lock's release-
//! acquire happens-before chain.  Inserting an `Acquire` or `Release`
//! ordering on the counter would create a spurious sync edge against
//! every concurrent lock op on a different instance — pessimising the
//! cache-line state without any correctness benefit.
//!
//! ## Safety
//!
//! Every FFI helper in this module validates the handle BEFORE
//! dereferencing the pool entry.  An out-of-range handle panics via
//! `assert!` — under the workspace's `panic = "abort"` setting this
//! halts the kernel cleanly rather than corrupting state via an
//! out-of-bounds array read.  Per the project's fail-closed FFI
//! convention this is the correct response to a malformed Lean-side
//! caller.

#[cfg(test)]
extern crate std;

use core::sync::atomic::{AtomicU64, Ordering};

use crate::queued_rw_lock::{CancelOutcome, HeldMode, QueuedRwLock};
use crate::ticket_lock::TicketLock;

// ============================================================================
// SM2.D audit-pass: cross-module test serialisation mutex
// ============================================================================
//
// Tests in `lock_bridge::runtime_tests` and tests in `crate::ffi::tests`
// both exercise the same `STATIC_*_POOL` slots (0..2) and observe
// trace-counter deltas with strict equality.  Cargo's default parallel
// test runner can interleave them, so a `lock_bridge`-side "counter
// advances by 1" snapshot can witness concurrent ffi-side increments
// and break the assertion.
//
// The mutex is defined at module scope (not inside `mod runtime_tests`)
// so that `crate::ffi::tests` can reach it via `pub(crate)` — a single
// source of truth for cross-module observation serialisation.

/// **WS-SM SM2.D audit-pass**: shared serialisation mutex for SM2.D
/// counter-observation tests across `lock_bridge::runtime_tests` and
/// `crate::ffi::tests`.
///
/// Test-only; `#[cfg(test)]`-gated.  See the audit-pass commentary
/// above for the rationale.
#[cfg(test)]
pub(crate) static LOCK_TRACE_TEST_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

// ============================================================================
// SM2.D pool dimensions
// ============================================================================

/// **WS-SM SM2.D**: capacity of the static `TicketLock` pool.
///
/// Defined as `crate::smp::MAX_SECONDARY_CORES + 1` so the pool size
/// structurally tracks `PlatformBinding::coreCount` (= 4 on RPi5) —
/// one lock per core for the cross-core test (SM2.D.8).  A future
/// multi-platform port that bumps `MAX_SECONDARY_CORES` automatically
/// propagates here; the Lean-side `staticTicketLockPoolSize` is
/// defined as `numCores`, so both sides remain in lockstep.
///
/// **Audit-pass-6 robustness fix** (pool size hardcoding): previously
/// hardcoded `= 4`; now derived structurally so the cross-language
/// agreement is mechanical rather than convention.
pub const STATIC_TICKET_LOCK_POOL_SIZE: usize = crate::smp::MAX_SECONDARY_CORES + 1;

/// **WS-SM SM2.D**: capacity of the static `RwLock` pool.
///
/// See [`STATIC_TICKET_LOCK_POOL_SIZE`] for the rationale.
pub const STATIC_RW_LOCK_POOL_SIZE: usize = crate::smp::MAX_SECONDARY_CORES + 1;

// **WS-SM SM2.D audit-pass-6 compile-time assertion**: pin the pool
// size to the canonical 4-core value.  A future PR that bumps
// `MAX_SECONDARY_CORES` past 3 must also extend the pool arrays
// below (which are sized via the constant) AND the Lean-side
// `numCores` AND the cross-language symmetry script — this
// assertion fails to elaborate if any side drifts, surfacing the
// regression at build time.
const _: () = {
    assert!(STATIC_TICKET_LOCK_POOL_SIZE == 4,
        "WS-SM SM2.D: STATIC_TICKET_LOCK_POOL_SIZE must equal 4 to match the RPi5 PlatformBinding.coreCount; \
         a multi-platform port must update the pool arrays below in lockstep.");
    assert!(STATIC_RW_LOCK_POOL_SIZE == 4,
        "WS-SM SM2.D: STATIC_RW_LOCK_POOL_SIZE must equal 4 to match the RPi5 PlatformBinding.coreCount.");
};

// ============================================================================
// SM2.D static lock pools
// ============================================================================

/// **WS-SM SM2.D**: static pool of 4 `TicketLock`s.
///
/// Addressed via the FFI helpers in this module by `u64` handle.
/// Initialisation is `const fn` so the array lives in `.bss` (zeroed at
/// boot via the bootloader's BSS-zero pass), keeping the kernel image
/// size unchanged by SM2.D.
///
/// **Lifetime**: `'static`.  Each pool entry is valid for the program's
/// lifetime; handles do not need lifetime parameters because the
/// referent is immortal.
pub static STATIC_TICKET_LOCK_POOL: [TicketLock; STATIC_TICKET_LOCK_POOL_SIZE] = [
    TicketLock::new(),
    TicketLock::new(),
    TicketLock::new(),
    TicketLock::new(),
];

/// **WS-SM SM2.D / WS-RR RR6.10**: static pool of 4 `QueuedRwLock`s.
///
/// See [`STATIC_TICKET_LOCK_POOL`] for the design notes, and this
/// module's header for why the entries are the ticket FIFO lock rather
/// than the CAS-retry one.
#[cfg(not(loom))]
pub static STATIC_RW_LOCK_POOL: [QueuedRwLock; STATIC_RW_LOCK_POOL_SIZE] = [
    QueuedRwLock::new(),
    QueuedRwLock::new(),
    QueuedRwLock::new(),
    QueuedRwLock::new(),
];

// **WS-RR RR6.20**: the loom build's pool.
//
// `loom`'s atomics are not `const`-constructible, so the `static` above
// does not compile under `--cfg loom`.  `loom::lazy_static!` is loom's
// own answer to exactly this, and it `Deref`s to the array so every
// `STATIC_RW_LOCK_POOL[idx]` below reads unchanged.  This is the only
// place in the HAL the loom cfg reaches outside `queued_rw_lock.rs`.
#[cfg(loom)]
loom::lazy_static! {
    pub static ref STATIC_RW_LOCK_POOL: [QueuedRwLock; STATIC_RW_LOCK_POOL_SIZE] = [
        QueuedRwLock::new(),
        QueuedRwLock::new(),
        QueuedRwLock::new(),
        QueuedRwLock::new(),
    ];
}

// ============================================================================
// SM2.D.4 — Tracing counters
// ============================================================================
//
// Each lock instance carries a pair of Relaxed atomic counters.  Always-on
// (no compile-time gating) because the cost is one wait-free atomic
// increment per FFI call (~1 ns on Cortex-A76) and the diagnostic value
// is critical for SM2.D.8 (verifying FFI calls actually serialise).

/// **WS-SM SM2.D.4**: per-pool-slot TicketLock acquire-call counter.
///
/// Incremented (Relaxed) by [`ticket_lock_acquire`] before delegating
/// to the inner `TicketLock::acquire`.  Read via
/// [`ticket_lock_acquire_count`].
pub static TICKET_LOCK_ACQUIRE_COUNT: [AtomicU64; STATIC_TICKET_LOCK_POOL_SIZE] = [
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
];

/// **WS-SM SM2.D.4**: per-pool-slot TicketLock release-call counter.
pub static TICKET_LOCK_RELEASE_COUNT: [AtomicU64; STATIC_TICKET_LOCK_POOL_SIZE] = [
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
];

/// **WS-SM SM2.D.4**: per-pool-slot RwLock acquire-read counter.
pub static RW_LOCK_ACQUIRE_READ_COUNT: [AtomicU64; STATIC_RW_LOCK_POOL_SIZE] = [
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
];

/// **WS-SM SM2.D.4**: per-pool-slot RwLock release-read counter.
pub static RW_LOCK_RELEASE_READ_COUNT: [AtomicU64; STATIC_RW_LOCK_POOL_SIZE] = [
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
];

/// **WS-SM SM2.D.4**: per-pool-slot RwLock acquire-write counter.
pub static RW_LOCK_ACQUIRE_WRITE_COUNT: [AtomicU64; STATIC_RW_LOCK_POOL_SIZE] = [
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
];

/// **WS-SM SM2.D.4**: per-pool-slot RwLock release-write counter.
pub static RW_LOCK_RELEASE_WRITE_COUNT: [AtomicU64; STATIC_RW_LOCK_POOL_SIZE] = [
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
];

/// **WS-LC LC3.7**: per-pool-slot RwLock **withdrawal** counter.
///
/// A withdrawal is neither an acquisition nor a release — it removes a
/// request — so it gets its own counter rather than sharing one and
/// making both figures mean two things.
pub static RW_LOCK_CANCEL_COUNT: [AtomicU64; STATIC_RW_LOCK_POOL_SIZE] = [
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
];

// ============================================================================
// SM2.D handle decoding
// ============================================================================

/// **WS-SM SM2.D**: decode a `u64` handle into a TicketLock pool index.
///
/// Returns `Some(idx)` for `handle < STATIC_TICKET_LOCK_POOL_SIZE`,
/// `None` otherwise.  Const-fn for use in compile-time validation
/// contexts.
///
/// The decoder is factored out as a pure `Option`-returning helper so
/// tests can exercise the rejection path without crossing the FFI
/// boundary (which `panic = "abort"` would convert to a process
/// abort).  The FFI wrappers in `ffi.rs` translate `None` into a
/// `panic!` that aborts the kernel under the fail-closed convention.
///
/// **Defense-in-depth narrowing**: the bound check runs in `u64` space
/// BEFORE the `as usize` cast.  Sele4n's only target is aarch64
/// (64-bit, `usize == u64`), so the cast is identity in practice.  A
/// hypothetical 32-bit port however would truncate the high bits of
/// `handle` if cast first — e.g., `handle = 0x1_0000_0001` would
/// truncate to `1` and silently alias to pool slot 1.  Performing the
/// bound check in `u64` space first guarantees that handles outside
/// `0..STATIC_TICKET_LOCK_POOL_SIZE` always reject, regardless of
/// `usize` width.  Mirrors the pattern used in
/// `ffi_per_core_*_count` (SM1.I.4 audit-pass-2).
#[inline]
#[must_use]
pub const fn decode_ticket_lock_handle(handle: u64) -> Option<usize> {
    if handle < STATIC_TICKET_LOCK_POOL_SIZE as u64 {
        Some(handle as usize)
    } else {
        None
    }
}

/// **WS-SM SM2.D**: decode a `u64` handle into a RwLock pool index.
///
/// Symmetric to [`decode_ticket_lock_handle`], including the
/// defense-in-depth narrowing comment.
#[inline]
#[must_use]
pub const fn decode_rw_lock_handle(handle: u64) -> Option<usize> {
    if handle < STATIC_RW_LOCK_POOL_SIZE as u64 {
        Some(handle as usize)
    } else {
        None
    }
}

// ============================================================================
// SM2.D.1 — TicketLock FFI helpers
// ============================================================================

/// **WS-SM SM2.D.1**: get a handle to a static TicketLock by pool index.
///
/// Returns a `u64` handle that the FFI helpers in this module accept.
/// Panics if `idx >= STATIC_TICKET_LOCK_POOL_SIZE` per the fail-closed
/// FFI convention.
///
/// At SM2.D the handle encoding is simply the index itself; SM5+ may
/// extend the encoding for per-object locks via a high-bit tag.
/// Callers MUST treat the returned `u64` as opaque.
#[inline]
#[must_use]
pub fn ticket_lock_static_handle(idx: u64) -> u64 {
    // Bound check in u64 space first so a hypothetical 32-bit port
    // would not truncate the high bits and silently alias to an
    // in-range slot.
    assert!(
        decode_ticket_lock_handle(idx).is_some(),
        "WS-SM SM2.D.1: ticket_lock_static_handle: idx={} exceeds pool size {}",
        idx,
        STATIC_TICKET_LOCK_POOL_SIZE
    );
    idx
}

/// **WS-SM SM2.D.1**: acquire the TicketLock identified by `handle`.
///
/// Returns the captured ticket (the value of `next_ticket` at capture
/// time).  Increments the per-slot `TICKET_LOCK_ACQUIRE_COUNT` counter
/// for SM2.D.4 tracing BEFORE the underlying acquire, so the counter
/// is incremented even if the acquire's spin-loop holds the call for
/// a long time (the counter records "this acquire call was issued",
/// not "this acquire call completed").
///
/// Panics if `handle` does not decode to a valid pool index.
pub fn ticket_lock_acquire(handle: u64) -> u64 {
    let idx = decode_ticket_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.1: ticket_lock_acquire: malformed handle {} (must be < {})",
            handle, STATIC_TICKET_LOCK_POOL_SIZE
        )
    });
    // SM2.D.4 trace: increment Relaxed counter before delegating.
    // wrapping_add to give defined behaviour at u64::MAX (unreachable
    // in practice at ~580 years@1GHz acquire rate but defensive).
    let _ = TICKET_LOCK_ACQUIRE_COUNT[idx].fetch_add(1, Ordering::Relaxed);
    STATIC_TICKET_LOCK_POOL[idx].acquire()
}

/// **WS-SM SM2.D.1**: release the TicketLock identified by `handle`.
///
/// Increments `serving` by 1 and broadcasts `sev`.  Increments the
/// per-slot `TICKET_LOCK_RELEASE_COUNT` counter for SM2.D.4 tracing.
///
/// The caller MUST be the current holder; misuse (release without
/// prior acquire, or double-release) is undefined behavior at the
/// abstract level and triggers a `debug_assert!` in the underlying
/// `TicketLock::release`.
///
/// Panics if `handle` does not decode to a valid pool index.
pub fn ticket_lock_release(handle: u64) {
    let idx = decode_ticket_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.1: ticket_lock_release: malformed handle {} (must be < {})",
            handle, STATIC_TICKET_LOCK_POOL_SIZE
        )
    });
    // SM2.D.4 trace: increment Relaxed counter.
    let _ = TICKET_LOCK_RELEASE_COUNT[idx].fetch_add(1, Ordering::Relaxed);
    STATIC_TICKET_LOCK_POOL[idx].release();
}

/// **WS-SM SM2.D.1**: peek at the TicketLock's holder state.
///
/// Returns a packed `u64` snapshot:
/// * bits 63..32 = `next_ticket` (truncated to u32)
/// * bits 31..0  = `serving`     (truncated to u32)
///
/// Under wf, `serving <= next_ticket` always holds; if the lock is
/// unheld, `serving == next_ticket`.  The Lean caller can extract
/// each half via shift+mask and reason about lock state at a snapshot
/// instant.
///
/// **NOT atomic with respect to other ops**: a concurrent acquire or
/// release on the same lock can race the two atomic loads inside this
/// function.  The returned snapshot may not correspond to any single
/// point in time.  This is acceptable for diagnostic use; callers that
/// need atomic state observation must hold the lock around the read.
///
/// Truncation at 2^32 is practical: at the project's design target of
/// ~10⁹ acquires/second per core × 4 cores, reaching 2^32 takes ~1
/// second — for diagnostic snapshots taken at human time scales the
/// truncated values stay informative.  At 2^32 the `next_ticket` value
/// rolls over in the high 32 bits relative to the snapshot, but the
/// `next_ticket - serving` difference (the non-negative number of
/// in-flight acquires under wf, since `serving <= next_ticket`)
/// remains correct modulo 2^32, which is the diagnostic quantity
/// callers care about.
///
/// Panics if `handle` does not decode to a valid pool index.
#[must_use]
pub fn ticket_lock_peek_holder(handle: u64) -> u64 {
    let idx = decode_ticket_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.1: ticket_lock_peek_holder: malformed handle {} (must be < {})",
            handle, STATIC_TICKET_LOCK_POOL_SIZE
        )
    });
    // Pack (next_ticket_low32, serving_low32) into one u64 via the
    // public `peek_next_ticket` / `peek_serving` accessors on
    // `TicketLock` (added in SM2.D for this purpose).  Both use
    // Acquire ordering on the underlying atomic loads.
    //
    // Audit-pass safety note: previous revisions of this function
    // used a raw-pointer cast against `TicketLock`'s `repr(C)` layout
    // to access its private fields.  That was a soft contract — a
    // future refactor adding a debug field at the start of TicketLock
    // would silently invalidate the offsets.  The dedicated public
    // accessors close this gap by making the access path explicit and
    // checked by the compiler.
    let lock = &STATIC_TICKET_LOCK_POOL[idx];
    let next = lock.peek_next_ticket() & 0xFFFF_FFFF;
    let srv = lock.peek_serving() & 0xFFFF_FFFF;
    (next << 32) | srv
}

/// **WS-SM SM2.D.4**: read the per-slot TicketLock acquire counter.
///
/// Returns a Relaxed snapshot of `TICKET_LOCK_ACQUIRE_COUNT[idx]`.
/// Used by the cross-core test (SM2.D.8) to verify FFI calls
/// actually serialise (sum of per-thread acquire calls = final
/// counter value).
///
/// Panics if `handle` does not decode to a valid pool index.
#[must_use]
pub fn ticket_lock_acquire_count(handle: u64) -> u64 {
    let idx = decode_ticket_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.4: ticket_lock_acquire_count: malformed handle {} (must be < {})",
            handle, STATIC_TICKET_LOCK_POOL_SIZE
        )
    });
    TICKET_LOCK_ACQUIRE_COUNT[idx].load(Ordering::Relaxed)
}

/// **WS-SM SM2.D.4**: read the per-slot TicketLock release counter.
#[must_use]
pub fn ticket_lock_release_count(handle: u64) -> u64 {
    let idx = decode_ticket_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.4: ticket_lock_release_count: malformed handle {} (must be < {})",
            handle, STATIC_TICKET_LOCK_POOL_SIZE
        )
    });
    TICKET_LOCK_RELEASE_COUNT[idx].load(Ordering::Relaxed)
}

// ============================================================================
// SM2.D.2 — RwLock FFI helpers
// ============================================================================

/// **WS-RR RR6.10**: the executing PE's id, as `QueuedRwLock`'s entry
/// points take it.
///
/// Read from `TPIDR_EL1` through `per_cpu::current_core_id_from_tpidr`,
/// whose documented range invariant is
/// `core_id < PlatformBinding.coreCount`; the pool is sized by the same
/// number (`STATIC_RW_LOCK_POOL_SIZE`), so the value is always in range
/// for `QueuedRwLock::MAX_WAITERS`.
///
/// It names the PE that is *running*, never one a caller supplied: the
/// FFI handle carries no core id, and inventing a parameter for one
/// would let a caller enqueue under another PE's name.  See the module
/// header for what the protocol does and does not read it for.
#[inline]
fn executing_core_id() -> u8 {
    // The invariant above bounds this well below `u8::MAX`; the
    // saturating cast is belt-and-braces for a mis-populated per-CPU
    // slot, and `QueuedRwLock`'s own range assert is the backstop.
    let id = crate::per_cpu::current_core_id_from_tpidr();
    debug_assert!(
        (id as usize) < crate::queued_rw_lock::MAX_WAITERS,
        "executing core id {id} out of range for the queued RwLock pool"
    );
    u8::try_from(id).unwrap_or(u8::MAX)
}

/// **WS-SM SM2.D.2**: get a handle to a static RwLock by pool index.
///
/// Symmetric to [`ticket_lock_static_handle`].
#[inline]
#[must_use]
pub fn rw_lock_static_handle(idx: u64) -> u64 {
    assert!(
        decode_rw_lock_handle(idx).is_some(),
        "WS-SM SM2.D.2: rw_lock_static_handle: idx={} exceeds pool size {}",
        idx,
        STATIC_RW_LOCK_POOL_SIZE
    );
    idx
}

/// **WS-SM SM2.D.2**: acquire a read lock on the RwLock identified by `handle`.
///
/// Increments `RW_LOCK_ACQUIRE_READ_COUNT[idx]` before delegating to
/// `RwLock::acquire_read`.  Panics on malformed `handle`.
pub fn rw_lock_acquire_read(handle: u64) {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.2: rw_lock_acquire_read: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    let _ = RW_LOCK_ACQUIRE_READ_COUNT[idx].fetch_add(1, Ordering::Relaxed);
    STATIC_RW_LOCK_POOL[idx].acquire_read(executing_core_id());
}

/// **WS-SM SM2.D.2**: release a read lock on the RwLock identified by `handle`.
pub fn rw_lock_release_read(handle: u64) {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.2: rw_lock_release_read: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    let _ = RW_LOCK_RELEASE_READ_COUNT[idx].fetch_add(1, Ordering::Relaxed);
    STATIC_RW_LOCK_POOL[idx].release_read(executing_core_id());
}

/// **WS-SM SM2.D.2**: acquire a write lock on the RwLock identified by `handle`.
pub fn rw_lock_acquire_write(handle: u64) {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.2: rw_lock_acquire_write: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    let _ = RW_LOCK_ACQUIRE_WRITE_COUNT[idx].fetch_add(1, Ordering::Relaxed);
    STATIC_RW_LOCK_POOL[idx].acquire_write(executing_core_id());
}

/// **WS-SM SM2.D.2**: release a write lock on the RwLock identified by `handle`.
pub fn rw_lock_release_write(handle: u64) {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.2: rw_lock_release_write: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    let _ = RW_LOCK_RELEASE_WRITE_COUNT[idx].fetch_add(1, Ordering::Relaxed);
    STATIC_RW_LOCK_POOL[idx].release_write(executing_core_id());
}

// ---------------------------------------------------------------------
// WS-LC LC3.7 — the cancellable acquisition
// ---------------------------------------------------------------------
//
// The four entry points above are the *blocking* form: they enqueue, wait
// and complete in one call, so a caller that changes its mind has no
// moment at which to do so.  A two-phase-locking growing phase that is
// refused needs exactly that moment, so the bridge exposes the phases.
//
// `rw_lock_acquire_read` and `rw_lock_complete_read` both count as one
// read acquisition, because they are: the blocking form *is* enqueue plus
// complete.  A withdrawal is a different event and gets its own counter.

/// The wire encoding of a request's mode across the foreign-function
/// surface (PR #890 review round 5): `0` is a read request, `1` a write
/// request, and anything else is malformed.
const RW_LOCK_MODE_READ: u64 = 0;
const RW_LOCK_MODE_WRITE: u64 = 1;

/// The wire encoding of a withdrawal's outcome: `0` when the request was
/// withdrawn, `1` when the core holds and owes a release
/// (`CancelOutcome`).
const RW_LOCK_CANCEL_WITHDRAWN: u64 = 0;
const RW_LOCK_CANCEL_HOLDING: u64 = 1;

/// **WS-LC LC3.7**: begin a cancellable acquisition on `handle`, taking a
/// ticket without waiting for it, in `mode` (PR #890 review round 5: the
/// lock records the mode at the issue, because whether the spec has
/// admitted a request — which `rw_lock_cancel` decides — depends on it).
///
/// The caller must follow with exactly one of `rw_lock_complete_read`,
/// `rw_lock_complete_write` or `rw_lock_cancel` for the ticket returned;
/// a completion in the other mode is refused.
#[must_use]
pub fn rw_lock_enqueue(handle: u64, mode: u64) -> u64 {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-LC LC3.7: rw_lock_enqueue: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    let mode = match mode {
        RW_LOCK_MODE_READ => HeldMode::Read,
        RW_LOCK_MODE_WRITE => HeldMode::Write,
        other => panic!(
            "PR #890 review round 5: rw_lock_enqueue: malformed mode {other} (must be \
             {RW_LOCK_MODE_READ} for a read request or {RW_LOCK_MODE_WRITE} for a write request)"
        ),
    };
    STATIC_RW_LOCK_POOL[idx].enqueue(executing_core_id(), mode)
}

/// **WS-LC LC3.7**: whether `ticket` is the one `handle` is serving, so a
/// caller polling rather than parking can tell when to complete.
#[must_use]
pub fn rw_lock_is_served(handle: u64, ticket: u64) -> bool {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-LC LC3.7: rw_lock_is_served: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    STATIC_RW_LOCK_POOL[idx].is_served(ticket)
}

/// **WS-LC LC3.7**: complete a read acquisition begun with
/// [`rw_lock_enqueue`].
pub fn rw_lock_complete_read(handle: u64, ticket: u64) {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-LC LC3.7: rw_lock_complete_read: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    let _ = RW_LOCK_ACQUIRE_READ_COUNT[idx].fetch_add(1, Ordering::Relaxed);
    STATIC_RW_LOCK_POOL[idx].complete_read(executing_core_id(), ticket);
}

/// **WS-LC LC3.7**: complete a write acquisition begun with
/// [`rw_lock_enqueue`].
pub fn rw_lock_complete_write(handle: u64, ticket: u64) {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-LC LC3.7: rw_lock_complete_write: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    let _ = RW_LOCK_ACQUIRE_WRITE_COUNT[idx].fetch_add(1, Ordering::Relaxed);
    STATIC_RW_LOCK_POOL[idx].complete_write(executing_core_id(), ticket);
}

/// **WS-LC LC3.7**: withdraw a request begun with [`rw_lock_enqueue`] —
/// or, when the spec has already admitted it, realise that admission
/// (PR #890 review round 5).
///
/// A withdrawal releases nothing and never installs a writer; it admits
/// only the reader run behind a withdrawn head, as the spec's `cancel`
/// does (`rwLock_cancel_not_effective_release`,
/// `rwLock_cancel_admits_only_the_head_reader_run` on the Lean side).
/// Returns `0` when the request was withdrawn and `1` when the core holds
/// and owes a release (`CancelOutcome::Holding`).  The withdrawal counter
/// counts *calls*, either outcome included.
#[must_use]
pub fn rw_lock_cancel(handle: u64, ticket: u64) -> u64 {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-LC LC3.7: rw_lock_cancel: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    let _ = RW_LOCK_CANCEL_COUNT[idx].fetch_add(1, Ordering::Relaxed);
    match STATIC_RW_LOCK_POOL[idx].cancel(executing_core_id(), ticket) {
        CancelOutcome::Withdrawn => RW_LOCK_CANCEL_WITHDRAWN,
        CancelOutcome::Holding => RW_LOCK_CANCEL_HOLDING,
    }
}

/// **WS-LC LC3.7**: how many withdrawals `handle` has seen.
#[must_use]
pub fn rw_lock_cancel_count(handle: u64) -> u64 {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-LC LC3.7: rw_lock_cancel_count: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    RW_LOCK_CANCEL_COUNT[idx].load(Ordering::Relaxed)
}

/// **WS-SM SM2.D.2**: snapshot of the RwLock state.
///
/// Returns the packed `(writer_held, reader_count)` from the underlying
/// `RwLock::snapshot` — same bit layout as the abstract Lean
/// `encodeRwLock` / `RwLockEncoded`:
///
/// * bit 63 = writer-held flag
/// * bits 0..62 = reader count
///
/// **NOT atomic with respect to other ops**: a concurrent acquire or
/// release on the same lock can change the snapshot value between the
/// call and its observation.  Acceptable for diagnostic use; callers
/// that need atomic state observation must hold a lock around the
/// read.
///
/// Panics if `handle` does not decode to a valid pool index.
#[must_use]
pub fn rw_lock_snapshot(handle: u64) -> u64 {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.2: rw_lock_snapshot: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    // WS-RR RR6.10: `QueuedRwLock::peek_state` returns the packed word
    // itself, which already *is* the abstract `encodeRwLock` form
    // documented at SM2.C.16 — bit 63 the writer flag, bits 0..62 the
    // reader count — because the two locks share one definition of that
    // layout (`queued_rw_lock.rs` imports `rw_lock`'s constants).  So
    // there is nothing to recompose here; decomposing and reassembling
    // it would be a second answer to a question the word already
    // answers.
    STATIC_RW_LOCK_POOL[idx].peek_state()
}

/// **WS-SM SM2.D.4**: read the per-slot RwLock acquire-read counter.
#[must_use]
pub fn rw_lock_acquire_read_count(handle: u64) -> u64 {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.4: rw_lock_acquire_read_count: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    RW_LOCK_ACQUIRE_READ_COUNT[idx].load(Ordering::Relaxed)
}

/// **WS-SM SM2.D.4**: read the per-slot RwLock release-read counter.
#[must_use]
pub fn rw_lock_release_read_count(handle: u64) -> u64 {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.4: rw_lock_release_read_count: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    RW_LOCK_RELEASE_READ_COUNT[idx].load(Ordering::Relaxed)
}

/// **WS-SM SM2.D.4**: read the per-slot RwLock acquire-write counter.
#[must_use]
pub fn rw_lock_acquire_write_count(handle: u64) -> u64 {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.4: rw_lock_acquire_write_count: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    RW_LOCK_ACQUIRE_WRITE_COUNT[idx].load(Ordering::Relaxed)
}

/// **WS-SM SM2.D.4**: read the per-slot RwLock release-write counter.
#[must_use]
pub fn rw_lock_release_write_count(handle: u64) -> u64 {
    let idx = decode_rw_lock_handle(handle).unwrap_or_else(|| {
        panic!(
            "WS-SM SM2.D.4: rw_lock_release_write_count: malformed handle {} (must be < {})",
            handle, STATIC_RW_LOCK_POOL_SIZE
        )
    });
    RW_LOCK_RELEASE_WRITE_COUNT[idx].load(Ordering::Relaxed)
}

// ============================================================================
// SM2.D.7 — Lock-primitive theorem inventory (Rust-side mirror)
// ============================================================================
//
// The authoritative SM2.D.7 inventory lives in the Lean module
// `SeLe4n.Kernel.Concurrency.LockPrimitives` (which carries each
// theorem's `Lean.Name` plus a size witness `lockPrimitives.length =
// 22`).  This Rust-side constant is a parallel artefact used by the
// `scripts/check_lock_ffi_symmetry.sh` cross-language symmetry gate to
// verify both sides agree on the canonical count.
//
// A regression that adds or removes a theorem on either side without
// updating the other will fail the symmetry check.

/// **WS-SM SM2.D.7**: canonical count of substantive SM2 theorems.
///
/// See `SeLe4n.Kernel.Concurrency.lockPrimitives_count` for the
/// authoritative Lean-side witness.  The split is:
///
/// * 4 memory-model theorems (irreflexive, transitive, antisymmetric,
///   aggregate partial-order)
/// * 6 TicketLock theorems (mutex, FIFO, bounded-wait, RA-pairing,
///   wf-invariant, reachability)
/// * 11 RwLock theorems (writer-readers exclusion, reader multiplicity,
///   FIFO admission, bounded-wait × 2, RA-pairing × 2, wf-invariant,
///   reader batching, writer liveness, writer safety)
/// * 4 refinement theorems (TicketLock, CAS-retry RwLock, deployed
///   QueuedRwLock, and the deployed lock's FIFO-admission payoff)
///
/// **WS-RR RR6.9 / RR6.19 / RR6.24 moved this from 22 to 25.**  The
/// liveness entry pointed at a single-step *safety* alias, the RwLock
/// refinement entry pointed at the form that assumes its own conclusion
/// block by block, and the lock the kernel actually deploys had no
/// entry at all.  See `LockPrimitives.lean`'s header for the detail.
pub const LOCK_THEOREM_COUNT: usize = 30;

// ============================================================================
// SM2.D.5 — Static linker-time check (build.rs scanner anchor)
// ============================================================================
//
// The build.rs scanner `scan_lock_bridge_rs_intact` verifies the
// presence of every SM2.D FFI helper in this file.  Refactoring that
// removes or renames a helper without updating the FFI export wall in
// `ffi.rs` would silently break the Lean ↔ Rust bridge.  The textual
// marker below is the scanner's anchor.

/// **WS-SM SM2.D.5 build-anchor**: marker constant ensuring the build
/// script can verify this module's presence.  The string is checked
/// textually in `build.rs` to confirm `lock_bridge.rs` participates in
/// the SM2.D FFI surface.
pub const LOCK_BRIDGE_BUILD_ANCHOR: &str = "WS-SM SM2.D lock-bridge module present";

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --------------------------------------------------------------------
    // Handle decoding
    // --------------------------------------------------------------------

    #[test]
    fn decode_ticket_lock_handle_accepts_valid_indices() {
        for idx in 0..STATIC_TICKET_LOCK_POOL_SIZE as u64 {
            assert_eq!(decode_ticket_lock_handle(idx), Some(idx as usize));
        }
    }

    #[test]
    fn decode_ticket_lock_handle_rejects_out_of_range() {
        assert_eq!(
            decode_ticket_lock_handle(STATIC_TICKET_LOCK_POOL_SIZE as u64),
            None
        );
        assert_eq!(decode_ticket_lock_handle(u64::MAX), None);
        assert_eq!(decode_ticket_lock_handle(99), None);
    }

    /// **WS-SM SM2.D**: 32-bit-truncation defense — handles where the
    /// low 32 bits happen to land in the pool range but the high 32
    /// bits are non-zero must reject.  Verifies the audit-pass fix
    /// that moved the bound check into u64 space before the `as usize`
    /// cast.
    ///
    /// On 64-bit targets `usize == u64` so the cast is identity; this
    /// test passes structurally.  On a hypothetical 32-bit port, a
    /// regression that re-introduced `(handle as usize) < POOL_SIZE`
    /// would silently accept these inputs — failing this test.
    #[test]
    fn decode_handles_reject_u64_with_high_bits_aliasing_slot() {
        assert_eq!(decode_ticket_lock_handle(0x1_0000_0001), None);
        assert_eq!(decode_ticket_lock_handle(0x1_0000_0002), None);
        assert_eq!(decode_ticket_lock_handle(0x1_0000_0003), None);
        assert_eq!(decode_ticket_lock_handle(0xFFFF_FFFF_0000_0000), None);
        assert_eq!(decode_rw_lock_handle(0x1_0000_0001), None);
        assert_eq!(decode_rw_lock_handle(0x1_0000_0002), None);
        assert_eq!(decode_rw_lock_handle(0xFFFF_FFFF_0000_0000), None);
    }

    #[test]
    fn decode_rw_lock_handle_accepts_valid_indices() {
        for idx in 0..STATIC_RW_LOCK_POOL_SIZE as u64 {
            assert_eq!(decode_rw_lock_handle(idx), Some(idx as usize));
        }
    }

    #[test]
    fn decode_rw_lock_handle_rejects_out_of_range() {
        assert_eq!(decode_rw_lock_handle(STATIC_RW_LOCK_POOL_SIZE as u64), None);
        assert_eq!(decode_rw_lock_handle(u64::MAX), None);
    }

    #[test]
    fn decode_handles_const_callable() {
        const T_OK: Option<usize> = decode_ticket_lock_handle(0);
        const T_OOR: Option<usize> = decode_ticket_lock_handle(99);
        const R_OK: Option<usize> = decode_rw_lock_handle(0);
        const R_OOR: Option<usize> = decode_rw_lock_handle(99);
        assert_eq!(T_OK, Some(0));
        assert_eq!(T_OOR, None);
        assert_eq!(R_OK, Some(0));
        assert_eq!(R_OOR, None);
    }

    // --------------------------------------------------------------------
    // Handle generation
    // --------------------------------------------------------------------

    #[test]
    fn ticket_lock_static_handle_returns_index() {
        for idx in 0..STATIC_TICKET_LOCK_POOL_SIZE as u64 {
            assert_eq!(ticket_lock_static_handle(idx), idx);
        }
    }

    #[test]
    #[should_panic(expected = "exceeds pool size")]
    fn ticket_lock_static_handle_out_of_range_panics() {
        let _ = ticket_lock_static_handle(STATIC_TICKET_LOCK_POOL_SIZE as u64);
    }

    #[test]
    fn rw_lock_static_handle_returns_index() {
        for idx in 0..STATIC_RW_LOCK_POOL_SIZE as u64 {
            assert_eq!(rw_lock_static_handle(idx), idx);
        }
    }

    #[test]
    #[should_panic(expected = "exceeds pool size")]
    fn rw_lock_static_handle_out_of_range_panics() {
        let _ = rw_lock_static_handle(STATIC_RW_LOCK_POOL_SIZE as u64);
    }

    // --------------------------------------------------------------------
    // Layout assumptions
    // --------------------------------------------------------------------

    #[test]
    fn ticket_lock_peek_accessors_match_runtime_state() {
        // The SM2.D.1 `ticket_lock_peek_holder` FFI helper composes
        // `peek_next_ticket` and `peek_serving` (added on TicketLock
        // for this purpose).  Verify those accessors return the live
        // values, not stale snapshots.
        let lock = TicketLock::new();
        assert_eq!(lock.peek_next_ticket(), 0);
        assert_eq!(lock.peek_serving(), 0);
        // After acquire: next_ticket = 1, serving = 0.
        let _ticket = lock.acquire();
        assert_eq!(lock.peek_next_ticket(), 1, "next_ticket advanced");
        assert_eq!(lock.peek_serving(), 0, "serving unchanged before release");
        // After release: next_ticket = 1, serving = 1.
        lock.release();
        assert_eq!(lock.peek_next_ticket(), 1);
        assert_eq!(lock.peek_serving(), 1);
        // Many cycles preserve the next == serving == count invariant
        // when no contention.
        for _ in 0..50u64 {
            let _ = lock.acquire();
            lock.release();
        }
        assert_eq!(lock.peek_next_ticket(), 51);
        assert_eq!(lock.peek_serving(), 51);
    }

    #[test]
    fn static_ticket_pool_size_matches_constant() {
        assert_eq!(STATIC_TICKET_LOCK_POOL.len(), STATIC_TICKET_LOCK_POOL_SIZE);
    }

    #[test]
    fn static_rw_pool_size_matches_constant() {
        assert_eq!(STATIC_RW_LOCK_POOL.len(), STATIC_RW_LOCK_POOL_SIZE);
    }

    /// **WS-RR RR6.10**: the deployed reader-writer lock is the ticket
    /// FIFO one.
    ///
    /// A type-level pin, not a size or a name: the binding below only
    /// elaborates if the pool's element type *is*
    /// `queued_rw_lock::QueuedRwLock`.  Reverting the pool to
    /// `rw_lock::RwLock` — which has no queue, and so does not satisfy
    /// the strict-FIFO specification this bridge is claimed to
    /// implement — fails to compile here as well as failing
    /// `build.rs`'s `scan_lock_bridge_rs_intact`.
    ///
    /// No state is asserted: the pool is global and the runtime tests
    /// below drive its slots concurrently, so a `peek_state() == 0`
    /// here would be a race rather than a check.
    #[test]
    fn deployed_rw_lock_is_the_ticket_fifo_lock() {
        let deployed: &[crate::queued_rw_lock::QueuedRwLock; STATIC_RW_LOCK_POOL_SIZE] =
            &STATIC_RW_LOCK_POOL;
        assert_eq!(deployed.len(), STATIC_RW_LOCK_POOL_SIZE);
    }

    /// **WS-RR RR6.10**: the deployed lock's packed word *is* the
    /// abstract `encodeRwLock` form, read through the layout constants
    /// `rw_lock` owns and `queued_rw_lock` imports.
    ///
    /// This is why `rw_lock_snapshot` can hand `peek_state()` straight
    /// to Lean with nothing to recompose.  Driven on a local lock, not
    /// a pool slot, so it asserts about the encoding rather than
    /// racing the runtime tests below.
    #[test]
    fn deployed_lock_state_word_is_the_abstract_encoding() {
        let lock = crate::queued_rw_lock::QueuedRwLock::new();
        assert_eq!(lock.peek_state(), 0, "unheld encodes as 0");

        lock.acquire_read(0);
        assert_eq!(
            lock.peek_state() & crate::rw_lock::READER_MASK,
            1,
            "one reader is reader-count 1"
        );
        assert_eq!(
            lock.peek_state() & crate::rw_lock::WRITER_BIT,
            0,
            "and the writer bit is clear"
        );
        lock.release_read(0);

        lock.acquire_write(0);
        assert_eq!(
            lock.peek_state(),
            crate::rw_lock::WRITER_BIT,
            "a writer encodes as exactly the writer bit"
        );
        lock.release_write(0);
        assert_eq!(lock.peek_state(), 0);
    }

    #[test]
    fn trace_counter_arrays_match_pool_size() {
        assert_eq!(
            TICKET_LOCK_ACQUIRE_COUNT.len(),
            STATIC_TICKET_LOCK_POOL_SIZE
        );
        assert_eq!(
            TICKET_LOCK_RELEASE_COUNT.len(),
            STATIC_TICKET_LOCK_POOL_SIZE
        );
        assert_eq!(RW_LOCK_ACQUIRE_READ_COUNT.len(), STATIC_RW_LOCK_POOL_SIZE);
        assert_eq!(RW_LOCK_RELEASE_READ_COUNT.len(), STATIC_RW_LOCK_POOL_SIZE);
        assert_eq!(RW_LOCK_ACQUIRE_WRITE_COUNT.len(), STATIC_RW_LOCK_POOL_SIZE);
        assert_eq!(RW_LOCK_RELEASE_WRITE_COUNT.len(), STATIC_RW_LOCK_POOL_SIZE);
    }

    // --------------------------------------------------------------------
    // LOCK_THEOREM_COUNT pinning
    // --------------------------------------------------------------------

    /// The count and its category breakdown must move together.
    ///
    /// Two assertions, because either alone is satisfiable by a drift: the
    /// literal catches a category changing without the total, and the sum
    /// catches the total changing without a category.  The test is named for
    /// the *relation* rather than for the number — a name carrying the figure
    /// has to be renamed on every bump, and a rename that is forgotten leaves
    /// a test whose name says one thing and whose body checks another.
    #[test]
    fn theorem_count_equals_its_category_breakdown() {
        assert_eq!(LOCK_THEOREM_COUNT, 30);
        // 4 memory-model + 6 TicketLock + 16 RwLock + 4 refinement = 30.
        assert_eq!(4 + 6 + 16 + 4, LOCK_THEOREM_COUNT);
    }

    // --------------------------------------------------------------------
    // Build anchor
    // --------------------------------------------------------------------

    #[test]
    fn build_anchor_string_intact() {
        assert!(LOCK_BRIDGE_BUILD_ANCHOR.contains("WS-SM SM2.D"));
        assert!(LOCK_BRIDGE_BUILD_ANCHOR.contains("lock-bridge"));
    }
}

#[cfg(test)]
mod runtime_tests {
    use super::*;

    // --------------------------------------------------------------------
    // SM2.D.1 — TicketLock acquire/release/peek_holder runtime tests
    //
    // These tests use disjoint pool slots from cross-thread tests below
    // to avoid contention.  Each test owns its slot exclusively:
    //   * acquire_release_returns_ticket   → slot 0
    //   * sm2d1_peek_holder_packs_counters       → slot 1
    //   * sm2d1_acquire_increments_counter       → slot 2
    //   * (slot 3 reserved for the cross-thread test sm2d8_*)
    //
    // The trace-counter tests use a private mutex to serialise their
    // observation against any concurrent test that might touch the same
    // slot.  Since cargo's default test runner uses multiple threads,
    // even disjoint-slot tests can race if the suite is re-run multiple
    // times without clearing the global counters; the mutex ensures
    // each test's pre/post snapshot is meaningful.
    // --------------------------------------------------------------------

    // The shared serialisation mutex is defined at the module level
    // below the test module (see `LOCK_TRACE_TEST_MUTEX` outside this
    // `mod runtime_tests`) so it is reachable from
    // `crate::ffi::tests` via `pub(crate)`.

    #[test]
    fn acquire_release_returns_ticket() {
        // Slot 0 is shared across multiple tests for sequential reuse;
        // the lock is re-usable across tests (since acquire+release
        // is monotonic).  We just verify acquire returns a u64 and
        // release doesn't panic.
        let _guard = LOCK_TRACE_TEST_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let h = ticket_lock_static_handle(0);
        // Snapshot the counter to verify advance below.
        let before_acq = ticket_lock_acquire_count(h);
        let before_rel = ticket_lock_release_count(h);
        let ticket = ticket_lock_acquire(h);
        // The ticket value reflects this slot's history of acquires.
        // We don't assert a specific value (other tests may have used
        // the slot), just that the call returned cleanly.
        let _ = ticket;
        ticket_lock_release(h);
        // Counters advanced by exactly 1.
        let after_acq = ticket_lock_acquire_count(h);
        let after_rel = ticket_lock_release_count(h);
        assert_eq!(
            after_acq,
            before_acq + 1,
            "acquire counter must advance by 1"
        );
        assert_eq!(
            after_rel,
            before_rel + 1,
            "release counter must advance by 1"
        );
    }

    #[test]
    fn peek_holder_packs_next_and_serving() {
        let _guard = LOCK_TRACE_TEST_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let h = ticket_lock_static_handle(1);
        // Snapshot before any op.  Since this test shares slot 1 with
        // potentially other tests in the future, we treat the
        // observed values as opaque baselines and verify the packing.
        let packed = ticket_lock_peek_holder(h);
        // Audit-pass-6: `packed >> 32` already produces a u32-valued
        // u64 (high bits cleared by the shift), so no extra mask
        // needed.  `packed & 0xFFFF_FFFF` extracts the low 32 bits.
        let next_low = packed >> 32;
        let srv_low = packed & 0xFFFF_FFFF;
        // Under wf: serving <= next_ticket.
        assert!(
            srv_low <= next_low,
            "serving ({}) must be <= next_ticket ({})",
            srv_low,
            next_low
        );
        // Do one acquire-release and verify both counters advance.
        let _ = ticket_lock_acquire(h);
        ticket_lock_release(h);
        let packed2 = ticket_lock_peek_holder(h);
        let next2 = packed2 >> 32;
        let srv2 = packed2 & 0xFFFF_FFFF;
        // Both counters advanced by 1.
        assert_eq!(next2, next_low + 1);
        assert_eq!(srv2, srv_low + 1);
    }

    #[test]
    fn acquire_increments_trace_counter() {
        let _guard = LOCK_TRACE_TEST_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let h = ticket_lock_static_handle(2);
        let before = ticket_lock_acquire_count(h);
        for _ in 0..5 {
            let _ = ticket_lock_acquire(h);
            ticket_lock_release(h);
        }
        let after = ticket_lock_acquire_count(h);
        assert_eq!(after, before + 5);
    }

    // --------------------------------------------------------------------
    // SM2.D.2 — RwLock runtime tests
    //
    // Slot layout:
    //   * sm2d2_read_acquire_release           → slot 0
    //   * sm2d2_write_acquire_release          → slot 1
    //   * snapshot_returns_state         → slot 2
    //   * (slot 3 reserved for cross-thread sm2d8_rw_*)
    // --------------------------------------------------------------------

    #[test]
    fn read_acquire_release_increments_counters() {
        let _guard = LOCK_TRACE_TEST_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let h = rw_lock_static_handle(0);
        let before_acq = rw_lock_acquire_read_count(h);
        let before_rel = rw_lock_release_read_count(h);
        rw_lock_acquire_read(h);
        rw_lock_release_read(h);
        let after_acq = rw_lock_acquire_read_count(h);
        let after_rel = rw_lock_release_read_count(h);
        assert_eq!(after_acq, before_acq + 1);
        assert_eq!(after_rel, before_rel + 1);
    }

    #[test]
    fn write_acquire_release_increments_counters() {
        let _guard = LOCK_TRACE_TEST_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let h = rw_lock_static_handle(1);
        let before_acq = rw_lock_acquire_write_count(h);
        let before_rel = rw_lock_release_write_count(h);
        rw_lock_acquire_write(h);
        rw_lock_release_write(h);
        let after_acq = rw_lock_acquire_write_count(h);
        let after_rel = rw_lock_release_write_count(h);
        assert_eq!(after_acq, before_acq + 1);
        assert_eq!(after_rel, before_rel + 1);
    }

    #[test]
    fn snapshot_returns_state() {
        let _guard = LOCK_TRACE_TEST_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let h = rw_lock_static_handle(2);
        // Before any op (or after a balanced sequence), state is unheld.
        let snap = rw_lock_snapshot(h);
        // Mask out writer bit: if no concurrent test holds the lock,
        // it should be 0.  We don't strictly assert this because other
        // tests in the same run may have left a transient state.
        // We DO verify the bit-mask encoding shape: writer bit at
        // position 63, reader bits at 0..62.
        let writer_bit = (snap >> 63) & 1;
        let reader_count = snap & crate::rw_lock::READER_MASK;
        assert!(writer_bit <= 1, "writer bit must be 0 or 1");
        assert!(reader_count <= crate::rw_lock::READER_MASK);
        // Acquire a read and check the count advances by 1.
        rw_lock_acquire_read(h);
        let snap_held = rw_lock_snapshot(h);
        let count_held = snap_held & crate::rw_lock::READER_MASK;
        let writer_held = (snap_held >> 63) & 1;
        assert!(
            count_held >= 1,
            "reader count must be at least 1 while held"
        );
        assert_eq!(
            writer_held, 0,
            "writer bit must be clear while a reader holds"
        );
        rw_lock_release_read(h);
    }

    // --------------------------------------------------------------------
    // SM2.D.8 — Cross-core serialization tests
    //
    // Verify that FFI calls actually serialise: N threads each
    // performing K acquire-release operations on the same lock leave
    // exactly N*K acquires and N*K releases in the trace counters
    // (no lost updates, no double increments).
    //
    // This is the canonical "the lock works" test at the FFI surface,
    // crucial for SM3+ per-object lock integration.  Uses slot 3 of
    // each pool exclusively.
    // --------------------------------------------------------------------

    // Slot-3 dedicated mutexes — split into ticket / rw pools because
    // the two pools have no shared state, so over-serialising via a
    // single mutex would be wasteful.  Each cross-core test owns its
    // slot 3 for its duration; the per-pool split allows ticket-pool
    // and rw-pool cross-core tests to run concurrently.
    //
    // Audit-pass-6 (LOW-10 finding): pre-audit had a single
    // `SM2D8_SLOT3_MUTEX` covering both pools.  Test correctness was
    // preserved (the single mutex over-serialised but didn't break
    // anything), but the split makes the lock-discipline intent
    // explicit and removes the spurious serialisation.
    static TICKET_SLOT3_TEST_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());
    static RW_SLOT3_TEST_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

    #[test]
    fn ticket_lock_cross_thread_serializes_increments() {
        use std::cell::UnsafeCell;
        use std::sync::Arc;
        let _guard = TICKET_SLOT3_TEST_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());

        // Use slot 3 exclusively.
        let h = ticket_lock_static_handle(3);

        // Snapshot pre-test counters so we can assert exact deltas.
        let pre_acq = ticket_lock_acquire_count(h);
        let pre_rel = ticket_lock_release_count(h);

        // Shared counter protected by the FFI-bridge lock.
        struct SharedCounter {
            handle: u64,
            count: UnsafeCell<u64>,
        }
        // SAFETY: SharedCounter is Sync because all access to `count`
        // is serialised through the TicketLock at `handle`.
        unsafe impl Sync for SharedCounter {}
        let shared = Arc::new(SharedCounter {
            handle: h,
            count: UnsafeCell::new(0),
        });

        const NUM_THREADS: usize = 4;
        const OPS_PER_THREAD: u64 = 100;

        let mut handles: std::vec::Vec<std::thread::JoinHandle<()>> = std::vec::Vec::new();
        for _ in 0..NUM_THREADS {
            let s = Arc::clone(&shared);
            handles.push(std::thread::spawn(move || {
                for _ in 0..OPS_PER_THREAD {
                    let _t = ticket_lock_acquire(s.handle);
                    // SAFETY: lock held via FFI bridge.
                    unsafe {
                        *s.count.get() += 1;
                    }
                    ticket_lock_release(s.handle);
                }
            }));
        }
        for hdl in handles {
            hdl.join().expect("worker panicked");
        }

        // SAFETY: all threads joined.
        let final_count = unsafe { *shared.count.get() };
        let expected = (NUM_THREADS as u64) * OPS_PER_THREAD;
        assert_eq!(
            final_count, expected,
            "FFI bridge failed to serialise: got {} increments, expected {}",
            final_count, expected
        );

        // Trace counters: exactly expected acquires and releases.
        let post_acq = ticket_lock_acquire_count(h);
        let post_rel = ticket_lock_release_count(h);
        assert_eq!(post_acq - pre_acq, expected, "acquire counter delta");
        assert_eq!(post_rel - pre_rel, expected, "release counter delta");
    }

    #[test]
    fn rw_lock_cross_thread_read_acquires_concurrent() {
        // Multiple readers should be allowed to hold the lock
        // concurrently.  Spawn N reader threads that each hold the read
        // lock for a short window and verify they observe the reader
        // count is at least 1 (and at most NUM_THREADS) during their
        // critical section.
        use std::sync::Arc;
        let _guard = RW_SLOT3_TEST_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());

        let h = rw_lock_static_handle(3);
        let pre_acq = rw_lock_acquire_read_count(h);
        let pre_rel = rw_lock_release_read_count(h);

        const NUM_READERS: usize = 4;
        const OPS_PER_READER: u64 = 50;

        let counter_observed_max = Arc::new(std::sync::Mutex::new(0u64));

        let mut handles: std::vec::Vec<std::thread::JoinHandle<()>> = std::vec::Vec::new();
        for pe in 0..NUM_READERS {
            let max_arc = Arc::clone(&counter_observed_max);
            handles.push(std::thread::spawn(move || {
                // One thread per PE (PR #890 review round 2): the bridge
                // reads the executing core's id, and on the host that is
                // the identity this thread adopts.
                let _pe = crate::per_cpu::HostCoreIdentity::adopt(pe);
                for _ in 0..OPS_PER_READER {
                    rw_lock_acquire_read(h);
                    let snap = rw_lock_snapshot(h);
                    let count = snap & crate::rw_lock::READER_MASK;
                    {
                        let mut m = max_arc.lock().unwrap_or_else(|e| e.into_inner());
                        if count > *m {
                            *m = count;
                        }
                    }
                    rw_lock_release_read(h);
                }
            }));
        }
        for hdl in handles {
            hdl.join().expect("reader panicked");
        }

        // Trace counters: exactly expected.
        let post_acq = rw_lock_acquire_read_count(h);
        let post_rel = rw_lock_release_read_count(h);
        let expected = (NUM_READERS as u64) * OPS_PER_READER;
        assert_eq!(post_acq - pre_acq, expected);
        assert_eq!(post_rel - pre_rel, expected);

        // Observed max reader count is at least 1 (every observer
        // saw itself as a reader); under reader-multiplicity (Lean
        // spec rwLock_reader_multiplicity Theorem 3.3.6.1), it could
        // be up to NUM_READERS.  On a single-core host with cooperative
        // scheduling we may see only 1, but on a multi-core host we
        // commonly see >= 2.  We assert just the lower bound.
        let max_observed = *counter_observed_max
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        assert!(
            max_observed >= 1,
            "every reader must observe itself: got max {}",
            max_observed
        );
        assert!(
            max_observed <= NUM_READERS as u64,
            "reader count cannot exceed reader thread count: got {} > {}",
            max_observed,
            NUM_READERS
        );
    }

    #[test]
    fn rw_lock_cross_thread_writer_excludes_readers() {
        // While a writer holds the lock, no reader can hold it.  Spawn
        // 1 writer + N readers contending for the same lock; verify
        // that during any moment, the snapshot is either (writer-held,
        // 0 readers) or (no writer, k readers).
        use std::sync::Arc;
        let _guard = RW_SLOT3_TEST_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());

        let h = rw_lock_static_handle(3);
        let pre_aw = rw_lock_acquire_write_count(h);
        let pre_rw = rw_lock_release_write_count(h);
        let pre_ar = rw_lock_acquire_read_count(h);
        let pre_rr = rw_lock_release_read_count(h);

        let invariant_broken = Arc::new(AtomicU64::new(0));

        const NUM_READERS: usize = 3;
        const READ_OPS: u64 = 30;
        const WRITE_OPS: u64 = 30;

        let mut handles: std::vec::Vec<std::thread::JoinHandle<()>> = std::vec::Vec::new();

        // 1 writer, on PE 0 (PR #890 review round 2: one thread per PE).
        {
            let ib = Arc::clone(&invariant_broken);
            handles.push(std::thread::spawn(move || {
                let _pe = crate::per_cpu::HostCoreIdentity::adopt(0);
                for _ in 0..WRITE_OPS {
                    rw_lock_acquire_write(h);
                    // Verify: writer held and zero readers.
                    let snap = rw_lock_snapshot(h);
                    let writer = (snap >> 63) & 1;
                    let count = snap & crate::rw_lock::READER_MASK;
                    if writer != 1 || count != 0 {
                        ib.fetch_add(1, Ordering::Relaxed);
                    }
                    rw_lock_release_write(h);
                }
            }));
        }

        // N readers, on PEs 1..=N.
        for pe in 1..=NUM_READERS {
            let ib = Arc::clone(&invariant_broken);
            handles.push(std::thread::spawn(move || {
                let _pe = crate::per_cpu::HostCoreIdentity::adopt(pe);
                for _ in 0..READ_OPS {
                    rw_lock_acquire_read(h);
                    // Verify: no writer.
                    let snap = rw_lock_snapshot(h);
                    let writer = (snap >> 63) & 1;
                    let count = snap & crate::rw_lock::READER_MASK;
                    if writer != 0 || count == 0 {
                        ib.fetch_add(1, Ordering::Relaxed);
                    }
                    rw_lock_release_read(h);
                }
            }));
        }

        for hdl in handles {
            hdl.join().expect("worker panicked");
        }

        assert_eq!(
            invariant_broken.load(Ordering::Relaxed),
            0,
            "writer-readers exclusion (Lean spec rwLock_writer_readers_exclusion) violated"
        );

        // Trace counters: exactly the expected total.
        assert_eq!(
            rw_lock_acquire_write_count(h) - pre_aw,
            WRITE_OPS,
            "write acquires"
        );
        assert_eq!(
            rw_lock_release_write_count(h) - pre_rw,
            WRITE_OPS,
            "write releases"
        );
        assert_eq!(
            rw_lock_acquire_read_count(h) - pre_ar,
            (NUM_READERS as u64) * READ_OPS,
            "read acquires"
        );
        assert_eq!(
            rw_lock_release_read_count(h) - pre_rr,
            (NUM_READERS as u64) * READ_OPS,
            "read releases"
        );
    }
}
