// SPDX-License-Identifier: GPL-3.0-or-later
//! Lock-bridge — Static lock pools + FFI helpers for SM2.D.
//!
//! **WS-SM SM2.D** (FFI bridge + integration): bridges the verified Lean lock
//! specifications (`SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean` and
//! `RwLock.lean`) and the Rust implementations (`ticket_lock.rs`,
//! `rw_lock.rs`) into a stable C-callable surface that the Lean kernel can
//! consume via `@[extern]` declarations.
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
//! * Each `TicketLock` / `RwLock` is `#[repr(C, align(64))]` (one cache
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

use crate::rw_lock::RwLock;
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
pub(crate) static SM2D_TRACE_TEST_MUTEX: std::sync::Mutex<()> =
    std::sync::Mutex::new(());

// ============================================================================
// SM2.D pool dimensions
// ============================================================================

/// **WS-SM SM2.D**: capacity of the static `TicketLock` pool.
///
/// Matches `PlatformBinding.coreCount = 4` on RPi5 so the cross-core
/// test (SM2.D.8) can exercise one lock per core.  Future SM3+
/// per-object locks add capacity via a separate handle encoding; this
/// constant pins the SM2.D static-pool size.
pub const STATIC_TICKET_LOCK_POOL_SIZE: usize = 4;

/// **WS-SM SM2.D**: capacity of the static `RwLock` pool.
///
/// See [`STATIC_TICKET_LOCK_POOL_SIZE`] for the rationale.
pub const STATIC_RW_LOCK_POOL_SIZE: usize = 4;

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

/// **WS-SM SM2.D**: static pool of 4 `RwLock`s.
///
/// See [`STATIC_TICKET_LOCK_POOL`] for the design notes.
pub static STATIC_RW_LOCK_POOL: [RwLock; STATIC_RW_LOCK_POOL_SIZE] = [
    RwLock::new(),
    RwLock::new(),
    RwLock::new(),
    RwLock::new(),
];

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
/// `serving - next_ticket` difference (the number of in-flight
/// acquires) remains correct modulo 2^32, which is the diagnostic
/// quantity callers care about.
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
    STATIC_RW_LOCK_POOL[idx].acquire_read();
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
    STATIC_RW_LOCK_POOL[idx].release_read();
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
    STATIC_RW_LOCK_POOL[idx].acquire_write();
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
    STATIC_RW_LOCK_POOL[idx].release_write();
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
    let (writer, count) = STATIC_RW_LOCK_POOL[idx].snapshot();
    let writer_bit = if writer { crate::rw_lock::WRITER_BIT } else { 0 };
    writer_bit | (count & crate::rw_lock::READER_MASK)
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
/// * 10 RwLock theorems (writer-readers exclusion, reader multiplicity,
///   FIFO admission, bounded-wait × 2, RA-pairing × 2, wf-invariant,
///   reader batching, no-writer-starvation)
/// * 2 refinement theorems (TicketLock refinement, RwLock refinement)
pub const SM2_THEOREM_COUNT: usize = 22;

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
pub const SM2D_BUILD_ANCHOR: &str = "WS-SM SM2.D lock-bridge module present";

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
    fn sm2d_decode_ticket_lock_handle_accepts_valid_indices() {
        for idx in 0..STATIC_TICKET_LOCK_POOL_SIZE as u64 {
            assert_eq!(decode_ticket_lock_handle(idx), Some(idx as usize));
        }
    }

    #[test]
    fn sm2d_decode_ticket_lock_handle_rejects_out_of_range() {
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
    fn sm2d_decode_handles_reject_u64_with_high_bits_aliasing_slot() {
        assert_eq!(decode_ticket_lock_handle(0x1_0000_0001), None);
        assert_eq!(decode_ticket_lock_handle(0x1_0000_0002), None);
        assert_eq!(decode_ticket_lock_handle(0x1_0000_0003), None);
        assert_eq!(decode_ticket_lock_handle(0xFFFF_FFFF_0000_0000), None);
        assert_eq!(decode_rw_lock_handle(0x1_0000_0001), None);
        assert_eq!(decode_rw_lock_handle(0x1_0000_0002), None);
        assert_eq!(decode_rw_lock_handle(0xFFFF_FFFF_0000_0000), None);
    }

    #[test]
    fn sm2d_decode_rw_lock_handle_accepts_valid_indices() {
        for idx in 0..STATIC_RW_LOCK_POOL_SIZE as u64 {
            assert_eq!(decode_rw_lock_handle(idx), Some(idx as usize));
        }
    }

    #[test]
    fn sm2d_decode_rw_lock_handle_rejects_out_of_range() {
        assert_eq!(
            decode_rw_lock_handle(STATIC_RW_LOCK_POOL_SIZE as u64),
            None
        );
        assert_eq!(decode_rw_lock_handle(u64::MAX), None);
    }

    #[test]
    fn sm2d_decode_handles_const_callable() {
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
    fn sm2d_ticket_lock_static_handle_returns_index() {
        for idx in 0..STATIC_TICKET_LOCK_POOL_SIZE as u64 {
            assert_eq!(ticket_lock_static_handle(idx), idx);
        }
    }

    #[test]
    #[should_panic(expected = "exceeds pool size")]
    fn sm2d_ticket_lock_static_handle_out_of_range_panics() {
        let _ = ticket_lock_static_handle(STATIC_TICKET_LOCK_POOL_SIZE as u64);
    }

    #[test]
    fn sm2d_rw_lock_static_handle_returns_index() {
        for idx in 0..STATIC_RW_LOCK_POOL_SIZE as u64 {
            assert_eq!(rw_lock_static_handle(idx), idx);
        }
    }

    #[test]
    #[should_panic(expected = "exceeds pool size")]
    fn sm2d_rw_lock_static_handle_out_of_range_panics() {
        let _ = rw_lock_static_handle(STATIC_RW_LOCK_POOL_SIZE as u64);
    }

    // --------------------------------------------------------------------
    // Layout assumptions
    // --------------------------------------------------------------------

    #[test]
    fn sm2d_ticket_lock_peek_accessors_match_runtime_state() {
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
    fn sm2d_static_ticket_pool_size_matches_constant() {
        assert_eq!(STATIC_TICKET_LOCK_POOL.len(), STATIC_TICKET_LOCK_POOL_SIZE);
    }

    #[test]
    fn sm2d_static_rw_pool_size_matches_constant() {
        assert_eq!(STATIC_RW_LOCK_POOL.len(), STATIC_RW_LOCK_POOL_SIZE);
    }

    #[test]
    fn sm2d_trace_counter_arrays_match_pool_size() {
        assert_eq!(TICKET_LOCK_ACQUIRE_COUNT.len(), STATIC_TICKET_LOCK_POOL_SIZE);
        assert_eq!(TICKET_LOCK_RELEASE_COUNT.len(), STATIC_TICKET_LOCK_POOL_SIZE);
        assert_eq!(RW_LOCK_ACQUIRE_READ_COUNT.len(), STATIC_RW_LOCK_POOL_SIZE);
        assert_eq!(RW_LOCK_RELEASE_READ_COUNT.len(), STATIC_RW_LOCK_POOL_SIZE);
        assert_eq!(RW_LOCK_ACQUIRE_WRITE_COUNT.len(), STATIC_RW_LOCK_POOL_SIZE);
        assert_eq!(RW_LOCK_RELEASE_WRITE_COUNT.len(), STATIC_RW_LOCK_POOL_SIZE);
    }

    // --------------------------------------------------------------------
    // SM2_THEOREM_COUNT pinning
    // --------------------------------------------------------------------

    #[test]
    fn sm2d_theorem_count_is_22() {
        assert_eq!(SM2_THEOREM_COUNT, 22);
        // Cross-check the breakdown:
        //   4 memory-model + 6 TicketLock + 10 RwLock + 2 refinement = 22.
        assert_eq!(4 + 6 + 10 + 2, SM2_THEOREM_COUNT);
    }

    // --------------------------------------------------------------------
    // Build anchor
    // --------------------------------------------------------------------

    #[test]
    fn sm2d_build_anchor_string_intact() {
        assert!(SM2D_BUILD_ANCHOR.contains("WS-SM SM2.D"));
        assert!(SM2D_BUILD_ANCHOR.contains("lock-bridge"));
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
    //   * sm2d1_acquire_release_returns_ticket   → slot 0
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
    // below the test module (see `SM2D_TRACE_TEST_MUTEX` outside this
    // `mod runtime_tests`) so it is reachable from
    // `crate::ffi::tests` via `pub(crate)`.

    #[test]
    fn sm2d1_acquire_release_returns_ticket() {
        // Slot 0 is shared across multiple tests for sequential reuse;
        // the lock is re-usable across tests (since acquire+release
        // is monotonic).  We just verify acquire returns a u64 and
        // release doesn't panic.
        let _guard = SM2D_TRACE_TEST_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
        assert_eq!(after_acq, before_acq + 1, "acquire counter must advance by 1");
        assert_eq!(after_rel, before_rel + 1, "release counter must advance by 1");
    }

    #[test]
    fn sm2d1_peek_holder_packs_next_and_serving() {
        let _guard = SM2D_TRACE_TEST_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        let h = ticket_lock_static_handle(1);
        // Snapshot before any op.  Since this test shares slot 1 with
        // potentially other tests in the future, we treat the
        // observed values as opaque baselines and verify the packing.
        let packed = ticket_lock_peek_holder(h);
        let next_low = (packed >> 32) & 0xFFFF_FFFF;
        let srv_low = packed & 0xFFFF_FFFF;
        // Under wf: serving <= next_ticket.
        assert!(
            srv_low <= next_low,
            "serving ({}) must be <= next_ticket ({})", srv_low, next_low
        );
        // Do one acquire-release and verify both counters advance.
        let _ = ticket_lock_acquire(h);
        ticket_lock_release(h);
        let packed2 = ticket_lock_peek_holder(h);
        let next2 = (packed2 >> 32) & 0xFFFF_FFFF;
        let srv2 = packed2 & 0xFFFF_FFFF;
        // Both counters advanced by 1.
        assert_eq!(next2, next_low + 1);
        assert_eq!(srv2, srv_low + 1);
    }

    #[test]
    fn sm2d1_acquire_increments_trace_counter() {
        let _guard = SM2D_TRACE_TEST_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
    //   * sm2d2_snapshot_returns_state         → slot 2
    //   * (slot 3 reserved for cross-thread sm2d8_rw_*)
    // --------------------------------------------------------------------

    #[test]
    fn sm2d2_read_acquire_release_increments_counters() {
        let _guard = SM2D_TRACE_TEST_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
    fn sm2d2_write_acquire_release_increments_counters() {
        let _guard = SM2D_TRACE_TEST_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
    fn sm2d2_snapshot_returns_state() {
        let _guard = SM2D_TRACE_TEST_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
        assert!(count_held >= 1, "reader count must be at least 1 while held");
        assert_eq!(writer_held, 0, "writer bit must be clear while a reader holds");
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

    // Slot-3 dedicated mutex so the cross-core tests don't race against
    // the other counter-observation tests above.  Each cross-core test
    // owns slot 3 for its duration.
    static SM2D8_SLOT3_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

    #[test]
    fn sm2d8_ticket_lock_cross_thread_serializes_increments() {
        use std::sync::Arc;
        use std::cell::UnsafeCell;
        let _guard = SM2D8_SLOT3_MUTEX.lock().unwrap_or_else(|e| e.into_inner());

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
    fn sm2d8_rw_lock_cross_thread_read_acquires_concurrent() {
        // Multiple readers should be allowed to hold the lock
        // concurrently.  Spawn N reader threads that each hold the read
        // lock for a short window and verify they observe the reader
        // count is at least 1 (and at most NUM_THREADS) during their
        // critical section.
        use std::sync::Arc;
        let _guard = SM2D8_SLOT3_MUTEX.lock().unwrap_or_else(|e| e.into_inner());

        let h = rw_lock_static_handle(3);
        let pre_acq = rw_lock_acquire_read_count(h);
        let pre_rel = rw_lock_release_read_count(h);

        const NUM_READERS: usize = 4;
        const OPS_PER_READER: u64 = 50;

        let counter_observed_max = Arc::new(std::sync::Mutex::new(0u64));

        let mut handles: std::vec::Vec<std::thread::JoinHandle<()>> = std::vec::Vec::new();
        for _ in 0..NUM_READERS {
            let max_arc = Arc::clone(&counter_observed_max);
            handles.push(std::thread::spawn(move || {
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
        let max_observed = *counter_observed_max.lock().unwrap_or_else(|e| e.into_inner());
        assert!(
            max_observed >= 1,
            "every reader must observe itself: got max {}",
            max_observed
        );
        assert!(
            max_observed <= NUM_READERS as u64,
            "reader count cannot exceed reader thread count: got {} > {}",
            max_observed, NUM_READERS
        );
    }

    #[test]
    fn sm2d8_rw_lock_cross_thread_writer_excludes_readers() {
        // While a writer holds the lock, no reader can hold it.  Spawn
        // 1 writer + N readers contending for the same lock; verify
        // that during any moment, the snapshot is either (writer-held,
        // 0 readers) or (no writer, k readers).
        use std::sync::Arc;
        let _guard = SM2D8_SLOT3_MUTEX.lock().unwrap_or_else(|e| e.into_inner());

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

        // 1 writer.
        {
            let ib = Arc::clone(&invariant_broken);
            handles.push(std::thread::spawn(move || {
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

        // N readers.
        for _ in 0..NUM_READERS {
            let ib = Arc::clone(&invariant_broken);
            handles.push(std::thread::spawn(move || {
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
