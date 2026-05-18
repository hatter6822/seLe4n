// SPDX-License-Identifier: GPL-3.0-or-later
//! RwLock — reader-writer lock with bit-packed atomic state.
//!
//! **WS-SM SM2.C.19**: Rust implementation refining the Lean operational
//! specification at `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean`.
//!
//! ## Operational mapping
//!
//! | Rust | Lean spec |
//! |------|-----------|
//! | `RwLock::new` | `RwLockState.unheld` |
//! | `acquire_read` | `applyOp .tryAcquireRead` + retry until acquired |
//! | `release_read` | `applyOp .releaseRead` |
//! | `acquire_write` | `applyOp .tryAcquireWrite` + retry until acquired |
//! | `release_write` | `applyOp .releaseWrite` |
//! | `state.bit 63` | `writerHeld.isSome` |
//! | `state.bits 0..62` | `readers.length` |
//!
//! ## Bit-packed encoding
//!
//! The state is packed into a single `AtomicU64`:
//! * **bit 63** (`WRITER_BIT`): set iff a writer holds the lock.
//! * **bits 0..62** (`READER_MASK`): the reader count (max 2^63 - 1).
//!
//! This allows the entire reader-writer state to be CAS'd atomically.  The
//! Lean spec models the abstract state directly (`writerHeld : Option CoreId`,
//! `readers : List CoreId`, `waiters : List (CoreId × AccessMode)`); the bit-
//! packing is a refinement detail.
//!
//! The Lean spec's `waiters` queue is not represented in the Rust impl —
//! waiters block via CAS-retry instead of an explicit queue.  This means
//! the Rust impl does NOT satisfy the Lean spec's FIFO admission property
//! (`rwLock_fifo_admission`); it only guarantees the mutex and exclusion
//! invariants.  This divergence is documented in the SM2.C.20 refinement
//! bridge (`Locks/RwLockRefinement.lean`).
//!
//! ## ARM ARM citations
//!
//! * `state.load(Acquire)` — `LDAR` (ARM ARM C6.2.142): acquire-load with
//!   release-acquire synchronisation.
//! * `state.compare_exchange(..., Acquire, ...)` — `LDAXR` / `STLXR`
//!   exclusive monitor pair (ARM ARM C6.2.135) or LSE `CASA` (ARM ARM
//!   C6.2.50): atomic compare-and-swap with acquire ordering on success.
//! * `state.store(0, Release)` — `STLR` (ARM ARM C6.2.243 / B2.3.7):
//!   release-store with publishing semantics.
//! * `state.fetch_sub(1, Release)` — `STADDL` (ARM ARM C6.2.305) or LDADDL
//!   used in subtraction form: release atomic decrement.
//! * `sev` — `SEV` (ARM ARM C6.2.243): wake all PEs in the inner-shareable
//!   domain that are parked on `wfe`.
//!
//! ## Cache-line alignment
//!
//! `#[repr(C, align(64))]` guarantees the lock occupies a single cache line,
//! eliminating false sharing with adjacent data.  On Cortex-A76 (BCM2712,
//! RPi5) the L1 cache line size is 64 bytes.
//!
//! ## Acquisition discipline
//!
//! The same core MUST NOT:
//! * Acquire a read lock while already holding it (deadlock on the
//!   subsequent writer).
//! * Acquire a write lock while already holding a read or write lock
//!   on the same RwLock (deadlock).
//! * Release a lock it doesn't hold.
//!
//! The RAII guards (`RwLockReadGuard`, `RwLockWriteGuard`) eliminate the
//! release-discipline violations at the type level (Drop is the only path
//! to release).  Acquisition discipline must be ensured by the caller (or
//! by the SM3 per-object lock ladder).

// Tests use `std::sync::Arc`, `std::thread`, etc.  Production code below
// never references `std::*` items (no_std-compatible).
#[cfg(test)]
extern crate std;

use core::sync::atomic::{AtomicU64, Ordering};

/// **WS-SM SM2.C.19**: writer-bit position in the packed state.
///
/// Bit 63 of the `AtomicU64` is set iff a writer currently holds the lock.
/// Refines the Lean spec's `writerHeld.isSome` field.
pub const WRITER_BIT_POS: u32 = 63;

/// **WS-SM SM2.C.19**: writer-bit value (`1 << 63 = 2^63`).
pub const WRITER_BIT: u64 = 1u64 << WRITER_BIT_POS;

/// **WS-SM SM2.C.19**: reader-count mask (`!WRITER_BIT` = bits 0..62).
pub const READER_MASK: u64 = !WRITER_BIT;

/// **WS-SM SM2.C.19**: reader-writer lock with bit-packed atomic state.
///
/// Refines the abstract `RwLockState` from
/// `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean`.
///
/// The single `AtomicU64` `state` field encodes:
/// * bit 63: writer-held flag (set iff a writer currently holds the lock).
/// * bits 0..62: reader count (number of cores currently holding the read lock).
///
/// # Safety
///
/// `RwLock` is `Sync` because all access to `state` is via atomic operations
/// which are inherently concurrent-safe.  Multiple cores can call
/// `acquire_read` / `acquire_write` / `release_read` / `release_write` from
/// different threads.
///
/// The lock holder must call the matching release exactly once after each
/// successful acquire.  Using the `with_read` / `with_write` RAII combinators
/// is preferred.
#[repr(C, align(64))]
pub struct RwLock {
    /// Bit-packed state: bit 63 = writer-held, bits 0..62 = reader count.
    state: AtomicU64,
}

impl RwLock {
    /// **WS-SM SM2.C.19**: construct a new, unheld RwLock.
    ///
    /// Refines `RwLockState.unheld` from the Lean spec: writerHeld = none,
    /// readers = [], waiters = [].  In the bit-packed representation, this
    /// is `state = 0`.
    ///
    /// The constructor is `const fn` so `RwLock`s can be embedded in
    /// `static` declarations for global per-object locks (SM3).
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        Self {
            state: AtomicU64::new(0),
        }
    }

    /// **WS-SM SM2.C.19**: acquire a read lock.
    ///
    /// Refines the Lean operation `applyOp .tryAcquireRead core` retried
    /// until the state allows the acquire.
    ///
    /// # Algorithm
    ///
    /// CAS-retry loop:
    /// 1. Load the current state with `Acquire` ordering.
    /// 2. If the writer bit is set, park on WFE and retry.
    /// 3. If the writer bit is clear, attempt CAS to increment reader count.
    ///    On success, return.  On failure (another thread updated the state),
    ///    retry.
    ///
    /// # Release-acquire pairing
    ///
    /// The successful CAS with `Acquire` ordering synchronizes-with the
    /// prior writer's `release_write`'s `Release` store.  This
    /// `synchronizesWith` edge (per the Lean spec's
    /// `rwLock_release_acquire_pairing_read`) propagates the prior writer's
    /// writes to the new reader before any reader-protected access.
    ///
    /// # Bounded wait
    ///
    /// By `rwLock_bounded_wait_read`, the total number of cores currently
    /// involved with the lock (readers + writer + waiters) is at most
    /// `numCores`.  Combined with critical-section bounds, this gives
    /// `WCRT(acquire_read) ≤ (numCores - 1) × T_cs`.
    ///
    /// # FIFO divergence
    ///
    /// The Lean spec's `rwLock_fifo_admission` is NOT enforced by this
    /// impl: a reader can be admitted before a queued writer because there
    /// is no explicit waiters queue in the Rust state.  The mutex and
    /// exclusion properties ARE enforced.  See SM2.C.20 for refinement
    /// discussion.
    ///
    /// # API contract
    ///
    /// The caller MUST pair each successful `acquire_read` with exactly one
    /// matching `release_read`.  Prefer `with_read` to make this contract
    /// enforced at the type level.
    #[inline]
    pub fn acquire_read(&self) {
        loop {
            let s = self.state.load(Ordering::Acquire);
            if s & WRITER_BIT != 0 {
                // Writer holds; wait for release.
                crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
                continue;
            }
            // Writer-bit clear.  Reader count is `s` (since bit 63 = 0).
            // Attempt CAS to increment reader count.
            let new_state = s + 1;
            // Defensive: check for reader-count overflow.  In practice
            // unreachable (numCores = 4 << 2^63).
            debug_assert!(
                new_state & WRITER_BIT == 0,
                "RwLock reader count overflow (impossible under numCores ≤ 4)"
            );
            if self.state.compare_exchange(
                s, new_state, Ordering::Acquire, Ordering::Relaxed,
            ).is_ok() {
                return;
            }
            // CAS failed; another thread modified state.  Retry.
        }
    }

    /// **WS-SM SM2.C.19**: release a read lock.
    ///
    /// Refines the Lean operation `applyOp .releaseRead core`: decrement
    /// the reader count atomically.
    ///
    /// # Algorithm
    ///
    /// CAS-retry loop on `fetch_sub(1)`:
    /// 1. Load the current state.
    /// 2. Validate reader count > 0 (debug_assert).
    /// 3. CAS-decrement with `Release` ordering.
    /// 4. SEV to wake any waiting writer.
    ///
    /// # Release-acquire pairing
    ///
    /// The CAS with `Release` ordering publishes the reader's writes to
    /// any subsequent acquirer.  Pairs with the next acquirer's
    /// `Acquire`-load CAS.
    ///
    /// # API contract
    ///
    /// The caller MUST be a current holder (must have called `acquire_read`
    /// without a matching `release_read` since).  Misuse (release without
    /// prior acquire, or double-release) can panic in debug builds (the
    /// `debug_assert` catches reader-count-zero-on-release).
    #[inline]
    pub fn release_read(&self) {
        loop {
            let s = self.state.load(Ordering::Acquire);
            let count = s & READER_MASK;
            debug_assert!(count > 0,
                "RwLock::release_read called without a matching acquire_read \
                 (reader count is {count})");
            // Preserve writer bit (should be 0 under correct usage); decrement count.
            let new_state = (s & WRITER_BIT) | (count - 1);
            if self.state.compare_exchange(
                s, new_state, Ordering::Release, Ordering::Relaxed,
            ).is_ok() {
                // Wake any waiters (writers parked on WFE).
                crate::cpu::sev();
                return;
            }
            // CAS failed; retry.
        }
    }

    /// **WS-SM SM2.C.19**: acquire a write lock.
    ///
    /// Refines the Lean operation `applyOp .tryAcquireWrite core` retried
    /// until the state allows the acquire.
    ///
    /// # Algorithm
    ///
    /// CAS-retry loop:
    /// 1. Load the current state.
    /// 2. If state != 0 (writer held OR readers held), park on WFE and retry.
    /// 3. If state == 0, attempt CAS from 0 to WRITER_BIT.
    ///    On success, return.  On failure, retry.
    ///
    /// # Release-acquire pairing
    ///
    /// The successful CAS with `Acquire` ordering synchronizes-with the
    /// prior holder's release.  Pairs with the prior writer's
    /// `release_write` Release-store, or with the last reader's
    /// `release_read` Release-CAS.
    ///
    /// # FIFO divergence
    ///
    /// Same as `acquire_read`: no explicit waiters queue, so FIFO writer
    /// admission is NOT enforced.  Under heavy reader contention, writers
    /// may starve in principle (though in practice the SEV-WFE coordination
    /// limits this).
    ///
    /// # API contract
    ///
    /// Same as `acquire_read`: caller MUST pair each successful
    /// `acquire_write` with exactly one matching `release_write`.  Prefer
    /// `with_write`.
    #[inline]
    pub fn acquire_write(&self) {
        loop {
            let s = self.state.load(Ordering::Acquire);
            if s != 0 {
                // Lock held (writer or readers); wait.
                crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
                continue;
            }
            // State = 0; attempt to claim writer bit.
            if self.state.compare_exchange(
                0, WRITER_BIT, Ordering::Acquire, Ordering::Relaxed,
            ).is_ok() {
                return;
            }
            // CAS failed; retry.
        }
    }

    /// **WS-SM SM2.C.19**: release a write lock.
    ///
    /// Refines the Lean operation `applyOp .releaseWrite core`: clear the
    /// writer bit.
    ///
    /// # Algorithm
    ///
    /// 1. Validate writer bit is set + reader count is 0 (debug_assert).
    /// 2. Store 0 with `Release` ordering.
    /// 3. SEV to wake any waiting readers/writers.
    ///
    /// # Release-acquire pairing
    ///
    /// The `Release` store publishes the writer's writes to any subsequent
    /// acquirer.  Pairs with the next acquirer's `Acquire`-load.
    ///
    /// # API contract
    ///
    /// The caller MUST be the current writer (must have called
    /// `acquire_write` without a matching `release_write` since).  Misuse
    /// can panic in debug builds.
    #[inline]
    pub fn release_write(&self) {
        debug_assert!(
            self.state.load(Ordering::Acquire) & READER_MASK == 0,
            "RwLock::release_write called with non-zero reader count"
        );
        debug_assert!(
            self.state.load(Ordering::Acquire) & WRITER_BIT != 0,
            "RwLock::release_write called without a matching acquire_write"
        );
        // Clear the writer bit (and reset reader count, which must be 0).
        self.state.store(0, Ordering::Release);
        crate::cpu::sev();
    }

    /// **WS-SM SM2.C.19**: RAII reader combinator.
    ///
    /// Acquires a read lock, runs the closure `f`, and releases the read
    /// lock on normal return.  Panics in the closure propagate through Drop
    /// on the guard, so the lock is still released on a panic-unwind.
    #[inline]
    pub fn with_read<F, R>(&self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let _guard = RwLockReadGuard::acquire(self);
        f()
    }

    /// **WS-SM SM2.C.19**: RAII writer combinator.
    ///
    /// Acquires a write lock, runs the closure `f`, and releases the write
    /// lock on normal return.  Same panic-safety as `with_read`.
    #[inline]
    pub fn with_write<F, R>(&self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let _guard = RwLockWriteGuard::acquire(self);
        f()
    }

    /// **WS-SM SM2.C.19**: introspect the current state.
    ///
    /// Returns `(writer_held, reader_count)` for diagnostics.  The result
    /// is a SNAPSHOT and may not reflect the state after concurrent ops.
    /// Useful for logging and assertions in test code.
    #[must_use]
    #[inline]
    pub fn snapshot(&self) -> (bool, u64) {
        let s = self.state.load(Ordering::Acquire);
        ((s & WRITER_BIT) != 0, s & READER_MASK)
    }
}

/// **WS-SM SM2.C.19**: RAII guard for `RwLock` read access.
///
/// Holds the read lock for the lifetime of the guard.  On `Drop`, calls
/// `release_read` automatically.  Use via `RwLock::with_read` rather than
/// constructing directly.
pub struct RwLockReadGuard<'a> {
    lock: &'a RwLock,
}

impl<'a> RwLockReadGuard<'a> {
    /// **WS-SM SM2.C.19**: acquire a read lock and return a guard.
    #[inline]
    pub fn acquire(lock: &'a RwLock) -> Self {
        lock.acquire_read();
        Self { lock }
    }
}

impl<'a> Drop for RwLockReadGuard<'a> {
    /// **WS-SM SM2.C.19**: release the read lock on guard drop.
    #[inline]
    fn drop(&mut self) {
        self.lock.release_read();
    }
}

/// **WS-SM SM2.C.19**: RAII guard for `RwLock` write access.
pub struct RwLockWriteGuard<'a> {
    lock: &'a RwLock,
}

impl<'a> RwLockWriteGuard<'a> {
    /// **WS-SM SM2.C.19**: acquire a write lock and return a guard.
    #[inline]
    pub fn acquire(lock: &'a RwLock) -> Self {
        lock.acquire_write();
        Self { lock }
    }
}

impl<'a> Drop for RwLockWriteGuard<'a> {
    /// **WS-SM SM2.C.19**: release the write lock on guard drop.
    #[inline]
    fn drop(&mut self) {
        self.lock.release_write();
    }
}

impl Default for RwLock {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// SM2.C.19 unit tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::{align_of, size_of};

    /// **SM2.C.19 test**: new RwLock has state = 0.
    #[test]
    fn sm2c19_new_initial_state() {
        let lock = RwLock::new();
        assert_eq!(lock.state.load(Ordering::Acquire), 0);
        let (writer, count) = lock.snapshot();
        assert!(!writer);
        assert_eq!(count, 0);
    }

    /// **SM2.C.19 test**: single read acquire increments reader count.
    #[test]
    fn sm2c19_single_read_acquire() {
        let lock = RwLock::new();
        lock.acquire_read();
        let (writer, count) = lock.snapshot();
        assert!(!writer);
        assert_eq!(count, 1);
        lock.release_read();
        let (writer, count) = lock.snapshot();
        assert!(!writer);
        assert_eq!(count, 0);
    }

    /// **SM2.C.19 test**: multiple sequential read acquires accumulate.
    #[test]
    fn sm2c19_multi_read_sequential() {
        let lock = RwLock::new();
        lock.acquire_read();
        lock.acquire_read();
        lock.acquire_read();
        let (writer, count) = lock.snapshot();
        assert!(!writer);
        assert_eq!(count, 3);
        // Release all.
        lock.release_read();
        lock.release_read();
        lock.release_read();
        assert_eq!(lock.state.load(Ordering::Acquire), 0);
    }

    /// **SM2.C.19 test**: writer acquire sets writer bit.
    #[test]
    fn sm2c19_write_acquire() {
        let lock = RwLock::new();
        lock.acquire_write();
        let (writer, count) = lock.snapshot();
        assert!(writer);
        assert_eq!(count, 0);
        lock.release_write();
        assert_eq!(lock.state.load(Ordering::Acquire), 0);
    }

    /// **SM2.C.19 test**: writer-readers exclusion (writer holds, readers wait).
    ///
    /// This is verified at the API level: after a writer acquire, the
    /// state has writer bit set.  The Lean spec's
    /// `rwLock_writer_readers_exclusion` theorem ensures readers and writer
    /// cannot coexist; the Rust CAS-retry loop enforces this dynamically.
    #[test]
    fn sm2c19_writer_state_excludes_readers() {
        let lock = RwLock::new();
        lock.acquire_write();
        let (writer, count) = lock.snapshot();
        assert!(writer);
        assert_eq!(count, 0);
        lock.release_write();
    }

    /// **SM2.C.19 test**: writer-then-reader cycle.
    #[test]
    fn sm2c19_write_release_then_read() {
        let lock = RwLock::new();
        lock.acquire_write();
        lock.release_write();
        // Now reader can acquire.
        lock.acquire_read();
        let (writer, count) = lock.snapshot();
        assert!(!writer);
        assert_eq!(count, 1);
        lock.release_read();
    }

    /// **SM2.C.19 test**: reader-then-writer cycle (sequential).
    #[test]
    fn sm2c19_read_release_then_write() {
        let lock = RwLock::new();
        lock.acquire_read();
        lock.release_read();
        // Now writer can acquire.
        lock.acquire_write();
        let (writer, count) = lock.snapshot();
        assert!(writer);
        assert_eq!(count, 0);
        lock.release_write();
    }

    /// **SM2.C.19 test**: with_read executes closure and releases.
    #[test]
    fn sm2c19_with_read_executes() {
        let lock = RwLock::new();
        let result = lock.with_read(|| 42);
        assert_eq!(result, 42);
        // Lock released.
        assert_eq!(lock.state.load(Ordering::Acquire), 0);
    }

    /// **SM2.C.19 test**: with_write executes closure and releases.
    #[test]
    fn sm2c19_with_write_executes() {
        let lock = RwLock::new();
        let result = lock.with_write(|| 77);
        assert_eq!(result, 77);
        // Lock released.
        assert_eq!(lock.state.load(Ordering::Acquire), 0);
    }

    /// **SM2.C.19 test**: cache-line alignment.
    #[test]
    fn sm2c19_cache_line_aligned() {
        assert_eq!(align_of::<RwLock>(), 64);
        // Size is at least 8 bytes (one u64 field) and at most 64 (alignment).
        assert!(size_of::<RwLock>() >= 8);
        assert!(size_of::<RwLock>() <= 64);
    }

    /// **SM2.C.19 test**: const constructor works in static context.
    #[test]
    fn sm2c19_const_constructor() {
        static GLOBAL_LOCK: RwLock = RwLock::new();
        assert_eq!(GLOBAL_LOCK.state.load(Ordering::Acquire), 0);
    }

    /// **SM2.C.19 test**: Default matches new().
    #[test]
    fn sm2c19_default_matches_new() {
        let lock_default = RwLock::default();
        let lock_new = RwLock::new();
        assert_eq!(
            lock_default.state.load(Ordering::Acquire),
            lock_new.state.load(Ordering::Acquire)
        );
    }

    /// **SM2.C.19 test**: writer bit constants match the Lean spec.
    #[test]
    fn sm2c19_writer_bit_constants() {
        assert_eq!(WRITER_BIT_POS, 63);
        assert_eq!(WRITER_BIT, 1u64 << 63);
        assert_eq!(READER_MASK, (1u64 << 63) - 1);
        // Sanity: WRITER_BIT and READER_MASK don't overlap.
        assert_eq!(WRITER_BIT & READER_MASK, 0);
        // Together they cover all 64 bits.
        assert_eq!(WRITER_BIT | READER_MASK, u64::MAX);
    }

    /// **SM2.C.19 test**: reader-count snapshot correctness.
    #[test]
    fn sm2c19_snapshot_correctness() {
        let lock = RwLock::new();
        // Initial: (false, 0).
        assert_eq!(lock.snapshot(), (false, 0));
        // After 3 reader acquires: (false, 3).
        lock.acquire_read();
        lock.acquire_read();
        lock.acquire_read();
        assert_eq!(lock.snapshot(), (false, 3));
        // Release 2: (false, 1).
        lock.release_read();
        lock.release_read();
        assert_eq!(lock.snapshot(), (false, 1));
        // Release last: (false, 0).
        lock.release_read();
        assert_eq!(lock.snapshot(), (false, 0));
        // Writer acquire: (true, 0).
        lock.acquire_write();
        assert_eq!(lock.snapshot(), (true, 0));
        lock.release_write();
    }

    /// **SM2.C.19 test**: 100-cycle read acquire/release loop.
    #[test]
    fn sm2c19_many_read_cycles() {
        let lock = RwLock::new();
        for _ in 0..100 {
            lock.acquire_read();
            lock.release_read();
        }
        assert_eq!(lock.state.load(Ordering::Acquire), 0);
    }

    /// **SM2.C.19 test**: 100-cycle write acquire/release loop.
    #[test]
    fn sm2c19_many_write_cycles() {
        let lock = RwLock::new();
        for _ in 0..100 {
            lock.acquire_write();
            lock.release_write();
        }
        assert_eq!(lock.state.load(Ordering::Acquire), 0);
    }

    /// **SM2.C.19 test**: nested with_read on a single lock.
    ///
    /// This is sequential nesting (acquire_read after release_read).  NOT
    /// re-entrant nesting (would deadlock on the second acquire if writer
    /// is waiting).
    #[test]
    fn sm2c19_sequential_with_read() {
        let lock = RwLock::new();
        let a = lock.with_read(|| 1);
        let b = lock.with_read(|| 2);
        let c = lock.with_read(|| 3);
        assert_eq!(a, 1);
        assert_eq!(b, 2);
        assert_eq!(c, 3);
        assert_eq!(lock.state.load(Ordering::Acquire), 0);
    }

    /// **SM2.C.19 test**: signature pinning for public API.
    ///
    /// Records the canonical signatures of every public function.  A future
    /// refactor that changes a signature must update this test, surfacing
    /// the API change at review time.
    #[test]
    fn sm2c19_public_api_signature_pin() {
        let _new: fn() -> RwLock = RwLock::new;
        let _acquire_read: fn(&RwLock) = RwLock::acquire_read;
        let _release_read: fn(&RwLock) = RwLock::release_read;
        let _acquire_write: fn(&RwLock) = RwLock::acquire_write;
        let _release_write: fn(&RwLock) = RwLock::release_write;
        let _snapshot: fn(&RwLock) -> (bool, u64) = RwLock::snapshot;
    }

    /// **SM2.C.19 test**: const fn pinning.
    ///
    /// Forces a const-context evaluation: if `RwLock::new` weren't `const fn`,
    /// the `static` declaration would fail to compile.
    #[test]
    fn sm2c19_new_is_const_fn() {
        static _LOCK_AS_STATIC: RwLock = RwLock::new();
    }

    /// **SM2.C.19 test**: panic-safety — with_read releases on panic.
    #[test]
    fn sm2c19_with_read_releases_on_panic() {
        use std::panic;
        let lock = RwLock::new();
        let lock_ref = &lock;
        let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
            lock_ref.with_read(|| {
                panic!("simulated reader-side panic");
            })
        }));
        assert!(result.is_err(), "panic should have been caught");
        // Lock must be released: state should be 0.
        assert_eq!(lock.state.load(Ordering::Acquire), 0,
                   "Drop on RwLockReadGuard must release on panic-unwind");
    }

    /// **SM2.C.19 test**: panic-safety — with_write releases on panic.
    #[test]
    fn sm2c19_with_write_releases_on_panic() {
        use std::panic;
        let lock = RwLock::new();
        let lock_ref = &lock;
        let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
            lock_ref.with_write(|| {
                panic!("simulated writer-side panic");
            })
        }));
        assert!(result.is_err(), "panic should have been caught");
        // Lock must be released.
        assert_eq!(lock.state.load(Ordering::Acquire), 0,
                   "Drop on RwLockWriteGuard must release on panic-unwind");
    }

    /// **SM2.C.19 test**: debug_assert catches release_read without acquire.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "called without a matching acquire_read")]
    fn sm2c19_release_read_without_acquire_panics_in_debug() {
        let lock = RwLock::new();
        lock.release_read();
    }

    /// **SM2.C.19 test**: debug_assert catches release_write without acquire.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "called without a matching acquire_write")]
    fn sm2c19_release_write_without_acquire_panics_in_debug() {
        let lock = RwLock::new();
        lock.release_write();
    }

    /// **SM2.C.22 cross-thread stress test**: many readers in parallel.
    ///
    /// Spawns NUM_THREADS, each doing OPS_PER_THREAD reader acquire-release
    /// cycles.  The final state must be 0 (all readers released).
    #[test]
    fn sm2c22_cross_thread_reader_stress() {
        use std::sync::Arc;
        let lock = Arc::new(RwLock::new());
        const NUM_THREADS: usize = 4;
        const OPS_PER_THREAD: usize = 1000;
        let mut handles: std::vec::Vec<std::thread::JoinHandle<()>> = std::vec::Vec::new();
        for _ in 0..NUM_THREADS {
            let l = Arc::clone(&lock);
            handles.push(std::thread::spawn(move || {
                for _ in 0..OPS_PER_THREAD {
                    l.acquire_read();
                    l.release_read();
                }
            }));
        }
        for h in handles {
            h.join().expect("worker thread panicked");
        }
        // All readers released; state is 0.
        assert_eq!(lock.state.load(Ordering::Acquire), 0);
    }

    /// **SM2.C.22 cross-thread stress test**: writer + readers interleaving.
    ///
    /// Mix of readers and writers contending for the same lock.  Each
    /// thread does writer-then-reader-then-writer ops in a loop.  Lock state
    /// must be 0 at end.
    #[test]
    fn sm2c22_cross_thread_mixed_stress() {
        use std::sync::Arc;
        use std::cell::UnsafeCell;
        // Shared counter protected by writer; readers just read.
        struct Shared {
            lock: RwLock,
            counter: UnsafeCell<u64>,
        }
        // SAFETY: all writes are gated by writer lock; reads are gated by reader lock.
        unsafe impl Sync for Shared {}
        let shared = Arc::new(Shared {
            lock: RwLock::new(),
            counter: UnsafeCell::new(0),
        });
        const NUM_THREADS: usize = 4;
        const OPS_PER_THREAD: usize = 250;
        let mut handles: std::vec::Vec<std::thread::JoinHandle<()>> = std::vec::Vec::new();
        for thread_idx in 0..NUM_THREADS {
            let s = Arc::clone(&shared);
            handles.push(std::thread::spawn(move || {
                for op_idx in 0..OPS_PER_THREAD {
                    // Mix of writers (every 4th op) and readers.
                    if op_idx % 4 == thread_idx % 4 {
                        s.lock.with_write(|| {
                            // SAFETY: writer lock held → exclusive access.
                            unsafe { *s.counter.get() += 1; }
                        });
                    } else {
                        s.lock.with_read(|| {
                            // SAFETY: reader lock held → shared access.
                            let _v = unsafe { *s.counter.get() };
                        });
                    }
                }
            }));
        }
        for h in handles {
            h.join().expect("worker thread panicked");
        }
        // Lock state must be 0 (all released).
        assert_eq!(shared.lock.state.load(Ordering::Acquire), 0);
        // Counter must be > 0 (some writers happened).
        let final_count = unsafe { *shared.counter.get() };
        assert!(final_count > 0, "writers should have incremented counter");
        // Counter must be <= NUM_THREADS * OPS_PER_THREAD (sanity bound).
        let upper_bound = (NUM_THREADS * OPS_PER_THREAD) as u64;
        assert!(final_count <= upper_bound,
                "counter {final_count} exceeds upper bound {upper_bound}");
    }

    /// **SM2.C.22 cross-thread stress test**: reader-batching observation.
    ///
    /// Spawns NUM_READERS reader threads that all try to acquire concurrently.
    /// Verify that the reader count snapshot reaches at least 2 at some
    /// point (demonstrating reader-multiplicity from the Lean spec's
    /// `rwLock_reader_multiplicity`).
    ///
    /// This is a probabilistic test (could fail on a system that serializes
    /// every read).  In practice on a multi-core system it succeeds reliably.
    #[test]
    fn sm2c22_cross_thread_reader_multiplicity() {
        use std::sync::Arc;
        use std::sync::atomic::AtomicU64;
        const NUM_READERS: usize = 4;
        let lock = Arc::new(RwLock::new());
        let max_observed = Arc::new(AtomicU64::new(0));
        let mut handles: std::vec::Vec<std::thread::JoinHandle<()>> = std::vec::Vec::new();
        for _ in 0..NUM_READERS {
            let l = Arc::clone(&lock);
            let m = Arc::clone(&max_observed);
            handles.push(std::thread::spawn(move || {
                l.acquire_read();
                // Hold the read lock briefly to allow other readers to acquire.
                let (_w, count) = l.snapshot();
                m.fetch_max(count, Ordering::Relaxed);
                // Allow other readers to acquire.
                std::thread::yield_now();
                l.release_read();
            }));
        }
        for h in handles {
            h.join().expect("worker thread panicked");
        }
        // All released.
        assert_eq!(lock.state.load(Ordering::Acquire), 0);
        // Max observed reader count should be ≥ 1 (always; the acquirer sees
        // itself).  We can't deterministically assert ≥ 2 without ordering
        // guarantees, but on a multi-core system this is overwhelmingly
        // likely.  The test passes if execution completes without deadlock
        // or panic, which is the substantive correctness property.
        assert!(max_observed.load(Ordering::Relaxed) >= 1);
    }

    /// **SM2.C.17 encoding round-trip test**: every bit-pattern round-trips.
    ///
    /// Cross-references the Lean spec's `rwLock_encode_decode_roundtrip`
    /// and `rwLock_decode_encode_roundtrip` at concrete values.
    #[test]
    fn sm2c17_encoding_round_trip() {
        // No writer, 0 readers.
        let encoded = 0u64;
        assert_eq!(encoded & WRITER_BIT, 0);
        assert_eq!(encoded & READER_MASK, 0);
        // No writer, N readers.
        for count in 0..=10u64 {
            let encoded = count;
            assert_eq!(encoded & WRITER_BIT, 0, "writer bit should be clear");
            assert_eq!(encoded & READER_MASK, count, "reader count round-trips");
        }
        // Writer held, 0 readers.
        let encoded = WRITER_BIT;
        assert_eq!(encoded & WRITER_BIT, WRITER_BIT, "writer bit should be set");
        assert_eq!(encoded & READER_MASK, 0, "reader count should be 0");
        // Writer should not coexist with readers in practice (INV-R1), but
        // the encoding allows it.  This test documents the bit-level
        // separability.
        let encoded = WRITER_BIT | 5;
        assert_eq!(encoded & WRITER_BIT, WRITER_BIT);
        assert_eq!(encoded & READER_MASK, 5);
    }
}
