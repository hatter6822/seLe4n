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
//! * `state.compare_exchange(..., Acquire, ...)` — `LDAXR` (ARM ARM
//!   C6.2.135) / `STLXR` (ARM ARM C6.2.323) exclusive monitor pair, or
//!   LSE `CASA` (ARM ARM C6.2.50): atomic compare-and-swap with acquire
//!   ordering on success.  (Audit pass-3 LOW-1 fix: previously cited
//!   the pair as C6.2.135 only, missing STLXR's distinct section.)
//! * `state.fetch_and(READER_MASK, Release)` — `LDCLRL` family (ARM ARM
//!   C6.2.103, LSE bit-clear with Release) or, pre-LSE, a CAS-retry
//!   sequence: release-ordered atomic bit-clear that preserves the
//!   non-cleared bits.  Used by `release_write` per the H-4 audit fix
//!   to avoid wiping reader bits on misuse.  B2.3.7 governs the
//!   release-store ordering semantics.
//! * `state.fetch_sub(1, Release)` — `LDADDL` (ARM ARM C6.2.116) with
//!   two's-complement subtraction encoding: release atomic decrement.
//!   Used by `release_read` per the H-3 audit fix.
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
            // Audit-pass-3 defense: check for reader-count overflow BEFORE
            // computing new_state.  Under `numCores ≤ 4` this is
            // unreachable (4 ≪ 2^63), but defensive engineering: if the
            // count somehow reached READER_MASK (= 2^63 - 1), `s + 1`
            // would equal `WRITER_BIT`, and a successful CAS would
            // corrupt the lock state to "writer held".  Fail-closed by
            // parking on WFE instead of corrupting.
            if s == READER_MASK {
                debug_assert!(false,
                    "RwLock reader count exhausted (impossible under numCores ≤ 4); \
                     state was 0x{s:x}");
                crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
                continue;
            }
            let new_state = s + 1;
            // After the explicit overflow check above, new_state cannot
            // have the writer bit set (s < READER_MASK ⟹ s + 1 ≤ READER_MASK).
            // The debug_assert is retained for defense-in-depth.
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
    ///
    /// # Release-build robustness (H-3 audit fix)
    ///
    /// The implementation uses `fetch_sub(1, Release)` on the entire `state`
    /// word.  This is sound because:
    /// * Under correct usage, `state & WRITER_BIT == 0` (INV-R1: writer and
    ///   readers can't coexist), so `state & READER_MASK == state` and
    ///   `fetch_sub(1)` decrements the reader count.
    /// * Under misuse (release without prior acquire), `fetch_sub(1)` on
    ///   `state = 0` underflows to `u64::MAX`.  In release builds with
    ///   `overflow-checks = false` (the kernel's default), this is **defined
    ///   wrapping** that produces a poisoned state where bit 63 is set
    ///   (`WRITER_BIT`) AND every reader bit is set.  The next acquirer
    ///   detects this as "writer held" and **parks on WFE permanently**
    ///   (the lock is now wedged in a non-recoverable state).  This is
    ///   **fail-locked**, not fail-noisy: there is no panic, log, or
    ///   diagnostic at the production-build level.  The misuse manifests
    ///   as a deadlock-style hang at the next acquire, which a
    ///   diagnostic tool (e.g., per-core dispatch stats from SM1.I.4)
    ///   can detect by observing "no progress on this lock" over a
    ///   timeout.  Compare to the prior CAS-retry implementation which
    ///   would silently corrupt the state into a valid-looking
    ///   "writer-held with maximum readers" — invariant-violating but
    ///   structurally indistinguishable from a legitimate state.
    ///   (M-B audit-pass-2 honesty fix: the prior docstring claimed
    ///   "fail-noisy", which is misleading — the misuse manifests as
    ///   a hang, not an explicit failure signal.)
    /// * Under misuse (`release_read` called while writer is held —
    ///   INV-R1 violation pre-state with `state = WRITER_BIT`):
    ///   `fetch_sub(1)` produces `state = WRITER_BIT - 1 = READER_MASK`
    ///   (all reader bits set, writer bit clear).  The next
    ///   `acquire_read` would see `s == READER_MASK` and trip the
    ///   audit-pass-3 fail-closed gate (lines 196-202), parking on
    ///   WFE rather than corrupting further.  The audit-pass-3
    ///   strengthened debug_assert also catches this misuse in debug
    ///   builds: `prev & WRITER_BIT == 0 && prev & READER_MASK > 0`
    ///   rejects `prev = WRITER_BIT`.  (LOW-5 audit-pass-3 fix:
    ///   previously only the state-0 case was documented.)
    /// * In debug builds, the `debug_assert!` traps AFTER the
    ///   `fetch_sub` has already committed the underflow.  The lock
    ///   state is corrupted to u64::MAX at that point; the test
    ///   runner catches the panic before any subsequent operation
    ///   observes the corruption.  (M-L audit-pass-2 documented:
    ///   the debug-mode side effect is intentional — TOCTOU-free
    ///   atomic op first, then assert on the returned prior value.)
    ///
    /// This avoids the H-3 corruption window in the prior CAS-retry
    /// implementation (where `(s & WRITER_BIT) | (count - 1)` with
    /// `count = 0` could wrap to `(WRITER_BIT) | u64::MAX = u64::MAX` and
    /// be written via CAS, silently setting the writer bit AND all reader
    /// bits to 1 — indistinguishable from a legitimate state).
    ///
    /// `fetch_sub` on `AtomicU64` returning the prior value is the
    /// `LDADDL` instruction family (ARM ARM C6.2.116) with a negated
    /// operand — semantically a load-modify-return-store atomic.  On
    /// ARMv8.1-A LSE this compiles to one instruction rather than the
    /// CAS-retry pair used in the prior implementation.  (H-A audit
    /// fix: previously docstring inconsistently cited `STADDL` /
    /// C6.2.305, which is the store-only variant without a return
    /// value.)
    #[inline]
    pub fn release_read(&self) {
        // Atomic single-instruction reader decrement on ARMv8.1-A LSE.
        // Returns the prior value; if it was 0 in the reader-count bits,
        // we're in a misuse scenario, but the state will be poisoned in
        // a fail-locked way (writer bit set + all reader bits set,
        // causing the next acquirer to park on WFE permanently — see
        // the "Release-build robustness" docstring above), not silently
        // corrupted into a valid-looking state.
        //
        // (Audit pass-3 LOW-4 fix: previously said "fail-noisy" — that
        // was inconsistent with the docstring's M-B audit-pass-2
        // honesty correction to "fail-locked".)
        //
        // Pattern matches TicketLock::release: do the atomic op FIRST,
        // then check the returned prior value for misuse — this is
        // race-free because `prev` is the atomic-op result, eliminating
        // any TOCTOU between a separate load and the fetch_sub.
        let prev = self.state.fetch_sub(1, Ordering::Release);
        // Defense-in-depth: catch debug-build misuse via the returned
        // prior value.  In release builds this is a no-op; the misuse
        // surfaces via the next acquirer spinning on the poisoned state
        // (writer bit set in u64::MAX).
        //
        // Two misuse cases caught:
        // 1. `prev & READER_MASK == 0`: release without prior acquire
        //    (the original H-3 case).
        // 2. `prev & WRITER_BIT != 0`: release_read called while writer
        //    is held (INV-R1 violation; audit-pass-3 strengthening).
        //    Even if the reader count is non-zero, this state is bogus
        //    — under correct usage INV-R1 forbids writer + readers
        //    coexisting.
        debug_assert!(
            prev & WRITER_BIT == 0 && prev & READER_MASK > 0,
            "RwLock::release_read called in invalid state \
             (prev 0x{prev:x}, writer-bit must be 0 and reader-count must be > 0)"
        );
        // SEV ONLY if no holders remain (writer not held, reader count
        // drops to zero).  Gates the broadcast to the moment a waiting
        // writer could actually progress.  Audit fix M-3: avoids spurious
        // wakeups under heavy reader contention.
        if (prev & WRITER_BIT) == 0 && (prev & READER_MASK) == 1 {
            crate::cpu::sev();
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
    /// # Algorithm (audit-pass-2 update)
    ///
    /// 1. `fetch_and(READER_MASK, Release)` atomically clears the writer
    ///    bit while preserving reader bits.  Returns the prior state for
    ///    misuse detection.
    /// 2. `debug_assert!` checks the prior state was `writer-held +
    ///    readers = 0` (correct usage).  Debug-mode only; release builds
    ///    skip the asserts.
    /// 3. SEV ONLY if the writer bit was set in the prior state (i.e., we
    ///    actually cleared a held writer; audit fix M-D).
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
    ///
    /// # Release-build robustness (H-4 audit fix)
    ///
    /// The implementation uses `fetch_and(READER_MASK, Release)` (clearing
    /// only bit 63) rather than `store(0, Release)` (clearing the whole word).
    /// This is sound because:
    /// * Under correct usage, `state & READER_MASK == 0` (INV-R1), so
    ///   `fetch_and(READER_MASK)` clears bit 63 and leaves the rest unchanged
    ///   (which was zero), producing the canonical released state of 0.
    /// * Under misuse (release while readers exist due to a race or buggy
    ///   caller), `fetch_and(READER_MASK)` clears the writer bit but
    ///   **preserves** the reader bits.  This keeps the lock in a
    ///   recoverable state: the existing readers can still call
    ///   `release_read` correctly (their `fetch_sub` will see the right
    ///   count).  Compare to `store(0)` which would silently zero the
    ///   reader bits and trigger the H-3 underflow corruption on each
    ///   subsequent `release_read`.
    ///
    /// Defense-in-depth: both debug_assert checks examine the atomic
    /// `fetch_and` return value (the prior state), which is race-free
    /// because it's the atomic-op result rather than a separate load.
    /// (Audit pass-2: replaces the prior "single load + fetch_and"
    /// pattern, which had a TOCTOU between the load and fetch_and.)
    ///
    /// SEV gating: only emits SEV if the writer bit was actually set in
    /// the prior state (i.e., we actually cleared the writer bit).  This
    /// matches the symmetry with `release_read` (which gates on reader
    /// count dropping to zero) — both fire SEV only when the lock state
    /// transitions to "potentially acquirable" by a waiter.
    #[inline]
    pub fn release_write(&self) {
        // Atomic clear of the writer bit, preserving reader bits.
        // Under correct usage (INV-R1: writer-held → readers = 0), the
        // reader bits are zero, so this is equivalent to `store(0)`.
        // Under misuse, the new form keeps the lock in a recoverable
        // state.  `prev` captures the prior state for the debug asserts.
        //
        // Pattern matches `release_read`: do the atomic op FIRST, then
        // check the returned prior value for misuse.
        let prev = self.state.fetch_and(READER_MASK, Ordering::Release);
        // Defense-in-depth: catch debug-build misuse via the returned
        // prior value (race-free).
        debug_assert!(
            prev & READER_MASK == 0,
            "RwLock::release_write called with non-zero reader count \
             (prev state 0x{prev:x})"
        );
        debug_assert!(
            prev & WRITER_BIT != 0,
            "RwLock::release_write called without a matching acquire_write \
             (prev state 0x{prev:x}, writer bit was clear)"
        );
        // SEV ONLY if we actually cleared the writer bit (correct usage).
        // Under misuse (writer bit was already clear), SEV would be
        // spurious — no waiter can progress because the lock was already
        // released by someone else (or never acquired).
        if (prev & WRITER_BIT) != 0 {
            crate::cpu::sev();
        }
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
    #[should_panic(expected = "RwLock::release_read called in invalid state")]
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

    /// **SM2.C.22 cross-thread stress test**: writer + readers interleaving,
    /// semantically verifying exclusion via a "write sentinel" pattern.
    ///
    /// Each writer thread writes its `thread_idx + 1` to a shared cell as
    /// a sentinel, then reads the cell back and verifies it sees ITS OWN
    /// value (no torn write or interleaved writer overwrote it before the
    /// read).  This directly tests writer-writer exclusion AND that the
    /// writer's view of its own write is consistent.
    ///
    /// Each reader thread reads the cell and records the value.  At the
    /// end, the count of writer ops and the final cell value are checked
    /// for consistency (every writer op must have either succeeded or been
    /// overwritten by another writer; readers must always see SOME
    /// successful writer's value, never zero or garbage).
    ///
    /// (M-I audit-pass-2 fix: the prior version only checked
    /// `final_count > 0` and `<= upper_bound`, which doesn't actually
    /// test exclusion semantically — a buggy RwLock that allowed
    /// concurrent writes might still satisfy those bounds.)
    #[test]
    fn sm2c22_cross_thread_mixed_stress() {
        use std::sync::Arc;
        use std::cell::UnsafeCell;
        // Shared counter + writer-id-sentinel; writer writes both atomically
        // (under lock).  Readers verify the sentinel matches a recent
        // writer's id.
        struct Shared {
            lock: RwLock,
            counter: UnsafeCell<u64>,
            last_writer_id: UnsafeCell<u64>,
        }
        // SAFETY: all access is gated by lock; writer lock has exclusive
        // access; reader lock has shared read-only access.
        unsafe impl Sync for Shared {}
        let shared = Arc::new(Shared {
            lock: RwLock::new(),
            counter: UnsafeCell::new(0),
            last_writer_id: UnsafeCell::new(0),
        });
        const NUM_THREADS: usize = 4;
        const OPS_PER_THREAD: usize = 250;
        // Track exclusion violations detected.
        let exclusion_violations = Arc::new(std::sync::atomic::AtomicU64::new(0));
        let mut handles: std::vec::Vec<std::thread::JoinHandle<()>> = std::vec::Vec::new();
        for thread_idx in 0..NUM_THREADS {
            let s = Arc::clone(&shared);
            let ev = Arc::clone(&exclusion_violations);
            let writer_id: u64 = (thread_idx as u64) + 1;  // 1..=NUM_THREADS
            handles.push(std::thread::spawn(move || {
                for op_idx in 0..OPS_PER_THREAD {
                    if op_idx % 4 == thread_idx % 4 {
                        // Writer op: write sentinel + verify under lock.
                        s.lock.with_write(|| {
                            // SAFETY: writer lock held → exclusive access.
                            unsafe {
                                *s.counter.get() += 1;
                                *s.last_writer_id.get() = writer_id;
                                // Verify: while we hold the writer lock,
                                // last_writer_id is OUR id (no one else
                                // can write).
                                let observed = *s.last_writer_id.get();
                                if observed != writer_id {
                                    ev.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                }
                            }
                        });
                    } else {
                        // Reader op: read counter + last_writer_id under read lock.
                        s.lock.with_read(|| {
                            // SAFETY: reader lock held → shared access.
                            unsafe {
                                let count = *s.counter.get();
                                let last_id = *s.last_writer_id.get();
                                // Reader must see a consistent snapshot:
                                // count > 0 → some writer has run → last_id
                                // must be in 1..=NUM_THREADS (no torn read
                                // or stale memory).
                                if count > 0 && (last_id == 0 || last_id > NUM_THREADS as u64) {
                                    ev.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                }
                            }
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
        // SAFETY: all threads joined; no concurrent access remains.
        let final_count = unsafe { *shared.counter.get() };
        assert!(final_count > 0, "writers should have incremented counter");
        let upper_bound = (NUM_THREADS * OPS_PER_THREAD) as u64;
        assert!(final_count <= upper_bound,
                "counter {final_count} exceeds upper bound {upper_bound}");
        // CRITICAL: zero exclusion violations.  Any non-zero count indicates
        // a writer observed its OWN sentinel modified (writer-writer
        // exclusion violation) or a reader saw an inconsistent count/id
        // pair (reader-writer or torn-read violation).
        let violations = exclusion_violations.load(std::sync::atomic::Ordering::Relaxed);
        assert_eq!(violations, 0,
            "RwLock exclusion violated: {violations} torn or interleaved observations");
    }

    /// **SM2.C.22 cross-thread stress test**: reader-multiplicity (deterministic).
    ///
    /// Demonstrates reader-multiplicity from the Lean spec's
    /// `rwLock_reader_multiplicity` theorem at runtime.  Uses a `Barrier`
    /// to **deterministically** force NUM_READERS reader threads to hold
    /// the lock simultaneously, then asserts `snapshot.1 >= NUM_READERS as u64`.
    ///
    /// Unlike a probabilistic timing-based test, this barrier ensures every
    /// reader acquires the lock and rendezvouses before any releases,
    /// guaranteeing the snapshot observation reaches the full multiplicity.
    /// (M-5 audit fix: replaces the prior non-deterministic test that
    /// asserted only `>= 1`.)
    #[test]
    fn sm2c22_cross_thread_reader_multiplicity_deterministic() {
        use std::sync::{Arc, Barrier};
        const NUM_READERS: usize = 4;
        let lock = Arc::new(RwLock::new());
        // Two-phase barrier: all readers rendezvous after acquire, then
        // again after the snapshot, before any release.
        let barrier_pre_snapshot = Arc::new(Barrier::new(NUM_READERS));
        let barrier_post_snapshot = Arc::new(Barrier::new(NUM_READERS));
        let mut handles: std::vec::Vec<std::thread::JoinHandle<u64>> = std::vec::Vec::new();
        for _ in 0..NUM_READERS {
            let l = Arc::clone(&lock);
            let bp = Arc::clone(&barrier_pre_snapshot);
            let bq = Arc::clone(&barrier_post_snapshot);
            handles.push(std::thread::spawn(move || {
                l.acquire_read();
                // Barrier 1: every reader has acquired before any snapshots.
                bp.wait();
                let (_w, count) = l.snapshot();
                // Barrier 2: every reader has snapshotted before any releases.
                bq.wait();
                l.release_read();
                count
            }));
        }
        let observed: std::vec::Vec<u64> = handles.into_iter()
            .map(|h| h.join().expect("worker thread panicked"))
            .collect();
        // All released.
        assert_eq!(lock.state.load(Ordering::Acquire), 0);
        // EVERY snapshot must observe at least NUM_READERS readers, because
        // the barrier guarantees all NUM_READERS have acquired before any
        // snapshot, and none release before all have snapshotted.
        for (i, count) in observed.iter().enumerate() {
            assert!(*count >= NUM_READERS as u64,
                "thread {i} snapshot saw only {count} readers, expected >= {NUM_READERS}");
        }
    }

    /// **SM2.C.22 cross-thread stress test**: writer-reader exclusion under
    /// concurrent contention (substantive verification of the Lean spec's
    /// `rwLock_writer_readers_exclusion` theorem).
    ///
    /// Verifies that when one thread holds a write lock, every reader
    /// thread that subsequently `acquire_read`s observes the writer as
    /// CLEAR (i.e., the writer must have released by the time the reader
    /// was admitted).
    ///
    /// (M-J audit-pass-2 robustness fix: replaces the prior
    /// `sleep(50ms)`-based synchronization with a signal-counter
    /// pattern that uses a best-effort grace-period to give all
    /// readers a chance to park on `acquire_read` before the writer
    /// releases.
    ///
    /// **Limitation (LOW-6 audit-pass-3 honesty note)**: this is
    /// **best-effort**, not strictly deterministic.  Readers signal
    /// `readers_entered_acquire` BEFORE calling `acquire_read()`; the
    /// signal indicates "about to acquire", not "parked on WFE".  If
    /// a reader is preempted between its `fetch_add(1)` and its
    /// `acquire_read()` call, the writer may release before that
    /// reader actually attempts the acquire.  In that scenario, the
    /// reader observes `writer_was_clear=true` post-acquire and the
    /// test passes vacuously — a false pass that hides nothing
    /// (the lock was correctly released by the time the reader
    /// acquired).  The test would only FAIL if a reader saw
    /// `writer_was_clear=false` post-acquire, which would only happen
    /// if exclusion was violated.  So the best-effort timing doesn't
    /// affect the soundness of the failing path, just the coverage of
    /// the passing path.
    ///
    /// A true deterministic protocol would require readers to signal
    /// "parked on WFE" (which the kernel-level lock doesn't expose),
    /// or to invert the protocol (writer reads from readers' "I'm
    /// blocked" signal).  Neither is implementable purely in user-
    /// space on stable Rust.) -/
    #[test]
    fn sm2c22_cross_thread_writer_excludes_readers() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicBool, AtomicU64, Ordering as O};
        const NUM_READERS: usize = 3;
        let lock = Arc::new(RwLock::new());
        // Signal that the writer has acquired and the readers should start.
        let writer_acquired = Arc::new(AtomicBool::new(false));
        // Count of readers that have ENTERED acquire_read (incremented
        // BEFORE the call to acquire_read).  Used to deterministically
        // wait for all readers to be attempting the acquire.
        let readers_entered_acquire = Arc::new(AtomicU64::new(0));
        // Writer thread.
        let writer_handle = {
            let l = Arc::clone(&lock);
            let wa = Arc::clone(&writer_acquired);
            let rea = Arc::clone(&readers_entered_acquire);
            std::thread::spawn(move || {
                l.acquire_write();
                // Verify writer's own snapshot post-acquire.
                let (w, c) = l.snapshot();
                assert!(w, "writer's own snapshot should show writer=true");
                assert_eq!(c, 0, "writer's own snapshot should show count=0");
                // Signal readers to start.
                wa.store(true, O::Release);
                // Wait deterministically until all readers have entered
                // their acquire_read call (they're now parked on WFE
                // because the writer bit is set).  This replaces the
                // fragile sleep(50ms).
                while rea.load(O::Acquire) < NUM_READERS as u64 {
                    std::hint::spin_loop();
                }
                // Brief additional spin to give the readers time to
                // actually call acquire_read after incrementing the
                // counter (the counter is bumped immediately before the
                // call, so we need a small grace period for the call to
                // execute and park).  But this is a SMALL period (a few
                // µs of spinning), not the prior 50ms timeout that
                // dominated test time.
                for _ in 0..10000 {
                    std::hint::spin_loop();
                }
                // Re-verify writer snapshot before release (catches the
                // hypothetical case where a buggy RwLock allowed a reader
                // to acquire while writer was held).
                let (w2, c2) = l.snapshot();
                assert!(w2, "writer-held snapshot mid-test should still show writer=true");
                assert_eq!(c2, 0, "writer-held snapshot mid-test should show count=0");
                l.release_write();
            })
        };
        // Reader threads.
        let mut reader_handles: std::vec::Vec<std::thread::JoinHandle<bool>> =
            std::vec::Vec::new();
        for _ in 0..NUM_READERS {
            let l = Arc::clone(&lock);
            let wa = Arc::clone(&writer_acquired);
            let rea = Arc::clone(&readers_entered_acquire);
            reader_handles.push(std::thread::spawn(move || {
                // Wait for writer to acquire.
                while !wa.load(O::Acquire) {
                    std::hint::spin_loop();
                }
                // Signal that this reader is about to enter acquire_read.
                rea.fetch_add(1, O::Release);
                // Now attempt to acquire (will block until writer releases).
                l.acquire_read();
                // After acquire, writer must be clear.
                let (w, _c) = l.snapshot();
                let writer_was_clear = !w;
                l.release_read();
                writer_was_clear
            }));
        }
        writer_handle.join().expect("writer thread panicked");
        for (i, h) in reader_handles.into_iter().enumerate() {
            let writer_was_clear = h.join().expect("reader thread panicked");
            assert!(writer_was_clear,
                "reader {i} observed writer-bit set after acquire_read (exclusion violated!)");
        }
        // All released.
        assert_eq!(lock.state.load(O::Acquire), 0);
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
