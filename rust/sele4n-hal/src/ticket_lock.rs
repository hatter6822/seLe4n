// SPDX-License-Identifier: GPL-3.0-or-later
//! TicketLock — FIFO spinlock with bounded wait.
//!
//! **WS-SM SM2.B.16**: Rust implementation refining the Lean operational
//! specification at `SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean`.
//! The refinement is structural: every Rust state mutation corresponds
//! to a Lean `applyOp` / `releaseAndPromote` transition, and the Rust
//! invariants match the eight wf conjuncts (INV-T1..T8).
//!
//! ## Operational mapping
//!
//! | Rust | Lean spec |
//! |------|-----------|
//! | `TicketLock::new` | `TicketLockState.unheld` |
//! | `acquire` | `applyOp .tryAcquire` + spin on `observeServing` |
//! | `release` | `releaseAndPromote core` |
//! | `next_ticket: AtomicU64` | `TicketLockState.nextTicket: Nat` |
//! | `serving: AtomicU64` | `TicketLockState.serving: Nat` |
//!
//! The Lean spec models `pending` and `held` explicitly because abstract
//! reasoning requires them; the Rust impl tracks them implicitly through
//! the gap between `next_ticket` and `serving`.  The refinement φ between
//! the two representations (SM2.D, post-1.0) will be a structural
//! simulation argument tying each atomic op to its Lean counterpart.
//!
//! ## ARM ARM citations
//!
//! * `next_ticket.fetch_add(1, Acquire)` — `LDADDA` (ARM ARM C6.2.116):
//!   atomic load + add + store with acquire semantics.  Captures the
//!   ticket atomically; on ARMv8.1-A LSE this is one instruction.
//! * `serving.load(Acquire)` — `LDAR` (ARM ARM C6.2.142): acquire-load
//!   that synchronises-with the release-store that produced the value.
//!   The acquire-load establishes a happens-before edge from the prior
//!   holder's critical section to the new holder.
//! * `serving.fetch_add(1, Release)` — `STADDL` (ARM ARM C6.2.305):
//!   release-store that publishes every prior write on the releasing
//!   core to any acquire-load that observes the new value.
//! * `sev` — `SEV` (ARM ARM C6.2.243): hint instruction that sets the
//!   local event register on every PE in the inner-shareable domain.
//!   Wakes spin-waiters parked on `wfe`.
//!
//! ## Cache-line alignment
//!
//! `#[repr(C, align(64))]` guarantees the lock occupies a single cache
//! line, eliminating false sharing with adjacent data.  On Cortex-A76
//! (BCM2712, RPi5) the L1 cache line size is 64 bytes; the alignment
//! ensures `next_ticket` and `serving` share a line, so an atomic
//! `fetch_add` on either does not invalidate neighboring cache lines.
//!
//! ## Bounded WFE
//!
//! The spin-loop uses `wfe_bounded` instead of a bare busy-wait so that
//! a parked PE wakes within `WFE_DEFAULT_TIMEOUT_TICKS` ticks (10 ms at
//! 54 MHz) even if a `sev` is missed.  The Lean spec's
//! `ticketLock_bounded_wait` theorem proves that the queue has at most
//! `numCores - 1` other waiters ahead; combined with a critical section
//! bound `T_cs`, this gives WCRT(acquire) ≤ (numCores - 1) × T_cs.

use core::sync::atomic::{AtomicU64, Ordering};

/// **WS-SM SM2.B.16**: FIFO spinlock with bounded wait.
///
/// Refines the abstract `TicketLockState` from
/// `SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean`.
///
/// The two atomic fields correspond directly to the Lean spec's
/// `nextTicket` and `serving` counters; `pending` and `held` are
/// implicit (tracked through the gap between the two counters and
/// the per-core captured ticket in CPU register state).
///
/// # Safety
///
/// `TicketLock` is `Sync` because both atomic operations
/// (`fetch_add`, `load`) are inherently concurrent-safe.  Multiple
/// cores can call `acquire` / `release` from different threads.
///
/// The lock holder must call `release` exactly once after `acquire`.
/// Using the `with_lock` RAII combinator is preferred to avoid
/// forgetting `release` on early returns or panics.
#[repr(C, align(64))]
pub struct TicketLock {
    /// Monotone counter: the next ticket to be issued.
    ///
    /// Each `acquire` calls `fetch_add(1, Acquire)` to atomically
    /// capture the current value and increment for the next acquirer.
    /// Refines `TicketLockState.nextTicket : Nat`.
    next_ticket: AtomicU64,
    /// Monotone counter: the ticket currently being served.
    ///
    /// Released by `release` via `fetch_add(1, Release)`.  Read by
    /// `acquire`'s spin-loop via `load(Acquire)` to detect when its
    /// captured ticket is being served.  Refines
    /// `TicketLockState.serving : Nat`.
    serving: AtomicU64,
}

impl TicketLock {
    /// **WS-SM SM2.B.16**: construct a new, unheld TicketLock.
    ///
    /// Refines `TicketLockState.unheld` from the Lean spec: both
    /// counters start at zero, the implicit `pending` queue is empty,
    /// and no core holds the lock.
    ///
    /// The constructor is `const fn` so `TicketLock`s can be embedded
    /// in `static` declarations for global per-object locks (SM3).
    #[must_use]
    pub const fn new() -> Self {
        Self {
            next_ticket: AtomicU64::new(0),
            serving: AtomicU64::new(0),
        }
    }

    /// **WS-SM SM2.B.16**: acquire the lock, returning the captured ticket.
    ///
    /// Refines the Lean operation
    /// `applyOp .tryAcquire core` followed by repeated
    /// `applyOp .observeServing core obs` until `obs = captured_ticket`.
    ///
    /// # Algorithm
    ///
    /// 1. `fetch_add(1, Acquire)` on `next_ticket` to atomically
    ///    capture this caller's ticket and increment the counter.
    ///    Refines the abstract `captureTicket` step.
    /// 2. Spin until `serving.load(Acquire) == my_ticket`.  Each
    ///    iteration calls `wfe_bounded` to park the PE in a
    ///    low-power state until either a `sev` arrives (typically
    ///    from another core's `release`) or the WFE timeout
    ///    elapses.  Refines the abstract
    ///    `applyOp .observeServing` iterations.
    /// 3. Return the captured ticket.  The caller must pass this to
    ///    `release` (or use `with_lock` to handle the lifecycle).
    ///
    /// # FIFO guarantee
    ///
    /// By the Lean spec's `ticketLock_fifo` theorem, captures observe
    /// strictly-increasing tickets: if core C₁ captures at time t₁
    /// and core C₂ at time t₂ > t₁, then C₁'s ticket < C₂'s ticket.
    /// Since `serving` is incremented exactly once per release,
    /// captures are served in capture order.
    ///
    /// # Bounded wait
    ///
    /// By `ticketLock_bounded_wait`, the captured ticket is at most
    /// `numCores - 1` away from the current serving value.  Combined
    /// with a critical section bound `T_cs`, this gives
    /// WCRT(acquire) ≤ (numCores - 1) × T_cs.
    ///
    /// # Release-acquire pairing
    ///
    /// The `Acquire` ordering on the spin-loop's `serving.load`
    /// pairs with the `Release` ordering on the prior holder's
    /// `serving.fetch_add(1, Release)` in `release()`.  This
    /// `synchronizesWith` edge (per the Lean spec's
    /// `ticketLock_release_acquire_pairing`) propagates the prior
    /// holder's writes to the new holder before any critical-section
    /// code runs.
    pub fn acquire(&self) -> u64 {
        // Step 1: capture ticket via atomic fetch-add with Acquire ordering.
        let my_ticket = self.next_ticket.fetch_add(1, Ordering::Acquire);
        // Step 2: spin until our ticket is being served.
        while self.serving.load(Ordering::Acquire) != my_ticket {
            crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
        }
        // Step 3: return captured ticket.
        my_ticket
    }

    /// **WS-SM SM2.B.16**: release the lock.
    ///
    /// Refines the Lean operation `releaseAndPromote core`: advances
    /// `serving` by 1 (publishing the prior holder's writes) and
    /// broadcasts `sev` to wake any waiters.
    ///
    /// # Algorithm
    ///
    /// 1. `fetch_add(1, Release)` on `serving` to atomically advance
    ///    the counter and publish prior writes.  This step alone is
    ///    sufficient on a polled spin-wait — the next waiter's
    ///    `load(Acquire)` will observe the new value.
    /// 2. `sev` broadcasts an event to every PE in the inner-shareable
    ///    domain, waking any waiters parked on `wfe`.  Without this,
    ///    waiters could remain parked until their `wfe_bounded` timeout
    ///    expires (10 ms at 54 MHz), introducing avoidable latency.
    ///
    /// # Atomicity
    ///
    /// The two steps (fetch_add + sev) are NOT a single atomic op,
    /// but the kernel's invariant is preserved either way:
    /// * If `sev` arrives at a waiter BEFORE the waiter's `wfe`: the
    ///   waiter's local event register is already set, so `wfe`
    ///   returns immediately.
    /// * If `sev` arrives AFTER the waiter's `wfe`: the waiter wakes
    ///   from the `sev` immediately.
    /// * If the `sev` is missed entirely (impossible on RPi5's
    ///   single-cluster topology, but defensive): the waiter wakes
    ///   from its `wfe_bounded` timeout and re-checks `serving`.
    ///
    /// # Refinement
    ///
    /// The Lean spec's `releaseAndPromote` is a composed step that
    /// includes the promotion of the next pending entry.  On the
    /// abstract side, the promotion sets `held := some next_waiter`.
    /// On the concrete side, the next waiter's spin-loop observes
    /// the new `serving` value and exits — the "promotion" happens
    /// implicitly in the waiter's code, not in this `release`.  This
    /// is operationally equivalent to the Lean spec's atomic
    /// composition (the abstract observation is what makes the
    /// abstract promotion explicit; the concrete representation
    /// elides the explicit holder).
    pub fn release(&self) {
        // Step 1: release-store on `serving` to advance and publish writes.
        self.serving.fetch_add(1, Ordering::Release);
        // Step 2: SEV to wake any waiters parked on WFE.
        crate::cpu::sev();
    }

    /// **WS-SM SM2.B.16**: RAII combinator — acquire, execute, release.
    ///
    /// Acquires the lock, runs the closure `f`, and releases the lock
    /// on normal return.  Panics in the closure propagate through Drop
    /// on the guard, so the lock is still released on a panic-unwind
    /// (when panics are unwound rather than aborting).
    ///
    /// This is the preferred way to use the lock — it eliminates the
    /// possibility of forgetting `release` on early returns.
    ///
    /// # Example
    ///
    /// ```ignore
    /// static LOCK: TicketLock = TicketLock::new();
    /// LOCK.with_lock(|| {
    ///     // Critical section.
    ///     // Lock is automatically released when this closure returns.
    /// });
    /// ```
    pub fn with_lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let _guard = TicketLockGuard::acquire(self);
        f()
    }
}

/// **WS-SM SM2.B.16**: RAII guard for `TicketLock`.
///
/// Holds the lock for the lifetime of the guard.  On `Drop`, calls
/// `release()` automatically.  Use via `TicketLock::with_lock` rather
/// than constructing directly.
///
/// # Lifetime invariant
///
/// The guard's `'a` lifetime parameter ties the guard to the lock
/// instance, so Rust's borrow checker prevents the lock from being
/// dropped while a guard exists.  This is a stronger guarantee than
/// the Lean spec's `mutex` theorem provides at the kernel-state
/// level — the Rust type system enforces single-ownership statically.
pub struct TicketLockGuard<'a> {
    lock: &'a TicketLock,
    /// Captured ticket, retained for diagnostic / debugging purposes.
    /// Not used in the release path (which always increments `serving`
    /// regardless of which holder is releasing).
    _ticket: u64,
}

impl<'a> TicketLockGuard<'a> {
    /// **WS-SM SM2.B.16**: acquire the lock and return a guard.
    ///
    /// Calls `lock.acquire()`; the returned guard holds the lock
    /// until dropped.
    pub fn acquire(lock: &'a TicketLock) -> Self {
        let ticket = lock.acquire();
        Self { lock, _ticket: ticket }
    }

    /// **WS-SM SM2.B.16**: get the captured ticket for diagnostic use.
    #[must_use]
    pub fn ticket(&self) -> u64 {
        self._ticket
    }
}

impl<'a> Drop for TicketLockGuard<'a> {
    /// **WS-SM SM2.B.16**: release the lock on guard drop.
    ///
    /// Calls `self.lock.release()`.  Drop semantics guarantee this
    /// runs on normal return AND on panic-unwind, so the lock is
    /// never permanently held even if the critical section panics.
    fn drop(&mut self) {
        self.lock.release();
    }
}

impl Default for TicketLock {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// SM2.B.16 unit tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::{align_of, size_of};

    /// **SM2.B.16 test**: new TicketLock has both counters at zero.
    #[test]
    fn sm2b16_new_initial_state() {
        let lock = TicketLock::new();
        assert_eq!(lock.next_ticket.load(Ordering::Acquire), 0);
        assert_eq!(lock.serving.load(Ordering::Acquire), 0);
    }

    /// **SM2.B.16 test**: first acquire returns ticket 0.
    #[test]
    fn sm2b16_first_acquire_returns_zero() {
        let lock = TicketLock::new();
        let ticket = lock.acquire();
        assert_eq!(ticket, 0);
    }

    /// **SM2.B.16 test**: first acquire increments next_ticket to 1.
    #[test]
    fn sm2b16_acquire_increments_next_ticket() {
        let lock = TicketLock::new();
        let _ = lock.acquire();
        assert_eq!(lock.next_ticket.load(Ordering::Acquire), 1);
    }

    /// **SM2.B.16 test**: release increments serving by 1.
    #[test]
    fn sm2b16_release_increments_serving() {
        let lock = TicketLock::new();
        let _ = lock.acquire();
        lock.release();
        assert_eq!(lock.serving.load(Ordering::Acquire), 1);
    }

    /// **SM2.B.16 test**: full acquire-release cycle returns to ready state.
    ///
    /// After acquire + release, both counters are 1 and a new acquire
    /// captures ticket 1 (not 0 — the previous ticket was consumed).
    #[test]
    fn sm2b16_acquire_release_acquire() {
        let lock = TicketLock::new();
        let t1 = lock.acquire();
        lock.release();
        let t2 = lock.acquire();
        assert_eq!(t1, 0);
        assert_eq!(t2, 1);
    }

    /// **SM2.B.16 test**: with_lock executes the closure.
    #[test]
    fn sm2b16_with_lock_executes_closure() {
        let lock = TicketLock::new();
        let result = lock.with_lock(|| 42);
        assert_eq!(result, 42);
    }

    /// **SM2.B.16 test**: with_lock releases the lock on normal return.
    #[test]
    fn sm2b16_with_lock_releases_on_return() {
        let lock = TicketLock::new();
        lock.with_lock(|| {});
        // serving incremented to 1 after release.
        assert_eq!(lock.serving.load(Ordering::Acquire), 1);
        // next_ticket also at 1 after one acquire.
        assert_eq!(lock.next_ticket.load(Ordering::Acquire), 1);
    }

    /// **SM2.B.16 test**: with_lock supports nested operations on
    /// a different lock (no deadlock potential since each lock is
    /// independent).
    #[test]
    fn sm2b16_with_lock_nested_distinct_locks() {
        let lock_a = TicketLock::new();
        let lock_b = TicketLock::new();
        let result = lock_a.with_lock(|| lock_b.with_lock(|| 7));
        assert_eq!(result, 7);
        // Both locks released.
        assert_eq!(lock_a.serving.load(Ordering::Acquire), 1);
        assert_eq!(lock_b.serving.load(Ordering::Acquire), 1);
    }

    /// **SM2.B.16 test**: TicketLockGuard exposes the captured ticket.
    #[test]
    fn sm2b16_guard_exposes_ticket() {
        let lock = TicketLock::new();
        // First acquire captures ticket 0.
        {
            let guard = TicketLockGuard::acquire(&lock);
            assert_eq!(guard.ticket(), 0);
        }
        // Second acquire captures ticket 1.
        {
            let guard = TicketLockGuard::acquire(&lock);
            assert_eq!(guard.ticket(), 1);
        }
    }

    /// **SM2.B.16 test**: cache-line alignment.
    ///
    /// The `#[repr(C, align(64))]` attribute guarantees the lock
    /// occupies a single 64-byte cache line.  This eliminates false
    /// sharing with adjacent data.
    #[test]
    fn sm2b16_cache_line_aligned() {
        assert_eq!(align_of::<TicketLock>(), 64);
        // Size is at least 16 bytes (two u64 fields) and at most 64
        // (the alignment).  The exact size depends on Rust's layout
        // decisions but must be ≤ 64.
        assert!(size_of::<TicketLock>() >= 16);
        assert!(size_of::<TicketLock>() <= 64);
    }

    /// **SM2.B.16 test**: const constructor is usable in static context.
    ///
    /// This is a compile-time check: if `TicketLock::new()` weren't
    /// `const fn`, the `static` declaration would fail to compile.
    #[test]
    fn sm2b16_const_constructor_in_static() {
        static GLOBAL_LOCK: TicketLock = TicketLock::new();
        // Verify the static is usable.
        assert_eq!(GLOBAL_LOCK.next_ticket.load(Ordering::Acquire), 0);
        assert_eq!(GLOBAL_LOCK.serving.load(Ordering::Acquire), 0);
    }

    /// **SM2.B.16 test**: Default implementation matches new().
    #[test]
    fn sm2b16_default_matches_new() {
        let lock_default = TicketLock::default();
        let lock_new = TicketLock::new();
        assert_eq!(
            lock_default.next_ticket.load(Ordering::Acquire),
            lock_new.next_ticket.load(Ordering::Acquire)
        );
        assert_eq!(
            lock_default.serving.load(Ordering::Acquire),
            lock_new.serving.load(Ordering::Acquire)
        );
    }

    /// **SM2.B.16 test**: signature pinning — `new` is `const fn`.
    ///
    /// Forces a const-context evaluation; a non-const constructor
    /// would fail to compile.
    ///
    /// Uses `static` (not `const`) so clippy's
    /// `declare_interior_mutable_const` lint is satisfied — atomics
    /// are interior-mutable types, and clippy correctly prefers
    /// `static` for them.  The `static` binding is just as effective
    /// as a const binding at proving `new()` is `const fn`: a
    /// non-const constructor would fail to compile in either context.
    #[test]
    fn sm2b16_new_is_const_fn() {
        static _LOCK_AS_STATIC: TicketLock = TicketLock::new();
    }

    /// **SM2.B.16 test**: FIFO ordering at the level of two
    /// sequential acquires.
    ///
    /// After acquire-release-acquire-release, the captured tickets
    /// are 0 and 1 (the second is later than the first).  This is
    /// the local-thread analog of the Lean spec's `ticketLock_fifo`
    /// theorem.
    #[test]
    fn sm2b16_sequential_acquires_have_fifo_tickets() {
        let lock = TicketLock::new();
        let t1 = lock.acquire();
        lock.release();
        let t2 = lock.acquire();
        lock.release();
        let t3 = lock.acquire();
        lock.release();
        assert_eq!(t1, 0);
        assert_eq!(t2, 1);
        assert_eq!(t3, 2);
        // After three acquire-release cycles, both counters are at 3.
        assert_eq!(lock.next_ticket.load(Ordering::Acquire), 3);
        assert_eq!(lock.serving.load(Ordering::Acquire), 3);
    }

    /// **SM2.B.16 test**: with_lock + with_lock on the SAME lock
    /// (sequential, not nested).
    ///
    /// Verifies the lock can be re-used after release.
    #[test]
    fn sm2b16_sequential_with_lock() {
        let lock = TicketLock::new();
        let a = lock.with_lock(|| 1);
        let b = lock.with_lock(|| 2);
        let c = lock.with_lock(|| 3);
        assert_eq!(a, 1);
        assert_eq!(b, 2);
        assert_eq!(c, 3);
        // After three acquire-release cycles, both counters at 3.
        assert_eq!(lock.next_ticket.load(Ordering::Acquire), 3);
        assert_eq!(lock.serving.load(Ordering::Acquire), 3);
    }

    /// **SM2.B.16 test**: signature pinning — public API (non-guard methods).
    ///
    /// Records the canonical signatures of every public function on
    /// `TicketLock` itself.  A future refactor that changes a signature
    /// must update this test, surfacing the API change at review time.
    ///
    /// The `TicketLockGuard` methods are not pinned here because
    /// their lifetime parameters resist `fn` pointer coercion in
    /// stable Rust; they are exercised at runtime by
    /// `sm2b16_guard_exposes_ticket` and `sm2b16_with_lock_*`.
    #[test]
    fn sm2b16_public_api_signature_pin() {
        let _new: fn() -> TicketLock = TicketLock::new;
        let _acquire: fn(&TicketLock) -> u64 = TicketLock::acquire;
        let _release: fn(&TicketLock) = TicketLock::release;
    }

    /// **SM2.B.16 test**: many short acquire-release cycles produce
    /// monotone counters.
    ///
    /// 100 cycles of acquire-release should leave both counters at 100.
    #[test]
    fn sm2b16_many_cycles_monotone() {
        let lock = TicketLock::new();
        for i in 0..100u64 {
            let t = lock.acquire();
            assert_eq!(t, i);
            lock.release();
        }
        assert_eq!(lock.next_ticket.load(Ordering::Acquire), 100);
        assert_eq!(lock.serving.load(Ordering::Acquire), 100);
    }
}
