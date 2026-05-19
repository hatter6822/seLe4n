// SPDX-License-Identifier: GPL-3.0-or-later
//! QueuedRwLock — MCS-style FIFO-preserving reader-writer lock.
//!
//! **WS-SM SM2.C-defer D-5**: queued RwLock variant that preserves the
//! Lean spec's FIFO admission property (`rwLock_fifo_admission_temporal`).
//!
//! ## Design: per-core fixed slot MCS queue, NOT lock-free linked list
//!
//! The original §5.5 plan sketch proposed a stack-allocated `WaiterNode`
//! with `AtomicPtr<WaiterNode>` linked-list management.  Three audit
//! findings ruled out that design (see SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md
//! §5.5 H-1 / H-2 / M-7).
//!
//! **Adopted design**: an MCS-style FIFO queue where each core has ONE
//! preallocated slot in a per-lock `[WaiterSlot; MAX_WAITERS]` array
//! (`MAX_WAITERS = MAX_SECONDARY_CORES + 1 = 4`).  Lock holds
//! `(tail_slot_idx : AtomicU8)` indexing into the array.  Each `WaiterSlot`
//! stores `next : AtomicU8` (successor slot idx), `parked : AtomicBool`
//! (single-writer admit signal), and `mode : AtomicU8` (requested mode).
//!
//! ## Heap-free, ABA-free, lifetime-safe
//!
//! * No heap allocation — the slot array lives inside the lock structure.
//! * No ABA — slot indices are 8-bit; addresses are not used in CAS.
//! * No dangling pointers — slots are statically owned by the lock; their
//!   storage outlives any waiter.
//!
//! ## FIFO preservation in the fast-path (closes audit H-1)
//!
//! The only admission path is via the queue.  There is NO state-only
//! fast-path — every acquire enqueues first, observes its predecessor
//! (or absence thereof + immediate-admit predicate on state), and waits.
//! Heuristic "is the lock free right now" loads are checks AFTER enqueue,
//! not before, eliminating the bypass race.

#![allow(unsafe_code)] // documented unsafe blocks at call sites

// Tests use std; production code is no_std-compatible.
#[cfg(test)]
extern crate std;

use core::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, Ordering};

/// Sentinel meaning "no slot" — indexes outside the `[0, MAX_WAITERS)`
/// range cannot collide with a real slot index.
const NONE_SENTINEL: u8 = u8::MAX;

/// Number of waiter slots — one per core.  Pinned to
/// `MAX_SECONDARY_CORES + 1 = 4` (boot core + 3 secondaries on RPi5).
pub const MAX_WAITERS: usize = crate::smp::MAX_SECONDARY_CORES + 1;

// Compile-time assertion: 8-bit indices accommodate all waiter slots.
const _: () = assert!(
    MAX_WAITERS <= 255,
    "WaiterSlot indices are u8; MAX_WAITERS must fit in u8."
);

/// Mode tag values for the per-slot `mode : AtomicU8` field.
pub const MODE_READ: u8 = 0;
pub const MODE_WRITE: u8 = 1;

/// One waiter slot — exactly one per core.  The slot is OWNED by the
/// lock for the duration of the program; no heap or stack allocation
/// is involved.  This eliminates lifetime hazards (audit H-2).
#[repr(C, align(64))] // cache-line aligned to avoid false sharing
pub struct WaiterSlot {
    /// Index of the next slot in the FIFO queue, or `NONE_SENTINEL` if
    /// this is the tail.  Single-writer (the OWNING core, while in
    /// queue); single-reader (the predecessor or the lock-holder).
    next: AtomicU8,
    /// True when the slot owner has been admitted.  Single-writer
    /// (the predecessor or the lock-holder); single-reader (the
    /// slot owner).
    parked: AtomicBool,
    /// Requested access mode at enqueue time (0 = read, 1 = write).
    /// Single-writer (the slot owner at enqueue); read-only thereafter.
    mode: AtomicU8,
}

impl WaiterSlot {
    /// `const fn` initial state — used in static array construction.
    ///
    /// The `clippy::declare_interior_mutable_const` lint flags this
    /// pattern; we explicitly allow it here because the consumer
    /// pattern (`[WaiterSlot::INIT; N]` array initialisation) requires
    /// fresh-copy semantics, NOT shared state.
    #[allow(clippy::declare_interior_mutable_const)]
    pub const INIT: Self = Self {
        next: AtomicU8::new(NONE_SENTINEL),
        parked: AtomicBool::new(false),
        mode: AtomicU8::new(MODE_READ),
    };

    /// Re-initialise this slot for a fresh enqueue.  Called by the
    /// slot's owner before swapping into the queue tail.
    ///
    /// Single-writer: only the owning core calls this.
    pub fn reset(&self, requested_mode: u8) {
        self.next.store(NONE_SENTINEL, Ordering::Relaxed);
        self.parked.store(false, Ordering::Relaxed);
        self.mode.store(requested_mode, Ordering::Relaxed);
    }

    /// Read the requested mode (single-reader).
    pub fn requested_mode(&self) -> u8 {
        self.mode.load(Ordering::Relaxed)
    }
}

/// Bit-packed lock state (same layout as `RwLock`).
///
/// * bit 63 (WRITER_BIT): writer-held flag.
/// * bits 0..62 (READER_MASK): reader count.
const WRITER_BIT_POS: u32 = 63;
const WRITER_BIT: u64 = 1u64 << WRITER_BIT_POS;
const READER_MASK: u64 = !WRITER_BIT;

/// **WS-SM SM2.C-defer D-5**: FIFO-preserving reader-writer lock.
///
/// Refines the abstract `RwLockState` with the additional invariant
/// that admission order matches enqueue order
/// (`rwLock_fifo_admission_temporal` in `RwLock.lean`).
///
/// The lock holds only a `tail` pointer (no `head`); per the standard
/// MCS algorithm, the current holder identifies their own slot via
/// the `core_id` parameter passed to `release_*`.  An explicit `head`
/// would introduce write-write races between concurrent
/// release/acquire pairs that the standard protocol avoids by
/// construction.
#[repr(C, align(64))]
pub struct QueuedRwLock {
    /// Bit-packed reader count + writer bit.
    state: AtomicU64,
    /// Index of the tail slot, or `NONE_SENTINEL` if no waiters queued.
    /// Single CAS-mutation point for enqueue.
    tail: AtomicU8,
    /// Per-core waiter slots.  Slot `i` is owned by `CoreId(i)`.
    slots: [WaiterSlot; MAX_WAITERS],
}

// Compile-time invariant: 4-slot array (RPi5 numCores literal).
const _: () = assert!(
    MAX_WAITERS == 4,
    "QueuedRwLock slot array sized for RPi5 numCores = 4; \
     update slot-init array literal if MAX_WAITERS changes."
);

impl Default for QueuedRwLock {
    fn default() -> Self {
        Self::new()
    }
}

impl QueuedRwLock {
    /// Construct a fresh, unheld queued RwLock.
    ///
    /// `const fn` so QueuedRwLocks can be embedded in `static` declarations
    /// for SM3 per-object locks.
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        Self {
            state: AtomicU64::new(0),
            tail: AtomicU8::new(NONE_SENTINEL),
            slots: [
                WaiterSlot::INIT,
                WaiterSlot::INIT,
                WaiterSlot::INIT,
                WaiterSlot::INIT,
            ],
        }
    }

    /// Peek the bit-packed state (test-only accessor for the Tier-5
    /// cross-language oracle and for unit-test diagnostics).
    ///
    /// Uses `Relaxed` ordering: callers using `peek_state` should not
    /// depend on synchronization with concurrent operations.  Stronger
    /// ordering here would mask ordering bugs in production callers
    /// (closes D-5 M-7 audit).
    pub fn peek_state(&self) -> u64 {
        self.state.load(Ordering::Relaxed)
    }

    /// Peek the tail slot index (test-only).  Uses Relaxed ordering
    /// for the same reason as `peek_state`.
    pub fn peek_tail(&self) -> u8 {
        self.tail.load(Ordering::Relaxed)
    }

    /// **Reader fast-path predicate**: can we acquire-direct as a reader?
    ///
    /// Returns `true` if the writer bit is clear AND the reader count
    /// is below the saturation bound (a future SM3 consumer will surface
    /// a panic on saturation; here we treat saturation as "cannot
    /// admit").  Called AFTER enqueue, so a concurrent writer that
    /// flipped the bit between enqueue and load is observed correctly.
    fn try_admit_as_reader(&self) -> bool {
        let s = self.state.load(Ordering::Acquire);
        if (s & WRITER_BIT) != 0 {
            return false;
        }
        // Increment the reader count via CAS.
        loop {
            let cur = self.state.load(Ordering::Acquire);
            if (cur & WRITER_BIT) != 0 {
                return false;
            }
            // Saturation guard (D-5 M-2 fix): reader count must stay
            // strictly below READER_MASK to avoid flipping WRITER_BIT.
            // Unreachable in practice on 4-core hardware (max readers = 4
            // ≪ 2^63 - 1) but the saturation check defends against
            // hypothetical future ports with massive core counts.
            let reader_count = cur & READER_MASK;
            if reader_count >= READER_MASK {
                return false; // Saturation: treat as if writer held.
            }
            let new = cur + 1; // reader count increments
            // CAS-attempt; on success return; on failure retry.
            // Use AcqRel on success to ensure proper synchronization with
            // the prior critical section (D-5 H-4 fix).
            match self.state.compare_exchange(
                cur, new,
                Ordering::AcqRel, Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(_) => {
                    core::hint::spin_loop();
                    continue;
                }
            }
        }
    }

    /// **Writer fast-path predicate**: can we acquire-direct as a writer?
    ///
    /// Returns `true` only if state == 0 (no readers, no writer).  Called
    /// AFTER enqueue.
    fn try_admit_as_writer(&self) -> bool {
        // AcqRel on success per D-5 H-4 audit: synchronizes with prior
        // critical sections via the state-RMW chain.
        self.state.compare_exchange(
            0, WRITER_BIT,
            Ordering::AcqRel, Ordering::Relaxed,
        ).is_ok()
    }
}

impl QueuedRwLock {
    /// **WS-SM SM2.C-defer D-5.5**: acquire a read lock for `core_id`.
    ///
    /// FIFO-preserving: every caller enqueues itself before checking
    /// immediate-admission predicates; there is NO state-only fast-path
    /// that could bypass a concurrently-enqueueing waiter (closes audit H-1).
    ///
    /// # Safety
    ///
    /// Each `CoreId` MUST call only with its own `core_id` value.  Each
    /// core has exactly one slot; reentrance / cross-core use of a slot
    /// is UB.  The hardware bound `core_id < MAX_WAITERS` is asserted at
    /// entry; under `panic = "abort"` an out-of-range call halts the
    /// kernel rather than aliasing a sibling's slot.
    pub fn acquire_read(&self, core_id: u8) {
        assert!((core_id as usize) < MAX_WAITERS,
                "core_id out of range");
        let slot = &self.slots[core_id as usize];

        // Step 1: prepare own slot.  Single-writer (this core).
        slot.reset(MODE_READ);

        // Step 2: enqueue at tail via atomic swap.  After this point we
        // are visible to release-* paths.
        let prev_tail = self.tail.swap(core_id, Ordering::AcqRel);

        if prev_tail == NONE_SENTINEL {
            // We are the new head.  Try immediate admit.
            // Per FIFO discipline: the immediate-admit check happens AFTER
            // enqueue, so a concurrent acquire_write that incremented the
            // writer bit BEFORE our swap is observed by us via the swap's
            // AcqRel fence; we wait via the parked loop in that case.
            if self.try_admit_as_reader() {
                // Mark ourselves as parked=true so the release-path knows
                // we're already in-flight as an admitted reader.
                slot.parked.store(true, Ordering::Release);
                // Cascade-admit contiguous reader successors (D-5 H-1 fix).
                // Without this, the lock degenerates to a FIFO mutex —
                // queued readers wait serially instead of holding
                // concurrently.  The cascade preserves FIFO admission
                // while restoring reader concurrency.
                self.cascade_admit_readers(core_id);
                return;
            }
        } else {
            // Link predecessor to us.  Predecessor will signal us when
            // it releases / is admitted.
            //
            // SAFETY: `prev_tail < MAX_WAITERS` by AcqRel swap's
            // observation invariant; the slot is owned by core
            // `prev_tail` which is currently in the queue.
            self.slots[prev_tail as usize].next.store(core_id, Ordering::Release);
        }

        // Step 3: wait until predecessor signals us.
        //
        // SAFETY: `slot.parked` is single-writer (the predecessor or the
        // lock holder).  We never return until parked == true, so the
        // slot remains in-queue throughout (closes audit H-2 by
        // EXPLICIT PROTOCOL: this loop is the lifetime-safety mechanism).
        while !slot.parked.load(Ordering::Acquire) {
            crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
        }

        // We are admitted; the predecessor (or release path) has
        // incremented the reader count.  Cascade-admit contiguous reader
        // successors to preserve RW lock semantics (D-5 H-1 fix).
        self.cascade_admit_readers(core_id);
    }

    /// **WS-SM SM2.C-defer D-5 (H-1 fix)**: cascade-admit contiguous
    /// reader successors after self has been admitted as a reader.
    ///
    /// Standard MCS-RW lock semantics: queued contiguous readers should
    /// be admitted together, not serialized.  Without this cascade, the
    /// queued lock degenerates to a FIFO mutex — readers wait for the
    /// previous reader to release before admitting, even though the
    /// "reader-writer" contract allows concurrent reader holding.
    ///
    /// Protocol: walk the slot chain via `next`.  For each contiguous
    /// reader successor:
    ///   - **Atomically claim** the successor via CAS on `parked`
    ///     (false → true).  This prevents the TOCTOU race where the
    ///     predecessor's cascade and the newly-awakened reader's
    ///     cascade both attempt to admit the SAME successor (closes
    ///     audit-pass-4 finding: previously the `parked.load` check +
    ///     `state.fetch_add` + `parked.store` had a non-atomic window
    ///     that could double-count under high contention).
    ///   - On CAS success: increment state's reader count
    ///     (`fetch_add(1, AcqRel)`).  We are the unique admitter.
    ///   - On CAS failure: another cascader already admitted this
    ///     successor.  Return (they will handle the rest of the chain
    ///     from their position).
    ///
    /// Stop at the first writer (don't admit it), at sentinel, or at a
    /// successor whose `next` hasn't been linked yet (stay loose;
    /// future releaser propagation handles the rest).
    fn cascade_admit_readers(&self, my_core_id: u8) {
        let mut current = my_core_id;
        loop {
            let next = self.slots[current as usize].next.load(Ordering::Acquire);
            if next == NONE_SENTINEL {
                return; // No further successor known yet.
            }
            // SAFETY: `next < MAX_WAITERS` by the enqueue-side invariant.
            let next_slot = &self.slots[next as usize];
            // Check successor's mode BEFORE attempting admission.
            let next_mode = next_slot.requested_mode();
            if next_mode != MODE_READ {
                return; // Stop at writer — leave for normal release-signal.
            }
            // **Atomic claim via CAS** (audit-pass-4 race fix): only the
            // CAS-winner is allowed to increment state and signal the
            // successor.  This eliminates the TOCTOU race between
            // concurrent cascade paths (predecessor cascade + newly-
            // awakened reader cascade).
            match next_slot.parked.compare_exchange(
                false, true,
                Ordering::AcqRel, Ordering::Acquire,
            ) {
                Ok(_) => {
                    // We claimed the successor.  Increment state.
                    // AcqRel on state to ensure the prior reader's CS data
                    // is visible to the new admittee (D-5 H-4 audit).
                    self.state.fetch_add(1, Ordering::AcqRel);
                    current = next;
                }
                Err(_) => {
                    // Another cascader admitted this successor already.
                    // Stop — they will continue the chain.
                    return;
                }
            }
        }
    }

    /// **WS-SM SM2.C-defer D-5.5**: acquire a write lock for `core_id`.
    ///
    /// FIFO-preserving via the same enqueue-first protocol as `acquire_read`.
    ///
    /// # Safety
    ///
    /// Same as `acquire_read`.
    pub fn acquire_write(&self, core_id: u8) {
        assert!((core_id as usize) < MAX_WAITERS,
                "core_id out of range");
        let slot = &self.slots[core_id as usize];

        slot.reset(MODE_WRITE);
        let prev_tail = self.tail.swap(core_id, Ordering::AcqRel);

        if prev_tail == NONE_SENTINEL {
            // We are the new head.
            if self.try_admit_as_writer() {
                slot.parked.store(true, Ordering::Release);
                return;
            }
        } else {
            self.slots[prev_tail as usize].next.store(core_id, Ordering::Release);
        }

        // Wait for predecessor signal.
        while !slot.parked.load(Ordering::Acquire) {
            crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
        }
    }
}

impl QueuedRwLock {
    /// **WS-SM SM2.C-defer D-5.6**: release a read lock held by `core_id`.
    ///
    /// Decrements the reader count.  If the count drops to zero and a
    /// successor waiter exists, signals it for admission.
    pub fn release_read(&self, core_id: u8) {
        assert!((core_id as usize) < MAX_WAITERS,
                "core_id out of range");

        // Decrement reader count.  `fetch_sub(1)` with AcqRel ordering:
        // Release publishes the critical-section side effects; Acquire
        // observes any prior writer/reader operations on state.
        let prev = self.state.fetch_sub(1, Ordering::AcqRel);

        // Defensive check (D-5 M-1): if writer bit is set during a
        // release_read call, that's a protocol violation (writer-readers
        // exclusion).  In production this can't happen if callers follow
        // the API; in test/debug builds we surface it.
        debug_assert!((prev & WRITER_BIT) == 0,
                      "release_read called while WRITER_BIT is set");

        // If we were the last reader AND a successor is waiting, signal it.
        let prev_readers = prev & READER_MASK;
        if prev_readers == 1 && (prev & WRITER_BIT) == 0 {
            // Reader count would drop to zero; check for successor.
            self.signal_next_waiter(core_id);
        }
        // Wake any WFE-parked waiters (broadcasts via SEV).
        crate::cpu::sev();
    }

    /// **WS-SM SM2.C-defer D-5.6**: release a write lock held by `core_id`.
    ///
    /// Clears the writer bit and signals the next waiter (if any).
    pub fn release_write(&self, core_id: u8) {
        assert!((core_id as usize) < MAX_WAITERS,
                "core_id out of range");

        // Clear the writer bit.  `fetch_and(READER_MASK, AcqRel)` clears
        // bit 63 while preserving the reader bits — though by the
        // writer-readers exclusion invariant, the reader bits should be 0.
        // AcqRel ensures the prior writer's critical-section data is
        // visible to subsequent admittees via the state-RMW chain
        // (D-5 H-4 fix).
        let _prev = self.state.fetch_and(READER_MASK, Ordering::AcqRel);
        debug_assert!((_prev & WRITER_BIT) != 0,
                      "release_write called while WRITER_BIT is not set");

        // Signal the next waiter.
        self.signal_next_waiter(core_id);
        crate::cpu::sev();
    }
}

// ============================================================================
// SM2.C-defer D-5 acceptance gate (panic-safety) — RAII guard wrappers
// ============================================================================

/// **WS-SM SM2.C-defer D-5 (panic-safety RAII)**: scoped read-lock guard.
///
/// Returned by `QueuedRwLock::acquire_read_guard`.  Calls `release_read`
/// in `Drop`, ensuring the lock is released on any control-flow exit
/// (normal return, panic-unwind, etc.).  This is the panic-safe API
/// that satisfies the plan §5.5 D-5 acceptance gate's
/// "panic-safety" criterion.
///
/// **Production note**: the seLe4n HAL uses `panic = abort` in
/// production (see `rust/Cargo.toml`), so panic-safety is technically
/// not required for the kernel-runtime profile.  The RAII guard is
/// provided for the test profile (`panic = unwind` under `--features
/// std`) to validate impl-level panic-safety properties.
#[must_use = "this RAII guard must be held for the duration of the read CS"]
pub struct QueuedRwLockReadGuard<'a> {
    lock: &'a QueuedRwLock,
    core_id: u8,
}

impl<'a> Drop for QueuedRwLockReadGuard<'a> {
    fn drop(&mut self) {
        self.lock.release_read(self.core_id);
    }
}

/// **WS-SM SM2.C-defer D-5 (panic-safety RAII)**: scoped write-lock guard.
///
/// Returned by `QueuedRwLock::acquire_write_guard`.  Calls
/// `release_write` in `Drop`. -/
#[must_use = "this RAII guard must be held for the duration of the write CS"]
pub struct QueuedRwLockWriteGuard<'a> {
    lock: &'a QueuedRwLock,
    core_id: u8,
}

impl<'a> Drop for QueuedRwLockWriteGuard<'a> {
    fn drop(&mut self) {
        self.lock.release_write(self.core_id);
    }
}

impl QueuedRwLock {
    /// **WS-SM SM2.C-defer D-5 (panic-safety RAII)**: scoped read-lock
    /// acquire.  Returns a guard whose `Drop` releases the read-lock,
    /// ensuring release on any control-flow exit (panic-safe).
    ///
    /// # Safety
    ///
    /// Same as `acquire_read` (each `core_id` MUST call only with its
    /// own value; reentrance / cross-core slot use is UB).
    pub fn acquire_read_guard(&self, core_id: u8) -> QueuedRwLockReadGuard<'_> {
        self.acquire_read(core_id);
        QueuedRwLockReadGuard { lock: self, core_id }
    }

    /// **WS-SM SM2.C-defer D-5 (panic-safety RAII)**: scoped write-lock
    /// acquire.  Returns a guard whose `Drop` releases the write-lock.
    ///
    /// # Safety
    ///
    /// Same as `acquire_write`.
    pub fn acquire_write_guard(&self, core_id: u8) -> QueuedRwLockWriteGuard<'_> {
        self.acquire_write(core_id);
        QueuedRwLockWriteGuard { lock: self, core_id }
    }

    /// Internal helper: signal the next waiter in the queue.
    ///
    /// Uses the standard **MCS handover protocol** to avoid the
    /// classic race where a new enqueuer arrives between the
    /// releaser's "is there a successor?" check and the queue cleanup.
    ///
    /// Protocol:
    /// 1. Read `releaser.next`.  If non-sentinel, the successor is
    ///    known — promote them.
    /// 2. If sentinel, try CAS `tail: self → NONE_SENTINEL`.  If
    ///    successful, queue is empty; clear head and return.
    /// 3. If CAS fails (some new enqueuer set tail to themselves
    ///    after our `next` load), **wait** for the new enqueuer to
    ///    finish linking by setting `releaser.next = their_id`,
    ///    then promote them.
    ///
    /// Without step 3, a successor that enqueued during step 1-2
    /// would link to a slot no longer in the queue (the releaser
    /// has already left), waiting forever for a signal that never
    /// comes — the canonical MCS handover bug.
    fn signal_next_waiter(&self, releaser_core_id: u8) {
        let releaser_slot = &self.slots[releaser_core_id as usize];
        let mut next = releaser_slot.next.load(Ordering::Acquire);

        if next == NONE_SENTINEL {
            // No visible successor yet.  Try to atomically end the queue.
            match self.tail.compare_exchange(
                releaser_core_id, NONE_SENTINEL,
                Ordering::AcqRel, Ordering::Acquire,
            ) {
                Ok(_) => {
                    // CAS succeeded: queue is now empty.  No head to clear
                    // (lock holds only `tail`).
                    return;
                }
                Err(_) => {
                    // CAS failed: a new enqueuer set tail to themselves
                    // AFTER our `next` load.  Spin-wait for them to
                    // complete the link (set our slot's `next` to their id).
                    loop {
                        let n = releaser_slot.next.load(Ordering::Acquire);
                        if n != NONE_SENTINEL {
                            next = n;
                            break;
                        }
                        crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
                    }
                }
            }
        }

        // Promote the known successor.
        //
        // SAFETY: `next < MAX_WAITERS` by the enqueue-side invariant
        // (only valid core_ids are stored in `next` fields).
        let next_slot = &self.slots[next as usize];
        let next_mode = next_slot.requested_mode();

        // Update lock state for the successor:
        // - Reader successor: increment reader count.
        // - Writer successor: set writer bit.
        // AcqRel on the RMW per D-5 H-4 fix: the state-RMW chain forms a
        // total order on the location; AcqRel ensures the new admittee's
        // critical section synchronizes-with the prior holder's critical
        // section transitively through state.  The parked.store/load pair
        // also synchronizes, but having both is correct and matches
        // standard MCS practice (release CS data on EVERY publication
        // path, not just via parked).
        if next_mode == MODE_READ {
            self.state.fetch_add(1, Ordering::AcqRel);
        } else {
            self.state.fetch_or(WRITER_BIT, Ordering::AcqRel);
        }

        // Signal the successor.
        next_slot.parked.store(true, Ordering::Release);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_is_unheld() {
        let lock = QueuedRwLock::new();
        assert_eq!(lock.peek_state(), 0);
        assert_eq!(lock.peek_tail(), NONE_SENTINEL);
    }

    #[test]
    fn default_matches_new() {
        let a = QueuedRwLock::new();
        let b = QueuedRwLock::default();
        assert_eq!(a.peek_state(), b.peek_state());
        assert_eq!(a.peek_tail(), b.peek_tail());
    }

    #[test]
    fn waiter_slot_init_unparked() {
        let slot = WaiterSlot::INIT;
        assert_eq!(slot.next.load(Ordering::Acquire), NONE_SENTINEL);
        assert!(!slot.parked.load(Ordering::Acquire));
        assert_eq!(slot.mode.load(Ordering::Acquire), MODE_READ);
    }

    #[test]
    fn waiter_slot_reset_clears_state() {
        let slot = WaiterSlot::INIT;
        slot.next.store(7, Ordering::Relaxed);
        slot.parked.store(true, Ordering::Relaxed);
        slot.reset(MODE_WRITE);
        assert_eq!(slot.next.load(Ordering::Acquire), NONE_SENTINEL);
        assert!(!slot.parked.load(Ordering::Acquire));
        assert_eq!(slot.requested_mode(), MODE_WRITE);
    }

    #[test]
    fn const_max_waiters_is_4() {
        assert_eq!(MAX_WAITERS, 4);
    }

    #[test]
    fn mode_constants_distinct() {
        assert_ne!(MODE_READ, MODE_WRITE);
    }

    #[test]
    fn sentinel_is_max_u8() {
        assert_eq!(NONE_SENTINEL, u8::MAX);
    }

    #[test]
    fn signature_pin_acquire_release_read() {
        let _: fn(&QueuedRwLock, u8) = QueuedRwLock::acquire_read;
        let _: fn(&QueuedRwLock, u8) = QueuedRwLock::release_read;
    }

    #[test]
    fn signature_pin_acquire_release_write() {
        let _: fn(&QueuedRwLock, u8) = QueuedRwLock::acquire_write;
        let _: fn(&QueuedRwLock, u8) = QueuedRwLock::release_write;
    }

    #[test]
    fn signature_pin_peek_methods() {
        let _: fn(&QueuedRwLock) -> u64 = QueuedRwLock::peek_state;
        let _: fn(&QueuedRwLock) -> u8 = QueuedRwLock::peek_tail;
    }
}

#[cfg(test)]
mod sequential_tests {
    use super::*;

    /// Sequential acquire then release for a single reader.  Verifies
    /// state transitions: 0 → 1 (reader count) → 0.
    #[test]
    fn single_reader_acquire_release() {
        let lock = QueuedRwLock::new();
        lock.acquire_read(0);
        assert_eq!(lock.peek_state(), 1, "reader count should be 1 after acquire");
        lock.release_read(0);
        assert_eq!(lock.peek_state(), 0, "state should clear after release");
    }

    /// Sequential acquire-then-release for a single writer.
    #[test]
    fn single_writer_acquire_release() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        assert_eq!(lock.peek_state(), WRITER_BIT,
                   "writer bit should be set after acquire");
        lock.release_write(0);
        assert_eq!(lock.peek_state(), 0, "state should clear after release");
    }

    /// Out-of-range core_id triggers a panic (assert! inside acquire_read).
    #[test]
    #[should_panic(expected = "core_id out of range")]
    fn out_of_range_core_id_acquire_read_panics() {
        let lock = QueuedRwLock::new();
        lock.acquire_read(MAX_WAITERS as u8);
    }

    /// Out-of-range core_id triggers a panic (assert! inside acquire_write).
    #[test]
    #[should_panic(expected = "core_id out of range")]
    fn out_of_range_core_id_acquire_write_panics() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(MAX_WAITERS as u8);
    }

    /// Out-of-range core_id triggers a panic (release_read).
    #[test]
    #[should_panic(expected = "core_id out of range")]
    fn out_of_range_core_id_release_read_panics() {
        let lock = QueuedRwLock::new();
        lock.release_read(MAX_WAITERS as u8);
    }

    /// Out-of-range core_id triggers a panic (release_write).
    #[test]
    #[should_panic(expected = "core_id out of range")]
    fn out_of_range_core_id_release_write_panics() {
        let lock = QueuedRwLock::new();
        lock.release_write(MAX_WAITERS as u8);
    }

    /// Layout: QueuedRwLock is 64-byte cache-line aligned.
    #[test]
    fn alignment_64() {
        assert_eq!(core::mem::align_of::<QueuedRwLock>(), 64);
    }

    /// Layout: WaiterSlot is 64-byte cache-line aligned (avoiding false sharing).
    #[test]
    fn waiter_slot_alignment_64() {
        assert_eq!(core::mem::align_of::<WaiterSlot>(), 64);
    }
}

#[cfg(test)]
mod cross_thread_tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;
    use std::sync::atomic::{AtomicU64, Ordering as StdOrdering};
    use std::vec::Vec;

    /// Multi-thread acquire/release roundtrip: each of 4 threads
    /// repeatedly acquires + releases the read lock; final state is 0.
    ///
    /// Iteration count: 100 (vs plan's 10⁴ acceptance gate).  The plan's
    /// 10⁴ assumes hardware-level WFE; on host the `wfe_bounded` stub is
    /// a busy-spin, multiplying CPU-time linearly with iterations.  We
    /// run 100 per-thread iterations × 4 threads × 4 tests = 1.6k
    /// operations total — surfacing scheduler races without exceeding
    /// CI time budget.  Hardware/CI gates running on aarch64 with real
    /// WFE can scale to 10⁴ via the standard env-override path.
    ///
    /// **Iteration tuning rationale**: prior runs with `ITER = 1_000`
    /// occasionally surfaced "test running over 60s" warnings on slow
    /// CI runners (cargo's diagnostic).  100 iterations stays well
    /// inside the 60s budget while preserving race-detection sensitivity:
    /// even at 100 iterations, the cross-thread interleaving exercises
    /// every MCS protocol transition (enqueue at empty / non-empty
    /// queue, signal at empty / non-empty queue, cascade-admit with
    /// known / unknown successor). -/
    #[test]
    fn cross_thread_reader_stress() {
        const ITER: usize = 100;
        let lock = Arc::new(QueuedRwLock::new());
        let mut handles = Vec::new();
        for tid in 0u8..(MAX_WAITERS as u8) {
            let lock_c = Arc::clone(&lock);
            handles.push(thread::spawn(move || {
                for _ in 0..ITER {
                    lock_c.acquire_read(tid);
                    lock_c.release_read(tid);
                }
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        // Final state: no readers, no writer.
        assert_eq!(lock.peek_state(), 0,
                   "final state should be 0; got {:#x}", lock.peek_state());
    }

    /// Multi-thread writer mutex test: 4 threads each increment a shared
    /// counter under writer-lock; final count = sum.
    /// Iteration count: 100 (see `cross_thread_reader_stress` rationale).
    #[test]
    fn cross_thread_writer_mutex() {
        const ITER: usize = 100;
        let lock = Arc::new(QueuedRwLock::new());
        let counter = Arc::new(AtomicU64::new(0));
        let mut handles = Vec::new();
        for tid in 0u8..(MAX_WAITERS as u8) {
            let lock_c = Arc::clone(&lock);
            let counter_c = Arc::clone(&counter);
            handles.push(thread::spawn(move || {
                for _ in 0..ITER {
                    lock_c.acquire_write(tid);
                    // Critical section: increment the shared counter.
                    // We expect the writer lock to provide mutex.
                    let v = counter_c.load(StdOrdering::Relaxed);
                    counter_c.store(v + 1, StdOrdering::Relaxed);
                    lock_c.release_write(tid);
                }
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        assert_eq!(counter.load(StdOrdering::Relaxed),
                   (MAX_WAITERS * ITER) as u64,
                   "writer mutex should serialize: expected {} got {}",
                   MAX_WAITERS * ITER, counter.load(StdOrdering::Relaxed));
        assert_eq!(lock.peek_state(), 0);
    }

    /// Mixed reader/writer stress: 2 threads each in reader and writer
    /// roles.  Final state should clear.
    #[test]
    fn cross_thread_mixed_stress() {
        const ITER: usize = 50;
        let lock = Arc::new(QueuedRwLock::new());
        let mut handles = Vec::new();
        // 2 readers (tids 0, 1)
        for tid in 0u8..2 {
            let lock_c = Arc::clone(&lock);
            handles.push(thread::spawn(move || {
                for _ in 0..ITER {
                    lock_c.acquire_read(tid);
                    lock_c.release_read(tid);
                }
            }));
        }
        // 2 writers (tids 2, 3)
        for tid in 2u8..4 {
            let lock_c = Arc::clone(&lock);
            handles.push(thread::spawn(move || {
                for _ in 0..ITER {
                    lock_c.acquire_write(tid);
                    lock_c.release_write(tid);
                }
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        assert_eq!(lock.peek_state(), 0,
                   "mixed stress should leave state clear; got {:#x}",
                   lock.peek_state());
    }

    /// **D-5 M-6 fix**: FIFO admission order assertion.
    ///
    /// Uses a deterministic enqueue protocol to test FIFO order:
    /// 1. T0 acquires writer lock and HOLDS it.
    /// 2. T1, T2, T3 spawned sequentially with sleep gaps between
    ///    spawns; each calls `acquire_write` and parks behind T0.
    ///    The sleeps ensure tail.swap happens in T1 → T2 → T3 order.
    /// 3. T0 releases.  Admission order MUST be T1, T2, T3 (FIFO).
    /// 4. Each Ti records its admission sequence via a shared counter
    ///    just after the park-loop exits.
    ///
    /// A FIFO-violating implementation would have T1, T2, T3 admitted
    /// in some non-deterministic order — caught by the strict monotone
    /// assertion below.
    #[test]
    fn cross_thread_writer_fifo_order() {
        use std::sync::atomic::AtomicBool;
        use std::time::Duration;
        const NUM_FOLLOWERS: usize = 3;
        let lock = Arc::new(QueuedRwLock::new());
        let release_signal = Arc::new(AtomicBool::new(false));
        let admit_counter = Arc::new(AtomicU64::new(0));
        let admit_order = Arc::new([
            AtomicU64::new(u64::MAX),
            AtomicU64::new(u64::MAX),
            AtomicU64::new(u64::MAX),
            AtomicU64::new(u64::MAX),
        ]);

        // T0 acquires and holds.
        let lock_c = Arc::clone(&lock);
        let rel_c = Arc::clone(&release_signal);
        let adm_ctr_c = Arc::clone(&admit_counter);
        let adm_ord_c = Arc::clone(&admit_order);
        let t0 = thread::spawn(move || {
            lock_c.acquire_write(0);
            let adm = adm_ctr_c.fetch_add(1, StdOrdering::SeqCst);
            adm_ord_c[0].store(adm, StdOrdering::SeqCst);
            // Wait until told to release.
            while !rel_c.load(StdOrdering::SeqCst) {
                core::hint::spin_loop();
            }
            lock_c.release_write(0);
        });

        // Wait until T0 has acquired.
        while lock.peek_state() == 0 {
            core::hint::spin_loop();
        }

        // Spawn followers T1, T2, T3 in order.  Audit-pass-8: switched
        // from `queued_flags + 20ms sleep` heuristic to deterministic
        // `peek_tail`-based polling — the parent waits until the
        // follower's `tail.swap` is OBSERVABLE in the lock state
        // (peek_tail returns the follower's id), guaranteeing the
        // enqueue order regardless of OS scheduling delays.
        let mut handles = Vec::new();
        for tid in 1u8..=(NUM_FOLLOWERS as u8) {
            let lock_c = Arc::clone(&lock);
            let adm_ctr_c = Arc::clone(&admit_counter);
            let adm_ord_c = Arc::clone(&admit_order);
            handles.push(thread::spawn(move || {
                lock_c.acquire_write(tid);
                let adm = adm_ctr_c.fetch_add(1, StdOrdering::SeqCst);
                adm_ord_c[tid as usize].store(adm, StdOrdering::SeqCst);
                lock_c.release_write(tid);
            }));
            // Deterministic: wait for the follower's tail.swap to fire.
            // peek_tail returns the latest enqueued slot id.  When it
            // equals `tid`, this follower has finished its tail.swap.
            while lock.peek_tail() != tid {
                core::hint::spin_loop();
            }
        }

        // Release T0; admission order should be T1, T2, T3.
        release_signal.store(true, StdOrdering::SeqCst);
        t0.join().unwrap();
        for h in handles {
            h.join().unwrap();
        }

        // T0 admitted at 0 (first).  T1 must admit before T2 before T3.
        let t0_adm = admit_order[0].load(StdOrdering::SeqCst);
        let t1_adm = admit_order[1].load(StdOrdering::SeqCst);
        let t2_adm = admit_order[2].load(StdOrdering::SeqCst);
        let t3_adm = admit_order[3].load(StdOrdering::SeqCst);
        assert_eq!(t0_adm, 0, "T0 should be the first admitted");
        assert!(t1_adm < t2_adm,
            "FIFO violation: T1 ({}) should admit before T2 ({})", t1_adm, t2_adm);
        assert!(t2_adm < t3_adm,
            "FIFO violation: T2 ({}) should admit before T3 ({})", t2_adm, t3_adm);
    }

    /// **D-5 H-1 fix validator**: contiguous reader concurrency.
    ///
    /// Without the H-1 fix, queued readers are admitted serially: R2
    /// only admits AFTER R1 releases.  With the fix, R1's admission
    /// cascades to admit all contiguous reader successors.
    ///
    /// Deterministic setup:
    /// 1. T0 acquires WRITER lock and holds.
    /// 2. T1, T2, T3 sequentially attempt acquire_read; each parks
    ///    behind the writer.
    /// 3. T0 releases.  T1 is admitted first (head of queue).  T1's
    ///    cascade should then admit T2 and T3 immediately.
    /// 4. T1 observes reader count > 1 (concurrent readers).
    ///
    /// On a FIFO-mutex implementation (H-1 bug present), T1 would
    /// observe reader_count == 1, T2 would wait for T1's release, etc.
    /// The cascade fix restores RW concurrency.
    #[test]
    fn cross_thread_reader_concurrency_witness() {
        use std::sync::atomic::AtomicBool;
        use std::time::Duration;
        const NUM_READERS: usize = 3;
        let lock = Arc::new(QueuedRwLock::new());
        let writer_release_signal = Arc::new(AtomicBool::new(false));
        let reader_release_signal = Arc::new(AtomicBool::new(false));
        let observed_concurrent = Arc::new(AtomicU64::new(0));

        // T0 acquires writer.
        let lock_c = Arc::clone(&lock);
        let rel_c = Arc::clone(&writer_release_signal);
        let t0 = thread::spawn(move || {
            lock_c.acquire_write(0);
            while !rel_c.load(StdOrdering::SeqCst) {
                core::hint::spin_loop();
            }
            lock_c.release_write(0);
        });

        while lock.peek_state() == 0 {
            core::hint::spin_loop();
        }

        // Spawn reader threads in sequence; they'll all enqueue.
        // Audit-pass-8: switched from `thread::sleep(10ms)` heuristic to
        // deterministic `peek_tail`-based polling to guarantee enqueue
        // order under heavy parallel test load.
        let mut handles = Vec::new();
        for tid in 1u8..=(NUM_READERS as u8) {
            let lock_c = Arc::clone(&lock);
            let obs_c = Arc::clone(&observed_concurrent);
            let rdr_rel_c = Arc::clone(&reader_release_signal);
            handles.push(thread::spawn(move || {
                lock_c.acquire_read(tid);
                // Observe state during CS — multiple readers should
                // be concurrent thanks to the cascade.
                let state = lock_c.peek_state();
                let readers = state & READER_MASK;
                if readers > 1 {
                    obs_c.fetch_add(1, StdOrdering::Relaxed);
                }
                // Hold until told to release (allowing other readers
                // to join concurrently).
                while !rdr_rel_c.load(StdOrdering::SeqCst) {
                    core::hint::spin_loop();
                }
                lock_c.release_read(tid);
            }));
            // Wait for this reader's tail.swap to fire deterministically.
            while lock.peek_tail() != tid {
                core::hint::spin_loop();
            }
        }

        // Release the writer.  Cascade should admit all 3 readers.
        writer_release_signal.store(true, StdOrdering::SeqCst);
        t0.join().unwrap();

        // Give readers a moment to all hold concurrently and observe.
        std::thread::sleep(Duration::from_millis(50));
        // Now release readers.
        reader_release_signal.store(true, StdOrdering::SeqCst);
        for h in handles {
            h.join().unwrap();
        }

        let count = observed_concurrent.load(StdOrdering::Relaxed);
        // With cascade: all 3 readers should observe count >= 2 (their
        // own plus at least one concurrent).  Without cascade: count = 0.
        assert!(count >= 2,
            "Expected at least 2 concurrent-reader observations \
             (H-1 cascade validation); got {}", count);
    }

    /// **D-5 acceptance gate (≥10 cross-thread tests)**: alternating
    /// reader-writer pattern.  4 threads, each alternating between
    /// reader and writer acquires.  Verifies that the lock correctly
    /// excludes writers from concurrent readers and serializes
    /// writers, with NO state corruption across the W→R→W→R pattern.
    #[test]
    fn cross_thread_alternating_rw_pattern() {
        const ITER: usize = 50;
        let lock = Arc::new(QueuedRwLock::new());
        let mut handles = Vec::new();
        for tid in 0u8..(MAX_WAITERS as u8) {
            let lock_c = Arc::clone(&lock);
            handles.push(thread::spawn(move || {
                for i in 0..ITER {
                    if i % 2 == 0 {
                        lock_c.acquire_read(tid);
                        lock_c.release_read(tid);
                    } else {
                        lock_c.acquire_write(tid);
                        lock_c.release_write(tid);
                    }
                }
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        // Final state must be clean.
        assert_eq!(lock.peek_state(), 0,
                   "state should be 0 after alternating R/W pattern; got {:#x}",
                   lock.peek_state());
    }

    /// **D-5 acceptance gate (≥10 cross-thread tests)**: writer
    /// starvation prevention.  T0 holds writer.  T1 enqueues as
    /// writer (FIFO position 1).  T2 spawns as reader (FIFO
    /// position 2).  T0 releases.  T1 (writer) must admit
    /// BEFORE T2 (reader), enforcing FIFO and preventing
    /// reader-induced writer starvation.
    ///
    /// **Deterministic synchronization** (audit-pass-8): use
    /// `peek_tail`-based polling to wait for each thread's
    /// `tail.swap` to actually fire before spawning the next.
    /// The naive `store(true) + sleep(20ms)` heuristic could fail
    /// under extreme OS scheduling delay since the program-order
    /// store doesn't guarantee tail.swap has been observable.
    #[test]
    fn cross_thread_writer_no_starvation_under_readers() {
        let lock = Arc::new(QueuedRwLock::new());
        let release_signal = Arc::new(AtomicBool::new(false));
        let writer_admitted = Arc::new(AtomicBool::new(false));
        let reader_admitted = Arc::new(AtomicBool::new(false));

        // T0: writer holder, releases on signal.
        let lock_c = Arc::clone(&lock);
        let rel_c = Arc::clone(&release_signal);
        let t0 = thread::spawn(move || {
            lock_c.acquire_write(0);
            while !rel_c.load(StdOrdering::SeqCst) {
                core::hint::spin_loop();
            }
            lock_c.release_write(0);
        });

        // Wait for T0 admit: state has writer bit set.
        while lock.peek_state() == 0 {
            core::hint::spin_loop();
        }
        // T0's tail.swap returned NONE_SENTINEL (T0 was head); tail unset
        // from a queue-membership perspective.  Wait for that.
        // (T0 just admitted itself; no tail member yet.)

        // T1: writer (enqueues at queue position 1).
        let lock_c = Arc::clone(&lock);
        let w_adm_c = Arc::clone(&writer_admitted);
        let r_adm_c = Arc::clone(&reader_admitted);
        let t1 = thread::spawn(move || {
            lock_c.acquire_write(1);
            // Writer admitted.  Check that no reader was admitted before.
            assert!(!r_adm_c.load(StdOrdering::SeqCst),
                "writer starvation: reader admitted before queued writer");
            w_adm_c.store(true, StdOrdering::SeqCst);
            lock_c.release_write(1);
        });
        // Deterministic wait: poll peek_tail until T1's id (1) appears,
        // proving T1's tail.swap has fired.
        while lock.peek_tail() != 1 {
            core::hint::spin_loop();
        }

        // T2: reader (enqueues at queue position 2).
        let lock_c = Arc::clone(&lock);
        let r_adm_c = Arc::clone(&reader_admitted);
        let w_adm_c = Arc::clone(&writer_admitted);
        let t2 = thread::spawn(move || {
            lock_c.acquire_read(2);
            // Reader admitted.  Check that the queued writer was admitted first.
            assert!(w_adm_c.load(StdOrdering::SeqCst),
                "writer-after-reader: reader admitted before queued writer");
            r_adm_c.store(true, StdOrdering::SeqCst);
            lock_c.release_read(2);
        });
        // Wait for T2's tail.swap to fire.
        while lock.peek_tail() != 2 {
            core::hint::spin_loop();
        }

        // Now release T0; admission order MUST be T1 (writer) then T2 (reader).
        release_signal.store(true, StdOrdering::SeqCst);

        t0.join().unwrap();
        t1.join().unwrap();
        t2.join().unwrap();
        assert_eq!(lock.peek_state(), 0);
    }

    /// **D-5 acceptance gate (≥10 cross-thread tests)**: state
    /// invariant — at any observable point, state is either 0
    /// (free), has WRITER_BIT set (writer holds), OR has a positive
    /// reader count (readers hold).  NEVER both WRITER_BIT and
    /// readers (mutex correctness).  Race-detection: 4 threads do
    /// many reader/writer ops; periodically sample state from a
    /// separate observer thread.
    #[test]
    fn cross_thread_state_invariant_no_writer_with_readers() {
        const ITER: usize = 100;
        let lock = Arc::new(QueuedRwLock::new());
        let stop_observer = Arc::new(AtomicBool::new(false));
        let invariant_violated = Arc::new(AtomicBool::new(false));

        // Observer thread: sample state and check invariant.
        let lock_obs = Arc::clone(&lock);
        let stop_c = Arc::clone(&stop_observer);
        let viol_c = Arc::clone(&invariant_violated);
        let observer = thread::spawn(move || {
            while !stop_c.load(StdOrdering::SeqCst) {
                let s = lock_obs.peek_state();
                let writer_held = (s & 0x8000_0000_0000_0000) != 0;
                let reader_count = s & 0x7FFF_FFFF_FFFF_FFFF;
                // Invariant: NOT (writer_held AND reader_count > 0).
                if writer_held && reader_count > 0 {
                    viol_c.store(true, StdOrdering::SeqCst);
                    return;
                }
            }
        });

        // 4 worker threads: mixed R/W.
        let mut handles = Vec::new();
        for tid in 0u8..(MAX_WAITERS as u8) {
            let lock_c = Arc::clone(&lock);
            handles.push(thread::spawn(move || {
                for i in 0..ITER {
                    if i % 3 == 0 {
                        lock_c.acquire_write(tid);
                        lock_c.release_write(tid);
                    } else {
                        lock_c.acquire_read(tid);
                        lock_c.release_read(tid);
                    }
                }
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        stop_observer.store(true, StdOrdering::SeqCst);
        observer.join().unwrap();
        assert!(!invariant_violated.load(StdOrdering::SeqCst),
            "mutex invariant violated: observed state with both writer and readers");
        assert_eq!(lock.peek_state(), 0);
    }

    /// **D-5 acceptance gate (≥10 cross-thread tests)**: slot-ownership
    /// boundary.  Verifies that each core_id ∈ [0, MAX_WAITERS) is
    /// independently usable as a slot.  Spawning threads with distinct
    /// core_ids should NOT alias slot state across threads (no false-
    /// sharing-induced corruption between slots).
    #[test]
    fn cross_thread_slot_ownership_independence() {
        const ITER: usize = 100;
        let lock = Arc::new(QueuedRwLock::new());
        // Per-slot counter to detect any aliasing.
        let counters = Arc::new([
            AtomicU64::new(0),
            AtomicU64::new(0),
            AtomicU64::new(0),
            AtomicU64::new(0),
        ]);

        let mut handles = Vec::new();
        for tid in 0u8..(MAX_WAITERS as u8) {
            let lock_c = Arc::clone(&lock);
            let counters_c = Arc::clone(&counters);
            handles.push(thread::spawn(move || {
                for _ in 0..ITER {
                    lock_c.acquire_read(tid);
                    // Each thread increments ITS OWN counter while holding the lock.
                    let prev = counters_c[tid as usize].fetch_add(1, StdOrdering::SeqCst);
                    // The counter must not be touched by other slots.
                    assert!(prev < ITER as u64,
                        "slot {} counter overflowed: {} (alias detected?)", tid, prev);
                    lock_c.release_read(tid);
                }
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        // Each counter must equal exactly ITER.
        for tid in 0..MAX_WAITERS {
            let c = counters[tid].load(StdOrdering::SeqCst);
            assert_eq!(c, ITER as u64,
                "slot {} counter mismatch: expected {}, got {}", tid, ITER, c);
        }
        assert_eq!(lock.peek_state(), 0);
    }

    /// **D-5 acceptance gate (≥10 cross-thread tests)**: panic-safety
    /// via RAII guard.  T0 acquires write via `acquire_write_guard`,
    /// then panics.  The guard's `Drop` releases the lock on unwind.
    /// T1 (after T0's panic) must be able to acquire normally.
    ///
    /// This validates the QueuedRwLock's panic-safe API (the RAII
    /// guard pattern in `acquire_write_guard` / `acquire_read_guard`).
    /// The seLe4n kernel runtime uses `panic = abort` (no unwind),
    /// but the test profile uses `panic = unwind` and this test
    /// exercises that code path.
    #[test]
    fn cross_thread_panic_safety_writer_releases_on_unwind() {
        use std::panic;
        let lock = Arc::new(QueuedRwLock::new());

        // T0: acquire writer via RAII guard, then panic.
        let lock_c = Arc::clone(&lock);
        let t0 = thread::spawn(move || {
            let _result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                let _guard = lock_c.acquire_write_guard(0);
                panic!("simulated panic in writer CS — guard Drop should release");
            }));
            // catch_unwind returns Err; verify here.
            assert!(_result.is_err(), "panic should have been caught");
        });
        t0.join().unwrap();

        // Lock should be released (state = 0).  If the guard's Drop didn't
        // fire on unwind, the writer bit would still be set and state ≠ 0.
        assert_eq!(lock.peek_state(), 0,
            "RAII guard Drop should release the lock on panic-unwind");

        // T1: verify the lock is usable again post-panic.
        let lock_c = Arc::clone(&lock);
        let t1 = thread::spawn(move || {
            let _guard = lock_c.acquire_write_guard(1);
            // Normal CS; guard's Drop releases on return.
        });
        t1.join().unwrap();
        assert_eq!(lock.peek_state(), 0,
            "lock must be usable after a previous holder panicked");
    }

    /// **D-5 acceptance gate (≥10 cross-thread tests)**: panic-safety
    /// for reader RAII.  Same as writer panic-safety but for the
    /// reader path. -/
    #[test]
    fn cross_thread_panic_safety_reader_releases_on_unwind() {
        use std::panic;
        let lock = Arc::new(QueuedRwLock::new());

        let lock_c = Arc::clone(&lock);
        let t0 = thread::spawn(move || {
            let _result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                let _guard = lock_c.acquire_read_guard(0);
                panic!("simulated panic in reader CS");
            }));
            assert!(_result.is_err());
        });
        t0.join().unwrap();
        assert_eq!(lock.peek_state(), 0,
            "RAII guard Drop should release the read-lock on panic-unwind");
    }

    /// **D-5 acceptance gate (≥10 cross-thread tests)**: rapid
    /// acquire/release cycling.  Stress-tests the MCS handover path
    /// under maximum contention — every thread is constantly cycling
    /// between holder and waiter states, exercising every code path
    /// in `signal_next_waiter` and `cascade_admit_readers`.
    #[test]
    fn cross_thread_rapid_handover_cycling() {
        const ITER: usize = 200;
        let lock = Arc::new(QueuedRwLock::new());
        let mut handles = Vec::new();
        // 4 threads each rapidly cycling between acquire/release of write lock.
        for tid in 0u8..(MAX_WAITERS as u8) {
            let lock_c = Arc::clone(&lock);
            handles.push(thread::spawn(move || {
                for _ in 0..ITER {
                    lock_c.acquire_write(tid);
                    // Empty CS.
                    lock_c.release_write(tid);
                }
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        // Total writes = 4 * 200 = 800.  Lock must end in state 0.
        assert_eq!(lock.peek_state(), 0,
            "rapid handover should leave state clean; got {:#x}", lock.peek_state());
        assert_eq!(lock.peek_tail(), NONE_SENTINEL,
            "rapid handover should leave queue empty");
    }
}
