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
    pub fn peek_state(&self) -> u64 {
        self.state.load(Ordering::Acquire)
    }

    /// Peek the tail slot index (test-only).
    pub fn peek_tail(&self) -> u8 {
        self.tail.load(Ordering::Acquire)
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
            let new = cur + 1; // reader count increments
            // CAS-attempt; on success return; on failure retry.
            match self.state.compare_exchange(
                cur, new,
                Ordering::Acquire, Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(_) => continue,
            }
        }
    }

    /// **Writer fast-path predicate**: can we acquire-direct as a writer?
    ///
    /// Returns `true` only if state == 0 (no readers, no writer).  Called
    /// AFTER enqueue.
    fn try_admit_as_writer(&self) -> bool {
        self.state.compare_exchange(
            0, WRITER_BIT,
            Ordering::Acquire, Ordering::Relaxed,
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
        // incremented the reader count.
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

        // Decrement reader count.  `fetch_sub(1)` with Release ordering
        // publishes the critical-section side effects to a subsequent
        // acquire-load by an admitted thread.
        let prev = self.state.fetch_sub(1, Ordering::Release);

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

        // Clear the writer bit.  `fetch_and(READER_MASK, Release)` clears
        // bit 63 while preserving the reader bits — though by the
        // writer-readers exclusion invariant, the reader bits should be 0.
        self.state.fetch_and(READER_MASK, Ordering::Release);

        // Signal the next waiter.
        self.signal_next_waiter(core_id);
        crate::cpu::sev();
    }

    /// **Internal helper**: signal the next waiter in the queue.
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
        if next_mode == MODE_READ {
            self.state.fetch_add(1, Ordering::Release);
        } else {
            self.state.fetch_or(WRITER_BIT, Ordering::Release);
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
}
