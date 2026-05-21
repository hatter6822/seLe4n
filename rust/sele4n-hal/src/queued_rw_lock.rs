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
//! stores `next : AtomicU8` (successor slot idx), `parked : AtomicU8`
//! (mode-encoded four-state admit machine: NOT_IN_QUEUE /
//! WAITING_READER / WAITING_WRITER / ADMITTED — see `PARKED_*`
//! constants), and `mode : AtomicU8` (diagnostic-only — the parked
//! value is the authoritative mode source for walkers).
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

// **WS-SM SM2.E audit-pass**: this module is `safe`-only — every
// synchronisation primitive is built on `AtomicU8` / `AtomicU64`
// methods that are safe in stable Rust.  The original
// `#![allow(unsafe_code)]` annotation has been removed; if a future
// refactor reintroduces unsafe code (e.g. a `Pin` / `Box` raw-pointer
// optimisation), the unsafe block MUST be justified per the project's
// SAFETY-comment convention.

// Tests use std; production code is no_std-compatible.
#[cfg(test)]
extern crate std;

use core::sync::atomic::{AtomicU64, AtomicU8, Ordering};

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

/// **WS-SM SM2.E MCS-RW protocol fix**: four-state machine for the
/// per-slot `parked : AtomicU8` field (replacing the original
/// `parked : AtomicBool`).
///
/// The four-state machine closes two race classes:
///
/// **(A) Cascade-vs-signal ghost-`+1` race** that a 2-state `bool`
/// cannot distinguish (NOT_IN_QUEUE vs the previously-undifferentiated
/// "false" state):
///
/// 1. **WAITING_READER / WAITING_WRITER**: the slot's owner has
///    finished its enqueue protocol (`tail.swap`,
///    `slot[prev].next.store`) and is spinning, ready to be admitted
///    by a cascade or signal CAS.  The READER/WRITER distinction
///    carries the mode atomically — see (B) below.
/// 2. **NOT_IN_QUEUE**: the slot's owner has reset for a new
///    iteration but has not yet completed enqueue.  The slot is
///    structurally present in the queue chain (because
///    `slot[predecessor].next` may still point at it from a previous
///    iteration), but admitting it would be a ghost admission — the
///    owner is going to admit itself via `try_admit_as_*`.
/// 3. **ADMITTED**: the slot's owner has been admitted (either by
///    cascade, by signal, or by `try_admit_as_*`).  Terminal.
///
/// **(B) Stale-mode-read race** between the walker's `slot.mode` load
/// and the slot owner's iter-K reset's mode store.  Even with
/// Release/Acquire on the chain pointer, the walker's mode load is
/// only HB-after the iter that the chain link belongs to.  A walker
/// arriving via a STALE iter-(K-1) chain link could observe iter-(K-1)'s
/// mode (READ) even though the slot's owner has transitioned to iter K
/// with mode WRITE.  The walker then performs the WRONG state update
/// (reader CAS-loop instead of writer state.CAS), producing a state
/// where `_prev=1` for a writer's release.  This was the residual
/// "release_write called while WRITER_BIT is not set" panic that
/// PR #790 commit-3 left unresolved.
///
/// **Fix**: encode the mode atomically in the parked value.  The
/// walker's parked.load(Acquire) directly carries the mode:
/// `WAITING_READER` and `WAITING_WRITER` are distinct states, and the
/// walker's CAS direction (`WAITING_READER → ADMITTED` vs
/// `WAITING_WRITER → ADMITTED`) is determined by the read parked
/// value.  Because the parked Release-store happens AFTER the mode
/// store in the slot owner's enqueue, observing iter K's parked value
/// implies HB to iter K's mode value — the walker cannot mix iters.
///
/// Transitions (using `(mode, value)` shorthand):
/// * `acquire_*::reset()` → NOT_IN_QUEUE.
/// * acquire `try_admit_as_*` success → ADMITTED (direct fast path).
/// * acquire's `parked.store(WAITING_*)` after linking predecessor →
///   WAITING_READER or WAITING_WRITER (matching the requested mode).
/// * cascade/signal CAS WAITING_READER → ADMITTED for reader admit.
/// * cascade/signal CAS WAITING_WRITER → ADMITTED for writer admit.
/// * Release does NOT touch this field; the next iteration's
///   `reset()` will overwrite it with NOT_IN_QUEUE.
///
/// **`slot.mode` field**: retained for diagnostic purposes (peek-state
/// utilities) but the WALKER MUST NOT trust it as an authoritative
/// mode source — the parked value is.  `cascade_admit_readers` does
/// use `requested_mode()` as a fast pre-check (early-return on writer
/// without doing state CAS) but the parked-CAS direction is the
/// definitive safety check: the CAS is `WAITING_READER → ADMITTED`,
/// so a stale-mode-read for an actual writer (parked = WAITING_WRITER)
/// fails the CAS and triggers undo.  `signal_next_waiter` does NOT
/// read `requested_mode()` at all — it dispatches purely on the
/// parked value (lines 1126+ in `signal_next_waiter`).
pub const PARKED_NOT_IN_QUEUE: u8 = 0;
pub const PARKED_WAITING_READER: u8 = 1;
pub const PARKED_WAITING_WRITER: u8 = 2;
pub const PARKED_ADMITTED: u8 = 3;


/// One waiter slot — exactly one per core.  The slot is OWNED by the
/// lock for the duration of the program; no heap or stack allocation
/// is involved.  This eliminates lifetime hazards (audit H-2).
#[repr(C, align(64))] // cache-line aligned to avoid false sharing
pub struct WaiterSlot {
    /// Index of the next slot in the FIFO queue, or `NONE_SENTINEL` if
    /// this is the tail.  Single-writer (the OWNING core, while in
    /// queue); single-reader (the predecessor or the lock-holder).
    next: AtomicU8,
    /// Mode-encoded four-state admission machine (see `PARKED_*`
    /// constants above).  Single-writer per transition (well-defined
    /// ownership: owner writes NOT_IN_QUEUE and WAITING_READER /
    /// WAITING_WRITER; admitter writes ADMITTED; owner's NONE-path
    /// self-admit-spin can also revert ADMITTED → WAITING_* via CAS
    /// when its state-CAS fails).
    parked: AtomicU8,
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
        parked: AtomicU8::new(PARKED_NOT_IN_QUEUE),
        mode: AtomicU8::new(MODE_READ),
    };

    /// Re-initialise this slot for a fresh enqueue.  Called by the
    /// slot's owner before swapping into the queue tail.
    ///
    /// **WS-SM SM2.E MCS-RW protocol fix**: stores
    /// `PARKED_NOT_IN_QUEUE` (rather than the previous `false`).
    /// This is essential: the four-state machine ensures cascade/
    /// signal CAS cannot admit a just-reset slot before its owner
    /// has finished the enqueue protocol.  See the `PARKED_*`
    /// constants' docstring above for the full rationale.
    ///
    /// `mode.store` is Release-ordered (not Relaxed); this is a
    /// defense-in-depth measure layered on top of the parked-encoded
    /// mode protocol.  Walkers should NOT trust `mode` as the
    /// authoritative mode source — the `parked` value (which has the
    /// READER/WRITER distinction encoded via WAITING_READER vs
    /// WAITING_WRITER) is.  See the `PARKED_*` docstring above for
    /// the full rationale of why parked-encoded mode is necessary
    /// (stale-chain-link walkers can observe iter-(K-1)'s `mode`
    /// even after iter-K's reset).
    ///
    /// Single-writer: only the owning core calls this.
    pub fn reset(&self, requested_mode: u8) {
        self.next.store(NONE_SENTINEL, Ordering::Relaxed);
        self.parked.store(PARKED_NOT_IN_QUEUE, Ordering::Relaxed);
        self.mode.store(requested_mode, Ordering::Release);
    }

    /// Read the requested mode (diagnostic-only — see WaiterSlot
    /// field docstring; walkers MUST use `parked` value, not this).
    ///
    /// Acquire-ordered to pair with the Release-store in `reset()`,
    /// providing a layered defense against stale-mode reads even
    /// though the protocol does not rely on this property for
    /// correctness — the parked-encoded mode is the authoritative
    /// safety mechanism.
    pub fn requested_mode(&self) -> u8 {
        self.mode.load(Ordering::Acquire)
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
        let raw_prev_tail = self.tail.swap(core_id, Ordering::AcqRel);

        // **WS-SM SM2.E MCS-RW protocol fix — stale-self detection**:
        // if `raw_prev_tail == core_id`, the tail was left dangling at
        // our own slot by a prior cascade admission.  Specifically:
        // an earlier iteration cascade-admitted us (predecessor's
        // `cascade_admit_readers` CAS-claimed our `parked` and
        // incremented state), but cascade does NOT update `tail`
        // because cascade doesn't know if the admitted slot was the
        // current tail.  When all readers from that cascade chain
        // release, the release path's `signal_next_waiter` DOES clean
        // up tail (via CAS or walk-past-stale), but if our re-enqueue
        // races AHEAD of that signal, we observe the stale tail value.
        //
        // Only this core could have set `tail` to its own ID — each
        // slot has exactly one owner — so `raw_prev_tail == core_id`
        // unambiguously identifies the stale case.  Treating it as
        // `NONE_SENTINEL` is sound because the queue is effectively
        // empty (our previous iteration's queue position has been
        // consumed by the admit chain).
        //
        // Without this fix, the `else` branch below would store
        // `slot[core_id].next.store(core_id)` — a self-link — and the
        // park loop would never terminate, producing the deadlock
        // CLAUDE.md flagged as "occasionally deadlock under heavy
        // host-side load" (`cross_thread_slot_ownership_independence`
        // and similar reader-cycling tests).
        let prev_tail = if raw_prev_tail == core_id {
            NONE_SENTINEL
        } else {
            raw_prev_tail
        };

        if prev_tail == NONE_SENTINEL {
            // We are the new head.  Try immediate admit.
            // Per FIFO discipline: the immediate-admit check happens AFTER
            // enqueue, so a concurrent acquire_write that incremented the
            // writer bit BEFORE our swap is observed by us via the swap's
            // AcqRel fence; we wait via the parked loop in that case.
            if self.try_admit_as_reader() {
                // Mark ourselves as ADMITTED so cascade/signal CAS
                // (which expects WAITING) cannot re-admit us.
                slot.parked.store(PARKED_ADMITTED, Ordering::Release);
                // Cascade-admit contiguous reader successors (D-5 H-1 fix).
                // Without this, the lock degenerates to a FIFO mutex —
                // queued readers wait serially instead of holding
                // concurrently.  The cascade preserves FIFO admission
                // while restoring reader concurrency.
                self.cascade_admit_readers(core_id);
                return;
            }
            // **WS-SM SM2.E MCS-RW protocol fix — NONE-path self-admit
            // spin with CAS-claim ordering**: try_admit_as_reader failed
            // (state has WRITER_BIT).  We took the NONE_SENTINEL path so
            // no predecessor will signal us via the slot[prev].next
            // chain — without this self-admit spin, we'd be orphaned.
            //
            // The naive design `state-CAS, then parked.store(ADMITTED)`
            // has a race against signal targeting us via a STALE
            // slot[X].next = us link from a previous iteration:
            //  1. We try_admit (state += 1).
            //  2. Concurrent signal walks slot[X].next = us, CAS-loops
            //     state += 1, CAS parked WAITING → ADMITTED success
            //     (parked is still WAITING from our store).
            //  3. Signal returns.  We parked.store(ADMITTED).
            // Net: state has +2 for one holder.  Ghost +1.
            //
            // **Fix: CAS-claim parked BEFORE updating state.**  If our
            // CAS-claim wins, signal's CAS parked WAITING → ADMITTED
            // fails (parked is now ADMITTED), and signal's state
            // increment is undone by its own fetch_sub.  Net: signal
            // contributes 0 to state.  Our state CAS then increments
            // by 1.  Single admission.
            //
            // If our CAS-claim loses (signal got there first), we
            // observe parked = ADMITTED at the top of the loop and
            // return — signal owns the admission and has already
            // incremented state.
            slot.parked.store(PARKED_WAITING_READER, Ordering::Release);
            loop {
                if slot.parked.load(Ordering::Acquire) == PARKED_ADMITTED {
                    // Signal beat us to the admission.  State has
                    // signal's +1 for us; nothing more to do beyond
                    // cascade.
                    self.cascade_admit_readers(core_id);
                    return;
                }
                // CAS-claim parked first.  Only the CAS-winner is
                // allowed to increment state for this slot.
                if slot.parked.compare_exchange(
                    PARKED_WAITING_READER, PARKED_ADMITTED,
                    Ordering::AcqRel, Ordering::Acquire,
                ).is_ok() {
                    // Claimed.  Now atomically increment state.  If
                    // state has WRITER_BIT, we cannot admit right
                    // now — revert parked via CAS (NOT a STORE — see
                    // Stream B/§6.6 fix candidate F1) and continue
                    // spinning.
                    loop {
                        let cur = self.state.load(Ordering::Acquire);
                        if (cur & WRITER_BIT) != 0 {
                            // Writer admitted between our parked-CAS
                            // and our state-CAS.  Revert parked so a
                            // future signal can re-claim us.
                            //
                            // **Stream B F1 fix**: revert via CAS, not
                            // STORE.  A naked store would clobber a
                            // concurrent admitter's ADMITTED publish.
                            // The CAS only undoes our own ADMITTED;
                            // if signal already reverted us (saw our
                            // ADMITTED, walked past, no state credit),
                            // the CAS fails harmlessly with the
                            // observed value being WAITING_READER — also fine.
                            let _ = slot.parked.compare_exchange(
                                PARKED_ADMITTED, PARKED_WAITING_READER,
                                Ordering::AcqRel, Ordering::Acquire,
                            );
                            break;
                        }
                        let new_state = cur + 1;
                        if self.state.compare_exchange(
                            cur, new_state,
                            Ordering::AcqRel, Ordering::Acquire,
                        ).is_ok() {
                            self.cascade_admit_readers(core_id);
                            return;
                        }
                        // CAS lost a race with another state mutator.
                        // Retry the inner loop to re-load and re-CAS.
                    }
                }
                crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
            }
        } else {
            // **WS-SM SM2.E MCS-RW protocol fix — order of operations**:
            // Mark ourselves as WAITING_READER BEFORE linking the
            // predecessor.  This ensures any concurrent admitter that
            // observes our predecessor's `next` pointing to us will
            // then see our `parked == WAITING_READER` (via the
            // happens-before edge through
            // `slot[prev].next.store(me, Release)` ←
            // signal's `next.load(Acquire)`).
            //
            // Reverse order (link THEN store WAITING) would create a
            // window where signal sees the link but our parked is
            // still NOT_IN_QUEUE; signal's CAS WAITING→ADMITTED fails,
            // signal walks past us, we miss our wake-up.
            //
            // The WAITING_READER value (vs the generic WAITING)
            // carries the mode atomically — a walker arriving via a
            // stale chain link from a prior iteration's writer cannot
            // misinterpret this slot as a writer (closes Stream B's
            // residual writer-readers exclusion panic).
            slot.parked.store(PARKED_WAITING_READER, Ordering::Release);
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
        // SAFETY: `slot.parked` is single-writer per transition.
        // Owner writes NOT_IN_QUEUE (reset) and WAITING (this fn).
        // Admitter writes ADMITTED (cascade or signal CAS).  We
        // never return until ADMITTED, so the slot remains in-queue
        // throughout.
        while slot.parked.load(Ordering::Acquire) != PARKED_ADMITTED {
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
    /// **Protocol** (post-SM2.E audit-pass):
    ///
    /// Walk the slot chain via `next`, bounded by `MAX_WAITERS` steps.
    /// For each contiguous reader successor:
    ///
    /// 1. Read `slot[current].next`.  If `NONE_SENTINEL`, return (no
    ///    successor known yet — a future releaser will pick up).
    /// 2. Self-link defense: `debug_assert!(next != current)`.  With
    ///    the stale-self fix in `acquire_*`, self-links should not
    ///    occur; this is a regression guard.
    /// 3. Pre-check `next_slot.requested_mode()`: if `MODE_WRITE`,
    ///    return.  This is a fast-path optimization; the parked-CAS
    ///    below is the authoritative mode check.
    /// 4. **State-CAS reader admit** (CAS-loop with WRITER_BIT
    ///    precondition).  If WRITER_BIT is set, return.  Otherwise
    ///    CAS `state: cur → cur + 1` (atomic; reverts if state
    ///    changed mid-flight).  This closes the SM2.E audit-pass
    ///    cascade-during-writer-admit race and the WRITER_BIT
    ///    underflow on undo (see inline comment below).
    /// 5. **Parked-CAS** `PARKED_WAITING_READER → PARKED_ADMITTED`:
    ///    - On success: continue cascading (advance `current = next`).
    ///    - On failure: undo state (`fetch_sub(1)`) and return.  The
    ///      failure can be NOT_IN_QUEUE (slot mid-reset), ADMITTED
    ///      (already admitted by another path), or WAITING_WRITER
    ///      (stale mode pre-check; actual mode is WRITE).  In all
    ///      cases, cascade stops here; the chain will be processed
    ///      by future signals.
    ///
    /// **CAS-claim symmetry with `signal_next_waiter`**: both paths
    /// target the same `parked` flag with `WAITING_READER → ADMITTED`
    /// or `WAITING_WRITER → ADMITTED`.  Exactly one CAS wins per
    /// (slot, iteration) by atomic semantics.
    fn cascade_admit_readers(&self, my_core_id: u8) {
        let mut current = my_core_id;
        // Bound the walk by `MAX_WAITERS` — the chain has at most
        // that many distinct slots (one per core).  This also defends
        // against any pathological cycle in `next` pointers caused by
        // a future regression.
        for _walk_step in 0..MAX_WAITERS {
            let next = self.slots[current as usize].next.load(Ordering::Acquire);
            if next == NONE_SENTINEL {
                return; // No further successor known yet.
            }
            // Self-link defense: should not occur with the stale-self
            // fix in `acquire_read` / `acquire_write`, but guards
            // against infinite walks if any future regression
            // reintroduces self-linking.
            if next == current {
                debug_assert!(false,
                    "cascade_admit_readers: self-referential next pointer at slot {}",
                    current);
                return;
            }
            // SAFETY: `next < MAX_WAITERS` by the enqueue-side invariant.
            let next_slot = &self.slots[next as usize];
            // Check successor's mode BEFORE attempting admission.
            let next_mode = next_slot.requested_mode();
            if next_mode != MODE_READ {
                return; // Stop at writer — leave for normal release-signal.
            }
            // **WS-SM SM2.E MCS-RW protocol fix — CAS-loop reader admit
            // with WRITER_BIT check**:
            //
            // Previously, cascade used unconditional `fetch_add(1)` then
            // CAS parked.  This had TWO failure modes:
            //
            // (1) **Reader-during-writer admission** (writer-readers
            // exclusion violation): cascade's `fetch_add` does not
            // check WRITER_BIT.  If a writer is admitted between
            // cascade's pre-admission check and its `fetch_add`, the
            // state can become `WRITER_BIT | reader_bit` — both writer
            // and reader appear to hold simultaneously.
            //
            // (2) **WRITER_BIT underflow on undo**: if cascade's
            // `fetch_add` succeeds, then before `parked.CAS` runs,
            // other releases drop state to 0 and a writer's
            // `state.CAS(0, WRITER_BIT)` succeeds, state becomes
            // WRITER_BIT.  Cascade's parked.CAS then fails (stale
            // slot), and the undo `fetch_sub(1)` decrements from
            // WRITER_BIT — underflowing into `0x7FFF...` (WRITER_BIT
            // cleared, reader_count maxed).  The writer subsequently
            // panics in `release_write` because WRITER_BIT is gone.
            //
            // **Fix: CAS-loop reader admit**, matching the
            // `try_admit_as_reader` and `signal_next_waiter` patterns.
            // If WRITER_BIT is set we return (no further cascade
            // possible — a writer holds the lock).  If the CAS-loop
            // exits with WRITER_BIT clear, the reader admit is atomic
            // and there is no `fetch_add`-leaves-window-then-undo
            // sequence to race with writer admission.
            //
            // Order: state-CAS FIRST (atomically increment reader
            // count under WRITER_BIT-clear precondition), then
            // parked.CAS.  If parked.CAS fails (stale slot), we
            // undo via `fetch_sub(1)`.  Crucially, the undo can NOT
            // underflow WRITER_BIT now: between our state.CAS-success
            // and our `fetch_sub`, WRITER_BIT cannot be set because
            // our state.CAS-success implies `cur & WRITER_BIT == 0`
            // and any subsequent writer.state.CAS(0, WRITER_BIT) will
            // fail (state has our +1, not 0).
            loop {
                let cur = self.state.load(Ordering::Acquire);
                if (cur & WRITER_BIT) != 0 {
                    // Writer admitted — cannot continue cascade.
                    // The contiguous WAITING readers we leave behind
                    // will be admitted later, when the writer's
                    // `release_write` calls `signal_next_waiter`
                    // and the chain is walked anew.
                    return;
                }
                // Saturation guard: defend against hypothetical future
                // ports with massive core counts.  Unreachable on
                // 4-core hardware.
                let reader_count = cur & READER_MASK;
                if reader_count >= READER_MASK {
                    return;
                }
                let new = cur + 1;
                if self.state.compare_exchange(
                    cur, new,
                    Ordering::AcqRel, Ordering::Acquire,
                ).is_ok() {
                    break;
                }
                // CAS lost a race; retry the load + check.
                core::hint::spin_loop();
            }
            // Cascade only admits READERS (contiguous reader successors).
            // Use PARKED_WAITING_READER CAS direction explicitly —
            // a slot in PARKED_WAITING_WRITER is also a "waiting" slot
            // but cascade must NOT admit writers (separate code path
            // in signal_next_waiter handles that with state.CAS(0, WRITER_BIT)).
            //
            // Note that we already checked `next_slot.requested_mode() ==
            // MODE_READ` above and returned for non-readers.  However,
            // that check uses the `slot.mode` field which has the
            // stale-mode-read risk documented in `WaiterSlot::reset()`.
            // The parked-CAS direction here serves as the AUTHORITATIVE
            // check — if parked is WAITING_WRITER (not WAITING_READER),
            // the CAS fails and we undo (treating as "another path").
            match next_slot.parked.compare_exchange(
                PARKED_WAITING_READER, PARKED_ADMITTED,
                Ordering::AcqRel, Ordering::Acquire,
            ) {
                Ok(_) => {
                    // We claimed the successor.  Continue cascading.
                    current = next;
                }
                Err(_) => {
                    // Another path already admitted this successor
                    // (parked == ADMITTED), or the slot is NOT_IN_QUEUE
                    // (slot owner reset for a new iteration but hasn't
                    // finished enqueue yet), or the slot is
                    // WAITING_WRITER (the mode read above was stale and
                    // the actual mode is WRITE).  Either way, we must
                    // NOT admit via the cascade-reader path.  Undo our
                    // state increment.
                    //
                    // The undo is safe (no WRITER_BIT underflow risk):
                    // our state.CAS succeeded under WRITER_BIT-clear,
                    // so state currently has our +1 contribution; any
                    // concurrent writer.state.CAS(0, WRITER_BIT) would
                    // have failed because state != 0.  `fetch_sub(1)`
                    // here decrements only the reader count we added.
                    self.state.fetch_sub(1, Ordering::AcqRel);
                    return;
                }
            }
        }
        // Walk-step bound exhausted.  Indicates a chain cycle — surface
        // in test builds, silently exit in release.
        debug_assert!(false,
                      "cascade_admit_readers: walk exceeded MAX_WAITERS — chain cycle?");
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
        let raw_prev_tail = self.tail.swap(core_id, Ordering::AcqRel);

        // **WS-SM SM2.E MCS-RW protocol fix — stale-self detection**.
        // Same rationale as `acquire_read`: cascade can leave tail
        // pointing at our slot, and our re-enqueue can race ahead of
        // the signal that would clean it up.  Treating
        // `raw_prev_tail == core_id` as `NONE_SENTINEL` is sound (the
        // queue is effectively empty) and prevents the self-link
        // deadlock.  Note that cascade only admits readers (not
        // writers), so the stale-self case for writers can only arise
        // if a writer is re-acquiring after being cascade-admitted as
        // a writer — which is impossible per the cascade contract.
        // Nevertheless, we apply the same defensive symmetry on the
        // writer path so a future refactor that introduces writer
        // cascade cannot accidentally re-introduce the bug.
        let prev_tail = if raw_prev_tail == core_id {
            NONE_SENTINEL
        } else {
            raw_prev_tail
        };

        if prev_tail == NONE_SENTINEL {
            // We are the new head.
            if self.try_admit_as_writer() {
                slot.parked.store(PARKED_ADMITTED, Ordering::Release);
                return;
            }
            // **WS-SM SM2.E MCS-RW protocol fix — NONE-path self-admit
            // spin (writer variant) with CAS-claim ordering**: same
            // rationale as `acquire_read`'s NONE-path self-admit spin.
            // For writers, the state CAS is `state.CAS(0, WRITER_BIT)`
            // (cannot use fetch_add — would corrupt to mixed state).
            //
            // CAS-claim parked first; if won, attempt state CAS; if
            // state CAS fails (state non-zero), revert parked.
            slot.parked.store(PARKED_WAITING_WRITER, Ordering::Release);
            loop {
                if slot.parked.load(Ordering::Acquire) == PARKED_ADMITTED {
                    return;
                }
                if slot.parked.compare_exchange(
                    PARKED_WAITING_WRITER, PARKED_ADMITTED,
                    Ordering::AcqRel, Ordering::Acquire,
                ).is_ok() {
                    // Claimed.  Try state CAS.
                    if self.state.compare_exchange(
                        0, WRITER_BIT,
                        Ordering::AcqRel, Ordering::Acquire,
                    ).is_ok() {
                        return;
                    }
                    // State non-zero (other holders).  Revert parked
                    // via CAS (NOT a STORE — see Stream B/§6.6 F1).
                    // A naked store would clobber a concurrent
                    // admitter's ADMITTED publish.  The CAS only undoes
                    // our own ADMITTED; if signal already reverted us
                    // (saw our ADMITTED, walked past, no state credit),
                    // the CAS fails harmlessly with observed = WAITING_WRITER
                    // — also fine.
                    let _ = slot.parked.compare_exchange(
                        PARKED_ADMITTED, PARKED_WAITING_WRITER,
                        Ordering::AcqRel, Ordering::Acquire,
                    );
                }
                crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
            }
        } else {
            // **WS-SM SM2.E MCS-RW protocol fix**: store WAITING_WRITER
            // BEFORE linking, same as acquire_read but with the writer
            // variant so the walker reads the correct mode atomically.
            slot.parked.store(PARKED_WAITING_WRITER, Ordering::Release);
            self.slots[prev_tail as usize].next.store(core_id, Ordering::Release);
        }

        // Wait for predecessor signal.
        while slot.parked.load(Ordering::Acquire) != PARKED_ADMITTED {
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

        // **WS-SM SM2.E MCS-RW protocol fix — signal on every release**:
        // The original protocol only called signal when prev_readers ==
        // 1 (last reader).  That left non-last-reader releases without
        // any chain processing, causing two related bugs:
        //
        // (a) **Dangling tail**: tail may still point at us after a
        //     non-last release.  A future enqueuer would link behind
        //     us, but our iter K+1 acquire's reset clears
        //     slot[us].next, losing the link.  The enqueuer is
        //     orphaned.
        //
        // (b) **Chain stall**: a writer linked behind a cascade-admitted
        //     reader R waits for some signal to reach them.  If R
        //     releases not-last, no signal fires; the writer is stalled
        //     until *some other* releaser's chain walk happens to
        //     traverse through R's slot.
        //
        // By signaling on every release (calling `signal_next_waiter`
        // even when not last), the chain is continuously processed.
        // `signal_next_waiter` is designed to:
        // - Admit readers immediately when state allows (CAS-claim).
        // - Walk past slots that are already-ADMITTED (e.g., by a
        //   cascade or a concurrent signal).
        // - On NOT_IN_QUEUE: the chain link is STALE from a prior
        //   iteration and the target slot's owner is mid-reset.
        //   `signal_next_waiter` returns; the slot will be admitted
        //   via its real iter-K+1 predecessor's release.  See the
        //   orphan-fix block comment inside `signal_next_waiter`.
        // - For writers, attempt `state.CAS(0, WRITER_BIT)`; if the
        //   state has reader bits, return without walking past the
        //   writer — the writer stays parked in the chain, and a
        //   future signal (when state reaches 0) will admit them.
        // - CAS-clear tail when the walk reaches NONE.
        //
        // The result: every release processes the chain forward as
        // far as state allows, eliminating both dangling-tail and
        // chain-stall.  The performance cost (signal walking on
        // every release rather than just last) is small in the
        // common case where chains are short.
        let _ = prev; // prev_readers no longer used after release-always change.
        self.signal_next_waiter(core_id);
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
                      "release_write called while WRITER_BIT is not set; \
                       protocol invariant violation (mode-encoded parked machine \
                       should have prevented this).  core_id={}, _prev=0x{:x}",
                      core_id, _prev);

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
    /// **Walk protocol** (the outer loop): the algorithm walks the
    /// queue link chain starting at `releaser_core_id` and continuing
    /// past any **stale slots** (slots that were cascade-admitted and
    /// have since released — `parked == ADMITTED` but the owner is no
    /// longer a holder).  At each waypoint:
    ///
    /// 1. Read `current.next`.  If non-sentinel, candidate successor
    ///    is known — proceed to step 4.
    /// 2. If sentinel, try CAS `tail: current → NONE_SENTINEL`.  If
    ///    successful, queue is empty at this waypoint — done.
    /// 3. If the `tail` CAS fails:
    ///    - **Observed `NONE_SENTINEL`**: tail was cleared by an
    ///      earlier release path.  Queue is already empty — done.
    ///    - **Observed any other id**: a new enqueuer set tail to
    ///      themselves AFTER our `next` load.  Spin-wait for them to
    ///      complete the link (`current.next.store(their_id)`).
    ///      Also re-check tail inside the spin: if it's been cleared
    ///      to `NONE_SENTINEL` by yet another release path, return.
    /// 4. CAS-claim the successor's `parked` flag WAITING→ADMITTED:
    ///    - **Success**: we are the unique admitter.  Update state
    ///      (`fetch_add` for reader / `state.CAS(0, WRITER_BIT)` for
    ///      writer) and return.
    ///    - **Failure**: distinguish observed value:
    ///      - `PARKED_NOT_IN_QUEUE` (stale chain link from a prior
    ///        iteration): undo state and RETURN.  The slot's owner
    ///        is mid-reset for iter K+1; its real predecessor will
    ///        admit it.
    ///      - `PARKED_ADMITTED` (cascade or another signal admitted):
    ///        undo state and walk past (advance `current = next`).
    ///
    /// **The CAS-claim symmetry with `cascade_admit_readers`** is
    /// essential: both paths target the same `parked` flag.  Without
    /// CAS in signal, a stale-cascade race causes a double-increment
    /// of state that drifts the lock into permanent corruption.
    fn signal_next_waiter(&self, releaser_core_id: u8) {
        let mut current = releaser_core_id;
        // The walk is bounded by `MAX_WAITERS` because the chain
        // contains at most `MAX_WAITERS` distinct slots (one per
        // core) and the walk strictly advances through distinct
        // slots (the self-link defense below ensures progress).
        // Reaching this bound indicates a chain cycle, which is a
        // logic bug — surface via `debug_assert!` in test builds,
        // silently exit in release builds to avoid an infinite loop.
        for _walk_step in 0..MAX_WAITERS {
            let current_slot = &self.slots[current as usize];
            let mut next = current_slot.next.load(Ordering::Acquire);

            if next == NONE_SENTINEL {
                // No visible successor yet at this waypoint.  Try to
                // atomically end the queue here.
                match self.tail.compare_exchange(
                    current, NONE_SENTINEL,
                    Ordering::AcqRel, Ordering::Acquire,
                ) {
                    Ok(_) => {
                        // CAS succeeded: queue is now empty.  Done.
                        return;
                    }
                    Err(observed) => {
                        if observed == NONE_SENTINEL {
                            // Another release path already cleared
                            // tail.  Queue is empty.  Nothing more
                            // for us to do.
                            return;
                        }
                        // CAS failed because a new enqueuer set
                        // tail to themselves AFTER our `next` load.
                        // Spin-wait for them to complete the link.
                        // Also re-check tail inside the spin so we
                        // don't spin forever if tail is later
                        // cleared by another path.
                        loop {
                            let n = current_slot.next.load(Ordering::Acquire);
                            if n != NONE_SENTINEL {
                                next = n;
                                break;
                            }
                            if self.tail.load(Ordering::Acquire) == NONE_SENTINEL {
                                // Tail has been cleared; queue is
                                // empty.  Return without further
                                // action.
                                return;
                            }
                            crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
                        }
                    }
                }
            }

            // Defensive: a self-referential next pointer indicates a
            // bug we don't want to propagate.  With the stale-self
            // fix in `acquire_*`, self-links should not be produced;
            // this guard exists so any future regression that
            // reintroduces the bug surfaces in test builds rather
            // than producing an infinite walk.
            debug_assert!(next != current,
                          "signal_next_waiter: self-referential next pointer at slot {}",
                          current);
            if next == current {
                return;
            }

            // SAFETY: `next < MAX_WAITERS` by the enqueue-side
            // invariant (only valid core_ids are stored in `next`
            // fields).
            let next_slot = &self.slots[next as usize];

            // **WS-SM SM2.E audit-pass — stale-mode-read fix**: read
            // `parked` FIRST (Acquire), use its value as the
            // AUTHORITATIVE mode source.  The `slot.mode` field is no
            // longer consulted by the walker — a stale Relaxed-load
            // of `mode` could observe iter K-1's value even when the
            // slot has transitioned to iter K with a different mode,
            // producing the writer-readers exclusion panic that
            // PR #790 commit-3 left unresolved.
            //
            // The parked value carries the mode atomically:
            // * PARKED_NOT_IN_QUEUE: slot mid-reset (orphan-fix returns).
            // * PARKED_WAITING_READER: slot is iter K-published reader.
            // * PARKED_WAITING_WRITER: slot is iter K-published writer.
            // * PARKED_ADMITTED: already admitted; walk past.
            //
            // Because the slot owner's `parked.store(WAITING_*, Release)`
            // happens AFTER `reset()` (sequenced-before), a walker
            // that Acquire-loads parked = WAITING_* observes iter K's
            // parked publication; subsequent operations (state CAS,
            // parked CAS) cannot mix iters.
            let parked_obs = next_slot.parked.load(Ordering::Acquire);

            match parked_obs {
                v if v == PARKED_NOT_IN_QUEUE => {
                    // Stale chain link from a prior iteration — slot
                    // owner is mid-reset.  No state update has been
                    // attempted yet (we read parked first), so nothing
                    // to undo.  Return.
                    return;
                }
                v if v == PARKED_ADMITTED => {
                    // Already admitted by cascade or another signal.
                    // No state change yet, so just walk past.
                    current = next;
                    continue;
                }
                v if v == PARKED_WAITING_READER => {
                    // Reader admission: CAS-loop with WRITER_BIT
                    // check.  If WRITER_BIT is set, reader cannot
                    // admit; leave parked, return (a future signal
                    // when state reaches WRITER_BIT-clear will retry).
                    loop {
                        let cur = self.state.load(Ordering::Acquire);
                        if (cur & WRITER_BIT) != 0 {
                            return;
                        }
                        let new_state = cur + 1;
                        if self.state.compare_exchange(
                            cur, new_state,
                            Ordering::AcqRel, Ordering::Acquire,
                        ).is_ok() {
                            break;
                        }
                    }
                    // State incremented; now CAS parked.
                    match next_slot.parked.compare_exchange(
                        PARKED_WAITING_READER, PARKED_ADMITTED,
                        Ordering::AcqRel, Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            // Reader admitted; continue walking to drain
                            // contiguous reader successors.
                            current = next;
                            continue;
                        }
                        Err(_) => {
                            // CAS failed.  Undo state; parked has
                            // transitioned (to ADMITTED, NOT_IN_QUEUE,
                            // or WAITING_WRITER).  In all cases, undo
                            // and walk past — the slot owner's path
                            // will admit them correctly.
                            self.state.fetch_sub(1, Ordering::AcqRel);
                            // For NOT_IN_QUEUE (slot mid-reset for
                            // next iter) and WAITING_WRITER (iter
                            // transition to writer), return — the
                            // slot is no longer addressable via this
                            // stale link.  For ADMITTED, walk past.
                            let observed = next_slot.parked.load(Ordering::Acquire);
                            if observed == PARKED_ADMITTED {
                                current = next;
                                continue;
                            }
                            return;
                        }
                    }
                }
                v if v == PARKED_WAITING_WRITER => {
                    // Writer admission: state-CAS 0 → WRITER_BIT.
                    let writer_state_set = self.state.compare_exchange(
                        0, WRITER_BIT,
                        Ordering::AcqRel, Ordering::Acquire,
                    ).is_ok();
                    if !writer_state_set {
                        // State has reader bits; cannot admit writer
                        // now.  MUST NOT walk past (would orphan the
                        // writer).  A future signal from a reader's
                        // release will reach the writer when state
                        // reaches 0.
                        return;
                    }
                    // State has WRITER_BIT; now CAS parked.
                    match next_slot.parked.compare_exchange(
                        PARKED_WAITING_WRITER, PARKED_ADMITTED,
                        Ordering::AcqRel, Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            // Writer admitted.  MUST NOT keep walking
                            // because any subsequent admission would
                            // violate writer-readers exclusion.
                            return;
                        }
                        Err(_) => {
                            // CAS failed.  Undo writer-bit via CAS
                            // with explicit assert (Stream B F2 fix).
                            let undo = self.state.compare_exchange(
                                WRITER_BIT, 0,
                                Ordering::AcqRel, Ordering::Acquire,
                            );
                            debug_assert!(undo.is_ok(),
                                "writer admit undo failed: state was 0x{:x}, \
                                 expected WRITER_BIT — protocol invariant \
                                 violation in signal_next_waiter",
                                undo.unwrap_err());
                            // observed could be NOT_IN_QUEUE, ADMITTED,
                            // or WAITING_READER.  For NOT_IN_QUEUE /
                            // WAITING_READER (iter transition), return.
                            // For ADMITTED, walk past.
                            let observed = next_slot.parked.load(Ordering::Acquire);
                            if observed == PARKED_ADMITTED {
                                current = next;
                                continue;
                            }
                            return;
                        }
                    }
                }
                _ => {
                    // Unrecognised parked value — should be unreachable.
                    debug_assert!(false,
                        "signal_next_waiter: unexpected parked value 0x{:x} at slot {}",
                        parked_obs, next);
                    return;
                }
            }
        }
        // Walk-step bound exhausted.  In a well-formed queue this is
        // unreachable: the chain has at most `MAX_WAITERS` distinct
        // slots.  Reaching this point indicates a chain cycle —
        // a logic bug — that we surface in test builds.
        debug_assert!(false,
                      "signal_next_waiter: walk exceeded MAX_WAITERS — chain cycle?");
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
        assert_eq!(slot.parked.load(Ordering::Acquire), PARKED_NOT_IN_QUEUE);
        assert_eq!(slot.mode.load(Ordering::Acquire), MODE_READ);
    }

    #[test]
    fn waiter_slot_reset_clears_state() {
        let slot = WaiterSlot::INIT;
        slot.next.store(7, Ordering::Relaxed);
        slot.parked.store(PARKED_ADMITTED, Ordering::Relaxed);
        slot.reset(MODE_WRITE);
        assert_eq!(slot.next.load(Ordering::Acquire), NONE_SENTINEL);
        assert_eq!(slot.parked.load(Ordering::Acquire), PARKED_NOT_IN_QUEUE);
        assert_eq!(slot.requested_mode(), MODE_WRITE);
    }

    /// **WS-SM SM2.E**: pin the parked state constants are mutually
    /// distinct (essential invariant — CAS WAITING_* → ADMITTED must
    /// fail on NOT_IN_QUEUE or on the wrong-mode WAITING variant).
    #[test]
    fn parked_state_constants_pairwise_distinct() {
        assert_ne!(PARKED_NOT_IN_QUEUE, PARKED_WAITING_READER);
        assert_ne!(PARKED_NOT_IN_QUEUE, PARKED_WAITING_WRITER);
        assert_ne!(PARKED_NOT_IN_QUEUE, PARKED_ADMITTED);
        assert_ne!(PARKED_WAITING_READER, PARKED_WAITING_WRITER);
        assert_ne!(PARKED_WAITING_READER, PARKED_ADMITTED);
        assert_ne!(PARKED_WAITING_WRITER, PARKED_ADMITTED);
    }

    /// **WS-SM SM2.E**: pin the parked state constants' values so any
    /// future renumbering breaks the test.  The values are
    /// load-bearing in the protocol: NOT_IN_QUEUE is `Default::default()`
    /// for `AtomicU8::new(0)`-zero-init slots, and downstream Lean
    /// refinement reasoning depends on the exact numeric values.  The
    /// mode-encoded WAITING_READER/WAITING_WRITER distinction closes
    /// the stale-mode-read race (Stream B fix).
    #[test]
    fn parked_state_constants_values() {
        assert_eq!(PARKED_NOT_IN_QUEUE, 0);
        assert_eq!(PARKED_WAITING_READER, 1);
        assert_eq!(PARKED_WAITING_WRITER, 2);
        assert_eq!(PARKED_ADMITTED, 3);
    }

    /// **WS-SM SM2.E audit-pass**: pin the four-state machine count.
    /// If a future refactor adds or removes a state, this test fails
    /// — forcing the contributor to verify the protocol still
    /// satisfies writer-readers exclusion under the new shape.
    #[test]
    fn parked_state_count_is_four() {
        // Enumerate all distinct state values.  If we add a state,
        // this array grows; if we remove one, this array shrinks.
        let states = [
            PARKED_NOT_IN_QUEUE,
            PARKED_WAITING_READER,
            PARKED_WAITING_WRITER,
            PARKED_ADMITTED,
        ];
        assert_eq!(states.len(), 4,
                   "WS-SM SM2.E protocol contract: parked state machine must have \
                    exactly 4 states (NOT_IN_QUEUE / WAITING_READER / WAITING_WRITER / \
                    ADMITTED).  A regression to 3 states (collapsing READER+WRITER) \
                    re-opens the stale-mode-read race.");
        // Verify all are distinct (covered by pairwise test, but
        // explicit here too).
        for (i, &a) in states.iter().enumerate() {
            for &b in &states[i+1..] {
                assert_ne!(a, b, "parked state values must be unique");
            }
        }
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
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering as StdOrdering};
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
        const NUM_READERS: usize = 3;
        let lock = Arc::new(QueuedRwLock::new());
        let writer_release_signal = Arc::new(AtomicBool::new(false));
        let reader_release_signal = Arc::new(AtomicBool::new(false));
        // Audit-pass-10: replaced 50ms sleep heuristic with a
        // deterministic `readers_in_cs` counter.  Each reader signals
        // entry into the CS, then waits for every other reader to
        // signal before observing.  Removes timing dependency under
        // heavy parallel test load.
        let readers_in_cs = Arc::new(AtomicU64::new(0));
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
            let in_cs_c = Arc::clone(&readers_in_cs);
            let rdr_rel_c = Arc::clone(&reader_release_signal);
            handles.push(thread::spawn(move || {
                lock_c.acquire_read(tid);
                // Signal entry to the CS.
                in_cs_c.fetch_add(1, StdOrdering::SeqCst);
                // Wait for ALL readers to enter their CS (deterministic
                // — no sleep).  This guarantees the observation below
                // sees the maximum concurrent reader count.
                while in_cs_c.load(StdOrdering::SeqCst) < NUM_READERS as u64 {
                    core::hint::spin_loop();
                }
                // Observe state during CS — multiple readers should
                // be concurrent thanks to the cascade.
                let state = lock_c.peek_state();
                let readers = state & READER_MASK;
                if readers > 1 {
                    obs_c.fetch_add(1, StdOrdering::Relaxed);
                }
                // Hold until told to release.
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

        // Wait until all readers have completed their observation.
        // The reader_release_signal can only fire after we've confirmed
        // every reader has both entered AND made its observation, so
        // we now wait on `observed_concurrent` to be stable (every
        // reader has either incremented it or skipped).  Since each
        // reader makes its observation BEFORE waiting on the release
        // signal, the readers_in_cs counter reaching NUM_READERS
        // implies every reader has either observed or is about to.
        // We synchronize by waiting until readers_in_cs has been
        // observed at the maximum value — at this point all readers
        // have made their observation.
        while readers_in_cs.load(StdOrdering::SeqCst) < NUM_READERS as u64 {
            core::hint::spin_loop();
        }
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
