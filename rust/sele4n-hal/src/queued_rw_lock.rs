// SPDX-License-Identifier: GPL-3.0-or-later
//! QueuedRwLock — ticket-based FIFO-preserving reader-writer lock.
//!
//! **WS-SM SM2.C-defer D-5**: queued RwLock variant that preserves the
//! Lean spec's FIFO admission property (`rwLock_fifo_admission_temporal`).
//!
//! ## Why this is a ticket lock and not an MCS queue
//!
//! Through v0.32.147 this was an MCS-style queue: each core owned one
//! preallocated `WaiterSlot` in a per-lock array, the lock held a `tail`
//! index, and slots were chained by `next` indices while a four-state
//! `parked` machine tracked admission. **It deadlocked**, and the reason
//! was structural rather than a missing case.
//!
//! The captured failure (v0.32.147, full trace in the plan): a writer
//! queued behind a reader, the reader released and its walk *reached* the
//! writer but could not admit it because other readers still held the
//! lock, so it returned — leaving the admission to "a future signal from
//! a reader's release", exactly as that site's comment claimed. The last
//! reader then released, but readers are admitted *en masse* by cascade
//! and release independently, so its slot was no longer in the queue: its
//! `next` was a fossil from an earlier incarnation, its walk dead-ended on
//! a slot that had since been reset, and it never reached the writer. The
//! writer's one remaining link was then destroyed by its predecessor's
//! next `reset()`, and it parked forever with the lock **free** — `state
//! == 0`, no holder, and no releaser left to signal anyone.
//!
//! A first repair recorded the deferred waiter so whoever drained the lock
//! could finish the admission. It fixed that interleaving and immediately
//! exposed a second, independent one: `signal_next_waiter` tripping its
//! own "walk exceeded MAX_WAITERS — chain cycle?" assertion, because two
//! cores can link behind each other across incarnations and close a cycle.
//!
//! Both defects have one cause: **a core's slot is reused the moment it
//! re-acquires, while other cores still hold references to it.** Every
//! guard the old protocol accumulated — stale-self detection, the
//! mode-encoded parked machine, CAS-claim symmetry, walk-past-stale,
//! signal-on-every-release — was a patch on a consequence of that. Adding
//! a sixth patch was not going to converge.
//!
//! A ticket lock has no links, so none of it can happen. There is no
//! `next` to go stale, no slot to reuse, no chain to cycle, no walk to
//! dead-end, and no handoff that can be dropped.
//!
//! ## The algorithm
//!
//! Two monotone counters. `next_ticket` hands out positions;
//! `now_serving` names the position entitled to enter. A waiter spins
//! until `now_serving` reaches its ticket, then:
//!
//! * a **reader** joins the reader count and *immediately* advances
//!   `now_serving`, so a contiguous run of readers enters together;
//! * a **writer** waits for the reader count to reach zero, takes the
//!   lock exclusively, and advances `now_serving` when it releases.
//!
//! `state` keeps its bit-packed layout (bit 63 writer, bits 0..62 reader
//! count), so the writer-readers exclusion invariant and `peek_state` read
//! exactly as before.
//!
//! ## Why it cannot deadlock
//!
//! `now_serving` is advanced **exactly once per ticket**, unconditionally,
//! by whoever that ticket admits — a reader on entry, a writer on exit.
//! No path returns without either advancing it or holding the lock, so it
//! reaches every ticket that is issued. That is the property the MCS
//! version could not maintain: there, the duty to admit the next waiter
//! belonged to whichever core happened to hold a chain reference, and that
//! reference could be stale, destroyed, or unreachable.
//!
//! * **Mutual exclusion.** A writer sets `WRITER_BIT` only by CAS from
//!   `state == 0`, so no reader is active at that instant, and no reader
//!   can enter afterwards because entering requires the ticket the writer
//!   still holds. Two writers hold different tickets.
//! * **Reader concurrency.** Readers pass the ticket on at entry, so every
//!   reader between two writers holds concurrently.
//! * **FIFO.** Admission order *is* ticket order — a stronger and simpler
//!   guarantee than the chain gave.
//! * **Starvation freedom.** A waiter's wait is bounded by the number of
//!   tickets ahead of it.
//! * **Wraparound.** Tickets are `u64`; at one acquisition per nanosecond
//!   that is ~584 years.
//!
//! ## API compatibility
//!
//! `acquire_read` / `release_read` / `acquire_write` / `release_write` and
//! both guards are unchanged, `core_id` is still validated against
//! `MAX_WAITERS`, and `peek_state` / `peek_tail` still report what they
//! did. All twelve cross-thread behavioural tests carried over unchanged
//! and validate this implementation.
//!
//! ## Concurrency-safety note
//!
//! No `unsafe` code: this primitive is built on `AtomicU64` / `AtomicU8`
//! methods that are safe in stable Rust.

// Tests use std; production code is no_std-compatible.
#[cfg(test)]
extern crate std;

// **WS-RR RR6.20**: the atomics this lock is built from come from `loom`
// when the crate is compiled with `--cfg loom`, and from `core`
// otherwise.
//
// This is the whole reason the loom gate can explore anything.  A
// `loom` dev-dependency on its own explores *nothing*: loom instruments
// its own atomic types, and a lock built on `core::sync::atomic` is
// invisible to it however many `loom::model` blocks surround it.  The
// alias is what puts the deployed lock inside the model.
//
// `--cfg loom` is set by `scripts/test_loom_queued_rw_lock.sh` and by
// nothing else; every ordinary build resolves `core`.
#[cfg(not(loom))]
use core::sync::atomic::{fence, AtomicU64, AtomicU8, Ordering};
#[cfg(loom)]
use loom::sync::atomic::{fence, AtomicU64, AtomicU8, Ordering};

/// Sentinel meaning "no core" — `peek_tail` reports this before any core
/// has enqueued on a fresh lock.
const NONE_SENTINEL: u8 = u8::MAX;

/// **WS-LC LC3.1**: the empty value of a withdrawal slot.
///
/// Slots hold `ticket + 1`, so zero is free to mean "nothing withdrawn"
/// without reserving a ticket number.
const NO_WITHDRAWAL: u64 = 0;

/// Number of cores that may contend — one per core. Pinned to
/// `MAX_SECONDARY_CORES + 1 = 4` (boot core + 3 secondaries on RPi5).
///
/// The ticket protocol itself imposes no bound on waiters; this remains
/// the contract on valid `core_id` arguments, which every entry point
/// still checks.
pub const MAX_WAITERS: usize = crate::smp::MAX_SECONDARY_CORES + 1;

// Bit-packed lock state: bit 63 writer-held, bits 0..62 reader count.
//
// Taken from `crate::rw_lock` rather than redeclared.  The two locks
// share this layout by design — the module docs above say `state` keeps
// it, `peek_state` reports it, and `lock_bridge::rw_lock_snapshot` hands
// it to Lean as the abstract `encodeRwLock` form — and one question
// answered in two places will eventually diverge.  There is one
// definition of the layout and both locks read it.
use crate::rw_lock::{READER_MASK, WRITER_BIT};

/// **WS-SM SM2.C-defer D-5**: FIFO-preserving reader-writer lock.
///
/// Refines the abstract `RwLockState` with the additional invariant that
/// admission order matches enqueue order
/// (`rwLock_fifo_admission_temporal` in `RwLock.lean`).
#[repr(C, align(64))]
pub struct QueuedRwLock {
    /// Bit-packed reader count + writer bit.
    state: AtomicU64,
    /// Next ticket to hand out. Monotone; `fetch_add` is the single
    /// enqueue point, which is what makes admission order total.
    next_ticket: AtomicU64,
    /// The ticket currently entitled to enter. Monotone, advanced
    /// exactly once per issued ticket — see the module docs; this is the
    /// whole of the deadlock-freedom argument.
    now_serving: AtomicU64,
    /// The core that most recently took a ticket, or `NONE_SENTINEL` if
    /// none has. Observability only — no protocol decision reads it —
    /// but it keeps `peek_tail`'s meaning ("who enqueued last") for the
    /// cross-thread tests that use it to sequence their threads.
    last_enqueued: AtomicU8,
    /// **WS-LC LC3.1**: one withdrawal slot per core.
    ///
    /// `NO_WITHDRAWAL` (zero) means "this core has withdrawn nothing";
    /// any other value is `ticket + 1` for the ticket it has withdrawn.
    /// The offset is what lets zero be the empty marker without
    /// reserving a ticket value, and it costs the same wraparound
    /// assumption the ticket counters already make.
    ///
    /// A core holds at most one outstanding ticket, so one slot per core
    /// is enough — which is also why the Lean model abstracts the array
    /// to a *set* of withdrawn tickets and states the two consequences
    /// (at most one publication per core, distinct tickets) as
    /// invariants rather than deriving them from the array shape.
    ///
    /// 32 bytes on top of the 25 the other four words use, so the lock
    /// is still one 64-byte cache line.
    cancelled: [AtomicU64; MAX_WAITERS],
}

impl Default for QueuedRwLock {
    fn default() -> Self {
        Self::new()
    }
}

impl QueuedRwLock {
    /// Construct a fresh, unheld queued RwLock.
    ///
    /// `const fn` so QueuedRwLocks can be embedded in `static`
    /// declarations for SM3 per-object locks.
    ///
    /// **WS-RR RR6.20**: `loom`'s atomics are not `const`-constructible,
    /// so under `--cfg loom` the constructor loses its `const` and
    /// `lock_bridge.rs`'s static pool is built through
    /// `loom::lazy_static!` instead.  Nothing else changes, and no
    /// ordinary build sees either variant.
    #[must_use]
    #[inline]
    #[cfg(not(loom))]
    pub const fn new() -> Self {
        Self {
            state: AtomicU64::new(0),
            next_ticket: AtomicU64::new(0),
            now_serving: AtomicU64::new(0),
            last_enqueued: AtomicU8::new(NONE_SENTINEL),
            cancelled: [const { AtomicU64::new(NO_WITHDRAWAL) }; MAX_WAITERS],
        }
    }

    /// **WS-RR RR6.20**: the loom-build constructor.  Same fields, no
    /// `const` — see the note on the `cfg(not(loom))` form above.
    #[must_use]
    #[inline]
    #[cfg(loom)]
    pub fn new() -> Self {
        Self {
            state: AtomicU64::new(0),
            next_ticket: AtomicU64::new(0),
            now_serving: AtomicU64::new(0),
            last_enqueued: AtomicU8::new(NONE_SENTINEL),
            cancelled: core::array::from_fn(|_| AtomicU64::new(NO_WITHDRAWAL)),
        }
    }

    /// **WS-RR RR6.20**: the wait hint both spin loops use.
    ///
    /// On hardware this is the bounded `wfe` park the protocol is built
    /// around.  Under `--cfg loom` it is `loom::thread::yield_now()`:
    /// loom drives the schedule itself, and a spin loop that never
    /// yields to it would explore one interleaving and call the model
    /// complete.  The production path is byte-for-byte what it was.
    #[inline]
    fn park_hint() {
        #[cfg(loom)]
        loom::thread::yield_now();
        #[cfg(not(loom))]
        crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
    }

    /// Peek the bit-packed state (test-only accessor for the Tier-5
    /// cross-language oracle and for unit-test diagnostics).
    #[must_use]
    #[inline]
    pub fn peek_state(&self) -> u64 {
        self.state.load(Ordering::Acquire)
    }

    /// Peek the core at the back of the queue, or `NONE_SENTINEL` when
    /// no core is outstanding.
    ///
    /// Diagnostics and test sequencing only — no protocol decision reads
    /// it. It reports what the MCS `tail` it replaced reported: the most
    /// recent enqueuer while any core is outstanding, and `NONE_SENTINEL`
    /// once the queue drains.
    ///
    /// "Outstanding" is `next_ticket != now_serving`, i.e. some ticket has
    /// been issued that has not yet been passed on. A *reader* holding
    /// the lock is not outstanding by that measure — it passes its ticket
    /// on at entry — which is the same answer the old `tail` gave, since
    /// a cascade-admitted reader was no longer in the chain either.
    ///
    /// `now_serving` is read first so a concurrent enqueue cannot make an
    /// empty queue look occupied.
    #[must_use]
    #[inline]
    pub fn peek_tail(&self) -> u8 {
        let serving = self.now_serving.load(Ordering::Acquire);
        if self.next_ticket.load(Ordering::Acquire) == serving {
            NONE_SENTINEL
        } else {
            self.last_enqueued.load(Ordering::Acquire)
        }
    }

    /// Peek `(next_ticket, now_serving)` — diagnostics and unit tests.
    ///
    /// `next_ticket - now_serving` is the number of cores enqueued and
    /// not yet admitted.
    #[must_use]
    #[inline]
    pub fn peek_tickets(&self) -> (u64, u64) {
        // now_serving first: reading it before next_ticket cannot make
        // the difference appear negative under concurrent enqueue.
        let serving = self.now_serving.load(Ordering::Acquire);
        (self.next_ticket.load(Ordering::Acquire), serving)
    }

    /// Take the next ticket and record the enqueue for `peek_tail`.
    #[inline]
    fn take_ticket(&self, core_id: u8) -> u64 {
        let ticket = self.next_ticket.fetch_add(1, Ordering::AcqRel);
        self.last_enqueued.store(core_id, Ordering::Release);
        ticket
    }

    /// Spin until `ticket` is the one being served.
    #[inline]
    fn await_turn(&self, ticket: u64) {
        while self.now_serving.load(Ordering::Acquire) != ticket {
            Self::park_hint();
        }
    }

    /// Hand the ticket on and wake anyone parked on it, then skip past
    /// any ticket whose holder has **withdrawn**.
    ///
    /// `fetch_add` rather than a store of `ticket + 1`: only the core
    /// being served calls this, and exactly once, so the two are
    /// equivalent — but `fetch_add` cannot regress `now_serving` if that
    /// assumption is ever broken, and a regressing `now_serving` would
    /// admit two cores at once.
    ///
    /// # **WS-LC LC3.2**: the skip loop
    ///
    /// A withdrawn ticket has nobody waiting on it, so nobody will ever
    /// pass it on — and `now_serving` owes exactly one advance per
    /// issued ticket, so it cannot simply be removed.  Whoever uncovers
    /// it retires it instead: claim the slot, advance again, repeat.
    ///
    /// The claim is a **compare-exchange and it is the arbiter**.  The
    /// withdrawing core also checks whether it is the head, so both it
    /// and this loop can reach the same ticket; exactly one of them
    /// wins the exchange, and only the winner advances.  Without that,
    /// two advances for one ticket would run `now_serving` past a live
    /// waiter and admit two cores at once.
    ///
    /// # Termination
    ///
    /// Each iteration *consumes* a published withdrawal, and a core can
    /// publish one only for a ticket it has been issued — so the loop
    /// exits as soon as the uncovered ticket is live, which is after at
    /// most one iteration per outstanding withdrawal.  There is
    /// deliberately no iteration cap: a cap that fired would leave a
    /// tombstone at the head with nobody left to retire it, which is the
    /// stall this loop exists to prevent.  `debug_assert` bounds it in
    /// debug builds so a protocol regression is loud rather than slow.
    #[inline]
    fn pass_turn(&self) {
        let mut uncovered = self.now_serving.fetch_add(1, Ordering::SeqCst) + 1;
        crate::cpu::sev();
        let mut skipped = 0usize;
        while self.claim_withdrawal_of(uncovered) {
            uncovered = self.now_serving.fetch_add(1, Ordering::SeqCst) + 1;
            crate::cpu::sev();
            skipped += 1;
            debug_assert!(
                skipped <= MAX_WAITERS,
                "skip loop exceeded one withdrawal per core; a slot is being \
                 refilled below the ticket being served"
            );
        }
    }

    /// **WS-LC LC3.2**: claim the withdrawal of `ticket`, if one is
    /// published.
    ///
    /// Returns `true` iff *this* call cleared the slot — the arbitration
    /// the skip loop and `cancel` share.  At most one slot can hold a
    /// given ticket, because a ticket is issued to one core and a core
    /// publishes only tickets it holds, so the scan finds at most one
    /// match and one exchange decides it.
    #[inline]
    fn claim_withdrawal_of(&self, ticket: u64) -> bool {
        // The store-load fence that closes the store-buffer window — see
        // `cancel`.  Its partner is the one in `cancel`, and both are
        // needed: this one sits between the caller's own store (the
        // `fetch_add` in `pass_turn`, or the publish in `cancel`) and the
        // slot reads below.
        fence(Ordering::SeqCst);
        let published = ticket + 1;
        for slot in &self.cancelled {
            if slot.load(Ordering::SeqCst) != published {
                continue;
            }
            if slot
                .compare_exchange(published, NO_WITHDRAWAL, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok()
            {
                return true;
            }
        }
        false
    }

    /// **WS-SM SM2.C-defer D-5.5**: acquire a read lock for `core_id`.
    ///
    /// Blocks until every earlier ticket has been served. Readers admit
    /// contiguously: this passes the ticket on as soon as it has joined
    /// the reader count, so a run of queued readers enters together.
    pub fn acquire_read(&self, core_id: u8) {
        let ticket = self.enqueue(core_id);
        self.await_turn(ticket);
        self.complete_read(core_id, ticket);
    }

    /// **WS-LC LC3.1**: begin a *cancellable* acquisition — take a
    /// ticket without waiting for it.
    ///
    /// The caller then either waits for its turn and completes
    /// ([`complete_read`](Self::complete_read) /
    /// [`complete_write`](Self::complete_write)), or gives up and
    /// withdraws ([`cancel`](Self::cancel)).  Exactly one of the three
    /// must happen for every ticket issued: `now_serving` owes one
    /// advance per issue, and all three deliver it.
    ///
    /// This is the entry point a two-phase-locking growing phase needs.
    /// The blocking [`acquire_read`](Self::acquire_read) and
    /// [`acquire_write`](Self::acquire_write) are written *on* it rather
    /// than beside it, so there is one implementation of each step.
    #[must_use]
    pub fn enqueue(&self, core_id: u8) -> u64 {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        self.take_ticket(core_id)
    }

    /// **WS-LC LC3.1**: whether `ticket` is the one currently entitled
    /// to enter, so a caller polling instead of parking can tell when to
    /// complete.
    #[must_use]
    #[inline]
    pub fn is_served(&self, ticket: u64) -> bool {
        // `SeqCst`, and this is the other half — see `cancel`.
        self.now_serving.load(Ordering::SeqCst) == ticket
    }

    /// **WS-LC LC3.1**: complete a read acquisition begun with
    /// [`enqueue`](Self::enqueue).
    ///
    /// The caller must hold `ticket` and it must be served
    /// ([`is_served`](Self::is_served)).
    pub fn complete_read(&self, core_id: u8, ticket: u64) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        debug_assert!(
            self.is_served(ticket),
            "complete_read called on a ticket that is not being served"
        );

        // Our turn. No writer can hold the lock here: a writer clears
        // WRITER_BIT before advancing `now_serving` past its own ticket,
        // so by the time we are served the bit is already clear.
        debug_assert!(
            (self.state.load(Ordering::Acquire) & WRITER_BIT) == 0,
            "writer-readers exclusion violated: reader served while \
             WRITER_BIT set"
        );
        self.state.fetch_add(1, Ordering::AcqRel);

        // Pass the ticket on BEFORE returning, so the next queued reader
        // enters concurrently with us rather than after our release.
        self.pass_turn();
    }

    /// **WS-LC LC3.1**: complete a write acquisition begun with
    /// [`enqueue`](Self::enqueue), blocking until the readers admitted
    /// ahead of it have drained.
    ///
    /// The writer keeps its ticket; [`release_write`](Self::release_write)
    /// retires it.
    pub fn complete_write(&self, core_id: u8, ticket: u64) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        debug_assert!(
            self.is_served(ticket),
            "complete_write called on a ticket that is not being served"
        );
        // Readers admitted ahead of us may still hold, but no NEW reader
        // can enter — entering requires the ticket we hold — so the
        // count is monotonically decreasing and this terminates.
        //
        // Admission is a CAS from exactly `0`, never `fetch_or`: the CAS
        // is what makes "no reader is active at the instant the writer
        // bit is set" a property of the operation rather than of the
        // preceding load.
        while self
            .state
            .compare_exchange(0, WRITER_BIT, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            Self::park_hint();
        }
    }

    /// **WS-LC LC3.1**: withdraw a request begun with
    /// [`enqueue`](Self::enqueue).
    ///
    /// Removes the caller's request from the queue.  It **releases
    /// nothing** — a withdrawal is not a release, so it cannot break
    /// exclusion — and it costs the waiters behind it nothing: their
    /// tickets are unchanged and the withdrawn one is retired without
    /// admitting anybody.
    ///
    /// # Publish, *then* check
    ///
    /// The order is the protocol, not a preference.  Publishing first
    /// means a concurrent [`pass_turn`](Self::pass_turn) that reaches
    /// this ticket either sees the publication and skips it, or does not
    /// — in which case it has not yet advanced past us, so our own head
    /// check will still find us served and we retire the ticket
    /// ourselves.  Checking first loses that: the previous holder can
    /// pass into our ticket and find the slot empty between our check
    /// and our store, after which nobody is left to retire it and the
    /// lock stalls with a tombstone at the head.
    ///
    /// The compare-exchange in [`claim_withdrawal_of`](Self::claim_withdrawal_of)
    /// is what keeps the other direction safe: when both we and the
    /// previous holder reach the ticket, exactly one of us clears the
    /// slot and advances.
    ///
    /// # Why there is a fence on each side
    ///
    /// Publish-then-check is the **store-buffer** shape: we store our
    /// slot and then load `now_serving`, while the core ahead stores
    /// `now_serving` (its `fetch_add`) and then loads our slot.  A store
    /// followed by a load of a *different* location is the one pair that
    /// acquire/release ordering does not constrain, so **both** loads may
    /// return the pre-store value: we conclude we are not the head, the
    /// core ahead concludes there is nothing to skip, and the ticket is
    /// never retired.
    ///
    /// That is not a theoretical reading.  `loom` produced exactly that
    /// interleaving against the first version of this function, and
    /// reported the result the model is written to catch: `now_serving`
    /// one short of `next_ticket`, the slot still published, the lock
    /// stalled with a tombstone at the head.
    ///
    /// The fix is the textbook one and it is a `SeqCst` **fence** on each
    /// side — here, and at the top of
    /// [`claim_withdrawal_of`](Self::claim_withdrawal_of), which is the
    /// path both the skip loop and this function reach the slot through.
    /// A fence is what orders a store against a later load; making the
    /// four accesses themselves `SeqCst` is not enough, and it was tried
    /// first.  With the fences, at least one side observes the other and
    /// the compare-exchange decides which one acts.
    ///
    /// On the deployed architecture this is cheap: AArch64's `stlr` /
    /// `ldar` are already sequentially consistent, so the fence adds one
    /// `dmb ish` and nothing else changes.
    ///
    /// # Refinement
    ///
    /// Corresponds to the Lean block `queuedBlock.cancel_queued` — the
    /// publish followed by `skipDeadOps`, one shape covering both cases
    /// this function branches on (`QueuedRwLockRefinement.lean`).
    pub fn cancel(&self, core_id: u8, ticket: u64) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        self.cancelled[core_id as usize].store(ticket + 1, Ordering::SeqCst);
        fence(Ordering::SeqCst);
        if self.is_served(ticket) && self.claim_withdrawal_of(ticket) {
            // We were the head and we won the slot, so retiring this
            // ticket is ours to do; `pass_turn` also skips whatever it
            // uncovers.
            self.pass_turn();
        } else {
            // Somebody ahead of us will uncover the tombstone and skip
            // it.  Wake any core parked waiting for its own turn.
            crate::cpu::sev();
        }
    }

    /// **WS-LC LC3.1**: whether `core_id` has a withdrawal published and
    /// unclaimed — the test-only accessor the Tier-5 oracle reads.
    #[must_use]
    #[inline]
    pub fn peek_withdrawal(&self, core_id: u8) -> Option<u64> {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        match self.cancelled[core_id as usize].load(Ordering::Acquire) {
            NO_WITHDRAWAL => None,
            published => Some(published - 1),
        }
    }

    /// **WS-SM SM2.C-defer D-5.6**: release a read lock held by `core_id`.
    ///
    /// The ticket was passed on at acquire, so this only leaves the
    /// reader count — there is no successor to signal and therefore no
    /// handoff that can be lost.
    pub fn release_read(&self, core_id: u8) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        let prev = self.state.fetch_sub(1, Ordering::AcqRel);
        debug_assert!(
            (prev & WRITER_BIT) == 0,
            "release_read called while WRITER_BIT is set"
        );
        debug_assert!(
            (prev & READER_MASK) != 0,
            "release_read called with no readers held (count underflow)"
        );
        // Wake a writer that is waiting for the reader count to drain.
        crate::cpu::sev();
    }

    /// **WS-SM SM2.C-defer D-5.5**: acquire a write lock for `core_id`.
    ///
    /// Blocks until every earlier ticket has been served, then until the
    /// readers admitted ahead of it have drained.
    pub fn acquire_write(&self, core_id: u8) {
        let ticket = self.enqueue(core_id);
        self.await_turn(ticket);
        self.complete_write(core_id, ticket);
    }

    /// **WS-SM SM2.C-defer D-5.6**: release a write lock held by `core_id`.
    ///
    /// Clears the writer bit, then passes the ticket on. That order is
    /// required: a reader served by the next ticket must not observe
    /// WRITER_BIT still set.
    pub fn release_write(&self, core_id: u8) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        let prev = self.state.fetch_and(READER_MASK, Ordering::AcqRel);
        debug_assert!(
            (prev & WRITER_BIT) != 0,
            "release_write called while WRITER_BIT is not set; core_id={}, prev=0x{:x}",
            core_id,
            prev
        );
        debug_assert!(
            (prev & READER_MASK) == 0,
            "writer-readers exclusion violated: readers present at write release"
        );
        self.pass_turn();
    }

    /// **WS-RR RR6.1**: take the currently-served ticket, or fail.
    ///
    /// Returns `Some(ticket)` iff a ticket was issued *and* it is the
    /// one `now_serving` names, so the caller may proceed straight to
    /// the served-ticket tail with no `await_turn` spin.  Returns `None`
    /// without issuing anything otherwise.
    ///
    /// # Why the CAS rather than `take_ticket`'s `fetch_add`
    ///
    /// `fetch_add` always issues, so a caller that then finds itself not
    /// served must either spin (blocking) or retire a ticket it never
    /// used.  `compare_exchange(t, t + 1)` guarded by `t == now_serving`
    /// issues *only* when the ticket will be served immediately, so a
    /// failed attempt leaves both counters untouched.
    ///
    /// # Why success implies the ticket is served
    ///
    /// `now_serving` is read first.  If it advanced between that read
    /// and the CAS, then `next_ticket` advanced at least as far
    /// (`now_serving <= next_ticket` is the protocol invariant) and the
    /// CAS from `t` fails.  If the CAS succeeds, ticket `t` was issued
    /// by *this* call, and a ticket is retired only by its holder, so
    /// nothing could have advanced `now_serving` past `t`.  Hence
    /// `now_serving == t` on success.
    ///
    /// This is the single-attempt analogue of `take_ticket` +
    /// `await_turn`; every protocol property the pair establishes is
    /// established here, and the issued ticket is still retired exactly
    /// once (by `pass_turn` on the caller's entry or exit path).
    #[inline]
    fn try_take_served_ticket(&self, core_id: u8) -> Option<u64> {
        let serving = self.now_serving.load(Ordering::Acquire);
        if self
            .next_ticket
            .compare_exchange(serving, serving + 1, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return None;
        }
        self.last_enqueued.store(core_id, Ordering::Release);
        Some(serving)
    }

    /// **WS-RR RR6.1**: attempt a read acquire once, without blocking.
    ///
    /// Returns `true` iff the read lock was acquired.  On `true` the
    /// state moved exactly as [`acquire_read`](Self::acquire_read) would
    /// have: the reader count rose by one and the ticket was passed on,
    /// so the lock is left in the same condition a blocking acquire
    /// leaves it.  On `false` nothing was written at all.
    ///
    /// # Why this exists
    ///
    /// The Tier-5 cross-language oracle drives a *real* lock rather than
    /// a software mirror of it.  A single-threaded driver cannot call
    /// [`acquire_read`](Self::acquire_read) when a ticket is outstanding
    /// ahead of it — `await_turn` would park forever, since the only
    /// core that could advance `now_serving` is the one parked.
    ///
    /// # Refinement
    ///
    /// Corresponds to the Lean concrete block
    /// `[.nextTicketFetchAdd, .lastEnqueuedStore, .nowServingLoad,
    ///   .stateLoad, .stateFetchAddReader, .nowServingFetchAdd, .sev]`
    /// (`QueuedRwLockOp` in
    /// `SeLe4n/Kernel/Concurrency/Locks/QueuedRwLockRefinement.lean`).
    ///
    /// # API contract
    ///
    /// A `true` return MUST be paired with exactly one
    /// [`release_read`](Self::release_read).
    #[must_use]
    pub fn try_acquire_read(&self, core_id: u8) -> bool {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        if self.try_take_served_ticket(core_id).is_none() {
            return false;
        }
        // Served. No writer can hold here: a writer holds its ticket
        // from admission until `release_write` passes it on, and clears
        // WRITER_BIT before doing so — so a served ticket implies the
        // bit is clear, exactly as in `acquire_read`.
        debug_assert!(
            (self.state.load(Ordering::Acquire) & WRITER_BIT) == 0,
            "writer-readers exclusion violated: reader served while \
             WRITER_BIT set"
        );
        self.state.fetch_add(1, Ordering::AcqRel);
        self.pass_turn();
        true
    }

    /// **WS-RR RR6.1**: attempt a write acquire once, without blocking.
    ///
    /// Returns `true` iff the write lock was acquired.  On `true` the
    /// caller holds both the lock and its ticket, exactly as after
    /// [`acquire_write`](Self::acquire_write); the ticket is retired by
    /// [`release_write`](Self::release_write).
    ///
    /// On `false` the attempt either issued nothing, or — when it was
    /// served but readers admitted ahead of it had not drained — passes
    /// its ticket straight on.  Passing on a ticket the holder never
    /// used is the same single advance the protocol requires of every
    /// issued ticket, so `now_serving` still advances exactly once per
    /// issue and no waiter is stranded.
    ///
    /// # API contract
    ///
    /// A `true` return MUST be paired with exactly one
    /// [`release_write`](Self::release_write).
    #[must_use]
    pub fn try_acquire_write(&self, core_id: u8) -> bool {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        if self.try_take_served_ticket(core_id).is_none() {
            return false;
        }
        // Served. Admission is a CAS from exactly `0`, as in
        // `acquire_write` — readers admitted ahead of us may still hold.
        if self
            .state
            .compare_exchange(0, WRITER_BIT, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            return true;
        }
        // Not admitted: retire the ticket we were served rather than
        // hold it, so the next waiter is not blocked behind an attempt
        // that gave up.
        self.pass_turn();
        false
    }

    /// Acquire a read lock, returning an RAII guard.
    #[must_use]
    pub fn acquire_read_guard(&self, core_id: u8) -> QueuedRwLockReadGuard<'_> {
        self.acquire_read(core_id);
        QueuedRwLockReadGuard {
            lock: self,
            core_id,
        }
    }

    /// Acquire a write lock, returning an RAII guard.
    #[must_use]
    pub fn acquire_write_guard(&self, core_id: u8) -> QueuedRwLockWriteGuard<'_> {
        self.acquire_write(core_id);
        QueuedRwLockWriteGuard {
            lock: self,
            core_id,
        }
    }
}

// ============================================================================
// RAII guards
// ============================================================================

/// RAII read guard — releases on drop, including during unwind.
pub struct QueuedRwLockReadGuard<'a> {
    lock: &'a QueuedRwLock,
    core_id: u8,
}

impl Drop for QueuedRwLockReadGuard<'_> {
    fn drop(&mut self) {
        self.lock.release_read(self.core_id);
    }
}

/// RAII write guard — releases on drop, including during unwind.
pub struct QueuedRwLockWriteGuard<'a> {
    lock: &'a QueuedRwLock,
    core_id: u8,
}

impl Drop for QueuedRwLockWriteGuard<'_> {
    fn drop(&mut self) {
        self.lock.release_write(self.core_id);
    }
}
// ============================================================================
// WS-RR RR6.20 — loom exhaustive-interleaving model
// ============================================================================

/// **WS-RR RR6.20**: `loom::model` runs over the **deployed** lock.
///
/// These compile only under `--cfg loom`, where the atomics alias at the
/// top of this file resolves to `loom::sync::atomic`.  That is what
/// makes them explore anything: loom instruments its own atomic types,
/// so a `loom::model` block around a lock built on `core::sync::atomic`
/// would run one interleaving and report success.
///
/// The plan's D-5 acceptance gate is "exhaustive-interleaving runs pass
/// on op-sequences of length ≤ 4", so each model is two threads with one
/// or two lock operations each — which is where loom's exploration is
/// exhaustive rather than bounded.
///
/// Run with `scripts/test_loom_queued_rw_lock.sh`.
#[cfg(loom)]
mod loom_model {
    use super::*;
    use loom::sync::atomic::AtomicUsize;
    use loom::sync::Arc;

    /// Mutual exclusion: two writers, and neither observes the other
    /// inside its critical section.
    ///
    /// The assertion is on the packed word, so it fails on the exact
    /// state the protocol forbids — `WRITER_BIT` together with a second
    /// writer's, or with a reader's count.
    #[test]
    fn two_writers_are_mutually_exclusive() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let a = Arc::clone(&lock);
            let t = loom::thread::spawn(move || {
                a.acquire_write(0);
                assert_eq!(a.peek_state(), WRITER_BIT, "writer saw a foreign holder");
                a.release_write(0);
            });
            lock.acquire_write(1);
            assert_eq!(lock.peek_state(), WRITER_BIT, "writer saw a foreign holder");
            lock.release_write(1);
            t.join().unwrap();
            assert_eq!(lock.peek_state(), 0, "the lock did not drain");
        });
    }

    /// Writer-readers exclusion: a reader and a writer contend, and the
    /// writer never holds while the reader count is non-zero.
    #[test]
    fn reader_and_writer_never_overlap() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let a = Arc::clone(&lock);
            let t = loom::thread::spawn(move || {
                a.acquire_read(0);
                assert_eq!(
                    a.peek_state() & WRITER_BIT,
                    0,
                    "reader admitted while the writer bit was set"
                );
                a.release_read(0);
            });
            lock.acquire_write(1);
            assert_eq!(
                lock.peek_state() & READER_MASK,
                0,
                "writer admitted with readers still holding"
            );
            lock.release_write(1);
            t.join().unwrap();
            assert_eq!(lock.peek_state(), 0);
        });
    }

    /// Reader concurrency: two readers, and neither is excluded by the
    /// other — the count is always in `1..=2` while either holds.
    #[test]
    fn two_readers_share_the_lock() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let a = Arc::clone(&lock);
            let t = loom::thread::spawn(move || {
                a.acquire_read(0);
                let s = a.peek_state();
                assert_eq!(s & WRITER_BIT, 0);
                assert!((1..=2).contains(&(s & READER_MASK)), "reader count {s:#x}");
                a.release_read(0);
            });
            lock.acquire_read(1);
            let s = lock.peek_state();
            assert_eq!(s & WRITER_BIT, 0);
            assert!((1..=2).contains(&(s & READER_MASK)), "reader count {s:#x}");
            lock.release_read(1);
            t.join().unwrap();
            assert_eq!(lock.peek_state(), 0);
        });
    }

    /// The ticket interval closes on every interleaving: `now_serving`
    /// advances exactly once per issued ticket, so once both threads
    /// have released, nothing is outstanding.
    ///
    /// This is the state-level half of `queuedSim`'s ticket-interval
    /// conjunct (`QueuedRwLockRefinement.lean` §3), checked here against
    /// every schedule rather than against one.
    #[test]
    fn ticket_interval_closes_on_every_interleaving() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let a = Arc::clone(&lock);
            let t = loom::thread::spawn(move || {
                a.acquire_read(0);
                a.release_read(0);
            });
            lock.acquire_write(1);
            lock.release_write(1);
            t.join().unwrap();
            let (next, serving) = lock.peek_tickets();
            assert_eq!(next, serving, "a ticket was issued and never retired");
            assert_eq!(next, 2, "exactly one ticket per acquisition");
            assert_eq!(lock.peek_state(), 0);
            assert_eq!(lock.peek_tail(), NONE_SENTINEL);
        });
    }

    /// A refused non-blocking write attempt retires the ticket it was
    /// served, so it cannot strand a later waiter — the property WS-RR
    /// RR6.1's `try_acquire_write` documents.
    #[test]
    fn refused_try_acquire_write_leaves_nothing_outstanding() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let a = Arc::clone(&lock);
            let t = loom::thread::spawn(move || {
                if a.try_acquire_write(0) {
                    a.release_write(0);
                }
            });
            if lock.try_acquire_read(1) {
                lock.release_read(1);
            }
            t.join().unwrap();
            let (next, serving) = lock.peek_tickets();
            assert_eq!(next, serving, "a refused attempt left a ticket outstanding");
            assert_eq!(lock.peek_state(), 0);
        });
    }

    // ------------------------------------------------------------------
    // WS-LC LC3.3 — the withdrawal race
    // ------------------------------------------------------------------
    //
    // Four models, and between them they cover every way the canceller and
    // the core ahead of it can meet.  The interval check is the load-bearing
    // assertion in three of them: a withdrawal that nobody retires does not
    // deadlock the model — the threads all finish — it leaves `now_serving`
    // short of `next_ticket`, with a tombstone at the head and no core left
    // to skip it.  That is the stall, and `next == serving` is what sees it.

    /// A **mid-queue** withdrawal is retired by the core ahead of it, and
    /// retires nothing else: the interval still closes and the lock still
    /// drains.
    ///
    /// The case no existing model covers — every other retirement in this
    /// protocol is performed by the ticket's own holder from the head.
    #[test]
    fn mid_queue_withdrawal_is_skipped_by_the_core_ahead() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let a = Arc::clone(&lock);
            // Core 0 takes the lock first, so core 1's ticket is behind it.
            lock.acquire_write(0);
            let ticket = lock.enqueue(1);
            let t = loom::thread::spawn(move || {
                a.cancel(1, ticket);
            });
            lock.release_write(0);
            t.join().unwrap();
            let (next, serving) = lock.peek_tickets();
            assert_eq!(
                next, serving,
                "a withdrawn ticket was never retired: the lock is stalled                  (slot={:?}, state={:#x})",
                lock.peek_withdrawal(1),
                lock.peek_state()
            );
            assert_eq!(next, 2, "exactly one ticket per enqueue");
            assert_eq!(lock.peek_state(), 0, "a withdrawal must release nothing");
            assert_eq!(
                lock.peek_withdrawal(1),
                None,
                "the withdrawal slot was not reclaimed"
            );
        });
    }

    /// The withdrawal races the **turn-pass from both sides**: the
    /// canceller's own head check and the previous holder's skip loop can
    /// reach the same ticket, and the compare-exchange decides.  Two
    /// advances for one ticket would run `now_serving` past `next_ticket`.
    #[test]
    fn withdrawal_races_pass_turn_from_both_sides() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let a = Arc::clone(&lock);
            lock.acquire_write(0);
            let ticket = lock.enqueue(1);
            // Both threads can reach ticket 1: one releasing into it, one
            // withdrawing from it.
            let t = loom::thread::spawn(move || {
                a.release_write(0);
            });
            lock.cancel(1, ticket);
            t.join().unwrap();
            let (next, serving) = lock.peek_tickets();
            assert_eq!(
                serving, next,
                "the ticket was retired twice (or not at all): both sides of \
                 the race advanced, or neither did"
            );
            assert_eq!(next, 2);
            assert_eq!(lock.peek_state(), 0);
            assert_eq!(lock.peek_withdrawal(1), None);
        });
    }

    /// A withdrawal of the **already-served** ticket — the canceller is the
    /// head — is retired by the canceller itself, since nobody else will
    /// ever pass it on.
    #[test]
    fn withdrawal_of_a_served_ticket_retires_itself() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let a = Arc::clone(&lock);
            // Nothing holds the lock, so core 0's ticket is served at once.
            let ticket = lock.enqueue(0);
            let t = loom::thread::spawn(move || {
                a.acquire_read(1);
                a.release_read(1);
            });
            lock.cancel(0, ticket);
            t.join().unwrap();
            let (next, serving) = lock.peek_tickets();
            assert_eq!(serving, next, "the served ticket was never retired");
            assert_eq!(next, 2);
            assert_eq!(lock.peek_state(), 0);
            assert_eq!(lock.peek_withdrawal(0), None);
        });
    }

    /// **Mutual exclusion survives a withdrawal.**  A core that withdraws
    /// releases nothing, so it cannot let a second writer in; and the
    /// skip must not advance `now_serving` past the ticket of a core that
    /// is still waiting.
    #[test]
    fn writers_stay_exclusive_across_a_withdrawal() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let held = Arc::new(AtomicUsize::new(0));
            let a = Arc::clone(&lock);
            let ha = Arc::clone(&held);
            // Core 2 withdraws from behind, while cores 0 and 1 both write.
            let ticket = {
                lock.acquire_write(0);
                let t = lock.enqueue(2);
                lock.release_write(0);
                t
            };
            let t = loom::thread::spawn(move || {
                a.cancel(2, ticket);
                a.acquire_write(1);
                let prev = ha.fetch_add(1, Ordering::AcqRel);
                assert_eq!(prev, 0, "two writers held the lock at once");
                ha.fetch_sub(1, Ordering::AcqRel);
                a.release_write(1);
            });
            lock.acquire_write(0);
            let prev = held.fetch_add(1, Ordering::AcqRel);
            assert_eq!(prev, 0, "two writers held the lock at once");
            held.fetch_sub(1, Ordering::AcqRel);
            lock.release_write(0);
            t.join().unwrap();
            let (next, serving) = lock.peek_tickets();
            assert_eq!(serving, next, "a ticket was issued and never retired");
            assert_eq!(lock.peek_state(), 0);
        });
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
    fn const_max_waiters_is_4() {
        assert_eq!(MAX_WAITERS, 4);
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

    // ------------------------------------------------------------------
    // WS-RR RR6.1 — non-blocking single-attempt entry points
    // ------------------------------------------------------------------

    /// **RR6.1**: on an unheld lock a read attempt succeeds and leaves
    /// the lock exactly as `acquire_read` does — reader count up by one,
    /// ticket passed on, nothing outstanding.
    #[test]
    fn try_acquire_read_matches_acquire_read_on_uncontended() {
        let attempted = QueuedRwLock::new();
        let blocking = QueuedRwLock::new();
        for _ in 0..4 {
            assert!(
                attempted.try_acquire_read(0),
                "uncontended attempt succeeds"
            );
            blocking.acquire_read(0);
            assert_eq!(attempted.peek_state(), blocking.peek_state());
            assert_eq!(attempted.peek_tickets(), blocking.peek_tickets());
        }
        for _ in 0..4 {
            attempted.release_read(0);
            blocking.release_read(0);
            assert_eq!(attempted.peek_state(), blocking.peek_state());
        }
        assert_eq!(attempted.peek_state(), 0);
        assert_eq!(attempted.peek_tail(), NONE_SENTINEL);
    }

    /// **RR6.1**: on an unheld lock a write attempt succeeds and leaves
    /// the lock exactly as `acquire_write` does — writer bit set and the
    /// ticket still held (retired by `release_write`).
    #[test]
    fn try_acquire_write_matches_acquire_write_on_uncontended() {
        let attempted = QueuedRwLock::new();
        let blocking = QueuedRwLock::new();
        assert!(
            attempted.try_acquire_write(1),
            "uncontended attempt succeeds"
        );
        blocking.acquire_write(1);
        assert_eq!(attempted.peek_state(), blocking.peek_state());
        assert_eq!(attempted.peek_tickets(), blocking.peek_tickets());
        assert_eq!(attempted.peek_state(), WRITER_BIT);
        // The writer's ticket is outstanding while it holds.
        assert_eq!(attempted.peek_tickets(), (1, 0));
        attempted.release_write(1);
        blocking.release_write(1);
        assert_eq!(attempted.peek_state(), blocking.peek_state());
        assert_eq!(attempted.peek_tickets(), blocking.peek_tickets());
        assert_eq!(attempted.peek_state(), 0);
    }

    /// **RR6.1**: a write attempt served while readers hold retires its
    /// ticket instead of keeping it, so `now_serving` still advances
    /// exactly once per issue and no later waiter is stranded.
    #[test]
    fn try_acquire_write_under_readers_retires_its_ticket() {
        let lock = QueuedRwLock::new();
        assert!(lock.try_acquire_read(0));
        let (next_before, serving_before) = lock.peek_tickets();
        assert_eq!(next_before, serving_before, "reader passed its ticket on");

        assert!(
            !lock.try_acquire_write(1),
            "writer must not admit under a reader"
        );
        assert_eq!(
            lock.peek_state(),
            1,
            "the failed attempt left the state alone"
        );
        let (next_after, serving_after) = lock.peek_tickets();
        assert_eq!(
            next_after - serving_after,
            0,
            "a served-but-refused writer must not leave its ticket outstanding"
        );
        assert_eq!(next_after, next_before + 1, "exactly one ticket was issued");
        assert_eq!(
            serving_after,
            serving_before + 1,
            "and it was retired exactly once"
        );

        // The queue is usable afterwards.
        lock.release_read(0);
        assert!(lock.try_acquire_write(1));
        lock.release_write(1);
        assert_eq!(lock.peek_state(), 0);
    }

    /// **RR6.1**: a read attempt fails, and writes nothing at all, when a
    /// ticket is outstanding ahead of it.
    #[test]
    fn try_acquire_read_fails_while_a_ticket_is_outstanding() {
        let lock = QueuedRwLock::new();
        // A writer holds, so its ticket is outstanding.
        assert!(lock.try_acquire_write(0));
        let state_before = lock.peek_state();
        let tickets_before = lock.peek_tickets();
        assert!(!lock.try_acquire_read(1));
        assert_eq!(lock.peek_state(), state_before);
        assert_eq!(
            lock.peek_tickets(),
            tickets_before,
            "a refused attempt issues no ticket"
        );
        lock.release_write(0);
        assert!(lock.try_acquire_read(1));
        lock.release_read(1);
    }

    /// **RR6.1**: two write attempts cannot both succeed.
    #[test]
    fn try_acquire_write_is_exclusive() {
        let lock = QueuedRwLock::new();
        assert!(lock.try_acquire_write(0));
        assert!(!lock.try_acquire_write(1));
        assert_eq!(lock.peek_state(), WRITER_BIT);
        lock.release_write(0);
    }

    /// **RR6.1**: `core_id` is validated on the non-blocking entries too.
    #[test]
    #[should_panic(expected = "core_id out of range")]
    fn try_acquire_read_rejects_out_of_range_core_id() {
        let lock = QueuedRwLock::new();
        let _ = lock.try_acquire_read(MAX_WAITERS as u8);
    }

    /// **RR6.1**: same for the write entry.
    #[test]
    #[should_panic(expected = "core_id out of range")]
    fn try_acquire_write_rejects_out_of_range_core_id() {
        let lock = QueuedRwLock::new();
        let _ = lock.try_acquire_write(MAX_WAITERS as u8);
    }

    /// **RR6.1**: signature pin — both attempts are
    /// `(&self, u8) -> bool` and `#[must_use]`.
    #[test]
    fn signature_pin_try_acquire() {
        let _r: fn(&QueuedRwLock, u8) -> bool = QueuedRwLock::try_acquire_read;
        let _w: fn(&QueuedRwLock, u8) -> bool = QueuedRwLock::try_acquire_write;
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
        assert_eq!(
            lock.peek_state(),
            1,
            "reader count should be 1 after acquire"
        );
        lock.release_read(0);
        assert_eq!(lock.peek_state(), 0, "state should clear after release");
    }

    /// Sequential acquire-then-release for a single writer.
    #[test]
    fn single_writer_acquire_release() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        assert_eq!(
            lock.peek_state(),
            WRITER_BIT,
            "writer bit should be set after acquire"
        );
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

    /// WS-LC LC3.1: the withdrawal slots fit the cache line the lock
    /// already occupies, so adding them costs no second line.
    #[test]
    fn withdrawal_slots_fit_the_cache_line() {
        assert!(core::mem::size_of::<QueuedRwLock>() <= 64);
    }

    // ------------------------------------------------------------------
    // WS-LC LC3.1/LC3.2 — the withdrawal
    // ------------------------------------------------------------------

    /// A withdrawal of the ticket currently being served is retired by
    /// the withdrawing core itself: nobody else will ever pass it on.
    #[test]
    fn cancel_of_a_served_ticket_retires_it() {
        let lock = QueuedRwLock::new();
        let ticket = lock.enqueue(0);
        assert!(
            lock.is_served(ticket),
            "a fresh lock serves the first ticket"
        );

        lock.cancel(0, ticket);

        let (next, serving) = lock.peek_tickets();
        assert_eq!(next, 1, "one ticket was issued");
        assert_eq!(serving, next, "and it was retired");
        assert_eq!(lock.peek_withdrawal(0), None, "the slot was reclaimed");
        assert_eq!(lock.peek_state(), 0, "a withdrawal releases nothing");
    }

    /// A withdrawal from behind a holder is retired by that holder's
    /// release, and until then it is a tombstone: the lock word is
    /// untouched and `now_serving` has not moved.
    #[test]
    fn cancel_behind_a_holder_is_retired_by_the_release() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        let ticket = lock.enqueue(1);
        assert!(!lock.is_served(ticket), "the writer still holds its ticket");

        lock.cancel(1, ticket);
        assert_eq!(
            lock.peek_state(),
            WRITER_BIT,
            "a withdrawal must not release the writer's lock"
        );
        assert_eq!(
            lock.peek_withdrawal(1),
            Some(ticket),
            "the withdrawal is published until somebody uncovers it"
        );
        let (_, serving_before) = lock.peek_tickets();
        assert_eq!(serving_before, 0, "nothing has been retired yet");

        lock.release_write(0);

        let (next, serving) = lock.peek_tickets();
        assert_eq!(next, 2);
        assert_eq!(serving, next, "the release skipped the tombstone");
        assert_eq!(lock.peek_withdrawal(1), None);
        assert_eq!(lock.peek_state(), 0);
    }

    /// A **run** of withdrawals is retired by one release: the skip loop
    /// keeps going while the ticket it uncovers is withdrawn.
    #[test]
    fn cancel_run_is_retired_by_one_release() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        let first = lock.enqueue(1);
        let second = lock.enqueue(2);
        lock.cancel(1, first);
        lock.cancel(2, second);

        lock.release_write(0);

        let (next, serving) = lock.peek_tickets();
        assert_eq!(next, 3, "three tickets were issued");
        assert_eq!(serving, next, "all three were retired");
        assert_eq!(lock.peek_withdrawal(1), None);
        assert_eq!(lock.peek_withdrawal(2), None);
        assert_eq!(lock.peek_state(), 0);
    }

    /// The skip stops at the first **live** request: a waiter behind a
    /// tombstone is served, not skipped past.
    #[test]
    fn cancel_leaves_a_live_waiter_its_turn() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        let withdrawn = lock.enqueue(1);
        let live = lock.enqueue(2);
        lock.cancel(1, withdrawn);

        lock.release_write(0);

        assert!(
            lock.is_served(live),
            "the live waiter behind the tombstone must be the one served"
        );
        let (next, serving) = lock.peek_tickets();
        assert_eq!(next, 3);
        assert_eq!(next - serving, 1, "exactly the live ticket is outstanding");

        lock.complete_write(2, live);
        assert_eq!(lock.peek_state(), WRITER_BIT);
        lock.release_write(2);
        let (next, serving) = lock.peek_tickets();
        assert_eq!(serving, next);
    }

    /// Withdrawing a request one no longer has — the slot is already
    /// reclaimed — is not a second retirement.
    #[test]
    fn cancel_does_not_retire_a_ticket_twice() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        let ticket = lock.enqueue(1);
        lock.cancel(1, ticket);
        lock.release_write(0);
        let (next, serving) = lock.peek_tickets();
        assert_eq!(serving, next);

        // The slot is empty, so a repeat publish is a fresh tombstone for
        // a ticket that is no longer outstanding; the head check refuses
        // it because `now_serving` has moved past it.
        lock.cancel(1, ticket);
        let (next_after, serving_after) = lock.peek_tickets();
        assert_eq!(next_after, next, "no ticket was issued");
        assert_eq!(
            serving_after, serving,
            "a stale withdrawal must not advance now_serving"
        );
    }

    /// The two-phase form composes to exactly what the blocking acquire
    /// does — which is why `acquire_read` is written on it rather than
    /// beside it.
    #[test]
    fn enqueue_then_complete_read_matches_acquire_read() {
        let staged = QueuedRwLock::new();
        let ticket = staged.enqueue(0);
        staged.complete_read(0, ticket);

        let blocking = QueuedRwLock::new();
        blocking.acquire_read(0);

        assert_eq!(staged.peek_state(), blocking.peek_state());
        assert_eq!(staged.peek_tickets(), blocking.peek_tickets());
        assert_eq!(staged.peek_tail(), blocking.peek_tail());
    }

    /// And the write form likewise.
    #[test]
    fn enqueue_then_complete_write_matches_acquire_write() {
        let staged = QueuedRwLock::new();
        let ticket = staged.enqueue(0);
        staged.complete_write(0, ticket);

        let blocking = QueuedRwLock::new();
        blocking.acquire_write(0);

        assert_eq!(staged.peek_state(), blocking.peek_state());
        assert_eq!(staged.peek_tickets(), blocking.peek_tickets());
    }
}

#[cfg(test)]
mod cross_thread_tests {
    use super::*;
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering as StdOrdering};
    use std::sync::Arc;
    use std::thread;
    use std::vec::Vec;

    /// **WS-RR RR6.22**: iterations per cross-thread stress test.
    ///
    /// The plan's D-5 acceptance gate asks for `>= 10^4` per run; the
    /// tests shipped at 50, 100 and 200, which is a smoke test rather
    /// than a stress test — a handover race that needs a few thousand
    /// attempts to surface would pass every run.  The whole
    /// cross-thread module ran in ~0.1 s at the old counts, so the
    /// budget was never the reason.
    #[cfg(not(miri))]
    const STRESS_ITER: usize = 10_000;

    /// Under miri every atomic access is interpreted and the
    /// data-race detector tracks each one, so the same loop is roughly
    /// three orders of magnitude slower.  Miri's value here is
    /// *undefined behaviour and data races*, which show up in the first
    /// few interleavings — not in the ten-thousandth — so the miri run
    /// keeps the coverage and drops the repetition.
    #[cfg(miri)]
    const STRESS_ITER: usize = 4;

    /// **WS-RR RR6.22**: writer acquisitions in the FIFO-order test.
    ///
    /// The plan's "FIFO test iteration count >= 10^4" figure.  Admission
    /// order in a ticket lock *is* ticket order, so the check is that
    /// `now_serving` advances exactly once per acquisition and that no
    /// two holders overlap — over ten thousand of them.
    #[cfg(not(miri))]
    const FIFO_ACQUISITIONS: usize = 10_000;
    #[cfg(miri)]
    const FIFO_ACQUISITIONS: usize = 8;

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
    /// the cross-thread interleaving exercises every ticket-protocol
    /// transition: issue at an empty and at a non-empty queue, pass-turn
    /// from a reader's entry and from a writer's exit, and a writer's
    /// CAS loop draining readers admitted ahead of it.  (This comment
    /// described the retired MCS queue's `signal_next_waiter` /
    /// `cascade_admit_readers` walk until WS-RR RR6.22; the protocol has
    /// been a ticket lock since v0.32.148.) -/
    #[test]
    fn cross_thread_reader_stress() {
        const ITER: usize = STRESS_ITER;
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
        assert_eq!(
            lock.peek_state(),
            0,
            "final state should be 0; got {:#x}",
            lock.peek_state()
        );
    }

    /// Multi-thread writer mutex test: 4 threads each increment a shared
    /// counter under writer-lock; final count = sum.
    /// Iteration count: `STRESS_ITER` (see `cross_thread_reader_stress`).
    #[test]
    fn cross_thread_writer_mutex() {
        const ITER: usize = STRESS_ITER;
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
        assert_eq!(
            counter.load(StdOrdering::Relaxed),
            (MAX_WAITERS * ITER) as u64,
            "writer mutex should serialize: expected {} got {}",
            MAX_WAITERS * ITER,
            counter.load(StdOrdering::Relaxed)
        );
        assert_eq!(lock.peek_state(), 0);
    }

    /// Mixed reader/writer stress: 2 threads each in reader and writer
    /// roles.  Final state should clear.
    #[test]
    fn cross_thread_mixed_stress() {
        const ITER: usize = STRESS_ITER;
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
        assert_eq!(
            lock.peek_state(),
            0,
            "mixed stress should leave state clear; got {:#x}",
            lock.peek_state()
        );
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
        assert!(
            t1_adm < t2_adm,
            "FIFO violation: T1 ({}) should admit before T2 ({})",
            t1_adm,
            t2_adm
        );
        assert!(
            t2_adm < t3_adm,
            "FIFO violation: T2 ({}) should admit before T3 ({})",
            t2_adm,
            t3_adm
        );
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
        assert!(
            count >= 2,
            "Expected at least 2 concurrent-reader observations \
             (H-1 cascade validation); got {}",
            count
        );
    }

    /// **D-5 acceptance gate (≥10 cross-thread tests)**: alternating
    /// reader-writer pattern.  4 threads, each alternating between
    /// reader and writer acquires.  Verifies that the lock correctly
    /// excludes writers from concurrent readers and serializes
    /// writers, with NO state corruption across the W→R→W→R pattern.
    #[test]
    fn cross_thread_alternating_rw_pattern() {
        const ITER: usize = STRESS_ITER;
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
        assert_eq!(
            lock.peek_state(),
            0,
            "state should be 0 after alternating R/W pattern; got {:#x}",
            lock.peek_state()
        );
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
            assert!(
                !r_adm_c.load(StdOrdering::SeqCst),
                "writer starvation: reader admitted before queued writer"
            );
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
            assert!(
                w_adm_c.load(StdOrdering::SeqCst),
                "writer-after-reader: reader admitted before queued writer"
            );
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
        const ITER: usize = STRESS_ITER;
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
        assert!(
            !invariant_violated.load(StdOrdering::SeqCst),
            "mutex invariant violated: observed state with both writer and readers"
        );
        assert_eq!(lock.peek_state(), 0);
    }

    /// **D-5 acceptance gate (≥10 cross-thread tests)**: slot-ownership
    /// boundary.  Verifies that each core_id ∈ [0, MAX_WAITERS) is
    /// independently usable as a slot.  Spawning threads with distinct
    /// core_ids should NOT alias slot state across threads (no false-
    /// sharing-induced corruption between slots).
    #[test]
    fn cross_thread_slot_ownership_independence() {
        const ITER: usize = STRESS_ITER;
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
                    assert!(
                        prev < ITER as u64,
                        "slot {} counter overflowed: {} (alias detected?)",
                        tid,
                        prev
                    );
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
            assert_eq!(
                c, ITER as u64,
                "slot {} counter mismatch: expected {}, got {}",
                tid, ITER, c
            );
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
        assert_eq!(
            lock.peek_state(),
            0,
            "RAII guard Drop should release the lock on panic-unwind"
        );

        // T1: verify the lock is usable again post-panic.
        let lock_c = Arc::clone(&lock);
        let t1 = thread::spawn(move || {
            let _guard = lock_c.acquire_write_guard(1);
            // Normal CS; guard's Drop releases on return.
        });
        t1.join().unwrap();
        assert_eq!(
            lock.peek_state(),
            0,
            "lock must be usable after a previous holder panicked"
        );
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
        assert_eq!(
            lock.peek_state(),
            0,
            "RAII guard Drop should release the read-lock on panic-unwind"
        );
    }

    /// **D-5 acceptance gate (≥10 cross-thread tests)**: rapid
    /// acquire/release cycling.  Stress-tests the ticket handover under
    /// maximum contention — every thread is constantly cycling between
    /// holder and waiter, so `take_ticket`, `await_turn` and `pass_turn`
    /// run back to back on every core.  (This comment named the retired
    /// MCS queue's `signal_next_waiter` / `cascade_admit_readers` until
    /// WS-RR RR6.22.)
    #[test]
    fn cross_thread_rapid_handover_cycling() {
        const ITER: usize = STRESS_ITER;
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
        assert_eq!(
            lock.peek_state(),
            0,
            "rapid handover should leave state clean; got {:#x}",
            lock.peek_state()
        );
        assert_eq!(
            lock.peek_tail(),
            NONE_SENTINEL,
            "rapid handover should leave queue empty"
        );
    }

    /// **WS-RR RR6.22**: FIFO admission order over `FIFO_ACQUISITIONS`
    /// writer acquisitions.
    ///
    /// The plan's D-5 gate asks for a FIFO test at `>= 10^4` iterations.
    /// The shipped one sequences four threads through a single handover
    /// and checks the order once, which is a scenario rather than a
    /// stress test.
    ///
    /// Admission order in a ticket lock **is** ticket order, so the
    /// check is on `now_serving`: while a writer holds, `now_serving`
    /// names its ticket, and successive holders must see it strictly
    /// increase.  The read-modify-write of `last_serving` happens inside
    /// the writer's critical section, so if the lock ever admitted two
    /// writers at once this test would either see a non-increasing
    /// `now_serving` or trip the exclusivity assertion beside it.
    ///
    /// The closing assertion is the ticket-interval one: exactly one
    /// ticket issued and retired per acquisition, nothing outstanding.
    #[test]
    fn cross_thread_writer_fifo_order_over_many_acquisitions() {
        const THREADS: usize = MAX_WAITERS;
        let rounds = FIFO_ACQUISITIONS / THREADS;
        let total = rounds * THREADS;

        let lock = Arc::new(QueuedRwLock::new());
        // `serving + 1`, so the initial `0` is below every real value.
        let last_serving = Arc::new(AtomicU64::new(0));

        let mut handles = Vec::new();
        for core in 0..THREADS {
            let lock_c = Arc::clone(&lock);
            let last_c = Arc::clone(&last_serving);
            handles.push(thread::spawn(move || {
                for _ in 0..rounds {
                    lock_c.acquire_write(core as u8);
                    assert_eq!(
                        lock_c.peek_state(),
                        WRITER_BIT,
                        "a second holder was admitted alongside core {core}"
                    );
                    let (next, serving) = lock_c.peek_tickets();
                    assert!(
                        serving < next,
                        "the holder's own ticket is not outstanding \
                         (next={next}, serving={serving})"
                    );
                    let prev = last_c.swap(serving + 1, StdOrdering::SeqCst);
                    assert!(
                        serving + 1 > prev,
                        "admission order regressed: now_serving {serving} \
                         after a holder at {}",
                        prev.saturating_sub(1)
                    );
                    lock_c.release_write(core as u8);
                }
            }));
        }
        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(lock.peek_state(), 0, "the lock did not drain");
        let (next, serving) = lock.peek_tickets();
        assert_eq!(
            next as usize, total,
            "exactly one ticket must be issued per acquisition"
        );
        assert_eq!(
            serving, next,
            "every issued ticket must be retired exactly once"
        );
        assert_eq!(lock.peek_tail(), NONE_SENTINEL);
    }
}
