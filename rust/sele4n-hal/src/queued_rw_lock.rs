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
//! One thing is **stronger** than the API it replaced (PR #890 review
//! rounds 2 and 3, and the class they were instances of): **every entry
//! point decides the executing core's own case, on words the lock owns,
//! before it writes anything.**  Three words per core — `held` (what it
//! holds), `request` (the one ticket it has issued and not yet retired as
//! a request), `cancelled` (its published withdrawal) — say whether the
//! core is idle, queued, withdrawn or holding, and each of the spec's
//! no-ops is a branch on them rather than a contract policed by a
//! `debug_assert` that vanishes in release builds: a holder re-acquiring,
//! a non-holder releasing, a holder withdrawing, a queued core acquiring
//! again or enqueueing again all change nothing, a terminator is verified
//! against the record rather than the caller's ticket, and a completion
//! waits for its own turn.  The two-phase-locking unwind withdraws at and
//! releases every member of a footprint whether or not the core holds it,
//! and relies on exactly those identities.  Rounds 2 and 3 each found one
//! entry point deciding on a contract instead; the cause was the same both
//! times — the lock did not know the core's situation — and the three
//! words are what closed it, with `per_core_state_matrix` pinning every
//! entry point in every state and `build.rs` holding the entry-point list
//! to that matrix.
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

/// The three values of a core's **held** word (PR #890 review round 2):
/// the core holds nothing, holds the lock as a reader, or holds it as
/// the writer.  See `QueuedRwLock::held`.
const HELD_NONE: u8 = 0;
const HELD_READ: u8 = 1;
const HELD_WRITE: u8 = 2;

/// A core's **live request**: `NO_REQUEST` (zero), or `ticket + 1` for
/// the one ticket the core has been issued and not yet retired as a
/// request — passed at a reader's entry, retired at a writer's release,
/// or withdrawn.  The third of the three per-core words (`held`,
/// `cancelled`, `request`), and the one that closes the class behind
/// PR #890 review rounds 2 and 3: with it the lock knows, for every
/// entry point, whether the executing core is idle, queued, withdrawn or
/// holding, and decides on that rather than on a caller's belief.
const NO_REQUEST: u64 = 0;

/// The ticket [`QueuedRwLock::enqueue`] returns to a core that already
/// **holds** the lock as a reader: there is nothing to wait for, so
/// [`QueuedRwLock::is_served`] reports it served at once and every
/// terminator treats it as the holder's no-op.  A real ticket is never
/// this value — the counters stay below it (`hNoWrap` in the Lean model,
/// `QueuedRwLockRefinement.lean`), and a writer holder is handed the
/// ticket it still holds instead.
pub const HELD_TICKET: u64 = u64::MAX;

/// What a core holds, as `peek_held` reports it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeldMode {
    /// The core holds the lock as a reader.
    Read,
    /// The core holds the lock as the writer.
    Write,
}

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
    /// **WS-LC LC3.1**: one withdrawal slot per core.
    ///
    /// `NO_WITHDRAWAL` (zero) means "this core has withdrawn nothing";
    /// any other value is `ticket + 1` for the ticket it has withdrawn.
    /// The offset is what lets zero be the empty marker without
    /// reserving a ticket value, and it costs the same wraparound
    /// assumption the ticket counters already make.
    ///
    /// **One slot holds one withdrawal, so a core may not take a second
    /// ticket while its slot is published** (WS-LC closure audit).  A
    /// slot is cleared only by the compare-exchange that retires the
    /// ticket it names — the skip loop's when `now_serving` uncovers
    /// that ticket, or the withdrawing core's own when it was already
    /// the head — and until then the ticket is owed an advance that
    /// nothing but that claim will make.  A second `cancel` by the same
    /// core would overwrite the publication, and the first ticket would
    /// then never be retired: `now_serving` stops on it, and the lock is
    /// stalled with every later waiter behind a ticket no core holds.
    /// That was reachable through a contract-respecting sequence —
    /// enqueue, withdraw, enqueue, withdraw, with the first withdrawal
    /// still unclaimed — so `enqueue` refuses to issue until the slot is
    /// empty (`await_withdrawal_retired`), a wait strictly shorter than
    /// the fresh ticket would have faced anyway.  The Lean model states
    /// the same rule as the issue's precondition (`opEnabled` on
    /// `nextTicketFetchAdd`) and carries "one outstanding ticket per
    /// core" as a `QueuedTicketWf` conjunct (`ledgerCoresNodup`), from
    /// which "at most one publication per core" is a theorem
    /// (`QueuedTicketWf.withdrawal_unique`) rather than a property read
    /// off this array's shape.
    ///
    /// The shared protocol words — the three counters and this array —
    /// fill the first 64-byte cache line together with the byte-sized
    /// words; the per-core request words below fill the second.
    cancelled: [AtomicU64; MAX_WAITERS],
    /// The core that most recently took a ticket, or `NONE_SENTINEL` if
    /// none has. Observability only — no protocol decision reads it —
    /// but it keeps `peek_tail`'s meaning ("who enqueued last") for the
    /// cross-thread tests that use it to sequence their threads.
    last_enqueued: AtomicU8,
    /// **PR #890 review round 2**: what each core holds — `HELD_NONE`,
    /// `HELD_READ` or `HELD_WRITE`.
    ///
    /// This is what makes a release by a non-holder the **spec's no-op**
    /// (`RwLockState.applyOp`'s `releaseRead` / `releaseWrite` arms:
    /// releasing a lock one does not hold changes nothing) rather than a
    /// contract a `debug_assert` polices.  Before it, `release_read` was
    /// an unconditional `fetch_sub` and `release_write` an unconditional
    /// clear-and-pass-turn, so a non-holder's release in a release build
    /// underflowed the reader count or handed the turn to the next
    /// waiter while the real writer still held — and the two-phase-locking
    /// unwind (`unwindAll`, WS-LC LC4) releases **every** member of a
    /// footprint, holding or not, relying on exactly the identity the lock
    /// did not implement.  The refinement had claimed the identity as a
    /// stuttering block, which no code path performed.
    ///
    /// Each word is written and read by its own core only — set at that
    /// core's admission, consulted and cleared at its release — so the
    /// accesses need no cross-core ordering; `Acquire` / `Release` are
    /// used anyway, at no measurable cost, so no reader of this code has
    /// to reconstruct that argument.  The Lean model carries the words as
    /// the sets `heldRead` / `heldWrite` and relates them to the spec's
    /// `readers` / `writerHeld` (`queuedHeldSim`), which is what lets
    /// the release no-op blocks be *derived* rather than assumed.
    held: [AtomicU8; MAX_WAITERS],
    /// **The class closure**: each core's live request — `NO_REQUEST`,
    /// or `ticket + 1` for the one ticket it has issued and not yet
    /// retired as a request.
    ///
    /// Rounds 2 and 3 of PR #890's review each found one entry point
    /// deciding on a caller contract where the spec has a no-op: a
    /// release by a non-holder, then a withdrawal by a holder.  Both had
    /// the same cause — the lock did not know the executing core's
    /// situation, so the refinement asserted a stutter the code did not
    /// perform and the two-phase-locking unwind relied on it.  The held
    /// word answered "does this core hold, and how"; this word answers
    /// the remaining question, "does this core have a request, and which
    /// ticket is it".  With the three words every entry point decides
    /// the executing core's case itself: `enqueue` by a queued core
    /// returns the ticket it has rather than a second one, the fused
    /// acquisitions by a queued core acquire nothing new, a terminator
    /// is verified against the record rather than the caller's ticket,
    /// and a completion waits for its own turn rather than trusting that
    /// the caller polled.  The Lean model carries it as `requests`, pinned
    /// to the ghost ledger's live entries (`queuedRequestsSim`).
    ///
    /// Written and read by its own core only, like `held`.  Placed after
    /// the byte-sized words so it fills the lock's second cache line,
    /// where its owner-only writes contend with none of the shared
    /// counters.
    request: [AtomicU64; MAX_WAITERS],
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
            cancelled: [const { AtomicU64::new(NO_WITHDRAWAL) }; MAX_WAITERS],
            last_enqueued: AtomicU8::new(NONE_SENTINEL),
            held: [const { AtomicU8::new(HELD_NONE) }; MAX_WAITERS],
            request: [const { AtomicU64::new(NO_REQUEST) }; MAX_WAITERS],
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
            cancelled: core::array::from_fn(|_| AtomicU64::new(NO_WITHDRAWAL)),
            last_enqueued: AtomicU8::new(NONE_SENTINEL),
            held: core::array::from_fn(|_| AtomicU8::new(HELD_NONE)),
            request: core::array::from_fn(|_| AtomicU64::new(NO_REQUEST)),
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

    /// Take the next ticket, record it as the core's live request, and
    /// record the enqueue for `peek_tail`.
    #[inline]
    fn take_ticket(&self, core_id: u8) -> u64 {
        let ticket = self.next_ticket.fetch_add(1, Ordering::AcqRel);
        self.request[core_id as usize].store(ticket + 1, Ordering::Release);
        self.last_enqueued.store(core_id, Ordering::Release);
        ticket
    }

    /// The live request `core_id` is terminating, verified against the
    /// lock's own record rather than the caller's belief.
    ///
    /// A core with no live request asked to enter or leave a queue it is
    /// not in: a second terminator for a ticket already completed or
    /// withdrawn, or one for a ticket never issued.  Proceeding on the
    /// caller's word would admit it ahead of the queue, so it is refused
    /// outright, in every build.  A caller naming a ticket other than the
    /// one it holds is reported in debug builds; the request the core
    /// actually has is the one the spec's operation is about, and it is
    /// the one used.
    #[inline]
    fn own_request(&self, core_id: u8, ticket: u64, entry: &str) -> u64 {
        let own = self.request[core_id as usize].load(Ordering::Acquire);
        assert!(
            own != NO_REQUEST,
            "{entry} called by core {core_id}, which has no live request (ticket {ticket})"
        );
        debug_assert!(
            ticket == own - 1,
            "{entry} called by core {core_id} with ticket {ticket}, but its request is {}",
            own - 1
        );
        own - 1
    }

    /// Whether `core_id` is **involved** — holding, or holding a live
    /// request — read from its own two words.  Every entry point decides
    /// the executing core's case on these before it writes anything.
    #[inline]
    fn involved(&self, core_id: u8) -> bool {
        self.held[core_id as usize].load(Ordering::Acquire) != HELD_NONE
            || self.request[core_id as usize].load(Ordering::Acquire) != NO_REQUEST
    }

    /// **WS-LC closure audit**: park until this core's withdrawal slot
    /// is empty, so the ticket about to be issued cannot share the slot
    /// with a withdrawal nobody has claimed yet.
    ///
    /// The slot is cleared by exactly one compare-exchange — the skip
    /// loop's when `now_serving` uncovers the withdrawn ticket, or the
    /// withdrawing core's own when it was already the head — so this
    /// returns once the lock has retired that ticket.  That is strictly
    /// sooner than a fresh ticket would be served: `now_serving` has to
    /// pass the withdrawn ticket before it can reach any later one.  So
    /// the wait adds no blocking the acquisition would not have incurred
    /// on its own, and every progress argument that covers `await_turn`
    /// covers it.  Every claim is followed by a `pass_turn` advance and
    /// its `sev`, which is what wakes a core parked here.
    ///
    /// Only the executing core stores a non-zero value into its own slot
    /// (`cancel`), so once this observes the slot empty it stays empty
    /// until the core itself withdraws again.
    #[inline]
    fn await_withdrawal_retired(&self, core_id: u8) {
        while self.cancelled[core_id as usize].load(Ordering::SeqCst) != NO_WITHDRAWAL {
            Self::park_hint();
        }
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
    /// Each iteration *claims* a published withdrawal — a
    /// compare-exchange from `ticket + 1` to empty, so no publication is
    /// consumed twice — and a withdrawal is published only for an issued
    /// ticket, by the core that holds it, into that core's one slot.
    /// So the loop runs at most one iteration per withdrawal published
    /// while it runs, each for a distinct issued ticket, and exits as
    /// soon as the uncovered ticket is live.  It is **not** bounded by
    /// `MAX_WAITERS`: a core whose withdrawal this loop has just retired
    /// may enqueue again at the head and withdraw again before the next
    /// scan, and lose the arbitration a second time — that is a new
    /// ticket, not a refilled slot, so a per-core iteration cap would
    /// fire on a correct execution (WS-LC closure audit; the cap that
    /// used to be here did).  The bound that *is* a protocol invariant,
    /// `now_serving <= next_ticket`, is what `advance_now_serving`
    /// checks.  There is deliberately no iteration cap: a cap that fired
    /// would leave a tombstone at the head with nobody left to retire
    /// it, which is the stall this loop exists to prevent.
    #[inline]
    fn pass_turn(&self) {
        let mut uncovered = self.advance_now_serving();
        while self.claim_withdrawal_of(uncovered) {
            uncovered = self.advance_now_serving();
        }
    }

    /// Advance `now_serving` by one, wake every parked core, and return
    /// the ticket that is now being served.
    ///
    /// `now_serving <= next_ticket` is the protocol invariant
    /// (`QueuedTicketWf.servingLeNext`, `QueuedRwLockRefinement.lean`),
    /// and an advance that runs past `next_ticket` is exactly a ticket
    /// retired twice — the failure the withdrawal arbitration exists to
    /// prevent.  `next_ticket` is read after the advance and only grows,
    /// so the check can miss a violation but never invent one.
    #[inline]
    fn advance_now_serving(&self) -> u64 {
        let uncovered = self.now_serving.fetch_add(1, Ordering::SeqCst) + 1;
        crate::cpu::sev();
        debug_assert!(
            uncovered <= self.next_ticket.load(Ordering::SeqCst),
            "now_serving ran past next_ticket: a ticket was retired twice"
        );
        uncovered
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
    ///
    /// A core that already holds the lock — as a reader or as the writer
    /// — takes no ticket and changes nothing: the spec's `tryAcquireRead`
    /// arm for an involved core (PR #890 review round 2; the refinement's
    /// `acquireRead_noop` block used to describe a path this function
    /// did not have).  A core with a *queued* request is not a holder
    /// and must not call this; that is the one-outstanding-ticket
    /// contract, stated by `ledgerCoresNodup` on the Lean side.
    pub fn acquire_read(&self, core_id: u8) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        // An involved core acquires nothing new — the spec's no-op.  A
        // holder already holds; a core with a live request is inside its
        // own acquisition, or holds a split-API ticket it must finish
        // through the spelling that began it, and taking a second ticket
        // here is what the one-outstanding-ticket rule forbids.
        if self.involved(core_id) {
            return;
        }
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
    ///
    /// # Blocks while the core's last withdrawal is unclaimed
    ///
    /// A ticket is issued only once this core's withdrawal slot is
    /// empty (`await_withdrawal_retired`).  The slot holds one
    /// withdrawal, and a second ticket taken while the first is still
    /// published could be withdrawn over it — losing the first
    /// publication and stalling the lock on a ticket nobody holds.  The
    /// wait ends when the lock retires the withdrawn ticket, which
    /// happens before any later ticket could be served, so it costs the
    /// caller nothing a fresh ticket would not have cost.  The
    /// non-blocking [`try_acquire_read`](Self::try_acquire_read) and
    /// [`try_acquire_write`](Self::try_acquire_write) are *refused* in
    /// the same state, since the withdrawn ticket is still outstanding.
    #[must_use]
    pub fn enqueue(&self, core_id: u8) -> u64 {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        // A core with a live request has its ticket already: the spec's
        // `tryAcquire*` by an involved core changes nothing, and here
        // that reads "the request you have is the one that will be
        // admitted" — the same ticket, never a second one, which is what
        // keeps one outstanding ticket per core a fact the lock
        // establishes rather than a contract it asks for.
        let own = self.request[core_id as usize].load(Ordering::Acquire);
        if own != NO_REQUEST {
            return own - 1;
        }
        // A reader holder has nothing to wait for: the sentinel is served
        // at once, and every terminator treats it as the holder's no-op.
        // (A writer holder still holds its ticket and was returned it
        // above.)
        if self.held[core_id as usize].load(Ordering::Acquire) != HELD_NONE {
            return HELD_TICKET;
        }
        self.await_withdrawal_retired(core_id);
        self.take_ticket(core_id)
    }

    /// **WS-LC LC3.1**: whether `ticket` is the one currently entitled
    /// to enter, so a caller polling instead of parking can tell when to
    /// complete.
    #[must_use]
    #[inline]
    pub fn is_served(&self, ticket: u64) -> bool {
        // A holder's sentinel is served at once; see `enqueue`.
        // `SeqCst`, and this is the other half — see `cancel`.
        ticket == HELD_TICKET || self.now_serving.load(Ordering::SeqCst) == ticket
    }

    /// **WS-LC LC3.1**: complete a read acquisition begun with
    /// [`enqueue`](Self::enqueue).
    ///
    /// Decided on the executing core's own words: a holder completes
    /// nothing (the spec's no-op, where the holder's sentinel from
    /// `enqueue` lands), a core with no live request is refused outright
    /// (`own_request`), and the request completed is the one the lock
    /// recorded for the core.  The lock then waits for its own turn
    /// rather than trusting that the caller polled
    /// [`is_served`](Self::is_served) — a completion ahead of the turn
    /// would admit a reader ahead of the queue — which costs a served
    /// caller one load.
    pub fn complete_read(&self, core_id: u8, ticket: u64) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        if self.held[core_id as usize].load(Ordering::Acquire) != HELD_NONE {
            return;
        }
        let ticket = self.own_request(core_id, ticket, "complete_read");
        self.await_turn(ticket);

        // Our turn. No writer can hold the lock here: a writer clears
        // WRITER_BIT before advancing `now_serving` past its own ticket,
        // so by the time we are served the bit is already clear.
        debug_assert!(
            (self.state.load(Ordering::Acquire) & WRITER_BIT) == 0,
            "writer-readers exclusion violated: reader served while \
             WRITER_BIT set"
        );
        self.state.fetch_add(1, Ordering::AcqRel);
        self.held[core_id as usize].store(HELD_READ, Ordering::Release);
        // A reader passes its ticket on at entry: it has no request now.
        self.request[core_id as usize].store(NO_REQUEST, Ordering::Release);

        // Pass the ticket on BEFORE returning, so the next queued reader
        // enters concurrently with us rather than after our release.
        self.pass_turn();
    }

    /// **WS-LC LC3.1**: complete a write acquisition begun with
    /// [`enqueue`](Self::enqueue), blocking until the readers admitted
    /// ahead of it have drained.
    ///
    /// The writer keeps its ticket; [`release_write`](Self::release_write)
    /// retires it.  Decided on the core's own words exactly as
    /// [`complete_read`](Self::complete_read) is.
    pub fn complete_write(&self, core_id: u8, ticket: u64) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        if self.held[core_id as usize].load(Ordering::Acquire) != HELD_NONE {
            return;
        }
        let ticket = self.own_request(core_id, ticket, "complete_write");
        self.await_turn(ticket);
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
        self.held[core_id as usize].store(HELD_WRITE, Ordering::Release);
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
    /// # A holder withdraws nothing
    ///
    /// The two-phase-locking unwind (`unwindAll`, WS-LC LC4) withdraws at
    /// every member of a footprint before it releases, holding or not,
    /// and the spec's `cancel` is the identity for a holder (INV-R4 keeps
    /// holders out of the queue).  A writer still **holds its ticket** —
    /// `now_serving` names it — so a withdrawal of it would be claimed at
    /// once and `pass_turn` would advance the counter under a set writer
    /// bit; `release_write` then advanced it again, past a live waiter.
    /// A `debug_assert` stood in for the identity and vanished in release
    /// builds (PR #890 review round 3).  The held word decides now: a
    /// core whose word reads held returns before anything is published.
    /// A reader's ticket was passed at entry and is refused as stale
    /// below either way.
    ///
    /// # Only the core's own live request is withdrawn
    ///
    /// The ticket published is the one the lock recorded for the core
    /// (`request`), never the argument: a core with no live request —
    /// its ticket retired, already withdrawn, or never issued — withdraws
    /// nothing, which is the spec's no-op and subsumes the closure
    /// audit's stale-ticket refusal (a publication for a retired ticket
    /// is one no skip loop will ever claim, and `enqueue` waits on the
    /// slot, so it would park the core's next acquisition for good).  A
    /// caller naming a ticket other than its own is reported in debug
    /// builds and its own request is withdrawn regardless, so the lock
    /// never publishes a tombstone for a ticket another core holds.  The
    /// record is monotone in the way the old counter check was: a live
    /// request's ticket is passed by nobody but its own core, so the
    /// request is cleared before `now_serving` can move past it.
    ///
    /// # Refinement
    ///
    /// Corresponds to the Lean block `queuedBlock.cancel_queued` — the
    /// held-word and counter loads, the publish, then `skipDeadOps`, one
    /// shape covering both cases this function branches on
    /// (`QueuedRwLockRefinement.lean`).  A holder's withdrawal and a
    /// withdrawal of a retired ticket are the model's `cancel_noop`
    /// block: `cancelPublish` is enabled only for an outstanding ticket
    /// of a core holding nothing (`opEnabled`).
    pub fn cancel(&self, core_id: u8, ticket: u64) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        // A holder withdraws nothing — see the section above.  This
        // core's own word, read before anything is published.
        if self.held[core_id as usize].load(Ordering::Acquire) != HELD_NONE {
            return;
        }
        // Only the core's own live request is withdrawn — the section
        // above.  `own` is `ticket + 1` for that request, which is also
        // the slot encoding.
        let own = self.request[core_id as usize].load(Ordering::Acquire);
        if own == NO_REQUEST {
            return;
        }
        debug_assert!(
            ticket == own - 1,
            "cancel called by core {core_id} with ticket {ticket}, but its request is {}",
            own - 1
        );
        let ticket = own - 1;
        debug_assert!(
            self.now_serving.load(Ordering::SeqCst) <= ticket,
            "a live request's ticket was passed by another core"
        );
        // The request ends here whatever the arbitration below decides:
        // from this core's side the ticket is a tombstone the slot tracks.
        self.request[core_id as usize].store(NO_REQUEST, Ordering::Release);
        self.cancelled[core_id as usize].store(own, Ordering::SeqCst);
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

    /// `core_id`'s live request, per its request word — the test-only
    /// accessor the Tier-5 oracle checks against the spec's queue and
    /// held writer (`check_requests`).
    #[must_use]
    #[inline]
    pub fn peek_request(&self, core_id: u8) -> Option<u64> {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        match self.request[core_id as usize].load(Ordering::Acquire) {
            NO_REQUEST => None,
            own => Some(own - 1),
        }
    }

    /// What `core_id` holds, per its held word — the test-only accessor
    /// the Tier-5 oracle checks against the spec's `readers` and
    /// `writerHeld`.
    #[must_use]
    #[inline]
    pub fn peek_held(&self, core_id: u8) -> Option<HeldMode> {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        match self.held[core_id as usize].load(Ordering::Acquire) {
            HELD_READ => Some(HeldMode::Read),
            HELD_WRITE => Some(HeldMode::Write),
            _ => None,
        }
    }

    /// **WS-SM SM2.C-defer D-5.6**: release a read lock held by `core_id`.
    ///
    /// The ticket was passed on at acquire, so this only leaves the
    /// reader count — there is no successor to signal and therefore no
    /// handoff that can be lost.
    ///
    /// # A release by a non-holder is the spec's no-op
    ///
    /// The held word is consulted **before** the count is touched (PR
    /// #890 review round 2): a core that does not hold the lock as a
    /// reader returns having written nothing, which is exactly
    /// `RwLockState.applyOp`'s `releaseRead` arm.  The two-phase-locking
    /// unwind releases every member of its footprint, holding or not, and
    /// relies on this; before the word existed the decrement was
    /// unconditional and a non-holder's release underflowed the count in
    /// a release build.  The order is pinned by `build.rs`
    /// (`scan_queued_rw_lock_protocol_intact`, check 3).
    pub fn release_read(&self, core_id: u8) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        if self.held[core_id as usize].load(Ordering::Acquire) != HELD_READ {
            return;
        }
        self.held[core_id as usize].store(HELD_NONE, Ordering::Release);
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
    ///
    /// A core that already holds the lock takes no ticket and changes
    /// nothing — see [`acquire_read`](Self::acquire_read).
    pub fn acquire_write(&self, core_id: u8) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        // As in `acquire_read`: an involved core acquires nothing new.
        if self.involved(core_id) {
            return;
        }
        let ticket = self.enqueue(core_id);
        self.await_turn(ticket);
        self.complete_write(core_id, ticket);
    }

    /// **WS-SM SM2.C-defer D-5.6**: release a write lock held by `core_id`.
    ///
    /// Clears the writer bit, then passes the ticket on. That order is
    /// required: a reader served by the next ticket must not observe
    /// WRITER_BIT still set.
    ///
    /// # A release by a non-holder is the spec's no-op
    ///
    /// As in [`release_read`](Self::release_read): the held word is
    /// consulted before anything is written, so a core that is not the
    /// writer neither clears the bit nor passes a turn it does not own —
    /// which, before the word existed, admitted the next waiter while the
    /// real writer still held.
    pub fn release_write(&self, core_id: u8) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        if self.held[core_id as usize].load(Ordering::Acquire) != HELD_WRITE {
            return;
        }
        self.held[core_id as usize].store(HELD_NONE, Ordering::Release);
        // The writer's ticket is retired by the pass below; its request
        // ends here.
        self.request[core_id as usize].store(NO_REQUEST, Ordering::Release);
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
    ///
    /// # Why a pending withdrawal is refused without a slot read
    ///
    /// The blocking `enqueue` waits until the caller's withdrawal slot
    /// is empty (WS-LC closure audit).  Here that condition is a
    /// consequence rather than a wait: a published withdrawal names a
    /// ticket that is still outstanding — `now_serving` passes a
    /// withdrawn ticket only through the claim that clears its slot —
    /// so while one is published `next_ticket != now_serving` and the
    /// exchange fails.  The `debug_assert` pins the derivation on every
    /// interleaving the loom models explore.
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
        self.request[core_id as usize].store(serving + 1, Ordering::Release);
        self.last_enqueued.store(core_id, Ordering::Release);
        debug_assert!(
            self.cancelled[core_id as usize].load(Ordering::SeqCst) == NO_WITHDRAWAL,
            "a served ticket was issued to a core whose withdrawal is still published"
        );
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
    /// [`release_read`](Self::release_read).  A core that already holds
    /// the lock gets `false` and no ticket: the call acquired nothing,
    /// which is the spec's no-op for an involved core.
    #[must_use]
    pub fn try_acquire_read(&self, core_id: u8) -> bool {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        // An involved core acquires nothing new (the fused spelling's
        // branch); a queued core's own outstanding ticket would also make
        // the exchange below fail, but the decision is the core's, not a
        // coincidence of the counters.
        if self.involved(core_id) {
            return false;
        }
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
        self.held[core_id as usize].store(HELD_READ, Ordering::Release);
        self.request[core_id as usize].store(NO_REQUEST, Ordering::Release);
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
    /// [`release_write`](Self::release_write).  A core that already holds
    /// the lock gets `false` and no ticket, as in
    /// [`try_acquire_read`](Self::try_acquire_read).
    #[must_use]
    pub fn try_acquire_write(&self, core_id: u8) -> bool {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        if self.involved(core_id) {
            return false;
        }
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
            self.held[core_id as usize].store(HELD_WRITE, Ordering::Release);
            return true;
        }
        // Not admitted: retire the ticket we were served rather than
        // hold it, so the next waiter is not blocked behind an attempt
        // that gave up.  The request ends with it.
        self.request[core_id as usize].store(NO_REQUEST, Ordering::Release);
        self.pass_turn();
        false
    }

    /// Acquire a read lock, returning an RAII guard.
    ///
    /// A guard taken by a core that already holds the lock acquires
    /// nothing — the spec's no-op, which [`acquire_read`](Self::acquire_read)
    /// implements — and therefore **releases nothing** when it drops
    /// (PR #890 review round 3): a nested same-core guard used to release
    /// the hold the outer scope still relied on.  The guard records
    /// whether it acquired, and the hold ends with the guard that took it.
    #[must_use]
    pub fn acquire_read_guard(&self, core_id: u8) -> QueuedRwLockReadGuard<'_> {
        // The words are this core's own, so the read cannot race the
        // acquisition it precedes; an involved core's guard acquires
        // nothing, exactly as the acquisition it wraps.
        let acquired = !self.involved(core_id);
        if acquired {
            self.acquire_read(core_id);
        }
        QueuedRwLockReadGuard {
            lock: self,
            core_id,
            acquired,
        }
    }

    /// Acquire a write lock, returning an RAII guard.
    ///
    /// Same contract as [`acquire_read_guard`](Self::acquire_read_guard):
    /// a guard taken by a holder acquires nothing and releases nothing.
    #[must_use]
    pub fn acquire_write_guard(&self, core_id: u8) -> QueuedRwLockWriteGuard<'_> {
        let acquired = !self.involved(core_id);
        if acquired {
            self.acquire_write(core_id);
        }
        QueuedRwLockWriteGuard {
            lock: self,
            core_id,
            acquired,
        }
    }
}

// ============================================================================
// RAII guards
// ============================================================================

/// RAII read guard — releases on drop, including during unwind, the
/// hold it took; a guard that took none (its core already held) releases
/// none (PR #890 review round 3).
pub struct QueuedRwLockReadGuard<'a> {
    lock: &'a QueuedRwLock,
    core_id: u8,
    /// Whether this guard's construction acquired the lock.
    acquired: bool,
}

impl QueuedRwLockReadGuard<'_> {
    /// Whether this guard holds an acquisition of its own, as opposed to
    /// riding on one its core already had.
    #[must_use]
    pub fn acquired(&self) -> bool {
        self.acquired
    }
}

impl Drop for QueuedRwLockReadGuard<'_> {
    fn drop(&mut self) {
        if self.acquired {
            self.lock.release_read(self.core_id);
        }
    }
}

/// RAII write guard — releases on drop, including during unwind, the
/// hold it took; a guard that took none releases none.
pub struct QueuedRwLockWriteGuard<'a> {
    lock: &'a QueuedRwLock,
    core_id: u8,
    /// Whether this guard's construction acquired the lock.
    acquired: bool,
}

impl QueuedRwLockWriteGuard<'_> {
    /// Whether this guard holds an acquisition of its own.
    #[must_use]
    pub fn acquired(&self) -> bool {
        self.acquired
    }
}

impl Drop for QueuedRwLockWriteGuard<'_> {
    fn drop(&mut self) {
        if self.acquired {
            self.lock.release_write(self.core_id);
        }
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

    // ------------------------------------------------------------------
    // WS-LC closure audit — the double withdrawal, and the slot as a
    // precondition of the issue
    // ------------------------------------------------------------------
    //
    // The four models above withdraw at most once per core, which is why
    // none of them saw this: with one slot per core, a second withdrawal
    // published while the first is unclaimed overwrote it, and the ticket
    // the first named was never retired.  The sequence is one every
    // documented contract permits — enqueue, withdraw, enqueue, withdraw —
    // so the fix is at the issue, not at the withdrawal: `enqueue` parks
    // until the slot is empty, and the non-blocking attempts are refused
    // in the same state.  Both models assert the interval closes, which
    // is what a lost tombstone breaks.

    /// A core withdraws twice — enqueue, withdraw, enqueue, withdraw —
    /// while the core ahead of it holds and then releases.  The second
    /// `enqueue` parks until the release has retired the first
    /// withdrawal; the release's skip loop and the second withdrawal then
    /// arbitrate the second ticket as usual.  Every interleaving must end
    /// with both tickets retired and the slot empty.
    ///
    /// Decisiveness (see `scripts/test_loom_queued_rw_lock.sh`): keep the
    /// slot wait in `enqueue` and move it *after* `take_ticket`, and this
    /// model fails with `now_serving` one short of `next_ticket`.
    #[test]
    fn double_withdrawal_by_one_core_does_not_strand_the_lock() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let a = Arc::clone(&lock);
            lock.acquire_write(0);
            let t = loom::thread::spawn(move || {
                let first = a.enqueue(1);
                a.cancel(1, first);
                let second = a.enqueue(1);
                a.cancel(1, second);
            });
            lock.release_write(0);
            t.join().unwrap();
            let (next, serving) = lock.peek_tickets();
            assert_eq!(
                serving,
                next,
                "a withdrawn ticket was never retired: the lock is stalled \
                 (slot={:?}, state={:#x})",
                lock.peek_withdrawal(1),
                lock.peek_state()
            );
            assert_eq!(next, 3, "exactly one ticket per enqueue");
            assert_eq!(lock.peek_withdrawal(1), None, "the slot was reclaimed");
            assert_eq!(lock.peek_state(), 0, "a withdrawal releases nothing");
        });
    }

    /// A non-blocking attempt by a core whose withdrawal is still
    /// published is refused, and issues nothing: the withdrawn ticket is
    /// outstanding, so `next_ticket != now_serving`.  Once the release
    /// has retired it the attempt may succeed.  Either way the interval
    /// closes, and `try_take_served_ticket`'s `debug_assert` — a served
    /// ticket is never issued over a published slot — is checked on
    /// every interleaving.
    #[test]
    fn pending_withdrawal_refuses_the_non_blocking_attempt() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let a = Arc::clone(&lock);
            lock.acquire_write(0);
            let ticket = lock.enqueue(1);
            let t = loom::thread::spawn(move || {
                a.cancel(1, ticket);
                if a.try_acquire_read(1) {
                    a.release_read(1);
                }
            });
            lock.release_write(0);
            t.join().unwrap();
            let (next, serving) = lock.peek_tickets();
            assert_eq!(serving, next, "a ticket was issued and never retired");
            assert!(
                next == 2 || next == 3,
                "the attempt either issued nothing (2 tickets) or was served \
                 after the retirement (3), never over the published slot: {next}"
            );
            assert_eq!(lock.peek_withdrawal(1), None);
            assert_eq!(lock.peek_state(), 0);
        });
    }

    // ------------------------------------------------------------------
    // PR #890 review round 2 — a non-holder's release, under concurrency
    // ------------------------------------------------------------------

    /// The two-phase-locking unwind's shape: a core withdraws its queued
    /// request and then releases the member in both modes, as
    /// `unwindAll` does for every member of a footprint, while the core
    /// ahead holds and releases.  On every interleaving the writer's
    /// critical section is never invaded, the turn is passed once, and
    /// the held words end empty.
    #[test]
    fn unwind_by_a_non_holder_never_touches_the_holder() {
        loom::model(|| {
            let lock = Arc::new(QueuedRwLock::new());
            let a = Arc::clone(&lock);
            lock.acquire_write(0);
            let ticket = lock.enqueue(1);
            let t = loom::thread::spawn(move || {
                a.cancel(1, ticket);
                a.release_read(1);
                a.release_write(1);
            });
            // The writer's critical section: nothing else may hold.
            assert_eq!(lock.peek_state(), WRITER_BIT, "the writer was displaced");
            lock.release_write(0);
            t.join().unwrap();
            let (next, serving) = lock.peek_tickets();
            assert_eq!(serving, next, "a turn was passed by a non-holder, or never");
            assert_eq!(next, 2);
            assert_eq!(lock.peek_state(), 0);
            assert_eq!(lock.peek_held(0), None);
            assert_eq!(lock.peek_held(1), None);
        });
    }

    // ------------------------------------------------------------------
    // PR #890 review round 2 — the enumerated two-thread programs
    // ------------------------------------------------------------------
    //
    // The D-5 acceptance criterion promised exhaustive-interleaving runs
    // "on op-sequences of length <= 4", and the eleven handwritten models
    // above are scenarios, not an enumeration.  This is the enumeration,
    // at the bound that is both meaningful and affordable: every
    // two-thread program with **one contract-respecting unit per thread**
    // — a unit being a complete acquisition-and-release in one of the
    // lock's spellings, a withdrawal followed by the unwind's releases, or
    // (review round 3) an acquisition followed by the unwind at the held
    // member — which is at most five lock operations per thread.  Arbitrary
    // operation sequences would include contract violations (a release
    // without a hold was one, until round 2 made it the spec's no-op; two
    // live tickets on one core still is), which the lock does not define.
    // Units are drawn from one list, so a new spelling added to the lock
    // is added here and is then paired with every other automatically.

    /// One thread's whole program.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Unit {
        /// `acquire_read`, check no writer, `release_read`.
        ReadHold,
        /// `acquire_write`, check exclusive, `release_write`.
        WriteHold,
        /// `enqueue`, poll `is_served`, `complete_read`, `release_read`.
        SplitRead,
        /// `enqueue`, poll `is_served`, `complete_write`, `release_write`.
        SplitWrite,
        /// `try_acquire_read`, releasing only on success.
        TryRead,
        /// `try_acquire_write`, releasing only on success.
        TryWrite,
        /// `enqueue`, `cancel`, then the unwind's two releases.
        WithdrawAndUnwind,
        /// `enqueue`, poll, `complete_read`, then the unwind at a member
        /// the core **holds** as a reader: `cancel` of its own (passed)
        /// ticket, then both releases (PR #890 review round 3).
        HoldReadThenUnwind,
        /// `enqueue`, poll, `complete_write`, then the unwind at a member
        /// the core **holds** as the writer: `cancel` of the ticket it
        /// still holds, then both releases.  This is the shape on which a
        /// withdrawal that reached the publish advanced `now_serving`
        /// under a set writer bit, and the release advanced it again.
        HoldWriteThenUnwind,
        /// `enqueue` twice — the second returns the same ticket — then
        /// the fused `acquire_read`, which acquires nothing new, then the
        /// split completion and the release (the class closure).
        EnqueueTwiceThenRead,
        /// The same with `acquire_write` and `complete_write`.
        EnqueueTwiceThenWrite,
    }

    const UNITS: [Unit; 11] = [
        Unit::ReadHold,
        Unit::WriteHold,
        Unit::SplitRead,
        Unit::SplitWrite,
        Unit::TryRead,
        Unit::TryWrite,
        Unit::WithdrawAndUnwind,
        Unit::HoldReadThenUnwind,
        Unit::HoldWriteThenUnwind,
        Unit::EnqueueTwiceThenRead,
        Unit::EnqueueTwiceThenWrite,
    ];

    /// Run `unit` on `core`.  `writers` counts writers inside their
    /// critical section; a reader asserts it is zero, a writer asserts
    /// it was zero on entry.
    fn run_unit(lock: &QueuedRwLock, writers: &AtomicUsize, core: u8, unit: Unit) {
        let in_read = || {
            assert_eq!(
                lock.peek_state() & WRITER_BIT,
                0,
                "reader admitted under a writer"
            );
            assert_eq!(
                writers.load(Ordering::SeqCst),
                0,
                "reader ran inside a writer's section"
            );
            assert_eq!(lock.peek_held(core), Some(HeldMode::Read));
        };
        let in_write = || {
            assert_eq!(
                writers.fetch_add(1, Ordering::SeqCst),
                0,
                "two writers at once"
            );
            assert_eq!(
                lock.peek_state(),
                WRITER_BIT,
                "writer admitted with readers"
            );
            assert_eq!(lock.peek_held(core), Some(HeldMode::Write));
            writers.fetch_sub(1, Ordering::SeqCst);
        };
        match unit {
            Unit::ReadHold => {
                lock.acquire_read(core);
                in_read();
                lock.release_read(core);
            }
            Unit::WriteHold => {
                lock.acquire_write(core);
                in_write();
                lock.release_write(core);
            }
            Unit::SplitRead => {
                let t = lock.enqueue(core);
                while !lock.is_served(t) {
                    loom::thread::yield_now();
                }
                lock.complete_read(core, t);
                in_read();
                lock.release_read(core);
            }
            Unit::SplitWrite => {
                let t = lock.enqueue(core);
                while !lock.is_served(t) {
                    loom::thread::yield_now();
                }
                lock.complete_write(core, t);
                in_write();
                lock.release_write(core);
            }
            Unit::TryRead => {
                if lock.try_acquire_read(core) {
                    in_read();
                    lock.release_read(core);
                }
            }
            Unit::TryWrite => {
                if lock.try_acquire_write(core) {
                    in_write();
                    lock.release_write(core);
                }
            }
            Unit::WithdrawAndUnwind => {
                let t = lock.enqueue(core);
                lock.cancel(core, t);
                lock.release_read(core);
                lock.release_write(core);
            }
            Unit::HoldReadThenUnwind => {
                let t = lock.enqueue(core);
                while !lock.is_served(t) {
                    loom::thread::yield_now();
                }
                lock.complete_read(core, t);
                in_read();
                lock.cancel(core, t);
                in_read();
                lock.release_read(core);
                lock.release_write(core);
            }
            Unit::HoldWriteThenUnwind => {
                let t = lock.enqueue(core);
                while !lock.is_served(t) {
                    loom::thread::yield_now();
                }
                lock.complete_write(core, t);
                in_write();
                lock.cancel(core, t);
                in_write();
                lock.release_read(core);
                lock.release_write(core);
            }
            Unit::EnqueueTwiceThenRead => {
                let t = lock.enqueue(core);
                assert_eq!(lock.enqueue(core), t, "one outstanding ticket per core");
                lock.acquire_read(core);
                assert_eq!(
                    lock.peek_held(core),
                    None,
                    "a queued core acquired nothing new"
                );
                lock.complete_read(core, t);
                in_read();
                lock.release_read(core);
            }
            Unit::EnqueueTwiceThenWrite => {
                let t = lock.enqueue(core);
                assert_eq!(lock.enqueue(core), t, "one outstanding ticket per core");
                lock.acquire_write(core);
                assert_eq!(
                    lock.peek_held(core),
                    None,
                    "a queued core acquired nothing new"
                );
                lock.complete_write(core, t);
                in_write();
                lock.release_write(core);
            }
        }
    }

    /// Every unordered pair of units, one per thread, explored
    /// exhaustively; after both threads finish the lock is drained, every
    /// issued ticket retired, every slot and held word empty.  Unordered,
    /// because the two cores are symmetric.
    #[test]
    fn every_pair_of_units_is_safe() {
        for (i, &a) in UNITS.iter().enumerate() {
            for &b in &UNITS[i..] {
                loom::model(move || {
                    let lock = Arc::new(QueuedRwLock::new());
                    let writers = Arc::new(AtomicUsize::new(0));
                    let (l1, w1) = (Arc::clone(&lock), Arc::clone(&writers));
                    let t = loom::thread::spawn(move || run_unit(&l1, &w1, 1, b));
                    run_unit(&lock, &writers, 0, a);
                    t.join().unwrap();
                    let (next, serving) = lock.peek_tickets();
                    assert_eq!(serving, next, "{a:?}/{b:?}: a ticket was never retired");
                    assert_eq!(lock.peek_state(), 0, "{a:?}/{b:?}: the lock did not drain");
                    for core in 0..2u8 {
                        assert_eq!(lock.peek_withdrawal(core), None, "{a:?}/{b:?}: slot");
                        assert_eq!(lock.peek_held(core), None, "{a:?}/{b:?}: held word");
                        assert_eq!(lock.peek_request(core), None, "{a:?}/{b:?}: request");
                    }
                });
            }
        }
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
    /// ticket passed on, nothing outstanding.  Four cores do it, since
    /// a second acquisition by the *same* core is the spec's no-op (the
    /// first cut of this test had one core acquire four times and
    /// asserted a recursive count the spec never had).
    #[test]
    fn try_acquire_read_matches_acquire_read_on_uncontended() {
        let attempted = QueuedRwLock::new();
        let blocking = QueuedRwLock::new();
        for core in 0..4u8 {
            assert!(
                attempted.try_acquire_read(core),
                "uncontended attempt succeeds"
            );
            blocking.acquire_read(core);
            assert_eq!(attempted.peek_state(), blocking.peek_state());
            assert_eq!(attempted.peek_tickets(), blocking.peek_tickets());
            assert_eq!(attempted.peek_held(core), Some(HeldMode::Read));
        }
        for core in 0..4u8 {
            attempted.release_read(core);
            blocking.release_read(core);
            assert_eq!(attempted.peek_state(), blocking.peek_state());
            assert_eq!(attempted.peek_held(core), None);
        }
        assert_eq!(attempted.peek_state(), 0);
        assert_eq!(attempted.peek_tail(), NONE_SENTINEL);
    }

    /// **PR #890 review round 2**: a holder's re-acquisition is the spec's
    /// no-op on every spelling — no ticket, no count, and the held word
    /// unchanged — and the one release that follows drains the lock.
    #[test]
    fn reacquisition_by_a_holder_is_a_noop() {
        let lock = QueuedRwLock::new();
        lock.acquire_read(0);
        let after_first = (lock.peek_state(), lock.peek_tickets());
        lock.acquire_read(0);
        assert!(!lock.try_acquire_read(0), "a holder acquires nothing");
        assert!(
            !lock.try_acquire_write(0),
            "a reader cannot become the writer by asking"
        );
        lock.acquire_write(0);
        assert_eq!((lock.peek_state(), lock.peek_tickets()), after_first);
        assert_eq!(lock.peek_held(0), Some(HeldMode::Read));
        lock.release_read(0);
        assert_eq!(lock.peek_state(), 0);
        assert_eq!(lock.peek_held(0), None);

        lock.acquire_write(1);
        let after_write = (lock.peek_state(), lock.peek_tickets());
        lock.acquire_write(1);
        lock.acquire_read(1);
        assert!(!lock.try_acquire_write(1));
        assert_eq!((lock.peek_state(), lock.peek_tickets()), after_write);
        assert_eq!(lock.peek_held(1), Some(HeldMode::Write));
        lock.release_write(1);
        assert_eq!(lock.peek_state(), 0);
        let (next, serving) = lock.peek_tickets();
        assert_eq!(serving, next, "exactly one ticket was issued and retired");
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

    /// Layout: the shared protocol words — the three counters, the
    /// withdrawal slots, the tail byte and the held bytes — fit the first
    /// 64-byte cache line, and the per-core request words fill the
    /// second, where their owner-only writes contend with nothing shared.
    #[test]
    fn shared_words_fill_the_first_line_and_requests_the_second() {
        assert!(core::mem::offset_of!(QueuedRwLock, held) + MAX_WAITERS <= 64);
        assert_eq!(core::mem::offset_of!(QueuedRwLock, request), 64);
        assert_eq!(core::mem::size_of::<QueuedRwLock>(), 128);
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
    /// reclaimed — is not a second retirement, and (WS-LC closure audit)
    /// it publishes nothing: a publication for a retired ticket is one
    /// no skip loop will ever claim, and `enqueue` waits on the slot, so
    /// it would park this core's next acquisition for good.
    #[test]
    fn cancel_does_not_retire_a_ticket_twice() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        let ticket = lock.enqueue(1);
        lock.cancel(1, ticket);
        lock.release_write(0);
        let (next, serving) = lock.peek_tickets();
        assert_eq!(serving, next);

        // `now_serving` has moved past the ticket, so the withdrawal is
        // refused before anything is published.
        lock.cancel(1, ticket);
        let (next_after, serving_after) = lock.peek_tickets();
        assert_eq!(next_after, next, "no ticket was issued");
        assert_eq!(
            serving_after, serving,
            "a stale withdrawal must not advance now_serving"
        );
        assert_eq!(
            lock.peek_withdrawal(1),
            None,
            "a stale withdrawal must publish nothing"
        );

        // And the core is not wedged: its next acquisition is issued at
        // once (an occupied slot would park it here forever).
        let again = lock.enqueue(1);
        assert!(lock.is_served(again));
        lock.complete_write(1, again);
        assert_eq!(lock.peek_state(), WRITER_BIT);
        lock.release_write(1);
        let (next_end, serving_end) = lock.peek_tickets();
        assert_eq!(serving_end, next_end);
    }

    /// A withdrawal naming **another core's** served write ticket, by a
    /// core with no request of its own, withdraws nothing: the lock
    /// publishes only the executing core's own recorded request, so the
    /// writer keeps its turn and no tombstone appears for its ticket.
    /// (A holder's own withdrawal is the no-op the held word decides,
    /// `cancel_by_a_holder_is_a_noop`.)
    #[test]
    fn cancel_naming_another_cores_ticket_withdraws_nothing() {
        let lock = QueuedRwLock::new();
        let ticket = lock.enqueue(0);
        lock.complete_write(0, ticket);
        let before = (lock.peek_state(), lock.peek_tickets());
        lock.cancel(1, ticket);
        assert_eq!((lock.peek_state(), lock.peek_tickets()), before);
        assert_eq!(lock.peek_withdrawal(0), None);
        assert_eq!(lock.peek_withdrawal(1), None);
        lock.release_write(0);
        let (next, serving) = lock.peek_tickets();
        assert_eq!(
            serving, next,
            "the turn was passed exactly once, by the release"
        );
    }

    // ------------------------------------------------------------------
    // PR #890 review round 3 — a holder withdraws nothing; a guard
    // releases only what it acquired
    // ------------------------------------------------------------------

    /// The unwind at a member the core holds: `cancel` of the ticket a
    /// writer still holds, or of the ticket a reader passed at entry,
    /// publishes nothing and moves nothing — decided by the held word,
    /// so it holds in release builds too.  Before, a writer's withdrawal
    /// was refused by a `debug_assert` only.
    #[test]
    fn cancel_by_a_holder_is_a_noop() {
        let lock = QueuedRwLock::new();
        let t = lock.enqueue(0);
        lock.complete_write(0, t);
        let before = (lock.peek_state(), lock.peek_tickets());
        lock.cancel(0, t);
        assert_eq!((lock.peek_state(), lock.peek_tickets()), before);
        assert_eq!(lock.peek_withdrawal(0), None, "nothing published");
        assert_eq!(lock.peek_held(0), Some(HeldMode::Write));
        // The turn is passed exactly once, by the release.
        let waiter = lock.enqueue(1);
        assert!(!lock.is_served(waiter));
        lock.release_write(0);
        assert!(
            lock.is_served(waiter),
            "the release hands the turn to the waiter"
        );
        lock.complete_read(1, waiter);
        let before = (lock.peek_state(), lock.peek_tickets());
        lock.cancel(1, waiter);
        assert_eq!((lock.peek_state(), lock.peek_tickets()), before);
        assert_eq!(lock.peek_withdrawal(1), None);
        assert_eq!(lock.peek_held(1), Some(HeldMode::Read));
        lock.release_read(1);
        let (next, serving) = lock.peek_tickets();
        assert_eq!(serving, next, "two tickets issued, two retired");
        assert_eq!(lock.peek_state(), 0);
        // And through the fused spelling, naming the served ticket.
        lock.acquire_write(2);
        let (_, serving) = lock.peek_tickets();
        lock.cancel(2, serving);
        assert_eq!(lock.peek_state(), WRITER_BIT);
        assert_eq!(lock.peek_tickets().1, serving);
        lock.release_write(2);
        assert_eq!(lock.peek_state(), 0);
    }

    /// A nested same-core read guard acquires nothing and releases
    /// nothing: the hold ends with the guard that took it.  Before, the
    /// inner guard's drop released the outer scope's hold.
    #[test]
    fn nested_read_guards_on_one_core_release_once() {
        let lock = QueuedRwLock::new();
        let outer = lock.acquire_read_guard(0);
        assert!(outer.acquired());
        {
            let inner = lock.acquire_read_guard(0);
            assert!(!inner.acquired(), "a holder acquires nothing");
            assert_eq!(lock.peek_state(), 1);
        }
        assert_eq!(lock.peek_state(), 1, "the inner guard released nothing");
        assert_eq!(lock.peek_held(0), Some(HeldMode::Read));
        drop(outer);
        assert_eq!(lock.peek_state(), 0);
        assert_eq!(lock.peek_held(0), None);
        let (next, serving) = lock.peek_tickets();
        assert_eq!(serving, next);
    }

    /// The same for the write guard, and for a read guard taken under a
    /// write guard (a holder in either mode acquires nothing).
    #[test]
    fn nested_write_guards_on_one_core_release_once() {
        let lock = QueuedRwLock::new();
        let outer = lock.acquire_write_guard(1);
        assert!(outer.acquired());
        {
            let inner = lock.acquire_write_guard(1);
            assert!(!inner.acquired());
            let read_under_write = lock.acquire_read_guard(1);
            assert!(!read_under_write.acquired());
            assert_eq!(lock.peek_state(), WRITER_BIT);
        }
        assert_eq!(
            lock.peek_state(),
            WRITER_BIT,
            "still held by the outer guard"
        );
        assert_eq!(lock.peek_held(1), Some(HeldMode::Write));
        drop(outer);
        assert_eq!(lock.peek_state(), 0);
        let (next, serving) = lock.peek_tickets();
        assert_eq!(serving, next, "one ticket issued and retired");
    }

    /// A guard on a core that holds nothing is an ordinary acquisition
    /// and release — the round-3 change costs the common case nothing.
    #[test]
    fn guards_on_distinct_cores_acquire_and_release() {
        let lock = QueuedRwLock::new();
        {
            let a = lock.acquire_read_guard(0);
            let b = lock.acquire_read_guard(1);
            assert!(a.acquired() && b.acquired());
            assert_eq!(lock.peek_state(), 2);
        }
        assert_eq!(lock.peek_state(), 0);
        {
            let w = lock.acquire_write_guard(2);
            assert!(w.acquired());
            assert_eq!(lock.peek_state(), WRITER_BIT);
        }
        assert_eq!(lock.peek_state(), 0);
    }

    // ------------------------------------------------------------------
    // The class closure — every entry point decides the executing core's
    // case on the lock's own words
    // ------------------------------------------------------------------

    /// A reader holder's `enqueue` returns the held sentinel: served at
    /// once, and every terminator treats it as the holder's no-op.  A
    /// writer holder is returned the ticket it still holds, with the
    /// same outcome.  No second ticket is issued in either case.
    #[test]
    fn enqueue_by_a_holder_issues_nothing() {
        let lock = QueuedRwLock::new();
        lock.acquire_read(0);
        let tickets = lock.peek_tickets();
        let t = lock.enqueue(0);
        assert_eq!(t, HELD_TICKET);
        assert!(lock.is_served(t));
        assert_eq!(lock.peek_tickets(), tickets, "no ticket issued");
        lock.complete_read(0, t);
        lock.complete_write(0, t);
        lock.cancel(0, t);
        assert_eq!(lock.peek_state(), 1);
        assert_eq!(lock.peek_held(0), Some(HeldMode::Read));
        assert_eq!(lock.peek_request(0), None);
        lock.release_read(0);

        lock.acquire_write(1);
        let tickets = lock.peek_tickets();
        let own = lock.enqueue(1);
        assert_eq!(Some(own), lock.peek_request(1), "the writer's own ticket");
        assert!(lock.is_served(own));
        assert_eq!(lock.peek_tickets(), tickets);
        lock.complete_write(1, own);
        lock.cancel(1, own);
        assert_eq!(lock.peek_state(), WRITER_BIT);
        assert_eq!(lock.peek_tickets(), tickets, "nothing passed");
        lock.release_write(1);
        assert_eq!(lock.peek_request(1), None);
        let (next, serving) = lock.peek_tickets();
        assert_eq!(serving, next);
    }

    /// A queued core's second `enqueue` returns the ticket it has: one
    /// outstanding ticket per core is a fact the lock establishes.  Its
    /// fused acquisitions and non-blocking attempts acquire nothing new,
    /// and its guards record that they acquired nothing.
    #[test]
    fn a_queued_core_is_issued_no_second_ticket() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        let t = lock.enqueue(1);
        let tickets = lock.peek_tickets();
        assert_eq!(lock.enqueue(1), t, "idempotent");
        lock.acquire_read(1);
        lock.acquire_write(1);
        assert!(!lock.try_acquire_read(1));
        assert!(!lock.try_acquire_write(1));
        {
            let g = lock.acquire_read_guard(1);
            assert!(!g.acquired());
        }
        assert_eq!(lock.peek_tickets(), tickets, "no ticket issued");
        assert_eq!(lock.peek_held(1), None, "still queued, not holding");
        assert_eq!(lock.peek_request(1), Some(t));
        lock.release_write(0);
        lock.complete_read(1, t);
        assert_eq!(lock.peek_held(1), Some(HeldMode::Read));
        assert_eq!(lock.peek_request(1), None);
        lock.release_read(1);
        let (next, serving) = lock.peek_tickets();
        assert_eq!(serving, next, "two tickets issued, two retired");
    }

    /// A completion waits for its own turn: a caller that did not poll
    /// `is_served` is not admitted ahead of the queue.
    #[test]
    fn complete_waits_for_its_turn() {
        use std::sync::Arc;
        let lock = Arc::new(QueuedRwLock::new());
        lock.acquire_write(0);
        let t = lock.enqueue(1);
        let entered = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let (l, e) = (Arc::clone(&lock), Arc::clone(&entered));
        let waiter = std::thread::spawn(move || {
            l.complete_read(1, t);
            e.store(true, Ordering::SeqCst);
            assert_eq!(l.peek_state() & WRITER_BIT, 0, "admitted under the writer");
            l.release_read(1);
        });
        std::thread::sleep(std::time::Duration::from_millis(20));
        assert!(!entered.load(Ordering::SeqCst), "completed before its turn");
        assert_eq!(lock.peek_state(), WRITER_BIT);
        lock.release_write(0);
        waiter.join().expect("waiter panicked");
        assert!(entered.load(Ordering::SeqCst));
        assert_eq!(lock.peek_state(), 0);
    }

    /// A terminator by a core with no live request is refused outright,
    /// in every build: it would enter a queue the core is not in.
    #[test]
    #[should_panic(expected = "has no live request")]
    fn a_terminator_without_a_request_is_refused() {
        let lock = QueuedRwLock::new();
        lock.complete_read(0, 0);
    }

    /// The same for a second completion after a withdrawal — a second
    /// terminator for one ticket.
    #[test]
    #[should_panic(expected = "has no live request")]
    fn a_second_terminator_for_one_ticket_is_refused() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        let t = lock.enqueue(1);
        lock.cancel(1, t);
        lock.complete_write(1, t);
    }

    /// A caller naming a ticket other than its own is reported in debug
    /// builds; the request the lock recorded is the one withdrawn.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "but its request is")]
    fn a_withdrawal_naming_another_ticket_is_reported() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        let t = lock.enqueue(1);
        lock.cancel(1, t + 1);
    }

    /// The per-core state a core can be in, as the lock's own words say
    /// it.  `Queued` is a live request whose turn has come but that is
    /// not yet completed — the same words as a request still waiting, and
    /// the form a single thread can drive through every entry point.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum CoreState {
        Idle,
        Queued,
        Withdrawn,
        HoldsRead,
        HoldsWrite,
    }

    const CORE_STATES: [CoreState; 5] = [
        CoreState::Idle,
        CoreState::Queued,
        CoreState::Withdrawn,
        CoreState::HoldsRead,
        CoreState::HoldsWrite,
    ];

    /// Every entry point that takes the executing core's id.  `build.rs`
    /// holds this list to the `pub fn`s of the lock that take `core_id`,
    /// so an entry point added to the lock is added here or the build
    /// fails, and the `match` below then refuses to run until it is
    /// classified in every state.
    const PER_CORE_ENTRY_POINTS: &[&str] = &[
        "acquire_read",
        "acquire_write",
        "release_read",
        "release_write",
        "try_acquire_read",
        "try_acquire_write",
        "enqueue",
        "complete_read",
        "complete_write",
        "cancel",
        "acquire_read_guard",
        "acquire_write_guard",
        "peek_withdrawal",
        "peek_held",
        "peek_request",
    ];

    /// Put core 0 into `state`, using core 1 as the writer that keeps a
    /// request queued or a withdrawal unretired.  Returns core 0's ticket
    /// where it has one.
    fn drive_core_zero_into(lock: &QueuedRwLock, state: CoreState) -> Option<u64> {
        match state {
            CoreState::Idle => None,
            CoreState::Queued => {
                lock.acquire_write(1);
                let t = lock.enqueue(0);
                lock.release_write(1);
                assert!(lock.is_served(t));
                Some(t)
            }
            CoreState::Withdrawn => {
                lock.acquire_write(1);
                let t = lock.enqueue(0);
                lock.cancel(0, t);
                assert_eq!(lock.peek_withdrawal(0), Some(t), "unretired: core 1 holds");
                Some(t)
            }
            CoreState::HoldsRead => {
                lock.acquire_read(0);
                None
            }
            CoreState::HoldsWrite => {
                lock.acquire_write(0);
                lock.peek_request(0)
            }
        }
    }

    type Snapshot = (u64, (u64, u64), Option<u64>, Option<HeldMode>, Option<u64>);

    fn snapshot(lock: &QueuedRwLock) -> Snapshot {
        (
            lock.peek_state(),
            lock.peek_tickets(),
            lock.peek_withdrawal(0),
            lock.peek_held(0),
            lock.peek_request(0),
        )
    }

    /// **The class closure, pinned**: every entry point, in every per-core
    /// state, does what the words say — a no-op where the spec no-ops, a
    /// refusal where the core has nothing to terminate, and the real
    /// operation otherwise.  Derived from the two lists above, so a state
    /// or an entry point added without a classification fails here.
    #[test]
    fn per_core_state_matrix() {
        use std::panic::{catch_unwind, AssertUnwindSafe};
        for &state in &CORE_STATES {
            for &entry in PER_CORE_ENTRY_POINTS {
                let lock = QueuedRwLock::new();
                let ticket = drive_core_zero_into(&lock, state);
                let before = snapshot(&lock);
                let t = ticket.unwrap_or(0);
                // What the entry point may do in this state.
                let refused = matches!(state, CoreState::Idle | CoreState::Withdrawn)
                    && matches!(entry, "complete_read" | "complete_write");
                let parks = state == CoreState::Withdrawn
                    && matches!(
                        entry,
                        "acquire_read"
                            | "acquire_write"
                            | "enqueue"
                            | "acquire_read_guard"
                            | "acquire_write_guard"
                    );
                if parks {
                    // Parks until core 1 retires the withdrawal — the
                    // loom model `double_withdrawal_by_one_core_does_not_strand_the_lock`
                    // covers the wait; a single thread cannot.
                    continue;
                }
                let outcome = catch_unwind(AssertUnwindSafe(|| match entry {
                    "acquire_read" => lock.acquire_read(0),
                    "acquire_write" => lock.acquire_write(0),
                    "release_read" => lock.release_read(0),
                    "release_write" => lock.release_write(0),
                    "try_acquire_read" => {
                        let _ = lock.try_acquire_read(0);
                    }
                    "try_acquire_write" => {
                        let _ = lock.try_acquire_write(0);
                    }
                    "enqueue" => {
                        let _ = lock.enqueue(0);
                    }
                    "complete_read" => lock.complete_read(0, t),
                    "complete_write" => lock.complete_write(0, t),
                    "cancel" => lock.cancel(0, t),
                    "acquire_read_guard" => drop(lock.acquire_read_guard(0)),
                    "acquire_write_guard" => drop(lock.acquire_write_guard(0)),
                    "peek_withdrawal" => {
                        let _ = lock.peek_withdrawal(0);
                    }
                    "peek_held" => {
                        let _ = lock.peek_held(0);
                    }
                    "peek_request" => {
                        let _ = lock.peek_request(0);
                    }
                    other => panic!("entry point {other} is not classified in the matrix"),
                }));
                let after = snapshot(&lock);
                if refused {
                    assert!(outcome.is_err(), "{entry:?} in {state:?} must be refused");
                    assert_eq!(
                        after, before,
                        "{entry:?} in {state:?}: refused, so untouched"
                    );
                    continue;
                }
                assert!(outcome.is_ok(), "{entry:?} in {state:?} must not panic");
                // The spec's no-ops, and the observation-only accessors.
                let noop = match (state, entry) {
                    (_, "peek_withdrawal" | "peek_held" | "peek_request") => true,
                    (CoreState::Idle, "release_read" | "release_write" | "cancel") => true,
                    // An involved core's guard acquires nothing and so
                    // releases nothing: a no-op in both directions.
                    (
                        CoreState::Queued | CoreState::HoldsRead | CoreState::HoldsWrite,
                        "acquire_read_guard" | "acquire_write_guard",
                    ) => true,
                    (
                        CoreState::Queued,
                        "acquire_read" | "acquire_write" | "release_read" | "release_write"
                        | "try_acquire_read" | "try_acquire_write" | "enqueue",
                    ) => true,
                    (
                        CoreState::Withdrawn,
                        "release_read" | "release_write" | "try_acquire_read" | "try_acquire_write"
                        | "cancel",
                    ) => true,
                    (
                        CoreState::HoldsRead,
                        "acquire_read" | "acquire_write" | "release_write" | "try_acquire_read"
                        | "try_acquire_write" | "enqueue" | "complete_read" | "complete_write"
                        | "cancel",
                    ) => true,
                    (
                        CoreState::HoldsWrite,
                        "acquire_read" | "acquire_write" | "release_read" | "try_acquire_read"
                        | "try_acquire_write" | "enqueue" | "complete_read" | "complete_write"
                        | "cancel",
                    ) => true,
                    _ => false,
                };
                if noop {
                    assert_eq!(after, before, "{entry:?} in {state:?} is the spec's no-op");
                } else {
                    assert_ne!(after, before, "{entry:?} in {state:?} must act");
                }
            }
        }
    }

    // ------------------------------------------------------------------
    // PR #890 review round 2 — a release by a non-holder is the spec's no-op
    // ------------------------------------------------------------------

    /// A core that does not hold the lock as a reader releases nothing:
    /// another core's read hold survives it, count and held word intact.
    /// Before the held word existed this decremented the count under the
    /// real holder, in release builds silently.
    #[test]
    fn release_read_by_a_non_holder_is_a_noop() {
        let lock = QueuedRwLock::new();
        lock.acquire_read(0);
        let before = (lock.peek_state(), lock.peek_tickets());
        lock.release_read(1);
        lock.release_read(2);
        assert_eq!((lock.peek_state(), lock.peek_tickets()), before);
        assert_eq!(lock.peek_held(0), Some(HeldMode::Read));
        assert_eq!(lock.peek_held(1), None);
        lock.release_read(0);
        assert_eq!(lock.peek_state(), 0);
        // And on an unheld lock: no underflow.
        lock.release_read(0);
        assert_eq!(lock.peek_state(), 0);
    }

    /// A core that is not the writer neither clears the bit nor passes
    /// the turn: the writer keeps the lock, and a waiter behind it is not
    /// admitted by a stranger's release.
    #[test]
    fn release_write_by_a_non_holder_is_a_noop() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        let waiter = lock.enqueue(1);
        let before = (lock.peek_state(), lock.peek_tickets());
        lock.release_write(2);
        lock.release_write(1);
        assert_eq!((lock.peek_state(), lock.peek_tickets()), before);
        assert_eq!(lock.peek_state(), WRITER_BIT);
        assert!(
            !lock.is_served(waiter),
            "a stranger's release must not pass the turn"
        );
        lock.release_write(0);
        assert!(lock.is_served(waiter));
        lock.complete_write(1, waiter);
        lock.release_write(1);
        assert_eq!(lock.peek_state(), 0);
    }

    /// The two-phase-locking unwind's shape, sequentially: a core that
    /// withdrew a queued request then "releases" the member in both
    /// modes, as `unwindAll` does for every member of a footprint.  The
    /// holder's state is untouched and the interval still closes.
    #[test]
    fn unwind_after_withdrawal_releases_nothing() {
        let lock = QueuedRwLock::new();
        lock.acquire_write(0);
        let ticket = lock.enqueue(1);
        lock.cancel(1, ticket);
        lock.release_read(1);
        lock.release_write(1);
        assert_eq!(lock.peek_state(), WRITER_BIT, "the holder still holds");
        assert_eq!(lock.peek_held(0), Some(HeldMode::Write));
        lock.release_write(0);
        let (next, serving) = lock.peek_tickets();
        assert_eq!(serving, next);
        assert_eq!(lock.peek_state(), 0);
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

    /// **WS-LC closure audit**: the double withdrawal.
    ///
    /// A core withdraws from behind a holder, re-enqueues and withdraws
    /// again while its first withdrawal is still unclaimed.  With one
    /// slot per core the second publication used to overwrite the
    /// first, and the holder's release then stopped `now_serving` on a
    /// ticket nobody held: the lock stalled with the tombstone lost, on
    /// a sequence every documented contract permits.  `enqueue` now
    /// waits for the slot, so the second ticket is issued only after the
    /// release has retired the first.
    ///
    /// The withdrawing thread signals just before its second `enqueue`,
    /// and the holder yields a few times after seeing the signal before
    /// releasing, so the wait is exercised rather than skipped on most
    /// iterations; `double_withdrawal_by_one_core_does_not_strand_the_lock`
    /// in the loom module is the exhaustive form.
    #[test]
    fn cross_thread_double_withdrawal_does_not_strand_the_lock() {
        const ITER: usize = if STRESS_ITER >= 100 {
            STRESS_ITER / 100
        } else {
            1
        };
        for _ in 0..ITER {
            let lock = Arc::new(QueuedRwLock::new());
            let reached_second_enqueue = Arc::new(AtomicBool::new(false));
            lock.acquire_write(0);

            let lock_w = Arc::clone(&lock);
            let flag = Arc::clone(&reached_second_enqueue);
            let withdrawer = thread::spawn(move || {
                let first = lock_w.enqueue(1);
                lock_w.cancel(1, first);
                flag.store(true, StdOrdering::SeqCst);
                // Parks until core 0's release has retired `first`.
                let second = lock_w.enqueue(1);
                lock_w.cancel(1, second);
            });

            while !reached_second_enqueue.load(StdOrdering::SeqCst) {
                thread::yield_now();
            }
            for _ in 0..8 {
                thread::yield_now();
            }
            lock.release_write(0);
            withdrawer.join().unwrap();

            let (next, serving) = lock.peek_tickets();
            assert_eq!(next, 3, "exactly three tickets were issued");
            assert_eq!(
                serving,
                next,
                "a withdrawn ticket was never retired: the lock is stalled \
                 (slot={:?}, state={:#x})",
                lock.peek_withdrawal(1),
                lock.peek_state()
            );
            assert_eq!(lock.peek_withdrawal(1), None, "the slot was reclaimed");
            assert_eq!(lock.peek_state(), 0, "a withdrawal releases nothing");

            // The lock is usable afterwards, by the withdrawing core too.
            lock.acquire_write(1);
            assert_eq!(lock.peek_state(), WRITER_BIT);
            lock.release_write(1);
            let (next_end, serving_end) = lock.peek_tickets();
            assert_eq!(serving_end, next_end);
        }
    }

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
