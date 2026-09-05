// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-SM SM2.C-defer D-6 / WS-RR RR6.2, RR6.3**: Rust-side RwLock
//! oracle binary for the Tier-5 cross-language correspondence harness.
//!
//! See `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` §5.6 and
//! `docs/planning/SMP_RELEASE_READINESS_PLAN.md` §RR6.
//!
//! ## Operation
//!
//! Reads an op-sequence on stdin (textual wire format), replays it
//! against **both deployed lock implementations** —
//! `sele4n_hal::rw_lock::RwLock` (CAS-retry) and
//! `sele4n_hal::queued_rw_lock::QueuedRwLock` (ticket FIFO) — and
//! prints the serialised state on stdout, one line per step: the initial
//! state, then the state after every operation.
//!
//! ## What changed at RR6.2, and why
//!
//! Through v0.34.48 this binary held a *software model* of the lock: a
//! second transliteration of `RwLockState.applyOp`, in Rust.  Two
//! transliterations of the same function agreeing tells you nothing
//! about the lock the kernel deploys, which is what the harness exists
//! to check.  Its docstring said so, and named the obstacle: the real
//! `acquire_read` / `acquire_write` **block** under contention, and a
//! single-threaded driver that parks on `wfe` is the only core that
//! could ever send the `sev` to wake itself.
//!
//! RR6.1 removed the obstacle by adding non-blocking single-attempt
//! entry points — `RwLock::try_acquire_read` / `try_acquire_write` and
//! `QueuedRwLock::try_acquire_read` / `try_acquire_write` — each one
//! iteration of the corresponding blocking loop with the retry removed.
//! This driver holds two real locks in process memory and moves them
//! only through those entry points and the real `release_*` methods.
//!
//! ## What is driven, and what is bookkeeping
//!
//! The abstract spec's state has three fields; the concrete locks
//! represent two of them:
//!
//! | Abstract field | CAS-retry lock | Ticket lock | Source here |
//! |----------------|----------------|-------------|-------------|
//! | `writerHeld` | bit 63 of `state` (the flag only) | the `held` words | **read from the ticket lock's words** |
//! | `readers` | bits 0..62 of `state` (the count only) | the `held` words | **read from the ticket lock's words** |
//! | `waiters` | not represented | the `request` words, ordered by ticket, with the `request_mode` words | **read from the ticket lock's words** |
//!
//! So the whole rendered line — *which* core holds the writer, *which*
//! cores hold as readers, and the queue *in order with each request's
//! mode* — is read back out of the ticket lock's per-core words after
//! every operation (PR #890 review round 5); the CAS-retry lock's packed
//! flag and count are cross-checked against it (`check_implementations_agree`)
//! and against the spec's counts (`check_encoding`).  Before this round
//! both oracles printed `W=<flag>;R=<count>;Q=<length>`, so a spec
//! regression that promoted the wrong waiter, reordered the queue or
//! changed a queued mode was invisible to the comparison: the counts
//! agreed while the identities did not.
//!
//! The driver still keeps a mirror of the spec's state — the branch of
//! `applyOp` to take, and which cores to admit when the spec promotes,
//! are decisions the driver makes from it — but nothing rendered comes
//! from the mirror.  The mirror is instead *held to the words* after
//! every operation: the ticket interval is exactly the held writer plus
//! the queued waiters plus the withdrawals nobody has skipped yet
//! (`check_ticket_interval`); the ticket being served is never one of
//! those withdrawals (`check_head_live` — `queuedSim`'s
//! `queuedHeadLive`, and the check that sees a stalled lock); each
//! core's withdrawal slot holds exactly the withdrawal the spec says is
//! pending for it (`check_withdrawal_slots`); each core's held word
//! reads what the spec says it holds (`check_holders`); and each core's
//! request word and mode word read the live request the spec has for
//! it (`check_requests`).  Those are the state-level half of the
//! `queuedSim` relation proved in
//! `SeLe4n/Kernel/Concurrency/Locks/QueuedRwLockRefinement.lean`; the
//! waiters-to-interval half is the part the proof carries and the
//! single-threaded harness cannot.  A waiter occupies the real queue by
//! *spinning in `await_turn`*, which a single-threaded driver cannot do,
//! so a queued waiter here holds a real ticket and is completed by the
//! driver exactly when the spec admits it.
//!
//! ## Traces a single thread cannot execute
//!
//! `QueuedRwLock::enqueue` parks until the calling core's previous
//! withdrawal has been retired by the core ahead of it (WS-LC closure
//! audit — issuing over a published slot is how the lock lost a
//! withdrawal and stalled).  A trace that asks a core to acquire while
//! its own withdrawal is still published therefore asks this thread to
//! wait for a release only another thread could perform.  That is not
//! a sequential execution of the deployed lock at all — the
//! refinement's `acquire*_enqueue` blocks require the slot empty — so
//! the driver reports it as such (`Halt::NotSequential`, exit status 3)
//! rather than guess a linearisation, and the harness counts the
//! exclusion instead of comparing outputs the two oracles cannot both
//! have.
//!
//! Admission order **is** exercised: when the abstract promotes a batch
//! of readers or a single writer — at a release, and (PR #890 review
//! round 5) at a withdrawal that uncovers a reader run at the head — the
//! driver replays exactly those cores against the real ticket lock, in
//! exactly that order, and every one of those attempts must succeed.  A
//! ticket lock that admitted a different core, or refused one the spec
//! admits, fails the run.
//!
//! **What a withdrawal decides is asserted** (PR #890 review round 5).
//! The deployed `cancel` reports whether it withdrew or realised an
//! admission the spec had already made (`CancelOutcome`), and the driver
//! holds that verdict to the spec's: a queued waiter's withdrawal must
//! report `Withdrawn`, a holder's — issued with the ticket the core held
//! — and an uninvolved core's must report the no-op.  A lock that
//! withdrew a request the spec had promoted, or entered on one the spec
//! still queues, fails the run before the words are compared.
//!
//! **So are the spec's no-ops** (PR #890 review round 2, completed by
//! the class closure behind rounds 2 and 3).  A release by a non-holder,
//! a withdrawal by a holder or by a core with no request, and a
//! re-acquisition by any *involved* core — a holder or a queued waiter
//! — are issued to the real ticket lock, which must decide each on the
//! executing core's own words and return without touching anything;
//! `check_holders` then holds every core's held word to the spec's
//! `readers` / `writerHeld` (`queuedSim`'s `queuedHeldSim`) and
//! `check_requests` every core's request word to the spec's queue and
//! held writer (`queuedRequestsSim`).  Before the words existed the
//! driver gated the no-ops itself, so the lock was never asked the
//! question the two-phase-locking unwind asks of it; and until the
//! request word existed a queued waiter's re-acquisition was issued to
//! neither lock, because the lock had no record of the waiter's request
//! and a second ticket was the caller contract's violation rather than
//! a path the lock had.  The CAS-retry lock is still not sent the
//! no-ops: it has no holder bookkeeping, a non-holder's release there is
//! an unconditional `fetch_sub`, and its refinement bridge carries no
//! block for the call — that is its caller contract, not a no-op.
//!
//! ## Wire format
//!
//! `R<core>` = tryAcquireRead, `r<core>` = releaseRead,
//! `W<core>` = tryAcquireWrite, `w<core>` = releaseWrite,
//! `c<core>` = cancel (WS-LC LC3.6).
//! Each op is terminated by a comma `,`.
//!
//! ## Output format
//!
//! One line per state — the initial state, then one after each op —
//! each `W=<core|->;R=<sorted reader cores>;Q=<core:r|w,...>`: the
//! writer's identity, the reader **set** (sorted, because the spec's
//! `readers` order is not semantic — the Lean fold prepends a promoted
//! batch and the driver here admits one core at a time), and the queue
//! in order with each request's mode.  Matches the Lean oracle
//! (`tests/Tier5/RwLockOracle.lean`) line for line, so a mid-trace
//! divergence that later converges is caught too.

use std::io::Read;

use sele4n_hal::queued_rw_lock::{CancelOutcome, HeldMode, QueuedRwLock};
use sele4n_hal::rw_lock::{RwLock, WRITER_BIT};

/// Cores the wire format may name.  Matches the Lean oracle's
/// `numCores` gate and `QueuedRwLock::MAX_WAITERS`.
const NUM_CORES: u8 = 4;

/// Exit status on a trace that does not parse — the Lean oracle's too,
/// so the harness reads one number for one condition on both sides.
const PARSE_ERROR_STATUS: i32 = 2;

/// The Rust mirror of the abstract `RwLockOp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Op {
    AcquireRead(u8),
    ReleaseRead(u8),
    AcquireWrite(u8),
    ReleaseWrite(u8),
    /// **WS-LC LC3.6**: withdraw a queued request (`RwLockOp.cancel`).
    Cancel(u8),
}

/// Parse one token (no comma).  Returns `None` on parse error, which
/// includes a core id the model does not have.
fn parse_op(tok: &str) -> Option<Op> {
    let tok = tok.trim();
    if tok.is_empty() {
        return None;
    }
    let head = tok.chars().next()?;
    let rest = &tok[head.len_utf8()..];
    let core: u8 = rest.parse().ok()?;
    if core >= NUM_CORES {
        return None;
    }
    match head {
        'R' => Some(Op::AcquireRead(core)),
        'r' => Some(Op::ReleaseRead(core)),
        'W' => Some(Op::AcquireWrite(core)),
        'w' => Some(Op::ReleaseWrite(core)),
        'c' => Some(Op::Cancel(core)),
        _ => None,
    }
}

/// Parse a comma-separated op-sequence.
fn parse_trace(input: &str) -> Option<Vec<Op>> {
    let mut ops = Vec::new();
    for tok in input.split(',') {
        let tok = tok.trim();
        if tok.is_empty() {
            continue;
        }
        ops.push(parse_op(tok)?);
    }
    Some(ops)
}

/// Why a replay stopped short of a post-state.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Halt {
    /// A mismatch between the two deployed implementations, between an
    /// implementation and the admission the spec dictates, or between
    /// the ticket lock's words and the expectation derived from the
    /// spec.  Exit status 1.
    Divergence(String),
    /// The trace asks a core to acquire while its own withdrawal is
    /// still published — see the module docs.  Exit status 3; the
    /// harness counts these rather than comparing outputs.
    NotSequential(String),
}

impl Halt {
    fn message(&self) -> &str {
        match self {
            Halt::Divergence(m) | Halt::NotSequential(m) => m,
        }
    }
}

/// The driver: the abstract queue the concrete locks do not carry, plus
/// one live instance of each deployed implementation.
struct Driver {
    /// Writer holder, per the abstract spec.  Drives which concrete
    /// operation is issued; the *flag* reported is read from the locks.
    writer_held: Option<u8>,
    /// Reader cores currently holding, per the abstract spec, each with
    /// the ticket it was admitted on.  Same role as the writer: identity
    /// is abstract, the *count* reported is concrete.  The ticket is kept
    /// (PR #890 review round 3) so a holder's withdrawal can be issued to
    /// the ticket lock with the ticket the core actually held.
    readers: Vec<(u8, u64)>,
    /// Waiters in FIFO order: `(core, mode_is_write, ticket)`.
    ///
    /// **WS-LC LC3.6**: the ticket is the queued lock's, and carrying it
    /// is what makes a waiter *concrete*.  Before this the driver
    /// admitted every core the spec admits and left queued waiters
    /// abstract, so the ticket lock never had more than one outstanding
    /// ticket and its queue was never exercised — and a withdrawal, which
    /// is an operation *on* the queue, would have had nothing to
    /// withdraw.  The CAS-retry lock has no queue and so takes no part in
    /// this; that asymmetry is `opCorresponds.cancel_no_queue`.
    waiters: Vec<(u8, bool, u64)>,
    /// **WS-LC LC3.6**: `(core, ticket)` for each withdrawn ticket the
    /// lock has not yet skipped, oldest first.
    ///
    /// Driver-side, so the checks compare the lock's counters and slots
    /// against an expectation derived from the *spec* rather than read
    /// back out of the lock.  The core is recorded (WS-LC closure audit)
    /// so `check_withdrawal_slots` can hold each per-core slot to the
    /// one withdrawal the spec says is pending for that core.
    tombstones: Vec<(u8, u64)>,
    /// The deployed CAS-retry lock (`rust/sele4n-hal/src/rw_lock.rs`).
    cas: RwLock,
    /// The deployed ticket FIFO lock
    /// (`rust/sele4n-hal/src/queued_rw_lock.rs`).
    queued: QueuedRwLock,
}

impl Driver {
    fn new() -> Self {
        Self {
            writer_held: None,
            readers: Vec::new(),
            waiters: Vec::new(),
            tombstones: Vec::new(),
            cas: RwLock::new(),
            queued: QueuedRwLock::new(),
        }
    }

    /// Predicate: `c` is already a holder or a waiter.  The abstract
    /// spec's `RwLockState.coreInvolved`.
    fn core_involved(&self, c: u8) -> bool {
        self.reader_ticket(c).is_some()
            || self.writer_held == Some(c)
            || self.waiters.iter().any(|w| w.0 == c)
    }

    /// The ticket `c` was admitted on as a reader, if it holds as one.
    fn reader_ticket(&self, c: u8) -> Option<u64> {
        self.readers.iter().find(|r| r.0 == c).map(|r| r.1)
    }

    // ---------------------------------------------------------------
    // Concrete admission / release — the only places the real locks move
    // ---------------------------------------------------------------

    /// Admit `c` as a reader on both real locks.  Both attempts must
    /// succeed: the spec admits here, so an implementation that refuses
    /// has diverged from it.
    fn admit_reader(&mut self, c: u8, ticket: u64) -> Result<(), Halt> {
        if !self.cas.try_acquire_read() {
            return Err(Halt::Divergence(format!(
                "cas-retry lock refused a read admission the spec grants (core {c}, state 0x{:x})",
                self.packed_cas()
            )));
        }
        if !self.queued.is_served(ticket) {
            return Err(Halt::Divergence(format!(
                "ticket lock is not serving the ticket the spec admits (core {c}, ticket \
                 {ticket}, tickets {:?})",
                self.queued.peek_tickets()
            )));
        }
        self.queued.complete_read(c, ticket);
        self.readers.insert(0, (c, ticket));
        Ok(())
    }

    /// Admit `c` as the writer on both real locks.
    fn admit_writer(&mut self, c: u8, ticket: u64) -> Result<(), Halt> {
        if !self.cas.try_acquire_write() {
            return Err(Halt::Divergence(format!(
                "cas-retry lock refused a write admission the spec grants (core {c}, state 0x{:x})",
                self.packed_cas()
            )));
        }
        if !self.queued.is_served(ticket) {
            return Err(Halt::Divergence(format!(
                "ticket lock is not serving the ticket the spec admits (core {c}, ticket \
                 {ticket}, tickets {:?})",
                self.queued.peek_tickets()
            )));
        }
        self.queued.complete_write(c, ticket);
        self.writer_held = Some(c);
        Ok(())
    }

    /// **PR #890 review round 2**, widened by the class closure: issue an
    /// *involved* core's re-acquisition to the real ticket lock — the
    /// spec's no-op, which the lock decides on the core's own words: a
    /// holder returns on its held word, a queued waiter on its request
    /// word.  A waiter used to be issued to neither lock, because the
    /// lock had no record of its request and a second ticket was the
    /// caller contract's violation rather than a path the lock had; now
    /// the fused acquisition *is* that path, and returns.  The words are
    /// read first so a lock that had forgotten both fails the run
    /// instead of parking this single thread on a ticket nobody would
    /// ever serve.
    fn reacquire_as_involved(&self, c: u8, write: bool) -> Result<(), Halt> {
        if !self.core_involved(c) {
            return Ok(());
        }
        if self.queued.peek_held(c).is_none() && self.queued.peek_request(c).is_none() {
            return Err(Halt::Divergence(format!(
                "core {c} is involved per the spec but both its words are clear; \
                 re-acquiring would take a ticket and park"
            )));
        }
        if write {
            self.queued.acquire_write(c);
        } else {
            self.queued.acquire_read(c);
        }
        Ok(())
    }

    /// Release `c`'s read lock on both real locks.
    fn release_reader(&mut self, c: u8) {
        self.readers.retain(|x| x.0 != c);
        self.cas.release_read();
        self.queued.release_read(c);
    }

    /// Release the write lock on both real locks.
    fn release_writer(&mut self, c: u8) {
        self.writer_held = None;
        self.cas.release_write();
        self.queued.release_write(c);
    }

    // ---------------------------------------------------------------
    // Abstract step function — mirrors `RwLockState.applyOp`
    // ---------------------------------------------------------------

    /// Apply one operation.  The branch taken is the abstract spec's;
    /// every state change it dictates is performed on the real locks.
    fn apply(&mut self, op: Op) -> Result<(), Halt> {
        match op {
            Op::AcquireRead(c) => {
                if self.core_involved(c) {
                    return self.reacquire_as_involved(c, false);
                }
                self.refuse_parked_issue(c)?;
                // Every acquisition takes a real ticket, whether it is
                // admitted at once or queued — that is what makes a
                // queued waiter concrete (WS-LC LC3.6) — and records the
                // mode the lock decides a later withdrawal on.
                let ticket = self.queued.enqueue(c, HeldMode::Read);
                // Strict FIFO (SM2.C-defer §5.3): a new reader enqueues
                // iff any holder OR any queued waiter exists.  This is
                // `applyOp`'s branch verbatim; the pre-RR6.2 model here
                // used the retired "head waiter is a writer" test, which
                // differs on states the spec's INV-R5 rules out but which
                // nothing in this binary ruled out.
                if self.writer_held.is_some() || !self.waiters.is_empty() {
                    self.waiters.push((c, false, ticket));
                    Ok(())
                } else {
                    self.admit_reader(c, ticket)
                }
            }
            Op::ReleaseRead(c) => {
                if self.reader_ticket(c).is_none() {
                    // The spec's no-op, issued to the real ticket lock:
                    // its held word must make `release_read` return
                    // without touching the count, which `check_all`
                    // then verifies.  The CAS-retry lock is not sent it —
                    // a non-holder's release is outside its contract.
                    self.queued.release_read(c);
                    return Ok(());
                }
                self.release_reader(c);
                // `promoteWaitersIfReadersEmpty`.
                if self.readers.is_empty() && self.writer_held.is_none() {
                    self.promote_head()?;
                }
                Ok(())
            }
            Op::AcquireWrite(c) => {
                if self.core_involved(c) {
                    return self.reacquire_as_involved(c, true);
                }
                self.refuse_parked_issue(c)?;
                let ticket = self.queued.enqueue(c, HeldMode::Write);
                if self.writer_held.is_some()
                    || !self.readers.is_empty()
                    || !self.waiters.is_empty()
                {
                    self.waiters.push((c, true, ticket));
                    Ok(())
                } else {
                    self.admit_writer(c, ticket)
                }
            }
            Op::ReleaseWrite(c) => {
                if self.writer_held != Some(c) {
                    // As for `ReleaseRead`: the ticket lock's word must
                    // make this return without clearing anything.
                    self.queued.release_write(c);
                    return Ok(());
                }
                self.release_writer(c);
                // `promoteWaitersOnWriterRelease`.
                self.promote_head()
            }
            Op::Cancel(c) => {
                // `applyOp .cancel`: drop `c`'s queued request, then —
                // PR #890 review round 5 — promote the reader run that a
                // withdrawn head uncovers.  A core that is holding, or
                // that has no request, is untouched on both sides — and
                // both are issued to the real ticket lock: a *holder's*
                // withdrawal (PR #890 review round 3) with the ticket the
                // core actually held — the writer still holds its own, a
                // reader's was passed at entry — and (the class closure)
                // an uninvolved core's with the ticket being served, a
                // belief the lock must refuse on its own record of the
                // core's request rather than on the ticket named.  The
                // lock's words must make each publish nothing, which
                // `check_all` then verifies; and what each reports is
                // held to the spec's verdict (`expect_outcome`).
                if self.writer_held == Some(c) {
                    let (_, serving) = self.queued.peek_tickets();
                    let outcome = self.queued.cancel(c, serving);
                    return Self::expect_outcome(
                        c,
                        "the held writer",
                        outcome,
                        CancelOutcome::Holding,
                    );
                }
                if let Some(ticket) = self.reader_ticket(c) {
                    let outcome = self.queued.cancel(c, ticket);
                    return Self::expect_outcome(
                        c,
                        "a holding reader",
                        outcome,
                        CancelOutcome::Holding,
                    );
                }
                let Some(i) = self.waiters.iter().position(|w| w.0 == c) else {
                    let (_, serving) = self.queued.peek_tickets();
                    let outcome = self.queued.cancel(c, serving);
                    return Self::expect_outcome(
                        c,
                        "an uninvolved core",
                        outcome,
                        CancelOutcome::Withdrawn,
                    );
                };
                let (_, _, ticket) = self.waiters.remove(i);
                // A queued waiter is a request the spec has not admitted,
                // so the lock — deciding on its own words: a served write
                // request with a reader holding, or a read request with
                // a live write request ahead of it — must withdraw it.
                // `Holding` here is the served-ticket defect this round
                // closed: the lock entering on a request the spec queues.
                let outcome = self.queued.cancel(c, ticket);
                Self::expect_outcome(c, "a queued waiter", outcome, CancelOutcome::Withdrawn)?;
                // The withdrawal is retired at once when the core was the
                // head, and left as a tombstone otherwise.  Recording it
                // driver-side is what lets `check_ticket_interval` derive
                // the expected interval from the spec rather than read it
                // back out of the lock's own slots.
                let (_, serving) = self.queued.peek_tickets();
                if ticket >= serving {
                    self.tombstones.push((c, ticket));
                }
                self.retire_passed_tombstones();
                // `cancelPromotes`: no writer holds and the new head is a
                // reader — in a reachable state, exactly when the
                // withdrawer was the head, whose retirement passed the
                // turn to the run behind it.  The spec admits that run;
                // the driver admits the same cores in the same order.
                if self.writer_held.is_none() && matches!(self.waiters.first(), Some((_, false, _)))
                {
                    self.promote_reader_run()?;
                }
                Ok(())
            }
        }
    }

    /// **PR #890 review round 5**: the deployed withdrawal's verdict must
    /// be the spec's.  `who` names the case the spec is in for `c`.
    fn expect_outcome(
        c: u8,
        who: &str,
        outcome: CancelOutcome,
        expected: CancelOutcome,
    ) -> Result<(), Halt> {
        if outcome != expected {
            return Err(Halt::Divergence(format!(
                "cancel by core {c} — {who} per the spec — reported {outcome:?}, but the \
                 spec's withdrawal is {expected:?}"
            )));
        }
        Ok(())
    }

    /// Admit the contiguous run of readers at the head of the queue, in
    /// queue order — the reader arm of both promotions, since the spec's
    /// `promoteWaitersOnWriterRelease` and its `cancel` share it.
    fn promote_reader_run(&mut self) -> Result<(), Halt> {
        let mut batch = Vec::new();
        while let Some((c, false, ticket)) = self.waiters.first().copied() {
            batch.push((c, ticket));
            self.waiters.remove(0);
        }
        // Admit in queue order: the spec's batch order is the ticket
        // lock's ticket order.
        for (c, ticket) in batch {
            self.admit_reader(c, ticket)?;
            // Each admission passes its own ticket on, which can uncover
            // a tombstone the skip loop then retires.
            self.retire_passed_tombstones();
        }
        Ok(())
    }

    /// **WS-LC LC3.6**: forget tombstones the lock has already skipped.
    ///
    /// A withdrawn ticket below `now_serving` has been retired by
    /// somebody's skip loop; keeping it would make the expected interval
    /// too wide.
    fn retire_passed_tombstones(&mut self) {
        let (_, serving) = self.queued.peek_tickets();
        self.tombstones.retain(|&(_, t)| t >= serving);
    }

    /// **WS-LC closure audit**: refuse to replay an acquisition the
    /// deployed lock would park.
    ///
    /// `QueuedRwLock::enqueue` waits until the core's withdrawal slot is
    /// empty, and only a release or an entry by the core ahead can empty
    /// it — which, on this thread, would be a later op in the trace.
    /// The decision reads the lock's own slot, which is the fact; the
    /// spec-derived bookkeeping is held to it by `check_withdrawal_slots`
    /// after every op, so the two cannot disagree here unnoticed.
    fn refuse_parked_issue(&self, c: u8) -> Result<(), Halt> {
        match self.queued.peek_withdrawal(c) {
            None => Ok(()),
            Some(ticket) => Err(Halt::NotSequential(format!(
                "core {c} would park in enqueue: its withdrawal of ticket {ticket} is \
                 still published, and only another core's release can retire it"
            ))),
        }
    }

    /// Promote the head of the queue: a single writer, or the whole
    /// contiguous run of readers.
    ///
    /// The promoted cores are replayed against the real locks in exactly
    /// this order, and each attempt must succeed — which is where the
    /// ticket lock's admission order is checked against the spec's.
    fn promote_head(&mut self) -> Result<(), Halt> {
        // The release that brought us here ran the skip loop, so whatever
        // tombstones it uncovered are gone.
        self.retire_passed_tombstones();
        match self.waiters.first().copied() {
            None => Ok(()),
            Some((c, true, ticket)) => {
                self.waiters.remove(0);
                self.admit_writer(c, ticket)
            }
            Some((_, false, _)) => self.promote_reader_run(),
        }
    }

    // ---------------------------------------------------------------
    // Cross-checks
    // ---------------------------------------------------------------

    /// The CAS-retry lock's packed word, recomposed from `snapshot`.
    fn packed_cas(&self) -> u64 {
        let (writer, count) = self.cas.snapshot();
        (if writer { WRITER_BIT } else { 0 }) | count
    }

    /// Both deployed implementations must hold the same packed state
    /// after every operation.  They are different algorithms refining
    /// one spec; a disagreement is a refinement defect in one of them.
    fn check_implementations_agree(&self) -> Result<(), Halt> {
        let cas = self.packed_cas();
        let queued = self.queued.peek_state();
        if cas != queued {
            return Err(Halt::Divergence(format!(
                "deployed implementations disagree: cas-retry 0x{cas:x} vs ticket 0x{queued:x}"
            )));
        }
        Ok(())
    }

    /// The ticket lock's outstanding-ticket count is the held writer,
    /// plus the queued waiters, plus the withdrawals nobody has skipped
    /// yet.
    ///
    /// **WS-LC LC3.6 — re-derived, not patched.**  This used to read
    /// `expected = writer_held.is_some()`, and it was right *because the
    /// driver never left a waiter spinning*: every core the spec queued
    /// was abstract, so the only outstanding ticket was a holding
    /// writer's.  Once waiters hold real tickets that constant is simply
    /// a different quantity, and a withdrawal adds a third kind of
    /// outstanding ticket that is neither a holder's nor a waiter's.
    /// Widening the constant would have hidden both.
    ///
    /// Every ticket in `[now_serving, next_ticket)` is therefore exactly
    /// one of: the writer's (it holds its ticket until `release_write`),
    /// a waiter's, or a tombstone.  A *reader* passes its ticket on at
    /// entry, so a holding reader contributes none.  That partition is
    /// the reachable-state instance of `queuedSim`'s ticket-interval
    /// relation, now including its `liveLedger` half.
    fn check_ticket_interval(&self) -> Result<(), Halt> {
        let (next, serving) = self.queued.peek_tickets();
        if serving > next {
            return Err(Halt::Divergence(format!(
                "ticket lock regressed: now_serving {serving} > next_ticket {next}"
            )));
        }
        let pending = self
            .tombstones
            .iter()
            .filter(|&&(_, t)| t >= serving)
            .count() as u64;
        let expected = u64::from(self.writer_held.is_some()) + self.waiters.len() as u64 + pending;
        let outstanding = next - serving;
        if outstanding != expected {
            return Err(Halt::Divergence(format!(
                "ticket interval is {outstanding} (next {next}, serving {serving}) but the \
                 spec state has writer_held={:?}, {} waiter(s) and {pending} tombstone(s)",
                self.writer_held,
                self.waiters.len()
            )));
        }
        Ok(())
    }

    /// The concrete words must encode the abstract holder state, per
    /// `encodeRwLock`: bit 63 is `writerHeld.isSome`, bits 0..62 are
    /// `readers.length`.
    fn check_encoding(&self) -> Result<(), Halt> {
        let packed = self.packed_cas();
        let expected = (if self.writer_held.is_some() {
            WRITER_BIT
        } else {
            0
        }) | self.readers.len() as u64;
        if packed != expected {
            return Err(Halt::Divergence(format!(
                "concrete state 0x{packed:x} does not encode the spec state \
                 (writer_held={:?}, readers={:?}) — expected 0x{expected:x}",
                self.writer_held, self.readers
            )));
        }
        Ok(())
    }

    /// **WS-LC closure audit**: the ticket being served is never a
    /// withdrawn one — `queuedSim`'s `queuedHeadLive`, at the block
    /// boundary every op ends on.
    ///
    /// This is the check that sees a stalled lock, and the interval
    /// check alone does not: when a withdrawal is *lost* — overwritten
    /// in its core's slot before anything skipped it — the ticket stays
    /// outstanding, the driver still counts it as pending, and the
    /// interval balances exactly while `now_serving` sits on a ticket
    /// nobody will ever retire.  The double-withdrawal stall passed
    /// `check_ticket_interval` for that reason; it fails here.
    fn check_head_live(&self) -> Result<(), Halt> {
        let (next, serving) = self.queued.peek_tickets();
        if serving < next && self.tombstones.iter().any(|&(_, t)| t == serving) {
            return Err(Halt::Divergence(format!(
                "the ticket being served ({serving}) is a withdrawn one nobody retired: \
                 the lock is stalled (next {next}, tombstones {:?})",
                self.tombstones
            )));
        }
        Ok(())
    }

    /// **WS-LC closure audit**: each core's withdrawal slot holds exactly
    /// the withdrawal the spec says is pending for that core.
    ///
    /// Three relations at once, each the concrete form of a
    /// `QueuedTicketWf` fact: a slot is published iff a withdrawal of
    /// that core is outstanding (`cancelledOutstanding`), it names that
    /// withdrawal's ticket, and no core has two pending withdrawals
    /// (`holder_ticket_unique`).  A stale publication — a slot naming a
    /// ticket the lock has passed — and a lost one — a pending withdrawal
    /// whose slot is empty — both fail here.
    fn check_withdrawal_slots(&self) -> Result<(), Halt> {
        let (_, serving) = self.queued.peek_tickets();
        for core in 0..NUM_CORES {
            let pending: Vec<u64> = self
                .tombstones
                .iter()
                .filter(|&&(c, t)| c == core && t >= serving)
                .map(|&(_, t)| t)
                .collect();
            if pending.len() > 1 {
                return Err(Halt::Divergence(format!(
                    "core {core} has {} pending withdrawals {pending:?}; a core holds one \
                     outstanding ticket and can withdraw at most one",
                    pending.len()
                )));
            }
            let expected = pending.first().copied();
            let slot = self.queued.peek_withdrawal(core);
            if slot != expected {
                return Err(Halt::Divergence(format!(
                    "withdrawal slot of core {core} holds {slot:?} but the spec-derived \
                     pending withdrawal is {expected:?} (serving {serving})"
                )));
            }
        }
        Ok(())
    }

    /// **PR #890 review round 2**: each core's held word reads exactly
    /// what the spec says the core holds — `queuedSim`'s
    /// `queuedHeldSim`, at the block boundary every op ends on.
    ///
    /// This is the check behind the no-op gates in `apply`: a
    /// non-holder's release and a holder's re-acquisition are issued to
    /// the real ticket lock, and it is the word pinned here that makes
    /// them return without moving anything.  A word reading held for a
    /// core the spec has released would let that core's next
    /// acquisition skip the queue; one reading clear for a holder would
    /// make its release a no-op and leak the hold.
    fn check_holders(&self) -> Result<(), Halt> {
        for core in 0..NUM_CORES {
            let expected = if self.writer_held == Some(core) {
                Some(HeldMode::Write)
            } else if self.reader_ticket(core).is_some() {
                Some(HeldMode::Read)
            } else {
                None
            };
            let actual = self.queued.peek_held(core);
            if actual != expected {
                return Err(Halt::Divergence(format!(
                    "held word of core {core} reads {actual:?} but the spec has \
                     writer_held={:?}, readers={:?} (expected {expected:?})",
                    self.writer_held, self.readers
                )));
            }
        }
        Ok(())
    }

    /// **The class closure behind PR #890 review rounds 2 and 3**: every
    /// core's request word reads exactly the live request the spec has
    /// for it — the served ticket for the held writer, its own ticket
    /// for a queued waiter, and nothing for a reader (a reader passes
    /// its ticket on at entry), a withdrawn core or an uninvolved one.
    /// `queuedSim`'s `queuedRequestsSim`.
    ///
    /// This is the word the fused acquisitions and `enqueue` decide a
    /// queued core's no-op on, and the one the terminators verify a
    /// caller's ticket against.  A word reading a request the spec does
    /// not have would refuse that core's next acquisition; one reading
    /// clear for a waiter would issue it a second ticket, which is the
    /// stall the one-outstanding-ticket contract used to guard against
    /// by convention alone.
    fn check_requests(&self) -> Result<(), Halt> {
        let (_, serving) = self.queued.peek_tickets();
        for core in 0..NUM_CORES {
            let expected = if self.writer_held == Some(core) {
                Some((serving, HeldMode::Write))
            } else {
                self.waiters
                    .iter()
                    .find(|w| w.0 == core)
                    .map(|w| (w.2, if w.1 { HeldMode::Write } else { HeldMode::Read }))
            };
            let actual = self
                .queued
                .peek_request(core)
                .map(|ticket| (ticket, self.queued.peek_request_mode(core)));
            let actual = actual
                .map(|(ticket, mode)| (ticket, mode.expect("a live request has a mode word")));
            if actual != expected {
                return Err(Halt::Divergence(format!(
                    "request word of core {core} reads {actual:?} but the spec has \
                     writer_held={:?}, waiters={:?} (expected {expected:?})",
                    self.writer_held, self.waiters
                )));
            }
        }
        Ok(())
    }

    /// Every invariant checked after each operation.
    fn check_all(&self) -> Result<(), Halt> {
        self.check_implementations_agree()?;
        self.check_ticket_interval()?;
        self.check_head_live()?;
        self.check_withdrawal_slots()?;
        self.check_holders()?;
        self.check_requests()?;
        self.check_encoding()
    }

    /// Render the state, **from the ticket lock's words** (PR #890
    /// review round 5): the writer is the core whose held word reads
    /// `Write`, the readers are the cores whose held words read `Read`
    /// (sorted), and the queue is every core with a live request and no
    /// hold — a holding writer keeps its request — in ticket order, each
    /// with the mode its mode word records.  Nothing here is the
    /// driver's mirror; the mirror was held to these words by
    /// `check_all` before this is called.
    fn render(&self) -> String {
        let mut writer: Option<u8> = None;
        let mut readers: Vec<u8> = Vec::new();
        let mut queue: Vec<(u64, u8, HeldMode)> = Vec::new();
        for core in 0..NUM_CORES {
            match self.queued.peek_held(core) {
                Some(HeldMode::Write) => {
                    assert!(writer.is_none(), "two held words read Write");
                    writer = Some(core);
                }
                Some(HeldMode::Read) => readers.push(core),
                None => {
                    if let Some(ticket) = self.queued.peek_request(core) {
                        let mode = self
                            .queued
                            .peek_request_mode(core)
                            .expect("a live request has a mode word");
                        queue.push((ticket, core, mode));
                    }
                }
            }
        }
        queue.sort_unstable_by_key(|&(ticket, core, _)| (ticket, core));
        let w = writer.map_or_else(|| "-".to_string(), |c| c.to_string());
        let r = readers
            .iter()
            .map(u8::to_string)
            .collect::<Vec<_>>()
            .join(",");
        let q = queue
            .iter()
            .map(|&(_, c, mode)| {
                let m = if mode == HeldMode::Write { 'w' } else { 'r' };
                format!("{c}:{m}")
            })
            .collect::<Vec<_>>()
            .join(",");
        format!("W={w};R={r};Q={q}")
    }
}

/// Replay a whole trace, checking after every operation.  Returns one
/// rendered line per state: the initial one, then one after each op.
fn run_trace(ops: &[Op]) -> Result<Vec<String>, Halt> {
    let mut driver = Driver::new();
    driver.check_all()?;
    let mut lines = vec![driver.render()];
    for op in ops {
        driver.apply(*op)?;
        driver.check_all()?;
        lines.push(driver.render());
    }
    Ok(lines)
}

fn main() {
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .expect("failed to read stdin");
    let Some(ops) = parse_trace(&input) else {
        eprintln!("rw_lock_oracle: parse error");
        std::process::exit(PARSE_ERROR_STATUS);
    };
    match run_trace(&ops) {
        Ok(lines) => println!("{}", lines.join("\n")),
        Err(halt) => {
            let (label, status) = match halt {
                Halt::Divergence(_) => ("DIVERGENCE", 1),
                Halt::NotSequential(_) => ("NOT SEQUENTIALLY EXECUTABLE", 3),
            };
            eprintln!("rw_lock_oracle: {label} — {}", halt.message());
            std::process::exit(status);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every rendered line of a trace: the initial state and one per op.
    fn lines(trace: &str) -> Vec<String> {
        let ops = parse_trace(trace).expect("parse");
        run_trace(&ops).expect("no divergence")
    }

    /// The final state of a trace.
    fn render(trace: &str) -> String {
        lines(trace)
            .pop()
            .expect("the initial state is always rendered")
    }

    #[test]
    fn parse_op_acquire_read() {
        assert_eq!(parse_op("R0"), Some(Op::AcquireRead(0)));
        assert_eq!(parse_op("R3"), Some(Op::AcquireRead(3)));
    }

    #[test]
    fn parse_op_release_read() {
        assert_eq!(parse_op("r1"), Some(Op::ReleaseRead(1)));
    }

    #[test]
    fn parse_op_acquire_write() {
        assert_eq!(parse_op("W2"), Some(Op::AcquireWrite(2)));
    }

    #[test]
    fn parse_op_release_write() {
        assert_eq!(parse_op("w0"), Some(Op::ReleaseWrite(0)));
    }

    #[test]
    fn parse_op_rejects_garbage() {
        assert_eq!(parse_op(""), None);
        assert_eq!(parse_op("XYZ"), None);
        assert_eq!(parse_op("Rabc"), None);
    }

    /// The Lean oracle rejects a core id outside `numCores`; so does
    /// this one, rather than panicking inside `QueuedRwLock`'s range
    /// assert with a different exit status.
    #[test]
    fn parse_op_rejects_core_id_out_of_range() {
        assert_eq!(parse_op("R4"), None);
        assert_eq!(parse_op("w9"), None);
    }

    #[test]
    fn parse_trace_simple() {
        let trace = parse_trace("R0,R1,r0,").unwrap();
        assert_eq!(trace.len(), 3);
        assert_eq!(trace[0], Op::AcquireRead(0));
        assert_eq!(trace[1], Op::AcquireRead(1));
        assert_eq!(trace[2], Op::ReleaseRead(0));
    }

    #[test]
    fn empty_trace_yields_unheld() {
        assert_eq!(render(""), "W=-;R=;Q=");
    }

    #[test]
    fn single_reader_acquire() {
        assert_eq!(render("R0,"), "W=-;R=0;Q=");
    }

    #[test]
    fn single_writer_acquire() {
        assert_eq!(render("W0,"), "W=0;R=;Q=");
    }

    #[test]
    fn reader_blocked_by_writer_enqueues() {
        assert_eq!(render("W0,R1,"), "W=0;R=;Q=1:r");
    }

    /// A writer release promotes the queued reader — and the promotion
    /// is replayed on both real locks, so the reader count reported here
    /// came out of two live atomic words.
    #[test]
    fn release_promotes_waiter() {
        assert_eq!(render("W0,R1,w0,"), "W=-;R=1;Q=");
    }

    /// A contiguous run of queued readers is admitted together.
    #[test]
    fn writer_release_batch_promotes_readers() {
        assert_eq!(render("W0,R1,R2,R3,w0,"), "W=-;R=1,2,3;Q=");
    }

    /// A queued writer is promoted alone, and holds its ticket.
    #[test]
    fn reader_release_promotes_queued_writer() {
        assert_eq!(render("R0,W1,r0,"), "W=1;R=;Q=");
    }

    /// Strict FIFO: a reader arriving behind a queued writer waits, even
    /// though the CAS-retry lock's own `acquire_read` would admit it.
    /// The driver follows the spec, which is what makes the harness a
    /// refinement check rather than an implementation echo.
    #[test]
    fn reader_behind_queued_writer_enqueues() {
        assert_eq!(render("R0,W1,R2,"), "W=-;R=0;Q=1:w,2:r");
    }

    #[test]
    fn render_state_matches_lean_format() {
        // R0,R1,r0,W2,w2, — W2 enqueues behind reader 1; w2 is then a
        // no-op because 2 is a waiter, not the writer.
        assert_eq!(render("R0,R1,r0,W2,w2,"), "W=-;R=1;Q=2:w");
    }

    #[test]
    fn all_readers_acquire_and_release() {
        assert_eq!(render("R0,R1,R2,R3,"), "W=-;R=0,1,2,3;Q=");
        assert_eq!(render("R0,R1,R2,R3,r0,r1,r2,r3,"), "W=-;R=;Q=");
    }

    /// A queue of writers drains one at a time.
    #[test]
    fn writer_queue_drains_in_order() {
        assert_eq!(render("W0,W1,W2,W3,"), "W=0;R=;Q=1:w,2:w,3:w");
        assert_eq!(render("W0,W1,W2,W3,w0,"), "W=1;R=;Q=2:w,3:w");
        assert_eq!(render("W0,W1,W2,W3,w0,w1,w2,w3,"), "W=-;R=;Q=");
    }

    /// Double acquire by the same core is a no-op on both sides.  The
    /// holder's re-acquisition **reaches the real ticket lock** (PR #890
    /// review round 2), whose held word must make it return at once; the
    /// counts read back afterwards must not have moved.
    #[test]
    fn double_acquire_is_a_noop() {
        assert_eq!(render("R0,R0,R0,"), "W=-;R=0;Q=");
        assert_eq!(render("W0,W0,"), "W=0;R=;Q=");
        // Crossing modes: a reader asking for the write lock, and the
        // writer asking for the read lock, are holders and stand still.
        assert_eq!(render("R0,W0,"), "W=-;R=0;Q=");
        assert_eq!(render("W0,R0,"), "W=0;R=;Q=");
        // A queued waiter re-acquiring is the spec's no-op too, and is
        // issued to the ticket lock, which returns on the core's request
        // word (`a_waiter_reacquiring_is_issued_and_changes_nothing`).
        assert_eq!(render("W0,R1,R1,"), "W=0;R=;Q=1:r");
    }

    /// A queued waiter re-acquiring is the spec's no-op and **reaches the
    /// real ticket lock** (the class closure behind PR #890 review rounds
    /// 2 and 3): the fused acquisition returns on the core's request
    /// word, taking no second ticket, and the queue is unchanged in
    /// length and in order — the waiter is still admitted, once, when
    /// its turn comes.  Before the request word existed a second ticket
    /// was what this call would have taken, and the driver issued it to
    /// neither lock.
    #[test]
    fn a_waiter_reacquiring_is_issued_and_changes_nothing() {
        assert_eq!(render("W0,R1,R1,W1,"), "W=0;R=;Q=1:r");
        assert_eq!(render("W0,R1,R1,w0,"), "W=-;R=1;Q=");
        assert_eq!(render("R0,W1,W1,R1,r0,"), "W=1;R=;Q=");
    }

    /// A withdrawal by a core with no request is the spec's no-op and
    /// **reaches the real ticket lock**, which refuses it on its own
    /// record of the core's request — not on the ticket named, which is
    /// the one being served.
    #[test]
    fn cancel_by_an_uninvolved_core_is_a_noop_on_the_ticket_lock() {
        assert_eq!(render("c0,"), "W=-;R=;Q=");
        assert_eq!(render("W0,c1,"), "W=0;R=;Q=");
        assert_eq!(render("W0,R1,c1,c1,w0,"), "W=-;R=;Q=");
    }

    /// Releasing without holding is a no-op.  It **reaches the real
    /// ticket lock** (PR #890 review round 2), whose held word must make
    /// `release_read` / `release_write` return without touching a word —
    /// the identity the two-phase-locking unwind relies on — and must
    /// not reach the CAS-retry lock, whose unconditional `fetch_sub`
    /// would underflow.
    #[test]
    fn release_without_hold_is_a_noop() {
        assert_eq!(render("r0,"), "W=-;R=;Q=");
        assert_eq!(render("w0,"), "W=-;R=;Q=");
        assert_eq!(render("R0,r1,"), "W=-;R=0;Q=");
        // The writer releasing as a reader, and a reader releasing as
        // the writer: neither holds what it releases.
        assert_eq!(render("W0,r0,"), "W=0;R=;Q=");
        assert_eq!(render("R0,w0,"), "W=-;R=0;Q=");
        // A queued waiter releasing: its word reads clear, and the
        // holder ahead of it keeps the lock.
        assert_eq!(render("W0,R1,r1,"), "W=0;R=;Q=1:r");
        assert_eq!(render("R0,W1,w1,"), "W=-;R=0;Q=1:w");
    }

    /// A holder's withdrawal is the spec's no-op and now **reaches the
    /// real ticket lock** (PR #890 review round 3), whose held word must
    /// make it publish nothing: the writer keeps its turn, a reader keeps
    /// its count, and the waiter behind a withdrawing writer is admitted
    /// by the release — exactly once.  Before the word, a writer's
    /// withdrawal that reached the publish passed the turn under the set
    /// bit and the release passed it again.
    #[test]
    fn cancel_by_a_holder_is_a_noop_on_the_ticket_lock() {
        assert_eq!(render("W0,c0,"), "W=0;R=;Q=");
        assert_eq!(render("R0,c0,"), "W=-;R=0;Q=");
        assert_eq!(render("R0,R1,c1,c0,"), "W=-;R=0,1;Q=");
        // The waiter behind a withdrawing writer is admitted by the
        // release, and the turn is passed once.
        assert_eq!(render("W0,R1,c0,w0,"), "W=-;R=1;Q=");
        assert_eq!(render("W0,W1,c0,w0,"), "W=1;R=;Q=");
        assert_eq!(render("R0,W1,c0,r0,"), "W=1;R=;Q=");
    }

    /// `check_holders` reports a held word the spec does not account
    /// for, in both directions: a hold the lock records and the spec
    /// does not, and a hold the spec records and the lock has lost.
    #[test]
    fn check_holders_reports_a_planted_divergence() {
        let driver = Driver::new();
        driver.queued.acquire_read(2);
        let err = driver
            .check_holders()
            .expect_err("must report the extra hold");
        assert!(
            err.message().contains("held word of core 2"),
            "unexpected report: {}",
            err.message()
        );
        driver.queued.release_read(2);
        driver.check_holders().expect("released: consistent again");

        let mut driver = Driver::new();
        driver.readers.push((1, 0));
        let err = driver
            .check_holders()
            .expect_err("must report the lost hold");
        assert!(
            err.message().contains("held word of core 1"),
            "unexpected report: {}",
            err.message()
        );
    }

    /// An involved core whose words the lock has lost is reported, not
    /// parked: `reacquire_as_involved` reads both words before it
    /// re-acquires, so the single-threaded driver never enqueues behind
    /// a ticket nobody would serve — for a lost hold and for a lost
    /// request alike.
    #[test]
    fn reacquire_as_involved_fails_closed_on_lost_words() {
        let mut driver = Driver::new();
        driver.readers.push((0, 0));
        match driver.reacquire_as_involved(0, false) {
            Err(Halt::Divergence(why)) => {
                assert!(why.contains("both its words are clear"), "{why}")
            }
            other => panic!("expected a divergence, got {other:?}"),
        }
        let mut driver = Driver::new();
        driver.waiters.push((3, true, 0));
        match driver.reacquire_as_involved(3, true) {
            Err(Halt::Divergence(why)) => {
                assert!(why.contains("both its words are clear"), "{why}")
            }
            other => panic!("expected a divergence, got {other:?}"),
        }
    }

    /// `check_requests` reports a request word the spec does not account
    /// for, in both directions: a request the lock records and the spec
    /// does not, and a request the spec records and the lock has lost.
    #[test]
    fn check_requests_reports_a_planted_divergence() {
        let driver = Driver::new();
        let _ = driver.queued.enqueue(2, HeldMode::Read);
        let err = driver
            .check_requests()
            .expect_err("must report the extra request");
        assert!(
            err.message().contains("request word of core 2"),
            "unexpected report: {}",
            err.message()
        );

        let mut driver = Driver::new();
        driver.waiters.push((1, false, 0));
        let err = driver
            .check_requests()
            .expect_err("must report the lost request");
        assert!(
            err.message().contains("request word of core 1"),
            "unexpected report: {}",
            err.message()
        );

        // PR #890 review round 5: a request whose mode word disagrees
        // with the spec's queued mode is reported too — the word the
        // lock decides a reader's withdrawal on.
        let mut driver = Driver::new();
        driver.queued.acquire_write(0);
        driver.writer_held = Some(0);
        let ticket = driver.queued.enqueue(3, HeldMode::Write);
        driver.waiters.push((3, false, ticket));
        let err = driver
            .check_requests()
            .expect_err("must report the mode mismatch");
        assert!(
            err.message().contains("request word of core 3"),
            "unexpected report: {}",
            err.message()
        );
    }

    /// The ticket interval closes on every trace the harness generates:
    /// no operation leaves a ticket outstanding without a writer.
    #[test]
    fn ticket_interval_holds_across_a_mixed_trace() {
        // `run_trace` checks after every op; reaching the end is the
        // assertion.  Reader-batch promotion, writer promotion, no-op
        // gates and re-acquisition all appear here.
        assert_eq!(render("R0,R1,W2,r0,r1,w2,R3,W0,r3,w0,"), "W=-;R=;Q=");
    }

    /// The two deployed implementations track each other word for word
    /// across a long deterministic trace.
    #[test]
    fn implementations_agree_across_a_long_trace() {
        let mut trace = String::new();
        for n in 0..256u32 {
            let core = (n % 4) as u8;
            match n % 6 {
                0 => trace.push_str(&format!("R{core},")),
                1 => trace.push_str(&format!("W{core},")),
                2 => trace.push_str(&format!("r{core},")),
                3 => trace.push_str(&format!("w{core},")),
                4 => trace.push_str(&format!("R{},", (core + 1) % 4)),
                _ => trace.push_str(&format!("r{},", (core + 1) % 4)),
            }
        }
        let ops = parse_trace(&trace).expect("parse");
        // Any divergence between the abstract spec, the CAS-retry lock
        // and the ticket lock fails here.
        run_trace(&ops).expect("no divergence over 256 ops");
    }

    /// **WS-LC closure audit**: a core re-acquiring while its own
    /// withdrawal is unclaimed would park in `enqueue`, so the trace is
    /// refused as not sequentially executable — never replayed with a
    /// guessed linearisation, and never a hang.
    #[test]
    fn reacquire_over_a_pending_withdrawal_is_not_sequential() {
        let ops = parse_trace("W0,W1,c1,W1,").expect("parse");
        match run_trace(&ops) {
            Err(Halt::NotSequential(why)) => assert!(why.contains("would park"), "{why}"),
            other => panic!("expected NotSequential, got {other:?}"),
        }
        let ops = parse_trace("W0,R1,c1,R1,w0,").expect("parse");
        assert!(matches!(run_trace(&ops), Err(Halt::NotSequential(_))));
    }

    /// **WS-LC closure audit**: the double withdrawal — the trace on
    /// which the deployed lock lost a withdrawal and stalled — cannot be
    /// replayed at all now, because its second acquisition is the parked
    /// one; and once the release has retired the first withdrawal, the
    /// same core withdraws again without incident.
    #[test]
    fn double_withdrawal_is_excluded_and_the_retired_form_replays() {
        let ops = parse_trace("W0,W1,c1,W1,c1,w0,").expect("parse");
        assert!(matches!(run_trace(&ops), Err(Halt::NotSequential(_))));
        // Retired by the release, core 1 acquires the free lock directly and
        // its second withdrawal is a holder's no-op.
        assert_eq!(render("W0,W1,c1,w0,W1,c1,"), "W=1;R=;Q=");
        // Retired by the release, queued again behind a new holder, and
        // withdrawn again — the second withdrawal is retired by that
        // holder's release.
        assert_eq!(render("W0,W1,c1,w0,W2,W1,c1,w2,"), "W=-;R=;Q=");
    }

    /// **WS-LC closure audit**: a withdrawn ticket left at the head —
    /// the stalled lock's signature — is reported.  Constructed by hand:
    /// the spec records a pending withdrawal of the served ticket.
    #[test]
    fn check_head_live_reports_a_planted_stall() {
        let mut driver = Driver::new();
        let ticket = driver.queued.enqueue(1, HeldMode::Write);
        driver.tombstones.push((1, ticket));
        let err = driver.check_head_live().expect_err("must report");
        assert!(
            err.message().contains("the lock is stalled"),
            "unexpected report: {}",
            err.message()
        );
    }

    /// **WS-LC closure audit**: a pending withdrawal whose slot is empty
    /// (a lost publication) and a published slot the spec has no
    /// withdrawal for (a stale publication) are both reported.
    #[test]
    fn check_withdrawal_slots_reports_lost_and_stale_publications() {
        let mut driver = Driver::new();
        driver.queued.acquire_write(0);
        let ticket = driver.queued.enqueue(1, HeldMode::Read);
        driver.tombstones.push((1, ticket));
        let err = driver.check_withdrawal_slots().expect_err("lost");
        assert!(err.message().contains("holds None"), "{}", err.message());

        driver.tombstones.clear();
        assert_eq!(driver.queued.cancel(1, ticket), CancelOutcome::Withdrawn);
        let err = driver.check_withdrawal_slots().expect_err("stale");
        assert!(err.message().contains("holds Some"), "{}", err.message());
    }

    /// The driver reports a divergence rather than papering over it.
    /// Constructed by hand: a state the spec says is writer-held, with
    /// the real lock left unheld underneath it.
    #[test]
    fn check_encoding_reports_a_planted_divergence() {
        let mut driver = Driver::new();
        driver.writer_held = Some(0);
        let err = driver.check_encoding().expect_err("must report");
        assert!(
            err.message().contains("does not encode the spec state"),
            "unexpected report: {}",
            err.message()
        );
    }

    /// Same for the ticket interval: a writer the spec believes holds,
    /// with no ticket outstanding on the real ticket lock.
    #[test]
    fn check_ticket_interval_reports_a_planted_divergence() {
        let mut driver = Driver::new();
        driver.writer_held = Some(1);
        let err = driver.check_ticket_interval().expect_err("must report");
        assert!(
            err.message().contains("ticket interval is 0"),
            "unexpected report: {}",
            err.message()
        );
    }

    /// And for the implementation cross-check: move one lock and not
    /// the other.
    #[test]
    fn check_implementations_agree_reports_a_planted_divergence() {
        let driver = Driver::new();
        assert!(driver.cas.try_acquire_read());
        let err = driver
            .check_implementations_agree()
            .expect_err("must report");
        assert!(
            err.message().contains("deployed implementations disagree"),
            "unexpected report: {}",
            err.message()
        );
        driver.cas.release_read();
    }

    // ------------------------------------------------------------------
    // PR #890 review round 5 — the identity line, and the promoting
    // withdrawal
    // ------------------------------------------------------------------

    /// Every step is rendered, from the initial state on, and each line
    /// names the cores: a promotion that admitted the wrong waiter, or
    /// the right one in the wrong order, would differ here where the
    /// old count form agreed.
    #[test]
    fn every_step_is_rendered_with_identities() {
        assert_eq!(
            lines("W0,R1,R2,w0,"),
            [
                "W=-;R=;Q=",
                "W=0;R=;Q=",
                "W=0;R=;Q=1:r",
                "W=0;R=;Q=1:r,2:r",
                "W=-;R=1,2;Q=",
            ]
        );
        // The reader set is sorted whatever order the cores entered in.
        assert_eq!(render("R3,R1,R2,"), "W=-;R=1,2,3;Q=");
        // The queue is in ticket order with each request's mode.
        assert_eq!(render("R0,W3,R1,W2,"), "W=-;R=0;Q=3:w,1:r,2:w");
    }

    /// A mid-trace divergence that later converges is caught: the line
    /// after the divergent step differs even though the final lines
    /// agree.  Constructed by comparing the rendered vector against the
    /// one the spec produces, which is what the harness does line by
    /// line.
    #[test]
    fn a_transient_divergence_is_visible_in_the_lines() {
        let rendered = lines("W0,R1,w0,r1,");
        let spec = [
            "W=-;R=;Q=",
            "W=0;R=;Q=",
            "W=0;R=;Q=1:r",
            "W=-;R=1;Q=",
            "W=-;R=;Q=",
        ];
        assert_eq!(rendered, spec);
        // The same trace with the reader as core 2 shares the first two
        // lines and the last, and differs in between — a comparison of
        // final states alone would have passed it.
        let other = lines("W0,R2,w0,r2,");
        assert_eq!(other.first(), rendered.first());
        assert_eq!(other.last(), rendered.last());
        assert_ne!(other, rendered);
    }

    /// The spec's withdrawal promotes the reader run a withdrawn head
    /// uncovers (`applyOp_cancel_of_promotes`): the served writer behind
    /// a reader withdraws, and the readers queued behind it enter while
    /// the reader holds.  On the ticket lock the withdrawal passes the
    /// turn and the driver admits the run in ticket order; the rendered
    /// lines show the run entering at the withdrawal, not at a release.
    #[test]
    fn cancel_of_the_head_promotes_the_reader_run_behind_it() {
        assert_eq!(
            lines("R0,W1,R2,R3,c1,"),
            [
                "W=-;R=;Q=",
                "W=-;R=0;Q=",
                "W=-;R=0;Q=1:w",
                "W=-;R=0;Q=1:w,2:r",
                "W=-;R=0;Q=1:w,2:r,3:r",
                "W=-;R=0,2,3;Q=",
            ]
        );
        // The run stops at the next writer, which keeps waiting for the
        // readers to drain.
        assert_eq!(render("R0,W1,R2,W3,R0,c1,"), "W=-;R=0,2;Q=3:w");
        assert_eq!(render("R0,W1,R2,W3,c1,r0,r2,"), "W=3;R=;Q=");
    }

    /// A withdrawal that is not the head's promotes nobody — the head
    /// was promotable already or is not — and one behind a holding
    /// writer promotes nobody either (`rwLock_cancel_nonhead_admits_no_one`).
    #[test]
    fn cancel_off_the_head_promotes_nobody() {
        // Behind a holding writer: the reader now at the head waits for
        // the release.
        assert_eq!(render("W0,W1,R2,c1,"), "W=0;R=;Q=2:r");
        assert_eq!(render("W0,W1,R2,c1,w0,"), "W=-;R=2;Q=");
        // Behind a queued writer head under readers: the writer stays
        // the head, and the readers behind it stay queued.
        assert_eq!(render("R0,W1,W2,R3,c2,"), "W=-;R=0;Q=1:w,3:r");
        // A withdrawn reader from the middle of a run behind a writer.
        assert_eq!(render("W0,R1,R2,R3,c2,"), "W=0;R=;Q=1:r,3:r");
        assert_eq!(render("W0,R1,R2,R3,c2,w0,"), "W=-;R=1,3;Q=");
    }

    /// The withdrawal's verdict is held to the spec's: a mirror that
    /// records a waiter the lock has already admitted — here, a reader
    /// the spec would have promoted — is reported as a divergence on the
    /// outcome, before the words are compared.
    #[test]
    fn cancel_outcome_reports_a_planted_divergence() {
        let mut driver = Driver::new();
        // The lock: core 1's read request is served on a calm lock, so
        // the spec's promotion has admitted it; the mirror is made to
        // believe it is still queued.
        let ticket = driver.queued.enqueue(1, HeldMode::Read);
        driver.waiters.push((1, false, ticket));
        match driver.apply(Op::Cancel(1)) {
            Err(Halt::Divergence(why)) => {
                assert!(why.contains("reported Holding"), "{why}");
                assert!(why.contains("a queued waiter"), "{why}");
            }
            other => panic!("expected a divergence on the outcome, got {other:?}"),
        }
    }

    /// The parse-error exit status is the Lean oracle's too (`2`), so the
    /// harness can tell a parse failure from a divergence on either side.
    #[test]
    fn parse_error_status_is_pinned() {
        assert_eq!(PARSE_ERROR_STATUS, 2);
    }
}
