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
//! prints the canonical serialised post-state on stdout.
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
//! | `writerHeld.isSome` | bit 63 of `state` | bit 63 of `state` | **read from both locks** |
//! | `readers.length` | bits 0..62 of `state` | bits 0..62 of `state` | **read from both locks** |
//! | `waiters` | not represented | ticket interval, mode is core-local | driver bookkeeping |
//!
//! So `W=` and `R=` are read back out of the real atomic words after
//! every operation and cross-checked between the two implementations;
//! a disagreement fails the run.  `Q=` is the driver's own queue.
//!
//! The queue has to be the driver's, in both cases and for different
//! reasons.  The CAS-retry lock has no queue at all — that is the
//! documented non-representation in `rwLockSim`.  The ticket lock does
//! have one, and since WS-LC LC3.6 every queued waiter holds a *real*
//! ticket of it; but a waiter occupies the queue by *spinning in
//! `await_turn`*, which a single-threaded driver cannot do, and the
//! access **mode** of a queued waiter is core-local in the real
//! protocol and appears in no shared word.  So the driver keeps the
//! queue and checks, after every operation, everything the ticket lock
//! does expose: the ticket interval is exactly the held writer plus the
//! queued waiters plus the withdrawals nobody has skipped yet
//! (`check_ticket_interval`); the ticket being served is never one of
//! those withdrawals (`check_head_live` — `queuedSim`'s
//! `queuedHeadLive`, and the check that sees a stalled lock); and each
//! core's withdrawal slot holds exactly the withdrawal the spec says is
//! pending for it (`check_withdrawal_slots`).  Those are the state-level
//! half of the `queuedSim` relation proved in
//! `SeLe4n/Kernel/Concurrency/Locks/QueuedRwLockRefinement.lean`; the
//! waiters-to-interval half is the part the proof carries and the
//! single-threaded harness cannot.
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
//! of readers or a single writer, the driver replays exactly those
//! cores against the real ticket lock, in exactly that order, and every
//! one of those attempts must succeed.  A ticket lock that admitted a
//! different core, or refused one the spec admits, fails the run.
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
//! `W=<flag>;R=<count>;Q=<n>` — matches the Lean oracle
//! (`tests/Tier5/RwLockOracle.lean`).

use std::io::Read;

use sele4n_hal::queued_rw_lock::QueuedRwLock;
use sele4n_hal::rw_lock::{RwLock, READER_MASK, WRITER_BIT};

/// Cores the wire format may name.  Matches the Lean oracle's
/// `numCores` gate and `QueuedRwLock::MAX_WAITERS`.
const NUM_CORES: u8 = 4;

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
    /// Reader cores currently holding, per the abstract spec.  Same
    /// role: identity is abstract, the *count* reported is concrete.
    readers: Vec<u8>,
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
        self.readers.contains(&c)
            || self.writer_held == Some(c)
            || self.waiters.iter().any(|w| w.0 == c)
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
        self.readers.insert(0, c);
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

    /// Release `c`'s read lock on both real locks.
    fn release_reader(&mut self, c: u8) {
        self.readers.retain(|x| *x != c);
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
                    return Ok(()); // no-op gate
                }
                self.refuse_parked_issue(c)?;
                // Every acquisition takes a real ticket, whether it is
                // admitted at once or queued — that is what makes a
                // queued waiter concrete (WS-LC LC3.6).
                let ticket = self.queued.enqueue(c);
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
                if !self.readers.contains(&c) {
                    return Ok(()); // no-op gate
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
                    return Ok(());
                }
                self.refuse_parked_issue(c)?;
                let ticket = self.queued.enqueue(c);
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
                    return Ok(());
                }
                self.release_writer(c);
                // `promoteWaitersOnWriterRelease`.
                self.promote_head()
            }
            Op::Cancel(c) => {
                // `applyOp .cancel`: drop `c`'s queued request, and
                // nothing else.  A core that is holding, or that has no
                // request, is untouched on both sides.
                let Some(i) = self.waiters.iter().position(|w| w.0 == c) else {
                    return Ok(());
                };
                let (_, _, ticket) = self.waiters.remove(i);
                self.queued.cancel(c, ticket);
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
                Ok(())
            }
        }
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
            Some((_, false, _)) => {
                let mut batch = Vec::new();
                while let Some((c, false, ticket)) = self.waiters.first().copied() {
                    batch.push((c, ticket));
                    self.waiters.remove(0);
                }
                // Admit in queue order: the spec's batch order is the
                // ticket lock's ticket order.
                for (c, ticket) in batch {
                    self.admit_reader(c, ticket)?;
                    // Each admission passes its own ticket on, which can
                    // uncover a tombstone the skip loop then retires.
                    self.retire_passed_tombstones();
                }
                Ok(())
            }
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

    /// Every invariant checked after each operation.
    fn check_all(&self) -> Result<(), Halt> {
        self.check_implementations_agree()?;
        self.check_ticket_interval()?;
        self.check_head_live()?;
        self.check_withdrawal_slots()?;
        self.check_encoding()
    }

    /// Render the post-state.  `W=` and `R=` are read out of the real
    /// locks; `Q=` is the driver's queue.
    fn render(&self) -> String {
        let packed = self.packed_cas();
        let flag = u8::from((packed & WRITER_BIT) != 0);
        let count = packed & READER_MASK;
        format!("W={};R={};Q={}", flag, count, self.waiters.len())
    }
}

/// Replay a whole trace, checking after every operation.
fn run_trace(ops: &[Op]) -> Result<String, Halt> {
    let mut driver = Driver::new();
    driver.check_all()?;
    for op in ops {
        driver.apply(*op)?;
        driver.check_all()?;
    }
    Ok(driver.render())
}

fn main() {
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .expect("failed to read stdin");
    let Some(ops) = parse_trace(&input) else {
        eprintln!("rw_lock_oracle: parse error");
        std::process::exit(2);
    };
    match run_trace(&ops) {
        Ok(rendered) => println!("{rendered}"),
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

    fn render(trace: &str) -> String {
        let ops = parse_trace(trace).expect("parse");
        run_trace(&ops).expect("no divergence")
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
        assert_eq!(render(""), "W=0;R=0;Q=0");
    }

    #[test]
    fn single_reader_acquire() {
        assert_eq!(render("R0,"), "W=0;R=1;Q=0");
    }

    #[test]
    fn single_writer_acquire() {
        assert_eq!(render("W0,"), "W=1;R=0;Q=0");
    }

    #[test]
    fn reader_blocked_by_writer_enqueues() {
        assert_eq!(render("W0,R1,"), "W=1;R=0;Q=1");
    }

    /// A writer release promotes the queued reader — and the promotion
    /// is replayed on both real locks, so the reader count reported here
    /// came out of two live atomic words.
    #[test]
    fn release_promotes_waiter() {
        assert_eq!(render("W0,R1,w0,"), "W=0;R=1;Q=0");
    }

    /// A contiguous run of queued readers is admitted together.
    #[test]
    fn writer_release_batch_promotes_readers() {
        assert_eq!(render("W0,R1,R2,R3,w0,"), "W=0;R=3;Q=0");
    }

    /// A queued writer is promoted alone, and holds its ticket.
    #[test]
    fn reader_release_promotes_queued_writer() {
        assert_eq!(render("R0,W1,r0,"), "W=1;R=0;Q=0");
    }

    /// Strict FIFO: a reader arriving behind a queued writer waits, even
    /// though the CAS-retry lock's own `acquire_read` would admit it.
    /// The driver follows the spec, which is what makes the harness a
    /// refinement check rather than an implementation echo.
    #[test]
    fn reader_behind_queued_writer_enqueues() {
        assert_eq!(render("R0,W1,R2,"), "W=0;R=1;Q=2");
    }

    #[test]
    fn render_state_matches_lean_format() {
        // R0,R1,r0,W2,w2, — W2 enqueues behind reader 1; w2 is then a
        // no-op because 2 is a waiter, not the writer.
        assert_eq!(render("R0,R1,r0,W2,w2,"), "W=0;R=1;Q=1");
    }

    #[test]
    fn all_readers_acquire_and_release() {
        assert_eq!(render("R0,R1,R2,R3,"), "W=0;R=4;Q=0");
        assert_eq!(render("R0,R1,R2,R3,r0,r1,r2,r3,"), "W=0;R=0;Q=0");
    }

    /// A queue of writers drains one at a time.
    #[test]
    fn writer_queue_drains_in_order() {
        assert_eq!(render("W0,W1,W2,W3,"), "W=1;R=0;Q=3");
        assert_eq!(render("W0,W1,W2,W3,w0,"), "W=1;R=0;Q=2");
        assert_eq!(render("W0,W1,W2,W3,w0,w1,w2,w3,"), "W=0;R=0;Q=0");
    }

    /// Double acquire by the same core is a no-op on both sides, so the
    /// real locks' counts must not move either.
    #[test]
    fn double_acquire_is_a_noop() {
        assert_eq!(render("R0,R0,R0,"), "W=0;R=1;Q=0");
        assert_eq!(render("W0,W0,"), "W=1;R=0;Q=0");
    }

    /// Releasing without holding is a no-op — and must not reach the
    /// real `release_read`, whose `debug_assert` would trip on the
    /// underflow.
    #[test]
    fn release_without_hold_is_a_noop() {
        assert_eq!(render("r0,"), "W=0;R=0;Q=0");
        assert_eq!(render("w0,"), "W=0;R=0;Q=0");
        assert_eq!(render("R0,r1,"), "W=0;R=1;Q=0");
    }

    /// The ticket interval closes on every trace the harness generates:
    /// no operation leaves a ticket outstanding without a writer.
    #[test]
    fn ticket_interval_holds_across_a_mixed_trace() {
        // `run_trace` checks after every op; reaching the end is the
        // assertion.  Reader-batch promotion, writer promotion, no-op
        // gates and re-acquisition all appear here.
        assert_eq!(render("R0,R1,W2,r0,r1,w2,R3,W0,r3,w0,"), "W=0;R=0;Q=0");
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
        assert_eq!(render("W0,W1,c1,w0,W1,c1,"), "W=1;R=0;Q=0");
        // Retired by the release, queued again behind a new holder, and
        // withdrawn again — the second withdrawal is retired by that
        // holder's release.
        assert_eq!(render("W0,W1,c1,w0,W2,W1,c1,w2,"), "W=0;R=0;Q=0");
    }

    /// **WS-LC closure audit**: a withdrawn ticket left at the head —
    /// the stalled lock's signature — is reported.  Constructed by hand:
    /// the spec records a pending withdrawal of the served ticket.
    #[test]
    fn check_head_live_reports_a_planted_stall() {
        let mut driver = Driver::new();
        let ticket = driver.queued.enqueue(1);
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
        let ticket = driver.queued.enqueue(1);
        driver.tombstones.push((1, ticket));
        let err = driver.check_withdrawal_slots().expect_err("lost");
        assert!(err.message().contains("holds None"), "{}", err.message());

        driver.tombstones.clear();
        driver.queued.cancel(1, ticket);
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
}
