// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-SM SM2.C-defer D-6**: Rust-side RwLock oracle binary for the
//! Tier-5 cross-language correspondence harness.
//!
//! See `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` §5.6.
//!
//! ## Operation
//!
//! Reads an op-sequence on stdin (textual wire format), executes the
//! ops against a software model that mirrors the bit-packed state
//! evolution of the actual `RwLock`, prints the canonical serialised
//! post-state on stdout.
//!
//! ## Why a software model, not the real RwLock?
//!
//! The actual `sele4n_hal::rw_lock::RwLock` is built for multi-core SMP
//! use; its `acquire_read` / `acquire_write` BLOCK under contention via
//! WFE waits.  Driving a single-threaded sequence containing
//! "contended" ops (e.g., acquire-read while a writer holds) would
//! deadlock the test runner.
//!
//! The software model here mirrors the SAME bit-packed state transitions
//! that the real `RwLock` would perform if every op succeeded on first
//! try.  This validates the wire-format level correspondence: both the
//! Lean oracle (which folds `applyOp` over the abstract spec) and this
//! Rust oracle (which folds the bit-packed state transitions) produce
//! the same `(W=, R=)` tuple for any valid input sequence.
//!
//! The full bisimulation theorem (D-4 in `RwLockRefinement.lean`)
//! proves this correspondence formally.  The Tier-5 oracle harness
//! provides an EMPIRICAL cross-check that catches integration-level
//! regressions that the formal proof might not surface (e.g., a Lean
//! refactor that changes the abstract semantics in a way the Rust impl
//! does not mirror).
//!
//! ## Wire format
//!
//! `R<core>` = tryAcquireRead, `r<core>` = releaseRead,
//! `W<core>` = tryAcquireWrite, `w<core>` = releaseWrite.
//! Each op is terminated by a comma `,`.
//!
//! ## Output format
//!
//! `W=<flag>;R=<count>;Q=<n>` — matches the Lean oracle.

use std::io::Read;

const WRITER_BIT: u64 = 1u64 << 63;

/// The Rust mirror of the abstract `RwLockOp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Op {
    AcquireRead(u8),
    ReleaseRead(u8),
    AcquireWrite(u8),
    ReleaseWrite(u8),
}

/// Parse one token (no comma).  Returns `None` on parse error.
fn parse_op(tok: &str) -> Option<Op> {
    let tok = tok.trim();
    if tok.is_empty() {
        return None;
    }
    let head = tok.chars().next()?;
    let rest = &tok[head.len_utf8()..];
    let core: u8 = rest.parse().ok()?;
    match head {
        'R' => Some(Op::AcquireRead(core)),
        'r' => Some(Op::ReleaseRead(core)),
        'W' => Some(Op::AcquireWrite(core)),
        'w' => Some(Op::ReleaseWrite(core)),
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

/// Abstract state mirror.  Tracks the per-core membership in readers
/// and the queue, so the post-state can be rendered to match the Lean
/// oracle's output.
#[derive(Debug, Clone, Default)]
struct AbstractState {
    /// Writer-held flag (mirror of bit 63 of RwLock::state).
    writer_held: Option<u8>,
    /// Reader cores currently holding the read lock.
    readers: Vec<u8>,
    /// Waiters in FIFO order: (core, mode_is_write).
    waiters: Vec<(u8, bool)>,
}

impl AbstractState {
    /// Predicate: `c` is already "involved" (holder or waiter).
    fn core_involved(&self, c: u8) -> bool {
        self.readers.contains(&c)
            || self.writer_held == Some(c)
            || self.waiters.iter().any(|w| w.0 == c)
    }

    /// Apply one operation, mirroring the Lean `applyOp` semantics.
    fn apply(&mut self, op: Op) {
        match op {
            Op::AcquireRead(c) => {
                if self.core_involved(c) {
                    return; // no-op
                }
                if self.writer_held.is_some() {
                    // Writer holds → enqueue.
                    self.waiters.push((c, false));
                } else {
                    // No writer; check head of queue.
                    match self.waiters.first() {
                        Some((_, true)) => {
                            // Head waiter is writer → enqueue (FIFO).
                            self.waiters.push((c, false));
                        }
                        _ => {
                            // Either empty or reader head → acquire.
                            self.readers.insert(0, c);
                        }
                    }
                }
            }
            Op::ReleaseRead(c) => {
                if !self.readers.contains(&c) {
                    return; // no-op
                }
                self.readers.retain(|x| *x != c);
                // If readers list is now empty AND no writer, promote
                // the head of the queue.
                if self.readers.is_empty() && self.writer_held.is_none() {
                    self.promote_head();
                }
            }
            Op::AcquireWrite(c) => {
                if self.core_involved(c) {
                    return;
                }
                if self.writer_held.is_some() || !self.readers.is_empty() {
                    self.waiters.push((c, true));
                } else {
                    self.writer_held = Some(c);
                }
            }
            Op::ReleaseWrite(c) => {
                if self.writer_held != Some(c) {
                    return;
                }
                self.writer_held = None;
                self.promote_head();
            }
        }
    }

    /// Promote the head of the queue.  If head is a writer, single-promote.
    /// If head is a reader, batch-promote all contiguous readers.
    fn promote_head(&mut self) {
        match self.waiters.first().copied() {
            None => {}
            Some((c, true)) => {
                // Writer head → single-promote.
                self.writer_held = Some(c);
                self.waiters.remove(0);
            }
            Some((_, false)) => {
                // Reader head → batch-promote contiguous readers.
                let mut readers_to_admit = Vec::new();
                while let Some((c, false)) = self.waiters.first().copied() {
                    readers_to_admit.push(c);
                    self.waiters.remove(0);
                }
                // Prepend admitted readers to the readers list.
                let mut new_readers = readers_to_admit;
                new_readers.append(&mut self.readers);
                self.readers = new_readers;
            }
        }
    }

    /// Render to the canonical textual form.
    fn render(&self) -> String {
        let flag = if self.writer_held.is_some() { 1 } else { 0 };
        let count = self.readers.len();
        let waiters = self.waiters.len();
        format!("W={};R={};Q={}", flag, count, waiters)
    }

    /// Compute the bit-packed `u64` state (for cross-checking with the
    /// real `RwLock::peek_state()` output if needed).
    #[allow(dead_code)]
    fn to_packed(&self) -> u64 {
        let writer_bit = if self.writer_held.is_some() { WRITER_BIT } else { 0 };
        let reader_count = self.readers.len() as u64;
        writer_bit | reader_count
    }
}

fn main() {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input)
        .expect("failed to read stdin");
    let ops = parse_trace(&input).expect("parse error");
    let mut state = AbstractState::default();
    for op in ops {
        state.apply(op);
    }
    println!("{}", state.render());
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let state = AbstractState::default();
        assert_eq!(state.render(), "W=0;R=0;Q=0");
    }

    #[test]
    fn single_reader_acquire() {
        let mut state = AbstractState::default();
        state.apply(Op::AcquireRead(0));
        assert_eq!(state.render(), "W=0;R=1;Q=0");
    }

    #[test]
    fn single_writer_acquire() {
        let mut state = AbstractState::default();
        state.apply(Op::AcquireWrite(0));
        assert_eq!(state.render(), "W=1;R=0;Q=0");
    }

    #[test]
    fn reader_blocked_by_writer_enqueues() {
        let mut state = AbstractState::default();
        state.apply(Op::AcquireWrite(0));
        state.apply(Op::AcquireRead(1));
        assert_eq!(state.render(), "W=1;R=0;Q=1");
    }

    #[test]
    fn release_promotes_waiter() {
        let mut state = AbstractState::default();
        state.apply(Op::AcquireWrite(0));
        state.apply(Op::AcquireRead(1));
        state.apply(Op::ReleaseWrite(0));
        // After release, reader 1 is promoted.
        assert_eq!(state.render(), "W=0;R=1;Q=0");
    }

    #[test]
    fn render_state_matches_lean_format() {
        let mut state = AbstractState::default();
        // R0,R1,r0,W2,w2,
        state.apply(Op::AcquireRead(0));
        state.apply(Op::AcquireRead(1));
        state.apply(Op::ReleaseRead(0));
        state.apply(Op::AcquireWrite(2));
        state.apply(Op::ReleaseWrite(2));
        // After: writer=none, readers=[1], waiters=[].
        // But wait — when writer 2 tried to acquire while reader 1 was
        // holding, it ENQUEUED.  Then ReleaseWrite(2) is a no-op (writer
        // isn't 2; 2 is in waiters).  So state: R=1, Q=1.
        //
        // Match the Lean trace: W=0;R=1;Q=1.
        assert_eq!(state.render(), "W=0;R=1;Q=1");
    }

    #[test]
    fn to_packed_writer_only() {
        let mut state = AbstractState::default();
        state.apply(Op::AcquireWrite(0));
        assert_eq!(state.to_packed(), WRITER_BIT);
    }

    #[test]
    fn to_packed_readers_only() {
        let mut state = AbstractState::default();
        state.apply(Op::AcquireRead(0));
        state.apply(Op::AcquireRead(1));
        assert_eq!(state.to_packed(), 2);
    }
}
