// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-RR RR5.6 / RR5.7** — the kernel-entry seams *before* any core is
//! marked ready.
//!
//! The readiness mask is process-global and monotone: `mark_lean_ready` only
//! sets bits and nothing clears one.  A unit test inside `sele4n-hal`'s
//! `#[cfg(test)]` modules therefore cannot observe the not-ready side of a seam
//! whose ready side another test in the same binary exercises — whichever runs
//! second sees a mask the first one moved.
//!
//! An integration test is a separate binary, so this process starts with the
//! mask at its boot value (`0`, no core ready) and nothing here ever marks a
//! core.  That makes the refusal arms observable end to end rather than only at
//! the helper that implements them.
//!
//! What is pinned: the SVC seam halts, which on the host lane is a panic —
//! caught here rather than aborting the run.  (The raw cross-core suspend seam
//! this binary also pinned was retired at WS-ZA ZA6.10.)
//!
//! **PR #889 review**: the gate precedes the SVC seam's prefilter, not the
//! other way round.  The halt exists because a thread on a not-ready core is
//! never preempted again, so *any* frame returned to it is the CPU forever —
//! an `invalidSyscallNumber` frame from the prefilter as much as a dispatched
//! one.  The second case pins that an out-of-range id halts on a not-ready
//! core rather than being refused as a frame.

use sele4n_hal::svc_dispatch::{dispatch_svc, SyscallId};

#[test]
fn svc_seam_halts_before_any_core_is_ready() {
    // `cpu::fatal_halt` panics on the host lane; catch it so this assertion is
    // an observation rather than an abort.  `catch_unwind` is sound here: the
    // seam commits nothing before the gate, so no state is left torn.
    let outcome = std::panic::catch_unwind(|| dispatch_svc(SyscallId::Send.to_u32()));
    assert!(
        outcome.is_err(),
        "an SVC on a core whose Lean runtime is not initialized must halt the \
         core, not return a frame the thread resumes on"
    );
}

#[test]
fn svc_out_of_range_id_halts_before_the_prefilter() {
    // PR #889 review: the readiness gate is consulted before the id prefilter,
    // so an out-of-range id on a not-ready core halts rather than being handed
    // back as an `InvalidSyscallId` the thread would resume on.
    let outcome = std::panic::catch_unwind(|| dispatch_svc(SyscallId::ENCODING_BOUND));
    assert!(
        outcome.is_err(),
        "an out-of-range syscall id on a not-ready core must halt, not be refused \
         by the prefilter — a refusal is a frame the thread resumes on"
    );
}

// The whole SVC arm — the trap-level gate ahead of the full-width narrowing of
// `x7`, so an oversized syscall word halts on a not-ready core rather than
// being delivered as an unknown-syscall frame — cannot be observed here:
// `handle_synchronous_exception` is `extern "C"`, and the host lane's halt is
// a panic that cannot unwind through it (the process aborts instead).  That
// ordering is pinned structurally by `build.rs::svc_arm_readiness_gate_status`.
