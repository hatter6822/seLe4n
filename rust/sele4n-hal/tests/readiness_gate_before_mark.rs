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
//! What is pinned:
//!
//! * the cross-core suspend seam refuses with `KernelError::IllegalState`
//!   rather than entering a runtime this PE has not initialized, and refuses
//!   *without* dispatching (the stand-in returns `NotImplemented = 17`, so the
//!   two outcomes are distinguishable); and
//! * the SVC seam halts, which on the host lane is a panic — caught here rather
//!   than aborting the run.
//!
//! The SVC seam's prefilter rejections are *not* affected: they precede the
//! gate, so an invalid syscall id is still refused as an invalid syscall id on
//! a not-ready core, which the third case checks.

use sele4n_hal::ffi::{sele4n_suspend_thread, SUSPEND_BEFORE_LEAN_READY_STATUS};
use sele4n_hal::svc_dispatch::{dispatch_svc, DispatchError, SyscallArgs, SyscallId};

/// The zero-argument frame the seam tests dispatch with.
fn zero_args() -> SyscallArgs {
    SyscallArgs {
        msg_info: 0,
        msg_regs: [0; 6],
        ipc_buffer_addr: None,
        elr: 0,
        spsr: 0,
        sp_el0: 0,
        x30: 0,
    }
}

#[test]
fn suspend_seam_refuses_before_any_core_is_ready() {
    let status = sele4n_suspend_thread(42);
    assert_eq!(
        status, SUSPEND_BEFORE_LEAN_READY_STATUS,
        "a suspend on a core whose Lean runtime is not initialized must be \
         refused with IllegalState"
    );
    assert_ne!(
        status, 17,
        "the refusal must happen INSTEAD of the dispatch, not after it \
         (17 is the stand-in's own NotImplemented)"
    );
    assert_ne!(status, 0, "the refusal must not decode as success");
}

#[test]
fn svc_seam_halts_before_any_core_is_ready() {
    // `cpu::fatal_halt` panics on the host lane; catch it so this assertion is
    // an observation rather than an abort.  `catch_unwind` is sound here: the
    // seam commits nothing before the gate, so no state is left torn.
    let outcome = std::panic::catch_unwind(|| {
        let args = zero_args();
        dispatch_svc(SyscallId::Send.to_u32(), &args)
    });
    assert!(
        outcome.is_err(),
        "an SVC on a core whose Lean runtime is not initialized must halt the \
         core, not return a frame the thread resumes on"
    );
}

#[test]
fn svc_prefilter_still_rejects_before_the_gate() {
    // The prefilter runs before the readiness gate, so a rejected id is
    // reported as such rather than halting — the gate did not swallow the
    // seam's own argument validation.
    let args = zero_args();
    let outcome = std::panic::catch_unwind(|| dispatch_svc(SyscallId::COUNT, &args));
    assert_eq!(
        outcome.ok(),
        Some(Err(DispatchError::InvalidSyscallId)),
        "an out-of-range syscall id must be refused by the prefilter, before \
         the readiness gate is consulted"
    );
}
