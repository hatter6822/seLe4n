// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-RR RR5.6 / RR5.7** — the kernel-entry seams *after* the executing core
//! is marked ready.
//!
//! The companion of `readiness_gate_before_mark.rs`, which pins the refusal
//! arms.  Together the two binaries cover both sides of the gate on the host
//! lane, where the gate is genuinely compiled and executed rather than cfg'd
//! out — so the control flow these tests exercise is the control flow hardware
//! takes.
//!
//! **Why a separate binary at all.**  The readiness mask is process-global and
//! one-way: `mark_lean_ready` sets a bit and nothing clears it.  Inside
//! `sele4n-hal`'s own `#[cfg(test)]` modules core `0`'s bit is already owned by
//! `timer::tests::per_core_timer_tick_isr_never_advances_global_tick_count`,
//! which asserts the bit is *unset* when it starts; and on the host lane every
//! seam reads a constant core id of `0`, so there is no second core to borrow.
//! These tests therefore live where marking core `0` disturbs nobody.

use sele4n_hal::svc_dispatch::{
    dispatch_svc, error_frame_regs, DispatchError, SvcOutcome, SyscallArgs, SyscallId,
    ERROR_LABEL_BASE,
};
use sele4n_hal::trap::{handle_synchronous_exception, TrapFrame};

/// `ESR_EL1.EC` for an AArch64 `SVC` (the trap module's `ec::SVC_AARCH64`,
/// which is private to it).
const EC_SVC_AARCH64: u64 = 0x15;

/// Mark the executing (host) core ready.  Idempotent and monotone, so the
/// tests below may run in any order and in parallel.
fn mark_this_core_ready() {
    let core = sele4n_hal::per_cpu::current_core_id_from_tpidr() as usize;
    // SAFETY: host-side test — `hw_target` is off, so no seam is compiled to
    // call a Lean-emitted symbol and the readiness promise is vacuous (see
    // `lean_ready::mark_lean_ready`'s safety contract).
    unsafe { sele4n_hal::lean_ready::mark_lean_ready(core) };
}

fn zero_frame() -> TrapFrame {
    TrapFrame {
        gprs: [0; 31],
        sp_el0: 0,
        elr_el1: 0,
        spsr_el1: 0,
        esr_el1: 0,
        far_el1: 0,
    }
}

/// Moved from `svc_dispatch`'s unit tests at RR5.6 (see this file's header).
#[test]
fn dispatch_svc_routes_to_inner_dispatcher() {
    mark_this_core_ready();
    // Send takes 0 inline args so any frame is accepted; the inner
    // stand-in publishes the label-encoded `NotImplemented` (discriminant
    // 17 -> label 18) error frame into core 0's mailbox slot and
    // returns outcome tag 0.  WS-RA: a kernel rejection arrives as an
    // ordinary FRAME whose x1 label carries the error, undecoded here.
    let frame = zero_frame();
    let args = SyscallArgs::from_trap_frame(&frame);
    let result = dispatch_svc(SyscallId::Send.to_u32(), &args);
    assert_eq!(result, Ok(SvcOutcome::Frame(error_frame_regs(17))));
    // The frame's x1 word is the status label in MessageInfo position
    // (ABI v3: the top of the label range, base 0xFFF00).
    assert_eq!(error_frame_regs(17)[1], (0xFFF00u64 + 17) << 9);
}

/// Moved from `svc_dispatch`'s unit tests at RR5.6 (see this file's header).
#[test]
fn dispatch_svc_accepts_single_register_tcb_management_syscalls() {
    mark_this_core_ready();
    for sid in [
        SyscallId::TcbSetPriority,
        SyscallId::TcbSetMCPriority,
        SyscallId::TcbSetIPCBuffer,
        SyscallId::TcbSetAffinity,
        SyscallId::TcbSetFaultHandler,
    ] {
        // A length-1 message (exactly what the `sele4n-sys` wrappers send).
        let args = SyscallArgs {
            msg_info: 1,
            msg_regs: [0; 6],
            ipc_buffer_addr: None,
            elr: 0,
            spsr: 0,
            sp_el0: 0,
            x30: 0,
        };
        // Must clear the argument-count gate (any result other than the
        // count-mismatch rejection is acceptable here; on the host lane the
        // inner symbol is a stand-in).
        let result = dispatch_svc(sid as u32, &args);
        assert_ne!(
            result,
            Err(DispatchError::InvalidArgument),
            "length-1 call to {sid:?} must not be rejected by the arg-count gate",
        );
    }
}

/// Moved from `trap`'s unit tests at PR #889 review (the SVC arm halts on a
/// not-ready core before the narrowing, so the frames these paths publish are
/// observable only with the core marked ready): a syscall number outside
/// `SyscallId` takes the unknown-syscall seam, whose host-lane half publishes
/// the `invalidSyscallNumber` status frame (discriminant 31) — never a
/// success, never the thread's own request registers.
#[test]
fn unknown_syscall_id_on_ready_core_publishes_status_frame() {
    mark_this_core_ready();
    let mut frame = zero_frame();
    frame.esr_el1 = EC_SVC_AARCH64 << 26;
    frame.gprs[7] = 0xFFFF; // no such syscall
    frame.gprs[0] = 0xDEAD;
    handle_synchronous_exception(&mut frame);
    assert_eq!(frame.x0(), 0);
    assert_eq!(frame.x1(), (ERROR_LABEL_BASE + 31) << 9);
    assert_eq!([frame.x2(), frame.x3(), frame.x4(), frame.x5()], [0; 4]);
}

/// Moved from `trap`'s unit tests at PR #889 review (see above): the syscall
/// number is validated at its full 64-bit width.  `0x1_0000_0002` narrows to
/// syscall 2, which an `as u32` would have dispatched (the host stub answers
/// it with the `notImplemented` frame, discriminant 17); it is an unknown
/// syscall, and on the host lane that is the `invalidSyscallNumber` status
/// frame (31).
#[test]
fn wide_syscall_number_on_ready_core_is_unknown_syscall() {
    mark_this_core_ready();
    let mut frame = zero_frame();
    frame.esr_el1 = EC_SVC_AARCH64 << 26;
    frame.gprs[7] = 0x1_0000_0002;
    handle_synchronous_exception(&mut frame);
    assert_eq!(frame.x0(), 0);
    assert_eq!(frame.x1(), (ERROR_LABEL_BASE + 31) << 9);
    assert_ne!(frame.x1(), (ERROR_LABEL_BASE + 17) << 9);
}

/// PR #889 review: with the core ready, the prefilters run and refuse as
/// before — the gate moved ahead of them, it did not replace them.  (These
/// were `svc_dispatch`'s unit tests `dispatch_svc_rejects_invalid_syscall_id`
/// and `dispatch_svc_rejects_argument_count_below_minimum`; the gate made
/// their answer depend on readiness, which the lib binary cannot assume.)
#[test]
fn prefilters_still_refuse_on_a_ready_core() {
    mark_this_core_ready();
    let args = SyscallArgs::from_trap_frame(&zero_frame());
    assert_eq!(
        dispatch_svc(SyscallId::COUNT, &args),
        Err(DispatchError::InvalidSyscallId),
        "an out-of-range id is refused by the prefilter once the core is ready"
    );
    assert_eq!(
        dispatch_svc(SyscallId::TcbSetPriority.to_u32(), &args),
        Err(DispatchError::InvalidArgument),
        "a short message is refused by the argument-count prefilter once the core is ready"
    );
    // CSpaceMint needs four inline words; a zero-length message is short.
    assert_eq!(
        dispatch_svc(SyscallId::CSpaceMint.to_u32(), &args),
        Err(DispatchError::InvalidArgument),
        "a length-0 CSpaceMint is refused by the argument-count prefilter"
    );
}

/// Moved from `trap`'s unit tests at PR #889 review: an `SVC` increments the
/// executing core's syscall count.  The count is recorded before the readiness
/// gate; here the core is ready, so the arm runs to a frame and the count is
/// observed after an ordinary return.  Concurrent tests in this binary can only
/// raise the counter, so a strict increase is the right observation.
#[test]
fn svc_increments_per_core_syscall_count() {
    mark_this_core_ready();
    let core = sele4n_hal::per_cpu::current_core_id_from_tpidr() as usize;
    let before = sele4n_hal::per_cpu_stats::syscall_count_for(core);
    let mut frame = zero_frame();
    frame.esr_el1 = EC_SVC_AARCH64 << 26;
    handle_synchronous_exception(&mut frame);
    let after = sele4n_hal::per_cpu_stats::syscall_count_for(core);
    assert!(
        after > before,
        "SVC must increment per-core syscall_count (was {before}, now {after})"
    );
}

/// Moved from `ffi`'s unit tests at RR5.7 (see this file's header).
#[test]
fn sele4n_suspend_thread_brackets_inner_call() {
    mark_this_core_ready();
    // The wrapper must invoke the inner stand-in (which returns
    // NotImplemented = 17 on the host lane) and return its result.
    // This proves the bracket dispatches into the inner symbol.
    let result = sele4n_hal::ffi::sele4n_suspend_thread(42);
    assert_eq!(
        result, 17,
        "suspendThread bracket must forward inner stand-in return"
    );
}

/// Moved from `ffi`'s unit tests at RR5.7 (see this file's header).
#[test]
fn sele4n_suspend_thread_handles_zero_tid() {
    mark_this_core_ready();
    // ThreadId 0 is the sentinel; the wrapper must still invoke the
    // inner dispatch (which performs sentinel rejection at the Lean
    // layer).  This proves the bracket is a transparent forwarder
    // and does not pre-filter ids.
    let result = sele4n_hal::ffi::sele4n_suspend_thread(0);
    assert_eq!(result, 17, "bracket must not pre-filter sentinel");
}

/// Moved from `ffi`'s unit tests at RR5.7 (see this file's header).
#[test]
fn sele4n_suspend_thread_disables_interrupts_during_call() {
    mark_this_core_ready();
    // The bracket calls `with_interrupts_disabled`, which on host
    // is a no-op closure call.  We assert that it does not
    // panic and that the return value matches the inner stand-in.
    // The atomicity contract (interrupts actually disabled on
    // hardware) is enforced by the aarch64 implementation of
    // `interrupts::with_interrupts_disabled`.
    let r1 = sele4n_hal::ffi::sele4n_suspend_thread(1);
    let r2 = sele4n_hal::ffi::sele4n_suspend_thread(2);
    assert_eq!(r1, r2, "bracket must be deterministic");
}
