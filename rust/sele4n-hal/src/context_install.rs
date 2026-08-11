// SPDX-License-Identifier: GPL-3.0-or-later
/*
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
*/

//! **WS-SM SM8.B (PR #861 review rounds 18/19)**: the context-install seam.
//!
//! Before this module, a change of current thread lived entirely inside the
//! Lean `SystemState`.  The SVC handler wrote its result into the *original*
//! caller's `TrapFrame` and returned through it, so hardware resumed the thread
//! the model had just descheduled — and because `syscallDispatchFromAbi`
//! identifies its caller solely by `currentOnCore`, that thread's next syscall
//! was attributed to whichever thread the model believed was running.
//!
//! The kernel stages the incoming thread's registers here during the same
//! critical section that commits the transition, and [`install_into_frame`]
//! applies them to the trap frame before exception return.
//!
//! # Scope, and why it is a refusal rather than a partial switch
//!
//! A complete ARM64 context switch also writes `TTBR0_EL1` (and with it the
//! ASID) so the incoming thread runs under its own translation tables.  The
//! model cannot supply that value: `VSpaceRoot` carries an ASID and an abstract
//! `VAddr -> PAddr` mapping table, not the physical base of a hardware
//! translation table, and no `VSpaceRoot -> TTBR0` binding exists anywhere in
//! the kernel.
//!
//! So the Lean side (`PriorityInheritance.contextInstallFor`) only ever stages
//! a switch whose incoming and outgoing threads **share a `vspaceRoot`** —
//! proven by `contextInstallFor_install_same_vspace`.  For those the register
//! file is the whole context and no `TTBR0_EL1` write is required, which makes
//! this install complete and correct.  A switch that crosses address spaces
//! calls [`ffi_context_install_refuse`](crate::ffi::ffi_context_install_refuse)
//! instead and the system halts, because installing registers under the wrong
//! page tables is a memory-isolation violation and strictly worse than not
//! switching at all.
//!
//! `SPSR_EL1` is likewise not modelled and is deliberately left as the trap
//! entry saved it: every thread staged here is an EL0 thread interrupted by an
//! SVC from the same exception level, so the saved PSTATE is the one the
//! incoming thread needs.  A future EL-crossing switch must revisit this.

use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

/// General-purpose registers carried by an install: x0..x30.
///
/// Matches `TrapFrame::gprs` and the Lean `contextInstallGprCount`.  The zero
/// register is not stored by any frame, so this is `RegName::arm64GPRCount`
/// (32) minus one.
pub const CONTEXT_GPR_COUNT: usize = 31;

/// A staged context awaiting installation into the trap frame.
///
/// Per-core state is unnecessary: staging happens inside the kernel-entry
/// critical section (SM5.I) and is consumed by the same core before it returns,
/// so at most one staged context is live at a time.  `committed` is the
/// handshake — a partially-staged buffer is never installed.
pub struct StagedContext {
    gprs: [AtomicU64; CONTEXT_GPR_COUNT],
    sp_el0: AtomicU64,
    elr_el1: AtomicU64,
    committed: AtomicBool,
}

impl StagedContext {
    /// A staging buffer with nothing committed.
    pub const fn new() -> Self {
        #[allow(clippy::declare_interior_mutable_const)]
        const ZERO: AtomicU64 = AtomicU64::new(0);
        Self {
            gprs: [ZERO; CONTEXT_GPR_COUNT],
            sp_el0: AtomicU64::new(0),
            elr_el1: AtomicU64::new(0),
            committed: AtomicBool::new(false),
        }
    }
}

impl Default for StagedContext {
    fn default() -> Self {
        Self::new()
    }
}

/// The kernel's staging buffer.
pub static STAGED_CONTEXT: StagedContext = StagedContext::new();

/// Open a staging round, discarding whatever a previous one left behind.
///
/// Clearing `committed` first is load-bearing: it makes a torn stage
/// (begin without commit, e.g. a fault between the two) fail closed as
/// "nothing to install" rather than installing a half-written frame.
pub fn stage_begin_in(buf: &StagedContext) {
    buf.committed.store(false, Ordering::Relaxed);
}

/// Stage one general-purpose register.  Out-of-range indices are dropped
/// rather than wrapping — the commit's own bounds are what matter.
pub fn stage_gpr_in(buf: &StagedContext, index: usize, value: u64) {
    if index < CONTEXT_GPR_COUNT {
        buf.gprs[index].store(value, Ordering::Relaxed);
    }
}

/// Commit the staged registers together with `SP_EL0` and the exception-return
/// address.  Release ordering publishes every prior `stage_gpr_in` write.
pub fn stage_commit_in(buf: &StagedContext, sp: u64, pc: u64) {
    buf.sp_el0.store(sp, Ordering::Relaxed);
    buf.elr_el1.store(pc, Ordering::Relaxed);
    buf.committed.store(true, Ordering::Release);
}

/// Is a context staged and ready to install?
pub fn is_committed_in(buf: &StagedContext) -> bool {
    buf.committed.load(Ordering::Acquire)
}

/// Install a committed context into `frame`, and clear the buffer.
///
/// Returns `true` when a context was installed.  Consuming the commit flag is
/// what keeps a stale stage from being applied to a later, unrelated
/// exception return.
pub fn install_into_frame_in(buf: &StagedContext, frame: &mut crate::trap::TrapFrame) -> bool {
    if !is_committed_in(buf) {
        return false;
    }
    for (i, slot) in frame.gprs.iter_mut().enumerate().take(CONTEXT_GPR_COUNT) {
        *slot = buf.gprs[i].load(Ordering::Relaxed);
    }
    frame.sp_el0 = buf.sp_el0.load(Ordering::Relaxed);
    frame.elr_el1 = buf.elr_el1.load(Ordering::Relaxed);
    buf.committed.store(false, Ordering::Release);
    true
}

/// Install into `frame` from the kernel's staging buffer.
pub fn install_into_frame(frame: &mut crate::trap::TrapFrame) -> bool {
    install_into_frame_in(&STAGED_CONTEXT, frame)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn blank_frame() -> crate::trap::TrapFrame {
        crate::trap::TrapFrame {
            gprs: [0; 31],
            sp_el0: 0,
            elr_el1: 0,
            spsr_el1: 0xdead_beef,
            esr_el1: 0,
            far_el1: 0,
        }
    }

    #[test]
    fn uncommitted_stage_installs_nothing() {
        let buf = StagedContext::new();
        let mut frame = blank_frame();
        stage_begin_in(&buf);
        for i in 0..CONTEXT_GPR_COUNT {
            stage_gpr_in(&buf, i, 0x1000 + i as u64);
        }
        // No commit: a torn stage must fail closed.
        assert!(!install_into_frame_in(&buf, &mut frame));
        assert_eq!(frame.gprs, [0; 31]);
    }

    #[test]
    fn committed_stage_installs_every_register() {
        let buf = StagedContext::new();
        let mut frame = blank_frame();
        stage_begin_in(&buf);
        for i in 0..CONTEXT_GPR_COUNT {
            stage_gpr_in(&buf, i, 0x1000 + i as u64);
        }
        stage_commit_in(&buf, 0xaaaa, 0xbbbb);
        assert!(install_into_frame_in(&buf, &mut frame));
        for i in 0..CONTEXT_GPR_COUNT {
            assert_eq!(frame.gprs[i], 0x1000 + i as u64, "gpr {i}");
        }
        assert_eq!(frame.sp_el0, 0xaaaa);
        assert_eq!(frame.elr_el1, 0xbbbb);
    }

    #[test]
    fn spsr_is_left_alone() {
        // Not modelled, and deliberately preserved: the incoming thread is
        // resumed at the exception level the trap entry saved.
        let buf = StagedContext::new();
        let mut frame = blank_frame();
        stage_begin_in(&buf);
        stage_commit_in(&buf, 1, 2);
        assert!(install_into_frame_in(&buf, &mut frame));
        assert_eq!(frame.spsr_el1, 0xdead_beef);
    }

    #[test]
    fn install_consumes_the_commit() {
        // The load-bearing one: a stale stage must not be applied to a later,
        // unrelated exception return.
        let buf = StagedContext::new();
        let mut frame = blank_frame();
        stage_begin_in(&buf);
        stage_gpr_in(&buf, 0, 0x77);
        stage_commit_in(&buf, 1, 2);
        assert!(install_into_frame_in(&buf, &mut frame));

        let mut later = blank_frame();
        assert!(!install_into_frame_in(&buf, &mut later));
        assert_eq!(later.gprs[0], 0, "a consumed stage must not install again");
    }

    #[test]
    fn begin_invalidates_a_previous_commit() {
        let buf = StagedContext::new();
        stage_begin_in(&buf);
        stage_commit_in(&buf, 1, 2);
        assert!(is_committed_in(&buf));
        stage_begin_in(&buf);
        assert!(
            !is_committed_in(&buf),
            "a new round must not inherit the previous commit"
        );
    }

    #[test]
    fn out_of_range_gpr_is_dropped_not_wrapped() {
        let buf = StagedContext::new();
        let mut frame = blank_frame();
        stage_begin_in(&buf);
        stage_gpr_in(&buf, CONTEXT_GPR_COUNT, 0xbad);
        stage_gpr_in(&buf, u64::MAX as usize, 0xbad);
        stage_commit_in(&buf, 0, 0);
        assert!(install_into_frame_in(&buf, &mut frame));
        assert!(
            frame.gprs.iter().all(|&g| g == 0),
            "an out-of-range index must not alias a real register"
        );
    }

    #[test]
    fn gpr_count_matches_the_frame() {
        let frame = blank_frame();
        assert_eq!(CONTEXT_GPR_COUNT, frame.gprs.len());
    }
}
