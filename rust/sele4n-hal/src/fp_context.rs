// SPDX-License-Identifier: GPL-3.0-or-later
// seLe4n  - A Lean Microkernel
// Copyright (C) 2026  Adam Hall
// This program comes with ABSOLUTELY NO WARRANTY.
// This is free software, and you are welcome to redistribute it
// under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

//! **WS-BP BP7.9 — the lazy FP/SIMD switch's register side.**
//!
//! The Lean kernel decides whose FP/SIMD state each core's registers hold
//! (`MachineState.fpOwner`) and when it changes hands
//! (`Architecture.fpAccessOnCore`, `Architecture.fpReleaseOnCore`); this module
//! is what moves the values.  Two per-core buffers of [`FP_CONTEXT_WORDS`]
//! doublewords — the Lean `FpContext.word` layout — carry them across the FFI:
//!
//! * [`capture`] stores the live registers into the core's **capture** buffer
//!   (`sele4n_fp_save_context`), which the Lean kernel reads word by word
//!   ([`captured_word`]) and commits into the owner's TCB.  The save routine
//!   leaves the trap **armed**: a capture is taken exactly when the values are
//!   about to stop being the running thread's.
//! * The Lean kernel stages the context it answers word by word into the core's
//!   **load** buffer ([`stage_word`]) and [`load_commit`] loads it
//!   (`sele4n_fp_load_context`) — every register the context names, `FPCR` and
//!   `FPSR` included, so nothing a previous owner left survives — with the trap
//!   lifted.
//!
//! The restore that ends every entry then sets the trap for what the core
//! resumes ([`set_trap_for_resume`]): lifted exactly when it resumes its owner.
//!
//! The four routines are hand-written assembly in `fp_context.S`'s own section,
//! the only kernel code that names an FP/SIMD register (the disassembly gate
//! exempts them by symbol) or writes `CPACR_EL1` outside the boot prologues
//! (`build.rs`'s `FP_CONTEXT_CPACR_WRITERS`).  On the host there are no FP/SIMD
//! registers to move, so the routines are absent and the buffers are the whole
//! observable — which is what the host tests drive.

use core::cell::UnsafeCell;

/// **WS-BP BP7.9**: the words a thread's FP/SIMD context occupies — `v0`–`v31`
/// as 64 doublewords, then `FPCR`, then `FPSR`.  Equal to the Lean
/// `SeLe4n.fpContextWordCount`.
pub const FP_CONTEXT_WORDS: usize = 66;

/// A core's FP/SIMD buffer, 16-byte aligned for the `stp`/`ldp q` pairs.
#[repr(C, align(16))]
pub struct FpBuffer(UnsafeCell<[u64; FP_CONTEXT_WORDS]>);

// SAFETY: buffer `c` is read and written only by core `c`, inside one kernel
// entry that holds the global kernel-entry lock, so no two accesses to one
// buffer are ever concurrent.
unsafe impl Sync for FpBuffer {}

impl FpBuffer {
    /// An all-zero buffer.
    pub const fn new() -> Self {
        Self(UnsafeCell::new([0; FP_CONTEXT_WORDS]))
    }

    /// Word `index`, or `None` past the context.
    #[must_use]
    pub fn word(&self, index: usize) -> Option<u64> {
        // SAFETY: see the `Sync` impl — only the owning core touches the
        // buffer, and not concurrently with itself.
        unsafe { (*self.0.get()).get(index).copied() }
    }

    /// Set word `index`; `false` past the context.
    pub fn set_word(&self, index: usize, value: u64) -> bool {
        // SAFETY: as in `word`.
        match unsafe { (*self.0.get()).get_mut(index) } {
            Some(slot) => {
                *slot = value;
                true
            }
            None => false,
        }
    }

    /// The buffer's base address, for the save and load routines.
    #[cfg_attr(
        not(all(feature = "hw_target", target_arch = "aarch64")),
        allow(dead_code)
    )]
    fn as_mut_ptr(&self) -> *mut u64 {
        self.0.get().cast::<u64>()
    }
}

impl Default for FpBuffer {
    fn default() -> Self {
        Self::new()
    }
}

/// **WS-BP BP7.9**: per core, the buffer [`capture`] fills.
pub type FpBuffers = [FpBuffer; crate::svc_dispatch::RETURN_FRAME_CORES];

static CAPTURE: FpBuffers = [const { FpBuffer::new() }; crate::svc_dispatch::RETURN_FRAME_CORES];
static LOAD: FpBuffers = [const { FpBuffer::new() }; crate::svc_dispatch::RETURN_FRAME_CORES];

#[cfg(all(feature = "hw_target", target_arch = "aarch64"))]
extern "C" {
    /// # Safety
    ///
    /// `buf` must point to [`FP_CONTEXT_WORDS`] writable, 16-byte-aligned
    /// doublewords that nothing else accesses for the call's duration, and the
    /// caller must be at EL1 (the routine writes `CPACR_EL1`).  It stores the
    /// live FP/SIMD registers there and leaves the FP/SIMD trap armed.
    fn sele4n_fp_save_context(buf: *mut u64);
    /// # Safety
    ///
    /// `buf` must point to [`FP_CONTEXT_WORDS`] readable, 16-byte-aligned
    /// doublewords, and the caller must be at EL1.  It loads every FP/SIMD
    /// register, `FPCR` and `FPSR` from there and leaves the trap lifted, so it
    /// must be called only for the context of the thread the core resumes.
    fn sele4n_fp_load_context(buf: *const u64);
    /// # Safety
    ///
    /// EL1 only.  Lifts the FP/SIMD trap; sound only when the core's registers
    /// hold the FP/SIMD state of the thread it resumes.
    fn sele4n_fp_trap_lift();
    /// # Safety
    ///
    /// EL1 only.  Arms the FP/SIMD trap (`CPACR_EL1 := 0`), the boot value.
    fn sele4n_fp_trap_arm();
}

fn core_index() -> usize {
    crate::per_cpu::current_core_id_from_tpidr() as usize
}

/// **WS-BP BP7.9**: save the executing PE's live FP/SIMD registers into its
/// capture buffer, arming the trap (`Platform.FFI.ffiFpCapture`).
pub fn capture() {
    let Some(buf) = CAPTURE.get(core_index()) else {
        crate::gic::halt_all();
    };
    #[cfg(all(feature = "hw_target", target_arch = "aarch64"))]
    // SAFETY: `buf` is this core's capture buffer — 66 aligned doublewords only
    // this core touches, inside the kernel-entry lock — and the kernel runs at
    // EL1.
    unsafe {
        sele4n_fp_save_context(buf.as_mut_ptr());
    }
    #[cfg(not(all(feature = "hw_target", target_arch = "aarch64")))]
    let _ = buf;
}

/// **WS-BP BP7.9**: word `index` of the executing PE's capture buffer; `0`
/// past the context (`Platform.FFI.ffiFpCapturedWord`).
#[must_use]
pub fn captured_word(index: u32) -> u64 {
    CAPTURE
        .get(core_index())
        .and_then(|b| b.word(index as usize))
        .unwrap_or(0)
}

/// **WS-BP BP7.9**: stage word `index` of the context the executing PE loads
/// (the testable form takes the buffers and the core).  `false` past the
/// context or the core array.
pub fn stage_word_in(buffers: &FpBuffers, core: usize, index: u32, value: u64) -> bool {
    buffers
        .get(core)
        .is_some_and(|b| b.set_word(index as usize, value))
}

/// **WS-BP BP7.9**: stage word `index` of the executing PE's load
/// (`Platform.FFI.ffiFpStageWord`).  A word past the context is a kernel
/// defect — the Lean kernel stages exactly [`FP_CONTEXT_WORDS`] — so it halts
/// the system rather than loading a partly staged context.
pub fn stage_word(index: u32, value: u64) {
    if !stage_word_in(&LOAD, core_index(), index, value) {
        crate::gic::halt_all();
    }
}

/// **WS-BP BP7.9**: load the executing PE's staged context into its FP/SIMD
/// registers and lift the trap (`Platform.FFI.ffiFpLoadCommit`).
pub fn load_commit() {
    let Some(buf) = LOAD.get(core_index()) else {
        crate::gic::halt_all();
    };
    #[cfg(all(feature = "hw_target", target_arch = "aarch64"))]
    // SAFETY: `buf` is this core's load buffer, fully staged by the Lean
    // kernel with the context of the thread this core resumes (the switch just
    // made it the owner), and the kernel runs at EL1.
    unsafe {
        sele4n_fp_load_context(buf.as_mut_ptr());
    }
    #[cfg(not(all(feature = "hw_target", target_arch = "aarch64")))]
    let _ = buf;
}

/// **WS-BP BP7.9**: word `index` of the executing PE's staged load — the
/// host tests' observable of what [`load_commit`] would load.
#[must_use]
pub fn staged_word(index: u32) -> u64 {
    LOAD.get(core_index())
        .and_then(|b| b.word(index as usize))
        .unwrap_or(0)
}

/// **WS-BP BP7.9**: set the FP/SIMD trap for what the core resumes — lifted
/// exactly when the Lean restore says the core resumes its FP owner
/// (`RestoreTarget.user`'s `fpLive`), armed otherwise.
pub fn set_trap_for_resume(owner_resumes: bool) {
    #[cfg(all(feature = "hw_target", target_arch = "aarch64"))]
    // SAFETY: the kernel runs at EL1, and the lift is taken only when the Lean
    // kernel's committed state records the resumed thread as this core's FP
    // owner, whose values the registers hold.
    unsafe {
        if owner_resumes {
            sele4n_fp_trap_lift();
        } else {
            sele4n_fp_trap_arm();
        }
    }
    #[cfg(not(all(feature = "hw_target", target_arch = "aarch64")))]
    let _ = owner_resumes;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_wire_layout_is_the_lean_one() {
        // 32 vector registers as two doublewords each, FPCR, FPSR.
        assert_eq!(FP_CONTEXT_WORDS, 2 * 32 + 2);
        assert_eq!(core::mem::align_of::<FpBuffer>(), 16);
        assert_eq!(core::mem::size_of::<FpBuffer>(), FP_CONTEXT_WORDS * 8);
    }

    #[test]
    fn a_staged_word_lands_in_its_core_and_nowhere_else() {
        let buffers: FpBuffers =
            [const { FpBuffer::new() }; crate::svc_dispatch::RETURN_FRAME_CORES];
        assert!(stage_word_in(&buffers, 1, 64, 0xF0C4));
        assert_eq!(buffers[1].word(64), Some(0xF0C4));
        assert_eq!(buffers[0].word(64), Some(0));
    }

    #[test]
    fn a_word_past_the_context_or_the_cores_is_refused() {
        let buffers: FpBuffers =
            [const { FpBuffer::new() }; crate::svc_dispatch::RETURN_FRAME_CORES];
        assert!(!stage_word_in(&buffers, 0, FP_CONTEXT_WORDS as u32, 1));
        assert!(!stage_word_in(
            &buffers,
            crate::svc_dispatch::RETURN_FRAME_CORES,
            0,
            1
        ));
        assert_eq!(buffers[0].word(FP_CONTEXT_WORDS), None);
    }
}
