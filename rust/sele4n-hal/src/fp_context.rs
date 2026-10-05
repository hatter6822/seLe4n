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
//! doublewords — the Lean `FpContext.word` layout — carry them across the FFI,
//! the whole context in **one** call each way (`ffi::fp_context_to_lean`,
//! `ffi::fp_context_of_lean`), where the seam used to move one word per call:
//!
//! * [`capture`] stores the live registers into the core's **capture** buffer
//!   (`sele4n_fp_save_context`) and hands the buffer's words over, which the
//!   Lean kernel commits into the owner's TCB.  The save routine leaves the
//!   trap **armed**: a capture is taken exactly when the values are about to
//!   stop being the running thread's.
//! * The Lean kernel stages the context it answers into the core's **load**
//!   buffer ([`stage_context`]) and [`load_commit`] loads it
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

/// A thread's FP/SIMD context as its [`FP_CONTEXT_WORDS`] words, in the Lean
/// `FpContext.word` layout — the form the context crosses the boundary in.
pub type FpContextWords = [u64; FP_CONTEXT_WORDS];

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

    /// The buffer's words.
    #[must_use]
    pub fn words(&self) -> FpContextWords {
        // SAFETY: see the `Sync` impl — only the owning core touches the
        // buffer, and not concurrently with itself.
        unsafe { *self.0.get() }
    }

    /// Overwrite every word of the buffer.
    pub fn set_words(&self, words: &FpContextWords) {
        // SAFETY: as in `words`.
        unsafe { *self.0.get() = *words };
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

/// **WS-BP BP7.9**: per core, the buffer [`load_commit`] loads — what
/// `ffi::ffi_fp_stage_context` stages into.
#[must_use]
pub fn load_buffers() -> &'static FpBuffers {
    &LOAD
}

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
/// capture buffer, arming the trap, and hand the buffer's words over — the
/// whole context in one call (`Platform.FFI.ffiFpCapture`).  On the host there
/// are no registers to save, so the answer is the buffer as it stands.
#[must_use]
pub fn capture() -> FpContextWords {
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
    buf.words()
}

/// **WS-BP BP7.9**: stage the context the executing PE loads, whole (the
/// testable form takes the buffers and the core).  `false` past the core
/// array, with nothing written.
pub fn stage_context_in(buffers: &FpBuffers, core: usize, words: &FpContextWords) -> bool {
    match buffers.get(core) {
        Some(buf) => {
            buf.set_words(words);
            true
        }
        None => false,
    }
}

/// **WS-BP BP7.9**: stage the executing PE's load, the whole context in one
/// call (`Platform.FFI.ffiFpStageContext`).  A core past the buffers is a
/// kernel defect, so it halts the system rather than loading nothing.
pub fn stage_context(words: &FpContextWords) {
    if !stage_context_in(&LOAD, core_index(), words) {
        crate::gic::halt_all();
    }
}

/// **WS-BP BP7.9**: load the executing PE's staged context into its FP/SIMD
/// registers (`Platform.FFI.ffiFpLoadCommit`).
///
/// **PR #904 (`v0.36.41`)**: the trap is **re-armed** after the load.  The load
/// routine lifts it to reach the registers, and leaving it lifted made the
/// thread's FP state live before the restore commit decided whether the core
/// resumes that thread; the commit lifts it for a resume of the owner
/// ([`set_trap_for_resume`]), so the trap and the frame are set by one step.
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
    set_trap_for_resume(false);
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

    /// A staged context lands whole in its core's buffer, every word at its
    /// own position (the words are distinct), and in no other core's.
    #[test]
    fn a_staged_context_lands_in_its_core_and_nowhere_else() {
        let buffers: FpBuffers =
            [const { FpBuffer::new() }; crate::svc_dispatch::RETURN_FRAME_CORES];
        let words: FpContextWords = core::array::from_fn(|i| 0xF0C4_0000 + i as u64);
        assert!(stage_context_in(&buffers, 1, &words));
        assert_eq!(buffers[1].words(), words);
        assert_eq!(buffers[0].words(), [0; FP_CONTEXT_WORDS]);
    }

    /// A core past the buffers is refused, with nothing written anywhere.
    #[test]
    fn a_core_past_the_buffers_is_refused() {
        let buffers: FpBuffers =
            [const { FpBuffer::new() }; crate::svc_dispatch::RETURN_FRAME_CORES];
        let words: FpContextWords = [1; FP_CONTEXT_WORDS];
        assert!(!stage_context_in(
            &buffers,
            crate::svc_dispatch::RETURN_FRAME_CORES,
            &words
        ));
        for buf in &buffers {
            assert_eq!(buf.words(), [0; FP_CONTEXT_WORDS]);
        }
    }

    /// On the host a capture is the capture buffer as it stands: all zeroes,
    /// `FP_CONTEXT_WORDS` of them.
    #[test]
    fn a_host_capture_is_the_zero_buffer() {
        assert_eq!(capture(), [0; FP_CONTEXT_WORDS]);
    }
}
