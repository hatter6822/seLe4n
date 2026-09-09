// SPDX-License-Identifier: GPL-3.0-or-later
//! Syscall trap — the library's one unsafe operation, the `svc #0` instruction.
//!
//! On ARM64 (AArch64), the kernel entry point is the `svc #0` instruction.
//! On non-AArch64 targets (host testing), a mock implementation is provided.
//! The two are a `cfg` split of one signature, not two functions: exactly one
//! of them exists in any given compilation, which is what lets `invoke_syscall`
//! have a single, target-independent call site.

use crate::{decode_response, encode_syscall, SyscallRequest, SyscallResponse};
use sele4n_types::{KernelError, KernelResult};

/// Invoke a raw syscall by writing registers and executing `svc #0`.
///
/// # Safety
///
/// This function is `unsafe` because it triggers a supervisor call exception.
/// The caller must ensure the register contents encode a valid syscall request.
/// This is the only `unsafe fn` in the entire `libsele4n` library, and the
/// `asm!` below is its only unsafe operation.
///
/// On non-AArch64 targets, this returns an `InvalidSyscallNumber` error
/// response (use `invoke_syscall` with the `std` feature for testing).
///
/// # Register clobbers (U3-A / U-H11)
///
/// The `svc #0` instruction triggers an exception into EL1, where the kernel
/// is free to modify any caller-saved register. We use `clobber_abi("C")` to
/// inform the compiler that all AArch64 caller-saved registers (x8–x18,
/// x29/x30, NZCV, SIMD/FP) may be clobbered by the kernel. Without this,
/// the compiler may assume those registers are preserved across the `svc`,
/// leading to silent register corruption.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
#[allow(unsafe_code)]
pub unsafe fn raw_syscall(regs: &mut [u64; 7]) {
    // ARM64 ABI: x0=cap_addr, x1=msg_info, x2-x5=msg_regs, x7=syscall_num
    // The kernel writes results back into x0-x5.
    //
    // U3-A: `clobber_abi("C")` tells the compiler that all caller-saved
    // registers per the AAPCS64 calling convention may be modified by the
    // kernel during the exception. This includes x8-x18, x29, x30, NZCV,
    // and all SIMD/FP registers. The explicit `inout`/`in`/`lateout`
    // operands for x0-x7 take precedence over the clobber set.
    // AK4-H (R-ABI-L5): `lateout("x6") _` is redundant here — `clobber_abi("C")`
    // already declares x0..x18 as caller-saved per AAPCS64, so x6 is implicitly
    // clobbered. We keep the explicit annotation for readability: it makes the
    // kernel's use of x6 as a scratch register visible at the call site. Removing
    // it is a no-op codegen-wise.
    //
    // The `unsafe` block is explicit rather than inherited from the `unsafe fn`
    // signature: the crate denies `unsafe_op_in_unsafe_fn`, so an unsafe
    // operation anywhere in this library has to say so at its own site.
    //
    // SAFETY: the operands describe the register effect of the trap exactly —
    // x0-x5 are read and written by the kernel (`inout`), x7 is read (`in`),
    // x6 is written (`lateout`), and `clobber_abi("C")` covers every other
    // AAPCS64 caller-saved register the kernel may touch. `nostack` is sound
    // because the instruction pushes nothing: AAPCS64 has no red zone, and the
    // kernel switches to its own stack on the exception. The trap's *effect* on
    // kernel state is the caller's obligation, stated in `# Safety` above.
    unsafe {
        core::arch::asm!(
            "svc #0",
            inout("x0") regs[0],
            inout("x1") regs[1],
            inout("x2") regs[2],
            inout("x3") regs[3],
            inout("x4") regs[4],
            inout("x5") regs[5],
            in("x7") regs[6],
            lateout("x6") _,
            clobber_abi("C"),
            options(nostack),
        );
    }
}

/// Host-testing capture of the last request the mock trap saw (PR #866
/// round-3 review).  The conformance suite calls the **real** `sele4n-sys`
/// wrappers and reads back the exact registers their encode produced, so
/// wrapper-shape pins exercise the genuine definitions instead of
/// hand-duplicated literals — the drift that let two wrong lengths and
/// two missing syscalls pass a green table while four real wrappers were
/// rejected at the HAL prefilter.
///
/// `core::sync::atomic` (no_std-compatible); tests that read the capture
/// must serialise around the wrapper call (parallel test threads share
/// these slots).
#[cfg(not(target_arch = "aarch64"))]
pub mod host_capture {
    use core::sync::atomic::{AtomicU64, Ordering};

    /// The last request's raw registers `[x0, x1, x2, x3, x4, x5, x7]`,
    /// exactly as `encode_syscall` produced them.
    pub static LAST_REQUEST: [AtomicU64; 7] = [
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
    ];

    /// Snapshot the captured registers.
    pub fn last_request() -> [u64; 7] {
        let mut out = [0u64; 7];
        for (slot, value) in LAST_REQUEST.iter().zip(out.iter_mut()) {
            *value = slot.load(Ordering::Relaxed);
        }
        out
    }

    pub(super) fn record(regs: &[u64; 7]) {
        for (slot, value) in LAST_REQUEST.iter().zip(regs.iter()) {
            slot.store(*value, Ordering::Relaxed);
        }
    }
}

/// The `x1` word the host mock publishes: `MessageInfo { length 0,
/// extraCaps 0, label ERROR_LABEL_BASE + InvalidSyscallNumber }`.
///
/// Built through this crate's **own** encoder rather than by re-deriving the
/// bit layout.  It was written out as `(ERROR_LABEL_BASE + d) << 9`, which is
/// the `label` shift from [`MessageInfo::encode`] copied into a second place
/// *in the crate that owns the encoder* — so moving the layout would have left
/// the mock publishing wrong bits, and the host test would not have noticed
/// (it asserted only that the result was *an* error).  The kernel side keeps
/// its own copy of the constant on purpose (`sele4n-hal`'s `error_frame_regs`,
/// under that crate's zero-runtime-deps discipline, pinned against
/// `sele4n_types` by a `const` assertion); there is no such reason here.
///
/// `const`, so the label's fit in the 20-bit field is checked when this file
/// compiles rather than when a host test happens to run.
#[cfg(not(target_arch = "aarch64"))]
const MOCK_ERROR_FRAME_X1: u64 = {
    let info = crate::message_info::MessageInfo::new_const(
        0,
        0,
        sele4n_types::ERROR_LABEL_BASE + (KernelError::InvalidSyscallNumber as u64),
    );
    match info.encode() {
        Ok(word) => word,
        Err(_) => panic!("the mock's error label must fit the MessageInfo label field"),
    }
};

/// Mock raw_syscall for non-AArch64 targets (host testing).
///
/// Records the request registers into [`host_capture`] (so conformance
/// tests can drive the real wrappers and inspect what they encoded), then
/// returns an error response (InvalidSyscallNumber) since there is no
/// kernel to handle the syscall.
///
/// # Safety
///
/// This body performs no unsafe operation: it writes the caller's own register
/// array and nothing else.  It is `unsafe fn` for **signature parity** with the
/// AArch64 variant above, which genuinely is unsafe — that is what lets
/// `invoke_syscall` carry exactly one `unsafe` block for both targets instead
/// of a `cfg`-split call site, and it keeps a host caller under the same
/// obligation the hardware caller has, so a caller written and tested on the
/// host cannot silently lose that obligation when cross-compiled.
///
/// That first sentence is **checked, not asserted**: the crate denies
/// `unsafe_op_in_unsafe_fn`, so an `unsafe fn` body is no longer an implicit
/// unsafe context, and this body containing no `unsafe` block is the compiler's
/// statement that it needs none.  A future edit that reached for a raw pointer
/// or a foreign call here would fail to compile rather than quietly making the
/// docstring false.
///
/// The two variants are held to one signature by CI building both targets
/// (`scripts/test_rust.sh` for the host, `scripts/test_aarch64_cross_build.sh`
/// for `aarch64-unknown-none`); a change to one alone fails the other.
#[cfg(not(target_arch = "aarch64"))]
#[inline(always)]
#[allow(unsafe_code)]
pub unsafe fn raw_syscall(regs: &mut [u64; 7]) {
    host_capture::record(regs);
    // Mock (WS-RA shape, ABI v3): an error rides the x1 label in the top of
    // the label range (label ERROR_LABEL_BASE + d = discriminant d), with
    // x0 = 0 — exactly the frame the kernel's `errorFrame` would publish
    // for InvalidSyscallNumber.
    regs[0] = 0;
    regs[1] = MOCK_ERROR_FRAME_X1;
    regs[2] = 0;
    regs[3] = 0;
    regs[4] = 0;
    regs[5] = 0;
}

/// Safe syscall invocation wrapper.
///
/// Encodes the request into registers, invokes the syscall trap, and
/// decodes the response. This is the primary entry point for all
/// high-level wrappers in `sele4n-sys`.
///
/// V2-H: Returns `InvalidMessageInfo` if the MessageInfo label exceeds
/// the 20-bit encoding limit (detected during encode).
#[inline]
#[allow(unsafe_code)]
pub fn invoke_syscall(req: SyscallRequest) -> KernelResult<SyscallResponse> {
    let mut regs = encode_syscall(&req)?;
    // SAFETY: `encode_syscall` produces a valid register array from a typed
    // `SyscallRequest`. The kernel validates all parameters on entry. This is
    // the single syscall boundary in the entire library.
    unsafe { raw_syscall(&mut regs) };
    decode_response(regs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::message_info::MessageInfo;
    use sele4n_types::{CPtr, SyscallId};

    /// The mock publishes the **InvalidSyscallNumber** frame, and
    /// `decode_response` reads back exactly that error.
    ///
    /// This asserted only `result.is_err()`, which any error whatsoever
    /// satisfies — a presence check standing in for the relation "the mock
    /// publishes the frame the kernel's `errorFrame` would".  A wrong
    /// discriminant, a wrong label base, or a shifted layout all passed it.
    /// Naming the error closes the encode/decode round trip.
    #[test]
    #[cfg(not(target_arch = "aarch64"))]
    fn mock_syscall_returns_invalid_syscall_number() {
        let req = SyscallRequest {
            cap_addr: CPtr::from(0u64),
            msg_info: MessageInfo::new(0, 0, 0).unwrap(),
            msg_regs: [0; 4],
            syscall_id: SyscallId::Send,
        };
        assert_eq!(invoke_syscall(req), Err(KernelError::InvalidSyscallNumber));
    }

    /// The mock's `x1` carries the status in the **top** of the 20-bit label
    /// range (ABI v3), and `x0` and the message registers are zero — the shape
    /// `Architecture.errorFrame` publishes.  Read back through
    /// `MessageInfo::decode`, so this pins the label *value* independently of
    /// the bit layout the constant was built with.
    #[test]
    #[cfg(not(target_arch = "aarch64"))]
    // The crate is `#![deny(unsafe_code)]`; calling the trap directly needs the
    // same targeted allow the three production sites carry.
    #[allow(unsafe_code)]
    fn mock_error_frame_matches_the_kernel_shape() {
        let mut regs = [1u64; 7];
        // SAFETY: the host mock writes only this register array (see its
        // `# Safety` note — it is `unsafe fn` for signature parity alone).
        unsafe { raw_syscall(&mut regs) };
        assert_eq!(regs[0], 0, "x0 must be 0 on an error frame");
        assert_eq!(
            MessageInfo::decode(regs[1]).unwrap().label(),
            sele4n_types::ERROR_LABEL_BASE + (KernelError::InvalidSyscallNumber as u64),
            "x1 must carry ERROR_LABEL_BASE + discriminant in its label"
        );
        assert_eq!(
            &regs[2..6],
            &[0, 0, 0, 0],
            "no message registers on an error"
        );
    }

    /// A label at the very top of the range still fits the 20-bit field, so
    /// the `const` construction of the mock frame cannot be one discriminant
    /// away from overflowing it unnoticed.
    #[test]
    fn every_error_discriminant_fits_the_label_field() {
        let top = sele4n_types::ERROR_LABEL_BASE + 255;
        assert!(
            MessageInfo::new(0, 0, top).is_ok(),
            "ERROR_LABEL_BASE + 255 must remain encodable"
        );
        assert!(
            MessageInfo::new(0, 0, top + 1).is_err(),
            "and one past it must not — the range is exactly 256 wide"
        );
    }
}
