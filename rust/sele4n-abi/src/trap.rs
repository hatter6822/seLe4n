// SPDX-License-Identifier: GPL-3.0-or-later
//! Syscall trap — the library's one unsafe operation, the `svc #0` instruction.
//!
//! On ARM64 (AArch64), the kernel entry point is the `svc #0` instruction.
//! On non-AArch64 targets (host testing), a mock implementation is provided.
//! The two are a `cfg` split of one signature, not two functions: exactly one
//! of them exists in any given compilation, which is what lets `invoke_syscall`
//! have a single, target-independent call site.

use crate::decode::decode_issued;
use crate::encode::REG_SYSCALL_NUM;
use crate::{encode_syscall, SyscallRequest, SyscallResponse};
use sele4n_types::{KernelError, KernelResult, Syscall};

/// Invoke a raw syscall by writing registers and executing `svc #0`.
///
/// # Safety
///
/// This function is `unsafe` because it triggers a supervisor call exception.
/// The caller must ensure the register contents encode a valid syscall request.
/// This is the only `unsafe fn` in the entire `libsele4n` library, and the
/// `asm!` below is its only unsafe operation.
///
/// On non-AArch64 targets, a mock answers instead: a `Call` gets an
/// `InvalidSyscallNumber` error frame, and every other syscall its own
/// registers back.
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
pub unsafe fn raw_syscall(regs: &mut [u64; 8]) {
    // ARM64 ABI: x0=cap_addr, x1=msg_info, x2-x5=msg_regs, x6=reply register
    // (seL4-MCS `replyRegister`), x7=syscall_num.
    // The kernel writes results back into x0-x5.
    //
    // U3-A: `clobber_abi("C")` tells the compiler that all caller-saved
    // registers per the AAPCS64 calling convention may be modified by the
    // kernel during the exception. This includes x8-x18, x29, x30, NZCV,
    // and all SIMD/FP registers. The explicit `inout`/`in`/`lateout`
    // operands for x0-x7 take precedence over the clobber set.
    //
    // The `unsafe` block is explicit rather than inherited from the `unsafe fn`
    // signature: the crate denies `unsafe_op_in_unsafe_fn`, so an unsafe
    // operation anywhere in this library has to say so at its own site.
    //
    // SAFETY: the operands describe the register effect of the trap exactly —
    // x0-x5 are read and written by the kernel (`inout`), x6 and x7 are read
    // (`in`), and `clobber_abi("C")` covers every other
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
            in("x6") regs[6],
            in("x7") regs[7],
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

    /// The last request's raw registers `[x0, x1, x2, x3, x4, x5, x6, x7]`,
    /// exactly as `encode_syscall` produced them.
    pub static LAST_REQUEST: [AtomicU64; 8] = [
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
        AtomicU64::new(0),
    ];

    /// Snapshot the captured registers.
    pub fn last_request() -> [u64; 8] {
        let mut out = [0u64; 8];
        for (slot, value) in LAST_REQUEST.iter().zip(out.iter_mut()) {
            *value = slot.load(Ordering::Relaxed);
        }
        out
    }

    pub(super) fn record(regs: &[u64; 8]) {
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
/// `const`, so the label's fit in the 52-bit field is checked when this file
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
/// answers as the kernel answers a refusal, since there is no kernel to
/// handle the syscall: a `Call` gets the InvalidSyscallNumber error frame,
/// and every other syscall resumes with the registers it trapped with —
/// seL4 writes an error only to a `Call` (`handleInvocation` replies only
/// `if (isCall)`; the kernel's `SyscallOutcome.resumes`).
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
/// for `aarch64-unknown-none-softfloat`); a change to one alone fails the other.
#[cfg(not(target_arch = "aarch64"))]
#[inline(always)]
#[allow(unsafe_code)]
pub unsafe fn raw_syscall(regs: &mut [u64; 8]) {
    host_capture::record(regs);
    // A refused non-`Call` resumes with its trapped registers: write nothing.
    if Syscall::from_word(regs[REG_SYSCALL_NUM]) != Some(Syscall::Call) {
        return;
    }
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
/// The response is read by the **seL4 syscall issued** — the one the `x7`
/// word [`encode_syscall`] produced names — through
/// [`decode_issued`]: only a `Call` returns a kernel error; a receive returns
/// the message it received; a `Send`, `NBSend` or `Yield` returns nothing,
/// and its registers, which the kernel leaves as the caller trapped with
/// them, are not read.
///
/// Returns `InvalidMessageInfo` if the MessageInfo label exceeds seL4's
/// 52-bit field (detected during encode).
#[inline]
#[allow(unsafe_code)]
pub fn invoke_syscall(req: SyscallRequest) -> KernelResult<SyscallResponse> {
    let mut regs = encode_syscall(&req)?;
    // The syscall the trap issues, read from the word it carries.  The
    // encoder writes a `Syscall::word`, so this names one; a word that named
    // none would be refused before trapping rather than decoded.
    let issued =
        Syscall::from_word(regs[REG_SYSCALL_NUM]).ok_or(KernelError::InvalidSyscallNumber)?;
    // SAFETY: `encode_syscall` produces a valid register array from a typed
    // `SyscallRequest`. The kernel validates all parameters on entry. This is
    // the single syscall boundary in the entire library.
    unsafe { raw_syscall(&mut regs) };
    // The response frame is `x0`-`x5`; x6 and x7 carry nothing back.
    decode_issued(
        issued,
        [regs[0], regs[1], regs[2], regs[3], regs[4], regs[5], 0],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::message_info::MessageInfo;
    use sele4n_types::{CPtr, SyscallId};

    fn request(syscall_id: SyscallId, label: u64) -> SyscallRequest {
        SyscallRequest {
            cap_addr: CPtr::from(9u64),
            msg_info: MessageInfo::new(1, 0, label).unwrap(),
            msg_regs: [11, 0, 0, 0],
            syscall_id,
            reply_cap: CPtr::NULL,
        }
    }

    /// The label `ERROR_LABEL_BASE + 1`: `ObjectNotFound`'s status label on
    /// a `Call`, and an ordinary message label everywhere else.
    const STATUS_RANGE_LABEL: u64 = sele4n_types::ERROR_LABEL_BASE + 1;

    /// A `Call` gets the mock's **InvalidSyscallNumber** frame, and the
    /// decode reads back exactly that error — for an IPC call and for a
    /// labelled invocation, both of which the encoder issues as `Call`.
    #[test]
    #[cfg(not(target_arch = "aarch64"))]
    fn mock_call_returns_invalid_syscall_number() {
        for sid in [SyscallId::Call, SyscallId::CSpaceMint] {
            assert_eq!(sid.syscall(), Syscall::Call);
            assert_eq!(
                invoke_syscall(request(sid, 0)),
                Err(KernelError::InvalidSyscallNumber),
                "{sid:?}"
            );
        }
    }

    /// **A `Send` whose own label lies in the status range succeeds.**  The
    /// kernel writes no register for a `Send`, `NBSend` or `Yield`, so the
    /// caller's `x1` comes back as it went out; read as a status it would be
    /// `ObjectNotFound` (the second assertion pins that the frame really is
    /// the one a status decode misreads).  Every operation the encoder issues
    /// as a syscall that returns nothing is driven: send, reply, signal and
    /// yield.
    #[test]
    #[cfg(not(target_arch = "aarch64"))]
    fn send_with_a_status_range_label_returns_ok() {
        for sid in [
            SyscallId::Send,
            SyscallId::Reply,
            SyscallId::NotificationSignal,
            SyscallId::Yield,
        ] {
            assert!(sid.syscall().returns_nothing(), "{sid:?}");
            let req = request(sid, STATUS_RANGE_LABEL);
            let regs = encode_syscall(&req).unwrap();
            assert_eq!(
                crate::decode_response([regs[0], regs[1], regs[2], regs[3], regs[4], regs[5], 0]),
                Err(KernelError::ObjectNotFound),
                "{sid:?}: the untouched frame reads as a status"
            );
            assert_eq!(
                invoke_syscall(req),
                Ok(SyscallResponse::NOTHING),
                "{sid:?}: a syscall that returns nothing succeeds"
            );
        }
    }

    /// **A receive returns its frame as the message received**, a
    /// status-range label included.  Under the mock a receive resumes with its
    /// trapped registers, so the frame is the request's own: badge `x0`, the
    /// label and the first message register come back as data.
    #[test]
    #[cfg(not(target_arch = "aarch64"))]
    fn receive_returns_a_status_range_label_as_data() {
        for sid in [
            SyscallId::Receive,
            SyscallId::NotificationWait,
            SyscallId::ReplyRecv,
        ] {
            let issued = sid.syscall();
            assert!(issued != Syscall::Call && !issued.returns_nothing());
            let resp = invoke_syscall(request(sid, STATUS_RANGE_LABEL))
                .unwrap_or_else(|e| panic!("{sid:?}: a receive returns no status, got {e:?}"));
            assert_eq!(resp.badge(), sele4n_types::Badge::from(9u64), "{sid:?}");
            assert_eq!(resp.msg_info().label(), STATUS_RANGE_LABEL, "{sid:?}");
            assert_eq!(resp.msg_regs[0], 11, "{sid:?}");
        }
    }

    /// The mock's `Call` frame: `x1` carries the status in the **top** of the
    /// 52-bit label range (ABI v3), and `x0` and the message registers are
    /// zero — the shape `Architecture.errorFrame` publishes.  Read back
    /// through `MessageInfo::decode`, so this pins the label *value*
    /// independently of the bit layout the constant was built with.  Every
    /// other syscall gets its registers back untouched.
    #[test]
    #[cfg(not(target_arch = "aarch64"))]
    // The crate is `#![deny(unsafe_code)]`; calling the trap directly needs the
    // same targeted allow the three production sites carry.
    #[allow(unsafe_code)]
    fn mock_writes_an_error_frame_only_to_call() {
        for issued in Syscall::ALL {
            let mut regs = [1u64; 8];
            regs[REG_SYSCALL_NUM] = issued.word();
            let trapped = regs;
            // SAFETY: the host mock writes only this register array (see its
            // `# Safety` note — it is `unsafe fn` for signature parity alone).
            unsafe { raw_syscall(&mut regs) };
            if issued != Syscall::Call {
                assert_eq!(regs, trapped, "{issued:?} must resume untouched");
                continue;
            }
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
    }

    /// A label at the very top of the range still fits the 52-bit field, so
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
