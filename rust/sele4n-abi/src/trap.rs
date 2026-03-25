//! Syscall trap — the **single** `unsafe` block in the entire library.
//!
//! On ARM64 (AArch64), the kernel entry point is the `svc #0` instruction.
//! On non-AArch64 targets (host testing), a mock implementation is provided.

use sele4n_types::{KernelResult, KernelError};
use crate::{SyscallRequest, SyscallResponse, encode_syscall, decode_response};

/// Invoke a raw syscall by writing registers and executing `svc #0`.
///
/// # Safety
///
/// This function is `unsafe` because it triggers a supervisor call exception.
/// The caller must ensure the register contents encode a valid syscall request.
/// This is the **only** unsafe function in the entire `libsele4n` library.
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

/// Mock raw_syscall for non-AArch64 targets (host testing).
///
/// Returns an error response (InvalidSyscallNumber) since there is no
/// kernel to handle the syscall. Tests should use the mock infrastructure
/// in the `std` feature instead.
///
/// # Safety
///
/// Same contract as the ARM64 variant. The mock implementation is safe in
/// practice — it only writes to the provided register array.
#[cfg(not(target_arch = "aarch64"))]
#[inline(always)]
#[allow(unsafe_code)]
pub unsafe fn raw_syscall(regs: &mut [u64; 7]) {
    // Mock: set x0 to InvalidSyscallNumber error code
    regs[0] = KernelError::InvalidSyscallNumber as u64;
    // Clear return registers
    regs[1] = 0;
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
/// T3-A: Returns `InvalidMessageInfo` if the MessageInfo label exceeds
/// the 55-bit encoding limit (detected during encode).
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
    use sele4n_types::{CPtr, SyscallId};
    use crate::message_info::MessageInfo;

    #[test]
    #[cfg(not(target_arch = "aarch64"))]
    fn mock_syscall_returns_error() {
        let req = SyscallRequest {
            cap_addr: CPtr::from(0u64),
            msg_info: MessageInfo::new(0, 0, 0).unwrap(),
            msg_regs: [0; 4],
            syscall_id: SyscallId::Send,
        };
        let result = invoke_syscall(req);
        // Mock returns InvalidSyscallNumber
        assert!(result.is_err());
    }
}
