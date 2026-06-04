// SPDX-License-Identifier: GPL-3.0-or-later
//! TCB operation syscall argument structures (D1/D2/D3).
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 1201–1340.
//! D1: Suspend/Resume (capability-only, no additional arguments).
//! D2: SetPriority/SetMCPriority (priority value from MR[0]).
//! D3: SetIPCBuffer (buffer address from MR[0]).

use sele4n_types::{KernelError, KernelResult};

/// Maximum configurable priority value (8-bit, matching Lean `Priority` range 0xFF).
/// Re-uses `sched_context::MAX_PRIORITY` (same value) — defined here for local clarity.
const MAX_PRIORITY: u64 = 255;

/// IPC buffer alignment in bytes (2^9 = 512, matching seL4 `seL4_IPCBufferSizeBits = 9`).
pub const IPC_BUFFER_ALIGNMENT: u64 = 512;

/// Arguments for `tcbSuspend` (syscall 20).
/// Capability-only: no additional arguments — target thread identified by capability.
///
/// Lean: `SuspendArgs` (SyscallArgDecode.lean:1201–1203)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SuspendArgs;

impl SuspendArgs {
    pub const fn encode(&self) -> [u64; 0] {
        []
    }

    /// Decode from message registers. No registers required.
    pub fn decode(_regs: &[u64]) -> KernelResult<Self> {
        Ok(Self)
    }
}

/// Arguments for `tcbResume` (syscall 21).
/// Capability-only: no additional arguments — target thread identified by capability.
///
/// Lean: `ResumeArgs` (SyscallArgDecode.lean:1207–1209)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResumeArgs;

impl ResumeArgs {
    pub const fn encode(&self) -> [u64; 0] {
        []
    }

    /// Decode from message registers. No registers required.
    pub fn decode(_regs: &[u64]) -> KernelResult<Self> {
        Ok(Self)
    }
}

/// Arguments for `tcbSetPriority` (syscall 22).
/// Register mapping: x2=newPriority.
///
/// Lean: `SetPriorityArgs` (SyscallArgDecode.lean:1243–1246)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetPriorityArgs {
    pub new_priority: u64,
}

impl SetPriorityArgs {
    pub const fn encode(&self) -> [u64; 1] {
        [self.new_priority]
    }

    /// Decode from message registers. Requires 1 register.
    /// Validates priority ≤ 255 at the decode boundary.
    /// Returns `InvalidArgument` on out-of-range (matches Lean `decodeSetPriorityArgs`).
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.is_empty() { return Err(KernelError::InvalidMessageInfo); }
        if regs[0] > MAX_PRIORITY {
            return Err(KernelError::InvalidArgument);
        }
        Ok(Self { new_priority: regs[0] })
    }
}

/// Arguments for `tcbSetMCPriority` (syscall 23).
/// Register mapping: x2=newMCP.
///
/// Lean: `SetMCPriorityArgs` (SyscallArgDecode.lean:1250–1253)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetMCPriorityArgs {
    pub new_mcp: u64,
}

impl SetMCPriorityArgs {
    pub const fn encode(&self) -> [u64; 1] {
        [self.new_mcp]
    }

    /// Decode from message registers. Requires 1 register.
    /// Validates MCP ≤ 255 at the decode boundary.
    /// Returns `InvalidArgument` on out-of-range (matches Lean `decodeSetMCPriorityArgs`).
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.is_empty() { return Err(KernelError::InvalidMessageInfo); }
        if regs[0] > MAX_PRIORITY {
            return Err(KernelError::InvalidArgument);
        }
        Ok(Self { new_mcp: regs[0] })
    }
}

/// Arguments for `tcbSetIPCBuffer` (syscall 24).
/// Register mapping: x2=bufferAddr.
///
/// Lean: `SetIPCBufferArgs` (SyscallArgDecode.lean:1312–1315)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetIPCBufferArgs {
    pub buffer_addr: u64,
}

impl SetIPCBufferArgs {
    pub const fn encode(&self) -> [u64; 1] {
        [self.buffer_addr]
    }

    /// Decode from message registers. Requires 1 register.
    /// Validates alignment to `IPC_BUFFER_ALIGNMENT` (512 bytes).
    ///
    /// Uses the bitwise-AND form `(addr & MASK) != 0` rather than
    /// `addr % ALIGN != 0` so the check is lint-clean on the project's
    /// pinned MSRV (Rust 1.82, predating clippy 1.87's
    /// `manual_is_multiple_of` lint) without needing an
    /// `#[allow(clippy::manual_is_multiple_of)]` workaround — and
    /// without the paired `#[allow(unknown_lints)]` that would
    /// otherwise be required to keep the inner allow lint-clean on
    /// 1.82.  `IPC_BUFFER_ALIGNMENT = 512` is a power of 2, so the
    /// two forms are mathematically equivalent.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.is_empty() { return Err(KernelError::InvalidMessageInfo); }
        if (regs[0] & (IPC_BUFFER_ALIGNMENT - 1)) != 0 {
            return Err(KernelError::AlignmentError);
        }
        Ok(Self { buffer_addr: regs[0] })
    }
}

/// Arguments for `tcbSetAffinity` (syscall 25).
/// Register mapping: x2 = the raw affinity word.  Values `0 .. numCores-1` bind
/// the target thread to that core; the marker `numCores` unbinds it.  The semantic
/// range check is the kernel's `decodeAffinity` responsibility (so the raw word is
/// passed through unvalidated here).
///
/// Lean: `SetAffinityArgs` (SyscallArgDecode.lean, WS-SM SM5.H.4)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetAffinityArgs {
    pub affinity_raw: u64,
}

impl SetAffinityArgs {
    pub const fn encode(&self) -> [u64; 1] {
        [self.affinity_raw]
    }

    /// Decode from message registers. Requires 1 register (the raw affinity word).
    /// The semantic range check (`< numCores`, or the unbind marker) is performed
    /// kernel-side by `decodeAffinity`, matching Lean `decodeSetAffinityArgs`.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.is_empty() { return Err(KernelError::InvalidMessageInfo); }
        Ok(Self { affinity_raw: regs[0] })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- D1: Suspend/Resume --

    #[test]
    fn suspend_roundtrip() {
        assert_eq!(SuspendArgs::decode(&[]).unwrap(), SuspendArgs);
        // Extra registers are ignored
        assert_eq!(SuspendArgs::decode(&[1, 2, 3]).unwrap(), SuspendArgs);
    }

    #[test]
    fn resume_roundtrip() {
        assert_eq!(ResumeArgs::decode(&[]).unwrap(), ResumeArgs);
        assert_eq!(ResumeArgs::decode(&[42]).unwrap(), ResumeArgs);
    }

    // -- D2: SetPriority/SetMCPriority --

    #[test]
    fn set_priority_roundtrip() {
        let args = SetPriorityArgs { new_priority: 128 };
        assert_eq!(SetPriorityArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn set_priority_max_valid() {
        let args = SetPriorityArgs::decode(&[255]).unwrap();
        assert_eq!(args.new_priority, 255);
    }

    #[test]
    fn set_priority_out_of_range() {
        assert_eq!(SetPriorityArgs::decode(&[256]), Err(KernelError::InvalidArgument));
    }

    #[test]
    fn set_priority_insufficient_regs() {
        assert_eq!(SetPriorityArgs::decode(&[]), Err(KernelError::InvalidMessageInfo));
    }

    #[test]
    fn set_mcp_roundtrip() {
        let args = SetMCPriorityArgs { new_mcp: 64 };
        assert_eq!(SetMCPriorityArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn set_mcp_out_of_range() {
        assert_eq!(SetMCPriorityArgs::decode(&[256]), Err(KernelError::InvalidArgument));
    }

    #[test]
    fn set_mcp_insufficient_regs() {
        assert_eq!(SetMCPriorityArgs::decode(&[]), Err(KernelError::InvalidMessageInfo));
    }

    // -- D3: SetIPCBuffer --

    #[test]
    fn set_ipc_buffer_roundtrip() {
        let args = SetIPCBufferArgs { buffer_addr: 512 };
        assert_eq!(SetIPCBufferArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn set_ipc_buffer_aligned() {
        let args = SetIPCBufferArgs::decode(&[1024]).unwrap();
        assert_eq!(args.buffer_addr, 1024);
    }

    #[test]
    fn set_ipc_buffer_unaligned() {
        assert_eq!(SetIPCBufferArgs::decode(&[513]), Err(KernelError::AlignmentError));
    }

    #[test]
    fn set_ipc_buffer_zero() {
        // Zero is aligned (0 % 512 == 0)
        let args = SetIPCBufferArgs::decode(&[0]).unwrap();
        assert_eq!(args.buffer_addr, 0);
    }

    #[test]
    fn set_ipc_buffer_insufficient_regs() {
        assert_eq!(SetIPCBufferArgs::decode(&[]), Err(KernelError::InvalidMessageInfo));
    }

    // -- WS-SM SM5.H.4: SetAffinity --

    #[test]
    fn set_affinity_roundtrip() {
        let args = SetAffinityArgs { affinity_raw: 2 };
        assert_eq!(SetAffinityArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn set_affinity_unbind_marker() {
        // The unbind marker (numCores = 4 on RPi5) is passed through unvalidated;
        // the kernel's `decodeAffinity` interprets it.
        let args = SetAffinityArgs::decode(&[4]).unwrap();
        assert_eq!(args.affinity_raw, 4);
    }

    #[test]
    fn set_affinity_passes_through_large_value() {
        // The ABI decode does not range-check; the kernel rejects out-of-range.
        let args = SetAffinityArgs::decode(&[999]).unwrap();
        assert_eq!(args.affinity_raw, 999);
    }

    #[test]
    fn set_affinity_insufficient_regs() {
        assert_eq!(SetAffinityArgs::decode(&[]), Err(KernelError::InvalidMessageInfo));
    }
}
