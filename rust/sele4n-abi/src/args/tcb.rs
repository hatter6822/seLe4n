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
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.is_empty() { return Err(KernelError::InvalidMessageInfo); }
        if !regs[0].is_multiple_of(IPC_BUFFER_ALIGNMENT) {
            return Err(KernelError::AlignmentError);
        }
        Ok(Self { buffer_addr: regs[0] })
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
}
