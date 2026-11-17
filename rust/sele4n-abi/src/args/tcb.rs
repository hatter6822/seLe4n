// SPDX-License-Identifier: GPL-3.0-or-later
//! TCB operation syscall argument structures (D1/D2/D3).
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 1201–1340.
//! D1: Suspend/Resume (capability-only, no additional arguments).
//! D2: SetPriority/SetMCPriority (priority value from MR[0]).
//! D3: SetIPCBuffer (buffer address from MR[0]).

use sele4n_types::{KernelError, KernelResult};

/// Maximum configurable priority value (8-bit, matching Lean `Priority` range 0xFF).
const MAX_PRIORITY: u64 = 255;

/// IPC buffer alignment in bytes, which is also the buffer's size (2^10 = 1024,
/// matching seL4's 64-bit `seL4_IPCBufferSizeBits = 10`): a buffer aligned to its
/// size lies in one 4 KiB frame.
pub const IPC_BUFFER_ALIGNMENT: u64 = 1024;

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
        if regs.is_empty() {
            return Err(KernelError::InvalidMessageInfo);
        }
        if regs[0] > MAX_PRIORITY {
            return Err(KernelError::InvalidArgument);
        }
        Ok(Self {
            new_priority: regs[0],
        })
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
        if regs.is_empty() {
            return Err(KernelError::InvalidMessageInfo);
        }
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
    ///
    /// The address is carried as given: seL4's `decodeSetIPCBuffer` checks
    /// its alignment (`IPC_BUFFER_ALIGNMENT`) in `checkValidIPCBuffer`, after
    /// the frame capability, so the kernel refuses a misaligned address with
    /// `AlignmentError` only once the capability is a non-device frame.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.is_empty() {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            buffer_addr: regs[0],
        })
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
        if regs.is_empty() {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            affinity_raw: regs[0],
        })
    }
}

/// Arguments for `tcbSetSpace` (syscall 38) — seL4-MCS's `TCB_SetSpace`.
/// Register mapping: x2 = seL4's `cspace_root_data` (when nonzero, the CSpace
/// root copy's guard in bits 63:6 and guard size in bits 5:0, as
/// `updateCapData` reads a CNode capability's data word); x3 = seL4's
/// `vspace_root_data`.  The capabilities travel as extra caps, addressed in
/// the **caller's** CSpace by the IPC buffer's `caps_or_badges` words:
/// extra cap 0 is the fault endpoint copied into the thread's fault-handler
/// slot (an empty slot clears it), extra cap 1 the new CSpace root (a CNode)
/// and extra cap 2 the new VSpace root.  The target thread must be suspended.
///
/// Lean: `SetSpaceArgs` (SyscallArgDecode.lean)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetSpaceArgs {
    pub cspace_root_data: u64,
    pub vspace_root_data: u64,
}

impl SetSpaceArgs {
    /// Extra-cap index of the fault endpoint.
    pub const FAULT_EP_EXTRA_CAP: usize = 0;
    /// Extra-cap index of the CSpace root.
    pub const CSPACE_ROOT_EXTRA_CAP: usize = 1;
    /// Extra-cap index of the VSpace root.
    pub const VSPACE_ROOT_EXTRA_CAP: usize = 2;
    /// Number of extra caps the invocation carries.
    pub const EXTRA_CAPS: usize = 3;

    pub const fn encode(&self) -> [u64; 2] {
        [self.cspace_root_data, self.vspace_root_data]
    }

    /// Decode from message registers. Requires 2 registers.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 2 {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            cspace_root_data: regs[0],
            vspace_root_data: regs[1],
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- WS-BP BP7.1: SetSpace --

    #[test]
    fn set_space_roundtrip() {
        let args = SetSpaceArgs {
            cspace_root_data: (0x5 << 6) | 3,
            vspace_root_data: 0x22,
        };
        assert_eq!(SetSpaceArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn set_space_requires_two_registers() {
        assert_eq!(
            SetSpaceArgs::decode(&[1]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

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
        assert_eq!(
            SetPriorityArgs::decode(&[256]),
            Err(KernelError::InvalidArgument)
        );
    }

    #[test]
    fn set_priority_insufficient_regs() {
        assert_eq!(
            SetPriorityArgs::decode(&[]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

    #[test]
    fn set_mcp_roundtrip() {
        let args = SetMCPriorityArgs { new_mcp: 64 };
        assert_eq!(SetMCPriorityArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn set_mcp_out_of_range() {
        assert_eq!(
            SetMCPriorityArgs::decode(&[256]),
            Err(KernelError::InvalidArgument)
        );
    }

    #[test]
    fn set_mcp_insufficient_regs() {
        assert_eq!(
            SetMCPriorityArgs::decode(&[]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

    // -- D3: SetIPCBuffer --

    #[test]
    fn set_ipc_buffer_roundtrip() {
        let args = SetIPCBufferArgs { buffer_addr: 1024 };
        assert_eq!(SetIPCBufferArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn set_ipc_buffer_aligned() {
        let args = SetIPCBufferArgs::decode(&[2048]).unwrap();
        assert_eq!(args.buffer_addr, 2048);
    }

    #[test]
    fn set_ipc_buffer_unaligned_decodes() {
        // The alignment is the operation's check, after the frame capability.
        assert_eq!(SetIPCBufferArgs::decode(&[513]).unwrap().buffer_addr, 513);
        assert_eq!(
            SetIPCBufferArgs::decode(&[0x1E00]).unwrap().buffer_addr,
            0x1E00
        );
    }

    #[test]
    fn set_ipc_buffer_zero() {
        // Zero is aligned (0 % 1024 == 0)
        let args = SetIPCBufferArgs::decode(&[0]).unwrap();
        assert_eq!(args.buffer_addr, 0);
    }

    #[test]
    fn set_ipc_buffer_insufficient_regs() {
        assert_eq!(
            SetIPCBufferArgs::decode(&[]),
            Err(KernelError::InvalidMessageInfo)
        );
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
        assert_eq!(
            SetAffinityArgs::decode(&[]),
            Err(KernelError::InvalidMessageInfo)
        );
    }
}
