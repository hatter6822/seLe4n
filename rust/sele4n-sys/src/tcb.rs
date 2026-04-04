//! TCB (Thread Control Block) operations — suspend, resume, priority, IPC buffer.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — D1 (suspend/resume), D2 (priority),
//! D3 (IPC buffer). All require `.write` right on the target TCB capability.

use sele4n_types::{CPtr, KernelResult, SyscallId};
use sele4n_abi::{MessageInfo, SyscallRequest, SyscallResponse, invoke_syscall};
use sele4n_abi::args::tcb::*;

/// Suspend a thread (transition to Inactive state).
///
/// Lean: `suspendThread` (Lifecycle/Suspend.lean) — requires `.write` right.
/// Capability-only: no additional message registers needed.
#[inline]
pub fn tcb_suspend(
    tcb_cap: CPtr,
) -> KernelResult<SyscallResponse> {
    let _args = SuspendArgs;
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::TcbSuspend,
    })
}

/// Resume a suspended thread (transition to Ready state).
///
/// Lean: `resumeThread` (Lifecycle/Suspend.lean) — requires `.write` right.
/// Capability-only: no additional message registers needed.
#[inline]
pub fn tcb_resume(
    tcb_cap: CPtr,
) -> KernelResult<SyscallResponse> {
    let _args = ResumeArgs;
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::TcbResume,
    })
}

/// Set a thread's scheduling priority.
///
/// Lean: `setPriorityOp` (SchedContext/PriorityManagement.lean) — requires
/// `.write` right. Priority must be ≤ 255 and bounded by the caller's MCP.
#[inline]
pub fn tcb_set_priority(
    tcb_cap: CPtr,
    new_priority: u64,
) -> KernelResult<SyscallResponse> {
    let args = SetPriorityArgs { new_priority };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::TcbSetPriority,
    })
}

/// Set a thread's maximum controlled priority (MCP).
///
/// Lean: `setMCPriorityOp` (SchedContext/PriorityManagement.lean) — requires
/// `.write` right. MCP must be ≤ 255.
#[inline]
pub fn tcb_set_mcp(
    tcb_cap: CPtr,
    new_mcp: u64,
) -> KernelResult<SyscallResponse> {
    let args = SetMCPriorityArgs { new_mcp };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::TcbSetMCPriority,
    })
}

/// Set a thread's IPC buffer address.
///
/// Lean: `setIPCBufferOp` (Architecture/IpcBufferValidation.lean) — requires
/// `.write` right. Address must be aligned to 512 bytes (seL4 convention).
#[inline]
pub fn tcb_set_ipc_buffer(
    tcb_cap: CPtr,
    buffer_addr: u64,
) -> KernelResult<SyscallResponse> {
    let args = SetIPCBufferArgs { buffer_addr };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::TcbSetIPCBuffer,
    })
}
