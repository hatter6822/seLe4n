// SPDX-License-Identifier: GPL-3.0-or-later
//! TCB (Thread Control Block) operations — suspend, resume, priority, IPC buffer,
//! CPU affinity.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — D1 (suspend/resume), D2 (priority),
//! D3 (IPC buffer), WS-SM SM5.H.4 (CPU affinity). All require `.write` right on the
//! target TCB capability.

use sele4n_abi::args::tcb::*;
use sele4n_abi::{invoke_syscall, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{CPtr, KernelResult, SyscallId};

/// Suspend a thread (transition to Inactive state).
///
/// Lean: `suspendThread` (Lifecycle/Suspend.lean) — requires `.write` right.
/// Capability-only: no additional message registers needed.
#[inline]
pub fn tcb_suspend(tcb_cap: CPtr) -> KernelResult<SyscallResponse> {
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
pub fn tcb_resume(tcb_cap: CPtr) -> KernelResult<SyscallResponse> {
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
pub fn tcb_set_priority(tcb_cap: CPtr, new_priority: u64) -> KernelResult<SyscallResponse> {
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
pub fn tcb_set_mcp(tcb_cap: CPtr, new_mcp: u64) -> KernelResult<SyscallResponse> {
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
pub fn tcb_set_ipc_buffer(tcb_cap: CPtr, buffer_addr: u64) -> KernelResult<SyscallResponse> {
    let args = SetIPCBufferArgs { buffer_addr };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::TcbSetIPCBuffer,
    })
}

/// Set a thread's CPU affinity and migrate it to its new home core (WS-SM SM5.H.4).
///
/// `affinity_raw` values `0 .. numCores-1` bind the target to that core; the marker
/// `numCores` (4 on RPi5) unbinds it (runs on any core).  Requires the `.write` right
/// on the target TCB capability.
///
/// Lean: `setThreadCpuAffinityOp` (Scheduler/Operations/Core.lean), dispatched as
/// `SyscallId.tcbSetAffinity` in `API.lean`.
#[inline]
pub fn tcb_set_affinity(tcb_cap: CPtr, affinity_raw: u64) -> KernelResult<SyscallResponse> {
    let args = SetAffinityArgs { affinity_raw };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::TcbSetAffinity,
    })
}

/// Install a thread's fault handler (PR #887 review) — seL4's
/// `seL4_TCB_SetSpace` fault endpoint, as its own invocation.
///
/// `handler_cptr` is a CPtr **in the target thread's CSpace** naming an
/// endpoint capability with send and grant or grant-reply; the kernel
/// validates it at set time (`setThreadFaultHandlerOp`, the same resolution
/// the fault path runs) and refuses a CPtr that would not deliver, so a
/// misconfiguration surfaces here rather than as a suspended thread later.
/// Requires `.write` on the target TCB capability.
///
/// Lean: `setThreadFaultHandlerOp` (IPC/Operations/Fault.lean), dispatched as
/// `SyscallId.tcbSetFaultHandler` in `API.lean`.
#[inline]
pub fn tcb_set_fault_handler(tcb_cap: CPtr, handler_cptr: u64) -> KernelResult<SyscallResponse> {
    let args = SetFaultHandlerArgs { handler_cptr };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::TcbSetFaultHandler,
    })
}

/// Bind a notification object to a TCB (PR #866 round-3 review: the
/// wrapper the ABI documented but never had — the syscall was callable
/// only via hand-encoded requests, leaving it outside the prefilter
/// conformance sweep).
///
/// Lean: the `.tcbBindNotification` arm (API.lean, WS-SM SM6.B) —
/// requires `.write` on the target TCB capability, and the notification
/// is resolved through a **capability** in the caller's own CSpace
/// (`notification_cap`, MR\[0\]), not a raw object id: a TCB-cap holder
/// must also hold `.write` on the notification to redirect its signals.
#[inline]
pub fn tcb_bind_notification(
    tcb_cap: CPtr,
    notification_cap: CPtr,
) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [notification_cap.into(), 0, 0, 0],
        syscall_id: SyscallId::TcbBindNotification,
    })
}

/// Unbind the target TCB's bound notification (no-op error if none).
///
/// Lean: the `.tcbUnbindNotification` arm (API.lean, WS-SM SM6.B) —
/// requires `.write` on the target TCB capability; no message registers
/// (`decodeTcbUnbindNotificationArgs` reads none).
#[inline]
pub fn tcb_unbind_notification(tcb_cap: CPtr) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::TcbUnbindNotification,
    })
}
