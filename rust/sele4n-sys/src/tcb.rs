// SPDX-License-Identifier: GPL-3.0-or-later
//! TCB (Thread Control Block) operations — suspend, resume, priority, IPC buffer,
//! CPU affinity.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — D1 (suspend/resume), D2 (priority),
//! D3 (IPC buffer), WS-SM SM5.H.4 (CPU affinity). All require `.write` right on the
//! target TCB capability.

use sele4n_abi::args::tcb::*;
use sele4n_abi::{invoke_syscall, IpcBuffer, MessageInfo, SyscallRequest, SyscallResponse};
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
        reply_cap: CPtr::NULL,
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
        reply_cap: CPtr::NULL,
    })
}

/// Set a thread's scheduling priority — seL4's `seL4_TCB_SetPriority`.
///
/// `authority` is a thread capability address **in the caller's CSpace**; it is
/// the message's extra capability 0 (`caps_or_badges[0]`), and the new priority
/// must not exceed that thread's maximum controlled priority.  No extra
/// capability is `TruncatedMessage`; one that is not a thread capability is
/// `InvalidCapability` (cap number 1).  Requires `.write` on `tcb_cap`.
///
/// Lean: `setPriorityOnCore` (SchedContext/PriorityManagementPerCore.lean),
/// with the authority resolved by `resolvePriorityAuthority` (API.lean).
#[inline]
pub fn tcb_set_priority(
    tcb_cap: CPtr,
    authority: CPtr,
    new_priority: u64,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    let args = SetPriorityArgs { new_priority };
    let encoded = args.encode();
    buf.caps_or_badges[0] = authority.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(1, 1, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::TcbSetPriority,
        reply_cap: CPtr::NULL,
    })
}

/// Set a thread's maximum controlled priority (MCP) — seL4's
/// `seL4_TCB_SetMCPriority`.
///
/// `authority` is a thread capability address in the caller's CSpace, the
/// message's extra capability 0, whose maximum controlled priority bounds the
/// new one, as for [`tcb_set_priority`].  Requires `.write` on `tcb_cap`.
///
/// Lean: `setMCPriorityOnCore` (SchedContext/PriorityManagementPerCore.lean).
#[inline]
pub fn tcb_set_mcp(
    tcb_cap: CPtr,
    authority: CPtr,
    new_mcp: u64,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    let args = SetMCPriorityArgs { new_mcp };
    let encoded = args.encode();
    buf.caps_or_badges[0] = authority.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(1, 1, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::TcbSetMCPriority,
        reply_cap: CPtr::NULL,
    })
}

/// Set a thread's IPC buffer — seL4's `seL4_TCB_SetIPCBuffer`.
///
/// `buffer_frame` is a capability address **in the caller's CSpace** naming
/// the buffer's frame; it is the message's extra capability 0
/// (`caps_or_badges[0]`).  For a nonzero `buffer_addr` the kernel derives it,
/// refuses anything but a non-device frame (`IllegalOperation`) and an address
/// not aligned to `IPC_BUFFER_ALIGNMENT` (`AlignmentError`), and installs the
/// derived capability in the thread's buffer slot; a zero `buffer_addr`
/// empties the slot.  The thread need not be suspended.  Requires `.write`
/// on `tcb_cap`.
///
/// Lean: `setIPCBufferOp` (Architecture/IpcBufferValidation.lean).
#[inline]
pub fn tcb_set_ipc_buffer(
    tcb_cap: CPtr,
    buffer_addr: u64,
    buffer_frame: CPtr,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    let args = SetIPCBufferArgs { buffer_addr };
    let encoded = args.encode();
    buf.caps_or_badges[0] = buffer_frame.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(1, 1, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::TcbSetIPCBuffer,
        reply_cap: CPtr::NULL,
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
        reply_cap: CPtr::NULL,
    })
}

/// Set a suspended thread's fault endpoint, CSpace root and VSpace root —
/// seL4-MCS's `TCB_SetSpace`.
///
/// The three capabilities travel as the message's extra capabilities,
/// addressed **in the caller's CSpace** through `caps_or_badges` of `buf`, the
/// caller's IPC buffer: extra cap 0 is `fault_ep`, copied into the thread's
/// fault-handler slot (an endpoint capability with send and grant or
/// grant-reply; an empty slot clears the handler), extra cap 1 the new CSpace
/// root (a CNode) and extra cap 2 the new VSpace root — for instance one
/// carved from an untyped.  Fewer than three extra capabilities is
/// `TruncatedMessage`.  Requires `.write` on the target TCB capability, and the
/// target must be suspended (`IllegalState` otherwise).  `cspace_root_data` is
/// seL4's `cspace_root_data`: zero keeps the source capability's guard; a
/// nonzero word sets the new root's guard and guard size (`updateCapData`).
/// `vspace_root_data` is seL4's `vspace_root_data`, which AArch64 leaves the
/// VSpace root capability unchanged by.
///
/// Lean: `copyThreadSpacesZombie` (Capability/FrameFinalise.lean) over
/// `copyThreadSpaces` (Lifecycle/Operations/SetSpace.lean), dispatched as
/// `SyscallId.tcbSetSpace` in `API.lean`.
#[inline]
pub fn tcb_set_space(
    tcb_cap: CPtr,
    fault_ep: CPtr,
    cspace_root: CPtr,
    vspace_root: CPtr,
    cspace_root_data: u64,
    vspace_root_data: u64,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    let args = SetSpaceArgs {
        cspace_root_data,
        vspace_root_data,
    };
    let encoded = args.encode();
    buf.caps_or_badges[SetSpaceArgs::FAULT_EP_EXTRA_CAP] = fault_ep.raw();
    buf.caps_or_badges[SetSpaceArgs::CSPACE_ROOT_EXTRA_CAP] = cspace_root.raw();
    buf.caps_or_badges[SetSpaceArgs::VSPACE_ROOT_EXTRA_CAP] = vspace_root.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(2, SetSpaceArgs::EXTRA_CAPS as u8, 0),
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::TcbSetSpace,
        reply_cap: CPtr::NULL,
    })
}

/// Bind a notification object to a TCB (PR #866 round-3 review: the
/// wrapper the ABI documented but never had — the syscall was callable
/// only via hand-encoded requests, leaving it outside the prefilter
/// conformance sweep).
///
/// Lean: the `.tcbBindNotification` arm (API.lean, WS-SM SM6.B) —
/// requires `.write` on the target TCB capability, and the notification
/// is resolved through a **capability** in the caller's own CSpace, not a raw
/// object id: a TCB-cap holder must also hold `.write` on the notification to
/// redirect its signals.  `notification_cap` is the message's extra capability
/// 0 (`caps_or_badges[0]` of `buf`, the caller's IPC buffer), as seL4's
/// `seL4_TCB_BindNotification` passes it; no message word is sent, and no
/// extra capability is `TruncatedMessage`.
#[inline]
pub fn tcb_bind_notification(
    tcb_cap: CPtr,
    notification_cap: CPtr,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    buf.caps_or_badges[0] = notification_cap.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(0, 1, 0),
        msg_regs: [0, 0, 0, 0],
        syscall_id: SyscallId::TcbBindNotification,
        reply_cap: CPtr::NULL,
    })
}

/// Unbind the target TCB's bound notification (no-op error if none).
///
/// Lean: the `.tcbUnbindNotification` arm (API.lean, WS-SM SM6.B) —
/// requires `.write` on the target TCB capability; no message registers
/// (the arm decodes no arguments).
#[inline]
pub fn tcb_unbind_notification(tcb_cap: CPtr) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: tcb_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::TcbUnbindNotification,
        reply_cap: CPtr::NULL,
    })
}
