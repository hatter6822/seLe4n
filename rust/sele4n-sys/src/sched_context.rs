// SPDX-License-Identifier: GPL-3.0-or-later
//! SchedContext operations — configure, bind, unbind — and the yield.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiSchedContextConfigure`,
//! `apiSchedContextBind`, `apiSchedContextUnbind`. Added in WS-Z Phase Z5.
//! Bind and unbind require `.write` on the SchedContext capability; configure
//! requires `.write` on a core's scheduling-control capability (WS-ZA ZA6.4).

use sele4n_abi::args::sched_context::*;
use sele4n_abi::{invoke_syscall, IpcBuffer, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{CPtr, KernelResult, SyscallId};

/// Configure a scheduling context's CBS parameters through a core's
/// scheduling control — seL4-MCS's `seL4_SchedControl_ConfigureFlags`.
///
/// Lean: the `.schedContextConfigure` arm (API.lean).  WS-ZA ZA6.4: the invoked
/// capability `sched_control` is a core's scheduling control (`.write`), the only
/// authority to set a budget and period; `sched_context` (MR\[0\]) is the address,
/// in the caller's own CSpace, of a `.write` capability to the context, resolved
/// by `resolveSchedControlConfigureTarget`.  A context bound to a thread homed on
/// another core is refused (`ThreadOnDifferentCore`).  Parameters: budget,
/// period, priority (≤255), deadline, domain (≤15); priority and domain travel
/// in one word (MR\[3\]).
///
/// This syscall requires 5 message registers, but ARM64 only provides 4
/// inline (x2–x5). The 5th value (`deadline`) is written to the IPC buffer's
/// overflow slot 0 (message register index 4), which the kernel reads at the
/// entry (`ipcBufferReadMrK`) on the register-routed path.
#[inline]
#[allow(clippy::too_many_arguments)]
pub fn sched_context_configure(
    sched_control: CPtr,
    sched_context: CPtr,
    budget: u64,
    period: u64,
    priority: u64,
    deadline: u64,
    domain: u64,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    let args = SchedContextConfigureArgs {
        sched_context,
        budget,
        period,
        priority,
        deadline,
        domain,
    };
    let encoded = args.encode();
    // The 5th word (the deadline) goes to the IPC buffer's overflow slot
    // (register index 4).  AK4-F (R-ABI-M04): `set_mr(4)` returns `Ok(())` on
    // success; overflow-slot write only.
    buf.set_mr(4, encoded[4])?;
    invoke_syscall(SyscallRequest {
        cap_addr: sched_control,
        msg_info: MessageInfo::new_const(5, 0, 0),
        msg_regs: [encoded[0], encoded[1], encoded[2], encoded[3]],
        syscall_id: SyscallId::SchedContextConfigure,
    })
}

/// Bind a scheduling context to a thread.
///
/// Lean: the `.schedContextBind` arm (API.lean) — requires `.write` on the
/// SchedContext capability **and** `.write` on a TCB capability the caller
/// holds: `tcb_cap` (MR\[0\]) is the capability address, in the caller's own
/// CSpace, of the thread to bind, resolved by the kernel through
/// `resolveSchedContextBindThread` (`v0.35.204`; a raw `ThreadId` until then,
/// which let a SchedContext-capability holder bind — and re-prioritise — any
/// thread it could name).  Same shape as `tcb_bind_notification`.
#[inline]
pub fn sched_context_bind(sc_cap: CPtr, tcb_cap: CPtr) -> KernelResult<SyscallResponse> {
    let args = SchedContextBindArgs { tcb_cap };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: sc_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::SchedContextBind,
    })
}

/// Unbind a scheduling context from its currently bound thread.
///
/// Lean: `apiSchedContextUnbind` (API.lean) — requires `.write` right.
/// Capability-only: no additional message registers needed.
#[inline]
pub fn sched_context_unbind(sc_cap: CPtr) -> KernelResult<SyscallResponse> {
    let _args = SchedContextUnbindArgs;
    invoke_syscall(SyscallRequest {
        cap_addr: sc_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::SchedContextUnbind,
    })
}

/// Give up the rest of the caller's allotment — seL4's `seL4_Yield` under MCS.
///
/// A thread bound to a scheduling context forfeits its remaining budget until
/// the next refill; an unbound thread ends its time slice and goes behind the
/// threads of its own priority.  The kernel then chooses again on the calling
/// core.  Invokes no capability: the capability address and message registers
/// are ignored.
///
/// Lean: `yieldOnCore` (Scheduler/Operations/Core.lean), WS-ZA ZA4.3.
#[inline]
pub fn yield_now() -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: CPtr::from(0u64),
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::Yield,
    })
}
