// SPDX-License-Identifier: GPL-3.0-or-later
//! SchedContext operations — configure, bind, unbind, consumed — and the yield.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiSchedContextConfigure`,
//! `apiSchedContextBind`, `apiSchedContextUnbind`. Added in WS-Z Phase Z5.
//! Bind and unbind require `.write` on the SchedContext capability; configure
//! is invoked on a core's scheduling-control capability (WS-ZA ZA6.4).

use sele4n_abi::args::sched_context::*;
use sele4n_abi::{invoke_syscall, IpcBuffer, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{CPtr, KernelResult, SyscallId};

/// Configure a scheduling context's CBS parameters through a core's
/// scheduling control — seL4-MCS's `seL4_SchedControl_ConfigureFlags`.
///
/// Lean: the `.schedContextConfigure` arm (API.lean).  WS-ZA ZA6.4: the invoked
/// capability `sched_control` is a core's scheduling control, the only
/// authority to set a budget and period.  WS-SX SX6.4: `sched_context` is the
/// message's extra capability 0 (`caps_or_badges[0]` of `buf`), the address,
/// in the caller's own CSpace, of a capability to the context, resolved by
/// `resolveSchedControlConfigureTarget`; no extra capability is
/// `TruncatedMessage`; as in seL4, the capability needs no right, only the
/// scheduling-context kind.  A context bound to a thread homed on another core
/// is moved, with its thread, to the control's core.  The words are seL4-MCS's:
/// budget, period, extra refills (at most `MAX_REFILLS - MIN_REFILLS`; the
/// context then holds up to `extra_refills + MIN_REFILLS` refills), badge, and
/// flags (bit 0 is `seL4_SchedContext_Sporadic`).
///
/// This syscall requires 5 message registers, but ARM64 only provides 4
/// inline (x2–x5). The 5th word (`flags`) is written to the IPC buffer's
/// overflow slot 0 (message register index 4), which the kernel reads at the
/// entry (`ipcBufferReadMrK`) on the register-routed path.
#[inline]
#[allow(clippy::too_many_arguments)]
pub fn sched_context_configure(
    sched_control: CPtr,
    sched_context: CPtr,
    budget: u64,
    period: u64,
    extra_refills: u64,
    badge: u64,
    flags: u64,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    let encoded = SchedContextConfigureArgs {
        budget,
        period,
        extra_refills,
        badge,
        flags,
    }
    .encode();
    // The 5th word (the flags) goes to the IPC buffer's overflow slot
    // (register index 4).  AK4-F (R-ABI-M04): `set_mr(4)` returns `Ok(())` on
    // success; overflow-slot write only.
    buf.set_mr(4, encoded[4])?;
    buf.caps_or_badges[0] = sched_context.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: sched_control,
        msg_info: MessageInfo::new_const(5, 1, 0),
        msg_regs: [encoded[0], encoded[1], encoded[2], encoded[3]],
        syscall_id: SyscallId::SchedContextConfigure,
        reply_cap: CPtr::NULL,
    })
}

/// Bind a scheduling context to a thread — seL4-MCS's `seL4_SchedContext_Bind`.
///
/// Lean: the `.schedContextBind` arm (API.lean) — requires `.write` on the
/// SchedContext capability **and** `.write` on a TCB capability the caller
/// holds: `tcb_cap` is the capability address, in the caller's own CSpace, of
/// the thread to bind, the message's extra capability 0 (`caps_or_badges[0]`
/// of `buf`, the caller's IPC buffer), resolved by the kernel through
/// `resolveSchedContextBindThread`.  No message word is sent; no extra
/// capability is `TruncatedMessage`.  Same shape as `tcb_bind_notification`.
#[inline]
pub fn sched_context_bind(
    sc_cap: CPtr,
    tcb_cap: CPtr,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    buf.caps_or_badges[0] = tcb_cap.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: sc_cap,
        msg_info: MessageInfo::new_const(0, 1, 0),
        msg_regs: [0, 0, 0, 0],
        syscall_id: SyscallId::SchedContextBind,
        reply_cap: CPtr::NULL,
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
        reply_cap: CPtr::NULL,
    })
}

/// Read and reset a scheduling context's consumed time — seL4's
/// `seL4_SchedContext_Consumed`.
///
/// The kernel returns the time the context has consumed since the last reading
/// (in timer ticks, saturated at a word) in the first message register and
/// resets it to zero.  Requires the `Write` right on the SchedContext
/// capability; no message registers are sent.
///
/// Lean: `schedContextConsumedOnCore` (SchedContext/YieldLink.lean), WS-ZA ZA6.9.
#[inline]
pub fn sched_context_consumed(sc_cap: CPtr) -> KernelResult<u64> {
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: sc_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::SchedContextConsumed,
        reply_cap: CPtr::NULL,
    })?;
    Ok(resp.msg_regs[0])
}

/// Yield to the thread bound to a scheduling context — seL4's
/// `seL4_SchedContext_YieldTo`.
///
/// The kernel refuses (`IllegalState`) a context with no bound thread, a
/// context bound to the caller, a bound thread whose priority exceeds the
/// caller's maximum controlled priority, and a caller with a yield pending.
/// Otherwise it resumes the context and, when its thread is schedulable, either
/// moves the thread to the head of its priority on its home core (a thread
/// homed on another core, or ranked below the caller) or, on the caller's own
/// core, runs it ahead of the caller, which waits at the head of its own
/// priority.  The consumed time returns in the first message register: at once
/// in the first case, when the caller next runs in the second.  Requires the
/// `Write` right on the SchedContext capability; no message registers are sent.
///
/// Lean: `schedContextYieldToOnCore` (SchedContext/Operations.lean), WS-ZA ZA6.29.
#[inline]
pub fn sched_context_yield_to(sc_cap: CPtr) -> KernelResult<u64> {
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: sc_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::SchedContextYieldTo,
        reply_cap: CPtr::NULL,
    })?;
    Ok(resp.msg_regs[0])
}

/// Give up the rest of the caller's allotment — seL4's `seL4_Yield` under MCS.
///
/// A thread bound to a scheduling context forfeits its remaining budget until
/// the next refill; an unbound thread ends its time slice and goes behind the
/// threads of its own priority.  The kernel then chooses again on the calling
/// core.  Invokes no capability: the capability address and message registers
/// are ignored.
///
/// Returns nothing, as libsel4's `seL4_Yield` returns `void`: the kernel writes
/// no register for a `Yield`.
///
/// Lean: `yieldOnCore` (Scheduler/Operations/Core.lean), WS-ZA ZA4.3.
#[inline]
pub fn yield_now() -> KernelResult<()> {
    invoke_syscall(SyscallRequest {
        cap_addr: CPtr::from(0u64),
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::Yield,
        reply_cap: CPtr::NULL,
    })
    .map(|_| ())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// WS-SX SX6.4: the context travels as extra capability 0 and the flags
    /// word as message register 4 (the IPC buffer's overflow slot 0).
    #[test]
    fn configure_names_the_context_as_extra_cap_zero() {
        let mut buf = IpcBuffer::new();
        let cap = CPtr::from(1u64);
        let sc = CPtr::from(2u64);
        let _ = sched_context_configure(cap, sc, 10, 100, 0, 77, 1, &mut buf);
        assert_eq!(buf.caps_or_badges[0], 2);
        assert_eq!(buf.get_mr(4), Ok(1));
    }
}
