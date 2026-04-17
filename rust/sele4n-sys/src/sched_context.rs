//! SchedContext operations — configure, bind, unbind.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiSchedContextConfigure`,
//! `apiSchedContextBind`, `apiSchedContextUnbind`. Added in WS-Z Phase Z5.
//! All require `.write` right on the target SchedContext capability.

use sele4n_types::{CPtr, KernelResult, SyscallId, ThreadId};
use sele4n_abi::{MessageInfo, SyscallRequest, SyscallResponse, IpcBuffer, invoke_syscall};
use sele4n_abi::args::sched_context::*;

/// Configure a scheduling context's CBS parameters.
///
/// Lean: `apiSchedContextConfigure` (API.lean) — requires `.write` right.
/// Parameters: budget, period, priority (≤255), deadline, domain (≤15).
///
/// Domain is validated at the ABI decode boundary against
/// `numDomainsVal = 16` (zero-indexed 0..=15).
///
/// This syscall requires 5 message registers, but ARM64 only provides 4
/// inline (x2–x5). The 5th value (`domain`) is written to the IPC buffer's
/// overflow slot 0 (message register index 4).
///
/// AK4-A (R-ABI-C01): The kernel merges the IPC-buffer overflow into
/// `msgRegs` via `decodeSyscallArgsFromState` (RegisterDecode.lean),
/// which reads `ipcBufferReadMr 0` when `msgInfo.length > 4`. The
/// per-syscall decoder `decodeSchedContextConfigureArgs` then consumes
/// `msgRegs[4]` (the merged `domain` value) via `requireMsgReg`.
#[inline]
pub fn sched_context_configure(
    sc_cap: CPtr,
    budget: u64,
    period: u64,
    priority: u64,
    deadline: u64,
    domain: u64,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    let args = SchedContextConfigureArgs {
        budget,
        period,
        priority,
        deadline,
        domain,
    };
    let encoded = args.encode();
    // Write 5th parameter (domain) to IPC buffer overflow slot (register index 4).
    // Per Lean SyscallArgDecode.lean:958-962, the kernel reads:
    //   budget=msgRegs[0], period=msgRegs[1], priority=msgRegs[2],
    //   deadline=msgRegs[3], domain=msgRegs[4]
    // With 4 inline registers (x2-x5), msgRegs[4] requires IPC buffer.
    // AK4-F (R-ABI-M04): `set_mr(4)` now returns `Ok(())` on success
    // (was `Ok(true)` / `Ok(false)`); overflow-slot write only.
    buf.set_mr(4, encoded[4])?;
    invoke_syscall(SyscallRequest {
        cap_addr: sc_cap,
        msg_info: MessageInfo::new_const(5, 0, 0),
        msg_regs: [encoded[0], encoded[1], encoded[2], encoded[3]],
        syscall_id: SyscallId::SchedContextConfigure,
    })
}

/// Bind a scheduling context to a thread.
///
/// Lean: `apiSchedContextBind` (API.lean) — requires `.write` right.
/// The thread is identified by its ThreadId passed in MR[0].
#[inline]
pub fn sched_context_bind(
    sc_cap: CPtr,
    thread_id: ThreadId,
) -> KernelResult<SyscallResponse> {
    let args = SchedContextBindArgs { thread_id };
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
pub fn sched_context_unbind(
    sc_cap: CPtr,
) -> KernelResult<SyscallResponse> {
    let _args = SchedContextUnbindArgs;
    invoke_syscall(SyscallRequest {
        cap_addr: sc_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::SchedContextUnbind,
    })
}
