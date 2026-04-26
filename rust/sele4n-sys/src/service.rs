// SPDX-License-Identifier: GPL-3.0-or-later
//! Service registry operations — register, revoke, query.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiServiceRegister`, `apiServiceRevoke`,
//! `apiServiceQuery`. Added in WS-Q1-D.

use sele4n_types::{CPtr, InterfaceId, ServiceId, KernelResult, SyscallId};
use sele4n_abi::{MessageInfo, SyscallRequest, SyscallResponse, IpcBuffer, invoke_syscall};
use sele4n_abi::args::service::*;

/// Register a service with the given interface specification.
///
/// Lean: `apiServiceRegister` (API.lean) — requires `.write` right.
///
/// This syscall requires 5 message registers, but ARM64 only provides 4
/// inline (x2–x5). The 5th value (`requires_grant`) is written to the
/// IPC buffer's overflow slot 0 (message register index 4).
///
/// AK4-A (R-ABI-C01): The kernel merges the IPC-buffer overflow into
/// `msgRegs` via `decodeSyscallArgsFromState` (RegisterDecode.lean),
/// which reads `ipcBufferReadMr 0` when `msgInfo.length > 4`. The
/// per-syscall decoder `decodeServiceRegisterArgs` then consumes
/// `msgRegs[4]` (the merged `requires_grant` value) via `requireMsgReg`,
/// and AK4-B strict validation rejects values ≥ 2.
#[inline]
pub fn service_register(
    endpoint_cap: CPtr,
    interface_id: InterfaceId,
    method_count: u64,
    max_message_size: u64,
    max_response_size: u64,
    requires_grant: bool,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    let args = ServiceRegisterArgs {
        interface_id,
        method_count,
        max_message_size,
        max_response_size,
        requires_grant,
    };
    let encoded = args.encode();
    // Write 5th parameter to IPC buffer overflow slot (register index 4)
    buf.set_mr(4, encoded[4])?;
    invoke_syscall(SyscallRequest {
        cap_addr: endpoint_cap,
        msg_info: MessageInfo::new_const(5, 0, 0),
        msg_regs: [encoded[0], encoded[1], encoded[2], encoded[3]],
        syscall_id: SyscallId::ServiceRegister,
    })
}

/// Revoke (unregister) a service by its ServiceId.
///
/// Lean: `apiServiceRevoke` (API.lean) — requires `.write` right.
#[inline]
pub fn service_revoke(
    service_cap: CPtr,
    target_service: ServiceId,
) -> KernelResult<SyscallResponse> {
    let args = ServiceRevokeArgs { target_service };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: service_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::ServiceRevoke,
    })
}

/// Query services by capability (endpoint lookup).
///
/// Lean: `apiServiceQuery` (API.lean) — requires `.read` right.
/// No additional message registers — the endpoint object ID comes from
/// the capability target.
#[inline]
pub fn service_query(
    endpoint_cap: CPtr,
) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: endpoint_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::ServiceQuery,
    })
}
