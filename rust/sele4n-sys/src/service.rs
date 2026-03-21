//! Service registry operations — register, revoke, query.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiServiceRegister`, `apiServiceRevoke`,
//! `apiServiceQuery`. Added in WS-Q1-D.

use sele4n_types::{CPtr, InterfaceId, ServiceId, KernelResult, SyscallId};
use sele4n_abi::{MessageInfo, SyscallRequest, SyscallResponse, invoke_syscall};
use sele4n_abi::args::service::*;

/// Register a service with the given interface specification.
///
/// Lean: `apiServiceRegister` (API.lean) — requires `.write` right.
///
/// Creates a service registration binding the caller's endpoint capability
/// to the specified interface specification.
#[must_use]
pub fn service_register(
    endpoint_cap: CPtr,
    interface_id: InterfaceId,
    method_count: u64,
    max_message_size: u64,
    max_response_size: u64,
    requires_grant: bool,
) -> KernelResult<SyscallResponse> {
    let args = ServiceRegisterArgs {
        interface_id,
        method_count,
        max_message_size,
        max_response_size,
        requires_grant,
    };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: endpoint_cap,
        msg_info: MessageInfo { length: 5, extra_caps: 0, label: 0 },
        // Pack 5 values into 4 inline regs + overflow via msg_info.length
        msg_regs: [encoded[0], encoded[1], encoded[2], encoded[3]],
        syscall_id: SyscallId::ServiceRegister,
    })
}

/// Revoke (unregister) a service by its ServiceId.
///
/// Lean: `apiServiceRevoke` (API.lean) — requires `.write` right.
#[must_use]
pub fn service_revoke(
    service_cap: CPtr,
    target_service: ServiceId,
) -> KernelResult<SyscallResponse> {
    let args = ServiceRevokeArgs { target_service };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: service_cap,
        msg_info: MessageInfo { length: 1, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::ServiceRevoke,
    })
}

/// Query services by capability (endpoint lookup).
///
/// Lean: `apiServiceQuery` (API.lean) — requires `.write` right.
/// No additional message registers — the endpoint object ID comes from
/// the capability target.
#[must_use]
pub fn service_query(
    endpoint_cap: CPtr,
) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: endpoint_cap,
        msg_info: MessageInfo { length: 0, extra_caps: 0, label: 0 },
        msg_regs: [0; 4],
        syscall_id: SyscallId::ServiceQuery,
    })
}
