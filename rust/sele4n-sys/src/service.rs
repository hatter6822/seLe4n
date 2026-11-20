// SPDX-License-Identifier: GPL-3.0-or-later
//! Service registry operations — register, revoke, query.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiServiceRegister`, `apiServiceRevoke`,
//! `apiServiceQuery`. Added in WS-Q1-D.
//!
//! All three are invocations of the **service-registry capability** (WS-SX
//! SX6.7), so no message label selects an operation on an endpoint (whose
//! Send and Call are IPC in seL4 whatever the label): the endpoint is the
//! message's extra capability 0 (`caps_or_badges[0]` of the caller's IPC
//! buffer, `resolveServiceEndpoint`), as seL4 passes an argument capability.

use sele4n_abi::args::service::*;
use sele4n_abi::{invoke_syscall, IpcBuffer, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{CPtr, InterfaceId, KernelResult, ServiceId, SyscallId};

/// Register a service with the given interface specification.
///
/// Lean: `apiServiceRegister` (API.lean) — requires the `.write` right on
/// the service-registry capability `registry_cap` and on the endpoint
/// capability `endpoint_cap`, extra capability 0.
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
#[allow(clippy::too_many_arguments)]
pub fn service_register(
    registry_cap: CPtr,
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
    buf.caps_or_badges[0] = endpoint_cap.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: registry_cap,
        msg_info: MessageInfo::new_const(5, 1, 0),
        msg_regs: [encoded[0], encoded[1], encoded[2], encoded[3]],
        syscall_id: SyscallId::ServiceRegister,
        reply_cap: CPtr::NULL,
    })
}

/// Revoke the service registered on an endpoint.
///
/// Lean: the `.serviceRevoke` arm (API.lean) — requires the `.write` right on
/// the service-registry capability and on the endpoint capability, extra
/// capability 0, and the checked dispatcher admits it only when the caller's
/// label flows to the endpoint's (`revokeServiceChecked`).  The kernel
/// removes the registration the endpoint records
/// (`revokeServiceByRecordedRegistration`): the capabilities are the
/// authority, and no message registers are read, so the caller names no
/// service.
#[inline]
pub fn service_revoke(
    registry_cap: CPtr,
    endpoint_cap: CPtr,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    buf.caps_or_badges[0] = endpoint_cap.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: registry_cap,
        msg_info: MessageInfo::new_const(0, 1, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::ServiceRevoke,
        reply_cap: CPtr::NULL,
    })
}

/// Query services by capability (endpoint lookup).
///
/// Lean: the `.serviceQuery` arm (API.lean) — requires the `.read` right on
/// the service-registry capability and on the endpoint capability, extra
/// capability 0, and the checked dispatcher admits it only when the
/// endpoint's label flows to the caller's (`lookupServiceChecked`).  No
/// message registers — the endpoint object ID comes from the extra
/// capability's target.
///
/// WS-RA RA.D.3: returns the resolved registration's **typed**
/// [`ServiceId`], constructed from the `x0` word — the answer the kernel
/// computed and, before the flip, discarded (`lookupServiceByCap`'s
/// result was thrown away and this wrapper handed back an opaque
/// `SyscallResponse` of the caller's own registers).  Staged by the
/// `.serviceQuery` arm via `returnFrameOfWord`.
///
/// PR #866 round-2 review: typed, not a bare `u64`, so callers cannot mix
/// the result with unrelated words (the project's typed-identifier
/// convention).  Both halves of the service API name the registration by
/// the endpoint that records it: `service_query(registry, ep, buf)` reads it
/// and `service_revoke(registry, ep, buf)` removes it.
#[inline]
pub fn service_query(
    registry_cap: CPtr,
    endpoint_cap: CPtr,
    buf: &mut IpcBuffer,
) -> KernelResult<ServiceId> {
    buf.caps_or_badges[0] = endpoint_cap.raw();
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: registry_cap,
        msg_info: MessageInfo::new_const(0, 1, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::ServiceQuery,
        reply_cap: CPtr::NULL,
    })?;
    Ok(ServiceId::from(resp.value()))
}
