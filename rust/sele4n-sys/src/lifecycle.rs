//! Lifecycle operations — retype with type tag validation.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiLifecycleRetype`.

use sele4n_types::{CPtr, ObjId, KernelResult, SyscallId};
use sele4n_abi::{MessageInfo, SyscallRequest, SyscallResponse, invoke_syscall};
use sele4n_abi::args::{LifecycleRetypeArgs, TypeTag};

/// Retype an untyped memory object into a specific kernel object type.
///
/// Lean: `apiLifecycleRetype` (API.lean) — requires `.retype` right.
///
/// The `type_tag` specifies the target object type (0=TCB, 1=Endpoint,
/// 2=Notification, 3=CNode, 4=VSpaceRoot, 5=Untyped). The `size` is a
/// hint for variable-size objects (e.g., CNode radix width).
#[inline]
pub fn lifecycle_retype(
    untyped_cap: CPtr,
    target_obj: ObjId,
    type_tag: TypeTag,
    size: u64,
) -> KernelResult<SyscallResponse> {
    let args = LifecycleRetypeArgs {
        target_obj,
        new_type: type_tag.to_u64(),
        size,
    };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: untyped_cap,
        msg_info: MessageInfo { length: 3, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], encoded[1], encoded[2], 0],
        syscall_id: SyscallId::LifecycleRetype,
    })
}

/// Convenience: retype to create a TCB.
pub fn retype_tcb(untyped_cap: CPtr, target: ObjId) -> KernelResult<SyscallResponse> {
    lifecycle_retype(untyped_cap, target, TypeTag::Tcb, 0)
}

/// Convenience: retype to create an Endpoint.
pub fn retype_endpoint(untyped_cap: CPtr, target: ObjId) -> KernelResult<SyscallResponse> {
    lifecycle_retype(untyped_cap, target, TypeTag::Endpoint, 0)
}

/// Convenience: retype to create a Notification.
pub fn retype_notification(untyped_cap: CPtr, target: ObjId) -> KernelResult<SyscallResponse> {
    lifecycle_retype(untyped_cap, target, TypeTag::Notification, 0)
}

/// Convenience: retype to create a CNode with the given radix width.
pub fn retype_cnode(untyped_cap: CPtr, target: ObjId, radix_bits: u64) -> KernelResult<SyscallResponse> {
    lifecycle_retype(untyped_cap, target, TypeTag::CNode, radix_bits)
}

/// Convenience: retype to create a VSpaceRoot.
pub fn retype_vspace_root(untyped_cap: CPtr, target: ObjId) -> KernelResult<SyscallResponse> {
    lifecycle_retype(untyped_cap, target, TypeTag::VSpaceRoot, 0)
}
