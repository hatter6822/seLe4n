// SPDX-License-Identifier: GPL-3.0-or-later
//! Lifecycle operations — retype with type tag validation.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiLifecycleRetype`, and the
//! `.untypedRetype` arm (`untypedRetypeFromCap`).

use sele4n_abi::args::{LifecycleRetypeArgs, TypeTag, UntypedRetypeArgs};
use sele4n_abi::{invoke_syscall, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{CPtr, KernelResult, ObjId, Slot, SyscallId};

/// Carve a new object out of an untyped the caller holds — seL4's
/// `seL4_Untyped_Retype`.
///
/// Lean: the `.untypedRetype` arm (API.lean, `untypedRetypeFromCap`), WS-BP
/// BP7.1.  Requires the `Retype` right on `untyped_cap`.  The kernel places the
/// new object at the page on the untyped's watermark (a device untyped yields a
/// device frame), zeroes a RAM page, stores it as object `child_id` — which must
/// hold no object yet — and installs a capability to it (read, write, grant) at
/// `dst_slot` of the CNode `dst_cnode` names in the caller's CSpace; that
/// capability must carry `Write` and the slot must be empty and addressable.
///
/// Only [`TypeTag::Frame`] is carved; every other tag is `InvalidArgument`.  A
/// frame is the object [`crate::vspace::vspace_map`] maps: this is the only way
/// a thread comes to hold mappable memory.
#[inline]
pub fn untyped_retype(
    untyped_cap: CPtr,
    type_tag: TypeTag,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    let args = UntypedRetypeArgs {
        new_type: type_tag,
        child_id,
        dst_cnode,
        dst_slot,
    };
    invoke_syscall(SyscallRequest {
        cap_addr: untyped_cap,
        msg_info: MessageInfo::new_const(4, 0, 0),
        msg_regs: args.encode(),
        syscall_id: SyscallId::UntypedRetype,
    })
}

/// Convenience: carve one frame out of `untyped_cap`.
pub fn untyped_retype_frame(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    untyped_retype(untyped_cap, TypeTag::Frame, child_id, dst_cnode, dst_slot)
}

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
        new_type: type_tag,
        size,
    };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: untyped_cap,
        msg_info: MessageInfo::new_const(3, 0, 0),
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
pub fn retype_cnode(
    untyped_cap: CPtr,
    target: ObjId,
    radix_bits: u64,
) -> KernelResult<SyscallResponse> {
    lifecycle_retype(untyped_cap, target, TypeTag::CNode, radix_bits)
}

/// Convenience: retype to create a VSpaceRoot.
pub fn retype_vspace_root(untyped_cap: CPtr, target: ObjId) -> KernelResult<SyscallResponse> {
    lifecycle_retype(untyped_cap, target, TypeTag::VSpaceRoot, 0)
}
