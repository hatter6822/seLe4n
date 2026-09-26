// SPDX-License-Identifier: GPL-3.0-or-later
//! Lifecycle operations — retype with type tag validation.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiLifecycleRetype`, and the
//! `.untypedRetype` arm (`untypedRetypeFromCap`), and the `.untypedReset` arm
//! (`untypedReset`).

use sele4n_abi::args::{LifecycleRetypeArgs, TypeTag, UntypedRetypeArgs};
use sele4n_abi::{invoke_syscall, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{CPtr, KernelResult, ObjId, Slot, SyscallId};

/// Carve a new object out of an untyped the caller holds — seL4's
/// `seL4_Untyped_Retype`.
///
/// Lean: the `.untypedRetype` arm (API.lean, `untypedRetypeFromCap`), WS-BP
/// BP7.1.  Requires the `Retype` right on `untyped_cap`.  The kernel places the
/// new object at the untyped's watermark, stores it as object `child_id` —
/// which must hold no object yet — and installs a capability to it at
/// `dst_slot` of the CNode `dst_cnode` names in the caller's CSpace; that
/// capability must carry `Write` and the slot must be empty and addressable.
///
/// Two kinds are carved.  [`TypeTag::Frame`] with `size_bits = 0`: one page (a
/// device untyped yields a device frame), zeroed if it is RAM, handed back with
/// read, write and grant — the object [`crate::vspace::vspace_map`] maps, and
/// the only way a thread comes to hold mappable memory.  [`TypeTag::Untyped`]
/// with `size_bits` in [`MIN_UNTYPED_SIZE_BITS`, `MAX_UNTYPED_SIZE_BITS`]: a
/// child untyped of `2^size_bits` bytes of the parent's memory kind, handed
/// back with read, write and retype, from which the holder carves in turn.
/// Every other combination is `InvalidArgument`.
///
/// [`MIN_UNTYPED_SIZE_BITS`]: sele4n_abi::args::MIN_UNTYPED_SIZE_BITS
/// [`MAX_UNTYPED_SIZE_BITS`]: sele4n_abi::args::MAX_UNTYPED_SIZE_BITS
#[inline]
pub fn untyped_retype(
    untyped_cap: CPtr,
    type_tag: TypeTag,
    size_bits: u64,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    let args = UntypedRetypeArgs {
        new_type: type_tag,
        size_bits,
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
    untyped_retype(
        untyped_cap,
        TypeTag::Frame,
        0,
        child_id,
        dst_cnode,
        dst_slot,
    )
}

/// Convenience: carve a child untyped of `2^size_bits` bytes out of
/// `untyped_cap` (WS-BP BP7.1 slice 4).
pub fn untyped_retype_untyped(
    untyped_cap: CPtr,
    size_bits: u64,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    untyped_retype(
        untyped_cap,
        TypeTag::Untyped,
        size_bits,
        child_id,
        dst_cnode,
        dst_slot,
    )
}

/// Hand an untyped's memory back to it — seL4's `resetUntypedCap`.
///
/// Lean: the `.untypedReset` arm (API.lean, `untypedReset`), WS-BP BP7.1.
/// Requires the `Retype` right on `untyped_cap`.  Refused with
/// `RevocationRequired` while any capability anywhere still names an object
/// carved from the untyped — at any depth, since a child untyped's own carves
/// are the untyped's memory too — so revoke the untyped capability first.  On
/// success every mapping of a page in the untyped's region is gone, every
/// carved frame and child untyped no longer exists, and the next
/// [`untyped_retype`] carves from the start of the region again.
#[inline]
pub fn untyped_reset(untyped_cap: CPtr) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: untyped_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::UntypedReset,
    })
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
