// SPDX-License-Identifier: GPL-3.0-or-later
//! Lifecycle operations — carving objects out of an untyped, and resetting it.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — the `.untypedRetype` arm
//! (`untypedRetypeFromCap`) and the `.untypedReset` arm (`untypedReset`).
//! WS-ZA ZA5.4 part 14 retired the in-place `lifecycle_retype` (syscall 8):
//! every object is carved from an untyped.

use sele4n_abi::args::{TypeTag, UntypedRetypeArgs};
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
/// Every kind is carved (WS-ZA ZA5.4 part 14), with seL4's sizes; the
/// accepted `size_bits` per kind are on [`UntypedRetypeArgs`].
/// [`TypeTag::Frame`]: one page (a device untyped yields a device frame),
/// zeroed if it is RAM, handed back with read, write and grant — the object
/// [`crate::vspace::vspace_map`] maps.  [`TypeTag::Untyped`]: a child untyped
/// of `2^size_bits` bytes, `size_bits` in [`MIN_UNTYPED_SIZE_BITS`,
/// `MAX_UNTYPED_SIZE_BITS`], handed back with read, write and retype.
/// [`TypeTag::VSpaceRoot`]: an address space on one zeroed RAM page under an
/// ASID the kernel picks (`ResourceExhausted` when every ASID is taken).
/// [`TypeTag::PageTable`]: one zeroed table page.  The other kernel objects —
/// [`TypeTag::Tcb`], [`TypeTag::Endpoint`], [`TypeTag::Notification`],
/// [`TypeTag::CNode`], [`TypeTag::Reply`] and [`TypeTag::SchedContext`] — are
/// carved at seL4's object sizes, each on a boundary of its own size (the
/// free index is rounded up to it, as seL4's `alignUp`), from RAM only (`UntypedDeviceRestriction` from a device
/// untyped), and handed back with every right but retype.  Every other
/// combination is `InvalidArgument`.
///
/// [`UntypedRetypeArgs`]: sele4n_abi::args::UntypedRetypeArgs
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

/// Convenience: carve an address space — a VSpace root on its own zeroed table
/// page, under a fresh ASID — out of `untyped_cap` (WS-BP BP7.1 slice 4b).
pub fn untyped_retype_vspace_root(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    untyped_retype(
        untyped_cap,
        TypeTag::VSpaceRoot,
        0,
        child_id,
        dst_cnode,
        dst_slot,
    )
}

/// Convenience: carve an intermediate page table — one zeroed page — out of
/// `untyped_cap` (WS-BP BP7.1), to install with
/// [`crate::vspace::page_table_map`].
pub fn untyped_retype_page_table(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    untyped_retype(
        untyped_cap,
        TypeTag::PageTable,
        0,
        child_id,
        dst_cnode,
        dst_slot,
    )
}

/// Convenience: carve a thread out of `untyped_cap` (WS-ZA ZA5.4 part 14) —
/// in the carving core's domain, with that core as its affinity, no roots and
/// priority 0, as seL4's `createObject` makes one.
pub fn untyped_retype_tcb(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    untyped_retype(untyped_cap, TypeTag::Tcb, 0, child_id, dst_cnode, dst_slot)
}

/// Convenience: carve an endpoint, both queues empty, out of `untyped_cap`.
pub fn untyped_retype_endpoint(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    untyped_retype(
        untyped_cap,
        TypeTag::Endpoint,
        0,
        child_id,
        dst_cnode,
        dst_slot,
    )
}

/// Convenience: carve an idle notification out of `untyped_cap`.
pub fn untyped_retype_notification(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    untyped_retype(
        untyped_cap,
        TypeTag::Notification,
        0,
        child_id,
        dst_cnode,
        dst_slot,
    )
}

/// Convenience: carve a CNode of `2^radix_bits` empty slots out of
/// `untyped_cap`, `radix_bits` in [`MIN_CNODE_RADIX_BITS`, `MAX_CNODE_RADIX_BITS`].
///
/// [`MIN_CNODE_RADIX_BITS`]: sele4n_abi::args::MIN_CNODE_RADIX_BITS
/// [`MAX_CNODE_RADIX_BITS`]: sele4n_abi::args::MAX_CNODE_RADIX_BITS
pub fn untyped_retype_cnode(
    untyped_cap: CPtr,
    radix_bits: u64,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    untyped_retype(
        untyped_cap,
        TypeTag::CNode,
        radix_bits,
        child_id,
        dst_cnode,
        dst_slot,
    )
}

/// Convenience: carve a reply object, with no caller, out of `untyped_cap`.
pub fn untyped_retype_reply(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    untyped_retype(
        untyped_cap,
        TypeTag::Reply,
        0,
        child_id,
        dst_cnode,
        dst_slot,
    )
}

/// Convenience: carve a scheduling context of `2^size_bits` bytes, with no
/// budget and no bound thread, out of `untyped_cap`; `size_bits` is at least
/// [`MIN_SCHED_CONTEXT_SIZE_BITS`].
///
/// [`MIN_SCHED_CONTEXT_SIZE_BITS`]: sele4n_abi::args::MIN_SCHED_CONTEXT_SIZE_BITS
pub fn untyped_retype_sched_context(
    untyped_cap: CPtr,
    size_bits: u64,
    child_id: ObjId,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    untyped_retype(
        untyped_cap,
        TypeTag::SchedContext,
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
