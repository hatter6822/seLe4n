// SPDX-License-Identifier: GPL-3.0-or-later
//! Lifecycle operations — carving objects out of an untyped.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — the `.untypedRetype` arm
//! (`untypedRetypeFromCap`).  As in seL4, a carve through a capability with
//! no derivation child resets the untyped first, so there is no separate
//! reset call (WS-SX SX7.1).
//! WS-ZA ZA5.4 part 14 retired the in-place `lifecycle_retype` (syscall 8):
//! every object is carved from an untyped.

use sele4n_abi::args::{TypeTag, UntypedRetypeArgs};
use sele4n_abi::{invoke_syscall, IpcBuffer, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{CPtr, KernelResult, ObjId, SyscallId};

/// Where a retype puts the capabilities it hands back — seL4's destination
/// operands (WS-SX SX6.3, D9): `root` is a CNode capability in the caller's
/// CSpace, passed as the message's extra capability 0; `node_index` and
/// `node_depth` name the destination CNode under it (depth 0: `root` itself);
/// `node_offset` is the first slot of the window in that CNode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RetypeDestination {
    pub root: CPtr,
    pub node_index: CPtr,
    pub node_depth: u64,
    pub node_offset: u64,
}

/// Carve new objects out of an untyped the caller holds — seL4's
/// `seL4_Untyped_Retype`.
///
/// Lean: the `.untypedRetype` arm (API.lean, `untypedRetypeFromCap`), WS-BP
/// BP7.1.  Requires the `Retype` right on `untyped_cap`.  The kernel carves
/// `num_objects` objects of one kind, one after another from the untyped's
/// watermark, stores object `i` as object `child_id + i` — each of which must
/// hold no object yet — and installs a capability to object `i` in slot
/// `dst.node_offset + i` of the window `dst` names (WS-SX SX6.3, D9): every
/// slot empty (`TargetSlotOccupied` otherwise, before anything is written),
/// the count in `1..=`[`RETYPE_FAN_OUT_LIMIT`] and the window inside the CNode
/// (seL4's `RangeError` otherwise).  Every check precedes every write, so a
/// refused retype creates nothing.  No right is required of `dst.root`.  As in seL4
/// the message is the six words `type`, `size_bits`, `node_index`,
/// `node_depth`, `node_offset`, `num_objects`, then the model's `child_id`;
/// words 4 to 6 go in the IPC buffer's message registers 4 to 6 and `dst.root`
/// in `caps_or_badges[0]`.
///
/// Every kind is carved (WS-ZA ZA5.4 part 14), with seL4's sizes; the
/// accepted `size_bits` per kind are on [`UntypedRetypeArgs`].
/// [`TypeTag::Frame`]: one page (a device untyped yields a device frame),
/// zeroed if it is RAM, handed back with read, write and grant — the object
/// [`crate::vspace::vspace_map`] maps.  [`TypeTag::Untyped`]: a child untyped
/// of `2^size_bits` bytes, `size_bits` in [`MIN_UNTYPED_SIZE_BITS`,
/// `MAX_UNTYPED_SIZE_BITS`], handed back with read, write and retype.
/// [`TypeTag::VSpaceRoot`]: an address space on one zeroed RAM page under an
/// ASID the kernel picks, the least free one for each root in turn
/// (`ResourceExhausted` when fewer ASIDs are free than roots requested).
/// [`TypeTag::PageTable`]: one zeroed table page.  The other kernel objects —
/// [`TypeTag::Tcb`], [`TypeTag::Endpoint`], [`TypeTag::Notification`],
/// [`TypeTag::CNode`], [`TypeTag::Reply`] and [`TypeTag::SchedContext`] — are
/// carved at seL4's object sizes, each on a boundary of its own size (the
/// free index is rounded up to it, as seL4's `alignUp`), from RAM only (`UntypedDeviceRestriction` from a device
/// untyped), and handed back with every right but retype.  Every other
/// combination is `InvalidArgument`.
///
/// [`UntypedRetypeArgs`]: sele4n_abi::args::UntypedRetypeArgs
/// [`RETYPE_FAN_OUT_LIMIT`]: sele4n_abi::args::RETYPE_FAN_OUT_LIMIT
/// [`MIN_UNTYPED_SIZE_BITS`]: sele4n_abi::args::MIN_UNTYPED_SIZE_BITS
/// [`MAX_UNTYPED_SIZE_BITS`]: sele4n_abi::args::MAX_UNTYPED_SIZE_BITS
#[inline]
pub fn untyped_retype(
    untyped_cap: CPtr,
    type_tag: TypeTag,
    size_bits: u64,
    dst: RetypeDestination,
    num_objects: u64,
    child_id: ObjId,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    let args = UntypedRetypeArgs {
        new_type: type_tag,
        size_bits,
        node_index: dst.node_index,
        node_depth: dst.node_depth,
        node_offset: dst.node_offset,
        num_objects,
        child_id,
    };
    let encoded = args.encode();
    buf.set_mr(4, encoded[4])?;
    buf.set_mr(5, encoded[5])?;
    buf.set_mr(6, encoded[6])?;
    buf.caps_or_badges[0] = dst.root.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: untyped_cap,
        msg_info: MessageInfo::new_const(7, 1, 0),
        msg_regs: [encoded[0], encoded[1], encoded[2], encoded[3]],
        syscall_id: SyscallId::UntypedRetype,
        reply_cap: CPtr::NULL,
    })
}

/// Convenience: carve one frame out of `untyped_cap`.
pub fn untyped_retype_frame(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst: RetypeDestination,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    untyped_retype(untyped_cap, TypeTag::Frame, 0, dst, 1, child_id, buf)
}

/// Convenience: carve an address space — a VSpace root on its own zeroed table
/// page, under a fresh ASID — out of `untyped_cap` (WS-BP BP7.1 slice 4b).
pub fn untyped_retype_vspace_root(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst: RetypeDestination,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    untyped_retype(untyped_cap, TypeTag::VSpaceRoot, 0, dst, 1, child_id, buf)
}

/// Convenience: carve an intermediate page table — one zeroed page — out of
/// `untyped_cap` (WS-BP BP7.1), to install with
/// [`crate::vspace::page_table_map`].
pub fn untyped_retype_page_table(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst: RetypeDestination,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    untyped_retype(untyped_cap, TypeTag::PageTable, 0, dst, 1, child_id, buf)
}

/// Convenience: carve a thread out of `untyped_cap` (WS-ZA ZA5.4 part 14) —
/// in the carving core's domain, with that core as its affinity, no roots and
/// priority 0, as seL4's `createObject` makes one.
pub fn untyped_retype_tcb(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst: RetypeDestination,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    untyped_retype(untyped_cap, TypeTag::Tcb, 0, dst, 1, child_id, buf)
}

/// Convenience: carve an endpoint, both queues empty, out of `untyped_cap`.
pub fn untyped_retype_endpoint(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst: RetypeDestination,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    untyped_retype(untyped_cap, TypeTag::Endpoint, 0, dst, 1, child_id, buf)
}

/// Convenience: carve an idle notification out of `untyped_cap`.
pub fn untyped_retype_notification(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst: RetypeDestination,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    untyped_retype(untyped_cap, TypeTag::Notification, 0, dst, 1, child_id, buf)
}

/// Convenience: carve a reply object, with no caller, out of `untyped_cap`.
pub fn untyped_retype_reply(
    untyped_cap: CPtr,
    child_id: ObjId,
    dst: RetypeDestination,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    untyped_retype(untyped_cap, TypeTag::Reply, 0, dst, 1, child_id, buf)
}

/// Convenience: carve a child untyped of `2^size_bits` bytes out of
/// `untyped_cap` (WS-BP BP7.1 slice 4).
pub fn untyped_retype_untyped(
    untyped_cap: CPtr,
    size_bits: u64,
    child_id: ObjId,
    dst: RetypeDestination,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    untyped_retype(
        untyped_cap,
        TypeTag::Untyped,
        size_bits,
        dst,
        1,
        child_id,
        buf,
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
    dst: RetypeDestination,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    untyped_retype(
        untyped_cap,
        TypeTag::CNode,
        radix_bits,
        dst,
        1,
        child_id,
        buf,
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
    dst: RetypeDestination,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    untyped_retype(
        untyped_cap,
        TypeTag::SchedContext,
        size_bits,
        dst,
        1,
        child_id,
        buf,
    )
}
