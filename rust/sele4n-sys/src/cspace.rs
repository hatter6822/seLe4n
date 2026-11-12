// SPDX-License-Identifier: GPL-3.0-or-later
//! CSpace operations — capability mint, copy, move, delete.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiCspaceMint`, `apiCspaceCopy`,
//! `apiCspaceMove`, `apiCspaceDelete`, `apiCspaceRevoke`.

use sele4n_abi::args::cspace::*;
use sele4n_abi::{invoke_syscall, IpcBuffer, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{AccessRights, Badge, CPtr, KernelResult, Slot, SyscallId};

/// Mint a badged capability from the slot `slots` names in its source root
/// into the empty slot it names in `cnode_cap`'s CNode (seL4's
/// `seL4_CNode_Mint` addressing, [`CNodeOpArgs`]).
///
/// Lean: the `.cspaceMint` arm (API.lean) — requires `.grant` right on
/// `cnode_cap`.  The new capability's rights are the source's masked with
/// `rights` (seL4's `maskCapRights`: masking, never a refusal), and its badge
/// is `badge`.  The badge is the fifth word, written to the IPC buffer's
/// overflow slot 0 (message register 4).
#[inline]
pub fn cspace_mint(
    cnode_cap: CPtr,
    slots: CNodeOpArgs,
    rights: AccessRights,
    badge: Badge,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    let args = CSpaceMintArgs {
        copy: CSpaceCopyArgs { slots, rights },
        badge,
    };
    let encoded = args.encode();
    buf.set_mr(4, encoded[4])?;
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo::new_const(5, 0, 0),
        msg_regs: [encoded[0], encoded[1], encoded[2], encoded[3]],
        syscall_id: SyscallId::CSpaceMint,
    })
}

/// Copy a capability from the slot `slots` names in its source root into the
/// empty slot it names in `cnode_cap`'s CNode (seL4's `seL4_CNode_Copy`
/// addressing, [`CNodeOpArgs`]), its rights masked with `rights` (seL4's
/// copy takes a rights operand and masks with it; `AccessRights::ALL` copies
/// the capability unchanged).
///
/// Lean: the `.cspaceCopy` arm (API.lean) — requires `.grant` right on
/// `cnode_cap`.
#[inline]
pub fn cspace_copy(
    cnode_cap: CPtr,
    slots: CNodeOpArgs,
    rights: AccessRights,
) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo::new_const(4, 0, 0),
        msg_regs: CSpaceCopyArgs { slots, rights }.encode(),
        syscall_id: SyscallId::CSpaceCopy,
    })
}

/// Move a capability from the slot `slots` names in its source root into the
/// empty slot it names in `cnode_cap`'s CNode (seL4's `seL4_CNode_Move`
/// addressing, [`CNodeOpArgs`]).
///
/// Lean: `apiCspaceMove` (API.lean) — requires `.grant` right on `cnode_cap`.
#[inline]
pub fn cspace_move(cnode_cap: CPtr, slots: CNodeOpArgs) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo::new_const(4, 0, 0),
        msg_regs: slots.encode(),
        syscall_id: SyscallId::CSpaceMove,
    })
}

/// Delete a capability from a slot.
///
/// Lean: `apiCspaceDelete` (API.lean) — requires `.write` right on `cnode_cap`.
///
/// Deleting a **frame** capability that made a mapping removes that mapping
/// (the `.cspaceDelete` arm runs `cspaceDeleteSlotFinalising`, seL4's
/// `finaliseCap` → `unmapPage`).  A mapping recorded on the capability that is
/// no longer in place — the address was unmapped through a VSpace capability
/// since — removes nothing.
///
/// A slot with derived capabilities is deleted like any other: they stay, now
/// derived from the deleted capability's own parent (seL4's `cteDelete`), so a
/// revoke of that parent still reaches them.
#[inline]
pub fn cspace_delete(cnode_cap: CPtr, target_slot: Slot) -> KernelResult<SyscallResponse> {
    let args = CSpaceDeleteArgs { target_slot };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::CSpaceDelete,
    })
}

/// Revoke every capability derived from the one in `target_slot`.
///
/// Lean: the `.cspaceRevoke` arm (API.lean, WS-RR RR8.16) — requires `.write`
/// on `cnode_cap`, and routes to `cspaceRevokeCdtFinalising`, seL4's
/// `cteRevoke`: it deletes and finalises the slot's first CDT child until it
/// has none, across *arbitrary* CSpaces rather than only the containing CNode.
///
/// The source slot itself **survives**: revocation destroys a capability's
/// derivations, not the capability, which is what distinguishes it from
/// `cspace_delete`.  It takes
/// the delete's register shape (`decodeCSpaceDeleteArgs`: targetSlot MR\[0\]),
/// since both name one slot of the invoked CNode.  Every mapping a destroyed
/// frame capability made is removed with it (`cspaceRevokeCdtFinalising`).
#[inline]
pub fn cspace_revoke(cnode_cap: CPtr, target_slot: Slot) -> KernelResult<SyscallResponse> {
    let args = CSpaceDeleteArgs { target_slot };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::CspaceRevoke,
    })
}

/// Mint a delegable copy of a reply capability from `src_slot` into
/// `dst_slot` of the same CNode (PR #866 round-3 review: the wrapper the
/// ABI documented but never had).
///
/// Lean: the `.mintReplyCap` arm (API.lean, PR #822 Phase H) — requires
/// `.grant` on `cnode_cap`; its two slots are the invoked CNode's
/// (`decodeMintReplyCapArgs`: srcSlot MR\[0\], dstSlot MR\[1\]).  Distinct
/// from `cspace_copy` because the kernel routes it through
/// `mintReplyCapWithCdt`, which validates that the source holds a reply
/// capability and records the CDT derivation.
#[inline]
pub fn mint_reply_cap(
    cnode_cap: CPtr,
    src_slot: Slot,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    let args = MintReplyCapArgs { src_slot, dst_slot };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo::new_const(2, 0, 0),
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::MintReplyCap,
    })
}
