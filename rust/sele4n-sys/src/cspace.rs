// SPDX-License-Identifier: GPL-3.0-or-later
//! CSpace operations — capability mint, copy, move, delete.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiCspaceMint`, `apiCspaceCopy`,
//! `apiCspaceMove`, `apiCspaceDelete`.

use sele4n_abi::args::cspace::*;
use sele4n_abi::{invoke_syscall, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{AccessRights, Badge, CPtr, KernelResult, Slot, SyscallId};

/// Mint a new capability with restricted rights and/or badge.
///
/// Lean: `apiCspaceMint` (API.lean) — requires `.grant` right on `cnode_cap`.
///
/// Creates a new capability in `dst_slot` derived from the capability in
/// `src_slot`, with rights restricted to `rights` and badge set to `badge`.
#[inline]
pub fn cspace_mint(
    cnode_cap: CPtr,
    src_slot: Slot,
    dst_slot: Slot,
    rights: AccessRights,
    badge: Badge,
) -> KernelResult<SyscallResponse> {
    let args = CSpaceMintArgs {
        src_slot,
        dst_slot,
        rights,
        badge,
    };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo::new_const(4, 0, 0),
        msg_regs: encoded,
        syscall_id: SyscallId::CSpaceMint,
    })
}

/// Copy a capability without modification.
///
/// Lean: `apiCspaceCopy` (API.lean) — requires `.grant` right on `cnode_cap`.
#[inline]
pub fn cspace_copy(
    cnode_cap: CPtr,
    src_slot: Slot,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    let args = CSpaceCopyArgs { src_slot, dst_slot };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo::new_const(2, 0, 0),
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::CSpaceCopy,
    })
}

/// Move a capability from one slot to another.
///
/// Lean: `apiCspaceMove` (API.lean) — requires `.grant` right on `cnode_cap`.
#[inline]
pub fn cspace_move(
    cnode_cap: CPtr,
    src_slot: Slot,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    let args = CSpaceMoveArgs { src_slot, dst_slot };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo::new_const(2, 0, 0),
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::CSpaceMove,
    })
}

/// Delete a capability from a slot.
///
/// Lean: `apiCspaceDelete` (API.lean) — requires `.write` right on `cnode_cap`.
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

/// Mint a delegable copy of a reply capability from `src_slot` into
/// `dst_slot` of the same CNode (PR #866 round-3 review: the wrapper the
/// ABI documented but never had).
///
/// Lean: the `.mintReplyCap` arm (API.lean, PR #822 Phase H) — requires
/// `.grant` on `cnode_cap`, and reuses the `cspaceCopy` register shape
/// (`decodeCSpaceCopyArgs`: srcSlot MR\[0\], dstSlot MR\[1\]).  Distinct
/// from `cspace_copy` because the kernel routes it through
/// `mintReplyCapWithCdt`, which validates that the source holds a reply
/// capability and records the CDT derivation.
#[inline]
pub fn mint_reply_cap(
    cnode_cap: CPtr,
    src_slot: Slot,
    dst_slot: Slot,
) -> KernelResult<SyscallResponse> {
    let args = CSpaceCopyArgs { src_slot, dst_slot };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo::new_const(2, 0, 0),
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::MintReplyCap,
    })
}
