//! CSpace operations — capability mint, copy, move, delete.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiCspaceMint`, `apiCspaceCopy`,
//! `apiCspaceMove`, `apiCspaceDelete`.

use sele4n_types::{CPtr, Slot, Badge, AccessRights, KernelResult, SyscallId};
use sele4n_abi::{MessageInfo, SyscallRequest, SyscallResponse, invoke_syscall};
use sele4n_abi::args::cspace::*;

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
    let args = CSpaceMintArgs { src_slot, dst_slot, rights, badge };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo { length: 4, extra_caps: 0, label: 0 },
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
        msg_info: MessageInfo { length: 2, extra_caps: 0, label: 0 },
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
        msg_info: MessageInfo { length: 2, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::CSpaceMove,
    })
}

/// Delete a capability from a slot.
///
/// Lean: `apiCspaceDelete` (API.lean) — requires `.write` right on `cnode_cap`.
#[inline]
pub fn cspace_delete(
    cnode_cap: CPtr,
    target_slot: Slot,
) -> KernelResult<SyscallResponse> {
    let args = CSpaceDeleteArgs { target_slot };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: cnode_cap,
        msg_info: MessageInfo { length: 1, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::CSpaceDelete,
    })
}
