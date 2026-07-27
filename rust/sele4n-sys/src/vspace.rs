// SPDX-License-Identifier: GPL-3.0-or-later
//! VSpace operations — map (with W^X enforcement) and unmap.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiVspaceMap`, `apiVspaceUnmap`.

use sele4n_types::{CPtr, Asid, VAddr, PAddr, KernelResult, SyscallId};
#[cfg(test)]
use sele4n_types::KernelError;
use sele4n_abi::{MessageInfo, SyscallRequest, SyscallResponse, invoke_syscall};
use sele4n_abi::args::{VSpaceMapArgs, VSpaceUnmapArgs, VSpaceUnifyInstructionArgs, PagePerms};

/// Map a physical page into a virtual address space.
///
/// Lean: `apiVspaceMap` (API.lean) — requires `.write` right on `vspace_cap`.
///
/// Enforces W^X: the WRITE and EXECUTE permission bits cannot both be set.
/// Returns `PolicyDenied` if the W^X constraint is violated.
#[inline]
pub fn vspace_map(
    vspace_cap: CPtr,
    asid: Asid,
    vaddr: VAddr,
    paddr: PAddr,
    perms: PagePerms,
) -> KernelResult<SyscallResponse> {
    // W^X pre-check (client-side, before syscall)
    perms.validate_wx()?;

    let args = VSpaceMapArgs { asid, vaddr, paddr, perms };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: vspace_cap,
        msg_info: MessageInfo::new_const(4, 0, 0),
        msg_regs: encoded,
        syscall_id: SyscallId::VSpaceMap,
    })
}

/// Unmap a page from a virtual address space.
///
/// Lean: `apiVspaceUnmap` (API.lean) — requires `.write` right on `vspace_cap`.
#[inline]
pub fn vspace_unmap(
    vspace_cap: CPtr,
    asid: Asid,
    vaddr: VAddr,
) -> KernelResult<SyscallResponse> {
    let args = VSpaceUnmapArgs { asid, vaddr };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: vspace_cap,
        msg_info: MessageInfo::new_const(2, 0, 0),
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::VSpaceUnmap,
    })
}

/// **WS-SM SM7.D**: publish freshly written instructions — unify the data and
/// instruction views of one mapped page.
///
/// Lean: `Architecture.vspaceUnifyInstructionPage` (PerCoreCacheModel.lean),
/// live through `API.dispatchWithCap`.  seLe4n's equivalent of seL4's
/// `seL4_ARM_Page_Unify_Instruction`.
///
/// **When you need this.**  After writing code through a *writable* mapping — a
/// JIT emitting instructions, a loader or dynamic linker placing a segment —
/// the stores sit in the data cache, while an instruction fetch reads at the
/// Point of Unification.  Without this call the fetch may observe the *old*
/// contents of the page, even on the very core that performed the stores.  The
/// kernel cannot do it implicitly: it has no way to know when a writer has
/// finished emitting, and a JIT patching an already-mapped page never re-enters
/// a mapping operation at all.
///
/// **Authority.**  Requires the `.write` right on `vspace_cap`, and the
/// capability must name the VSpace root bound to `asid` — publishing code is
/// gated on being able to write it.  A capability for a different address space
/// is refused with `IllegalAuthority`.
///
/// Deliberately **not** gated on the mapping being executable: the writer holds
/// the *data* mapping, so requiring execute permission would make the operation
/// useless in exactly the case it exists for.
///
/// Fails closed with `AsidNotBound` if `asid` is unbound and `TranslationFault`
/// if `vaddr` is not mapped in that address space, so it can only maintain
/// memory the caller already has a translation for.
#[inline]
pub fn vspace_unify_instruction(
    vspace_cap: CPtr,
    asid: Asid,
    vaddr: VAddr,
) -> KernelResult<SyscallResponse> {
    let args = VSpaceUnifyInstructionArgs { asid, vaddr };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: vspace_cap,
        msg_info: MessageInfo::new_const(2, 0, 0),
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::VSpaceUnifyInstruction,
    })
}

/// Convenience: map a read-only page.
pub fn vspace_map_read_only(
    vspace_cap: CPtr, asid: Asid, vaddr: VAddr, paddr: PAddr,
) -> KernelResult<SyscallResponse> {
    vspace_map(vspace_cap, asid, vaddr, paddr, PagePerms::READ)
}

/// Convenience: map a read-write page.
pub fn vspace_map_read_write(
    vspace_cap: CPtr, asid: Asid, vaddr: VAddr, paddr: PAddr,
) -> KernelResult<SyscallResponse> {
    vspace_map(vspace_cap, asid, vaddr, paddr, PagePerms::READ | PagePerms::WRITE)
}

/// Convenience: map a read-execute page (code).
pub fn vspace_map_read_execute(
    vspace_cap: CPtr, asid: Asid, vaddr: VAddr, paddr: PAddr,
) -> KernelResult<SyscallResponse> {
    vspace_map(vspace_cap, asid, vaddr, paddr, PagePerms::READ | PagePerms::EXECUTE)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wx_violation_rejected() {
        let wx = PagePerms::WRITE | PagePerms::EXECUTE;
        let result = vspace_map(CPtr::from(1u64), Asid::from(1u64), VAddr::from(0x1000u64), PAddr::from(0x2000u64), wx);
        assert_eq!(result, Err(KernelError::PolicyDenied));
    }
}
