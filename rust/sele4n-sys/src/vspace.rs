//! VSpace operations — map (with W^X enforcement) and unmap.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiVspaceMap`, `apiVspaceUnmap`.

use sele4n_types::{CPtr, Asid, VAddr, PAddr, KernelResult, SyscallId};
#[cfg(test)]
use sele4n_types::KernelError;
use sele4n_abi::{MessageInfo, SyscallRequest, SyscallResponse, invoke_syscall};
use sele4n_abi::args::{VSpaceMapArgs, VSpaceUnmapArgs, PagePerms};

/// Map a physical page into a virtual address space.
///
/// Lean: `apiVspaceMap` (API.lean) — requires `.write` right on `vspace_cap`.
///
/// Enforces W^X: the WRITE and EXECUTE permission bits cannot both be set.
/// Returns `PolicyDenied` if the W^X constraint is violated.
#[must_use]
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

    let args = VSpaceMapArgs { asid, vaddr, paddr, perms: perms.0 as u64 };
    let encoded = args.encode();
    invoke_syscall(SyscallRequest {
        cap_addr: vspace_cap,
        msg_info: MessageInfo { length: 4, extra_caps: 0, label: 0 },
        msg_regs: encoded,
        syscall_id: SyscallId::VSpaceMap,
    })
}

/// Unmap a page from a virtual address space.
///
/// Lean: `apiVspaceUnmap` (API.lean) — requires `.write` right on `vspace_cap`.
#[must_use]
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
        msg_info: MessageInfo { length: 2, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::VSpaceUnmap,
    })
}

/// Convenience: map a read-only page.
#[must_use]
pub fn vspace_map_read_only(
    vspace_cap: CPtr, asid: Asid, vaddr: VAddr, paddr: PAddr,
) -> KernelResult<SyscallResponse> {
    vspace_map(vspace_cap, asid, vaddr, paddr, PagePerms::READ)
}

/// Convenience: map a read-write page.
#[must_use]
pub fn vspace_map_read_write(
    vspace_cap: CPtr, asid: Asid, vaddr: VAddr, paddr: PAddr,
) -> KernelResult<SyscallResponse> {
    vspace_map(vspace_cap, asid, vaddr, paddr, PagePerms(PagePerms::READ.0 | PagePerms::WRITE.0))
}

/// Convenience: map a read-execute page (code).
#[must_use]
pub fn vspace_map_read_execute(
    vspace_cap: CPtr, asid: Asid, vaddr: VAddr, paddr: PAddr,
) -> KernelResult<SyscallResponse> {
    vspace_map(vspace_cap, asid, vaddr, paddr, PagePerms(PagePerms::READ.0 | PagePerms::EXECUTE.0))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wx_violation_rejected() {
        let wx = PagePerms(PagePerms::WRITE.0 | PagePerms::EXECUTE.0);
        let result = vspace_map(CPtr(1), Asid(1), VAddr(0x1000), PAddr(0x2000), wx);
        assert_eq!(result, Err(KernelError::PolicyDenied));
    }
}
