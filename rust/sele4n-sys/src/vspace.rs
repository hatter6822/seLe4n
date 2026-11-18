// SPDX-License-Identifier: GPL-3.0-or-later
//! VSpace operations — map (with W^X enforcement) and unmap.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiVspaceMap`, `apiVspaceUnmap`.

use sele4n_abi::args::{PagePerms, PageTableMapArgs, VSpaceMapArgs, VSpaceUnifyInstructionArgs};
use sele4n_abi::{invoke_syscall, IpcBuffer, MessageInfo, SyscallRequest, SyscallResponse};
#[cfg(test)]
use sele4n_types::KernelError;
use sele4n_types::{Asid, CPtr, KernelResult, SyscallId, VAddr};

/// Map a frame into a virtual address space — seL4's `seL4_ARM_Page_Map`.
///
/// Lean: the `.vspaceMap` arm of `dispatchCapabilityOnly` (API.lean), through
/// `resolvePageMapOperands` and `vspaceMapOrRemapFromFrameCap`.
///
/// **Authority (WS-BP BP7.1, WS-SX SX6.3).**  The call is an invocation of
/// `frame_cap`, a capability to the **frame** being mapped — authority over
/// the memory: the page installed is that frame's own base, so a caller can
/// map only memory it holds a frame capability for.  The frame capability
/// must carry `.read` (every mapping is at least readable), and `.write` as
/// well for a writable mapping (`IllegalAuthority` otherwise).
/// `vspace_root` is the address, **in the caller's CSpace**, of a capability
/// to the address space (held with `Write`), sent as the message's extra
/// capability 0 (`caps_or_badges[0]` of `buf`, the caller's IPC buffer); a
/// message naming none is `TruncatedMessage`, and a root its own ASID does
/// not resolve to is `InvalidCapability`.  A **device** frame may be mapped
/// neither executable nor cacheable, and a **RAM** frame must be mapped
/// cacheable (`PolicyDenied` otherwise): set `PagePerms::CACHEABLE` exactly
/// when the frame is RAM.
///
/// The mapping is recorded on the frame capability that made it, so deleting
/// or revoking that capability unmaps it.  Mapping again through a capability
/// whose recorded mapping is in place is seL4's remap, at the same address
/// space and address only.
///
/// Enforces W^X: the WRITE and EXECUTE permission bits cannot both be set.
/// Returns `PolicyDenied` if the W^X constraint is violated.
#[inline]
pub fn vspace_map(
    frame_cap: CPtr,
    vspace_root: CPtr,
    vaddr: VAddr,
    perms: PagePerms,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    // W^X pre-check (client-side, before syscall)
    perms.validate_wx()?;

    let encoded = VSpaceMapArgs::from_perms(vaddr, perms).encode();
    buf.caps_or_badges[0] = vspace_root.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: frame_cap,
        msg_info: MessageInfo::new_const(3, 1, 0),
        msg_regs: [encoded[0], encoded[1], encoded[2], 0],
        syscall_id: SyscallId::VSpaceMap,
        reply_cap: CPtr::NULL,
    })
}

/// Install an intermediate page table — seL4's `seL4_ARM_PageTable_Map`.
///
/// `table_cap` names the table (held with `Write`); `vspace_root` is the
/// address, **in the caller's CSpace**, of a capability to the address space
/// (held with `Write`), sent as the message's extra capability 0
/// (`caps_or_badges[0]` of `buf`, the caller's IPC buffer); the words are
/// `vaddr` and seL4's attributes word (0).  A message naming no extra
/// capability is `TruncatedMessage`.  The table is installed at the
/// shallowest level the walk to `vaddr` is missing, so three calls make an
/// address mappable; a fourth is refused with `MappingConflict`.  A carved
/// address space maps a frame only where its walk is complete
/// (`TranslationFault` otherwise).
///
/// Lean: `pageTableMap` (Architecture/PageTableInstall.lean), dispatched as
/// `SyscallId.pageTableMap` in `API.lean` (WS-BP BP7.1, WS-SX SX6.3).
#[inline]
pub fn page_table_map(
    table_cap: CPtr,
    vspace_root: CPtr,
    vaddr: VAddr,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    let args = PageTableMapArgs {
        vaddr: vaddr.raw(),
        attr: 0,
    };
    let encoded = args.encode();
    buf.caps_or_badges[0] = vspace_root.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: table_cap,
        msg_info: MessageInfo::new_const(2, 1, 0),
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::PageTableMap,
        reply_cap: CPtr::NULL,
    })
}

/// Take an intermediate page table out of its address space — seL4's
/// `seL4_ARM_PageTable_Unmap`.  Refused with `RevocationRequired` while a
/// mapping or a deeper table still passes through it.
///
/// Lean: `pageTableUnmap` (Architecture/PageTableInstall.lean), WS-BP BP7.1.
#[inline]
pub fn page_table_unmap(table_cap: CPtr) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: table_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0, 0, 0, 0],
        syscall_id: SyscallId::PageTableUnmap,
        reply_cap: CPtr::NULL,
    })
}

/// Unmap the page a frame capability mapped — seL4's `seL4_ARM_Page_Unmap`.
///
/// Invoked on the frame capability with no message word: the kernel removes
/// the mapping that capability records (only while the address still maps
/// that frame) and clears the record.  A capability that records no mapping
/// unmaps nothing and succeeds.
///
/// Lean: `vspaceUnmapFrameCap` (Capability/FrameFinalise.lean), the `.vspaceUnmap`
/// arm of `dispatchCapabilityOnly` (API.lean) — requires `.read` on `frame_cap`.
#[inline]
pub fn vspace_unmap(frame_cap: CPtr) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: frame_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0, 0, 0, 0],
        syscall_id: SyscallId::VSpaceUnmap,
        reply_cap: CPtr::NULL,
    })
}

/// **WS-SM SM7.D**: publish freshly written instructions — unify the data and
/// instruction views of one mapped page.
///
/// Lean: `Architecture.vspaceUnifyInstructionPage` (PerCoreCacheModel.lean),
/// live through `API.dispatchWithCapChecked`.  seLe4n's equivalent of seL4's
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
/// Fails closed with `TranslationFault` if `vaddr` is not mapped in that address
/// space, so it can only maintain memory the caller already has a translation
/// for.
///
/// **An unbound `asid` returns `IllegalAuthority`, not `AsidNotBound`.** The
/// capability binding runs first and treats an ASID that resolves to no VSpace
/// root as authorized by no capability — deliberately, so the unauthorized path
/// cannot be used as an ASID-existence oracle. Callers matching on the error
/// should expect `IllegalAuthority` for both "wrong address space" and
/// "no such address space".
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
        reply_cap: CPtr::NULL,
    })
}

/// Convenience: map a read-only page of RAM.
pub fn vspace_map_read_only(
    frame_cap: CPtr,
    vspace_root: CPtr,
    vaddr: VAddr,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    vspace_map(
        frame_cap,
        vspace_root,
        vaddr,
        PagePerms::READ | PagePerms::CACHEABLE,
        buf,
    )
}

/// Convenience: map a read-write page of RAM.
pub fn vspace_map_read_write(
    frame_cap: CPtr,
    vspace_root: CPtr,
    vaddr: VAddr,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    vspace_map(
        frame_cap,
        vspace_root,
        vaddr,
        PagePerms::READ | PagePerms::WRITE | PagePerms::CACHEABLE,
        buf,
    )
}

/// Convenience: map a read-execute page (code) of RAM.
pub fn vspace_map_read_execute(
    frame_cap: CPtr,
    vspace_root: CPtr,
    vaddr: VAddr,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    vspace_map(
        frame_cap,
        vspace_root,
        vaddr,
        PagePerms::READ | PagePerms::EXECUTE | PagePerms::CACHEABLE,
        buf,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wx_violation_rejected() {
        let wx = PagePerms::WRITE | PagePerms::EXECUTE;
        let mut buf = IpcBuffer::new();
        let result = vspace_map(
            CPtr::from(1u64),
            CPtr::from(2u64),
            VAddr::from(0x1000u64),
            wx,
            &mut buf,
        );
        assert_eq!(result, Err(KernelError::PolicyDenied));
    }
}
