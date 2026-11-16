// SPDX-License-Identifier: GPL-3.0-or-later
//! VSpace syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 117–131.

use crate::args::PagePerms;
use sele4n_types::{Asid, KernelError, KernelResult, VAddr};

/// Arguments for `vspaceMap` (syscall 9) — seL4's `seL4_ARM_Page_Map`.
/// Register mapping: x2 = the virtual address, x3 = seL4's rights word
/// (`CanWrite` bit 0, `CanRead` bit 1), x4 = seL4's attributes word
/// (`PageCacheable` bit 0, `ExecuteNever` bit 2).
///
/// WS-SX SX6.3 (D6): the call is an invocation **of the frame capability**
/// (the kernel maps that frame's own base, so holding the capability is the
/// authority over the memory), and the address space is the message's extra
/// capability 0; no word names either, and no ASID word is sent: the address
/// space's own ASID is used.  Both words are total, as seL4's
/// `rightsFromWord` and `vmAttributesFromWord` are; a writable and executable
/// request is refused by the kernel (`PolicyDenied`).
///
/// Lean: `PageMapArgs` (SyscallArgDecode.lean)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VSpaceMapArgs {
    pub vaddr: VAddr,
    pub rights: u64,
    pub attr: u64,
}

impl VSpaceMapArgs {
    /// The words for `perms`: read and write go to the rights word, execute
    /// (as `ExecuteNever` clear) and cacheable to the attributes word.  Every
    /// `Page_Map` mapping is a user mapping, so `PagePerms::USER` sends nothing.
    pub const fn from_perms(vaddr: VAddr, perms: PagePerms) -> Self {
        let p = perms.raw() as u64;
        // READ is bit 0 and WRITE bit 1 of `perms`; CanRead is bit 1 and
        // CanWrite bit 0 of seL4's rights word.
        let rights = ((p & 1) << 1) | ((p >> 1) & 1);
        // CACHEABLE is bit 4 and EXECUTE bit 2 of `perms`; PageCacheable is
        // bit 0 and ExecuteNever bit 2 of seL4's attributes word.
        let attr = ((p >> 4) & 1) | ((!p) & 4);
        Self {
            vaddr,
            rights,
            attr,
        }
    }

    pub const fn encode(&self) -> [u64; 3] {
        [self.vaddr.raw(), self.rights, self.attr]
    }

    /// Decode from message registers.  Requires 3 registers; no value is
    /// refused here (the kernel tests the address once the address space
    /// resolves).
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 3 {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            vaddr: VAddr::from(regs[0]),
            rights: regs[1],
            attr: regs[2],
        })
    }
}

/// Arguments for `vspaceUnmap` (syscall 10).
/// Register mapping: x2=asid, x3=vaddr.
///
/// Lean: `VSpaceUnmapArgs` (SyscallArgDecode.lean:128)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VSpaceUnmapArgs {
    pub asid: Asid,
    pub vaddr: VAddr,
}

impl VSpaceUnmapArgs {
    pub const fn encode(&self) -> [u64; 2] {
        [self.asid.raw(), self.vaddr.raw()]
    }

    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 2 {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            asid: Asid::from(regs[0]),
            vaddr: VAddr::from(regs[1]),
        })
    }
}

/// **WS-SM SM7.D**: arguments for `vspaceUnifyInstruction` (syscall 29) — an
/// address space and a virtual page, exactly the operand shape `vspaceUnmap`
/// takes.
///
/// Aliased rather than duplicated so the two share one encoder/decoder and one
/// set of round-trip tests; the distinct name keeps the *semantics* legible at
/// the call site.  This mirrors the Lean side, where
/// `VSpaceUnifyInstructionArgs` is an `abbrev` for `VSpaceUnmapArgs`
/// (`SyscallArgDecode.lean`).
pub type VSpaceUnifyInstructionArgs = VSpaceUnmapArgs;

/// Arguments for `pageTableMap` (syscall 39) — seL4's `seL4_ARM_PageTable_Map`.
/// Register mapping: x2 = a virtual address whose walk the table serves; x3 =
/// seL4's attributes word.  The address space (a capability held with
/// `Write`) is the message's extra capability 0, not a word.
///
/// Lean: `PageTableMapArgs` (SyscallArgDecode.lean, WS-BP BP7.1)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PageTableMapArgs {
    pub vaddr: u64,
    pub attr: u64,
}

impl PageTableMapArgs {
    pub const fn encode(&self) -> [u64; 2] {
        [self.vaddr, self.attr]
    }

    /// Decode from message registers. Requires 2 registers.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 2 {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            vaddr: regs[0],
            attr: regs[1],
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_roundtrip() {
        let args = VSpaceMapArgs::from_perms(
            VAddr::from(0x1000u64),
            PagePerms::try_from(0x15u64).unwrap(),
        );
        assert_eq!(args.rights, 2);
        assert_eq!(args.attr, 1);
        assert_eq!(VSpaceMapArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn map_words_follow_sel4() {
        // read|write, RAM, never executable: CanRead|CanWrite, Cacheable|ExecuteNever
        let rw = VSpaceMapArgs::from_perms(
            VAddr::from(0x1000u64),
            PagePerms::READ | PagePerms::WRITE | PagePerms::CACHEABLE,
        );
        assert_eq!((rw.rights, rw.attr), (3, 5));
        // a device page: read only, uncached, never executable
        let dev = VSpaceMapArgs::from_perms(VAddr::from(0x1000u64), PagePerms::READ);
        assert_eq!((dev.rights, dev.attr), (2, 4));
    }

    #[test]
    fn unmap_roundtrip() {
        let args = VSpaceUnmapArgs {
            asid: Asid::from(1u64),
            vaddr: VAddr::from(0x3000u64),
        };
        assert_eq!(VSpaceUnmapArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn unify_instruction_roundtrip() {
        // WS-SM SM7.D: the unify operand shape is the unmap operand shape.
        let args = VSpaceUnifyInstructionArgs {
            asid: Asid::from(2u64),
            vaddr: VAddr::from(0x4000u64),
        };
        assert_eq!(
            VSpaceUnifyInstructionArgs::decode(&args.encode()).unwrap(),
            args
        );
    }

    #[test]
    fn page_table_map_roundtrip() {
        let args = PageTableMapArgs {
            vaddr: 0x4000_0000,
            attr: 0,
        };
        assert_eq!(PageTableMapArgs::decode(&args.encode()).unwrap(), args);
        assert_eq!(
            PageTableMapArgs::decode(&[1]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

    #[test]
    fn map_insufficient_regs() {
        assert_eq!(
            VSpaceMapArgs::decode(&[1, 2]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

    #[test]
    fn map_words_are_total() {
        assert!(VSpaceMapArgs::decode(&[0x1000, u64::MAX, u64::MAX]).is_ok());
    }
}
