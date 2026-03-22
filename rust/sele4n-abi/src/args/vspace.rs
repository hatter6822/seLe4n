//! VSpace syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 117–131.

use sele4n_types::{Asid, VAddr, PAddr, KernelError, KernelResult};

/// Arguments for `vspaceMap` (syscall 9).
/// Register mapping: x2=asid, x3=vaddr, x4=paddr, x5=perms word.
///
/// Lean: `VSpaceMapArgs` (SyscallArgDecode.lean:119)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VSpaceMapArgs {
    pub asid: Asid,
    pub vaddr: VAddr,
    pub paddr: PAddr,
    pub perms: u64,
}

impl VSpaceMapArgs {
    pub const fn encode(&self) -> [u64; 4] {
        [self.asid.raw(), self.vaddr.raw(), self.paddr.raw(), self.perms]
    }

    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 4 { return Err(KernelError::InvalidMessageInfo); }
        Ok(Self {
            asid: Asid::from(regs[0]),
            vaddr: VAddr::from(regs[1]),
            paddr: PAddr::from(regs[2]),
            perms: regs[3],
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
        if regs.len() < 2 { return Err(KernelError::InvalidMessageInfo); }
        Ok(Self { asid: Asid::from(regs[0]), vaddr: VAddr::from(regs[1]) })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_roundtrip() {
        let args = VSpaceMapArgs {
            asid: Asid::from(1u64), vaddr: VAddr::from(0x1000u64), paddr: PAddr::from(0x2000u64), perms: 0x07,
        };
        assert_eq!(VSpaceMapArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn unmap_roundtrip() {
        let args = VSpaceUnmapArgs { asid: Asid::from(1u64), vaddr: VAddr::from(0x3000u64) };
        assert_eq!(VSpaceUnmapArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn map_insufficient_regs() {
        assert_eq!(VSpaceMapArgs::decode(&[1, 2, 3]), Err(KernelError::InvalidMessageInfo));
    }
}
