//! VSpace syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 117–131.

use sele4n_types::{Asid, VAddr, PAddr, KernelError, KernelResult};
use crate::args::PagePerms;

/// Arguments for `vspaceMap` (syscall 9).
/// Register mapping: x2=asid, x3=vaddr, x4=paddr, x5=perms word.
///
/// T3-C/M-NEW-10: The `perms` field is typed as `PagePerms` (validated 5-bit
/// bitmask) instead of raw `u64`. The decode method rejects invalid permission
/// values at the ABI boundary, preventing malformed register contents from
/// propagating into the kernel.
///
/// Lean: `VSpaceMapArgs` (SyscallArgDecode.lean:119)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VSpaceMapArgs {
    pub asid: Asid,
    pub vaddr: VAddr,
    pub paddr: PAddr,
    pub perms: PagePerms,
}

impl VSpaceMapArgs {
    pub const fn encode(&self) -> [u64; 4] {
        [self.asid.raw(), self.vaddr.raw(), self.paddr.raw(), self.perms.raw() as u64]
    }

    /// Decode register values into typed VSpaceMapArgs.
    ///
    /// T3-C/M-NEW-10: Validates that `regs[3]` (perms) is a valid 5-bit
    /// permission bitmask (0–0x1F). Values > 0x1F are rejected with
    /// `InvalidMessageInfo` to prevent silent truncation.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 4 { return Err(KernelError::InvalidMessageInfo); }
        let perms = PagePerms::try_from(regs[3])?;
        Ok(Self {
            asid: Asid::from(regs[0]),
            vaddr: VAddr::from(regs[1]),
            paddr: PAddr::from(regs[2]),
            perms,
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
            asid: Asid::from(1u64), vaddr: VAddr::from(0x1000u64), paddr: PAddr::from(0x2000u64),
            perms: PagePerms::try_from(0x07u64).unwrap(),
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

    // T3-C: Invalid perms rejected at decode boundary
    #[test]
    fn map_invalid_perms_rejected() {
        assert_eq!(VSpaceMapArgs::decode(&[1, 0x1000, 0x2000, 0xFF]),
                   Err(KernelError::InvalidMessageInfo));
        assert_eq!(VSpaceMapArgs::decode(&[1, 0x1000, 0x2000, 0x20]),
                   Err(KernelError::InvalidMessageInfo));
        assert_eq!(VSpaceMapArgs::decode(&[1, 0x1000, 0x2000, u64::MAX]),
                   Err(KernelError::InvalidMessageInfo));
    }

    #[test]
    fn map_valid_perms_boundary() {
        // 0x00 and 0x1F are both valid
        assert!(VSpaceMapArgs::decode(&[1, 0x1000, 0x2000, 0x00]).is_ok());
        assert!(VSpaceMapArgs::decode(&[1, 0x1000, 0x2000, 0x1F]).is_ok());
    }
}
