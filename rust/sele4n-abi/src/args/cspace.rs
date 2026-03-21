//! CSpace syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 76–171.

use sele4n_types::{Slot, Badge, AccessRights, KernelError, KernelResult};

/// Arguments for `cspaceMint` (syscall 4).
/// Register mapping: x2=srcSlot, x3=dstSlot, x4=rights bitmask, x5=badge.
///
/// Lean: `CSpaceMintArgs` (SyscallArgDecode.lean:78)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CSpaceMintArgs {
    pub src_slot: Slot,
    pub dst_slot: Slot,
    pub rights: AccessRights,
    pub badge: Badge,
}

impl CSpaceMintArgs {
    /// Encode into message registers.
    pub const fn encode(&self) -> [u64; 4] {
        [self.src_slot.0, self.dst_slot.0, self.rights.0 as u64, self.badge.0]
    }

    /// Decode from message registers. Requires 4 registers.
    ///
    /// R-M01 fix: validates that the rights register fits in u8 and only
    /// uses valid rights bits (0–4). Values > 0x1F are rejected.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 4 { return Err(KernelError::InvalidMessageInfo); }
        if regs[2] > 0x1F {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            src_slot: Slot(regs[0]),
            dst_slot: Slot(regs[1]),
            rights: AccessRights(regs[2] as u8),
            badge: Badge(regs[3]),
        })
    }
}

/// Arguments for `cspaceCopy` (syscall 5).
/// Register mapping: x2=srcSlot, x3=dstSlot.
///
/// Lean: `CSpaceCopyArgs` (SyscallArgDecode.lean:87)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CSpaceCopyArgs {
    pub src_slot: Slot,
    pub dst_slot: Slot,
}

impl CSpaceCopyArgs {
    pub const fn encode(&self) -> [u64; 2] {
        [self.src_slot.0, self.dst_slot.0]
    }

    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 2 { return Err(KernelError::InvalidMessageInfo); }
        Ok(Self { src_slot: Slot(regs[0]), dst_slot: Slot(regs[1]) })
    }
}

/// Arguments for `cspaceMove` (syscall 6).
/// Register mapping: x2=srcSlot, x3=dstSlot.
///
/// Lean: `CSpaceMoveArgs` (SyscallArgDecode.lean:93)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CSpaceMoveArgs {
    pub src_slot: Slot,
    pub dst_slot: Slot,
}

impl CSpaceMoveArgs {
    pub const fn encode(&self) -> [u64; 2] {
        [self.src_slot.0, self.dst_slot.0]
    }

    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 2 { return Err(KernelError::InvalidMessageInfo); }
        Ok(Self { src_slot: Slot(regs[0]), dst_slot: Slot(regs[1]) })
    }
}

/// Arguments for `cspaceDelete` (syscall 7).
/// Register mapping: x2=targetSlot.
///
/// Lean: `CSpaceDeleteArgs` (SyscallArgDecode.lean:101)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CSpaceDeleteArgs {
    pub target_slot: Slot,
}

impl CSpaceDeleteArgs {
    pub const fn encode(&self) -> [u64; 1] {
        [self.target_slot.0]
    }

    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.is_empty() { return Err(KernelError::InvalidMessageInfo); }
        Ok(Self { target_slot: Slot(regs[0]) })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mint_roundtrip() {
        let args = CSpaceMintArgs {
            src_slot: Slot(1), dst_slot: Slot(2),
            rights: AccessRights(0x07), badge: Badge(42),
        };
        let encoded = args.encode();
        let decoded = CSpaceMintArgs::decode(&encoded).unwrap();
        assert_eq!(decoded, args);
    }

    #[test]
    fn copy_roundtrip() {
        let args = CSpaceCopyArgs { src_slot: Slot(10), dst_slot: Slot(20) };
        assert_eq!(CSpaceCopyArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn move_roundtrip() {
        let args = CSpaceMoveArgs { src_slot: Slot(3), dst_slot: Slot(7) };
        assert_eq!(CSpaceMoveArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn delete_roundtrip() {
        let args = CSpaceDeleteArgs { target_slot: Slot(99) };
        assert_eq!(CSpaceDeleteArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn mint_insufficient_regs() {
        assert_eq!(CSpaceMintArgs::decode(&[1, 2, 3]), Err(KernelError::InvalidMessageInfo));
    }

    #[test]
    fn delete_empty_regs() {
        assert_eq!(CSpaceDeleteArgs::decode(&[]), Err(KernelError::InvalidMessageInfo));
    }

    #[test]
    fn mint_rights_valid_boundary() {
        // 0x1F = all 5 rights bits set — maximum valid value
        let regs = [1, 2, 0x1F, 42];
        let args = CSpaceMintArgs::decode(&regs).unwrap();
        assert_eq!(args.rights, AccessRights(0x1F));
    }

    #[test]
    fn mint_rights_zero() {
        let regs = [1, 2, 0, 42];
        let args = CSpaceMintArgs::decode(&regs).unwrap();
        assert_eq!(args.rights, AccessRights(0));
    }

    #[test]
    fn mint_rights_truncation_rejected() {
        // 0x20 — bit 5 set, exceeds valid rights range
        assert_eq!(CSpaceMintArgs::decode(&[1, 2, 0x20, 42]), Err(KernelError::InvalidMessageInfo));
        // 0xFF — u8 max
        assert_eq!(CSpaceMintArgs::decode(&[1, 2, 0xFF, 42]), Err(KernelError::InvalidMessageInfo));
        // 0x100 — would truncate to 0x00 without bounds check
        assert_eq!(CSpaceMintArgs::decode(&[1, 2, 0x100, 42]), Err(KernelError::InvalidMessageInfo));
        // u64::MAX — worst case
        assert_eq!(CSpaceMintArgs::decode(&[1, 2, u64::MAX, 42]), Err(KernelError::InvalidMessageInfo));
    }
}
