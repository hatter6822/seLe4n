// SPDX-License-Identifier: GPL-3.0-or-later
//! CSpace syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 76–171.

use sele4n_types::{AccessRights, Badge, CPtr, KernelError, KernelResult, Slot};

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
        [
            self.src_slot.raw(),
            self.dst_slot.raw(),
            self.rights.raw() as u64,
            self.badge.raw(),
        ]
    }

    /// Decode from message registers. Requires 4 registers.
    ///
    /// R-M01 fix: validates that the rights register fits in u8 and only
    /// uses valid rights bits (0–4). Values > 0x1F are rejected.
    /// V1-F (M-RS-4): Returns `InvalidArgument` (not `InvalidMessageInfo`)
    /// for invalid rights — the message structure is correct, the argument
    /// value is invalid.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 4 {
            return Err(KernelError::InvalidMessageInfo);
        }
        if regs[2] > 0x1F {
            return Err(KernelError::InvalidArgument);
        }
        Ok(Self {
            src_slot: Slot::from(regs[0]),
            dst_slot: Slot::from(regs[1]),
            rights: AccessRights::try_from(regs[2] as u8)
                .map_err(|_| KernelError::InvalidArgument)?,
            badge: Badge::from(regs[3]),
        })
    }
}

/// The CNode operation word: the fourth argument of `cspaceCopy`,
/// `cspaceMove` and `cspaceMint`, packing the two depths (and a mint's rights).
///
/// Lean: `CNodeOpWord` (SyscallArgDecode.lean).  Both sides render their
/// layout by decoding each bit alone, against
/// `tests/fixtures/abi_layout.expected` (`tests/conformance.rs`).
pub mod cnode_op_word {
    /// Bits `[0, 8)`: the destination depth.
    pub const DEST_DEPTH_SHIFT: u32 = 0;
    /// Bits `[8, 16)`: the source depth.
    pub const SRC_DEPTH_SHIFT: u32 = 8;
    /// Each depth's width.
    pub const DEPTH_WIDTH: u32 = 8;
    /// Bits `[16, 21)`: a mint's rights.
    pub const RIGHTS_SHIFT: u32 = 16;
    /// The rights' width.
    pub const RIGHTS_WIDTH: u32 = 5;

    const DEPTH_MASK: u64 = (1 << DEPTH_WIDTH) - 1;
    const RIGHTS_MASK: u64 = (1 << RIGHTS_WIDTH) - 1;

    /// The word naming the two depths and the rights.
    pub const fn pack(dest_depth: u8, src_depth: u8, rights: u8) -> u64 {
        ((dest_depth as u64) << DEST_DEPTH_SHIFT)
            | ((src_depth as u64) << SRC_DEPTH_SHIFT)
            | (((rights as u64) & RIGHTS_MASK) << RIGHTS_SHIFT)
    }

    /// The destination depth a word names.
    pub const fn dest_depth(word: u64) -> u8 {
        ((word >> DEST_DEPTH_SHIFT) & DEPTH_MASK) as u8
    }

    /// The source depth a word names.
    pub const fn src_depth(word: u64) -> u8 {
        ((word >> SRC_DEPTH_SHIFT) & DEPTH_MASK) as u8
    }

    /// The rights a mint's word names.
    pub const fn rights(word: u64) -> u8 {
        ((word >> RIGHTS_SHIFT) & RIGHTS_MASK) as u8
    }

    /// A copy's or a move's word sets no bit past the two depths.
    pub const fn addressing_fits(word: u64) -> bool {
        word >> RIGHTS_SHIFT == 0
    }

    /// A mint's word sets no bit past the depths and the rights.
    pub const fn mint_fits(word: u64) -> bool {
        word >> (RIGHTS_SHIFT + RIGHTS_WIDTH) == 0
    }
}

/// The two slots of a CNode Copy or Move, as seL4 names them: the destination
/// by an index and a depth in the invoked CNode, the source by an index and a
/// depth in the source root, a CNode capability's address in the caller's
/// CSpace.
/// Register mapping: x2=destIndex, x3=srcRoot, x4=srcIndex, x5=the depths
/// ([`cnode_op_word`]).
///
/// Lean: `CNodeOpArgs` (SyscallArgDecode.lean)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CNodeOpArgs {
    pub dest_index: CPtr,
    pub src_root: CPtr,
    pub src_index: CPtr,
    pub dest_depth: u8,
    pub src_depth: u8,
}

impl CNodeOpArgs {
    /// Encode into message registers.
    pub const fn encode(&self) -> [u64; 4] {
        [
            self.dest_index.raw(),
            self.src_root.raw(),
            self.src_index.raw(),
            cnode_op_word::pack(self.dest_depth, self.src_depth, 0),
        ]
    }

    /// Decode from message registers. Requires 4 registers; a depth word with
    /// a bit set past the two depths is `InvalidArgument`.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 4 {
            return Err(KernelError::InvalidMessageInfo);
        }
        if !cnode_op_word::addressing_fits(regs[3]) {
            return Err(KernelError::InvalidArgument);
        }
        Ok(Self {
            dest_index: CPtr::from(regs[0]),
            src_root: CPtr::from(regs[1]),
            src_index: CPtr::from(regs[2]),
            dest_depth: cnode_op_word::dest_depth(regs[3]),
            src_depth: cnode_op_word::src_depth(regs[3]),
        })
    }
}

/// Arguments for `cspaceCopy` (syscall 5): the two slots.
pub type CSpaceCopyArgs = CNodeOpArgs;

/// Arguments for `cspaceMove` (syscall 6): the two slots.
pub type CSpaceMoveArgs = CNodeOpArgs;

/// Arguments for `mintReplyCap`: two slots of the invoked CNode.
/// Register mapping: x2=srcSlot, x3=dstSlot.
///
/// Lean: `MintReplyCapArgs` (SyscallArgDecode.lean)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MintReplyCapArgs {
    pub src_slot: Slot,
    pub dst_slot: Slot,
}

impl MintReplyCapArgs {
    pub const fn encode(&self) -> [u64; 2] {
        [self.src_slot.raw(), self.dst_slot.raw()]
    }

    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 2 {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            src_slot: Slot::from(regs[0]),
            dst_slot: Slot::from(regs[1]),
        })
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
        [self.target_slot.raw()]
    }

    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.is_empty() {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            target_slot: Slot::from(regs[0]),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mint_roundtrip() {
        let args = CSpaceMintArgs {
            src_slot: Slot::from(1u64),
            dst_slot: Slot::from(2u64),
            rights: AccessRights::try_from(0x07u8).unwrap(),
            badge: Badge::from(42u64),
        };
        let encoded = args.encode();
        let decoded = CSpaceMintArgs::decode(&encoded).unwrap();
        assert_eq!(decoded, args);
    }

    #[test]
    fn copy_roundtrip() {
        let args = CSpaceCopyArgs {
            dest_index: CPtr::from(10u64),
            src_root: CPtr::from(3u64),
            src_index: CPtr::from(20u64),
            dest_depth: 64,
            src_depth: 5,
        };
        assert_eq!(CSpaceCopyArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn move_roundtrip() {
        let args = CSpaceMoveArgs {
            dest_index: CPtr::from(3u64),
            src_root: CPtr::from(1u64),
            src_index: CPtr::from(7u64),
            dest_depth: 1,
            src_depth: 255,
        };
        assert_eq!(CSpaceMoveArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn cnode_op_word_refuses_stray_bits() {
        assert_eq!(
            CSpaceCopyArgs::decode(&[1, 2, 3, 1 << 16]),
            Err(KernelError::InvalidArgument)
        );
        assert_eq!(
            CSpaceCopyArgs::decode(&[1, 2, 3]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

    #[test]
    fn mint_reply_cap_roundtrip() {
        let args = MintReplyCapArgs {
            src_slot: Slot::from(4u64),
            dst_slot: Slot::from(9u64),
        };
        assert_eq!(MintReplyCapArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn delete_roundtrip() {
        let args = CSpaceDeleteArgs {
            target_slot: Slot::from(99u64),
        };
        assert_eq!(CSpaceDeleteArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn mint_insufficient_regs() {
        assert_eq!(
            CSpaceMintArgs::decode(&[1, 2, 3]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

    #[test]
    fn delete_empty_regs() {
        assert_eq!(
            CSpaceDeleteArgs::decode(&[]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

    #[test]
    fn mint_rights_valid_boundary() {
        // 0x1F = all 5 rights bits set — maximum valid value
        let regs = [1, 2, 0x1F, 42];
        let args = CSpaceMintArgs::decode(&regs).unwrap();
        assert_eq!(args.rights, AccessRights::try_from(0x1Fu8).unwrap());
    }

    #[test]
    fn mint_rights_zero() {
        let regs = [1, 2, 0, 42];
        let args = CSpaceMintArgs::decode(&regs).unwrap();
        assert_eq!(args.rights, AccessRights::try_from(0u8).unwrap());
    }

    #[test]
    fn mint_rights_truncation_rejected() {
        // V1-F: invalid rights return InvalidArgument (not InvalidMessageInfo)
        // 0x20 — bit 5 set, exceeds valid rights range
        assert_eq!(
            CSpaceMintArgs::decode(&[1, 2, 0x20, 42]),
            Err(KernelError::InvalidArgument)
        );
        // 0xFF — u8 max
        assert_eq!(
            CSpaceMintArgs::decode(&[1, 2, 0xFF, 42]),
            Err(KernelError::InvalidArgument)
        );
        // 0x100 — would truncate to 0x00 without bounds check
        assert_eq!(
            CSpaceMintArgs::decode(&[1, 2, 0x100, 42]),
            Err(KernelError::InvalidArgument)
        );
        // u64::MAX — worst case
        assert_eq!(
            CSpaceMintArgs::decode(&[1, 2, u64::MAX, 42]),
            Err(KernelError::InvalidArgument)
        );
    }
}
