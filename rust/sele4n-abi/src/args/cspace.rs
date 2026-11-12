// SPDX-License-Identifier: GPL-3.0-or-later
//! CSpace syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 76–171.

use sele4n_types::{AccessRights, Badge, CPtr, KernelError, KernelResult, Slot};

/// The CNode operation word: the fourth argument of `cspaceCopy`,
/// `cspaceMove` and `cspaceMint`, packing the two depths (and, for a copy or
/// a mint, the rights mask).
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
    /// Bits `[16, 21)`: a copy's or a mint's rights mask.
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

    /// The rights mask a copy's or a mint's word names.
    pub const fn rights(word: u64) -> u8 {
        ((word >> RIGHTS_SHIFT) & RIGHTS_MASK) as u8
    }

    /// A move's word sets no bit past the two depths.
    pub const fn addressing_fits(word: u64) -> bool {
        word >> RIGHTS_SHIFT == 0
    }

    /// A copy's or a mint's word sets no bit past the depths and the rights.
    pub const fn rights_fits(word: u64) -> bool {
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

/// Arguments for `cspaceCopy` (syscall 5): the two slots and the rights mask
/// the copy's rights are masked with (seL4's `seL4_CNode_Copy`, whose rights
/// operand masks the copied capability; it never refuses one).
/// Register mapping: x2=destIndex, x3=srcRoot, x4=srcIndex, x5=the depths and
/// the rights ([`cnode_op_word`]).
///
/// Lean: `CSpaceCopyArgs` (SyscallArgDecode.lean)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CSpaceCopyArgs {
    pub slots: CNodeOpArgs,
    pub rights: AccessRights,
}

impl CSpaceCopyArgs {
    /// Encode into message registers.
    pub const fn encode(&self) -> [u64; 4] {
        [
            self.slots.dest_index.raw(),
            self.slots.src_root.raw(),
            self.slots.src_index.raw(),
            cnode_op_word::pack(
                self.slots.dest_depth,
                self.slots.src_depth,
                self.rights.raw(),
            ),
        ]
    }

    /// Decode from message registers. Requires 4 registers; a word with a bit
    /// set past the depths and the rights is `InvalidArgument`.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 4 {
            return Err(KernelError::InvalidMessageInfo);
        }
        if !cnode_op_word::rights_fits(regs[3]) {
            return Err(KernelError::InvalidArgument);
        }
        Ok(Self {
            slots: CNodeOpArgs {
                dest_index: CPtr::from(regs[0]),
                src_root: CPtr::from(regs[1]),
                src_index: CPtr::from(regs[2]),
                dest_depth: cnode_op_word::dest_depth(regs[3]),
                src_depth: cnode_op_word::src_depth(regs[3]),
            },
            rights: AccessRights::try_from(cnode_op_word::rights(regs[3]))
                .map_err(|_| KernelError::InvalidArgument)?,
        })
    }
}

/// Arguments for `cspaceMove` (syscall 6): the two slots.  A move takes no
/// rights, as in seL4.
pub type CSpaceMoveArgs = CNodeOpArgs;

/// Arguments for `cspaceMint` (syscall 4): a copy's two slots and rights
/// mask, and the badge.  The kernel masks the new capability's rights with
/// the requested ones (seL4's `maskCapRights`); it never refuses them.
/// Register mapping: x2..x5 as [`CSpaceCopyArgs`], the badge in the IPC
/// buffer's overflow slot 0 (message register 4).
///
/// Lean: `CSpaceMintArgs` (SyscallArgDecode.lean)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CSpaceMintArgs {
    pub copy: CSpaceCopyArgs,
    pub badge: Badge,
}

impl CSpaceMintArgs {
    /// Encode into message registers (the fifth goes to the IPC buffer).
    pub const fn encode(&self) -> [u64; 5] {
        let c = self.copy.encode();
        [c[0], c[1], c[2], c[3], self.badge.raw()]
    }

    /// Decode from message registers. Requires 5 registers.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 5 {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            copy: CSpaceCopyArgs::decode(regs)?,
            badge: Badge::from(regs[4]),
        })
    }
}

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

    fn slots() -> CNodeOpArgs {
        CNodeOpArgs {
            dest_index: CPtr::from(10u64),
            src_root: CPtr::from(3u64),
            src_index: CPtr::from(20u64),
            dest_depth: 64,
            src_depth: 5,
        }
    }

    #[test]
    fn mint_roundtrip() {
        let args = CSpaceMintArgs {
            copy: CSpaceCopyArgs {
                slots: slots(),
                rights: AccessRights::try_from(0x07u8).unwrap(),
            },
            badge: Badge::from(42u64),
        };
        assert_eq!(CSpaceMintArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn copy_roundtrip() {
        let args = CSpaceCopyArgs {
            slots: slots(),
            rights: AccessRights::ALL,
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
        // A move's word carries no rights.
        assert_eq!(
            CSpaceMoveArgs::decode(&[1, 2, 3, 1 << 16]),
            Err(KernelError::InvalidArgument)
        );
        // A copy's carries them in [16, 21), and nothing past.
        assert!(CSpaceCopyArgs::decode(&[1, 2, 3, 0x1F << 16]).is_ok());
        assert_eq!(
            CSpaceCopyArgs::decode(&[1, 2, 3, 1 << 21]),
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
            CSpaceMintArgs::decode(&[1, 2, 3, 0]),
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
    fn mint_rights_every_mask_decodes() {
        for r in 0u64..=0x1F {
            let args = CSpaceMintArgs::decode(&[1, 2, 3, r << 16, 42]).unwrap();
            assert_eq!(u64::from(args.copy.rights.raw()), r);
        }
    }

    #[test]
    fn mint_word_past_rights_rejected() {
        // A bit past the rights field is `InvalidArgument`, not a short message.
        assert_eq!(
            CSpaceMintArgs::decode(&[1, 2, 3, 1 << 21, 42]),
            Err(KernelError::InvalidArgument)
        );
        assert_eq!(
            CSpaceMintArgs::decode(&[1, 2, 3, u64::MAX, 42]),
            Err(KernelError::InvalidArgument)
        );
    }
}
