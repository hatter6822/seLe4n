// SPDX-License-Identifier: GPL-3.0-or-later
//! CSpace syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`.

use sele4n_types::{AccessRights, Badge, CPtr, KernelError, KernelResult, Slot};

/// The low five bits of a rights word name the rights; seL4's
/// `rightsFromWord` reads them and ignores the rest.
const RIGHTS_MASK: u64 = 0x1F;

/// The rights a rights word names (its high bits ignored, as in seL4).
fn rights_of_word(word: u64) -> AccessRights {
    match AccessRights::try_from((word & RIGHTS_MASK) as u8) {
        Ok(r) => r,
        Err(_) => AccessRights::EMPTY,
    }
}

/// The two slots of a CNode Copy, Mint or Move, in seL4's
/// `decodeCNodeInvocation` word order: the destination by an index and a
/// depth in the invoked CNode, the source by an index and a depth in the
/// source root.  The source root is not a word: it is the message's extra
/// capability 0, named in the IPC buffer's `caps_or_badges[0]`.
/// Message registers: 0=destIndex, 1=destDepth, 2=srcIndex, 3=srcDepth.
/// A depth outside `1..=64` is the kernel's `RangeError`, refused at lookup.
///
/// Lean: `CNodeOpArgs` (SyscallArgDecode.lean)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CNodeOpArgs {
    pub dest_index: CPtr,
    pub dest_depth: u64,
    pub src_index: CPtr,
    pub src_depth: u64,
}

impl CNodeOpArgs {
    /// Encode into message registers.
    pub const fn encode(&self) -> [u64; 4] {
        [
            self.dest_index.raw(),
            self.dest_depth,
            self.src_index.raw(),
            self.src_depth,
        ]
    }

    /// Decode from message registers. Requires 4 registers (seL4's
    /// `TruncatedMessage` below that).
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 4 {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            dest_index: CPtr::from(regs[0]),
            dest_depth: regs[1],
            src_index: CPtr::from(regs[2]),
            src_depth: regs[3],
        })
    }
}

/// Arguments for `cspaceCopy` (syscall 5): the two slots and the rights mask
/// the copied capability's rights are masked with (seL4's
/// `seL4_CNode_Copy`; it never refuses a mask).
/// Message registers: 0..3 as [`CNodeOpArgs`], 4=rights.
///
/// Lean: `CSpaceCopyArgs` (SyscallArgDecode.lean)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CSpaceCopyArgs {
    pub slots: CNodeOpArgs,
    pub rights: AccessRights,
}

impl CSpaceCopyArgs {
    /// Encode into message registers (the fifth goes to the IPC buffer).
    pub const fn encode(&self) -> [u64; 5] {
        let s = self.slots.encode();
        [s[0], s[1], s[2], s[3], self.rights.raw() as u64]
    }

    /// Decode from message registers. Requires 5 registers; the rights
    /// word's bits past the five rights are ignored, as in seL4.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 5 {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            slots: CNodeOpArgs::decode(regs)?,
            rights: rights_of_word(regs[4]),
        })
    }
}

/// Arguments for `cspaceMove` (syscall 6): the two slots.  A move takes no
/// rights, as in seL4.
pub type CSpaceMoveArgs = CNodeOpArgs;

/// Arguments for `cspaceMint` (syscall 4): a copy's two slots and rights
/// mask, and the badge.  The kernel masks the new capability's rights with
/// the requested ones (seL4's `maskCapRights`); it never refuses them.
/// Message registers: 0..4 as [`CSpaceCopyArgs`], 5=badge (seL4's
/// `seL4_CNode_Mint` order).
///
/// Lean: `CSpaceMintArgs` (SyscallArgDecode.lean)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CSpaceMintArgs {
    pub copy: CSpaceCopyArgs,
    pub badge: Badge,
}

impl CSpaceMintArgs {
    /// Encode into message registers (the fifth and sixth go to the IPC
    /// buffer).
    pub const fn encode(&self) -> [u64; 6] {
        let c = self.copy.encode();
        [c[0], c[1], c[2], c[3], c[4], self.badge.raw()]
    }

    /// Decode from message registers. Requires 6 registers.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 6 {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            copy: CSpaceCopyArgs::decode(regs)?,
            badge: Badge::from(regs[5]),
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
            dest_depth: 64,
            src_index: CPtr::from(20u64),
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
            dest_depth: 1,
            src_index: CPtr::from(7u64),
            src_depth: 64,
        };
        assert_eq!(CSpaceMoveArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn sel4_word_order() {
        let a = CSpaceMintArgs::decode(&[1, 2, 3, 4, 5, 6]).unwrap();
        assert_eq!(a.copy.slots.dest_index, CPtr::from(1u64));
        assert_eq!(a.copy.slots.dest_depth, 2);
        assert_eq!(a.copy.slots.src_index, CPtr::from(3u64));
        assert_eq!(a.copy.slots.src_depth, 4);
        assert_eq!(a.copy.rights.raw(), 5);
        assert_eq!(a.badge, Badge::from(6u64));
    }

    #[test]
    fn rights_word_high_bits_ignored() {
        // seL4's `rightsFromWord` reads the low bits only; no word is refused.
        let a = CSpaceCopyArgs::decode(&[1, 2, 3, 4, u64::MAX]).unwrap();
        assert_eq!(a.rights, AccessRights::ALL);
        let a = CSpaceCopyArgs::decode(&[1, 2, 3, 4, 1 << 21]).unwrap();
        assert_eq!(a.rights, AccessRights::EMPTY);
        for r in 0u64..=0x1F {
            let m = CSpaceMintArgs::decode(&[1, 2, 3, 4, r, 42]).unwrap();
            assert_eq!(u64::from(m.copy.rights.raw()), r);
        }
    }

    #[test]
    fn short_messages_truncated() {
        assert_eq!(
            CSpaceMoveArgs::decode(&[1, 2, 3]),
            Err(KernelError::InvalidMessageInfo)
        );
        assert_eq!(
            CSpaceCopyArgs::decode(&[1, 2, 3, 4]),
            Err(KernelError::InvalidMessageInfo)
        );
        assert_eq!(
            CSpaceMintArgs::decode(&[1, 2, 3, 4, 5]),
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
    fn delete_empty_regs() {
        assert_eq!(
            CSpaceDeleteArgs::decode(&[]),
            Err(KernelError::InvalidMessageInfo)
        );
    }
}
