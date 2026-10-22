// SPDX-License-Identifier: GPL-3.0-or-later
//! Lifecycle syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`.
//!
//! WS-ZA ZA5.4 part 14 retired the in-place `lifecycleRetype` (syscall 8) and
//! its `LifecycleRetypeArgs`: every object is carved from an untyped through
//! [`UntypedRetypeArgs`], and number 8 stays reserved.

use super::type_tag::TypeTag;
use sele4n_types::{CPtr, KernelError, KernelResult, ObjId, Slot};

/// Arguments for `untypedRetype` (syscall 36) — seL4's `seL4_Untyped_Retype`.
/// Register mapping: x2=newType tag in bits `[0, 8)` and the object's size as a
/// power of two in bits `[8, 64)` (seL4's `size_bits`), x3=childId, x4=destination
/// CNode capability address, x5=destination slot.
///
/// Lean: `UntypedRetypeArgs` (SyscallArgDecode.lean), decoded by
/// `decodeUntypedRetypeArgs`.  The syscall is invoked on the **untyped**
/// capability, and every kind is carved (WS-ZA ZA5.4 part 14), with seL4's
/// sizes: [`TypeTag::Frame`], [`TypeTag::PageTable`], [`TypeTag::VSpaceRoot`],
/// [`TypeTag::Tcb`], [`TypeTag::Endpoint`], [`TypeTag::Notification`] and
/// [`TypeTag::Reply`] take `size_bits = 0`; [`TypeTag::Untyped`] takes
/// `size_bits` in [`MIN_UNTYPED_SIZE_BITS`, `MAX_UNTYPED_SIZE_BITS`];
/// [`TypeTag::CNode`] takes its radix in [`MIN_CNODE_RADIX_BITS`,
/// [`MAX_CNODE_RADIX_BITS`]] (seL4's `seL4_SlotBits` is 5, so a CNode of radix
/// `r` is `2^(r+5)` bytes); [`TypeTag::SchedContext`] takes its size in
/// [`MIN_SCHED_CONTEXT_SIZE_BITS`, `MAX_UNTYPED_SIZE_BITS`].  Anything else is
/// `InvalidArgument`.
///
/// `size_bits` shares MR0 with the tag because all four argument registers are
/// taken.  A frame's MR0 is its tag alone, exactly as before the field existed.
/// `encode` keeps the low 56 bits of `size_bits`; every size the kernel accepts
/// is far below that.
///
/// WS-BP BP7.1 (`v0.36.5`; `size_bits` at slice 4, `v0.36.8`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UntypedRetypeArgs {
    pub new_type: TypeTag,
    pub size_bits: u64,
    pub child_id: ObjId,
    pub dst_cnode: CPtr,
    pub dst_slot: Slot,
}

/// The smallest child untyped a carve makes, as a power of two: one page.
/// Lean: `minUntypedSizeBits`.
pub const MIN_UNTYPED_SIZE_BITS: u64 = 12;
/// The largest child untyped a carve makes, as a power of two — seL4's
/// `seL4_MaxUntypedBits` on AArch64.  Lean: `maxUntypedSizeBits`.
pub const MAX_UNTYPED_SIZE_BITS: u64 = 47;
/// The smallest CNode radix a carve makes.  Lean: `minCNodeRadixBits`.
pub const MIN_CNODE_RADIX_BITS: u64 = 1;
/// seL4's `seL4_SlotBits` on AArch64: a CNode slot is `2^5` bytes.  Lean:
/// `cnodeSlotBits`.
pub const CNODE_SLOT_BITS: u64 = 5;
/// The largest CNode radix a carve makes: one that fills the largest untyped.
/// Lean: `maxCNodeRadixBits`.
pub const MAX_CNODE_RADIX_BITS: u64 = MAX_UNTYPED_SIZE_BITS - CNODE_SLOT_BITS;
/// seL4's `seL4_MinSchedContextBits` on AArch64.  Lean:
/// `minSchedContextSizeBits`.
pub const MIN_SCHED_CONTEXT_SIZE_BITS: u64 = 7;

impl UntypedRetypeArgs {
    pub const fn encode(&self) -> [u64; 4] {
        [
            self.new_type.to_u64() | (self.size_bits << 8),
            self.child_id.raw(),
            self.dst_cnode.raw(),
            self.dst_slot.raw(),
        ]
    }

    /// Decode from message registers. Requires 4 registers; the low byte of
    /// `regs[0]` must be a valid type tag (`InvalidTypeTag` otherwise), as the
    /// Lean decoder requires, and the rest of the word is `size_bits`.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 4 {
            return Err(KernelError::InvalidMessageInfo);
        }
        let new_type = TypeTag::from_u64(regs[0] & 0xFF)?;
        Ok(Self {
            new_type,
            size_bits: regs[0] >> 8,
            child_id: ObjId::from(regs[1]),
            dst_cnode: CPtr::from(regs[2]),
            dst_slot: Slot::from(regs[3]),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn untyped_retype_roundtrip() {
        let args = UntypedRetypeArgs {
            new_type: TypeTag::Frame,
            size_bits: 0,
            child_id: ObjId::from(77u64),
            dst_cnode: CPtr::from(3u64),
            dst_slot: Slot::from(12u64),
        };
        assert_eq!(UntypedRetypeArgs::decode(&args.encode()).unwrap(), args);
        // A frame's MR0 is its tag alone.
        assert_eq!(args.encode()[0], TypeTag::Frame.to_u64());
        let child = UntypedRetypeArgs {
            new_type: TypeTag::Untyped,
            size_bits: 21,
            ..args
        };
        assert_eq!(child.encode()[0], 5 | (21 << 8));
        assert_eq!(UntypedRetypeArgs::decode(&child.encode()).unwrap(), child);
    }

    #[test]
    fn untyped_retype_insufficient_regs_and_bad_tag() {
        assert_eq!(
            UntypedRetypeArgs::decode(&[8, 1, 2]),
            Err(KernelError::InvalidMessageInfo)
        );
        assert_eq!(
            UntypedRetypeArgs::decode(&[10, 1, 2, 3]),
            Err(KernelError::InvalidTypeTag)
        );
    }

    #[test]
    fn untyped_retype_sized_kinds_roundtrip() {
        // WS-ZA ZA5.4 part 14: a CNode's radix and a scheduling context's size
        // ride in MR0's upper bits, as a child untyped's does.
        let base = UntypedRetypeArgs {
            new_type: TypeTag::CNode,
            size_bits: MIN_CNODE_RADIX_BITS + 2,
            child_id: ObjId::from(42u64),
            dst_cnode: CPtr::from(3u64),
            dst_slot: Slot::from(4u64),
        };
        assert_eq!(base.encode()[0], 3 | (3 << 8));
        assert_eq!(UntypedRetypeArgs::decode(&base.encode()).unwrap(), base);
        let sc = UntypedRetypeArgs {
            new_type: TypeTag::SchedContext,
            size_bits: MIN_SCHED_CONTEXT_SIZE_BITS,
            ..base
        };
        assert_eq!(sc.encode()[0], 6 | (7 << 8));
        assert_eq!(UntypedRetypeArgs::decode(&sc.encode()).unwrap(), sc);
        assert_eq!(MAX_CNODE_RADIX_BITS, 42);
    }

    // V1-C: invalid type tag values must be rejected
    #[test]
    fn invalid_type_tag_rejected() {
        // WS-BP BP7.1: 10 is the first invalid tag (PageTable = 9).
        for tag in [10u64, 100, 0xFF] {
            assert_eq!(
                UntypedRetypeArgs::decode(&[tag, 1, 2, 3]),
                Err(KernelError::InvalidTypeTag)
            );
        }
    }

    #[test]
    fn all_valid_type_tags() {
        for i in 0..=9u64 {
            let args = UntypedRetypeArgs::decode(&[i, 1, 2, 3]).unwrap();
            assert_eq!(args.new_type.to_u64(), i);
        }
    }
}
