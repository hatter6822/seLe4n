// SPDX-License-Identifier: GPL-3.0-or-later
//! Lifecycle syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`.
//!
//! WS-ZA ZA5.4 part 14 retired the in-place `lifecycleRetype` (syscall 8) and
//! its `LifecycleRetypeArgs`: every object is carved from an untyped through
//! [`UntypedRetypeArgs`], and number 8 stays reserved.

use super::type_tag::TypeTag;
use sele4n_types::{CPtr, KernelError, KernelResult, ObjId};

/// Arguments for `untypedRetype` (syscall 36) — seL4's `seL4_Untyped_Retype`.
/// Message registers, in seL4's `decodeUntypedInvocation` order: 0=type,
/// 1=`size_bits`, 2=node index and 3=node depth of the destination CNode under
/// the root, 4=node offset (the first destination slot), 5=object count
/// (`node_window`); 6=child id, the model's object id word after seL4's six.
/// The root is not a word: it is the message's extra capability 0, named in
/// the IPC buffer's `caps_or_badges[0]` (WS-SX SX6.3, D9).  Words 4–6 are the
/// IPC buffer's overflow words.
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
/// `InvalidArgument`.  The object count is at most [`RETYPE_FAN_OUT_LIMIT`].
///
/// WS-BP BP7.1 (`v0.36.5`; `size_bits` at slice 4, `v0.36.8`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UntypedRetypeArgs {
    pub new_type: TypeTag,
    pub size_bits: u64,
    pub node_index: CPtr,
    pub node_depth: u64,
    pub node_offset: u64,
    pub num_objects: u64,
    pub child_id: ObjId,
}

/// seL4's `CONFIG_RETYPE_FAN_OUT_LIMIT` in the model's configuration: the
/// most objects one retype creates.  Lean: `retypeFanOutLimit`.
pub const RETYPE_FAN_OUT_LIMIT: u64 = 1;

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
    /// Encode into message registers (the fifth to seventh go to the IPC
    /// buffer).
    pub const fn encode(&self) -> [u64; 7] {
        [
            self.new_type.to_u64(),
            self.size_bits,
            self.node_index.raw(),
            self.node_depth,
            self.node_offset,
            self.num_objects,
            self.child_id.raw(),
        ]
    }

    /// Decode from message registers. Requires 7 registers; `regs[0]` must be
    /// a valid type tag (`InvalidTypeTag` otherwise), as the Lean decoder
    /// requires.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 7 {
            return Err(KernelError::InvalidMessageInfo);
        }
        let new_type = TypeTag::from_u64(regs[0])?;
        Ok(Self {
            new_type,
            size_bits: regs[1],
            node_index: CPtr::from(regs[2]),
            node_depth: regs[3],
            node_offset: regs[4],
            num_objects: regs[5],
            child_id: ObjId::from(regs[6]),
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
            node_index: CPtr::from(0u64),
            node_depth: 0,
            node_offset: 12,
            num_objects: 1,
            child_id: ObjId::from(77u64),
        };
        assert_eq!(UntypedRetypeArgs::decode(&args.encode()).unwrap(), args);
        // seL4's word order: the type, then the size, each a word of its own.
        assert_eq!(args.encode()[0], TypeTag::Frame.to_u64());
        assert_eq!(args.encode()[4], 12);
        assert_eq!(args.encode()[5], 1);
        assert_eq!(args.encode()[6], 77);
        let child = UntypedRetypeArgs {
            new_type: TypeTag::Untyped,
            size_bits: 21,
            ..args
        };
        assert_eq!(child.encode()[0], 5);
        assert_eq!(child.encode()[1], 21);
        assert_eq!(UntypedRetypeArgs::decode(&child.encode()).unwrap(), child);
    }

    #[test]
    fn untyped_retype_insufficient_regs_and_bad_tag() {
        assert_eq!(
            UntypedRetypeArgs::decode(&[8, 0, 0, 0, 1, 1]),
            Err(KernelError::InvalidMessageInfo)
        );
        assert_eq!(
            UntypedRetypeArgs::decode(&[10, 0, 0, 0, 1, 1, 3]),
            Err(KernelError::InvalidTypeTag)
        );
    }

    #[test]
    fn untyped_retype_sized_kinds_roundtrip() {
        // WS-ZA ZA5.4 part 14: a CNode's radix and a scheduling context's size
        // are the size word, as a child untyped's is.
        let base = UntypedRetypeArgs {
            new_type: TypeTag::CNode,
            size_bits: MIN_CNODE_RADIX_BITS + 2,
            node_index: CPtr::from(3u64),
            node_depth: 64,
            node_offset: 4,
            num_objects: RETYPE_FAN_OUT_LIMIT,
            child_id: ObjId::from(42u64),
        };
        assert_eq!(base.encode()[1], 3);
        assert_eq!(UntypedRetypeArgs::decode(&base.encode()).unwrap(), base);
        let sc = UntypedRetypeArgs {
            new_type: TypeTag::SchedContext,
            size_bits: MIN_SCHED_CONTEXT_SIZE_BITS,
            ..base
        };
        assert_eq!(sc.encode()[1], 7);
        assert_eq!(UntypedRetypeArgs::decode(&sc.encode()).unwrap(), sc);
        assert_eq!(MAX_CNODE_RADIX_BITS, 42);
    }

    // V1-C: invalid type tag values must be rejected
    #[test]
    fn invalid_type_tag_rejected() {
        // WS-BP BP7.1: 10 is the first invalid tag (PageTable = 9).
        for tag in [10u64, 100, 0xFF] {
            assert_eq!(
                UntypedRetypeArgs::decode(&[tag, 0, 2, 3, 4, 1, 6]),
                Err(KernelError::InvalidTypeTag)
            );
        }
    }

    #[test]
    fn all_valid_type_tags() {
        for i in 0..=9u64 {
            let args = UntypedRetypeArgs::decode(&[i, 0, 2, 3, 4, 1, 6]).unwrap();
            assert_eq!(args.new_type.to_u64(), i);
        }
    }
}
