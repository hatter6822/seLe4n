// SPDX-License-Identifier: GPL-3.0-or-later
//! Lifecycle syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 109–115.

use super::type_tag::TypeTag;
use sele4n_types::{CPtr, KernelError, KernelResult, ObjId, Slot};

/// Arguments for `lifecycleRetype` (syscall 8).
/// Register mapping: x2=targetObj, x3=newType tag, x4=size hint.
///
/// Lean: `LifecycleRetypeArgs` (SyscallArgDecode.lean:111)
///
/// V1-C (M-RS-1): `new_type` is now `TypeTag` (validated enum) rather than
/// raw `u64`, preventing invalid type tag values from reaching kernel logic.
///
/// AK4-H (R-ABI-L1) / WS-SM SM6.D: `TypeTag` currently accepts 8 values:
/// `0=Tcb, 1=Endpoint, 2=Notification, 3=CNode, 4=VSpaceRoot,
/// 5=Untyped, 6=SchedContext, 7=Reply`. See `type_tag.rs::TypeTag::from_u64`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LifecycleRetypeArgs {
    pub target_obj: ObjId,
    pub new_type: TypeTag,
    pub size: u64,
}

impl LifecycleRetypeArgs {
    pub const fn encode(&self) -> [u64; 3] {
        [self.target_obj.raw(), self.new_type.to_u64(), self.size]
    }

    /// Decode from message registers. Requires 3 registers.
    ///
    /// V1-C: Validates `regs[1]` through `TypeTag::from_u64()`, which rejects
    /// values > 7. Returns `InvalidTypeTag` for invalid type tags,
    /// `InvalidMessageInfo` for insufficient registers.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 3 {
            return Err(KernelError::InvalidMessageInfo);
        }
        let new_type = TypeTag::from_u64(regs[1])?;
        Ok(Self {
            target_obj: ObjId::from(regs[0]),
            new_type,
            size: regs[2],
        })
    }
}

/// Arguments for `untypedRetype` (syscall 36) — seL4's `seL4_Untyped_Retype`.
/// Register mapping: x2=newType tag, x3=childId, x4=destination CNode
/// capability address, x5=destination slot.
///
/// Lean: `UntypedRetypeArgs` (SyscallArgDecode.lean), decoded by
/// `decodeUntypedRetypeArgs`.  The syscall is invoked on the **untyped**
/// capability; the kernel carves only [`TypeTag::Frame`] and refuses every
/// other valid tag with `InvalidArgument`.
///
/// WS-BP BP7.1 (`v0.36.5`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UntypedRetypeArgs {
    pub new_type: TypeTag,
    pub child_id: ObjId,
    pub dst_cnode: CPtr,
    pub dst_slot: Slot,
}

impl UntypedRetypeArgs {
    pub const fn encode(&self) -> [u64; 4] {
        [
            self.new_type.to_u64(),
            self.child_id.raw(),
            self.dst_cnode.raw(),
            self.dst_slot.raw(),
        ]
    }

    /// Decode from message registers. Requires 4 registers; `regs[0]` must be
    /// a valid type tag (`InvalidTypeTag` otherwise), as the Lean decoder
    /// requires.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 4 {
            return Err(KernelError::InvalidMessageInfo);
        }
        let new_type = TypeTag::from_u64(regs[0])?;
        Ok(Self {
            new_type,
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
            child_id: ObjId::from(77u64),
            dst_cnode: CPtr::from(3u64),
            dst_slot: Slot::from(12u64),
        };
        assert_eq!(UntypedRetypeArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn untyped_retype_insufficient_regs_and_bad_tag() {
        assert_eq!(
            UntypedRetypeArgs::decode(&[8, 1, 2]),
            Err(KernelError::InvalidMessageInfo)
        );
        assert_eq!(
            UntypedRetypeArgs::decode(&[9, 1, 2, 3]),
            Err(KernelError::InvalidTypeTag)
        );
    }

    #[test]
    fn roundtrip() {
        let args = LifecycleRetypeArgs {
            target_obj: ObjId::from(42u64),
            new_type: TypeTag::Notification,
            size: 4096,
        };
        assert_eq!(LifecycleRetypeArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn insufficient_regs() {
        assert_eq!(
            LifecycleRetypeArgs::decode(&[1, 2]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

    // V1-C: Invalid type tag values must be rejected
    #[test]
    fn invalid_type_tag_rejected() {
        // WS-BP BP7.1: 9 is the first invalid tag (Frame = 8).
        assert_eq!(
            LifecycleRetypeArgs::decode(&[42, 9, 0]),
            Err(KernelError::InvalidTypeTag)
        );
        assert_eq!(
            LifecycleRetypeArgs::decode(&[42, 100, 0]),
            Err(KernelError::InvalidTypeTag)
        );
        assert_eq!(
            LifecycleRetypeArgs::decode(&[42, u64::MAX, 0]),
            Err(KernelError::InvalidTypeTag)
        );
    }

    #[test]
    fn all_valid_type_tags() {
        for i in 0..=7u64 {
            let args = LifecycleRetypeArgs::decode(&[1, i, 0]).unwrap();
            assert_eq!(args.new_type.to_u64(), i);
        }
    }
}
