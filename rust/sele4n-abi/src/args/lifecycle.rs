//! Lifecycle syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 109–115.

use sele4n_types::{ObjId, KernelError, KernelResult};
use super::type_tag::TypeTag;

/// Arguments for `lifecycleRetype` (syscall 8).
/// Register mapping: x2=targetObj, x3=newType tag, x4=size hint.
///
/// Lean: `LifecycleRetypeArgs` (SyscallArgDecode.lean:111)
///
/// V1-C (M-RS-1): `new_type` is now `TypeTag` (validated enum) rather than
/// raw `u64`, preventing invalid type tag values from reaching kernel logic.
///
/// AK4-H (R-ABI-L1): `TypeTag` currently accepts 7 values:
/// `0=Tcb, 1=Endpoint, 2=Notification, 3=CNode, 4=VSpaceRoot,
/// 5=Untyped, 6=SchedContext`. See `type_tag.rs::TypeTag::from_u64`.
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
    /// values > 6. Returns `InvalidTypeTag` for invalid type tags,
    /// `InvalidMessageInfo` for insufficient registers.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 3 { return Err(KernelError::InvalidMessageInfo); }
        let new_type = TypeTag::from_u64(regs[1])?;
        Ok(Self {
            target_obj: ObjId::from(regs[0]),
            new_type,
            size: regs[2],
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let args = LifecycleRetypeArgs { target_obj: ObjId::from(42u64), new_type: TypeTag::Notification, size: 4096 };
        assert_eq!(LifecycleRetypeArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn insufficient_regs() {
        assert_eq!(LifecycleRetypeArgs::decode(&[1, 2]), Err(KernelError::InvalidMessageInfo));
    }

    // V1-C: Invalid type tag values must be rejected
    #[test]
    fn invalid_type_tag_rejected() {
        assert_eq!(LifecycleRetypeArgs::decode(&[42, 7, 0]), Err(KernelError::InvalidTypeTag));
        assert_eq!(LifecycleRetypeArgs::decode(&[42, 100, 0]), Err(KernelError::InvalidTypeTag));
        assert_eq!(LifecycleRetypeArgs::decode(&[42, u64::MAX, 0]), Err(KernelError::InvalidTypeTag));
    }

    #[test]
    fn all_valid_type_tags() {
        for i in 0..=6u64 {
            let args = LifecycleRetypeArgs::decode(&[1, i, 0]).unwrap();
            assert_eq!(args.new_type.to_u64(), i);
        }
    }
}
