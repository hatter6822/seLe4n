//! Type tag for retype operations.
//!
//! Lean: `SeLe4n/Model/Object/Structures.lean:1391` (`KernelObjectType`)
//! and `SeLe4n/Kernel/Lifecycle/Operations.lean:808` (`objectOfTypeTag`).

use sele4n_types::{KernelError, KernelResult};

/// Kernel object type tag for retype operations.
///
/// 6 variants (0–5), matching `KernelObjectType` in Lean.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u64)]
pub enum TypeTag {
    Tcb = 0,
    Endpoint = 1,
    Notification = 2,
    CNode = 3,
    VSpaceRoot = 4,
    Untyped = 5,
}

impl TypeTag {
    /// Convert from a raw u64. Returns `InvalidTypeTag` for values > 5.
    pub const fn from_u64(v: u64) -> KernelResult<Self> {
        match v {
            0 => Ok(Self::Tcb),
            1 => Ok(Self::Endpoint),
            2 => Ok(Self::Notification),
            3 => Ok(Self::CNode),
            4 => Ok(Self::VSpaceRoot),
            5 => Ok(Self::Untyped),
            _ => Err(KernelError::InvalidTypeTag),
        }
    }

    /// Convert to raw u64.
    #[inline]
    pub const fn to_u64(self) -> u64 { self as u64 }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        for i in 0..=5u64 {
            let tag = TypeTag::from_u64(i).unwrap();
            assert_eq!(tag.to_u64(), i);
        }
    }

    #[test]
    fn out_of_range() {
        assert_eq!(TypeTag::from_u64(6), Err(KernelError::InvalidTypeTag));
    }
}
