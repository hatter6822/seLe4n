// SPDX-License-Identifier: GPL-3.0-or-later
//! Type tag for retype operations.
//!
//! Lean: `SeLe4n/Model/Object/Structures.lean:1391` (`KernelObjectType`)
//! and `SeLe4n/Kernel/Lifecycle/Operations.lean:808` (`objectOfTypeTag`).

use sele4n_types::{KernelError, KernelResult};

/// Kernel object type tag for retype operations.
///
/// 8 variants (0–7), matching `KernelObjectType` in Lean.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u64)]
pub enum TypeTag {
    Tcb = 0,
    Endpoint = 1,
    Notification = 2,
    CNode = 3,
    VSpaceRoot = 4,
    Untyped = 5,
    /// Z1: Scheduling context object type
    SchedContext = 6,
    /// WS-SM SM6.D: first-class Reply object (seL4-MCS)
    Reply = 7,
}

impl TypeTag {
    /// Convert from a raw u64. Returns `InvalidTypeTag` for values > 7.
    pub const fn from_u64(v: u64) -> KernelResult<Self> {
        match v {
            0 => Ok(Self::Tcb),
            1 => Ok(Self::Endpoint),
            2 => Ok(Self::Notification),
            3 => Ok(Self::CNode),
            4 => Ok(Self::VSpaceRoot),
            5 => Ok(Self::Untyped),
            6 => Ok(Self::SchedContext),
            7 => Ok(Self::Reply),
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
        for i in 0..=7u64 {
            let tag = TypeTag::from_u64(i).unwrap();
            assert_eq!(tag.to_u64(), i);
        }
    }

    #[test]
    fn out_of_range() {
        assert_eq!(TypeTag::from_u64(8), Err(KernelError::InvalidTypeTag));
    }

    #[test]
    fn sched_context_discriminant() {
        assert_eq!(TypeTag::SchedContext.to_u64(), 6);
        assert_eq!(TypeTag::from_u64(6).unwrap(), TypeTag::SchedContext);
    }

    #[test]
    fn reply_discriminant() {
        assert_eq!(TypeTag::Reply.to_u64(), 7);
        assert_eq!(TypeTag::from_u64(7).unwrap(), TypeTag::Reply);
    }
}
