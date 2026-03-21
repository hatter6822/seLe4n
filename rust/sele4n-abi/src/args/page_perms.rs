//! Page permissions bitmask for VSpace operations.
//!
//! Enforces W^X: write + execute cannot be simultaneously set.

use sele4n_types::{KernelError, KernelResult};

/// Page permission bitmask for VSpace map operations.
///
/// Matches the `perms` field in `VSpaceMapArgs`. Enforces W^X safety:
/// the WRITE and EXECUTE bits cannot both be set simultaneously.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct PagePerms(pub u8);

impl PagePerms {
    pub const READ: Self = Self(1 << 0);
    pub const WRITE: Self = Self(1 << 1);
    pub const EXECUTE: Self = Self(1 << 2);
    pub const USER: Self = Self(1 << 3);
    pub const CACHEABLE: Self = Self(1 << 4);

    /// Check if the permissions satisfy W^X: write and execute cannot
    /// both be set simultaneously.
    #[inline]
    pub const fn is_wx_safe(&self) -> bool {
        (self.0 & (Self::WRITE.0 | Self::EXECUTE.0)) != (Self::WRITE.0 | Self::EXECUTE.0)
    }

    /// Validate W^X safety, returning an error if violated.
    pub const fn validate_wx(&self) -> KernelResult<()> {
        if self.is_wx_safe() {
            Ok(())
        } else {
            Err(KernelError::PolicyDenied)
        }
    }

    #[inline]
    pub const fn contains(&self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }
}

impl From<u64> for PagePerms {
    #[inline]
    fn from(v: u64) -> Self { Self(v as u8) }
}

impl From<PagePerms> for u64 {
    #[inline]
    fn from(p: PagePerms) -> u64 { p.0 as u64 }
}

impl core::ops::BitOr for PagePerms {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self { Self(self.0 | rhs.0) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wx_safe() {
        assert!(PagePerms::READ.is_wx_safe());
        assert!(PagePerms::WRITE.is_wx_safe());
        assert!(PagePerms::EXECUTE.is_wx_safe());
        assert!((PagePerms::READ | PagePerms::WRITE).is_wx_safe());
        assert!((PagePerms::READ | PagePerms::EXECUTE).is_wx_safe());
    }

    #[test]
    fn wx_violation() {
        let wx = PagePerms::WRITE | PagePerms::EXECUTE;
        assert!(!wx.is_wx_safe());
        assert_eq!(wx.validate_wx(), Err(KernelError::PolicyDenied));
    }
}
