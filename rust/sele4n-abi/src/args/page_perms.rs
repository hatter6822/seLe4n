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
pub struct PagePerms(pub(crate) u8);

impl PagePerms {
    pub const READ: Self = Self(1 << 0);

    /// Returns the raw inner value.
    #[inline]
    pub const fn raw(&self) -> u8 { self.0 }
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

impl TryFrom<u64> for PagePerms {
    type Error = KernelError;
    /// R-M02 fix: validates that the permissions value fits in 5 bits (0–0x1F).
    /// Values > 0x1F are rejected to prevent silent truncation.
    /// V1-F consistency: returns `InvalidArgument` (not `InvalidMessageInfo`)
    /// because the message structure is correct — the argument value is invalid.
    #[inline]
    fn try_from(v: u64) -> Result<Self, Self::Error> {
        if v > 0x1F { return Err(KernelError::InvalidArgument); }
        Ok(Self(v as u8))
    }
}

impl From<PagePerms> for u64 {
    #[inline]
    fn from(p: PagePerms) -> u64 { p.0 as u64 }
}

/// V1-G (M-RS-5): `BitOr` combines permission bits. The result is always
/// well-formed (≤ 0x1F), but may violate W^X. Callers must check
/// `is_wx_safe()` or `validate_wx()` before passing to kernel operations.
/// This is intentional: combining permissions is a data operation, while
/// W^X enforcement is a policy check at the point of use (defense in depth).
///
/// Note: `vspace_map()` in `sele4n-sys` already calls `validate_wx()` before
/// issuing the syscall, and the kernel re-validates on entry.
impl core::ops::BitOr for PagePerms {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self { Self(self.0 | rhs.0) }
}

/// Fallible OR that rejects W^X violations at combine time.
/// Use this when you want early rejection without a separate validation step.
impl PagePerms {
    /// Combine two permission sets, returning `PolicyDenied` if the result
    /// would violate W^X (write + execute simultaneously set).
    pub const fn checked_bitor(self, rhs: Self) -> Result<Self, KernelError> {
        let combined = Self(self.0 | rhs.0);
        if combined.is_wx_safe() {
            Ok(combined)
        } else {
            Err(KernelError::PolicyDenied)
        }
    }
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

    #[test]
    fn try_from_valid_boundary() {
        assert_eq!(PagePerms::try_from(0u64).unwrap(), PagePerms(0));
        assert_eq!(PagePerms::try_from(0x1Fu64).unwrap(), PagePerms(0x1F));
    }

    // V1-G: checked_bitor rejects W^X at combine time
    #[test]
    fn checked_bitor_safe() {
        assert!(PagePerms::READ.checked_bitor(PagePerms::WRITE).is_ok());
        assert!(PagePerms::READ.checked_bitor(PagePerms::EXECUTE).is_ok());
    }

    #[test]
    fn checked_bitor_wx_rejected() {
        assert_eq!(PagePerms::WRITE.checked_bitor(PagePerms::EXECUTE), Err(KernelError::PolicyDenied));
    }

    #[test]
    fn try_from_truncation_rejected() {
        // V1-F consistency: invalid perms return InvalidArgument
        assert_eq!(PagePerms::try_from(0x20u64), Err(KernelError::InvalidArgument));
        assert_eq!(PagePerms::try_from(0xFFu64), Err(KernelError::InvalidArgument));
        assert_eq!(PagePerms::try_from(0x100u64), Err(KernelError::InvalidArgument));
        assert_eq!(PagePerms::try_from(u64::MAX), Err(KernelError::InvalidArgument));
    }
}
