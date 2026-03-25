//! Access rights model — 1:1 mapping from `SeLe4n.Model.AccessRight` and
//! `SeLe4n.Model.AccessRightSet`.
//!
//! Lean source: `SeLe4n/Model/Object/Types.lean` lines 33–115.

/// Individual access right. Matches `SeLe4n.Model.AccessRight` inductive.
///
/// Each right maps to a unique bit position (0–4) via `to_bit()`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum AccessRight {
    /// Bit 0: read permission.
    Read = 0,
    /// Bit 1: write permission.
    Write = 1,
    /// Bit 2: grant permission.
    Grant = 2,
    /// Bit 3: grant-reply permission.
    GrantReply = 3,
    /// Bit 4: retype permission (WS-H15c/A-42).
    Retype = 4,
}

impl AccessRight {
    /// Bit position for this right. Lean: `AccessRight.toBit`.
    #[inline]
    pub const fn to_bit(self) -> u8 { self as u8 }

    /// All access rights in canonical order (bit 0..4).
    /// Lean: `AccessRight.all`.
    pub const ALL: [AccessRight; 5] = [
        Self::Read,
        Self::Write,
        Self::Grant,
        Self::GrantReply,
        Self::Retype,
    ];

    /// Convert from a bit position. Returns `None` for positions > 4.
    #[inline]
    pub const fn from_bit(bit: u8) -> Option<Self> {
        match bit {
            0 => Some(Self::Read),
            1 => Some(Self::Write),
            2 => Some(Self::Grant),
            3 => Some(Self::GrantReply),
            4 => Some(Self::Retype),
            _ => None,
        }
    }
}

/// Order-independent access right set using bitmask representation.
///
/// Matches `SeLe4n.Model.AccessRightSet` — a word-sized bitmask where each
/// of the 5 access rights maps to bit position 0..4.
///
/// All operations are O(1) bitwise.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct AccessRights(pub(crate) u8);

impl AccessRights {
    /// Empty rights set (no permissions).
    pub const EMPTY: Self = Self(0);

    /// Returns the raw inner value.
    #[inline]
    pub const fn raw(&self) -> u8 { self.0 }

    /// Read-only.
    pub const READ: Self = Self(1 << 0);
    /// Write-only.
    pub const WRITE: Self = Self(1 << 1);
    /// Grant-only.
    pub const GRANT: Self = Self(1 << 2);
    /// Grant-reply-only.
    pub const GRANT_REPLY: Self = Self(1 << 3);
    /// Retype-only.
    pub const RETYPE: Self = Self(1 << 4);

    /// All rights.
    pub const ALL: Self = Self(0x1F);

    /// Construct a rights set from a single right.
    /// Lean: `AccessRightSet.singleton`.
    #[inline]
    pub const fn singleton(r: AccessRight) -> Self {
        Self(1 << r.to_bit())
    }

    /// Membership test — O(1) bit check.
    /// Lean: `AccessRightSet.mem`.
    #[inline]
    pub const fn contains(&self, r: AccessRight) -> bool {
        (self.0 >> r.to_bit()) & 1 != 0
    }

    /// Subset test — O(1) bitwise check.
    /// Lean: `AccessRightSet.subset`.
    #[inline]
    pub const fn is_subset_of(&self, other: &AccessRights) -> bool {
        self.0 & other.0 == self.0
    }

    /// Union of two rights sets (bitwise OR).
    /// Lean: `AccessRightSet.union`.
    #[inline]
    pub const fn union(self, other: AccessRights) -> AccessRights {
        AccessRights(self.0 | other.0)
    }

    /// Intersection of two rights sets (bitwise AND).
    /// Lean: `AccessRightSet.inter`.
    #[inline]
    pub const fn inter(self, other: AccessRights) -> AccessRights {
        AccessRights(self.0 & other.0)
    }
}

/// U3-D / U-M33: `TryFrom<u8>` replaces the former blanket `From<u8>`.
///
/// Only values 0..=0x1F (bits 0–4) are valid access rights bitmasks.
/// Values with bits 5–7 set are rejected with `InvalidAccessRights`.
///
/// For infallible construction from known-valid constants, use the
/// `AccessRights` associated constants (`READ`, `WRITE`, `ALL`, etc.)
/// or `AccessRights::singleton()`.
impl TryFrom<u8> for AccessRights {
    type Error = AccessRightsError;

    #[inline]
    fn try_from(v: u8) -> Result<Self, Self::Error> {
        if v > 0x1F {
            Err(AccessRightsError(v))
        } else {
            Ok(Self(v))
        }
    }
}

impl From<AccessRights> for u8 { #[inline] fn from(r: AccessRights) -> u8 { r.0 } }

/// Error returned when constructing `AccessRights` from an invalid byte.
///
/// U3-D / U-M33: Values with bits 5–7 set are not valid access rights.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AccessRightsError(pub u8);

impl core::ops::BitOr for AccessRights {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self { self.union(rhs) }
}

impl core::ops::BitAnd for AccessRights {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self { self.inter(rhs) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn singleton_contains() {
        let s = AccessRights::singleton(AccessRight::Grant);
        assert!(s.contains(AccessRight::Grant));
        assert!(!s.contains(AccessRight::Read));
    }

    #[test]
    fn union_contains_both() {
        let rw = AccessRights::READ | AccessRights::WRITE;
        assert!(rw.contains(AccessRight::Read));
        assert!(rw.contains(AccessRight::Write));
        assert!(!rw.contains(AccessRight::Grant));
    }

    #[test]
    fn subset_check() {
        let r = AccessRights::READ;
        let rw = AccessRights::READ | AccessRights::WRITE;
        assert!(r.is_subset_of(&rw));
        assert!(!rw.is_subset_of(&r));
    }

    #[test]
    fn order_independent() {
        let rw1 = AccessRights::READ | AccessRights::WRITE;
        let rw2 = AccessRights::WRITE | AccessRights::READ;
        assert_eq!(rw1, rw2);
    }

    #[test]
    fn intersection() {
        let rw = AccessRights::READ | AccessRights::WRITE;
        let wg = AccessRights::WRITE | AccessRights::GRANT;
        let w = rw & wg;
        assert!(w.contains(AccessRight::Write));
        assert!(!w.contains(AccessRight::Read));
        assert!(!w.contains(AccessRight::Grant));
    }

    #[test]
    fn all_rights() {
        let all = AccessRights::ALL;
        for r in AccessRight::ALL {
            assert!(all.contains(r));
        }
    }

    // U3-D: TryFrom<u8> validation tests
    #[test]
    fn try_from_valid_range() {
        for v in 0..=0x1Fu8 {
            assert!(AccessRights::try_from(v).is_ok());
            assert_eq!(AccessRights::try_from(v).unwrap().raw(), v);
        }
    }

    #[test]
    fn try_from_invalid_rejected() {
        for v in 0x20..=0xFFu8 {
            assert!(AccessRights::try_from(v).is_err());
        }
    }

    #[test]
    fn try_from_error_contains_value() {
        let err = AccessRights::try_from(0x80u8).unwrap_err();
        assert_eq!(err, AccessRightsError(0x80));
    }
}
