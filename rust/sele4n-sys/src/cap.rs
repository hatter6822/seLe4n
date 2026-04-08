//! Phantom-typed capability handles — compile-time rights tracking.
//!
//! `Cap<Obj, Rts>` encodes the object type and access rights at the type level,
//! enabling the compiler to reject invalid operations at compile time.
//!
//! This module uses sealed traits to prevent external implementations.

use sele4n_types::{CPtr, AccessRights};
use core::marker::PhantomData;

// ============================================================================
// Sealed trait pattern
// ============================================================================

mod sealed {
    pub trait Sealed {}
}

/// Marker trait for capability object types. Sealed — cannot be implemented
/// outside this crate.
pub trait CapObject: sealed::Sealed {
    /// Human-readable name for diagnostics.
    const NAME: &'static str;
}

/// Marker trait for capability rights descriptors. Sealed.
pub trait CapRights: sealed::Sealed {
    /// The rights bitmask this descriptor represents.
    const RIGHTS: AccessRights;
}

// ============================================================================
// Object type markers
// ============================================================================

/// Endpoint object marker.
pub struct Endpoint;
impl sealed::Sealed for Endpoint {}
impl CapObject for Endpoint { const NAME: &'static str = "Endpoint"; }

/// Notification object marker.
pub struct Notification;
impl sealed::Sealed for Notification {}
impl CapObject for Notification { const NAME: &'static str = "Notification"; }

/// CNode object marker.
pub struct CNode;
impl sealed::Sealed for CNode {}
impl CapObject for CNode { const NAME: &'static str = "CNode"; }

/// TCB (Thread Control Block) object marker.
pub struct Tcb;
impl sealed::Sealed for Tcb {}
impl CapObject for Tcb { const NAME: &'static str = "TCB"; }

/// VSpaceRoot object marker.
pub struct VSpaceRoot;
impl sealed::Sealed for VSpaceRoot {}
impl CapObject for VSpaceRoot { const NAME: &'static str = "VSpaceRoot"; }

/// Untyped memory object marker.
pub struct Untyped;
impl sealed::Sealed for Untyped {}
impl CapObject for Untyped { const NAME: &'static str = "Untyped"; }

/// AF6-D: Scheduling context object marker.
/// Used with `Cap<SchedContext>` for type-safe SchedContext capability handles.
pub struct SchedContext;
impl sealed::Sealed for SchedContext {}
impl CapObject for SchedContext { const NAME: &'static str = "SchedContext"; }

// ============================================================================
// Rights markers
// ============================================================================

/// Full rights (read + write + grant + grant_reply + retype).
pub struct FullRights;
impl sealed::Sealed for FullRights {}
impl CapRights for FullRights { const RIGHTS: AccessRights = AccessRights::ALL; }

/// Read-only rights.
pub struct ReadOnly;
impl sealed::Sealed for ReadOnly {}
impl CapRights for ReadOnly { const RIGHTS: AccessRights = AccessRights::READ; }

/// Read-write rights.
pub struct ReadWrite;
impl sealed::Sealed for ReadWrite {}
impl CapRights for ReadWrite {
    const RIGHTS: AccessRights = AccessRights::READ.union(AccessRights::WRITE);
}

/// Grant rights (for CSpace operations).
pub struct GrantRights;
impl sealed::Sealed for GrantRights {}
impl CapRights for GrantRights {
    const RIGHTS: AccessRights = AccessRights::GRANT.union(AccessRights::READ);
}

// ============================================================================
// Capability error type (S1-D)
// ============================================================================

/// Errors that can occur during capability rights operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CapError {
    /// The requested rights are not a subset of the capability's current rights.
    RightsNotSubset {
        /// The rights that were requested.
        requested: AccessRights,
        /// The rights currently held by the capability.
        current: AccessRights,
    },
}

// ============================================================================
// Phantom-typed capability handle
// ============================================================================

/// A phantom-typed capability handle.
///
/// `Obj` tracks the kernel object type and `Rts` tracks the access rights,
/// both at the type level. The underlying `CPtr` is the runtime capability
/// address used for syscalls.
///
/// For `Restricted` capabilities, `restricted_rights` carries the actual
/// runtime-computed rights mask (the intersection of the original rights
/// and the caller-supplied mask).
///
/// # Rights restriction
///
/// Capabilities can be restricted (rights reduced) but never upgraded.
/// Use `to_read_only()` for safe unconditional restriction, or
/// `restrict()` for runtime-checked restriction to an arbitrary mask.
/// Both return `Result` to allow callers to handle rights violations
/// without panicking.
pub struct Cap<Obj: CapObject, Rts: CapRights> {
    ptr: CPtr,
    /// For `Restricted` caps, the actual rights after restriction.
    /// For other caps, this mirrors `Rts::RIGHTS`.
    restricted_rights: AccessRights,
    _obj: PhantomData<Obj>,
    _rts: PhantomData<Rts>,
}

/// Rights descriptor for a runtime-restricted capability produced by
/// `Cap::restrict()`. The actual rights bitmask is stored in the `Cap`'s
/// `restricted_rights` field — `Restricted::RIGHTS` returns `EMPTY` as a
/// placeholder since the real mask is only known at runtime.
pub struct Restricted;
impl sealed::Sealed for Restricted {}
impl CapRights for Restricted {
    // S1-F: This const is a type-level placeholder only. The actual rights
    // for a Restricted cap are stored in `Cap::restricted_rights` at runtime.
    // Use `Cap::rights()` to get the real rights.
    const RIGHTS: AccessRights = AccessRights::EMPTY;
}

impl<Obj: CapObject, Rts: CapRights> Cap<Obj, Rts> {
    /// Create a new capability handle from a raw CPtr.
    ///
    /// # Safety contract (logical, not memory)
    ///
    /// The caller asserts that the CPtr actually refers to an object of type
    /// `Obj` with at least the rights described by `Rts`. No runtime check
    /// is performed — the kernel validates on each syscall.
    pub const fn from_cptr(ptr: CPtr) -> Self {
        Self { ptr, restricted_rights: Rts::RIGHTS, _obj: PhantomData, _rts: PhantomData }
    }

    /// Get the underlying CPtr for syscall invocation.
    pub const fn cptr(&self) -> CPtr { self.ptr }

    /// Get the actual rights for this capability.
    ///
    /// For statically-typed caps (`FullRights`, `ReadOnly`, etc.), this returns
    /// the compile-time constant. For `Restricted` caps, this returns the
    /// runtime-computed rights mask stored at restriction time (S1-F fix).
    pub const fn rights(&self) -> AccessRights { self.restricted_rights }

    /// Convert to a read-only capability.
    ///
    /// Returns `Err(CapError::RightsNotSubset)` if READ is not a subset of
    /// the current rights. Safe for `FullRights`, `ReadOnly`, `ReadWrite`,
    /// and `GrantRights` (all include READ). For `Restricted` caps, succeeds
    /// only if the restricted rights include READ.
    pub fn to_read_only(self) -> Result<Cap<Obj, ReadOnly>, CapError> {
        if AccessRights::READ.is_subset_of(&self.restricted_rights) {
            Ok(Cap { ptr: self.ptr, restricted_rights: AccessRights::READ, _obj: PhantomData, _rts: PhantomData })
        } else {
            Err(CapError::RightsNotSubset {
                requested: AccessRights::READ,
                current: self.restricted_rights,
            })
        }
    }

    /// Restrict this capability to the given `mask`.
    ///
    /// Returns `Err(CapError::RightsNotSubset)` if `mask` is not a subset
    /// of the current rights. This replaces the former panic-based
    /// implementation (S1-D/S1-E) and enforces that rights can only be
    /// reduced, never escalated.
    pub fn restrict(self, mask: AccessRights) -> Result<Cap<Obj, Restricted>, CapError> {
        if mask.is_subset_of(&self.restricted_rights) {
            // S1-F: Store the actual restricted rights in the Cap struct
            Ok(Cap { ptr: self.ptr, restricted_rights: mask, _obj: PhantomData, _rts: PhantomData })
        } else {
            Err(CapError::RightsNotSubset {
                requested: mask,
                current: self.restricted_rights,
            })
        }
    }
}

// Copy provides Clone automatically; no manual Clone impl needed.
impl<Obj: CapObject, Rts: CapRights> Copy for Cap<Obj, Rts> {}
impl<Obj: CapObject, Rts: CapRights> Clone for Cap<Obj, Rts> {
    fn clone(&self) -> Self { *self }
}

impl<Obj: CapObject, Rts: CapRights> core::fmt::Debug for Cap<Obj, Rts> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Cap<{}, rights=0x{:02x}>({})", Obj::NAME, self.restricted_rights.raw(), self.ptr.raw())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cap_preserves_cptr() {
        let cap: Cap<Endpoint, FullRights> = Cap::from_cptr(CPtr::from(42u64));
        assert_eq!(cap.cptr(), CPtr::from(42u64));
    }

    #[test]
    fn cap_rights() {
        let cap: Cap<Endpoint, ReadOnly> = Cap::from_cptr(CPtr::from(1u64));
        assert!(cap.rights().contains(sele4n_types::AccessRight::Read));
        assert!(!cap.rights().contains(sele4n_types::AccessRight::Write));
    }

    #[test]
    fn cap_to_read_only_always_safe() {
        let full: Cap<CNode, FullRights> = Cap::from_cptr(CPtr::from(10u64));
        let ro: Cap<CNode, ReadOnly> = full.to_read_only().unwrap();
        assert_eq!(ro.cptr(), CPtr::from(10u64));
        assert_eq!(ro.rights(), AccessRights::READ);
    }

    #[test]
    fn cap_restrict_subset_succeeds() {
        let full: Cap<Endpoint, FullRights> = Cap::from_cptr(CPtr::from(5u64));
        let rw_mask = AccessRights::READ | AccessRights::WRITE;
        let restricted: Cap<Endpoint, Restricted> = full.restrict(rw_mask).unwrap();
        assert_eq!(restricted.cptr(), CPtr::from(5u64));
        // S1-F: Restricted cap now returns actual rights, not EMPTY
        assert_eq!(restricted.rights(), rw_mask);
    }

    #[test]
    fn cap_restrict_superset_returns_err() {
        let ro: Cap<Endpoint, ReadOnly> = Cap::from_cptr(CPtr::from(1u64));
        // ReadOnly = 0x01, ALL = 0x1F — 0x1F is NOT a subset of 0x01
        let result = ro.restrict(AccessRights::ALL);
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            CapError::RightsNotSubset {
                requested: AccessRights::ALL,
                current: AccessRights::READ,
            }
        );
    }

    #[test]
    fn cap_restrict_empty_always_safe() {
        let ro: Cap<Endpoint, ReadOnly> = Cap::from_cptr(CPtr::from(7u64));
        let restricted = ro.restrict(AccessRights::EMPTY).unwrap();
        assert_eq!(restricted.cptr(), CPtr::from(7u64));
        assert_eq!(restricted.rights(), AccessRights::EMPTY);
    }

    #[test]
    fn cap_to_read_only_on_restricted_without_read_returns_err() {
        let full: Cap<Endpoint, FullRights> = Cap::from_cptr(CPtr::from(3u64));
        let restricted = full.restrict(AccessRights::WRITE).unwrap();
        // Restricted to WRITE only — READ is not present, should fail
        let result = restricted.to_read_only();
        assert!(result.is_err());
    }

    #[test]
    fn cap_to_read_only_on_restricted_with_read_succeeds() {
        let full: Cap<Endpoint, FullRights> = Cap::from_cptr(CPtr::from(3u64));
        let rw = AccessRights::READ | AccessRights::WRITE;
        let restricted = full.restrict(rw).unwrap();
        // Restricted to READ|WRITE — READ is present, should succeed
        let ro = restricted.to_read_only().unwrap();
        assert_eq!(ro.rights(), AccessRights::READ);
    }

    #[test]
    fn restricted_rights_reflect_actual_mask() {
        let full: Cap<Notification, FullRights> = Cap::from_cptr(CPtr::from(9u64));
        let mask = AccessRights::READ | AccessRights::GRANT;
        let restricted = full.restrict(mask).unwrap();
        // S1-F: rights() must return the actual restricted mask, not EMPTY
        assert_eq!(restricted.rights(), mask);
        assert!(restricted.rights().contains(sele4n_types::AccessRight::Read));
        assert!(restricted.rights().contains(sele4n_types::AccessRight::Grant));
        assert!(!restricted.rights().contains(sele4n_types::AccessRight::Write));
    }

    #[test]
    fn cap_full_rights_value() {
        let full: Cap<Endpoint, FullRights> = Cap::from_cptr(CPtr::from(1u64));
        assert_eq!(full.rights(), AccessRights::ALL);
        assert_eq!(full.rights().raw(), 0x1f);
    }

    #[test]
    fn cap_restricted_rights_value_in_debug() {
        let full: Cap<Endpoint, FullRights> = Cap::from_cptr(CPtr::from(1u64));
        let restricted = full.restrict(AccessRights::READ).unwrap();
        assert_eq!(restricted.rights(), AccessRights::READ);
        assert_eq!(restricted.rights().raw(), 0x01);
    }

    /// AF6-D: SchedContext marker type exists and is usable with Cap.
    #[test]
    fn cap_sched_context_marker() {
        let cap: Cap<SchedContext, FullRights> = Cap::from_cptr(CPtr::from(42u64));
        assert_eq!(cap.cptr(), CPtr::from(42u64));
        assert_eq!(cap.rights(), AccessRights::ALL);
        assert_eq!(SchedContext::NAME, "SchedContext");
    }
}
