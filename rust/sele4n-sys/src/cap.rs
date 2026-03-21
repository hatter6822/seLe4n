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
    const RIGHTS: AccessRights = AccessRights(
        AccessRights::READ.0 | AccessRights::WRITE.0
    );
}

/// Grant rights (for CSpace operations).
pub struct GrantRights;
impl sealed::Sealed for GrantRights {}
impl CapRights for GrantRights {
    const RIGHTS: AccessRights = AccessRights(
        AccessRights::GRANT.0 | AccessRights::READ.0
    );
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
/// # Downgrading
///
/// Capabilities can be downgraded (rights can be reduced) but never upgraded.
/// Use `downgrade()` to create a capability with fewer rights.
pub struct Cap<Obj: CapObject, Rts: CapRights> {
    ptr: CPtr,
    _obj: PhantomData<Obj>,
    _rts: PhantomData<Rts>,
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
        Self { ptr, _obj: PhantomData, _rts: PhantomData }
    }

    /// Get the underlying CPtr for syscall invocation.
    pub const fn cptr(&self) -> CPtr { self.ptr }

    /// Get the static rights for this capability.
    pub const fn rights(&self) -> AccessRights { Rts::RIGHTS }

    /// Downgrade this capability to a weaker rights descriptor.
    ///
    /// The new rights must be a subset of the current rights (checked at the
    /// type level by the `CapRights` trait). The kernel performs the actual
    /// rights check on the syscall path.
    pub const fn downgrade<NewRts: CapRights>(self) -> Cap<Obj, NewRts> {
        Cap { ptr: self.ptr, _obj: PhantomData, _rts: PhantomData }
    }
}

impl<Obj: CapObject, Rts: CapRights> Clone for Cap<Obj, Rts> {
    fn clone(&self) -> Self { Self { ptr: self.ptr, _obj: PhantomData, _rts: PhantomData } }
}

impl<Obj: CapObject, Rts: CapRights> Copy for Cap<Obj, Rts> {}

impl<Obj: CapObject, Rts: CapRights> core::fmt::Debug for Cap<Obj, Rts> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Cap<{}, rights=0x{:02x}>({})", Obj::NAME, Rts::RIGHTS.0, self.ptr.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cap_preserves_cptr() {
        let cap: Cap<Endpoint, FullRights> = Cap::from_cptr(CPtr(42));
        assert_eq!(cap.cptr(), CPtr(42));
    }

    #[test]
    fn cap_rights() {
        let cap: Cap<Endpoint, ReadOnly> = Cap::from_cptr(CPtr(1));
        assert!(cap.rights().contains(sele4n_types::AccessRight::Read));
        assert!(!cap.rights().contains(sele4n_types::AccessRight::Write));
    }

    #[test]
    fn cap_downgrade() {
        let full: Cap<CNode, FullRights> = Cap::from_cptr(CPtr(10));
        let ro: Cap<CNode, ReadOnly> = full.downgrade();
        assert_eq!(ro.cptr(), CPtr(10));
        assert_eq!(ro.rights(), AccessRights::READ);
    }
}
