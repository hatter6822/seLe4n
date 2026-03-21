//! Typed kernel identifiers — 14 newtype wrappers over `u64`.
//!
//! Each identifier mirrors a Lean `structure Foo where val : Nat` in
//! `SeLe4n/Prelude.lean`. All use `#[repr(transparent)]` for ABI compatibility
//! and provide `From<u64>` / `Into<u64>` conversions.
//!
//! Sentinel convention: value 0 is reserved as "unallocated" / "invalid"
//! for `ObjId`, `ThreadId`, `ServiceId`, `CPtr`, and `InterfaceId`,
//! matching seL4's `seL4_CapNull` convention (H-06/WS-E3).

/// Kernel object identifier. Value 0 is the reserved sentinel (H-06/WS-E3).
///
/// Lean: `SeLe4n.ObjId` (Prelude.lean:30)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ObjId(pub u64);

impl ObjId {
    /// The sentinel (invalid) object ID.
    pub const SENTINEL: Self = Self(0);

    /// Returns `true` if this is the reserved sentinel value.
    #[inline]
    pub const fn is_reserved(&self) -> bool { self.0 == 0 }

    /// Returns `true` if this is a valid (non-sentinel) identifier.
    #[inline]
    pub const fn is_valid(&self) -> bool { self.0 != 0 }
}

impl From<u64> for ObjId { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<ObjId> for u64 { #[inline] fn from(id: ObjId) -> u64 { id.0 } }

/// Thread (TCB) identifier. Value 0 is the reserved sentinel (H-06/WS-E3).
///
/// Lean: `SeLe4n.ThreadId` (Prelude.lean:62)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ThreadId(pub u64);

impl ThreadId {
    /// The sentinel (invalid) thread ID.
    pub const SENTINEL: Self = Self(0);

    #[inline]
    pub const fn is_reserved(&self) -> bool { self.0 == 0 }

    /// Convert to `ObjId`, preserving the injection property.
    /// Lean: `ThreadId.toObjId` (Prelude.lean:93)
    #[inline]
    pub const fn to_obj_id(&self) -> ObjId { ObjId(self.0) }
}

impl From<u64> for ThreadId { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<ThreadId> for u64 { #[inline] fn from(id: ThreadId) -> u64 { id.0 } }

/// Capability-space pointer value.
///
/// Lean: `SeLe4n.CPtr` (Prelude.lean:284)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct CPtr(pub u64);

impl CPtr {
    /// The null capability pointer, analogous to `seL4_CapNull`.
    pub const NULL: Self = Self(0);

    #[inline]
    pub const fn is_reserved(&self) -> bool { self.0 == 0 }
}

impl From<u64> for CPtr { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<CPtr> for u64 { #[inline] fn from(p: CPtr) -> u64 { p.0 } }

/// Slot index within a CNode.
///
/// Lean: `SeLe4n.Slot` (Prelude.lean:318)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Slot(pub u64);

impl From<u64> for Slot { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<Slot> for u64 { #[inline] fn from(s: Slot) -> u64 { s.0 } }

/// Scheduling domain identifier.
///
/// Lean: `SeLe4n.DomainId` (Prelude.lean:128)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct DomainId(pub u64);

impl From<u64> for DomainId { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<DomainId> for u64 { #[inline] fn from(d: DomainId) -> u64 { d.0 } }

/// Thread priority level (EDF scheduling).
///
/// Lean: `SeLe4n.Priority` (Prelude.lean:151)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Priority(pub u64);

impl From<u64> for Priority { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<Priority> for u64 { #[inline] fn from(p: Priority) -> u64 { p.0 } }

/// Deadline for EDF scheduling. 0 means "no deadline" (infinite, lowest urgency).
///
/// Lean: `SeLe4n.Deadline` (Prelude.lean:178)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Deadline(pub u64);

impl Deadline {
    /// No deadline set (infinite deadline, lowest urgency).
    pub const NONE: Self = Self(0);

    /// Immediate deadline (most urgent).
    pub const IMMEDIATE: Self = Self(1);
}

impl From<u64> for Deadline { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<Deadline> for u64 { #[inline] fn from(d: Deadline) -> u64 { d.0 } }

/// Interrupt request line identifier.
///
/// Lean: `SeLe4n.Irq` (Prelude.lean:204)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Irq(pub u64);

impl From<u64> for Irq { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<Irq> for u64 { #[inline] fn from(i: Irq) -> u64 { i.0 } }

/// Service identity in the orchestration layer. Value 0 is sentinel (H-06/WS-E3).
///
/// Lean: `SeLe4n.ServiceId` (Prelude.lean:227)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ServiceId(pub u64);

impl ServiceId {
    pub const SENTINEL: Self = Self(0);

    #[inline]
    pub const fn is_reserved(&self) -> bool { self.0 == 0 }
}

impl From<u64> for ServiceId { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<ServiceId> for u64 { #[inline] fn from(s: ServiceId) -> u64 { s.0 } }

/// Interface specification identifier. Value 0 is sentinel.
///
/// Lean: `SeLe4n.InterfaceId` (Prelude.lean:256)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct InterfaceId(pub u64);

impl InterfaceId {
    pub const SENTINEL: Self = Self(0);

    #[inline]
    pub const fn is_reserved(&self) -> bool { self.0 == 0 }
}

impl From<u64> for InterfaceId { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<InterfaceId> for u64 { #[inline] fn from(i: InterfaceId) -> u64 { i.0 } }

/// Endpoint or notification badge value.
/// Bounded to 64-bit machine word (Lean: `machineWordBits = 64`).
///
/// Lean: `SeLe4n.Badge` (Prelude.lean:351)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Badge(pub u64);

impl Badge {
    /// Bitwise OR for notification badge accumulation.
    /// Lean: `Badge.bor` (Prelude.lean:380)
    #[inline]
    pub const fn bor(self, other: Badge) -> Badge {
        Badge(self.0 | other.0)
    }
}

impl From<u64> for Badge { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<Badge> for u64 { #[inline] fn from(b: Badge) -> u64 { b.0 } }

/// Address-space identifier (ASID).
///
/// Lean: `SeLe4n.ASID` (Prelude.lean:411)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Asid(pub u64);

impl From<u64> for Asid { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<Asid> for u64 { #[inline] fn from(a: Asid) -> u64 { a.0 } }

/// Virtual-memory address.
///
/// Lean: `SeLe4n.VAddr` (Prelude.lean:434)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct VAddr(pub u64);

impl From<u64> for VAddr { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<VAddr> for u64 { #[inline] fn from(a: VAddr) -> u64 { a.0 } }

/// Physical-memory address.
///
/// Lean: `SeLe4n.PAddr` (Prelude.lean:457)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct PAddr(pub u64);

impl From<u64> for PAddr { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<PAddr> for u64 { #[inline] fn from(a: PAddr) -> u64 { a.0 } }

/// Register-width machine word (raw register value).
///
/// Lean: `SeLe4n.RegValue` (Machine.lean:42)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct RegValue(pub u64);

impl From<u64> for RegValue { #[inline] fn from(v: u64) -> Self { Self(v) } }
impl From<RegValue> for u64 { #[inline] fn from(r: RegValue) -> u64 { r.0 } }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn thread_id_to_obj_id_preserves_value() {
        let tid = ThreadId(42);
        assert_eq!(tid.to_obj_id(), ObjId(42));
    }

    #[test]
    fn thread_id_to_obj_id_injective() {
        let t1 = ThreadId(1);
        let t2 = ThreadId(2);
        assert_ne!(t1.to_obj_id(), t2.to_obj_id());
    }

    #[test]
    fn sentinel_is_reserved() {
        assert!(ObjId::SENTINEL.is_reserved());
        assert!(ThreadId::SENTINEL.is_reserved());
        assert!(CPtr::NULL.is_reserved());
        assert!(ServiceId::SENTINEL.is_reserved());
        assert!(InterfaceId::SENTINEL.is_reserved());
    }

    #[test]
    fn badge_bor_commutative() {
        let a = Badge(0x0F);
        let b = Badge(0xF0);
        assert_eq!(a.bor(b), b.bor(a));
    }

    #[test]
    fn badge_bor_idempotent() {
        let a = Badge(0xFF);
        assert_eq!(a.bor(a), a);
    }

    #[test]
    fn from_u64_roundtrip() {
        assert_eq!(u64::from(ObjId::from(42u64)), 42u64);
        assert_eq!(u64::from(ThreadId::from(7u64)), 7u64);
        assert_eq!(u64::from(CPtr::from(100u64)), 100u64);
        assert_eq!(u64::from(Slot::from(5u64)), 5u64);
        assert_eq!(u64::from(Badge::from(999u64)), 999u64);
    }
}
