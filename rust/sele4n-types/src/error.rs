// SPDX-License-Identifier: GPL-3.0-or-later
//! Kernel error enumeration — mirrors `SeLe4n.Model.KernelError`.
//!
//! Lean source: `SeLe4n/Model/State.lean` lines 19–97.
//! Discriminants 0–51 are a 1:1 mapping from the Lean inductive (52 variants
//! after AN7-E's `PartialResolution` at 51).
//! `UnknownKernelError` (255) is a Rust-only sentinel for forward compatibility.

/// All kernel error variants, plus a Rust-only forward-compatibility sentinel.
///
/// Discriminants 0–48 match the Lean `KernelError` inductive exactly.
/// `UnknownKernelError` (255) is a Rust-side sentinel for unrecognized codes.
/// The discriminant values use `#[repr(u32)]` for ABI stability.
///
/// U3-F / U-L08: `#[non_exhaustive]` ensures that adding new error variants
/// in future kernel versions is a non-breaking change for downstream crates.
/// External `match` statements must include a wildcard arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
#[repr(u32)]
pub enum KernelError {
    InvalidCapability = 0,
    ObjectNotFound = 1,
    IllegalState = 2,
    IllegalAuthority = 3,
    PolicyDenied = 4,
    DependencyViolation = 5,
    SchedulerInvariantViolation = 6,
    EndpointStateMismatch = 7,
    EndpointQueueEmpty = 8,
    AsidNotBound = 9,
    VspaceRootInvalid = 10,
    MappingConflict = 11,
    TranslationFault = 12,
    FlowDenied = 13,
    DeclassificationDenied = 14,
    AlreadyWaiting = 15,
    CyclicDependency = 16,
    NotImplemented = 17,
    TargetSlotOccupied = 18,
    ReplyCapInvalid = 19,
    UntypedRegionExhausted = 20,
    UntypedTypeMismatch = 21,
    UntypedDeviceRestriction = 22,
    UntypedAllocSizeTooSmall = 23,
    ChildIdSelfOverwrite = 24,
    ChildIdCollision = 25,
    AddressOutOfBounds = 26,
    IpcMessageTooLarge = 27,
    IpcMessageTooManyCaps = 28,
    BackingObjectMissing = 29,
    InvalidRegister = 30,
    InvalidSyscallNumber = 31,
    InvalidMessageInfo = 32,
    InvalidTypeTag = 33,
    /// T1-F/H-4: Resource exhaustion (e.g., fuel exhaustion in streaming BFS revocation)
    ResourceExhausted = 34,
    /// T1-F/H-4: Capability pointer exceeds word64 bounds
    InvalidCapPtr = 35,
    /// T1-F/H-4: Object count exceeds maxObjects capacity
    ObjectStoreCapacityExceeded = 36,
    /// T1-F/H-4: Allocation base not page-aligned for VSpace-bound objects
    AllocationMisaligned = 37,
    /// U-H03: Delete attempted on slot with CDT children (must revoke first)
    RevocationRequired = 38,
    /// U5-E/U-M07: Syscall argument decode failed (e.g., invalid permission bits)
    InvalidArgument = 39,
    /// V4-B/M-HW-1: MMIO access at unaligned address (4-byte for 32-bit, 8-byte for 64-bit)
    MmioUnaligned = 40,
    /// X5-E/M-11: Syscall-specific argument decode failure (distinct from generic InvalidArgument)
    InvalidSyscallArgument = 41,
    /// Z6: IPC timeout — budget-driven timeout for IPC blocking operations
    IpcTimeout = 42,
    /// D3-B: IPC buffer address not aligned to ipcBufferAlignment (512 bytes)
    AlignmentError = 43,
    /// AG3-C: Virtual memory fault (data abort or instruction abort)
    VmFault = 44,
    /// AG3-C: User-mode exception (alignment, unknown reason)
    UserException = 45,
    /// AG3-C: Hardware fault (SError/asynchronous abort)
    HardwareFault = 46,
    /// AG3-C: Operation not supported (e.g., FIQ on this platform)
    NotSupported = 47,
    /// AG3-D: Unmapped interrupt received (no handler registered)
    InvalidIrq = 48,
    /// AL6 (WS-AL / AK7-F.cascade): `storeObjectKindChecked` rejected a
    /// cross-variant write to an existing object store entry.
    InvalidObjectType = 49,
    /// AL1b (WS-AL / AK7-I.cascade): capability operation rejected the
    /// `Capability.null` sentinel. Distinct from `InvalidCapability`
    /// (slot empty or non-object target) — this specifically signals the
    /// seL4_CapNull convention (`.object` target with reserved ObjId AND
    /// empty rights). Emitted by the kernel's `NonNullCap.ofCap?` type-level
    /// promotion failure path at `cspaceMint` / `cspaceCopy` / `cspaceMove`.
    NullCapability = 50,
    /// AN7-E (API-M01): `resolveExtraCaps` encountered an unresolvable
    /// capability address AND the noisy-resolution debug option was
    /// enabled.  Default ABI path silently drops unresolvable caps
    /// (seL4-compatible); this variant surfaces partial resolution
    /// explicitly when the kernel is built with
    /// `set_option sele4n.debug.noisyResolution true` on the Lean side.
    PartialResolution = 51,
    /// AF6-A: Kernel returned an error code not recognized by this ABI version.
    /// Discriminant 255 is a reserved sentinel outside the kernel range 0–51.
    UnknownKernelError = 255,
}

impl KernelError {
    /// Convert from a raw `u32` discriminant. Returns `None` for out-of-range values.
    pub const fn from_u32(v: u32) -> Option<Self> {
        match v {
            0 => Some(Self::InvalidCapability),
            1 => Some(Self::ObjectNotFound),
            2 => Some(Self::IllegalState),
            3 => Some(Self::IllegalAuthority),
            4 => Some(Self::PolicyDenied),
            5 => Some(Self::DependencyViolation),
            6 => Some(Self::SchedulerInvariantViolation),
            7 => Some(Self::EndpointStateMismatch),
            8 => Some(Self::EndpointQueueEmpty),
            9 => Some(Self::AsidNotBound),
            10 => Some(Self::VspaceRootInvalid),
            11 => Some(Self::MappingConflict),
            12 => Some(Self::TranslationFault),
            13 => Some(Self::FlowDenied),
            14 => Some(Self::DeclassificationDenied),
            15 => Some(Self::AlreadyWaiting),
            16 => Some(Self::CyclicDependency),
            17 => Some(Self::NotImplemented),
            18 => Some(Self::TargetSlotOccupied),
            19 => Some(Self::ReplyCapInvalid),
            20 => Some(Self::UntypedRegionExhausted),
            21 => Some(Self::UntypedTypeMismatch),
            22 => Some(Self::UntypedDeviceRestriction),
            23 => Some(Self::UntypedAllocSizeTooSmall),
            24 => Some(Self::ChildIdSelfOverwrite),
            25 => Some(Self::ChildIdCollision),
            26 => Some(Self::AddressOutOfBounds),
            27 => Some(Self::IpcMessageTooLarge),
            28 => Some(Self::IpcMessageTooManyCaps),
            29 => Some(Self::BackingObjectMissing),
            30 => Some(Self::InvalidRegister),
            31 => Some(Self::InvalidSyscallNumber),
            32 => Some(Self::InvalidMessageInfo),
            33 => Some(Self::InvalidTypeTag),
            34 => Some(Self::ResourceExhausted),
            35 => Some(Self::InvalidCapPtr),
            36 => Some(Self::ObjectStoreCapacityExceeded),
            37 => Some(Self::AllocationMisaligned),
            38 => Some(Self::RevocationRequired),
            39 => Some(Self::InvalidArgument),
            40 => Some(Self::MmioUnaligned),
            41 => Some(Self::InvalidSyscallArgument),
            42 => Some(Self::IpcTimeout),
            43 => Some(Self::AlignmentError),
            44 => Some(Self::VmFault),
            45 => Some(Self::UserException),
            46 => Some(Self::HardwareFault),
            47 => Some(Self::NotSupported),
            48 => Some(Self::InvalidIrq),
            49 => Some(Self::InvalidObjectType),
            50 => Some(Self::NullCapability),
            51 => Some(Self::PartialResolution),
            255 => Some(Self::UnknownKernelError),
            _ => None,
        }
    }
}

#[cfg(feature = "std")]
impl std::fmt::Display for KernelError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidCapability => write!(f, "invalid capability"),
            Self::ObjectNotFound => write!(f, "object not found"),
            Self::IllegalState => write!(f, "illegal state"),
            Self::IllegalAuthority => write!(f, "illegal authority"),
            Self::PolicyDenied => write!(f, "policy denied"),
            Self::DependencyViolation => write!(f, "dependency violation"),
            Self::SchedulerInvariantViolation => write!(f, "scheduler invariant violation"),
            Self::EndpointStateMismatch => write!(f, "endpoint state mismatch"),
            Self::EndpointQueueEmpty => write!(f, "endpoint queue empty"),
            Self::AsidNotBound => write!(f, "ASID not bound"),
            Self::VspaceRootInvalid => write!(f, "vspace root invalid"),
            Self::MappingConflict => write!(f, "mapping conflict"),
            Self::TranslationFault => write!(f, "translation fault"),
            Self::FlowDenied => write!(f, "flow denied"),
            Self::DeclassificationDenied => write!(f, "declassification denied"),
            Self::AlreadyWaiting => write!(f, "already waiting"),
            Self::CyclicDependency => write!(f, "cyclic dependency"),
            Self::NotImplemented => write!(f, "not implemented"),
            Self::TargetSlotOccupied => write!(f, "target slot occupied"),
            Self::ReplyCapInvalid => write!(f, "reply cap invalid"),
            Self::UntypedRegionExhausted => write!(f, "untyped region exhausted"),
            Self::UntypedTypeMismatch => write!(f, "untyped type mismatch"),
            Self::UntypedDeviceRestriction => write!(f, "untyped device restriction"),
            Self::UntypedAllocSizeTooSmall => write!(f, "untyped alloc size too small"),
            Self::ChildIdSelfOverwrite => write!(f, "child ID self overwrite"),
            Self::ChildIdCollision => write!(f, "child ID collision"),
            Self::AddressOutOfBounds => write!(f, "address out of bounds"),
            Self::IpcMessageTooLarge => write!(f, "IPC message too large"),
            Self::IpcMessageTooManyCaps => write!(f, "IPC message too many caps"),
            Self::BackingObjectMissing => write!(f, "backing object missing"),
            Self::InvalidRegister => write!(f, "invalid register"),
            Self::InvalidSyscallNumber => write!(f, "invalid syscall number"),
            Self::InvalidMessageInfo => write!(f, "invalid message info"),
            Self::InvalidTypeTag => write!(f, "invalid type tag"),
            Self::ResourceExhausted => write!(f, "resource exhausted"),
            Self::InvalidCapPtr => write!(f, "invalid capability pointer"),
            Self::ObjectStoreCapacityExceeded => write!(f, "object store capacity exceeded"),
            Self::AllocationMisaligned => write!(f, "allocation misaligned"),
            Self::RevocationRequired => write!(f, "revocation required"),
            Self::InvalidArgument => write!(f, "invalid argument"),
            Self::MmioUnaligned => write!(f, "MMIO access at unaligned address"),
            Self::InvalidSyscallArgument => write!(f, "invalid syscall argument"),
            Self::IpcTimeout => write!(f, "IPC timeout"),
            Self::AlignmentError => write!(f, "alignment error"),
            Self::VmFault => write!(f, "virtual memory fault"),
            Self::UserException => write!(f, "user exception"),
            Self::HardwareFault => write!(f, "hardware fault"),
            Self::NotSupported => write!(f, "not supported"),
            Self::InvalidIrq => write!(f, "invalid IRQ"),
            Self::InvalidObjectType => write!(f, "invalid object type"),
            Self::NullCapability => write!(f, "null capability (seL4_CapNull sentinel)"),
            Self::PartialResolution => write!(f, "partial capability resolution (noisy-resolution debug mode)"),
            Self::UnknownKernelError => write!(f, "unknown kernel error"),
        }
    }
}

/// Standard kernel result type.
pub type KernelResult<T> = Result<T, KernelError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_u32_roundtrip() {
        // AN7-E (API-M01): variants 0-51 must roundtrip after
        // PartialResolution was added at discriminant 51 (extending AL1b's
        // range of 0..=50 with NullCapability at 50).
        for i in 0..=51u32 {
            let e = KernelError::from_u32(i).unwrap();
            assert_eq!(e as u32, i);
        }
    }

    #[test]
    fn from_u32_out_of_range() {
        // T1-G: Discriminants in gaps and beyond range must return None
        assert!(KernelError::from_u32(52).is_none());
        assert!(KernelError::from_u32(254).is_none());
        // 255 is now UnknownKernelError (AF6-A sentinel)
        assert_eq!(KernelError::from_u32(255), Some(KernelError::UnknownKernelError));
        assert!(KernelError::from_u32(256).is_none());
        assert!(KernelError::from_u32(u32::MAX).is_none());
    }

    /// T1-H: Cross-validation — verify new variants have correct discriminants
    #[test]
    fn new_variants_discriminants() {
        assert_eq!(KernelError::ResourceExhausted as u32, 34);
        assert_eq!(KernelError::InvalidCapPtr as u32, 35);
        assert_eq!(KernelError::ObjectStoreCapacityExceeded as u32, 36);
        assert_eq!(KernelError::AllocationMisaligned as u32, 37);
        assert_eq!(KernelError::RevocationRequired as u32, 38);
        assert_eq!(KernelError::InvalidArgument as u32, 39);
        assert_eq!(KernelError::MmioUnaligned as u32, 40);
        assert_eq!(KernelError::InvalidSyscallArgument as u32, 41);
        assert_eq!(KernelError::IpcTimeout as u32, 42);
        assert_eq!(KernelError::AlignmentError as u32, 43);
        // AG3: Exception/interrupt error variants
        assert_eq!(KernelError::VmFault as u32, 44);
        assert_eq!(KernelError::UserException as u32, 45);
        assert_eq!(KernelError::HardwareFault as u32, 46);
        assert_eq!(KernelError::NotSupported as u32, 47);
        assert_eq!(KernelError::InvalidIrq as u32, 48);
        // AL6 (WS-AL / AK7-F.cascade): kind-check rejection
        assert_eq!(KernelError::InvalidObjectType as u32, 49);
        // AL1b (WS-AL / AK7-I.cascade): null-cap type-level rejection
        assert_eq!(KernelError::NullCapability as u32, 50);
        // AN7-E (API-M01): partial resolution under noisy-resolution debug
        assert_eq!(KernelError::PartialResolution as u32, 51);
    }

    /// T1-H: Cross-validation — verify Lean-Rust enum correspondence
    /// The Lean KernelError inductive has these 4 variants at positions 34-37:
    ///   | resourceExhausted       (34)
    ///   | invalidCapPtr           (35)
    ///   | objectStoreCapacityExceeded (36)
    ///   | allocationMisaligned    (37)
    #[test]
    fn lean_rust_correspondence() {
        // AN7-E (API-M01): 52 variants (0-51) — verify total
        // variant count matches Lean (extends AL1b's range).
        let max_valid = 51u32;
        assert!(KernelError::from_u32(max_valid).is_some());
        assert!(KernelError::from_u32(max_valid + 1).is_none());

        // Verify from_u32: unknown discriminants in the gap (52–254) return None
        assert!(KernelError::from_u32(100).is_none());
    }

    /// T1-H: Discriminant ordering — kernel variants 0–51 are sequential
    /// (AN7-E extended the range with PartialResolution at 51).
    #[test]
    fn discriminant_ordering() {
        let mut prev = None;
        for i in 0..=51u32 {
            let e = KernelError::from_u32(i);
            assert!(e.is_some(), "gap at discriminant {i}");
            if let Some(p) = prev {
                assert!(p < i, "non-sequential at {i}");
            }
            prev = Some(i);
        }
    }

    /// AF6-A: UnknownKernelError sentinel at discriminant 255
    /// (AN7-E: the 51 gap closed, so the None range starts at 52).
    #[test]
    fn unknown_kernel_error_sentinel() {
        assert_eq!(KernelError::UnknownKernelError as u32, 255);
        assert_eq!(KernelError::from_u32(255), Some(KernelError::UnknownKernelError));
        // Gap between 51 and 255 is all None
        for i in 52..255u32 {
            assert!(KernelError::from_u32(i).is_none(), "unexpected variant at {i}");
        }
    }
}
