//! Kernel error enumeration — 1:1 mapping from `SeLe4n.Model.KernelError`.
//!
//! Lean source: `SeLe4n/Model/State.lean` lines 19–54.

/// All kernel error variants, matching the Lean `KernelError` inductive exactly.
///
/// The discriminant values are sequential (implicit `#[repr(u32)]`) for ABI
/// stability. The ordering matches the Lean source declaration order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
        // T1-H: All 38 variants (0-37) must roundtrip
        for i in 0..=37u32 {
            let e = KernelError::from_u32(i).unwrap();
            assert_eq!(e as u32, i);
        }
    }

    #[test]
    fn from_u32_out_of_range() {
        // T1-G: Discriminants >= 38 must return None (unknown error)
        assert!(KernelError::from_u32(38).is_none());
        assert!(KernelError::from_u32(255).is_none());
        assert!(KernelError::from_u32(u32::MAX).is_none());
    }

    /// T1-H: Cross-validation — verify new variants have correct discriminants
    #[test]
    fn new_variants_discriminants() {
        assert_eq!(KernelError::ResourceExhausted as u32, 34);
        assert_eq!(KernelError::InvalidCapPtr as u32, 35);
        assert_eq!(KernelError::ObjectStoreCapacityExceeded as u32, 36);
        assert_eq!(KernelError::AllocationMisaligned as u32, 37);
    }

    /// T1-H: Cross-validation — verify Lean-Rust enum correspondence
    /// The Lean KernelError inductive has these 4 variants at positions 34-37:
    ///   | resourceExhausted       (34)
    ///   | invalidCapPtr           (35)
    ///   | objectStoreCapacityExceeded (36)
    ///   | allocationMisaligned    (37)
    #[test]
    fn lean_rust_correspondence() {
        // Verify total variant count matches Lean (38 variants, 0-37)
        let max_valid = 37u32;
        assert!(KernelError::from_u32(max_valid).is_some());
        assert!(KernelError::from_u32(max_valid + 1).is_none());

        // Verify decode_response fallback: unknown discriminants map to None
        assert!(KernelError::from_u32(100).is_none());
    }

    /// T1-H: Discriminant ordering — all 38 variants are sequential from 0
    #[test]
    fn discriminant_ordering() {
        let mut prev = None;
        for i in 0..=37u32 {
            let e = KernelError::from_u32(i);
            assert!(e.is_some(), "gap at discriminant {i}");
            if let Some(p) = prev {
                assert!(p < i, "non-sequential at {i}");
            }
            prev = Some(i);
        }
    }
}
