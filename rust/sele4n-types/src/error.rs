// SPDX-License-Identifier: GPL-3.0-or-later
//! Kernel error enumeration — mirrors `SeLe4n.Model.KernelError`.
//!
//! Lean source: `SeLe4n/Model/KernelError.lean`.
//! Discriminants 0–60 other than the retired 35 and 37 are a 1:1 mapping from
//! the Lean inductive (59 variants after `RangeError` at 59 and `FailedLookup` at
//! 60 — seL4's `seL4_RangeError` and `seL4_FailedLookup` for a CNode
//! operation's address — and `TruncatedMessage` at 58 — seL4's
//! `seL4_TruncatedMessage`, an invocation's message shorter than its decode
//! reads — and WS-RR RR7.14's `IpcCancelled` at 57, the error a forcibly-cancelled
//! blocking IPC returns, distinct from `IpcTimeout`'s budget expiry —
//! WS-SM SM9.C.1's `DeclassificationDeniedAtReceiver` at 56,
//! WS-SM SM9.A.2's `AuditFieldTooLarge` at 55, WS-SM SM8.C.9's
//! `AuditLogCapacityExceeded` at 54 and WS-SM SM5.B's
//! `ThreadOnDifferentCore` at 53, extending R5.E's
//! `MissingSchedContext` at 52 and AN7-E's `PartialResolution` at 51).
//! Discriminant 35 is retired (WS-SX SX1.3, the former `InvalidCapPtr`, which
//! no register can provoke once a register is a 64-bit word) and 37 is retired
//! (WS-ZA ZA5.4 part 14, the former `AllocationMisaligned`): no variant carries
//! either and neither is reassigned (see [`KernelError::RETIRED`]).
//! `UnknownKernelError` (255) is a Rust-only sentinel for forward compatibility.
//!
//! A discriminant names an error's **code**.  Five codes carry seL4's error
//! payload in the message registers (`setMRs_syscall_error`): see
//! [`SyscallError`], which decodes a code and its payload words.

/// All kernel error variants, plus a Rust-only forward-compatibility sentinel.
///
/// Discriminants 0–60 (35 and 37 retired) match the Lean `KernelError` inductive exactly.
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
    // 35: retired (WS-SX SX1.3, `InvalidCapPtr`); reserved.
    /// T1-F/H-4: Object count exceeds maxObjects capacity
    ObjectStoreCapacityExceeded = 36,
    // 37: retired (WS-ZA ZA5.4 part 14, `AllocationMisaligned`); reserved.
    /// U-H03: Destroying an object or mapping still in use (unmap, cancel or revoke first)
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
    /// WS-AL AL6 (cascades AK7-F): `storeObjectKindChecked` rejected a
    /// cross-variant write to an existing object store entry.
    InvalidObjectType = 49,
    /// WS-AL AL1b (cascades AK7-I): capability operation rejected the
    /// `Capability.null` sentinel. Distinct from `InvalidCapability`
    /// (slot empty or non-object target) — this specifically signals the
    /// seL4_CapNull convention (`.object` target with reserved ObjId AND
    /// empty rights). Emitted by the kernel's `NonNullCap.ofCap?` type-level
    /// promotion failure path at `cspaceMint` / `cspaceCopy` / `cspaceMove`.
    NullCapability = 50,
    /// AN7-E (API-M01): the gated extra-cap resolver met an unresolvable
    /// capability address.  The default ABI path silently drops
    /// unresolvable caps (seL4-compatible), and today every dispatch arm
    /// takes it, so the kernel does not yet return this variant: the
    /// deployment policy that would select the gated resolver is registered
    /// debt (`docs/REGISTERED_DEBT.md` table C).
    PartialResolution = 51,
    /// R5.E (DEEP-SCH-04): A bound-budget scheduler path lost track of
    /// its bound `SchedContext` (object not found in the kernel `objects`
    /// table).  Pre-R5, this case was silently absorbed by a no-preempt
    /// fallback; under the runtime-checked `crossSubsystemInvariant`
    /// (specifically `schedContextStoreConsistent`) the branch is
    /// unreachable, but surfacing it as a distinct discriminant lets
    /// observability layers report the invariant drift instead of
    /// silently masking it.  Userspace handlers will typically treat
    /// this as a fatal kernel-side invariant violation and surface it
    /// as `SchedulerInvariantViolation` to the application.
    MissingSchedContext = 52,
    /// WS-SM SM5.B.4 (plan §3.2, Theorem 3.2.3): a per-core context switch
    /// (`switchToThreadOnCore`) was asked to dispatch a thread on a core other
    /// than the core its `cpuAffinity` binds it to.  Cross-core migration is a
    /// separate, explicit operation; a context switch never implicitly
    /// migrates.  Distinct from `SchedulerInvariantViolation` so the per-core
    /// scheduler and userspace can tell a genuine wrong-core dispatch from an
    /// unrelated scheduler fault.
    ThreadOnDifferentCore = 53,
    /// WS-SM SM8.C.9: the declassification audit trail is at
    /// `maxDeclassificationAuditEntries`, so the downgrade was refused rather
    /// than performed unrecorded.  Distinct from `DeclassificationDenied`
    /// (policy refused) and `ResourceExhausted` (an unrelated resource): only
    /// this one means "drain the audit trail".
    AuditLogCapacityExceeded = 54,
    /// WS-SM SM9.A.2: an audit-trail field the reader was asked to export needs
    /// more than `maxAuditFieldChunks` chunks, so the kernel **refused the
    /// read** rather than returning a truncated value.  Distinct from
    /// `InvalidArgument`, because the caller's argument was well-formed — it is
    /// the *value* that does not fit, which is a statement about the kernel's
    /// export width and not about the request.
    AuditFieldTooLarge = 55,
    /// WS-SM SM9.C.1: a data-carrying declassification gates **two** hops — the
    /// caller into the notification, and the notification onward into the
    /// resolved receiver — and this is the second one refusing.  Distinct from
    /// `DeclassificationDenied` because the refusal ledger stores exactly this
    /// field, and a monitor reading a bare "denied" cannot tell an unauthorized
    /// caller from an authorized caller aimed at an unauthorized sink; the two
    /// call for opposite responses.
    DeclassificationDeniedAtReceiver = 56,
    /// WS-RR RR7.14: a thread's blocking IPC was forcibly cancelled — by
    /// `.tcbSuspend` on a blocked victim, by lifecycle cleanup, or by a retype
    /// of an object it was blocked on.  Distinct from `IpcTimeout`, which is the
    /// SchedContext budget expiring under a live operation: a timed-out caller
    /// may retry the same call, a cancelled one has had its queue entry
    /// destroyed.
    IpcCancelled = 57,
    /// seL4's `seL4_TruncatedMessage`: an invocation's message holds fewer
    /// argument words than its decode reads.  Answered once the capability is
    /// found and its kind accepted, before any argument is read.
    TruncatedMessage = 58,
    /// seL4's `seL4_RangeError`: an invocation argument outside the range its
    /// operation admits — a CNode operation's depth outside `1..=64` — refused
    /// before the lookup it would bound.  Payload: the range's min and max.
    RangeError = 59,
    /// seL4's `seL4_FailedLookup`: a CNode operation's address that does not
    /// resolve, or names an empty source slot.  Payload: whether it was the
    /// source's, then seL4's lookup fault ([`LookupFault`]).
    FailedLookup = 60,
    /// AF6-A: Kernel returned an error code not recognized by this ABI version.
    /// Discriminant 255 is a reserved sentinel outside the kernel range 0–60.
    UnknownKernelError = 255,
}

impl KernelError {
    /// Retired discriminants, reserved and never reassigned.  `35` was
    /// `InvalidCapPtr`, a capability-pointer register past `2^64`, which no
    /// register can hold once a register is a 64-bit word; `37` was
    /// `AllocationMisaligned`, which no carve returns once the free index is
    /// rounded up to the object's boundary.  `from_u32` maps each to `None`.
    /// Mirrors Lean's `KernelError.retiredDiscriminants`.
    pub const RETIRED: [u32; 2] = [35, 37];

    /// Convert from a raw `u32` discriminant. Returns `None` for out-of-range
    /// and retired values.
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
            36 => Some(Self::ObjectStoreCapacityExceeded),
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
            52 => Some(Self::MissingSchedContext),
            53 => Some(Self::ThreadOnDifferentCore),
            54 => Some(Self::AuditLogCapacityExceeded),
            55 => Some(Self::AuditFieldTooLarge),
            56 => Some(Self::DeclassificationDeniedAtReceiver),
            57 => Some(Self::IpcCancelled),
            58 => Some(Self::TruncatedMessage),
            59 => Some(Self::RangeError),
            60 => Some(Self::FailedLookup),
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
            Self::ObjectStoreCapacityExceeded => write!(f, "object store capacity exceeded"),
            Self::RevocationRequired => write!(f, "revocation required"),
            Self::InvalidArgument => write!(f, "invalid argument"),
            Self::MmioUnaligned => write!(f, "MMIO access at unaligned address"),
            Self::InvalidSyscallArgument => write!(f, "invalid syscall argument"),
            Self::IpcTimeout => write!(f, "IPC timeout"),
            Self::IpcCancelled => write!(
                f,
                "blocking IPC cancelled (the operation was destroyed, not timed out — reissuing may be meaningless)"
            ),
            Self::AlignmentError => write!(f, "alignment error"),
            Self::VmFault => write!(f, "virtual memory fault"),
            Self::UserException => write!(f, "user exception"),
            Self::HardwareFault => write!(f, "hardware fault"),
            Self::NotSupported => write!(f, "not supported"),
            Self::InvalidIrq => write!(f, "invalid IRQ"),
            Self::InvalidObjectType => write!(f, "invalid object type"),
            Self::NullCapability => write!(f, "null capability (seL4_CapNull sentinel)"),
            Self::PartialResolution => write!(f, "partial capability resolution (noisy-resolution debug mode)"),
            Self::MissingSchedContext => write!(f, "scheduler bound thread references missing SchedContext (cross-subsystem invariant drift)"),
            Self::ThreadOnDifferentCore => write!(f, "thread bound to a different core (context switch never migrates)"),
            Self::AuditLogCapacityExceeded => write!(f, "declassification audit trail full (downgrade refused rather than left unrecorded)"),
            Self::AuditFieldTooLarge => write!(f, "audit field too wide to export (read refused rather than truncated)"),
            Self::DeclassificationDeniedAtReceiver => write!(f, "declassification denied at the resolved receiver (the second hop, not the caller's)"),
            Self::TruncatedMessage => write!(f, "message shorter than the invocation's arguments"),
            Self::RangeError => write!(f, "argument outside its operation's range"),
            Self::FailedLookup => write!(f, "capability address lookup failed"),
            Self::UnknownKernelError => write!(f, "unknown kernel error"),
        }
    }
}

/// Standard kernel result type.
pub type KernelResult<T> = Result<T, KernelError>;

/// seL4's `lookup_fault` (`include/object/structures_64.bf`), as
/// `setMRs_lookup_failure` writes it: the type word (`lufType + 1`), then its
/// fields.  Mirrors Lean's `SeLe4n.Model.LookupFault`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LookupFault {
    /// `seL4_InvalidRoot` (1): the root capability is not a CNode capability.
    InvalidRoot,
    /// `seL4_MissingCapability` (2).
    MissingCapability { bits_left: u64 },
    /// `seL4_DepthMismatch` (3).
    DepthMismatch { bits_left: u64, bits_found: u64 },
    /// `seL4_GuardMismatch` (4): `guard_found` is the CNode capability's guard.
    GuardMismatch {
        bits_left: u64,
        guard_found: u64,
        bits_found: u64,
    },
}

impl LookupFault {
    /// The words the fault occupies: the type word and its fields.
    pub const fn word_count(&self) -> usize {
        match self {
            Self::InvalidRoot => 1,
            Self::MissingCapability { .. } => 2,
            Self::DepthMismatch { .. } => 3,
            Self::GuardMismatch { .. } => 4,
        }
    }

    /// Decode a fault from its words (type word first).  `None` when the
    /// type word names no fault or the words are too few for it.
    pub fn decode(words: &[u64]) -> Option<Self> {
        let w = |i: usize| words.get(i).copied();
        match w(0)? {
            1 => Some(Self::InvalidRoot),
            2 => Some(Self::MissingCapability { bits_left: w(1)? }),
            3 => Some(Self::DepthMismatch {
                bits_left: w(1)?,
                bits_found: w(2)?,
            }),
            4 => Some(Self::GuardMismatch {
                bits_left: w(1)?,
                guard_found: w(2)?,
                bits_found: w(3)?,
            }),
            _ => None,
        }
    }
}

/// A kernel error with its payload, as `setMRs_syscall_error`
/// (`src/object/tcb.c`) writes it into the message registers.  Mirrors the
/// Lean `KernelError`'s payload fields (`KernelError.payloadWord`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SyscallError {
    /// MR0: the capability's number (`0` the invoked one, `i + 1` extra
    /// capability `i`).
    InvalidCapability { cap_number: u64 },
    /// MR0: the argument's number.
    InvalidArgument { arg_number: u64 },
    /// MR0, MR1: the range's min and max.
    RangeError { min: u64, max: u64 },
    /// MR0: whether the source's lookup failed; MR1..: the lookup fault.
    FailedLookup {
        was_source: bool,
        fault: LookupFault,
    },
    /// MR0: the memory the untyped has left.
    UntypedRegionExhausted { memory_left: u64 },
    /// A code that carries no payload.
    Code(KernelError),
}

impl SyscallError {
    /// The error's code.
    pub const fn code(&self) -> KernelError {
        match self {
            Self::InvalidCapability { .. } => KernelError::InvalidCapability,
            Self::InvalidArgument { .. } => KernelError::InvalidArgument,
            Self::RangeError { .. } => KernelError::RangeError,
            Self::FailedLookup { .. } => KernelError::FailedLookup,
            Self::UntypedRegionExhausted { .. } => KernelError::UntypedRegionExhausted,
            Self::Code(e) => *e,
        }
    }

    /// The payload's words in seL4's order (at most five).
    pub fn payload(&self) -> ([u64; 5], usize) {
        let mut w = [0u64; 5];
        let n = match *self {
            Self::InvalidCapability { cap_number } => {
                w[0] = cap_number;
                1
            }
            Self::InvalidArgument { arg_number } => {
                w[0] = arg_number;
                1
            }
            Self::RangeError { min, max } => {
                w[0] = min;
                w[1] = max;
                2
            }
            Self::FailedLookup { was_source, fault } => {
                w[0] = u64::from(was_source);
                match fault {
                    LookupFault::InvalidRoot => w[1] = 1,
                    LookupFault::MissingCapability { bits_left } => {
                        w[1] = 2;
                        w[2] = bits_left;
                    }
                    LookupFault::DepthMismatch {
                        bits_left,
                        bits_found,
                    } => {
                        w[1] = 3;
                        w[2] = bits_left;
                        w[3] = bits_found;
                    }
                    LookupFault::GuardMismatch {
                        bits_left,
                        guard_found,
                        bits_found,
                    } => {
                        w[1] = 4;
                        w[2] = bits_left;
                        w[3] = guard_found;
                        w[4] = bits_found;
                    }
                }
                1 + fault.word_count()
            }
            Self::UntypedRegionExhausted { memory_left } => {
                w[0] = memory_left;
                1
            }
            Self::Code(_) => 0,
        };
        (w, n)
    }

    /// Decode a code and the message's words (`mrs`, the message's length of
    /// them, the fifth read from the caller's IPC buffer).  `None` when the
    /// words are too few for the code — a guard mismatch whose fifth word the
    /// kernel could not write (no IPC buffer, length 4) is one.
    pub fn decode(code: KernelError, mrs: &[u64]) -> Option<Self> {
        let w = |i: usize| mrs.get(i).copied();
        Some(match code {
            KernelError::InvalidCapability => Self::InvalidCapability { cap_number: w(0)? },
            KernelError::InvalidArgument => Self::InvalidArgument { arg_number: w(0)? },
            KernelError::RangeError => Self::RangeError {
                min: w(0)?,
                max: w(1)?,
            },
            KernelError::FailedLookup => Self::FailedLookup {
                was_source: w(0)? != 0,
                fault: LookupFault::decode(mrs.get(1..)?)?,
            },
            KernelError::UntypedRegionExhausted => {
                Self::UntypedRegionExhausted { memory_left: w(0)? }
            }
            other => Self::Code(other),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_u32_roundtrip() {
        // AN7-E (API-M01): variants 0-51 added through prior workstreams.
        // R5.E (DEEP-SCH-04): MissingSchedContext added at discriminant 52.
        // WS-SM SM5.B.4: ThreadOnDifferentCore added at discriminant 53.
        // WS-SM SM8.C.9: AuditLogCapacityExceeded added at discriminant 54.
        // WS-SM SM9.A.2: AuditFieldTooLarge added at discriminant 55.
        // WS-SM SM9.C.1: DeclassificationDeniedAtReceiver added at discriminant 56.
        // WS-RR RR7.14: IpcCancelled added at discriminant 57.
        // TruncatedMessage added at discriminant 58.
        // RangeError and FailedLookup added at discriminants 59 and 60.
        for i in 0..=60u32 {
            if KernelError::RETIRED.contains(&i) {
                assert!(KernelError::from_u32(i).is_none(), "retired {i} decoded");
                continue;
            }
            let e = KernelError::from_u32(i).unwrap();
            assert_eq!(e as u32, i);
        }
    }

    #[test]
    fn from_u32_out_of_range() {
        // T1-G: Discriminants in gaps and beyond range must return None
        assert!(KernelError::from_u32(61).is_none());
        assert!(KernelError::from_u32(254).is_none());
        // 255 is now UnknownKernelError (AF6-A sentinel)
        assert_eq!(
            KernelError::from_u32(255),
            Some(KernelError::UnknownKernelError)
        );
        assert!(KernelError::from_u32(256).is_none());
        assert!(KernelError::from_u32(u32::MAX).is_none());
    }

    /// T1-H: Cross-validation — verify new variants have correct discriminants
    #[test]
    fn new_variants_discriminants() {
        assert_eq!(KernelError::ResourceExhausted as u32, 34);
        // 35 is retired: no variant carries it.
        assert!(KernelError::from_u32(35).is_none());
        assert_eq!(KernelError::ObjectStoreCapacityExceeded as u32, 36);
        // 37 is retired: no variant carries it.
        assert_eq!(KernelError::RETIRED, [35, 37]);
        assert!(KernelError::from_u32(37).is_none());
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
        // WS-AL AL6 (cascades AK7-F): kind-check rejection
        assert_eq!(KernelError::InvalidObjectType as u32, 49);
        // WS-AL AL1b (cascades AK7-I): null-cap type-level rejection
        assert_eq!(KernelError::NullCapability as u32, 50);
        // AN7-E (API-M01): partial resolution under noisy-resolution debug
        assert_eq!(KernelError::PartialResolution as u32, 51);
        // R5.E (DEEP-SCH-04): cross-subsystem invariant drift surfacing
        assert_eq!(KernelError::MissingSchedContext as u32, 52);
        // WS-SM SM5.B.4: per-core switch reject-remote
        assert_eq!(KernelError::ThreadOnDifferentCore as u32, 53);
    }

    /// T1-H: Cross-validation — verify Lean-Rust enum correspondence
    /// The Lean KernelError inductive has these 2 variants at positions 34 and
    /// 36, and 35 and 37 are retired:
    ///   | resourceExhausted       (34)
    ///   | objectStoreCapacityExceeded (36)
    #[test]
    fn lean_rust_correspondence() {
        // 61 discriminants (0-60, 35 and 37 retired) — verify the range matches
        // Lean's `kernelErrorEncodingBound` (FailedLookup at 60).
        let max_valid = 60u32;
        assert!(KernelError::from_u32(max_valid).is_some());
        assert!(KernelError::from_u32(max_valid + 1).is_none());

        // Verify from_u32: unknown discriminants in the gap (61–254) return None
        assert!(KernelError::from_u32(100).is_none());
    }

    /// T1-H: Discriminant ordering — kernel variants 0–60 are sequential.
    /// RangeError (59) and FailedLookup (60) extended the range after
    /// TruncatedMessage at 58.
    #[test]
    fn discriminant_ordering() {
        let mut prev = None;
        for i in 0..=60u32 {
            let e = KernelError::from_u32(i);
            if KernelError::RETIRED.contains(&i) {
                assert!(e.is_none(), "retired discriminant {i} decoded");
                continue;
            }
            assert!(e.is_some(), "gap at discriminant {i}");
            if let Some(p) = prev {
                assert!(p < i, "non-sequential at {i}");
            }
            prev = Some(i);
        }
    }

    /// The payload decodes back to the error it was written from, for each
    /// payload code and each lookup fault.
    #[test]
    fn syscall_error_payload_roundtrip() {
        let cases = [
            SyscallError::InvalidCapability { cap_number: 1 },
            SyscallError::InvalidArgument { arg_number: 3 },
            SyscallError::RangeError { min: 1, max: 64 },
            SyscallError::UntypedRegionExhausted { memory_left: 4096 },
            SyscallError::FailedLookup {
                was_source: false,
                fault: LookupFault::InvalidRoot,
            },
            SyscallError::FailedLookup {
                was_source: true,
                fault: LookupFault::MissingCapability { bits_left: 64 },
            },
            SyscallError::FailedLookup {
                was_source: false,
                fault: LookupFault::DepthMismatch {
                    bits_left: 4,
                    bits_found: 7,
                },
            },
            SyscallError::FailedLookup {
                was_source: true,
                fault: LookupFault::GuardMismatch {
                    bits_left: 64,
                    guard_found: 2,
                    bits_found: 58,
                },
            },
            SyscallError::Code(KernelError::IllegalState),
        ];
        for e in cases {
            let (w, n) = e.payload();
            assert!(n <= 5);
            assert_eq!(SyscallError::decode(e.code(), &w[..n]), Some(e));
        }
        // A guard mismatch cut to four words (no buffer) does not decode.
        let gm = SyscallError::FailedLookup {
            was_source: false,
            fault: LookupFault::GuardMismatch {
                bits_left: 64,
                guard_found: 2,
                bits_found: 58,
            },
        };
        let (w, _) = gm.payload();
        assert_eq!(
            SyscallError::decode(KernelError::FailedLookup, &w[..4]),
            None
        );
    }

    /// AF6-A: UnknownKernelError sentinel at discriminant 255.
    /// The None range starts past the last kernel discriminant, 60.
    #[test]
    fn unknown_kernel_error_sentinel() {
        assert_eq!(KernelError::UnknownKernelError as u32, 255);
        assert_eq!(
            KernelError::from_u32(255),
            Some(KernelError::UnknownKernelError)
        );
        // Gap between 60 and 255 is all None
        for i in 61..255u32 {
            assert!(
                KernelError::from_u32(i).is_none(),
                "unexpected variant at {i}"
            );
        }
    }
}
