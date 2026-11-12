// SPDX-License-Identifier: GPL-3.0-or-later
//! AN9-F (DEF-R-HAL-L14 / RESOLVED): Typed SVC argument marshalling.
//!
//! This module owns the SVC trap's syscall-id decode.  The `handle_svc`
//! entry in `trap.rs` reads the syscall id from the raw `TrapFrame` and
//! dispatches to the Lean kernel via [`dispatch_svc`].
//!
//! ## Mirror discipline
//!
//! `SyscallId` here mirrors the 41-variant enum in
//! `sele4n-types/src/syscall.rs`.  We do NOT depend on `sele4n-types`
//! in the runtime build (the HAL crate is the lowest-level workspace
//! member with zero runtime dependencies, by design — see
//! `rust/sele4n-hal/Cargo.toml`), so the discriminants are duplicated
//! here.  The unit test `syscall_id_discriminants_match_lean_abi`
//! cross-checks this mirror against the canonical
//! `sele4n-types::SyscallId` (a dev-dependency, available only under
//! `#[cfg(test)]`) so any drift in the discriminants / `COUNT` /
//! `from_u32` decode fails the build — the previous self-referential
//! form (comparing the mirror to its own `COUNT`) could not catch a
//! missing variant.
//!
//! ## Argument layout
//!
//! seLe4n's syscall ABI (matching the Lean `arm64DefaultLayout` in
//! `SeLe4n/Kernel/Architecture/RegisterDecode.lean`):
//!
//! ```text
//! x0..x5 : inline message registers
//! x6     : ipc_buffer_addr     (caller's TPIDRRO_EL0; optional)
//! x7     : syscall_id          (SyscallId enum discriminant)
//! ```
//!
//! `MessageInfo` is packed into `x1` per AK4 ABI conventions (length,
//! extraCaps, label fields); the dispatcher reads none of it.  The Lean side
//! reads every argument register from the in-flight frame it takes whole
//! (`Platform.FFI.ffiTrapContext`), decodes `MessageInfo` via
//! `SeLe4n.Model.MessageInfo.mk`, and refuses an invocation whose message is
//! shorter than its arguments with `KernelError::TruncatedMessage` once its
//! capability is found, as seL4 does (`truncationMinimum`).

/// AN9-F + WS-RA: the dispatcher's **prefilter** rejection.
///
/// This type carries only the one rejection `dispatch_svc` itself makes
/// before reaching the Lean kernel: a syscall id that names no syscall.  The
/// argument-count prefilter is retired — the Lean kernel refuses a message
/// shorter than its invocation's arguments with `TruncatedMessage`, after
/// the capability lookup, in seL4's order.  The former
/// `Kernel(u32)` wrapper — which forwarded a discriminant decoded from
/// the retired bit-63 word — is gone: a Lean rejection now arrives as an
/// ordinary return frame whose `x1` label carries the error (the frame
/// passes through [`SvcOutcome::Frame`] undecoded; userspace's
/// `decode_response` is the single decode point, plan §3.2).
///
/// This also retires the documented discriminant collision (the legacy
/// raw `7` / `6` written into `x0` collided with
/// `KernelError::EndpointStateMismatch` / `SchedulerInvariantViolation`
/// on the wire — the "post-1.0 ABI cleanup" this workstream is): the
/// trap layer now maps the rejection to a label-encoded
/// `KernelError::InvalidSyscallNumber` frame ([`error_frame_regs`]), so a
/// prefilter rejection is indistinguishable
/// in *shape* from a kernel rejection and collides with nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DispatchError {
    /// Caller passed a syscall id that names no syscall: one at or past
    /// `SyscallId::ENCODING_BOUND`, or a retired number
    /// (`SyscallId::RETIRED`).  Surfaced to userspace as `KernelError::InvalidSyscallNumber`
    /// on the `x1` label.
    InvalidSyscallId,
}

impl DispatchError {
    /// The `KernelError` discriminant this prefilter rejection surfaces
    /// as (mirrors `sele4n-types::KernelError`:
    /// `InvalidSyscallNumber = 31`, `InvalidSyscallArgument = 41`; pinned
    /// against the canonical enum by the `#[cfg(test)]` mirror test).
    #[inline]
    pub const fn kernel_error_discriminant(self) -> u32 {
        match self {
            DispatchError::InvalidSyscallId => 31,
        }
    }
}

/// AN9-F: 41-variant syscall ID enum mirroring
/// `sele4n-types::SyscallId`.  Discriminants align with the Lean
/// `SyscallId.toNat` encoding so a `u64` syscall id read from the
/// trap frame's `x7` register decodes identically on both sides.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum SyscallId {
    Send = 0,
    Receive = 1,
    Call = 2,
    Reply = 3,
    CSpaceMint = 4,
    CSpaceCopy = 5,
    CSpaceMove = 6,
    CSpaceDelete = 7,
    // 8: retired (the in-place lifecycle retype, WS-ZA ZA5.4 part 14).
    VSpaceMap = 9,
    VSpaceUnmap = 10,
    ServiceRegister = 11,
    ServiceRevoke = 12,
    ServiceQuery = 13,
    NotificationSignal = 14,
    NotificationWait = 15,
    ReplyRecv = 16,
    SchedContextConfigure = 17,
    SchedContextBind = 18,
    SchedContextUnbind = 19,
    TcbSuspend = 20,
    TcbResume = 21,
    TcbSetPriority = 22,
    TcbSetMCPriority = 23,
    TcbSetIPCBuffer = 24,
    // WS-SM SM5.H.4: CPU-affinity configuration (+ run-queue/replenish migration).
    TcbSetAffinity = 25,
    // WS-SM SM6.B: notification binding (bind/unbind a notification to a TCB).
    TcbBindNotification = 26,
    TcbUnbindNotification = 27,
    // WS-SM SM6.D / PR #822 Phase H: derive a `.replyCap` from an `.object` cap to a
    // retyped Reply object.
    MintReplyCap = 28,
    /// WS-SM SM7.D: instruction/data unification of one mapped page.
    VSpaceUnifyInstruction = 29,
    /// WS-SM SM8.C.9: authorize and audit a cross-domain downgrade.
    Declassify = 30,
    /// WS-SM SM9.A.6: read one word of the declassification audit trail,
    /// through a view filtered by the caller's own clearance.
    AuditRead = 31,
    /// WS-SM SM9.A.6: drain a prefix of the declassification audit trail.
    /// Gated on the deployment's configured audit-monitor clearance, which is
    /// what makes the fail-closed 256-entry capacity bound survivable.
    AuditDrain = 32,
    /// WS-SM SM9.C.8: signal a notification whose badge may cross a boundary
    /// the base lattice denies.  Two gated hops — the signaller into the
    /// notification, and the notification onward into the resolved receiver —
    /// with the real delivery performed in between.
    DeclassifySignal = 33,
    /// PR #887 review: install a thread's fault-handler CPtr (seL4's
    /// `TCB_SetSpace` fault endpoint), validated kernel-side at set time.
    TcbSetFaultHandler = 34,
    /// WS-RR RR8.16 (`v0.35.190`): revoke every capability derived from the one
    /// in the named slot (seL4's `seL4_CNode_Revoke`).  The source slot itself
    /// survives — revocation destroys derivations, not the capability.
    CspaceRevoke = 35,
    /// WS-BP BP7.1 (`v0.36.5`): carve a frame out of an untyped the caller
    /// holds (seL4's `seL4_Untyped_Retype`); invoked on the untyped
    /// capability, x2..x5 = type tag, child object id, destination CNode
    /// capability address, destination slot.
    UntypedRetype = 36,
    /// WS-BP BP7.1 (`v0.36.6`): hand an untyped's memory back to it once no
    /// capability names a carved child (seL4's `resetUntypedCap`); invoked on
    /// the untyped capability, with no message registers.
    UntypedReset = 37,
    /// WS-BP BP7.1 (`v0.36.11`): set a suspended thread's CSpace and VSpace
    /// roots (seL4's `TCB_SetSpace`); x2/x3 = capability addresses of the two
    /// roots in the caller's CSpace.
    TcbSetSpace = 38,
    /// WS-BP BP7.1 (`v0.36.12`): install an intermediate page table (seL4's
    /// `seL4_ARM_PageTable_Map`); x2 = the address-space capability address,
    /// x3 = the virtual address.
    PageTableMap = 39,
    /// WS-BP BP7.1 (`v0.36.12`): take one out (`seL4_ARM_PageTable_Unmap`); no
    /// message registers.
    PageTableUnmap = 40,
    /// WS-ZA ZA4.3: give up the rest of the caller's budget or time slice
    /// (`seL4_Yield`); invokes no capability, no message registers.
    Yield = 41,
    /// WS-ZA ZA6.9: read and reset a scheduling context's consumed time
    /// (`seL4_SchedContext_Consumed`); no message registers.
    SchedContextConsumed = 42,
    /// WS-ZA ZA6.29: yield to the thread bound to a scheduling context
    /// (`seL4_SchedContext_YieldTo`); no message registers.
    SchedContextYieldTo = 43,
    /// WS-ZA ZA6.32: acknowledge an interrupt line (`seL4_IRQHandler_Ack`);
    /// no message registers.
    IrqHandlerAck = 44,
    /// WS-ZA ZA6.32: issue an interrupt-handler capability
    /// (`seL4_IRQControl_Get`); x2 the line, x3 the destination CNode, x4 the
    /// slot.
    IrqControlGet = 45,
    /// WS-ZA ZA6.32: bind a notification to an interrupt line
    /// (`seL4_IRQHandler_SetNotification`); x2 the notification capability.
    IrqHandlerSetNotification = 46,
    /// WS-ZA ZA6.32: unbind an interrupt line's notification
    /// (`seL4_IRQHandler_Clear`); no message registers.
    IrqHandlerClear = 47,
}

impl SyscallId {
    /// Total number of modelled syscalls (must match `sele4n-types`).
    pub const COUNT: u32 = 47;

    /// One past the largest syscall number (must match `sele4n-types`).
    pub const ENCODING_BOUND: u32 = 48;

    /// Retired syscall numbers, reserved and never reassigned (must match
    /// `sele4n-types`): `8`, the in-place lifecycle retype.
    pub const RETIRED: [u32; 1] = [8];

    /// AN9-F.1.b: decode a raw `u32` syscall id, rejecting values
    /// at or past `ENCODING_BOUND` and the retired numbers with `None`.
    pub const fn from_u32(v: u32) -> Option<Self> {
        match v {
            0 => Some(Self::Send),
            1 => Some(Self::Receive),
            2 => Some(Self::Call),
            3 => Some(Self::Reply),
            4 => Some(Self::CSpaceMint),
            5 => Some(Self::CSpaceCopy),
            6 => Some(Self::CSpaceMove),
            7 => Some(Self::CSpaceDelete),
            9 => Some(Self::VSpaceMap),
            10 => Some(Self::VSpaceUnmap),
            11 => Some(Self::ServiceRegister),
            12 => Some(Self::ServiceRevoke),
            13 => Some(Self::ServiceQuery),
            14 => Some(Self::NotificationSignal),
            15 => Some(Self::NotificationWait),
            16 => Some(Self::ReplyRecv),
            17 => Some(Self::SchedContextConfigure),
            18 => Some(Self::SchedContextBind),
            19 => Some(Self::SchedContextUnbind),
            20 => Some(Self::TcbSuspend),
            21 => Some(Self::TcbResume),
            22 => Some(Self::TcbSetPriority),
            23 => Some(Self::TcbSetMCPriority),
            24 => Some(Self::TcbSetIPCBuffer),
            25 => Some(Self::TcbSetAffinity),
            26 => Some(Self::TcbBindNotification),
            27 => Some(Self::TcbUnbindNotification),
            28 => Some(Self::MintReplyCap),
            29 => Some(Self::VSpaceUnifyInstruction),
            30 => Some(Self::Declassify),
            31 => Some(Self::AuditRead),
            32 => Some(Self::AuditDrain),
            33 => Some(Self::DeclassifySignal),
            34 => Some(Self::TcbSetFaultHandler),
            35 => Some(Self::CspaceRevoke),
            36 => Some(Self::UntypedRetype),
            37 => Some(Self::UntypedReset),
            38 => Some(Self::TcbSetSpace),
            39 => Some(Self::PageTableMap),
            40 => Some(Self::PageTableUnmap),
            41 => Some(Self::Yield),
            42 => Some(Self::SchedContextConsumed),
            43 => Some(Self::SchedContextYieldTo),
            44 => Some(Self::IrqHandlerAck),
            45 => Some(Self::IrqControlGet),
            46 => Some(Self::IrqHandlerSetNotification),
            47 => Some(Self::IrqHandlerClear),
            _ => None,
        }
    }

    /// AN9-F.1.b: raw discriminant.
    #[inline]
    pub const fn to_u32(self) -> u32 {
        self as u32
    }
}

/// WS-RA: the syscall ABI version this HAL speaks — the seL4 frame
/// convention (`x0` value, kernel status in the top of `x1`'s label range,
/// `x2`-`x5` message registers).  Version 1 was the retired bit-63
/// protocol; version 2 carried the status as label `d + 1`, which made a
/// delivered fault message's `seL4_Fault_tag` decode as a kernel error
/// (retired at WS-RR RR4).  Mirrors
/// `sele4n-types::SYSCALL_ABI_VERSION` and Lean's
/// `Architecture.syscallAbiVersion`.  The HAL carries zero runtime
/// dependencies by design (the mirror discipline documented in
/// `Cargo.toml`), so the cross-crate agreement is pinned where
/// `sele4n-types` is visible: a `#[cfg(test)]` `const` assertion makes
/// any drift fail **test compilation** (not merely a test run), and the
/// abi-crate conformance suite pins the same literal from the userspace
/// side — so a half-bumped tree cannot build its own test lane, let
/// alone pass it (plan §3.6).  The Lean side is a `decide` theorem
/// (`syscallAbiVersion_pinned`), failing the kernel build itself.
pub const SYSCALL_ABI_VERSION: u64 = 4;

/// WS-RR RR4 (ABI v3): the first kernel-status label — `2^52 - 256`, the
/// top 256 labels of seL4's 52-bit field.  Hand-duplicated from
/// `sele4n-types::ERROR_LABEL_BASE` per this crate's zero-runtime-deps
/// discipline; the cross-crate agreement is a `#[cfg(test)]` `const`
/// assertion below (a drift fails test *compilation*), and Lean pins the
/// same literal (`Architecture.errorLabelBase_eq`).
pub const ERROR_LABEL_BASE: u64 = (1 << 52) - 256;

/// WS-RA: number of return-frame mailbox slots — one per core.
pub const RETURN_FRAME_CORES: usize = crate::smp::MAX_SECONDARY_CORES + 1;

/// WS-RA (plan §3.3): the per-core syscall **return-frame mailbox**.
///
/// `lean_syscall_dispatch_cross_core` returns one scalar (the outcome
/// tag) and the FFI deliberately carries no `lean_object*`, so the six
/// return registers cross through this mailbox instead — the
/// `ShootdownOpMailbox` pattern.  Concurrency is trivial by construction,
/// unlike the shootdown mailbox's: slot `c` is written by core `c`'s own
/// syscall entry (via [`ffi_syscall_return_frame`], inside the Lean
/// export) and read by the same core's [`dispatch_svc`] inside the same
/// `with_kernel_entry` critical section, so accesses to a slot are
/// same-core program-ordered and `Relaxed` suffices.
pub struct ReturnFrameMailbox {
    regs: [[core::sync::atomic::AtomicU64; 6]; RETURN_FRAME_CORES],
}

impl ReturnFrameMailbox {
    /// A zeroed mailbox — the frame a slot yields before any syscall is
    /// the `Unit`-success frame (`x0 = 0`, label `0`).
    pub const fn new() -> Self {
        ReturnFrameMailbox {
            regs: [const { [const { core::sync::atomic::AtomicU64::new(0) }; 6] };
                RETURN_FRAME_CORES],
        }
    }
}

impl Default for ReturnFrameMailbox {
    fn default() -> Self {
        Self::new()
    }
}

/// WS-RA: the global per-core return-frame mailbox.
pub static RETURN_FRAMES: ReturnFrameMailbox = ReturnFrameMailbox::new();

/// WS-RA (testable inner form): publish a return frame into `core`'s slot.
/// Fail-closed on an out-of-range core id, like every FFI-facing bound in
/// this crate.
pub fn return_frame_publish_in(mb: &ReturnFrameMailbox, core: usize, regs: [u64; 6]) {
    assert!(
        core < RETURN_FRAME_CORES,
        "return_frame_publish: core {core} out of range"
    );
    for (slot, value) in mb.regs[core].iter().zip(regs.iter()) {
        slot.store(*value, core::sync::atomic::Ordering::Relaxed);
    }
}

/// WS-RA (testable inner form): read `core`'s published return frame.
pub fn return_frame_read_in(mb: &ReturnFrameMailbox, core: usize) -> [u64; 6] {
    assert!(
        core < RETURN_FRAME_CORES,
        "return_frame_read: core {core} out of range"
    );
    let mut out = [0u64; 6];
    for (value, slot) in out.iter_mut().zip(mb.regs[core].iter()) {
        *value = slot.load(core::sync::atomic::Ordering::Relaxed);
    }
    out
}

/// WS-RA RA.C.9: what a completed dispatch hands the trap layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SvcOutcome {
    /// The syscall returned: write `x0`-`x5` back into the caller's trap
    /// frame (the context restore, plan §3.3).  Errors are ordinary
    /// frames whose `x1` label carries the discriminant — this layer
    /// never decodes them (userspace's `decode_response` is the single
    /// decode point, plan §3.2).
    Frame([u64; 6]),
    /// The caller blocked: **no return frame exists for it** (its stale
    /// registers are not a return value; the real frame is staged by the
    /// unblocking arm and delivered by the context restore).  Since WS-BP
    /// BP7.6 the dispatch installs this core's successor and the trap layer
    /// returns through it; this variant is reached only when it installed
    /// nothing, where the hardware would `eret` back INTO the blocked
    /// caller, so the trap layer poisons its frame with
    /// [`blocked_resume_sentinel_regs`]: without the sentinel the
    /// caller's own request registers (an `x1` whose label is typically
    /// `0`) decode as a **false success** — the same fail-open class the
    /// retired pre-WS-RA protocol had (PR #866 review).
    Blocked,
    /// PR #887 review round 5: the caller **took a fault at the seam** — a
    /// failed capability lookup delivered to its fault handler, or the
    /// fail-closed suspend when no handler could take it (outcome tag 2,
    /// `SyscallOutcome.faulted`).  No frame exists, as for `Blocked`; but
    /// the model restarts this caller *at* the `SVC` on its handler's
    /// reply, so the `Blocked` sentinel — which `eret`s the caller past the
    /// `SVC` — would resume a thread the model has waiting on a fault.  The
    /// trap layer returns through the successor the dispatch installed, and
    /// halts on this variant only when it installed nothing, exactly as it
    /// does after a delivered unknown-syscall or abort fault
    /// (`halt_after_delivered_syscall_fault`).
    Faulted,
}

/// WS-RA: the label-encoded error frame for a prefilter rejection —
/// `x0 = 0`, `x1` = `MessageInfo {length 0, extraCaps 0, label
/// ERROR_LABEL_BASE + disc}` = `(ERROR_LABEL_BASE + disc) << 12`, no message
/// registers.  Mirrors Lean's `Architecture.errorFrame` (ABI v3: the status
/// range is the top of the label field, so label `0` means success,
/// discriminant `0` is a real error, and a delivered message's label —
/// always below the base — can never be read as either).
pub fn error_frame_regs(kernel_error_discriminant: u32) -> [u64; 6] {
    [
        0,
        (ERROR_LABEL_BASE + (kernel_error_discriminant as u64)) << 12,
        0,
        0,
        0,
        0,
    ]
}

/// The `x1` label of the blocked-resume sentinel: the maximum value the
/// 52-bit `MessageInfo` label field can carry (`sele4n-abi`'s
/// `MAX_LABEL`, hand-duplicated here per this crate's zero-runtime-deps
/// discipline; the cross-crate agreement is pinned under `#[cfg(test)]`).
///
/// Three properties make it the right sentinel, each pinned by a test:
/// in-field (so `MessageInfo::decode` accepts the word and the failure
/// surfaces at the error mapping, not as a malformed-word artifact),
/// nonzero (never a success), and the **last** label of the status range
/// — `ERROR_LABEL_BASE + 255`, naming discriminant 255, which the Lean
/// `KernelError` does not have and the Rust enumeration reserves for its
/// forward-compatibility sentinel `UnknownKernelError` — so
/// `decode_response` reads it as that variant by construction: an error the
/// verified kernel never emits, hence unambiguously "this is not a completed
/// syscall's frame".
pub const BLOCKED_RESUME_SENTINEL_LABEL: u64 = (1 << 52) - 1;

// Compile-time: the sentinel is the top of the status range and names a
// discriminant (255) beyond the kernel-emittable set `0..=56` (the test
// suite grounds that bound against the canonical `KernelError` space and
// pins 255 to the Rust-only sentinel variant).
const _: () = assert!(BLOCKED_RESUME_SENTINEL_LABEL == ERROR_LABEL_BASE + 255);
const _: () = assert!(BLOCKED_RESUME_SENTINEL_LABEL - ERROR_LABEL_BASE > 56);

/// The poison frame the trap layer writes for a blocked caller that the
/// hardware is about to resume anyway (PR #866 review).
///
/// A blocked caller has **no** return value — its real frame is staged
/// into its TCB by the unblocking arm (plan §4d) and delivered by the
/// context restore (WS-BP BP7.6).  When a dispatch installs no successor,
/// `trap.S` restores and `eret`s through the blocked caller's own saved
/// frame; left
/// untouched, those registers are the caller's request (`x1` typically
/// a label-`0` `MessageInfo`), which `decode_response` reads as a
/// **false success** whose `x0` "badge" is the caller's own capability
/// pointer — the exact fail-open class WS-RA exists to close.  This
/// frame makes that premature resume fail closed instead: label
/// [`BLOCKED_RESUME_SENTINEL_LABEL`] decodes as `UnknownKernelError`,
/// never as success and never as any kernel-emitted error.
///
/// The context restore replaces the whole frame with the successor's
/// before this write could run; the sentinel is the fallback when nothing
/// was installed, not part of the verified return convention (the Lean model stages
/// real frames only — `SyscallOutcome.mailboxFrame .blocks = .zero`).
pub fn blocked_resume_sentinel_regs() -> [u64; 6] {
    [0, BLOCKED_RESUME_SENTINEL_LABEL << 12, 0, 0, 0, 0]
}

/// AN9-F.2 / AN9-F.3 (restated by WS-RA): top-level SVC dispatcher.
///
/// Routes the trap through [`SyscallId::from_u32`] before delegating to
/// the Lean kernel via the
/// `lean_syscall_dispatch_cross_core` extern symbol (Lean-emitted via
/// `@[export lean_syscall_dispatch_cross_core]` in
/// `SeLe4n/Kernel/SyscallDispatchEntry.lean`, which routes into the verified
/// `Kernel.syscallEntryChecked` — with the executing core threaded for per-core
/// caller identification — and fires the diff-recovered cross-core SGIs).
///
/// **WS-RA (the return convention)**: the export returns the outcome
/// **tag** (`0` = the caller's return frame is in this core's
/// [`RETURN_FRAMES`] slot, `1` = the caller blocked) and the frame itself
/// crosses through the mailbox, read back *inside* the same
/// `with_kernel_entry` critical section as the dispatch.  The retired
/// bit-63 word is gone: this layer passes frames through undecoded.
///
/// Returns:
///   `Ok(SvcOutcome::Frame(regs))` — write `regs` into the trap frame.
///   `Ok(SvcOutcome::Blocked)`     — the caller blocked; no return frame
///                                   exists (the trap layer poisons the
///                                   frame with the fail-closed
///                                   [`blocked_resume_sentinel_regs`]
///                                   when the context restore installed no
///                                   successor).
///   `Ok(SvcOutcome::Faulted)`     — the caller took a fault at the seam
///                                   (tag 2); no frame exists and the trap
///                                   layer halts if no successor was
///                                   installed rather than resume the caller past the `SVC`
///                                   its handler's reply restarts it at.
///   `Err(error)`                  — prefilter rejection (invalid syscall
///                                   id); the trap layer
///                                   surfaces it as a label-encoded error
///                                   frame ([`error_frame_regs`]).
pub fn dispatch_svc(syscall_id: u32) -> Result<SvcOutcome, DispatchError> {
    // PR #866 round-2 review: the core index is the TPIDR-derived
    // *logical* id — the same source `ffi_syscall_return_frame` (the
    // mailbox writer) and `ffi_current_core_id` (the Lean dispatch's own
    // `executingCore`) read, and the only per-core index the boot-time
    // `check_per_cpu_invariants` gate validates (`core_id < coreCount`).
    // The packed MPIDR value (`cpu::current_core_id()`) is documented
    // opaque and non-contiguous: on a second-cluster core it reads e.g.
    // `0x100`, which (a) trips the mailbox bounds assert — aborting every
    // syscall on that core — and (b) silently disables the entry-lock
    // spin's shootdown self-service (its out-of-range guard fails closed),
    // recreating the ack deadlock the self-service exists to prevent.
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;

    // WS-RR RR5.6: the per-core readiness gate, which this seam did not
    // consult.  `kernel_entry.rs` stated over its five-entry table that "every
    // hardware seam above therefore also consults the per-core readiness gate
    // before its Lean call"; three of the five did, and this — the
    // highest-traffic route into the Lean runtime — was one of the two that
    // did not.  It is now derived rather than asserted: `build.rs`'s
    // `scan_lean_upcalls_readiness_gated` collects every Lean upcall in the
    // HAL from the Lean tree's `@[export]`s and fails the build unless a
    // readiness guard on the *executing* PE dominates each one.
    //
    // PR #889 review: the gate precedes the prefilter, not only the Lean
    // call.  The halt exists because a thread on a not-ready core can never be
    // preempted again (the timer seam consults the same mask), so *any* frame
    // returned to it hands it the CPU forever — an `invalidSyscallNumber`
    // frame from the prefilter below exactly as much as a dispatched one.
    // Consulting readiness after the prefilter left its rejection as a
    // resumable frame on a not-ready core.
    let (tag, regs) = if crate::lean_ready::lean_ready(core) {
        // AN9-F.1.b: reject ids outside the mirror enum's range.  The
        // message length is the Lean kernel's to check, after the capability
        // lookup, as seL4's decode checks it (`truncationMinimum`).
        if SyscallId::from_u32(syscall_id).is_none() {
            return Err(DispatchError::InvalidSyscallId);
        }

        // AN9-F.2: forward to the Lean-emitted dispatcher.
        //
        // WS-SM SM5.I: serialise kernel entry.  The Lean side commits its
        // post-state through `modifyGetKernelState`, an `IO.Ref.modifyGet`
        // — a read then a write, not a cross-core atomic — so two cores
        // dispatching concurrently would both read the same pre-state and
        // the second write would discard the first core's whole transition
        // while returning success for it.  The bracket makes the read and
        // the write one critical section against every other kernel entry.
        //
        // The lock is taken OUTSIDE any shootdown round lock the transition
        // itself may take (`completeShootdownRounds` takes that one inside
        // here), and its spin self-services this core's pending shootdown
        // obligation — without that a holder blocked on our acknowledgment
        // would deadlock against us, since IRQs are masked on this path and
        // the `.tlbShootdownReq` SGI cannot preempt the spin.
        //
        // WS-RA: the mailbox read happens INSIDE the critical section, so the
        // frame this call returns is the frame this call's commit published.
        crate::kernel_entry::with_kernel_entry(core, || {
            // SAFETY: `lean_syscall_dispatch_cross_core` is a Lean-emitted
            // extern "C" symbol resolved at link time.  It takes no argument:
            // the Lean side reads the syscall number (`x7`) and every argument
            // from the in-flight frame, in one call, the frame it saves into
            // the caller's context (WS-ZA ZA6.27), so no word passed here can
            // disagree with that frame.  `sid` above is this layer's own
            // prefilter, decoded from the same `x7`.
            // Calling it is sound from EL1 kernel context once this core's Lean
            // runtime is initialized — which the gate above just established.
            let tag = unsafe { lean_syscall_dispatch_cross_core() };
            (tag, return_frame_read_in(&RETURN_FRAMES, core))
        })
    } else {
        halt_syscall_before_lean_ready(core, u64::from(syscall_id))
    };

    match tag {
        0 => Ok(SvcOutcome::Frame(regs)),
        1 => Ok(SvcOutcome::Blocked),
        2 => Ok(SvcOutcome::Faulted),
        // `SyscallOutcome.tagWord` is total over {0, 1, 2}; anything else
        // means the FFI boundary itself is broken.  Fail closed and loud,
        // like every impossible-input arm in this crate.
        other => panic!("lean_syscall_dispatch_cross_core returned unknown outcome tag {other}"),
    }
}

// AN9-F.3 inner — Lean-emitted SVC dispatch entry.
//
// In production builds this resolves to the Lean kernel's
// `syscallDispatchCrossCoreEntry` (a BaseIO wrapper around the verified
// `syscallDispatchFromAbi` that threads the executing core for per-core caller
// identification and fires the diff-recovered cross-core SGIs), emitted as the
// C-callable symbol `lean_syscall_dispatch_cross_core` via
// `@[export lean_syscall_dispatch_cross_core]` in
// `SeLe4n/Kernel/SyscallDispatchEntry.lean`.  The Lean wrapper reads the live
// `SystemState` from the kernel-state IO.Ref and dispatches into the
// verified `syscallEntryChecked` entry point.
//
// WS-RA: the scalar return is the OUTCOME TAG (0 = the caller's return
// frame was published into this core's `RETURN_FRAMES` slot via
// `ffi_syscall_return_frame`; 1 = the caller blocked, no frame; 2 = the
// caller faulted at the seam, no frame, and the trap layer halts — PR #887
// review round 5).  The retired bit-63 word is gone.
//
// In test builds (`#[cfg(test)]`) a Rust-side stub publishes the
// label-encoded `KernelError::NotImplemented` error frame and returns
// tag 0, so dispatch logic — including the mailbox read — can be
// exercised on host.
//
// WS-SM SM6.A (LANDED): the live entry is the cross-core-aware
// `lean_syscall_dispatch_cross_core` (`syscallDispatchCrossCoreEntry` in
// `SeLe4n/Kernel/SyscallDispatchEntry.lean`, now in the production library).  It
// runs the same verified `syscallDispatchFromAbi` — with the executing core
// (`currentCoreId`) threaded in, so the caller is identified and descheduled on
// its *own* core — and, after committing the post-state, fires the diff-recovered
// cross-core `.reschedule` SGIs (`computeCrossCoreSgis` + `fireCrossCoreSgis`),
// the syscall analogue of `lean_per_core_timer_tick`.  Single-core-inert (the SGI
// list is empty at the boot core).
//
// **WS-RR RR5.8**: the declaration is gated on `feature = "hw_target"`, not on
// `cfg(not(test))`.  Under the old gating a host build that was not a test
// build — `cargo build -p sele4n-hal`, the default host profile — still
// compiled a call path to a bare-metal Lean symbol that nothing on the host
// provides.  The readiness gate above cannot close that: it decides whether the
// call *executes*, not whether it is *compiled*.  `build.rs`'s
// `scan_lean_externs_hw_target_gated` now refuses any Lean symbol declared,
// defined or called outside a `hw_target` region.
#[cfg(feature = "hw_target")]
extern "C" {
    /// # Safety
    ///
    /// Sound only on a core whose Lean runtime is initialised — the SVC seam
    /// checks `lean_ready` on the executing PE before every outcome, including
    /// its prefilters — and only for an `SVC` taken from EL0, inside the
    /// handler that published the frame (`trap::InFlightFrame`) the Lean side
    /// reads the syscall number and its arguments from (WS-ZA ZA6.27: the
    /// Lean entry fails closed, `.faulted`, on a frame not taken from EL0 or
    /// whose `x7` is no `u32`); the outcome tag the call returns decides
    /// whether the frame may be `eret`ed.
    fn lean_syscall_dispatch_cross_core() -> u64;
}

/// AN9-F.4 host-lane stand-in (WS-RA shape): publishes the label-encoded
/// `KernelError::NotImplemented` (discriminant 17 → label 18) error frame
/// into core 0's mailbox slot and returns outcome tag 0, mirroring what
/// the live export does for a kernel rejection — so host tests exercise
/// the tag/mailbox protocol end to end.
///
/// **WS-RR RR5.8**: this used to be `#[cfg(test)] #[no_mangle] extern "C"`,
/// which had two consequences.  It put `lean_syscall_dispatch_cross_core` — a
/// bare-metal kernel entry point — into the symbol table of every host *test*
/// binary, and it left every other host build with the extern declared under
/// `cfg(not(test))` and nothing defining it, so the default host profile
/// compiled a call path to a symbol nothing on the host provides.  A plain,
/// private Rust `unsafe fn` under `cfg(not(hw_target))` has neither property:
/// it defines no linker-visible symbol, and the `extern "C"` declaration of the
/// real export is confined to `hw_target`, where `build.rs`'s
/// `scan_lean_externs_hw_target_gated` holds it.
///
/// `unsafe` so the call site reads identically on both lanes — the seam's one
/// `unsafe { … }` block is the production form, not an `#[allow(unused_unsafe)]`
/// concession to the host.
///
/// # Safety
///
/// None beyond the call: this stand-in touches only the return-frame mailbox.
#[cfg(not(feature = "hw_target"))]
unsafe fn lean_syscall_dispatch_cross_core() -> u64 {
    return_frame_publish_in(&RETURN_FRAMES, 0, error_frame_regs(17));
    0
}

/// **WS-RR RR5.6**: what an `SVC` does on a core whose Lean runtime is not
/// initialized — halt.
///
/// PR #887 left this decision to RR5 (`trap.rs`, round 3: "what a not-ready
/// core should do with an `SVC` at all is RR5's question").  A fail-closed
/// frame would be architecturally coherent — unlike an abort, the `SVC`
/// advanced the PC — but the per-core timer tick consults the same readiness
/// mask and degrades to record-and-re-arm on a not-ready core, so a thread
/// there is never preempted, never charged budget and never rescheduled:
/// returning an error hands it the CPU forever and converts an initialization
/// defect into a starvation of every other thread on the core.  Halting the
/// core is the only outcome that does not resume the thread.
///
/// PR #889 review: this is the outcome of **every** `SVC` on a not-ready
/// core, whatever `x7` holds — a valid id, an unknown one, a word wider than
/// the ABI can name (`trap.rs` halts before the narrowing), or a short message
/// — because the argument above is about resuming the thread, not about which
/// frame it would resume on.  Hence the raw 64-bit syscall word, not a
/// narrowed id.
///
/// Reachable on hardware only on a core that has not marked itself ready —
/// since WS-BP BP6 none takes an EL0 exception before then; on the host
/// lane `fatal_halt` panics, which the readiness integration tests observe
/// through `catch_unwind`.
pub(crate) fn halt_syscall_before_lean_ready(core: usize, syscall_word: u64) -> ! {
    crate::kprintln!(
        "[core {}] SVC (x7=0x{:x}) before the Lean runtime is initialized on this core; \
         halting fail-closed (a returned frame would never be preempted)",
        core,
        syscall_word
    );
    crate::cpu::fatal_halt()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// **WS-RR RR5.6**: the seam refuses to serve an `SVC` on a core whose Lean
    /// runtime is not initialized, and the refusal is a halt rather than a
    /// return.  On the host lane `cpu::fatal_halt` panics, so reaching the
    /// barrier fails the test loudly — which is what `#[should_panic]` asserts.
    ///
    /// The policy this pins is stated in full on
    /// `halt_syscall_before_lean_ready`: an `SVC` *could* be answered with an
    /// error frame (unlike an abort, the exception advanced the PC), but the
    /// per-core timer tick consults the same mask, so a thread on a not-ready
    /// core would never be preempted again.
    #[test]
    #[should_panic(expected = "fail-closed halt reached")]
    fn syscall_before_lean_ready_halts() {
        halt_syscall_before_lean_ready(3, u64::from(SyscallId::Send.to_u32()));
    }

    #[test]
    fn syscall_id_discriminants_match_lean_abi() {
        // Round-trip every variant.  If a new syscall lands in Lean,
        // this test must be extended in lockstep.
        let mut variants = 0;
        for i in 0..SyscallId::ENCODING_BOUND {
            if SyscallId::RETIRED.contains(&i) {
                assert!(SyscallId::from_u32(i).is_none(), "retired id {} decodes", i);
                continue;
            }
            let sid = SyscallId::from_u32(i).unwrap();
            assert_eq!(sid.to_u32(), i, "round-trip failed at id {}", i);
            variants += 1;
        }
        assert_eq!(variants, SyscallId::COUNT);
        assert!(SyscallId::from_u32(SyscallId::ENCODING_BOUND).is_none());
        assert!(SyscallId::from_u32(255).is_none());
    }

    /// WS-SM SM5.H.4 audit: cross-check the hand-mirrored HAL `SyscallId`
    /// against the canonical `sele4n-types::SyscallId` (the same source the
    /// verified Lean kernel and the `sele4n-abi`/`sele4n-sys` user ABI use).
    /// This catches the exact drift the audit found — a syscall added to Lean
    /// and `sele4n-types` but NOT to this HAL trap-dispatcher mirror, which
    /// would reject the syscall at the trap boundary before it reaches the kernel.
    /// The previous self-referential round-trip (against this enum's own COUNT)
    /// could not detect a missing variant.
    #[test]
    fn syscall_id_mirror_matches_sele4n_types() {
        // Counts, bounds and retired numbers agree.
        assert_eq!(
            SyscallId::COUNT as usize,
            sele4n_types::SyscallId::COUNT,
            "HAL SyscallId::COUNT drifted from sele4n-types"
        );
        assert_eq!(
            u64::from(SyscallId::ENCODING_BOUND),
            sele4n_types::SyscallId::ENCODING_BOUND
        );
        assert_eq!(
            SyscallId::RETIRED.map(u64::from),
            sele4n_types::SyscallId::RETIRED
        );
        // Every canonical discriminant decodes to a HAL variant with the same
        // raw u32, and vice-versa (the boundary is exactly [0, ENCODING_BOUND)
        // less the retired numbers, which neither decodes).
        for i in 0..SyscallId::ENCODING_BOUND {
            let Some(canonical) = sele4n_types::SyscallId::from_u64(u64::from(i)) else {
                assert!(
                    SyscallId::from_u32(i).is_none(),
                    "HAL decodes id {i} the canonical set lacks"
                );
                continue;
            };
            assert_eq!(
                canonical.to_u64(),
                u64::from(i),
                "sele4n-types round-trip failed at id {i}"
            );
            let hal =
                SyscallId::from_u32(i).expect("HAL mirror must decode every canonical syscall id");
            assert_eq!(
                hal.to_u32(),
                i,
                "HAL mirror discriminant drifted from sele4n-types at id {i}"
            );
        }
        // The first out-of-range id is rejected by BOTH.
        let oob = SyscallId::ENCODING_BOUND;
        assert!(SyscallId::from_u32(oob).is_none());
        assert!(sele4n_types::SyscallId::from_u64(u64::from(oob)).is_none());
    }

    // PR #889 review: `dispatch_svc_rejects_invalid_syscall_id` moved out of
    // this binary.  The readiness gate precedes the prefilter, so what an
    // invalid id does depends on whether this core is ready — and core 0's
    // readiness bit is set mid-run by the timer suite in this binary, so
    // neither answer can be asserted here.  The not-ready answer (halt) is
    // `tests/readiness_gate_before_mark.rs`; the ready answer (the prefilter
    // refusal) is `tests/readiness_gate_after_mark.rs`.

    // WS-RR RR5.6: `dispatch_svc_routes_to_inner_dispatcher` moved to
    // `tests/readiness_gate_after_mark.rs` — reaching the dispatch stand-in
    // means marking core 0 ready, and the timer suite in this binary owns that
    // bit.  See that file's header.

    #[test]
    fn dispatch_error_surfaces_as_kernel_error_discriminants() {
        // WS-RA: the prefilter rejection surfaces as a real KernelError
        // discriminant on the x1 label — InvalidSyscallNumber = 31 —
        // retiring the legacy raw 7 / 6
        // x0 writes and their documented collision with
        // EndpointStateMismatch / SchedulerInvariantViolation.
        assert_eq!(
            DispatchError::InvalidSyscallId.kernel_error_discriminant(),
            31
        );
        // Pinned against the canonical enum, not just literals.
        assert_eq!(
            DispatchError::InvalidSyscallId.kernel_error_discriminant(),
            sele4n_types::KernelError::InvalidSyscallNumber as u32
        );
    }

    // WS-RA (plan 3.6): the HAL mirror and the sele4n-types canonical
    // constant must agree, and the agreement must fail at test
    // *compilation* — a `const` assertion, not a runtime `assert_eq!` —
    // so a half-bumped tree cannot even build the test lane.  Lean pins
    // the same literal via `syscallAbiVersion_pinned` (a `decide`
    // theorem, failing the kernel build), and the abi-crate conformance
    // suite pins its own read of the canonical constant.
    const _: () = assert!(SYSCALL_ABI_VERSION == sele4n_types::SYSCALL_ABI_VERSION);
    // WS-RR RR4 (ABI v3): the status-range base mirror, held to the canonical
    // constant the same way.
    const _: () = assert!(ERROR_LABEL_BASE == sele4n_types::ERROR_LABEL_BASE);

    #[test]
    fn syscall_abi_version_matches_canonical_pin() {
        // The literal itself, pinned at runtime so a coordinated bump of
        // both mirrors without a protocol change still surfaces here.
        assert_eq!(SYSCALL_ABI_VERSION, 4);
        assert_eq!(ERROR_LABEL_BASE, 0xF_FFFF_FFFF_FF00);
    }

    #[test]
    fn return_frame_mailbox_roundtrip() {
        // WS-RA: the per-core mailbox round-trips a frame per slot and
        // slots are independent.
        let mb = ReturnFrameMailbox::new();
        return_frame_publish_in(&mb, 0, [1, 2, 3, 4, 5, 6]);
        return_frame_publish_in(&mb, 1, [7, 8, 9, 10, 11, 12]);
        assert_eq!(return_frame_read_in(&mb, 0), [1, 2, 3, 4, 5, 6]);
        assert_eq!(return_frame_read_in(&mb, 1), [7, 8, 9, 10, 11, 12]);
        // A fresh slot reads as the Unit-success frame (all zero).
        assert_eq!(return_frame_read_in(&mb, 2), [0; 6]);
    }

    #[test]
    fn error_frame_regs_offsets_every_discriminant() {
        // WS-RA / ABI v3: every KernelError discriminant 0..=60 rides the
        // x1 label at ERROR_LABEL_BASE + disc (label 0 is success;
        // discriminant 0 is a real error — the aliasing the offset from
        // zero exists to prevent; and every label below the base is a
        // delivered message's own, so no error can be read as a delivery
        // either), and no other register carries anything.
        for disc in 0..=60u32 {
            let regs = error_frame_regs(disc);
            assert_eq!(
                regs[1] >> 12,
                ERROR_LABEL_BASE + (disc as u64),
                "label must be ERROR_LABEL_BASE + disc"
            );
            assert_ne!(regs[1] >> 12, 0, "no error may alias the success label");
            assert!(
                regs[1] >> 12 >= ERROR_LABEL_BASE,
                "no error may fall into the delivery label range"
            );
            assert!(
                regs[1] >> 12 <= BLOCKED_RESUME_SENTINEL_LABEL,
                "label must stay in-field"
            );
            assert_eq!(regs[1] & 0x1FF, 0, "length/extraCaps must be zero");
            assert_eq!([regs[0], regs[2], regs[3], regs[4], regs[5]], [0; 5]);
            // …and the userspace decoder reads it back as that error.
            let mut frame = [0u64; 7];
            frame[..6].copy_from_slice(&regs);
            assert_eq!(
                sele4n_abi::decode_response(frame),
                Err(sele4n_types::KernelError::from_u32(disc)
                    .unwrap_or(sele4n_types::KernelError::UnknownKernelError))
            );
        }
        // The four fault tags a handler receives are deliveries, not status:
        // the property v2 lacked.
        for tag in [1u64, 2, 3, 6] {
            let resp = sele4n_abi::decode_response([0, tag << 12, 0, 0, 0, 0, 0])
                .expect("a fault tag label is a delivery");
            assert_eq!(resp.msg_info().label(), tag);
        }
    }

    /// WS-RA (PR #866 review): the blocked-resume sentinel's raw shape —
    /// `x0 = 0`, `x1` = the maximum in-field label, no message registers —
    /// and the three properties that make the label the right sentinel.
    #[test]
    fn blocked_resume_sentinel_shape() {
        let regs = blocked_resume_sentinel_regs();
        assert_eq!(regs[1] >> 12, BLOCKED_RESUME_SENTINEL_LABEL);
        assert_eq!(regs[1] & 0x1FF, 0, "length/extraCaps must be zero");
        assert_eq!([regs[0], regs[2], regs[3], regs[4], regs[5]], [0; 5]);
        // In-field: the hand-duplicated label equals the canonical
        // `sele4n-abi` MAX_LABEL, so `MessageInfo::decode` accepts the
        // word and the failure surfaces at the error mapping — the
        // sentinel is "no kernel emitted this", not "malformed word".
        assert_eq!(
            BLOCKED_RESUME_SENTINEL_LABEL,
            sele4n_abi::message_info::MAX_LABEL,
        );
        let mi = sele4n_abi::MessageInfo::decode(regs[1]).expect("sentinel x1 must be in-field");
        assert_eq!(mi.label(), BLOCKED_RESUME_SENTINEL_LABEL);
        // Nonzero (never success) and the last label of the status range,
        // naming discriminant 255 — beyond the kernel-emittable set
        // 0..=60, and exactly the Rust-only `UnknownKernelError` sentinel.
        // The range position is a compile-time assert at the constant's
        // definition; these GROUND the 60 against the canonical KernelError
        // space (`DepthMismatch` is the last real discriminant, 61 the
        // first unknown) and the 255 against the sentinel variant.
        assert_ne!(BLOCKED_RESUME_SENTINEL_LABEL, 0);
        assert_eq!(BLOCKED_RESUME_SENTINEL_LABEL - ERROR_LABEL_BASE, 255);
        assert!(sele4n_types::KernelError::from_u32(60).is_some());
        assert!(sele4n_types::KernelError::from_u32(61).is_none());
        assert_eq!(
            sele4n_types::KernelError::from_u32(255),
            Some(sele4n_types::KernelError::UnknownKernelError)
        );
        for disc in 0..=60u32 {
            assert_ne!(
                error_frame_regs(disc)[1],
                regs[1],
                "sentinel must not collide with the discriminant-{disc} error frame",
            );
        }
    }

    /// WS-RA (PR #866 review): the cross-crate pin — the canonical
    /// userspace decoder reads the sentinel as `UnknownKernelError`, an
    /// error the verified kernel never emits.  This is the property the
    /// trap-layer write exists for: a blocked caller that the hardware
    /// resumes with no context restored
    /// observes a fail-closed error, never a false success built from its
    /// own stale request registers.
    #[test]
    fn blocked_resume_sentinel_decodes_fail_closed() {
        let s = blocked_resume_sentinel_regs();
        let decoded = sele4n_abi::decode_response([s[0], s[1], s[2], s[3], s[4], s[5], 0]);
        assert_eq!(decoded, Err(sele4n_types::KernelError::UnknownKernelError));
        // The load-bearing negative: WITHOUT the sentinel the resumed
        // caller's frame is its own request — x1 a label-0 MessageInfo,
        // x0 its capability pointer — which decodes as a SUCCESS whose
        // "badge" is the cap pointer.  This is the fail-open path the
        // sentinel closes.
        let stale_request = [7u64, 0, 0, 0, 0, 0, 0];
        let stale = sele4n_abi::decode_response(stale_request).expect("stale request decodes Ok");
        assert_eq!(stale.value(), 7, "the false 'badge' is the cap pointer");
    }

    #[test]
    fn syscall_id_from_u32_names_the_late_ids() {
        assert_eq!(SyscallId::from_u32(34), Some(SyscallId::TcbSetFaultHandler));
        assert_eq!(SyscallId::from_u32(35), Some(SyscallId::CspaceRevoke));
        assert_eq!(SyscallId::from_u32(36), Some(SyscallId::UntypedRetype));
        assert_eq!(SyscallId::from_u32(37), Some(SyscallId::UntypedReset));
        assert_eq!(SyscallId::from_u32(38), Some(SyscallId::TcbSetSpace));
        assert_eq!(SyscallId::from_u32(39), Some(SyscallId::PageTableMap));
        assert_eq!(SyscallId::from_u32(40), Some(SyscallId::PageTableUnmap));
        assert_eq!(SyscallId::from_u32(41), Some(SyscallId::Yield));
        assert_eq!(SyscallId::from_u32(44), Some(SyscallId::IrqHandlerAck));
        assert_eq!(SyscallId::from_u32(45), Some(SyscallId::IrqControlGet));
        assert_eq!(SyscallId::from_u32(47), Some(SyscallId::IrqHandlerClear));
        assert_eq!(SyscallId::from_u32(48), None);
        assert_eq!(
            SyscallId::from_u32(42),
            Some(SyscallId::SchedContextConsumed)
        );
        assert_eq!(
            SyscallId::from_u32(43),
            Some(SyscallId::SchedContextYieldTo)
        );
        assert_eq!(
            SyscallId::from_u32(46),
            Some(SyscallId::IrqHandlerSetNotification)
        );
    }
}
