// SPDX-License-Identifier: GPL-3.0-or-later
//! AN9-F (DEF-R-HAL-L14 / RESOLVED): Typed SVC argument marshalling.
//!
//! This module owns the typed-argument extraction for SVC traps.  The
//! `handle_svc` entry in `trap.rs` reads the raw `TrapFrame`, calls
//! [`SyscallArgs::from_trap_frame`] to produce a structured view, and
//! then dispatches to the Lean kernel via [`dispatch_svc`].
//!
//! ## Mirror discipline
//!
//! `SyscallId` here mirrors the 34-variant enum in
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
//! x0..x5 : msg_regs[0..6]      (inline message registers)
//! x6     : ipc_buffer_addr     (caller's TPIDRRO_EL0; optional)
//! x7     : syscall_id          (SyscallId enum discriminant)
//! ```
//!
//! `MessageInfo` is packed into `x1` per AK4 ABI conventions (length,
//! extraCaps, label fields); the dispatcher passes it through opaquely
//! to the Lean side, which decodes via `SeLe4n.Model.MessageInfo.mk`.

use crate::trap::TrapFrame;

/// AN9-F + WS-RA: the dispatcher's **prefilter** rejections.
///
/// Post-WS-RA this type carries only the two rejections `dispatch_svc`
/// itself makes before reaching the Lean kernel.  The former
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
/// trap layer now maps these to label-encoded
/// `KernelError::InvalidSyscallNumber` / `InvalidSyscallArgument` frames
/// ([`error_frame_regs`]), so a prefilter rejection is indistinguishable
/// in *shape* from a kernel rejection and collides with nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DispatchError {
    /// Caller passed a syscall id outside the valid `0..SyscallId::COUNT`
    /// range.  Surfaced to userspace as `KernelError::InvalidSyscallNumber`
    /// on the `x1` label.
    InvalidSyscallId,
    /// Caller passed an argument count below the syscall's minimum
    /// (validated against `MessageInfo.length`).  Surfaced to userspace as
    /// `KernelError::InvalidSyscallArgument` on the `x1` label.
    InvalidArgument,
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
            DispatchError::InvalidArgument => 41,
        }
    }
}

/// AN9-F: 35-variant syscall ID enum mirroring
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
    LifecycleRetype = 8,
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
}

impl SyscallId {
    /// Total number of modelled syscalls (must match `sele4n-types`).
    pub const COUNT: u32 = 35;

    /// AN9-F.1.b: decode a raw `u32` syscall id, rejecting values
    /// outside the valid 0..=33 range with `None`.
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
            8 => Some(Self::LifecycleRetype),
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
            _ => None,
        }
    }

    /// AN9-F.1.b: raw discriminant.
    #[inline]
    pub const fn to_u32(self) -> u32 {
        self as u32
    }

    /// AN9-F.1.c: number of inline message registers consumed by this
    /// syscall.  Used to validate `MessageInfo.length` at the
    /// per-syscall handler stub before forwarding to Lean.
    ///
    /// Values are conservative ABI minimums per AK4; some syscalls
    /// (e.g., `ServiceRegister`) accept additional registers via the
    /// IPC buffer overflow region (see AK4-A R-ABI-C01).
    pub const fn min_inline_args(self) -> u32 {
        match self {
            Self::Send | Self::Receive | Self::Reply => 0,
            Self::Call => 0,
            // WS-RA (RA.D.1): reconciled with the Lean decoders, which are
            // the authority — `decodeCSpaceMintArgs` reads exactly FOUR
            // registers (srcSlot, dstSlot, rights, badge), `decodeCSpaceCopyArgs`
            // (shared by move) exactly TWO, and `decodeLifecycleRetypeArgs`
            // exactly THREE.  The previous minimums (5 / 4 / 4 / 4) exceeded
            // what the wrappers send (`cspace_mint` length 4, `cspace_copy` /
            // `cspace_move` 2, `lifecycle_retype` 3), so this gate rejected
            // every one of those calls with `InvalidArgument` before the
            // kernel — four wrappers unreachable on hardware, the same
            // off-by-N class the `TcbSetPriority` note below records.
            Self::CSpaceMint => 4,
            Self::CSpaceCopy => 2,
            Self::CSpaceMove => 2,
            Self::CSpaceDelete => 1,
            Self::LifecycleRetype => 3,
            Self::VSpaceMap => 4,
            Self::VSpaceUnmap => 2,
            Self::ServiceRegister => 4,
            Self::ServiceRevoke => 1,
            // WS-RA (RA.D.1, found by the wrapper-length conformance pin):
            // the `.serviceQuery` arm reads NO message registers — the
            // endpoint comes from the capability target — and the wrapper
            // sends length 0.  The previous minimum of 1 rejected every
            // call, the fifth unreachable-wrapper instance of this class.
            Self::ServiceQuery => 0,
            Self::NotificationSignal => 1,
            Self::NotificationWait => 0,
            Self::ReplyRecv => 0,
            Self::SchedContextConfigure => 5,
            // PR #866 round-3 review (the RA.D.1 unreachable-wrapper class,
            // four MORE instances): reconciled with the Lean decoders, the
            // authority.  `decodeSchedContextBindArgs` reads exactly ONE
            // register (`requireMsgReg msgRegs 0`, the thread id);
            // `decodeSchedContextUnbindArgs`, `decodeSuspendArgs` and
            // `decodeResumeArgs` read NONE (`pure {}` — the target comes
            // from the capability).  The previous minimums (2 / 1 / 1 / 1)
            // exceeded what the wrappers send (1 / 0 / 0 / 0), so this gate
            // rejected every one of those calls with `InvalidArgument`
            // before the kernel.  Caught by the rebuilt
            // `wrapper_lengths_clear_prefilter_minimums` sweep, which now
            // drives the REAL wrappers against THIS real table.
            Self::SchedContextBind => 1,
            Self::SchedContextUnbind => 0,
            Self::TcbSuspend => 0,
            Self::TcbResume => 0,
            // Each of these reads exactly ONE inline register (`requireMsgReg
            // decoded.msgRegs 0` in `decodeSet{Priority,MCPriority,IPCBuffer}Args`,
            // whose docstrings state "Requires 1 message register").  The matching
            // `sele4n-sys` wrappers send `MessageInfo::new_const(1, 0, 0)` (length 1),
            // so a minimum of 2 rejected every valid call at `dispatch_svc`'s
            // `len < min_inline_args` gate (`1 < 2`), making these three TCB
            // management syscalls unreachable on hardware before reaching the
            // verified kernel.  The ABI contract is one inline register.
            Self::TcbSetPriority => 1,
            Self::TcbSetMCPriority => 1,
            Self::TcbSetIPCBuffer => 1,
            // WS-SM SM5.H.4: x2 = the raw affinity word (1 inline register).
            Self::TcbSetAffinity => 1,
            // PR #887 review: x2 = the fault-handler CPtr (1 inline register,
            // `requireMsgReg 0` in `decodeSetFaultHandlerArgs`).
            Self::TcbSetFaultHandler => 1,
            // WS-SM SM6.B: bind takes 1 register (notification id); unbind none.
            Self::TcbBindNotification => 1,
            Self::TcbUnbindNotification => 0,
            // PR #822 Phase H: mintReplyCap reuses the cspaceCopy decode (srcSlot in
            // x2, dstSlot in x3) — two inline registers.
            Self::MintReplyCap => 2,
            // WS-SM SM7.D: unify takes the same two registers as unmap
            // (asid in x2, vaddr in x3) — it names an address space and a page.
            Self::VSpaceUnifyInstruction => 2,
            // WS-SM SM8.C.9: declassify takes **no** inline argument registers.
            // The operand is the capability itself (which names the target
            // object), and both security domains are resolved kernel-side — the
            // source from the subject the executing core is running, the
            // destination from the target object.  A caller that could supply
            // either would be writing its own audit record.
            Self::Declassify => 0,
            // WS-SM SM9.A.10: the reader takes THREE inline registers
            // (`decodeAuditReadArgs`: opcode, view index, chunk index) and the
            // drain ONE (`decodeAuditDrainArgs`: the count of entries to
            // remove).  Reconciled against the Lean decoders, which are the
            // authority — the RA.D.1 unreachable-wrapper class this table has
            // now produced nine instances of.
            Self::AuditRead => 3,
            Self::AuditDrain => 1,
            // WS-SM SM9.C.8: the declassifying signal reuses the ordinary
            // signal's decode (`decodeNotificationSignalArgs`) — the badge in
            // x2, one inline register.  Neither security domain is an operand,
            // for the reason `Declassify` takes none: the source is read off
            // the subject the executing core is running and the two
            // destinations off the notification and its resolved receiver.
            Self::DeclassifySignal => 1,
        }
    }
}

/// AN9-F.1.a: typed view of an SVC trap frame's argument registers.
///
/// Constructed from a `TrapFrame` via [`SyscallArgs::from_trap_frame`].
/// The Lean side decodes this struct via the pre-existing
/// `decodeSyscallArgsFromState` helper (`SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`).
#[derive(Debug, Clone, Copy)]
pub struct SyscallArgs {
    /// Packed `MessageInfo` field (length | extraCaps | label).
    pub msg_info: u64,
    /// Inline message registers `x0..x5` (`msg_regs[0..6]`).
    pub msg_regs: [u64; 6],
    /// Caller's IPC buffer address from `x6` (`TPIDRRO_EL0`).  Set to
    /// `None` when the field is zero (no IPC buffer registered).
    pub ipc_buffer_addr: Option<u64>,
    /// PR #887 review round 3: the `SVC`'s return address (`ELR_EL1`).  A
    /// blocking IPC syscall whose capability lookup fails is not answered
    /// with an error frame — seL4's `handleInvocation` / `handleRecv`
    /// deliver a `CapFault` to the thread's fault handler — and that fault's
    /// message reports the faulting `SVC` (`ELR_EL1 - 4`) as the restart PC.
    pub elr: u64,
    /// The saved PSTATE (`SPSR_EL1`), carried outbound in the fault context
    /// and never written back (the fail-closed half of `sanitiseRegister`).
    pub spsr: u64,
    /// `SP_EL0` — the fault window's stack pointer.
    pub sp_el0: u64,
    /// `x30` — the fault window's link register.
    pub x30: u64,
}

impl SyscallArgs {
    /// AN9-F.1.a: extract the typed argument view from a trap frame.
    ///
    /// Layout per `arm64DefaultLayout`:
    ///   `x1` = `msg_info`
    ///   `x0..x5` = `msg_regs[0..6]`
    ///   `x6` = `ipc_buffer_addr` (zero ⇒ `None`)
    ///
    /// Note that `x7` is the `syscall_id` and is read separately by
    /// the dispatcher; it is NOT part of [`SyscallArgs`].
    ///
    /// PR #887 review round 3: `ELR_EL1`, `SPSR_EL1`, `SP_EL0` and `x30`
    /// cross too, so a capability fault raised by the Lean dispatcher can
    /// build its context from the trap frame's window rather than from the
    /// register mirror's stale last-syscall contents.
    pub fn from_trap_frame(frame: &TrapFrame) -> Self {
        let raw_buf = frame.gprs[6];
        Self {
            msg_info: frame.x1(),
            msg_regs: [
                frame.x0(),
                frame.x1(),
                frame.x2(),
                frame.x3(),
                frame.x4(),
                frame.x5(),
            ],
            ipc_buffer_addr: if raw_buf == 0 { None } else { Some(raw_buf) },
            elr: frame.elr_el1,
            spsr: frame.spsr_el1,
            sp_el0: frame.sp_el0,
            x30: frame.gprs[30],
        }
    }

    /// AN9-F.1.c (layout corrected by WS-RA RA.C.3): extract the `length`
    /// field from `msg_info`.  The MessageInfo layout — one layout, three
    /// mirrors (`SeLe4n.Model.MessageInfo.encode`,
    /// `sele4n-abi/src/message_info.rs`, and this reader) — is
    ///   bits  [ 6: 0] = length      (≤ 120)
    ///   bits  [ 8: 7] = extraCaps   (≤ 3)
    ///   bits  [28: 9] = label       (20 bits)
    /// The previous reader here masked `0x0FFF` under a doc comment
    /// claiming a `length[11:0] / extraCaps[13:12] / label[63:14]` packing
    /// that nothing else in the tree used — so any request with a nonzero
    /// extraCaps or label over-read its length (harmless only because the
    /// authoritative Lean decode re-validates fail-closed downstream;
    /// load-bearing now that WS-RA makes `x1` layouts carry the return
    /// convention in both directions).
    #[inline]
    pub fn message_length(&self) -> u32 {
        (self.msg_info & 0x7F) as u32
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
pub const SYSCALL_ABI_VERSION: u64 = 3;

/// WS-RR RR4 (ABI v3): the first kernel-status label — `0xFFF00`, the top
/// 256 labels of the 20-bit field.  Hand-duplicated from
/// `sele4n-types::ERROR_LABEL_BASE` per this crate's zero-runtime-deps
/// discipline; the cross-crate agreement is a `#[cfg(test)]` `const`
/// assertion below (a drift fails test *compilation*), and Lean pins the
/// same literal (`Architecture.errorLabelBase_eq`).
pub const ERROR_LABEL_BASE: u64 = (1 << 20) - 256;

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
    /// unblocking arm and delivered by the SM10.1 context restore).  This
    /// variant is that seam's trap-layer hook — when
    /// `contextRestoreSeamLive` flips, the trap layer installs a runnable
    /// successor's context here.  Until then the hardware `eret`s back
    /// INTO the blocked caller, so the trap layer must poison its frame
    /// with [`blocked_resume_sentinel_regs`]: without the sentinel the
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
    /// trap layer halts on this variant pending the SM10.1 successor
    /// install, exactly as it does after a delivered unknown-syscall or
    /// abort fault (`halt_after_delivered_syscall_fault`).
    Faulted,
}

/// WS-RA: the label-encoded error frame for a prefilter rejection —
/// `x0 = 0`, `x1` = `MessageInfo {length 0, extraCaps 0, label
/// ERROR_LABEL_BASE + disc}` = `(ERROR_LABEL_BASE + disc) << 9`, no message
/// registers.  Mirrors Lean's `Architecture.errorFrame` (ABI v3: the status
/// range is the top of the label field, so label `0` means success,
/// discriminant `0` is a real error, and a delivered message's label —
/// always below the base — can never be read as either).
pub fn error_frame_regs(kernel_error_discriminant: u32) -> [u64; 6] {
    [
        0,
        (ERROR_LABEL_BASE + (kernel_error_discriminant as u64)) << 9,
        0,
        0,
        0,
        0,
    ]
}

/// The `x1` label of the blocked-resume sentinel: the maximum value the
/// 20-bit `MessageInfo` label field can carry (`sele4n-abi`'s
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
pub const BLOCKED_RESUME_SENTINEL_LABEL: u64 = (1 << 20) - 1;

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
/// SM10.1 context restore.  Until `contextRestoreSeamLive` flips, the
/// trap path cannot install a successor, so `trap.S` restores and
/// `eret`s through the blocked caller's own saved frame; left
/// untouched, those registers are the caller's request (`x1` typically
/// a label-`0` `MessageInfo`), which `decode_response` reads as a
/// **false success** whose `x0` "badge" is the caller's own capability
/// pointer — the exact fail-open class WS-RA exists to close.  This
/// frame makes that premature resume fail closed instead: label
/// [`BLOCKED_RESUME_SENTINEL_LABEL`] decodes as `UnknownKernelError`,
/// never as success and never as any kernel-emitted error.
///
/// The SM10.1 context restore REPLACES the write with the successor's
/// frame install; the sentinel is the interim occupant of that seam,
/// not part of the verified return convention (the Lean model stages
/// real frames only — `SyscallOutcome.mailboxFrame .blocks = .zero`).
pub fn blocked_resume_sentinel_regs() -> [u64; 6] {
    [0, BLOCKED_RESUME_SENTINEL_LABEL << 9, 0, 0, 0, 0]
}

/// AN9-F.2 / AN9-F.3 (restated by WS-RA): top-level SVC dispatcher.
///
/// Routes the trap through [`SyscallId::from_u32`] and validates the
/// inline-argument count against [`SyscallId::min_inline_args`] before
/// delegating to the Lean kernel via the
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
///                                   until the SM10.1 context restore
///                                   installs a successor instead).
///   `Ok(SvcOutcome::Faulted)`     — the caller took a fault at the seam
///                                   (tag 2); no frame exists and the trap
///                                   layer halts pending SM10.1 rather
///                                   than resume the caller past the `SVC`
///                                   its handler's reply restarts it at.
///   `Err(error)`                  — prefilter rejection (invalid syscall
///                                   id / argument count); the trap layer
///                                   surfaces it as a label-encoded error
///                                   frame ([`error_frame_regs`]).
pub fn dispatch_svc(syscall_id: u32, args: &SyscallArgs) -> Result<SvcOutcome, DispatchError> {
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
    // PR #889 review: the gate precedes **every** prefilter, not only the Lean
    // call.  The halt exists because a thread on a not-ready core can never be
    // preempted again (the timer seam consults the same mask), so *any* frame
    // returned to it hands it the CPU forever — an `invalidSyscallNumber` or
    // `invalidArgument` frame from the prefilters below exactly as much as a
    // dispatched one.  Consulting readiness after the prefilters left both
    // rejections as resumable frames on a not-ready core.
    let (tag, regs) = if crate::lean_ready::lean_ready(core) {
        // AN9-F.1.b: reject ids outside the mirror enum's range.
        let sid = match SyscallId::from_u32(syscall_id) {
            Some(sid) => sid,
            None => return Err(DispatchError::InvalidSyscallId),
        };

        // AN9-F.1.c: validate the inline-arg count from MessageInfo.length
        let len = args.message_length();
        if len < sid.min_inline_args() {
            return Err(DispatchError::InvalidArgument);
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
            // extern "C" symbol resolved at link time.  The arguments cross
            // the FFI boundary as `u32 + 12 × u64` which the Lean side reads
            // via the @[extern] declaration in
            // `SeLe4n/Kernel/SyscallDispatchEntry.lean`.  Calling it is sound
            // from EL1 kernel context once this core's Lean runtime is
            // initialized — which the gate above just established.
            let tag = unsafe {
                lean_syscall_dispatch_cross_core(
                    sid.to_u32(),
                    args.msg_info,
                    args.msg_regs[0],
                    args.msg_regs[1],
                    args.msg_regs[2],
                    args.msg_regs[3],
                    args.msg_regs[4],
                    args.msg_regs[5],
                    args.ipc_buffer_addr.unwrap_or(0),
                    args.elr,
                    args.spsr,
                    args.sp_el0,
                    args.x30,
                )
            };
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
    fn lean_syscall_dispatch_cross_core(
        syscall_id: u32,
        msg_info: u64,
        x0: u64,
        x1: u64,
        x2: u64,
        x3: u64,
        x4: u64,
        x5: u64,
        ipc_buffer_addr: u64,
        elr: u64,
        spsr: u64,
        sp_el0: u64,
        x30: u64,
    ) -> u64;
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
#[allow(clippy::too_many_arguments)]
unsafe fn lean_syscall_dispatch_cross_core(
    _syscall_id: u32,
    _msg_info: u64,
    _x0: u64,
    _x1: u64,
    _x2: u64,
    _x3: u64,
    _x4: u64,
    _x5: u64,
    _ipc_buffer_addr: u64,
    _elr: u64,
    _spsr: u64,
    _sp_el0: u64,
    _x30: u64,
) -> u64 {
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
/// Reachable on hardware only before SM10.1 marks the core ready; on the host
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

    fn zero_frame() -> TrapFrame {
        TrapFrame {
            gprs: [0; 31],
            sp_el0: 0,
            elr_el1: 0,
            spsr_el1: 0,
            esr_el1: 0,
            far_el1: 0,
        }
    }

    #[test]
    fn syscall_id_discriminants_match_lean_abi() {
        // Round-trip every variant.  If a new syscall lands in Lean,
        // this test must be extended in lockstep.
        for i in 0..SyscallId::COUNT {
            let sid = SyscallId::from_u32(i).unwrap();
            assert_eq!(sid.to_u32(), i, "round-trip failed at id {}", i);
        }
        assert!(SyscallId::from_u32(SyscallId::COUNT).is_none());
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
        // Counts agree.
        assert_eq!(
            SyscallId::COUNT as usize,
            sele4n_types::SyscallId::COUNT,
            "HAL SyscallId::COUNT drifted from sele4n-types"
        );
        // Every canonical discriminant decodes to a HAL variant with the same
        // raw u32, and vice-versa (the boundary is exactly [0, COUNT)).
        for i in 0..sele4n_types::SyscallId::COUNT as u32 {
            let canonical = sele4n_types::SyscallId::from_u64(u64::from(i))
                .expect("canonical syscall id must decode");
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
        let oob = sele4n_types::SyscallId::COUNT as u32;
        assert!(SyscallId::from_u32(oob).is_none());
        assert!(sele4n_types::SyscallId::from_u64(u64::from(oob)).is_none());
    }

    #[test]
    fn syscall_args_from_trap_frame_extracts_x0_to_x5() {
        let mut frame = zero_frame();
        frame.gprs[0] = 0x1111;
        frame.gprs[1] = 0x2222;
        frame.gprs[2] = 0x3333;
        frame.gprs[3] = 0x4444;
        frame.gprs[4] = 0x5555;
        frame.gprs[5] = 0x6666;
        frame.gprs[6] = 0x7777;
        let args = SyscallArgs::from_trap_frame(&frame);
        assert_eq!(
            args.msg_regs,
            [0x1111, 0x2222, 0x3333, 0x4444, 0x5555, 0x6666]
        );
        assert_eq!(args.ipc_buffer_addr, Some(0x7777));
        // msg_info comes from x1
        assert_eq!(args.msg_info, 0x2222);
    }

    #[test]
    fn syscall_args_zero_ipc_buffer_decodes_to_none() {
        let mut frame = zero_frame();
        frame.gprs[6] = 0;
        let args = SyscallArgs::from_trap_frame(&frame);
        assert_eq!(args.ipc_buffer_addr, None);
    }

    #[test]
    fn syscall_args_message_length_extracts_length_field() {
        // WS-RA RA.C.3: the real MessageInfo layout — length[6:0],
        // extraCaps[8:7], label[28:9].  A nonzero label and extraCaps must
        // NOT bleed into the length (the pre-fix 0x0FFF mask read label
        // bits 9-11 as length).
        let mut frame = zero_frame();
        frame.gprs[1] = (0xCAFE_u64 << 9) | (0x3 << 7) | 0x04;
        let args = SyscallArgs::from_trap_frame(&frame);
        assert_eq!(args.message_length(), 4);
    }

    // PR #889 review: `dispatch_svc_rejects_invalid_syscall_id` and
    // `dispatch_svc_rejects_argument_count_below_minimum` moved out of this
    // binary.  The readiness gate now precedes the prefilters, so what an
    // invalid id or a short message does depends on whether this core is
    // ready — and core 0's readiness bit is set mid-run by the timer suite in
    // this binary, so neither answer can be asserted here.  The not-ready
    // answer (halt) is `tests/readiness_gate_before_mark.rs`; the ready answer
    // (the prefilter refusals) is `tests/readiness_gate_after_mark.rs`.

    // WS-RR RR5.6: `dispatch_svc_routes_to_inner_dispatcher` moved to
    // `tests/readiness_gate_after_mark.rs` — reaching the dispatch stand-in
    // means marking core 0 ready, and the timer suite in this binary owns that
    // bit.  See that file's header.

    #[test]
    fn dispatch_error_surfaces_as_kernel_error_discriminants() {
        // WS-RA: the prefilter rejections surface as real KernelError
        // discriminants on the x1 label — InvalidSyscallNumber = 31,
        // InvalidSyscallArgument = 41 — retiring the legacy raw 7 / 6
        // x0 writes and their documented collision with
        // EndpointStateMismatch / SchedulerInvariantViolation.
        assert_eq!(
            DispatchError::InvalidSyscallId.kernel_error_discriminant(),
            31
        );
        assert_eq!(
            DispatchError::InvalidArgument.kernel_error_discriminant(),
            41
        );
        // Pinned against the canonical enum, not just literals.
        assert_eq!(
            DispatchError::InvalidSyscallId.kernel_error_discriminant(),
            sele4n_types::KernelError::InvalidSyscallNumber as u32
        );
        assert_eq!(
            DispatchError::InvalidArgument.kernel_error_discriminant(),
            sele4n_types::KernelError::InvalidSyscallArgument as u32
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
        assert_eq!(SYSCALL_ABI_VERSION, 3);
        assert_eq!(ERROR_LABEL_BASE, 0xFFF00);
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
        // WS-RA / ABI v3: every KernelError discriminant 0..=56 rides the
        // x1 label at ERROR_LABEL_BASE + disc (label 0 is success;
        // discriminant 0 is a real error — the aliasing the offset from
        // zero exists to prevent; and every label below the base is a
        // delivered message's own, so no error can be read as a delivery
        // either), and no other register carries anything.
        for disc in 0..=56u32 {
            let regs = error_frame_regs(disc);
            assert_eq!(
                regs[1] >> 9,
                ERROR_LABEL_BASE + (disc as u64),
                "label must be ERROR_LABEL_BASE + disc"
            );
            assert_ne!(regs[1] >> 9, 0, "no error may alias the success label");
            assert!(
                regs[1] >> 9 >= ERROR_LABEL_BASE,
                "no error may fall into the delivery label range"
            );
            assert!(
                regs[1] >> 9 <= BLOCKED_RESUME_SENTINEL_LABEL,
                "label must stay in-field"
            );
            assert_eq!(regs[1] & 0x1FF, 0, "length/extraCaps must be zero");
            assert_eq!([regs[0], regs[2], regs[3], regs[4], regs[5]], [0; 5]);
            // …and the userspace decoder reads it back as that error.
            let mut frame = [0u64; 7];
            frame[..6].copy_from_slice(&regs);
            assert_eq!(
                sele4n_abi::decode_response(frame),
                Err(sele4n_types::KernelError::from_u32(disc).expect("0..=56 are all valid"))
            );
        }
        // The four fault tags a handler receives are deliveries, not status:
        // the property v2 lacked.
        for tag in [1u64, 2, 3, 6] {
            let resp = sele4n_abi::decode_response([0, tag << 9, 0, 0, 0, 0, 0])
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
        assert_eq!(regs[1] >> 9, BLOCKED_RESUME_SENTINEL_LABEL);
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
        // 0..=56, and exactly the Rust-only `UnknownKernelError` sentinel.
        // The range position is a compile-time assert at the constant's
        // definition; these GROUND the 56 against the canonical KernelError
        // space (56 is the last real discriminant, 57 the first unknown)
        // and the 255 against the sentinel variant.
        assert_ne!(BLOCKED_RESUME_SENTINEL_LABEL, 0);
        assert_eq!(BLOCKED_RESUME_SENTINEL_LABEL - ERROR_LABEL_BASE, 255);
        assert!(sele4n_types::KernelError::from_u32(56).is_some());
        assert!(sele4n_types::KernelError::from_u32(57).is_none());
        assert_eq!(
            sele4n_types::KernelError::from_u32(255),
            Some(sele4n_types::KernelError::UnknownKernelError)
        );
        for disc in 0..=56u32 {
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
    /// resumes prematurely (the SM10.1 context restore is not live)
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
    fn syscall_id_min_inline_args_match_abi_contract() {
        // Spot-check the canonical ABI values against the Lean decoders
        // (the authority — WS-RA RA.D.1 reconciled the drifted entries).
        assert_eq!(SyscallId::CSpaceMint.min_inline_args(), 4);
        assert_eq!(SyscallId::CSpaceCopy.min_inline_args(), 2);
        assert_eq!(SyscallId::CSpaceMove.min_inline_args(), 2);
        assert_eq!(SyscallId::LifecycleRetype.min_inline_args(), 3);
        assert_eq!(SyscallId::ServiceRegister.min_inline_args(), 4);
        // PR #866 round-3 review: suspend / resume / unbind read NO message
        // registers (`decodeSuspendArgs` / `decodeResumeArgs` /
        // `decodeSchedContextUnbindArgs` are `pure {}` — the target comes
        // from the capability), and bind reads exactly ONE (the thread id).
        // The previous minimums (1 / 1 / 1 / 2) rejected every real wrapper
        // call at this gate — the RA.D.1 unreachable-wrapper class again.
        assert_eq!(SyscallId::TcbSuspend.min_inline_args(), 0);
        assert_eq!(SyscallId::TcbResume.min_inline_args(), 0);
        assert_eq!(SyscallId::SchedContextUnbind.min_inline_args(), 0);
        assert_eq!(SyscallId::SchedContextBind.min_inline_args(), 1);
        assert_eq!(SyscallId::Send.min_inline_args(), 0);
        // The four single-register TCB-management syscalls each read exactly ONE
        // inline register (`requireMsgReg decoded.msgRegs 0` in their decoders;
        // docstrings "Requires 1 message register") and their `sele4n-sys`
        // wrappers all send `MessageInfo::new_const(1, 0, 0)` (length 1).  The
        // minimum MUST be 1: a minimum of 2 rejected every valid call at
        // `dispatch_svc`'s `len < min_inline_args` gate (`1 < 2`), making the
        // syscall unreachable on hardware before reaching the verified kernel.
        assert_eq!(SyscallId::TcbSetPriority.min_inline_args(), 1);
        assert_eq!(SyscallId::TcbSetMCPriority.min_inline_args(), 1);
        assert_eq!(SyscallId::TcbSetIPCBuffer.min_inline_args(), 1);
        // WS-SM SM5.H.4: tcbSetAffinity follows the same one-register contract
        // (the raw affinity word, msgReg[0]) — matching `decodeSetAffinityArgs`
        // (requireMsgReg 0) and the `tcb_set_affinity` wrapper.
        assert_eq!(SyscallId::TcbSetAffinity.min_inline_args(), 1);
        // PR #887 review: the fault-handler CPtr is one inline register too.
        assert_eq!(SyscallId::TcbSetFaultHandler.min_inline_args(), 1);
        assert_eq!(SyscallId::from_u32(34), Some(SyscallId::TcbSetFaultHandler));
        assert_eq!(SyscallId::from_u32(35), None);
    }

    // WS-RR RR5.6: the regression guard for the off-by-one ABI bug — a valid
    // length-1 `tcbSetPriority` / `tcbSetMCPriority` / `tcbSetIPCBuffer` call
    // must pass the `dispatch_svc` argument-count gate rather than be rejected
    // at the trap boundary — is now
    // `dispatch_svc_accepts_single_register_tcb_management_syscalls` in
    // `tests/readiness_gate_after_mark.rs`: it reaches the dispatch stand-in,
    // so it needs core 0 marked ready, and the timer suite in this binary owns
    // that bit.
}
