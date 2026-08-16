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
//! `SyscallId` here mirrors the 26-variant enum in
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

/// AN9-F: 26-variant syscall ID enum mirroring
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
}

impl SyscallId {
    /// Total number of modelled syscalls (must match `sele4n-types`).
    pub const COUNT: u32 = 31;

    /// AN9-F.1.b: decode a raw `u32` syscall id, rejecting values
    /// outside the valid 0..=30 range with `None`.
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
            Self::SchedContextBind => 2,
            Self::SchedContextUnbind => 1,
            Self::TcbSuspend => 1,
            Self::TcbResume => 1,
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
/// convention (`x0` value, offset error label on `x1`, `x2`-`x5` message
/// registers).  Version 1 was the retired bit-63 protocol.  Mirrors
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
pub const SYSCALL_ABI_VERSION: u64 = 2;

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
    /// The caller blocked: **no** frame exists for it and nothing may be
    /// written back (its stale registers are not a return value).  The
    /// staged frame is delivered by the SM10.E context restore; this
    /// variant is that seam's trap-layer hook.
    Blocked,
}

/// WS-RA: the label-encoded error frame for a prefilter rejection —
/// `x0 = 0`, `x1` = `MessageInfo {length 0, extraCaps 0, label disc + 1}`
/// = `(disc + 1) << 9`, no message registers.  Mirrors Lean's
/// `Architecture.errorFrame` (the `+ 1` is the §3.1 offset: label `0`
/// means success, and discriminant `0` is a real error).
pub fn error_frame_regs(kernel_error_discriminant: u32) -> [u64; 6] {
    [0, ((kernel_error_discriminant as u64) + 1) << 9, 0, 0, 0, 0]
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
///   `Ok(SvcOutcome::Blocked)`     — the caller blocked; write nothing.
///   `Err(error)`                  — prefilter rejection (invalid syscall
///                                   id / argument count); the trap layer
///                                   surfaces it as a label-encoded error
///                                   frame ([`error_frame_regs`]).
pub fn dispatch_svc(syscall_id: u32, args: &SyscallArgs) -> Result<SvcOutcome, DispatchError> {
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
    let core = crate::cpu::current_core_id() as usize;
    let (tag, regs) = crate::kernel_entry::with_kernel_entry(core, || {
        // SAFETY (production): `lean_syscall_dispatch_cross_core` is a
        // Lean-emitted extern "C" symbol resolved at link time.  The
        // arguments cross the FFI boundary as `u32 + 8 × u64` which the
        // Lean side reads via the @[extern] declaration in
        // `SeLe4n/Kernel/SyscallDispatchEntry.lean`.
        #[allow(unused_unsafe)]
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
            )
        };
        (tag, return_frame_read_in(&RETURN_FRAMES, core))
    });

    match tag {
        0 => Ok(SvcOutcome::Frame(regs)),
        1 => Ok(SvcOutcome::Blocked),
        // `SyscallOutcome.tagWord` is total over {0, 1}; anything else
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
// `ffi_syscall_return_frame`; 1 = the caller blocked, no frame).  The
// retired bit-63 word is gone.
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
#[cfg(not(test))]
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
    ) -> u64;
}

/// AN9-F.4 test stub (WS-RA shape): publishes the label-encoded
/// `KernelError::NotImplemented` (discriminant 17 → label 18) error frame
/// into core 0's mailbox slot and returns outcome tag 0, mirroring what
/// the live export does for a kernel rejection — so host tests exercise
/// the tag/mailbox protocol end to end.
#[cfg(test)]
#[no_mangle]
extern "C" fn lean_syscall_dispatch_cross_core(
    _syscall_id: u32,
    _msg_info: u64,
    _x0: u64,
    _x1: u64,
    _x2: u64,
    _x3: u64,
    _x4: u64,
    _x5: u64,
    _ipc_buffer_addr: u64,
) -> u64 {
    return_frame_publish_in(&RETURN_FRAMES, 0, error_frame_regs(17));
    0
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn dispatch_svc_rejects_invalid_syscall_id() {
        let frame = zero_frame();
        let args = SyscallArgs::from_trap_frame(&frame);
        let result = dispatch_svc(SyscallId::COUNT, &args);
        assert_eq!(result, Err(DispatchError::InvalidSyscallId));
    }

    #[test]
    fn dispatch_svc_rejects_argument_count_below_minimum() {
        // CSpaceMint requires 4 inline args; supplying length=0 must
        // be rejected before the inner dispatcher is called.
        let frame = zero_frame();
        let args = SyscallArgs::from_trap_frame(&frame); // length=0
        let result = dispatch_svc(SyscallId::CSpaceMint.to_u32(), &args);
        assert_eq!(result, Err(DispatchError::InvalidArgument));
    }

    #[test]
    fn dispatch_svc_routes_to_inner_dispatcher() {
        // Send takes 0 inline args so any frame is accepted; the inner
        // stub publishes the label-encoded `NotImplemented` (discriminant
        // 17 -> label 18) error frame into core 0's mailbox slot and
        // returns outcome tag 0.  WS-RA: a kernel rejection arrives as an
        // ordinary FRAME whose x1 label carries the error, undecoded here.
        let frame = zero_frame();
        let args = SyscallArgs::from_trap_frame(&frame);
        let result = dispatch_svc(SyscallId::Send.to_u32(), &args);
        assert_eq!(result, Ok(SvcOutcome::Frame(error_frame_regs(17))));
        // The frame's x1 word is the offset label in MessageInfo position.
        assert_eq!(error_frame_regs(17)[1], 18u64 << 9);
    }

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

    #[test]
    fn syscall_abi_version_matches_canonical_pin() {
        // The literal itself, pinned at runtime so a coordinated bump of
        // both mirrors without a protocol change still surfaces here.
        assert_eq!(SYSCALL_ABI_VERSION, 2);
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
        // WS-RA: every KernelError discriminant 0..=54 rides the x1 label
        // offset by one (label 0 is success; discriminant 0 is a real
        // error — the aliasing the offset exists to prevent), and no
        // other register carries anything.  This replaces the retired
        // `DispatchError::Kernel(disc).to_u32()` loop, whose 0..=51 bound
        // had also gone stale against the real 0..=54 range.
        for disc in 0..=54u32 {
            let regs = error_frame_regs(disc);
            assert_eq!(regs[1] >> 9, (disc as u64) + 1, "label must be disc + 1");
            assert_ne!(regs[1] >> 9, 0, "no error may alias the success label");
            assert_eq!(regs[1] & 0x1FF, 0, "length/extraCaps must be zero");
            assert_eq!([regs[0], regs[2], regs[3], regs[4], regs[5]], [0; 5]);
        }
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
        assert_eq!(SyscallId::TcbSuspend.min_inline_args(), 1);
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
    }

    /// Regression guard for the off-by-one ABI bug: a valid length-1
    /// `tcbSetPriority` / `tcbSetMCPriority` / `tcbSetIPCBuffer` call must
    /// pass the `dispatch_svc` argument-count gate, not be rejected at the
    /// trap boundary.  Pre-fix these three required 2 inline registers while
    /// the wrappers sent 1, so every call returned `InvalidArgument`.
    #[test]
    fn dispatch_svc_accepts_single_register_tcb_management_syscalls() {
        for sid in [
            SyscallId::TcbSetPriority,
            SyscallId::TcbSetMCPriority,
            SyscallId::TcbSetIPCBuffer,
            SyscallId::TcbSetAffinity,
        ] {
            // A length-1 message (exactly what the `sele4n-sys` wrappers send).
            let args = SyscallArgs {
                msg_info: 1,
                msg_regs: [0; 6],
                ipc_buffer_addr: None,
            };
            // Must clear the argument-count gate (any result other than the
            // count-mismatch rejection is acceptable here; in test builds the
            // inner symbol is a stub).
            let result = dispatch_svc(sid as u32, &args);
            assert_ne!(
                result,
                Err(DispatchError::InvalidArgument),
                "length-1 call to {sid:?} must not be rejected by the arg-count gate",
            );
        }
    }
}
