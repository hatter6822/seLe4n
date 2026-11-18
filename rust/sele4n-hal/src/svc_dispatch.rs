// SPDX-License-Identifier: GPL-3.0-or-later
//! AN9-F (DEF-R-HAL-L14 / RESOLVED): Typed SVC argument marshalling.
//!
//! This module owns the SVC trap's syscall decode.  The `handle_svc`
//! entry in `trap.rs` hands seL4's syscall word, the raw `TrapFrame`'s full
//! `x7`, to [`dispatch_svc`], whose prefilter names the syscall with
//! [`Syscall::from_word`] before it dispatches to the Lean kernel.  A word
//! that names none of seL4-MCS's eleven syscalls is seL4's `UnknownSyscall`
//! fault.
//!
//! ## Mirror discipline
//!
//! [`Syscall`] here mirrors the eleven-variant enum in
//! `sele4n-types/src/syscall.rs` (seL4's `syscall.xml`, `api-mcs`).  We do
//! NOT depend on `sele4n-types` in the runtime build (the HAL crate is the
//! lowest-level workspace member with zero runtime dependencies, by design
//! — see `rust/sele4n-hal/Cargo.toml`), so the numbers are duplicated here.
//! The unit test `syscall_mirror_matches_sele4n_types` cross-checks this
//! mirror against the canonical `sele4n-types::Syscall` (a dev-dependency,
//! available only under `#[cfg(test)]`), so any drift in the numbers, the
//! words or the decode fails the test build.  No operation is named in a
//! register: the kernel selects it from the syscall, the invoked
//! capability's type and the message label (WS-SX SX7).
//!
//! ## Argument layout
//!
//! seLe4n's syscall ABI (matching the Lean `arm64DefaultLayout` in
//! `SeLe4n/Kernel/Architecture/RegisterDecode.lean`):
//!
//! ```text
//! x0..x5 : inline message registers
//! x6     : reply register      (seL4-MCS `replyRegister`: the reply cap a
//!          Recv / NBRecv / ReplyRecv names)
//! x7     : syscall word        (seL4's syscall number, negated)
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
    /// The trap's `x7` names none of seL4-MCS's eleven syscalls
    /// ([`Syscall::from_word`] answers `None`): seL4's `UnknownSyscall`,
    /// delivered to the thread's fault handler, or, with no handler,
    /// surfaced as `KernelError::InvalidSyscallNumber` on the `x1` label.
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

/// **seL4's system calls** (`syscall.xml`, `api-mcs`), mirroring
/// `sele4n-types::Syscall` and the Lean `Syscall`: the trap carries the
/// number negated in `x7`.  An operation is not a syscall; the kernel selects
/// it from the syscall, the invoked capability's type and the message label.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Syscall {
    /// `seL4_SysCall`, -1.
    Call,
    /// `seL4_SysReplyRecv`, -2.
    ReplyRecv,
    /// `seL4_SysNBSendRecv`, -3.
    NBSendRecv,
    /// `seL4_SysNBSendWait`, -4.
    NBSendWait,
    /// `seL4_SysSend`, -5.
    Send,
    /// `seL4_SysNBSend`, -6.
    NBSend,
    /// `seL4_SysRecv`, -7.
    Recv,
    /// `seL4_SysNBRecv`, -8.
    NBRecv,
    /// `seL4_SysWait`, -9.
    Wait,
    /// `seL4_SysNBWait`, -10.
    NBWait,
    /// `seL4_SysYield`, -11.
    Yield,
}

impl Syscall {
    /// Every syscall, in seL4's numbering order.
    pub const ALL: [Syscall; 11] = [
        Self::Call,
        Self::ReplyRecv,
        Self::NBSendRecv,
        Self::NBSendWait,
        Self::Send,
        Self::NBSend,
        Self::Recv,
        Self::NBRecv,
        Self::Wait,
        Self::NBWait,
        Self::Yield,
    ];

    /// The syscall's number, the negation of the word in `x7` (1 to 11).
    pub const fn number(self) -> u32 {
        match self {
            Self::Call => 1,
            Self::ReplyRecv => 2,
            Self::NBSendRecv => 3,
            Self::NBSendWait => 4,
            Self::Send => 5,
            Self::NBSend => 6,
            Self::Recv => 7,
            Self::NBRecv => 8,
            Self::Wait => 9,
            Self::NBWait => 10,
            Self::Yield => 11,
        }
    }

    /// The word the trap carries in `x7`: the number negated.
    pub const fn word(self) -> u64 {
        0u64.wrapping_sub(self.number() as u64)
    }

    /// The syscall a number names.
    pub const fn from_number(n: u32) -> Option<Self> {
        match n {
            1 => Some(Self::Call),
            2 => Some(Self::ReplyRecv),
            3 => Some(Self::NBSendRecv),
            4 => Some(Self::NBSendWait),
            5 => Some(Self::Send),
            6 => Some(Self::NBSend),
            7 => Some(Self::Recv),
            8 => Some(Self::NBRecv),
            9 => Some(Self::Wait),
            10 => Some(Self::NBWait),
            11 => Some(Self::Yield),
            _ => None,
        }
    }

    /// The syscall an `x7` word names, the trap's prefilter: the word's
    /// negation, when that fits 32 bits, read as a number.  Every other
    /// word is an unknown syscall.
    pub const fn from_word(w: u64) -> Option<Self> {
        let n = w.wrapping_neg();
        if n < (1u64 << 32) {
            Self::from_number(n as u32)
        } else {
            None
        }
    }
}

/// WS-RA: the syscall ABI version this HAL speaks — the seL4 frame
/// convention (`x0` value, kernel status in the top of `x1`'s label range,
/// `x2`-`x5` message registers).  Version 1 was the retired bit-63
/// protocol; version 2 carried the status as label `d + 1`, which made a
/// delivered fault message's `seL4_Fault_tag` decode as a kernel error
/// (retired at WS-RR RR4); version 4 took seL4's `seL4_MessageInfo_t`
/// layout; version 5 carries seL4's error payload in an error frame's
/// message registers, with its length in `x1`.  Mirrors
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
pub const SYSCALL_ABI_VERSION: u64 = 5;

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
    /// WS-SX SX7.2: the caller **resumes with the registers it trapped
    /// with** (outcome tag 3, `SyscallOutcome.resumes`).  seL4 answers an
    /// invocation's error only on a `Call` (`handleInvocation`, `if (isCall)
    /// replyFromKernel_error`); a `Send` or `NBSend` that fails, and an
    /// `NBSend` whose capability lookup fails, write no message register.
    /// The trap layer writes nothing over the trapped `x0`-`x5`.
    Resumed,
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
/// Routes the trap's full `x7` word through [`Syscall::from_word`] (the
/// prefilter) before delegating to
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
///   `Ok(SvcOutcome::Resumed)`     — the caller resumes with the registers
///                                   it trapped with (tag 3): a non-`Call`
///                                   whose error seL4 discards.
///   `Ok(SvcOutcome::Faulted)`     — the caller took a fault at the seam
///                                   (tag 2); no frame exists and the trap
///                                   layer halts if no successor was
///                                   installed rather than resume the caller past the `SVC`
///                                   its handler's reply restarts it at.
///   `Err(error)`                  — prefilter rejection (a word that names
///                                   none of the eleven syscalls); the trap
///                                   layer delivers it as seL4's
///                                   `UnknownSyscall` fault.
pub fn dispatch_svc(syscall_word: u64) -> Result<SvcOutcome, DispatchError> {
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
        // WS-SX SX7.2: reject a word that names none of seL4-MCS's eleven
        // syscalls.  The operation is the kernel's to select (from the
        // syscall, the invoked capability's type and the label), and the
        // message length the kernel's to check, after the capability lookup,
        // as seL4's decode checks it (`truncationMinimum`).
        if Syscall::from_word(syscall_word).is_none() {
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
        halt_syscall_before_lean_ready(core, syscall_word)
    };

    match tag {
        0 => Ok(SvcOutcome::Frame(regs)),
        1 => Ok(SvcOutcome::Blocked),
        2 => Ok(SvcOutcome::Faulted),
        3 => Ok(SvcOutcome::Resumed),
        // `SyscallOutcome.tagWord` is total over {0, 1, 2, 3}; anything else
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
        halt_syscall_before_lean_ready(3, Syscall::Send.word());
    }

    /// The HAL's prefilter names exactly seL4-MCS's eleven syscalls, by the
    /// same numbers and words as the canonical `sele4n-types::Syscall` (the
    /// source the verified Lean kernel and the user ABI use): a drift — a
    /// renumbered syscall, a word the HAL decodes differently — fails here.
    #[test]
    fn syscall_mirror_matches_sele4n_types() {
        assert_eq!(Syscall::ALL.len(), sele4n_types::Syscall::ALL.len());
        for (hal, canonical) in Syscall::ALL.iter().zip(sele4n_types::Syscall::ALL.iter()) {
            assert_eq!(hal.number(), canonical.number(), "{hal:?} number drifted");
            assert_eq!(hal.word(), canonical.word(), "{hal:?} word drifted");
            assert_eq!(Syscall::from_word(hal.word()), Some(*hal));
            assert_eq!(Syscall::from_number(hal.number()), Some(*hal));
        }
        // The words around the eleven, and the retired internal codes the
        // pre-SX7 ABI put in `x7`, name no syscall.
        for w in [
            0u64,
            1,
            2,
            16,
            41,
            47,
            48,
            u64::from(u32::MAX),
            0u64.wrapping_sub(12),
        ] {
            assert_eq!(Syscall::from_word(w), None, "word {w:#x}");
            assert_eq!(sele4n_types::Syscall::from_word(w), None, "word {w:#x}");
        }
        // A negated number past 32 bits is not narrowed into one.
        assert_eq!(Syscall::from_word(0u64.wrapping_sub((1 << 32) + 1)), None);
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
        assert_eq!(SYSCALL_ABI_VERSION, 5);
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
        // space (`FailedLookup` is the last real discriminant, 61 the
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
}
