// SPDX-License-Identifier: GPL-3.0-or-later
//! Trap frame structure and exception handler dispatch.
//!
//! The assembly entry points (vectors.S / trap.S) save the full CPU context
//! into a `TrapFrame` on the kernel stack, then call into these Rust handlers.
//! On return, the assembly restores context and executes ERET.

/// Saved CPU context during an exception.
///
/// Layout must match the assembly save/restore macros in `trap.S`:
/// - GPRs x0-x30 at offsets 0..248 (31 × 8 B)
/// - SP_EL0 at offset 248
/// - ELR_EL1 at offset 256
/// - SPSR_EL1 at offset 264
/// - ESR_EL1 at offset 272 (AK5-F — read-only snapshot at exception entry)
/// - FAR_EL1 at offset 280 (AK5-F — read-only snapshot at exception entry)
/// - TPIDR_EL0 at offset 288 (v0.36.30 — the thread pointer)
/// - one padding word at offset 296
///
/// Total size: 38 × 8 = 304 bytes, 16-byte aligned.
///
/// **`TPIDR_EL0` is thread context.**  EL0 writes it with no trap, so until
/// v0.36.30, when nothing saved or restored it, a thread could read the value
/// the previous thread on its core had written: a 64-bit storage channel
/// between any two threads sharing a core, across domains.  It is saved at
/// every entry and restored at every exit, and a context restore installs the
/// incoming thread's own value (word 34).
///
/// **No FP/SIMD register is saved, and that is sound only because the
/// kernel touches none.**  Both boot entries trap FP/SIMD at EL0 and EL1
/// (`CPACR_EL1 := 0`, pinned by `build.rs`'s `scan_fp_trap_prologue`), the
/// crate is built for `aarch64-unknown-none-softfloat`, and
/// `scripts/check_fp_simd_free_objects.py` proves the release objects use
/// no vector register.  Kernel code that touched one would halt at EL1 —
/// and, were the trap ever lifted, would overwrite the interrupted thread's
/// `q0`–`q31`, which nothing here would restore.  Per-thread FP state is
/// WS-BP BP7.9's.
///
/// AK5-F (R-HAL-H04 / HIGH): ESR_EL1 and FAR_EL1 are saved at exception
/// entry so that handlers read a STABLE snapshot rather than the live
/// register. A nested exception (e.g., SError during data-abort handling)
/// would otherwise mutate the live ESR/FAR before the outer handler reads
/// them, producing incorrect classification and fault-address reports.
use core::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64, AtomicU8, Ordering};

#[repr(C, align(16))]
pub struct TrapFrame {
    /// General-purpose registers x0-x30 (31 registers).
    pub gprs: [u64; 31],
    /// User-mode stack pointer (SP_EL0).
    pub sp_el0: u64,
    /// Exception Link Register — return address.
    pub elr_el1: u64,
    /// Saved Program Status Register — saved PSTATE.
    pub spsr_el1: u64,
    /// AK5-F: Exception Syndrome Register snapshot at trap entry.
    /// Written by `trap.S:save_context`, READ-ONLY from Rust.
    pub esr_el1: u64,
    /// AK5-F: Fault Address Register snapshot at trap entry.
    /// Written by `trap.S:save_context`, READ-ONLY from Rust.
    pub far_el1: u64,
    /// v0.36.30: the thread pointer `TPIDR_EL0`, saved at entry and restored
    /// at exit by `trap.S`; word 34 of a thread's context.
    pub tpidr_el0: u64,
    /// Padding that keeps the frame a multiple of 16 bytes.  Never read.
    pub reserved: u64,
}

/// Size of TrapFrame in bytes (for assembly offset calculations).
/// 304 bytes: AK5-F grew it 272 -> 288, v0.36.30 to 304 for `TPIDR_EL0`.
pub const TRAP_FRAME_SIZE: usize = core::mem::size_of::<TrapFrame>();

// Compile-time layout assertions (AK5-F).
const _: () = assert!(TRAP_FRAME_SIZE == 304);
const _: () = assert!(core::mem::align_of::<TrapFrame>() == 16);
const _: () = assert!(core::mem::offset_of!(TrapFrame, gprs) == 0);
const _: () = assert!(core::mem::offset_of!(TrapFrame, sp_el0) == 248);
const _: () = assert!(core::mem::offset_of!(TrapFrame, elr_el1) == 256);
const _: () = assert!(core::mem::offset_of!(TrapFrame, spsr_el1) == 264);
const _: () = assert!(core::mem::offset_of!(TrapFrame, esr_el1) == 272);
const _: () = assert!(core::mem::offset_of!(TrapFrame, far_el1) == 280);
const _: () = assert!(core::mem::offset_of!(TrapFrame, tpidr_el0) == 288);

/// **WS-BP BP7.3: the number of words a thread's context occupies in a trap
/// frame** — `x0`–`x30`, `SP_EL0`, `ELR_EL1`, `SPSR_EL1`, `TPIDR_EL0`.  The
/// Lean kernel receives all of them in one call ([`in_flight_context`],
/// `Architecture.TrapContext`, `trapFrameWordCount`).
pub const TRAP_FRAME_CONTEXT_WORDS: u32 = 35;
// The Lean `Architecture.TrapContext` has exactly this many `UInt64` fields
// (`trapFrameWordCount`); the compiler checks the pin, no scanner does.
const _: () = assert!(TRAP_FRAME_CONTEXT_WORDS == 35);

/// A thread's context as it crosses the Lean boundary: the
/// [`TRAP_FRAME_CONTEXT_WORDS`] words in layout order.
pub type TrapContextWords = [u64; TRAP_FRAME_CONTEXT_WORDS as usize];

/// **WS-BP BP7.3**: a thread's context in `frame`, in layout order — word `i`
/// is `x<i>` for `i < 31`, then `SP_EL0`, `ELR_EL1`, `SPSR_EL1`, `TPIDR_EL0`.
/// `ESR_EL1` and `FAR_EL1` are the trap's, not the thread's, and are not part
/// of it.
#[must_use]
pub fn trap_frame_context(frame: &TrapFrame) -> TrapContextWords {
    let mut words = [0; TRAP_FRAME_CONTEXT_WORDS as usize];
    words[..31].copy_from_slice(&frame.gprs);
    words[31] = frame.sp_el0;
    words[32] = frame.elr_el1;
    words[33] = frame.spsr_el1;
    words[34] = frame.tpidr_el0;
    words
}

/// **WS-BP BP7.3: the trap frame each PE is handling**, published for the Lean
/// kernel to read the whole outgoing context from.  Slot `c` is written only by
/// core `c` — on entry to a handler, and restored when it returns — and read
/// only by core `c`'s own Lean entry inside the same handler, so the accesses
/// to a slot are same-core program-ordered and `Relaxed` suffices.
pub type InFlightSlots = [AtomicPtr<TrapFrame>; crate::svc_dispatch::RETURN_FRAME_CORES];

/// The slots every handler publishes into.
static IN_FLIGHT_FRAMES: InFlightSlots =
    [const { AtomicPtr::new(core::ptr::null_mut()) }; crate::svc_dispatch::RETURN_FRAME_CORES];

/// **WS-BP BP7.3**: a PE's in-flight frame, published for the duration of a
/// handler and withdrawn when the guard drops — so a Lean entry never reads a
/// frame whose stack slot has been popped.  A nested handler restores the frame
/// it displaced.
pub struct InFlightFrame<'s> {
    slots: &'s InFlightSlots,
    core: usize,
    previous: *mut TrapFrame,
}

impl InFlightFrame<'static> {
    /// Publish `frame` as the executing PE's in-flight frame.
    pub fn publish(frame: &mut TrapFrame) -> Self {
        let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
        // WS-BP BP7.6: a restore belongs to the handler that ran it, so the
        // flag a previous handler on this PE may have left set is cleared
        // before this one can read it.
        if let Some(flag) = RESTORED.get(core) {
            flag.store(false, Ordering::Relaxed);
        }
        InFlightFrame::publish_in(&IN_FLIGHT_FRAMES, core, frame)
    }
}

impl<'s> InFlightFrame<'s> {
    /// Publish `frame` in `slots[core]` (the testable form).
    pub fn publish_in(slots: &'s InFlightSlots, core: usize, frame: &mut TrapFrame) -> Self {
        assert!(
            core < slots.len(),
            "InFlightFrame::publish: core {core} out of range"
        );
        let previous = slots[core].swap(frame as *mut TrapFrame, Ordering::Relaxed);
        InFlightFrame {
            slots,
            core,
            previous,
        }
    }
}

impl Drop for InFlightFrame<'_> {
    fn drop(&mut self) {
        self.slots[self.core].store(self.previous, Ordering::Relaxed);
    }
}

/// **WS-BP BP7.3**: the context of the frame published in `slots[core]`, or
/// `None` when none is (the testable form).
#[must_use]
pub fn in_flight_context_in(slots: &InFlightSlots, core: usize) -> Option<TrapContextWords> {
    let ptr = slots.get(core)?.load(Ordering::Relaxed);
    if ptr.is_null() {
        return None;
    }
    // SAFETY: a non-null slot holds the frame a handler on this PE published
    // through `InFlightFrame::publish_in` and has not yet withdrawn: the guard
    // lives in that handler's frame, below this call on the same stack, so the
    // `TrapFrame` it names is live, and the handler is suspended in the call
    // that reached here, so nothing writes it across this read.  Only core
    // `core` writes slot `core`.
    let frame = unsafe { &*ptr };
    Some(trap_frame_context(frame))
}

/// The slots every handler publishes into, for the FFI entry that reads the
/// executing PE's own (`ffi::ffi_trap_context`).
#[must_use]
pub fn in_flight_frames() -> &'static InFlightSlots {
    &IN_FLIGHT_FRAMES
}

/// **WS-BP BP7.3**: the context of the executing PE's in-flight frame, or
/// `None` when no frame is published.
#[must_use]
pub fn in_flight_context() -> Option<TrapContextWords> {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    in_flight_context_in(in_flight_frames(), core)
}

/// **WS-BP BP7.4: the context each PE is about to resume**, staged whole by
/// the Lean kernel (`Platform.FFI.restoreTrapFrame`) in the layout of
/// [`trap_frame_context`], then committed into the in-flight frame
/// by [`restore_commit_in`].  Slot `c` is written and read only by core `c`,
/// inside one handler, so `Relaxed` suffices.
pub type RestoreStaging =
    [[AtomicU64; TRAP_FRAME_CONTEXT_WORDS as usize]; crate::svc_dispatch::RETURN_FRAME_CORES];

/// **WS-BP BP7.4**: per core, whether the frame the handler will `eret`
/// through has been replaced by a restore since the handler began.
pub type RestoredFlags = [AtomicBool; crate::svc_dispatch::RETURN_FRAME_CORES];

static RESTORE_STAGING: RestoreStaging =
    [const { [const { AtomicU64::new(0) }; TRAP_FRAME_CONTEXT_WORDS as usize] };
        crate::svc_dispatch::RETURN_FRAME_CORES];

static RESTORED: RestoredFlags =
    [const { AtomicBool::new(false) }; crate::svc_dispatch::RETURN_FRAME_CORES];

/// **WS-BP BP7.4**: restore kind `0` — resume a user thread from the staged
/// context.
pub const RESTORE_KIND_USER: u32 = 0;

/// **WS-BP BP7.4**: restore kind `1` — the core has no thread to run, so it
/// resumes [`kernel_idle_loop`] at EL1.
pub const RESTORE_KIND_IDLE: u32 = 1;

/// **WS-BP BP7.9**: restore kind `2` — kind `0` for a thread whose FP/SIMD
/// values the core's registers hold (the Lean `RestoreTarget.user`'s
/// `fpLive`): the commit lifts the FP/SIMD trap for it, where kinds `0` and `1`
/// arm it.
pub const RESTORE_KIND_USER_FP_LIVE: u32 = 2;

/// **WS-BP BP7.4**: the `SPSR_EL1` a user resume may carry — the condition
/// flags of the staged value and nothing else, so the `eret` lands at **EL0t**
/// with every exception unmasked whatever the saved word says.  A thread's
/// `pstate` is state the thread can influence (a register write, a hand-built
/// frame); letting its mode bits through would let it `eret` into EL1.
#[must_use]
pub const fn sanitise_user_spsr(value: u64) -> u64 {
    value & 0xF000_0000
}

/// **WS-BP BP7.4**: `SPSR_EL1` for the idle resume — EL1h (`M = 0b0101`),
/// DAIF clear, so the idle loop takes the interrupt that ends it.
pub const IDLE_SPSR: u64 = 0x5;

/// **WS-BP BP7.4: the core's wait when no thread is runnable.**  Entered by
/// `eret` from a restore of kind [`RESTORE_KIND_IDLE`], at EL1h with IRQs
/// unmasked, and by a core's own bring-up through [`enter_idle_wait`]; it keeps
/// no state, so a later restore may replace its frame outright.
pub extern "C" fn kernel_idle_loop() -> ! {
    loop {
        crate::cpu::wfi();
    }
}

/// **WS-BP BP8.1: whether each core has handed itself to the idle wait.**
///
/// A restore replaces the frame an interrupt was taken on, and an EL1-origin
/// frame is not always replaceable: the bring-up of every core (the boot
/// core's Phases 6 and 7, a secondary's steps after its first reschedule)
/// runs with IRQs unmasked, because the boot core must acknowledge shootdowns
/// through the Phase 7 wait and a secondary publishes `CORE_IRQ_READY` only
/// after it unmasks.  A timer tick there commits a scheduling decision and
/// stages a restore; replacing the bring-up frame would abandon the rest of
/// the bring-up — the secondary's IRQ-readiness publication, the boot core's
/// topology refusal — for good.  The first Lean-linked boot under QEMU did
/// exactly that: every secondary's first tick resumed the idle loop over its
/// bring-up, no secondary published IRQ-readiness, and the boot halted.
///
/// So an EL1-origin frame is replaced only once its core has **handed off**:
/// [`enter_idle_wait`] sets the flag and never returns, so after it every
/// EL1-origin frame on that core is the idle loop's, and before it no thread
/// has run on the core (a thread runs only through a restore), so every frame
/// is the kernel's own bring-up.  The decision is therefore exact, not a
/// heuristic on the frame's contents.  A restore the core declines is not
/// lost: the committed state names what the core runs, the interrupted
/// bring-up saved nothing into any thread (`trapFromEl0` is false of an
/// EL1-origin frame), and the core's first tick after its handoff restores the
/// same target.  Each flag is written by its own core and read by that core's
/// own handlers, so program order and the exception entry order it.
pub type IdleHandoffFlags = [AtomicBool; crate::svc_dispatch::RETURN_FRAME_CORES];

static IDLE_HANDOFF: IdleHandoffFlags =
    [const { AtomicBool::new(false) }; crate::svc_dispatch::RETURN_FRAME_CORES];

/// **WS-BP BP8.1: each core's first idle dispatch, and whether it has been
/// reported.**  `0` none yet, `1` committed and not yet reported, `2`
/// reported.  A restore of kind [`RESTORE_KIND_IDLE`] that replaces a frame
/// moves a core from `0` to `1`; the IRQ handler, once its kernel-entry
/// bracket has been released, moves it from `1` to `2` and prints one line —
/// the boot log's evidence that the kernel, not the bring-up, now owns the
/// core.  The print is outside the bracket for a reason: a core still printing
/// its bring-up with IRQs unmasked may hold the console lock while it waits
/// for the kernel-entry lock, so printing under that lock could deadlock.  At
/// the report the interrupted frame is the idle loop or a thread (a restore
/// replaced it, so the core had handed off), neither of which holds the
/// console lock.
pub type FirstIdleFlags = [AtomicU8; crate::svc_dispatch::RETURN_FRAME_CORES];

static FIRST_IDLE: FirstIdleFlags =
    [const { AtomicU8::new(0) }; crate::svc_dispatch::RETURN_FRAME_CORES];

/// **WS-BP BP8.1**: record that `core`'s frame was replaced by an idle resume
/// (the testable form); only the first one counts.
pub fn note_idle_dispatch_in(flags: &FirstIdleFlags, core: usize) {
    if let Some(flag) = flags.get(core) {
        let _ = flag.compare_exchange(0, 1, Ordering::Relaxed, Ordering::Relaxed);
    }
}

/// **WS-BP BP8.1**: take `core`'s first-idle report (the testable form):
/// `true` exactly once, after an idle resume was noted.
#[must_use]
pub fn take_first_idle_report_in(flags: &FirstIdleFlags, core: usize) -> bool {
    flags.get(core).is_some_and(|flag| {
        flag.compare_exchange(1, 2, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
    })
}

/// **WS-BP BP8.1**: print the executing core's first idle dispatch, once.
/// Called by the IRQ handler after its kernel-entry bracket is released.
pub fn report_first_idle_dispatch() {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    if take_first_idle_report_in(&FIRST_IDLE, core) {
        crate::kprintln!("[sched] core {core}: first idle dispatch");
    }
}

/// **WS-BP BP8.1: hand the executing core to the idle wait** (the testable
/// form): set `core`'s handoff flag, after which a restore may replace an
/// EL1-origin frame on it.
pub fn hand_off_to_idle_in(handoff: &IdleHandoffFlags, core: usize) {
    if let Some(flag) = handoff.get(core) {
        flag.store(true, Ordering::Relaxed);
    }
}

/// **WS-BP BP8.1: the last thing a core's bring-up does.**  Marks the core
/// handed off ([`IdleHandoffFlags`]) and enters [`kernel_idle_loop`]; the
/// caller has already unmasked IRQs, so the next tick or SGI takes the core
/// from here to whatever the kernel committed for it.
pub fn enter_idle_wait() -> ! {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    hand_off_to_idle_in(&IDLE_HANDOFF, core);
    kernel_idle_loop()
}

/// Why a restore was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RestoreRefusal {
    /// A kind other than [`RESTORE_KIND_USER`] or [`RESTORE_KIND_IDLE`].
    UnknownKind,
    /// A core id outside the slot arrays.
    CoreOutOfRange,
}

/// **WS-BP BP7.4**: stage `core`'s whole resume context (the testable form).
pub fn restore_stage_context_in(
    staging: &RestoreStaging,
    core: usize,
    context: &TrapContextWords,
) -> Result<(), RestoreRefusal> {
    let slot = staging.get(core).ok_or(RestoreRefusal::CoreOutOfRange)?;
    for (word, value) in slot.iter().zip(context) {
        word.store(*value, Ordering::Relaxed);
    }
    Ok(())
}

/// **PR #904 (`v0.36.41`)**: where an idle restore resumes — the idle loop's
/// address, and the SP_EL0 an EL1 frame carries (the PE's fault stack top).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IdleResume {
    /// The idle loop's address, `ELR_EL1` of the idle frame.
    pub pc: u64,
    /// The PE's fault stack top, `SP_EL0` of the idle frame.
    pub sp_el0: u64,
}

/// **WS-BP BP7.4: commit a staged resume into the frame the handler will
/// `eret` through** (the testable form).  `Ok(false)` when no frame is
/// published on `core` — the entry was not reached from a trap, and there is
/// nothing to resume into — and when the frame was taken at EL1 before the
/// core handed itself to the idle wait, which is the kernel's own bring-up
/// (WS-BP BP8.1, [`IdleHandoffFlags`]); `Ok(true)` when the frame was replaced and
/// `restored[core]` set.  A user resume copies the staged words with
/// `SPSR_EL1` sanitised ([`sanitise_user_spsr`]); an idle resume clears the
/// general-purpose registers, sets `SP_EL0` to `idle.sp_el0` and aims
/// `ELR_EL1` at `idle.pc`.
/// The syndrome words are the trap's and are left alone.
pub fn restore_commit_in(
    slots: &InFlightSlots,
    staging: &RestoreStaging,
    restored: &RestoredFlags,
    handoff: &IdleHandoffFlags,
    core: usize,
    kind: u32,
    idle: IdleResume,
) -> Result<bool, RestoreRefusal> {
    if kind != RESTORE_KIND_USER && kind != RESTORE_KIND_IDLE && kind != RESTORE_KIND_USER_FP_LIVE {
        return Err(RestoreRefusal::UnknownKind);
    }
    let slot = slots.get(core).ok_or(RestoreRefusal::CoreOutOfRange)?;
    let words = staging.get(core).ok_or(RestoreRefusal::CoreOutOfRange)?;
    let flag = restored.get(core).ok_or(RestoreRefusal::CoreOutOfRange)?;
    let handed_off = handoff.get(core).ok_or(RestoreRefusal::CoreOutOfRange)?;
    let ptr = slot.load(Ordering::Relaxed);
    if ptr.is_null() {
        return Ok(false);
    }
    // SAFETY: as in `in_flight_context_in` — a non-null slot names the
    // frame a handler on this PE published and has not withdrawn; that
    // handler is suspended in the call that reached here, so this is the only
    // live reference to the frame for the duration of the write, and only
    // core `core` writes slot `core`.
    let frame = unsafe { &mut *ptr };
    // WS-BP BP8.1: a frame taken at EL1 before the core handed itself to the
    // idle wait is the kernel's own bring-up, resumed as it stands
    // ([`IdleHandoffFlags`]).
    if !exception_taken_from_el0(frame.spsr_el1) && !handed_off.load(Ordering::Relaxed) {
        return Ok(false);
    }
    if kind == RESTORE_KIND_USER || kind == RESTORE_KIND_USER_FP_LIVE {
        let word = |i: usize| words[i].load(Ordering::Relaxed);
        for (i, gpr) in frame.gprs.iter_mut().enumerate() {
            *gpr = word(i);
        }
        frame.sp_el0 = word(31);
        frame.elr_el1 = word(32);
        frame.spsr_el1 = sanitise_user_spsr(word(33));
        frame.tpidr_el0 = word(34);
    } else {
        frame.gprs = [0; 31];
        // PR #904 (`v0.36.41`): the idle loop runs at EL1, where every PE
        // holds SP_EL0 at its fault stack's top (`vectors.S` 0x200 switches to
        // it), so the idle frame carries that value rather than a thread's.
        frame.sp_el0 = idle.sp_el0;
        frame.elr_el1 = idle.pc;
        frame.spsr_el1 = IDLE_SPSR;
        // The idle loop reads no thread pointer; clearing it leaves no thread's
        // value in the core while it waits.
        frame.tpidr_el0 = 0;
    }
    flag.store(true, Ordering::Relaxed);
    Ok(true)
}

/// **PR #904 (`v0.36.41`)**: the top of `core`'s fault stack,
/// `__fault_stacks_bottom + (core + 1) * FAULT_STACK_SIZE` — the value SP_EL0
/// holds while the PE runs at EL1 (`boot.S`, `trap.S`'s `set_fault_stack`),
/// so an idle frame, which resumes at EL1, carries it.  The host has no link
/// script and answers `0`.
#[must_use]
pub fn fault_stack_top(core: usize) -> u64 {
    #[cfg(target_arch = "aarch64")]
    {
        extern "C" {
            static __fault_stacks_bottom: u8;
        }
        (&raw const __fault_stacks_bottom as u64) + (core as u64 + 1) * crate::mmu::FAULT_STACK_SIZE
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = core;
        0
    }
}

/// **WS-BP BP7.4**: take (and clear) `core`'s restored flag — whether the
/// frame the handler is about to `eret` through was replaced by a restore
/// (the testable form).
#[must_use]
pub fn take_restored_in(restored: &RestoredFlags, core: usize) -> bool {
    restored
        .get(core)
        .is_some_and(|flag| flag.swap(false, Ordering::Relaxed))
}

/// The per-core staging buffers, for the FFI entry that stages the executing
/// PE's own (`ffi::ffi_restore_stage_context`).
#[must_use]
pub fn restore_staging() -> &'static RestoreStaging {
    &RESTORE_STAGING
}

/// **WS-BP BP7.4**: stage the executing PE's whole resume context.
pub fn restore_stage_context(context: &TrapContextWords) -> Result<(), RestoreRefusal> {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    restore_stage_context_in(restore_staging(), core, context)
}

/// **WS-BP BP7.4**: commit the executing PE's staged resume.
///
/// **WS-BP BP7.9**: and set the FP/SIMD trap for what it resumes — lifted for
/// [`RESTORE_KIND_USER_FP_LIVE`], armed for every other kind — once the frame
/// is replaced, so the trap and the frame the handler `eret`s through always
/// describe the same thread.
///
/// **PR #904 (`v0.36.41`)**: the resumed thread's translation is installed
/// here, **after** the frame is replaced and only if it was.  A commit that
/// declines — no frame published (a secondary's first reschedule), or an EL1
/// frame on a core that has not handed itself to the idle wait — leaves
/// `TTBR0_EL1` and the FP/SIMD trap as the kernel had them, so a core that
/// continues its bring-up never does so under a thread's address space or with
/// the trap lifted.  Before this the Lean restore installed the translation
/// first and committed second, and the order rested on two facts standing in
/// for it (every user root carries the kernel window; the kernel is FP-free).
pub fn restore_commit(
    kind: u32,
    translation: crate::user_translation::Translation,
) -> Result<bool, RestoreRefusal> {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    let replaced = restore_commit_in(
        &IN_FLIGHT_FRAMES,
        &RESTORE_STAGING,
        &RESTORED,
        &IDLE_HANDOFF,
        core,
        kind,
        IdleResume {
            pc: kernel_idle_loop as *const () as usize as u64,
            sp_el0: fault_stack_top(core),
        },
    )?;
    if replaced {
        crate::user_translation::install_translation(translation);
        crate::fp_context::set_trap_for_resume(kind == RESTORE_KIND_USER_FP_LIVE);
        if kind == RESTORE_KIND_IDLE {
            note_idle_dispatch_in(&FIRST_IDLE, core);
        }
    }
    Ok(replaced)
}

/// **WS-BP BP7.4**: take the executing PE's restored flag.  The trap arms
/// consult it once the context-restore seam is live (BP7.6): a replaced frame
/// is resumed as it stands, never overwritten by a return frame or a poison.
#[must_use]
pub fn take_restored() -> bool {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    take_restored_in(&RESTORED, core)
}

impl TrapFrame {
    /// ABI register accessors matching the seLe4n syscall convention:
    /// x0 = capability pointer, x1 = message info, x2-x5 = message registers,
    /// x7 = syscall number.
    /// x0 — capability pointer / first argument.
    #[inline(always)]
    pub fn x0(&self) -> u64 {
        self.gprs[0]
    }

    /// x1 — message info / second argument.
    #[inline(always)]
    pub fn x1(&self) -> u64 {
        self.gprs[1]
    }

    /// x2 — message register 0.
    #[inline(always)]
    pub fn x2(&self) -> u64 {
        self.gprs[2]
    }

    /// x3 — message register 1.
    #[inline(always)]
    pub fn x3(&self) -> u64 {
        self.gprs[3]
    }

    /// x4 — message register 2.
    #[inline(always)]
    pub fn x4(&self) -> u64 {
        self.gprs[4]
    }

    /// x5 — message register 3.
    #[inline(always)]
    pub fn x5(&self) -> u64 {
        self.gprs[5]
    }

    /// x7 — syscall number.
    #[inline(always)]
    pub fn x7(&self) -> u64 {
        self.gprs[7]
    }

    /// Set x0 (the primary return value: badge / queried word / `0`).
    #[inline(always)]
    pub fn set_x0(&mut self, val: u64) {
        self.gprs[0] = val;
    }

    /// Set x1 (the returned `MessageInfo` word — its label carries the
    /// kernel status in the top of the label range: `0` = success,
    /// `ERROR_LABEL_BASE + d` = `KernelError` discriminant `d`, anything
    /// below the base a delivered message's own label).
    #[inline(always)]
    pub fn set_x1(&mut self, val: u64) {
        self.gprs[1] = val;
    }

    /// Set x2 (message register 0).  WS-RA: added with the return
    /// convention — before the flip nothing wrote any register but `x0`
    /// back, which is the defect the workstream exists to fix.
    #[inline(always)]
    pub fn set_x2(&mut self, val: u64) {
        self.gprs[2] = val;
    }

    /// Set x3 (message register 1).
    #[inline(always)]
    pub fn set_x3(&mut self, val: u64) {
        self.gprs[3] = val;
    }

    /// Set x4 (message register 2).
    #[inline(always)]
    pub fn set_x4(&mut self, val: u64) {
        self.gprs[4] = val;
    }

    /// Set x5 (message register 3).
    #[inline(always)]
    pub fn set_x5(&mut self, val: u64) {
        self.gprs[5] = val;
    }

    /// WS-RA (plan §3.3): restore a full six-register return frame —
    /// the context-restore shape the SVC return path uses.
    #[inline(always)]
    pub fn set_return_frame(&mut self, regs: [u64; 6]) {
        self.gprs[..6].copy_from_slice(&regs);
    }

    /// **WS-RR RR4.24**: set `ELR_EL1` — the address the `eret` returns to.
    ///
    /// The mutator the trap frame lacked before RR4, and the reason a fault
    /// reply could not have been honoured on hardware: seL4's fault reply
    /// distinguishes a **resume** (the thread restarts at the instruction
    /// that faulted, once the handler has repaired what faulted) from a
    /// **restart** (the reply supplied a new PC), and both are writes to this
    /// field.  Without it the trap layer could only ever return to the
    /// faulting instruction, which is the RR4 finding itself.
    ///
    /// Mirrors `SeLe4n.Kernel.Architecture.FaultRestartFrame.pc`, which the
    /// verified `RegisterFile.stageRestartFrame` installs as the thread's
    /// saved `pc`.
    #[inline(always)]
    pub fn set_elr_el1(&mut self, val: u64) {
        self.elr_el1 = val;
    }

    /// **WS-RR RR4.24**: set the saved user stack pointer (`SP_EL0`).
    ///
    /// The second word a fault reply may override — seL4's
    /// `fault_messages[MessageID_Syscall]` and `[MessageID_Exception]` both
    /// carry `SP_EL0` — mirroring `FaultRestartFrame.sp`.
    #[inline(always)]
    pub fn set_sp_el0(&mut self, val: u64) {
        self.sp_el0 = val;
    }

    /// **WS-RR RR4.16/RR4.24**: install a fault-restart frame.
    ///
    /// The Rust half of the verified `RegisterFile.stageRestartFrame`, in the
    /// same field order: `x0`-`x7`, the link register, the restart PC, and the
    /// stack pointer.  `regs` is `[x0..x7, lr, pc, sp]` — the flat encoding
    /// the Lean `FaultRestartFrame` marshals to, so the two sides carry one
    /// layout and not two.
    ///
    /// `SPSR_EL1` is deliberately **not** written: this model keeps PSTATE out
    /// of a fault handler's reach (see `Model.FaultContext.spsr`), which is
    /// strictly the fail-closed side of seL4's `sanitiseRegister`.
    ///
    /// **Consumer**: none on the live path.  The restart frame is installed
    /// into the *Lean* TCB by `applyFaultRestart` at reply time, and since
    /// WS-BP BP7.6 it reaches hardware through the context restore, which
    /// copies the whole saved context (`restore_commit_in`) rather than
    /// calling a per-field mutator.  This mutator and its two siblings remain
    /// the Rust half of the verified `stageRestartFrame` layout and are held
    /// to it by the host tests.
    #[inline(always)]
    pub fn set_fault_restart_frame(&mut self, regs: [u64; 11]) {
        self.gprs[..8].copy_from_slice(&regs[..8]);
        self.gprs[30] = regs[8];
        self.elr_el1 = regs[9];
        self.sp_el0 = regs[10];
    }
}

/// ESR_EL1 Exception Class (EC) field values.
/// ARM ARM D17.2.40: ESR_EL1 bits [31:26].
///
/// **WS-RR RR4.25**: the only reader of these names is the pre-readiness
/// mirror (`classify_synchronous_exception_mirror`) and the tests that pin it
/// against Lean.  Once a core is ready the mapping is the Lean model's
/// (`classifySynchronousException`), and `build.rs` holds
/// `handle_synchronous_exception`'s routing to the `sync_class::` tags it
/// returns: an `ec::` constant in the routing arms is the second
/// classification path RR4.25 retired, and the scanner rejects it.  PR #887
/// review round 2 compiles the table on every target because a core whose
/// Lean runtime is not yet initialized must still classify — through the
/// mirror — rather than enter a Lean-emitted symbol.
mod ec {
    /// SVC instruction execution in AArch64 state.
    pub const SVC_AARCH64: u64 = 0x15;
    /// Instruction Abort from a lower Exception level.
    pub const IABT_LOWER: u64 = 0x20;
    /// Instruction Abort from the current Exception level.
    pub const IABT_CURRENT: u64 = 0x21;
    /// PC alignment fault.
    pub const PC_ALIGN: u64 = 0x22;
    /// Data Abort from a lower Exception level.
    pub const DABT_LOWER: u64 = 0x24;
    /// Data Abort from the current Exception level.
    pub const DABT_CURRENT: u64 = 0x25;
    /// SP alignment fault.
    pub const SP_ALIGN: u64 = 0x26;
    /// WS-BP BP7.9: access to SIMD or floating-point functionality trapped by
    /// `CPACR_EL1.FPEN` — the lazy FP/SIMD switch's trap.
    pub const FP_ACCESS: u64 = 0x07;
}

/// Kernel error discriminants matching `sele4n-types::KernelError` and
/// Lean `SeLe4n.Model.KernelError`. Defined locally to avoid adding a
/// crate dependency from `sele4n-hal` (bare-metal HAL with zero deps).
///
/// AI1-A/AI1-B: Named constants replace bare numeric literals for
/// maintainability and cross-reference clarity.
mod error_code {
    /// `KernelError::NotImplemented = 17` — the discriminant the host
    /// lane's SVC dispatch publishes, since no Lean kernel is linked
    /// there.  On hardware the SVC arm reaches the real dispatch (AN9-F)
    /// behind the readiness gate (WS-RR RR5), so this value is a
    /// host-lane observable and a cross-reference, not the seam's
    /// contract; `handle_sync_svc_via_frame` pins it and
    /// `svc_arm_never_publishes_a_success_label` pins the property that
    /// does hold on every arm.
    #[allow(dead_code)]
    pub const NOT_IMPLEMENTED: u32 = 17;
    /// `KernelError::VmFault = 44` — data abort or instruction abort.
    pub const VM_FAULT: u32 = 44;
    /// `KernelError::UserException = 45` — alignment fault, unknown exception.
    /// Matches Lean `ExceptionModel.lean` mapping of `pcAlignment`,
    /// `spAlignment`, and `unknownReason` to `.error .userException`.
    pub const USER_EXCEPTION: u32 = 45;
}

/// Extract the Exception Class from ESR_EL1.
///
/// **WS-RR RR4.25**: this is a *diagnostic* reader, not a classifier.  It
/// feeds the unhandled-exception log line and the pre-readiness mirror
/// (`classify_synchronous_exception_mirror`); once a core is ready the routing
/// decision comes from the Lean model ([`classify_synchronous_exception`]),
/// so a running kernel has one classification path and not two.
#[inline(always)]
fn esr_ec(esr: u64) -> u64 {
    (esr >> 26) & 0x3F
}

/// **WS-RR RR4.25**: the synchronous exception classes, as the Lean model
/// tags them.
///
/// The values mirror `SeLe4n.Kernel.syncExceptionClassTag`
/// (`SeLe4n/Kernel/FaultEntry.lean`) and nothing else: the *mapping* from
/// `ESR_EL1` to a class lives in Lean's `classifySynchronousException`; the
/// pre-readiness mirror (`classify_synchronous_exception_mirror`) restates it
/// and is pinned to it over all 64 EC values, so a running kernel's routing
/// cannot classify differently — this side can only fail to recognise a tag,
/// which it routes to the same fail-closed unknown-exception arm the Lean map
/// defaults to.
pub mod sync_class {
    /// `SVC` from AArch64 — the syscall path, not a fault.
    pub const SVC: u32 = 0;
    /// Data abort.
    pub const DATA_ABORT: u32 = 1;
    /// Instruction abort.
    pub const INSTR_ABORT: u32 = 2;
    /// PC alignment fault.
    pub const PC_ALIGNMENT: u32 = 3;
    /// SP alignment fault.
    pub const SP_ALIGNMENT: u32 = 4;
    /// Anything the model does not classify.
    pub const UNKNOWN_REASON: u32 = 5;
    /// A data or instruction abort taken from the **current** EL — the kernel
    /// itself faulted (PR #887 review).  Never delivered; the handler halts.
    pub const KERNEL_ABORT: u32 = 6;
    /// **WS-BP BP7.9**: a trapped FP/SIMD access (EC `0x07`) — routed to the
    /// lazy switch, never delivered as a fault.
    pub const FP_ACCESS: u32 = 7;
}

/// **PR #887 review**: was the exception taken from EL0?
///
/// Reads `SPSR_EL1.M[3:2]` — the exception level the PE was in when the
/// exception was taken: `0` for EL0, `1` for EL1.  Mirrors the Lean
/// `ExceptionContext.takenFromEl0`.  The syndrome-independent half of the
/// kernel-origin gate: `KERNEL_ABORT` catches the two abort classes whose EC
/// encodes "current EL", but an alignment fault or an undefined instruction
/// has one EC whichever EL raised it, and only the saved PSTATE says which.
#[inline(always)]
fn exception_taken_from_el0(spsr: u64) -> bool {
    (spsr >> 2) & 0x3 == 0
}

/// **PR #887 review**: halt if the exception was taken from EL1.
///
/// Both `__el0_sync_entry` and `__el1_sync_entry` land in
/// `handle_synchronous_exception`, and before this gate a kernel page fault
/// was classified by EC alone, attributed to the current user thread, and —
/// once `lean_ready` flips — delivered to that thread's fault handler with
/// the kernel's FAR, ESR and register window, whose reply could then resume
/// the kernel at the faulting instruction.  A kernel-origin exception halts
/// with a diagnostic and is never routed, never delivered, and never
/// `eret`ed through.  A plain Rust function rather than a block inside the
/// `extern "C"` handler so the host lane can observe the halt (a panic
/// cannot unwind across a C-ABI frame).
#[inline(always)]
fn halt_if_kernel_origin(frame: &TrapFrame, esr: u64) {
    if !exception_taken_from_el0(frame.spsr_el1) {
        crate::kprintln!(
            "kernel-origin synchronous exception: EC=0x{:02x} ESR=0x{:016x} ELR=0x{:016x} FAR=0x{:016x} SPSR=0x{:016x}",
            esr_ec(esr),
            esr,
            frame.elr_el1,
            frame.far_el1,
            frame.spsr_el1
        );
        crate::cpu::fatal_halt();
    }
}

/// **PR #887 review**: a data or instruction abort taken from the current EL
/// — the kernel faulted.  The origin gate halts on every EL1-origin exception
/// already; this is the syndrome-classified half of the same rule, so a
/// `KERNEL_ABORT` reaching it (a saved PSTATE claiming EL0 with a current-EL
/// syndrome) is a contradiction the kernel must not interpret.
#[inline(always)]
fn halt_on_kernel_abort(frame: &TrapFrame, esr: u64) -> ! {
    crate::kprintln!(
        "kernel abort: EC=0x{:02x} ESR=0x{:016x} ELR=0x{:016x} FAR=0x{:016x}",
        esr_ec(esr),
        esr,
        frame.elr_el1,
        frame.far_el1
    );
    crate::cpu::fatal_halt()
}

/// **WS-RR RR4.25**: classify a synchronous exception **through the Lean
/// model** once this core may enter it.
///
/// On the hardware target a *ready* core calls
/// `lean_classify_synchronous_exception` (`@[export]` on
/// `SeLe4n.Kernel.classifySynchronousExceptionExport`), so the routing decision
/// and the delivered fault's kind come from one classifier and cannot drift
/// apart — the `esr_ec` match this replaced could, and a drift on the abort
/// arms would have routed a fault to the wrong handler, or to none.
///
/// **PR #887 review round 2 — the upcall is behind the readiness gate.**  The
/// contract in `lean_ready.rs` admits no exception for a pure function: no
/// Lean-emitted symbol may be entered from a PE whose runtime state is not
/// initialized, and the first cut called this one unconditionally on the
/// strength of a SAFETY comment claiming it needed no runtime.  The claim was
/// about the function; the contract is about the symbol, and a scanner cannot
/// tell the difference.  So a core that is not ready classifies through
/// `classify_synchronous_exception_mirror` — the same `esr_ec` table the host
/// lane runs, pinned to the Lean mapping across all 64 EC values by
/// `sync_class_mirrors_lean_ec_table` — and the routing then reaches the
/// seams' fail-closed halves (`deliver_fault`'s status frame), which is the
/// documented pre-readiness behaviour of the whole fault path.  Reachable
/// on no core since WS-BP BP6 marks each one ready before it unmasks IRQs: no core
/// runs EL0 code without a Lean runtime, and an EL1-origin exception halts
/// before classification (`halt_if_kernel_origin`).  `build.rs` pins the
/// relation — the Lean call sits after the gate in this body, the mirror is
/// the other branch — and `scan_lean_upcalls_readiness_gated` derives the set
/// of every Lean upcall in the HAL from the Lean tree's `@[export]`s, so the
/// next upcall cannot be written outside the gate silently.
///
/// It is a pure query: no kernel state is read or committed, so it needs no
/// entry lock and is called *before* one is taken, which is what lets the
/// caller route an `SVC` away from the fault path without entering the kernel
/// twice.
#[cfg(feature = "hw_target")]
#[inline]
fn classify_synchronous_exception(esr: u64) -> u32 {
    let core_id = crate::per_cpu::current_core_id_from_tpidr();
    if crate::lean_ready::lean_ready(core_id as usize) {
        extern "C" {
            /// # Safety
            ///
            /// Calling this is sound only on a core whose Lean runtime is
            /// initialised — `lean_ready(current_core_id_from_tpidr())` must
            /// have returned `true` on *this* PE, which the enclosing branch
            /// has just checked.  A not-ready core must classify through the
            /// Rust mirror instead; the two are pinned to one table.
            fn lean_classify_synchronous_exception(esr: u64) -> u32;
        }
        // SAFETY: `lean_classify_synchronous_exception` is the C-callable
        // wrapper the Lean compiler emits for
        // `Kernel.classifySynchronousExceptionExport`.  It takes a `u64` and
        // returns a `u32` and reads no kernel state.  It does allocate: the
        // generated C builds an `ExceptionContext` on the Lean heap, outside
        // the kernel-entry lock, which is why the heap keeps its own lock
        // (`lean_heap.rs`, the concurrency note).  This core's Lean runtime is
        // initialized — the `lean_ready` gate just checked — so entering the
        // symbol is within the runtime's contract.
        unsafe { lean_classify_synchronous_exception(esr) }
    } else {
        classify_synchronous_exception_mirror(esr)
    }
}

/// The host lane has no Lean symbol to call, so it classifies through the
/// mirror unconditionally — the same answers a not-yet-ready core gets on
/// hardware.
#[cfg(not(feature = "hw_target"))]
#[inline]
fn classify_synchronous_exception(esr: u64) -> u32 {
    classify_synchronous_exception_mirror(esr)
}

/// **The pre-readiness classifier**: the `ESR_EL1` exception-class table as
/// the Lean model defines it, in Rust.
///
/// Two callers: the host test lane, where the Lean symbol is not linked, and
/// a hardware core whose Lean runtime is not yet initialized (see
/// [`classify_synchronous_exception`]).  It is **not** a second live
/// classification path for a running kernel: once a core is ready every
/// exception it takes is classified in Lean, and this table's only job is to
/// agree with that one.  Agreement is pinned from both sides —
/// `sync_class_mirrors_lean_ec_table` walks all 64 EC values against the
/// expected table here, and the Lean suite walks the same 64 values against
/// `classifySynchronousException` — so a mapping edit on either side that the
/// other does not mirror fails a test rather than routing a fault to the wrong
/// handler.
#[inline]
fn classify_synchronous_exception_mirror(esr: u64) -> u32 {
    match esr_ec(esr) {
        ec::SVC_AARCH64 => sync_class::SVC,
        ec::DABT_LOWER => sync_class::DATA_ABORT,
        ec::IABT_LOWER => sync_class::INSTR_ABORT,
        ec::DABT_CURRENT | ec::IABT_CURRENT => sync_class::KERNEL_ABORT,
        ec::PC_ALIGN => sync_class::PC_ALIGNMENT,
        ec::SP_ALIGN => sync_class::SP_ALIGNMENT,
        ec::FP_ACCESS => sync_class::FP_ACCESS,
        _ => sync_class::UNKNOWN_REASON,
    }
}

/// **WS-RR RR4.23**: deliver a fault to the faulting thread's handler through
/// the verified Lean fault path, or — when this core's Lean runtime is not up
/// — publish a fail-closed error frame.
///
/// The delivery half is `lean_handle_fault`
/// (`@[export]` on `SeLe4n.Kernel.faultEntry`), which spills the trap frame's
/// fault window (`x0`-`x7`, `SP_EL0`, `x30`) into the faulting thread's saved
/// register context, classifies, builds the fault message from those
/// registers, and runs the verified, flow-checked `faultDeliverOnCoreChecked`:
/// the thread blocks on its handler's endpoint
/// awaiting a reply, or — with no usable handler — is descheduled and marked
/// `.Inactive`.  Either way it comes out **not runnable on this core**
/// (`faultEntryStep_not_dispatchable`), which is what makes the pre-RR4
/// fault loop unrepresentable.
///
/// It runs inside [`crate::kernel_entry::with_kernel_entry`]: the Lean entry
/// commits through an `IO.Ref` read-then-write, not a cross-core atomic, so it
/// must be serialised like every other state-committing seam.
///
/// # Why the core halts afterwards
///
/// The model has just descheduled the faulting thread, and since WS-BP BP7.6
/// the entry installs what this core resumes — its successor, or the idle
/// loop — into the frame `trap.S` returns through, so the handler returns
/// (`take_restored`).  A delivery that installed nothing would `eret` through
/// the faulting thread's own frame, straight back onto the instruction that
/// faulted, which is precisely the defect RR4 exists to remove, so that
/// fallback stops the core: `fatal_halt` after a diagnostic, rather than
/// spin.
///
/// # The not-ready path (WS-RR RR4.22; PR #887 review round 3)
///
/// A core whose Lean runtime is not up cannot deliver — and, on hardware, it
/// cannot return either: the abort left `ELR_EL1` on the faulting
/// instruction, so a published frame would be `eret`ed back into the same
/// abort and the core would wedge.  The not-ready path therefore **halts**
/// (`halt_abort_before_lean_ready`), which makes both branches of this
/// function diverge on hardware; the SVC seam, whose exception advanced the
/// PC, is the one place a fallback frame is a coherent return.  The host lane
/// keeps the RR4.22 fallback frame as the harness observable — a full
/// **status-label** frame (ABI v3): `x0 = 0`, `x1` a `MessageInfo` whose
/// label is `ERROR_LABEL_BASE + discriminant`, and `x2`-`x5` cleared, never
/// the retired raw-discriminant-in-`x0` shape that left `x1` untouched and
/// let a resumed thread decode a fault as a successful syscall carrying a
/// forged badge — and `build.rs` pins that the frame write is host-only and
/// the halt sits on the not-ready path.
#[allow(unused_variables)]
fn deliver_fault(frame: &mut TrapFrame, fallback_discriminant: u32) {
    #[cfg(feature = "hw_target")]
    {
        let core_id = crate::per_cpu::current_core_id_from_tpidr();
        if crate::lean_ready::lean_ready(core_id as usize) {
            extern "C" {
                // The fifteen words the Lean seam consumes: the syndrome, and
                // the fault window the trap frame saved (`x0`-`x7`, `SP_EL0`,
                // `x30`) — the registers seL4's `setMRs_fault` reads and
                // `handleFaultReply` writes.  The window is spilled into the
                // thread's saved register context on the Lean side before the
                // fault context is built (`writeFaultRegistersToTcb`): the
                // Lean mirror of the register file is partial and, between
                // syscalls, holds the *last syscall's* arguments, so building
                // the context from the mirror alone would report a stale
                // argument window and, on resume, reinstall it over the
                // thread's live registers.
                /// # Safety
                ///
                /// Sound only on a core whose Lean runtime is initialised
                /// (`lean_ready` checked on *this* PE) and only for an
                /// exception taken from EL0: a kernel-origin frame must halt
                /// before reaching here, or a user-level handler would receive
                /// the kernel's own register window.  The fifteen words must be
                /// the live trap frame's fault window, not the partial Lean
                /// register mirror, which between syscalls holds the previous
                /// syscall's arguments.
                #[allow(clippy::too_many_arguments)]
                fn lean_handle_fault(
                    core_id: u64,
                    esr: u64,
                    elr: u64,
                    spsr: u64,
                    far: u64,
                    x0: u64,
                    x1: u64,
                    x2: u64,
                    x3: u64,
                    x4: u64,
                    x5: u64,
                    x6: u64,
                    x7: u64,
                    sp_el0: u64,
                    lr: u64,
                ) -> crate::lean_runtime::LeanBaseIoUnit;
            }
            let (esr, elr, spsr, far) =
                (frame.esr_el1, frame.elr_el1, frame.spsr_el1, frame.far_el1);
            let g = frame.gprs;
            let sp_el0 = frame.sp_el0;
            // SAFETY: `lean_handle_fault` is the C-callable wrapper the Lean
            // compiler emits for `Kernel.faultEntry`
            // (`@[export lean_handle_fault]`).  It takes fifteen `u64`s and
            // returns its `BaseIO Unit` value, `lean_box(0)`; calling it is sound from EL1 exception context
            // once this core's Lean runtime is initialized (the gate just
            // checked) and inside the kernel-entry lock (taken below), which is
            // what serialises its `IO.Ref` commit.
            let res = crate::kernel_entry::with_kernel_entry(core_id as usize, || unsafe {
                lean_handle_fault(
                    core_id, esr, elr, spsr, far, g[0], g[1], g[2], g[3], g[4], g[5], g[6], g[7],
                    sp_el0, g[30],
                )
            });
            // The export returns its `BaseIO Unit` value, `lean_box(0)`,
            // checked outside the bracket so a malformed one halts this PE
            // without holding the kernel-entry lock
            // (`lean_runtime::discharge_base_io`).
            // SAFETY: `res` is the value the export just returned; if it is
            // a heap object this caller owns its one reference.
            unsafe { crate::lean_runtime::discharge_base_io(res, "lean_handle_fault") };
            // WS-BP BP7.6: the delivery descheduled the faulting thread and the
            // kernel installed what this core resumes — its successor, or the
            // idle loop — so the handler returns through that.
            if crate::trap::take_restored() {
                return;
            }
            crate::kprintln!(
                "[core {}] fault delivered and no context restored; halting (ESR=0x{:016x} ELR=0x{:016x})",
                core_id,
                esr,
                elr
            );
            crate::cpu::fatal_halt();
        }
        // PR #887 review round 3: a core whose Lean runtime is not up cannot
        // deliver, and a status frame cannot fail-close an abort — `trap.S`
        // would `eret` through the unchanged `ELR_EL1` onto the instruction
        // that faulted, and the core would take the same abort forever.  So
        // the not-ready path halts, as the delivered arm does.
        halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);
    }
    // The host lane's fallback: the harness observable that the abort arms
    // reached this seam (`handle_sync_data_abort_via_frame` and the
    // per-core counter tests drive the whole handler).  On hardware the
    // function never returns; `build.rs` pins that this write is host-only.
    #[cfg(not(feature = "hw_target"))]
    frame.set_return_frame(crate::svc_dispatch::error_frame_regs(fallback_discriminant));
}

/// **WS-BP BP7.9: the lazy FP/SIMD switch** — EC `0x07` from EL0.
///
/// The Lean half is `lean_handle_fp_access` (`@[export]` on
/// `SeLe4n.Kernel.fpAccessEntry`): it saves the trap frame, captures the core's
/// registers if they hold a recorded owner's live values, commits
/// `Architecture.fpAccessOnCore`, loads the faulting thread's own saved context
/// (`fp_context::load_commit`) and restores the thread — whose `ELR_EL1` still
/// names the FP/SIMD instruction — with the trap lifted, so the instruction
/// re-executes with the thread's own state.  When the thread's live values are
/// on another core the switch answers *retry*: nothing is loaded, the trap stays
/// armed and the thread traps again until that core has released them.
///
/// Same lock, same readiness gate and same restored-frame return as
/// [`deliver_fault`].  A core whose Lean runtime is not up cannot switch and
/// cannot return — `ELR_EL1` is on the trapped instruction, so a returned frame
/// would trap again forever — so it halts, as an abort does
/// ([`halt_abort_before_lean_ready`]); and a switch that restored nothing halts
/// too, since returning through the unchanged frame re-executes into the same
/// trap.  The host lane has no FP/SIMD registers and no Lean kernel, so the arm
/// is inert there.
#[allow(unused_variables)]
fn deliver_fp_access(frame: &mut TrapFrame) {
    #[cfg(feature = "hw_target")]
    {
        let core_id = crate::per_cpu::current_core_id_from_tpidr();
        if crate::lean_ready::lean_ready(core_id as usize) {
            extern "C" {
                /// # Safety
                ///
                /// Sound only on a core whose Lean runtime is initialised
                /// (`lean_ready` checked on *this* PE), inside the kernel-entry
                /// lock, and only for an FP/SIMD trap taken from EL0: the entry
                /// loads a thread's FP/SIMD context into this PE's registers and
                /// lifts the trap for the thread its committed state runs here.
                fn lean_handle_fp_access(core_id: u64) -> crate::lean_runtime::LeanBaseIoUnit;
            }
            // SAFETY: `lean_handle_fp_access` is the C-callable wrapper the
            // Lean compiler emits for `Kernel.fpAccessEntry`
            // (`@[export lean_handle_fp_access]`).  It takes one `u64` and
            // returns its `BaseIO Unit` value, `lean_box(0)`; sound from EL1
            // exception context once this core's Lean runtime is initialized
            // (the gate just checked) and inside the kernel-entry lock (taken
            // here), which serialises its `IO.Ref` commits.
            let res = crate::kernel_entry::with_kernel_entry(core_id as usize, || unsafe {
                lean_handle_fp_access(core_id)
            });
            // SAFETY: `res` is the value the export just returned; if it is
            // a heap object this caller owns its one reference.
            unsafe { crate::lean_runtime::discharge_base_io(res, "lean_handle_fp_access") };
            // The switch restored the thread that trapped, with the trap set
            // for it; return through that frame.
            if crate::trap::take_restored() {
                return;
            }
            crate::kprintln!(
                "[core {}] FP/SIMD access switched and no context restored; halting (ELR=0x{:016x})",
                core_id,
                frame.elr_el1
            );
            crate::cpu::fatal_halt();
        }
        halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);
    }
}

/// **PR #887 review round 3**: an EL0 abort taken on a core whose Lean
/// runtime is not initialized.  Nothing can be delivered (there is no model
/// to deliver into) and nothing can be returned: the abort left `ELR_EL1` on
/// the faulting instruction, so any frame the handler published would be
/// `eret`ed straight back into the same abort — the wedge RR4 exists to
/// remove, reintroduced on the fallback.  The only fail-closed action is to
/// stop the core, as `deliver_fault`'s delivered arm does when no context
/// was restored.  The SVC seam is different and keeps its status frame: an `SVC`
/// advances `ELR_EL1` past itself, so a frame returned to a thread is a
/// coherent outcome there (and the not-ready behaviour of the SVC seam as a
/// whole is RR5's to decide, together with the ungated `dispatch_svc` beside
/// it).  Unreachable today — no core sets `lean_ready`, and no user thread
/// exists before the runtime that creates it — and pinned by
/// `abort_before_lean_ready_halts` on the host lane, where `fatal_halt`
/// panics.
/// **PR #887 review round 5**: a syscall-raised fault has been delivered (or
/// the caller suspended fail-closed) by the Lean dispatch — outcome tag 2,
/// `SyscallOutcome.faulted`.  The model has descheduled the caller and, on
/// the handler's reply, restarts it at the `SVC` (`svcFaultIP`).  Since
/// WS-BP BP7.6 the dispatch installs this core's successor and the SVC arm
/// returns through it before reaching this helper; the helper is the fallback
/// for a dispatch that installed nothing, where returning would `eret` the
/// caller past the `SVC` it is to re-issue, so the core stops.  Pinned by
/// `delivered_syscall_fault_halts` on the host lane, where `fatal_halt`
/// panics, and by `scan_trap_rs_faulted_outcome_halts` in `build.rs`.
fn halt_after_delivered_syscall_fault(frame: &TrapFrame) -> ! {
    crate::kprintln!(
        "syscall fault delivered and no context restored; halting (x7=0x{:x} ELR=0x{:016x})",
        frame.x7(),
        frame.elr_el1
    );
    crate::cpu::fatal_halt()
}

#[cfg_attr(not(feature = "hw_target"), allow(dead_code))]
fn halt_abort_before_lean_ready(core_id: u64, esr: u64, elr: u64) -> ! {
    crate::kprintln!(
        "[core {}] EL0 abort before the Lean runtime is ready; halting (ESR=0x{:016x} ELR=0x{:016x})",
        core_id,
        esr,
        elr
    );
    crate::cpu::fatal_halt()
}

/// **PR #887 review**: deliver an unknown-syscall fault through the verified
/// Lean path, or — when this core's Lean runtime is not up — publish the
/// fail-closed `invalidSyscallNumber` status frame the prefilter used to.
///
/// The delivery half is `lean_handle_unknown_syscall` (`@[export]` on
/// `SeLe4n.Kernel.unknownSyscallEntry`), which builds seL4's `UnknownSyscall`
/// fault from the syscall-number register (`x7`) and the trap frame's fault
/// window and runs the same flow-checked delivery as `deliver_fault`: the
/// thread blocks on its handler's endpoint awaiting a reply (a handler that
/// emulates the call replies and the thread continues after the `SVC`), or —
/// with no usable handler — is suspended fail-closed.  Same lock, same
/// readiness gate, same restored-frame return and same fallback halt as
/// `deliver_fault`, for the same reasons.
///
/// The not-ready path differs from `deliver_fault`'s, deliberately: this seam
/// keeps its status frame, because an `SVC` advances `ELR_EL1` past itself
/// and a frame returned to the thread is a coherent outcome, where an abort's
/// would re-execute the faulting instruction (PR #887 review round 3).  What
/// a not-ready core should do with an `SVC` at all is RR5's question, asked
/// once for the whole SVC seam together with the ungated `dispatch_svc`.
///
/// **WS-RR RR5.6 / PR #889 review**: answered — a not-ready core **halts** on
/// every `SVC`, in the routing arm, *before* this delivery is reached (see the
/// `sync_class::SVC` arm).  So on hardware the readiness branch below is only
/// ever taken with the core ready; the status-frame fallback after it is the
/// host lane's observable (no `hw_target`, no gate compiled), reached by the
/// integration tests that mark the host core ready first.
#[allow(unused_variables)]
fn deliver_unknown_syscall(frame: &mut TrapFrame) {
    #[cfg(feature = "hw_target")]
    {
        let core_id = crate::per_cpu::current_core_id_from_tpidr();
        if crate::lean_ready::lean_ready(core_id as usize) {
            extern "C" {
                /// # Safety
                ///
                /// Sound only on a core whose Lean runtime is initialised
                /// (`lean_ready` checked on *this* PE) and only for an `SVC`
                /// taken from EL0.  The caller must pass the live trap frame's
                /// window; the model restarts the faulting thread at the `SVC`,
                /// so a stale window would be reinstalled over its registers.
                #[allow(clippy::too_many_arguments)]
                fn lean_handle_unknown_syscall(
                    core_id: u64,
                    esr: u64,
                    elr: u64,
                    spsr: u64,
                    far: u64,
                    x0: u64,
                    x1: u64,
                    x2: u64,
                    x3: u64,
                    x4: u64,
                    x5: u64,
                    x6: u64,
                    x7: u64,
                    sp_el0: u64,
                    lr: u64,
                ) -> crate::lean_runtime::LeanBaseIoUnit;
            }
            let (esr, elr, spsr, far) =
                (frame.esr_el1, frame.elr_el1, frame.spsr_el1, frame.far_el1);
            let g = frame.gprs;
            let sp_el0 = frame.sp_el0;
            // SAFETY: `lean_handle_unknown_syscall` is the C-callable wrapper
            // the Lean compiler emits for `Kernel.unknownSyscallEntry`
            // (`@[export lean_handle_unknown_syscall]`).  Fifteen `u64`s and
            // its `BaseIO Unit` value, `lean_box(0)`; sound from EL1 exception context once this core's
            // Lean runtime is initialized (the gate just checked) and inside
            // the kernel-entry lock (taken below), which serialises its
            // `IO.Ref` commit.
            let res = crate::kernel_entry::with_kernel_entry(core_id as usize, || unsafe {
                lean_handle_unknown_syscall(
                    core_id, esr, elr, spsr, far, g[0], g[1], g[2], g[3], g[4], g[5], g[6], g[7],
                    sp_el0, g[30],
                )
            });
            // The export returns its `BaseIO Unit` value, `lean_box(0)`,
            // checked outside the bracket so a malformed one halts this PE
            // without holding the kernel-entry lock
            // (`lean_runtime::discharge_base_io`).
            // SAFETY: `res` is the value the export just returned; if it is
            // a heap object this caller owns its one reference.
            unsafe { crate::lean_runtime::discharge_base_io(res, "lean_handle_unknown_syscall") };
            // WS-BP BP7.6: as for an abort — return through what the kernel
            // installed for this core.
            if crate::trap::take_restored() {
                return;
            }
            crate::kprintln!(
                "[core {}] unknown syscall delivered and no context restored; halting (x7=0x{:x} ELR=0x{:016x})",
                core_id,
                g[7],
                elr
            );
            crate::cpu::fatal_halt();
        }
    }
    frame.set_return_frame(crate::svc_dispatch::error_frame_regs(
        crate::svc_dispatch::DispatchError::InvalidSyscallId.kernel_error_discriminant(),
    ));
}

/// Synchronous exception handler — called from assembly after context save.
///
/// Routes to the appropriate handler based on the ESR_EL1 Exception Class:
/// - SVC (0x15): Syscall dispatch (reads x0-x5, x7 from TrapFrame)
/// - Data/Instruction Abort: VM fault handling (placeholder)
/// - Other: Unhandled exception (prints diagnostic and halts)
///
/// AG9-F: CSDB after ESR classification prevents speculative execution of
/// the wrong handler branch (Spectre v1 mitigation for exception dispatch).
///
/// AK5-F (R-HAL-H04 / HIGH): ESR and FAR are read from the saved TrapFrame,
/// not from the live registers. This keeps the classification stable under
/// nested exceptions — a SError or second data-abort during fault handling
/// would otherwise mutate the live ESR/FAR before we inspected them.
#[no_mangle]
pub extern "C" fn handle_synchronous_exception(frame: &mut TrapFrame) {
    let esr = frame.esr_el1;
    // WS-BP BP7.3: the frame is the Lean kernel's to read for the handler's
    // duration, so the whole outgoing context reaches the thread's TCB.
    let _in_flight = InFlightFrame::publish(frame);
    // PR #887 review: **an exception taken from EL1 is the kernel's own
    // fault**, whatever its syndrome — halt before routing anything.  The
    // `build.rs` scanner pins that this call precedes the classification.
    halt_if_kernel_origin(frame, esr);
    // WS-RR RR4.25: the class comes from the Lean model, not from a second
    // `esr_ec` match here.  `esr_ec` survives as a diagnostic reader only.
    let exception_class = classify_synchronous_exception(esr);

    // AG9-F: CSDB after reading the exception class ensures speculative
    // execution cannot bypass the match and enter the wrong handler.
    crate::barriers::csdb();

    match exception_class {
        sync_class::SVC => {
            // CLOSED at AN9-F: Wire Lean FFI dispatch via the
            // `dispatch_svc` shim (closes DEF-R-HAL-L14 per WS-AN AN9-F).
            // CLOSED at WS-RC R2.B: Lean side substantively routes
            // into `Kernel.syscallEntryChecked` (closes DEEP-FFI-01).
            //
            // The seLe4n ABI uses x7 for the syscall number (Lean
            // `arm64DefaultLayout.syscallNumReg = ⟨7⟩`).  The
            // dispatcher reads x0..x5 + msg_info from the trap frame,
            // validates argument count against `MessageInfo.length`,
            // and forwards via the `lean_syscall_dispatch_cross_core`
            // `extern "C"` symbol (Lean-emitted from
            // `SeLe4n/Kernel/SyscallDispatchEntry.lean`) into the Lean
            // kernel.
            //
            // **WS-RR RR8.13**: this named `syscall_dispatch_inner` and
            // described the ABI v1 status convention — a raw
            // `KernelError` discriminant in `x0`, wrapped as
            // `DispatchError::Kernel(disc)`.  Both were retired: the
            // legacy export is gone (see `kernel_entry.rs`'s own note),
            // and WS-RA's `SYSCALL_ABI_VERSION = 3` puts the status in
            // the **`x1` MessageInfo label** at `errorLabelBase + d`,
            // with `x0` carrying the badge or primary result at full
            // width.  The scalar export return is the *outcome tag*
            // (`0` = the mailbox frame is the caller's return, `1` =
            // the caller blocked, `2` = it faulted), and the six-word
            // frame travels through `ffiSyscallReturnFrame`.  A comment
            // naming a deleted symbol and a retired convention is what
            // `docs/planning/UNFINISHED_SMP_WORK.md` §4 finding 11
            // recorded; this is that finding closed.
            //
            // WS-SM SM1.I.4: record per-core syscall count for
            // benchmarking / post-mortem attribution.  Wait-free
            // (single AtomicU64::fetch_add) and not on any
            // correctness path.
            let _ = crate::per_cpu_stats::record_syscall();
            // PR #889 review: the readiness decision precedes **every** SVC
            // outcome — the full-width narrowing below, the id and
            // argument-count prefilters inside `dispatch_svc`, and the
            // unknown-syscall delivery — because the halt's reason (a thread on
            // a not-ready core is never preempted again, so any frame returned
            // to it is the CPU forever) does not depend on which of those
            // outcomes the `SVC` would otherwise take.  Before this the
            // oversized-`x7` and prefilter paths resumed the caller on a
            // not-ready core with an error frame.  `dispatch_svc` consults the
            // gate again on its own path, which is where `build.rs` derives the
            // Lean call's dominance from; this one covers the outcomes that
            // never reach it.
            if !crate::lean_ready::lean_ready(crate::per_cpu::current_core_id_from_tpidr() as usize)
            {
                crate::svc_dispatch::halt_syscall_before_lean_ready(
                    crate::per_cpu::current_core_id_from_tpidr() as usize,
                    frame.x7(),
                );
            }
            let args = crate::svc_dispatch::SyscallArgs::from_trap_frame(frame);
            // PR #887 review round 3: the syscall number is the FULL 64-bit
            // `x7`.  Narrowing first would make `0x1_0000_0002` syscall 2; a
            // word the ABI cannot name is an unknown syscall, delivered to the
            // thread's fault handler like any other, with the full word.
            let dispatched = match u32::try_from(frame.x7()) {
                Ok(syscall_id) => crate::svc_dispatch::dispatch_svc(syscall_id, &args),
                Err(_) => Err(crate::svc_dispatch::DispatchError::InvalidSyscallId),
            };
            // WS-BP BP7.6: the Lean dispatch installed what this core resumes —
            // the caller with its result staged in its context, the thread its
            // syscall switched to, or the idle loop — so the handler returns
            // through that frame and publishes nothing over it.  Every arm below
            // is the fallback for a dispatch that installed nothing.
            if crate::trap::take_restored() {
                return;
            }
            // WS-RA (plan §3.1/§3.3): the writeback is a six-register
            // context restore — `x0` the value, the offset error label on
            // `x1`, `x2`-`x5` message registers.  A blocked caller has NO
            // return frame (its stale registers are not a return value;
            // since WS-BP BP7.6 the context restore above installs what the
            // core resumes instead).  Prefilter rejections
            // surface as label-encoded error frames like every kernel
            // rejection, retiring the raw-discriminant `x0` write and its
            // documented collision.
            match dispatched {
                Ok(crate::svc_dispatch::SvcOutcome::Frame(regs)) => frame.set_return_frame(regs),
                // PR #887 review round 5: the caller took a fault at the
                // seam (a failed capability lookup delivered to its handler,
                // or the fail-closed suspend).  No frame exists, and the
                // model restarts the caller AT the `SVC` on its handler's
                // reply — the `Blocked` sentinel would `eret` it past the
                // `SVC` instead.  Reached only when the dispatch installed no
                // context (the restore returns above), so this arm halts, as
                // the delivered unknown-syscall and abort paths do.
                Ok(crate::svc_dispatch::SvcOutcome::Faulted) => {
                    halt_after_delivered_syscall_fault(frame);
                }
                Ok(crate::svc_dispatch::SvcOutcome::Blocked) => {
                    // Reached only when the dispatch installed no context
                    // (WS-BP BP7.6's restore returns above).  `trap.S` would
                    // then `eret` through the blocked caller's own saved
                    // frame, so poison it: left untouched, the caller's request
                    // registers (an `x1` label of `0`) decode as a false
                    // success carrying the caller's own capability
                    // pointer as the "badge" (PR #866 review).  The
                    // sentinel makes the premature resume fail closed —
                    // its label decodes as `UnknownKernelError`, never as
                    // success and never as a kernel-emitted error.
                    frame.set_return_frame(crate::svc_dispatch::blocked_resume_sentinel_regs());
                }
                // PR #887 review: a syscall number outside `SyscallId` is
                // seL4's `UnknownSyscall` fault — delivered to the thread's
                // fault handler (so a handler can emulate the call), not an
                // `invalidSyscallNumber` frame handed back to the thread.
                Err(crate::svc_dispatch::DispatchError::InvalidSyscallId) => {
                    deliver_unknown_syscall(frame);
                }
                Err(e) => frame.set_return_frame(crate::svc_dispatch::error_frame_regs(
                    e.kernel_error_discriminant(),
                )),
            }
        }
        sync_class::KERNEL_ABORT => {
            // PR #887 review: the kernel faulted — halt, never deliver.
            halt_on_kernel_abort(frame, esr);
        }
        sync_class::FP_ACCESS => {
            // WS-BP BP7.9: a thread used FP/SIMD with its core's trap armed —
            // the lazy switch loads its context and restarts the instruction.
            // An EL1-origin one halted above (`halt_if_kernel_origin`): the
            // kernel is FP-free, so an FP instruction at EL1 is a defect.
            deliver_fp_access(frame);
        }
        sync_class::DATA_ABORT | sync_class::INSTR_ABORT => {
            // WS-RR RR4.21/RR4.23: an abort is **delivered** to the faulting
            // thread's fault handler, not returned to the thread that took it.
            // The pre-RR4 arm set `x0 = VM_FAULT` and returned, so `trap.S`
            // `eret`ed straight back onto the faulting instruction: any user
            // thread touching an unmapped page wedged its core forever.
            //
            // WS-SM SM1.I.4: per-core VM-fault attribution, unchanged.
            let _ = crate::per_cpu_stats::record_vm_fault();
            deliver_fault(frame, error_code::VM_FAULT);
        }
        sync_class::PC_ALIGNMENT | sync_class::SP_ALIGNMENT => {
            // WS-RR RR4.21: an alignment fault is a `userException` fault and
            // is delivered on the same path, for the same reason — returning
            // it to the faulting thread re-executes the misaligned access.
            // WS-SM SM1.I.4: per-core user-exception attribution.
            let _ = crate::per_cpu_stats::record_user_exception();
            deliver_fault(frame, error_code::USER_EXCEPTION);
        }
        _ => {
            // Unknown exception class — a `userException` fault, delivered
            // like the rest.  The diagnostic reports the raw EC, which is
            // what a reader needs when the model did not classify it.
            // WS-SM SM1.I.4: per-core user-exception attribution.
            let _ = crate::per_cpu_stats::record_user_exception();
            crate::kprintln!(
                "unhandled exception class: EC=0x{:02x} ESR=0x{:016x}",
                esr_ec(esr),
                esr
            );
            deliver_fault(frame, error_code::USER_EXCEPTION);
        }
    }
}

// The single-core `handle_irq` that predated the per-core IRQ path was
// removed when `trap.S`'s IRQ vectors were redirected to
// [`handle_irq_per_core`] (the redirect the SM1.I.1 seam was staged
// for).  Its contracts survive in the per-core handler: the AG5-C
// acknowledge → EOI → dispatch sequence (via `dispatch_irq_with_iar`),
// the AI1-C/M-26 tick-count ownership rule (the global `TICK_COUNT` is
// advanced exclusively by the Lean kernel via `ffi_timer_reprogram`;
// the ISR only re-arms the comparator and records the per-core
// diagnostic counter), and the AN8-C.3 panic-lint discipline.

/// **WS-SM SM1.I.1 / SM5**: Per-core IRQ handler entry — the IRQ path
/// `trap.S`'s `__el0_irq_entry` / `__el1_irq_entry` vectors branch to.
///
/// Reads the calling core's id from `TPIDR_EL1` via
/// [`crate::per_cpu::current_core_id_from_tpidr`], records per-core IRQ
/// dispatch / timer-tick / SGI statistics ([`crate::per_cpu_stats`]),
/// then dispatches the IRQ through
/// [`crate::gic::dispatch_irq_with_iar`] (which acknowledges, EOIs with
/// the full IAR, and preserves the source-CPU bits — the AG5-C sequence).
/// The dispatch closure routes by INTID:
///
///   * `INTID == TIMER_PPI_ID (30)` →
///     [`crate::timer::per_core_timer_tick_isr`]: records the per-core
///     tick, re-arms the per-core comparator, and drives the verified
///     Lean per-core scheduler timer tick (`lean_per_core_timer_tick`)
///     inside `kernel_entry::with_kernel_entry`.  The global
///     `TICK_COUNT` is untouched — it is advanced exclusively by the
///     Lean kernel via `ffi_timer_reprogram` (the AI1-C/M-26
///     single-owner rule).
///   * `INTID < MAX_SGI_INTID (16)` → record the per-core SGI counter,
///     then route through [`crate::gic::dispatch_sgi`] with genuine
///     source-CPU attribution.  Registered kernel-coordination SGIs
///     (SM0.H INTIDs: `.reschedule` 0 via
///     [`reschedule_sgi_handler`], `.tlbShootdownReq` 1, `.haltAll` 4)
///     run their handlers; unregistered INTIDs dispatch to the table's
///     no-op log arm.
///   * Other INTIDs → log a diagnostic with the per-core `[core N]`
///     prefix so the boot trace is unambiguously per-core attributable.
///
/// # Cost
///
/// Relative to a handler without per-core attribution: 1 × `mrs
/// tpidr_el1` (~3 cycles) + 1 × cache-hot load of `PerCpuData.core_id`
/// (~3 cycles) + 1 × atomic counter increment (~5 cycles uncontended on
/// Cortex-A76).  Subset counters (timer / SGI) add another atomic per
/// matched branch.  Total overhead < 20 cycles per IRQ.
///
/// # Panic discipline
///
/// AN8-C.3 (H-19): `#[deny(clippy::panic)]` (with the related
/// `clippy::unreachable` and `clippy::todo` panic-equivalents) so a
/// future edit that inserts a direct panic in the handler body fails
/// `cargo clippy`.  A panicking IRQ handler halts the kernel under
/// `panic = "abort"`, which is a structural-correctness hazard; the
/// handler signals recoverable conditions through return values, not
/// unwinding.
#[no_mangle]
#[deny(clippy::panic, clippy::unreachable, clippy::todo)]
pub extern "C" fn handle_irq_per_core(frame: &mut TrapFrame) {
    // WS-BP BP7.3: a preempted thread's whole context is the Lean kernel's to
    // save for the handler's duration.
    let _in_flight = InFlightFrame::publish(frame);
    // Read the calling core's id from TPIDR_EL1.  On hardware this is
    // pre-set by `boot.rs::rust_boot_main` (boot core) or
    // `boot.S::secondary_entry` (secondaries) before any kernel-mode
    // code runs.  On host the stub returns 0.
    //
    // WS-SM SM5.D.1: the calling core's id is now the per-core scheduler
    // dispatch key — the timer branch passes it to
    // `timer::per_core_timer_tick_isr(core_id)`, which drives the verified Lean
    // per-core timer tick for *this* core's scheduler slots.  (Pinned by
    // `build.rs::scan_trap_rs_handle_irq_per_core_intact`.)
    let core_id = crate::per_cpu::current_core_id_from_tpidr();

    crate::gic::dispatch_irq_with_iar(|intid, source_cpu| {
        // WS-SM SM1.I.4 audit-pass-1: record the IRQ dispatch only
        // on the non-spurious / non-out-of-range path (inside the
        // dispatcher's `Handled` closure).  This matches the
        // `record_irq_dispatch` docstring which states "called for
        // every non-spurious IRQ that reaches the dispatcher".  If
        // we incremented outside the closure (the pre-audit form),
        // spurious IAR reads (INTID >= 1020) and out-of-range INTIDs
        // (>= MAX_SUPPORTED_INTID) would inflate the per-core
        // counter — useful for hardware-level diagnostics but
        // misleading for SM5+ scheduler observability that wants to
        // count actual dispatched IRQs.
        let _ = crate::per_cpu_stats::record_irq_dispatch();
        if intid == crate::gic::TIMER_PPI_ID {
            // WS-SM SM5.D.1: the per-core CNTP timer ISR.  Records the
            // per-core tick, re-arms the per-core comparator, and drives the
            // verified Lean per-core scheduler timer tick
            // (`Kernel.timerTickOnCore` via `lean_per_core_timer_tick(core_id)`)
            // for *this* core's scheduler slots.  The per-core tick counter is
            // an SMP-localised diagnostic, independent of the primary-owned
            // global `TICK_COUNT` (advanced once per global tick by
            // `ffi_timer_reprogram`) — mirroring the Lean model where
            // `timerTickOnCore` reads but never advances `machine.timer`.
            //
            // The same AN8-C.4 re-entrancy guarantee applies: the IRQ
            // is acknowledged + EOI'd before this closure runs, and the
            // CPU-interface running-priority mask holds INTID 30 off
            // until PSTATE.I clears on exception return.
            crate::timer::per_core_timer_tick_isr(core_id);
        } else if intid < u32::from(crate::gic::MAX_SGI_INTID) {
            // SGI dispatch range (INTIDs 0..15).  WS-SM SM1.I.1: the
            // per-core SGI counter advances so test infrastructure
            // (SM1.H.5 round-trip; SM5+ scheduler observability) can
            // confirm SGIs arrived on the expected core.
            //
            // WS-SM SM7.B.3: the deferred handler dispatch is live —
            // `dispatch_irq_with_iar` preserves the full IAR, so the
            // SM1.F.5 table receives the genuine source CPU (bits
            // [12:10]) and the EOI carried the GIC-400 §4.4.5 SGI
            // CPUID field.  Unregistered INTIDs dispatch to the
            // table's no-op log arm (the pre-SM7.B observable
            // behaviour for SGI kinds without a handler).
            let _ = crate::per_cpu_stats::record_sgi_dispatch();
            #[allow(clippy::cast_possible_truncation)]
            crate::gic::dispatch_sgi(intid as u8, source_cpu);
        } else {
            // Non-timer, non-SGI INTID: log with per-core attribution.
            //
            // AG7 will additionally wire device interrupts (SPIs) to
            // notification signals via FFI; that's SM5+ work.
            //
            // Audit-pass-4: per-line atomicity via `kprintln_core!`
            // (see SGI branch above for rationale).
            crate::kprintln_core!("IRQ: unhandled INTID {}", intid);
        }
    });
    // WS-BP BP8.1: the dispatch's kernel-entry bracket is released here.
    report_first_idle_dispatch();
}

/// **WS-SM SM0.H / SM5.C.5**: the `.reschedule` SGI INTID, matching
/// `SeLe4n.Kernel.Concurrency.SgiKind.reschedule.toIntid` (pinned by
/// `SgiKind.reschedule_intid` on the Lean side).  Owned here next to
/// its handler, mirroring `gic::HALT_ALL_INTID` and
/// `shootdown::TLB_SHOOTDOWN_REQ_INTID`.
pub const RESCHEDULE_INTID: u8 = 0;

// Compile-time pins (WS-SM SM0.H): the INTID matches the SM0.H
// reservation (0 = `.reschedule`, mirrored by the Lean-side
// `SgiKind.reschedule_intid`) and sits inside the SGI range the
// SM1.F.5 handler table covers.  Const asserts, not tests, so drift
// fails the build before any test runs — the same discipline as the
// `TrapFrame` layout pins above.
const _: () = assert!(RESCHEDULE_INTID == 0);
const _: () = assert!(RESCHEDULE_INTID < crate::gic::MAX_SGI_INTID);

/// **WS-SM SM5.C.5**: the `.reschedule` SGI handler — the receiver seam
/// of the cross-core wake protocol.
///
/// When a remote wake enqueues a thread on this core's run queue, the
/// waker fires SGI INTID 0 (`SgiKind::reschedule`, SM0.H) at this core.
/// [`handle_irq_per_core`] routes the SGI here via the SM1.F.5 handler
/// table, and this handler drives the verified Lean reschedule
/// transition (`Kernel.handleRescheduleSgiOnCore` via the
/// `lean_per_core_reschedule` export): re-choose the highest-priority
/// budget-eligible runnable thread and switch to it only if it strictly
/// outranks the current thread.
///
/// The Lean call commits kernel state, so it takes the kernel-entry
/// lock ([`crate::kernel_entry::with_kernel_entry`]) exactly like the
/// timer-tick and syscall entries.  Non-reentrancy is safe for the same
/// reason as the tick: the SGI is acknowledged + EOI'd before the
/// handler runs, and `PSTATE.I` stays masked until exception return, so
/// this handler can never interrupt another kernel entry on its own
/// core.
///
/// Gated on `feature = "hw_target"`: on the host no kernel image is
/// linked, so the handler records the wake statistic only (the SGI
/// counter advanced in [`handle_irq_per_core`]'s dispatch branch) and
/// the reschedule itself is exercised by the Lean test suites against
/// the pure `perCoreRescheduleStep`.
///
/// The `_source_cpu` attribution is diagnostic only: the reschedule
/// decision depends on the receiving core's run queue, not on who
/// poked it.
fn reschedule_sgi_handler(_intid: u8, _source_cpu: u8) {
    let core_id = crate::per_cpu::current_core_id_from_tpidr();
    #[cfg(feature = "hw_target")]
    {
        // Lean-runtime readiness gate: a PE must never enter a Lean runtime
        // it has not initialized (the constraint shootdown.rs states in
        // prose, structural since `lean_ready`).  A not-yet-ready core
        // drops the reschedule — the woken thread stays enqueued on this
        // core's run queue, and the dispatch happens at this core's first
        // ready-side scheduling point instead (its bring-up reschedule or
        // its next tick); nothing is lost, only deferred.
        if crate::lean_ready::lean_ready(core_id as usize) {
            // SAFETY: `lean_per_core_reschedule` is the C-callable wrapper the
            // Lean compiler emits for `Kernel.perCoreRescheduleEntry`
            // (`@[export lean_per_core_reschedule]`).  It takes a `u64` core id
            // and returns its `BaseIO Unit` value, `lean_box(0)`; calling it is sound from EL1 IRQ context
            // after per-core hardware init has completed (the SGI can only be
            // taken once `enable_irq` ran on this core, which is after the
            // bring-up entry established this core's scheduler state) AND this
            // core's Lean runtime is initialized (the gate just checked).
            extern "C" {
                /// # Safety
                ///
                /// Sound from EL1 IRQ context on a core that has completed
                /// `enable_irq` (so the `.reschedule` SGI can be taken at all)
                /// and whose Lean runtime is initialised — `lean_ready` checked
                /// on *this* PE.  `core_id` must be the executing PE's own id.
                fn lean_per_core_reschedule(core_id: u64) -> crate::lean_runtime::LeanBaseIoUnit;
            }
            // SAFETY: `lean_per_core_reschedule` is the Lean-emitted
            // `extern "C"` entry declared just above; calling it is sound from
            // EL1 IRQ context under the two conditions stated there -- this
            // core's per-core hardware init has completed and its Lean runtime
            // is initialized -- and inside the kernel-entry bracket, which
            // serialises its `IO.Ref` commit against every other entry.
            let res = crate::kernel_entry::with_kernel_entry(core_id as usize, || unsafe {
                lean_per_core_reschedule(core_id)
            });
            // The export returns its `BaseIO Unit` value, `lean_box(0)`,
            // checked outside the bracket so a malformed one halts this PE
            // without holding the kernel-entry lock
            // (`lean_runtime::discharge_base_io`).
            // SAFETY: `res` is the value the export just returned; if it is
            // a heap object this caller owns its one reference.
            unsafe { crate::lean_runtime::discharge_base_io(res, "lean_per_core_reschedule") };
        }
    }
    #[cfg(not(feature = "hw_target"))]
    let _ = core_id;
}

/// **WS-SM SM5.C.5**: register the `.reschedule` handler.
///
/// # Safety
///
/// Must be called during single-core boot with IRQs disabled, before
/// `bring_up_secondaries` — the [`crate::gic::register_sgi_handler`]
/// write-once contract, same as the shootdown and haltAll handlers.
pub unsafe fn register_reschedule_sgi_handler() {
    // SAFETY: this function's own `# Safety` contract -- boot, single-core,
    // IRQs disabled, before `bring_up_secondaries` -- is exactly
    // `register_sgi_handler`'s write-once precondition.
    unsafe {
        crate::gic::register_sgi_handler(RESCHEDULE_INTID, reschedule_sgi_handler);
    }
}

/// SError handler — called from assembly on system error exceptions.
///
/// SErrors are typically unrecoverable hardware errors (DRAM parity error,
/// system-level interconnect fault, etc.). Log and halt permanently.
///
/// AK5-K (R-HAL-M12 / MEDIUM): Return type is `-> !` to communicate the
/// never-return guarantee to the compiler. AK10 completes the remediation:
/// `trap.S::__el0_serror_entry` / `__el1_serror_entry` now branch to `b .`
/// after `bl handle_serror` (instead of the previously-dead `restore_context`
/// fall-through) so the core halts in place if divergence is ever violated.
///
/// **The v0.36.2 audit**: SError is unmasked on every PE once its vectors
/// are installed (`interrupts::enable_serror`), so this handler is reachable,
/// and it reports through the console's **unlocked** writer: the interrupted
/// context on this PE may hold the console lock — a store to an MMIO address
/// no device answers is the commonest SError source, and that store is a
/// console write as often as not — and taking the lock here would spin on
/// it forever, silently.  The syndrome and the return address are printed
/// because they are what a wrong board constant leaves behind.
#[no_mangle]
pub extern "C" fn handle_serror(frame: &mut TrapFrame) -> ! {
    use core::fmt::Write;
    let (esr, elr) = (frame.esr_el1, frame.elr_el1);
    crate::uart::with_boot_uart_unlocked_for_fatal(|uart| {
        let _ = writeln!(
            uart,
            "FATAL: SError exception (ESR_EL1 = {esr:#x}, ELR_EL1 = {elr:#x})"
        );
    });
    loop {
        crate::cpu::wfe();
    }
}

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests {
    use super::*;

    /// A fault stack top for the restore tests (PR #904).
    const FAULT_STACK_TOP: u64 = 0x7F_0000;

    /// An idle resume at `pc` for the restore tests.
    fn idle(pc: u64) -> IdleResume {
        IdleResume {
            pc,
            sp_el0: FAULT_STACK_TOP,
        }
    }

    /// WS-BP BP7.3: the context words are the frame's fields in order, and
    /// the trap's own syndrome registers are not part of a thread's context.
    #[test]
    fn a_threads_context_is_the_frames_first_thirty_five_words() {
        let mut frame = zero_frame();
        for (i, r) in frame.gprs.iter_mut().enumerate() {
            *r = 0x100 + i as u64;
        }
        frame.sp_el0 = 0xAAAA;
        frame.elr_el1 = 0xBBBB;
        frame.spsr_el1 = 0x2000_0000;
        frame.esr_el1 = 0xDEAD;
        frame.far_el1 = 0xBEEF;
        frame.tpidr_el0 = 0x7777_0000;
        let words = trap_frame_context(&frame);
        for (i, word) in words.iter().take(31).enumerate() {
            assert_eq!(*word, 0x100 + i as u64);
        }
        assert_eq!(words[31], 0xAAAA);
        assert_eq!(words[32], 0xBBBB);
        assert_eq!(words[33], 0x2000_0000);
        assert_eq!(words[34], 0x7777_0000);
        assert!(
            !words.contains(&0xDEAD) && !words.contains(&0xBEEF),
            "the syndrome words are the trap's, not the thread's"
        );
    }

    /// WS-BP BP7.3: a frame is readable only while its handler's guard lives,
    /// a nested handler restores the frame it displaced, and each core reads
    /// its own slot.
    #[test]
    fn an_in_flight_frame_is_readable_only_while_published() {
        let slots: InFlightSlots = [const { AtomicPtr::new(core::ptr::null_mut()) };
            crate::svc_dispatch::RETURN_FRAME_CORES];
        let mut outer = zero_frame();
        outer.gprs[6] = 6;
        let mut inner = zero_frame();
        inner.gprs[6] = 66;
        assert_eq!(in_flight_context_in(&slots, 1).map(|c| c[6]), None);
        {
            let _o = InFlightFrame::publish_in(&slots, 1, &mut outer);
            assert_eq!(in_flight_context_in(&slots, 1).map(|c| c[6]), Some(6));
            assert_eq!(
                in_flight_context_in(&slots, 0).map(|c| c[6]),
                None,
                "another core's slot"
            );
            {
                let _i = InFlightFrame::publish_in(&slots, 1, &mut inner);
                assert_eq!(in_flight_context_in(&slots, 1).map(|c| c[6]), Some(66));
            }
            assert_eq!(
                in_flight_context_in(&slots, 1).map(|c| c[6]),
                Some(6),
                "the outer frame is restored"
            );
        }
        assert_eq!(
            in_flight_context_in(&slots, 1).map(|c| c[6]),
            None,
            "withdrawn when the handler returns"
        );
        assert_eq!(
            in_flight_context_in(&slots, 99).map(|c| c[6]),
            None,
            "a core past the slots"
        );
    }

    /// A context whose word `i` is `base + i`.
    fn staged_context(base: u64) -> TrapContextWords {
        core::array::from_fn(|i| base + i as u64)
    }

    fn fresh_restore() -> (
        InFlightSlots,
        RestoreStaging,
        RestoredFlags,
        IdleHandoffFlags,
    ) {
        (
            [const { AtomicPtr::new(core::ptr::null_mut()) };
                crate::svc_dispatch::RETURN_FRAME_CORES],
            [const { [const { AtomicU64::new(0) }; TRAP_FRAME_CONTEXT_WORDS as usize] };
                crate::svc_dispatch::RETURN_FRAME_CORES],
            [const { AtomicBool::new(false) }; crate::svc_dispatch::RETURN_FRAME_CORES],
            [const { AtomicBool::new(false) }; crate::svc_dispatch::RETURN_FRAME_CORES],
        )
    }

    /// WS-BP BP7.4: a user resume replaces every context word of the frame
    /// the handler will `eret` through, sanitises `SPSR_EL1` to EL0t, leaves
    /// the trap's own syndrome words alone, and sets the restored flag once.
    #[test]
    fn a_user_restore_replaces_the_in_flight_context() {
        let (slots, staging, restored, handoff) = fresh_restore();
        let mut context = staged_context(1000);
        // A hostile pstate: EL1h with DAIF masked and NZCV set.
        context[33] = 0xF000_03C5;
        restore_stage_context_in(&staging, 2, &context).unwrap();
        let mut frame = zero_frame();
        frame.esr_el1 = 0x5600_0000;
        frame.far_el1 = 0xDEAD;
        // v0.36.30: the thread pointer the previous thread on this core wrote.
        frame.tpidr_el0 = 0x5EC2_E700;
        {
            let _g = InFlightFrame::publish_in(&slots, 2, &mut frame);
            assert_eq!(
                restore_commit_in(
                    &slots,
                    &staging,
                    &restored,
                    &handoff,
                    2,
                    RESTORE_KIND_USER,
                    idle(0x4242),
                ),
                Ok(true)
            );
        }
        for i in 0..31 {
            assert_eq!(frame.gprs[i], 1000 + i as u64);
        }
        assert_eq!(frame.sp_el0, 1031);
        assert_eq!(frame.elr_el1, 1032);
        assert_eq!(
            frame.spsr_el1, 0xF000_0000,
            "mode and DAIF must not survive"
        );
        assert_eq!(frame.esr_el1, 0x5600_0000);
        assert_eq!(frame.far_el1, 0xDEAD);
        assert_eq!(
            frame.tpidr_el0, 1034,
            "the incoming thread resumes with its own thread pointer, not the outgoing one's"
        );
        assert!(take_restored_in(&restored, 2));
        assert!(!take_restored_in(&restored, 2), "the flag is taken once");
        assert!(
            !take_restored_in(&restored, 1),
            "another core's flag is untouched"
        );
    }

    /// WS-BP BP7.9: the FP-live user resume (kind 2) installs the staged
    /// context exactly as a plain user resume does — the kinds differ only in
    /// the FP/SIMD trap the hardware commit sets, never in the frame.
    #[test]
    fn an_fp_live_restore_installs_the_same_frame_as_a_user_restore() {
        let run = |kind: u32| {
            let (slots, staging, restored, handoff) = fresh_restore();
            restore_stage_context_in(&staging, 0, &staged_context(500)).unwrap();
            let mut frame = zero_frame();
            {
                let _g = InFlightFrame::publish_in(&slots, 0, &mut frame);
                assert_eq!(
                    restore_commit_in(&slots, &staging, &restored, &handoff, 0, kind, idle(0),),
                    Ok(true)
                );
            }
            (
                frame.gprs,
                frame.sp_el0,
                frame.elr_el1,
                frame.spsr_el1,
                frame.tpidr_el0,
            )
        };
        assert_eq!(run(RESTORE_KIND_USER_FP_LIVE), run(RESTORE_KIND_USER));
    }

    /// WS-BP BP7.4: an idle resume aims the frame at the idle loop at EL1h
    /// with interrupts unmasked and carries no register of the thread it
    /// replaced.
    #[test]
    fn an_idle_restore_resumes_the_idle_loop() {
        let (slots, staging, restored, handoff) = fresh_restore();
        let mut frame = zero_frame();
        frame.gprs = [7; 31];
        frame.sp_el0 = 9;
        frame.elr_el1 = 0x40_0000;
        frame.tpidr_el0 = 0x5EC2_E700;
        {
            let _g = InFlightFrame::publish_in(&slots, 0, &mut frame);
            assert_eq!(
                restore_commit_in(
                    &slots,
                    &staging,
                    &restored,
                    &handoff,
                    0,
                    RESTORE_KIND_IDLE,
                    idle(0x8_1234),
                ),
                Ok(true)
            );
        }
        assert_eq!(frame.gprs, [0; 31]);
        // PR #904: the idle loop runs at EL1 with SP_EL0 at the fault stack.
        assert_eq!(frame.sp_el0, FAULT_STACK_TOP);
        assert_eq!(frame.elr_el1, 0x8_1234);
        assert_eq!(frame.spsr_el1, IDLE_SPSR);
        assert_eq!(frame.tpidr_el0, 0, "an idle core keeps no thread's pointer");
        assert!(take_restored_in(&restored, 0));
    }

    /// WS-BP BP7.4: with no frame published there is nothing to resume into,
    /// so the commit is a no-op that sets no flag; an unknown kind and a core
    /// outside the slots are refused.
    #[test]
    fn a_restore_without_a_frame_is_a_no_op_and_bad_operands_are_refused() {
        let (slots, staging, restored, handoff) = fresh_restore();
        assert_eq!(
            restore_commit_in(
                &slots,
                &staging,
                &restored,
                &handoff,
                1,
                RESTORE_KIND_USER,
                idle(0),
            ),
            Ok(false)
        );
        assert!(!take_restored_in(&restored, 1));
        // WS-BP BP7.9: kind 2 is the FP-live user resume, so it is a kind the
        // commit knows; kind 3 is not.
        assert_eq!(
            restore_commit_in(
                &slots,
                &staging,
                &restored,
                &handoff,
                1,
                RESTORE_KIND_USER_FP_LIVE,
                idle(0),
            ),
            Ok(false)
        );
        assert_eq!(
            restore_commit_in(&slots, &staging, &restored, &handoff, 1, 3, idle(0),),
            Err(RestoreRefusal::UnknownKind)
        );
        assert_eq!(
            restore_stage_context_in(&staging, 99, &staged_context(0)),
            Err(RestoreRefusal::CoreOutOfRange)
        );
        assert_eq!(
            restore_commit_in(
                &slots,
                &staging,
                &restored,
                &handoff,
                99,
                RESTORE_KIND_IDLE,
                idle(0),
            ),
            Err(RestoreRefusal::CoreOutOfRange)
        );
    }

    /// WS-BP BP8.1: a frame taken at EL1 before its core handed itself to the
    /// idle wait is the kernel's own bring-up, so neither a user nor an idle
    /// restore replaces it and no flag is set; once the core hands off, the
    /// same restore replaces it.  An EL0-origin frame is replaced either way
    /// (the tests above run with no core handed off), and handing off one core
    /// hands off no other.
    #[test]
    fn a_bring_up_frame_is_replaced_only_after_its_core_hands_off() {
        let el1h = |frame: &mut TrapFrame| {
            frame.elr_el1 = 0x4008_0000;
            frame.spsr_el1 = 0x3C5;
            frame.gprs = [3; 31];
        };
        for kind in [
            RESTORE_KIND_USER,
            RESTORE_KIND_USER_FP_LIVE,
            RESTORE_KIND_IDLE,
        ] {
            let (slots, staging, restored, handoff) = fresh_restore();
            restore_stage_context_in(&staging, 1, &staged_context(700)).unwrap();
            let mut frame = zero_frame();
            el1h(&mut frame);
            {
                let _g = InFlightFrame::publish_in(&slots, 1, &mut frame);
                assert_eq!(
                    restore_commit_in(
                        &slots,
                        &staging,
                        &restored,
                        &handoff,
                        1,
                        kind,
                        idle(0x8_1234),
                    ),
                    Ok(false),
                    "a bring-up frame is resumed as it stands"
                );
            }
            assert_eq!(frame.elr_el1, 0x4008_0000);
            assert_eq!(frame.spsr_el1, 0x3C5);
            assert_eq!(frame.gprs, [3; 31]);
            assert!(!take_restored_in(&restored, 1));

            hand_off_to_idle_in(&handoff, 2);
            {
                let _g = InFlightFrame::publish_in(&slots, 1, &mut frame);
                assert_eq!(
                    restore_commit_in(
                        &slots,
                        &staging,
                        &restored,
                        &handoff,
                        1,
                        kind,
                        idle(0x8_1234),
                    ),
                    Ok(false),
                    "another core's handoff is not this core's"
                );
            }
            assert_eq!(frame.elr_el1, 0x4008_0000);

            hand_off_to_idle_in(&handoff, 1);
            {
                let _g = InFlightFrame::publish_in(&slots, 1, &mut frame);
                assert_eq!(
                    restore_commit_in(
                        &slots,
                        &staging,
                        &restored,
                        &handoff,
                        1,
                        kind,
                        idle(0x8_1234),
                    ),
                    Ok(true),
                    "after the handoff an EL1 frame is the idle loop's"
                );
            }
            let expected_pc = if kind == RESTORE_KIND_IDLE {
                0x8_1234
            } else {
                700 + 32
            };
            assert_eq!(frame.elr_el1, expected_pc);
            assert!(take_restored_in(&restored, 1));
        }
        // A core outside the flag array is refused, not read past.
        let (slots, staging, restored, handoff) = fresh_restore();
        hand_off_to_idle_in(&handoff, 99);
        assert_eq!(
            restore_commit_in(
                &slots,
                &staging,
                &restored,
                &handoff,
                99,
                RESTORE_KIND_IDLE,
                idle(0),
            ),
            Err(RestoreRefusal::CoreOutOfRange)
        );
    }

    /// WS-BP BP8.1: the first-idle report fires exactly once per core, only
    /// after an idle resume was noted, and one core's note is not another's.
    #[test]
    fn the_first_idle_dispatch_is_reported_once_per_core() {
        let flags: FirstIdleFlags =
            [const { AtomicU8::new(0) }; crate::svc_dispatch::RETURN_FRAME_CORES];
        assert!(!take_first_idle_report_in(&flags, 1), "nothing noted yet");
        note_idle_dispatch_in(&flags, 1);
        assert!(!take_first_idle_report_in(&flags, 2), "another core's note");
        assert!(take_first_idle_report_in(&flags, 1));
        assert!(!take_first_idle_report_in(&flags, 1), "reported once");
        note_idle_dispatch_in(&flags, 1);
        assert!(
            !take_first_idle_report_in(&flags, 1),
            "a later idle resume is not the first"
        );
        note_idle_dispatch_in(&flags, 99);
        assert!(!take_first_idle_report_in(&flags, 99));
    }

    /// WS-BP BP7.4: sanitisation keeps exactly the condition flags.
    #[test]
    fn user_spsr_sanitisation_keeps_only_nzcv() {
        assert_eq!(sanitise_user_spsr(0), 0);
        assert_eq!(sanitise_user_spsr(u64::MAX), 0xF000_0000);
        assert_eq!(sanitise_user_spsr(0x3C5), 0);
    }

    /// AK5-F test helper: construct a zero-initialized TrapFrame.
    fn zero_frame() -> TrapFrame {
        TrapFrame {
            gprs: [0; 31],
            sp_el0: 0,
            elr_el1: 0,
            spsr_el1: 0,
            esr_el1: 0,
            far_el1: 0,
            tpidr_el0: 0,
            reserved: 0,
        }
    }

    // ------------------------------------------------------------------------
    // WS-SM SM1.I (audit-pass-3) — PER_CPU_STATS observation mutex.
    //
    // The SM1.I.4 trap-handler tests read+write the global
    // `crate::per_cpu_stats::PER_CPU_STATS` array via
    // `handle_synchronous_exception` and `*_count_for(0)` accessors.
    //
    // Most of these tests assert `after > before` (the per-EC-branch
    // counter advances by AT LEAST 1).  That property tolerates
    // concurrent parallel-test writers — even if another test also
    // writes to the same counter, `after > before` still holds.
    //
    // But ONE test
    // (`per_core_counters_track_distinct_exception_branches`)
    // asserts `vm_after == vm_before` (the SVC branch does NOT touch
    // `vmfault_count`).  Under cargo's parallel test execution, a
    // concurrent test that calls `handle_synchronous_exception` with
    // a DABT or IABT ESR would increment `vmfault_count` between our
    // two reads, producing a transient failure even though the SVC
    // branch correctly did not touch the counter.
    //
    // Audit-pass-3 (per the external audit's H2 finding): serialise
    // every SM1.I.4 test that observes `PER_CPU_STATS[0]` via this
    // private mutex.  The serialisation is invisible to other tests
    // and adds no runtime cost in production.
    //
    // Audit-pass-4 (poisoning defence): every test that acquires this
    // mutex uses `.lock().unwrap_or_else(|e| e.into_inner())` instead
    // of `.lock().unwrap()`.  A failed `assert_eq!` / `assert!` inside
    // a holder would otherwise poison the mutex and cascade-fail every
    // subsequent SM1.I.4 test with `PoisonError`, burying the
    // diagnostic of the *original* failure.  The recovery pattern
    // bypasses poisoning so subsequent tests run normally and surface
    // their own diagnostics (the original failure is already reported
    // by cargo's test harness).
    static PER_CORE_STATS_OBSERVATION_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

    /// PR #887 review round 2 (CI flake made structural): **every** host test
    /// that drives `handle_synchronous_exception` records into the same
    /// process-global counters — `current_core_id_from_tpidr()` is core 0 on
    /// every test thread — so a test that only checks a return frame can
    /// still land a `record_vm_fault` between the two reads of an
    /// observation test's snapshot pair.  The observation tests hold the
    /// mutex across their pair and call the handler directly; every other
    /// driver goes through here, so no recorder runs inside a pair.
    fn drive_sync(frame: &mut TrapFrame) {
        let _guard = PER_CORE_STATS_OBSERVATION_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        handle_synchronous_exception(frame);
    }

    #[test]
    fn trap_frame_size_is_304_bytes() {
        // AK5-F grew TrapFrame 272 -> 288 (ESR_EL1 + FAR_EL1); v0.36.30 to 304
        // (TPIDR_EL0 + one padding word).
        assert_eq!(TRAP_FRAME_SIZE, 304);
        assert_eq!(core::mem::size_of::<TrapFrame>(), 304);
    }

    #[test]
    fn trap_frame_alignment_is_16() {
        // AK5-F: TrapFrame is 16-byte aligned for AArch64 SP discipline.
        assert_eq!(core::mem::align_of::<TrapFrame>(), 16);
    }

    #[test]
    fn trap_frame_field_offsets() {
        // Verify field offsets match assembly save_context/restore_context macros.
        assert_eq!(core::mem::offset_of!(TrapFrame, gprs), 0);
        assert_eq!(core::mem::offset_of!(TrapFrame, sp_el0), 248);
        assert_eq!(core::mem::offset_of!(TrapFrame, elr_el1), 256);
        assert_eq!(core::mem::offset_of!(TrapFrame, spsr_el1), 264);
        // AK5-F: ESR + FAR snapshot offsets.
        assert_eq!(core::mem::offset_of!(TrapFrame, esr_el1), 272);
        assert_eq!(core::mem::offset_of!(TrapFrame, far_el1), 280);
        assert_eq!(core::mem::offset_of!(TrapFrame, tpidr_el0), 288);
    }

    #[test]
    fn trap_frame_gpr_accessors() {
        let mut frame = zero_frame();

        // Set ABI registers
        frame.gprs[0] = 0xCAFE;
        frame.gprs[1] = 0xBEEF;
        frame.gprs[2] = 0x1111;
        frame.gprs[3] = 0x2222;
        frame.gprs[4] = 0x3333;
        frame.gprs[5] = 0x4444;
        frame.gprs[7] = 0x7777;

        assert_eq!(frame.x0(), 0xCAFE);
        assert_eq!(frame.x1(), 0xBEEF);
        assert_eq!(frame.x2(), 0x1111);
        assert_eq!(frame.x3(), 0x2222);
        assert_eq!(frame.x4(), 0x3333);
        assert_eq!(frame.x5(), 0x4444);
        assert_eq!(frame.x7(), 0x7777);
    }

    #[test]
    fn trap_frame_setters() {
        let mut frame = zero_frame();
        frame.set_x0(42);
        frame.set_x1(99);
        assert_eq!(frame.gprs[0], 42);
        assert_eq!(frame.gprs[1], 99);
    }

    // ========================================================================
    // AK5-F: ESR/FAR snapshot semantics
    // ========================================================================

    #[test]
    fn trap_frame_esr_far_roundtrip() {
        // T01 (AK5-F.6): Synthesize a frame with known ESR + FAR; assert the
        // handler-side accessors read them back.
        let mut frame = zero_frame();
        frame.esr_el1 = 0xDEAD_BEEF;
        frame.far_el1 = 0x1234_5678;
        assert_eq!(frame.esr_el1, 0xDEAD_BEEF);
        assert_eq!(frame.far_el1, 0x1234_5678);
    }

    // **WS-RR RR7.37 (register finding 84, swept)**: `handle_sync_reads_esr_from_frame`
    // and `per_core_counters_track_distinct_exception_branches` moved to
    // `tests/readiness_gate_after_mark.rs`.  Both drive an `SVC` through
    // `handle_synchronous_exception`, whose arm halts the core before doing
    // anything when the executing PE is not marked ready — and on the host lane
    // `fatal_halt` panics inside an `extern "C"` handler, which **aborts the
    // whole test binary** rather than failing one test.  The readiness bit in
    // this binary is owned by
    // `timer::tests::per_core_timer_tick_isr_never_advances_global_tick_count`,
    // which asserts it is unset when it starts and sets it partway through, so
    // these tests passed only when cargo happened to schedule that one first.
    // CLAUDE.md's rule is that no test in the library binary may assume core 0's
    // readiness in either direction; these two did, and losing the race took
    // every other test in the binary down with them.

    #[test]
    fn handle_sync_data_abort_via_frame() {
        // AK5-F.3: DABT from lower EL is classified from frame ESR, not
        // from live register — proves the handler is not reading live mrs.
        //
        // WS-RR RR4.22: the abort arm now publishes a full **status-label**
        // frame (ABI v3) instead of the retired raw discriminant in `x0`.
        // On the host lane `deliver_fault` takes its fallback: `x0 = 0`,
        // `x1` a `MessageInfo` whose label is `ERROR_LABEL_BASE + VM_FAULT`,
        // and `x2`-`x5` cleared.  Under the retired convention this asserted
        // `x0 == 44` and left `x1` untouched — the fail-open shape a resumed
        // thread could decode as a success.  PR #887 review round 3: this
        // frame is the *host lane's* observable only; on hardware a not-ready
        // core halts instead (`abort_before_lean_ready_halts`), because an
        // abort's frame would be `eret`ed back into the abort.
        let mut frame = zero_frame();
        frame.esr_el1 = ec::DABT_LOWER << 26;
        frame.far_el1 = 0xFFFF_0000_DEAD_0000;
        drive_sync(&mut frame);
        assert_eq!(frame.x0(), 0);
        assert_eq!(
            frame.x1(),
            (crate::svc_dispatch::ERROR_LABEL_BASE + u64::from(error_code::VM_FAULT)) << 9
        );
        assert_eq!([frame.x2(), frame.x3(), frame.x4(), frame.x5()], [0; 4]);
        // FAR is preserved in the frame (not mutated by the handler).
        assert_eq!(frame.far_el1, 0xFFFF_0000_DEAD_0000);
    }

    #[test]
    fn nested_exception_does_not_clobber_frame_esr() {
        // T04 (AK5-F.6): An outer handler reads its frame's ESR; simulating a
        // subsequent trap (by constructing a second frame) does not mutate
        // the first frame's snapshot.
        let mut outer = zero_frame();
        outer.esr_el1 = ec::DABT_LOWER << 26;
        outer.far_el1 = 0xAAAA;

        // Simulate a subsequent trap: a second frame with different ESR/FAR.
        // PR #887 review: it is a *lower*-EL instruction abort, because a
        // current-EL one is a kernel-origin exception and halts the core
        // before any frame is read (`halt_if_kernel_origin`) — the frame
        // isolation this test pins is a property of the delivered path.
        let mut inner = zero_frame();
        inner.esr_el1 = ec::IABT_LOWER << 26;
        inner.far_el1 = 0xBBBB;
        drive_sync(&mut inner);

        // The outer frame remains untouched.
        assert_eq!(outer.esr_el1, ec::DABT_LOWER << 26);
        assert_eq!(outer.far_el1, 0xAAAA);
    }

    /// **WS-RR RR4.25**: the host lane's classification mirror agrees with the
    /// Lean model's `classifySynchronousException` on **every** EC value.
    ///
    /// Enumerated rather than spot-checked, and stated as an explicit expected
    /// table rather than by re-deriving it from `esr_ec`: a mutation that keeps
    /// every token but *changes the mapping* — swapping the abort arms, folding
    /// `SP_ALIGN` into the unknown arm, moving `SVC` — is exactly the drift
    /// that would route a fault to the wrong handler, and only a table can
    /// catch it.  On hardware the mirror classifies only before a core is
    /// ready (`classify_synchronous_exception` is the Lean call once it is), so
    /// this pins both the host lane and the pre-readiness path to the answers
    /// the Lean classifier gives.
    #[test]
    fn sync_class_mirrors_lean_ec_table() {
        for raw_ec in 0u64..64 {
            let esr = raw_ec << 26;
            let expected = match raw_ec {
                0x15 => sync_class::SVC,
                0x24 => sync_class::DATA_ABORT,
                0x20 => sync_class::INSTR_ABORT,
                // PR #887 review: current-EL aborts are the kernel's own.
                0x25 | 0x21 => sync_class::KERNEL_ABORT,
                0x22 => sync_class::PC_ALIGNMENT,
                0x26 => sync_class::SP_ALIGNMENT,
                // WS-BP BP7.9: the lazy FP/SIMD switch's trap.
                0x07 => sync_class::FP_ACCESS,
                _ => sync_class::UNKNOWN_REASON,
            };
            assert_eq!(
                classify_synchronous_exception_mirror(esr),
                expected,
                "EC 0x{raw_ec:02x} classified differently from the Lean model"
            );
        }
    }

    /// **WS-RR RR4.25**: the five class tags are the Lean
    /// `syncExceptionClassTag` values, pinned as literals.
    #[test]
    fn sync_class_tags_match_lean() {
        assert_eq!(sync_class::SVC, 0);
        assert_eq!(sync_class::DATA_ABORT, 1);
        assert_eq!(sync_class::INSTR_ABORT, 2);
        assert_eq!(sync_class::PC_ALIGNMENT, 3);
        assert_eq!(sync_class::SP_ALIGNMENT, 4);
        assert_eq!(sync_class::UNKNOWN_REASON, 5);
        assert_eq!(sync_class::FP_ACCESS, 7);
        assert_eq!(sync_class::KERNEL_ABORT, 6);
    }

    /// **PR #887 review**: the origin predicate reads `SPSR_EL1.M[3:2]`.
    #[test]
    fn exception_origin_reads_spsr_el() {
        assert!(exception_taken_from_el0(0)); // EL0t
        assert!(exception_taken_from_el0(0x3C0)); // EL0t with DAIF set
        assert!(exception_taken_from_el0(0x10)); // AArch32 EL0 (M[4] set)
        assert!(!exception_taken_from_el0(0x3C4)); // EL1t
        assert!(!exception_taken_from_el0(0x3C5)); // EL1h
        assert!(!exception_taken_from_el0(0x5)); // EL1h, DAIF clear
    }

    /// **PR #887 review**: a synchronous exception taken from EL1 — a kernel
    /// page fault — halts instead of being classified and delivered to the
    /// current user thread.  On the host lane `fatal_halt` panics, which is
    /// the observable; the gate is exercised directly because a panic cannot
    /// unwind across the `extern "C"` handler frame.
    #[test]
    #[should_panic]
    fn kernel_origin_gate_halts_on_el1() {
        let mut frame = zero_frame();
        frame.esr_el1 = ec::DABT_LOWER << 26; // the syndrome alone looks like a user fault…
        frame.spsr_el1 = 0x3C5; // …but the PE was at EL1h when it was taken.
        halt_if_kernel_origin(&frame, frame.esr_el1);
    }

    /// **PR #887 review**: …and passes an EL0-origin exception through.
    #[test]
    fn kernel_origin_gate_passes_el0() {
        let mut frame = zero_frame();
        frame.esr_el1 = ec::DABT_LOWER << 26;
        frame.spsr_el1 = 0x3C0; // EL0t, DAIF set
        halt_if_kernel_origin(&frame, frame.esr_el1);
    }

    /// **PR #887 review round 3**: an EL0 abort on a core whose Lean runtime
    /// is not up halts.  A status frame cannot fail-close an abort — `eret`
    /// through the unchanged `ELR_EL1` re-executes the faulting instruction —
    /// so the not-ready path diverges like the delivered arm; on the host
    /// lane `fatal_halt` panics, which is the observable.
    #[test]
    #[should_panic]
    fn abort_before_lean_ready_halts() {
        halt_abort_before_lean_ready(0, ec::DABT_LOWER << 26, 0x4_0000);
    }

    /// **PR #887 review round 5**: a delivered syscall fault (outcome tag 2)
    /// with no context restored halts the core — returning would `eret` the caller
    /// past the `SVC` the model has it restart at.  On the host lane
    /// `fatal_halt` panics, which is the observable.
    #[test]
    #[should_panic]
    fn delivered_syscall_fault_halts() {
        let mut frame = zero_frame();
        frame.esr_el1 = ec::SVC_AARCH64 << 26;
        frame.gprs[7] = 2;
        halt_after_delivered_syscall_fault(&frame);
    }

    /// **PR #887 review**: a current-EL abort syndrome halts on its own class,
    /// independently of the origin gate.
    #[test]
    #[should_panic]
    fn current_el_abort_halts() {
        let mut frame = zero_frame();
        frame.esr_el1 = ec::DABT_CURRENT << 26;
        halt_on_kernel_abort(&frame, frame.esr_el1);
    }

    /// **PR #887 review**: …and the instruction-abort half of the class does
    /// too — the syndrome the kernel raises by branching to an unmapped or
    /// non-executable address, which the data-abort case above cannot stand
    /// in for.
    #[test]
    #[should_panic]
    fn current_el_instruction_abort_halts() {
        let mut frame = zero_frame();
        frame.esr_el1 = ec::IABT_CURRENT << 26;
        halt_on_kernel_abort(&frame, frame.esr_el1);
    }

    // PR #889 review: the SVC arm's not-ready behaviour — every `SVC` halts,
    // an unknown id and an oversized `x7` included, *before* the narrowing —
    // is not observable from a host test: `handle_synchronous_exception` is
    // `extern "C"`, and a panic (the host lane's `fatal_halt`) cannot unwind
    // through it, so the process aborts instead of the test catching it.  The
    // ordering is pinned structurally by `build.rs`'s
    // `svc_arm_readiness_gate_status` (the gate is a top-level statement of
    // the arm, ahead of the `dispatched` binding, on the executing core,
    // ending in the diverging halt); the behaviour is pinned at the plain-Rust
    // seam `dispatch_svc` in `tests/readiness_gate_before_mark.rs`.  The
    // frames the unknown-syscall paths publish on a *ready* core moved to
    // `tests/readiness_gate_after_mark.rs`
    // (`unknown_syscall_id_on_ready_core_publishes_status_frame`,
    // `wide_syscall_number_on_ready_core_is_unknown_syscall`).

    /// **WS-RR RR4.25**: the low ESR bits (IL, ISS) do not change the class —
    /// the classification reads EC alone, exactly as the Lean
    /// `classifySynchronousException_depends_only_on_esr` companion states of
    /// the other three syndrome words.
    #[test]
    fn sync_class_ignores_iss_bits() {
        let base = ec::DABT_LOWER << 26;
        assert_eq!(
            classify_synchronous_exception(base),
            classify_synchronous_exception(base | 0x01FF_FFFF)
        );
    }

    /// **WS-RR RR4.24**: `ELR_EL1` is writable — the mutator the trap frame
    /// lacked, and without which a fault reply could only ever return the
    /// thread to the instruction that faulted.
    #[test]
    fn trap_frame_elr_mutator() {
        let mut frame = zero_frame();
        frame.elr_el1 = 0x1000;
        frame.set_elr_el1(0xDEAD_BEEF_0000);
        assert_eq!(frame.elr_el1, 0xDEAD_BEEF_0000);
    }

    /// **WS-RR RR4.24**: and so is the saved user stack pointer.
    #[test]
    fn trap_frame_sp_el0_mutator() {
        let mut frame = zero_frame();
        frame.set_sp_el0(0x7FFF_0000);
        assert_eq!(frame.sp_el0, 0x7FFF_0000);
    }

    /// **WS-RR RR4.16/RR4.24**: a fault-restart frame installs `x0`-`x7`, the
    /// link register, the restart PC and the stack pointer — and **nothing
    /// else**.  `SPSR_EL1` in particular survives: this model keeps PSTATE out
    /// of a fault handler's reach.
    #[test]
    fn trap_frame_fault_restart_frame() {
        let mut frame = zero_frame();
        frame.spsr_el1 = 0x3C5;
        frame.gprs[8] = 0xC0FFEE;
        frame.gprs[29] = 0xFEEDFACE;
        // [x0..x7, lr, pc, sp]
        frame.set_fault_restart_frame([10, 11, 12, 13, 14, 15, 16, 17, 0x30, 0x9000, 0x8000]);
        assert_eq!(
            [
                frame.x0(),
                frame.x1(),
                frame.x2(),
                frame.x3(),
                frame.x4(),
                frame.x5(),
                frame.gprs[6],
                frame.gprs[7]
            ],
            [10, 11, 12, 13, 14, 15, 16, 17]
        );
        assert_eq!(frame.gprs[30], 0x30);
        assert_eq!(frame.elr_el1, 0x9000);
        assert_eq!(frame.sp_el0, 0x8000);
        // Untouched: PSTATE, and every register outside the restart window.
        assert_eq!(frame.spsr_el1, 0x3C5);
        assert_eq!(frame.gprs[8], 0xC0FFEE);
        assert_eq!(frame.gprs[29], 0xFEEDFACE);
    }

    /// **WS-RR RR4.22**: every exception arm that is not `SVC` publishes a
    /// **status-label** frame (ABI v3) — `x0 = 0`, the error in the top of
    /// `x1`'s label range, `x2`-`x5` cleared — and never the retired raw
    /// discriminant in `x0` with `x1` left as the faulting thread found it.
    ///
    /// The `x1` assertion is the load-bearing half: the pre-RR4 arms wrote
    /// only `x0`, so a resumed thread whose `x1` carried a label below 512
    /// decoded the fault as a *successful syscall* with a forged badge.
    #[test]
    fn exception_arms_publish_offset_label_frames() {
        let cases: [(u64, u32); 5] = [
            (ec::DABT_LOWER, error_code::VM_FAULT),
            (ec::IABT_LOWER, error_code::VM_FAULT),
            (ec::PC_ALIGN, error_code::USER_EXCEPTION),
            (ec::SP_ALIGN, error_code::USER_EXCEPTION),
            (0x3F, error_code::USER_EXCEPTION),
        ];
        for (raw_ec, disc) in cases {
            let mut frame = zero_frame();
            frame.esr_el1 = raw_ec << 26;
            // Seed `x1` with a label a decoder would read as success, so a
            // regression that stops writing `x1` fails here rather than in
            // userspace.
            frame.gprs[1] = 0;
            frame.gprs[0] = 0xDEAD;
            drive_sync(&mut frame);
            assert_eq!(
                frame.x0(),
                0,
                "EC 0x{raw_ec:02x}: x0 must be the value channel, not the status"
            );
            assert_eq!(
                frame.x1(),
                (crate::svc_dispatch::ERROR_LABEL_BASE + u64::from(disc)) << 9,
                "EC 0x{raw_ec:02x}: x1 must carry the status label"
            );
            assert_eq!([frame.x2(), frame.x3(), frame.x4(), frame.x5()], [0; 4]);
        }
    }

    #[test]
    fn esr_ec_extraction() {
        // SVC from AArch64: EC = 0x15, bits [31:26]
        let esr_svc = 0x15u64 << 26;
        assert_eq!(esr_ec(esr_svc), ec::SVC_AARCH64);

        // Data Abort from lower EL: EC = 0x24
        let esr_dabt = 0x24u64 << 26;
        assert_eq!(esr_ec(esr_dabt), ec::DABT_LOWER);

        // Instruction Abort from lower EL: EC = 0x20
        let esr_iabt = 0x20u64 << 26;
        assert_eq!(esr_ec(esr_iabt), ec::IABT_LOWER);

        // PC alignment fault: EC = 0x22
        let esr_pc = 0x22u64 << 26;
        assert_eq!(esr_ec(esr_pc), ec::PC_ALIGN);

        // SP alignment fault: EC = 0x26
        let esr_sp = 0x26u64 << 26;
        assert_eq!(esr_ec(esr_sp), ec::SP_ALIGN);
    }

    #[test]
    fn esr_ec_preserves_lower_bits() {
        // EC = 0x15 with ISS = 0x42 (lower 25 bits should be ignored)
        let esr = (0x15u64 << 26) | 0x42;
        assert_eq!(esr_ec(esr), ec::SVC_AARCH64);
    }

    // AI1-A: Verify error code constants match sele4n-types KernelError discriminants
    #[test]
    fn error_code_vm_fault_matches_lean() {
        // Lean ExceptionModel.lean: data/instruction abort → .error .vmFault
        // sele4n-types error.rs: VmFault = 44
        assert_eq!(error_code::VM_FAULT, 44);
    }

    #[test]
    fn error_code_user_exception_matches_lean() {
        // Lean ExceptionModel.lean:175-177: pcAlignment, spAlignment,
        // unknownReason all map to .error .userException
        // sele4n-types error.rs: UserException = 45
        assert_eq!(error_code::USER_EXCEPTION, 45);
    }

    #[test]
    fn error_code_not_implemented_matches_lean() {
        // sele4n-types error.rs: NotImplemented = 17
        assert_eq!(error_code::NOT_IMPLEMENTED, 17);
    }

    // ========================================================================
    // WS-SM SM1.I.1 / SM5 — Per-core IRQ handler entry tests
    //
    // `handle_irq_per_core` is the live IRQ path (`trap.S`'s
    // `__el0_irq_entry` / `__el1_irq_entry` branch to it; pinned by
    // `build.rs::scan_trap_s_irq_vector_redirect`).  We verify:
    //
    //   1. The function exists with the expected `extern "C" fn(&mut TrapFrame)`
    //      ABI signature — the assembly entry resolves it.
    //   2. Calling it on host increments the per-core IRQ counter.
    //      (The dispatcher on host reads `acknowledge_irq_classified`,
    //      which on host MMIO returns Spurious/OutOfRange — the
    //      ABI exercise does not require a real GIC.)
    //   3. The `#[no_mangle]` attribute is preserved so the linker
    //      can resolve the symbol at the assembly entry vector.
    //
    // The dispatch-closure branches (timer / SGI / unhandled) are
    // tested at the per_cpu_stats inner-form level and at the trap
    // unit-test level via cross-module composition.
    // ========================================================================

    #[test]
    fn handle_irq_per_core_has_correct_abi_signature() {
        // Function-pointer coercion: extern "C" fn(&mut TrapFrame) is
        // the assembly's expected entry signature.  A future regression
        // that changes the signature (e.g., to `fn(u64, &mut TrapFrame)`
        // for a hypothetical per-CPU explicit pass) would fail to
        // coerce here at compile time.
        let _: extern "C" fn(&mut TrapFrame) = handle_irq_per_core;
    }

    #[test]
    fn handle_irq_per_core_no_mangle_attribute_preserved() {
        // The symbol must have a stable linker-visible address so
        // `trap.S`'s IRQ entry can resolve it.  Take the address-of
        // and assert non-null.  Inlining or dead-code elimination
        // would null this; `#[no_mangle]` prevents both.
        let p = handle_irq_per_core as *const ();
        assert!(
            !p.is_null(),
            "handle_irq_per_core must have a stable linker-visible address"
        );
    }

    #[test]
    fn reschedule_sgi_handler_matches_sgi_handler_signature() {
        // WS-SM SM5.C.5: the `.reschedule` handler must coerce to the
        // SM1.F.5 `SgiHandler` table signature `fn(u8, u8)` so
        // `register_reschedule_sgi_handler` can install it.  (The
        // INTID value itself is pinned at compile time by the
        // `const _: () = assert!(...)` pins beside `RESCHEDULE_INTID`.)
        let _: crate::gic::SgiHandler = reschedule_sgi_handler;
    }

    #[test]
    fn reschedule_sgi_handler_host_call_does_not_panic() {
        // WS-SM SM5.C.5: on host no kernel image is linked
        // (`hw_target` off), so the handler is the record-only arm.
        // Verify it returns without panicking for any source CPU.
        reschedule_sgi_handler(RESCHEDULE_INTID, 0);
        reschedule_sgi_handler(RESCHEDULE_INTID, 3);
    }

    #[test]
    fn handle_irq_per_core_runtime_call_does_not_panic() {
        // SM1.I.1 audit-pass-1: actually invoke `handle_irq_per_core`
        // on host and verify it returns without panicking.  The host
        // GIC stub returns INTID 0 from `acknowledge_irq` (mmio_read32
        // on a host base returns 0), which `dispatch_irq_classified`
        // classifies as `Handled(0)`.  The closure then takes the
        // SGI branch (INTID 0 < MAX_SGI_INTID = 16) and logs.  This
        // exercises the full call path on host without requiring
        // hardware.
        let mut frame = zero_frame();
        handle_irq_per_core(&mut frame);
        // No assertion on counter values — those depend on the
        // running test order and the global PER_CPU_STATS state.
        // The property we're asserting is "doesn't panic".
    }

    #[test]
    fn handle_irq_per_core_advances_per_core_irq_count() {
        // SM1.I.1: a successful invocation must advance the per-core
        // IRQ counter.  We compare before/after snapshots; the delta
        // includes any concurrent IRQs from parallel tests, but the
        // delta MUST be >= 1 (this thread's call).
        //
        // Because `dispatch_irq` only runs the closure on the
        // `Handled` arm (and the host stub's INTID 0 IS handled), we
        // expect exactly 1 increment from this thread.  Parallel
        // tests can add more, so we check `after > before`.
        let before = crate::per_cpu_stats::irq_count_for(0);
        let mut frame = zero_frame();
        handle_irq_per_core(&mut frame);
        let after = crate::per_cpu_stats::irq_count_for(0);
        assert!(
            after > before,
            "handle_irq_per_core must advance per-core irq_count \
             (before={}, after={})",
            before,
            after
        );
    }

    // ========================================================================
    // WS-SM SM1.I.4 — synchronous-exception per-core stats wiring tests
    //
    // The four exception-class branches (SVC, DABT, IABT, PC_ALIGN /
    // SP_ALIGN, Unknown) each increment a distinct per-core counter
    // through `crate::per_cpu_stats`.  The tests below cross-check
    // that calling `handle_synchronous_exception` advances the
    // appropriate counter.
    //
    // Note: these tests share the global `PER_CPU_STATS` array, so
    // they read pre-call snapshots and compare deltas (rather than
    // absolute values).  This makes them robust under cargo's
    // parallel test execution where other suites may concurrently
    // increment the same global counters.
    // ========================================================================

    // PR #889 review: `handle_sync_svc_increments_per_core_syscall_count` moved
    // to `tests/readiness_gate_after_mark.rs` (`svc_increments_per_core_syscall_count`):
    // driving an `SVC` through the handler now halts on a not-ready core, which
    // in this binary is an abort (see the note above), and core 0's readiness
    // is not this binary's to assume in either direction.

    #[test]
    fn handle_sync_dabt_increments_per_core_vm_fault_count() {
        // Audit-pass-3: see PER_CORE_STATS_OBSERVATION_MUTEX docstring.
        let _guard = PER_CORE_STATS_OBSERVATION_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let before = crate::per_cpu_stats::vm_fault_count_for(0);
        let mut frame = zero_frame();
        frame.esr_el1 = ec::DABT_LOWER << 26;
        handle_synchronous_exception(&mut frame);
        let after = crate::per_cpu_stats::vm_fault_count_for(0);
        assert!(
            after > before,
            "DABT must increment per-core vm_fault_count (was {}, now {})",
            before,
            after
        );
    }

    #[test]
    fn handle_sync_iabt_increments_per_core_vm_fault_count() {
        let _guard = PER_CORE_STATS_OBSERVATION_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let before = crate::per_cpu_stats::vm_fault_count_for(0);
        let mut frame = zero_frame();
        frame.esr_el1 = ec::IABT_LOWER << 26;
        handle_synchronous_exception(&mut frame);
        let after = crate::per_cpu_stats::vm_fault_count_for(0);
        assert!(
            after > before,
            "IABT must increment per-core vm_fault_count (was {}, now {})",
            before,
            after
        );
    }

    #[test]
    fn handle_sync_alignment_increments_per_core_user_exception_count() {
        let _guard = PER_CORE_STATS_OBSERVATION_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let before = crate::per_cpu_stats::user_exception_count_for(0);
        let mut frame = zero_frame();
        frame.esr_el1 = ec::PC_ALIGN << 26;
        handle_synchronous_exception(&mut frame);
        let after = crate::per_cpu_stats::user_exception_count_for(0);
        assert!(
            after > before,
            "PC alignment must increment per-core user_exception_count (was {}, now {})",
            before,
            after
        );
    }

    #[test]
    fn handle_sync_sp_alignment_increments_per_core_user_exception_count() {
        let _guard = PER_CORE_STATS_OBSERVATION_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let before = crate::per_cpu_stats::user_exception_count_for(0);
        let mut frame = zero_frame();
        frame.esr_el1 = ec::SP_ALIGN << 26;
        handle_synchronous_exception(&mut frame);
        let after = crate::per_cpu_stats::user_exception_count_for(0);
        assert!(
            after > before,
            "SP alignment must increment per-core user_exception_count (was {}, now {})",
            before,
            after
        );
    }

    #[test]
    fn handle_sync_unknown_ec_increments_per_core_user_exception_count() {
        let _guard = PER_CORE_STATS_OBSERVATION_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let before = crate::per_cpu_stats::user_exception_count_for(0);
        let mut frame = zero_frame();
        // EC = 0x3F (RES1, not a valid known class) → unknown branch.
        frame.esr_el1 = 0x3Fu64 << 26;
        handle_synchronous_exception(&mut frame);
        let after = crate::per_cpu_stats::user_exception_count_for(0);
        assert!(
            after > before,
            "Unknown EC must increment per-core user_exception_count (was {}, now {})",
            before,
            after
        );
    }
}
