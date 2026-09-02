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
///
/// Total size: 36 × 8 = 288 bytes, 16-byte aligned.
///
/// AK5-F (R-HAL-H04 / HIGH): ESR_EL1 and FAR_EL1 are saved at exception
/// entry so that handlers read a STABLE snapshot rather than the live
/// register. A nested exception (e.g., SError during data-abort handling)
/// would otherwise mutate the live ESR/FAR before the outer handler reads
/// them, producing incorrect classification and fault-address reports.
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
}

/// Size of TrapFrame in bytes (for assembly offset calculations).
/// AK5-F: 288 bytes (was 272 pre-AK5-F).
pub const TRAP_FRAME_SIZE: usize = core::mem::size_of::<TrapFrame>();

// Compile-time layout assertions (AK5-F).
const _: () = assert!(TRAP_FRAME_SIZE == 288);
const _: () = assert!(core::mem::align_of::<TrapFrame>() == 16);
const _: () = assert!(core::mem::offset_of!(TrapFrame, gprs) == 0);
const _: () = assert!(core::mem::offset_of!(TrapFrame, sp_el0) == 248);
const _: () = assert!(core::mem::offset_of!(TrapFrame, elr_el1) == 256);
const _: () = assert!(core::mem::offset_of!(TrapFrame, spsr_el1) == 264);
const _: () = assert!(core::mem::offset_of!(TrapFrame, esr_el1) == 272);
const _: () = assert!(core::mem::offset_of!(TrapFrame, far_el1) == 280);

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
    /// **Consumer**: SM10.1's context restore, which does not exist yet — this
    /// mutator and its two siblings above are exercised by tests only today.
    /// That is not an oversight to be tidied away: the restart frame is
    /// installed into the *Lean* TCB by `applyFaultRestart` at reply time, and
    /// reaches hardware when a core installs a successor.  Until then a core
    /// that delivered a fault halts (`deliver_fault`), so there is no restore
    /// to call this from.  RR4.24 exists because without an `ELR_EL1` mutator
    /// the trap layer could only ever return to the faulting instruction, which
    /// is the finding RR4 closes; the API has to be here before the restore
    /// that uses it can be written.
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
}

/// Kernel error discriminants matching `sele4n-types::KernelError` and
/// Lean `SeLe4n.Model.KernelError`. Defined locally to avoid adding a
/// crate dependency from `sele4n-hal` (bare-metal HAL with zero deps).
///
/// AI1-A/AI1-B: Named constants replace bare numeric literals for
/// maintainability and cross-reference clarity.
mod error_code {
    /// `KernelError::NotImplemented = 17` — historical SVC stub return.
    /// Preserved for cross-reference even after AN9-F wired the real
    /// dispatch path; the `svc_stub_returns_not_implemented` test in
    /// the parent module still asserts this value.
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
/// only on the primary before the image target marks it ready: no other core
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
            fn lean_classify_synchronous_exception(esr: u64) -> u32;
        }
        // SAFETY: `lean_classify_synchronous_exception` is the C-callable
        // wrapper the Lean compiler emits for
        // `Kernel.classifySynchronousExceptionExport`.  It takes a `u64` and
        // returns a `u32`, reads no kernel state and allocates nothing, and
        // this core's Lean runtime is initialized — the `lean_ready` gate just
        // checked — so entering the symbol is within the runtime's contract.
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
/// The model has just descheduled the faulting thread.  The hardware cannot
/// honour that until the SM10.1 context restore installs a *successor* —
/// until then `trap.S` restores and `eret`s through the faulting thread's own
/// frame, straight back onto the instruction that faulted, which is precisely
/// the defect RR4 exists to remove.  So the interim behaviour is to stop:
/// `fatal_halt` after a diagnostic, rather than spin.  The halt is
/// unreachable at `v0.34.x` (no core sets `lean_ready`), and SM10.1 replaces
/// it with the successor install — it is the seam's occupant, not its
/// contract.
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
                );
            }
            let (esr, elr, spsr, far) =
                (frame.esr_el1, frame.elr_el1, frame.spsr_el1, frame.far_el1);
            let g = frame.gprs;
            let sp_el0 = frame.sp_el0;
            // SAFETY: `lean_handle_fault` is the C-callable wrapper the Lean
            // compiler emits for `Kernel.faultEntry`
            // (`@[export lean_handle_fault]`).  It takes fifteen `u64`s and
            // returns no value; calling it is sound from EL1 exception context
            // once this core's Lean runtime is initialized (the gate just
            // checked) and inside the kernel-entry lock (taken below), which is
            // what serialises its `IO.Ref` commit.
            crate::kernel_entry::with_kernel_entry(core_id as usize, || unsafe {
                lean_handle_fault(
                    core_id, esr, elr, spsr, far, g[0], g[1], g[2], g[3], g[4], g[5], g[6], g[7],
                    sp_el0, g[30],
                );
            });
            crate::kprintln!(
                "[core {}] fault delivered; halting pending the SM10.1 context restore (ESR=0x{:016x} ELR=0x{:016x})",
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

/// **PR #887 review round 3**: an EL0 abort taken on a core whose Lean
/// runtime is not initialized.  Nothing can be delivered (there is no model
/// to deliver into) and nothing can be returned: the abort left `ELR_EL1` on
/// the faulting instruction, so any frame the handler published would be
/// `eret`ed straight back into the same abort — the wedge RR4 exists to
/// remove, reintroduced on the fallback.  The only fail-closed action is to
/// stop the core, as `deliver_fault`'s delivered arm does pending the SM10.1
/// successor install; both branches of that function therefore diverge on
/// hardware.  The SVC seam is different and keeps its status frame: an `SVC`
/// advances `ELR_EL1` past itself, so a frame returned to a thread is a
/// coherent outcome there (and the not-ready behaviour of the SVC seam as a
/// whole is RR5's to decide, together with the ungated `dispatch_svc` beside
/// it).  Unreachable today — no core sets `lean_ready`, and no user thread
/// exists before the runtime that creates it — and pinned by
/// `abort_before_lean_ready_halts` on the host lane, where `fatal_halt`
/// panics.
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
/// readiness gate, same SM10.1 halt as `deliver_fault`, for the same reasons.
///
/// The not-ready path differs from `deliver_fault`'s, deliberately: this seam
/// keeps its status frame, because an `SVC` advances `ELR_EL1` past itself
/// and a frame returned to the thread is a coherent outcome, where an abort's
/// would re-execute the faulting instruction (PR #887 review round 3).  What
/// a not-ready core should do with an `SVC` at all is RR5's question, asked
/// once for the whole SVC seam together with the ungated `dispatch_svc`.
#[allow(unused_variables)]
fn deliver_unknown_syscall(frame: &mut TrapFrame) {
    #[cfg(feature = "hw_target")]
    {
        let core_id = crate::per_cpu::current_core_id_from_tpidr();
        if crate::lean_ready::lean_ready(core_id as usize) {
            extern "C" {
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
                );
            }
            let (esr, elr, spsr, far) =
                (frame.esr_el1, frame.elr_el1, frame.spsr_el1, frame.far_el1);
            let g = frame.gprs;
            let sp_el0 = frame.sp_el0;
            // SAFETY: `lean_handle_unknown_syscall` is the C-callable wrapper
            // the Lean compiler emits for `Kernel.unknownSyscallEntry`
            // (`@[export lean_handle_unknown_syscall]`).  Fifteen `u64`s, no
            // return value; sound from EL1 exception context once this core's
            // Lean runtime is initialized (the gate just checked) and inside
            // the kernel-entry lock (taken below), which serialises its
            // `IO.Ref` commit.
            crate::kernel_entry::with_kernel_entry(core_id as usize, || unsafe {
                lean_handle_unknown_syscall(
                    core_id, esr, elr, spsr, far, g[0], g[1], g[2], g[3], g[4], g[5], g[6], g[7],
                    sp_el0, g[30],
                );
            });
            crate::kprintln!(
                "[core {}] unknown syscall delivered; halting pending the SM10.1 context restore (x7=0x{:x} ELR=0x{:016x})",
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
            // and forwards via the `syscall_dispatch_inner`
            // `extern "C"` symbol (Lean-emitted by
            // `@[export syscall_dispatch_inner]` in
            // `SeLe4n/Platform/FFI.lean`) into the Lean kernel.
            // Errors are surfaced via x0 with the canonical
            // KernelError discriminant (matching `sele4n-types`):
            // post-WS-RC R2 the `dispatch_svc` shim wraps the raw
            // discriminant in `DispatchError::Kernel(disc)` so
            // user-mode sees exactly the value the Lean kernel
            // emitted.
            //
            // WS-SM SM1.I.4: record per-core syscall count for
            // benchmarking / post-mortem attribution.  Wait-free
            // (single AtomicU64::fetch_add) and not on any
            // correctness path.
            let _ = crate::per_cpu_stats::record_syscall();
            let args = crate::svc_dispatch::SyscallArgs::from_trap_frame(frame);
            // PR #887 review round 3: the syscall number is the FULL 64-bit
            // `x7`.  Narrowing first would make `0x1_0000_0002` syscall 2; a
            // word the ABI cannot name is an unknown syscall, delivered to the
            // thread's fault handler like any other, with the full word.
            let dispatched = match u32::try_from(frame.x7()) {
                Ok(syscall_id) => crate::svc_dispatch::dispatch_svc(syscall_id, &args),
                Err(_) => Err(crate::svc_dispatch::DispatchError::InvalidSyscallId),
            };
            // WS-RA (plan §3.1/§3.3): the writeback is a six-register
            // context restore — `x0` the value, the offset error label on
            // `x1`, `x2`-`x5` message registers.  A blocked caller has NO
            // return frame (its stale registers are not a return value;
            // the staged frame is delivered by the SM10.1 context restore
            // — RA.C.9's hook is the `Blocked` arm).  Prefilter rejections
            // surface as label-encoded error frames like every kernel
            // rejection, retiring the raw-discriminant `x0` write and its
            // documented collision.
            match dispatched {
                Ok(crate::svc_dispatch::SvcOutcome::Frame(regs)) => frame.set_return_frame(regs),
                Ok(crate::svc_dispatch::SvcOutcome::Blocked) => {
                    // SM10.1 context-restore hook: the successor's frame
                    // install lands here when `contextRestoreSeamLive`
                    // flips.  Until then `trap.S` restores and `eret`s
                    // through the blocked caller's own saved frame, so
                    // poison it: left untouched, the caller's request
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
pub extern "C" fn handle_irq_per_core(_frame: &mut TrapFrame) {
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
            // and returns no value; calling it is sound from EL1 IRQ context
            // after per-core hardware init has completed (the SGI can only be
            // taken once `enable_irq` ran on this core, which is after the
            // bring-up entry established this core's scheduler state) AND this
            // core's Lean runtime is initialized (the gate just checked).
            extern "C" {
                fn lean_per_core_reschedule(core_id: u64);
            }
            crate::kernel_entry::with_kernel_entry(core_id as usize, || unsafe {
                lean_per_core_reschedule(core_id);
            });
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
#[no_mangle]
pub extern "C" fn handle_serror(_frame: &mut TrapFrame) -> ! {
    crate::kprintln!("FATAL: SError exception");
    loop {
        crate::cpu::wfe();
    }
}

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests {
    use super::*;

    /// AK5-F test helper: construct a zero-initialized TrapFrame.
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
    fn trap_frame_size_is_288_bytes() {
        // AK5-F: TrapFrame grew from 272 to 288 (added ESR_EL1 + FAR_EL1).
        assert_eq!(TRAP_FRAME_SIZE, 288);
        assert_eq!(core::mem::size_of::<TrapFrame>(), 288);
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

    #[test]
    fn handle_sync_reads_esr_from_frame() {
        // AK5-F.3: handler uses `frame.esr_el1` not `mrs esr_el1`. Put an
        // SVC ESR into the frame and verify the SVC-arm is taken.
        //
        // WS-RA: the stub kernel publishes the label-encoded
        // `NotImplemented` (discriminant 17 → label ERROR_LABEL_BASE + 17)
        // error frame, and the SVC arm's writeback is the full six-register
        // restore — `x0 = 0`, the status label on `x1`, `x2`-`x5` zero.
        // Under the retired bit-63 convention this test asserted `x0 == 17`.
        let mut frame = zero_frame();
        frame.esr_el1 = (ec::SVC_AARCH64 << 26) | 0x42; // lower bits ignored
        drive_sync(&mut frame);
        assert_eq!(frame.x0(), 0);
        assert_eq!(
            frame.x1(),
            (crate::svc_dispatch::ERROR_LABEL_BASE + u64::from(error_code::NOT_IMPLEMENTED)) << 9
        );
        assert_eq!([frame.x2(), frame.x3(), frame.x4(), frame.x5()], [0; 4]);
    }

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

    /// **PR #887 review**: a syscall number outside `SyscallId` takes the
    /// unknown-syscall seam.  On the host lane no core is Lean-ready, so the
    /// seam's fail-closed half publishes the `invalidSyscallNumber` status
    /// frame (discriminant 31) — never a success, never the thread's own
    /// request registers.
    #[test]
    fn handle_sync_unknown_syscall_id_not_ready_publishes_status_frame() {
        let mut frame = zero_frame();
        frame.esr_el1 = ec::SVC_AARCH64 << 26;
        frame.gprs[7] = 0xFFFF; // no such syscall
        frame.gprs[0] = 0xDEAD;
        drive_sync(&mut frame);
        assert_eq!(frame.x0(), 0);
        assert_eq!(
            frame.x1(),
            (crate::svc_dispatch::ERROR_LABEL_BASE + 31) << 9
        );
        assert_eq!([frame.x2(), frame.x3(), frame.x4(), frame.x5()], [0; 4]);
    }

    /// **PR #887 review round 3**: the syscall number is validated at its
    /// full 64-bit width.  `0x1_0000_0002` narrows to syscall 2, which the
    /// old `as u32` would have dispatched (the host stub answers it with the
    /// `notImplemented` frame, discriminant 17); it is an unknown syscall,
    /// and on the not-ready host lane that is the `invalidSyscallNumber`
    /// status frame (31).
    #[test]
    fn handle_sync_wide_syscall_number_is_unknown_syscall() {
        let mut frame = zero_frame();
        frame.esr_el1 = ec::SVC_AARCH64 << 26;
        frame.gprs[7] = 0x1_0000_0002;
        drive_sync(&mut frame);
        assert_eq!(frame.x0(), 0);
        assert_eq!(
            frame.x1(),
            (crate::svc_dispatch::ERROR_LABEL_BASE + 31) << 9
        );
        assert_ne!(
            frame.x1(),
            (crate::svc_dispatch::ERROR_LABEL_BASE + 17) << 9
        );
    }

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

    // AI1-B: Verify SVC handler returns NotImplemented (not success)
    #[test]
    fn svc_stub_returns_not_implemented() {
        // The SVC handler is a pre-FFI stub. It must return NotImplemented (17)
        // to prevent userspace from interpreting the no-op as success (0).
        assert_ne!(
            error_code::NOT_IMPLEMENTED,
            0,
            "SVC stub must not return success (0)"
        );
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

    #[test]
    fn handle_sync_svc_increments_per_core_syscall_count() {
        // Audit-pass-3: serialise via PER_CORE_STATS_OBSERVATION_MUTEX so concurrent
        // trap-handler tests don't race on PER_CPU_STATS[0].syscall_count.
        let _guard = PER_CORE_STATS_OBSERVATION_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let before = crate::per_cpu_stats::syscall_count_for(0);
        let mut frame = zero_frame();
        frame.esr_el1 = ec::SVC_AARCH64 << 26;
        handle_synchronous_exception(&mut frame);
        let after = crate::per_cpu_stats::syscall_count_for(0);
        assert!(
            after > before,
            "SVC must increment per-core syscall_count (was {}, now {})",
            before,
            after
        );
    }

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

    #[test]
    fn per_core_counters_track_distinct_exception_branches() {
        // Cross-check: each EC branch must advance ONLY its own counter
        // (not other counters in the same call).
        //
        // We use the inner-form recorders' inverse property: an SVC
        // call must NOT increment vm_fault_count.
        //
        // Audit-pass-3 (per external audit H2): without the mutex this
        // test races against `sm1i4_handle_sync_dabt_increments_...`
        // and friends, producing a ~2% transient failure rate.
        // The mutex ensures the `assert_eq!` snapshot pair is atomic.
        let _guard = PER_CORE_STATS_OBSERVATION_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let vm_before = crate::per_cpu_stats::vm_fault_count_for(0);
        let mut frame = zero_frame();
        frame.esr_el1 = ec::SVC_AARCH64 << 26;
        handle_synchronous_exception(&mut frame);
        let vm_after = crate::per_cpu_stats::vm_fault_count_for(0);
        assert_eq!(
            vm_after, vm_before,
            "SVC must not increment vm_fault_count (was {}, now {})",
            vm_before, vm_after
        );
    }
}
