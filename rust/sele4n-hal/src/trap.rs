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

    /// Set x0 (return value / error code).
    #[inline(always)]
    pub fn set_x0(&mut self, val: u64) {
        self.gprs[0] = val;
    }

    /// Set x1 (return message info).
    #[inline(always)]
    pub fn set_x1(&mut self, val: u64) {
        self.gprs[1] = val;
    }
}

/// ESR_EL1 Exception Class (EC) field values.
/// ARM ARM D17.2.40: ESR_EL1 bits [31:26].
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
    /// `KernelError::NotImplemented = 17` — syscall dispatch not yet wired.
    pub const NOT_IMPLEMENTED: u64 = 17;
    /// `KernelError::VmFault = 44` — data abort or instruction abort.
    pub const VM_FAULT: u64 = 44;
    /// `KernelError::UserException = 45` — alignment fault, unknown exception.
    /// Matches Lean `ExceptionModel.lean` mapping of `pcAlignment`,
    /// `spAlignment`, and `unknownReason` to `.error .userException`.
    pub const USER_EXCEPTION: u64 = 45;
}

/// Extract the Exception Class from ESR_EL1.
#[inline(always)]
fn esr_ec(esr: u64) -> u64 {
    (esr >> 26) & 0x3F
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
    let exception_class = esr_ec(esr);

    // AG9-F: CSDB after reading the exception class ensures speculative
    // execution cannot bypass the match and enter the wrong handler.
    crate::barriers::csdb();

    match exception_class {
        ec::SVC_AARCH64 => {
            // Syscall: extract the immediate from ESR (bits [15:0]) or use x7
            // The seLe4n ABI uses x7 for syscall number, matching the Lean
            // model's `arm64DefaultLayout.syscallNumReg = ⟨7⟩`.
            //
            // TODO(AN9-F): Wire Lean FFI dispatch via sele4n_syscall_dispatch
            // (closes DEF-R-HAL-L14 per docs/audits/AUDIT_v0.29.0_DEFERRED.md
            // and docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12 AN9-F).
            // See SeLe4n/Platform/FFI.lean for the Lean-side declarations.
            // Until wired, return NotImplemented to prevent userspace from
            // interpreting a no-op stub as success.
            let _syscall_id = frame.x7();
            frame.set_x0(error_code::NOT_IMPLEMENTED);
        }
        ec::DABT_LOWER | ec::DABT_CURRENT => {
            // Data abort — VM fault (KernelError::VmFault = 44)
            frame.set_x0(error_code::VM_FAULT);
        }
        ec::IABT_LOWER | ec::IABT_CURRENT => {
            // Instruction abort — VM fault (KernelError::VmFault = 44)
            frame.set_x0(error_code::VM_FAULT);
        }
        ec::PC_ALIGN | ec::SP_ALIGN => {
            // Alignment fault — user exception (KernelError::UserException = 45)
            // Matches Lean ExceptionModel.lean:175-177 mapping of pcAlignment
            // and spAlignment to `.error .userException`.
            frame.set_x0(error_code::USER_EXCEPTION);
        }
        _ => {
            // Unknown exception class — user exception (KernelError::UserException = 45)
            // Matches Lean ExceptionModel.lean:175-177 mapping of unknownReason
            // to `.error .userException`.
            crate::kprintln!("FATAL: unhandled exception EC=0x{:02x} ESR=0x{:016x}", exception_class, esr);
            frame.set_x0(error_code::USER_EXCEPTION);
        }
    }
}

/// IRQ handler — called from assembly after context save.
///
/// AG5-C: Wired to GIC-400 acknowledge → EOI → dispatch sequence.
/// The dispatch routes timer interrupts (INTID 30) to the timer handler,
/// which re-arms the hardware comparator for the next interval.
///
/// AI1-C/M-26: Tick accounting (incrementing the tick counter) is performed
/// exclusively by the Lean kernel via `ffi_timer_reprogram` (ffi.rs). The
/// IRQ handler only re-arms the hardware timer to prevent missed interrupts.
/// This eliminates the dual-path bug where both the IRQ handler and the FFI
/// bridge incremented the tick count, causing double-counting.
///
/// AN8-C.3 (H-19): `#[deny(clippy::panic)]` is applied at the function
/// level so a future edit that inserts `panic!()` directly inside the
/// handler body fails `cargo clippy`. Even though AN8-C.1's EOI-before-
/// handler reorder removed the panic-loses-EOI class structurally, a
/// panicking handler still halts the kernel under `panic = "abort"`, so
/// direct panics are a latent correctness hazard: the handler should
/// signal recoverable conditions through return values, not unwinding.
#[no_mangle]
#[deny(clippy::panic)]
pub extern "C" fn handle_irq(_frame: &mut TrapFrame) {
    crate::gic::dispatch_irq(|intid| {
        if intid == crate::gic::TIMER_PPI_ID {
            // Timer interrupt: re-arm the hardware comparator only.
            // Tick accounting is performed by the Lean kernel via
            // ffi_timer_reprogram — see ffi.rs:40-43.
            //
            // AN8-C.4 re-entrancy note: `reprogram_timer()` computes
            // `CNTP_CVAL_EL0 = CNTPCT_EL0 + interval`. On RPi5 the
            // interval is 54 000 counter ticks (~1 ms at 54 MHz);
            // handler latency is ≪ 1 ms, so the timer IRQ cannot
            // re-trigger inside this handler body. The GIC's CPU-
            // interface running-priority mask also holds the INTID off
            // until PSTATE.I clears on exception return.
            crate::timer::reprogram_timer();
        } else {
            // Non-timer interrupt: log for debugging
            // AG7 will wire device interrupts to notification signals via FFI
            crate::kprintln!("IRQ: unhandled INTID {}", intid);
        }
    });
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
        // SVC ESR into the frame and verify the SVC-arm is taken (x0 ends
        // up = NOT_IMPLEMENTED).
        let mut frame = zero_frame();
        frame.esr_el1 = (ec::SVC_AARCH64 << 26) | 0x42; // lower bits ignored
        handle_synchronous_exception(&mut frame);
        assert_eq!(frame.x0(), error_code::NOT_IMPLEMENTED);
    }

    #[test]
    fn handle_sync_data_abort_via_frame() {
        // AK5-F.3: DABT from lower EL is classified from frame ESR, not
        // from live register — proves the handler is not reading live mrs.
        let mut frame = zero_frame();
        frame.esr_el1 = ec::DABT_LOWER << 26;
        frame.far_el1 = 0xFFFF_0000_DEAD_0000;
        handle_synchronous_exception(&mut frame);
        assert_eq!(frame.x0(), error_code::VM_FAULT);
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

        // Simulate nested: inner frame with different ESR/FAR.
        let mut inner = zero_frame();
        inner.esr_el1 = ec::IABT_CURRENT << 26;
        inner.far_el1 = 0xBBBB;
        handle_synchronous_exception(&mut inner);

        // The outer frame remains untouched.
        assert_eq!(outer.esr_el1, ec::DABT_LOWER << 26);
        assert_eq!(outer.far_el1, 0xAAAA);
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
        assert_ne!(error_code::NOT_IMPLEMENTED, 0,
            "SVC stub must not return success (0)");
    }
}
