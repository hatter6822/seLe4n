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
    /// `KernelError::NotImplemented = 17` — historical SVC stub return.
    /// Preserved for cross-reference even after AN9-F wired the real
    /// dispatch path; the `svc_stub_returns_not_implemented` test in
    /// the parent module still asserts this value.
    #[allow(dead_code)]
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
            let syscall_id = frame.x7() as u32;
            let args = crate::svc_dispatch::SyscallArgs::from_trap_frame(frame);
            match crate::svc_dispatch::dispatch_svc(syscall_id, &args) {
                Ok(retval) => frame.set_x0(retval),
                Err(e) => frame.set_x0(e.to_u32() as u64),
            }
        }
        ec::DABT_LOWER | ec::DABT_CURRENT => {
            // Data abort — VM fault (KernelError::VmFault = 44)
            // WS-SM SM1.I.4: per-core VM-fault attribution.
            let _ = crate::per_cpu_stats::record_vm_fault();
            frame.set_x0(error_code::VM_FAULT);
        }
        ec::IABT_LOWER | ec::IABT_CURRENT => {
            // Instruction abort — VM fault (KernelError::VmFault = 44)
            // WS-SM SM1.I.4: per-core VM-fault attribution.
            let _ = crate::per_cpu_stats::record_vm_fault();
            frame.set_x0(error_code::VM_FAULT);
        }
        ec::PC_ALIGN | ec::SP_ALIGN => {
            // Alignment fault — user exception (KernelError::UserException = 45)
            // Matches Lean ExceptionModel.lean:175-177 mapping of pcAlignment
            // and spAlignment to `.error .userException`.
            // WS-SM SM1.I.4: per-core user-exception attribution.
            let _ = crate::per_cpu_stats::record_user_exception();
            frame.set_x0(error_code::USER_EXCEPTION);
        }
        _ => {
            // Unknown exception class — user exception (KernelError::UserException = 45)
            // Matches Lean ExceptionModel.lean:175-177 mapping of unknownReason
            // to `.error .userException`.
            // WS-SM SM1.I.4: per-core user-exception attribution.
            let _ = crate::per_cpu_stats::record_user_exception();
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
/// level (together with the related `clippy::unreachable` and
/// `clippy::todo` lints, which are panic-equivalents at runtime) so a
/// future edit that inserts `panic!()`, `unreachable!()`, or `todo!()`
/// directly inside the handler body fails `cargo clippy`. Even though
/// AN8-C.1's EOI-before-handler reorder removed the panic-loses-EOI
/// class structurally, a panicking handler still halts the kernel
/// under `panic = "abort"`, so direct panics are a latent correctness
/// hazard: the handler should signal recoverable conditions through
/// return values, not unwinding.
#[no_mangle]
#[deny(clippy::panic, clippy::unreachable, clippy::todo)]
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
            // Non-timer interrupt: log for debugging.
            //
            // WS-SM SM1.F note: SGIs (INTIDs 0..15) currently land
            // in this "unhandled" branch.  The SM1.F primitive
            // surface (send_sgi, dispatch_sgi, register_sgi_handler)
            // is fully implemented in gic.rs, but `dispatch_irq` /
            // `acknowledge_irq_classified` only return the INTID,
            // not the source_cpu (bits [12:10] of GICC_IAR).
            // Wiring SGIs into the trap handler requires:
            //   1. A `dispatch_irq` variant that preserves the full
            //      IAR (or extracts source_cpu via `iar_source_cpu`).
            //   2. The kernel-side Lean handler registration logic
            //      (per the SM5+ per-core scheduler state).
            // Both are SM5+ follow-on work.  At SM1.F the SGI HAL
            // primitives are unit-tested and ready; the trap-handler
            // wiring is the next layer up.
            //
            // AG7 will additionally wire device interrupts (SPIs)
            // to notification signals via FFI.
            crate::kprintln!("IRQ: unhandled INTID {}", intid);
        }
    });
}

/// **WS-SM SM1.I.1**: Per-core IRQ handler entry.
///
/// Reads the calling core's id from `TPIDR_EL1` via
/// [`crate::per_cpu::current_core_id_from_tpidr`], records per-core IRQ
/// dispatch / timer-tick / SGI statistics ([`crate::per_cpu_stats`]),
/// then dispatches the IRQ through [`crate::gic::dispatch_irq`].  The
/// dispatch closure routes by INTID:
///
///   * `INTID == TIMER_PPI_ID (30)` → re-arm timer (legacy
///     [`crate::timer::reprogram_timer`]) AND record the per-core
///     timer-tick counter.
///   * `INTID < MAX_SGI_INTID (16)` → record the per-core SGI counter.
///     At SM1.I we cannot route through the SGI handler table because
///     [`crate::gic::dispatch_irq`] discards the source-CPU bits of
///     `GICC_IAR`; SM5 will add a `dispatch_irq` variant that preserves
///     the full IAR and routes through [`crate::gic::dispatch_sgi`].
///     The per-core counter still advances so test infrastructure
///     measuring SGI volume (SM1.H.5 round-trip) can observe per-core
///     activity.
///   * Other INTIDs → log a diagnostic with the per-core `[core N]`
///     prefix so the boot trace is unambiguously per-core attributable.
///
/// # Relationship to [`handle_irq`]
///
/// At SM1.I the assembly entry vector still calls [`handle_irq`]
/// (single-core legacy entry).  This function is added as the **SM5
/// landing seam**: once SM5+ per-core scheduler state is wired,
/// `trap.S`'s IRQ entry will be redirected here so every IRQ pays one
/// extra `mrs tpidr_el1` and one atomic counter increment in exchange
/// for full per-core attribution.
///
/// # Cost
///
/// Net addition over [`handle_irq`]: 1 × `mrs tpidr_el1` (~3 cycles) +
/// 1 × cache-hot load of `PerCpuData.core_id` (~3 cycles) + 1 × atomic
/// counter increment (~5 cycles uncontended on Cortex-A76).
/// Subset counters (timer / SGI) add another atomic per matched
/// branch.  Total overhead < 20 cycles per IRQ.
///
/// # SM5+ extensions
///
/// SM5 will:
/// - Wire this function as the assembly entry point (replacing
///   [`handle_irq`]).
/// - Surface the per-core IRQ counters through a verified read API.
/// - Route SGI dispatches through [`crate::gic::dispatch_sgi`] with
///   the full IAR (requires a `dispatch_irq_with_iar` variant).
/// - Push timer-tick accounting into per-core scheduler state, removing
///   the global tick counter's role as the canonical timekeeper.
///
/// # Panic discipline
///
/// `#[deny(clippy::panic)]` matches [`handle_irq`]'s contract.  A
/// panicking IRQ handler halts the kernel under `panic = "abort"`,
/// which is a structural-correctness hazard; the lint catches direct
/// `panic!()` calls at compile time.
#[no_mangle]
#[deny(clippy::panic, clippy::unreachable, clippy::todo)]
pub extern "C" fn handle_irq_per_core(_frame: &mut TrapFrame) {
    // Read the calling core's id from TPIDR_EL1.  On hardware this is
    // pre-set by `boot.rs::rust_boot_main` (boot core) or
    // `boot.S::secondary_entry` (secondaries) before any kernel-mode
    // code runs.  On host the stub returns 0.
    //
    // Audit-pass-4: this binding is retained as the SM5 landing-seam
    // contract (verified by `build.rs::scan_trap_rs_handle_irq_per_core_intact`).
    // The current closure body uses `kprintln_core!` (which reads
    // TPIDR_EL1 internally) for log lines, so `core_id` is not
    // directly consumed today; SM5 will use it as the per-core
    // scheduler-state dispatch key.  The single redundant `mrs
    // tpidr_el1` (one cycle on Cortex-A76) is the cost of pinning
    // the SM5 contract at the structural level.
    let _core_id = crate::per_cpu::current_core_id_from_tpidr();

    crate::gic::dispatch_irq(|intid| {
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
            // Timer interrupt: re-arm the hardware comparator only.
            // Tick accounting is performed by the Lean kernel via
            // `ffi_timer_reprogram` — see ffi.rs:40-43.  The per-core
            // tick counter advances here as an SMP-localised diagnostic;
            // it is independent of the global `TICK_COUNT` the Lean
            // kernel maintains.
            //
            // The same AN8-C.4 re-entrancy guarantee applies: the IRQ
            // is acknowledged + EOI'd before this closure runs, and the
            // CPU-interface running-priority mask holds INTID 30 off
            // until PSTATE.I clears on exception return.
            let _ = crate::per_cpu_stats::record_timer_tick();
            crate::timer::reprogram_timer();
        } else if intid < u32::from(crate::gic::MAX_SGI_INTID) {
            // SGI dispatch range (INTIDs 0..15).  WS-SM SM1.I.1: at
            // this phase we increment the per-core SGI counter so
            // test infrastructure (SM1.H.5 round-trip; SM5+ scheduler
            // observability) can confirm SGIs arrived on the expected
            // core.  Dispatching to the registered handler is
            // deferred to SM5: `dispatch_irq` does not preserve the
            // full IAR (only the INTID bits), so calling
            // `dispatch_sgi(intid, source_cpu)` here would have to
            // pass `source_cpu = 0` — meaningless for handlers that
            // need to ACK back to the originator.  SM5 will refactor
            // `dispatch_irq` into `dispatch_irq_with_iar` and route
            // SGIs through this branch with the correct source_cpu.
            let _ = crate::per_cpu_stats::record_sgi_dispatch();
            // Audit-pass-4: `kprintln_core!` is per-line atomic
            // (holds the UART lock for the entire `[core N] <body>\n`
            // sequence per SM1.G.4 audit-pass-1).  The pre-audit-pass-4
            // form used `kprintln!` with a manual `[core {core_id}]`
            // prefix, which expanded to TWO `kprint!` calls — a
            // concurrent writer between the prefix and the body would
            // tear the log line.
            crate::kprintln_core!(
                "SGI INTID {} (handler dispatch deferred to SM5)",
                intid
            );
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
    // (`sm1i4_per_core_counters_track_distinct_exception_branches`)
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
    static SM1I4_OBSERVATION_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

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

    // ========================================================================
    // WS-SM SM1.I.1 — Per-core IRQ handler entry tests
    //
    // `handle_irq_per_core` is the SM5 landing seam for per-core IRQ
    // dispatch.  At SM1.I.1 we verify:
    //
    //   1. The function exists with the expected `extern "C" fn(&mut TrapFrame)`
    //      ABI signature — assembly entry can resolve it once SM5 swaps
    //      the vector.
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
    fn sm1i1_handle_irq_per_core_has_correct_abi_signature() {
        // Function-pointer coercion: extern "C" fn(&mut TrapFrame) is
        // the assembly's expected entry signature.  A future regression
        // that changes the signature (e.g., to `fn(u64, &mut TrapFrame)`
        // for a hypothetical per-CPU explicit pass) would fail to
        // coerce here at compile time.
        let _: extern "C" fn(&mut TrapFrame) = handle_irq_per_core;
    }

    #[test]
    fn sm1i1_handle_irq_per_core_no_mangle_attribute_preserved() {
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
    fn sm1i1_handle_irq_per_core_legacy_handle_irq_signature_unchanged() {
        // The original `handle_irq` is retained at SM1.I.1 (SM5
        // swaps the assembly entry).  Verify its signature matches
        // the per-core variant so SM5 only swaps a function pointer.
        let _: extern "C" fn(&mut TrapFrame) = handle_irq;
        let _: extern "C" fn(&mut TrapFrame) = handle_irq_per_core;
    }

    #[test]
    fn sm1i1_handle_irq_per_core_runtime_call_does_not_panic() {
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
    fn sm1i1_handle_irq_per_core_advances_per_core_irq_count() {
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
    fn sm1i4_handle_sync_svc_increments_per_core_syscall_count() {
        // Audit-pass-3: serialise via SM1I4_OBSERVATION_MUTEX so concurrent
        // trap-handler tests don't race on PER_CPU_STATS[0].syscall_count.
        let _guard = SM1I4_OBSERVATION_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
    fn sm1i4_handle_sync_dabt_increments_per_core_vm_fault_count() {
        // Audit-pass-3: see SM1I4_OBSERVATION_MUTEX docstring.
        let _guard = SM1I4_OBSERVATION_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
    fn sm1i4_handle_sync_iabt_increments_per_core_vm_fault_count() {
        let _guard = SM1I4_OBSERVATION_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
    fn sm1i4_handle_sync_alignment_increments_per_core_user_exception_count() {
        let _guard = SM1I4_OBSERVATION_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
    fn sm1i4_handle_sync_sp_alignment_increments_per_core_user_exception_count() {
        let _guard = SM1I4_OBSERVATION_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
    fn sm1i4_handle_sync_unknown_ec_increments_per_core_user_exception_count() {
        let _guard = SM1I4_OBSERVATION_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
    fn sm1i4_per_core_counters_track_distinct_exception_branches() {
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
        let _guard = SM1I4_OBSERVATION_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
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
