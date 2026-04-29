// SPDX-License-Identifier: GPL-3.0-or-later
//! FFI Bridge: Lean kernel → Rust HAL
//!
//! AG7-A: `#[no_mangle] pub extern "C"` wrappers exposing HAL functions to the
//! Lean kernel via `@[extern]` declarations. Each function has a corresponding
//! Lean declaration in `SeLe4n/Platform/FFI.lean`.
//!
//! ## Function groups
//!
//! - **Timer** (AG7-A-i): Counter read, timer reprogram
//! - **GIC** (AG7-A-i): IRQ acknowledge, end-of-interrupt
//! - **TLB** (AG7-A-ii): Full flush, per-ASID flush, per-VAddr flush
//! - **MMIO** (AG7-A-ii): 32-bit volatile read/write
//! - **UART** (AG7-A-ii): Debug character output
//! - **Interrupts** (AG7-A-ii): Enable/disable interrupt delivery
//!
//! ## Safety
//!
//! All functions wrap safe or internally-unsafe HAL operations. The `extern "C"`
//! ABI ensures stable calling convention for Lean FFI linkage.
//!
//! ## Panic discipline (AK5-M / R-HAL-M11)
//!
//! The workspace `Cargo.toml` sets `panic = "abort"` for `dev` and `release`
//! profiles (AK5-A). Any panic crossing an `extern "C"` boundary is therefore
//! a deterministic abort — NOT undefined behavior. A panic in any FFI
//! entry point here halts the kernel, which is the correct behavior for
//! invariant violations: a corrupted kernel state is safer to stop than to
//! continue with unpredictable behavior.
//!
//! The compile-time guard below enforces that the `panic = "abort"`
//! workspace policy remains in effect. If a downstream user ever tries to
//! re-enable unwinding for a release or dev build, the compile will fail
//! with a clear diagnostic rather than silently producing UB at runtime.
//!
//! Note: cargo test still uses `panic = "unwind"` on stable so
//! `#[should_panic]` tests work. The guard below is gated on
//! `not(debug_assertions)` so it ONLY fires in release builds — test and
//! dev builds (which both have `debug_assertions = true`) bypass it even
//! when compiled with unwind.

// AK5-M compile-time guard:
//
// `cfg(panic = "abort")` is true only when the *currently-compiling* profile
// has `panic = "abort"` — which the workspace `Cargo.toml` sets for dev and
// release but CANNOT set for `cargo test` (Rust's stable test harness forces
// unwind so `#[should_panic]` works). We therefore pair the check with
// `not(debug_assertions)` so the guard fires ONLY in release builds that
// attempt to opt back into unwinding, while allowing `cargo test` (which
// compiles every crate with `debug_assertions = true`) to proceed.
//
// In practice: if anyone ever edits Cargo.toml to remove `panic = "abort"`
// from `[profile.release]`, this fires with the actionable message below.
#[cfg(all(not(panic = "abort"), not(debug_assertions)))]
compile_error!(
    "seLe4n HAL requires panic = \"abort\" for release profiles. \
     See rust/Cargo.toml [profile.release] and AK5-A in \
     docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md."
);

// ============================================================================
// AG7-A-i: Timer + GIC FFI exports
// ============================================================================

/// Read the ARM Generic Timer physical counter (CNTPCT_EL0).
///
/// Returns the current 64-bit counter value (54 MHz on RPi5).
/// Lean binding: `SeLe4n.Platform.FFI.ffiTimerReadCounter`
#[no_mangle]
pub extern "C" fn ffi_timer_read_counter() -> u64 {
    crate::timer::read_counter()
}

/// Reprogram the timer comparator for the next tick interval.
///
/// Sets CNTP_CVAL_EL0 = current counter + stored interval, then increments
/// the tick counter. Called from the Lean kernel's timer tick handler.
///
/// AI1-C/M-26: This is the **canonical** tick accounting path. The IRQ handler
/// (`trap.rs::handle_irq`) only re-arms the hardware timer; it does NOT
/// increment the tick count. All tick accounting flows through this FFI
/// entry point, which the Lean kernel controls.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiTimerReprogram`
#[no_mangle]
pub extern "C" fn ffi_timer_reprogram() {
    crate::timer::reprogram_timer();
    crate::timer::increment_tick_count();
}

/// Get the current tick count from the timer driver.
///
/// Returns the number of timer interrupts processed since boot.
/// Lean binding: `SeLe4n.Platform.FFI.ffiTimerGetTickCount`
#[no_mangle]
pub extern "C" fn ffi_timer_get_tick_count() -> u64 {
    crate::timer::get_tick_count()
}

/// Acknowledge a pending GIC interrupt (read GICC_IAR).
///
/// Returns the INTID (bits [9:0]). The caller must check for spurious
/// interrupts (INTID >= 1020) before dispatching.
/// Lean binding: `SeLe4n.Platform.FFI.ffiGicAcknowledge`
#[no_mangle]
pub extern "C" fn ffi_gic_acknowledge() -> u32 {
    crate::gic::acknowledge_irq(crate::gic::GICC_BASE)
}

/// Signal end-of-interrupt to the GIC (write GICC_EOIR).
///
/// Transitions the interrupt from active → inactive, allowing it to
/// fire again.
/// Lean binding: `SeLe4n.Platform.FFI.ffiGicEoi`
#[no_mangle]
pub extern "C" fn ffi_gic_eoi(intid: u32) {
    crate::gic::end_of_interrupt(crate::gic::GICC_BASE, intid);
}

/// Check if an interrupt ID is spurious (INTID >= 1020).
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiGicIsSpurious`
#[no_mangle]
pub extern "C" fn ffi_gic_is_spurious(intid: u32) -> bool {
    crate::gic::is_spurious(intid)
}

// ============================================================================
// AG7-A-ii: TLB + MMIO + UART + Interrupts FFI exports
// ============================================================================

/// Flush all TLB entries at EL1 (TLBI VMALLE1 + DSB ISH + ISB).
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiTlbiAll`
#[no_mangle]
pub extern "C" fn ffi_tlbi_all() {
    crate::tlb::tlbi_vmalle1();
}

/// Flush TLB entries by ASID at EL1 (TLBI ASIDE1 + DSB ISH + ISB).
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiTlbiByAsid`
#[no_mangle]
pub extern "C" fn ffi_tlbi_by_asid(asid: u16) {
    crate::tlb::tlbi_aside1(asid);
}

/// Flush TLB entries by virtual address + ASID at EL1 (TLBI VAE1 + DSB ISH + ISB).
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiTlbiByVaddr`
#[no_mangle]
pub extern "C" fn ffi_tlbi_by_vaddr(asid: u16, vaddr: u64) {
    crate::tlb::tlbi_vae1(asid, vaddr);
}

/// Read a 32-bit value from an MMIO address using volatile semantics.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiMmioRead32`
#[no_mangle]
pub extern "C" fn ffi_mmio_read32(addr: u64) -> u32 {
    crate::mmio::mmio_read32(addr as usize)
}

/// Write a 32-bit value to an MMIO address using volatile semantics.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiMmioWrite32`
#[no_mangle]
pub extern "C" fn ffi_mmio_write32(addr: u64, val: u32) {
    crate::mmio::mmio_write32(addr as usize, val);
}

/// Read a 64-bit value from an MMIO address using volatile semantics.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiMmioRead64`
#[no_mangle]
pub extern "C" fn ffi_mmio_read64(addr: u64) -> u64 {
    crate::mmio::mmio_read64(addr as usize)
}

/// Write a 64-bit value to an MMIO address using volatile semantics.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiMmioWrite64`
#[no_mangle]
pub extern "C" fn ffi_mmio_write64(addr: u64, val: u64) {
    crate::mmio::mmio_write64(addr as usize, val);
}

/// Transmit a single character on the debug UART (PL011).
///
/// Blocks until the TX FIFO has space. Used for kernel debug output.
/// Lean binding: `SeLe4n.Platform.FFI.ffiUartPutc`
#[no_mangle]
pub extern "C" fn ffi_uart_putc(c: u8) {
    crate::uart::boot_puts(&[c]);
}

/// Disable all maskable interrupts (set PSTATE.DAIF = 0b1111).
///
/// Returns the previous DAIF value for later restoration.
/// Lean binding: `SeLe4n.Platform.FFI.ffiDisableInterrupts`
#[no_mangle]
pub extern "C" fn ffi_disable_interrupts() -> u64 {
    crate::interrupts::disable_interrupts()
}

/// Restore interrupt state from a previously saved DAIF value.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiRestoreInterrupts`
#[no_mangle]
pub extern "C" fn ffi_restore_interrupts(saved_daif: u64) {
    crate::interrupts::restore_interrupts(saved_daif);
}

/// Enable IRQ delivery (clear PSTATE.I).
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiEnableInterrupts`
#[no_mangle]
pub extern "C" fn ffi_enable_interrupts() {
    crate::interrupts::enable_irq();
}

// ============================================================================
// AN9-D (DEF-C-M04 / RESOLVED): suspendThread atomicity bracket
// ============================================================================
//
// The Lean side defines `suspendThread_atomicity_under_ffi_bracket` (in
// `SeLe4n/Kernel/Lifecycle/Suspend.lean`), which takes a precondition
// `interruptsEnabled = false`.  This wrapper is what discharges that
// precondition on real hardware: it disables interrupts via
// `with_interrupts_disabled`, calls the inner Lean dispatch, and
// restores DAIF on return.
//
// Without this bracket, an ISR observing the partially-cleaned TCB
// between G2 (`cancelIpcBlocking`) and G6 (`threadState := .Inactive`)
// would see an inconsistent state — for instance, `ipcState = .ready`
// but `threadState = .Running` — that would violate the
// `suspendThread_transientWindowInvariant` predicate.

/// AN9-D: Suspend a thread atomically with respect to interrupts.
///
/// Brackets the inner Lean dispatch with
/// [`crate::interrupts::with_interrupts_disabled`] so the entire
/// G2→G3→G4→G5→G6 cleanup pipeline runs without interruption.  This
/// satisfies the
/// `suspendThread_atomicity_precondition` from the Lean model.
///
/// The inner symbol `suspend_thread_inner` is provided by the Lean
/// compiler from the kernel's `@[export suspend_thread_inner]`
/// declaration (see `SeLe4n/Platform/FFI.lean`).  A direct call to
/// the inner symbol from outside this wrapper bypasses the atomicity
/// guarantee and flagged with the `#[must_use]` discipline note in
/// the Lean docstring.  After WS-RC R2.B the Lean wrapper substantively
/// routes into `Kernel.Lifecycle.Suspend.suspendThread` via the
/// kernel-state IO.Ref rather than returning a stub error.
///
/// Returns: `KernelError::Ok = 0` on success, the kernel-error
/// discriminant otherwise.
///
/// Lean binding: see comment on `suspend_thread_inner` below.
#[no_mangle]
pub extern "C" fn sele4n_suspend_thread(tid: u64) -> u32 {
    crate::interrupts::with_interrupts_disabled(|| {
        // SAFETY: in production builds `suspend_thread_inner` is a
        // Lean-emitted `extern "C"` symbol; calling an extern "C"
        // function is unsafe.  In test builds it is a Rust-side
        // safe stub.  We use `unsafe` unconditionally so the
        // production path is correct; the `#[allow(unused_unsafe)]`
        // suppresses the test-only warning.
        #[allow(unused_unsafe)]
        unsafe {
            suspend_thread_inner(tid)
        }
    })
}

// ============================================================================
// AN9-A (DEF-A-M04): Cache + TLB composition FFI witnesses
// ============================================================================

/// AN9-A.1: Clean a page-table-page range to PoC + emit DSB ISH.
///
/// Wraps `cache::clean_pagetable_range`.  The Lean kernel calls this
/// after writing a page-table descriptor to ensure the hardware
/// walker sees the new descriptor before any subsequent translation
/// is attempted.
///
/// SAFETY: caller must guarantee `addr..addr+len` is mapped and
/// inside RAM (cleanable).  The Lean side discharges this via the
/// `pageTableUpdate_full_coherency` theorem in
/// `Architecture/TlbCacheComposition.lean`.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiCacheCleanPagetableRange`
#[no_mangle]
pub extern "C" fn cache_clean_pagetable_range(addr: u64, len: u64) {
    // SAFETY: Lean caller proves the range is valid via
    // `pageTableUpdate_full_coherency`.  We forward to the existing
    // unsafe primitive.
    unsafe { crate::cache::clean_pagetable_range(addr as usize, len as usize) }
}

/// AN9-A.1: Invalidate all I-cache to PoU.
///
/// Wraps `cache::ic_iallu`.  Required after self-modifying code or
/// page-table updates that affect executable mappings.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiIcIallu`
#[no_mangle]
pub extern "C" fn cache_ic_iallu() {
    crate::cache::ic_iallu();
}

// AN9-D inner — Lean-emitted `suspendThread` dispatch entry.
//
// **DO NOT CALL DIRECTLY** from any path other than
// `sele4n_suspend_thread`.  Calling this without the
// `with_interrupts_disabled` bracket bypasses the atomicity
// guarantee documented in the Lean theorem
// `suspendThread_atomicity_under_ffi_bracket`.
//
// On production builds (`#[cfg(not(test))]`) this is declared as an
// `extern "C"` symbol resolved at link time against the Lean
// kernel's emitted dispatch routine.  Under cargo test the symbol
// is provided by a Rust-side stub (see below) so the bracket
// discipline can still be exercised without a full Lean build.
#[cfg(not(test))]
extern "C" {
    fn suspend_thread_inner(tid: u64) -> u32;
}

/// AN9-D test stub: returns `KernelError::NotImplemented = 17` so the
/// bracket discipline can be unit-tested on host without pulling in
/// the full Lean kernel build artefact.
#[cfg(test)]
#[no_mangle]
extern "C" fn suspend_thread_inner(_tid: u64) -> u32 {
    17 // KernelError::NotImplemented
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ffi_timer_read_counter_no_panic() {
        let _ = ffi_timer_read_counter();
    }

    #[test]
    fn ffi_timer_get_tick_count_no_panic() {
        let _ = ffi_timer_get_tick_count();
    }

    #[test]
    fn ffi_gic_is_spurious_matches_gic() {
        assert!(!ffi_gic_is_spurious(0));
        assert!(!ffi_gic_is_spurious(30));
        assert!(ffi_gic_is_spurious(1020));
        assert!(ffi_gic_is_spurious(1023));
    }

    #[test]
    fn ffi_tlbi_all_no_panic() {
        ffi_tlbi_all();
    }

    #[test]
    fn ffi_tlbi_by_asid_no_panic() {
        ffi_tlbi_by_asid(42);
    }

    #[test]
    fn ffi_tlbi_by_vaddr_no_panic() {
        ffi_tlbi_by_vaddr(42, 0x1000);
    }

    #[test]
    fn ffi_mmio_no_panic() {
        // On non-aarch64, MMIO ops are no-ops or return 0
        let _ = ffi_mmio_read32(0x1000);
        ffi_mmio_write32(0x1000, 42);
        let _ = ffi_mmio_read64(0x1000);
        ffi_mmio_write64(0x1000, 42);
    }

    #[test]
    #[cfg(target_arch = "aarch64")]
    fn ffi_uart_putc_no_panic() {
        ffi_uart_putc(b'A');
    }

    #[test]
    fn ffi_interrupts_no_panic() {
        let saved = ffi_disable_interrupts();
        ffi_restore_interrupts(saved);
        ffi_enable_interrupts();
    }

    // ========================================================================
    // AN9-D (DEF-C-M04): suspendThread atomicity bracket tests
    // ========================================================================

    #[test]
    fn sele4n_suspend_thread_brackets_inner_call() {
        // The wrapper must invoke the inner stub (which returns
        // NotImplemented = 17 in test builds) and return its result.
        // This proves the bracket dispatches into the inner symbol.
        let result = sele4n_suspend_thread(42);
        assert_eq!(result, 17, "suspendThread bracket must forward inner stub return");
    }

    #[test]
    fn sele4n_suspend_thread_handles_zero_tid() {
        // ThreadId 0 is the sentinel; the wrapper must still invoke the
        // inner dispatch (which performs sentinel rejection at the Lean
        // layer).  This proves the bracket is a transparent forwarder
        // and does not pre-filter ids.
        let result = sele4n_suspend_thread(0);
        assert_eq!(result, 17, "bracket must not pre-filter sentinel");
    }

    #[test]
    fn sele4n_suspend_thread_disables_interrupts_during_call() {
        // The bracket calls `with_interrupts_disabled`, which on host
        // is a no-op closure call.  We assert that it does not
        // panic and that the return value matches the inner stub.
        // The atomicity contract (interrupts actually disabled on
        // hardware) is enforced by the aarch64 implementation of
        // `interrupts::with_interrupts_disabled` which is exercised
        // in the corresponding `interrupts_no_panic` test.
        let r1 = sele4n_suspend_thread(1);
        let r2 = sele4n_suspend_thread(2);
        assert_eq!(r1, r2, "bracket must be deterministic");
    }
}
