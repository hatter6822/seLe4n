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
     See rust/Cargo.toml [profile.release] and AK5-A in the \
     WS-AN AN9 portfolio (closed at v0.30.11; see docs/WORKSTREAM_HISTORY.md)."
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
/// **Local (non-broadcast) variant**.  Reserved for the boot-time
/// MMU-init path BEFORE secondaries have started; production
/// kernel code under SMP must use [`ffi_tlbi_for_sharing`] to
/// route through the IS or OS variant per the platform's
/// `SharingDomain`.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiTlbiAll`
#[no_mangle]
pub extern "C" fn ffi_tlbi_all() {
    crate::tlb::tlbi_vmalle1();
}

/// Flush TLB entries by ASID at EL1 (TLBI ASIDE1 + DSB ISH + ISB).
///
/// **Local (non-broadcast) variant**.  See [`ffi_tlbi_all`] for
/// SMP usage notes.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiTlbiByAsid`
#[no_mangle]
pub extern "C" fn ffi_tlbi_by_asid(asid: u16) {
    crate::tlb::tlbi_aside1(asid);
}

/// Flush TLB entries by virtual address + ASID at EL1 (TLBI VAE1 + DSB ISH + ISB).
///
/// **Local (non-broadcast) variant**.  See [`ffi_tlbi_all`] for
/// SMP usage notes.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiTlbiByVaddr`
#[no_mangle]
pub extern "C" fn ffi_tlbi_by_vaddr(asid: u16, vaddr: u64) {
    crate::tlb::tlbi_vae1(asid, vaddr);
}

// ============================================================================
// WS-SM SM1.E.4 — Sharing-domain-routed TLBI FFI exports
// ============================================================================
//
// The Lean kernel calls these FFI exports through the typed
// `Architecture.tlbiForSharing` wrapper, which encodes the
// (SharingDomain, TlbInvalidation) pair as a tag + operand pair
// suitable for C-callable transmission.
//
// Discriminant encoding (matches `SeLe4n.Kernel.Architecture` Lean
// wrapper; pinned by `tests/SmpFoundationsSuite.lean` runtime checks):
//
//   domain_tag : 0 = Inner, 1 = Outer
//   op_tag     : 0 = Vmalle1, 1 = Vae1, 2 = Aside1, 3 = Vale1
//   asid       : 16-bit ASID (RES0 for Vmalle1)
//   vaddr      : page-aligned VA (RES0 for Vmalle1, Aside1)
//
// **Fail-closed contract**: unknown tags PANIC rather than silently
// falling back.  Audit-pass-1 reasoning: the FFI is a security
// boundary; silent fallbacks (e.g., "unknown op → no-op") create
// silent correctness violations because the caller assumed the TLB
// was invalidated.  Per the project's `panic = "abort"` release
// profile, the panic halts the kernel — the correct response to a
// corrupted FFI ABI call.  A well-formed Lean caller using
// `Architecture.tlbiForSharing` cannot reach the panic arm because
// the tag-encoding theorems (`SharingDomain.toTag_in_range`,
// `TlbInvalidation.toOpTag_in_range`) prove every emitted tag is
// in-range at the Lean type level.
//
// The decoder helpers below are factored out as `Option`-returning
// pure functions so unit tests can verify their behaviour (including
// the failure paths) without crossing the FFI boundary, which Rust
// edition 2021 treats as `non-unwinding panic. aborting.` even
// under the test profile.

/// **WS-SM SM1.E.4 audit-pass-1**: Decode an FFI `domain_tag` into a
/// typed `SharingDomain`, returning `None` on out-of-range input.
///
/// This is the testable inner form of the FFI dispatcher's first
/// stage.  Calling `ffi_tlbi_for_sharing(2, _, _, _)` would panic
/// (the FFI wrapper does `match decode_sharing_domain_tag(tag) {
/// Some => use, None => panic! }`); calling
/// `decode_sharing_domain_tag(2)` directly returns `None` cleanly
/// so tests can exercise the rejection path without crashing the
/// test runner (panic-across-`extern "C"` is `non-unwinding panic.
/// aborting.` under Rust edition 2021).
#[inline]
const fn decode_sharing_domain_tag(tag: u32) -> Option<crate::tlb::SharingDomain> {
    match tag {
        0 => Some(crate::tlb::SharingDomain::Inner),
        1 => Some(crate::tlb::SharingDomain::Outer),
        _ => None,
    }
}

/// **WS-SM SM1.E.4 audit-pass-1**: Decode an FFI `(op_tag, asid, vaddr)`
/// triple into a typed `TlbInvalidation`, returning `None` on
/// out-of-range `op_tag`.
///
/// Testable inner form of the FFI dispatcher's second stage.  See
/// `decode_sharing_domain_tag` for the rationale.
///
/// The unused operands for each variant are simply ignored: the
/// resulting `TlbInvalidation::Vmalle1` (op_tag=0) discards both
/// `asid` and `vaddr`; `Aside1` discards `vaddr`.  This matches the
/// Lean-side `TlbInvalidation.toAsid` / `toVaddr` semantics which
/// return `0` for unused fields.
#[inline]
const fn decode_tlb_invalidation_tag(
    op_tag: u32,
    asid: u16,
    vaddr: u64,
) -> Option<crate::tlb::TlbInvalidation> {
    match op_tag {
        0 => Some(crate::tlb::TlbInvalidation::Vmalle1),
        1 => Some(crate::tlb::TlbInvalidation::Vae1 { asid, vaddr }),
        2 => Some(crate::tlb::TlbInvalidation::Aside1 { asid }),
        3 => Some(crate::tlb::TlbInvalidation::Vale1 { asid, vaddr }),
        _ => None,
    }
}

/// **WS-SM SM1.E.4**: Sharing-domain-routed TLBI dispatcher FFI export.
///
/// Routes the Lean-side `Architecture.tlbiForSharing` call to one of
/// the eight IS/OS TLBI variants based on `domain_tag` and `op_tag`.
/// See the module-level comment above for the discriminant encoding.
///
/// `asid` and `vaddr` are consumed only by the variants that need them;
/// `Vmalle1` ignores both, `Aside1` ignores `vaddr`.  The Lean caller
/// passes `0` for unused fields.
///
/// # Panics
///
/// Panics (which under `panic = "abort"` aborts the kernel) if either
/// `domain_tag >= 2` or `op_tag >= 4`.  Both bounds are structurally
/// guaranteed by the Lean-side typed `Architecture.tlbiForSharing`
/// wrapper via `SharingDomain.toTag_in_range` and
/// `TlbInvalidation.toOpTag_in_range`, so a well-formed Lean caller
/// never trips them — the panics are defense-in-depth against FFI
/// ABI corruption.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiTlbiForSharing`
#[no_mangle]
pub extern "C" fn ffi_tlbi_for_sharing(
    domain_tag: u32,
    op_tag: u32,
    asid: u16,
    vaddr: u64,
) {
    // Audit-pass-1: fail-closed on unknown tags.  Silent fallback
    // (the pre-audit behaviour) violated the kernel's correctness
    // contract — the caller assumed the TLB was invalidated.
    let domain = match decode_sharing_domain_tag(domain_tag) {
        Some(d) => d,
        None => panic!(
            "WS-SM SM1.E.4: ffi_tlbi_for_sharing: domain_tag must be \
             0 (Inner) or 1 (Outer), got {}",
            domain_tag
        ),
    };
    let op = match decode_tlb_invalidation_tag(op_tag, asid, vaddr) {
        Some(o) => o,
        None => panic!(
            "WS-SM SM1.E.4: ffi_tlbi_for_sharing: op_tag must be 0..=3 \
             (Vmalle1=0, Vae1=1, Aside1=2, Vale1=3), got {}",
            op_tag
        ),
    };
    crate::tlb::tlbi_for_sharing(domain, op);
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
// WS-SM SM1.F.6 — SGI primitive FFI exports
// ============================================================================
//
// Three send-SGI variants exposed to Lean.  Each forwards directly to
// the corresponding `gic::send_sgi*` primitive.  All three emit
// `dsb ish` BEFORE the GICD_SGIR write per SM1.F.8 / ARM ARM B2.7.5,
// so prior kernel-state writes are observable on every IS-domain PE
// before the SGI fires on the receiver.

/// **WS-SM SM1.F.6**: Send an SGI to one or more target CPU
/// interfaces by explicit bitmask.
///
/// `target_mask` — 8-bit bitmask of target CPU interfaces (bit i =
/// CPU i).  On RPi5 only bits 0..3 are meaningful.
/// `intid` — SGI INTID (`0..15`).
///
/// Forwards to [`crate::gic::send_sgi`], inheriting the panic-on-
/// out-of-range-INTID contract.  Panics here cross the FFI boundary
/// as a clean abort under `panic = "abort"` (production) or unwind
/// (test); both halt the kernel rather than corrupt the GIC.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiSendSgi`
#[no_mangle]
pub extern "C" fn ffi_send_sgi(target_mask: u8, intid: u8) {
    crate::gic::send_sgi(target_mask, intid);
}

/// **WS-SM SM1.F.6**: Send an SGI to the calling core only.
///
/// `intid` — SGI INTID (`0..15`).
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiSendSgiToSelf`
#[no_mangle]
pub extern "C" fn ffi_send_sgi_to_self(intid: u8) {
    crate::gic::send_sgi_to_self(intid);
}

/// **WS-SM SM1.F.6**: Send an SGI to all cores except the caller.
///
/// `intid` — SGI INTID (`0..15`).
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiSendSgiToAllButSelf`
#[no_mangle]
pub extern "C" fn ffi_send_sgi_to_all_but_self(intid: u8) {
    crate::gic::send_sgi_to_all_but_self(intid);
}

// ============================================================================
// WS-SM SM1.B.5 (closes SMP-M4): per-CPU core-id FFI export
// ============================================================================

/// **WS-SM SM1.B.5**: return the calling core's id, read from
/// `TPIDR_EL1` on aarch64.
///
/// Routes through `per_cpu::current_core_id_from_tpidr` so the
/// Lean kernel can identify which core it is running on without
/// reading MPIDR + masking.  The Lean side wraps the raw `u64`
/// return in a typed `CoreId = Fin numCores` via the
/// `Concurrency.currentCoreId : BaseIO CoreId` definition; that
/// wrapper performs the `core_id < numCores` range check (which
/// always succeeds under the post-boot invariants enforced by
/// `check_per_cpu_invariants`).
///
/// **Range invariant**: the returned value satisfies
/// `result < PlatformBinding.coreCount`.  On aarch64 this is enforced
/// by `check_per_cpu_invariants()` (verifying every slot's `core_id`
/// matches its array index, where the index is itself
/// `< MAX_SECONDARY_CORES + 1 = coreCount`).  On host the function
/// returns 0 deterministically.
///
/// Lean binding: `SeLe4n.Platform.FFI.ffiCurrentCoreId`.
#[no_mangle]
pub extern "C" fn ffi_current_core_id() -> u64 {
    crate::per_cpu::current_core_id_from_tpidr()
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

    // ========================================================================
    // WS-SM SM1.B.5 — ffi_current_core_id export tests
    // ========================================================================

    #[test]
    fn ffi_current_core_id_returns_zero_on_host() {
        // SM1.B.5: on host the FFI export returns 0 because
        // `current_core_id_from_tpidr` reads from
        // `PER_CPU_DATA[0].core_id` = 0.  Asserting equality (not
        // just `<`) makes the host stub's behaviour explicit so a
        // future regression that breaks the stub surfaces here.
        assert_eq!(ffi_current_core_id(), 0);
    }

    #[test]
    fn ffi_current_core_id_in_range() {
        // SM1.B.5: the returned core_id must satisfy
        // `core_id < PlatformBinding.coreCount`.  The Lean wrapper
        // (`Concurrency.currentCoreId`) re-checks this to recover
        // a typed `Fin numCores`; a regression that returned an
        // out-of-range value would panic at the Lean side, but we
        // double-check on the Rust side too.
        let id = ffi_current_core_id();
        assert!(
            (id as usize) < crate::per_cpu::PER_CPU_DATA.len(),
            "ffi_current_core_id() = {} ≥ coreCount = {}",
            id,
            crate::per_cpu::PER_CPU_DATA.len()
        );
    }

    #[test]
    fn ffi_current_core_id_matches_per_cpu_accessor() {
        // SM1.B.5: the FFI export must agree with the underlying
        // `current_core_id_from_tpidr` accessor.  This catches a
        // future regression where one is updated but not the other.
        assert_eq!(
            ffi_current_core_id(),
            crate::per_cpu::current_core_id_from_tpidr()
        );
    }

    // ========================================================================
    // WS-SM SM1.E.4 — `ffi_tlbi_for_sharing` dispatcher tests
    //
    // The dispatcher routes the (domain_tag, op_tag, asid, vaddr) tuple
    // to one of the eight underlying IS/OS TLBI variants.  Tests
    // exercise every combination + the defensive fallback for
    // unrecognised tags.
    // ========================================================================

    #[test]
    fn sm1e4_ffi_tlbi_for_sharing_inner_vmalle1_no_panic() {
        // (Inner, Vmalle1) → tlbi_vmalle1is via the dispatcher.
        ffi_tlbi_for_sharing(0, 0, 0, 0);
    }

    #[test]
    fn sm1e4_ffi_tlbi_for_sharing_outer_vmalle1_no_panic() {
        // (Outer, Vmalle1) → tlbi_vmalle1os via the dispatcher.
        ffi_tlbi_for_sharing(1, 0, 0, 0);
    }

    #[test]
    fn sm1e4_ffi_tlbi_for_sharing_inner_vae1_no_panic() {
        ffi_tlbi_for_sharing(0, 1, 42, 0x1000);
    }

    #[test]
    fn sm1e4_ffi_tlbi_for_sharing_outer_vae1_no_panic() {
        ffi_tlbi_for_sharing(1, 1, 42, 0x1000);
    }

    #[test]
    fn sm1e4_ffi_tlbi_for_sharing_inner_aside1_no_panic() {
        ffi_tlbi_for_sharing(0, 2, 7, 0);
    }

    #[test]
    fn sm1e4_ffi_tlbi_for_sharing_outer_aside1_no_panic() {
        ffi_tlbi_for_sharing(1, 2, 7, 0);
    }

    #[test]
    fn sm1e4_ffi_tlbi_for_sharing_inner_vale1_no_panic() {
        ffi_tlbi_for_sharing(0, 3, 3, 0x4000);
    }

    #[test]
    fn sm1e4_ffi_tlbi_for_sharing_outer_vale1_no_panic() {
        ffi_tlbi_for_sharing(1, 3, 3, 0x4000);
    }

    // ----------------------------------------------------------------
    // SM1.E.4 audit-pass-1: fail-closed contract for unknown tags.
    //
    // The pre-audit `ffi_tlbi_for_sharing` had silent fallbacks for
    // unknown domain_tag (→ Inner) and op_tag (→ no-op).  Both were
    // unsafe: the caller assumed the TLB was invalidated, but the
    // fallbacks silently changed the broadcast scope (Inner on a
    // multi-cluster topology leaves stale translations on other
    // clusters) or skipped the invalidation entirely.
    //
    // The post-audit dispatcher panics on out-of-range tags (fails
    // closed under `panic = "abort"`).  The panic itself cannot be
    // exercised here because Rust edition 2021 treats panic-across-
    // `extern "C"` as `non-unwinding panic. aborting.` — the test
    // process would abort with SIGABRT.
    //
    // Instead we test the FACTORED-OUT decoder helpers
    // (`decode_sharing_domain_tag`, `decode_tlb_invalidation_tag`)
    // which return `Option` and can be exercised cleanly.  The FFI
    // wrapper's `match ... { Some => use, None => panic!() }`
    // pattern means decoder coverage is a faithful proxy for FFI
    // coverage.

    #[test]
    fn sm1e4_decode_sharing_domain_tag_accepts_0_and_1() {
        // Audit-pass-1: the only valid tags are 0 (Inner) and 1 (Outer).
        assert_eq!(
            decode_sharing_domain_tag(0),
            Some(crate::tlb::SharingDomain::Inner)
        );
        assert_eq!(
            decode_sharing_domain_tag(1),
            Some(crate::tlb::SharingDomain::Outer)
        );
    }

    #[test]
    fn sm1e4_decode_sharing_domain_tag_rejects_out_of_range() {
        // Audit-pass-1: every other value rejects via None.  The FFI
        // wrapper translates None into a panic that aborts the kernel.
        assert_eq!(decode_sharing_domain_tag(2), None);
        assert_eq!(decode_sharing_domain_tag(3), None);
        assert_eq!(decode_sharing_domain_tag(99), None);
        assert_eq!(decode_sharing_domain_tag(u32::MAX), None);
    }

    #[test]
    fn sm1e4_decode_sharing_domain_tag_const_callable() {
        // Audit-pass-1: decoder is `const fn` so call sites with
        // literal arguments evaluate at compile time.
        const D0: Option<crate::tlb::SharingDomain> = decode_sharing_domain_tag(0);
        const D2: Option<crate::tlb::SharingDomain> = decode_sharing_domain_tag(2);
        assert_eq!(D0, Some(crate::tlb::SharingDomain::Inner));
        assert_eq!(D2, None);
    }

    #[test]
    fn sm1e4_decode_tlb_invalidation_tag_accepts_0_to_3() {
        // Audit-pass-1: the four valid op_tags map to typed variants.
        assert_eq!(
            decode_tlb_invalidation_tag(0, 0, 0),
            Some(crate::tlb::TlbInvalidation::Vmalle1)
        );
        assert_eq!(
            decode_tlb_invalidation_tag(1, 42, 0x1000),
            Some(crate::tlb::TlbInvalidation::Vae1 { asid: 42, vaddr: 0x1000 })
        );
        assert_eq!(
            decode_tlb_invalidation_tag(2, 7, 0),
            Some(crate::tlb::TlbInvalidation::Aside1 { asid: 7 })
        );
        assert_eq!(
            decode_tlb_invalidation_tag(3, 3, 0x4000),
            Some(crate::tlb::TlbInvalidation::Vale1 { asid: 3, vaddr: 0x4000 })
        );
    }

    #[test]
    fn sm1e4_decode_tlb_invalidation_tag_rejects_out_of_range() {
        // Audit-pass-1: any tag >= 4 returns None.  The FFI wrapper
        // translates None into a panic.
        assert_eq!(decode_tlb_invalidation_tag(4, 0, 0), None);
        assert_eq!(decode_tlb_invalidation_tag(5, 0, 0), None);
        assert_eq!(decode_tlb_invalidation_tag(99, 0, 0), None);
        assert_eq!(decode_tlb_invalidation_tag(u32::MAX, 0, 0), None);
    }

    #[test]
    fn sm1e4_decode_tlb_invalidation_tag_const_callable() {
        // Audit-pass-1: decoder is `const fn`.
        const OP_VMALLE1: Option<crate::tlb::TlbInvalidation> =
            decode_tlb_invalidation_tag(0, 0, 0);
        const OP_BAD: Option<crate::tlb::TlbInvalidation> =
            decode_tlb_invalidation_tag(4, 0, 0);
        assert_eq!(OP_VMALLE1, Some(crate::tlb::TlbInvalidation::Vmalle1));
        assert_eq!(OP_BAD, None);
    }

    #[test]
    fn sm1e4_decode_tlb_invalidation_tag_vmalle1_discards_operands() {
        // Audit-pass-1: Vmalle1 (op_tag=0) ignores asid and vaddr.
        // Verify the variant is identical regardless of operand inputs.
        let with_zeros = decode_tlb_invalidation_tag(0, 0, 0);
        let with_data = decode_tlb_invalidation_tag(0, 0xFFFF, 0xDEAD_BEEF);
        assert_eq!(with_zeros, Some(crate::tlb::TlbInvalidation::Vmalle1));
        assert_eq!(with_data, Some(crate::tlb::TlbInvalidation::Vmalle1));
        assert_eq!(with_zeros, with_data);
    }

    #[test]
    fn sm1e4_decode_tlb_invalidation_tag_aside1_discards_vaddr() {
        // Audit-pass-1: Aside1 (op_tag=2) carries asid but ignores vaddr.
        let with_zero = decode_tlb_invalidation_tag(2, 5, 0);
        let with_data = decode_tlb_invalidation_tag(2, 5, 0xDEAD_BEEF);
        assert_eq!(with_zero, Some(crate::tlb::TlbInvalidation::Aside1 { asid: 5 }));
        assert_eq!(with_data, Some(crate::tlb::TlbInvalidation::Aside1 { asid: 5 }));
        assert_eq!(with_zero, with_data);
    }

    #[test]
    fn sm1e4_decode_signature_pins() {
        // Audit-pass-1: pin decoder signatures so a future refactor
        // (e.g., changing Option to Result) breaks compilation here.
        let _: fn(u32) -> Option<crate::tlb::SharingDomain> = decode_sharing_domain_tag;
        let _: fn(u32, u16, u64) -> Option<crate::tlb::TlbInvalidation> =
            decode_tlb_invalidation_tag;
    }

    #[test]
    fn sm1e4_ffi_tlbi_for_sharing_signature_pin() {
        // Pin the FFI signature.  A future ABI change would break
        // every Lean caller — pinning here surfaces the regression
        // at compile time.
        let _: extern "C" fn(u32, u32, u16, u64) = ffi_tlbi_for_sharing;
    }

    #[test]
    fn sm1e4_ffi_tlbi_for_sharing_combinatorial_coverage() {
        // SM1.E.4: cover every valid (domain, op) combination in one
        // tight loop.  This is the structural witness that the
        // dispatcher's match expression is exhaustive over the
        // documented tag range.
        for domain_tag in [0u32, 1] {
            for op_tag in [0u32, 1, 2, 3] {
                ffi_tlbi_for_sharing(domain_tag, op_tag, 1, 0x1000);
            }
        }
    }

    // ========================================================================
    // WS-SM SM1.F.6 — SGI primitive FFI export tests
    // ========================================================================

    #[test]
    fn sm1f6_ffi_send_sgi_no_panic_on_host() {
        // Host stub: GICD_SGIR write is a no-op via mmio_write32;
        // verify the FFI boundary doesn't panic.
        ffi_send_sgi(0x0F, 0); // INTID 0 (reschedule) to all cores
        ffi_send_sgi(0x01, 4); // INTID 4 (haltAll) to CPU 0 only
    }

    #[test]
    fn sm1f6_ffi_send_sgi_to_self_no_panic_on_host() {
        ffi_send_sgi_to_self(1); // INTID 1 (tlbShootdownReq)
    }

    #[test]
    fn sm1f6_ffi_send_sgi_to_all_but_self_no_panic_on_host() {
        ffi_send_sgi_to_all_but_self(2); // INTID 2 (tlbShootdownAck)
    }

    // ----------------------------------------------------------------
    // SM1.F.6: out-of-range INTID rejection.
    //
    // The FFI exports forward to `gic::send_sgi*` which panics on
    // INTID >= 16.  We do NOT exercise the panic via #[should_panic]
    // here because Rust's behaviour on panic across an `extern "C"`
    // boundary is `non-unwinding panic. aborting.` even under the
    // test profile (the `extern "C"` ABI does not support unwind by
    // default at edition 2021).
    //
    // The bound enforcement is tested via the underlying
    // `gic::tests::sm1f{2,3,4}_send_sgi*_panics_on_intid_16` tests
    // which exercise the panic at the safe Rust call site, before
    // the FFI boundary is crossed.  We pin the FFI signature here
    // and rely on the underlying gic test suite for the bound proof.

    #[test]
    fn sm1f6_ffi_send_sgi_signature_pin() {
        // Pin every FFI export's signature.
        let _: extern "C" fn(u8, u8) = ffi_send_sgi;
        let _: extern "C" fn(u8) = ffi_send_sgi_to_self;
        let _: extern "C" fn(u8) = ffi_send_sgi_to_all_but_self;
    }

    #[test]
    fn sm1f6_ffi_send_sgi_covers_every_kernel_reserved_intid() {
        // SM0.H reserves SGI INTIDs 0..4 for kernel coordination.
        // Verify every reserved INTID is callable through the FFI.
        for intid in 0..5u8 {
            ffi_send_sgi(0x0F, intid);
            ffi_send_sgi_to_self(intid);
            ffi_send_sgi_to_all_but_self(intid);
        }
    }
}
