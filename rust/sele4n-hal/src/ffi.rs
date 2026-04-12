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
}
