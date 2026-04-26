// SPDX-License-Identifier: GPL-3.0-or-later
//! Interrupt management primitives for ARMv8-A.
//!
//! Provides critical section support via DAIF register manipulation.
//! AG5-G: Interrupt-disabled region enforcement for kernel atomicity.
//!
//! ## DAIF Register (ARM ARM C5.2.5)
//!
//! PSTATE.DAIF controls masking of four exception types:
//! - D (bit 9): Debug exceptions
//! - A (bit 8): SError (asynchronous abort)
//! - I (bit 7): IRQ
//! - F (bit 6): FIQ
//!
//! On ARM64, exception entry automatically sets PSTATE.I (masks IRQ).
//! The kernel runs with IRQ masked throughout; this module provides
//! explicit control for the few paths that may need to re-enable.

/// Disable all maskable interrupts (D, A, I, F).
///
/// Sets PSTATE.DAIF = 0b1111 (all masked) via DAIFSet.
/// Returns the previous DAIF value for later restoration.
///
/// ARM ARM C5.2.5: DAIFSet is a write-only register that sets DAIF bits.
///
/// # AN8-E (R-HAL-L5): DAIF read-before-mask rationale
///
/// The DAIF read **must** happen before the DAIFSet write so we capture
/// the *pre-mask* state. Reading after the write would always return
/// `0b1111`, defeating the saved-and-restore semantics needed by nested
/// critical sections. This ordering is observable on ARM64 because
/// `mrs daif` and `msr daifset` are two separate instructions; the
/// compiler cannot reorder them across the function boundary because
/// both sides are `volatile` inline asm with `nomem` markers. The
/// `preserves_flags` option on the `daifset` write is correct because
/// DAIFSet does not touch NZCV.
#[inline(always)]
pub fn disable_interrupts() -> u64 {
    let saved = crate::read_sysreg!("daif");
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DAIFSet is a write-only register that masks interrupts.
        // Setting bits only increases masking — never unsafe. The #0xF
        // immediate sets all four DAIF bits. (ARM ARM C5.2.5)
        unsafe {
            core::arch::asm!("msr daifset, #0xf", options(nomem, nostack, preserves_flags));
        }
    }
    saved
}

/// Restore interrupt state from a previously saved DAIF value.
///
/// This correctly handles nested critical sections: if interrupts were
/// already disabled before the outer `disable_interrupts()`, restoring
/// the saved value keeps them disabled.
///
/// ARM ARM C5.2.5: Direct write to DAIF restores the full mask state.
#[inline(always)]
pub fn restore_interrupts(saved_daif: u64) {
    crate::write_sysreg!("daif", saved_daif);
}

/// Enable IRQ interrupts only (clear PSTATE.I, keep D/A/F unchanged).
///
/// ARM ARM C5.2.5: DAIFClr is a write-only register that clears DAIF bits.
/// Bit 1 in the immediate corresponds to IRQ (bit I in DAIF).
#[inline(always)]
pub fn enable_irq() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: DAIFClr clears interrupt mask bits. Clearing I enables IRQ
        // delivery. This is safe to call at EL1 when the GIC and vector table
        // are properly configured. (ARM ARM C5.2.5)
        unsafe {
            core::arch::asm!("msr daifclr, #0x2", options(nomem, nostack, preserves_flags));
        }
    }
}

/// Execute a closure with all interrupts disabled.
///
/// Saves the current DAIF state, masks all interrupts, executes the
/// closure, then restores the original DAIF state. This correctly
/// handles nesting: if interrupts were already disabled, they remain
/// disabled after the closure returns.
///
/// # Usage
///
/// ```no_run
/// # use sele4n_hal::interrupts::with_interrupts_disabled;
/// # fn do_atomic_work() -> u64 { 42 }
/// let result = with_interrupts_disabled(|| {
///     // Critical section: scheduler transitions, PIP propagation,
///     // endpoint queue mutations, donation chain operations.
///     do_atomic_work()
/// });
/// assert_eq!(result, 42);
/// ```
#[inline(always)]
pub fn with_interrupts_disabled<F: FnOnce() -> R, R>(f: F) -> R {
    let saved = disable_interrupts();
    let result = f();
    restore_interrupts(saved);
    result
}

/// Check if IRQ interrupts are currently enabled.
///
/// Returns `true` if PSTATE.I = 0 (IRQ not masked).
#[inline(always)]
pub fn are_interrupts_enabled() -> bool {
    let daif = crate::read_sysreg!("daif");
    // Bit 7 is the I (IRQ) mask bit; 0 means enabled
    (daif & (1 << 7)) == 0
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn with_interrupts_disabled_returns_value() {
        let result = with_interrupts_disabled(|| 42);
        assert_eq!(result, 42);
    }

    #[test]
    fn with_interrupts_disabled_nesting() {
        // Nested critical sections should work correctly
        let result = with_interrupts_disabled(|| {
            with_interrupts_disabled(|| 99)
        });
        assert_eq!(result, 99);
    }

    #[test]
    fn disable_interrupts_returns_saved_state() {
        // On non-aarch64, read_sysreg returns 0
        let saved = disable_interrupts();
        restore_interrupts(saved);
        // Should not panic
    }

    #[test]
    fn are_interrupts_enabled_on_host() {
        // On non-aarch64, DAIF reads as 0 → IRQ bit is 0 → enabled
        #[cfg(not(target_arch = "aarch64"))]
        assert!(are_interrupts_enabled());
    }
}
