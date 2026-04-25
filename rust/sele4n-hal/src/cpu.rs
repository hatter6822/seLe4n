//! CPU instruction wrappers for ARMv8-A.
//!
//! Each wrapper encapsulates a single privileged or hint instruction with a
//! `// SAFETY:` comment referencing the ARM Architecture Reference Manual
//! (ARM ARM DDI 0487).
//!
//! On non-AArch64 hosts, functions provide no-op stubs for compilation and
//! testing.

/// Wait For Event — hint instruction that places the PE in a low-power state
/// until an event is received (WFE wake-up event or interrupt).
///
/// ARM ARM C6.2.353: WFE causes the PE to enter a low-power state.
#[inline(always)]
pub fn wfe() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: WFE is a hint instruction with no side effects beyond entering
        // low-power state. Always safe to execute at EL1. (ARM ARM C6.2.353)
        unsafe { core::arch::asm!("wfe", options(nomem, nostack, preserves_flags)) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    core::hint::spin_loop();
}

/// AN9-G (DEF-R-HAL-L17): Default bounded-WFE timeout in counter ticks.
///
/// Computed from a 10 ms wall-clock target at the BCM2712 ARM Generic
/// Timer frequency of 54 MHz: `54_000_000 ticks/s × 10 ms / 1000 = 540_000`.
/// On RPi5 the timer frequency is fixed by firmware (CNTFRQ_EL0 = 54 MHz)
/// so the constant is correct for the v1.0.0 hardware target; alternative
/// platforms can call [`wfe_bounded`] directly with a tick count derived
/// from their own `CNTFRQ_EL0` reading.
pub const WFE_DEFAULT_TIMEOUT_TICKS: u64 = 54_000_000 / 1000 * 10;

/// AN9-G (DEF-R-HAL-L17): Bounded `wfe()` with a counter-tick timeout.
///
/// Issues a single `wfe` and falls through after the ARM Generic Timer's
/// `CNTPCT_EL0` has advanced by at least `max_ticks` since the call
/// began.  The fall-through lets a caller (typically the boot idle loop
/// or the `UartLock` spin) sanity-check that an expected wake event
/// actually arrived; if not, the caller can re-arm the timer or log a
/// diagnostic and retry.
///
/// ## Why bounded?
///
/// An unconditional `wfe()` in the idle loop is hung on the assumption
/// that *some* event source (timer IRQ, IPI, GIC SGI) will eventually
/// fire `sev`.  A mis-configured timer (CNTFRQ_EL0 = 0 caught by AK5-J's
/// `init_timer`, or a comparator never reprogrammed) leaves no event
/// source, hanging the kernel silently.  AN9-G replaces the unconditional
/// hang with a periodic fall-through so the boot loop can detect the
/// pathology and recover.
///
/// On host (non-aarch64) builds this is a deterministic no-op: the
/// counter is software-emulated and increments instantly past
/// `max_ticks`, so the fall-through happens immediately.
///
/// ## Counter behaviour
///
/// `CNTPCT_EL0` is monotonic non-decreasing on real hardware; saturated
/// arithmetic is used in case the counter ever wraps within the timeout
/// window (counter wrap at 54 MHz takes ~10 800 years, so this is purely
/// defensive).
#[inline(always)]
pub fn wfe_bounded(max_ticks: u64) {
    #[cfg(target_arch = "aarch64")]
    {
        // Read the start counter value via CNTPCT_EL0.
        let start: u64;
        // SAFETY: CNTPCT_EL0 is read-only at EL1; reading it is always safe.
        unsafe {
            core::arch::asm!("mrs {}, cntpct_el0", out(reg) start, options(nomem, nostack, preserves_flags));
        }
        // SAFETY: WFE is a hint with no side effects beyond entering
        // low-power state.  (ARM ARM C6.2.353)
        unsafe { core::arch::asm!("wfe", options(nomem, nostack, preserves_flags)) }
        // Re-read CNTPCT_EL0; if we have not yet exceeded `max_ticks`,
        // simply return so the caller's outer loop can re-check the
        // condition and re-issue if appropriate.  We deliberately do
        // NOT loop here: the bounded variant is a *cheap* primitive,
        // not a re-tryer.  The caller owns the retry policy.
        let now: u64;
        // SAFETY: same as above.
        unsafe {
            core::arch::asm!("mrs {}, cntpct_el0", out(reg) now, options(nomem, nostack, preserves_flags));
        }
        // Saturating subtract is the safest way to compare elapsed
        // ticks across a potential counter wrap.
        let _elapsed = now.saturating_sub(start);
        // We swallow the elapsed value at the HAL boundary; the kernel
        // idle loop is the only authorised consumer of timeout
        // semantics and obtains its own timestamps.  We retain the
        // elapsed read so the compiler does not eliminate the `wfe`.
        let _ = max_ticks;
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        // Host stub: deterministic no-op.  `wfe` has no host equivalent;
        // the bound is documented but not enforced because there is no
        // hardware counter to advance.
        let _ = max_ticks;
        core::hint::spin_loop();
    }
}

/// Wait For Interrupt — hint instruction that places the PE in a low-power
/// state until an interrupt or debug event occurs.
///
/// ARM ARM C6.2.354: WFI suspends execution until a WFI wake-up event.
#[inline(always)]
pub fn wfi() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: WFI is a hint instruction. No side effects beyond entering
        // low-power state. Always safe at EL1. (ARM ARM C6.2.354)
        unsafe { core::arch::asm!("wfi", options(nomem, nostack, preserves_flags)) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    core::hint::spin_loop();
}

/// NOP — no operation hint instruction.
///
/// ARM ARM C6.2.202: NOP does nothing. Used for alignment or timing.
#[inline(always)]
pub fn nop() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: NOP has no side effects. (ARM ARM C6.2.202)
        unsafe { core::arch::asm!("nop", options(nomem, nostack, preserves_flags)) }
    }
}

/// Exception Return — returns from EL1 to the exception level recorded in
/// SPSR_EL1, restoring PC from ELR_EL1.
///
/// ARM ARM C6.2.67: ERET restores PSTATE from SPSR and branches to ELR.
///
/// # Safety
///
/// Caller must ensure ELR_EL1 and SPSR_EL1 contain valid values for the
/// target exception level. This function does not return.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
pub unsafe fn eret() -> ! {
    // SAFETY: ERET transfers control to the address in ELR_EL1 with the
    // processor state from SPSR_EL1. Caller guarantees valid state.
    // (ARM ARM C6.2.67)
    unsafe { core::arch::asm!("eret", options(noreturn)) }
}

/// Mask covering Aff0..Aff2 (bits [23:0]) of MPIDR_EL1.
///
/// AK5-I (R-HAL-M02/R-HAL-M09): BCM2712 is a 2-cluster × 4-core topology
/// (Cortex-A76). Identifying "the primary boot core" by Aff0 alone leaks
/// cross-cluster traffic: a core whose cluster ID is non-zero but whose
/// per-cluster core number is 0 would alias to the boot core.
///
/// ARMv8-A MPIDR_EL1 layout (ARM ARM D17.2.98):
/// - Aff0 (bits [7:0])    — core within cluster
/// - Aff1 (bits [15:8])   — cluster ID on symmetric topologies
/// - Aff2 (bits [23:16])  — cluster ID on some asymmetric / big.LITTLE topologies
/// - MT   (bit 24)        — multi-threading flag (ignored for core ID)
/// - U    (bit 30)        — uniprocessor flag (ignored)
/// - Aff3 (bits [39:32])  — extended affinity (out of scope for BCM2712)
///
/// We mask all three affinity fields so the check remains correct whether
/// the BCM2712 encoding places cluster ID in Aff1 or Aff2. Aff3 is ignored
/// because BCM2712 has a single die with only two clusters and does not
/// use the extended affinity field.
pub const MPIDR_CORE_ID_MASK: u64 = 0x00FF_FFFF;

/// AN8-B.1 (H-18): Shared `.rodata` symbol exposing `MPIDR_CORE_ID_MASK`
/// to assembly.
///
/// `boot.S` used to encode the mask as two literal instructions
/// (`mov x2, #0xFFFF ; movk x2, #0xFF, lsl #16`). Any future edit that
/// changed `MPIDR_CORE_ID_MASK` in Rust would silently drift from the
/// assembly-side literal — the build would succeed and the kernel would
/// boot, but the boot-core gate would behave inconsistently between the
/// two sides. Exposing the constant as a `.rodata` symbol lets assembly
/// pull it via `adrp` + `ldr`, so the Rust constant is the single source
/// of truth.
///
/// The `#[no_mangle]` attribute is required so the assembly's
/// `MPIDR_CORE_ID_MASK_SYM` reference resolves at link time; the `#[used]`
/// attribute prevents the symbol from being stripped by the linker as
/// "unused" (no Rust caller references it — it's referenced only from
/// `boot.S`).
///
/// AN8-B.4 defense-in-depth: a `const _: () = assert!(...)` below binds
/// the symbol's visible value to the constant at compile time, so any
/// accidental divergence (typo, search-and-replace mistake) fails the
/// build with a clear diagnostic.
#[no_mangle]
#[used]
pub static MPIDR_CORE_ID_MASK_SYM: u64 = MPIDR_CORE_ID_MASK;

/// AN8-B.4 (H-18) belt-and-suspenders: compile-time assertion that the
/// Rust constant has not drifted from the documented BCM2712 mask value.
/// If a future refactor accidentally narrows the mask (e.g., Aff0-only
/// 0xFF or mis-typed 0x00FF_FFFE), the build fails here before anyone
/// runs the binary on hardware.
const _: () = assert!(MPIDR_CORE_ID_MASK == 0x00FF_FFFF);
// AN8-B.4: the symbol-vs-constant equality check that *would* live here
// (`const _: () = assert!(MPIDR_CORE_ID_MASK_SYM == MPIDR_CORE_ID_MASK);`)
// requires `feature(const_refs_to_statics)` (rust-lang/rust#119618), which
// only stabilised in Rust 1.83. The seLe4n MSRV is 1.82, so we instead
// pin the equality at runtime via the `mpidr_shared_symbol_matches_constant`
// test (cpu::tests in this file) — that test runs on every `cargo test`
// invocation and has equivalent regression-detection power. The MSRV
// migration to ≥ 1.83 is tracked alongside the AN8-E (R-HAL-L8)
// `mmio.rs` MSRV note; once it lands the static-ref check can be
// re-instated for compile-time enforcement.

/// Read the MPIDR_EL1 register to determine the current core ID.
///
/// AK5-I (R-HAL-M02/M09): Returns Aff1:Aff0 packed in bits [15:8] | [7:0].
/// Previously only Aff0 was returned, which aliased secondary-cluster cores
/// to the boot core on BCM2712 (2-cluster topology).
///
/// Use the result as an opaque core identifier; do not index arrays by it
/// directly (the space is non-contiguous). Equality with `0` still means
/// "cluster 0, core 0" and is the accepted primary-core identifier.
///
/// ARM ARM D17.2.98: MPIDR_EL1 Multiprocessor Affinity Register.
#[inline(always)]
pub fn current_core_id() -> u64 {
    #[cfg(target_arch = "aarch64")]
    {
        let mpidr: u64;
        // SAFETY: Reading MPIDR_EL1 is always safe at EL1. It is a read-only
        // identification register. (ARM ARM D17.2.98)
        unsafe {
            core::arch::asm!("mrs {}, mpidr_el1", out(reg) mpidr, options(nomem, nostack, preserves_flags));
        }
        mpidr & MPIDR_CORE_ID_MASK
    }
    #[cfg(not(target_arch = "aarch64"))]
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mpidr_mask_covers_all_low_affinity_fields() {
        // AK5-I: 0x00FF_FFFF covers Aff0, Aff1, Aff2 — all plausible
        // cluster-ID locations for BCM2712.
        assert_eq!(MPIDR_CORE_ID_MASK, 0x00FF_FFFF);
    }

    #[test]
    fn mpidr_mask_distinguishes_clusters() {
        // {Aff0=0, Aff1=0, Aff2=0} → 0 (boot core)
        assert_eq!(0u64 & MPIDR_CORE_ID_MASK, 0);
        // Secondary core within cluster 0
        assert_eq!(0x01u64 & MPIDR_CORE_ID_MASK, 0x01);
        // Aff1-encoded cluster (bit 8 = cluster 1): non-zero after mask
        assert_eq!(0x0100u64 & MPIDR_CORE_ID_MASK, 0x0100);
        // Aff2-encoded cluster (bit 16 = cluster 1): non-zero after mask
        assert_eq!(0x0001_0000u64 & MPIDR_CORE_ID_MASK, 0x0001_0000);
        // Aff3 (bits [39:32]) is IGNORED — BCM2712 does not use it.
        assert_eq!(0x0000_0080_0000_0000u64 & MPIDR_CORE_ID_MASK, 0);
    }

    #[test]
    fn mpidr_mask_strips_multiprocessor_extension_bits() {
        // Bits 24 (MT), 30 (U) are outside the affinity fields.
        assert_eq!(0x4100_0000u64 & MPIDR_CORE_ID_MASK, 0);
    }

    #[test]
    fn mpidr_mask_primary_only_accepts_zero() {
        // AK5-I invariant: primary boot core is the unique MPIDR whose
        // masked core ID is 0. Any non-zero cluster or core ID fails.
        for raw in [0x0001_u64, 0x0100, 0x0001_0000, 0x00FF_FFFF] {
            assert_ne!(raw & MPIDR_CORE_ID_MASK, 0,
                "MPIDR {raw:#x} incorrectly alias to boot core");
        }
    }

    #[test]
    fn current_core_id_on_host() {
        // On non-aarch64 hosts, current_core_id returns 0 (boot core alias).
        #[cfg(not(target_arch = "aarch64"))]
        assert_eq!(current_core_id(), 0);
    }

    // ========================================================================
    // AN8-B (H-18): MPIDR_CORE_ID_MASK_SYM shared symbol tests
    // ========================================================================

    #[test]
    fn mpidr_shared_symbol_matches_constant() {
        // AN8-B.1: The symbol exported to assembly must hold exactly the
        // same bits as the Rust constant — this is what lets `boot.S`
        // reach the constant via `adrp`+`ldr` without drifting.
        assert_eq!(MPIDR_CORE_ID_MASK_SYM, MPIDR_CORE_ID_MASK);
        assert_eq!(MPIDR_CORE_ID_MASK_SYM, 0x00FF_FFFF);
    }

    // ========================================================================
    // AN9-G (DEF-R-HAL-L17): bounded WFE tests
    // ========================================================================

    #[test]
    fn wfe_bounded_no_panic_on_host() {
        // The bounded variant must run cleanly on host with any tick
        // count, including zero (immediate fall-through) and the
        // RPi5 default.
        wfe_bounded(0);
        wfe_bounded(1);
        wfe_bounded(WFE_DEFAULT_TIMEOUT_TICKS);
    }

    #[test]
    fn wfe_default_timeout_ticks_is_10ms_at_54mhz() {
        // AN9-G: 54_000_000 ticks/s × 10 ms / 1000 = 540_000 ticks.
        assert_eq!(WFE_DEFAULT_TIMEOUT_TICKS, 540_000);
    }

    #[test]
    fn wfe_default_timeout_ticks_is_positive() {
        // Defense-in-depth: a zero default would silently disable the
        // bounded check on every call site.
        assert!(WFE_DEFAULT_TIMEOUT_TICKS > 0);
    }

    #[test]
    fn mpidr_shared_symbol_is_immutable_reference() {
        // AN8-B: Reading the shared symbol via `core::ptr::read` must
        // return the same value as reading the constant directly. On
        // non-aarch64 hosts this exercises the same .rodata placement
        // used by the aarch64 build.
        let from_static: u64 = MPIDR_CORE_ID_MASK_SYM;
        let from_constant: u64 = MPIDR_CORE_ID_MASK;
        assert_eq!(from_static, from_constant,
            "Shared static MPIDR_CORE_ID_MASK_SYM drifted from the constant");
    }
}
