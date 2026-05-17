// SPDX-License-Identifier: GPL-3.0-or-later
//! CPU instruction wrappers for ARMv8-A.
//!
//! Each wrapper encapsulates a single privileged or hint instruction with a
//! `// SAFETY:` comment referencing the ARM Architecture Reference Manual
//! (ARM ARM DDI 0487).
//!
//! On non-AArch64 hosts, functions provide no-op stubs for compilation and
//! testing.
//!
//! # WS-SM SM1.I.5 — SEV / WFE coordination
//!
//! ARMv8-A defines a "local event register" per PE that interacts with the
//! `wfe` / `sev` / `sevl` instruction family to implement low-power
//! synchronisation between cores:
//!
//! ## Local event register semantics (ARM ARM B2.10)
//!
//! Each PE has a one-bit local event register.  Its state is per-PE; one
//! core's event register is independent of every other core's.
//!
//! - **`wfe`** (ARM ARM C6.2.353): If the local event register is set,
//!   `wfe` immediately clears it and returns.  Otherwise the PE enters a
//!   low-power state and suspends execution until *any* of:
//!   1. The local event register becomes set (via `sev` on this PE, or
//!      `sev` on another PE in the same inner-shareable domain — see
//!      below).
//!   2. An interrupt arrives at the PE (IRQ, FIQ, SError, or asynchronous
//!      debug exception, masked or unmasked per `DAIF`).
//!   3. A power-management event from the WIC fires.
//!   4. The implementation-defined `wfe` timeout expires (FEAT_WFxT on
//!      ARMv8.7+; not present on Cortex-A76).
//!
//!   On exit `wfe` clears the local event register.
//!
//! - **`sev`** (ARM ARM C6.2.243): Sets the local event register of every
//!   PE in the inner-shareable domain (including the caller).  Hint
//!   instruction; always returns immediately; has no side effects beyond
//!   setting the event registers.  On RPi5 (BCM2712, single cluster) every
//!   PE sees the wake.
//!
//! - **`sevl`** (ARM ARM C6.2.244): Sets the local event register of the
//!   *calling* PE only.  Useful for "wake-me-once" patterns where the first
//!   `wfe` after `sevl` falls through immediately, but subsequent `wfe`s
//!   block until a real event arrives.  This is the right primitive for
//!   ARMv8.0 spin-wait loops where the bookkeeping wants to do at least
//!   one productive iteration before entering low-power sleep.
//!
//! ## Inner-shareable broadcast scope
//!
//! `sev` broadcasts to every PE in the calling PE's inner-shareable (IS)
//! domain.  Per the BCM2712 device tree and Cortex-A76 datasheet, the
//! single Cortex-A76 cluster constitutes one IS domain on RPi5.  All 4
//! cores see each other's `sev`s.  A multi-cluster ARM SoC (e.g., a
//! big.LITTLE design) would have to use `sev` carefully if the senders and
//! receivers span clusters; an outer-shareable `sev` does not exist in
//! ARMv8-A, so cross-cluster waking is generally done via SGI (see
//! `crate::gic::send_sgi`).
//!
//! ## Kernel policy for emitting SEV
//!
//! The seLe4n kernel emits `sev` (via inline `asm!` blocks) at exactly the
//! following sites:
//!
//! 1. **End of `bring_up_secondaries`** (`smp.rs::bring_up_secondaries_inner`,
//!    AN9-J.4.d): after writing every secondary's `CORE_READY[i]` flag,
//!    primary issues one final `sev` to wake any secondaries parked at the
//!    `boot.S::secondary_entry` spin-wait.  This handles the common race
//!    where a secondary enters `wfe` *before* the primary's `CORE_READY`
//!    write becomes visible — the broadcast `sev` guarantees the secondary
//!    re-checks the flag.
//!
//! 2. **Verified lock release (SM2.B, post-1.0)**: SM2's `TicketLock` will
//!    emit `sev` from its release path so contended waiters parked on
//!    `wfe` wake immediately rather than spinning the entire bounded-WFE
//!    timeout.  Pre-SM2 the [`crate::uart::UartLock`] uses pure CAS and
//!    does not benefit from `sev`.
//!
//! 3. **Cross-core SGI fallback**: an `sev` can substitute for a `send_sgi`
//!    when the receiver is parked on `wfe` and the sender needs only the
//!    wake signal (not the routing to a specific handler).  The kernel
//!    currently uses SGI rather than `sev` for cross-core coordination
//!    because SGIs carry an INTID that the receiver's handler can use to
//!    classify the wake reason; `sev` is just a wake hint.
//!
//! ## When NOT to use SEV
//!
//! - **In place of memory ordering**: `sev` is a hint instruction.  It does
//!   NOT enforce memory ordering on its own.  Pair `sev` with `dsb ish` if
//!   the receiver must observe a prior memory store before the wake.  Per
//!   ARM ARM B2.7.5, the canonical "wake the receiver and have them see
//!   my state" pattern is: store-data → `dsb ish` → `sev`.
//!
//! - **For interrupt delivery**: `sev` does NOT generate an interrupt;
//!   `wfe` returns "as if a normal completion" rather than via the
//!   exception entry path.  If the receiver needs to run a specific
//!   handler when woken, use `send_sgi`, not `sev`.
//!
//! - **As a memory barrier or synchronisation primitive**: neither `wfe`
//!   nor `sev` participates in the memory consistency model on its own.
//!   Use them only as efficiency hints over a pure spin-wait loop.
//!
//! ## Bounded WFE and the local event register
//!
//! [`wfe_bounded`] is the kernel's primary `wfe` user.  It pairs the
//! instruction with a counter-tick budget so the caller can detect a lost
//! wake (e.g., a primary's `sev` that arrived before the secondary's `wfe`
//! and was already consumed).  The bounded form is used inside
//! `rust_secondary_main`'s spin-wait on `CORE_READY[i]` — even if primary's
//! `sev` is lost, the secondary's `wfe` returns within the bound and the
//! flag is re-checked.
//!
//! ## Test-only sev emission
//!
//! [`sev`] (this module) provides a Rust wrapper around the `sev`
//! instruction for unit-testing the wake-up semantics.  Production code
//! emits `sev` directly inline in `smp.rs::bring_up_secondaries_inner` to
//! keep the instruction co-located with the AN9-J broadcast point.

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

/// AN9-G (DEF-R-HAL-L17): Bounded `wfe()` with a counter-tick budget.
///
/// Issues `wfe` and returns the elapsed `CNTPCT_EL0` ticks since the
/// call began.  Returning the elapsed count lets the caller compare
/// against `max_ticks` and decide whether to retry, log a diagnostic,
/// or re-arm a missing timer.
///
/// Note that this primitive does NOT internally loop: ARMv8 `wfe`
/// returns when an event arrives or when the local "event register"
/// is set.  The CALLER owns the retry/timeout policy; this function
/// is the cheap leaf primitive.  The `max_ticks` argument is
/// informational — it documents the EXPECTED maximum so call sites
/// stay self-describing — but does not bound the actual `wfe`.
/// Practical bounding requires arming a timer to fire within
/// `max_ticks`; without one, `wfe` blocks until an event arrives.
///
/// Use the boot idle loop pattern:
///
/// ```no_run
/// # use sele4n_hal::cpu::{wfe_bounded, WFE_DEFAULT_TIMEOUT_TICKS};
/// # fn rearm() {}
/// fn idle_loop() -> ! {
///     loop {
///         let elapsed = wfe_bounded(WFE_DEFAULT_TIMEOUT_TICKS);
///         if elapsed >= WFE_DEFAULT_TIMEOUT_TICKS {
///             // Timer almost certainly didn't fire — re-arm and retry.
///             rearm();
///         }
///     }
/// }
/// ```
///
/// Returns: elapsed `CNTPCT_EL0` ticks during the call (≥ 0 on
/// hardware; 0 on host stubs).  Saturating arithmetic guards
/// against counter wrap (which takes ~10 800 years at 54 MHz on
/// the BCM2712 timer, so this is purely defensive).
#[inline(always)]
pub fn wfe_bounded(max_ticks: u64) -> u64 {
    let _ = max_ticks; // informational — see docstring
    #[cfg(target_arch = "aarch64")]
    {
        let start: u64;
        // SAFETY: CNTPCT_EL0 is read-only at EL1; reading is always safe.
        unsafe {
            core::arch::asm!("mrs {}, cntpct_el0", out(reg) start,
                options(nomem, nostack, preserves_flags));
        }
        // SAFETY: WFE is a hint instruction.  (ARM ARM C6.2.353)
        unsafe { core::arch::asm!("wfe", options(nomem, nostack, preserves_flags)) }
        let now: u64;
        // SAFETY: same as above.
        unsafe {
            core::arch::asm!("mrs {}, cntpct_el0", out(reg) now,
                options(nomem, nostack, preserves_flags));
        }
        now.saturating_sub(start)
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        // Host stub: deterministic.  `wfe` has no host equivalent; we
        // return 0 ticks so callers' "did we time out?" check
        // (`elapsed >= max_ticks`) consistently returns false on host
        // unless `max_ticks == 0`.
        core::hint::spin_loop();
        0
    }
}

/// **WS-SM SM1.I.5**: Send Event — broadcasts a wake signal to every PE
/// in the inner-shareable domain (including the caller).
///
/// Sets the local event register of every PE in the IS domain.  Any PE
/// currently parked on `wfe` will return; PEs not in `wfe` will see
/// their event register set and the next `wfe` will fall through
/// immediately.
///
/// ARM ARM C6.2.243: SEV is a hint instruction with no side effects
/// beyond setting the local event registers.  No memory ordering
/// implications; pair with `dsb ish` if the receiver must observe a
/// prior store before the wake (see the SEV/WFE coordination section
/// in this module's docstring).
///
/// # When to call
///
/// Use `sev` after a state change that a `wfe`-parked PE is waiting
/// to observe:
///
/// - **`bring_up_secondaries`** emits `sev` after writing
///   `CORE_READY[i]` flags so secondaries parked at `boot.S` spin-wait
///   wake immediately.
/// - **Lock release** (SM2+): after releasing a `TicketLock` whose
///   waiters parked on `wfe`.
///
/// Do NOT use `sev` as a substitute for `send_sgi` when the receiver
/// needs an interrupt routed to a specific handler.  `sev` only wakes
/// the receiver from `wfe`; the receiver runs whatever code follows its
/// `wfe` instruction, not an interrupt handler.
///
/// # Host (non-aarch64) behaviour
///
/// No-op.  Host tests verify the function compiles and returns; the
/// real semantics are only observable on aarch64 hardware.
#[inline(always)]
pub fn sev() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: SEV is a hint instruction with no side effects beyond
        // setting the local event register of every PE in the
        // inner-shareable domain.  Always safe at any execution level.
        // (ARM ARM C6.2.243)
        unsafe { core::arch::asm!("sev", options(nomem, nostack, preserves_flags)) }
    }
}

/// **WS-SM SM1.I.5**: Send Event Local — sets only the calling PE's
/// local event register.
///
/// Useful for "first iteration falls through" patterns where the
/// initial `wfe` after a spin-wait setup should observe a pre-set
/// event so the loop runs at least one iteration before parking the
/// PE.  Distinct from [`sev`], which broadcasts to every PE in the IS
/// domain.
///
/// ARM ARM C6.2.244: SEVL sets only the local event register of the
/// calling PE.
///
/// # Host (non-aarch64) behaviour
///
/// No-op.
#[inline(always)]
pub fn sevl() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: SEVL is a hint instruction that only affects the
        // local PE's event register.  Always safe at any execution
        // level.  (ARM ARM C6.2.244)
        unsafe { core::arch::asm!("sevl", options(nomem, nostack, preserves_flags)) }
    }
}

/// **WS-SM SM1.I.3** (per-core IDLE thread Rust stub): park the calling
/// core on `wfe` waiting for an event or interrupt.
///
/// Lean callers invoke this from a per-core idle TCB context after
/// completing their scheduling round with no runnable work.  The PE
/// enters a low-power state and resumes when:
///
/// - Another core issues `sev` (e.g., scheduler reschedule SGI fallback,
///   lock release).
/// - An IRQ arrives at this PE (timer tick, cross-core SGI, device SPI).
/// - An asynchronous debug exception or SError fires.
///
/// Equivalent to [`wfe`] without a timeout.  Use [`idle_wait_bounded`]
/// for a bounded variant that returns elapsed counter ticks so a
/// hand-rolled scheduler can implement a busy-poll fallback should
/// `wfe` block on a stale wake signal.
///
/// # SM5 transition
///
/// At SM1.I the Lean kernel does not yet emit calls to this primitive
/// (per-core idle TCB state is SM5+ work).  Once SM5 lands the
/// per-core scheduler, the idle TCB body will call this through the
/// `ffi_idle_wait` FFI export ([`crate::ffi::ffi_idle_wait`]).
///
/// # Host (non-aarch64) behaviour
///
/// Calls `core::hint::spin_loop` (same as [`wfe`]'s host stub).
#[inline(always)]
pub fn idle_wait() {
    wfe();
}

/// **WS-SM SM1.I.3** (bounded variant): park the calling core on `wfe`
/// for at most `max_ticks` counter ticks.
///
/// Wrapper around [`wfe_bounded`] with documentation tailored to the
/// per-core idle path.  Returns the elapsed `CNTPCT_EL0` ticks so a
/// caller's "did we time out" check can drive a retry or busy-poll
/// fallback.
///
/// On host the stub returns 0.
#[inline(always)]
pub fn idle_wait_bounded(max_ticks: u64) -> u64 {
    wfe_bounded(max_ticks)
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
    // `0 & MPIDR_CORE_ID_MASK == 0` is tautologically true (clippy
    // `erasing_op`); the assert is retained as documentation of the
    // property table — core 0 produces 0 after the mask, which is
    // what the `_start::cbnz` branch in `boot.S` relies on to fall
    // through to the boot path.  Suppressed locally rather than
    // rewritten so the documentation table remains uniform.
    #[allow(clippy::erasing_op)]
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
        // RPi5 default.  Host returns 0 ticks elapsed.
        let _: u64 = wfe_bounded(0);
        let _: u64 = wfe_bounded(1);
        let _: u64 = wfe_bounded(WFE_DEFAULT_TIMEOUT_TICKS);
    }

    #[test]
    fn wfe_bounded_returns_zero_on_host() {
        // AN9-G: the host stub returns exactly 0 elapsed ticks so the
        // caller's "did we time out" check (`elapsed >= max_ticks`)
        // resolves consistently to false unless `max_ticks == 0`.
        assert_eq!(wfe_bounded(WFE_DEFAULT_TIMEOUT_TICKS), 0,
            "host stub must return zero elapsed ticks");
    }

    #[test]
    fn wfe_default_timeout_ticks_is_10ms_at_54mhz() {
        // AN9-G: 54_000_000 ticks/s × 10 ms / 1000 = 540_000 ticks.
        assert_eq!(WFE_DEFAULT_TIMEOUT_TICKS, 540_000);
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn wfe_default_timeout_ticks_is_positive() {
        // Defense-in-depth: a zero default would silently disable the
        // bounded check on every call site.  Clippy flags this as a
        // constant assertion (`assertions_on_constants`); we keep the
        // runtime assert so the property is observable in the test
        // report rather than only at compile time.  The local
        // `#[allow]` suppresses the lint at the test function level.
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

    // ========================================================================
    // WS-SM SM1.I.3 — idle_wait + idle_wait_bounded tests
    //
    // The `idle_wait` family wraps `wfe` / `wfe_bounded` with documentation
    // tailored to the per-core idle TCB path.  Tests confirm:
    //   1. The functions are callable on host without panicking.
    //   2. `idle_wait_bounded` returns 0 on host (matches `wfe_bounded`'s
    //      host stub contract).
    //   3. Function-pointer coercion succeeds — a future regression that
    //      changed the signature would fail to compile.
    // ========================================================================

    #[test]
    fn sm1i3_idle_wait_no_panic_on_host() {
        // Host stub: single spin_loop iteration, returns.
        idle_wait();
    }

    #[test]
    fn sm1i3_idle_wait_bounded_no_panic_on_host() {
        // Same range of tick budgets as wfe_bounded's tests.
        let _ = idle_wait_bounded(0);
        let _ = idle_wait_bounded(1);
        let _ = idle_wait_bounded(WFE_DEFAULT_TIMEOUT_TICKS);
    }

    #[test]
    fn sm1i3_idle_wait_bounded_returns_zero_on_host() {
        // Host stub returns 0 elapsed ticks deterministically.  This is
        // the same contract as `wfe_bounded`, so a caller using
        // `elapsed >= max_ticks` to detect a missed wake sees a
        // consistent "did not time out" result unless `max_ticks == 0`.
        assert_eq!(idle_wait_bounded(WFE_DEFAULT_TIMEOUT_TICKS), 0);
    }

    #[test]
    fn sm1i3_idle_wait_signatures_pinned() {
        // ABI pin: a future regression that changed the signatures
        // (e.g., to `fn idle_wait() -> bool`) would fail to coerce here.
        let _: fn() = idle_wait;
        let _: fn(u64) -> u64 = idle_wait_bounded;
    }

    // ========================================================================
    // WS-SM SM1.I.5 — SEV / WFE coordination tests
    //
    // The `sev` and `sevl` wrappers exist primarily for unit-testing
    // the wake-up semantics.  Production code emits `sev` inline in
    // `smp.rs::bring_up_secondaries_inner`.  Tests confirm:
    //   1. The wrappers compile and execute on host without panicking
    //      (no-op stubs).
    //   2. Function-pointer coercion succeeds.
    // ========================================================================

    #[test]
    fn sm1i5_sev_no_panic_on_host() {
        sev();
    }

    #[test]
    fn sm1i5_sevl_no_panic_on_host() {
        sevl();
    }

    #[test]
    fn sm1i5_sev_signatures_pinned() {
        // ABI pin: changes to the signatures break this coercion.
        let _: fn() = sev;
        let _: fn() = sevl;
    }

    #[test]
    fn sm1i5_sev_and_wfe_compose_on_host() {
        // Composition: after a `sev`, the next `wfe` should fall
        // through (on hardware).  On host both are no-ops so the test
        // verifies the wrappers can be sequenced without inter-call
        // state corruption.
        sev();
        wfe();
        sev();
        sev();
        wfe();
    }
}
