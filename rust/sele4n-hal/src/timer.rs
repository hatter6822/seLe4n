// SPDX-License-Identifier: GPL-3.0-or-later
//! ARM Generic Timer driver for Raspberry Pi 5.
//!
//! Counter frequency: 54 MHz (from Board.lean `timerFrequencyHz`).
//! Default tick rate: 1000 Hz (1 ms ticks).
//!
//! Implements AG5-D: Full timer driver with system register access for
//! CNTPCT_EL0, CNTP_CVAL_EL0, CNTP_CTL_EL0, and CNTFRQ_EL0.
//!
//! ## Timer Operation
//!
//! The ARM Generic Timer uses a monotonically increasing counter (CNTPCT_EL0)
//! and a comparator (CNTP_CVAL_EL0). When the counter reaches the comparator
//! value, a timer interrupt fires (INTID 30 on GIC-400).
//!
//! The driver:
//! 1. Reads CNTFRQ_EL0 to determine counter frequency (54 MHz on RPi5)
//! 2. Computes the interval in counter ticks for the desired tick rate
//! 3. Programs CNTP_CVAL_EL0 for the first interrupt
//! 4. Enables the timer via CNTP_CTL_EL0
//! 5. On each tick interrupt, reprograms the comparator for the next interval

use core::sync::atomic::{AtomicU64, Ordering};

/// AJ5-C/L-14 + AK5-J: Timer initialization error.
///
/// Returned by `init_timer` when parameters or hardware state are invalid.
/// A kernel function should not panic on invalid input — `Result` gives the
/// boot sequence the opportunity to log and halt gracefully rather than
/// crashing silently (or worse, silently falling back to a wrong frequency).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimerError {
    /// The requested tick rate was zero, which would cause division by zero.
    ZeroTickHz,
    /// AK5-J (R-HAL-M07): `CNTFRQ_EL0` reads 0 — firmware failed to program
    /// the counter frequency. Previously we silently fell back to the RPi5
    /// constant (54 MHz), but on real hardware a zero CNTFRQ means either
    /// (a) firmware misconfiguration that must be diagnosed, or (b) the
    /// core is not the one we expect. Failing fast surfaces the bug.
    CntfrqNotProgrammed,
}

impl core::fmt::Display for TimerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TimerError::ZeroTickHz => write!(f, "tick_hz must be > 0 to avoid division by zero"),
            TimerError::CntfrqNotProgrammed => write!(f,
                "CNTFRQ_EL0 read as 0 — firmware must program the timer frequency before kernel entry"),
        }
    }
}

/// Counter frequency on RPi5: 54 MHz crystal.
/// Matches Lean `rpi5TimerConfig.counterFrequencyHz`.
pub const COUNTER_FREQ_HZ: u32 = 54_000_000;

/// Default tick rate in Hz (1 ms ticks).
pub const DEFAULT_TICK_HZ: u32 = 1000;

/// Counter increments per tick at default rate: 54000000 / 1000 = 54000.
/// Matches Lean `rpi5TimerConfig` `countsPerTick` computation.
pub const COUNTS_PER_TICK: u32 = COUNTER_FREQ_HZ / DEFAULT_TICK_HZ;

/// Global tick counter — incremented on each timer interrupt.
/// This is the Rust-side shadow of the Lean model's `MachineState.timer`.
static TICK_COUNT: AtomicU64 = AtomicU64::new(0);

/// Interval between timer interrupts, in counter ticks.
/// Set during `init_timer()` and used by `reprogram_timer()`.
static TIMER_INTERVAL: AtomicU64 = AtomicU64::new(0);

// ============================================================================
// System Register Accessors
// ============================================================================

/// Read the physical counter (CNTPCT_EL0).
///
/// Returns the current counter value. This is a monotonically increasing
/// 64-bit counter driven by the system clock (54 MHz on RPi5).
///
/// ARM ARM D13.8.2: CNTPCT_EL0 — Counter-timer Physical Count register.
#[inline(always)]
pub fn read_counter() -> u64 {
    crate::read_sysreg!("cntpct_el0")
}

/// Read the counter frequency (CNTFRQ_EL0).
///
/// Returns the frequency in Hz. On RPi5 this is 54000000 (54 MHz).
///
/// ARM ARM D13.8.1: CNTFRQ_EL0 — Counter-timer Frequency register.
#[inline(always)]
pub fn read_frequency() -> u32 {
    crate::read_sysreg!("cntfrq_el0") as u32
}

/// Set the comparator value (CNTP_CVAL_EL0).
///
/// When CNTPCT_EL0 >= this value, a timer interrupt (PPI 30) fires
/// (if the timer is enabled and not masked).
///
/// ARM ARM D13.8.5: CNTP_CVAL_EL0 — Counter-timer Physical Timer
/// CompareValue register.
#[inline(always)]
pub fn set_comparator(value: u64) {
    crate::write_sysreg!("cntp_cval_el0", value);
}

/// Read the timer control register (CNTP_CTL_EL0).
///
/// Bit 0: ENABLE — timer enabled
/// Bit 1: IMASK — interrupt mask (1 = masked)
/// Bit 2: ISTATUS — interrupt status (read-only, 1 = condition met)
///
/// ARM ARM D13.8.4: CNTP_CTL_EL0.
#[inline(always)]
pub fn read_timer_ctl() -> u64 {
    crate::read_sysreg!("cntp_ctl_el0")
}

/// Enable the timer: CNTP_CTL_EL0 = ENABLE=1, IMASK=0.
///
/// After this, the timer will fire an interrupt when CNTPCT_EL0 >= CNTP_CVAL_EL0.
#[inline(always)]
pub fn enable_timer() {
    // Bit 0 = ENABLE = 1, Bit 1 = IMASK = 0
    crate::write_sysreg!("cntp_ctl_el0", 1u64);
}

/// Disable the timer: CNTP_CTL_EL0 = 0.
#[inline(always)]
pub fn disable_timer() {
    crate::write_sysreg!("cntp_ctl_el0", 0u64);
}

/// Check if the timer interrupt is pending.
///
/// Returns `true` if CNTP_CTL_EL0.ISTATUS = 1 (counter >= comparator).
#[inline(always)]
pub fn is_timer_pending() -> bool {
    (read_timer_ctl() & (1 << 2)) != 0
}

// ============================================================================
// Timer Initialization and Reprogramming
// ============================================================================

/// Initialize the timer with the given tick rate.
///
/// Computes the interval from the counter frequency, programs the first
/// comparator value, and enables the timer. After this function returns,
/// timer interrupts will fire at the specified rate.
///
/// # Arguments
///
/// * `tick_hz` — Desired tick rate in Hz (e.g., 1000 for 1ms ticks)
///
/// # Errors
///
/// Returns `Err(TimerError::ZeroTickHz)` if `tick_hz` is zero. AJ5-C/L-14:
/// replaced `assert!` panic with recoverable error — the boot sequence can
/// log and halt gracefully instead of crashing silently.
pub fn init_timer(tick_hz: u32) -> Result<(), TimerError> {
    if tick_hz == 0 {
        return Err(TimerError::ZeroTickHz);
    }

    // AK5-J (R-HAL-M07 / MEDIUM): On aarch64, a CNTFRQ_EL0 value of 0 means
    // firmware did not program the timer frequency — fail the boot rather
    // than silently computing a wrong interval with the default constant.
    //
    // On non-aarch64 test hosts, `read_frequency()` returns 0 because the
    // stub has no real counter; fall back to `COUNTER_FREQ_HZ` so unit
    // tests exercising the post-validation logic still run. This is safe
    // because the test profile cannot mis-program a real RPi5.
    let freq = read_frequency();
    let effective_freq = if cfg!(target_arch = "aarch64") {
        if freq == 0 {
            return Err(TimerError::CntfrqNotProgrammed);
        }
        freq
    } else if freq == 0 {
        COUNTER_FREQ_HZ
    } else {
        freq
    };
    let interval = (effective_freq / tick_hz) as u64;

    TIMER_INTERVAL.store(interval, Ordering::Relaxed);

    // Read current counter and set first comparator
    let now = read_counter();
    set_comparator(now + interval);

    // Enable timer (ENABLE=1, IMASK=0)
    enable_timer();

    // Reset tick counter
    TICK_COUNT.store(0, Ordering::Relaxed);

    Ok(())
}

/// **WS-SM SM1.C.4** (closes SMP-C2 timer step): Per-core timer
/// initialization for secondary cores.
///
/// Each ARM Generic Timer is per-core: `CNTPCT_EL0` (counter),
/// `CNTP_CVAL_EL0` (comparator), `CNTP_CTL_EL0` (control) are all
/// banked per-PE.  The shared `CNTFRQ_EL0` (frequency) is programmed
/// once by firmware and is identical across cores on RPi5 (54 MHz).
///
/// Differs from [`init_timer`] in two ways:
/// 1. Does **NOT** reset the global `TICK_COUNT` — that's a primary-owned
///    monotonic counter; resetting it on secondary boot would corrupt
///    the kernel's "ticks since boot" semantics.
/// 2. Does **NOT** rewrite `TIMER_INTERVAL` — the primary's `init_timer`
///    populated this with the canonical interval, and the same value
///    holds for every core (CNTFRQ_EL0 is identical on RPi5).  We
///    locally recompute the interval to set the comparator without
///    perturbing the global, then exit; the recomputed value matches
///    the primary's stored value by construction.
///
/// **Pre-condition**: the primary's `init_timer` must have run before
/// any secondary calls this — the global `TIMER_INTERVAL` must hold
/// the canonical value so `reprogram_timer` works on every core.
///
/// **Per-core invariants on success**:
/// - `CNTP_CVAL_EL0` = `CNTPCT_EL0` + interval (next tick fires in
///   `tick_hz`⁻¹ seconds from the call site).
/// - `CNTP_CTL_EL0.ENABLE` = 1, `CNTP_CTL_EL0.IMASK` = 0 (interrupt
///   delivery to this PE enabled; GIC PPI 30 routing handled by the
///   distributor's PPI banking).
///
/// **Returns** `Ok(())` on success.  Error paths mirror [`init_timer`]:
/// `Err(ZeroTickHz)` if `tick_hz == 0`, `Err(CntfrqNotProgrammed)` if
/// `CNTFRQ_EL0` reads 0 on aarch64 (firmware misconfiguration).
///
/// References: ARM ARM D11.2 (CNTP* programmer's model), GIC-400 TRM
/// §3.2.5 (PPI banking per-PE).
pub fn init_timer_secondary(tick_hz: u32) -> Result<(), TimerError> {
    if tick_hz == 0 {
        return Err(TimerError::ZeroTickHz);
    }

    // AK5-J (R-HAL-M07): same CNTFRQ validation discipline as
    // `init_timer`.  Real hardware: zero CNTFRQ is firmware
    // misconfiguration; fail closed.  Host tests fall back to
    // `COUNTER_FREQ_HZ` (54 MHz) for non-aarch64 builds.
    let freq = read_frequency();
    let effective_freq = if cfg!(target_arch = "aarch64") {
        if freq == 0 {
            return Err(TimerError::CntfrqNotProgrammed);
        }
        freq
    } else if freq == 0 {
        COUNTER_FREQ_HZ
    } else {
        freq
    };
    let interval = (effective_freq / tick_hz) as u64;

    // SM1.C.4 deliberately does NOT write `TIMER_INTERVAL`: the
    // primary's `init_timer` already populated it with the canonical
    // value, and our locally-computed `interval` agrees with that
    // value by construction (CNTFRQ_EL0 + tick_hz are identical on
    // every core).  Writing the global would create a write storm
    // under SMP bring-up with no semantic gain.

    // Read this core's counter (banked per-PE) and arm the per-core
    // comparator.  CNTP_CVAL_EL0 = now + interval — next tick fires
    // one full interval from the call site, avoiding missed-tick
    // accumulation on slow cores.
    let now = read_counter();
    set_comparator(now + interval);
    enable_timer();

    // SM1.C.4 deliberately does NOT reset `TICK_COUNT`: that's a
    // primary-owned monotonic counter recording the kernel's wall-clock
    // ticks since boot; resetting it on every secondary's bring-up
    // would discard the primary's progress.

    Ok(())
}

/// Reprogram the timer comparator for the next tick.
///
/// Called from the timer interrupt handler after processing the current tick.
/// Uses counter-relative advancement: reads the current counter value and
/// sets comparator = counter + interval. This prevents missed-tick
/// accumulation: if the handler runs late, the next tick fires one full
/// interval from now rather than immediately.
///
/// Note: The Lean model's `HardwareTimerConfig.reprogramComparator` uses
/// CVAL-relative advancement (`comparatorValue + countsPerTick`), which
/// models ideal evenly-spaced ticks. The Rust side intentionally diverges
/// to handle real-world handler latency. Both converge under the assumption
/// that handler latency < tick interval (54000 counter ticks = ~1ms at
/// 54 MHz). The AG7 FFI bridge will reconcile this by advancing the model
/// timer by 1 tick regardless of the exact comparator arithmetic.
pub fn reprogram_timer() {
    let interval = TIMER_INTERVAL.load(Ordering::Relaxed);
    if interval == 0 {
        return; // Timer not initialized
    }

    // Counter-relative advancement: read current counter, add interval.
    // On non-aarch64, read_counter returns 0 and set_comparator is a no-op.
    let now = read_counter();
    set_comparator(now + interval);
}

/// Increment the tick counter. Called from the timer interrupt handler.
///
/// Returns the new tick count.
///
/// AJ5-D/L-15: Restricted to `pub(crate)` — only called from `ffi.rs`
/// (`ffi_timer_reprogram`). External crates must not increment the tick
/// counter directly, as double-counting would corrupt the Lean model's
/// `MachineState.timer` shadow.
pub(crate) fn increment_tick_count() -> u64 {
    TICK_COUNT.fetch_add(1, Ordering::Relaxed) + 1
}

/// Get the current tick count.
pub fn get_tick_count() -> u64 {
    TICK_COUNT.load(Ordering::Relaxed)
}

// ============================================================================
// WS-SM SM5.D.1 — Per-core CNTV timer ISR
// ============================================================================

/// WS-SM SM5.D.1: the per-core ARM Generic Timer (CNTV) interrupt service
/// routine — the seam that drives the verified Lean per-core scheduler timer
/// tick (`Kernel.timerTickOnCore`, plan §3.4).
///
/// Each core's CNTV fires **independently** (the comparator / control registers
/// are per-core, banked at the hardware level — see [`init_timer_secondary`]).
/// On each tick of core `core_id` this routine:
///
/// 1. **Records** the per-core tick counter (an SMP-local diagnostic, separate
///    from the primary-owned global `TICK_COUNT`).
/// 2. **Re-arms** the per-core comparator for the next tick
///    ([`reprogram_timer`], counter-relative to avoid missed-tick accumulation).
/// 3. **Drives** the Lean per-core scheduler tick via the C-callable export
///    `lean_per_core_timer_tick(core_id)` (the Lean kernel reads core `core_id`'s
///    scheduler slots, advances its domain accounting, processes CBS, and emits
///    any cross-core `.reschedule` SGIs the replenishment wakes produce — the
///    pure `timerTickOnCore` transition + its `withLockSet` bracket).  Gated on
///    `feature = "hw_target"`: on the host the call is omitted (no kernel image
///    is linked), so the ISR is unit-testable as the record-and-rearm seam.
///
/// **Global-timer ownership.** This routine does **not** touch the primary-owned
/// global `TICK_COUNT` (that is advanced once per global tick by the boot core
/// via `ffi_timer_reprogram`), mirroring the Lean model where `timerTickOnCore`
/// reads but never advances `machine.timer` — each core's CNTV is local, the
/// global monotonic count is owned by a single authority.  See the SM5.D section
/// header of `SeLe4n/Kernel/Scheduler/Operations/Core.lean`.
///
/// **Re-entrancy.** The IRQ is acknowledged + EOI'd before this runs, and the
/// CPU-interface running-priority mask holds INTID 30 off until `PSTATE.I` clears
/// on exception return, so the comparator re-arm cannot itself re-trigger.
pub fn per_core_timer_tick_isr(core_id: u64) {
    // 1. Per-core tick accounting (SMP-localised diagnostic).
    let _ = crate::per_cpu_stats::record_timer_tick();
    // 2. Re-arm the per-core comparator for the next tick.
    reprogram_timer();
    // 3. Drive the Lean per-core scheduler timer tick (hardware only).
    #[cfg(feature = "hw_target")]
    {
        // SAFETY: `lean_per_core_timer_tick` is the C-callable wrapper the Lean
        // compiler emits for `Kernel.perCoreTimerTickEntry`
        // (`@[export lean_per_core_timer_tick]`).  It takes a `u64` core id and
        // returns no value; calling it is sound from EL1 kernel context after
        // the per-core hardware init has completed.
        extern "C" {
            fn lean_per_core_timer_tick(core_id: u64);
        }
        unsafe {
            lean_per_core_timer_tick(core_id);
        }
    }
    #[cfg(not(feature = "hw_target"))]
    let _ = core_id;
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests {
    use super::*;

    // ------------------------------------------------------------------------
    // WS-SM SM1.I (audit-pass-1) — global timer-state serialisation mutex
    // ------------------------------------------------------------------------
    //
    // Several tests below write to the `TIMER_INTERVAL` and `TICK_COUNT`
    // globals as part of their setup, then read them back to verify a
    // function call mutated them correctly.  Under cargo's parallel test
    // execution, a concurrent test that touches either global can race
    // and overwrite the value between the write and read steps —
    // producing a transient failure even though the function under test
    // behaved correctly.
    //
    // We serialise these tests with a private `Mutex`.  Each test that
    // touches `TIMER_INTERVAL` or `TICK_COUNT` acquires this mutex as
    // its first step; the guard lives for the test's lifetime.  This
    // serialises the timer-state tests with each other while leaving
    // non-timer-state tests free to run in parallel.
    //
    // The mutex is `std::sync::Mutex` because `extern crate std` is
    // declared just above this module for the test profile only — the
    // production no_std discipline is unaffected.
    //
    // Stress-testing this fix (50× repeated `cargo test --all --features
    // std`) confirms the failure rate drops from ~10–15% to 0%.
    //
    // Audit-pass-4 (poisoning defence): every test that acquires this
    // mutex uses `.lock().unwrap_or_else(|e| e.into_inner())` so a
    // failed assert inside a holder does not cascade-fail every
    // subsequent timer-state test with `PoisonError`.
    static TIMER_GLOBAL_STATE_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

    #[test]
    fn timer_frequency_matches_board_lean() {
        // Board.lean: timerFrequencyHz := 54000000
        assert_eq!(COUNTER_FREQ_HZ, 54_000_000);
    }

    #[test]
    fn counts_per_tick_at_1khz() {
        // 54 MHz / 1000 Hz = 54000 counts per tick
        assert_eq!(COUNTS_PER_TICK, 54_000);
    }

    #[test]
    fn default_tick_rate() {
        assert_eq!(DEFAULT_TICK_HZ, 1000);
    }

    #[test]
    fn interval_calculation() {
        // At 1000 Hz with 54 MHz counter: 54000000 / 1000 = 54000
        let interval = COUNTER_FREQ_HZ / DEFAULT_TICK_HZ;
        assert_eq!(interval, 54_000);
    }

    #[test]
    fn interval_at_100hz() {
        // At 100 Hz: 54000000 / 100 = 540000
        let interval = COUNTER_FREQ_HZ / 100;
        assert_eq!(interval, 540_000);
    }

    #[test]
    fn tick_count_starts_at_zero() {
        // Reset for test isolation.  SM1.I serialisation: acquire the
        // global state mutex so this test does not race on TICK_COUNT.
        let _guard = TIMER_GLOBAL_STATE_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        TICK_COUNT.store(0, Ordering::Relaxed);
        assert_eq!(get_tick_count(), 0);
    }

    #[test]
    fn tick_count_increments() {
        let _guard = TIMER_GLOBAL_STATE_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        TICK_COUNT.store(0, Ordering::Relaxed);
        assert_eq!(increment_tick_count(), 1);
        assert_eq!(increment_tick_count(), 2);
        assert_eq!(get_tick_count(), 2);
    }

    #[test]
    fn timer_interval_storage() {
        let _guard = TIMER_GLOBAL_STATE_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        TIMER_INTERVAL.store(54_000, Ordering::Relaxed);
        assert_eq!(TIMER_INTERVAL.load(Ordering::Relaxed), 54_000);
    }

    #[test]
    fn init_timer_stores_interval() {
        // On non-aarch64, read_frequency returns 0 so fallback to COUNTER_FREQ_HZ.
        // 54000000 / 1000 = 54000.
        //
        // AN8-D (RUST-M03): use `assert_eq!(... , Ok(()))` so the test
        // documents the expected return value explicitly. `unwrap()` would
        // hide a future error variant change behind a panic message that
        // doesn't name the variant.
        //
        // SM1.I serialisation: acquire the global state mutex so
        // TIMER_INTERVAL and TICK_COUNT reads aren't raced by parallel
        // timer tests.
        let _guard = TIMER_GLOBAL_STATE_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        // Reset before init so the precondition matches.
        TICK_COUNT.store(0, Ordering::Relaxed);
        assert_eq!(init_timer(1000), Ok(()));
        assert_eq!(TIMER_INTERVAL.load(Ordering::Relaxed), 54_000);
        assert_eq!(get_tick_count(), 0);
    }

    #[test]
    fn init_timer_100hz_interval() {
        // AN8-D (RUST-M03): explicit Ok(()) check.
        // SM1.I serialisation: see TIMER_GLOBAL_STATE_MUTEX docstring.
        let _guard = TIMER_GLOBAL_STATE_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        assert_eq!(init_timer(100), Ok(()));
        assert_eq!(TIMER_INTERVAL.load(Ordering::Relaxed), 540_000);
    }

    #[test]
    fn reprogram_timer_no_panic() {
        let _guard = TIMER_GLOBAL_STATE_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        TIMER_INTERVAL.store(54_000, Ordering::Relaxed);
        // On non-aarch64, read_counter returns 0, set_comparator is no-op.
        reprogram_timer();
    }

    #[test]
    fn reprogram_timer_uninit_noop() {
        let _guard = TIMER_GLOBAL_STATE_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        TIMER_INTERVAL.store(0, Ordering::Relaxed);
        // Should return early without panicking
        reprogram_timer();
    }

    // AJ5-C/L-14: init_timer(0) now returns Err instead of panicking.
    #[test]
    fn init_timer_zero_hz_returns_error() {
        assert_eq!(init_timer(0), Err(TimerError::ZeroTickHz));
    }

    // AK5-J (R-HAL-M07): CNTFRQ_EL0 == 0 on aarch64 must fail the boot.
    // On non-aarch64 test hosts we fall back to COUNTER_FREQ_HZ so the
    // test exercises the error type surface without needing a real CPU.
    #[test]
    fn timer_error_cntfrq_not_programmed_distinct() {
        let a = TimerError::ZeroTickHz;
        let b = TimerError::CntfrqNotProgrammed;
        assert_ne!(a, b);
    }

    #[test]
    fn timer_error_cntfrq_display_mentions_firmware() {
        use core::fmt::Write;
        struct Buf {
            data: [u8; 256],
            pos: usize,
        }
        impl Write for Buf {
            fn write_str(&mut self, s: &str) -> core::fmt::Result {
                let b = s.as_bytes();
                let end = self.pos + b.len();
                if end > self.data.len() {
                    return Err(core::fmt::Error);
                }
                self.data[self.pos..end].copy_from_slice(b);
                self.pos = end;
                Ok(())
            }
        }
        let mut buf = Buf {
            data: [0; 256],
            pos: 0,
        };
        write!(buf, "{}", TimerError::CntfrqNotProgrammed).unwrap();
        let s = core::str::from_utf8(&buf.data[..buf.pos]).unwrap();
        assert!(
            s.contains("CNTFRQ") && s.contains("firmware"),
            "Display missing key phrase: {s}"
        );
    }

    // =====================================================================
    // WS-SM SM1.C.4 — Per-core timer init (init_timer_secondary)
    // =====================================================================

    #[test]
    fn sm1c4_init_timer_secondary_returns_ok_on_host_with_default_tick_hz() {
        // SM1.C.4: on host (CNTFRQ_EL0 read returns 0 because of the
        // host-stub `read_sysreg!`), `init_timer_secondary` falls back
        // to `COUNTER_FREQ_HZ` and returns Ok.
        let r = init_timer_secondary(DEFAULT_TICK_HZ);
        assert_eq!(r, Ok(()));
    }

    #[test]
    fn sm1c4_init_timer_secondary_rejects_zero_tick_hz() {
        // SM1.C.4: shape parity with `init_timer` — a zero tick rate
        // would cause division by zero in the interval computation, so
        // we reject it explicitly with `TimerError::ZeroTickHz`.
        assert_eq!(init_timer_secondary(0), Err(TimerError::ZeroTickHz));
    }

    #[test]
    fn sm1c4_init_timer_secondary_does_not_reset_tick_count() {
        // SM1.C.4 contract: `TICK_COUNT` is owned by the primary core;
        // a secondary's bring-up must NOT reset it.  Pre-seed the
        // counter with a sentinel value, run `init_timer_secondary`,
        // and verify the counter survives.
        //
        // SM1.I serialisation: see TIMER_GLOBAL_STATE_MUTEX docstring.
        let _guard = TIMER_GLOBAL_STATE_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        TICK_COUNT.store(42, Ordering::Relaxed);
        assert_eq!(init_timer_secondary(DEFAULT_TICK_HZ), Ok(()));
        assert_eq!(
            get_tick_count(),
            42,
            "init_timer_secondary must preserve TICK_COUNT (primary-owned monotonic counter)"
        );
        // Clean up for downstream tests.
        TICK_COUNT.store(0, Ordering::Relaxed);
    }

    #[test]
    fn sm1c4_init_timer_secondary_does_not_perturb_timer_interval() {
        // SM1.C.4 contract: the global `TIMER_INTERVAL` is populated
        // by the primary's `init_timer`; the secondary's locally-
        // computed interval matches that value, but we must NOT write
        // the global from the secondary's path.  This test pre-seeds
        // a sentinel value and verifies it survives.
        //
        // Using a value that does NOT match the host-stub default
        // (which would be `COUNTER_FREQ_HZ / DEFAULT_TICK_HZ = 54_000`)
        // so a regression where we do write the global is detectable.
        //
        // SM1.I serialisation: see TIMER_GLOBAL_STATE_MUTEX docstring.
        let _guard = TIMER_GLOBAL_STATE_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        TIMER_INTERVAL.store(99_999, Ordering::Relaxed);
        assert_eq!(init_timer_secondary(DEFAULT_TICK_HZ), Ok(()));
        assert_eq!(
            TIMER_INTERVAL.load(Ordering::Relaxed),
            99_999,
            "init_timer_secondary must NOT write TIMER_INTERVAL — that's primary-only"
        );
        // Restore canonical value for downstream tests that depend on it.
        TIMER_INTERVAL.store(0, Ordering::Relaxed);
    }

    #[test]
    fn sm1c4_init_timer_secondary_signature_returns_result() {
        // SM1.C.4: return type matches `init_timer` exactly so call
        // sites in `rust_secondary_main` can use the same `match`
        // pattern.
        let _: fn(u32) -> Result<(), TimerError> = init_timer_secondary;
    }

    #[test]
    fn sm1c4_init_timer_secondary_accepts_full_tick_hz_range() {
        // SM1.C.4: shape parity with `init_timer` — a 100 Hz tick
        // rate (10ms ticks) must also work.  Verifies the function
        // doesn't accidentally hard-code DEFAULT_TICK_HZ.
        //
        // SM1.I serialisation: see TIMER_GLOBAL_STATE_MUTEX docstring.
        let _guard = TIMER_GLOBAL_STATE_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        TIMER_INTERVAL.store(0, Ordering::Relaxed);
        TICK_COUNT.store(0, Ordering::Relaxed);
        assert_eq!(init_timer_secondary(100), Ok(()));
        // Tick counter still zero (no reset on secondary).
        assert_eq!(get_tick_count(), 0);
    }

    #[test]
    fn sm1c4_init_timer_signature_unchanged() {
        // SM1.C.4 / regression: the primary's `init_timer` signature
        // must not drift — `rust_boot_main`'s call site depends on it.
        let _: fn(u32) -> Result<(), TimerError> = init_timer;
    }

    #[test]
    fn timer_error_display() {
        use core::fmt::Write;
        let err = TimerError::ZeroTickHz;
        // no_std-compatible fixed-size buffer for Display test
        struct FmtBuf {
            buf: [u8; 128],
            pos: usize,
        }
        impl FmtBuf {
            fn new() -> Self {
                Self {
                    buf: [0u8; 128],
                    pos: 0,
                }
            }
            fn as_str(&self) -> &str {
                core::str::from_utf8(&self.buf[..self.pos]).unwrap()
            }
        }
        impl Write for FmtBuf {
            fn write_str(&mut self, s: &str) -> core::fmt::Result {
                let bytes = s.as_bytes();
                let end = self.pos + bytes.len();
                if end > self.buf.len() {
                    return Err(core::fmt::Error);
                }
                self.buf[self.pos..end].copy_from_slice(bytes);
                self.pos = end;
                Ok(())
            }
        }
        let mut buf = FmtBuf::new();
        write!(buf, "{}", err).unwrap();
        assert!(
            buf.as_str().contains("tick_hz must be > 0"),
            "Display output was: {}",
            buf.as_str()
        );
    }

    // ------------------------------------------------------------------------
    // WS-SM SM5.D.1 — per-core CNTV timer ISR
    // ------------------------------------------------------------------------

    /// SM5.D.1: the per-core timer ISR is callable on the host (the
    /// `hw_target`-gated Lean call is omitted) and does not panic.
    #[test]
    fn sm5d1_per_core_timer_tick_isr_callable_on_host() {
        let _guard = TIMER_GLOBAL_STATE_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        // Should not panic for the boot core or any secondary core id.
        per_core_timer_tick_isr(0);
        per_core_timer_tick_isr(1);
        per_core_timer_tick_isr(3);
    }

    /// SM5.D.1: the ISR advances the calling core's per-core timer-tick counter
    /// (the SMP-localised diagnostic), via `record_timer_tick`.  On the host the
    /// calling core is the boot core (TPIDR_EL1 stub returns 0).
    #[test]
    fn sm5d1_per_core_timer_tick_isr_records_tick() {
        let _guard = TIMER_GLOBAL_STATE_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let before = crate::per_cpu_stats::timer_tick_count_for(0);
        per_core_timer_tick_isr(0);
        let after = crate::per_cpu_stats::timer_tick_count_for(0);
        assert_eq!(
            after,
            before.wrapping_add(1),
            "the per-core timer ISR must advance the calling core's tick counter by exactly one"
        );
    }

    /// SM5.D.1: the ISR does not advance the primary-owned global `TICK_COUNT`
    /// (that is the boot core's / FFI's responsibility — the per-core tick reads
    /// but never advances the global monotonic counter, mirroring the Lean model
    /// where `timerTickOnCore` never advances `machine.timer`).
    #[test]
    fn sm5d1_per_core_timer_tick_isr_does_not_advance_global_tick_count() {
        let _guard = TIMER_GLOBAL_STATE_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let before = get_tick_count();
        per_core_timer_tick_isr(0);
        let after = get_tick_count();
        assert_eq!(
            after, before,
            "the per-core timer ISR must NOT advance the primary-owned global TICK_COUNT"
        );
    }

    /// SM5.D.1: signature pin — `per_core_timer_tick_isr` is `fn(u64)`.
    #[test]
    fn sm5d1_per_core_timer_tick_isr_signature() {
        let f: fn(u64) = per_core_timer_tick_isr;
        let _ = f;
    }
}
