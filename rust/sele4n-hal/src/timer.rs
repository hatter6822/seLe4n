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
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

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
        // Reset for test isolation
        TICK_COUNT.store(0, Ordering::Relaxed);
        assert_eq!(get_tick_count(), 0);
    }

    #[test]
    fn tick_count_increments() {
        TICK_COUNT.store(0, Ordering::Relaxed);
        assert_eq!(increment_tick_count(), 1);
        assert_eq!(increment_tick_count(), 2);
        assert_eq!(get_tick_count(), 2);
    }

    #[test]
    fn timer_interval_storage() {
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
        assert_eq!(init_timer(1000), Ok(()));
        assert_eq!(TIMER_INTERVAL.load(Ordering::Relaxed), 54_000);
        assert_eq!(get_tick_count(), 0);
    }

    #[test]
    fn init_timer_100hz_interval() {
        // AN8-D (RUST-M03): explicit Ok(()) check.
        assert_eq!(init_timer(100), Ok(()));
        assert_eq!(TIMER_INTERVAL.load(Ordering::Relaxed), 540_000);
    }

    #[test]
    fn reprogram_timer_no_panic() {
        TIMER_INTERVAL.store(54_000, Ordering::Relaxed);
        // On non-aarch64, read_counter returns 0, set_comparator is no-op.
        reprogram_timer();
    }

    #[test]
    fn reprogram_timer_uninit_noop() {
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
        struct Buf { data: [u8; 256], pos: usize }
        impl Write for Buf {
            fn write_str(&mut self, s: &str) -> core::fmt::Result {
                let b = s.as_bytes();
                let end = self.pos + b.len();
                if end > self.data.len() { return Err(core::fmt::Error); }
                self.data[self.pos..end].copy_from_slice(b);
                self.pos = end;
                Ok(())
            }
        }
        let mut buf = Buf { data: [0; 256], pos: 0 };
        write!(buf, "{}", TimerError::CntfrqNotProgrammed).unwrap();
        let s = core::str::from_utf8(&buf.data[..buf.pos]).unwrap();
        assert!(s.contains("CNTFRQ") && s.contains("firmware"),
            "Display missing key phrase: {s}");
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
            fn new() -> Self { Self { buf: [0u8; 128], pos: 0 } }
            fn as_str(&self) -> &str {
                core::str::from_utf8(&self.buf[..self.pos]).unwrap()
            }
        }
        impl Write for FmtBuf {
            fn write_str(&mut self, s: &str) -> core::fmt::Result {
                let bytes = s.as_bytes();
                let end = self.pos + bytes.len();
                if end > self.buf.len() { return Err(core::fmt::Error); }
                self.buf[self.pos..end].copy_from_slice(bytes);
                self.pos = end;
                Ok(())
            }
        }
        let mut buf = FmtBuf::new();
        write!(buf, "{}", err).unwrap();
        assert!(buf.as_str().contains("tick_hz must be > 0"),
            "Display output was: {}", buf.as_str());
    }
}
