//! Performance measurement infrastructure for AG9-C (WCRT) and AG9-D (RunQueue).
//!
//! Provides cycle-accurate measurement primitives using the ARM Performance
//! Monitor Counters (PMU) on Cortex-A76. On non-AArch64 hosts, measurements
//! use a monotonic counter stub for compilation and unit testing.
//!
//! ## Hardware counters
//!
//! - PMCCNTR_EL0: Cycle counter (64-bit, counts CPU cycles when enabled)
//! - CNTPCT_EL0: System counter (54 MHz on RPi5, always available)
//!
//! ## Usage
//!
//! ```no_run
//! use sele4n_hal::profiling::{LatencyStats, read_cycle_counter};
//! # fn do_work() {}
//! let mut stats = LatencyStats::new();
//! for _ in 0..10_000 {
//!     let start = read_cycle_counter();
//!     do_work();
//!     let end = read_cycle_counter();
//!     stats.record(end - start);
//! }
//! // `stats` now contains min, max, mean (p99 / p99.9 not tracked —
//! // `LatencyStats` records a single-pass summary, not the full sample).
//! ```

use core::sync::atomic::{AtomicU64, Ordering};

/// Global monotonic counter for non-AArch64 hosts (test stub).
#[cfg(not(target_arch = "aarch64"))]
static STUB_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Read the CPU cycle counter (PMCCNTR_EL0).
///
/// Returns the current cycle count. On Cortex-A76 this counts at the CPU
/// clock rate (~2.4 GHz on RPi5). Must be enabled via PMCR_EL0 first.
///
/// ARM ARM D11.2: PMCCNTR_EL0 — Performance Monitors Cycle Count Register.
#[inline(always)]
pub fn read_cycle_counter() -> u64 {
    #[cfg(target_arch = "aarch64")]
    {
        crate::read_sysreg!("pmccntr_el0")
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        STUB_COUNTER.fetch_add(1, Ordering::Relaxed)
    }
}

/// Enable the PMU cycle counter for user/kernel measurement.
///
/// Sets PMCR_EL0.E (enable) and PMCR_EL0.C (reset cycle counter),
/// then enables PMCCNTR_EL0 via PMCNTENSET_EL0.
///
/// Must be called once during boot before any `read_cycle_counter()` calls.
///
/// ARM ARM D11.2: PMCR_EL0 — Performance Monitors Control Register.
pub fn enable_cycle_counter() {
    #[cfg(target_arch = "aarch64")]
    {
        // PMCR_EL0: bit 0 = E (enable), bit 2 = C (reset cycle counter)
        crate::write_sysreg!("pmcr_el0", 0x5u64);
        // PMCNTENSET_EL0: bit 31 = enable PMCCNTR_EL0
        crate::write_sysreg!("pmcntenset_el0", 1u64 << 31);
        // PMUSERENR_EL0: bit 0 = EN (enable EL0 access to PMU)
        crate::write_sysreg!("pmuserenr_el0", 1u64);
    }
}

/// Read the system counter (CNTPCT_EL0) — 54 MHz on RPi5.
///
/// Unlike the cycle counter, this is always available without PMU setup.
/// Lower resolution than PMCCNTR but does not require enablement.
#[inline(always)]
pub fn read_system_counter() -> u64 {
    crate::timer::read_counter()
}

/// Latency statistics accumulator.
///
/// AG9-C: Records min, max, sum, and count for computing scheduling
/// latency statistics across many samples. Designed for WCRT measurement
/// across 10,000+ timer ticks.
///
/// AG9-D: Also used for RunQueue operation profiling (insert/remove
/// cycle counts at various queue sizes).
pub struct LatencyStats {
    /// Minimum observed latency (cycles or counter ticks).
    pub min: u64,
    /// Maximum observed latency.
    pub max: u64,
    /// Sum of all latencies (for mean calculation).
    pub sum: u64,
    /// Number of samples recorded.
    pub count: u64,
}

impl Default for LatencyStats {
    fn default() -> Self {
        Self::new()
    }
}

impl LatencyStats {
    /// Create a new empty statistics accumulator.
    pub const fn new() -> Self {
        Self {
            min: u64::MAX,
            max: 0,
            sum: 0,
            count: 0,
        }
    }

    /// Record a single latency measurement.
    ///
    /// Uses saturating arithmetic for `sum` to prevent silent wraparound.
    /// If saturation occurs, `mean()` returns a pessimistic (inflated) value
    /// rather than garbage — the saturation condition is detectable via
    /// `sum == u64::MAX`.
    #[inline(always)]
    pub fn record(&mut self, latency: u64) {
        if latency < self.min {
            self.min = latency;
        }
        if latency > self.max {
            self.max = latency;
        }
        self.sum = self.sum.saturating_add(latency);
        self.count = self.count.saturating_add(1);
    }

    /// Compute the mean latency. Returns 0 if no samples recorded.
    pub fn mean(&self) -> u64 {
        if self.count == 0 { 0 } else { self.sum / self.count }
    }

    /// Check if any samples have been recorded.
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn latency_stats_new_is_empty() {
        let stats = LatencyStats::new();
        assert!(stats.is_empty());
        assert_eq!(stats.count, 0);
        assert_eq!(stats.mean(), 0);
    }

    #[test]
    fn latency_stats_single_sample() {
        let mut stats = LatencyStats::new();
        stats.record(100);
        assert!(!stats.is_empty());
        assert_eq!(stats.min, 100);
        assert_eq!(stats.max, 100);
        assert_eq!(stats.mean(), 100);
        assert_eq!(stats.count, 1);
    }

    #[test]
    fn latency_stats_multiple_samples() {
        let mut stats = LatencyStats::new();
        stats.record(10);
        stats.record(20);
        stats.record(30);
        assert_eq!(stats.min, 10);
        assert_eq!(stats.max, 30);
        assert_eq!(stats.mean(), 20);
        assert_eq!(stats.count, 3);
    }

    #[test]
    fn latency_stats_min_max_tracking() {
        let mut stats = LatencyStats::new();
        stats.record(50);
        stats.record(10);
        stats.record(90);
        stats.record(30);
        assert_eq!(stats.min, 10);
        assert_eq!(stats.max, 90);
    }

    #[test]
    fn latency_stats_sum_saturates() {
        let mut stats = LatencyStats::new();
        stats.record(u64::MAX);
        stats.record(1);
        // sum should saturate at u64::MAX, not wrap to 0
        assert_eq!(stats.sum, u64::MAX);
        assert_eq!(stats.count, 2);
        // mean is u64::MAX / 2 (pessimistic but not garbage)
        assert_eq!(stats.mean(), u64::MAX / 2);
    }

    #[test]
    fn read_cycle_counter_monotonic() {
        let a = read_cycle_counter();
        let b = read_cycle_counter();
        // On non-aarch64, stub counter is monotonically increasing
        assert!(b > a);
    }

    #[test]
    fn enable_cycle_counter_no_panic() {
        // On non-aarch64, this is a no-op
        enable_cycle_counter();
    }
}
