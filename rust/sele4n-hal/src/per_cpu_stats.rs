// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-SM SM1.I.4**: Per-core exception / interrupt statistics.
//!
//! Optional informational counters per core.  Useful for benchmarking,
//! cross-core attribution in post-mortem analysis, and Tier-3 sanity
//! invariants ("every core that ran for ≥ 1 tick saw ≥ 1 IRQ").  Not
//! required for correctness — every counter increment is wait-free and
//! the kernel's safety properties are independent of whether the
//! counters move.
//!
//! ## Layout
//!
//! Each core owns one [`PerCpuStats`] slot in the [`PER_CPU_STATS`]
//! static array.  Slots are 64-byte aligned (one cache line on
//! Cortex-A76) so a write to core *i*'s counters does not invalidate
//! core *j*'s cache line.  Without this, every counter increment from
//! a busy core would trigger cache-line ping-pong with every other
//! core that happens to be reading any of its own stats.
//!
//! Each counter is an [`core::sync::atomic::AtomicU64`] with `Relaxed`
//! ordering.  `Relaxed` is correct because:
//!
//! 1. The counters are not used as synchronisation primitives — no
//!    correctness property depends on the value being observed by
//!    another core in any particular order.
//! 2. `fetch_add(1, Relaxed)` on ARMv8-A compiles to `ldaddal` (or
//!    `ldxr/stxr` on pre-FEAT_LSE cores), both of which are
//!    wait-free at the hardware level.
//! 3. Loose ordering avoids inserting unnecessary `dmb` barriers that
//!    would slow the IRQ hot path for no observable benefit.
//!
//! ## Counters
//!
//! - `irq_count` — total IRQs the per-core handler dispatched
//!   (timer PPI + SGIs + SPIs that route to this core).  Incremented
//!   by [`record_irq_dispatch`] from [`crate::trap::handle_irq_per_core`].
//! - `timer_tick_count` — timer PPI (INTID 30) only.  A
//!   high-resolution counter for per-core scheduler tick accounting
//!   that SM5 will surface to the verified scheduler.
//! - `sgi_count` — SGIs (INTID 0..15) only.  Per-core cross-core
//!   coordination volume.
//! - `syscall_count` — SVC instructions executed from EL0 (synchronous
//!   exception class 0x15) that traversed this core's
//!   `handle_synchronous_exception`.  Useful for cross-core load
//!   attribution.
//! - `vmfault_count` — data and instruction aborts the synchronous
//!   handler classified as `KernelError::VmFault`.  Useful for
//!   diagnosing pathological per-core memory pressure.
//! - `user_exception_count` — synchronous exceptions classified as
//!   `KernelError::UserException` (alignment fault, unknown EC).
//!
//! ## SM5 consumption
//!
//! At SM1.I the counters are written by the per-core IRQ handler
//! ([`crate::trap::handle_irq_per_core`]) but read only by host unit
//! tests.  SM5+ will surface them via a verified kernel API for use
//! by:
//!
//! - Performance counters in the trace harness.
//! - A `/proc`-style debug interface a user-mode profiler queries.
//! - Tier-4 nightly QEMU bringup tests that assert "every core saw
//!   ≥ 1 timer tick within 100 ms" as a liveness invariant.
//!
//! ## Host (non-aarch64) behaviour
//!
//! Every entry point compiles and executes identically on host —
//! AtomicU64 has full support on x86_64.  The "current core" accessor
//! falls back to slot 0 on host (matching [`crate::cpu::current_core_id`]
//! and [`crate::per_cpu::current_core_id_from_tpidr`]).

use core::sync::atomic::{AtomicU64, Ordering};

use crate::smp::MAX_SECONDARY_CORES;

/// **WS-SM SM1.I.4**: Per-core exception / interrupt statistics block.
///
/// One slot per core, cache-line aligned (64 bytes on Cortex-A76) to
/// eliminate false sharing between adjacent cores' counters.  Field
/// layout is tuned for the IRQ hot path: `irq_count` is at offset 0
/// so the most-frequent counter benefits from the natural cache-line
/// fetch.
#[repr(C, align(64))]
pub struct PerCpuStats {
    /// Total IRQs the per-core handler dispatched.  Incremented by
    /// [`record_irq_dispatch`] on every IAR read that returns a
    /// non-spurious INTID.
    pub irq_count: AtomicU64,
    /// Timer PPI (INTID 30) interrupts only.  Subset of `irq_count`.
    pub timer_tick_count: AtomicU64,
    /// SGIs (INTID 0..15) only.  Subset of `irq_count`.
    pub sgi_count: AtomicU64,
    /// SVC instructions classified by `handle_synchronous_exception`.
    pub syscall_count: AtomicU64,
    /// Data + instruction aborts classified as `VmFault`.
    pub vmfault_count: AtomicU64,
    /// Alignment + unknown-EC synchronous exceptions classified as
    /// `UserException`.
    pub user_exception_count: AtomicU64,
    /// Padding to keep the struct exactly one cache line.  Two
    /// `AtomicU64` slots are reserved for SM5+ additions (e.g.,
    /// per-core "context switches", "preemptions").
    _reserved: [AtomicU64; 2],
}

impl PerCpuStats {
    /// **WS-SM SM1.I.4**: const constructor producing an all-zero
    /// stats block.
    ///
    /// `const fn` is required because [`PER_CPU_STATS`] is a `static`
    /// array — Rust forbids non-const initialisers for statics.
    ///
    /// The reserved tail is initialised to zero AtomicU64 instances
    /// the same way as the public fields; together with the
    /// `repr(C, align(64))` attribute this guarantees every byte of
    /// the slot is zero at boot, eliminating stale-RAM-leakage hazards
    /// for the SM5+ additions that will populate the reserved slots.
    #[inline]
    pub const fn zero() -> Self {
        Self {
            irq_count: AtomicU64::new(0),
            timer_tick_count: AtomicU64::new(0),
            sgi_count: AtomicU64::new(0),
            syscall_count: AtomicU64::new(0),
            vmfault_count: AtomicU64::new(0),
            user_exception_count: AtomicU64::new(0),
            _reserved: [AtomicU64::new(0), AtomicU64::new(0)],
        }
    }
}

/// **WS-SM SM1.I.4**: Per-core stats array, one slot per core.
///
/// Indexed by `core_id` (0..=`MAX_SECONDARY_CORES`).  Each slot
/// initialised to zero at compile time via [`PerCpuStats::zero`].
///
/// `#[no_mangle]` and `#[used]` preserve the symbol name so a future
/// hardware-side debug interface (a UART-poked "dump stats" command)
/// can resolve it via the linker map.
#[no_mangle]
#[used]
pub static PER_CPU_STATS: [PerCpuStats; MAX_SECONDARY_CORES + 1] = [
    PerCpuStats::zero(),
    PerCpuStats::zero(),
    PerCpuStats::zero(),
    PerCpuStats::zero(),
];

// Compile-time pin: each slot is exactly one cache line wide.  A future
// PR that adds an `AtomicU64` field beyond the reserved pair without
// updating the `_reserved` size will fail to elaborate here with a
// clear diagnostic, preventing accidental cross-cache-line growth.
const _: () = assert!(
    core::mem::size_of::<PerCpuStats>() == 64,
    "WS-SM SM1.I.4: PerCpuStats must be one cache line (64 bytes); \
     remove a `_reserved` slot when adding a new counter to stay within budget"
);

// Compile-time pin: cache-line aligned to avoid false sharing.
const _: () = assert!(
    core::mem::align_of::<PerCpuStats>() == 64,
    "WS-SM SM1.I.4: PerCpuStats must be 64-byte aligned to avoid false sharing"
);

// Compile-time pin: every plausible core has its own slot.  The type
// definition above already enforces this at the array literal, but we
// document the invariant locally so future maintainers don't try to
// dynamically resize.
//
// We deliberately do NOT use `const _: () = assert!(PER_CPU_STATS.len()
// == MAX_SECONDARY_CORES + 1, ...)` because reading a `static` from a
// const context requires `feature(const_refs_to_statics)` (rust-lang/
// rust#119618), stabilised only in Rust 1.83.  Seele4n MSRV is 1.82.

/// **WS-SM SM1.I.4**: read the calling core's stats slot.
///
/// Routes through [`crate::per_cpu::current_core_id_from_tpidr`] so
/// the same TPIDR_EL1-backed identification path is used as for
/// [`crate::per_cpu::current_per_cpu`].  On host the boot core's slot
/// (index 0) is always returned.
///
/// # Safety invariants
///
/// - The returned reference is `'static` because [`PER_CPU_STATS`] is
///   a `'static` array.  The slot's interior atomics are safe to
///   access concurrently from multiple cores per the AtomicU64
///   contract.
/// - The `core_id` read from TPIDR_EL1 must be in range
///   `0..=MAX_SECONDARY_CORES`; this is structurally enforced by
///   [`crate::per_cpu::check_per_cpu_invariants`] which runs at boot.
///   If the invariant is violated (which would indicate a corrupt
///   TPIDR_EL1), we deliberately panic rather than silently aliasing
///   to slot 0.
#[inline(always)]
pub fn current_per_cpu_stats() -> &'static PerCpuStats {
    let core_id = crate::per_cpu::current_core_id_from_tpidr() as usize;
    // Defensive bound check: a corrupt TPIDR_EL1 producing an
    // out-of-range core_id would otherwise alias to the boot slot,
    // silently mixing other cores' stats with the corrupt core's.
    // The post-boot invariants enforced by `check_per_cpu_invariants`
    // make this unreachable in well-formed kernel state, so the
    // panic is a defense-in-depth diagnostic rather than expected
    // control flow.
    assert!(
        core_id < PER_CPU_STATS.len(),
        "WS-SM SM1.I.4: current_per_cpu_stats: core_id {} out of range \
         (expected < {}); TPIDR_EL1 corrupt",
        core_id,
        PER_CPU_STATS.len()
    );
    &PER_CPU_STATS[core_id]
}

/// **WS-SM SM1.I.4**: record a dispatched IRQ on the calling core.
///
/// Increments [`PerCpuStats::irq_count`] for the current core.  Called
/// from [`crate::trap::handle_irq_per_core`] from inside the
/// `gic::dispatch_irq` closure, so the increment fires only for the
/// `Handled(intid)` arm — spurious INTIDs (>= 1020) and out-of-range
/// INTIDs (in `[MAX_SUPPORTED_INTID, SPURIOUS_THRESHOLD)`) do not
/// advance the counter (they're acknowledged + EOI'd but not
/// dispatched).  This makes the counter semantically equal to "actual
/// IRQs the per-core handler routed" rather than "IAR reads", which
/// is the more useful aggregate for SM5+ scheduler observability.
///
/// Returns the post-increment value (wrapping at `u64::MAX`) so test
/// callers can verify the counter advanced (the production path does
/// not consume the return; the IRQ handler discards it).
#[inline(always)]
pub fn record_irq_dispatch() -> u64 {
    current_per_cpu_stats()
        .irq_count
        .fetch_add(1, Ordering::Relaxed)
        .wrapping_add(1)
}

/// **WS-SM SM1.I.4**: record a timer tick on the calling core.
///
/// Increments both [`PerCpuStats::timer_tick_count`] (the
/// timer-specific counter) for the current core.  IRQ dispatch is
/// counted separately via [`record_irq_dispatch`] — callers in the
/// per-core handler invoke both.
///
/// Returns the post-increment value of `timer_tick_count`.
#[inline(always)]
pub fn record_timer_tick() -> u64 {
    current_per_cpu_stats()
        .timer_tick_count
        .fetch_add(1, Ordering::Relaxed)
        .wrapping_add(1)
}

/// **WS-SM SM1.I.4**: record an SGI dispatch on the calling core.
///
/// Increments [`PerCpuStats::sgi_count`] for the current core.
/// Returns the post-increment value.
#[inline(always)]
pub fn record_sgi_dispatch() -> u64 {
    current_per_cpu_stats()
        .sgi_count
        .fetch_add(1, Ordering::Relaxed)
        .wrapping_add(1)
}

/// **WS-SM SM1.I.4**: record a syscall (SVC) dispatch on the calling
/// core.
///
/// Called from [`crate::trap::handle_synchronous_exception`] before the
/// SVC handler routing.  Returns the post-increment value.
#[inline(always)]
pub fn record_syscall() -> u64 {
    current_per_cpu_stats()
        .syscall_count
        .fetch_add(1, Ordering::Relaxed)
        .wrapping_add(1)
}

/// **WS-SM SM1.I.4**: record a VM fault classification on the calling
/// core.
///
/// Called from `handle_synchronous_exception` for both data and
/// instruction aborts.  Returns the post-increment value.
#[inline(always)]
pub fn record_vm_fault() -> u64 {
    current_per_cpu_stats()
        .vmfault_count
        .fetch_add(1, Ordering::Relaxed)
        .wrapping_add(1)
}

/// **WS-SM SM1.I.4**: record a user-exception classification on the
/// calling core.
///
/// Called from `handle_synchronous_exception` for alignment faults and
/// unknown-EC exceptions.  Returns the post-increment value.
#[inline(always)]
pub fn record_user_exception() -> u64 {
    current_per_cpu_stats()
        .user_exception_count
        .fetch_add(1, Ordering::Relaxed)
        .wrapping_add(1)
}

/// **WS-SM SM1.I.4**: read a specific core's IRQ count (Relaxed
/// snapshot).
///
/// Returns 0 for out-of-range `core_id` (defensive — the production
/// callers always pass `core_id < MAX_SECONDARY_CORES + 1`, but the
/// out-of-range fallback prevents a panic on a misconfigured probe).
///
/// Safe to call from any core (atomics are inherently thread-safe).
/// The snapshot may be slightly stale on hardware because of the
/// `Relaxed` ordering — this is acceptable for a counter readout.
#[inline]
pub fn irq_count_for(core_id: usize) -> u64 {
    if core_id >= PER_CPU_STATS.len() {
        return 0;
    }
    PER_CPU_STATS[core_id].irq_count.load(Ordering::Relaxed)
}

/// **WS-SM SM1.I.4**: read a specific core's timer-tick count.
#[inline]
pub fn timer_tick_count_for(core_id: usize) -> u64 {
    if core_id >= PER_CPU_STATS.len() {
        return 0;
    }
    PER_CPU_STATS[core_id]
        .timer_tick_count
        .load(Ordering::Relaxed)
}

/// **WS-SM SM1.I.4**: read a specific core's SGI count.
#[inline]
pub fn sgi_count_for(core_id: usize) -> u64 {
    if core_id >= PER_CPU_STATS.len() {
        return 0;
    }
    PER_CPU_STATS[core_id].sgi_count.load(Ordering::Relaxed)
}

/// **WS-SM SM1.I.4**: read a specific core's syscall count.
#[inline]
pub fn syscall_count_for(core_id: usize) -> u64 {
    if core_id >= PER_CPU_STATS.len() {
        return 0;
    }
    PER_CPU_STATS[core_id]
        .syscall_count
        .load(Ordering::Relaxed)
}

/// **WS-SM SM1.I.4**: read a specific core's VM-fault count.
#[inline]
pub fn vm_fault_count_for(core_id: usize) -> u64 {
    if core_id >= PER_CPU_STATS.len() {
        return 0;
    }
    PER_CPU_STATS[core_id]
        .vmfault_count
        .load(Ordering::Relaxed)
}

/// **WS-SM SM1.I.4**: read a specific core's user-exception count.
#[inline]
pub fn user_exception_count_for(core_id: usize) -> u64 {
    if core_id >= PER_CPU_STATS.len() {
        return 0;
    }
    PER_CPU_STATS[core_id]
        .user_exception_count
        .load(Ordering::Relaxed)
}

/// **WS-SM SM1.I.4**: read the total IRQ count across all cores.
///
/// Sums every core's `irq_count`.  Useful as a single-line aggregate
/// in a boot diagnostic ("kernel handled N IRQs since boot").
#[inline]
pub fn total_irq_count() -> u64 {
    PER_CPU_STATS
        .iter()
        .map(|s| s.irq_count.load(Ordering::Relaxed))
        .sum()
}

/// **WS-SM SM1.I.4**: read the total syscall count across all cores.
#[inline]
pub fn total_syscall_count() -> u64 {
    PER_CPU_STATS
        .iter()
        .map(|s| s.syscall_count.load(Ordering::Relaxed))
        .sum()
}

// ============================================================================
// Inner forms — testable variants taking explicit slice references
// ============================================================================
//
// The production accessors above route through TPIDR_EL1 (the "current
// core" lookup), which on host always returns slot 0.  Tests that need
// to exercise cross-core stats accumulation use these `_in_slice`
// helpers with stack-local arrays so each test owns its own state.

/// **WS-SM SM1.I.4** (testable inner form): record an IRQ dispatch on
/// a specific slot in an explicit slice.
///
/// Returns the post-increment counter value.  Out-of-range `core_id`
/// is a programming error and panics in debug builds.
#[inline]
pub fn record_irq_dispatch_in_slice(slots: &[PerCpuStats], core_id: usize) -> u64 {
    debug_assert!(
        core_id < slots.len(),
        "WS-SM SM1.I.4: record_irq_dispatch_in_slice: core_id {} out of range",
        core_id
    );
    slots[core_id]
        .irq_count
        .fetch_add(1, Ordering::Relaxed)
        .wrapping_add(1)
}

/// **WS-SM SM1.I.4** (testable inner form): record a timer tick on
/// a specific slot in an explicit slice.
#[inline]
pub fn record_timer_tick_in_slice(slots: &[PerCpuStats], core_id: usize) -> u64 {
    debug_assert!(
        core_id < slots.len(),
        "WS-SM SM1.I.4: record_timer_tick_in_slice: core_id {} out of range",
        core_id
    );
    slots[core_id]
        .timer_tick_count
        .fetch_add(1, Ordering::Relaxed)
        .wrapping_add(1)
}

/// **WS-SM SM1.I.4** (testable inner form): record an SGI dispatch on
/// a specific slot in an explicit slice.
#[inline]
pub fn record_sgi_dispatch_in_slice(slots: &[PerCpuStats], core_id: usize) -> u64 {
    debug_assert!(
        core_id < slots.len(),
        "WS-SM SM1.I.4: record_sgi_dispatch_in_slice: core_id {} out of range",
        core_id
    );
    slots[core_id]
        .sgi_count
        .fetch_add(1, Ordering::Relaxed)
        .wrapping_add(1)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ------------------------------------------------------------------------
    // SM1.I.4.A — struct layout invariants
    // ------------------------------------------------------------------------

    #[test]
    fn sm1i4_per_cpu_stats_is_one_cache_line() {
        // The size assertion at module scope is compile-time; this
        // test confirms the runtime observation matches.
        assert_eq!(core::mem::size_of::<PerCpuStats>(), 64);
    }

    #[test]
    fn sm1i4_per_cpu_stats_is_64_byte_aligned() {
        assert_eq!(core::mem::align_of::<PerCpuStats>(), 64);
    }

    #[test]
    fn sm1i4_per_cpu_stats_zero_constructor_initialises_every_counter() {
        let s = PerCpuStats::zero();
        assert_eq!(s.irq_count.load(Ordering::Relaxed), 0);
        assert_eq!(s.timer_tick_count.load(Ordering::Relaxed), 0);
        assert_eq!(s.sgi_count.load(Ordering::Relaxed), 0);
        assert_eq!(s.syscall_count.load(Ordering::Relaxed), 0);
        assert_eq!(s.vmfault_count.load(Ordering::Relaxed), 0);
        assert_eq!(s.user_exception_count.load(Ordering::Relaxed), 0);
    }

    // ------------------------------------------------------------------------
    // SM1.I.4.B — static array population
    // ------------------------------------------------------------------------

    #[test]
    fn sm1i4_per_cpu_stats_array_has_one_slot_per_core() {
        // Loosely-coupled to MAX_SECONDARY_CORES + 1 = 4 on RPi5.
        assert_eq!(PER_CPU_STATS.len(), MAX_SECONDARY_CORES + 1);
        assert_eq!(PER_CPU_STATS.len(), 4);
    }

    #[test]
    fn sm1i4_per_cpu_stats_array_slots_are_distinct_addresses() {
        // Each core's slot must occupy a distinct cache line; without
        // this, cross-core writes would contend for the same line.
        let addrs: [usize; 4] = [
            &PER_CPU_STATS[0] as *const PerCpuStats as usize,
            &PER_CPU_STATS[1] as *const PerCpuStats as usize,
            &PER_CPU_STATS[2] as *const PerCpuStats as usize,
            &PER_CPU_STATS[3] as *const PerCpuStats as usize,
        ];
        for (i, &ai) in addrs.iter().enumerate() {
            for (j, &aj) in addrs.iter().enumerate().skip(i + 1) {
                assert_ne!(ai, aj, "PER_CPU_STATS[{}] and PER_CPU_STATS[{}] alias", i, j);
            }
        }
    }

    #[test]
    fn sm1i4_per_cpu_stats_array_slots_are_64_byte_aligned() {
        for (i, slot) in PER_CPU_STATS.iter().enumerate() {
            let addr = slot as *const PerCpuStats as usize;
            assert_eq!(
                addr % 64,
                0,
                "PER_CPU_STATS[{}] = {:#x} not 64-byte aligned",
                i,
                addr
            );
        }
    }

    #[test]
    fn sm1i4_per_cpu_stats_array_stride_matches_struct_size() {
        // PER_CPU_STATS has MAX_SECONDARY_CORES + 1 = 4 slots on RPi5.
        // Use a fixed-size array (no_std-friendly; no `Vec` allocation).
        let addrs: [usize; 4] = [
            &PER_CPU_STATS[0] as *const PerCpuStats as usize,
            &PER_CPU_STATS[1] as *const PerCpuStats as usize,
            &PER_CPU_STATS[2] as *const PerCpuStats as usize,
            &PER_CPU_STATS[3] as *const PerCpuStats as usize,
        ];
        for (i, w) in addrs.windows(2).enumerate() {
            assert_eq!(
                w[1] - w[0],
                core::mem::size_of::<PerCpuStats>(),
                "PER_CPU_STATS stride between slots {} and {}",
                i,
                i + 1
            );
        }
    }

    // ------------------------------------------------------------------------
    // SM1.I.4.C — current-core accessor (host: slot 0)
    // ------------------------------------------------------------------------

    #[test]
    fn sm1i4_current_per_cpu_stats_on_host_returns_slot_zero() {
        // Host stub: `current_core_id_from_tpidr` returns 0, so we
        // get slot 0.  Address comparison is the strict identity
        // check.
        let cs = current_per_cpu_stats();
        let cs_addr = cs as *const PerCpuStats as usize;
        let slot0_addr = &PER_CPU_STATS[0] as *const PerCpuStats as usize;
        assert_eq!(cs_addr, slot0_addr);
    }

    // ------------------------------------------------------------------------
    // SM1.I.4.D — inner-form recorders (test-only, stack-local state)
    // ------------------------------------------------------------------------

    fn fresh_stats_array() -> [PerCpuStats; 4] {
        [
            PerCpuStats::zero(),
            PerCpuStats::zero(),
            PerCpuStats::zero(),
            PerCpuStats::zero(),
        ]
    }

    #[test]
    fn sm1i4_record_irq_dispatch_in_slice_increments_only_named_slot() {
        let slots = fresh_stats_array();
        let v = record_irq_dispatch_in_slice(&slots, 2);
        assert_eq!(v, 1);
        assert_eq!(slots[0].irq_count.load(Ordering::Relaxed), 0);
        assert_eq!(slots[1].irq_count.load(Ordering::Relaxed), 0);
        assert_eq!(slots[2].irq_count.load(Ordering::Relaxed), 1);
        assert_eq!(slots[3].irq_count.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn sm1i4_record_irq_dispatch_in_slice_returns_post_increment_value() {
        let slots = fresh_stats_array();
        assert_eq!(record_irq_dispatch_in_slice(&slots, 1), 1);
        assert_eq!(record_irq_dispatch_in_slice(&slots, 1), 2);
        assert_eq!(record_irq_dispatch_in_slice(&slots, 1), 3);
    }

    #[test]
    fn sm1i4_record_timer_tick_in_slice_independent_of_irq_count() {
        // Per-counter independence: incrementing `timer_tick_count`
        // does not increment `irq_count` in the inner form (the
        // production handler increments both separately).
        let slots = fresh_stats_array();
        let _ = record_timer_tick_in_slice(&slots, 0);
        assert_eq!(slots[0].timer_tick_count.load(Ordering::Relaxed), 1);
        assert_eq!(slots[0].irq_count.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn sm1i4_record_sgi_dispatch_in_slice_independent_of_other_counters() {
        let slots = fresh_stats_array();
        let _ = record_sgi_dispatch_in_slice(&slots, 3);
        assert_eq!(slots[3].sgi_count.load(Ordering::Relaxed), 1);
        assert_eq!(slots[3].irq_count.load(Ordering::Relaxed), 0);
        assert_eq!(slots[3].timer_tick_count.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn sm1i4_recorders_in_slice_accumulate_across_all_slots() {
        let slots = fresh_stats_array();
        // Simulate: every core takes one timer tick.
        for i in 0..slots.len() {
            let _ = record_irq_dispatch_in_slice(&slots, i);
            let _ = record_timer_tick_in_slice(&slots, i);
        }
        let total_irq: u64 = slots
            .iter()
            .map(|s| s.irq_count.load(Ordering::Relaxed))
            .sum();
        let total_ticks: u64 = slots
            .iter()
            .map(|s| s.timer_tick_count.load(Ordering::Relaxed))
            .sum();
        assert_eq!(total_irq, slots.len() as u64);
        assert_eq!(total_ticks, slots.len() as u64);
    }

    // ------------------------------------------------------------------------
    // SM1.I.4.E — Out-of-range reads return 0 (defensive)
    // ------------------------------------------------------------------------

    #[test]
    fn sm1i4_irq_count_for_out_of_range_returns_zero() {
        // Defensive: an out-of-range probe must not panic.
        assert_eq!(irq_count_for(PER_CPU_STATS.len()), 0);
        assert_eq!(irq_count_for(usize::MAX), 0);
    }

    #[test]
    fn sm1i4_all_per_core_reads_return_zero_for_out_of_range() {
        let bad = PER_CPU_STATS.len() + 100;
        assert_eq!(irq_count_for(bad), 0);
        assert_eq!(timer_tick_count_for(bad), 0);
        assert_eq!(sgi_count_for(bad), 0);
        assert_eq!(syscall_count_for(bad), 0);
        assert_eq!(vm_fault_count_for(bad), 0);
        assert_eq!(user_exception_count_for(bad), 0);
    }

    // ------------------------------------------------------------------------
    // SM1.I.4.F — Inner-form panic on out-of-range (debug builds)
    // ------------------------------------------------------------------------

    #[test]
    #[should_panic(expected = "core_id 4 out of range")]
    fn sm1i4_record_irq_dispatch_in_slice_panics_on_out_of_range() {
        let slots = fresh_stats_array();
        let _ = record_irq_dispatch_in_slice(&slots, 4);
    }

    // ------------------------------------------------------------------------
    // SM1.I.4.G — Audit-pass-1: wrapping-add overflow defense
    //
    // The `record_*` functions return `fetch_add(1).wrapping_add(1)`.
    // Audit-pass-1 changed the post-fetch arithmetic from `+ 1` (which
    // would panic in debug builds on `u64::MAX + 1`) to
    // `.wrapping_add(1)` so the counter behavior is well-defined at
    // every input.  Practically a counter reaching u64::MAX would
    // take >200 years at GHz frequency, but defensive coding requires
    // a defined behavior at the boundary.
    //
    // These tests seed the counter near u64::MAX via the `pub`
    // `AtomicU64` field, then verify the `record_*_in_slice`
    // functions correctly wrap.
    // ------------------------------------------------------------------------

    #[test]
    fn sm1i4_record_irq_dispatch_in_slice_wraps_at_u64_max() {
        // Pre-seed the counter to u64::MAX - 1 and verify two
        // increments produce u64::MAX then 0 (wrapping).
        let slots = fresh_stats_array();
        slots[0].irq_count.store(u64::MAX - 1, Ordering::Relaxed);
        let v1 = record_irq_dispatch_in_slice(&slots, 0);
        assert_eq!(v1, u64::MAX, "first increment should produce u64::MAX");
        let v2 = record_irq_dispatch_in_slice(&slots, 0);
        assert_eq!(v2, 0, "second increment must wrap to 0 (not panic)");
        let v3 = record_irq_dispatch_in_slice(&slots, 0);
        assert_eq!(v3, 1, "third increment after wrap should produce 1");
    }

    #[test]
    fn sm1i4_record_timer_tick_in_slice_wraps_at_u64_max() {
        let slots = fresh_stats_array();
        slots[1].timer_tick_count.store(u64::MAX, Ordering::Relaxed);
        let v = record_timer_tick_in_slice(&slots, 1);
        assert_eq!(v, 0, "increment of u64::MAX counter must wrap");
    }

    #[test]
    fn sm1i4_record_sgi_dispatch_in_slice_wraps_at_u64_max() {
        let slots = fresh_stats_array();
        slots[2].sgi_count.store(u64::MAX, Ordering::Relaxed);
        let v = record_sgi_dispatch_in_slice(&slots, 2);
        assert_eq!(v, 0, "increment of u64::MAX counter must wrap");
    }
}
