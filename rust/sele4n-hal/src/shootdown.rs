// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-SM SM7.A.3**: per-core TLB-shootdown acknowledgment flags.
//!
//! The runtime realisation of the Lean model's
//! `TlbShootdownState.shootdownAck : Vector Bool numCores`
//! (`SeLe4n/Kernel/Architecture/TlbShootdown.lean`).  One
//! cache-line-aligned [`AtomicBool`] per core, polled by the shootdown
//! initiator and set by each target's `.tlbShootdownReq` SGI handler
//! (INTID 1; see the SGI reservation table in [`crate::gic`]).
//!
//! ## Protocol role (SMP_TLB_SHOOTDOWN_PLAN.md §3.2, §4.2)
//!
//! A shootdown round for `(asid, vaddr)` initiated by core `c₀`:
//!
//! 1. `c₀` calls [`reset_for_round`]`(c₀)` — every flag drops to
//!    `false` except `c₀`'s own (the initiator invalidates locally and
//!    is never waited on).
//! 2. `c₀` posts one descriptor per target into the Lean-side pending
//!    queues, then fires a `.tlbShootdownReq` SGI per target.
//!    [`crate::gic::send_sgi`] emits `dsb ish` **before** the GICD_SGIR
//!    write (SM1.F.8), so the flag clears from step 1 — and the queue
//!    writes — are globally observable before any target can take the
//!    interrupt.
//! 3. Each target's handler drains its queue, executes one local TLBI
//!    per descriptor, retires them (`dsb`), and only then calls
//!    [`ack_set`] — a **release**-store.
//! 4. `c₀` polls [`all_acked`] (**acquire**-loads, WFE-paced at
//!    SM7.B.5).  The release-acquire pairing guarantees that when `c₀`
//!    observes a target's `true`, that target's TLBI completion
//!    happens-before the observation — the synchronisation edge
//!    Theorem 3.3.1's remote-core case rests on (formalised against
//!    the SM2.A memory model at SM7.B.4, `shootdownAck_release_acquire`).
//!
//! ## Why `Relaxed` suffices for the round reset
//!
//! [`reset_for_round`]'s stores are `Relaxed` because both consumers
//! are already ordered by stronger mechanisms:
//!
//! * **Targets** never load their own flag — the clear only has to be
//!   visible before the target's handler *sets* the flag, and the
//!   `dsb ish` inside [`crate::gic::send_sgi`] orders the clear before
//!   the SGI that triggers the handler (ARM ARM B2.7: DSB completes
//!   all prior accesses before the SGIR write is issued).
//! * **The initiator's own poll** observes its prior store by
//!   same-location program-order coherence.
//!
//! Cross-round interference is excluded structurally: the VSpaceRoot
//! write lock serialises initiators, and a new round's reset
//! happens-after every previous-round ack-set (the previous initiator
//! only released the lock after its acquire-poll observed every ack,
//! which synchronises-with each release-set).  A straggling handler
//! from round *N* therefore cannot overwrite round *N+1*'s reset.
//!
//! ## Boot state
//!
//! All flags boot `true` — the quiescent "no round in flight, nobody
//! waited on" state, matching the Lean model's
//! `TlbShootdownState.initial` (`initial_ackOnCore`) so the very first
//! [`all_acked`] poll before any round would trivially succeed rather
//! than deadlock.
//!
//! ## Layout
//!
//! Each flag owns a full 64-byte cache line ([`ShootdownAckFlag`],
//! `repr(C, align(64))`) so a target's release-store does not
//! ping-pong the line under the initiator's poll of *other* targets'
//! flags — the same false-sharing discipline as
//! [`crate::per_cpu_stats::PerCpuStats`] and [`crate::per_cpu::PerCpuData`].
//!
//! ## Host (non-aarch64) behaviour
//!
//! Everything here is portable atomics — every entry point compiles
//! and executes identically under host `cargo test`.  Unit tests
//! mutate stack-local slices via the `_in_slice` inner forms (the
//! global [`SHOOTDOWN_ACK`] is only read, so parallel test threads
//! never race on it).

use core::sync::atomic::{AtomicBool, Ordering};

use crate::smp::MAX_SECONDARY_CORES;

/// **WS-SM SM7.A.3**: one core's shootdown-acknowledgment flag,
/// padded to a full cache line (64 bytes on Cortex-A76) to eliminate
/// false sharing between the per-core flags.
///
/// The explicit `_reserved` tail keeps every byte of the slot
/// deterministically initialised (no padding-byte hazards) and pins
/// the size independently of the alignment attribute.
#[repr(C, align(64))]
pub struct ShootdownAckFlag {
    /// `true` once this core has completed (and locally retired) every
    /// invalidation of the current shootdown round.  Set with
    /// `Ordering::Release` by the owning core's SGI handler; polled
    /// with `Ordering::Acquire` by the round initiator.
    pub acked: AtomicBool,
    /// Padding to a full cache line; reserved for SM7.B+ additions
    /// (e.g., a per-core drained-descriptor diagnostic counter).
    _reserved: [u8; 63],
}

impl ShootdownAckFlag {
    /// **WS-SM SM7.A.3**: const constructor with an explicit initial
    /// value.  `const fn` because [`SHOOTDOWN_ACK`] is a `static`.
    #[inline]
    pub const fn new(initial: bool) -> Self {
        Self {
            acked: AtomicBool::new(initial),
            _reserved: [0; 63],
        }
    }

    /// **WS-SM SM7.A.3**: the boot value — acknowledged (`true`),
    /// i.e. quiescent: no shootdown round is in flight, so nobody is
    /// waited on.  Matches the Lean `TlbShootdownState.initial`
    /// (`initial_ackOnCore = true`).
    #[inline]
    pub const fn acked_at_boot() -> Self {
        Self::new(true)
    }
}

/// **WS-SM SM7.A.3**: the per-core shootdown-acknowledgment flags,
/// one cache-line-aligned slot per core, indexed by `core_id`
/// (0..=`MAX_SECONDARY_CORES`).  All slots boot `true` (quiescent).
///
/// `#[no_mangle]` + `#[used]` preserve the symbol so a hardware-side
/// debug probe can resolve it via the linker map, mirroring
/// [`crate::per_cpu_stats::PER_CPU_STATS`].
#[no_mangle]
#[used]
pub static SHOOTDOWN_ACK: [ShootdownAckFlag; MAX_SECONDARY_CORES + 1] = [
    ShootdownAckFlag::acked_at_boot(),
    ShootdownAckFlag::acked_at_boot(),
    ShootdownAckFlag::acked_at_boot(),
    ShootdownAckFlag::acked_at_boot(),
];

// Compile-time pin: each flag owns exactly one cache line.  Growing the
// struct past 64 bytes (e.g. adding a field without shrinking the
// `_reserved` tail) fails the build here with a clear diagnostic.
const _: () = assert!(
    core::mem::size_of::<ShootdownAckFlag>() == 64,
    "WS-SM SM7.A.3: ShootdownAckFlag must be one cache line (64 bytes); \
     shrink the `_reserved` tail when adding a field to stay within budget"
);

// Compile-time pin: cache-line aligned to avoid false sharing between
// adjacent cores' flags.
const _: () = assert!(
    core::mem::align_of::<ShootdownAckFlag>() == 64,
    "WS-SM SM7.A.3: ShootdownAckFlag must be 64-byte aligned to avoid \
     false sharing"
);

// ============================================================================
// Inner forms — testable variants taking explicit slice references
// ============================================================================
//
// The production accessors below operate on the global [`SHOOTDOWN_ACK`]
// array.  Host unit tests exercise cross-core round lifecycles on
// stack-local arrays through these `_in_slice` forms so parallel test
// threads never mutate shared state; the production wrappers delegate
// here so the tested logic and the shipped logic are the same code.

/// **WS-SM SM7.A.3** (testable inner form): release-set one core's
/// acknowledgment flag in an explicit slice.
///
/// Out-of-range `core_id` is a protocol violation and panics
/// (fail-closed): silently ignoring the set would leave the initiator
/// waiting forever; aliasing to another slot would falsely acknowledge
/// a core whose TLB may still hold the stale entry — the exact SMP-C4
/// hazard SM7 exists to close.  Callers routed from the Lean side pass
/// a `CoreId = Fin numCores`, so the panic arm is structurally
/// unreachable from well-typed kernel code.
#[inline]
pub fn ack_set_in_slice(slots: &[ShootdownAckFlag], core_id: usize) {
    assert!(
        core_id < slots.len(),
        "WS-SM SM7.A.3: ack_set_in_slice: core_id {} out of range (expected < {})",
        core_id,
        slots.len()
    );
    slots[core_id].acked.store(true, Ordering::Release);
}

/// **WS-SM SM7.A.3** (testable inner form): acquire-load one core's
/// acknowledgment flag from an explicit slice.
///
/// Panics on out-of-range `core_id` (fail-closed; see
/// [`ack_set_in_slice`]).
#[inline]
pub fn ack_is_set_in_slice(slots: &[ShootdownAckFlag], core_id: usize) -> bool {
    assert!(
        core_id < slots.len(),
        "WS-SM SM7.A.3: ack_is_set_in_slice: core_id {} out of range (expected < {})",
        core_id,
        slots.len()
    );
    slots[core_id].acked.load(Ordering::Acquire)
}

/// **WS-SM SM7.A.3** (testable inner form): open a new shootdown round
/// in an explicit slice — every flag drops to `false` except the
/// initiator's own, which is born-`true` (the initiator invalidates
/// locally and is never waited on).  Mirrors the Lean
/// `beginShootdownRound` exactly (`beginShootdownRound_ackOnCore_iff`).
///
/// Stores are `Relaxed`; see the module docs for why the `dsb ish`
/// inside [`crate::gic::send_sgi`] (SM1.F.8) plus same-location
/// coherence make that sufficient.  Panics on out-of-range `initiator`
/// (fail-closed).
#[inline]
pub fn reset_for_round_in_slice(slots: &[ShootdownAckFlag], initiator: usize) {
    assert!(
        initiator < slots.len(),
        "WS-SM SM7.A.3: reset_for_round_in_slice: initiator {} out of range (expected < {})",
        initiator,
        slots.len()
    );
    for (i, slot) in slots.iter().enumerate() {
        slot.acked.store(i == initiator, Ordering::Relaxed);
    }
}

/// **WS-SM SM7.A.3** (testable inner form): acquire-poll every flag in
/// an explicit slice — the initiator wait-loop's exit condition
/// (plan §3.2 step 5).  Mirrors the Lean `allAcked` predicate.
#[inline]
pub fn all_acked_in_slice(slots: &[ShootdownAckFlag]) -> bool {
    slots.iter().all(|s| s.acked.load(Ordering::Acquire))
}

// ============================================================================
// Production accessors over the global SHOOTDOWN_ACK array
// ============================================================================

/// **WS-SM SM7.A.3**: release-set the given core's acknowledgment flag
/// in [`SHOOTDOWN_ACK`].
///
/// Called by a target core's `.tlbShootdownReq` SGI handler (SM7.B.3)
/// only *after* its drained invalidations have retired locally — the
/// release edge of the SM7.B.4 release-acquire pairing.  Panics on
/// out-of-range `core_id` (fail-closed; see [`ack_set_in_slice`]).
#[inline]
pub fn ack_set(core_id: usize) {
    ack_set_in_slice(&SHOOTDOWN_ACK, core_id);
}

/// **WS-SM SM7.A.3**: acquire-load the given core's acknowledgment
/// flag from [`SHOOTDOWN_ACK`].  Panics on out-of-range `core_id`
/// (fail-closed).
#[inline]
pub fn ack_is_set(core_id: usize) -> bool {
    ack_is_set_in_slice(&SHOOTDOWN_ACK, core_id)
}

/// **WS-SM SM7.A.3**: open a new shootdown round in [`SHOOTDOWN_ACK`]
/// — the runtime realisation of the Lean `beginShootdownRound`
/// (plan §3.2 step 1).  Must only be called by the round initiator
/// while it holds the serialising VSpaceRoot write lock (SM7.B.7);
/// panics on out-of-range `initiator` (fail-closed).
#[inline]
pub fn reset_for_round(initiator: usize) {
    reset_for_round_in_slice(&SHOOTDOWN_ACK, initiator);
}

/// **WS-SM SM7.A.3**: acquire-poll every flag in [`SHOOTDOWN_ACK`] —
/// the initiator wait-loop's exit condition (plan §3.2 step 5;
/// WFE-paced by SM7.B.5's bounded wait).
#[inline]
pub fn all_acked() -> bool {
    all_acked_in_slice(&SHOOTDOWN_ACK)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ------------------------------------------------------------------------
    // SM7.A.3.A — struct layout invariants
    // ------------------------------------------------------------------------

    #[test]
    fn sm7a3_shootdown_ack_flag_is_one_cache_line() {
        // The module-scope assertion is compile-time; this confirms the
        // runtime observation matches.
        assert_eq!(core::mem::size_of::<ShootdownAckFlag>(), 64);
    }

    #[test]
    fn sm7a3_shootdown_ack_flag_is_64_byte_aligned() {
        assert_eq!(core::mem::align_of::<ShootdownAckFlag>(), 64);
    }

    #[test]
    fn sm7a3_new_constructor_sets_requested_initial_value() {
        let t = ShootdownAckFlag::new(true);
        let f = ShootdownAckFlag::new(false);
        assert!(t.acked.load(Ordering::Acquire));
        assert!(!f.acked.load(Ordering::Acquire));
    }

    #[test]
    fn sm7a3_boot_constructor_is_acknowledged() {
        // Quiescent boot: `true` = "no round in flight, nobody waited
        // on", matching Lean `TlbShootdownState.initial_ackOnCore`.
        let s = ShootdownAckFlag::acked_at_boot();
        assert!(s.acked.load(Ordering::Acquire));
    }

    // ------------------------------------------------------------------------
    // SM7.A.3.B — global array population (read-only: parallel tests
    // must never mutate SHOOTDOWN_ACK)
    // ------------------------------------------------------------------------

    #[test]
    fn sm7a3_shootdown_ack_array_has_one_slot_per_core() {
        assert_eq!(SHOOTDOWN_ACK.len(), MAX_SECONDARY_CORES + 1);
        assert_eq!(SHOOTDOWN_ACK.len(), 4);
    }

    #[test]
    fn sm7a3_shootdown_ack_boots_quiescent_all_acknowledged() {
        // No test in this binary mutates the global array (all
        // behaviour tests use stack-local slices), so the boot values
        // are stable under parallel test execution.
        assert!(all_acked());
        for core_id in 0..SHOOTDOWN_ACK.len() {
            assert!(
                ack_is_set(core_id),
                "core {} must boot acknowledged",
                core_id
            );
        }
    }

    #[test]
    fn sm7a3_shootdown_ack_array_slots_are_distinct_cache_lines() {
        let addrs: [usize; 4] = [
            &SHOOTDOWN_ACK[0] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[1] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[2] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[3] as *const ShootdownAckFlag as usize,
        ];
        for (i, &ai) in addrs.iter().enumerate() {
            assert_eq!(
                ai % 64,
                0,
                "SHOOTDOWN_ACK[{}] = {:#x} not 64-byte aligned",
                i,
                ai
            );
            for (j, &aj) in addrs.iter().enumerate().skip(i + 1) {
                assert_ne!(
                    ai, aj,
                    "SHOOTDOWN_ACK[{}] and SHOOTDOWN_ACK[{}] alias",
                    i, j
                );
            }
        }
    }

    #[test]
    fn sm7a3_shootdown_ack_array_stride_matches_struct_size() {
        let addrs: [usize; 4] = [
            &SHOOTDOWN_ACK[0] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[1] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[2] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[3] as *const ShootdownAckFlag as usize,
        ];
        for (i, w) in addrs.windows(2).enumerate() {
            assert_eq!(
                w[1] - w[0],
                core::mem::size_of::<ShootdownAckFlag>(),
                "SHOOTDOWN_ACK stride between slots {} and {}",
                i,
                i + 1
            );
        }
    }

    // ------------------------------------------------------------------------
    // SM7.A.3.C — round lifecycle on stack-local slices
    // ------------------------------------------------------------------------

    fn fresh_boot_flags() -> [ShootdownAckFlag; 4] {
        [
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
        ]
    }

    #[test]
    fn sm7a3_reset_for_round_marks_only_initiator_acknowledged() {
        // Mirrors Lean `beginShootdownRound_ackOnCore_iff`: acked ⟺
        // core == initiator.
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 0);
        assert!(ack_is_set_in_slice(&slots, 0));
        assert!(!ack_is_set_in_slice(&slots, 1));
        assert!(!ack_is_set_in_slice(&slots, 2));
        assert!(!ack_is_set_in_slice(&slots, 3));
    }

    #[test]
    fn sm7a3_reset_for_round_works_for_every_initiator() {
        for initiator in 0..4usize {
            let slots = fresh_boot_flags();
            reset_for_round_in_slice(&slots, initiator);
            for (core, slot) in slots.iter().enumerate() {
                assert_eq!(
                    slot.acked.load(Ordering::Acquire),
                    core == initiator,
                    "round by initiator {}: core {} flag wrong",
                    initiator,
                    core
                );
            }
        }
    }

    #[test]
    fn sm7a3_ack_set_marks_exactly_the_named_core() {
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 0);
        ack_set_in_slice(&slots, 2);
        assert!(
            ack_is_set_in_slice(&slots, 0),
            "initiator stays acknowledged"
        );
        assert!(!ack_is_set_in_slice(&slots, 1), "core 1 untouched");
        assert!(ack_is_set_in_slice(&slots, 2), "core 2 now acknowledged");
        assert!(!ack_is_set_in_slice(&slots, 3), "core 3 untouched");
    }

    #[test]
    fn sm7a3_ack_set_is_idempotent() {
        // A spurious duplicate .tlbShootdownReq SGI re-acknowledges
        // harmlessly (its drain returns nothing; the re-set is a no-op).
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 1);
        ack_set_in_slice(&slots, 3);
        ack_set_in_slice(&slots, 3);
        assert!(ack_is_set_in_slice(&slots, 3));
        assert!(!ack_is_set_in_slice(&slots, 0));
        assert!(!ack_is_set_in_slice(&slots, 2));
    }

    #[test]
    fn sm7a3_all_acked_false_while_any_target_outstanding() {
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 0);
        assert!(!all_acked_in_slice(&slots), "3 targets outstanding");
        ack_set_in_slice(&slots, 1);
        assert!(!all_acked_in_slice(&slots), "2 targets outstanding");
        ack_set_in_slice(&slots, 2);
        assert!(!all_acked_in_slice(&slots), "1 target outstanding");
    }

    #[test]
    fn sm7a3_full_round_trip_reaches_all_acked() {
        // The wait-loop termination anchor at runtime: reset, then
        // every target acknowledges → all_acked.  Mirrors the Lean
        // `allCores_foldl_acknowledgeShootdown_allAcked`.
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 2);
        for target in [0usize, 1, 3] {
            ack_set_in_slice(&slots, target);
        }
        assert!(all_acked_in_slice(&slots));
    }

    #[test]
    fn sm7a3_back_to_back_rounds_reset_cleanly() {
        // Round N completes, round N+1 (different initiator) must see
        // a clean reset — no acknowledgment leaks across rounds.
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 0);
        for target in [1usize, 2, 3] {
            ack_set_in_slice(&slots, target);
        }
        assert!(all_acked_in_slice(&slots), "round N complete");
        reset_for_round_in_slice(&slots, 3);
        assert!(!all_acked_in_slice(&slots), "round N+1 freshly open");
        assert!(
            ack_is_set_in_slice(&slots, 3),
            "new initiator born-acknowledged"
        );
        assert!(
            !ack_is_set_in_slice(&slots, 0),
            "previous initiator now a target"
        );
    }

    #[test]
    fn sm7a3_empty_slice_is_vacuously_all_acked() {
        // Degenerate input: `all` over an empty iterator is true.  The
        // production array is never empty (4 slots), but the inner form
        // must be total.
        let slots: [ShootdownAckFlag; 0] = [];
        assert!(all_acked_in_slice(&slots));
    }

    // ------------------------------------------------------------------------
    // SM7.A.3.D — fail-closed bounds enforcement
    // ------------------------------------------------------------------------

    #[test]
    #[should_panic(expected = "ack_set_in_slice: core_id 4 out of range")]
    fn sm7a3_ack_set_panics_on_out_of_range_core() {
        let slots = fresh_boot_flags();
        ack_set_in_slice(&slots, 4);
    }

    #[test]
    #[should_panic(expected = "ack_is_set_in_slice: core_id 7 out of range")]
    fn sm7a3_ack_is_set_panics_on_out_of_range_core() {
        let slots = fresh_boot_flags();
        let _ = ack_is_set_in_slice(&slots, 7);
    }

    #[test]
    #[should_panic(expected = "reset_for_round_in_slice: initiator 4 out of range")]
    fn sm7a3_reset_for_round_panics_on_out_of_range_initiator() {
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 4);
    }
}
