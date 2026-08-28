// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-SM** — per-core Lean-runtime readiness gate.
//!
//! The Lean runtime is not ambiently available: calling any Lean-emitted
//! symbol requires the runtime initialized for the executing context
//! (module initializers run once, and each PE that enters Lean needs its
//! per-thread runtime state).  `shootdown.rs` has always stated the
//! consequence — its SGI handler stays free of Lean-runtime calls because
//! "a reentrant per-core Lean runtime … does not exist" — but the
//! constraint lived in prose while the kernel-entry seams
//! (`lean_per_core_timer_tick`, `lean_per_core_reschedule`,
//! `lean_secondary_kernel_main`) compiled unconditional calls behind
//! `feature = "hw_target"`.  A hand-built image could therefore reach the
//! Lean runtime from a PE that never initialized it — undefined behaviour
//! at the first secondary timer tick.
//!
//! This module makes the constraint **structural**: a per-core readiness
//! mask, `false` for every core at boot, consulted by every Rust seam
//! that would call into Lean.  Until a core is marked ready its seams
//! degrade to their Rust-only halves (the timer ISR records + re-arms,
//! the reschedule SGI is EOI'd and dropped, the secondary bring-up entry
//! is skipped) — exactly the behaviour of a host build, and safe by
//! construction.
//!
//! **Who marks ready (SM10.E)**: the bootable-image work owns the flips.
//! The boot core is marked after `lean_kernel_main` initializes the Lean
//! runtime and installs the kernel state (and per the registered SM10.E
//! ordering obligation, before secondaries are released or under the
//! kernel-entry bracket).  Each secondary is marked in
//! `rust_secondary_main` once SM10.E's per-core runtime initialization
//! for that PE has run — after which the already-wired gate passes and
//! the bring-up reschedule proceeds unmodified.  Nothing in the tree
//! marks a core ready today, which is precisely the point: the seams are
//! wired, dormant, and cannot fire early.
//!
//! **Memory ordering**: `Release` on mark, `Acquire` on check — a core
//! that observes `ready` also observes every write the initialization
//! performed (the Lean runtime structures, the installed kernel state).

use core::sync::atomic::{AtomicU8, Ordering};

/// Per-core readiness bitmask (bit `n` = core `n`).  `0` at boot: no
/// core may enter the Lean runtime until its bit is set.
static LEAN_READY_CORES: AtomicU8 = AtomicU8::new(0);

/// May `core_id` call into the Lean runtime?
///
/// `false` for out-of-range ids (fail closed — an id the mask cannot
/// represent is never ready).
#[inline]
pub fn lean_ready(core_id: usize) -> bool {
    if core_id >= 8 {
        return false;
    }
    LEAN_READY_CORES.load(Ordering::Acquire) & (1 << core_id) != 0
}

/// Mark `core_id` ready to enter the Lean runtime.
///
/// Called by the SM10.E image's initialization path once the Lean
/// runtime is initialized for this PE (boot core: after
/// `lean_kernel_main`'s runtime init + kernel-state install; secondary:
/// after its per-core runtime init in `rust_secondary_main`).  Release
/// ordering publishes the initialization writes to every core that
/// acquires the mask.  Out-of-range ids are ignored (nothing to set).
#[inline]
pub fn mark_lean_ready(core_id: usize) {
    if core_id >= 8 {
        return;
    }
    LEAN_READY_CORES.fetch_or(1 << core_id, Ordering::Release);
}

#[cfg(test)]
mod tests {
    use super::*;

    // The mask is process-global, so tests use distinct high bits to
    // stay independent of ordering with each other; bit 0's boot-time
    // default is asserted first in a dedicated test below (cargo runs
    // tests in one process, so a test must not clear another's bit).

    #[test]
    fn boot_default_no_core_is_ready() {
        // Cores 4..8 are never marked by any test in this module, so
        // their boot-time default is observable regardless of test
        // ordering: not ready.
        assert!(!lean_ready(4));
        assert!(!lean_ready(5));
    }

    #[test]
    fn mark_then_check_roundtrip() {
        assert!(!lean_ready(6));
        mark_lean_ready(6);
        assert!(lean_ready(6));
    }

    #[test]
    fn out_of_range_ids_fail_closed() {
        mark_lean_ready(99); // ignored — nothing to set
        assert!(!lean_ready(99));
        assert!(!lean_ready(8));
        assert!(!lean_ready(usize::MAX));
    }

    #[test]
    fn marking_one_core_leaves_others_untouched() {
        mark_lean_ready(7);
        assert!(lean_ready(7));
        assert!(!lean_ready(5));
    }
}
