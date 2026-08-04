// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-SM SM5.I** — kernel-entry serialisation.
//!
//! Every kernel entry commits its post-state through
//! `Platform.FFI.modifyGetKernelState`, which is an `IO.Ref.modifyGet`:
//! a read followed by a write, **not** a cross-core atomic. Two cores
//! committing concurrently both read `st`, both compute a post-state
//! from it, and the second write installs a state derived from a
//! pre-state that no longer holds — discarding the first core's entire
//! transition while telling its caller the syscall succeeded.
//!
//! No theorem is false because of this: kernel transitions are pure
//! functions and the theorems say what those functions compute. What a
//! lost update breaks is the *tie* between theorem and runtime — the
//! committed state stops being the one the verified function was
//! applied to. `preserves_foreign` (SM7.F.3) is the clearest casualty:
//! it guarantees a concurrent round's descriptors survive the catch-up,
//! which is worth having exactly once concurrent commits cannot destroy
//! each other wholesale.
//!
//! This module is the lock that closes it. Until it landed, five sites
//! across Lean and Rust described a serialisation that did not exist,
//! naming three mutually exclusive mechanisms — `IO.Ref` atomicity
//! (false of the primitive), a kernel-entry lock the trap handler holds
//! (absent), and per-object fine locks already in force (deferred by
//! SM3.C.9). All five now describe *this*.
//!
//! # What it protects
//!
//! Every Lean entry that commits kernel state — all three:
//!
//! | Lean export | Rust bracket |
//! |---|---|
//! | `lean_syscall_dispatch_cross_core` | `svc_dispatch::dispatch_svc` |
//! | `lean_per_core_timer_tick`         | `timer::handle_timer_interrupt` |
//! | `suspend_thread_cross_core`        | `ffi::sele4n_suspend_thread` |
//!
//! The third is the one to watch for: it reaches Lean through
//! `sele4n_suspend_thread` rather than a `lean_*` symbol, so a sweep
//! for `lean_` does not find it. A lost suspend is a thread that keeps
//! running after its caller was told it stopped.
//!
//! `lean_kernel_main` and `lean_secondary_kernel_main` are deliberately
//! **not** bracketed: they are bring-up entries that run before their
//! core participates in concurrent kernel entry, and `lean_kernel_main`
//! runs before any secondary exists at all.
//!
//! `syscall_dispatch_inner` and `suspend_thread_inner` are the legacy
//! boot-pinned seams the cross-core entries replaced; they are not
//! reachable from the trap path and are not bracketed.
//!
//! # Why the spin self-services
//!
//! The obvious implementation — spin on the lock — deadlocks, and the
//! deadlock is reachable rather than theoretical:
//!
//! 1. core A holds this lock inside a syscall, reaches
//!    `completeShootdownRounds`, opens a shootdown round and blocks
//!    waiting for core B's acknowledgment;
//! 2. core B is spinning here for the same lock;
//! 3. B can only acknowledge from its `.tlbShootdownReq` SGI handler,
//!    and **IRQs are masked on both kernel-entry paths**, so that SGI
//!    cannot preempt B's spin;
//! 4. A waits for an acknowledgment B cannot send; B waits for a lock A
//!    cannot release. Both cores hang until A's 10 ms shootdown
//!    deadline fires the fail-closed halt.
//!
//! Enabling interrupts around the spin does not fix this and makes it
//! worse: an IRQ taken mid-spin re-enters the kernel on a core that is
//! already queued for a non-reentrant lock, so the timer tick would
//! deadlock against its own core's pending syscall.
//!
//! The fix is the one SM7.B.7 already uses for the round lock: a waiter
//! **discharges its own obligation** instead of waiting to be
//! interrupted. On every failed poll a waiter calls
//! [`crate::shootdown::self_service_round`], which invalidates locally
//! and acknowledges the published round if this core owes one — the
//! same effect the SGI handler would have had, minus the interrupt.
//! So A's round always completes and A always releases.
//!
//! # Lock ordering
//!
//! This lock is acquired strictly **outside**
//! [`crate::shootdown::SHOOTDOWN_ROUND_LOCK`]: an entry takes this
//! lock, and only then may the transition it runs take the round lock.
//! Nothing acquires this lock while holding a round lock, so the order
//! is total and no cycle exists. [`assert_not_holding_round_lock`]
//! checks the direction that would create one.
//!
//! # Fairness and the WCRT bound
//!
//! Backed by the SM2 verified [`TicketLock`], so entry is FIFO: a core
//! cannot be starved by a neighbour that re-enters in a tight loop, and
//! the WCRT argument's "single lock, queue discipline" reading is the
//! one the runtime actually implements. The bound is
//! `numCores - 1` waiters ahead of you, each holding for at most one
//! kernel transition.
//!
//! # Fail-closed
//!
//! The spin is fuel-bounded ([`KERNEL_ENTRY_ACQUIRE_FUEL`]). Exhaustion
//! means the holder is wedged, and continuing would mean committing
//! against a state another core believes it owns — so the waiter halts
//! the system rather than proceeding, matching the SM7.B.6 discipline
//! for the shootdown barriers.

use crate::ticket_lock::TicketLock;

/// **WS-SM SM5.I**: the global kernel-entry lock.
///
/// One lock, not one per core: it exists to make kernel entry mutually
/// exclusive *across* cores, so a per-core lock would serialise nothing.
pub static KERNEL_ENTRY_LOCK: TicketLock = TicketLock::new();

/// **WS-SM SM5.I**: poll budget for a kernel-entry acquire.
///
/// A kernel transition is bounded work — no transition loops on
/// external input — so a holder that has not released after this many
/// polls is wedged rather than slow. Sized like
/// `shootdownRoundLockAcquireFuel`: far above any real hold time, so
/// exhaustion is diagnostic rather than a tuning parameter. Each poll
/// also does a local TLB invalidation at most once per round, so the
/// budget is not a busy-spin cost bound.
pub const KERNEL_ENTRY_ACQUIRE_FUEL: u64 = 1_000_000;

/// **WS-SM SM5.I**: the lock-order tripwire.
///
/// Acquiring the kernel-entry lock while holding
/// [`crate::shootdown::SHOOTDOWN_ROUND_LOCK`] is the one edge that
/// would close a cycle. No caller does it today; this makes a future
/// one fail loudly at the point of the mistake rather than as a hang.
#[inline]
pub fn assert_not_holding_round_lock() {
    debug_assert!(
        !crate::shootdown::round_lock_is_held(),
        "WS-SM SM5.I: kernel-entry lock must be acquired OUTSIDE \
         SHOOTDOWN_ROUND_LOCK; acquiring it while holding the round \
         lock closes a lock-order cycle"
    );
}

/// **WS-SM SM5.I** (testable inner form): acquire `lock`, self-servicing
/// this core's pending shootdown obligation on every failed poll.
///
/// Returns `true` once the ticket is being served, `false` if `fuel`
/// polls elapsed first (the caller decides what to do about that; the
/// production wrapper halts).
///
/// **On `false` the ticket has already been taken and is NOT released**
/// — that is deliberate. The lock is wedged by hypothesis, so the only
/// sound continuations are to halt or to hang, and a fail-closed halt
/// is the one this kernel takes. Reissuing the ticket would let the
/// caller proceed into a commit the holder still believes it owns.
#[must_use]
pub fn acquire_kernel_entry_in(
    lock: &TicketLock,
    core_id: usize,
    fuel: u64,
    mut service: impl FnMut(usize) -> bool,
) -> bool {
    let ticket = lock.take_ticket();
    let mut remaining = fuel;
    while lock.peek_serving() != ticket {
        if remaining == 0 {
            return false;
        }
        remaining -= 1;
        // Discharge our own shootdown obligation, if we owe one, so a
        // holder blocked on our acknowledgment can finish and release.
        // `service` returns false when nothing is outstanding, which is
        // the common case and costs one atomic load.
        let _serviced = service(core_id);
        crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
    }
    true
}

/// **WS-SM SM5.I**: release `lock`.
#[inline]
pub fn release_kernel_entry_in(lock: &TicketLock) {
    lock.release();
}

/// **WS-SM SM5.I**: acquire the global kernel-entry lock, or halt.
///
/// The production entry. Fails closed on fuel exhaustion via
/// [`crate::gic::halt_all`], which broadcasts the SM0.H `haltAll` SGI
/// before parking — a wedged kernel-entry lock means some core is
/// stuck inside a transition, so stopping only the core that noticed
/// would leave the others committing against a state nobody owns.
pub fn acquire_kernel_entry(core_id: usize) -> u64 {
    assert_not_holding_round_lock();
    if !acquire_kernel_entry_in(
        &KERNEL_ENTRY_LOCK,
        core_id,
        KERNEL_ENTRY_ACQUIRE_FUEL,
        crate::shootdown::self_service_round,
    ) {
        crate::kprintln!(
            "[FATAL] WS-SM SM5.I: kernel-entry lock acquire exhausted its \
             fuel on core {} — the holder is wedged; halting fail-closed",
            core_id
        );
        crate::gic::halt_all()
    }
    KERNEL_ENTRY_LOCK.peek_serving()
}

/// **WS-SM SM5.I**: release the global kernel-entry lock.
#[inline]
pub fn release_kernel_entry() {
    release_kernel_entry_in(&KERNEL_ENTRY_LOCK);
}

/// **WS-SM SM5.I**: run `f` with kernel entry serialised.
///
/// The bracket every kernel entry point uses. `f` must not itself
/// enter the kernel (the lock is not reentrant) and must not acquire
/// the shootdown round lock *before* this bracket — inside is correct
/// and is what `completeShootdownRounds` does.
pub fn with_kernel_entry<F, R>(core_id: usize, f: F) -> R
where
    F: FnOnce() -> R,
{
    let _ticket = acquire_kernel_entry(core_id);
    let out = f();
    release_kernel_entry();
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An uncontended acquire returns immediately and does not need to
    /// service anything.
    #[test]
    fn uncontended_acquire_succeeds_without_servicing() {
        let lock = TicketLock::new();
        let mut calls = 0;
        assert!(acquire_kernel_entry_in(&lock, 0, 8, |_| {
            calls += 1;
            false
        }));
        assert_eq!(calls, 0, "an uncontended acquire must not spin");
        release_kernel_entry_in(&lock);
    }

    /// Acquire / release round-trips leave the lock unheld, so the next
    /// acquire is again uncontended.
    #[test]
    fn release_restores_an_unheld_lock() {
        let lock = TicketLock::new();
        for _ in 0..4 {
            assert!(acquire_kernel_entry_in(&lock, 1, 8, |_| false));
            release_kernel_entry_in(&lock);
        }
        assert_eq!(lock.peek_serving(), lock.peek_next_ticket());
    }

    /// A held lock is not acquirable: the waiter burns its fuel and
    /// fails closed rather than entering.
    #[test]
    fn a_held_lock_exhausts_fuel_and_fails_closed() {
        let lock = TicketLock::new();
        assert!(acquire_kernel_entry_in(&lock, 0, 4, |_| false));
        // Second acquirer, holder never releases.
        assert!(
            !acquire_kernel_entry_in(&lock, 1, 4, |_| false),
            "a waiter must not enter a held lock"
        );
    }

    /// The load-bearing property: a waiter services its own obligation
    /// on every poll, which is what lets a holder blocked on this
    /// core's acknowledgment finish and release.
    #[test]
    fn a_waiter_services_its_obligation_on_every_poll() {
        let lock = TicketLock::new();
        assert!(acquire_kernel_entry_in(&lock, 0, 4, |_| false));
        let mut polls = 0usize;
        let mut wrong_core = 0usize;
        let _ = acquire_kernel_entry_in(&lock, 3, 5, |core| {
            polls += 1;
            if core != 3 {
                wrong_core += 1;
            }
            true
        });
        assert_eq!(
            polls, 5,
            "every poll must offer to discharge the obligation"
        );
        assert_eq!(
            wrong_core, 0,
            "a waiter services ITS OWN core, not the holder's"
        );
    }

    /// A waiter released by the holder proceeds, and the servicing hook
    /// stops being called once it is being served.
    #[test]
    fn a_released_waiter_proceeds() {
        let lock = TicketLock::new();
        assert!(acquire_kernel_entry_in(&lock, 0, 4, |_| false));
        release_kernel_entry_in(&lock);
        let mut calls = 0;
        assert!(acquire_kernel_entry_in(&lock, 1, 4, |_| {
            calls += 1;
            false
        }));
        assert_eq!(calls, 0);
    }

    /// `with_kernel_entry` releases even though the body returns a
    /// value, so a following acquire is uncontended.
    #[test]
    fn bracket_releases_after_the_body() {
        let lock = TicketLock::new();
        // Mirror `with_kernel_entry` against the local lock.
        let out = {
            assert!(acquire_kernel_entry_in(&lock, 0, 4, |_| false));
            let out = 42u64;
            release_kernel_entry_in(&lock);
            out
        };
        assert_eq!(out, 42);
        assert!(acquire_kernel_entry_in(&lock, 0, 4, |_| false));
    }
}
