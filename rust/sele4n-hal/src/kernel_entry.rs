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
//! Every Lean entry that commits kernel state — all five:
//!
//! | Lean export | Rust bracket |
//! |---|---|
//! | `lean_syscall_dispatch_cross_core` | `svc_dispatch::dispatch_svc` |
//! | `lean_per_core_timer_tick`         | `timer::per_core_timer_tick_isr` |
//! | `lean_per_core_reschedule`         | `trap::reschedule_sgi_handler` |
//! | `lean_secondary_kernel_main`       | `smp::rust_secondary_main` |
//! | `suspend_thread_cross_core`        | `ffi::sele4n_suspend_thread` |
//!
//! The last is the one to watch for: it reaches Lean through
//! `sele4n_suspend_thread` rather than a `lean_*` symbol, so a sweep
//! for `lean_` does not find it. A lost suspend is a thread that keeps
//! running after its caller was told it stopped.
//!
//! The secondary bring-up entry is bracketed *and* ordered: it runs
//! before `enable_irq` on its core, so a tick cannot preempt the
//! bracket and queue behind a ticket its own core holds (this lock is
//! not reentrant) — the same IRQs-masked-while-held discipline the trap
//! handlers get from `PSTATE.I` staying set until exception return.
//!
//! Bracketing is necessary but not sufficient: this lock serializes
//! access to `kernelStateRef`; it does not make the Lean runtime exist
//! on a PE.  Every hardware seam above therefore also consults the
//! per-core readiness gate ([`crate::lean_ready`]) before its Lean
//! call — a core SM10.1's initialization has not marked ready refuses
//! instead of entering a runtime it never initialized.
//!
//! **WS-RR RR5.6/RR5.7**: that sentence was false when it was written.
//! Three of the five seams consulted the gate; the SVC dispatch seam and
//! the cross-core suspend seam — the two that reach Lean through the
//! `svc_dispatch` / `ffi` boundary rather than an ISR — did not, and the
//! suspend seam is invisible to a `lean_` sweep besides.  Both now do,
//! and the claim is checked rather than asserted:
//! `build.rs::scan_lean_upcalls_readiness_gated` derives the upcall set
//! from the Lean tree's `@[export]`s and fails the build unless a
//! readiness guard on the *executing* PE dominates each call.
//!
//! What a not-ready core does differs by seam, because what it can
//! safely do differs.  The three ISR seams degrade to their Rust-only
//! halves (record-and-re-arm, EOI-and-drop, skip).  The suspend seam
//! returns `KernelError::IllegalState`: it is a C-callable API with an
//! error channel and no trapped thread waiting on it.  The SVC seam
//! **halts the core** — an `SVC` advanced the PC, so a frame *could* be
//! returned, but the timer seam consults the same mask, so a thread on a
//! not-ready core would never be preempted again
//! ([`crate::svc_dispatch`]'s `halt_syscall_before_lean_ready`).
//!
//! `lean_kernel_main` (the primary's boot seam, owed by the SM10.1
//! image target) is the one committing path outside the bracket today.
//! Phase 6 runs it after Phase 5 has released the secondaries, so its
//! `initialiseKernelState` install would race their bracketed ticks:
//! SM10.1 MUST either order the install before secondary release or
//! take this bracket around it (recorded in
//! `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md`).
//!
//! `syscall_dispatch_inner` and `suspend_thread_inner` were the legacy
//! boot-pinned seams the cross-core entries replaced.  **Both exports
//! are now retired** — the second by WS-RR RR5.17.  Until then this
//! module said `suspend_thread_inner` "is not reachable from the trap
//! path and is not bracketed", which was a statement about the HAL as it
//! stood rather than about the artefact: `@[export]` put a
//! kernel-state-committing C symbol in the linked image whose only
//! protection was that no Rust source declared it yet.  The Lean
//! definition survives as a single-core reference path for the dispatch
//! suite; no symbol does, so a future caller cannot reach it at all.
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
/// Acquiring the kernel-entry lock while **this core** holds
/// [`crate::shootdown::SHOOTDOWN_ROUND_LOCK`] is the one edge that
/// would close a cycle. No caller does it today; this makes a future
/// one fail loudly at the point of the mistake rather than as a hang.
///
/// **PR #889 review**: the question is ownership, not held-ness.  The
/// round lock is held by *some* core for the whole of every shootdown in
/// flight — that is its purpose — and during that window every other
/// core's timer tick, `SVC` or reschedule SGI reaches this bracket and
/// must **wait** here, self-servicing its own acknowledgment so the
/// initiator can finish.  A tripwire on the global held flag halted
/// exactly those innocent cores; it now asks whether the executing core
/// itself is the holder (`round_lock_held_by`), which the lock records.
///
/// **WS-RR RR5.18**: this was a `debug_assert!`, which a `--release`
/// build compiles out — and the image that ships is a `--release` build
/// (`scripts/test_qemu.sh` builds `kernel8.img` that way).  So the
/// tripwire existed only in the configuration where a deadlock is
/// cheapest to debug and was absent from the one where it is a hung
/// board, which inverts the point of having it.  It is now an
/// unconditional branch: one relaxed atomic load on a path that already
/// takes a ticket, against a fail-closed halt on the edge that would
/// otherwise hang two cores until the shootdown deadline fires.
///
/// Halting rather than panicking is deliberate: a cycle here is a
/// kernel-internal ordering defect, not a recoverable condition, and
/// [`crate::cpu::fatal_halt`] is the barrier every other such defect in
/// this crate takes.
#[inline]
pub fn assert_not_holding_round_lock(core_id: usize) {
    if crate::shootdown::round_lock_held_by(core_id) {
        crate::kprintln!(
            "[kernel-entry] FATAL: WS-SM SM5.I lock order violated on core {} — the \
             kernel-entry lock must be acquired OUTSIDE SHOOTDOWN_ROUND_LOCK; \
             acquiring it while holding the round lock closes a lock-order cycle",
            core_id
        );
        crate::cpu::fatal_halt();
    }
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
    assert_not_holding_round_lock(core_id);
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
    // The crate is `no_std`; tests may use std (threads for the SM5.I
    // contention witnesses) — same pattern as the shootdown.rs /
    // gic.rs / rw_lock.rs test mods.
    extern crate std;

    use super::*;

    /// **PR #889 review**: the lock-order tripwire asks who *owns* the round
    /// lock.  Another core holding it is the ordinary state of a shootdown
    /// in flight, and this core's kernel entry must pass the tripwire and
    /// wait; only the executing core holding it is the lock-order cycle the
    /// tripwire exists to stop.  Both halves on the global lock, serialised
    /// against the shootdown module's own global-lock test through its mutex.
    #[test]
    fn tripwire_trips_on_own_round_lock_hold_only() {
        let _guard = crate::shootdown::GLOBAL_ROUND_LOCK_TEST_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        assert!(
            crate::shootdown::round_lock_try_acquire_in(&crate::shootdown::SHOOTDOWN_ROUND_LOCK, 3),
            "the global round lock must be free at the start of this test"
        );
        // Another core (3) holds it: core 0's entry passes the tripwire.
        let other = std::panic::catch_unwind(|| assert_not_holding_round_lock(0));
        assert!(
            other.is_ok(),
            "a round lock held by ANOTHER core must not trip this core's lock-order \
             tripwire — that halted every innocent core during a shootdown"
        );
        // The holder itself (3) taking the kernel-entry lock is the cycle.
        let own = std::panic::catch_unwind(|| assert_not_holding_round_lock(3));
        assert!(
            own.is_err(),
            "the holder re-entering must halt (a panic on the host lane)"
        );
        crate::shootdown::round_lock_release();
        assert!(
            std::panic::catch_unwind(|| assert_not_holding_round_lock(3)).is_ok(),
            "released, nobody trips"
        );
    }

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

    // ========================================================================
    // WS-SM SM5.I — contention witnesses
    //
    // The six tests above drive the lock on ONE thread. That is the right
    // shape for the fuel and servicing arms, but it cannot exercise what
    // this lock is FOR: every property SM5.I claims is a statement about
    // two cores entering at once, and on one thread all of them hold
    // trivially — an uncontended `take_ticket` always equals
    // `peek_serving`, so the wait loop never runs.
    //
    // These run it with real threads on the `_in` forms, which take an
    // explicit lock precisely so contenders never touch the global. The
    // second is the important one: it reproduces the DEFECT rather than
    // testing the lock, by committing through the same read-then-write
    // shape `Platform.FFI.modifyGetKernelState` uses.
    //
    // Host scope, as for the SM7.F.3 witnesses: no SGIs, no per-PE TLB, a
    // different memory model. What is pinned is the mutual exclusion and
    // the fairness, not anything about TLBs. Hardware waits for SM10.1.
    // ========================================================================

    /// Contenders, capped at the host's real parallelism (min 2, so the
    /// wait loop is genuinely entered).
    fn contention_witness_threads() -> usize {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .clamp(2, 8)
    }

    /// **WS-SM SM5.I** (contention witness): at most one core is ever
    /// inside the kernel-entry bracket.
    ///
    /// The property the whole phase exists for. A ticket lock that handed
    /// out the same serving slot twice would let two cores commit against
    /// the same pre-state.
    #[test]
    fn concurrent_kernel_entries_never_overlap() {
        const PER_THREAD: usize = 150;
        let threads = contention_witness_threads();
        let lock = TicketLock::new();
        let occupancy = core::sync::atomic::AtomicU32::new(0);
        let max_seen = core::sync::atomic::AtomicU32::new(0);
        let entries = core::sync::atomic::AtomicUsize::new(0);
        let start = std::sync::Barrier::new(threads);
        std::thread::scope(|s| {
            for core_id in 0..threads {
                let (lock, occupancy, max_seen, entries, start) =
                    (&lock, &occupancy, &max_seen, &entries, &start);
                s.spawn(move || {
                    start.wait();
                    for _ in 0..PER_THREAD {
                        assert!(
                            acquire_kernel_entry_in(lock, core_id, 100_000_000, |_| false),
                            "core {core_id} exhausted its fuel under ordinary contention"
                        );
                        let now = occupancy.fetch_add(1, core::sync::atomic::Ordering::SeqCst) + 1;
                        max_seen.fetch_max(now, core::sync::atomic::Ordering::SeqCst);
                        occupancy.fetch_sub(1, core::sync::atomic::Ordering::SeqCst);
                        entries.fetch_add(1, core::sync::atomic::Ordering::SeqCst);
                        release_kernel_entry_in(lock);
                    }
                });
            }
        });
        assert_eq!(
            max_seen.load(core::sync::atomic::Ordering::SeqCst),
            1,
            "two cores were inside the kernel-entry bracket at once"
        );
        assert_eq!(
            entries.load(core::sync::atomic::Ordering::SeqCst),
            threads * PER_THREAD,
            "every entry must complete — a lost one means a wedged acquire"
        );
    }

    /// **WS-SM SM5.I** (defect witness): no kernel transition is lost
    /// under concurrent entry.
    ///
    /// This reproduces the P1 itself rather than the lock. The commit
    /// body is the read-then-write shape `modifyGetKernelState` has —
    /// read the state, compute a post-state from it, write it back — with
    /// a deliberate gap between the two halves so the interleaving is
    /// reached rather than merely possible. Unbracketed that loses
    /// updates; bracketed it must not, and the count is exact.
    #[test]
    fn no_kernel_transition_is_lost_under_concurrent_entry() {
        const PER_THREAD: usize = 100;
        let threads = contention_witness_threads();
        let lock = TicketLock::new();
        // The "kernel state": a plain cell, read and written separately,
        // exactly as `IO.Ref.modifyGet` does.
        let state = core::cell::UnsafeCell::new(0u64);
        struct Shared(core::cell::UnsafeCell<u64>);
        // SAFETY: every access below is inside the kernel-entry bracket,
        // which is what the test is asserting provides exclusion.
        unsafe impl Sync for Shared {}
        let shared = Shared(state);
        let start = std::sync::Barrier::new(threads);
        std::thread::scope(|s| {
            for core_id in 0..threads {
                let (lock, shared, start) = (&lock, &shared, &start);
                s.spawn(move || {
                    start.wait();
                    for _ in 0..PER_THREAD {
                        assert!(acquire_kernel_entry_in(lock, core_id, 100_000_000, |_| {
                            false
                        }));
                        // SAFETY: serialised by the bracket.
                        unsafe {
                            let p = shared.0.get();
                            let observed = core::ptr::read_volatile(p);
                            // Widen the read→write window WITHOUT
                            // surrendering the CPU. `yield_now()` here
                            // deschedules a thread that holds the lock,
                            // and with several contention tests sharing
                            // four cores the holder may not be rescheduled
                            // for a long time while every waiter spins —
                            // observed as an occasional multi-minute run.
                            // A spin burst widens the window just as well
                            // and cannot deschedule the holder.
                            for _ in 0..64 {
                                core::hint::spin_loop();
                            }
                            core::ptr::write_volatile(p, observed + 1);
                        }
                        release_kernel_entry_in(lock);
                    }
                });
            }
        });
        // SAFETY: all threads have joined.
        let final_state = unsafe { core::ptr::read_volatile(shared.0.get()) };
        assert_eq!(
            final_state,
            (threads * PER_THREAD) as u64,
            "a kernel transition was lost — the second writer installed a \
             post-state derived from a pre-state that no longer held"
        );
    }

    /// **WS-SM SM5.I** (fairness witness): a neighbour re-entering in a
    /// loop cannot starve another core.
    ///
    /// SM5.I chose the SM2 `TicketLock` over a CAS try-lock specifically
    /// so entry is FIFO. A test-and-set lock passes the exclusion witness
    /// above while letting one core monopolise entry, so exclusion alone
    /// does not establish what was chosen here.
    ///
    /// Measured as **overtaking while queued**, which is what FIFO
    /// actually promises: from the moment the victim takes its ticket,
    /// only cores already ahead of it may enter first. Two weaker
    /// formulations were tried and rejected:
    ///
    /// * *the victim exhausts its fuel* — depends on the budget being
    ///   small enough to reach, so shortening the run to keep it cheap
    ///   silently disarmed it (mutation-verified: at 100 iterations the
    ///   non-FIFO mutant passed);
    /// * *the hog:victim ratio over the whole run* — unsound on a
    ///   preemptive host, where the hog can hold the CPU for a full
    ///   timeslice while the victim is not scheduled at all and therefore
    ///   is not even contending. That is not starvation, but it inflates
    ///   the ratio; it failed 2 runs in 8.
    ///
    /// Sampling per acquire fixes both: a descheduled victim contributes
    /// no sample, and the majority test tolerates the scheduling jitter
    /// that made the ratio unusable while still catching systematic
    /// starvation, where essentially every sample is bad.
    #[test]
    fn a_re_entering_neighbour_does_not_starve_another_core() {
        const TARGET: usize = 100;
        // Under FIFO the hog can enter at most once between the victim
        // taking its ticket and being served (its ticket was already
        // ahead); 2 absorbs the unsynchronised read either side.
        const MAX_OVERTAKES: usize = 2;
        let lock = TicketLock::new();
        let hog_entries = core::sync::atomic::AtomicUsize::new(0);
        let victim_entries = core::sync::atomic::AtomicUsize::new(0);
        let victim_done = core::sync::atomic::AtomicBool::new(false);
        let prompt_serves = core::sync::atomic::AtomicUsize::new(0);
        let start = std::sync::Barrier::new(2);
        std::thread::scope(|s| {
            let (lock, hog_entries, victim_entries, victim_done, prompt_serves, start) = (
                &lock,
                &hog_entries,
                &victim_entries,
                &victim_done,
                &prompt_serves,
                &start,
            );
            s.spawn(move || {
                start.wait();
                while !victim_done.load(core::sync::atomic::Ordering::Acquire) {
                    assert!(acquire_kernel_entry_in(lock, 0, 100_000_000, |_| false));
                    hog_entries.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
                    release_kernel_entry_in(lock);
                }
            });
            s.spawn(move || {
                start.wait();
                // Do not start measuring until the hog is demonstrably
                // running: a bare barrier left the victim finishing before
                // the hog was first scheduled in 9 of 20 runs on a 4-core
                // host, which made the witness vacuous rather than wrong.
                while hog_entries.load(core::sync::atomic::Ordering::Relaxed) == 0 {
                    std::thread::yield_now();
                }
                for _ in 0..TARGET {
                    let before = hog_entries.load(core::sync::atomic::Ordering::Relaxed);
                    assert!(
                        acquire_kernel_entry_in(lock, 1, 100_000_000, |_| false),
                        "the victim exhausted its fuel — it was starved"
                    );
                    let overtaken =
                        hog_entries.load(core::sync::atomic::Ordering::Relaxed) - before;
                    if overtaken <= MAX_OVERTAKES {
                        prompt_serves.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
                    }
                    victim_entries.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
                    release_kernel_entry_in(lock);
                }
                victim_done.store(true, core::sync::atomic::Ordering::Release);
            });
        });
        let hog = hog_entries.load(core::sync::atomic::Ordering::Relaxed);
        let victim = victim_entries.load(core::sync::atomic::Ordering::Relaxed);
        assert_eq!(victim, TARGET, "the victim did not complete its entries");
        assert!(
            hog >= 1,
            "the hog never ran — the contention never happened"
        );
        let prompt = prompt_serves.load(core::sync::atomic::Ordering::Relaxed);
        assert!(
            prompt * 2 >= TARGET,
            "the victim was overtaken more than {MAX_OVERTAKES} times on \
             {} of its {TARGET} acquires (hog {hog}, victim {victim}) — entry \
             is not FIFO, so a re-entering neighbour can monopolise the kernel",
            TARGET - prompt
        );
    }
}
