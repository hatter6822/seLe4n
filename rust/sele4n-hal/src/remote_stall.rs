// SPDX-License-Identifier: GPL-3.0-or-later
//! The remote-core stall: a commit that changes what another core runs does
//! not return until that core has left the thread it was running **and saved
//! it**.
//!
//! seL4 stalls a remote core synchronously when an operation takes a thread
//! off it (`remoteTCBStall`: an IPI, then a wait until the remote core has
//! rescheduled), so the thread's registers are in its TCB, and it executes no
//! user instruction, once the operation has returned.  Here a commit may take
//! a thread off another core's current slot (a final delete's finalisation, a
//! suspend, an affinity change) while that core's hardware still runs it at
//! EL0.  Every committing entry therefore checks, after its commit, each other
//! core against the committed state (`Concurrency.stallChangedCores` on the
//! Lean side, [`stall_if_changed_in`] here), waits for any core it changed to
//! leave user mode, and records that core's save epoch; the core then returns
//! to EL0 only once each such core has completed a locked entry after the
//! record ([`await_remote_saves_in`], run by the user-exit gate).  That entry
//! saves the thread's live registers into its TCB
//! (`Architecture.saveVacatedFrameOnCore`), so the change returns only after
//! the remote save.
//!
//! ## The flags and the epochs
//!
//! Per core, one `AtomicBool` each:
//!
//! - [`AT_USER`]: the core is at EL0, or between its user-exit gate and the
//!   `eret`.  Cleared first thing on every exception entry
//!   ([`note_kernel_entry`]), before anything that can block, and set by the
//!   exit gate ([`enter_user_in`]) on every return to EL0.
//! - [`STALL_REQUESTED`]: a commit on another core changed what this core
//!   runs since the decision its next return to EL0 carries.  Set by the
//!   initiator under the kernel-entry lock, cleared by this core's own next
//!   kernel entry under the same lock ([`clear_stall_request`]), whose
//!   decision then reads the committed state.
//!
//! Per core, one `AtomicU64`:
//!
//! - [`SAVE_EPOCH`]: how many locked entries the core has completed.  Advanced
//!   by the core's own entry inside the kernel-entry lock, after its commit
//!   and before the release ([`note_locked_entry_in`]); the commit's first
//!   stage is the save of the frame the core trapped with.
//!
//! Per initiator and target, one `AtomicU64` of [`PENDING_SAVES`]: `0`, or the
//! target's epoch the initiator sampled under the lock, plus one.  Written and
//! read only by the initiator.
//!
//! ## Why the leave is sound
//!
//! The initiator holds the kernel-entry lock, so the committed state it
//! compares against is the one every later decision on the target reads.  It
//! stores the request and then loads the target's user flag; the target's
//! exit gate stores its user flag and then loads the request.  All four are
//! `SeqCst`, so at least one side sees the other's store (the store-buffering
//! litmus test):
//!
//! - the initiator sees the target at user: it pokes the target with the
//!   `.reschedule` SGI and waits until the flag clears, which the target's
//!   next exception entry does before anything else;
//! - the target's gate sees the request: it does not return to EL0 but takes
//!   the reschedule first, under the lock, so its next return carries a
//!   decision made on the committed state.
//!
//! Either way the target runs none of the thread the commit took off it
//! once the initiator's entry has returned.
//!
//! ## Why the save is sound
//!
//! The target's epoch moves only inside its locked entries, so the value the
//! initiator samples under the lock is the count of entries the target
//! completed before the commit.  The target's next locked entry after it
//! decides on the committed state, in which the thread is no longer current
//! there and is recorded as the target's resident thread
//! (`MachineState.residentOnCore`).  Every way the target reaches that entry
//! hands it the thread's frame: an exception from EL0 (the poke, or its own
//! trap), or the exit gate's refusal, which runs the reschedule with the frame
//! it was about to resume — the thread's restore target, its saved context.
//! The entry's first stage saves that frame into the resident thread's TCB.
//! So once the epoch has moved past the sample, the thread's registers are in
//! its TCB.  The wait runs **outside** the lock, after the initiator's entry
//! has returned in full, so each entry stays one atomic transition: no other
//! core's commit interleaves with the initiator's post-commit steps (the
//! shootdown, the FP/SIMD release, the restore, the HAL record), which read
//! values the commit produced.
//!
//! ## Why it cannot deadlock
//!
//! The target clears its user flag before it takes any lock, so a target
//! spinning on the kernel-entry lock the initiator holds is not at user and
//! is not waited on under the lock.  The save wait holds no lock, so the
//! target's entry can take it.  Two cores that each took the other's thread
//! wait on each other's epochs, and each serves its own request while it
//! waits: a set [`STALL_REQUESTED`] makes the waiter run its own reschedule
//! entry, which advances its epoch and ends the other's wait — seL4's lock
//! spin, which serves the stall IPI, in this kernel's terms.  The waiter also
//! discharges its shootdown obligation each poll, as a lock spinner does.
//! Every wait is bounded; exhausting [`STALL_WAIT_FUEL`] means the target is
//! wedged and the system halts fail-closed, as a wedged shootdown or
//! kernel-entry lock does.
//!
//! ## The rule this binds
//!
//! No invocation reads or writes another thread's saved registers today
//! except the yield's `setConsumed`, which `SystemState.yieldLinkedNotResident`
//! covers.  **Any future invocation that reads or writes another thread's
//! registers (a `TCB_ReadRegisters`, `WriteRegisters` or `CopyRegisters`)
//! must first wait on the target's save epoch** — refuse with a restart while
//! the target is current or resident on another core, stall it, and retry
//! after the epoch has moved — as seL4's `remoteTCBStall` heads
//! `decodeTCBInvocation`.  An invocation that touches no registers needs no
//! stall: every remote deschedule already goes through the vacate, the
//! residency record and this stall.

#[cfg(not(loom))]
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};
#[cfg(loom)]
use loom::sync::atomic::{AtomicBool, AtomicU64, Ordering};

/// The number of cores the stall tracks.
pub const STALL_CORES: usize = crate::svc_dispatch::RETURN_FRAME_CORES;

/// One flag per core.
pub type CoreFlags = [AtomicBool; STALL_CORES];

/// One save epoch per core.
pub type CoreEpochs = [AtomicU64; STALL_CORES];

/// Per initiator, per target: `0`, or the sampled target epoch plus one.
pub type PendingSaves = [[AtomicU64; STALL_CORES]; STALL_CORES];

/// Per core: the core is at EL0, or past its user-exit gate on the way there.
#[cfg(not(loom))]
pub static AT_USER: CoreFlags = [const { AtomicBool::new(false) }; STALL_CORES];

/// Per core: a commit on another core changed what the core runs since the
/// decision its next return to EL0 carries.
#[cfg(not(loom))]
pub static STALL_REQUESTED: CoreFlags = [const { AtomicBool::new(false) }; STALL_CORES];

/// Per core: the locked entries the core has completed.
#[cfg(not(loom))]
pub static SAVE_EPOCH: CoreEpochs = [const { AtomicU64::new(0) }; STALL_CORES];

/// Per initiator, per target: the save the initiator still waits on.
#[cfg(not(loom))]
pub static PENDING_SAVES: PendingSaves =
    [const { [const { AtomicU64::new(0) }; STALL_CORES] }; STALL_CORES];

// The loom build's globals: loom's atomics are not `const`-constructible, so
// the statics above do not compile under `--cfg loom` (`lock_bridge.rs`'s pool
// is the same).  The loom models use their own arrays; these only keep the
// crate's other users of the globals compiling.
#[cfg(loom)]
loom::lazy_static! {
    pub static ref AT_USER: CoreFlags = core::array::from_fn(|_| AtomicBool::new(false));
    pub static ref STALL_REQUESTED: CoreFlags = core::array::from_fn(|_| AtomicBool::new(false));
    pub static ref SAVE_EPOCH: CoreEpochs = core::array::from_fn(|_| AtomicU64::new(0));
    pub static ref PENDING_SAVES: PendingSaves =
        core::array::from_fn(|_| core::array::from_fn(|_| AtomicU64::new(0)));
}

/// One poll of a wait: a spin hint, or a yield to loom's scheduler.
#[inline]
fn relax() {
    #[cfg(not(loom))]
    core::hint::spin_loop();
    #[cfg(loom)]
    loom::thread::yield_now();
}

/// Poll budget for the initiator's wait.  A target at EL0 takes the
/// `.reschedule` SGI within interrupt latency; a target that has not entered
/// the kernel after this many polls is wedged.
pub const STALL_WAIT_FUEL: u64 = 100_000_000;

/// What [`stall_if_changed_in`] found.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StallOutcome {
    /// The committed state runs on the target what the target last decided
    /// to run, so nothing it runs was taken off it.
    Unchanged,
    /// The target was not at user: its next return to EL0 takes the
    /// reschedule first, or its in-progress kernel entry decides on the
    /// committed state.
    NotAtUser,
    /// The target was at user, was poked, and has since entered the kernel.
    Left,
    /// The target did not enter the kernel within the poll budget.
    TimedOut,
}

/// The core's exception entry (testable form): it is no longer at user.
#[inline]
pub fn note_kernel_entry_in(at_user: &CoreFlags, core: usize) {
    if let Some(flag) = at_user.get(core) {
        flag.store(false, Ordering::SeqCst);
    }
}

/// The executing core's exception entry: called first thing by every
/// handler an exception from EL0 reaches, before anything that can block.
#[inline]
pub fn note_kernel_entry() {
    note_kernel_entry_in(
        &AT_USER,
        crate::per_cpu::current_core_id_from_tpidr() as usize,
    );
}

/// The core's kernel entry under the kernel-entry lock (testable form): its
/// decision now reads the committed state, so a pending request is met.
#[inline]
pub fn clear_stall_request_in(requested: &CoreFlags, core: usize) {
    if let Some(flag) = requested.get(core) {
        flag.store(false, Ordering::SeqCst);
    }
}

/// [`clear_stall_request_in`] on the global flags, called by
/// [`crate::kernel_entry::with_kernel_entry`] once it holds the lock.
#[inline]
pub fn clear_stall_request(core: usize) {
    clear_stall_request_in(&STALL_REQUESTED, core);
}

/// The core's user-exit gate (testable form): mark the core at user, then
/// report whether it may return to EL0.  `false` means a commit on another
/// core changed what it runs: the flag is cleared again and the caller must
/// take the reschedule before it returns.
#[must_use]
pub fn enter_user_in(at_user: &CoreFlags, requested: &CoreFlags, core: usize) -> bool {
    let (Some(user), Some(request)) = (at_user.get(core), requested.get(core)) else {
        return true;
    };
    user.store(true, Ordering::SeqCst);
    if request.load(Ordering::SeqCst) {
        user.store(false, Ordering::SeqCst);
        false
    } else {
        true
    }
}

/// [`enter_user_in`] on the global flags.
#[must_use]
pub fn enter_user(core: usize) -> bool {
    enter_user_in(&AT_USER, &STALL_REQUESTED, core)
}

/// The initiator's check of one target (testable form).  `changed` is
/// whether the committed state runs on `target` something other than what
/// `target` last decided to run; `poke` sends `target` the `.reschedule` SGI.
pub fn stall_if_changed_in(
    at_user: &CoreFlags,
    requested: &CoreFlags,
    target: usize,
    changed: bool,
    fuel: u64,
    mut poke: impl FnMut(usize),
) -> StallOutcome {
    if !changed {
        return StallOutcome::Unchanged;
    }
    let (Some(user), Some(request)) = (at_user.get(target), requested.get(target)) else {
        return StallOutcome::Unchanged;
    };
    request.store(true, Ordering::SeqCst);
    if !user.load(Ordering::SeqCst) {
        return StallOutcome::NotAtUser;
    }
    poke(target);
    let mut remaining = fuel;
    while user.load(Ordering::SeqCst) {
        if remaining == 0 {
            return StallOutcome::TimedOut;
        }
        remaining -= 1;
        relax();
    }
    StallOutcome::Left
}

/// A recorded current-thread id (`ffi::NO_CURRENT_THREAD` for none) as the
/// Lean thread code: `0` for none, `tid + 1` for thread `tid`.
#[must_use]
pub const fn recorded_code(recorded: u64) -> u64 {
    if recorded == crate::ffi::NO_CURRENT_THREAD {
        0
    } else {
        recorded.wrapping_add(1)
    }
}

/// The core's locked entry has committed (testable form): advance its save
/// epoch.  Called inside the kernel-entry lock, after the entry's commit —
/// whose first stage saved the frame the core trapped with — and before the
/// release, so the epoch moves only while the core holds the lock.
#[inline]
pub fn note_locked_entry_in(epochs: &CoreEpochs, core: usize) {
    if let Some(epoch) = epochs.get(core) {
        epoch.fetch_add(1, Ordering::Release);
    }
}

/// [`note_locked_entry_in`] on the global epochs, called by
/// [`crate::kernel_entry::with_kernel_entry`] before it releases the lock.
#[inline]
pub fn note_locked_entry(core: usize) {
    note_locked_entry_in(&SAVE_EPOCH, core);
}

/// The initiator owes a wait on `target`'s save (testable form): record the
/// target's epoch, sampled now.  Called under the kernel-entry lock, after a
/// stall found the target changed, so the sample counts exactly the locked
/// entries the target completed before the commit.
pub fn record_pending_save_in(
    epochs: &CoreEpochs,
    pending: &PendingSaves,
    initiator: usize,
    target: usize,
) {
    let (Some(row), Some(epoch)) = (pending.get(initiator), epochs.get(target)) else {
        return;
    };
    if let Some(slot) = row.get(target) {
        slot.store(
            epoch.load(Ordering::Acquire).wrapping_add(1),
            Ordering::Relaxed,
        );
    }
}

/// [`record_pending_save_in`] on the global epochs and records.
pub fn record_pending_save(initiator: usize, target: usize) {
    record_pending_save_in(&SAVE_EPOCH, &PENDING_SAVES, initiator, target);
}

/// What [`await_remote_saves_in`] found.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SaveWait {
    /// The core owed no save wait.
    NoneOwed,
    /// Every target the core waited on has completed a locked entry since
    /// the sample, and so has saved the thread the commit took off it.
    Saved,
    /// A target completed no locked entry within the poll budget.
    TimedOut,
}

/// Whether every save `core` waits on has happened, clearing the ones that
/// have.  `true` when none is outstanding.
fn saves_met(epochs: &CoreEpochs, row: &[AtomicU64; STALL_CORES]) -> bool {
    let mut met = true;
    for (target, slot) in row.iter().enumerate() {
        let owed = slot.load(Ordering::Relaxed);
        if owed == 0 {
            continue;
        }
        let sampled = owed.wrapping_sub(1);
        if epochs[target].load(Ordering::Acquire) != sampled {
            slot.store(0, Ordering::Relaxed);
        } else {
            met = false;
        }
    }
    met
}

/// The initiator's wait for the saves it owes (testable form), run outside
/// the kernel-entry lock before the core returns to EL0 or its idle loop.
/// While it waits it serves its own stall request (`serve_request`: run this
/// core's reschedule entry, which advances its epoch) and its shootdown
/// obligation (`serve_round`), so two cores waiting on each other, or a holder
/// waiting on this core's acknowledgment, cannot deadlock.
pub fn await_remote_saves_in(
    epochs: &CoreEpochs,
    pending: &PendingSaves,
    requested: &CoreFlags,
    core: usize,
    fuel: u64,
    mut serve_request: impl FnMut(usize),
    mut serve_round: impl FnMut(usize) -> bool,
) -> SaveWait {
    let Some(row) = pending.get(core) else {
        return SaveWait::NoneOwed;
    };
    if row.iter().all(|slot| slot.load(Ordering::Relaxed) == 0) {
        return SaveWait::NoneOwed;
    }
    let mut remaining = fuel;
    loop {
        // The core's own request first: another core may be waiting on this
        // core's epoch, and this core's own request is the entry it waits
        // for, so it is served before the wait can end.
        if requested
            .get(core)
            .is_some_and(|r| r.load(Ordering::SeqCst))
        {
            serve_request(core);
        }
        if saves_met(epochs, row) {
            return SaveWait::Saved;
        }
        if remaining == 0 {
            return SaveWait::TimedOut;
        }
        remaining -= 1;
        let _served = serve_round(core);
        relax();
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    extern crate std;

    use super::*;

    fn flags() -> CoreFlags {
        [const { AtomicBool::new(false) }; STALL_CORES]
    }

    #[test]
    fn an_unchanged_target_is_not_requested_or_poked() {
        let (user, req) = (flags(), flags());
        user[1].store(true, Ordering::SeqCst);
        let out = stall_if_changed_in(&user, &req, 1, false, 10, |_| panic!("poked"));
        assert_eq!(out, StallOutcome::Unchanged);
        assert!(!req[1].load(Ordering::SeqCst));
    }

    #[test]
    fn a_target_in_the_kernel_is_requested_not_waited_on() {
        let (user, req) = (flags(), flags());
        let out = stall_if_changed_in(&user, &req, 2, true, 10, |_| panic!("poked"));
        assert_eq!(out, StallOutcome::NotAtUser);
        // Its next return to EL0 takes the reschedule first.
        assert!(!enter_user_in(&user, &req, 2));
        assert!(!user[2].load(Ordering::SeqCst));
        // Its kernel entry under the lock meets the request.
        clear_stall_request_in(&req, 2);
        assert!(enter_user_in(&user, &req, 2));
    }

    #[test]
    fn a_target_at_user_is_poked_and_waited_until_it_enters() {
        let (user, req) = (flags(), flags());
        user[3].store(true, Ordering::SeqCst);
        let mut poked = 0;
        let out = stall_if_changed_in(&user, &req, 3, true, 10, |c| {
            poked += 1;
            // The SGI's exception entry.
            note_kernel_entry_in(&user, c);
        });
        assert_eq!((out, poked), (StallOutcome::Left, 1));
    }

    #[test]
    fn a_target_that_never_enters_times_out() {
        let (user, req) = (flags(), flags());
        user[1].store(true, Ordering::SeqCst);
        let out = stall_if_changed_in(&user, &req, 1, true, 5, |_| {});
        assert_eq!(out, StallOutcome::TimedOut);
    }

    /// The store-buffering race between the initiator and the target's exit
    /// gate: on every interleaving either the initiator waits for the target
    /// or the target's gate refuses the return.
    #[test]
    fn the_initiator_or_the_gate_always_sees_the_other() {
        for _ in 0..2_000 {
            let user = std::sync::Arc::new(flags());
            let req = std::sync::Arc::new(flags());
            let (u2, r2) = (user.clone(), req.clone());
            let gate = std::thread::spawn(move || enter_user_in(&u2, &r2, 1));
            let out = stall_if_changed_in(&user, &req, 1, true, u64::MAX, |c| {
                note_kernel_entry_in(&user, c);
            });
            let returned_to_user = gate.join().unwrap();
            assert!(
                !(returned_to_user && out == StallOutcome::NotAtUser),
                "the target returned to user and the initiator did not wait"
            );
        }
    }

    fn epochs() -> CoreEpochs {
        [const { AtomicU64::new(0) }; STALL_CORES]
    }

    fn pending() -> PendingSaves {
        [const { [const { AtomicU64::new(0) }; STALL_CORES] }; STALL_CORES]
    }

    #[test]
    fn a_locked_entry_advances_its_own_epoch_only() {
        let e = epochs();
        note_locked_entry_in(&e, 2);
        note_locked_entry_in(&e, 2);
        assert_eq!(e[2].load(Ordering::SeqCst), 2);
        assert_eq!(e[1].load(Ordering::SeqCst), 0);
        // An out-of-range core advances nothing.
        note_locked_entry_in(&e, STALL_CORES);
    }

    #[test]
    fn a_core_that_owes_nothing_does_not_wait() {
        let (e, p, req) = (epochs(), pending(), flags());
        let out = await_remote_saves_in(&e, &p, &req, 0, 0, |_| panic!("served"), |_| false);
        assert_eq!(out, SaveWait::NoneOwed);
    }

    #[test]
    fn the_sample_counts_the_entries_before_the_commit_only() {
        let (e, p, req) = (epochs(), pending(), flags());
        // The target completed entries before the commit: they saved nothing
        // the commit took off it, and do not end the wait.
        note_locked_entry_in(&e, 1);
        note_locked_entry_in(&e, 1);
        record_pending_save_in(&e, &p, 0, 1);
        assert_eq!(p[0][1].load(Ordering::SeqCst), 3);
        let out = await_remote_saves_in(&e, &p, &req, 0, 4, |_| {}, |_| false);
        assert_eq!(out, SaveWait::TimedOut);
        // Its next locked entry is the save.
        note_locked_entry_in(&e, 1);
        let out = await_remote_saves_in(&e, &p, &req, 0, 0, |_| {}, |_| false);
        assert_eq!(out, SaveWait::Saved);
        // The wait is discharged once.
        assert_eq!(p[0][1].load(Ordering::SeqCst), 0);
        let out = await_remote_saves_in(&e, &p, &req, 0, 0, |_| {}, |_| false);
        assert_eq!(out, SaveWait::NoneOwed);
    }

    #[test]
    fn the_wait_ends_only_when_every_target_has_saved() {
        let (e, p, req) = (epochs(), pending(), flags());
        record_pending_save_in(&e, &p, 0, 1);
        record_pending_save_in(&e, &p, 0, 3);
        note_locked_entry_in(&e, 1);
        let out = await_remote_saves_in(&e, &p, &req, 0, 3, |_| {}, |_| false);
        assert_eq!(out, SaveWait::TimedOut);
        note_locked_entry_in(&e, 3);
        let out = await_remote_saves_in(&e, &p, &req, 0, 0, |_| {}, |_| false);
        assert_eq!(out, SaveWait::Saved);
    }

    #[test]
    fn the_waiter_serves_its_own_request_and_shootdown_obligation() {
        let (e, p, req) = (epochs(), pending(), flags());
        record_pending_save_in(&e, &p, 0, 1);
        req[0].store(true, Ordering::SeqCst);
        let (mut served, mut rounds) = (0, 0);
        let out = await_remote_saves_in(
            &e,
            &p,
            &req,
            0,
            8,
            |c| {
                served += 1;
                // This core's reschedule entry: it meets its request under
                // the lock and advances its own epoch.
                clear_stall_request_in(&req, c);
                note_locked_entry_in(&e, c);
            },
            |_| {
                rounds += 1;
                // The target's entry runs while this core polls.
                note_locked_entry_in(&e, 1);
                false
            },
        );
        assert_eq!(out, SaveWait::Saved);
        assert_eq!((served, rounds), (1, 1));
        assert_eq!(e[0].load(Ordering::SeqCst), 1);
    }

    /// Two cores that each took the other's thread wait on each other's
    /// epochs, outside the lock; each serves its own request, which is the
    /// entry the other waits on, so both finish.
    #[test]
    fn two_initiators_waiting_on_each_other_both_finish() {
        for _ in 0..500 {
            let e = std::sync::Arc::new(epochs());
            let p = std::sync::Arc::new(pending());
            let req = std::sync::Arc::new(flags());
            // Each commit, under the lock, requested the other and sampled it.
            req[1].store(true, Ordering::SeqCst);
            record_pending_save_in(&e, &p, 0, 1);
            req[0].store(true, Ordering::SeqCst);
            record_pending_save_in(&e, &p, 1, 0);
            let lock = std::sync::Arc::new(std::sync::Mutex::new(()));
            let run = |core: usize| {
                let (e, p, req, lock) = (e.clone(), p.clone(), req.clone(), lock.clone());
                std::thread::spawn(move || {
                    await_remote_saves_in(
                        &e,
                        &p,
                        &req,
                        core,
                        50_000_000,
                        |c| {
                            let _g = lock.lock().unwrap();
                            clear_stall_request_in(&req, c);
                            note_locked_entry_in(&e, c);
                        },
                        |_| false,
                    )
                })
            };
            let (a, b) = (run(0), run(1));
            assert_eq!(a.join().unwrap(), SaveWait::Saved);
            assert_eq!(b.join().unwrap(), SaveWait::Saved);
        }
    }

    #[test]
    fn an_out_of_range_record_or_wait_is_inert() {
        let (e, p, req) = (epochs(), pending(), flags());
        record_pending_save_in(&e, &p, STALL_CORES, 0);
        record_pending_save_in(&e, &p, 0, STALL_CORES);
        assert!(p.iter().flatten().all(|s| s.load(Ordering::SeqCst) == 0));
        let out = await_remote_saves_in(&e, &p, &req, STALL_CORES, 0, |_| {}, |_| false);
        assert_eq!(out, SaveWait::NoneOwed);
    }

    #[test]
    fn recorded_codes_match_the_lean_thread_codes() {
        assert_eq!(recorded_code(crate::ffi::NO_CURRENT_THREAD), 0);
        assert_eq!(recorded_code(0), 1);
        assert_eq!(recorded_code(41), 42);
    }
}

/// **The stall's loom model**: every interleaving of an initiator's commit,
/// its stall under the kernel-entry lock and its save wait outside it, against
/// the target's exception entry, its locked entry and its exit gate.  The
/// protocol functions are the deployed ones (`stall_if_changed_in`,
/// `record_pending_save_in`, `note_locked_entry_in`,
/// `await_remote_saves_in`, `enter_user_in`, `note_kernel_entry_in`) on loom's
/// atomics; the kernel-entry lock is a loom `Mutex` over a small kernel state
/// (current, resident and decided thread per core, and each thread's saved
/// register word).  Each model checks that no schedule deadlocks or times out
/// and that an initiator's wait ends only once the thread its commit took off
/// the target holds, in its TCB, the register word the thread trapped with.
#[cfg(loom)]
mod loom_model {
    extern crate std;

    use super::*;
    use loom::sync::{Arc, Condvar, Mutex};

    const NONE: usize = 0;
    const THREADS: usize = 4;
    /// Poll budget inside the model: loom yields at every poll, so a wait
    /// that needs more than this is a schedule that cannot progress.
    const FUEL: u64 = 64;

    struct Kernel {
        current: [usize; STALL_CORES],
        resident: [usize; STALL_CORES],
        decided: [usize; STALL_CORES],
        tcb: [u64; THREADS],
    }

    struct UserCores {
        poked: [bool; STALL_CORES],
        settled: u64,
    }

    struct Sim {
        at_user: CoreFlags,
        requested: CoreFlags,
        epochs: CoreEpochs,
        pending: PendingSaves,
        /// A core at EL0 runs user code until an exception: in the model it
        /// blocks until poked (the SGI) or until every core has settled, so
        /// the only spinning waits are the protocol's own.
        user: Mutex<UserCores>,
        wake: Condvar,
        live_at_trap: [AtomicU64; THREADS],
        kernel: Mutex<Kernel>,
    }

    impl Sim {
        /// Core `c` runs thread `c + 1` at EL0, decided and resident there.
        fn new(cores: usize) -> Self {
            let mut current = [NONE; STALL_CORES];
            for (c, slot) in current.iter_mut().enumerate().take(cores) {
                *slot = c + 1;
            }
            let sim = Sim {
                at_user: core::array::from_fn(|_| AtomicBool::new(false)),
                requested: core::array::from_fn(|_| AtomicBool::new(false)),
                epochs: core::array::from_fn(|_| AtomicU64::new(0)),
                pending: core::array::from_fn(|_| core::array::from_fn(|_| AtomicU64::new(0))),
                user: Mutex::new(UserCores {
                    poked: [false; STALL_CORES],
                    settled: 0,
                }),
                wake: Condvar::new(),
                live_at_trap: core::array::from_fn(|_| AtomicU64::new(0)),
                kernel: Mutex::new(Kernel {
                    current,
                    resident: current,
                    decided: current,
                    tcb: [0; THREADS],
                }),
            };
            for flag in sim.at_user.iter().take(cores) {
                flag.store(true, Ordering::SeqCst);
            }
            sim
        }

        /// One locked entry of core `c`, handed the frame of thread
        /// `trapped.0` holding register word `trapped.1`.  A core that still
        /// runs a thread commits `victim` (takes the thread off that core);
        /// then the settle, the HAL record, the stall and the epoch.  Answers
        /// what the core resumes.
        /// Answers the thread the core resumes and the core its commit
        /// stalled: the model's own record of the change, which the gate
        /// checks the save against without reading the HAL's record.
        fn locked_entry(
            &self,
            c: usize,
            trapped: (usize, u64),
            victim: Option<usize>,
        ) -> (usize, Option<usize>) {
            let mut k = self.kernel.lock().unwrap();
            clear_stall_request_in(&self.requested, c);
            // The save: the current thread's frame, or a vacated core's
            // resident's (`saveCapturedTrapFrame`).
            let (t, word) = trapped;
            if t != NONE && (k.current[c] == t || (k.current[c] == NONE && k.resident[c] == t)) {
                k.tcb[t] = word;
            }
            let mut stalled = None;
            if k.current[c] != NONE {
                if let Some(d) = victim {
                    k.current[d] = NONE;
                    stalled = Some(d);
                }
            }
            // The settle and the HAL record: this core resumes its current
            // thread, or its idle loop.
            k.resident[c] = k.current[c];
            k.decided[c] = k.current[c];
            if let Some(d) = stalled {
                let changed = k.decided[d] != k.current[d];
                let out =
                    stall_if_changed_in(&self.at_user, &self.requested, d, changed, FUEL, |x| {
                        self.user.lock().unwrap().poked[x] = true;
                        self.wake.notify_all();
                    });
                assert_ne!(
                    out,
                    StallOutcome::TimedOut,
                    "the target never left user mode"
                );
                if matches!(out, StallOutcome::NotAtUser | StallOutcome::Left) {
                    record_pending_save_in(&self.epochs, &self.pending, c, d);
                }
            }
            note_locked_entry_in(&self.epochs, c);
            (k.current[c], stalled)
        }

        /// Core `c`'s exit gate: the save wait, then the user flag.  Answers
        /// whether the core returned to EL0 (it resumes `resumes`, whose word
        /// is `word`).
        fn gate(&self, c: usize, mut resumes: usize, word: u64, stalled: Option<usize>) -> bool {
            let waited = await_remote_saves_in(
                &self.epochs,
                &self.pending,
                &self.requested,
                c,
                FUEL,
                |c| {
                    resumes = self.locked_entry(c, (resumes, word), None).0;
                },
                |_| false,
            );
            assert_ne!(waited, SaveWait::TimedOut, "a save wait never ended");
            if let Some(d) = stalled {
                // The initiator proceeds only after the target saved: the
                // thread its commit took off `d` holds, in its TCB, the word
                // it trapped with.
                let t = d + 1;
                let k = self.kernel.lock().unwrap();
                assert_eq!(
                    k.tcb[t],
                    self.live_at_trap[t].load(Ordering::SeqCst),
                    "the initiator's wait ended before the target saved"
                );
            }
            loop {
                if resumes == NONE {
                    return false;
                }
                if enter_user_in(&self.at_user, &self.requested, c) {
                    return true;
                }
                resumes = self.locked_entry(c, (resumes, word), None).0;
            }
        }

        /// Core `c`, running thread `c + 1` at EL0: it issues one syscall that
        /// commits `victim`, then answers pokes until every core has settled.
        fn run(&self, c: usize, victim: Option<usize>, cores: u64) {
            let me = c + 1;
            let mut word = (me as u64) * 100;
            let mut first = true;
            loop {
                if !first {
                    // At EL0: run until poked, or until every core settles.
                    let mut u = self.user.lock().unwrap();
                    loop {
                        if u.poked[c] {
                            u.poked[c] = false;
                            break;
                        }
                        if u.settled == cores {
                            return;
                        }
                        u = self.wake.wait(u).unwrap();
                    }
                    drop(u);
                }
                // The thread ran on and traps: its live word is new.
                word += 1;
                self.live_at_trap[me].store(word, Ordering::SeqCst);
                note_kernel_entry_in(&self.at_user, c);
                let (resumes, stalled) =
                    self.locked_entry(c, (me, word), if first { victim } else { None });
                let back = self.gate(c, resumes, word, stalled);
                if first {
                    self.user.lock().unwrap().settled += 1;
                    self.wake.notify_all();
                    first = false;
                }
                if !back {
                    // Vacated: the core idles, holding nothing.
                    let k = self.kernel.lock().unwrap();
                    assert_eq!(k.resident[c], NONE);
                    return;
                }
            }
        }
    }

    fn spawn_cores(victims: &'static [Option<usize>], bound: Option<usize>) {
        let mut builder = loom::model::Builder::new();
        if bound.is_some() {
            builder.preemption_bound = bound;
        }
        builder.check(move || {
            let cores = victims.len();
            let sim = Arc::new(Sim::new(cores));
            let handles: std::vec::Vec<_> = (1..cores)
                .map(|c| {
                    let sim = sim.clone();
                    loom::thread::spawn(move || sim.run(c, victims[c], cores as u64))
                })
                .collect();
            sim.run(0, victims[0], cores as u64);
            for h in handles {
                h.join().unwrap();
            }
        });
    }

    /// One initiator takes the target's thread while the target runs it,
    /// traps on its own, or sits between its entry and its gate.
    #[test]
    fn the_initiator_returns_only_after_the_target_saved() {
        spawn_cores(&[Some(1), None], None);
    }

    /// Two initiators, each taking the other's thread: whichever commits
    /// second is vacated and commits nothing, and neither wait deadlocks.
    #[test]
    fn two_initiators_against_each_other_both_finish() {
        spawn_cores(&[Some(1), Some(0)], None);
    }

    /// Three cores, each the initiator against the next: a core can wait on
    /// a save while another waits on its own, and serves its own request to
    /// end that wait.  Bounded at three preemptions.
    #[test]
    fn three_cores_in_a_ring_of_stalls_all_finish() {
        spawn_cores(&[Some(1), Some(2), Some(0)], Some(3));
    }
}
