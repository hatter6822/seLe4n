// SPDX-License-Identifier: GPL-3.0-or-later
//! The remote-core stall: a commit that changes what another core runs does
//! not return until that core has left the thread it was running.
//!
//! seL4 stalls a remote core synchronously when an operation takes a thread
//! off it (`remoteTCBStall`: an IPI, then a wait until the remote core has
//! entered the kernel), so a deleted or suspended thread executes no user
//! instruction once the operation has returned.  Here a commit may take a
//! thread off another core's current slot (a final delete's finalisation, a
//! suspend) while that core's hardware still runs it at EL0.  Every
//! committing entry therefore checks, after its commit, each other core
//! against the committed state (`Concurrency.stallChangedCores` on the Lean
//! side, [`stall_if_changed_in`] here) and waits for any core it changed to
//! leave user mode.
//!
//! ## The two flags
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
//! ## Why the wait is sound
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
//! ## Why it cannot deadlock
//!
//! The target clears its user flag before it takes any lock, so a target
//! spinning on the kernel-entry lock the initiator holds is not at user and
//! is not waited on.  Two cores taking each other's threads at once are
//! serialised by that lock: the second commit finds the first core inside
//! the kernel.  The initiator waits on nothing but the target's exception
//! entry, which EL0 cannot mask, so the wait is bounded; exhausting
//! [`STALL_WAIT_FUEL`] means the target is wedged and the system halts
//! fail-closed, as a wedged shootdown or kernel-entry lock does.

use core::sync::atomic::{AtomicBool, Ordering};

/// One flag per core.
pub type CoreFlags = [AtomicBool; crate::svc_dispatch::RETURN_FRAME_CORES];

/// Per core: the core is at EL0, or past its user-exit gate on the way there.
pub static AT_USER: CoreFlags =
    [const { AtomicBool::new(false) }; crate::svc_dispatch::RETURN_FRAME_CORES];

/// Per core: a commit on another core changed what the core runs since the
/// decision its next return to EL0 carries.
pub static STALL_REQUESTED: CoreFlags =
    [const { AtomicBool::new(false) }; crate::svc_dispatch::RETURN_FRAME_CORES];

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
        core::hint::spin_loop();
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

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;

    fn flags() -> CoreFlags {
        [const { AtomicBool::new(false) }; crate::svc_dispatch::RETURN_FRAME_CORES]
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

    #[test]
    fn recorded_codes_match_the_lean_thread_codes() {
        assert_eq!(recorded_code(crate::ffi::NO_CURRENT_THREAD), 0);
        assert_eq!(recorded_code(0), 1);
        assert_eq!(recorded_code(41), 42);
    }
}
