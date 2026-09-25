//! WS-BP BP2.3/BP2.4: the primary's entry into the Lean kernel.
//!
//! Lean compiles each module to an initializer that has to run before any
//! definition from that module is used: it evaluates the module's top-level
//! constants, runs its `initialize` blocks and calls the initializers of
//! everything the module imports.  The library root's initializer,
//! `initialize_seLe4n_SeLe4n`, therefore initializes the whole kernel.
//! Upstream's `lean_initialize_runtime_module` and
//! `lean_io_mark_end_initialization` are not called: they set up per-thread
//! heaps, the task manager and an "initialization finished" flag that the
//! kernel's runtime does not have, and the reachable link does not name them.
//!
//! **The order is enforced by a type, not by a scanner.**  `lean_kernel_main`
//! is reached only through [`enter_lean_kernel`], which takes a
//! [`LeanLibraryInitialised`] by value.  The only way to get one is from
//! [`initialise_with`], and only when the initializer reports success.  The
//! token is neither `Clone` nor `Copy`, and its field is private to this
//! module, so:
//!
//! * code that enters the kernel without initializing it does not compile;
//! * code that enters it twice from one initialization does not compile;
//! * a second initialization is refused at runtime, by the guard.
//!
//! **The install precedes the secondaries, and that is a type too** (WS-BP
//! BP4.2).  `lean_kernel_main` writes the whole kernel state outside every lock
//! bracket, so a secondary running a bracketed seam during it could commit a
//! transition the install then overwrites.  Rather than taking a lock around a
//! write nothing else may race, the race is made impossible: releasing a
//! secondary (`smp::bring_up_secondaries_inner`, which every bring-up path
//! reaches) consumes a [`SecondaryReleasePermit`], and on an image that links
//! the Lean kernel the only permit is the one [`enter_lean_kernel`] returns
//! *after* the install.  An image without the Lean kernel has no install to
//! order, and gets its permit from [`SecondaryReleasePermit::no_lean_kernel`],
//! which does not exist when the kernel is linked.
//!
//! **A failed initialization fails closed.**  If the initializer returns an
//! error, returns something that is not an `IO` result, or runs twice,
//! [`initialise_lean_library`] halts the whole system through
//! `gic::halt_all`.  By then the secondaries have started and are servicing
//! interrupts, so parking only the boot PE would leave them running for a
//! kernel that was never entered.  Since BP4.2 no secondary has been released at
//! that point, and the system-wide halt is still the right one: it is the one
//! barrier every boot-fatal refusal uses, whatever has started.

use core::sync::atomic::{AtomicBool, Ordering};

use crate::lean_runtime::{self, Obj};

/// Proof that the Lean library initializer ran once and succeeded.
///
/// Only [`initialise_with`] builds one, and only on success.  Its field is
/// private to this module and it is neither `Clone` nor `Copy`, so each
/// initialization licenses at most one kernel entry.
#[must_use = "the kernel is entered by passing this to `enter_lean_kernel`"]
#[derive(Debug)]
pub struct LeanLibraryInitialised {
    _private: (),
}

/// Licence to release the secondary PEs.
///
/// On an image that links the Lean kernel the only way to obtain one is
/// [`enter_lean_kernel`], which returns it after `lean_kernel_main` has
/// installed the kernel state; every secondary bring-up consumes one.  So a
/// secondary cannot be released while the unbracketed install runs — the
/// lost-commit shape `kernel_entry.rs` records is closed by construction rather
/// than by a lock (WS-BP BP4.2).  Its field is private to this module and it is
/// neither `Clone` nor `Copy`, so one install licenses one release.
#[must_use = "the secondaries are released by passing this to the bring-up"]
#[derive(Debug)]
pub struct SecondaryReleasePermit {
    _private: (),
}

impl SecondaryReleasePermit {
    /// The permit of an image with no Lean kernel linked: there is no install
    /// for a release to be ordered after.  Absent from an image that links the
    /// kernel (`hw_target`), so no code path there can release a secondary
    /// without the install's permit.  Test builds have it whatever the feature
    /// set, because they run no boot.
    #[cfg(any(test, not(feature = "hw_target")))]
    pub fn no_lean_kernel() -> Self {
        SecondaryReleasePermit { _private: () }
    }
}

/// Why initialization was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InitialisationRefused {
    /// The guard was already set: this is a second initialization.  The
    /// generated initializer is idempotent (it answers `ok` on a second call),
    /// so without this refusal a second call would be granted a second token.
    AlreadyRan,
    /// The initializer returned `IO` error.  The error object is released
    /// without being read, because reading it would mean calling back into
    /// Lean, and the runtime never does that.
    Error,
    /// The initializer returned a scalar, or a constructor whose tag is neither
    /// `ok` (0) nor `error` (1).  No generated initializer does that, so it is
    /// refused as a malformed result rather than read as success.
    Malformed {
        /// The tag found, or `None` for a scalar.
        tag: Option<u8>,
    },
}

/// Classify and consume an `IO` result.
///
/// Returns `Ok(())` exactly for a heap constructor with tag 0 (`lean.h`'s
/// `lean_io_result_is_ok`).  Every heap object, whatever its tag, has the
/// reference the initializer returned released.
///
/// # Safety
///
/// `res` must be a scalar or a live heap object whose one reference the caller
/// owns; this call consumes it.
unsafe fn consume_io_result(res: Obj) -> Result<(), InitialisationRefused> {
    if lean_runtime::is_scalar(res) {
        return Err(InitialisationRefused::Malformed { tag: None });
    }
    // SAFETY: `res` is a live heap object by the caller's contract and the
    // test above.
    let tag = unsafe { lean_runtime::tag(res) };
    // SAFETY: the reference is the caller's to hand over, and nothing below
    // reads `res` again.
    unsafe { lean_runtime::dec(res) };
    match tag {
        0 => Ok(()),
        1 => Err(InitialisationRefused::Error),
        other => Err(InitialisationRefused::Malformed { tag: Some(other) }),
    }
}

/// Run `initializer` once under `guard` and classify its result.
///
/// The guard is set before the initializer runs, so a second call is refused
/// whether the first one succeeded or not.  A failed initialization cannot be
/// retried: Lean's generated initializer sets its own "already initialized"
/// flag before it calls anything, so a second attempt would answer `ok`
/// without running the part that failed.
///
/// # Safety
///
/// `initializer` must return a scalar or a heap object whose one reference is
/// handed to this function.
pub unsafe fn initialise_with(
    guard: &AtomicBool,
    initializer: impl FnOnce() -> Obj,
) -> Result<LeanLibraryInitialised, InitialisationRefused> {
    if guard.swap(true, Ordering::AcqRel) {
        return Err(InitialisationRefused::AlreadyRan);
    }
    let res = initializer();
    // SAFETY: forwarded from the caller.
    unsafe { consume_io_result(res) }?;
    Ok(LeanLibraryInitialised { _private: () })
}

/// Set by the first call to [`initialise_lean_library`].
#[cfg(feature = "hw_target")]
static LEAN_LIBRARY_INITIALISED: AtomicBool = AtomicBool::new(false);

/// Run the Lean library initializer on the primary, or halt the system.
///
/// Returns only after the initializer has succeeded.  On any refusal it reports
/// the reason on the boot UART and calls `gic::halt_all()`.
#[cfg(feature = "hw_target")]
pub fn initialise_lean_library() -> LeanLibraryInitialised {
    extern "C" {
        /// # Safety
        ///
        /// Lean's generated initializer for the library root, `SeLe4n`.  It
        /// must run on the primary before any Lean definition is used, with
        /// `builtin = 1` because this is the image the kernel boots, not a
        /// plugin loaded into a running environment.  It returns an `IO` result
        /// whose one reference the caller owns.
        fn initialize_seLe4n_SeLe4n(builtin: u8) -> Obj;
    }
    let initializer = || {
        // SAFETY: called once, on the primary, before any Lean code runs;
        // `initialise_with`'s guard refuses a second call before it gets here,
        // and nothing else in the image calls this symbol.
        unsafe { initialize_seLe4n_SeLe4n(1) }
    };
    // SAFETY: the initializer returns an `IO` result whose one reference is
    // handed over, which is `initialise_with`'s contract.
    let outcome = unsafe { initialise_with(&LEAN_LIBRARY_INITIALISED, initializer) };
    match outcome {
        Ok(token) => token,
        Err(why) => {
            crate::kprintln!(
                "[boot] FATAL: Lean library initialization refused: {:?}",
                why
            );
            crate::gic::halt_all()
        }
    }
}

/// Enter the Lean kernel.  Consumes the proof that it was initialized, and
/// returns the licence to release the secondaries.
///
/// `lean_kernel_main` is the primary's boot install and the only Lean upcall
/// that runs outside the readiness gate: it installs the state every gated seam
/// reads, so it cannot sit behind that gate.  It returns only on success — a
/// refused boot halts the system inside it
/// (`Platform.FFI.bootAndInitialiseRPi5OrHalt`) — so reaching the `return`
/// below is reaching an installed kernel state, which is what the permit
/// certifies.
#[cfg(feature = "hw_target")]
pub fn enter_lean_kernel(
    initialised: LeanLibraryInitialised,
    dtb_ptr: u64,
) -> SecondaryReleasePermit {
    let LeanLibraryInitialised { _private: () } = initialised;
    extern "C" {
        /// # Safety
        ///
        /// The primary PE's one-time boot install, and the only Lean upcall
        /// that runs *outside* the readiness gate.  It must run exactly once,
        /// on the boot core, after the library initializer, before any other
        /// Lean upcall on any PE and before any secondary is released.
        /// `dtb_ptr` must be the firmware's device-tree pointer.
        fn lean_kernel_main(dtb_ptr: u64);
    }
    // SAFETY: the token proves the library initializer ran and succeeded, and
    // it is consumed here, so this call happens at most once per
    // initialization.  The firmware's DTB pointer is passed through.
    unsafe { lean_kernel_main(dtb_ptr) };
    SecondaryReleasePermit { _private: () }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean_runtime::{alloc_ctor, boxed, io_result_mk_error, io_result_mk_ok};

    fn run(res: Obj) -> Result<LeanLibraryInitialised, InitialisationRefused> {
        let guard = AtomicBool::new(false);
        // SAFETY: every caller hands over a fresh object or a scalar.
        unsafe { initialise_with(&guard, || res) }
    }

    #[test]
    fn an_ok_result_initialises() {
        assert!(run(io_result_mk_ok(boxed(0))).is_ok());
    }

    #[test]
    fn an_error_result_is_refused() {
        assert_eq!(
            run(io_result_mk_error(boxed(0))).unwrap_err(),
            InitialisationRefused::Error
        );
    }

    #[test]
    fn a_scalar_is_refused_not_read_as_success() {
        // `lean_box(0)` is what a successful initializer *wraps*, never what it
        // returns; returning it bare is malformed.
        assert_eq!(
            run(boxed(0)).unwrap_err(),
            InitialisationRefused::Malformed { tag: None }
        );
    }

    #[test]
    fn a_constructor_of_another_tag_is_refused() {
        for tag in [2u8, 3, 243] {
            assert_eq!(
                run(alloc_ctor(tag, 0, 0)).unwrap_err(),
                InitialisationRefused::Malformed { tag: Some(tag) }
            );
        }
    }

    #[test]
    fn a_second_initialisation_is_refused_after_success() {
        let guard = AtomicBool::new(false);
        // SAFETY: fresh objects.
        let first = unsafe { initialise_with(&guard, || io_result_mk_ok(boxed(0))) };
        assert!(first.is_ok());
        let mut ran = false;
        // SAFETY: the initializer is not called.
        let second = unsafe {
            initialise_with(&guard, || {
                ran = true;
                io_result_mk_ok(boxed(0))
            })
        };
        assert_eq!(second.unwrap_err(), InitialisationRefused::AlreadyRan);
        assert!(
            !ran,
            "a refused second initialization must not run the initializer"
        );
    }

    #[test]
    fn a_failed_initialisation_is_not_retried() {
        let guard = AtomicBool::new(false);
        // SAFETY: fresh objects.
        let first = unsafe { initialise_with(&guard, || io_result_mk_error(boxed(0))) };
        assert_eq!(first.unwrap_err(), InitialisationRefused::Error);
        // SAFETY: fresh objects.
        let second = unsafe { initialise_with(&guard, || io_result_mk_ok(boxed(0))) };
        assert_eq!(second.unwrap_err(), InitialisationRefused::AlreadyRan);
    }

    #[test]
    fn the_result_is_released() {
        // A shared result keeps one reference after the call, which proves the
        // call released exactly the one it was handed.
        let res = io_result_mk_ok(boxed(0));
        // SAFETY: `res` is live and owned here.
        unsafe { lean_runtime::inc(res) };
        let guard = AtomicBool::new(false);
        // SAFETY: one of the two references is handed over.
        assert!(unsafe { initialise_with(&guard, || res) }.is_ok());
        // SAFETY: `res` is still live: one reference remains.
        let rc = unsafe { lean_runtime::header(res) }.rc;
        assert_eq!(rc, 1);
        // SAFETY: the last reference.
        unsafe { lean_runtime::dec(res) };
    }
}
