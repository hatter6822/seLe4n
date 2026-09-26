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
//! **The permit also certifies a clean image** (WS-BP BP4.5).  Between the
//! install and minting the permit, [`enter_lean_kernel`] cleans the image's
//! loaded bytes to the Point of Unification and invalidates every instruction
//! cache in the domain (`cache::clean_boot_image_to_pou`), so no thread can be
//! dispatched — by a released secondary or by the boot core's own first
//! scheduling point, which follows Phase 5 — before an initial task's code is
//! fetchable as the firmware loaded it.
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
/// installed the kernel state and the image has been cleaned to the Point of
/// Unification (WS-BP BP4.5); every secondary bring-up consumes one.  So a
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
    unsafe { lean_runtime::consume_io_result(res) }.map_err(|why| match why {
        lean_runtime::IoResultRefused::Error => InitialisationRefused::Error,
        lean_runtime::IoResultRefused::Malformed { tag } => {
            InitialisationRefused::Malformed { tag }
        }
    })?;
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
        fn initialize_seLe4n_SeLe4n(builtin: u8) -> lean_runtime::LeanIoResult;
    }
    let initializer = || {
        // SAFETY: called once, on the primary, before any Lean code runs;
        // `initialise_with`'s guard refuses a second call before it gets here,
        // and nothing else in the image calls this symbol.
        unsafe { initialize_seLe4n_SeLe4n(1) }.into_obj()
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

/// The `ByteArray` the Lean entry parses, built from what the firmware's
/// pointer yielded.
///
/// WS-BP BP4.3.  A pointer the HAL cannot turn into a blob — NULL, a header
/// that is not a device tree, a `totalsize` beyond `MAX_DTB_SIZE` — is handed
/// over as the **empty** array rather than refused here: the verified Lean
/// parser refuses it (`DeviceTreeBootRefusal.unparseableBlob`) and the entry
/// halts every PE (`kernelMain_refuses`), so the decision "is this a board the
/// image may boot on" has one owner and it is the verified one.
#[must_use]
pub fn device_tree_blob(blob: Option<&[u8]>) -> Obj {
    lean_runtime::array::byte_array_of(blob.unwrap_or(&[]))
}

/// Enter the Lean kernel.  Consumes the proof that it was initialized, and
/// returns the licence to release the secondaries.
///
/// `lean_kernel_main` is the primary's boot install and the only Lean upcall
/// that runs outside the readiness gate: it installs the state every gated seam
/// reads, so it cannot sit behind that gate.  It returns only on success — a
/// device tree the verified parser refuses, a board that is not a Raspberry
/// Pi 5, and a refused boot all halt the system inside it
/// (`Platform.FFI.bootAndInitialiseRPi5FromDtbOrHalt`) — so reaching the
/// `return` below is reaching an installed kernel state.  The image's loaded
/// bytes are then cleaned to the Point of Unification before the permit is
/// minted (WS-BP BP4.5), which is the other thing the permit certifies.
///
/// WS-BP BP4.3: the firmware's device tree is copied into a Lean `ByteArray`
/// on the kernel's heap before the call, and the entry takes that copy's one
/// reference.  The copy is read with translation on, inside the window
/// `init_mmu` admitted (`mmu::dtb_window`), which is what makes forming the
/// slice sound.
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
        /// Lean upcall on any PE and before any secondary is released.  `dtb`
        /// must be a live `ByteArray` whose one reference the callee takes.
        fn lean_kernel_main(dtb: Obj) -> lean_runtime::LeanBaseIoUnit;
    }
    // SAFETY: `init_mmu` admitted `mmu::dtb_window(dtb_ptr)` — `MAX_DTB_SIZE`
    // bytes from the pointer, inside the kernel's reserved extent the boot map covers and
    // outside the image — so every slice `dtb_blob_from_ptr` can form lies in
    // mapped, readable memory nothing writes during boot.
    #[cfg(target_arch = "aarch64")]
    let blob = unsafe { crate::cmdline::dtb_blob_from_ptr(dtb_ptr) };
    #[cfg(not(target_arch = "aarch64"))]
    let blob: Option<&[u8]> = {
        let _ = dtb_ptr;
        None
    };
    let dtb = device_tree_blob(blob);
    // SAFETY: the token proves the library initializer ran and succeeded, and
    // it is consumed here, so this call happens at most once per
    // initialization.  `dtb` is the fresh `ByteArray` just built, whose one
    // reference is handed over.
    let res = unsafe { lean_kernel_main(dtb) };
    // SAFETY: `res` is the `BaseIO Unit` value `lean_kernel_main` just
    // returned (`lean_box(0)`); if it is a heap object this caller owns its one
    // reference.
    unsafe { lean_runtime::discharge_base_io(res, "lean_kernel_main") };
    // WS-BP BP4.5: the image's loaded bytes — where an initial task's code is
    // carried — are cleaned to the Point of Unification, and every instruction
    // cache dropped, before the permit that releases a secondary exists and so
    // before any PE can dispatch a thread.
    crate::cache::clean_boot_image_to_pou();
    // WS-BP BP4.6: the install has extended the boot map to the verified
    // board's RAM; from here every PE shares the tables, so they are sealed
    // before the permit that releases one exists.
    crate::mmu::seal_boot_map();
    // WS-BP BP6.1: the per-image half of the runtime handshake is done.  The
    // flag is published `Release` before the permit exists, so every PE the
    // permit releases acquires it through `CORE_READY` before its own per-PE
    // handshake reads it (`lean_ready::initialise_core_runtime`).
    crate::lean_ready::publish_kernel_installed();
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

    /// WS-BP BP4.3: a pointer the HAL could not turn into a blob is handed to
    /// Lean as the empty array — which the verified parser refuses — never as
    /// a refusal decided here.
    #[test]
    fn an_unreadable_device_tree_is_handed_over_empty() {
        let o = device_tree_blob(None);
        // SAFETY: `o` is the live array just built, owned here.
        unsafe {
            assert!(lean_runtime::array::sarray_bytes(o).is_empty());
            lean_runtime::dec(o);
        }
        let blob = [1u8, 2, 3];
        let o = device_tree_blob(Some(&blob));
        // SAFETY: as above.
        unsafe {
            assert_eq!(lean_runtime::array::sarray_bytes(o), &blob);
            lean_runtime::dec(o);
        }
    }
}
