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
//! **Who marks ready (WS-BP BP6)**.  Every PE marks *itself*, through one
//! function, [`become_ready_or_halt`], and at one point in its boot: after its
//! own hardware initialization and the per-PE half of the Lean runtime
//! handshake (BP6.1), and **before** it unmasks IRQs (BP6.2).  The boot core
//! does it in `rust_boot_main` once `lean_kernel_main` has installed the kernel
//! state; each secondary does it in `rust_secondary_main` once its MMU, vectors,
//! GIC CPU interface and timer are up.  So no PE ever takes an interrupt in the
//! degraded, Rust-only mode once the kernel exists, and `build.rs`'s
//! `readiness_publication_status` holds both sites to that order.
//!
//! **What "per-PE" means here (BP6.1).**  Upstream's runtime initializes a
//! per-thread heap, a task manager and a stack guard for each OS thread.  The
//! kernel's runtime (`lean_runtime`) has none of those: it serves every object
//! from the one kernel heap under its leaf lock, and no object is ever
//! multi-threaded.  The library initializer and the install are per-*image*
//! and run once, on the boot core.  What remains per-PE is the PE's own
//! posture, and [`initialise_core_runtime_with`] decides it before it mints the
//! [`LeanRuntimeReadyOnCore`] token that marking consumes:
//!
//! 1. the call runs on the PE it is about (`TPIDR_EL1` names it);
//! 2. the PE translates (`SCTLR_EL1.M`), since the kernel heap's lock — and
//!    the handshake's own once-only guard, which is why this is decided
//!    before it — is an exclusive-monitor atomic that needs Normal cacheable
//!    memory;
//! 3. the handshake runs once per PE (the guard);
//! 4. the kernel install has happened-before (an `Acquire` of the flag the
//!    install publishes with `Release` before it mints the secondaries'
//!    release permit);
//! 5. the PE runs on its **own** stack slot — Lean code on two PEs sharing a
//!    stack corrupts both, and nothing else would notice;
//! 6. the kernel heap answers an allocation and a free **from this PE**.
//!
//! **The mark is safe and the promise is a type.**  Until BP6 marking was an
//! `unsafe fn(core_id)` whose safety contract *was* the readiness promise.  It
//! now consumes a [`LeanRuntimeReadyOnCore`], whose only safe constructor is the
//! checked handshake; the one way to assert readiness without it is
//! [`LeanRuntimeReadyOnCore::assume_initialised`], which is `unsafe` and exists
//! for host tests, where no gated seam is compiled to call Lean.
//!
//! **Memory ordering**: `Release` on mark, `Acquire` on check — a core
//! that observes `ready` also observes every write the initialization
//! performed (the Lean runtime structures, the installed kernel state).

use core::sync::atomic::{AtomicBool, AtomicU8, Ordering};

/// Per-core readiness bitmask (bit `n` = core `n`).  `0` at boot: no
/// core may enter the Lean runtime until its bit is set.
static LEAN_READY_CORES: AtomicU8 = AtomicU8::new(0);

/// May `core_id` call into the Lean runtime?
///
/// `false` for out-of-range ids (fail closed — an id the mask cannot
/// represent is never ready).
#[inline]
pub fn lean_ready(core_id: usize) -> bool {
    mask_marks(ready_mask(), core_id)
}

/// The readiness mask as of this read (`Acquire`, so a set bit carries the
/// initialization behind it).  `smp::core_serves` reads it once per query.
#[inline]
pub fn ready_mask() -> u8 {
    LEAN_READY_CORES.load(Ordering::Acquire)
}

/// Whether `mask` marks `core_id` ready: the one reading of a bit in the
/// readiness mask, shared by [`lean_ready`] and `smp::core_serves_in` so the
/// two cannot decide an out-of-range id differently.
#[inline]
#[must_use]
pub fn mask_marks(mask: u8, core_id: usize) -> bool {
    core_id < 8 && mask & (1 << core_id) != 0
}

/// Bytes of one PE's kernel stack: `link.ld`'s `.stack` for the boot core and
/// each of the three `.smp_stacks` slots `boot.S::secondary_entry` hands a
/// secondary (`__smp_secondary_stack_top - (context_id - 1) * 64 KiB`).
pub const CORE_STACK_BYTES: usize = 0x1_0000;

/// The stack `core_id` must be running on, as `(lowest, highest)` addresses.
///
/// Core 0 runs on the boot stack `[boot_stack.0, boot_stack.1)`; secondary `c`
/// on the slot `boot.S` computes, which is the `c`-th 64 KiB region *below*
/// `secondary_stack_top`.  `None` for a core the image has no stack for.
#[must_use]
pub fn own_stack_extent(
    core_id: usize,
    boot_stack: (usize, usize),
    secondary_stack_top: usize,
) -> Option<(usize, usize)> {
    match core_id {
        0 => Some(boot_stack),
        c if c <= crate::smp::MAX_SECONDARY_CORES => {
            let hi = secondary_stack_top.checked_sub((c - 1) * CORE_STACK_BYTES)?;
            let lo = hi.checked_sub(CORE_STACK_BYTES)?;
            Some((lo, hi))
        }
        _ => None,
    }
}

/// What the per-PE handshake reads off the PE it runs on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CorePosture {
    /// The core `TPIDR_EL1` names — the PE actually executing.
    pub executing_core: u64,
    /// `SCTLR_EL1.M`: stage 1 translation is enabled on this PE.
    pub translation_enabled: bool,
    /// This PE's stack pointer at the handshake.
    pub stack_pointer: usize,
    /// The stack the core being initialized must be running on
    /// ([`own_stack_extent`]).
    pub own_stack: Option<(usize, usize)>,
}

/// Why a PE's per-core runtime handshake was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CoreRuntimeRefused {
    /// The core id is outside the readiness mask.
    OutOfRange,
    /// The handshake for `core` ran on another PE.
    NotTheExecutingCore { core: usize, executing: u64 },
    /// The handshake already ran for this core, successfully or not.  A
    /// refused handshake is not retried: its refusal is the boot's verdict.
    AlreadyInitialised,
    /// The kernel install has not published — the per-image half has not
    /// happened-before this PE.
    KernelNotInstalled,
    /// Stage 1 translation is off on this PE.
    TranslationDisabled,
    /// The PE is not running on the stack slot its core owns.
    StackNotOwnSlot {
        stack_pointer: usize,
        own_stack: Option<(usize, usize)>,
    },
    /// The kernel heap did not serve an allocation and a free from this PE.
    HeapUnreachable,
}

/// Proof that the per-PE half of the Lean runtime handshake succeeded on
/// `core`, on `core` itself.
///
/// Only [`initialise_core_runtime_with`] builds one on success (and
/// [`LeanRuntimeReadyOnCore::assume_initialised`], unsafely).  Its field is
/// private to this module and it is neither `Clone` nor `Copy`, so one
/// handshake licenses one mark.
#[must_use = "a core is marked ready by passing this to `mark_lean_ready`"]
#[derive(Debug)]
pub struct LeanRuntimeReadyOnCore {
    core: usize,
}

impl LeanRuntimeReadyOnCore {
    /// The core this token licenses.
    #[must_use]
    pub fn core(&self) -> usize {
        self.core
    }

    /// A token for `core_id` with no handshake behind it.
    ///
    /// # Safety
    ///
    /// Marking `core_id` ready with the result is a load-bearing promise:
    /// every gated seam (`timer::per_core_timer_tick_isr`,
    /// `trap::reschedule_sgi_handler`, `smp::rust_secondary_main`, the SVC and
    /// fault seams) will thereafter call Lean-emitted symbols from that PE.
    /// The caller must guarantee that the Lean runtime is initialized for that
    /// PE and the kernel state installed — or, as in the host tests that are
    /// this function's reason to exist, that no gated seam is compiled to call
    /// Lean at all (`hw_target` off), so the promise is vacuous.
    pub unsafe fn assume_initialised(core_id: usize) -> Self {
        LeanRuntimeReadyOnCore { core: core_id }
    }
}

/// Run the per-PE handshake for `core_id` and mint its token.
///
/// The checks run in the order the module docs list them.  `guard` is set for
/// `core_id` before anything past the translation check, so a second
/// handshake for one core is refused whether the first succeeded or not; the
/// two checks ahead of it are pure register reads, which is what lets a
/// refused PE be refused rather than parked on an atomic it cannot complete.
///
/// # Safety
///
/// `posture` must be read from the PE executing this call, and `heap_probe`
/// must allocate and free on the heap the Lean runtime serves; a fabricated
/// posture or a probe that answers `true` without allocating mints a token no
/// handshake stands behind.  [`initialise_core_runtime`] is the caller that
/// satisfies this on the image.
pub unsafe fn initialise_core_runtime_with(
    guard: &AtomicU8,
    installed: &AtomicBool,
    core_id: usize,
    posture: &CorePosture,
    heap_probe: impl FnOnce() -> bool,
) -> Result<LeanRuntimeReadyOnCore, CoreRuntimeRefused> {
    if core_id >= 8 {
        return Err(CoreRuntimeRefused::OutOfRange);
    }
    if posture.executing_core != core_id as u64 {
        return Err(CoreRuntimeRefused::NotTheExecutingCore {
            core: core_id,
            executing: posture.executing_core,
        });
    }
    // The v0.36.2 audit: translation is decided BEFORE the guard.  The guard
    // is a `fetch_or` — an exclusive-monitor access, which on a PE with
    // translation off (every access Device-nGnRnE, no global monitor on the
    // BCM271x) never succeeds — so a handshake that read the guard first
    // would spin forever on exactly the PE it exists to refuse.
    if !posture.translation_enabled {
        return Err(CoreRuntimeRefused::TranslationDisabled);
    }
    if guard.fetch_or(1 << core_id, Ordering::AcqRel) & (1 << core_id) != 0 {
        return Err(CoreRuntimeRefused::AlreadyInitialised);
    }
    if !installed.load(Ordering::Acquire) {
        return Err(CoreRuntimeRefused::KernelNotInstalled);
    }
    let on_own_stack = posture
        .own_stack
        .is_some_and(|(lo, hi)| lo < posture.stack_pointer && posture.stack_pointer <= hi);
    if !on_own_stack {
        return Err(CoreRuntimeRefused::StackNotOwnSlot {
            stack_pointer: posture.stack_pointer,
            own_stack: posture.own_stack,
        });
    }
    if !heap_probe() {
        return Err(CoreRuntimeRefused::HeapUnreachable);
    }
    Ok(LeanRuntimeReadyOnCore { core: core_id })
}

/// Set by the kernel install, `Release`, before it mints the permit that
/// releases the secondaries (`lean_entry::enter_lean_kernel`).
#[cfg(feature = "hw_target")]
static KERNEL_INSTALLED: AtomicBool = AtomicBool::new(false);

/// The per-core handshake guard: bit `n` set once core `n`'s handshake ran.
#[cfg(feature = "hw_target")]
static CORE_RUNTIME_INITIALISED: AtomicU8 = AtomicU8::new(0);

/// Publish that the kernel state is installed.  Called once, by
/// `lean_entry::enter_lean_kernel`, after `lean_kernel_main` returned and
/// before the secondaries' release permit exists.
#[cfg(feature = "hw_target")]
pub(crate) fn publish_kernel_installed() {
    KERNEL_INSTALLED.store(true, Ordering::Release);
}

/// The executing PE's posture, for the handshake of `core_id`.
#[cfg(feature = "hw_target")]
fn executing_posture(core_id: usize) -> CorePosture {
    #[cfg(target_arch = "aarch64")]
    {
        extern "C" {
            static __stack_bottom: u8;
            static __stack_top: u8;
            static __smp_secondary_stack_top: u8;
        }
        let boot_stack = (
            &raw const __stack_bottom as usize,
            &raw const __stack_top as usize,
        );
        let secondary_top = &raw const __smp_secondary_stack_top as usize;
        let stack_pointer: usize;
        // SAFETY: reads the stack pointer into a register; touches no memory
        // and no flags.
        unsafe {
            core::arch::asm!("mov {}, sp", out(reg) stack_pointer, options(nomem, nostack, preserves_flags));
        }
        CorePosture {
            executing_core: crate::per_cpu::current_core_id_from_tpidr(),
            translation_enabled: crate::registers::read_sctlr_el1() & 1 != 0,
            stack_pointer,
            own_stack: own_stack_extent(core_id, boot_stack, secondary_top),
        }
    }
    // A host build with `hw_target` (the clippy lane) never boots; its posture
    // refuses rather than inventing a stack.
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = core_id;
        CorePosture {
            executing_core: crate::per_cpu::current_core_id_from_tpidr(),
            translation_enabled: false,
            stack_pointer: 0,
            own_stack: None,
        }
    }
}

/// The per-PE handshake on the image (WS-BP BP6.1): the executing PE's posture
/// and one allocation and free on the kernel heap.
#[cfg(feature = "hw_target")]
pub fn initialise_core_runtime(
    core_id: usize,
) -> Result<LeanRuntimeReadyOnCore, CoreRuntimeRefused> {
    let posture = executing_posture(core_id);
    let heap_probe = || match crate::lean_heap::kernel_alloc(16, 8) {
        Ok(addr) => crate::lean_heap::kernel_free(addr).is_ok(),
        Err(_) => false,
    };
    // SAFETY: `posture` was just read from this PE's own registers and the
    // linker's stack symbols, and the probe allocates and frees on the kernel
    // heap every Lean object lives in.
    unsafe {
        initialise_core_runtime_with(
            &CORE_RUNTIME_INITIALISED,
            &KERNEL_INSTALLED,
            core_id,
            &posture,
            heap_probe,
        )
    }
}

/// Initialize `core_id`'s per-PE runtime and mark it ready, or halt through
/// `halt` (WS-BP BP6.1/BP6.2).
///
/// The one place a core is marked ready.  `rust_boot_main` calls it for the
/// boot core with `gic::halt_all` — nothing is released yet, and a boot core
/// that cannot serve the kernel is a boot that failed.  `rust_secondary_main`
/// calls it with `cpu::fatal_halt`: the secondary parks, it never publishes
/// `CORE_IRQ_READY`, and the boot core's bounded readiness wait refuses the
/// topology and halts the system (BP6.3).  Both call sites precede their
/// `enable_irq`, which `build.rs` holds them to.
#[cfg(feature = "hw_target")]
pub fn become_ready_or_halt(core_id: usize, halt: fn() -> !) {
    match initialise_core_runtime(core_id) {
        Ok(ready) => mark_lean_ready(ready),
        Err(why) => {
            crate::kprintln!(
                "[ready] core {}: FATAL: per-core Lean runtime refused: {:?}",
                core_id,
                why
            );
            halt()
        }
    }
}

/// Mark the token's core ready to enter the Lean runtime.
///
/// The token is the promise `mark_lean_ready` used to take as an `unsafe`
/// contract: the per-PE handshake ran on that core and succeeded (or, in a host
/// test, the promise is vacuous).  Release ordering publishes the handshake's
/// writes to every core that acquires the mask.  An out-of-range core — only
/// reachable through `assume_initialised` — sets nothing.
#[inline]
pub fn mark_lean_ready(ready: LeanRuntimeReadyOnCore) {
    let LeanRuntimeReadyOnCore { core } = ready;
    if core >= 8 {
        return;
    }
    LEAN_READY_CORES.fetch_or(1 << core, Ordering::Release);
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
        // SAFETY: host-side unit test — no gated seam is compiled to call
        // Lean here (`hw_target` off), so the readiness promise is vacuous.
        let ready = unsafe { LeanRuntimeReadyOnCore::assume_initialised(6) };
        mark_lean_ready(ready);
        assert!(lean_ready(6));
    }

    #[test]
    fn out_of_range_ids_fail_closed() {
        // SAFETY: host-side unit test (see above); out-of-range is a no-op.
        let ready = unsafe { LeanRuntimeReadyOnCore::assume_initialised(99) };
        mark_lean_ready(ready); // ignored — nothing to set
        assert!(!lean_ready(99));
        assert!(!lean_ready(8));
        assert!(!lean_ready(usize::MAX));
    }

    #[test]
    fn marking_one_core_leaves_others_untouched() {
        // SAFETY: host-side unit test (see above).
        let ready = unsafe { LeanRuntimeReadyOnCore::assume_initialised(7) };
        mark_lean_ready(ready);
        assert!(lean_ready(7));
        assert!(!lean_ready(5));
    }

    // ---------------------------------------------------------------
    // WS-BP BP6.1: the per-PE handshake.  Each test owns its guard and
    // its install flag, so none reads process-global state.
    // ---------------------------------------------------------------

    const BOOT_STACK: (usize, usize) = (0x10_0000, 0x11_0000);
    const SECONDARY_TOP: usize = 0x14_0000;

    fn posture(core: usize) -> CorePosture {
        let own = own_stack_extent(core, BOOT_STACK, SECONDARY_TOP);
        CorePosture {
            executing_core: core as u64,
            translation_enabled: true,
            stack_pointer: own.map_or(0, |(_, hi)| hi - 64),
            own_stack: own,
        }
    }

    fn handshake(
        guard: &AtomicU8,
        installed: bool,
        core: usize,
        posture: &CorePosture,
        heap: bool,
    ) -> Result<LeanRuntimeReadyOnCore, CoreRuntimeRefused> {
        let flag = AtomicBool::new(installed);
        // SAFETY: host-side unit test; the token is inspected, never marked.
        unsafe { initialise_core_runtime_with(guard, &flag, core, posture, || heap) }
    }

    #[test]
    fn each_core_owns_the_stack_slot_boot_s_gives_it() {
        assert_eq!(
            own_stack_extent(0, BOOT_STACK, SECONDARY_TOP),
            Some(BOOT_STACK)
        );
        assert_eq!(
            own_stack_extent(1, BOOT_STACK, SECONDARY_TOP),
            Some((SECONDARY_TOP - CORE_STACK_BYTES, SECONDARY_TOP))
        );
        assert_eq!(
            own_stack_extent(3, BOOT_STACK, SECONDARY_TOP),
            Some((
                SECONDARY_TOP - 3 * CORE_STACK_BYTES,
                SECONDARY_TOP - 2 * CORE_STACK_BYTES
            ))
        );
        assert_eq!(own_stack_extent(4, BOOT_STACK, SECONDARY_TOP), None);
    }

    #[test]
    fn a_handshake_on_its_own_pe_mints_a_token_for_that_core() {
        for core in 0..4 {
            let guard = AtomicU8::new(0);
            let token = handshake(&guard, true, core, &posture(core), true).unwrap();
            assert_eq!(token.core(), core);
        }
    }

    #[test]
    fn a_handshake_for_another_pe_is_refused() {
        let guard = AtomicU8::new(0);
        let mut p = posture(2);
        p.executing_core = 1;
        assert_eq!(
            handshake(&guard, true, 2, &p, true).unwrap_err(),
            CoreRuntimeRefused::NotTheExecutingCore {
                core: 2,
                executing: 1
            }
        );
        // The refusal happened before the guard: the right PE may still run it.
        assert!(handshake(&guard, true, 2, &posture(2), true).is_ok());
    }

    #[test]
    fn a_second_handshake_is_refused_whatever_the_first_did() {
        let guard = AtomicU8::new(0);
        assert_eq!(
            handshake(&guard, false, 1, &posture(1), true).unwrap_err(),
            CoreRuntimeRefused::KernelNotInstalled
        );
        assert_eq!(
            handshake(&guard, true, 1, &posture(1), true).unwrap_err(),
            CoreRuntimeRefused::AlreadyInitialised
        );
        // Another core's bit is untouched.
        assert!(handshake(&guard, true, 3, &posture(3), true).is_ok());
    }

    #[test]
    fn the_install_must_happen_before_the_handshake() {
        let guard = AtomicU8::new(0);
        assert_eq!(
            handshake(&guard, false, 0, &posture(0), true).unwrap_err(),
            CoreRuntimeRefused::KernelNotInstalled
        );
    }

    #[test]
    fn a_pe_without_translation_is_refused() {
        let guard = AtomicU8::new(0);
        let mut p = posture(1);
        p.translation_enabled = false;
        assert_eq!(
            handshake(&guard, true, 1, &p, true).unwrap_err(),
            CoreRuntimeRefused::TranslationDisabled
        );
        // The v0.36.2 audit: the refusal came before the guard was touched —
        // on the board the guard is an exclusive-monitor access that a PE
        // without translation cannot complete, so the check must not reach
        // it.  The retired order (guard first) leaves bit 1 set here.
        assert_eq!(guard.load(Ordering::Relaxed), 0, "the guard is untouched");
        assert!(handshake(&guard, true, 1, &posture(1), true).is_ok());
    }

    #[test]
    fn a_pe_on_another_cores_stack_is_refused() {
        // Core 2 running on core 1's slot — what a firmware that woke the
        // wrong PE with a valid context id would produce.
        let guard = AtomicU8::new(0);
        let mut p = posture(2);
        p.stack_pointer = posture(1).stack_pointer;
        assert!(matches!(
            handshake(&guard, true, 2, &p, true).unwrap_err(),
            CoreRuntimeRefused::StackNotOwnSlot { .. }
        ));
        // The slot's own top is inside it; its bottom, and one past its top,
        // are not (the stack grows down from the top).
        let (lo, hi) = posture(3).own_stack.unwrap();
        for (sp, ok) in [(hi, true), (lo + 16, true), (lo, false), (hi + 16, false)] {
            let guard = AtomicU8::new(0);
            let mut p = posture(3);
            p.stack_pointer = sp;
            assert_eq!(
                handshake(&guard, true, 3, &p, true).is_ok(),
                ok,
                "sp {sp:#x}"
            );
        }
        // A core the image has no stack for cannot be on its own stack.
        let guard = AtomicU8::new(0);
        let mut p = posture(5);
        p.executing_core = 5;
        assert!(matches!(
            handshake(&guard, true, 5, &p, true).unwrap_err(),
            CoreRuntimeRefused::StackNotOwnSlot {
                own_stack: None,
                ..
            }
        ));
    }

    #[test]
    fn an_unreachable_heap_is_refused() {
        let guard = AtomicU8::new(0);
        assert_eq!(
            handshake(&guard, true, 0, &posture(0), false).unwrap_err(),
            CoreRuntimeRefused::HeapUnreachable
        );
    }

    #[test]
    fn an_out_of_range_core_is_refused_before_anything_else() {
        let guard = AtomicU8::new(0);
        let mut p = posture(0);
        p.executing_core = 8;
        assert_eq!(
            handshake(&guard, true, 8, &p, true).unwrap_err(),
            CoreRuntimeRefused::OutOfRange
        );
        assert_eq!(guard.load(Ordering::Relaxed), 0);
    }
}
