-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.API
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Platform.Boot
-- WS-RC R2 audit: `bv_decide` for `encodeOk_high_bit_clear`.  The
-- tactic discharges closed `BitVec` propositions arising from
-- `UInt64`'s bitwise operations.
import Std.Tactic.BVDecide

/-!
# FFI Bridge: Lean Kernel ↔ Rust HAL

WS-RC R2 (closes DEEP-FFI-01/02/03 + DEEP-TEST-03).  After this phase
the Lean kernel's verified syscall entry (`syscallEntryChecked`) and
thread-suspend handler (`suspendThread`) are reachable from the
hardware SVC path.  The module also retains its prior role as the
holder of the `@[extern]` C-bridge declarations consumed by the Rust
HAL.

## Direction of the bridge

Two directions cross the FFI boundary:

1. **Lean → Rust** (most declarations in this file): Lean calls into
   the Rust HAL via `@[extern "ffi_*"]` `opaque` declarations.  Each
   such declaration corresponds to a `#[no_mangle] pub extern "C"`
   function in `rust/sele4n-hal/src/ffi.rs`.  On a hardware build the
   Lean compiler resolves these symbols against `libsele4n_hal.a`; on a
   simulation build (running via `lake env lean --run` or the
   `MainTraceHarness`) these symbols are never invoked because the
   pure-model paths replace them entirely.
2. **Rust → Lean** (the `@[export]` declarations): the Rust HAL needs
   to call back into the verified kernel after handling an exception
   bracket.  Lean emits a C-callable wrapper for each `@[export]`
   declaration; the Rust side declares a matching
   `extern "C" { fn ... }` block.

## Conditional compilation (DEEP-FFI-03)

The two directions are gated identically — by Lean 4's standard
attribute semantics rather than by an in-source preprocessor switch.
Lean does not have a `#ifdef`-style mechanism for excluding
declarations from compilation, so the "gating" is **link-time**:

- On a hardware build the Rust HAL is linked into the Lean output, so
  the `@[extern]` symbols resolve to the corresponding
  `#[no_mangle] pub extern "C"` functions in
  `rust/sele4n-hal/src/{ffi,svc_dispatch}.rs`, and the `@[export]`
  symbols (`suspend_thread_inner`, `syscall_dispatch_inner`) are
  reachable from the Rust caller via `extern "C" { fn ... }` blocks.
- On a simulation build (host development, CI smoke/full test runs)
  the Rust HAL is **not** linked.  Test paths consume the pure-model
  Lean kernel directly via `Testing/MainTraceHarness.lean` and the
  per-suite executables; the `@[extern]` bodies are never invoked
  because the simulation path never crosses the FFI boundary, and the
  `@[export]` symbols are emitted into the C output but reachable
  only from a future hardware build (not from the Lean test
  binaries, which never `dlsym` them).

Per WS-RC R12.B the gating is uniformly fail-closed: any path that
reaches an `@[extern]` symbol without the Rust HAL linked would
surface as a missing-symbol link error at build time — the desired
behaviour (no silent stub that pretends to do hardware work).
Symmetrically, an `@[export]` symbol is never invoked from a
simulation build because no Rust HAL is linked to make the upcall.

## Function groups

- **Timer**: Counter read, tick count, reprogram
- **GIC**: IRQ acknowledge, end-of-interrupt, spurious check
- **TLB**: Full flush, per-ASID flush, per-VAddr flush
- **MMIO**: 32/64-bit volatile read/write
- **UART**: Debug character output
- **Interrupts**: Enable/disable interrupt delivery
- **suspendThread bridge** (AN9-D / WS-RC R2.B): Lean ↔ Rust suspend
  with `with_interrupts_disabled` bracketing on the Rust side.
- **Syscall dispatch bridge** (AN9-F / WS-RC R2.B): Rust → Lean SVC
  dispatch routing into the verified `syscallEntryChecked`.

## Kernel-state IO.Ref (WS-RC R2.A)

The hardware SVC path is C-callable and therefore cannot thread
`SystemState` through its argument list the way the Lean simulation
path does.  Instead we keep the live kernel state in an `IO.Ref` that
the boot wrapper initialises and that every `@[export]` body reads on
entry / writes on exit.  Three alternatives were considered and
rejected:

1. **IO.Ref (chosen)** — single mutable cell, sequential SVC semantics
   on hardware (the Rust HAL serialises every SVC entry through
   `with_interrupts_disabled`), no per-syscall FFI overhead.
2. **Thread-local register-decoded snapshot** — rejected because it
   would multiply FFI symbols per syscall (one per register class) and
   force the Rust side to encode a typed-arg struct at every entry.
3. **Pure functional re-construction at every SVC entry** — rejected
   because it would force the Rust side to serialise the entire
   `SystemState` (object store, scheduler, CDT, …) at every SVC entry,
   making syscall cost unbounded in the object-store size.
-/

namespace SeLe4n.Platform.FFI

open SeLe4n
open SeLe4n.Kernel.Concurrency (bootCoreId)
open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Platform.Boot

/-- WS-RC R2.A: Provide a `Nonempty` witness for `LabelingContext` so an
    `IO.Ref LabelingContext` may be created at module load time via
    `initialize`.  We use `Nonempty` (not `Inhabited`) so the witness
    does NOT propagate as `(default : LabelingContext)` to downstream
    code that imports this module — preventing accidental use of the
    test labeling context as a "default" in contexts that should fail
    closed instead.  The witness value is `Kernel.testLabelingContext`,
    the same context used by `MainTraceHarness` and the dispatch test
    suite — it passes the `isInsecureDefaultContext` gate that
    `syscallEntryChecked` enforces. -/
instance : Nonempty LabelingContext := ⟨Kernel.testLabelingContext⟩

-- ============================================================================
-- AG7-A-iii: Timer FFI declarations
-- ============================================================================

/-- Read the ARM Generic Timer physical counter (CNTPCT_EL0).
    Returns the current 64-bit counter value (54 MHz on RPi5).
    Rust: `ffi_timer_read_counter` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_timer_read_counter"]
opaque ffiTimerReadCounter : BaseIO UInt64

/-- Reprogram the timer comparator for the next tick interval and
    increment the tick counter.
    Rust: `ffi_timer_reprogram` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_timer_reprogram"]
opaque ffiTimerReprogram : BaseIO Unit

/-- Get the current tick count (timer interrupts since boot).
    Rust: `ffi_timer_get_tick_count` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_timer_get_tick_count"]
opaque ffiTimerGetTickCount : BaseIO UInt64

-- ============================================================================
-- AG7-A-iii: GIC FFI declarations
-- ============================================================================

/-- Acknowledge a pending GIC interrupt (read GICC_IAR).
    Returns the INTID (bits [9:0]).
    Rust: `ffi_gic_acknowledge` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_gic_acknowledge"]
opaque ffiGicAcknowledge : BaseIO UInt32

/-- Signal end-of-interrupt to the GIC (write GICC_EOIR).
    Rust: `ffi_gic_eoi` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_gic_eoi"]
opaque ffiGicEoi : UInt32 → BaseIO Unit

/-- Check if an interrupt ID is spurious (INTID >= 1020).
    Rust: `ffi_gic_is_spurious` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_gic_is_spurious"]
opaque ffiGicIsSpurious : UInt32 → BaseIO Bool

-- ============================================================================
-- AG7-A-iii: TLB FFI declarations
-- ============================================================================

/-- Flush all TLB entries at EL1 (TLBI VMALLE1 + DSB ISH + ISB).
    Rust: `ffi_tlbi_all` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_tlbi_all"]
opaque ffiTlbiAll : BaseIO Unit

/-- Flush TLB entries by ASID at EL1 (TLBI ASIDE1 + DSB ISH + ISB).
    Rust: `ffi_tlbi_by_asid` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_tlbi_by_asid"]
opaque ffiTlbiByAsid : UInt16 → BaseIO Unit

/-- Flush TLB entries by virtual address + ASID (TLBI VAE1 + DSB ISH + ISB).
    Rust: `ffi_tlbi_by_vaddr` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_tlbi_by_vaddr"]
opaque ffiTlbiByVaddr : UInt16 → UInt64 → BaseIO Unit

-- ============================================================================
-- WS-SM SM1.E.4 — Sharing-domain-routed TLBI dispatcher FFI binding
-- ============================================================================
--
-- The Lean-side typed `Architecture.tlbiForSharing` wrapper encodes
-- a `(SharingDomain, TlbInvalidation)` pair into the (domainTag,
-- opTag, asid, vaddr) tuple expected by the Rust-side
-- `ffi_tlbi_for_sharing` dispatcher.
--
-- **Discriminant encoding** (mirrors `rust/sele4n-hal/src/ffi.rs`):
--
--   domainTag : UInt32   0 = Inner, 1 = Outer
--   opTag     : UInt32   0 = Vmalle1, 1 = Vae1, 2 = Aside1, 3 = Vale1
--   asid      : UInt16   16-bit ASID (RES0 for Vmalle1)
--   vaddr     : UInt64   page-aligned VA (RES0 for Vmalle1, Aside1)
--
-- The encoding is fixed: a future change requires the Rust dispatcher
-- and this declaration to be updated in lockstep, plus the
-- corresponding FFI ABI test in `tests/SmpFoundationsSuite.lean`.

/-- **WS-SM SM1.E.4**: Sharing-domain-routed TLBI dispatcher.
    Routes the (domainTag, opTag, asid, vaddr) tuple to one of the
    eight underlying IS/OS TLBI variants.

    Production callers should use the typed Lean-side wrapper in
    `SeLe4n.Kernel.Architecture` rather than calling this raw FFI
    directly — the typed wrapper exhaustively covers the
    `(SharingDomain, TlbInvalidation)` enumeration and prevents
    encoding errors at the call site.

    Rust: `ffi_tlbi_for_sharing` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_tlbi_for_sharing"]
opaque ffiTlbiForSharing :
    (domainTag : UInt32) → (opTag : UInt32) →
    (asid : UInt16) → (vaddr : UInt64) → BaseIO Unit

-- ============================================================================
-- WS-SM SM1.F.6 — SGI primitive FFI bindings
-- ============================================================================
--
-- The SGI primitives are inter-processor interrupt sends in the GIC's
-- INTID range [0, 16).  The kernel reserves the lowest five slots
-- (per `SeLe4n.Kernel.Concurrency.SgiKind`) for SMP coordination.
--
-- All three send variants emit `dsb ish` BEFORE writing GICD_SGIR per
-- SM1.F.8 / ARM ARM B2.7.5: prior kernel-state writes must be visible
-- on every IS-domain PE before the SGI fires on the receiver.
--
-- Lean callers should use the typed wrappers in a future
-- `SeLe4n.Kernel.Concurrency.Sgi` companion module (post-SM1.F that
-- builds on the `SgiKind` enum at SM0.H); the FFI declarations here
-- are the link-time bridge.

/-- **WS-SM SM1.F.6**: Send an SGI to one or more target CPU
    interfaces by explicit bitmask.

    `targetMask` — 8-bit bitmask of target CPU interfaces (bit i = CPU i).
    On RPi5 only bits 0..3 are meaningful.
    `intid` — SGI INTID (`0..15`).

    Panics on the Rust side if `intid >= 16`.  The Lean caller MUST
    constrain the intid to the SGI range (typically by passing
    `SgiKind.toIntid k |>.val |>.toUInt8` for a kernel-reserved
    SGI, which is structurally `< 16`).

    Rust: `ffi_send_sgi` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_send_sgi"]
opaque ffiSendSgi : (targetMask : UInt8) → (intid : UInt8) → BaseIO Unit

/-- **WS-SM SM1.F.6**: Send an SGI to the calling core only.

    `intid` — SGI INTID (`0..15`).  Useful for deferring work via an
    SGI without disturbing other cores.

    Rust: `ffi_send_sgi_to_self` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_send_sgi_to_self"]
opaque ffiSendSgiToSelf : (intid : UInt8) → BaseIO Unit

/-- **WS-SM SM1.F.6**: Send an SGI to all cores except the caller.

    `intid` — SGI INTID (`0..15`).  Most common SMP-coordination
    pattern: the caller has performed an action whose result every
    other core must observe (TLB shootdown, kernel-state quiesce,
    reschedule trigger).

    Rust: `ffi_send_sgi_to_all_but_self` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_send_sgi_to_all_but_self"]
opaque ffiSendSgiToAllButSelf : (intid : UInt8) → BaseIO Unit

-- ============================================================================
-- AG7-A-iii: MMIO FFI declarations
-- ============================================================================

/-- Read a 32-bit value from an MMIO address (volatile).
    Rust: `ffi_mmio_read32` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_mmio_read32"]
opaque ffiMmioRead32 : UInt64 → BaseIO UInt32

/-- Write a 32-bit value to an MMIO address (volatile).
    Rust: `ffi_mmio_write32` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_mmio_write32"]
opaque ffiMmioWrite32 : UInt64 → UInt32 → BaseIO Unit

/-- Read a 64-bit value from an MMIO address (volatile).
    Rust: `ffi_mmio_read64` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_mmio_read64"]
opaque ffiMmioRead64 : UInt64 → BaseIO UInt64

/-- Write a 64-bit value to an MMIO address (volatile).
    Rust: `ffi_mmio_write64` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_mmio_write64"]
opaque ffiMmioWrite64 : UInt64 → UInt64 → BaseIO Unit

-- ============================================================================
-- AG7-A-iii: UART FFI declarations
-- ============================================================================

/-- Transmit a single character on the debug UART (PL011).
    Rust: `ffi_uart_putc` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_uart_putc"]
opaque ffiUartPutc : UInt8 → BaseIO Unit

-- ============================================================================
-- AG7-A-iii: Interrupt FFI declarations
-- ============================================================================

/-- Disable all maskable interrupts. Returns saved DAIF for restoration.
    Rust: `ffi_disable_interrupts` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_disable_interrupts"]
opaque ffiDisableInterrupts : BaseIO UInt64

/-- Restore interrupt state from a previously saved DAIF value.
    Rust: `ffi_restore_interrupts` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_restore_interrupts"]
opaque ffiRestoreInterrupts : UInt64 → BaseIO Unit

/-- Enable IRQ delivery (clear PSTATE.I).
    Rust: `ffi_enable_interrupts` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_enable_interrupts"]
opaque ffiEnableInterrupts : BaseIO Unit

-- ============================================================================
-- WS-SM SM1.B.5 (closes SMP-M4): per-CPU core-id FFI declaration
-- ============================================================================

/-- **WS-SM SM1.B.5**: return the calling core's id, read from
    `TPIDR_EL1` on aarch64.

    On hardware the Rust side reads
    `per_cpu::current_core_id_from_tpidr()`, which dereferences the
    pointer stored in TPIDR_EL1 (set by `boot.rs::rust_boot_main` for
    the boot core and `boot.S::secondary_entry` for secondaries) and
    returns the `core_id` field of the resulting `PerCpuData` slot.

    **Range contract** (mirrors the Rust comment):
    `result.toNat < PlatformBinding.coreCount`.  The Lean-side
    `Concurrency.currentCoreId` wrapper re-checks this to recover a
    typed `Fin numCores`.

    Rust: `ffi_current_core_id` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_current_core_id"]
opaque ffiCurrentCoreId : BaseIO UInt64

-- ============================================================================
-- WS-SM SM1.I.3 — Per-core IDLE thread FFI declarations
-- ============================================================================

/-- **WS-SM SM1.I.3**: park the calling core on `wfe` waiting for an
    event or interrupt.

    On hardware the Rust side issues `wfe` (ARM ARM C6.2.353), which
    places the PE in a low-power state until any of: another core
    issues `sev`, an IRQ arrives, a debug exception fires, or a
    power-management event wakes the PE.  On host the stub returns
    immediately.

    **Production reachability**: at SM1.I.3 the Lean kernel does not
    yet emit calls to this primitive (per-core idle TCB state is SM5+
    work).  SM5 will wire the idle TCB body to this FFI symbol.

    Rust: `ffi_idle_wait` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_idle_wait"]
opaque ffiIdleWait : BaseIO Unit

/-- **WS-SM SM1.I.3**: bounded variant of `ffiIdleWait`.

    `maxTicks` — informational budget in `CNTPCT_EL0` counter ticks
    (54 MHz on RPi5, so 540 000 ticks = 10 ms; see
    `crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS`).  Returns elapsed ticks
    since the call began so the caller can detect "did we time out
    without seeing an event" via `elapsed >= maxTicks`.

    On host the stub returns 0 deterministically.

    Rust: `ffi_idle_wait_bounded` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_idle_wait_bounded"]
opaque ffiIdleWaitBounded : UInt64 → BaseIO UInt64

-- ============================================================================
-- WS-SM SM1.I.4 — Per-core stats FFI declarations
-- ============================================================================
--
-- Read accessors for the per-core `PerCpuStats` block.  All accessors
-- return 0 for out-of-range `coreId`.  The `record_*` writers are
-- not exposed via FFI because the production write path is the
-- Rust-side `handle_irq_per_core` / `handle_synchronous_exception`.

/-- **WS-SM SM1.I.4**: read a specific core's total IRQ count.

    Returns a `Relaxed` snapshot of `PerCpuStats.irq_count` for the
    named core.  Out-of-range `coreId` returns 0 (defensive — the
    production callers always pass `coreId < PlatformBinding.coreCount`).

    Rust: `ffi_per_core_irq_count` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_per_core_irq_count"]
opaque ffiPerCoreIrqCount : UInt64 → BaseIO UInt64

/-- **WS-SM SM1.I.4**: read a specific core's timer-tick count.

    Subset of `irq_count` covering only timer PPI (INTID 30).

    Rust: `ffi_per_core_timer_tick_count` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_per_core_timer_tick_count"]
opaque ffiPerCoreTimerTickCount : UInt64 → BaseIO UInt64

/-- **WS-SM SM1.I.4**: read a specific core's SGI count.

    Subset of `irq_count` covering only SGI INTIDs 0..15.

    Rust: `ffi_per_core_sgi_count` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_per_core_sgi_count"]
opaque ffiPerCoreSgiCount : UInt64 → BaseIO UInt64

/-- **WS-SM SM1.I.4**: read a specific core's syscall (SVC) count.

    Rust: `ffi_per_core_syscall_count` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_per_core_syscall_count"]
opaque ffiPerCoreSyscallCount : UInt64 → BaseIO UInt64

-- ============================================================================
-- WS-SM SM5.B.7 — Per-core context-switch FFI declarations
-- ============================================================================

/-- **WS-SM SM5.B.7**: record that core `coreId` is now running thread `tid`.

    The verified Lean kernel calls this after `switchToThreadOnCore`
    (`Scheduler/Operations/Selection.lean`) has computed the new per-core
    scheduler state, so the HAL's trap-return / dispatch path knows which
    thread to resume on this core.  Returns `0` on success, `1` on an
    out-of-range `coreId` (fail-closed — nothing is recorded).  A well-typed
    Lean caller passes `coreId < numCores`, so the `1` status is unreachable
    from the typed `Concurrency.switchToThreadHw` wrapper.

    Rust: `ffi_switch_to_thread` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_switch_to_thread"]
opaque ffiSwitchToThread : (tid : UInt64) → (coreId : UInt64) → BaseIO UInt64

/-- **WS-SM SM5.B.7**: read the per-core current-thread id recorded for
    `coreId` by the most recent `ffiSwitchToThread`.

    Returns the HAL sentinel (`u64::MAX`) for an out-of-range `coreId` or a
    core that has not had a switch recorded yet.

    Rust: `ffi_per_core_current_thread` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_per_core_current_thread"]
opaque ffiPerCoreCurrentThread : UInt64 → BaseIO UInt64

-- ============================================================================
-- WS-SM SM2.D — Verified-lock FFI declarations
-- ============================================================================
--
-- The Lean kernel reaches the verified TicketLock (`SeLe4n.Kernel.
-- Concurrency.Locks.TicketLock`) and RwLock (`SeLe4n.Kernel.Concurrency.
-- Locks.RwLock`) implementations through these `@[extern]` declarations.
-- Each resolves at link time to a corresponding `#[no_mangle] pub
-- extern "C"` function in `rust/sele4n-hal/src/ffi.rs`.
--
-- Handle encoding (SM2.D version):
--
--   handle : UInt64 — opaque pointer into a static lock pool.
--   At SM2.D, `handle = idx` for `idx ∈ [0, 4)` in each pool.
--   SM5 will extend the encoding for per-object locks via a high-bit
--   discriminator tag; the SM2.D-reserved low values remain
--   source-compatible.
--
-- Fail-closed contract: every helper panics on a malformed handle.
-- Well-formed Lean callers using the typed
-- `Kernel.Concurrency.LockBridge` wrappers cannot construct an invalid
-- handle because the smart constructors verify the bound at
-- elaboration time.

/-- **WS-SM SM2.D.1**: get a handle to a static TicketLock by pool
    index.  Panics on out-of-range index.

    Rust: `ffi_ticket_lock_static_handle` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_ticket_lock_static_handle"]
opaque ffiTicketLockStaticHandle : (idx : UInt64) → BaseIO UInt64

/-- **WS-SM SM2.D.1**: acquire the TicketLock identified by `handle`.

    Returns the captured ticket as `UInt64`.  Panics on malformed
    `handle`.

    The captured ticket is informational (for diagnostics / logging);
    the matching `ffiTicketLockRelease` does not require it.

    Rust: `ffi_ticket_lock_acquire` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_ticket_lock_acquire"]
opaque ffiTicketLockAcquire : (handle : UInt64) → BaseIO UInt64

/-- **WS-SM SM2.D.1**: release the TicketLock identified by `handle`.

    The caller MUST be the current holder.  Misuse (release without
    prior acquire, or double-release) triggers a `debug_assert!` in
    the underlying `TicketLock::release` on debug builds and is
    undefined behavior at the abstract level.

    Rust: `ffi_ticket_lock_release` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_ticket_lock_release"]
opaque ffiTicketLockRelease : (handle : UInt64) → BaseIO Unit

/-- **WS-SM SM2.D.1**: peek at the TicketLock's holder state.

    Returns a packed `UInt64`:
    - bits 63..32 = `next_ticket` (truncated to u32)
    - bits 31..0  = `serving`     (truncated to u32)

    Under the abstract wf invariant, `serving ≤ next_ticket` always.
    If the lock is unheld, `serving = next_ticket`.

    **NOT atomic with respect to other ops**: the snapshot may not
    correspond to any single point in time under concurrent acquires
    / releases.  Acceptable for diagnostic use; callers that need
    atomic state observation must hold the lock around the read.

    Rust: `ffi_ticket_lock_peek_holder` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_ticket_lock_peek_holder"]
opaque ffiTicketLockPeekHolder : (handle : UInt64) → BaseIO UInt64

/-- **WS-SM SM2.D.4**: read the per-slot TicketLock acquire counter.

    Returns a Relaxed snapshot of the total number of FFI
    `ffi_ticket_lock_acquire` calls for the slot identified by
    `handle`.  Used by the cross-core test (SM2.D.8) to verify FFI
    calls actually serialise.

    Rust: `ffi_ticket_lock_acquire_count` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_ticket_lock_acquire_count"]
opaque ffiTicketLockAcquireCount : (handle : UInt64) → BaseIO UInt64

/-- **WS-SM SM2.D.4**: read the per-slot TicketLock release counter.

    Rust: `ffi_ticket_lock_release_count` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_ticket_lock_release_count"]
opaque ffiTicketLockReleaseCount : (handle : UInt64) → BaseIO UInt64

/-- **WS-SM SM2.D.2**: get a handle to a static RwLock by pool index.
    Panics on out-of-range index.

    Rust: `ffi_rw_lock_static_handle` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_rw_lock_static_handle"]
opaque ffiRwLockStaticHandle : (idx : UInt64) → BaseIO UInt64

/-- **WS-SM SM2.D.2**: acquire a read lock on the RwLock identified by
    `handle`.  Panics on malformed `handle`.

    Rust: `ffi_rw_lock_acquire_read` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_rw_lock_acquire_read"]
opaque ffiRwLockAcquireRead : (handle : UInt64) → BaseIO Unit

/-- **WS-SM SM2.D.2**: release a read lock on the RwLock identified by
    `handle`.

    Rust: `ffi_rw_lock_release_read` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_rw_lock_release_read"]
opaque ffiRwLockReleaseRead : (handle : UInt64) → BaseIO Unit

/-- **WS-SM SM2.D.2**: acquire a write lock on the RwLock identified
    by `handle`.

    Rust: `ffi_rw_lock_acquire_write` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_rw_lock_acquire_write"]
opaque ffiRwLockAcquireWrite : (handle : UInt64) → BaseIO Unit

/-- **WS-SM SM2.D.2**: release a write lock on the RwLock identified
    by `handle`.

    Rust: `ffi_rw_lock_release_write` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_rw_lock_release_write"]
opaque ffiRwLockReleaseWrite : (handle : UInt64) → BaseIO Unit

/-- **WS-SM SM2.D.2**: snapshot of the RwLock state.

    Returns a packed `UInt64` matching the abstract spec's
    `encodeRwLock` / `RwLockEncoded` shape:
    - bit 63 = writer-held flag
    - bits 0..62 = reader count

    See `SeLe4n.Kernel.Concurrency.RwLockEncoded` (SM2.C.16) for the
    abstract refinement target.  **NOT atomic with respect to other
    ops**; same caveat as `ffiTicketLockPeekHolder`.

    Rust: `ffi_rw_lock_snapshot` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_rw_lock_snapshot"]
opaque ffiRwLockSnapshot : (handle : UInt64) → BaseIO UInt64

/-- **WS-SM SM2.D.4**: read the per-slot RwLock acquire-read counter.

    Rust: `ffi_rw_lock_acquire_read_count` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_rw_lock_acquire_read_count"]
opaque ffiRwLockAcquireReadCount : (handle : UInt64) → BaseIO UInt64

/-- **WS-SM SM2.D.4**: read the per-slot RwLock release-read counter.

    Rust: `ffi_rw_lock_release_read_count` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_rw_lock_release_read_count"]
opaque ffiRwLockReleaseReadCount : (handle : UInt64) → BaseIO UInt64

/-- **WS-SM SM2.D.4**: read the per-slot RwLock acquire-write counter.

    Rust: `ffi_rw_lock_acquire_write_count` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_rw_lock_acquire_write_count"]
opaque ffiRwLockAcquireWriteCount : (handle : UInt64) → BaseIO UInt64

/-- **WS-SM SM2.D.4**: read the per-slot RwLock release-write counter.

    Rust: `ffi_rw_lock_release_write_count` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_rw_lock_release_write_count"]
opaque ffiRwLockReleaseWriteCount : (handle : UInt64) → BaseIO UInt64

-- ============================================================================
-- WS-RC R2 — Hardware-mode kernel state + SVC bridge infrastructure
-- ============================================================================
--
-- This section provides the substantive routing the AN9-D / AN9-F stubs
-- below use to reach the verified `suspendThread` and `syscallEntryChecked`
-- entry points.  See the file header for the design rationale.
--
-- Subsections:
--   R2.B.0  — KernelError → UInt32 mapping (mirrors `rust/sele4n-types/src/error.rs`)
--   R2.B.0  — encodeError / encodeOk / decodeFfi (return-value encoding)
--   R2.A.1  — `kernelStateRef`, `kernelLabelingContextRef` (IO.Refs)
--   R2.A.2  — `initialiseKernelState`, `getKernelState`, `updateKernelState`
--   R2.A.3  — `bootAndInitialiseFromPlatform` (boot wrapper)
--   R2.B.1  — `writeFfiRegistersToTcb`, `readReturnValue` (helpers)
--   R2.B.1  — `syscallDispatchFromAbi` (typed-ABI entry point)

/-- WS-RC R2.B.0: Map a `KernelError` to its `u32` FFI discriminant.

The discriminants 0..53 mirror `rust/sele4n-types/src/error.rs` exactly.
A regression that adds a Lean variant without updating the Rust enum (or
vice versa) is caught by `tests/SyscallDispatchSuite.lean`'s round-trip
check (`KernelError.toUInt32` ∘ `SyscallId.toNat` matches the documented
table in `rust/sele4n-types/src/error.rs`).

Discriminant 17 (`notImplemented`) is the historical "stub" return; per
WS-RC R2 the FFI no longer emits it from the dispatch path — every error
now corresponds to a substantive kernel rejection. -/
def KernelError.toUInt32 : KernelError → UInt32
  | .invalidCapability             => 0
  | .objectNotFound                => 1
  | .illegalState                  => 2
  | .illegalAuthority              => 3
  | .policyDenied                  => 4
  | .dependencyViolation           => 5
  | .schedulerInvariantViolation   => 6
  | .endpointStateMismatch         => 7
  | .endpointQueueEmpty            => 8
  | .asidNotBound                  => 9
  | .vspaceRootInvalid             => 10
  | .mappingConflict               => 11
  | .translationFault              => 12
  | .flowDenied                    => 13
  | .declassificationDenied        => 14
  | .alreadyWaiting                => 15
  | .cyclicDependency              => 16
  | .notImplemented                => 17
  | .targetSlotOccupied            => 18
  | .replyCapInvalid               => 19
  | .untypedRegionExhausted        => 20
  | .untypedTypeMismatch           => 21
  | .untypedDeviceRestriction      => 22
  | .untypedAllocSizeTooSmall      => 23
  | .childIdSelfOverwrite          => 24
  | .childIdCollision              => 25
  | .addressOutOfBounds            => 26
  | .ipcMessageTooLarge            => 27
  | .ipcMessageTooManyCaps         => 28
  | .backingObjectMissing          => 29
  | .invalidRegister               => 30
  | .invalidSyscallNumber          => 31
  | .invalidMessageInfo            => 32
  | .invalidTypeTag                => 33
  | .resourceExhausted             => 34
  | .invalidCapPtr                 => 35
  | .objectStoreCapacityExceeded   => 36
  | .allocationMisaligned          => 37
  | .revocationRequired            => 38
  | .invalidArgument               => 39
  | .mmioUnaligned                 => 40
  | .invalidSyscallArgument        => 41
  | .ipcTimeout                    => 42
  | .alignmentError                => 43
  | .vmFault                       => 44
  | .userException                 => 45
  | .hardwareFault                 => 46
  | .notSupported                  => 47
  | .invalidIrq                    => 48
  | .invalidObjectType             => 49
  | .nullCapability                => 50
  | .partialResolution             => 51
  | .missingSchedContext           => 52
  | .threadOnDifferentCore         => 53

/-- WS-RC R2.B.0: Encode a `KernelError` into the FFI return contract.

Sets bit 63 (the error flag) and packs the discriminant into the low 32
bits.  The Rust dispatcher (`rust/sele4n-hal/src/svc_dispatch.rs::dispatch_svc`)
extracts both: `(raw >> 63) & 1` checks the flag, `raw as u32` extracts
the discriminant. -/
@[inline] def encodeError (e : KernelError) : UInt64 :=
  ((1 : UInt64) <<< 63) ||| (KernelError.toUInt32 e).toUInt64

/-- WS-RC R2.B.0: Encode a successful return value.

Bit 63 must be `0` (clear error flag); the low 63 bits carry the
return value.  Most syscalls return `Unit` and the FFI emits 0; some
syscalls (e.g., `cspaceMint` returning the new slot index) put the
result in the current thread's `x0` register, from which the FFI
caller reads it. -/
@[inline] def encodeOk (v : UInt64) : UInt64 :=
  -- Mask bit 63 to ensure success values cannot collide with the error
  -- flag.  Practical syscalls return small values; this only matters
  -- as a defensive correctness gate.
  v &&& 0x7FFFFFFFFFFFFFFF

/-- WS-RC R2.B.0: Round-trip of `encodeError` — every `KernelError`
    variant emits a value whose high bit is set.

The OR with `(1 <<< 63)` forces bit 63 to `1` regardless of the low
bits contributed by `KernelError.toUInt32`; case-splitting on `e`
reduces every variant to a concrete `UInt64` whose bit 63 is `1` by
direct computation.  This is the structural witness that the Rust
side's error-flag check (`(raw >> 63) & 1 == 1`) succeeds for every
encoded error. -/
theorem encodeError_high_bit_set (e : KernelError) :
    (encodeError e >>> 63) &&& 1 = 1 := by
  unfold encodeError KernelError.toUInt32
  cases e <;> decide

/-- WS-RC R2.B.0: Round-trip of `encodeOk` — the encoded value's
    bit 63 is clear for every `UInt64` argument.

The mask `0x7FFFFFFFFFFFFFFF` zeroes bit 63 unconditionally; the
underlying `UInt64` AND/SHR semantics propagate via `BitVec`.  This
is the structural witness that the Rust side's success-vs-error
disambiguation (`(raw >> 63) & 1 == 0`) succeeds for every encoded
success value, complementing `encodeError_high_bit_set`.

The proof reduces to a closed BitVec proposition that `decide`
solves via the `UInt64.toBitVec` lemmas. -/
theorem encodeOk_high_bit_clear (v : UInt64) :
    (encodeOk v >>> 63) &&& 1 = 0 := by
  unfold encodeOk
  -- Reduce to BitVec arithmetic via UInt64.toBitVec; the mask
  -- `0x7FFF...FF` clears bit 63 of every input, so the SHR(63) AND 1
  -- result is always 0.
  apply UInt64.eq_of_toBitVec_eq
  bv_decide

/-- WS-RC R2.A.1: The kernel-state holder used by the `@[export]`
    bodies on hardware.

We use a top-level `IO.Ref` rather than passing state through the FFI
argument list because (a) the SVC entry is C-callable and ABI-fixed,
(b) the Rust HAL serialises every entry through `with_interrupts_disabled`
so the IO.Ref needs no atomicity, and (c) the alternative — re-encoding
the entire `SystemState` per syscall — would cost O(object-store) at
every entry.

The initial value is `default : SystemState`; the boot wrapper
(`bootAndInitialiseFromPlatform`) overwrites it with the post-boot
state before the first syscall.  Tests exercising this path
(`tests/SyscallDispatchSuite.lean`) initialise it explicitly via
`initialiseKernelState`. -/
initialize kernelStateRef : IO.Ref SystemState ← IO.mkRef (default : SystemState)

/-- WS-RC R2.A.1: The deployment's labeling context.

The labeling context is a deployment-time configuration that
`syscallEntryChecked` consults to reject the insecure default
(`isInsecureDefaultContext` returns true for `defaultLabelingContext`).
Initialised to `Kernel.testLabelingContext` so the simulation
(non-hardware) test path passes the insecure-default gate; the boot
wrapper overrides it with the production policy on hardware. -/
initialize kernelLabelingContextRef : IO.Ref LabelingContext ←
  IO.mkRef Kernel.testLabelingContext

/-- WS-RC R2.A.2: Install a fresh `SystemState` into `kernelStateRef`.

Called once by the boot wrapper after `bootFromPlatformChecked`
returns `.ok`.  Tests call this directly to seed a known initial
state for negative checks (e.g., empty scheduler, unmapped IPC
buffer). -/
def initialiseKernelState (st : SystemState) : BaseIO Unit :=
  kernelStateRef.set st

/-- WS-RC R2.A.2: Read the current kernel state.

Used by every `@[export]` body on entry to obtain the live
`SystemState` before invoking the verified Lean handler. -/
def getKernelState : BaseIO SystemState :=
  kernelStateRef.get

/-- WS-RC R2.A.2: Apply a state-transforming function to the current
    kernel state. -/
def updateKernelState (f : SystemState → SystemState) : BaseIO Unit :=
  kernelStateRef.modify f

/-- WS-SM SM5.I: atomic read-modify-write of the kernel state, returning a
    by-product computed alongside the new state.  `f st = (a, st')` installs `st'`
    and returns `a`, all under a single `IO.Ref.modifyGet` so no concurrent writer
    can interleave between the read and the write (the per-core timer-tick driver
    uses this to commit `timerTickOnCore`'s new state and recover its cross-core
    SGIs in one step). -/
def modifyGetKernelState {α : Type} (f : SystemState → α × SystemState) : BaseIO α :=
  kernelStateRef.modifyGet f

/-- WS-RC R2.A.2: Install a fresh `LabelingContext` into the
    deployment policy slot.  The boot wrapper accepts a labeling
    context as an optional argument; tests use the same entry point
    to install the test or production policy explicitly. -/
def initialiseKernelLabelingContext (ctx : LabelingContext) : BaseIO Unit :=
  kernelLabelingContextRef.set ctx

/-- WS-RC R2.A.2: Read the deployment's labeling context. -/
def getKernelLabelingContext : BaseIO LabelingContext :=
  kernelLabelingContextRef.get

/-- WS-RC R2.A.3: Boot wrapper that runs `bootFromPlatformChecked`,
    installs the resulting `SystemState` into `kernelStateRef`, and
    optionally installs a labeling context.

On a hardware build the Rust HAL's kernel-init path calls this
function exactly once after low-level (assembly + Rust) init; the
returned `SystemState` is then live in `kernelStateRef` for every
subsequent SVC entry.  On a simulation build the function is a no-op
beyond what `bootFromPlatformChecked` already does — `MainTraceHarness`
keeps using `bootFromPlatformChecked` directly because every test path
threads state explicitly.

Returns the post-boot state on success or the boot error string on
failure (the same shape as `bootFromPlatformChecked`).  The IO.Ref is
NOT updated on the failure path — callers can detect the failure
explicitly without seeing partial state. -/
def bootAndInitialiseFromPlatform
    (config : PlatformConfig)
    (ctx : Option LabelingContext := none) :
    BaseIO (Except String SystemState) := do
  match bootFromPlatformChecked config with
  | Except.error e => pure (Except.error e)
  | Except.ok ist =>
    let st := ist.state
    initialiseKernelState st
    match ctx with
    | none      => pure ()
    | some lctx => initialiseKernelLabelingContext lctx
    pure (Except.ok st)

/-- WS-RC R2.B.1 helper: Write the FFI-passed register values into the
    given thread's TCB register file.

Mirrors what the ARM64 trap handler does on hardware: at SVC entry the
user's x0..x5 and x7 (syscall number) are spilled into the current
thread's saved register context.  The `decodeSyscallArgsFromState`
function (called downstream by `syscallEntryChecked`) reads from this
register file via `readReg layout.capPtrReg`, etc.

The FFI also passes a separate `msgInfo` parameter for ABI parity with
the Rust side, where `args.msg_info == args.msg_regs[1] == frame.x1()`
(see `rust/sele4n-hal/src/svc_dispatch.rs::SyscallArgs::from_trap_frame`).
We do **not** write `msgInfo` to the register file separately because
`x1` already populates the `layout.msgInfoReg = ⟨1⟩` slot that
`decodeMsgInfo` reads — writing both would be a redundant overwrite,
and the resulting `msgInfo` decoded by `syscallEntryChecked` is
extracted from `x1`'s bit pattern via `MessageInfo.decode`.  The
`msgInfo` parameter remains in `syscallDispatchFromAbi`'s signature
for FFI ABI parity but is not consulted inside this helper.

If the target object is not a TCB (or the lookup fails) the state is
returned unchanged — `syscallEntryChecked` will surface the error
(`.illegalState` or `.objectNotFound`) on the very next step. -/
def writeFfiRegistersToTcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (syscallId : UInt32)
    (x0 x1 x2 x3 x4 x5 : UInt64) : SystemState :=
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
      let layout := SeLe4n.arm64DefaultLayout
      let rf := tcb.registerContext
      -- x0 → capPtrReg (= ⟨0⟩); x1 → msgInfoReg (= ⟨1⟩) — `decodeMsgInfo`
      -- decodes the msgInfo from this slot via `MessageInfo.decode`.
      let rf := writeReg rf layout.capPtrReg     ⟨x0.toNat⟩
      let rf := writeReg rf layout.msgInfoReg    ⟨x1.toNat⟩
      let rf := writeReg rf ⟨2⟩                  ⟨x2.toNat⟩
      let rf := writeReg rf ⟨3⟩                  ⟨x3.toNat⟩
      let rf := writeReg rf ⟨4⟩                  ⟨x4.toNat⟩
      let rf := writeReg rf ⟨5⟩                  ⟨x5.toNat⟩
      let rf := writeReg rf layout.syscallNumReg ⟨syscallId.toNat⟩
      let tcb' := { tcb with registerContext := rf }
      { st with objects := st.objects.insert tid.toObjId (.tcb tcb') }
  | _ => st

/-- WS-RC R2.B.1 helper: Read the syscall return value from a thread's
    `x0` register, per AAPCS64.

Reads `tcb.registerContext.gpr ⟨0⟩` (the AAPCS64 / seL4 return-value
slot) from the post-syscall TCB and converts to a `UInt64`.  The
conversion truncates to the low 64 bits (the abstract model uses
`Nat` but the hardware register is 64-bit).

**Semantic note**: per the seL4 ABI, `x0` holds the syscall return
value on exit (e.g., a badge for `notificationWait`, a slot for
`cspaceMint`, or `0` for `Unit`-returning syscalls).  The verified
Lean syscall handlers that produce a return value are expected to
write it to the current thread's `x0` before returning.  Handlers
that return `Unit` (the majority) leave `x0` unchanged; in our
post-WS-RC R2 dispatch path, `x0` post-syscall therefore equals the
caller's own pre-syscall `x0` (since `writeFfiRegistersToTcb`
populates `pos[0]` with the FFI-passed `x0` argument before
`syscallEntryChecked` is invoked).  This is the documented current
behaviour — full seL4-ABI x0 compliance for value-returning syscalls
is tracked as a future refinement when each verified handler's
return-value semantics are formalised.

If the target object is not a TCB (or the lookup fails) the function
returns `0` — `syscallEntryChecked` should never produce a `.ok`
result with such a state, so the `0` arm is a totality witness, not
a behavioural shortcut. -/
def readReturnValue (st : SystemState) (tid : SeLe4n.ThreadId) : UInt64 :=
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
      let v := tcb.registerContext.gpr ⟨0⟩
      -- Take low 64 bits explicitly; the model uses `Nat` but the FFI
      -- contract is 64-bit.  Values ≥ 2^64 cannot be produced by
      -- well-typed verified handlers because `RegValue` is constructed
      -- from `UInt64.toNat` everywhere it's written.
      v.toNat.toUInt64
  | _ => 0

/-- WS-RC R2.B.1: Pure typed-ABI entry point invoked by the
    `syscall_dispatch_inner` `@[export]` wrapper.

The function name appears verbatim in `rust/sele4n-hal/src/svc_dispatch.rs:308`
as documentation for what the C-callable `syscall_dispatch_inner` symbol
ultimately routes into.  After WS-RC R2.B that documentation is
substantively true: the symbol's body is the BaseIO wrapper around
this function.

Pipeline:
  1. Verify the FFI ABI invariant `msgInfo == x1` (both come from
     `frame.x1()` on the Rust side per
     `rust/sele4n-hal/src/svc_dispatch.rs::SyscallArgs::from_trap_frame`).
     A mismatch indicates a malformed FFI call and is rejected with
     `.invalidSyscallArgument`.
  2. Look up `(st.scheduler.currentOnCore bootCoreId)` (must be `some` on a real syscall).
  3. Spill the FFI register values into the current thread's TCB
     `registerContext` (matches the ARM64 trap handler's spill).
  4. Invoke `syscallEntryChecked` with the deployment's labeling
     context and the canonical `arm64DefaultLayout`.
  5. Encode the result as `UInt64`: `encodeOk x0` on success,
     `encodeError ke` on failure.

`ipcBufferAddr` is passed for parity with the seL4 ABI; the verified
kernel reads the IPC buffer from `tcb.ipcBuffer` (set by
`tcbSetIPCBuffer`) rather than from this argument, so it is unused
inside the dispatch.  A future refinement may cross-validate the two
when telemetry is added. -/
def syscallDispatchFromAbi
    (ctx : LabelingContext)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 : UInt64)
    (_ipcBufferAddr : UInt64) : Kernel UInt64 :=
  fun st =>
    -- ABI consistency check: the Rust caller guarantees
    -- `msg_info == msg_regs[1] == frame.x1()` when constructing the
    -- `SyscallArgs` struct.  If the Lean side observes a mismatch,
    -- the FFI boundary has been violated and we reject before
    -- touching kernel state.
    if msgInfo != x1 then
      .ok (encodeError .invalidSyscallArgument, st)
    else
      match (st.scheduler.currentOnCore bootCoreId) with
      | none => .ok (encodeError .illegalState, st)
      | some tid =>
        let stRegs := writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5
        let layout := SeLe4n.arm64DefaultLayout
        match syscallEntryChecked ctx layout 32 stRegs with
        | .error ke => .ok (encodeError ke, stRegs)
        | .ok ((), st') => .ok (encodeOk (readReturnValue st' tid), st')

-- ============================================================================
-- AN9-D (DEF-C-M04): suspendThread atomicity bracket
-- ============================================================================

/-- AN9-D (DEF-C-M04): Lean → Rust direction.  Calls the
    `sele4n_suspend_thread` Rust wrapper that brackets the inner Lean
    dispatch with `with_interrupts_disabled`.

    Used when a Lean module invoking `suspendThread` from a path that
    must enforce hardware atomicity (i.e., not the abstract
    sequential model) wants to ensure the FFI bracket is in place.

    See `rust/sele4n-hal/src/ffi.rs::sele4n_suspend_thread`. -/
@[extern "sele4n_suspend_thread"]
opaque ffiSuspendThread : UInt64 → BaseIO UInt32

/-- AN9-D inner — Rust → Lean direction.  Exported so the Rust
    `sele4n_suspend_thread` wrapper can call back into the Lean
    suspend dispatch (after `with_interrupts_disabled` is set up).

    `@[export]` instructs the Lean compiler to emit a C-callable
    `suspend_thread_inner` symbol; the Rust side declares
    `extern "C" { fn suspend_thread_inner(...) -> u32; }` in
    `rust/sele4n-hal/src/ffi.rs`.

    Returns a `KernelError` discriminant; `0` means success (matching
    the `KernelError::Ok` slot reserved at AK4-A).

    **WS-RC R2.B (substantive)**: this body now reads the live
    `SystemState` from `kernelStateRef`, calls the verified
    `Kernel.Lifecycle.Suspend.suspendThread` handler with a
    type-checked `ValidThreadId`, writes the post-state back to the
    ref, and returns the encoded result.

    Failure modes:
    - `tid` corresponds to `ThreadId.sentinel` (the reserved value):
      reject with `.invalidArgument` (`KernelError.toUInt32 = 39`)
      without invoking `suspendThread` — the type system would
      otherwise refuse a `ValidThreadId` argument.
    - `suspendThread` returns `.error e`: forward `e`'s discriminant
      and leave `kernelStateRef` unchanged.
    - `suspendThread` returns `.ok st'`: install `st'` as the new
      kernel state and return `0` (`KernelError::Ok`-equivalent slot). -/
@[export suspend_thread_inner]
def suspendThreadInner (tid : UInt64) : BaseIO UInt32 := do
  let st ← getKernelState
  let threadId := SeLe4n.ThreadId.ofNat tid.toNat
  match threadId.toValid? with
  | none =>
      -- Sentinel rejected at the FFI boundary; matches the
      -- `ValidThreadId` discipline at the verified handler's
      -- signature.
      pure (KernelError.toUInt32 .invalidArgument)
  | some vtid =>
      match suspendThread st vtid with
      | Except.ok st' =>
          initialiseKernelState st'
          pure 0
      | Except.error e =>
          pure (KernelError.toUInt32 e)

-- ============================================================================
-- AN9-F (DEF-R-HAL-L14): SVC dispatch entry — Rust → Lean direction
-- ============================================================================

/-- AN9-F: Lean-side SVC dispatch routine called BY Rust through the
    `syscall_dispatch_inner` `extern "C"` symbol.  This is the
    Rust-→-Lean direction (opposite of every other declaration in
    this module): `@[export]` instructs the Lean compiler to emit a
    C-callable wrapper named `syscall_dispatch_inner` that resolves
    the Rust-side `extern "C" { fn syscall_dispatch_inner(...) }`
    declaration in `rust/sele4n-hal/src/svc_dispatch.rs`.

    Encoding of the return value (matching
    `rust/sele4n-hal/src/svc_dispatch.rs::dispatch_svc`):
    - bit 63 = 1  → low 32 bits = `KernelError` discriminant
    - bit 63 = 0  → low 63 bits = success return value (typically the
      callee-saved `x0` of the post-syscall TCB)

    **WS-RC R2.B (substantive)**: this body is now a thin BaseIO
    wrapper around the pure `syscallDispatchFromAbi` function.  It:

    1. Reads the live `SystemState` and `LabelingContext` from the
       kernel-state IO.Refs.
    2. Calls `syscallDispatchFromAbi` with the FFI register values.
    3. Writes the post-state back to `kernelStateRef`.
    4. Returns the encoded `UInt64` result.

    The "encoded as `UInt64`" contract makes the function total: the
    Lean side never raises an exception across the FFI boundary;
    every kernel rejection becomes an error-flagged `UInt64` value
    that the Rust caller decodes back into a `Result`. -/
@[export syscall_dispatch_inner]
def syscallDispatchInner
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 : UInt64)
    (ipcBufferAddr : UInt64) : BaseIO UInt64 := do
  let st  ← getKernelState
  let ctx ← getKernelLabelingContext
  match syscallDispatchFromAbi ctx syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr st with
  | Except.ok (encoded, st') =>
      initialiseKernelState st'
      pure encoded
  | Except.error e =>
      -- syscallDispatchFromAbi never returns `.error` — every kernel
      -- rejection is encoded into the success path with bit 63 set.
      -- This branch is therefore vacuous, but we discharge it
      -- defensively rather than relying on a `match`-exhaustiveness
      -- claim that future refactors might invalidate.
      pure (encodeError e)

-- ============================================================================
-- AN9-A (DEF-A-M04): TLB+Cache composition witnesses
-- ============================================================================

/-- AN9-A.1: TLB+Cache composition witness — clean a page-table page
    range followed by `dsb ish` so the writeback completes before any
    subsequent operation observes the page-table state.

    Rust: `cache::clean_pagetable_range` in `sele4n-hal/src/cache.rs`. -/
@[extern "cache_clean_pagetable_range"]
opaque ffiCacheCleanPagetableRange : UInt64 → UInt64 → BaseIO Unit

/-- AN9-A.1: I-cache invalidation witness — drop every I-cache line so
    subsequent instruction fetches re-read from coherent memory.

    Rust: `cache::ic_iallu` in `sele4n-hal/src/cache.rs`. -/
@[extern "cache_ic_iallu"]
opaque ffiIcIallu : BaseIO Unit

-- ============================================================================
-- WS-RC R2.B.5 — Correctness theorems for the syscall-dispatch bridge
-- ============================================================================

/-- WS-RC R2.B.5: The pure typed-ABI entry point never returns
    `Except.error` — every kernel rejection is encoded as a
    success-shaped `(encodedUInt64, state)` pair with bit 63 of the
    encoding set.  This is the structural witness that the FFI-side
    `syscallDispatchInner` BaseIO wrapper's `Except.error` arm is
    vacuous.

The proof unfolds `syscallDispatchFromAbi` and case-splits on the
scheduler's `current` slot and on the `syscallEntryChecked` result;
every branch produces an `.ok` value. -/
theorem syscallDispatchFromAbi_total
    (ctx : LabelingContext)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr : UInt64)
    (st : SystemState) :
    ∃ (encoded : UInt64) (st' : SystemState),
      syscallDispatchFromAbi ctx syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr st
        = Except.ok (encoded, st') := by
  unfold syscallDispatchFromAbi
  -- The function first checks the ABI invariant `msgInfo == x1`,
  -- then case-splits on `(st.scheduler.currentOnCore bootCoreId)`, then on the
  -- `syscallEntryChecked` result.  Every branch produces `.ok`.
  by_cases hMsg : msgInfo != x1
  · -- ABI mismatch path: returns `.ok (encodeError .invalidSyscallArgument, st)`.
    exact ⟨encodeError .invalidSyscallArgument, st, by simp [hMsg]⟩
  · -- ABI consistency holds: drive the if-then-else into the else branch
    -- using `hMsg` so the goal exposes the next match.
    cases (st.scheduler.currentOnCore bootCoreId) with
    | none =>
        exact ⟨encodeError .illegalState, st, by simp [hMsg]⟩
    | some tid =>
        cases hSyscall : syscallEntryChecked ctx SeLe4n.arm64DefaultLayout 32
                (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) with
        | error ke =>
            exact ⟨encodeError ke,
                   writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5,
                   by simp [hMsg, hSyscall]⟩
        | ok r =>
            obtain ⟨_, st'⟩ := r
            exact ⟨encodeOk (readReturnValue st' tid), st',
                   by simp [hMsg, hSyscall]⟩

/-- WS-RC R2.B.5: When `syscallEntryChecked` succeeds on the
    register-spilled state, `syscallDispatchFromAbi` returns the
    success-encoded `(encodeOk (readReturnValue st' tid), st')` pair
    where `st'` is the post-syscall state.

This is the substantive forward direction of the
`syscallDispatchFromAbi_ok_iff_syscallEntryChecked_ok` theorem
named in the WS-RC R2 plan.  Together with the `total` theorem
above, it pins the bridge's behaviour: no bypass, no shortcut,
the verified `syscallEntryChecked` is the sole source of `.ok`
results. -/
theorem syscallDispatchFromAbi_ok_of_syscallEntryChecked_ok
    (ctx : LabelingContext)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore bootCoreId) = some tid)
    (hSyscall :
      syscallEntryChecked ctx SeLe4n.arm64DefaultLayout 32
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
        = Except.ok ((), st')) :
    syscallDispatchFromAbi ctx syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr st
      = Except.ok (encodeOk (readReturnValue st' tid), st') := by
  unfold syscallDispatchFromAbi
  simp [hMsg, hCur, hSyscall]

/-- WS-RC R2.B.5: When `syscallEntryChecked` rejects on the
    register-spilled state, `syscallDispatchFromAbi` propagates the
    error via `encodeError` while preserving the post-spill
    `SystemState` (so the trap-handler-spilled registers are visible
    to any subsequent inspection of the kernel state). -/
theorem syscallDispatchFromAbi_error_of_syscallEntryChecked_error
    (ctx : LabelingContext)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore bootCoreId) = some tid)
    (hSyscall :
      syscallEntryChecked ctx SeLe4n.arm64DefaultLayout 32
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
        = Except.error ke) :
    syscallDispatchFromAbi ctx syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr st
      = Except.ok (encodeError ke,
                   writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
  unfold syscallDispatchFromAbi
  simp [hMsg, hCur, hSyscall]

/-- WS-RC R2.B.5: When the scheduler has no current thread, the FFI
    surfaces `.illegalState` without invoking `syscallEntryChecked`.

This is the FFI's defence against being called outside a syscall
context (e.g., during early boot before the scheduler has elected a
thread).  No state is mutated. -/
theorem syscallDispatchFromAbi_illegalState_when_no_current
    (ctx : LabelingContext)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr : UInt64)
    (st : SystemState)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore bootCoreId) = none) :
    syscallDispatchFromAbi ctx syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr st
      = Except.ok (encodeError .illegalState, st) := by
  unfold syscallDispatchFromAbi
  simp [hMsg, hCur]

/-- WS-RC R2.B.5: When the FFI ABI invariant `msgInfo == x1` is
    violated, the dispatcher rejects with `.invalidSyscallArgument`
    without touching kernel state.

This is the structural witness that ABI inconsistencies are detected
and rejected at the FFI boundary before any verified kernel handler
is invoked.  The ABI invariant holds by construction on the Rust
side (see `SyscallArgs::from_trap_frame`); a violation indicates
either a malformed caller or memory corruption — either way, the
safe response is to refuse the syscall. -/
theorem syscallDispatchFromAbi_abiMismatch_rejected
    (ctx : LabelingContext)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr : UInt64)
    (st : SystemState)
    (hMsg : msgInfo ≠ x1) :
    syscallDispatchFromAbi ctx syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr st
      = Except.ok (encodeError .invalidSyscallArgument, st) := by
  unfold syscallDispatchFromAbi
  -- `msgInfo ≠ x1` ⟹ `msgInfo != x1 = true` ⟹ the if-branch is taken.
  have : (msgInfo != x1) = true := by
    simp [bne_iff_ne, hMsg]
  simp [this]

/-- WS-RC R2.B.5: `writeFfiRegistersToTcb` reduces to the original
    state when the target object is not a TCB (or absent).  The
    `syscallEntryChecked` path then immediately surfaces
    `.objectNotFound` or `.illegalState` per its own preconditions.

The proof is a definitional unfolding — the `match` arm for
non-TCB / missing objects returns `st` unchanged. -/
theorem writeFfiRegistersToTcb_id_when_not_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (syscallId : UInt32)
    (x0 x1 x2 x3 x4 x5 : UInt64)
    (hNotTcb : ∀ tcb : TCB, st.objects[tid.toObjId]? ≠ some (.tcb tcb)) :
    writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 = st := by
  unfold writeFfiRegistersToTcb
  cases h : st.objects[tid.toObjId]? with
  | none => rfl
  | some obj =>
    cases obj with
    | tcb tcb =>
      exact absurd h (hNotTcb tcb)
    | endpoint _ => rfl
    | notification _ => rfl
    | cnode _ => rfl
    | vspaceRoot _ => rfl
    | untyped _ => rfl
    | schedContext _ => rfl

/-- WS-RC R2.B.5: `readReturnValue` is total — it reads `0` whenever
    the target object is not a TCB (or absent).  Used by callers that
    need to reason about the post-error encoded UInt64 without having
    to case-split on TCB presence. -/
theorem readReturnValue_zero_when_not_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNotTcb : ∀ tcb : TCB, st.objects[tid.toObjId]? ≠ some (.tcb tcb)) :
    readReturnValue st tid = 0 := by
  unfold readReturnValue
  cases h : st.objects[tid.toObjId]? with
  | none => rfl
  | some obj =>
    cases obj with
    | tcb tcb =>
      exact absurd h (hNotTcb tcb)
    | endpoint _ => rfl
    | notification _ => rfl
    | cnode _ => rfl
    | vspaceRoot _ => rfl
    | untyped _ => rfl
    | schedContext _ => rfl

end SeLe4n.Platform.FFI
