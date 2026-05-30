-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM5+ (SM1.B.5 typed FFI wrapper; consumed
-- once per-core scheduler state lands)
-- WS-SM SM1.B.5 (closes SMP-M4): typed wrapper for the
-- `ffi_current_core_id` FFI export.
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Platform.FFI

/-!
# WS-SM SM1.B.5 — `currentCoreId` typed FFI wrapper

This module wraps `Platform.FFI.ffiCurrentCoreId : BaseIO UInt64`
(produced by `rust/sele4n-hal/src/ffi.rs::ffi_current_core_id`) into a
typed `currentCoreId : BaseIO CoreId` that returns a `Fin numCores`.
The Rust side reads `TPIDR_EL1` on aarch64 — set by
`boot.rs::rust_boot_main` for the boot core and
`boot.S::secondary_entry` for secondaries — and returns the
`core_id` field of the resulting `PerCpuData` slot.

## Range invariant

The Rust side's `check_per_cpu_invariants()` boot gate verifies that
every slot in `PER_CPU_DATA` has `core_id == array_index`.  Since the
array has `MAX_SECONDARY_CORES + 1 = PlatformBinding.coreCount` slots
(pinned by compile-time assertions in `per_cpu.rs`), every plausible
`ffiCurrentCoreId` return value satisfies
`result.toNat < numCores`.  The wrapper here re-checks the bound and
panics on violation — a defensive runtime gate against the rare case
where TPIDR_EL1 is corrupt at the moment of the read (which would
indicate an in-flight memory-safety bug elsewhere).

## Production reachability

`Concurrency.currentCoreId` is reachable in the kernel's production
import closure via `SeLe4n/Platform/Staged.lean` — see that file for
the cross-subsystem build-anchor that forces this module to elaborate
on every CI run.

## Host vs hardware

On a hardware build the FFI symbol resolves to
`rust/sele4n-hal/src/ffi.rs::ffi_current_core_id`, which reads
`TPIDR_EL1` and returns the current core's id.  On a simulation
build (host development, CI smoke/full runs) the FFI symbol is never
invoked — the trace harness and test suites do not exercise per-core
state because the abstract model is single-core (SM5 will introduce
per-core scheduler state).  The wrapper is therefore a pass-through
that becomes meaningful once SM5+ per-core code lands.

## Anti-cycle note

This module imports `SeLe4n.Platform.FFI` (for `ffiCurrentCoreId`)
and `SeLe4n.Kernel.Concurrency.Types` (for `CoreId` / `numCores`).
`Platform.FFI` imports `Platform.Boot`, which transitively imports
`Platform.Contract`, which imports `Concurrency.Types`.  So the
required symbols are all in scope without a cycle:

  Concurrency.Types  ← Platform.Contract  ← Platform.Boot
                                          ← Platform.FFI
                                          ← Concurrency.Runtime (this file)

A future refactor that pulls the FFI declaration *down* into
`Concurrency.Types` would break the layering — `Concurrency.Types`
is a foundational module and must not depend on `Platform.*`.
-/

namespace SeLe4n.Kernel.Concurrency

/-- **WS-SM SM1.B.5** (closes SMP-M4): read the current core's
typed identifier from `TPIDR_EL1` via the Rust FFI.

The raw `UInt64` from `Platform.FFI.ffiCurrentCoreId` is range-checked
against `numCores` to recover a `Fin numCores`; an out-of-range value
panics rather than constructing a malformed `Fin`.  Under the
post-boot invariants (`check_per_cpu_invariants` having succeeded in
`boot.rs::rust_boot_main`) the panic arm is unreachable on hardware.

**Determinism**: under the abstract model the function is constant
`bootCoreId` — there is only one core in the verified model at SM1.B.
The function becomes meaningful at SM5 when per-core scheduler state
lands.

**Performance**: on aarch64 the call cost is one `mrs xN, tpidr_el1`
plus a cache-hot load of `PerCpuData.core_id` plus an `if` branch.
The `if h : ... < numCores` form is the standard Lean idiom for
recovering a `Fin n` from a `Nat` without introducing an unconditional
`unsafeCast`. -/
def currentCoreId : BaseIO CoreId := do
  let raw ← Platform.FFI.ffiCurrentCoreId
  if h : raw.toNat < numCores then
    pure ⟨raw.toNat, h⟩
  else
    -- On hardware this is unreachable under the post-boot invariants
    -- enforced by `check_per_cpu_invariants` in
    -- `rust/sele4n-hal/src/per_cpu.rs`.  On host the FFI stub returns
    -- 0 which trivially satisfies the bound.  The panic arm is a
    -- totality witness against a corrupt `TPIDR_EL1`.
    panic! s!"ffi_current_core_id returned {raw.toNat} ≥ numCores = {numCores}"

/-- **WS-SM SM1.B.5**: the typed core-id is always in range
`[0, numCores)`.  Trivial from the `Fin numCores` representation —
useful as a surface anchor so downstream Tier-3 scans can verify the
wrapper is wired through. -/
theorem currentCoreId_in_range_marker (c : CoreId) : c.val < numCores :=
  c.isLt

-- ============================================================================
-- WS-SM SM1.I.3 — Idle-wait typed wrappers
-- ============================================================================

/-- **WS-SM SM1.I.3**: typed wrapper for `Platform.FFI.ffiIdleWait`.

    Pure pass-through that surfaces the idle-wait primitive under the
    `Kernel.Concurrency` namespace.  At SM1.I.3 the Lean kernel has no
    per-core idle TCB to call this from; SM5 will wire it as the body
    of the verified idle-thread transition.

    **Behaviour**: on hardware parks the calling core on `wfe` until
    an event or interrupt arrives.  On host the stub returns
    immediately. -/
def idleWait : BaseIO Unit :=
  Platform.FFI.ffiIdleWait

/-- **WS-SM SM1.I.3**: typed wrapper for
    `Platform.FFI.ffiIdleWaitBounded`.

    `maxTicks` — counter-tick budget.  Returns elapsed ticks since the
    call began (≥ 0; 0 on host).  The Lean caller compares
    `elapsed >= maxTicks` to detect "did we time out without seeing an
    event". -/
def idleWaitBounded (maxTicks : UInt64) : BaseIO UInt64 :=
  Platform.FFI.ffiIdleWaitBounded maxTicks

-- ============================================================================
-- WS-SM SM1.I.4 — Per-core stats typed wrappers
-- ============================================================================

/-- **WS-SM SM1.I.4**: typed wrapper for
    `Platform.FFI.ffiPerCoreIrqCount`.

    Takes a typed `CoreId` (so the bound check on `core.val < numCores`
    is structural, not a runtime guard).  Returns the Relaxed snapshot
    of the core's `irq_count` counter. -/
def perCoreIrqCount (core : CoreId) : BaseIO UInt64 :=
  Platform.FFI.ffiPerCoreIrqCount (UInt64.ofNat core.val)

/-- **WS-SM SM1.I.4**: typed wrapper for
    `Platform.FFI.ffiPerCoreTimerTickCount`. -/
def perCoreTimerTickCount (core : CoreId) : BaseIO UInt64 :=
  Platform.FFI.ffiPerCoreTimerTickCount (UInt64.ofNat core.val)

/-- **WS-SM SM1.I.4**: typed wrapper for
    `Platform.FFI.ffiPerCoreSgiCount`. -/
def perCoreSgiCount (core : CoreId) : BaseIO UInt64 :=
  Platform.FFI.ffiPerCoreSgiCount (UInt64.ofNat core.val)

/-- **WS-SM SM1.I.4**: typed wrapper for
    `Platform.FFI.ffiPerCoreSyscallCount`. -/
def perCoreSyscallCount (core : CoreId) : BaseIO UInt64 :=
  Platform.FFI.ffiPerCoreSyscallCount (UInt64.ofNat core.val)

/-- **WS-SM SM1.I.4** structural marker: per-core stats accessors
return `BaseIO UInt64`.

A trivial witness used as a surface anchor — the four typed
accessors above must return a `BaseIO UInt64` so downstream Tier-3
scans verify the FFI bridge is wired through to the Rust counter
snapshots. -/
theorem perCoreIrqCount_returns_baseio_uint64_marker (core : CoreId) :
    (perCoreIrqCount core : BaseIO UInt64) =
      Platform.FFI.ffiPerCoreIrqCount (UInt64.ofNat core.val) := by
  rfl

/-- **WS-SM SM1.I.4** structural marker: `perCoreTimerTickCount` is a
direct FFI pass-through.  Audit-pass-1: symmetry with
`perCoreIrqCount_returns_baseio_uint64_marker`. -/
theorem perCoreTimerTickCount_returns_baseio_uint64_marker (core : CoreId) :
    (perCoreTimerTickCount core : BaseIO UInt64) =
      Platform.FFI.ffiPerCoreTimerTickCount (UInt64.ofNat core.val) := by
  rfl

/-- **WS-SM SM1.I.4** structural marker: `perCoreSgiCount` is a
direct FFI pass-through.  Audit-pass-1: symmetry. -/
theorem perCoreSgiCount_returns_baseio_uint64_marker (core : CoreId) :
    (perCoreSgiCount core : BaseIO UInt64) =
      Platform.FFI.ffiPerCoreSgiCount (UInt64.ofNat core.val) := by
  rfl

/-- **WS-SM SM1.I.4** structural marker: `perCoreSyscallCount` is a
direct FFI pass-through.  Audit-pass-1: symmetry. -/
theorem perCoreSyscallCount_returns_baseio_uint64_marker (core : CoreId) :
    (perCoreSyscallCount core : BaseIO UInt64) =
      Platform.FFI.ffiPerCoreSyscallCount (UInt64.ofNat core.val) := by
  rfl

/-- **WS-SM SM1.I.3** structural marker: `idleWait` is a direct FFI
pass-through.  Audit-pass-1: documenting the rfl pass-through that
the smoke test in `SmpFoundationsSuite.lean` exercises informally
deserves a proper theorem for Tier-3 surface scanning. -/
theorem idleWait_returns_baseio_unit_marker :
    (idleWait : BaseIO Unit) = Platform.FFI.ffiIdleWait := by
  rfl

/-- **WS-SM SM1.I.3** structural marker: `idleWaitBounded` is a
direct FFI pass-through. -/
theorem idleWaitBounded_returns_baseio_uint64_marker (maxTicks : UInt64) :
    (idleWaitBounded maxTicks : BaseIO UInt64) =
      Platform.FFI.ffiIdleWaitBounded maxTicks := by
  rfl

-- ============================================================================
-- WS-SM SM5.B.7 — Per-core context-switch typed wrappers
-- ============================================================================

/-- **WS-SM SM5.B.7**: typed wrapper for `Platform.FFI.ffiSwitchToThread`.

    Records (on the HAL side) that core `c` is now running thread `tid`, after
    the verified `switchToThreadOnCore` (`Scheduler/Operations/Selection.lean`)
    has computed the new per-core scheduler state.  Takes a typed `ThreadId`
    and `CoreId`, so the Rust-side `coreId < numCores` bound check never trips
    (`c.val < numCores`) — the `1` out-of-range status is unreachable from this
    typed entry point, so the returned status is always `0`.  At SM5.B.7 no
    Lean caller exists; SM5.C wires this into the per-core dispatch loop after
    a verified switch. -/
def switchToThreadHw (tid : SeLe4n.ThreadId) (c : CoreId) : BaseIO UInt64 :=
  Platform.FFI.ffiSwitchToThread (UInt64.ofNat tid.toNat) (UInt64.ofNat c.val)

/-- **WS-SM SM5.B.7**: typed wrapper for `Platform.FFI.ffiPerCoreCurrentThread`.

    Reads the per-core current-thread id the HAL recorded for core `c` (the
    value of the most recent `switchToThreadHw` for that core).  Returns the
    HAL sentinel (`u64::MAX`) for a core with no switch recorded yet. -/
def perCoreCurrentThreadHw (c : CoreId) : BaseIO UInt64 :=
  Platform.FFI.ffiPerCoreCurrentThread (UInt64.ofNat c.val)

/-- **WS-SM SM5.B.7** structural marker: `switchToThreadHw` is a direct FFI
pass-through (Tier-3 surface anchor; symmetry with the SM1.I marker family). -/
theorem switchToThreadHw_returns_baseio_uint64_marker
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (switchToThreadHw tid c : BaseIO UInt64) =
      Platform.FFI.ffiSwitchToThread (UInt64.ofNat tid.toNat) (UInt64.ofNat c.val) := by
  rfl

/-- **WS-SM SM5.B.7** structural marker: `perCoreCurrentThreadHw` is a direct
FFI pass-through. -/
theorem perCoreCurrentThreadHw_returns_baseio_uint64_marker (c : CoreId) :
    (perCoreCurrentThreadHw c : BaseIO UInt64) =
      Platform.FFI.ffiPerCoreCurrentThread (UInt64.ofNat c.val) := by
  rfl

end SeLe4n.Kernel.Concurrency
