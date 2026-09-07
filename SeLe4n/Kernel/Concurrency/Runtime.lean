-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.A: PRODUCTION (LANDED at the live cross-core `.call` completion).
-- `currentCoreId` / `fireCrossCoreSgis` / `emitWakeSgi` entered the production
-- import closure via `SyscallDispatchEntry` (the live `lean_syscall_dispatch_cross_core`
-- seam that fires the diff-recovered cross-core SGIs).  (Former "STATUS: staged"
-- marker replaced with this landing note per the implement-the-improvement rule.)
-- WS-SM SM1.B.5 (closes SMP-M4): typed wrapper for the
-- `ffi_current_core_id` FFI export.
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Concurrency.Sgi
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

-- ============================================================================
-- WS-RR RR7.33 — the snapshot the four accessors feed, and what it must say
-- ============================================================================

/-- **WS-RR RR7.33**: one core's counters, read together.

Register finding 98 was that the four accessors above are "declared, wrapped and
proven but read by nothing".  They are read by `perCoreStats` now, and the point
of reading them *together* is that the interesting facts are relations between
them: a tick and an SGI are both IRQs, and separately counted, so a snapshot of
one counter says nothing a snapshot of all four does not say better.

`syscalls` is not an interrupt count and is included because the same Rust
`PerCpuStats` slot carries it — a post-mortem that has the IRQ picture and not
the syscall picture is missing the half that says whether the core was running
user code at all. -/
structure PerCoreStatsSnapshot where
  /-- Total IRQs this core's handler dispatched — timer PPI, SGIs, and routed SPIs. -/
  irqs : UInt64
  /-- Timer PPI (INTID 30) only; a subset of `irqs`. -/
  timerTicks : UInt64
  /-- SGIs (INTID 0..15) only; a subset of `irqs`, disjoint from the timer PPI. -/
  sgis : UInt64
  /-- Synchronous `SVC` dispatches — not an interrupt, counted separately. -/
  syscalls : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- **WS-RR RR7.33**: read one core's whole counter slot.

The consumer the four accessors did not have.  Four `Relaxed` loads, so the
snapshot is *not* atomic as a whole — `irqs` may already have moved on by the
time `sgis` is read.  That is the right trade for counters the Rust module
states are "not required for correctness": a seq-cst snapshot would put barriers
on the IRQ hot path to buy an exactness no consumer needs.  It is also why
`perCoreStatsPlausible` below is a *plausibility* check with slack rather than
an equality. -/
def perCoreStats (core : CoreId) : BaseIO PerCoreStatsSnapshot := do
  let irqs ← perCoreIrqCount core
  let timerTicks ← perCoreTimerTickCount core
  let sgis ← perCoreSgiCount core
  let syscalls ← perCoreSyscallCount core
  pure { irqs, timerTicks, sgis, syscalls }

/-- **WS-RR RR7.33**: the sanity invariant `per_cpu_stats.rs` names and nothing
stated — "every core that ran for ≥ 1 tick saw ≥ 1 IRQ", generalised to the
containment the counters are defined by.

`timer_tick_count` counts INTID 30 and `sgi_count` counts INTIDs 0..15; both are
`irq_count` increments and the two INTID ranges are disjoint, so their sum is
bounded by the total.  Nothing constrains `syscalls`: an `SVC` is a synchronous
exception, not an interrupt.

**Read in a single direction.**  `false` means the snapshot cannot have come from
a coherent counter slot — a wiring defect in the FFI bridge, a core id resolving
to the wrong slot, or a counter that stopped being incremented where it is
documented to be.  `true` means only that nothing is provably wrong: the four
loads are independent, so a snapshot torn across a burst of interrupts is
plausible and still not a consistent instant. -/
def perCoreStatsPlausible (s : PerCoreStatsSnapshot) : Bool :=
  s.timerTicks.toNat + s.sgis.toNat ≤ s.irqs.toNat

/-- The docstring's own sentence, as a decidable consequence: a core that
recorded a timer tick recorded at least one IRQ. -/
theorem perCoreStatsPlausible_tick_implies_irq (s : PerCoreStatsSnapshot)
    (hPlausible : perCoreStatsPlausible s = true) (hTick : 0 < s.timerTicks.toNat) :
    0 < s.irqs.toNat := by
  unfold perCoreStatsPlausible at hPlausible
  have h := of_decide_eq_true hPlausible
  omega

/-- …and the same for an SGI, which is the cross-core half of the sentence. -/
theorem perCoreStatsPlausible_sgi_implies_irq (s : PerCoreStatsSnapshot)
    (hPlausible : perCoreStatsPlausible s = true) (hSgi : 0 < s.sgis.toNat) :
    0 < s.irqs.toNat := by
  unfold perCoreStatsPlausible at hPlausible
  have h := of_decide_eq_true hPlausible
  omega

/-- A core that has taken no interrupt at all is plausible — the boot state of
every secondary before its first tick, so the check must not fire there. -/
theorem perCoreStatsPlausible_zero :
    perCoreStatsPlausible { irqs := 0, timerTicks := 0, sgis := 0, syscalls := 0 } = true := by
  decide

/-- The load-bearing negative: a tick count that exceeds the IRQ total is
refused.  This is the shape a mis-wired accessor produces — two counters read
from different cores' slots — and the reason the predicate is worth stating
rather than assuming. -/
theorem perCoreStatsPlausible_refuses_ticks_over_irqs :
    perCoreStatsPlausible { irqs := 1, timerTicks := 2, sgis := 0, syscalls := 0 } = false := by
  decide

/-- **WS-RR RR7.33**: `perCoreStats` reads every accessor, in slot order.

The structural pin behind the finding: a refactor that drops one of the four
loads — the failure that would silently return a `default` field — fails here. -/
theorem perCoreStats_reads_every_accessor (core : CoreId) :
    perCoreStats core = (do
      let irqs ← perCoreIrqCount core
      let timerTicks ← perCoreTimerTickCount core
      let sgis ← perCoreSgiCount core
      let syscalls ← perCoreSyscallCount core
      pure { irqs, timerTicks, sgis, syscalls }) := by
  rfl

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

/-- **WS-SM SM5.B.7** (PR #805 review P2-2): the largest `ThreadId.toNat` that
    `switchToThreadHw` will encode over the FFI.  Any `tid.toNat <
    switchToThreadHwTidBound` both (a) fits in a `UInt64` (so `UInt64.ofNat`
    does not silently wrap) **and** (b) is distinct from the HAL's
    `NO_CURRENT_THREAD = u64::MAX` sentinel (`UInt64.size - 1`), so a recorded
    id can never be misread as "no current thread".  Equal to `2^64 - 1`. -/
def switchToThreadHwTidBound : Nat := UInt64.size - 1

/-- **WS-SM SM5.B.7** (PR #805 review P2-2): rejected-status returned by
    `switchToThreadHw` when the `ThreadId` is not FFI-encodable.  Shares the
    HAL's `0 = recorded`, `nonzero = not recorded` status convention (the Rust
    side already returns `1` for an out-of-range `core_id`); the Lean wrapper
    returns the same `1` when it refuses to encode an out-of-range `tid`,
    fail-closed. -/
def switchToThreadHwRejected : UInt64 := 1

/-- **WS-SM SM5.B.7**: typed wrapper for `Platform.FFI.ffiSwitchToThread`.

    Records (on the HAL side) that core `c` is now running thread `tid`, after
    the verified `switchToThreadOnCore` (`Scheduler/Operations/Selection.lean`)
    has computed the new per-core scheduler state.  Takes a typed `ThreadId`
    and `CoreId`.  The `CoreId` side is bound by construction (`c.val <
    numCores`), so the Rust-side `coreId < numCores` check never trips.

    The `ThreadId` side, however, wraps an *unbounded* `Nat` (PR #805 review
    P2-2), so the wrapper is **fail-closed** on it: a `tid` whose `toNat` does
    not fit in a `UInt64`, or that collides with the HAL `NO_CURRENT_THREAD =
    u64::MAX` sentinel (both captured by `tid.toNat ≥ switchToThreadHwTidBound`),
    is **not** encoded — the wrapper returns `switchToThreadHwRejected` (`1`,
    "not recorded") without touching the HAL, rather than silently recording the
    wrong thread id or aliasing "no current thread".  Mirrors the SM1.I.4
    u64-before-cast FFI discipline.  Well-formed kernel `ThreadId`s are far below
    the bound, so the happy path is unchanged.  At SM5.B.7 no Lean caller
    exists; SM5.C wires this into the per-core dispatch loop after a verified
    switch. -/
def switchToThreadHw (tid : SeLe4n.ThreadId) (c : CoreId) : BaseIO UInt64 :=
  if tid.toNat < switchToThreadHwTidBound then
    Platform.FFI.ffiSwitchToThread (UInt64.ofNat tid.toNat) (UInt64.ofNat c.val)
  else
    pure switchToThreadHwRejected

/-- **WS-SM SM5.B.7**: typed wrapper for `Platform.FFI.ffiPerCoreCurrentThread`.

    Reads the per-core current-thread id the HAL recorded for core `c` (the
    value of the most recent `switchToThreadHw` for that core).  Returns the
    HAL sentinel (`u64::MAX`) for a core with no switch recorded yet. -/
def perCoreCurrentThreadHw (c : CoreId) : BaseIO UInt64 :=
  Platform.FFI.ffiPerCoreCurrentThread (UInt64.ofNat c.val)

/-- **WS-SM SM5.B.7** structural marker: on an FFI-encodable `tid`
(`tid.toNat < switchToThreadHwTidBound`), `switchToThreadHw` is a direct FFI
pass-through (Tier-3 surface anchor; symmetry with the SM1.I marker family).
The encodability hypothesis is the PR #805 review P2-2 fail-closed guard;
well-formed kernel `ThreadId`s satisfy it trivially. -/
theorem switchToThreadHw_returns_baseio_uint64_marker
    (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : tid.toNat < switchToThreadHwTidBound) :
    (switchToThreadHw tid c : BaseIO UInt64) =
      Platform.FFI.ffiSwitchToThread (UInt64.ofNat tid.toNat) (UInt64.ofNat c.val) := by
  unfold switchToThreadHw
  rw [if_pos h]

/-- **WS-SM SM5.B.7** (PR #805 review P2-2 fail-closed witness): a `ThreadId`
that is not FFI-encodable (`tid.toNat ≥ switchToThreadHwTidBound` — too large
for `UInt64` or colliding with the `NO_CURRENT_THREAD` sentinel) is
**rejected** — `switchToThreadHw` returns `switchToThreadHwRejected` without
touching the HAL, so a valid Lean `ThreadId` can never be recorded as the wrong
thread or aliased to "no current thread". -/
theorem switchToThreadHw_rejects_unencodable
    (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : ¬ tid.toNat < switchToThreadHwTidBound) :
    (switchToThreadHw tid c : BaseIO UInt64) = pure switchToThreadHwRejected := by
  unfold switchToThreadHw
  rw [if_neg h]

/-- **WS-SM SM5.B.7** structural marker: `perCoreCurrentThreadHw` is a direct
FFI pass-through. -/
theorem perCoreCurrentThreadHw_returns_baseio_uint64_marker (c : CoreId) :
    (perCoreCurrentThreadHw c : BaseIO UInt64) =
      Platform.FFI.ffiPerCoreCurrentThread (UInt64.ofNat c.val) := by
  rfl


-- ============================================================================
-- WS-RR RR7.26 — recording the verified per-core thread choice on the HAL
--
-- Register §6 finding 45: `switchToThreadHw` had zero production callers while
-- both sides documented it as the seam the per-core scheduler's thread choice
-- reaches the hardware through.  The three state-committing per-core entries
-- now record their post-state's current thread through it, so the HAL's
-- per-core mirror follows the verified scheduler rather than lagging it.
--
-- One verb, not two call shapes: a transition that *vacates* a core has to
-- clear the mirror, and `switchToThreadHw` deliberately cannot write the
-- HAL's `NO_CURRENT_THREAD` sentinel (a `ThreadId` at that value is rejected
-- by `switchToThreadHwTidBound`, so no thread can be recorded as "none").
-- `recordCurrentThreadHw` takes the post-state's `Option ThreadId` and routes
-- each case to the verb that can express it.
-- ============================================================================

/-- **WS-RR RR7.26**: the HAL's "no thread recorded for this core" sentinel,
`ffi::NO_CURRENT_THREAD` = `u64::MAX`.

Equal to `switchToThreadHwTidBound` by construction, which is exactly why
`switchToThreadHw` refuses a `ThreadId` at or above it: the two meanings must
not alias, so the sentinel is writable only through `clearCurrentThreadHw`. -/
def noCurrentThreadHw : UInt64 := UInt64.ofNat switchToThreadHwTidBound

/-- **WS-RR RR7.26**: clear core `c`'s HAL current-thread mirror.

Writes the `NO_CURRENT_THREAD` sentinel through the same FFI verb
`switchToThreadHw` uses, which is the only way to express it: the typed
`ThreadId` path refuses that value precisely so a real thread can never be
recorded as "none".  Returns the HAL's `0 = recorded` status. -/
def clearCurrentThreadHw (c : CoreId) : BaseIO UInt64 :=
  Platform.FFI.ffiSwitchToThread noCurrentThreadHw (UInt64.ofNat c.val)

/-- **WS-RR RR7.26**: record what the verified per-core scheduler left running
on core `c`.

`some tid` records the thread; `none` — a transition that vacated the core —
clears the mirror rather than leaving it naming a thread that is no longer
current.  Leaving a stale name is not a harmless omission: `ffi_switch_to_thread`
is what a dispatch path reads to decide whose context to restore, so a mirror
that outlives its thread is a restore into a descheduled frame. -/
def recordCurrentThreadHw (cur? : Option SeLe4n.ThreadId) (c : CoreId) :
    BaseIO UInt64 :=
  match cur? with
  | some tid => switchToThreadHw tid c
  | none     => clearCurrentThreadHw c

/-- **WS-RR RR7.26**: the running case is the typed switch. -/
theorem recordCurrentThreadHw_some (tid : SeLe4n.ThreadId) (c : CoreId) :
    recordCurrentThreadHw (some tid) c = switchToThreadHw tid c := rfl

/-- **WS-RR RR7.26**: the vacated case clears the mirror — it is **not** a
no-op, which is the property the wiring depends on. -/
theorem recordCurrentThreadHw_none (c : CoreId) :
    recordCurrentThreadHw none c = clearCurrentThreadHw c := rfl

/-- **WS-RR RR7.26**: the sentinel a cleared mirror carries is exactly the value
`switchToThreadHw` refuses, so "no current thread" and "thread `u64::MAX`" can
never be confused at the seam. -/
theorem noCurrentThreadHw_not_writable_as_thread (tid : SeLe4n.ThreadId)
    (h : UInt64.ofNat tid.toNat = noCurrentThreadHw)
    (hFits : tid.toNat < UInt64.size) :
    ¬ tid.toNat < switchToThreadHwTidBound := by
  unfold noCurrentThreadHw switchToThreadHwTidBound at *
  have : tid.toNat = UInt64.size - 1 := by
    have := congrArg UInt64.toNat h
    simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hFits,
      Nat.mod_eq_of_lt (by omega : UInt64.size - 1 < UInt64.size)] using this
  omega

/-- **WS-RR RR7.26**: decode the raw core id a per-core kernel entry is invoked
with into a typed `CoreId`, or `none` when it names no core the model has.

The same guard the verified steps make (`perCoreRescheduleStep`,
`perCoreTimerTickStep`), lifted so the entry's *effects* can be gated by it too:
an entry called with an out-of-range id commits nothing, and must therefore
record nothing on the HAL either. -/
def coreIdOfUInt64? (coreId : UInt64) : Option CoreId :=
  if h : coreId.toNat < numCores then some ⟨coreId.toNat, h⟩ else none

/-- **WS-RR RR7.26**: `coreIdOfUInt64?` accepts exactly the ids the model has a
core for, and the core it yields is the one the verified step used. -/
@[simp] theorem coreIdOfUInt64?_eq_some (coreId : UInt64) (h : coreId.toNat < numCores) :
    coreIdOfUInt64? coreId = some ⟨coreId.toNat, h⟩ := by
  unfold coreIdOfUInt64?; rw [dif_pos h]

/-- **WS-RR RR7.26**: and refuses the rest. -/
@[simp] theorem coreIdOfUInt64?_eq_none (coreId : UInt64) (h : ¬ coreId.toNat < numCores) :
    coreIdOfUInt64? coreId = none := by
  unfold coreIdOfUInt64?; rw [dif_neg h]

/-- **WS-RR RR7.26**: the shared tail of the three state-committing per-core
entries — record on the HAL what the committed post-state left running.

Takes the pair the entry's atomic step returns: the core the raw id decoded to
and the thread that core's `current` slot holds afterwards.  `none` — a raw id
the model has no core for — records nothing, matching the step, which commits
nothing for such an id.

**A refused record clears the mirror rather than leaving it stale** (PR #892
review).  `switchToThreadHw` returns `switchToThreadHwRejected` *without
touching the HAL* for a `ThreadId` at or above `switchToThreadHwTidBound` — the
`u64::MAX` sentinel included — because that value is reserved for "no current
thread".  Discarding that verdict, as this tail did, left the mirror naming the
**previous** thread while the model had already committed a new one, which is
exactly the "restore into a descheduled frame" hazard `recordCurrentThreadHw`'s
own docstring warns about: `ffi_switch_to_thread`'s mirror is what a dispatch
path reads to decide whose context to restore.  Clearing is the fail-closed
answer available today — a cleared mirror means "no current thread", which a
restore path must treat as nothing to restore, rather than as somebody else.

The branch is **unreachable** on a well-formed state: `objectIndexBounded`
bounds every object id by `maxObjects` (65536), so no installed thread has an
id anywhere near `2 ^ 64 - 1`.  It is defence in depth against a corrupted
committed state, and defence in depth that throws its verdict away is not
defence at all.  Halting the core instead — the other fail-closed answer — is an
SM10.1 decision, because that is where the mirror is *read*; it is registered
rather than pre-empted here. -/
def recordCommittedCurrentThreadHw
    (r : Option (CoreId × Option SeLe4n.ThreadId)) : BaseIO Unit :=
  match r with
  | none => pure ()
  | some (c, cur?) => do
      let status ← recordCurrentThreadHw cur? c
      if status == switchToThreadHwRejected then
        let _ ← clearCurrentThreadHw c
        pure ()
      else
        pure ()

/-- **PR #892 review**: recording `none` never takes the fail-closed clear —
`clearCurrentThreadHw` is the record in that case, so the guard cannot loop or
double-write. -/
theorem recordCommittedCurrentThreadHw_none_is_clear (c : CoreId) :
    recordCommittedCurrentThreadHw (some (c, none)) =
      (do
        let status ← clearCurrentThreadHw c
        if status == switchToThreadHwRejected then
          let _ ← clearCurrentThreadHw c
          pure ()
        else
          pure ()) := rfl

/-- **PR #892 review**: an encodable thread takes the pass-through unchanged —
the fail-closed clear is reached only on the refusal `switchToThreadHw` returns
without touching the HAL. -/
theorem recordCommittedCurrentThreadHw_some_is_switch
    (c : CoreId) (tid : SeLe4n.ThreadId) :
    recordCommittedCurrentThreadHw (some (c, some tid)) =
      (do
        let status ← switchToThreadHw tid c
        if status == switchToThreadHwRejected then
          let _ ← clearCurrentThreadHw c
          pure ()
        else
          pure ()) := rfl

-- ============================================================================
-- WS-SM SM5.C.4 — Cross-core wake SGI-emission typed wrappers
-- ============================================================================

/-- **WS-SM SM5.C.4**: encode a `CoreId` as a single-bit GIC-400 CPU target
    mask — bit `c.val` set, every other bit clear.

    GICD_SGIR's `TargetListFilter = 0b00` interprets the 8-bit target list as a
    bitmask of CPU interfaces (bit `i` = CPU `i`), so a cross-core
    `.reschedule` SGI addressed to exactly one core `c` uses the mask `1 << c`.
    For RPi5 (`numCores = 4`) only bits `0..3` are ever set, well inside the
    8-bit field; the GIC-400 SGI target list is 8 bits, so this encoding is
    valid for any platform with `≤ 8` cores. -/
def coreIdTargetMask (c : CoreId) : UInt8 := UInt8.ofNat (1 <<< c.val)

/-- **WS-SM SM5.C.4**: the SGI INTID of an `SgiKind`, as the `UInt8` the
    `ffi_send_sgi` FFI expects.  Structurally `< 16` (`SgiKind.toIntid_in_range`),
    so the Rust-side `intid >= 16` panic never trips on a well-formed call. -/
def sgiIntidU8 (k : SgiKind) : UInt8 := UInt8.ofNat k.toIntid.val

/-- **WS-SM SM5.C.4**: emit an SGI of kind `k` to a single target core `c` over
    the FFI.  Wraps `Platform.FFI.ffiSendSgi` with the typed `CoreId` → target
    mask and `SgiKind` → INTID encodings, so the Rust-side bound checks
    (`targetMask` bits, `intid < 16`) never trip on a well-formed Lean call.

    **BKL-discipline ordering (SM5.C.4).**  This must be invoked *after* the
    wake's state write is committed and visible: the Rust `ffi_send_sgi` emits a
    `dsb ish` before writing `GICD_SGIR` (SM1.F.8 / ARM ARM B2.7.5), so the
    woken thread's run-queue insertion is observable on the target core before
    the `.reschedule` SGI fires there.  The verified `wakeThread` returns the
    SGI to emit; the runtime dispatch loop commits the state under
    `wakeThreadLockSet`, releases, then calls `emitWakeSgi`. -/
def sendSgiToCore (target : CoreId) (k : SgiKind) : BaseIO Unit :=
  Platform.FFI.ffiSendSgi (coreIdTargetMask target) (sgiIntidU8 k)

/-- **WS-SM SM5.C.4**: emit a cross-core `.reschedule` SGI to `target` — the
    poke a remote wake sends so the target core re-runs its scheduler
    (`handleRescheduleSgiOnCore`). -/
def sendRescheduleSgi (target : CoreId) : BaseIO Unit :=
  sendSgiToCore target SgiKind.reschedule

/-- **WS-SM SM5.C.4**: emit the optional SGI a `wakeThread` returned.  `none`
    (the target was the executing core — a local wake) emits nothing; `some
    (target, kind)` (a remote wake) emits the SGI.  This is the runtime side of
    the SM5.C.2 `wakeThread` decision: the pure `wakeThread` computes *whether*
    and *what* to emit, `emitWakeSgi` performs the FFI emission. -/
def emitWakeSgi (sgi : Option (CoreId × SgiKind)) : BaseIO Unit :=
  match sgi with
  | none => pure ()
  | some (target, k) => sendSgiToCore target k

/-- **WS-SM SM5.C.4** structural marker: `sendSgiToCore` is a direct FFI
    pass-through with the typed encodings. -/
theorem sendSgiToCore_eq_ffi (target : CoreId) (k : SgiKind) :
    (sendSgiToCore target k : BaseIO Unit) =
      Platform.FFI.ffiSendSgi (coreIdTargetMask target) (sgiIntidU8 k) := rfl

/-- **WS-SM SM5.C.4** structural marker: `sendRescheduleSgi` emits the
    `.reschedule` SGI. -/
theorem sendRescheduleSgi_eq (target : CoreId) :
    sendRescheduleSgi target = sendSgiToCore target SgiKind.reschedule := rfl

/-- **WS-SM SM5.C.4** structural marker: a local wake (`none`) emits no SGI. -/
theorem emitWakeSgi_none : (emitWakeSgi none : BaseIO Unit) = pure () := rfl

/-- **WS-SM SM5.C.4** structural marker: a remote wake (`some (target, kind)`)
    emits the SGI to the target core. -/
theorem emitWakeSgi_some (target : CoreId) (k : SgiKind) :
    (emitWakeSgi (some (target, k)) : BaseIO Unit) = sendSgiToCore target k := rfl

/-- **WS-SM SM5.C.4**: the `.reschedule` SGI's INTID byte is `0`. -/
theorem sgiIntidU8_reschedule : sgiIntidU8 SgiKind.reschedule = 0 := by decide

/-- **WS-SM SM5.C.4**: the boot core's GIC target mask is bit 0 (`= 1`). -/
theorem coreIdTargetMask_bootCore : coreIdTargetMask bootCoreId = 1 := by decide

-- ============================================================================
-- WS-SM SM5.F.4 — cross-core PIP wake dispatch (the SM6 firing layer)
-- ============================================================================

/-- **WS-SM SM5.F.4**: dedup a list of cross-core SGIs by target core, keeping the
    first occurrence of each target.  A per-core priority-inheritance boost *chain*
    (`propagatePipChainCrossCore`) can poke the same remote core more than once (two
    chain links sharing a home core); one `.reschedule` SGI per core suffices, and
    coalescing avoids a redundant cross-core IPI. -/
def dedupCrossCoreSgis (sgis : List (CoreId × SgiKind)) : List (CoreId × SgiKind) :=
  sgis.foldl (fun acc s => if acc.any (fun a => a.1 == s.1) then acc else acc ++ [s]) []

/-- **WS-SM SM5.F.4** (SM6 cross-core PIP dispatch — the runtime firing side): fire
    every cross-core `.reschedule` SGI a per-core priority-inheritance boost returned,
    coalesced by target core.  The pure SM5.F transitions (`pipBoostWithWake`,
    `propagatePipChainCrossCore`, `restoreToReadyWithWake`, `resumeThreadOnCore`)
    compute *which* cores to poke and the boost state; `fireCrossCoreSgis` performs the
    FFI emissions over `sendSgiToCore`.

    **BKL-discipline ordering (SM5.C.4 / SM1.F.8).**  Invoke *after* the boost state is
    committed and visible: each `ffi_send_sgi` emits `dsb ish` before writing
    `GICD_SGIR`, so a poked core observes the boosted holder's new run-queue bucket
    before its `.reschedule` SGI fires.  This is the dispatch the live IPC donation /
    timeout / resume paths invoke so a cross-core boost from a syscall fires its SGI. -/
def fireCrossCoreSgis (sgis : List (CoreId × SgiKind)) : BaseIO Unit :=
  (dedupCrossCoreSgis sgis).forM (fun s => sendSgiToCore s.1 s.2)

/-- **WS-SM SM5.F.4** marker: `dedupCrossCoreSgis []` is `[]`. -/
@[simp] theorem dedupCrossCoreSgis_nil : dedupCrossCoreSgis [] = [] := rfl

/-- **WS-SM SM5.F.4** marker: firing an empty SGI list is a no-op — the single-core
    (all-local) case fires nothing, so the dispatch is inert on single-core hardware. -/
@[simp] theorem fireCrossCoreSgis_nil : (fireCrossCoreSgis [] : BaseIO Unit) = pure () := rfl

/-- **WS-SM SM5.F.4** (fold-frame helper): every element of the dedup fold result is
    either in the seed accumulator or in the remaining list — the workhorse of
    `dedupCrossCoreSgis_subset`. -/
private theorem dedupFold_mem (l : List (CoreId × SgiKind)) :
    ∀ (acc : List (CoreId × SgiKind)) x,
      x ∈ l.foldl (fun acc s => if acc.any (fun a => a.1 == s.1) then acc else acc ++ [s]) acc →
        x ∈ acc ∨ x ∈ l := by
  induction l with
  | nil => intro acc x hx; exact Or.inl hx
  | cons head tail ih =>
    intro acc x hx
    simp only [List.foldl_cons] at hx
    rcases ih _ x hx with hStep | hTail
    · by_cases hc : (acc.any (fun a => a.1 == head.1)) = true
      · rw [if_pos hc] at hStep; exact Or.inl hStep
      · rw [if_neg hc] at hStep
        rcases List.mem_append.mp hStep with hAcc | hHead
        · exact Or.inl hAcc
        · exact Or.inr (by rw [List.mem_singleton.mp hHead]; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem head hTail)

/-- **WS-SM SM5.F.4**: every entry of a deduped SGI list was in the input — `dedup`
    introduces no SGI the boost did not request (it only drops duplicates). -/
theorem dedupCrossCoreSgis_subset (sgis : List (CoreId × SgiKind)) :
    ∀ x ∈ dedupCrossCoreSgis sgis, x ∈ sgis := by
  intro x hx
  rcases dedupFold_mem sgis [] x hx with hAcc | hL
  · simp at hAcc
  · exact hL

/-- **WS-SM SM5.F.4** (fold-frame helper): the dedup fold preserves core-distinctness —
    if the seed accumulator's target cores are `Nodup`, so are the result's.  The
    workhorse of `dedupCrossCoreSgis_nodup_cores`. -/
private theorem dedupFold_nodup_cores (l : List (CoreId × SgiKind)) :
    ∀ (acc : List (CoreId × SgiKind)), (acc.map (·.1)).Nodup →
      ((l.foldl (fun acc s => if acc.any (fun a => a.1 == s.1) then acc else acc ++ [s])
        acc).map (·.1)).Nodup := by
  induction l with
  | nil => intro acc hacc; exact hacc
  | cons head tail ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    by_cases hc : (acc.any (fun a => a.1 == head.1)) = true
    · rw [if_pos hc]; exact hacc
    · rw [if_neg hc, List.map_append, List.nodup_append]
      refine ⟨hacc, by simp, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      rw [List.mem_map] at ha
      obtain ⟨entry, hEntry, hEq⟩ := ha
      intro hContra
      have hCore : entry.1 = head.1 := hEq.trans hContra
      have hAny : acc.any (fun a => a.1 == head.1) = true := by
        rw [List.any_eq_true]
        exact ⟨entry, hEntry, by rw [hCore]; exact beq_self_eq_true _⟩
      exact absurd hAny hc

/-- **WS-SM SM5.F.4**: a deduped SGI list pokes each target core **at most once** — its
    target cores are pairwise distinct.  Together with `dedupCrossCoreSgis_subset` (no SGI
    the boost did not request) this is the full coalescing guarantee: a per-core boost
    *chain* that names the same remote home core on two links fires exactly one
    `.reschedule` IPI there, never a redundant cross-core poke (no IPI storm). -/
theorem dedupCrossCoreSgis_nodup_cores (sgis : List (CoreId × SgiKind)) :
    ((dedupCrossCoreSgis sgis).map (·.1)).Nodup :=
  dedupFold_nodup_cores sgis [] (by simp)

-- ============================================================================
-- WS-SM SM7.A.3 — Shootdown acknowledgment-flag typed wrappers
-- ============================================================================
--
-- Typed `CoreId` wrappers over the `ffi_shootdown_*` exports
-- (`rust/sele4n-hal/src/shootdown.rs` via `Platform.FFI`).  The
-- `Fin numCores` argument typing makes the Rust fail-closed bound
-- panics structurally unreachable (`shootdownAck_ffi_core_in_range`).
-- The SM7.B protocol composes these around the pure
-- `Architecture.TlbShootdownState` transitions: the target handler
-- acknowledges the round generation it serviced only after its drained
-- TLBIs retire; the initiator acquire-polls `shootdownAllAckedForRound`
-- (SM7.B.5's bounded wait).

/-- **WS-SM SM7.F.3**: acknowledge round generation `gen` for core `c` —
    the runtime effect of the pure `Architecture.acknowledgeShootdown` at
    core `c` (plan §3.2 step 4c; the SM7.B.4 release edge).  Monotone on
    the Rust side, so an acknowledgment names the round it discharged. -/
def shootdownAckRound (c : CoreId) (gen : Nat) : BaseIO Unit :=
  Platform.FFI.ffiShootdownAckRound (UInt64.ofNat c.val) (UInt64.ofNat gen)

/-- **WS-SM SM7.F.3**: acquire-load the highest round generation core
    `c` has acknowledged — the runtime read behind the pure
    `TlbShootdownState.ackOnCore c` (which holds for a round of
    generation `g` exactly when this value is `≥ g`). -/
def shootdownAckedGeneration (c : CoreId) : BaseIO Nat := do
  return (← Platform.FFI.ffiShootdownAckedGeneration (UInt64.ofNat c.val)).toNat

/-- **WS-SM SM7.F.3**: acquire-poll the acknowledgment slots for round
    generation `gen` — the runtime read of the pure
    `Architecture.allAcked` predicate restricted to the round's target
    set, the initiator wait-loop's exit condition (plan §3.2 step 5).

    There is deliberately **no** round *reset*: a round is identified by
    its generation rather than by a cleared flag vector, so nothing has
    to be cleared before it opens.  That is what removes the window in
    which a `.tlbShootdownReq` SGI left pending by an earlier round
    could acknowledge into this one. -/
def shootdownAllAckedForRound (gen : Nat) (initiator : CoreId) : BaseIO Bool := do
  return (← Platform.FFI.ffiShootdownAllAckedForRound (UInt64.ofNat gen)
    (UInt64.ofNat initiator.val)) != 0

/-- **WS-SM SM7.B.7 + SM7.F.3**: the cooperative round-lock acquire's
    self-service arm — if core `c` has not yet acknowledged the
    currently published round, flush its own TLB (the LOCAL
    `TLBI VMALLE1`, mirroring the Rust `.tlbShootdownReq` handler; the
    in-flight round's initiator owns the broadcast step) and acknowledge
    that round.  `true` = it serviced a round.

    A lock waiter must do this: with IRQs masked in the SVC path it
    cannot take the holder's `.tlbShootdownReq` SGI, yet the holder's
    round waits on this core's acknowledgment — a blind spin would
    deadlock into the wait-timeout panic. -/
def shootdownSelfServiceRound (c : CoreId) : BaseIO Bool := do
  return (← Platform.FFI.ffiShootdownSelfServiceRound (UInt64.ofNat c.val)) != 0

/-- **WS-SM SM7.B.7**: try to acquire THE global shootdown-round lock —
    the runtime realisation of `Architecture.ShootdownRoundLockId` (a
    Rust CAS try-lock; never blocks).  `false` means a round is in
    flight; the caller's cooperative loop must service its own pending
    shootdown obligation before retrying (see
    `ffiShootdownRoundLockTryAcquire`). -/
def shootdownRoundLockTryAcquire : BaseIO Bool := do
  return (← Platform.FFI.ffiShootdownRoundLockTryAcquire) != 0

/-- **WS-SM SM7.F.3** (PR #854 review P1): allocate the runtime round
    generation — the identity the hardware round runs under.

    Distinct from the model's `TlbShootdownState.roundGeneration` on
    purpose.  The model generation is allocated by the pure transition,
    inside the atomic state commit, and keys the *window drain* (which
    descriptors belong to this commit).  This one keys the *acknowledgment
    channel*, whose test is monotone (`acked_gen >= gen`), so it must
    order the round against the rounds whose acks could satisfy its wait
    — i.e. against hardware execution order.  Commit order is not that
    order: a core can commit generation N and stall before the round
    lock while another commits N+1 and runs its round to completion, at
    which point every target's `acked_gen` is N+1 and the N round's wait
    would pass with no target having serviced it (an under-invalidation
    — the SMP-C4 stale-TLB hazard).

    Allocated by a `fetch_add` performed **while holding the round lock**,
    so allocation order is execution order by construction.  Returns a
    value read from a `UInt64` counter, so the `UInt64.ofNat` narrowing
    on the publish/wait path round-trips exactly and the `Nat` round
    identity cannot alias at the FFI boundary; the Rust side additionally
    fails closed if the counter ever wraps.  The first generation is 1,
    never the vacuously-satisfied 0. -/
def shootdownAllocateRoundGeneration : BaseIO Nat := do
  return (← Platform.FFI.ffiShootdownAllocateRoundGeneration).toNat

/-- **WS-SM SM7.B.7**: release the global shootdown-round lock —
    **only** after the initiator observed `allAcked`.

    The timeout path is **not** a second caller: it retains the lock
    permanently, quarantining the subsystem, because a target that
    never certified its invalidation leaves a stale translation that
    no later round may run alongside.  See
    `Platform.FFI.ffiShootdownRoundLockRelease` for the full contract. -/
def shootdownRoundLockRelease : BaseIO Unit :=
  Platform.FFI.ffiShootdownRoundLockRelease

/-- **WS-SM SM7.B.6 + SM7.B.7**: park this PE permanently.  **Never
    returns** — see `Platform.FFI.ffiFatalHalt`.

    Prefer `fatalHaltAll` for a fail-closed barrier: parking one PE
    leaves the rest of the machine running. -/
def fatalHalt : BaseIO Unit :=
  Platform.FFI.ffiFatalHalt

/-- **WS-SM SM0.H + SM7.B.6/B.7**: broadcast `haltAll` to every other
    PE, then park this one.  **Never returns** — see
    `Platform.FFI.ffiFatalHaltAll`. -/
def fatalHaltAll : BaseIO Unit :=
  Platform.FFI.ffiFatalHaltAll

/-- **WS-SM SM7.B.5 + B.6 + SM7.F.3**: bounded acquire-poll for round
    generation `gen` acknowledged — the runtime wait loop
    (`Architecture.waitAllAckedBounded`'s realisation); `false` means
    timeout, the caller's fail-closed panic trigger. -/
def shootdownWaitAllAcked (gen : Nat) (initiator : CoreId)
    (onlineMask : UInt64) (timeoutTicks : UInt64) : BaseIO Bool := do
  return (← Platform.FFI.ffiShootdownWaitAllAcked (UInt64.ofNat gen)
    (UInt64.ofNat initiator.val) onlineMask timeoutTicks) != 0

/-- **WS-SM SM7.B.2**: one snapshot of the Rust `smp::CORE_IRQ_READY`
    bitmask (Acquire) — the runtime target-set mask of the SM7.A
    PR #838 P1 obligation.  The online set is the *IRQ-serviceable*
    flag each secondary publishes **itself** after `enable_irq`, NOT
    the primary's `CORE_READY` release handshake (PR #839 review P1):
    a released-but-not-yet-IRQ-ready core — or one wedged in the
    timer-init-failure halt loop — is excluded, so it can never hang
    the initiator's ack wait on an SGI it cannot service.  Round-scoped
    callers (`completeShootdownRounds`) read the mask **once** and test
    bits with `coreOnlineInMask`, so every target decision within a
    round sees the same snapshot (one FFI crossing instead of one per
    target; no rounds run concurrently with core bring-up per the
    SM7.A P1 contract, so the snapshot cannot go stale mid-round). -/
def shootdownOnlineMask : BaseIO UInt64 :=
  Platform.FFI.ffiShootdownOnlineMask

/-- **WS-SM SM7.B.2**: pure bit test against an online-mask snapshot. -/
def coreOnlineInMask (mask : UInt64) (c : CoreId) : Bool :=
  mask &&& ((1 : UInt64) <<< (UInt64.ofNat c.val)) != 0

/-- **WS-SM SM7.B.2**: is core `c` online?  Single-core convenience
    form — one mask read, one bit test.  Round-scoped callers should
    snapshot `shootdownOnlineMask` once instead. -/
def shootdownCoreOnline (c : CoreId) : BaseIO Bool := do
  let mask ← shootdownOnlineMask
  return coreOnlineInMask mask c

/-- **WS-SM SM7.B.2**: the convenience form is exactly the snapshot
    form's composition — the entry's one-read refactor changes no
    per-core decision. -/
theorem shootdownCoreOnline_eq_mask_test (c : CoreId) :
    shootdownCoreOnline c = do
      let mask ← shootdownOnlineMask
      return coreOnlineInMask mask c := rfl

/-- **WS-SM SM7.B.7**: the executing core's **local** full TLB flush
    (`TLBI VMALLE1` + `dsb ish` + `isb` — no inter-core broadcast) —
    the declared Lean-side mirror of the HAL primitive.

    A lock-waiter discharging its own pending shootdown obligation
    cleans exactly its own view (mirroring the Rust `.tlbShootdownReq`
    handler's local `tlbi vmalle1`), never other cores' — broadcasting
    there would be semantically harmless over-invalidation but
    architecturally wrong (the round's initiator owns the broadcast
    step).

    **WS-SM SM7.F.3**: the live self-service arm no longer issues this
    flush through the Lean seam.  An acknowledgment must name the round
    it discharged, so the generation read, the flush and the
    acknowledgment have to be indivisible with respect to a newer
    round's publish; splitting them across three FFI crossings would let
    a round publish in between and make the acknowledgment claim work
    this core had not done.  They are therefore one Rust call,
    `shootdownSelfServiceRound`, which issues exactly this flush. -/
def tlbiLocalFullFlush : BaseIO Unit :=
  Platform.FFI.ffiTlbiAll

/-- **WS-SM SM7.B (debt (1))**: begin publishing the round's operand set
    into the Rust per-descriptor mailbox (seqlock → writers-in-progress).
    The initiator calls this under the round lock, before firing the
    `.tlbShootdownReq` SGIs. -/
def shootdownPublishBegin : BaseIO Unit :=
  Platform.FFI.ffiShootdownPublishBegin

/-- **WS-SM SM7.B (debt (1))**: write one operand into the mailbox at slot
    `index` (raw `TlbInvalidation` encoding: `opTag` per
    `TlbInvalidation.toOpTag`, plus ASID / VAddr operands). -/
def shootdownPublishSlot (index : Nat) (opTag : UInt32) (asid : UInt16)
    (vaddr : UInt64) : BaseIO Unit :=
  Platform.FFI.ffiShootdownPublishSlot (UInt64.ofNat index) opTag asid vaddr

/-- **WS-SM SM7.B (debt (1)) + SM7.F.3**: commit the publish of `len`
    operands belonging to round generation `gen` (seqlock → stable, then
    the generation).  Over-capacity collapses to one `vmalle1`;
    `len == 0` leaves the mailbox empty (handler falls back to the
    conservative local `vmalle1`). -/
def shootdownPublishCommit (len : Nat) (gen : Nat) : BaseIO Unit :=
  Platform.FFI.ffiShootdownPublishCommit (UInt64.ofNat len) (UInt64.ofNat gen)

/-- **WS-SM SM7.F.3**: `shootdownAckRound` is the raw FFI export applied
    to the widened core id and generation — nothing else happens on the
    Lean side. -/
theorem shootdownAckRound_eq_ffi (c : CoreId) (gen : Nat) :
    shootdownAckRound c gen =
      Platform.FFI.ffiShootdownAckRound (UInt64.ofNat c.val)
        (UInt64.ofNat gen) := rfl

/-- **WS-SM SM7.F.3**: `shootdownSelfServiceRound` is the raw FFI export
    applied to the widened core id, tested against zero. -/
theorem shootdownSelfServiceRound_eq_ffi (c : CoreId) :
    shootdownSelfServiceRound c = do
      return (← Platform.FFI.ffiShootdownSelfServiceRound
        (UInt64.ofNat c.val)) != 0 := rfl

/-- **WS-SM SM7.A.3**: every core id a typed wrapper hands the FFI is
    within the Rust `SHOOTDOWN_ACK` bounds — `CoreId = Fin numCores`
    widens to a `UInt64` whose `toNat` is exactly `c.val < numCores`,
    so the Rust fail-closed panic arm (`shootdown_core_id_checked`) is
    unreachable from well-typed kernel code.  The SM7.A analogue of
    `tlbiForSharing_ffi_args_in_range`. -/
theorem shootdownAck_ffi_core_in_range :
    ∀ c : CoreId, (UInt64.ofNat c.val).toNat < numCores := by decide

end SeLe4n.Kernel.Concurrency
