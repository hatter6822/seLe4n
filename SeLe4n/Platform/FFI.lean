-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.API
import SeLe4n.Kernel.Architecture.SyscallReturn
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Platform.Boot
import SeLe4n.Platform.RPi5.Contract

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
  symbols (`suspend_thread_inner`; the syscall entry itself is
  `lean_syscall_dispatch_cross_core` in `Kernel/SyscallDispatchEntry.lean` —
  WS-RA removed the vestigial `syscall_dispatch_inner`) are
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
    code that imports this module — preventing accidental use of a
    non-deployment labeling context as a "default" in contexts that
    should fail closed instead.

    **WS-RR RR5.3**: the witness is `Kernel.defaultLabelingContext`, a context
    `isInsecureDefaultContext` *rejects*.  It used to be
    `Kernel.testLabelingContext`, chosen because it passed that gate — which is
    the fail-open this phase closes: the witness is the value the labeling
    reference holds before a boot installs one, so choosing an admitted context
    for it meant every checked syscall entry was served under an all-public
    policy until (and unless) a boot overrode it. -/
instance : Nonempty LabelingContext := ⟨Kernel.defaultLabelingContext⟩

-- ============================================================================
-- AG7-A-iii: Timer FFI declarations
-- ============================================================================

/-- Read the ARM Generic Timer physical counter (CNTPCT_EL0).
    Returns the current 64-bit counter value (54 MHz on RPi5).
    Rust: `ffi_timer_read_counter` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_timer_read_counter"]
opaque ffiTimerReadCounter : BaseIO UInt64

/-- Reprogram the timer comparator for the next tick interval — re-arm
    only.  Global tick accounting is single-path and its one site is
    `ffiTimerAdvanceTickCount` (below), driven by the committed run-loop
    step; this seam deliberately cannot increment, so a second
    incrementer cannot reappear (AI1-C / M-26).
    Rust: `ffi_timer_reprogram` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_timer_reprogram"]
opaque ffiTimerReprogram : BaseIO Unit

/-- Get the current tick count (committed model-clock advances since
    boot — see `ffiTimerAdvanceTickCount`).
    Rust: `ffi_timer_get_tick_count` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_timer_get_tick_count"]
opaque ffiTimerGetTickCount : BaseIO UInt64

/-- WS-SM SM5.I (commit-coupled shadow clock — PR #880 follow-up): advance
    the HAL's global tick counter (`TICK_COUNT`) by one.  Called by
    `perCoreTimerTickEntry` **iff** the just-committed run-loop step
    advanced the model clock (`machine.timer` — the boot core's committed
    success arm, `tickClockedState`; the flag is definitionally the clock
    delta, `perCoreTimerTickStepWithClockAdvance_flag_def`), so the HAL
    shadow tracks the model clock exactly on every arm: pre-readiness
    ticks, non-boot cores and fail-closed entries advance neither clock.
    The sole live-path incrementer of `TICK_COUNT` (AI1-C / M-26 single
    path, owner relocated from the boot-core ISR invocation, which counted
    invocations rather than commits); `ffiTimerReprogram` stays
    re-arm-only.  Lock-free on the Rust side (one atomic fetch-add), so
    calling it under the kernel-entry lock violates no ordering rule.
    Rust: `ffi_timer_advance_tick_count` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_timer_advance_tick_count"]
opaque ffiTimerAdvanceTickCount : BaseIO Unit

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
-- WS-SM SM7.A.3 — TLB-shootdown acknowledgment-flag FFI bindings
-- ============================================================================
--
-- The link-time bridge to the per-core `SHOOTDOWN_ACK` array
-- (`rust/sele4n-hal/src/shootdown.rs`) — the runtime realisation of the
-- Lean `TlbShootdownState.shootdownAck` vector.  Since SM7.F.3 each
-- slot holds a monotone *acknowledged round generation* rather than a
-- Boolean, so the Lean `ackOnCore c = true` for a round of generation
-- `g` corresponds to the runtime `acked_gen[c] >= g`; an acknowledgment
-- therefore names the round it discharged and a stale one can never
-- satisfy a later round.  Lean callers use the typed `CoreId` wrappers
-- in `SeLe4n/Kernel/Concurrency/Runtime.lean` (`shootdownAckRound` /
-- `shootdownAckedGeneration` / `shootdownAllAckedForRound` /
-- `shootdownSelfServiceRound`), whose `Fin numCores` typing makes the
-- Rust fail-closed panic arms structurally unreachable
-- (`shootdownAck_ffi_core_in_range`).
-- Release/acquire ordering rationale: shootdown.rs module docs; the
-- SM2.A-level formalisation is SM7.B.4 (`shootdownAck_release_acquire`).

/-- **WS-SM SM7.F.3**: acknowledge round generation `gen` for the given
    core (the target handler's plan §3.2 step 4c, AFTER the round's
    TLBIs retired locally).  Monotone (`fetch_max`) on the Rust side, so
    a stale handler can never lower a core's recorded generation.
    Panics on the Rust side if `coreId ≥ 4`.

    Rust: `ffi_shootdown_ack_round` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_shootdown_ack_round"]
opaque ffiShootdownAckRound : (coreId : UInt64) → (gen : UInt64) → BaseIO Unit

/-- **WS-SM SM7.F.3**: acquire-load the highest round generation the
    given core has acknowledged.  Panics on the Rust side if
    `coreId ≥ 4`.

    Rust: `ffi_shootdown_acked_generation` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_shootdown_acked_generation"]
opaque ffiShootdownAckedGeneration : (coreId : UInt64) → BaseIO UInt64

/-- **WS-SM SM7.F.3**: acquire-poll the acknowledgment slots for round
    generation `gen` — the initiator wait-loop's exit condition
    (plan §3.2 step 5); `1` = every IRQ-serviceable non-initiator core
    has acknowledged `gen`.  Panics on the Rust side if `initiator ≥ 4`.

    Rust: `ffi_shootdown_all_acked_for_round` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_shootdown_all_acked_for_round"]
opaque ffiShootdownAllAckedForRound :
    (gen : UInt64) → (initiator : UInt64) → BaseIO UInt64

/-- **WS-SM SM7.B.7 + SM7.F.3**: the cooperative round-lock acquire's
    self-service arm — if this core has not yet acknowledged the
    currently published round, flush its own TLB (`TLBI VMALLE1`, local)
    and acknowledge that round.  `1` = it serviced a round.  Combining
    the generation read, the flush and the acknowledgment in one Rust
    call keeps the "latch the generation BEFORE any TLB work" discipline
    in one place; splitting it across the FFI would let a newer round
    publish in between and make the acknowledgment name a round this
    core had not serviced.  Panics on the Rust side if `coreId ≥ 4`.

    Rust: `ffi_shootdown_self_service_round` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_shootdown_self_service_round"]
opaque ffiShootdownSelfServiceRound : (coreId : UInt64) → BaseIO UInt64

@[extern "ffi_shootdown_round_lock_try_acquire"]
opaque ffiShootdownRoundLockTryAcquire : BaseIO UInt64

/-- **WS-SM SM7.F.3** (PR #854 review P1): allocate the next runtime
    shootdown round generation (a `fetch_add` on the Rust counter; fails
    closed on wrap).

    The caller must already hold the round lock — that is what makes the
    allocation order the hardware execution order, which the monotone
    `acked_gen >= gen` wait depends on.

    Rust: `ffi_shootdown_allocate_round_generation` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_shootdown_allocate_round_generation"]
opaque ffiShootdownAllocateRoundGeneration : BaseIO UInt64

/-- **WS-SM SM7.B.7**: release the global shootdown-round lock —
    **only** after the initiator observed `allAcked`.

    There is no other legitimate caller.  On the timeout path the lock
    is deliberately retained **permanently**: a target never certified
    its invalidation, so every other core's round must block rather
    than proceed against a TLB this one could not clean, and holding
    the lock is what quarantines the subsystem.  Releasing it there —
    which this contract permitted until the PR #854 review, and which
    the runtime did until v0.32.130 — reopens the mailbox for the next
    round while the stale translation the barrier exists to prevent is
    still live.

    A caller written to this contract must therefore treat a timeout as
    terminal (`haltFailClosed`), never as a path that unwinds.

    Rust: `ffi_shootdown_round_lock_release` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_shootdown_round_lock_release"]
opaque ffiShootdownRoundLockRelease : BaseIO Unit

/-- **WS-SM SM7.B.6 + SM7.B.7**: park this PE permanently — the
    fail-closed barrier's actual stop.  **Never returns.**

    Lean's `panic!` cannot serve as a fail-closed barrier: it requires
    `[Inhabited α]` precisely because the runtime prints the message and
    then returns the default value, so in `BaseIO Unit` it reports the
    violation and execution continues (PR #854 review).  The seam
    therefore calls `panic!` for the diagnostic and this for the halt.

    The `BaseIO Unit` type is the FFI convention, not a claim that this
    returns — `ffi_fatal_halt` is `-> !` on the Rust side.  Callers must
    still not rely on that alone; see `haltFailClosed`.

    Rust: `ffi_fatal_halt` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_fatal_halt"]
opaque ffiFatalHalt : BaseIO Unit

/-- **WS-SM SM0.H + SM7.B.6/B.7 (PR #854 review)**: broadcast the
    `haltAll` SGI (INTID 4) to every other PE, then park this one.
    **Never returns.**

    This is the form the fail-closed barriers use.  `ffiFatalHalt` parks
    only the calling PE, which is not a barrier: the other cores keep
    running against a TLB this core has just declared it could not
    clean, and the target that never acknowledged can resume with the
    stale translation.  `SgiKind.haltAll` had been reserved since SM0.H
    and documented as "halt all cores" with no handler behind it; the
    Rust side now registers one at boot.

    Rust: `ffi_fatal_halt_all` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_fatal_halt_all"]
opaque ffiFatalHaltAll : BaseIO Unit

/-- **WS-SM SM7.B.5 + B.6 + SM7.F.3**: bounded acquire-poll for round
    generation `gen` acknowledged — spins up to `timeoutTicks`
    generic-timer ticks; returns `1` on observed all-acked-for-`gen`,
    `0` on timeout (the caller's fail-closed panic trigger; the poll's
    verdict semantics are `Architecture.shootdown_timeout_handling`).
    Panics on the Rust side if `initiator ≥ 4`.

    Rust: `ffi_shootdown_wait_all_acked` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_shootdown_wait_all_acked"]
opaque ffiShootdownWaitAllAcked :
    (gen : UInt64) → (initiator : UInt64) → (onlineMask : UInt64) →
      (timeoutTicks : UInt64) → BaseIO UInt64

/-- **WS-SM SM7.B.2 (runtime target masking)**: the online-core bitmask
    (bit `c` set ⇔ core `c` is IRQ-serviceable; the boot core is always
    set) — the SM7.A PR #838 P1 obligation's "target-set computation
    must enumerate online cores only" at the SGI-fire site.  Reads the
    Rust `smp::CORE_IRQ_READY` flags (Acquire) — the flag a secondary
    publishes itself after `enable_irq`, not the primary's `CORE_READY`
    release handshake (PR #839 review P1), so a core that cannot yet
    take an SGI is never a target.

    Rust: `ffi_shootdown_online_mask` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_shootdown_online_mask"]
opaque ffiShootdownOnlineMask : BaseIO UInt64

/-- **WS-SM SM7.B (debt (1))**: begin publishing the round's operand set
    into the per-descriptor mailbox (bumps the seqlock to
    writers-in-progress).  The initiator calls this under the global
    round lock, BEFORE it fires the `.tlbShootdownReq` SGIs.

    Rust: `ffi_shootdown_publish_begin` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_shootdown_publish_begin"]
opaque ffiShootdownPublishBegin : BaseIO Unit

/-- **WS-SM SM7.B (debt (1))**: write one operand at slot `index` into the
    mailbox.  `opTag` matches `Architecture.TlbInvalidation.toOpTag`
    (0=vmalle1, 1=vae1, 2=aside1, 3=vale1); the initiator loops over the
    round's collapsed operands supplying the index.

    Rust: `ffi_shootdown_publish_slot` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_shootdown_publish_slot"]
opaque ffiShootdownPublishSlot :
    (index : UInt64) → (opTag : UInt32) → (asid : UInt16) → (vaddr : UInt64) → BaseIO Unit

/-- **WS-SM SM7.B (debt (1)) + SM7.F.3**: commit the publish of `len`
    operands belonging to round generation `gen` (bumps the seqlock to
    stable, then publishes the generation).  `len` above capacity
    collapses to a single `vmalle1`; `len == 0` leaves the mailbox empty
    so the handler falls back to the conservative local `vmalle1`.

    Rust: `ffi_shootdown_publish_commit` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_shootdown_publish_commit"]
opaque ffiShootdownPublishCommit : (len : UInt64) → (gen : UInt64) → BaseIO Unit

-- ============================================================================
-- WS-RA RA.C.1: the per-core syscall return-frame mailbox
-- ============================================================================

/-- WS-RA (plan §3.3): publish the syscall return frame (`x0`-`x5`) into the
    executing core's return-frame mailbox, read back by `dispatch_svc`
    inside the same `with_kernel_entry` critical section — the
    `ShootdownOpMailbox` publish pattern, for the same reason (a scalar
    export return cannot carry six words, and the FFI deliberately carries
    no `lean_object*`).

    **Link-gating**: called ONLY from `syscallDispatchCrossCoreEntry`
    (`Kernel/SyscallDispatchEntry.lean`), never from the pure
    `syscallDispatchFromAbi` — host executables link this module's object
    and the suites drive the pure function, which must stay extern-free.

    Rust: `ffi_syscall_return_frame` in `sele4n-hal/src/ffi.rs`. -/
@[extern "ffi_syscall_return_frame"]
opaque ffiSyscallReturnFrame :
    (x0 x1 x2 x3 x4 x5 : UInt64) → BaseIO Unit

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
--   R2.B.0  — KernelError → UInt32 mapping (mirrors `rust/sele4n-types/src/error.rs`;
--              the bit-63 encodeError / encodeOk pair is RETIRED — WS-RA)
--   R2.A.1  — `kernelStateRef`, `kernelLabelingContextRef` (IO.Refs)
--   R2.A.2  — `initialiseKernelState`, `getKernelState`, `updateKernelState`
--   R2.A.3  — `bootAndInitialiseFromPlatform` (boot wrapper)
--   R2.B.1  — `writeFfiRegistersToTcb`, `readReturnValue` (helpers)
--   R2.B.1  — `syscallDispatchFromAbi` (typed-ABI entry point)

/-- WS-RC R2.B.0: Map a `KernelError` to its `u32` FFI discriminant.

The discriminants 0..54 mirror `rust/sele4n-types/src/error.rs` exactly.
A regression that adds a Lean variant without updating the Rust enum (or
vice versa) is caught by `tests/SyscallDispatchSuite.lean`'s round-trip
check (`KernelError.toUInt32` ∘ `SyscallId.toNat` matches the documented
table in `rust/sele4n-types/src/error.rs`).

Discriminant 17 (`notImplemented`) is the historical "stub" return; per
WS-RC R2 the FFI no longer emits it from the dispatch path — every error
now corresponds to a substantive kernel rejection.

WS-RA (RA.A.5): the 55-arm table moved to the canonical
`SeLe4n.Model.KernelError.toDiscriminant`
(`Kernel/Architecture/SyscallReturn.lean`), which also carries the inverse
`ofDiscriminant?` and the round-trip proofs; this function is its `UInt32`
instance so the discriminant table exists exactly once. -/
def KernelError.toUInt32 (e : KernelError) : UInt32 :=
  (SeLe4n.Model.KernelError.toDiscriminant e).toUInt32

/-- WS-RA (RA.A.5): the instance relationship, pinned — this `UInt32` map
and the canonical `Nat` table agree on every variant. -/
theorem KernelError.toUInt32_eq_toDiscriminant (e : KernelError) :
    (KernelError.toUInt32 e).toNat = SeLe4n.Model.KernelError.toDiscriminant e := by
  cases e <;> decide

-- ============================================================================
-- WS-RA: the bit-63 protocol is RETIRED
-- ============================================================================
--
-- `encodeError` / `encodeOk` and their theorems (`encodeError_high_bit_set`,
-- `encodeOk_high_bit_clear`) are deleted with the WS-RA flip.  Bit 63 was a
-- workaround for multiplexing status into the value register: with the
-- channels separated — `x0` the full-width value, the status label (ABI v3) on
-- `x1` (`Architecture.errorFrame`) — there is nothing to multiplex, and a
-- badge may use all 64 bits.  The hazard the protocol carried is retained as
-- the negative `Architecture.bit63Encoding_not_injective_on_badges`
-- (`Kernel/Architecture/SyscallReturn.lean`), stated over the retired mask
-- literal so it survives the functions' deletion, and Tier-3 negative
-- anchors keep `encodeOk` / `encodeError` from returning.

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
`syscallEntryChecked` consults to reject a labeling that provides no
domain separation (`isInsecureDefaultContext`).

**WS-RR RR5.3**: initialised to `Kernel.defaultLabelingContext`, which that
gate **rejects** — so every checked entry fails closed with `.policyDenied`
until `bootAndInitialiseFromPlatform` installs a real deployment context.
Before RR5.3 the initial value was `Kernel.testLabelingContext`, chosen
precisely because it passed the gate; combined with the boot wrapper's
`Option`-defaulting-to-`none` labeling argument, a boot that supplied no
context left an all-public policy live and every checked entry served under
it.  Both halves are closed: the argument is mandatory and the pre-boot value
is refused.

Simulation and test paths install `Kernel.harnessLabelingContext` explicitly
(via `initialiseKernelLabelingContext` or the boot wrapper), which is a real
two-domain deployment labeling rather than a guard-evading one.  The hardware
boot installs the platform binding's own labeling through
`bootAndInitialisePlatform` — for `RPi5Platform`,
`Kernel.confinedLabelingContext rpi5UpperDomainBase rpi5LowerWitnessIndex …`
(`Platform.RPi5.rpi5_deploymentLabeling`). -/
initialize kernelLabelingContextRef : IO.Ref LabelingContext ←
  IO.mkRef Kernel.defaultLabelingContext

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

/-- WS-SM SM5.I: read-modify-write of the kernel state, returning a
    by-product computed alongside the new state.  `f st = (a, st')` installs `st'`
    and returns `a` in one call, so no *further* read of the ref is needed to
    recover the by-product (the per-core timer-tick driver uses this to commit
    `timerTickOnCore`'s new state and recover its cross-core SGIs in one step).

    **This combinator is not itself a cross-core atomic.**  `IO.Ref.modifyGet`
    is a read followed by a write, not a hardware read-modify-write, so two
    cores calling it concurrently would lose one commit entirely: both read
    `st`, both compute from it, and the second write installs a post-state
    derived from a pre-state that no longer holds — silently discarding the
    first core's whole transition and returning success for it.  Every verified
    transition is a *pure function*, so the theorems say what `f` computes, not
    that `f` is applied to the state the caller last observed; that gap is
    closed by serialising kernel entry, not by this combinator.

    **Serialisation is present (SM5.I, v0.32.142).**  Every kernel entry that
    commits state runs inside
    `rust/sele4n-hal/src/kernel_entry.rs`'s `with_kernel_entry` bracket, so the
    read and the write are one critical section against every other kernel
    entry.  All five committing entries are bracketed —
    `lean_syscall_dispatch_cross_core` (`svc_dispatch::dispatch_svc`),
    `lean_per_core_timer_tick` (`timer::per_core_timer_tick_isr`, from
    `trap.rs::handle_irq_per_core`'s timer branch),
    `lean_per_core_reschedule` (`trap.rs::reschedule_sgi_handler`, the
    `.reschedule` SGI receiver),
    `lean_secondary_kernel_main` (`smp.rs::rust_secondary_main`, the bring-up
    reschedule — bracketed *and* invoked before `enable_irq` on its core, so a
    tick cannot re-enter the non-reentrant lock on the same core) and
    `suspend_thread_cross_core` (`ffi::sele4n_suspend_thread`).  The primary
    bring-up entry (`lean_kernel_main`, the SM10.1 image target's boot seam) is
    the one committing path outside the bracket: its `initialiseKernelState`
    install runs while secondaries may already be executing bracketed entries,
    so SM10.1 MUST either order the install before Phase 5 releases the
    secondaries or take this same bracket — an unbracketed install racing a
    bracketed tick can be overwritten by a commit derived from the
    pre-install state (the lost-commit shape above).  Recorded as an SM10.1
    obligation in `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md`.

    The lock is the SM2 verified `TicketLock`, so entry is FIFO and no core
    starves; it is acquired strictly **outside** `SHOOTDOWN_ROUND_LOCK`; and its
    spin **discharges the waiter's own pending shootdown obligation** on every
    poll (`shootdown::self_service_round`).  That last part is load-bearing
    rather than an optimisation: IRQs are masked on the kernel-entry paths, so a
    waiter cannot take the `.tlbShootdownReq` SGI, and a holder blocked on that
    waiter's acknowledgment would otherwise deadlock against it.  It is the same
    mechanism SM7.B.7 already uses for the round lock.

    Until v0.32.142 this said the serialisation was *owed*, and five sites
    across Lean and Rust described three mutually exclusive mechanisms, none of
    them live.  With the lock in place, SMP returns to the default decision #7
    states (`CmdlineConfig::default` has `smp_enabled: true`), which was gated on
    exactly this phase.  See `docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md`
    §"Kernel-entry serialisation". -/
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

/-- WS-RR RR5.3: the boot error a deployment labeling context that declares no
    verified domain separation is refused with.

Kept as a named definition rather than an inline literal so the fail-closed
arm has an identity a test can match on and a caller can recognise without
string-matching on prose. -/
def insecureLabelingContextBootError : String :=
  "boot refused: the deployment labeling context declares no verified domain \
   separation (LabelingContext.separatedThreads); build one with \
   Kernel.deploymentLabelingContext"

/-- PR #889 review round 3: the refusal for a labeling whose declared separation
witnesses are not installed threads of the boot state. -/
def uninstalledSeparationWitnessBootError : String :=
  "boot: the labeling's declared separation witnesses are not installed threads of the boot state (PR #889 review round 3)"

/-- PR #889 review round 3: the boot wrapper over a **declared core list** and a
labeling — the shared body of `bootAndInitialiseFromPlatform` (every model
core) and `bootAndInitialisePlatform` (the binding's cores).

Three refusals, in order, and none commits anything: the labeling guard
(`insecureLabelingContextBootError`), the checked boot's own rejection
(forwarded verbatim), and — new in this round — a boot whose labeling's
declared separation witnesses are not installed threads of the boot state
(`uninstalledSeparationWitnessBootError`, `declaredWitnessesInstalled`).  The
guard decides that the labeling separates two admissible *ids*; only the boot
state can say whether those ids are threads the deployment creates, and a
partition that separates no running thread is exactly the vacuous deployment
the guard exists to refuse. -/
def bootAndInitialiseFromPlatformOn
    (cores : List SeLe4n.Kernel.Concurrency.CoreId)
    (config : PlatformConfig)
    (ctx : LabelingContext) :
    BaseIO (Except String SystemState) := do
  if isInsecureDefaultContext ctx then
    pure (Except.error insecureLabelingContextBootError)
  else
    match bootFromPlatformCheckedWithIdleThreadsFor cores config with
    | Except.error e => pure (Except.error e)
    | Except.ok ist =>
      if declaredWitnessesInstalled ist.state ctx then
        let st := ist.state
        initialiseKernelState st
        initialiseKernelLabelingContext ctx
        pure (Except.ok st)
      else
        pure (Except.error uninstalledSeparationWitnessBootError)

/-- WS-RC R2.A.3 / **WS-RR RR5.2, RR5.3**: Boot wrapper that validates the
    deployment labeling context, runs `bootFromPlatformChecked`, installs the
    resulting `SystemState` into `kernelStateRef` and the context into
    `kernelLabelingContextRef`.

On a hardware build the Rust HAL's kernel-init path calls this
function exactly once after low-level (assembly + Rust) init; the
returned `SystemState` is then live in `kernelStateRef` for every
subsequent SVC entry.  On a simulation build the function is a no-op
beyond what the boot entry already does — `MainTraceHarness`
keeps using `bootFromPlatformChecked` directly because every test path
threads state explicitly.

**WS-RR RR5.14 — the boot entry is now `bootFromPlatformCheckedWithIdleThreads`.**
It used to be `bootFromPlatformChecked`, which installs no idle threads at all:
`currentOnCore c = none` on every core and `getTcb? (idleThreadId c) = none`, so
`idleDispatchableOnCore` was `false` everywhere and `idleFallbackOnCore` took its
`setCurrentOnCore c none` arm — every core would stall with nothing to run at its
first scheduling point.  Meanwhile SM5.J's `schedulerNoStall_smp` and the
`no_starvation_under_smp` capstone both take `hIdle : ∀ c,
idleThreadEnqueuedOnCore st c` **by hypothesis**, and no reachable state
discharged it.  The idle-installing wrapper that existed
(`bootFromPlatformWithIdleThreads`) had no runtime caller and, because it sets
current slots without enqueuing, would not have discharged it either.

The new entry is a thin composition over `bootFromPlatformChecked` — same
validation, same rejections, the seven results characterizing it unchanged — that
folds a per-core idle enqueue over `allCores`.  The hypothesis is discharged from
the state the kernel actually comes up in
(`bootFromPlatformCheckedWithIdleThreads_idleThreadEnqueuedOnCore`).

**RR5.2 — the labeling context is mandatory.**  It used to be
`ctx : Option LabelingContext := none`, and on the `none` path the wrapper
installed the boot state and left whatever the labeling reference already held
— which was `testLabelingContext`, an all-public-except-the-sentinel policy the
pre-RR5 guard admitted.  A hardware boot that simply did not pass a context
therefore came up with information-flow enforcement vacuous, silently.  The
argument now has no default, so "no context" is not expressible.

**RR5.3 — an inadmissible context fails the boot closed.**  Making the argument
mandatory removes *absence*; it does not remove a caller passing
`defaultLabelingContext` or any other labeling with no real separation.  The
wrapper therefore runs the same guard `syscallEntryChecked` runs
(`isInsecureDefaultContext`) **before** committing anything, and refuses with
`insecureLabelingContextBootError`.  Ordering is load-bearing: the check
precedes `initialiseKernelState`, so a refused boot leaves *both* references
untouched — the kernel-state reference at `default : SystemState` and the
labeling reference at its fail-closed pre-boot value — rather than leaving a
live post-boot state paired with a policy that enforces nothing.

Returns the post-boot state on success, or an error string on failure: the boot
error from `bootFromPlatformChecked` (which the idle entry forwards verbatim —
`bootFromPlatformCheckedWithIdleThreads_rejects_invalid`), or
`insecureLabelingContextBootError`.
Neither IO.Ref is updated on either failure path — callers can detect the
failure explicitly without seeing partial state. -/
def bootAndInitialiseFromPlatform
    (config : PlatformConfig)
    (ctx : LabelingContext) :
    BaseIO (Except String SystemState) :=
  bootAndInitialiseFromPlatformOn SeLe4n.Kernel.Concurrency.allCores config ctx

/-- WS-RR RR5.2: boot under the **platform binding's own** labeling.

`bootAndInitialiseFromPlatform` takes the labeling as an argument, which is the
right shape for a caller that has one — the SD suite installs a dozen — and the
wrong shape for the hardware boot, where *which* labeling is a deployment
decision that should be made once, where the platform is described, and not
re-made by whoever writes the boot call.  `PlatformBinding.deploymentLabeling`
(`Platform/Contract.lean`) is that decision — the `DeploymentLabeling` *source*,
not a context — and this entry boots under `PlatformBinding.labeling`, the
constructor's output on it: the RPi5 binding's source is
`Kernel.confinedDeploymentLabeling rpi5UpperDomainBase rpi5LowerWitnessIndex …`, so its labeling is
`Kernel.confinedLabelingContext rpi5UpperDomainBase rpi5LowerWitnessIndex …`
(`Platform.RPi5.rpi5_deploymentLabeling`, by `rfl`); the simulation bindings'
source is `Kernel.harnessDeploymentLabeling`.

Because the binding stores the source, the guard's admission
(`PlatformBinding.labeling_admitted`) and the whole of `LabelingContextValid`
(`PlatformBinding.labeling_valid`) are theorems of every binding rather than
proofs each one carries, so the refusal arm of `bootAndInitialiseFromPlatform`
is unreachable from here — machine-checked as
`bootAndInitialisePlatform_eq_checked_boot`: this entry accepts and rejects
exactly what `bootFromPlatformCheckedWithIdleThreads` does.  SM10.1's
`lean_kernel_main` is the intended caller, with `RPi5Platform`. -/
def bootAndInitialisePlatform (platform : Type) [PlatformBinding platform]
    (config : PlatformConfig) : BaseIO (Except String SystemState) :=
  bootAndInitialiseFromPlatformOn (PlatformBinding.declaredCores (platform := platform)) config
    (PlatformBinding.labeling (platform := platform))

/-- WS-RR RR5.2: under a binding's labeling the boot entry **cannot** be refused
    on the labeling — it is the checked idle boot followed by the two installs,
    and nothing else.  The proof is the binding-level admission theorem
    (`PlatformBinding.labeling_admitted`) rewriting the guard to `false`; there
    is no case analysis, because there is no case. -/
theorem bootAndInitialisePlatform_eq_checked_boot (platform : Type) [PlatformBinding platform]
    (config : PlatformConfig) :
    bootAndInitialisePlatform platform config =
      (match bootFromPlatformCheckedWithIdleThreadsFor
          (PlatformBinding.declaredCores (platform := platform)) config with
        | Except.error e => pure (Except.error e)
        | Except.ok ist =>
            if declaredWitnessesInstalled ist.state (PlatformBinding.labeling (platform := platform)) then do
              initialiseKernelState ist.state
              initialiseKernelLabelingContext (PlatformBinding.labeling (platform := platform))
              pure (Except.ok ist.state)
            else
              pure (Except.error uninstalledSeparationWitnessBootError)) := by
  unfold bootAndInitialisePlatform bootAndInitialiseFromPlatformOn
  rw [PlatformBinding.labeling_admitted]
  rfl

/-- PR #889 review round 3: on the Raspberry Pi 5 the checked platform boot's
idle install is the **all-cores** one — the binding declares every model core
(`rpi5_cores_eq_allCores`) — so the all-cores boot theorems (the characterised
queues, `threadStateConsistent`, the reservation) are theorems of the hardware
boot and not of a form it never runs. -/
theorem bootAndInitialisePlatform_rpi5_all_cores (config : PlatformConfig) :
    bootFromPlatformCheckedWithIdleThreadsFor
        (PlatformBinding.declaredCores (platform := SeLe4n.Platform.RPi5.RPi5Platform)) config =
      bootFromPlatformCheckedWithIdleThreads config := by
  rw [SeLe4n.Platform.RPi5.rpi5_cores_eq_allCores]
  rfl

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

**WS-RA**: since the flip this is `Architecture.readReturnFrame`'s `x0`
projection (`readReturnValue_eq_readReturnFrame_x0`), retained so the
existing theorem surface keeps meaning what it meant.  The slot it reads
is now genuinely written: value-returning dispatch arms stage their
results via `Architecture.writeReturnFrameToTcb` (RA.B.5-B.7), and the
boundary composes `.unit` frames rather than reading stale registers
(`syscallReturnOutcome`'s shape-driven read).  The pre-WS-RA note that
stood here — "x0 post-syscall equals the caller's own pre-syscall x0
… documented current behaviour" — described the missing return path and
is gone with it.

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

-- ============================================================================
-- WS-RA — the FFI half of the return-frame seam (RA.B.2, RA.B.5a)
-- ============================================================================
--
-- The staging functions themselves (`writeReturnFrameToTcb`,
-- `readReturnFrame`, `TCB.withReturnFrame`, the frame lemmas and the
-- round trip) live in `Kernel/Architecture/SyscallReturn.lean` — they must
-- sit *below* `Kernel/API.lean` so the dispatch arms can stage, and this
-- module sits above it.  What belongs here is only what reads them at the
-- FFI boundary.

/-- `readReturnValue` is `Architecture.readReturnFrame`'s `x0` projection —
the retained-instance relationship RA.B.2 promises, so every existing
theorem over `readReturnValue` keeps meaning what it meant. -/
theorem readReturnValue_eq_readReturnFrame_x0
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    readReturnValue st tid = (Architecture.readReturnFrame st tid).x0 := by
  unfold readReturnValue Architecture.readReturnFrame SystemState.getTcb?
  cases h : st.objects[tid.toObjId]? with
  | none => rfl
  | some obj => cases obj <;> rfl

/-- WS-RA RA.B.5a: the outcome a completed dispatch hands the boundary,
decided from the caller's **post-state** (plan §3.5 — outcome is
state-dependent, not id-dependent): a caller left IPC-blocked has no frame
yet (`.blocks`); a returning caller's frame is composed per
`syscallReturnShape` — constructed for `.unit` shapes, read from the
staged registers for value shapes (§3.3's shape-driven read).  An
unresolvable syscall id or a vanished caller TCB fail closed to the unit
frame. -/
def syscallReturnOutcome (syscallId : UInt32) (st : SystemState)
    (tid : SeLe4n.ThreadId) : Architecture.SyscallOutcome :=
  let blocked :=
    match st.getTcb? tid with
    | some tcb => Architecture.ipcStateBlocksReturn tcb.ipcState
    | none => false
  if blocked then
    .blocks
  else
    let shape :=
      ((SyscallId.ofNat? syscallId.toNat).map Architecture.syscallReturnShape).getD .unit
    .returns (Architecture.frameForShape shape (Architecture.readReturnFrame st tid))

-- ============================================================================
-- WS-SM SM9.B.9 — the refusal seam
-- ============================================================================

/-! ## Why the refusal audit is written here and nowhere else

`Kernel α = SystemState → Except KernelError (α × SystemState)`, so a kernel
transition's `.error` arm carries **no post-state** and no producer can be put
on it — which is what SM8.C's `declassification_refusal_is_unrecorded`
recorded, and why closing the gap needed either a total transformer for the
transition or a structure written one layer up.

One layer up is here.  `syscallDispatchFromAbi` already converts every kernel
error into a **committed** `(SyscallOutcome, state)` pair, and it does so with
every field a refusal record needs already in hand: the executing core, the
resolved subject, the deployment's labeling context, the raw syscall number and
`x0`, and the `KernelError` itself.  So the refusal audit costs no change to
the kernel's error discipline, no widening of `syscallEntryChecked`'s error
type (which would move ~40 theorem statements and break the two that bake in
*"an error changes nothing"*), and no decode replay.

**What the caller learns is unchanged.**  The outcome this arm returns is
`Architecture.errorFrame ke` — computed from the error alone, exactly as before
the ledger existed (`refusalLedger_write_is_caller_invisible`).  And
`recordRefusal` is **total**: a full ring evicts and counts the eviction rather
than refusing, so the ledger has no failure mode that could surface to the
caller.  That matters more than it looks: a fail-closed ledger would make its
own occupancy readable from an unprivileged syscall's outcome, which is exactly
the CC-8 channel the trail's fail-closed bound already forces and which the
plan requires SM9.B not to duplicate. -/

/-- WS-SM SM9.C.1 (`refusalRecord_names_failed_hop`): **re-resolve the receiver
a refused second hop was about**, from the pre-state the seam already holds.

Mirrors the dispatch's own resolution exactly — the caller's TCB, its CSpace
root's depth, `resolveCapAddress` on the supplied pointer, the slot's
capability, and the notification the capability targets — and then runs the
*same* `declassifiedSignalReceiver?` the transition's second-hop gate ran on
the *same* pre-state, so the two resolutions cannot disagree
(`refusedSignalReceiver?_resolves`).  `none` on any resolution failure: a
refusal whose capability never resolved has no second hop to name.

The SM9.B landing deferred this on the ground that "the seam cannot see" the
resolved receiver.  The premise was wrong: the transition resolves its receiver
from the pre-state deterministically, and the seam holds that pre-state and the
caller's `x0`, so the receiver is a pure re-computation — the SM8.D
`entryDecode` replay pattern, with the tie stated as a theorem rather than
assumed. -/
def refusedSignalReceiver? (st : SystemState) (tid : SeLe4n.ThreadId)
    (capPtr : SeLe4n.CPtr) : Option SeLe4n.ThreadId :=
  -- WS-SM SM9.D.7: the four resolution steps are `syscallOperandCap?`, shared
  -- with the taint-propagation planner.  They used to be spelled out here; one
  -- resolver means the seam's re-resolution and the planner's cannot drift
  -- apart, which matters because both claim to name the object the dispatch
  -- arm acted on.
  match syscallOperandCap? st tid capPtr with
  | none => none
  | some cap =>
    match cap.target with
    | .object nid => declassifiedSignalReceiver? st nid
    | _ => none

/-- WS-SM SM9.C.1: on the resolution path the dispatch itself took, the seam's
re-resolution **is** the transition's — both are `declassifiedSignalReceiver?`
at the same state and the same notification, so the record below names exactly
the thread the second-hop gate refused. -/
theorem refusedSignalReceiver?_resolves (st : SystemState) (tid : SeLe4n.ThreadId)
    (capPtr : SeLe4n.CPtr) (tcb : TCB) (rootCn : CNode)
    (ref : SlotRef) (cap : Capability) (nid : SeLe4n.ObjId)
    (hTcb : st.getTcb? tid = some tcb)
    (hRoot : st.getCNode? tcb.cspaceRoot = some rootCn)
    (hRef : resolveCapAddress tcb.cspaceRoot capPtr rootCn.depth st = .ok ref)
    (hSlot : SystemState.lookupSlotCap st ref = some cap)
    (hTarget : cap.target = .object nid) :
    refusedSignalReceiver? st tid capPtr = declassifiedSignalReceiver? st nid := by
  simp only [refusedSignalReceiver?, syscallOperandCap?, hTcb, hRoot, hRef, hSlot, hTarget]

/-- WS-SM SM9.C.1: the ledger record's `refusedReceiver` fill — the re-resolved
receiver **exactly when** the refusal is the declassifying signal's second hop,
and `none` for every other `(syscall, reason)` pair.

Keyed on both coordinates deliberately: a future second producer of
`.declassificationDeniedAtReceiver` would have its own resolution semantics,
and blindly running the notification resolver against its operand would record
a wrong attribution — so adding one forces a decision here, exactly as the
total `refusalSeamClass` forces one at the seam. -/
def refusalReceiverFor (st : SystemState) (tid : SeLe4n.ThreadId)
    (sid : SyscallId) (ke : KernelError) (x0 : UInt64) : Option SeLe4n.ThreadId :=
  if sid = SyscallId.declassifySignal ∧ ke = KernelError.declassificationDeniedAtReceiver then
    refusedSignalReceiver? st tid (SeLe4n.CPtr.ofNat x0.toNat)
  else none

/-- WS-SM SM9.C.1: the fill on the second-hop refusal. -/
@[simp] theorem refusalReceiverFor_receiver_hop (st : SystemState) (tid : SeLe4n.ThreadId)
    (x0 : UInt64) :
    refusalReceiverFor st tid .declassifySignal .declassificationDeniedAtReceiver x0 =
      refusedSignalReceiver? st tid (SeLe4n.CPtr.ofNat x0.toNat) := by
  simp [refusalReceiverFor]

/-- WS-SM SM9.C.1: every other refusal names no receiver. -/
theorem refusalReceiverFor_other (st : SystemState) (tid : SeLe4n.ThreadId)
    (sid : SyscallId) (ke : KernelError) (x0 : UInt64)
    (h : ¬(sid = SyscallId.declassifySignal ∧
      ke = KernelError.declassificationDeniedAtReceiver)) :
    refusalReceiverFor st tid sid ke x0 = none := by
  simp [refusalReceiverFor, h]

/-- WS-SM SM9.B.9: **record a refused syscall in the ledger**, if its
classification says to.

Fail-closed on an unrecognised syscall number: an ABI number the kernel cannot
decode cannot be classified either, and such a call never reached a
declassification path — `syscallEntryChecked` rejects it with
`.invalidSyscallNumber` before any transition runs.

The subject's domain is resolved **here**, from the dispatch's own context, and
stored: `(liftLegacyContext ctx).threadDomainOf tid` is definitionally the
domain the live declassification path assigns that subject, so a refusal and a
success name the same subject the same way.  Recomputing it later is not
available — `LabelingContext` is an argument to this function, not persistent
state (`refusalRecord_domain_is_seam_resolved_at_seam`). -/
def recordSyscallRefusal
    (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState) : SystemState :=
  match SyscallId.ofNat? syscallId.toNat with
  | none => st
  | some sid =>
      match refusalSeamClass sid with
      | .exempt => st
      | .records =>
          { st with
            declassificationRefusals :=
              recordRefusal st.declassificationRefusals
                { originatingCore := executingCore
                  subject := tid
                  subjectDomain := (liftLegacyContext ctx).threadDomainOf tid
                  syscall := sid
                  reason := ke
                  requestedTarget := SeLe4n.CPtr.ofNat x0.toNat
                  refusedReceiver := refusalReceiverFor st tid sid ke x0 } }

/-- WS-SM SM9.B.9: an exempt syscall's refusal is not recorded — the ledger is
a declassification audit, not a general syscall-failure log. -/
theorem recordSyscallRefusal_exempt
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState) (sid : SyscallId)
    (hDecode : SyscallId.ofNat? syscallId.toNat = some sid)
    (hExempt : refusalSeamClass sid = .exempt) :
    recordSyscallRefusal ctx executingCore syscallId tid ke x0 st = st := by
  simp only [recordSyscallRefusal, hDecode, hExempt]

/-- WS-SM SM9.B.9 (**fail-closed**): a syscall number the kernel cannot decode
records nothing.  There is no classification to consult, and no declassification
was attempted — `syscallEntryChecked` rejects such a call outright. -/
theorem recordSyscallRefusal_undecodable
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState)
    (hDecode : SyscallId.ofNat? syscallId.toNat = none) :
    recordSyscallRefusal ctx executingCore syscallId tid ke x0 st = st := by
  unfold recordSyscallRefusal
  rw [hDecode]

/-- WS-SM SM9.B.9: a recorded syscall's refusal lands in the ledger's selected
slot, attributed — the positive half of the classification. -/
theorem recordSyscallRefusal_records
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState) (sid : SyscallId)
    (hDecode : SyscallId.ofNat? syscallId.toNat = some sid)
    (hRecords : refusalSeamClass sid = .records) :
    (recordSyscallRefusal ctx executingCore syscallId tid ke x0 st).declassificationRefusals
      = recordRefusal st.declassificationRefusals
          { originatingCore := executingCore
            subject := tid
            subjectDomain := (liftLegacyContext ctx).threadDomainOf tid
            syscall := sid
            reason := ke
            requestedTarget := SeLe4n.CPtr.ofNat x0.toNat
            refusedReceiver := refusalReceiverFor st tid sid ke x0 } := by
  simp only [recordSyscallRefusal, hDecode, hRecords]

/-- WS-SM SM9.C.1 (**`refusalRecord_names_failed_hop`**): a refusal of the
declassifying signal's **second hop** is recorded naming the resolved
receiver — the thread the badge would have been delivered onward to — not
merely the original capability operand.

The two halves compose: the plan refuses with the receiver's discriminant only
when a receiver **was** resolved
(`declassifiedSignalPlan_deniedAtReceiver_resolves`), and the seam's
re-resolution runs the same `declassifiedSignalReceiver?` on the same pre-state
the transition's gate read (`refusedSignalReceiver?_resolves`), so the recorded
identity is exactly the one the gate refused.  The resolution premises are the
dispatch's own — the caller's TCB, its CSpace root, the capability at the
supplied pointer targeting the notification — which is what holds whenever the
dispatch produced this discriminant in the first place.

This closes the §3.1 obligation the SM9.B landing moved here: without it a
monitor reading `.declassificationDeniedAtReceiver` beside a raw `CPtr` could
not identify the bound waiter an attempted downgrade actually targeted, while
the *success* path is required to audit exactly that destination
(`declassifiedSignal_audits_actual_destination`). -/
theorem refusalRecord_names_failed_hop
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (x0 : UInt64) (st : SystemState)
    (tcb : TCB) (rootCn : CNode) (ref : SlotRef) (cap : Capability)
    (notifId : SeLe4n.ObjId) (actorDomain : SecurityDomain)
    (hDecode : SyscallId.ofNat? syscallId.toNat = some .declassifySignal)
    (hTcb : st.getTcb? tid = some tcb)
    (hRoot : st.getCNode? tcb.cspaceRoot = some rootCn)
    (hRef : resolveCapAddress tcb.cspaceRoot (SeLe4n.CPtr.ofNat x0.toNat) rootCn.depth st
      = .ok ref)
    (hSlot : SystemState.lookupSlotCap st ref = some cap)
    (hTarget : cap.target = .object notifId)
    (hPlan : declassifiedSignalPlan (liftLegacyContext ctx) ctx.declassificationPolicy
      notifId actorDomain st = .error .declassificationDeniedAtReceiver) :
    ∃ receiver,
      declassifiedSignalReceiver? st notifId = some receiver ∧
      (recordSyscallRefusal ctx executingCore syscallId tid
          .declassificationDeniedAtReceiver x0 st).declassificationRefusals
        = recordRefusal st.declassificationRefusals
            { originatingCore := executingCore
              subject := tid
              subjectDomain := (liftLegacyContext ctx).threadDomainOf tid
              syscall := .declassifySignal
              reason := .declassificationDeniedAtReceiver
              requestedTarget := SeLe4n.CPtr.ofNat x0.toNat
              refusedReceiver := some receiver } := by
  obtain ⟨receiver, hRecv⟩ := declassifiedSignalPlan_deniedAtReceiver_resolves
    (liftLegacyContext ctx) ctx.declassificationPolicy notifId actorDomain st hPlan
  refine ⟨receiver, hRecv, ?_⟩
  rw [recordSyscallRefusal_records ctx executingCore syscallId tid
    .declassificationDeniedAtReceiver x0 st .declassifySignal hDecode
    refusalSeamClass_declassifySignal]
  have hSeam : refusalReceiverFor st tid .declassifySignal
      .declassificationDeniedAtReceiver x0 = some receiver := by
    rw [refusalReceiverFor_receiver_hop,
      refusedSignalReceiver?_resolves st tid (SeLe4n.CPtr.ofNat x0.toNat) tcb rootCn ref cap
        notifId hTcb hRoot hRef hSlot hTarget, hRecv]
  rw [hSeam]

/-- WS-SM SM9.B.9 (**the frame**): recording a refusal writes the ledger and
**nothing else**.

Stated over the whole state rather than field by field: the post-state is the
pre-state with exactly one field replaced, so every other component — the
object store, the scheduler, the machine, and in particular the audit trail —
is carried through by construction. -/
theorem recordSyscallRefusal_frame
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState) :
    ∃ L : RefusalLedger,
      recordSyscallRefusal ctx executingCore syscallId tid ke x0 st =
        { st with declassificationRefusals := L } := by
  unfold recordSyscallRefusal
  split
  · exact ⟨st.declassificationRefusals, rfl⟩
  · split
    · exact ⟨st.declassificationRefusals, rfl⟩
    · exact ⟨_, rfl⟩

/-- WS-SM SM9.B.9 (**the bundle survives the refusal write**): every
`proofLayerInvariantBundle` conjunct holds of the committed post-state.

**Unconditional**, and that is the content: the ledger is bounded by its
*type* — a `Vector` ring and two `Fin` counters — so no conjunct reads it and
the writer owes nothing.  A `List` ring with `Nat` counters would have needed a
seventeenth conjunct and a capacity obligation at *every* writer, and this
theorem is where that cost would have been paid — the carriage block behind it
is owed either way, since no field write transports the bundle definitionally.

Not definitional: three conjuncts fail `isDefEq` outright for structural
reasons (v0.32.151), which is why the write is routed through
`Architecture.proofLayerInvariantBundle_setDeclassificationRefusals` rather than
closed by `rfl`. -/
theorem recordSyscallRefusal_preserves_proofLayerInvariantBundle
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState)
    (hInv : SeLe4n.Kernel.Architecture.proofLayerInvariantBundle st) :
    SeLe4n.Kernel.Architecture.proofLayerInvariantBundle
      (recordSyscallRefusal ctx executingCore syscallId tid ke x0 st) := by
  obtain ⟨L, hEq⟩ :=
    recordSyscallRefusal_frame ctx executingCore syscallId tid ke x0 st
  rw [hEq]
  exact SeLe4n.Kernel.Architecture.proofLayerInvariantBundle_setDeclassificationRefusals st L hInv

/-- WS-SM SM9.B.9: the object store is untouched by a refusal write — the
frame the "an error stages no return frame" statement rides. -/
theorem recordSyscallRefusal_objects_eq
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState) :
    (recordSyscallRefusal ctx executingCore syscallId tid ke x0 st).objects = st.objects := by
  unfold recordSyscallRefusal
  split
  · rfl
  · split <;> rfl

/-- WS-SM SM9.B.9: the scheduler is untouched by a refusal write. -/
theorem recordSyscallRefusal_scheduler_eq
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState) :
    (recordSyscallRefusal ctx executingCore syscallId tid ke x0 st).scheduler = st.scheduler := by
  unfold recordSyscallRefusal
  split
  · rfl
  · split <;> rfl

/-- WS-SM SM9.B.9: the machine is untouched by a refusal write. -/
theorem recordSyscallRefusal_machine_eq
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState) :
    (recordSyscallRefusal ctx executingCore syscallId tid ke x0 st).machine = st.machine := by
  unfold recordSyscallRefusal
  split
  · rfl
  · split <;> rfl

/-- WS-SM SM9.B.9: **the refusal write stages no return frame.**

`readReturnFrame` reads the caller's TCB register file, and the refusal write
does not touch the object store — so the frame the boundary would hand back is
exactly the one the argument spill left, which is what keeps WS-RA's RA.B.4
contract ("an error stages nothing") true of the committed state. -/
theorem recordSyscallRefusal_readReturnFrame_eq
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState) (t : SeLe4n.ThreadId) :
    Architecture.readReturnFrame
        (recordSyscallRefusal ctx executingCore syscallId tid ke x0 st) t
      = Architecture.readReturnFrame st t := by
  unfold Architecture.readReturnFrame SystemState.getTcb?
  rw [recordSyscallRefusal_objects_eq]

/-- WS-SM SM9.B.9 (**the subject's domain is resolved by the dispatch's own
context**): two deployments that label the same subject differently record
different source domains for the identical refusal.

The seam-level half of `refusalRecord_domain_is_seam_resolved`.  Together they
are the argument for storing the domain rather than the subject id alone: the
context is an *argument* to this function, not persistent state, so nothing a
later reader can consult determines which domain the subject held when it was
refused. -/
theorem refusalRecord_domain_is_seam_resolved_at_seam
    (ctx₁ ctx₂ : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState) (sid : SyscallId)
    (hDecode : SyscallId.ofNat? syscallId.toNat = some sid)
    (hRecords : refusalSeamClass sid = .records)
    (hDiffer : ctx₁.threadLabelOf tid ≠ ctx₂.threadLabelOf tid)
    (r₁ r₂ : DeclassificationRefusal)
    (hRec₁ : (recordSyscallRefusal ctx₁ executingCore syscallId tid ke x0 st).declassificationRefusals.recent.get
      st.declassificationRefusals.nextSlot = some r₁)
    (hRec₂ : (recordSyscallRefusal ctx₂ executingCore syscallId tid ke x0 st).declassificationRefusals.recent.get
      st.declassificationRefusals.nextSlot = some r₂) :
    r₁.subjectDomain ≠ r₂.subjectDomain := by
  rw [recordSyscallRefusal_records ctx₁ executingCore syscallId tid ke x0 st sid hDecode hRecords,
      recordRefusal_writes_selected_slot] at hRec₁
  rw [recordSyscallRefusal_records ctx₂ executingCore syscallId tid ke x0 st sid hDecode hRecords,
      recordRefusal_writes_selected_slot] at hRec₂
  obtain rfl := Option.some.inj hRec₁
  obtain rfl := Option.some.inj hRec₂
  intro hEq
  apply hDiffer
  have h : unembedLegacyDomain (embedLegacyLabel (ctx₁.threadLabelOf tid))
      = unembedLegacyDomain (embedLegacyLabel (ctx₂.threadLabelOf tid)) :=
    congrArg unembedLegacyDomain hEq
  simpa using h

/-- WS-SM SM9.B.10 (**the ledger congruence**): the recorded ledger depends on
the pre-state through the ledger **and** — since WS-SM SM9.C.1 — through the
second-hop receiver resolution, and through nothing else.

Every other component of the record is built from this function's own
arguments.  The `hRecv` premise is the SM9.C.1 cost of naming the failed hop's
receiver: `refusedReceiver` is re-resolved from the pre-state
(`refusedSignalReceiver?`), so two states must agree on that resolution for
their recorded rows to agree — exactly the shape the declassification's own
event congruence carries as `hSameEvent`, and for the same reason (a recorded
field that reads the state is a field the congruence must constrain).  This is
what makes the refusal write a congruence for SM9.A.4a's observation relation —
the §3.7 obligation every writer of a readable structure owes. -/
theorem recordSyscallRefusal_ledger_congr
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (s₁ s₂ : SystemState)
    (h : s₁.declassificationRefusals = s₂.declassificationRefusals)
    (hRecv : refusedSignalReceiver? s₁ tid (SeLe4n.CPtr.ofNat x0.toNat)
      = refusedSignalReceiver? s₂ tid (SeLe4n.CPtr.ofNat x0.toNat)) :
    (recordSyscallRefusal ctx executingCore syscallId tid ke x0 s₁).declassificationRefusals
      = (recordSyscallRefusal ctx executingCore syscallId tid ke x0 s₂).declassificationRefusals := by
  cases hD : SyscallId.ofNat? syscallId.toNat with
  | none =>
      simp only [recordSyscallRefusal, hD]
      exact h
  | some sid =>
      have hFor : refusalReceiverFor s₁ tid sid ke x0 = refusalReceiverFor s₂ tid sid ke x0 := by
        unfold refusalReceiverFor
        split
        · exact hRecv
        · rfl
      cases hC : refusalSeamClass sid with
      | exempt =>
          simp only [recordSyscallRefusal, hD, hC]
          exact h
      | records =>
          rw [recordSyscallRefusal_records ctx executingCore syscallId tid ke x0 s₁ sid hD hC,
              recordSyscallRefusal_records ctx executingCore syscallId tid ke x0 s₂ sid hD hC,
              h, hFor]

/-- WS-SM SM9.B.9 (**the security theorem the plan names**): a refusal write
leaves the declassification **audit trail** and its epoch untouched.

The ledger is not the trail, and this is what stops an unprivileged caller from
turning refusals into a denial of service against authorized downgrades: the
trail's bound is fail-closed at `maxDeclassificationAuditEntries`, so a caller
able to append to it on refusal could exhaust those entries and deny every
subsequent *authorized* declassification.  It cannot, because refusals go to a
different structure. -/
theorem refusalWrite_declassificationAuditLog_eq
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState) :
    (recordSyscallRefusal ctx executingCore syscallId tid ke x0 st).declassificationAuditLog
      = st.declassificationAuditLog ∧
    (recordSyscallRefusal ctx executingCore syscallId tid ke x0 st).declassificationAuditEpoch
      = st.declassificationAuditEpoch := by
  unfold recordSyscallRefusal
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- WS-SM SM9.B.9 (**the trail's capacity is untouched, operationally**): after
any refusal write, an authorized downgrade is admitted exactly when it was
admitted before.

The consequence of `refusalWrite_declassificationAuditLog_eq` that a monitor
and an operator actually care about: refusals cannot consume the trail's
capacity, so no volume of refused attempts can push an authorized downgrade
into `.auditLogCapacityExceeded`. -/
theorem refusalWrite_cannot_exhaust_trail
    (ctx : LabelingContext) (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (st : SystemState) (e : DeclassificationEvent) :
    (recordDeclassificationChecked
        (SystemState.declassificationAuditLog
          (recordSyscallRefusal ctx executingCore syscallId tid ke x0 st)) e).isSome
      = (recordDeclassificationChecked st.declassificationAuditLog e).isSome := by
  rw [(refusalWrite_declassificationAuditLog_eq ctx executingCore syscallId tid ke x0 st).1]

/-- PR #887 review round 3: the trap frame's fault window as the SVC seam
carries it.  `x0`-`x5` are the syscall arguments the seam already spills,
`x6` the IPC-buffer word (`ipcBufferAddr` crosses as `x6` verbatim), `x7` the
syscall number, and `SP_EL0` / `x30` cross with the round's ABI extension —
the same nine registers the abort entry spills, so a capability fault's
context is built from what the thread held at the `SVC`, never from the
mirror's stale last-syscall contents. -/
def syscallWindow (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 x6 spEl0 x30 : UInt64) :
    FaultRegisterWindow :=
  { gprs := #[x0, x1, x2, x3, x4, x5, x6, syscallId.toUInt64], sp := spEl0, lr := x30 }

/-- seL4's `FaultIP` on the syscall path: the `SVC` instruction itself, one
instruction before the return address `ELR_EL1` holds, so a payload-free
handler reply restarts the thread by re-issuing the syscall
(`handleFaultReply`'s `CapFault` arm answers `Restart`). -/
def svcFaultIP (elr : UInt64) : UInt64 := elr - 4

/-- PR #887 review round 3: which syscalls answer a failed capability lookup
with a **capability fault**, and the `seL4_CapFault_InRecvPhase` flag each
carries; `none` returns the error instead.

seL4's rule is the syscall's blocking flag, not the object invoked.
`handleInvocation(isBlocking := true)` — `SysSend` and `SysCall`, hence every
object invocation libsel4 issues as a `seL4_Call`, and `seL4_Signal`, which
*is* `seL4_Send` — raises `CapFault` with the flag clear when the invoked
capability cannot be looked up; `handleRecv(isBlocking := true)` — `SysRecv`,
`SysWait`, `SysReplyRecv` — raises it with the flag set.  Only the
non-blocking forms (`NBSend`, `NBRecv`, `NBWait`) return the error, and this
model defines none of them.  Under MCS a reply is a `Send` on the reply
object, so `.reply` faults in the send phase as `.send` does.

The two syscalls that return their lookup failure are the declassifying
pair, for a reason this model owns rather than inherits: SM9.B attributes and
**records** their refusals in the refusal ledger (`refusalSeamClass` =
`.records`) so a monitor sees every refused downgrade attempt, and a fault
would move that refusal out of the ledger and into a handler's mailbox.  The
partition is therefore the ledger's, and it is pinned
(`capFaultReceivePhase?_none_iff_records`): a syscall returns its lookup
failure exactly when the seam records it.  Total, with no wildcard: a new
syscall decides its arm at elaboration, and the pin decides it against the
ledger. -/
def capFaultReceivePhase? : SyscallId → Option Bool
  | .send                   => some false
  | .receive                => some true
  | .call                   => some false
  | .reply                  => some false
  | .cspaceMint             => some false
  | .cspaceCopy             => some false
  | .cspaceMove             => some false
  | .cspaceDelete           => some false
  | .lifecycleRetype        => some false
  | .vspaceMap              => some false
  | .vspaceUnmap            => some false
  | .serviceRegister        => some false
  | .serviceRevoke          => some false
  | .serviceQuery           => some false
  | .notificationSignal     => some false
  | .notificationWait       => some true
  | .replyRecv              => some true
  | .schedContextConfigure  => some false
  | .schedContextBind       => some false
  | .schedContextUnbind     => some false
  | .tcbSuspend             => some false
  | .tcbResume              => some false
  | .tcbSetPriority         => some false
  | .tcbSetMCPriority       => some false
  | .tcbSetIPCBuffer        => some false
  | .tcbSetAffinity         => some false
  | .tcbBindNotification    => some false
  | .tcbUnbindNotification  => some false
  | .mintReplyCap           => some false
  | .vspaceUnifyInstruction => some false
  | .declassify             => none
  | .auditRead              => some false
  | .auditDrain             => some false
  | .declassifySignal       => none
  | .tcbSetFaultHandler     => some false

/-- The partition, pinned against the ledger rather than listed twice: a
syscall returns its lookup failure exactly when the refusal seam records it.
A third recording syscall, or a fault arm given to a declassifying one, fails
here. -/
theorem capFaultReceivePhase?_none_iff_records (sid : SyscallId) :
    (capFaultReceivePhase? sid).isNone = decide (refusalSeamClass sid = .records) := by
  cases sid <;> rfl

/-- PR #887 review round 3: **the capability-fault producer's decision.**
Given the refusal `ke` the checked dispatcher returned for the thread `tid`
on the argument-spilled state `st`, decide whether it was the syscall's
capability lookup that failed on a syscall that faults
(`capFaultReceivePhase?`) — and if so, the fault to deliver.

The decision re-runs the dispatcher's own prologue on the same state: decode
the arguments from the spilled registers, build the gate
`dispatchSyscallChecked` builds (the caller's CSpace root, the root's depth,
the syscall's required right), and run the **resolution half** of its lookup,
`syscallResolveCap`.  The fault is produced only when that resolution fails
**with the very error the dispatcher returned**: seL4 raises the `CapFault`
from `lookupCapAndSlot`, and a capability that resolved but lacks the right
(`syscallLookupCap`'s `.illegalAuthority`, seL4's `decodeInvocation` refusing
an endpoint capability without send) is a syscall *error*, as is every
arm-level refusal on a resolved capability (a wrong-kind target, a full
queue).  Matching on the error, not only on the arm, is what keeps a refusal
raised *before* the lookup — the insecure-context rejection, a decode
failure — from being delivered as a fault the CSpace did not raise.
`capAddress` is the CPtr that failed, `inReceivePhase` the syscall's flag,
and the resolution's `KernelError` rides as the reason, the model's
`lookup_fault_t`.

The prologue is mirrored rather than shared because the dispatcher runs its
lookup *inside* `syscallInvoke` and surfaces only the error; the state the
mirror reads is the argument-spilled one the dispatcher decoded from, and the
per-core TLB fill between the two touches no object
(`tlbFillIpcBufferOnCore_frame`), so the two resolutions agree.  What the
mirror does not re-run is a second lookup an arm performs after the first
succeeded — `.replyRecv`'s reply capability — so that failure returns the
error rather than faulting (seL4-MCS's `lookupReply` faults there);
registered debt, not a silent divergence. -/
def syscallCapFaultOf (layout : SeLe4n.SyscallRegisterLayout) (st : SystemState)
    (tid : SeLe4n.ThreadId) (ke : KernelError) : Option Fault :=
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
    match SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
        st tid layout tcb.registerContext 32 with
    | .error _ => none
    | .ok decoded =>
      match capFaultReceivePhase? decoded.syscallId with
      | none => none
      | some inRecv =>
        match st.objects[tcb.cspaceRoot]? with
        | some (.cnode rootCn) =>
          let gate : SyscallGate :=
            { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
              capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
          match syscallResolveCap gate st with
          | .error e =>
              if e = ke then some (.capFault (UInt64.ofNat decoded.capAddr.toNat) inRecv e)
              else none
          | .ok _ => none
        | _ => none
  | _ => none

/-- PR #887 review round 3: deliver a syscall-raised capability fault — the
abort entry's delivery, at the SVC seam: spill the trap frame's window, build
the context from the spilled file with the `SVC` instruction as the restart
PC, and run the flow-checked delivery on the executing core.  The result is
the committed state; the outcome is `.faulted` (tag 2), because the faulting
thread is now waiting on its handler, no frame exists for it, and — until
SM10.1 installs successors — the trap layer must halt rather than `eret` the
thread past the `SVC` the handler's reply will restart it at (PR #887 review
round 5). -/
def deliverSyscallCapFault (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (fault : Fault) (w : FaultRegisterWindow)
    (elr spsr : UInt64) : SystemState :=
  let stW := writeFaultRegistersToTcb st tid w
  let fctx := Architecture.faultContextOfThread stW tid (svcFaultIP elr) spsr
  (faultDeliverOnCoreChecked ctx stW tid fault fctx executingCore).1

/-- A refusal on a syscall that returns its lookup failure (the recorded
declassifying pair) produces no capability fault — one of the two discharges
for every theorem below that is stated on the error-frame arm. -/
theorem syscallCapFaultOf_none_of_no_fault_phase (layout : SeLe4n.SyscallRegisterLayout)
    (st : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError) (tcb : TCB)
    (decoded : SeLe4n.Model.SyscallDecodeResult)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
        st tid layout tcb.registerContext 32 = .ok decoded)
    (hNot : capFaultReceivePhase? decoded.syscallId = none) :
    syscallCapFaultOf layout st tid ke = none := by
  simp [syscallCapFaultOf, hTcb, hDec, hNot]

/-- …and neither does a refusal whose capability **resolved**: the fault is
the lookup's, never the invocation's — a resolved capability refused on
rights or by its arm returns the error. -/
theorem syscallCapFaultOf_none_of_resolve_ok (layout : SeLe4n.SyscallRegisterLayout)
    (st : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError) (tcb : TCB)
    (decoded : SeLe4n.Model.SyscallDecodeResult) (inRecv : Bool)
    (rootCn : CNode) (cap : Capability)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
        st tid layout tcb.registerContext 32 = .ok decoded)
    (hIpc : capFaultReceivePhase? decoded.syscallId = some inRecv)
    (hRoot : st.objects[tcb.cspaceRoot]? = some (.cnode rootCn))
    (hResolve : syscallResolveCap
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        st = .ok (cap, st)) :
    syscallCapFaultOf layout st tid ke = none := by
  simp [syscallCapFaultOf, hTcb, hDec, hIpc, hRoot, hResolve]

/-- WS-RC R2.B.1 (restated at the WS-RA type): the pure typed-ABI entry
    point behind the `lean_syscall_dispatch_cross_core` export
    (`Kernel/SyscallDispatchEntry.lean`).

Pipeline:
  1. Verify the FFI ABI invariant `msgInfo == x1` (both come from
     `frame.x1()` on the Rust side per
     `rust/sele4n-hal/src/svc_dispatch.rs::SyscallArgs::from_trap_frame`).
     A mismatch indicates a malformed FFI call and is rejected with
     `.invalidSyscallArgument`.
  2. Look up `(st.scheduler.currentOnCore executingCore)` (must be `some` on a real syscall).
  3. Spill the FFI register values into the current thread's TCB
     `registerContext` (matches the ARM64 trap handler's spill).
  4. Invoke `syscallEntryChecked` with the deployment's labeling
     context and the canonical `arm64DefaultLayout`.
  5. Hand back a `SyscallOutcome` (WS-RA, plan §3.1/§3.5): on success
     `syscallReturnOutcome` decides `blocks` from the caller's post-state
     or composes the shape-driven return frame; on failure a **computed**
     error frame carries the status label on `x1`
     (`Architecture.errorFrame`), staged into no TCB
     (`syscallDispatchFromAbi_error_stages_no_frame`).
  6. WS-SM SM9.B.9: on failure, additionally record the attributed refusal
     for the syscalls `refusalSeamClass` admits.  This is the *only* way the
     committed error state differs from the argument-spilled one, it is
     invisible to the caller and to every observer
     (`refusalLedger_write_is_caller_invisible`, `recordSyscallRefusal_frame`),
     and it preserves the bundle
     (`recordSyscallRefusal_preserves_proofLayerInvariantBundle`).
  7. PR #887 review round 3: on failure, when the refusal is the syscall's
     **failed capability lookup** (`syscallCapFaultOf`: the resolution the
     dispatcher's gate ran, on a syscall `capFaultReceivePhase?` names),
     deliver a `capFault` to the thread's fault handler instead of returning
     the error — seL4's `handleInvocation` / `handleRecv` — and hand back
     `.faulted` (outcome tag 2; PR #887 review round 5): a delivered fault,
     on which the trap layer halts pending SM10.1 as it does for an
     unknown-syscall delivery, never the `.blocks` sentinel that would
     resume the thread past the `SVC`.
     The trap frame's `ELR_EL1`, `SPSR_EL1`, `SP_EL0` and `x30` cross for
     this: the fault context is built from the spilled window
     (`syscallWindow`) with the `SVC` instruction as the restart PC
     (`svcFaultIP`), so a payload-free reply re-issues the syscall.

`ipcBufferAddr` is passed for parity with the seL4 ABI; the verified
kernel reads the IPC buffer from `tcb.ipcBuffer` (set by
`tcbSetIPCBuffer`) rather than from this argument, so it is unused
inside the dispatch.  A future refinement may cross-validate the two
when telemetry is added. -/
def syscallDispatchFromAbi
    (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 : UInt64)
    (ipcBufferAddr : UInt64)
    (elr spsr spEl0 x30 : UInt64) : Kernel Architecture.SyscallOutcome :=
  fun st =>
    -- ABI consistency check: the Rust caller guarantees
    -- `msg_info == msg_regs[1] == frame.x1()` when constructing the
    -- `SyscallArgs` struct.  If the Lean side observes a mismatch,
    -- the FFI boundary has been violated and we reject before
    -- touching kernel state.  Errors ride the x1 label as frames computed
    -- HERE, never staged into any TCB (WS-RA RA.B.4,
    -- `syscallDispatchFromAbi_error_stages_no_frame`).  The two pre-dispatch
    -- rejections below return the pre-state itself; the entry rejection
    -- returns the argument-spilled state plus the SM9.B refusal record,
    -- which is projection-invisible and bundle-preserving.
    if msgInfo != x1 then
      .ok (.returns (Architecture.errorFrame .invalidSyscallArgument), st)
    else
      -- WS-SM SM6.A: resolve the caller on the *executing* (trapping) core, not
      -- the boot core, so a secondary-core syscall acts on that core's current
      -- thread; the cross-core dispatch seam reads `executingCore` from the
      -- hardware (`currentCoreId`).
      match (st.scheduler.currentOnCore executingCore) with
      | none => .ok (.returns (Architecture.errorFrame .illegalState), st)
      | some tid =>
        let stRegs := writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5
        let layout := SeLe4n.arm64DefaultLayout
        match syscallEntryChecked ctx layout executingCore 32 stRegs with
        | .error ke =>
            match syscallCapFaultOf layout stRegs tid ke with
            | some fault =>
                -- PR #887 review round 3: a syscall whose capability lookup
                -- failed is **delivered**, not returned — seL4's
                -- `handleInvocation` / `handleRecv` `CapFault`.  The outcome
                -- is `.faulted` (tag 2): the thread now waits on its handler,
                -- no frame exists for it, and the trap layer halts rather
                -- than resumes it (PR #887 review round 5).
                .ok (.faulted,
                     deliverSyscallCapFault ctx executingCore stRegs tid fault
                       (syscallWindow syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr spEl0 x30)
                       elr spsr)
            | none =>
                -- WS-SM SM9.B.9: the refusal seam.  The outcome is the error
                -- frame computed from `ke` alone — bit-identical to what this
                -- arm returned before the ledger existed — and the committed
                -- state additionally carries the attributed refusal record, for
                -- the syscalls the total `refusalSeamClass` admits.
                -- `recordRefusal` is total, so this adds no failure mode the
                -- caller could observe (`refusalLedger_write_is_caller_invisible`),
                -- and it writes a different structure from the trail, so refusals
                -- can never exhaust the trail's fail-closed capacity
                -- (`refusalWrite_declassificationAuditLog_eq`).
                .ok (.returns (Architecture.errorFrame ke),
                     recordSyscallRefusal ctx executingCore syscallId tid ke x0 stRegs)
        | .ok ((), st') => .ok (syscallReturnOutcome syscallId st' tid, st')

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
      kernel state and return `0` (`KernelError::Ok`-equivalent slot).

    **WS-SM SM6.E**: the live Rust atomicity bracket
    (`sele4n_suspend_thread`) resolves the **cross-core** entry
    `suspend_thread_cross_core` (`SyscallDispatchEntry.suspendThreadCrossCoreEntry`,
    backed by the verified per-core `suspendThreadOnCore`: home-core
    deschedule + remote `.reschedule` SGI after the commit).

    **WS-RR RR5.17 — the `@[export]` is RETIRED; this is a Lean-side
    reference path, not a C symbol.**

    The body commits through `initialiseKernelState`, a bare
    `kernelStateRef.set`, with no kernel-entry bracket around the
    read-modify-write.  `kernel_entry.rs` acknowledged that and argued it was
    harmless because nothing on the trap path reached it — which was true of the
    HAL as it stood, and is not a property of the artefact: `@[export]` makes it
    a live C symbol in the linked image, so *any* future Rust caller would get an
    unserialised kernel-state write, and a lost suspend is a thread that keeps
    running after its caller was told it stopped.

    Two remediations were open (register §5 finding 9): bracket the body, or
    retire the export and keep the definition for the suites.  Retiring is the
    stronger one and the one with precedent in this file — WS-RA removed the
    twin `syscall_dispatch_inner` for the same reason, and the tombstone below
    keeps it gone.  It removes the hazard rather than mitigating it: there is no
    symbol for a future caller to reach, so no bracket can be forgotten.
    Bracketing would also have needed the Lean body to take the kernel-entry
    lock through new FFI, which the simulation build cannot link — the suites
    that exercise this definition run with no HAL.

    What remains is a **single-core reference path** with no production caller,
    exercised by `tests/SyscallDispatchSuite.lean` (SD-020..SD-023) as the
    boot-pinned counterpart of the live cross-core entry.  New code must not
    call it: the live suspend is `suspendThreadCrossCoreEntry`, whose Rust
    wrapper takes the kernel-entry bracket and consults the per-core readiness
    gate (RR5.7). -/
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

-- ============================================================================
-- WS-SM SM7.D.1 — Instruction-cache maintenance broadcast
-- ============================================================================

/-- **WS-SM SM7.D.1**: broadcast I-cache invalidate-all witness —
    `IC IALLUIS` + `DSB ISH` + `ISB`, dropping every instruction-cache line on
    **every** PE of the Inner Shareable domain.

    The broadcast counterpart of `ffiIcIallu`.  The Lean model's
    `icInvalidateBroadcast … .iallu` is what this emits.

    Rust: `cache::ic_invalidate_all_inner_shareable` in
    `sele4n-hal/src/cache.rs`. -/
@[extern "cache_ic_ialluis"]
opaque ffiIcIalluIs : BaseIO Unit

/-- **WS-SM SM7.D.1**: typed instruction-cache maintenance dispatcher.

    Takes the `(opTag, addr, size)` encoding of an
    `Architecture.ICacheInvalidation` and emits the corresponding broadcast
    maintenance instruction plus its completing barriers:

      opTag : 0 = Iallu (`IC IALLUIS`), 1 = IvauPage (per-page `IC IVAU` loop),
              2 = UnifyPage (`DC CVAU` loop → `DSB` → `IC IVAU` loop → `DSB` → `ISB`),
              3 = CleanRangeIallu (`DC CVAU` loop over `[addr, addr+size)` →
                  `DSB` → `IC IALLUIS` → `DSB` → `ISB`)
      addr  : page base virtual address operand, or the range base for tag 3
              (RES0 for Iallu)
      size  : range length in bytes (tag 3 only; RES0 otherwise)

    The encoding is pinned to the Lean side by
    `ICacheInvalidation.toOpTag` / `.toPaddr` / `.toSize` and to the Rust side by
    `cache::decode_icache_invalidation`; the dispatcher **panics** on an
    out-of-range tag (fail closed — a silently skipped invalidation is a
    correctness violation the caller cannot detect), which
    `ICacheInvalidation.toOpTag_in_range` proves unreachable from any
    well-formed Lean caller.

    Tag 2 (`unifyPage`) is the `.vspaceUnifyInstruction` syscall's operand — the
    full ARMv8-A data-to-instruction sequence, whose *inter-loop* `DSB ISH`
    matters: the invalidations must not be observed before the cleans complete,
    or a PE could re-fill an instruction line from the pre-clean PoU content.

    Tag 3 (`cleanRangeIallu`) is the `.lifecycleRetype` operand, and carries the
    same inter-loop ordering for the same reason — with a caller-supplied extent
    (the scrubbed region) and a domain-wide invalidate, because a re-type cannot
    name the mappings that alias the frame it re-purposes.

    Rust: `ffi::cache_ic_maintenance` in `sele4n-hal/src/ffi.rs`. -/
@[extern "cache_ic_maintenance"]
opaque ffiIcMaintenance : UInt32 → UInt64 → UInt64 → BaseIO Unit

/-- **WS-SM SM7.D.1**: typed wrapper over `ffiIcMaintenance` — emit the
    inner-shareable broadcast maintenance for a typed operand.

    The bridge between the SM7.D model (`icInvalidateBroadcast`, which evolves
    every core's `perCoreICache` view) and the hardware: the model says which
    lines disappear on which cores, this call makes it so.

    For `.ivauPage p` the operand passed to the HAL is the page's **base
    address**: the `IC IVAU` instruction takes a *virtual* address and the PE
    translates it, and the boot tables identity-map RAM, so a RAM frame's kernel
    VA equals its PA and `ICacheInvalidation.toPaddr` is the correct operand.
    Note the granularity expansion — `IC IVAU` invalidates one 64-byte cache
    line, so the HAL issues `icacheLinesPerPage` of them for one page operand
    (`cache::ic_invalidate_page_inner_shareable`), exactly as seL4's
    `invalidateCacheRange_I` does.

    `.unifyPage p` uses the same operand under the same identity-map argument,
    and routes to `cache::unify_instruction_page_inner_shareable`: a `DC CVAU`
    loop over the page, `DSB ISH`, the `IC IVAU` loop, `DSB ISH`, `ISB`.  It is
    a *distinct* op tag rather than a stronger `.ivauPage` because the clean to
    the Point of Unification has no counterpart in the invalidation dimension —
    which is also why the emission ledger keeps it under a coverage preorder
    instead of a join (`ICacheInvalidation.iallu_not_covers_unifyPage`).

    `.cleanRangeIallu b s` passes `b` as the address and `s` as the length, and
    routes to `cache::clean_range_pou_then_invalidate_all_inner_shareable`.  It
    is the re-type's operand: `IC IALLUIS` alone would drop the stale
    instruction lines but leave the scrub's zeroing stores in the data cache, so
    the very next fetch would re-fill from the pre-scrub Point-of-Unification
    content — the previous owner's code.  The `DC CVAU` loop is what closes
    that, and bundling it into one operand is what keeps the ordering out of the
    ledger's accumulation order
    (`ICacheInvalidation.iallu_not_covers_cleanRangeIallu`). -/
def icMaintenanceBroadcast
    (op : SeLe4n.Kernel.Architecture.ICacheInvalidation) : BaseIO Unit :=
  ffiIcMaintenance op.toOpTag op.toPaddr op.toSize

/-- **WS-SM SM7.D.1**: the invalidate-all operand routes to op tag 0. -/
theorem icMaintenanceBroadcast_iallu_encoding :
    (SeLe4n.Kernel.Architecture.ICacheInvalidation.iallu).toOpTag = 0 ∧
    (SeLe4n.Kernel.Architecture.ICacheInvalidation.iallu).toPaddr = 0 :=
  ⟨rfl, rfl⟩

/-- **WS-SM SM7.D.1**: the per-page operand routes to op tag 1 carrying the
    page base address. -/
theorem icMaintenanceBroadcast_ivauPage_encoding (p : SeLe4n.PAddr) :
    (SeLe4n.Kernel.Architecture.ICacheInvalidation.ivauPage p).toOpTag = 1 ∧
    (SeLe4n.Kernel.Architecture.ICacheInvalidation.ivauPage p).toPaddr =
      UInt64.ofNat p.toNat :=
  ⟨rfl, rfl⟩

/-- **WS-SM SM7.D**: the re-type's range operand routes to op tag 3 carrying
    the scrubbed extent's base **and length** — the only operand for which the
    HAL reads the third word. -/
theorem icMaintenanceBroadcast_cleanRangeIallu_encoding
    (b : SeLe4n.PAddr) (s : Nat) :
    (SeLe4n.Kernel.Architecture.ICacheInvalidation.cleanRangeIallu b s).toOpTag = 3 ∧
    (SeLe4n.Kernel.Architecture.ICacheInvalidation.cleanRangeIallu b s).toPaddr =
      UInt64.ofNat b.toNat ∧
    (SeLe4n.Kernel.Architecture.ICacheInvalidation.cleanRangeIallu b s).toSize =
      UInt64.ofNat s :=
  ⟨rfl, rfl, rfl⟩


-- ============================================================================
-- WS-RA: the vestigial `syscall_dispatch_inner` export is REMOVED
-- ============================================================================
--
-- `syscallDispatchInner` was the boot-pinned single-core BaseIO wrapper
-- around `syscallDispatchFromAbi`, exported as `syscall_dispatch_inner`.
-- The Rust `svc_dispatch` extern was flipped to
-- `lean_syscall_dispatch_cross_core` at v0.31.67 (SM6.A), no Rust source
-- declared the symbol since, and it was the last production consumer of the
-- retired bit-63 protocol (`encodeOk` / `encodeError`).  Its planned SM10.1
-- removal moved into the WS-RA flip: a dead export still speaking a retired
-- protocol is a half-migrated artifact (plan §3.7).
-- `tests/SyscallDispatchSuite.lean`'s bridge coverage now drives the pure
-- `syscallDispatchFromAbi` plus the IO.Ref bootstrap directly.

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

    **Local (non-broadcast) variant** — it reaches only the executing PE.
    WS-SM SM7.D.1: production kernel code under SMP must use
    `icMaintenanceBroadcast` below, which routes to the Inner Shareable
    broadcast variants; this binding is kept for the single-PE boot path,
    symmetric with `ffiTlbiAll`.

    Rust: `cache::ic_iallu` in `sele4n-hal/src/cache.rs`. -/
@[extern "cache_ic_iallu"]
opaque ffiIcIallu : BaseIO Unit

-- ============================================================================
-- WS-RC R2.B.5 — Correctness theorems for the syscall-dispatch bridge
-- ============================================================================

/-- WS-RC R2.B.5 (restated at the WS-RA type): The pure typed-ABI entry
    point never returns `Except.error` — every kernel rejection is a
    success-shaped `(SyscallOutcome, state)` pair whose outcome carries
    the error on the `x1` label (`Architecture.errorFrame`).  This is the
    structural witness that the export wrapper's `Except.error` arm is
    vacuous.

The proof unfolds `syscallDispatchFromAbi` and case-splits on the
scheduler's `current` slot and on the `syscallEntryChecked` result;
every branch produces an `.ok` value. -/
theorem syscallDispatchFromAbi_total
    (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState) :
    ∃ (outcome : Architecture.SyscallOutcome) (st' : SystemState),
      syscallDispatchFromAbi ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st
        = Except.ok (outcome, st') := by
  unfold syscallDispatchFromAbi
  -- The function first checks the ABI invariant `msgInfo == x1`,
  -- then case-splits on `(st.scheduler.currentOnCore executingCore)`, then on the
  -- `syscallEntryChecked` result.  Every branch produces `.ok`.
  by_cases hMsg : msgInfo != x1
  · -- ABI mismatch path: an error frame on the pre-state.
    exact ⟨.returns (Architecture.errorFrame .invalidSyscallArgument), st, by simp [hMsg]⟩
  · -- ABI consistency holds: drive the if-then-else into the else branch
    -- using `hMsg` so the goal exposes the next match.
    cases (st.scheduler.currentOnCore executingCore) with
    | none =>
        exact ⟨.returns (Architecture.errorFrame .illegalState), st, by simp [hMsg]⟩
    | some tid =>
        cases hSyscall : syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32
                (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) with
        | error ke =>
            cases hCap : syscallCapFaultOf SeLe4n.arm64DefaultLayout
                (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid ke with
            | some fault =>
                exact ⟨.faulted,
                       deliverSyscallCapFault ctx executingCore
                         (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid fault
                         (syscallWindow syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr spEl0 x30)
                         elr spsr,
                       by simp [hMsg, hSyscall, hCap]⟩
            | none =>
                exact ⟨.returns (Architecture.errorFrame ke),
                       recordSyscallRefusal ctx executingCore syscallId tid ke x0
                         (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5),
                       by simp [hMsg, hSyscall, hCap]⟩
        | ok r =>
            obtain ⟨_, st'⟩ := r
            exact ⟨syscallReturnOutcome syscallId st' tid, st',
                   by simp [hMsg, hSyscall]⟩

/-- WS-RC R2.B.5 (restated at the WS-RA type): When `syscallEntryChecked`
    succeeds on the register-spilled state, `syscallDispatchFromAbi`
    returns `(syscallReturnOutcome syscallId st' tid, st')` — the outcome
    decided from the caller's post-state (blocked ⇒ `.blocks`; returning
    ⇒ the shape-driven frame composition).

Together with the `total` theorem above, it pins the bridge's behaviour:
no bypass, no shortcut, the verified `syscallEntryChecked` is the sole
source of success outcomes. -/
theorem syscallDispatchFromAbi_ok_of_syscallEntryChecked_ok
    (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore executingCore) = some tid)
    (hSyscall :
      syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
        = Except.ok ((), st')) :
    syscallDispatchFromAbi ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st
      = Except.ok (syscallReturnOutcome syscallId st' tid, st') := by
  unfold syscallDispatchFromAbi
  simp [hMsg, hCur, hSyscall]

/-- WS-RC R2.B.5 (restated at the WS-RA type, and again at SM9.B.9): when
    `syscallEntryChecked` rejects on the register-spilled state,
    `syscallDispatchFromAbi` propagates the error as a **computed** error
    frame — the status label on `x1` — over the post-spill `SystemState`
    **with the SM9.B refusal record applied**.

WS-RA RA.B.4's content survives the ledger: an error still stages nothing into
any TCB (`syscallDispatchFromAbi_error_stages_no_frame`, whose second conjunct
is exactly that), which is what keeps `syscallEntry_error_perCore_NI` and
`syscallEntry_error_preserves_proofLayerInvariantBundle` trivially true — both
are statements about `syscallEntryChecked`, whose error arm carries no
post-state at all.  What the ledger adds is confined to one `SystemState`
field: `recordSyscallRefusal_frame` names it, and the projection, machine,
scheduler, object-store and bundle frames say what it costs (nothing). -/
theorem syscallDispatchFromAbi_error_of_syscallEntryChecked_error
    (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore executingCore) = some tid)
    (hSyscall :
      syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
        = Except.error ke)
    (hNoCapFault : syscallCapFaultOf SeLe4n.arm64DefaultLayout
        (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid ke = none) :
    syscallDispatchFromAbi ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st
      = Except.ok (.returns (Architecture.errorFrame ke),
                   recordSyscallRefusal ctx executingCore syscallId tid ke x0
                     (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)) := by
  unfold syscallDispatchFromAbi
  simp [hMsg, hCur, hSyscall, hNoCapFault]

/-- PR #887 review round 3 (**the capability-fault arm**): when the checked
dispatcher refuses and the refusal is the syscall's failed capability
lookup, the seam **delivers** the fault — the outcome is
`.faulted` (tag 2, PR #887 review round 5) and the committed state is the
delivery on the executing core, built from the trap frame's window with the
`SVC` instruction as the restart PC.  The error-frame theorems above are
stated on the complementary arm (`hNoCapFault`); together the two cover the
refusal path. -/
theorem syscallDispatchFromAbi_capFault_faulted
    (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError) (fault : Fault)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore executingCore) = some tid)
    (hSyscall :
      syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
        = Except.error ke)
    (hCap : syscallCapFaultOf SeLe4n.arm64DefaultLayout
        (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid ke = some fault) :
    syscallDispatchFromAbi ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr
        elr spsr spEl0 x30 st
      = Except.ok (.faulted,
          deliverSyscallCapFault ctx executingCore
            (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid fault
            (syscallWindow syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr spEl0 x30) elr spsr) := by
  unfold syscallDispatchFromAbi
  simp [hMsg, hCur, hSyscall, hCap]

/-- WS-RA RA.B.4 (`syscallDispatchFromAbi_error_stages_no_frame`): on
every error arm the returned state carries **no return-frame write**.  The
error frame exists only in the returned *outcome*, computed at the boundary
from the `KernelError` (`Architecture.errorFrame`), never staged.

**Restated at SM9.B.9, and deliberately not weakened.**  The two pre-dispatch
rejections still return the pre-state itself; an entry rejection now returns
the argument-spilled state *plus* the attributed refusal record, so "returns
exactly the spilled state" would be false.  The property that mattered is not
state identity but that no TCB's return frame moved, and that is now the second
conjunct — `readReturnFrame` at the caller is literally unchanged across the
ledger write.  Stating it that way keeps the theorem true of the transition the
boundary actually runs, rather than of one it no longer performs. -/
theorem syscallDispatchFromAbi_error_stages_no_frame
    (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore executingCore) = some tid)
    (hSyscall :
      syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
        = Except.error ke)
    (hNoCapFault : syscallCapFaultOf SeLe4n.arm64DefaultLayout
        (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid ke = none) :
    (syscallDispatchFromAbi ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5
        ipcBufferAddr elr spsr spEl0 x30 st).map (·.2)
      = Except.ok (recordSyscallRefusal ctx executingCore syscallId tid ke x0
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)) ∧
    Architecture.readReturnFrame
        (recordSyscallRefusal ctx executingCore syscallId tid ke x0
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)) tid
      = Architecture.readReturnFrame
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid := by
  refine ⟨?_, recordSyscallRefusal_readReturnFrame_eq ctx executingCore syscallId tid ke x0 _ tid⟩
  rw [syscallDispatchFromAbi_error_of_syscallEntryChecked_error ctx executingCore
    syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st tid ke hMsg hCur hSyscall hNoCapFault]
  rfl

/-- WS-SM SM9.B.9 (**the caller learns exactly what it learned before**): on
the refusal arm the outcome handed back is the error frame computed from `ke`
alone — it mentions neither the ledger nor its occupancy.

This is the acceptance item the plan states as *"no distinguishable record of
the `auditLogCapacityExceeded` reason"* for the caller.  The record **does**
carry that reason, because it is the only durable evidence that an authorized
downgrade hit the trail's capacity bound and a monitor needs it; what must not
happen is that the *refused caller* can resolve it, and it cannot: the outcome
is `Architecture.errorFrame ke`, exactly as before the ledger existed, and
`recordRefusal` is total so the ledger contributes no error of its own.  The
occupancy channel is therefore closed by the ledger's read gate rather than by
discarding the evidence. -/
theorem refusalLedger_write_is_caller_invisible
    (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore executingCore) = some tid)
    (hSyscall :
      syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
        = Except.error ke)
    (hNoCapFault : syscallCapFaultOf SeLe4n.arm64DefaultLayout
        (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid ke = none) :
    (syscallDispatchFromAbi ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5
        ipcBufferAddr elr spsr spEl0 x30 st).map (·.1)
      = Except.ok (.returns (Architecture.errorFrame ke)) := by
  rw [syscallDispatchFromAbi_error_of_syscallEntryChecked_error ctx executingCore
    syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st tid ke hMsg hCur hSyscall hNoCapFault]
  rfl

/-- WS-SM SM9.B.9 (**the seam records, end to end**): a refused declassification
lands an attributed record in the committed state's ledger.

Stated at the boundary rather than at `recordSyscallRefusal`, because the
boundary is what the hardware calls: the composition of "the error arm commits a
state" with "that state carries the record" is the property SM8.C's registered
gap said could not be had. -/
theorem syscallDispatchFromAbi_records_refusal
    (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError) (sid : SyscallId)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore executingCore) = some tid)
    (hDecode : SyscallId.ofNat? syscallId.toNat = some sid)
    (hRecords : refusalSeamClass sid = .records)
    (hSyscall :
      syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
        = Except.error ke)
    (hNoCapFault : syscallCapFaultOf SeLe4n.arm64DefaultLayout
        (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid ke = none) :
    ∃ post : SystemState,
      (syscallDispatchFromAbi ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5
        ipcBufferAddr elr spsr spEl0 x30 st).map (·.2) = Except.ok post ∧
      post.declassificationRefusals.recent.get
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4
            x5).declassificationRefusals.nextSlot
        = some { originatingCore := executingCore
                 subject := tid
                 subjectDomain := (liftLegacyContext ctx).threadDomainOf tid
                 syscall := sid
                 reason := ke
                 requestedTarget := SeLe4n.CPtr.ofNat x0.toNat
                 refusedReceiver := refusalReceiverFor
                   (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
                   tid sid ke x0 } := by
  refine ⟨recordSyscallRefusal ctx executingCore syscallId tid ke x0
      (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5), ?_, ?_⟩
  · rw [syscallDispatchFromAbi_error_of_syscallEntryChecked_error ctx executingCore
      syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st tid ke hMsg hCur hSyscall hNoCapFault]
    rfl
  · rw [recordSyscallRefusal_records ctx executingCore syscallId tid ke x0 _ sid hDecode hRecords]
    exact recordRefusal_writes_selected_slot _ _

/-- WS-SM SM9.B.9 (**the load-bearing negative**): a refused *exempt* syscall
leaves the ledger exactly as it was.

Without it the ledger would be a general syscall-failure log, which is not what
the plan scopes and not what the ring is sized for: ordinary refusals — a
`.send` to a full endpoint queue, a bad capability — would evict the policy
exceptions a monitor is looking for, and any subject could clear the evidence
by issuing 32 failing syscalls. -/
theorem syscallDispatchFromAbi_exempt_refusal_frames_ledger
    (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError) (sid : SyscallId)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore executingCore) = some tid)
    (hDecode : SyscallId.ofNat? syscallId.toNat = some sid)
    (hExempt : refusalSeamClass sid = .exempt)
    (hSyscall :
      syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32
          (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
        = Except.error ke)
    (hNoCapFault : syscallCapFaultOf SeLe4n.arm64DefaultLayout
        (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid ke = none) :
    (syscallDispatchFromAbi ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5
        ipcBufferAddr elr spsr spEl0 x30 st).map (·.2)
      = Except.ok (writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
  rw [syscallDispatchFromAbi_error_of_syscallEntryChecked_error ctx executingCore
    syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st tid ke hMsg hCur hSyscall hNoCapFault,
    recordSyscallRefusal_exempt ctx executingCore syscallId tid ke x0 _ sid hDecode hExempt]
  rfl

/-- WS-RC R2.B.5: When the scheduler has no current thread, the FFI
    surfaces `.illegalState` without invoking `syscallEntryChecked`.

This is the FFI's defence against being called outside a syscall
context (e.g., during early boot before the scheduler has elected a
thread).  No state is mutated. -/
theorem syscallDispatchFromAbi_illegalState_when_no_current
    (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore executingCore) = none) :
    syscallDispatchFromAbi ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st
      = Except.ok (.returns (Architecture.errorFrame .illegalState), st) := by
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
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState)
    (hMsg : msgInfo ≠ x1) :
    syscallDispatchFromAbi ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st
      = Except.ok (.returns (Architecture.errorFrame .invalidSyscallArgument), st) := by
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
    | reply _ => rfl

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
    | reply _ => rfl

end SeLe4n.Platform.FFI
