-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Platform.FFI
import SeLe4n.Testing.StateBuilder
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.InformationFlow.Policy

/-!
# WS-RC R2.C — Hardware syscall dispatch regression suite

DEEP-TEST-03 closure.  This suite exercises the FFI bridge that
WS-RC R2 wires through `syscallEntryChecked`:

- `KernelError → UInt32` discriminant table mirrors
  `rust/sele4n-types/src/error.rs` exactly.
- `encodeError` always sets bit 63 of the encoded `UInt64`.
- `encodeOk` always clears bit 63 of the encoded `UInt64`.
- `bootAndInitialiseFromPlatform` installs the post-boot
  `SystemState` into `kernelStateRef`; subsequent
  `getKernelState` reads observe it.
- `suspendThreadInner` bridges the FFI `tid : UInt64` argument
  through to `Kernel.Lifecycle.Suspend.suspendThread` via the
  IO.Ref and returns the encoded `KernelError` discriminant.
- `syscallDispatchInner` bridges the FFI register-passing
  signature through to `syscallDispatchFromAbi` via the IO.Ref
  and returns the encoded `UInt64` per the high-bit-error
  contract.

Each test produces a single `[PASS]` / `[FAIL]` line; the executable
exits non-zero if any test fails.  Wired into `test_tier2_negative.sh`
and the Tier-3 invariant-surface anchor checker.
-/

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Platform.FFI

namespace SeLe4n.Testing.SyscallDispatchSuite

private def passLine (name : String) : IO Unit :=
  IO.println s!"[PASS] {name}"

private def failLine (name : String) (reason : String) : IO Unit := do
  IO.eprintln s!"[FAIL] {name}: {reason}"
  IO.Process.exit 1

private def expect (name : String) (cond : Bool) (reason : String) : IO Unit :=
  if cond then passLine name else failLine name reason

private def mkTcb (tid : Nat) (state : ThreadState := .Ready)
    (prio : Nat := 10) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩,
    cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0),
    threadState := state }

private def mkState (objs : List (ObjId × KernelObject))
    (current : Option SeLe4n.ThreadId := none) : SystemState :=
  let builder : SeLe4n.Testing.BootstrapBuilder := {
    objects := objs
    current := current
  }
  builder.buildChecked

-- ============================================================================
-- R2.B.0 — KernelError ↔ UInt32 round-trip and Rust contract checks
-- ============================================================================

/-- SD-001: `KernelError.toUInt32` matches the Rust enum's discriminants.

Pins ALL 52 variants (0..51) explicitly so a regression that
re-orders the Lean `inductive KernelError` or the `toUInt32` arms
silently is caught here.  The Rust side's
`from_u32_roundtrip` test pins the Rust enum self-consistency; this
test is the cross-language pin against
`rust/sele4n-types/src/error.rs::KernelError`. -/
private def sd001_kernelErrorDiscriminants : IO Unit := do
  let pin (name : String) (e : KernelError) (expected : UInt32) : IO Unit :=
    expect name
      (KernelError.toUInt32 e == expected)
      s!"{name}: expected {expected}, got {KernelError.toUInt32 e}"
  pin "sd001_00_invalidCapability"            .invalidCapability             0
  pin "sd001_01_objectNotFound"               .objectNotFound                1
  pin "sd001_02_illegalState"                 .illegalState                  2
  pin "sd001_03_illegalAuthority"             .illegalAuthority              3
  pin "sd001_04_policyDenied"                 .policyDenied                  4
  pin "sd001_05_dependencyViolation"          .dependencyViolation           5
  pin "sd001_06_schedulerInvariantViolation"  .schedulerInvariantViolation   6
  pin "sd001_07_endpointStateMismatch"        .endpointStateMismatch         7
  pin "sd001_08_endpointQueueEmpty"           .endpointQueueEmpty            8
  pin "sd001_09_asidNotBound"                 .asidNotBound                  9
  pin "sd001_10_vspaceRootInvalid"            .vspaceRootInvalid            10
  pin "sd001_11_mappingConflict"              .mappingConflict              11
  pin "sd001_12_translationFault"             .translationFault             12
  pin "sd001_13_flowDenied"                   .flowDenied                   13
  pin "sd001_14_declassificationDenied"       .declassificationDenied       14
  pin "sd001_15_alreadyWaiting"               .alreadyWaiting               15
  pin "sd001_16_cyclicDependency"             .cyclicDependency             16
  pin "sd001_17_notImplemented"               .notImplemented               17
  pin "sd001_18_targetSlotOccupied"           .targetSlotOccupied           18
  pin "sd001_19_replyCapInvalid"              .replyCapInvalid              19
  pin "sd001_20_untypedRegionExhausted"       .untypedRegionExhausted       20
  pin "sd001_21_untypedTypeMismatch"          .untypedTypeMismatch          21
  pin "sd001_22_untypedDeviceRestriction"     .untypedDeviceRestriction     22
  pin "sd001_23_untypedAllocSizeTooSmall"     .untypedAllocSizeTooSmall     23
  pin "sd001_24_childIdSelfOverwrite"         .childIdSelfOverwrite         24
  pin "sd001_25_childIdCollision"             .childIdCollision             25
  pin "sd001_26_addressOutOfBounds"           .addressOutOfBounds           26
  pin "sd001_27_ipcMessageTooLarge"           .ipcMessageTooLarge           27
  pin "sd001_28_ipcMessageTooManyCaps"        .ipcMessageTooManyCaps        28
  pin "sd001_29_backingObjectMissing"         .backingObjectMissing         29
  pin "sd001_30_invalidRegister"              .invalidRegister              30
  pin "sd001_31_invalidSyscallNumber"         .invalidSyscallNumber         31
  pin "sd001_32_invalidMessageInfo"           .invalidMessageInfo           32
  pin "sd001_33_invalidTypeTag"               .invalidTypeTag               33
  pin "sd001_34_resourceExhausted"            .resourceExhausted            34
  pin "sd001_35_invalidCapPtr"                .invalidCapPtr                35
  pin "sd001_36_objectStoreCapacityExceeded"  .objectStoreCapacityExceeded  36
  pin "sd001_37_allocationMisaligned"         .allocationMisaligned         37
  pin "sd001_38_revocationRequired"           .revocationRequired           38
  pin "sd001_39_invalidArgument"              .invalidArgument              39
  pin "sd001_40_mmioUnaligned"                .mmioUnaligned                40
  pin "sd001_41_invalidSyscallArgument"       .invalidSyscallArgument       41
  pin "sd001_42_ipcTimeout"                   .ipcTimeout                   42
  pin "sd001_43_alignmentError"               .alignmentError               43
  pin "sd001_44_vmFault"                      .vmFault                      44
  pin "sd001_45_userException"                .userException                45
  pin "sd001_46_hardwareFault"                .hardwareFault                46
  pin "sd001_47_notSupported"                 .notSupported                 47
  pin "sd001_48_invalidIrq"                   .invalidIrq                   48
  pin "sd001_49_invalidObjectType"            .invalidObjectType            49
  pin "sd001_50_nullCapability"               .nullCapability               50
  pin "sd001_51_partialResolution"            .partialResolution            51

/-- SD-002: `encodeError` sets bit 63 for every variant AND embeds
    the discriminant in the low 32 bits.

The runtime check exercises every one of the 52 `KernelError`
variants exactly once.  The structural witness for "bit 63 set" lives
at `SeLe4n.Platform.FFI.encodeError_high_bit_set` in `FFI.lean`. -/
private def sd002_encodeError : IO Unit := do
  let variants : List KernelError :=
    [ .invalidCapability, .objectNotFound, .illegalState
    , .illegalAuthority, .policyDenied, .dependencyViolation
    , .schedulerInvariantViolation, .endpointStateMismatch
    , .endpointQueueEmpty, .asidNotBound, .vspaceRootInvalid
    , .mappingConflict, .translationFault, .flowDenied
    , .declassificationDenied, .alreadyWaiting, .cyclicDependency
    , .notImplemented, .targetSlotOccupied, .replyCapInvalid
    , .untypedRegionExhausted, .untypedTypeMismatch
    , .untypedDeviceRestriction, .untypedAllocSizeTooSmall
    , .childIdSelfOverwrite, .childIdCollision, .addressOutOfBounds
    , .ipcMessageTooLarge, .ipcMessageTooManyCaps
    , .backingObjectMissing, .invalidRegister, .invalidSyscallNumber
    , .invalidMessageInfo, .invalidTypeTag, .resourceExhausted
    , .invalidCapPtr, .objectStoreCapacityExceeded
    , .allocationMisaligned, .revocationRequired, .invalidArgument
    , .mmioUnaligned, .invalidSyscallArgument, .ipcTimeout
    , .alignmentError, .vmFault, .userException, .hardwareFault
    , .notSupported, .invalidIrq, .invalidObjectType
    , .nullCapability, .partialResolution ]
  -- Pin variant count: matches the Lean inductive (52 variants 0..51).
  expect "sd002_variant_count_is_52"
    (variants.length == 52)
    s!"variants list should have 52 entries, got {variants.length}"
  for v in variants do
    let encoded := encodeError v
    -- Phase A: bit 63 is set.
    let highBitSet := (encoded >>> 63) &&& 1 == 1
    expect s!"sd002a_high_bit_set_{repr v}"
      highBitSet
      s!"encodeError {repr v} must have bit 63 set"
    -- Phase B: low 32 bits equal the toUInt32 discriminant.
    let lowDisc : UInt32 := (encoded.toNat % (2 ^ 32)).toUInt32
    expect s!"sd002b_disc_matches_{repr v}"
      (lowDisc == KernelError.toUInt32 v)
      s!"encodeError {repr v}: low 32 bits ({lowDisc}) must equal toUInt32 ({KernelError.toUInt32 v})"

/-- SD-003: `encodeOk` clears bit 63 for representative success
    values, AND preserves the low 63 bits when bit 63 was already 0.

The masking is the FFI-level implementation of the bit-63=error-flag
contract: the kernel's "successful return value" must fit in 63 bits.
For values < 2^63, encoding must be the identity.  For values ≥ 2^63,
encoding silently strips bit 63 (a documented FFI ABI constraint;
practical syscalls never return values ≥ 2^63). -/
private def sd003_encodeOk : IO Unit := do
  -- Phase A: bit 63 is clear for all inputs.
  let values : List UInt64 :=
    [ 0, 1, 42, 0xFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF ]
  for v in values do
    let encoded := encodeOk v
    let highBitSet := (encoded >>> 63) &&& 1 == 1
    expect s!"sd003a_high_bit_clear_{v}"
      (¬ highBitSet)
      s!"encodeOk {v} must have bit 63 clear"
  -- Phase B: identity preservation for inputs whose bit 63 is 0.
  let inRangeValues : List UInt64 :=
    [ 0, 1, 42, 0xFFFFFFFF, 0x7FFFFFFFFFFFFFFF ]
  for v in inRangeValues do
    expect s!"sd003b_identity_when_high_bit_clear_{v}"
      (encodeOk v == v)
      s!"encodeOk {v} must equal {v} when bit 63 is already clear"
  -- Phase C: bit-63 stripping for inputs whose bit 63 is 1.
  expect "sd003c_strips_bit_63_for_max"
    (encodeOk 0xFFFFFFFFFFFFFFFF == 0x7FFFFFFFFFFFFFFF)
    "encodeOk 0xFFFF...FFFF must equal 0x7FFF...FFFF (bit 63 stripped)"
  expect "sd003d_strips_bit_63_for_high_only"
    (encodeOk 0x8000000000000000 == 0)
    "encodeOk 0x8000...0000 must equal 0 (bit 63 stripped, low bits 0)"
  expect "sd003e_strips_bit_63_preserves_low"
    (encodeOk 0x8000000000000042 == 0x42)
    "encodeOk 0x8000...0042 must equal 0x42 (bit 63 stripped, low bits preserved)"

-- ============================================================================
-- R2.A — Kernel-state IO.Ref bootstrap path
-- ============================================================================

/-- SD-010: `initialiseKernelState` installs the given `SystemState`
    into `kernelStateRef`; a subsequent `getKernelState` reads it. -/
private def sd010_initialiseAndGet : IO Unit := do
  -- Build a small kernel state with a single TCB
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let st := mkState [(⟨1⟩, .tcb (mkTcb 1 .Ready))] (some tid)
  initialiseKernelState st
  let st' ← getKernelState
  match st'.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
      expect "sd010_tcb_round_trip" (tcb.threadState == .Ready)
        "TCB threadState must round-trip through the IO.Ref"
  | _ => failLine "sd010_tcb_lookup" "TCB lookup after IO.Ref round-trip failed"

/-- SD-011: `updateKernelState` applies a pure function in-place.

Verifies both the no-op (identity) case and a substantive transformation
that clears `scheduler.current`.  This is the API surface the future
hardware boot path uses to rotate the live state without going through
`initialiseKernelState`. -/
private def sd011_updateKernelState : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨2⟩
  let st := mkState [(⟨2⟩, .tcb (mkTcb 2 .Ready))] (some tid)
  initialiseKernelState st
  -- Identity update: the IO.Ref should still hold the same state.
  updateKernelState id
  let st' ← getKernelState
  expect "sd011a_identity_update_preserves_current"
    (st'.scheduler.current == some tid)
    "identity updateKernelState must preserve scheduler.current"
  -- Substantive transformation: clear scheduler.current.
  updateKernelState (fun s => { s with scheduler := { s.scheduler with current := none } })
  let st'' ← getKernelState
  expect "sd011b_substantive_update_clears_current"
    (st''.scheduler.current == none)
    "substantive updateKernelState must apply the transformation"
  -- Restore the original state to avoid affecting downstream tests.
  initialiseKernelState st

/-- SD-012: `initialiseKernelLabelingContext` installs the given
    context; `getKernelLabelingContext` reads it.

Indirectly verifies the round-trip via `isInsecureDefaultContext`:
- Installing `defaultLabelingContext` (insecure) makes
  `isInsecureDefaultContext` return `true`.
- Installing `testLabelingContext` (secure-shaped) makes it return
  `false`.

Two different installed contexts producing two different gate
results witnesses that the read API observes the most recently
installed value. -/
private def sd012_labelingContextRoundtrip : IO Unit := do
  -- Install the test context: insecure-default detector should be false.
  initialiseKernelLabelingContext SeLe4n.Kernel.testLabelingContext
  let ctx1 ← getKernelLabelingContext
  expect "sd012a_test_context_not_insecure"
    (¬ SeLe4n.Kernel.isInsecureDefaultContext ctx1)
    "testLabelingContext must NOT be detected as insecure-default"
  -- Install the default (insecure) context: detector should now be true.
  initialiseKernelLabelingContext SeLe4n.Kernel.defaultLabelingContext
  let ctx2 ← getKernelLabelingContext
  expect "sd012b_default_context_insecure"
    (SeLe4n.Kernel.isInsecureDefaultContext ctx2)
    "defaultLabelingContext must BE detected as insecure-default"
  -- Restore the test context for downstream tests.
  initialiseKernelLabelingContext SeLe4n.Kernel.testLabelingContext

-- ============================================================================
-- R2.B — suspendThreadInner integration via IO.Ref
-- ============================================================================

/-- SD-020: `suspendThreadInner` on a Ready thread returns 0
    (KernelError::Ok-equivalent) and transitions the TCB to Inactive
    in the IO.Ref. -/
private def sd020_suspendThreadInner_ready : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨3⟩
  let st := mkState [(⟨3⟩, .tcb (mkTcb 3 .Ready))] (some tid)
  initialiseKernelState st
  let result ← suspendThreadInner 3
  expect "sd020a_returns_zero" (result == 0)
    s!"suspendThreadInner of a Ready thread must return 0, got {result}"
  let st' ← getKernelState
  match st'.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
      expect "sd020b_thread_inactive"
        (tcb.threadState == .Inactive)
        "TCB must be Inactive after suspendThreadInner"
  | _ => failLine "sd020_tcb_missing" "TCB missing after suspend"

/-- SD-021: `suspendThreadInner` on an already-Inactive thread
    returns the `IllegalState` discriminant (2). -/
private def sd021_suspendThreadInner_inactive : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨4⟩
  let st := mkState [(⟨4⟩, .tcb (mkTcb 4 .Inactive))] (some tid)
  initialiseKernelState st
  let result ← suspendThreadInner 4
  expect "sd021_returns_illegalState"
    (result == KernelError.toUInt32 .illegalState)
    s!"suspendThreadInner of an Inactive thread must return IllegalState (2), got {result}"

/-- SD-022: `suspendThreadInner` on a non-existent thread returns
    the `InvalidArgument` discriminant (39). -/
private def sd022_suspendThreadInner_missing : IO Unit := do
  let st := mkState [(⟨5⟩, .tcb (mkTcb 5 .Ready))] (some ⟨5⟩)
  initialiseKernelState st
  let result ← suspendThreadInner 99
  expect "sd022_returns_invalidArgument"
    (result == KernelError.toUInt32 .invalidArgument)
    s!"suspendThreadInner of a missing thread must return InvalidArgument (39), got {result}"

/-- SD-023: `suspendThreadInner` on the reserved sentinel `tid = 0`
    returns InvalidArgument WITHOUT invoking `suspendThread`.

`ThreadId.sentinel` is defined as `⟨0⟩` (`H-06/WS-E3` in `Prelude.lean`),
so `tid : UInt64 = 0` flows through `ThreadId.ofNat 0 = ThreadId.sentinel`,
and `ThreadId.toValid?` returns `none` for this case (the smart
constructor refuses the reserved value).  The test verifies the FFI
boundary's sentinel rejection is non-bypassable. -/
private def sd023_suspendThreadInner_sentinel : IO Unit := do
  let st := mkState [(⟨6⟩, .tcb (mkTcb 6 .Ready))] (some ⟨6⟩)
  initialiseKernelState st
  -- Verify our understanding of the sentinel value first.
  expect "sd023_sentinel_is_zero"
    (SeLe4n.ThreadId.sentinel.toNat == 0)
    "ThreadId.sentinel must be value 0"
  let sentinel : UInt64 := SeLe4n.ThreadId.sentinel.toNat.toUInt64
  let result ← suspendThreadInner sentinel
  expect "sd023_returns_invalidArgument"
    (result == KernelError.toUInt32 .invalidArgument)
    "suspendThreadInner of the sentinel must return InvalidArgument"
  -- The state must be unchanged because the sentinel branch never
  -- invokes `suspendThread`.
  let st' ← getKernelState
  let oid : SeLe4n.ObjId := ⟨6⟩
  match st'.objects[oid]? with
  | some (.tcb tcb) =>
      expect "sd023_state_unchanged"
        (tcb.threadState == .Ready)
        "sentinel suspend must not mutate kernel state"
  | _ => failLine "sd023_tcb_missing" "test fixture invariant: TCB ⟨6⟩ should still exist"

-- ============================================================================
-- R2.B — syscallDispatchInner integration via IO.Ref
-- ============================================================================

/-- SD-030: `syscallDispatchInner` invoked with no current thread in
    the scheduler returns the `IllegalState` discriminant in the
    encoded UInt64 (bit 63 set, low 32 bits = 2). -/
private def sd030_syscallDispatchInner_noCurrent : IO Unit := do
  -- Empty scheduler.current = none.
  let st := mkState [] none
  initialiseKernelState st
  initialiseKernelLabelingContext SeLe4n.Kernel.testLabelingContext
  let raw ← syscallDispatchInner 0 0 0 0 0 0 0 0 0
  let highBitSet := (raw >>> 63) &&& 1 == 1
  let disc := raw.toNat % (2 ^ 32)
  expect "sd030a_high_bit_set" highBitSet
    "no-current dispatch must set the error flag (bit 63)"
  expect "sd030b_disc_illegalState"
    (disc == (KernelError.toUInt32 .illegalState).toNat)
    s!"discriminant must be IllegalState (2), got {disc}"

/-- SD-031: `syscallDispatchInner` writes register values into the
    current thread's TCB before invoking `syscallEntryChecked`.  We
    verify by checking that a syscall failure preserves the spilled
    registers (per `syscallDispatchFromAbi_error_of_syscallEntryChecked_error`). -/
private def sd031_syscallDispatchInner_spillsRegs : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨7⟩
  let st := mkState [(⟨7⟩, .tcb (mkTcb 7 .Ready))] (some tid)
  initialiseKernelState st
  initialiseKernelLabelingContext SeLe4n.Kernel.testLabelingContext
  -- Invoke with a syscallId that's out of the modeled range
  -- (UInt32 0x80000000 → fails decode → IllegalState/InvalidSyscallNumber).
  -- The exact failure mode depends on the dispatch path's first
  -- rejection point; we just need the call to return without
  -- crashing and preserve the IO.Ref.
  let _ ← syscallDispatchInner 0xFFFFFFFF 0 0xDEADBEEF 0 0 0 0 0 0
  let st' ← getKernelState
  match st'.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
      -- The x0 spill should be visible at gpr ⟨0⟩ even on the failure
      -- path.  This is the substantive witness that the FFI register
      -- spill happens before `syscallEntryChecked` is invoked.
      expect "sd031_x0_spilled"
        (tcb.registerContext.gpr ⟨0⟩ == ⟨0xDEADBEEF⟩)
        s!"x0 must be spilled into TCB (got {tcb.registerContext.gpr ⟨0⟩})"
  | _ => failLine "sd031_tcb_missing" "TCB missing after dispatch"

/-- SD-032: `syscallDispatchInner` rejects an unmodeled syscall id
    with the appropriate error discriminant in the encoded UInt64. -/
private def sd032_syscallDispatchInner_invalidSyscall : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨8⟩
  let st := mkState [(⟨8⟩, .tcb (mkTcb 8 .Ready))] (some tid)
  initialiseKernelState st
  initialiseKernelLabelingContext SeLe4n.Kernel.testLabelingContext
  -- syscallId 99 is outside the modeled set (0..24).
  let raw ← syscallDispatchInner 99 0 0 0 0 0 0 0 0
  let highBitSet := (raw >>> 63) &&& 1 == 1
  expect "sd032_invalid_syscall_high_bit"
    highBitSet
    "unmodeled syscall ID must surface as an error"

/-- SD-033: `syscallDispatchFromAbi_total` — the pure function never
    returns `Except.error`.  Witnessed by direct call: the result is
    always `.ok (encoded, st')`. -/
private def sd033_dispatchFromAbi_total : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨9⟩
  let st := mkState [(⟨9⟩, .tcb (mkTcb 9 .Ready))] (some tid)
  let ctx := SeLe4n.Kernel.testLabelingContext
  match syscallDispatchFromAbi ctx 99 0 0 0 0 0 0 0 0 st with
  | Except.ok _ =>
      passLine "sd033_dispatchFromAbi_returns_ok"
  | Except.error _ =>
      failLine "sd033_dispatchFromAbi_returns_ok"
        "syscallDispatchFromAbi must never return Except.error"

/-- SD-034: ABI consistency check — when `msgInfo ≠ x1`, the dispatch
    rejects with `.invalidSyscallArgument` without invoking
    `syscallEntryChecked`.

The Rust caller's `SyscallArgs::from_trap_frame` constructs `msg_info`
and `msg_regs[1]` from the same `frame.x1()` slot, so they should always
be equal at the ABI boundary.  A divergence indicates either a malformed
caller or memory corruption — the FFI rejects rather than proceeding. -/
private def sd034_dispatchInner_abiMismatch : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨10⟩
  let st := mkState [(⟨10⟩, .tcb (mkTcb 10 .Ready))] (some tid)
  initialiseKernelState st
  initialiseKernelLabelingContext SeLe4n.Kernel.testLabelingContext
  -- Pass msgInfo=0xAAAA and x1=0xBBBB (≠ msgInfo).  Per the FFI ABI
  -- contract these must agree; the dispatcher rejects.
  let raw ← syscallDispatchInner 0 0xAAAA 0 0xBBBB 0 0 0 0 0
  let highBitSet := (raw >>> 63) &&& 1 == 1
  let disc := raw.toNat % (2 ^ 32)
  expect "sd034a_high_bit_set" highBitSet
    "ABI-mismatched dispatch must surface as an error"
  expect "sd034b_disc_invalidSyscallArgument"
    (disc == (KernelError.toUInt32 .invalidSyscallArgument).toNat)
    s!"ABI-mismatch must yield InvalidSyscallArgument (41), got {disc}"
  -- Verify the kernel state is NOT mutated on the ABI-mismatch path.
  let st' ← getKernelState
  match st'.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
      -- TCB.registerContext.gpr ⟨0⟩ should still be the default value (0)
      -- because the dispatch rejected before writeFfiRegistersToTcb was called.
      expect "sd034c_no_register_spill_on_abi_mismatch"
        (tcb.registerContext.gpr ⟨0⟩ == ⟨0⟩)
        "ABI-mismatch must reject before spilling registers"
  | _ => failLine "sd034_tcb_missing" "TCB missing after ABI-mismatch dispatch"

/-- SD-035: Sequential dispatches — the IO.Ref state evolves
    correctly across multiple syscall invocations.

This regression-tests that the `kernelStateRef` mutation in
`syscallDispatchInner` is observable to the next syscall (the
hardware path's authoritative state update). -/
private def sd035_sequentialDispatches : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨11⟩
  let st := mkState [(⟨11⟩, .tcb (mkTcb 11 .Ready))] (some tid)
  initialiseKernelState st
  initialiseKernelLabelingContext SeLe4n.Kernel.testLabelingContext
  -- First dispatch: spills x0=0x111 into the TCB.
  let _ ← syscallDispatchInner 99 0 0x111 0 0 0 0 0 0
  let st1 ← getKernelState
  match st1.objects[tid.toObjId]? with
  | some (.tcb tcb1) =>
      expect "sd035a_first_dispatch_spilled"
        (tcb1.registerContext.gpr ⟨0⟩ == ⟨0x111⟩)
        "first dispatch must spill x0=0x111"
  | _ => failLine "sd035_tcb_missing_1" "TCB missing after first dispatch"
  -- Second dispatch: spills x0=0x222 into the (now-updated) TCB.
  let _ ← syscallDispatchInner 99 0 0x222 0 0 0 0 0 0
  let st2 ← getKernelState
  match st2.objects[tid.toObjId]? with
  | some (.tcb tcb2) =>
      expect "sd035b_second_dispatch_spilled"
        (tcb2.registerContext.gpr ⟨0⟩ == ⟨0x222⟩)
        "second dispatch must spill x0=0x222 (state evolved)"
  | _ => failLine "sd035_tcb_missing_2" "TCB missing after second dispatch"

-- ============================================================================
-- R2.A — bootAndInitialiseFromPlatform integration
-- ============================================================================

/-- SD-040: `bootAndInitialiseFromPlatform` on a well-formed (empty)
    config installs the post-boot state into `kernelStateRef`. -/
private def sd040_bootInitialise_emptyConfig_succeeds : IO Unit := do
  -- Seed the IO.Ref with a sentinel state so we can detect mutation.
  let sentinelTid : SeLe4n.ThreadId := ⟨123⟩
  let st := mkState [(⟨123⟩, .tcb (mkTcb 123 .Ready))] (some sentinelTid)
  initialiseKernelState st
  -- A PlatformConfig with empty IRQ + initialObjects tables is the
  -- minimally well-formed config (`PlatformConfig.wellFormed_empty`
  -- in Boot.lean).
  let cfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], initialObjects := [] }
  match ← bootAndInitialiseFromPlatform cfg with
  | Except.ok _ =>
      -- The IO.Ref has been overwritten with the post-boot state.
      -- The post-boot state has no objects, so `scheduler.current`
      -- is `none` (the sentinel TCB is gone).
      let st' ← getKernelState
      expect "sd040_bootInitialise_success_clears_sentinel"
        (st'.scheduler.current == none)
        "post-empty-boot state must have no current thread"
  | Except.error e =>
      failLine "sd040_bootInitialise_unexpected_error"
        s!"empty config should be well-formed, got error: {e}"

/-- SD-041: `bootAndInitialiseFromPlatform` accepts an optional
    labeling context and installs it into `kernelLabelingContextRef`. -/
private def sd041_bootInitialise_withLabelingContext : IO Unit := do
  let cfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], initialObjects := [] }
  -- Use the test labeling context as a proxy for a production policy.
  match ← bootAndInitialiseFromPlatform cfg
        (some SeLe4n.Kernel.testLabelingContext) with
  | Except.ok _ =>
      passLine "sd041_bootInitialise_with_labeling_context"
  | Except.error e =>
      failLine "sd041_bootInitialise_unexpected_error"
        s!"empty config + labeling context should succeed, got: {e}"

-- ============================================================================
-- Driver
-- ============================================================================

end SeLe4n.Testing.SyscallDispatchSuite

open SeLe4n.Testing.SyscallDispatchSuite in
def main : IO Unit := do
  IO.println "=== WS-RC R2.C SyscallDispatch Test Suite ==="
  IO.println "--- R2.B.0: KernelError discriminant + UInt64 encoding ---"
  sd001_kernelErrorDiscriminants
  sd002_encodeError
  sd003_encodeOk
  IO.println "--- R2.A: Kernel-state IO.Ref ---"
  sd010_initialiseAndGet
  sd011_updateKernelState
  sd012_labelingContextRoundtrip
  IO.println "--- R2.B: suspendThreadInner integration ---"
  sd020_suspendThreadInner_ready
  sd021_suspendThreadInner_inactive
  sd022_suspendThreadInner_missing
  sd023_suspendThreadInner_sentinel
  IO.println "--- R2.B: syscallDispatchInner integration ---"
  sd030_syscallDispatchInner_noCurrent
  sd031_syscallDispatchInner_spillsRegs
  sd032_syscallDispatchInner_invalidSyscall
  sd033_dispatchFromAbi_total
  sd034_dispatchInner_abiMismatch
  sd035_sequentialDispatches
  IO.println "--- R2.A: bootAndInitialiseFromPlatform integration ---"
  sd040_bootInitialise_emptyConfig_succeeds
  sd041_bootInitialise_withLabelingContext
  IO.println "=== All WS-RC R2.C SyscallDispatch tests passed ==="
