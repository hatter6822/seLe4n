-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Testing.Helpers
import SeLe4n.Testing.StateBuilder
import SeLe4n.Model.FrozenState
import SeLe4n.Model.Builder
import SeLe4n.Kernel.FrozenOps
-- WS-RC R3 (DEEP-BOOT-01): regression coverage for the boot VSpaceRoot
-- threading exercises `bootFromPlatformChecked`, the canonical RPi5
-- boot VSpace, and the `installBootVSpaceRoot` post-state.
import SeLe4n.Platform.Boot
import SeLe4n.Platform.RPi5.Contract
import SeLe4n.Platform.RPi5.VSpaceBoot
import SeLe4n.Platform.Sim.Contract
import SeLe4n.Kernel.Architecture.VSpaceInvariant

/-!
# Q9-A: Two-Phase Architecture Integration Test Suite

Comprehensive integration tests covering the full builder→freeze→execution
pipeline. Each test maps to a TPH-* scenario from the WS-Q master plan.

## Coverage Matrix

| TPH | Description                              | Test(s)            |
|-----|------------------------------------------|--------------------|
| 001 | Build IntermediateState from empty+objs  | tph001_*           |
| 003 | Freeze populated, verify lookup equiv    | tph003_*           |
| 005 | Frozen IPC send/receive                  | tph005_*           |
| 006 | Frozen scheduler tick (active)           | tph006_*           |
| 010 | Commutativity: builder→freeze=freeze→op  | tph010_*           |
| 012 | Pre-allocated slot retype in frozen      | tph012_*           |
| 014 | RunQueue operations in frozen state      | tph014_*           |
| 015 | WS-RC R3 boot VSpaceRoot threading       | tph015_*           |

Tests for TPH-002,004,007,008,009,011,013 are already covered in
FrozenStateSuite, FreezeProofSuite, and FrozenOpsSuite.
-/

open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency (bootCoreId)
open SeLe4n.Kernel.RadixTree
open SeLe4n.Kernel.FrozenOps
open SeLe4n.Model
open SeLe4n.Model.Builder
open SeLe4n.Platform
open SeLe4n.Platform.Boot
open SeLe4n.Kernel.Architecture

namespace SeLe4n.Testing.TwoPhaseArchSuite

/-- This suite's assertion is `SeLe4n.Testing.expectCond` at this suite's tag.

`SeLe4n/Testing/Helpers.lean` states in as many words that "all test suites
should import this module rather than defining private copies of these
functions", and this suite carried a private copy that differed only in the
capitalisation of its failure word.

Every label carries its scenario id and a letter indexing the assertion within
that scenario (`TPH-001a`, `TPH-001b`, ...) — running across the scenario's
sub-functions in declaration order, so two assertions that print the same text
(`timer advanced`, at `TPH-006a` and `TPH-006d`) are distinguishable.  That is
the convention `tests/fixtures/two_phase_arch_smoke.expected` asserts in its
`expected_trace_fragment` column, and `scripts/test_tier2_trace.sh` checks the
relation against this suite's real output. -/
private def expect (label : String) (cond : Bool) : IO Unit :=
  SeLe4n.Testing.expectCond "two-phase" label cond

/-- Helper: construct a minimal test TCB. -/
private def mkTcb (tid : Nat) (prio : Nat := 0) (dom : Nat := 0) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨dom⟩,
    cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0) }

/-- Helper: construct an empty FrozenSystemState. -/
private def emptyFrozenState : FrozenSystemState :=
  SeLe4n.Testing.emptyFrozenSystemState

/-- Helper: make a FrozenSystemState with given objects. -/
private def mkFrozenState (objs : List (ObjId × FrozenKernelObject))
    : FrozenSystemState :=
  SeLe4n.Testing.frozenStateOf objs

-- ============================================================================
-- TPH-001: Build IntermediateState from Empty + Objects
-- ============================================================================

/-- TPH-001a: mkEmptyIntermediateState satisfies all invariants. -/
private def tph001a_emptyBuilder : IO Unit := do
  let ist := mkEmptyIntermediateState
  -- Empty state must have allTablesInvExtK (proven at compile time)
  expect "TPH-001a empty builder valid" true
  -- Empty state has no objects
  expect "TPH-001b empty objects" (ist.state.objects.size == 0)
  expect "TPH-001c empty IRQs" (ist.state.irqHandlers.size == 0)

/-- TPH-001b: Builder.createObject inserts and preserves invariants. -/
private def tph001b_builderPipeline : IO Unit := do
  let ist := mkEmptyIntermediateState
  -- Create a TCB — TCBs have no embedded hash tables, so proofs are trivial
  let tcb1 := KernelObject.tcb (mkTcb 1 10 0)
  let ist1 := Builder.createObject ist ⟨1⟩ tcb1
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  expect "TPH-001d one object" (ist1.state.objects.size == 1)
  expect "TPH-001e object findable" ((ist1.state.objects[(⟨1⟩ : ObjId)]?).isSome)
  -- Create a second TCB
  let tcb2 := KernelObject.tcb (mkTcb 2 5 0)
  let ist2 := Builder.createObject ist1 ⟨2⟩ tcb2
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  expect "TPH-001f two objects" (ist2.state.objects.size == 2)
  expect "TPH-001g both findable" ((ist2.state.objects[(⟨1⟩ : ObjId)]?).isSome &&
    (ist2.state.objects[(⟨2⟩ : ObjId)]?).isSome)

/-- TPH-001c: Builder.registerIrq preserves invariants. -/
private def tph001c_builderIrq : IO Unit := do
  let ist := mkEmptyIntermediateState
  let ist' := Builder.registerIrq ist (SeLe4n.Irq.ofNat 3) ⟨100⟩
  expect "TPH-001h IRQ registered" (Option.isSome (ist'.state.irqHandlers[(SeLe4n.Irq.ofNat 3)]?))
  expect "TPH-001i IRQ table size 1" (ist'.state.irqHandlers.size == 1)

-- ============================================================================
-- TPH-003: Freeze Populated State — Full Pipeline Lookup Equivalence
-- ============================================================================

/-- TPH-003: Build populated state, freeze, verify all lookups match. -/
private def tph003_freezePopulated : IO Unit := do
  -- Build a state with multiple object types
  let ist := mkEmptyIntermediateState
  let tcb := KernelObject.tcb (mkTcb 1 10 0)
  let ist1 := Builder.createObject ist ⟨1⟩ tcb
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  let ep := KernelObject.endpoint { sendQ := {}, receiveQ := {} }
  let ist2 := Builder.createObject ist1 ⟨2⟩ ep
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  -- Add IRQ handler
  let ist3 := Builder.registerIrq ist2 (SeLe4n.Irq.ofNat 7) ⟨2⟩
  -- Freeze
  let fss := freeze ist3
  -- Verify objects lookup equivalence
  expect "TPH-003a frozen objects size 2" (fss.objects.data.size == 2)
  expect "TPH-003b frozen obj 1 exists" (Option.isSome (fss.objects.get? ⟨1⟩))
  expect "TPH-003c frozen obj 2 exists" (Option.isSome (fss.objects.get? ⟨2⟩))
  expect "TPH-003d frozen obj 99 none" (Option.isNone (fss.objects.get? ⟨99⟩))
  -- Verify IRQ handler lookup equivalence
  expect "TPH-003e frozen IRQ 7 exists" (Option.isSome (fss.irqHandlers.get? (SeLe4n.Irq.ofNat 7)))
  expect "TPH-003f frozen IRQ 99 none" (Option.isNone (fss.irqHandlers.get? (SeLe4n.Irq.ofNat 99)))
  -- Verify object types
  match fss.objects.get? ⟨1⟩ with
  | some obj => expect "TPH-003g obj 1 is TCB" (FrozenKernelObject.objectType obj == .tcb)
  | none => throw <| IO.userError "obj 1 missing"
  match fss.objects.get? ⟨2⟩ with
  | some obj => expect "TPH-003h obj 2 is endpoint" (FrozenKernelObject.objectType obj == .endpoint)
  | none => throw <| IO.userError "obj 2 missing"

-- ============================================================================
-- TPH-005: Frozen IPC Send/Receive (Full Transfer)
-- ============================================================================

/-- TPH-005a: Frozen endpoint send — sender blocks when no receiver. -/
private def tph005a_sendBlocks : IO Unit := do
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let senderTcb := mkTcb 1
  let fst := mkFrozenState [(⟨10⟩, .endpoint ep), (⟨1⟩, .tcb senderTcb)]
  let msg : IpcMessage := { registers := #[⟨42⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointSend ⟨10⟩ ⟨1⟩ msg fst with
  | .ok ((), fst') =>
      match frozenLookupTcb fst' ⟨1⟩ with
      | some tcb =>
          expect "TPH-005a sender blocked" (tcb.ipcState == .blockedOnSend ⟨10⟩)
          expect "TPH-005b message pending" (tcb.pendingMessage.isSome)
      | none => throw <| IO.userError "sender TCB missing"
  | .error _ => throw <| IO.userError "send should succeed"

/-- TPH-005b: Frozen endpoint receive — receiver blocks when no sender. -/
private def tph005b_receiveBlocks : IO Unit := do
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let recvTcb := mkTcb 2
  let fst := mkFrozenState [(⟨10⟩, .endpoint ep), (⟨2⟩, .tcb recvTcb)]
  match frozenEndpointReceive ⟨10⟩ ⟨2⟩ none fst with
  | .ok (_, fst') =>
      match frozenLookupTcb fst' ⟨2⟩ with
      | some tcb =>
          expect "TPH-005c receiver blocked" (tcb.ipcState == .blockedOnReceive ⟨10⟩)
      | none => throw <| IO.userError "receiver TCB missing"
  | .error _ => throw <| IO.userError "receive should succeed"

/-- TPH-005c: Frozen endpoint call — caller sends then blocks for reply. -/
private def tph005c_callBlocksForReply : IO Unit := do
  -- Set up an endpoint with a receiver already waiting
  let recvTcb : TCB := { mkTcb 2 with ipcState := .blockedOnReceive ⟨10⟩ }
  let ep : Endpoint := {
    receiveQ := { head := some ⟨2⟩, tail := some ⟨2⟩ }
    sendQ := {} }
  let callerTcb := mkTcb 3
  let fst := mkFrozenState [
    (⟨10⟩, .endpoint ep), (⟨2⟩, .tcb recvTcb), (⟨3⟩, .tcb callerTcb)]
  let msg : IpcMessage := { registers := #[⟨99⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointCall ⟨10⟩ ⟨3⟩ msg fst with
  | .ok ((), fst') =>
      -- Receiver should have been unblocked with the message
      match frozenLookupTcb fst' ⟨2⟩ with
      | some rTcb =>
          expect "TPH-005d receiver unblocked" (rTcb.ipcState == .ready)
          expect "TPH-005e receiver got message" (rTcb.pendingMessage.isSome)
      | none => throw <| IO.userError "receiver TCB missing"
      -- Caller should be blocked on reply
      match frozenLookupTcb fst' ⟨3⟩ with
      | some cTcb =>
          expect "TPH-005f caller blocked on reply" (
            match cTcb.ipcState with
            | .blockedOnReply _ _ => true
            | _ => false)
      | none => throw <| IO.userError "caller TCB missing"
  | .error e => throw <| IO.userError s!"call should succeed: {toString e}"

-- ============================================================================
-- TPH-006: Frozen Scheduler Tick (Active Thread)
-- ============================================================================

/-- TPH-006a: Timer tick with active current thread — time slice decremented. -/
private def tph006a_timerTickActive : IO Unit := do
  let tcb1 : TCB := { mkTcb 1 10 0 with timeSlice := 3 }
  let fst := { mkFrozenState [(⟨1⟩, .tcb tcb1)] with
    scheduler := { emptyFrozenState.scheduler with current := some ⟨1⟩ } }
  match frozenTimerTick fst with
  | .ok ((), fst') =>
      expect "TPH-006a timer advanced" (fst'.machine.timer == fst.machine.timer + 1)
      -- Time slice should be decremented (3 → 2)
      match frozenLookupTcb fst' ⟨1⟩ with
      | some tcb =>
          expect "TPH-006b time slice decremented" (tcb.timeSlice == 2)
      | none => throw <| IO.userError "TCB missing after tick"
      expect "TPH-006c current preserved" ((fst'.scheduler.current) == some ⟨1⟩)
  | .error e => throw <| IO.userError s!"tick should succeed: {toString e}"

/-- TPH-006b: Timer tick with expired time slice — preemption and reschedule. -/
private def tph006b_timerTickExpiry : IO Unit := do
  -- Thread with timeSlice=1, so the tick will expire it.
  -- byPriority has the thread so frozenSchedule can re-select it.
  let tcb1 : TCB := { mkTcb 1 10 0 with timeSlice := 1, ipcState := .ready }
  let byPrioRt := (RHTable.empty 16 : RHTable Priority (List ThreadId))
    |>.insert ⟨10⟩ [⟨1⟩]
  let memberRt := (RHTable.empty 16 : RHTable ThreadId Unit)
    |>.insert ⟨1⟩ ()
  let fst := { mkFrozenState [(⟨1⟩, .tcb tcb1)] with
    scheduler := {
      byPriority := freezeMap byPrioRt
      threadPriority := freezeMap (RHTable.empty 16)
      membership := freezeMap memberRt
      current := some ⟨1⟩
      activeDomain := ⟨0⟩
      domainTimeRemaining := 5
      domainSchedule := []
      domainScheduleIndex := 0
      configDefaultTimeSlice := 5
      replenishQueue := { entries := [], size := 0 }
    } }
  match frozenTimerTick fst with
  | .ok ((), fst') =>
      expect "TPH-006d timer advanced" (fst'.machine.timer == fst.machine.timer + 1)
      -- After expiry: current was cleared, frozenSchedule ran.
      -- The thread's time slice was reset to configDefaultTimeSlice (5).
      match frozenLookupTcb fst' ⟨1⟩ with
      | some tcb =>
          expect "TPH-006e time slice reset" (tcb.timeSlice == fst.scheduler.configDefaultTimeSlice)
      | none => throw <| IO.userError "TCB missing after expiry"
      -- frozenSchedule was called after clearing current. Thread 1 is the
      -- only eligible thread (domain 0, .ready), so it should be re-selected.
      expect "TPH-006f thread re-selected" ((fst'.scheduler.current) == some ⟨1⟩)
  | .error e => throw <| IO.userError s!"expiry should succeed: {toString e}"

/-- TPH-006c: Timer tick expiry with non-default configDefaultTimeSlice (MED-01
    semantic verification). Verifies that frozenTimerTick resets the time slice
    to the platform-configured value, not the hardcoded default. -/
private def tph006c_timerTickExpiryCustomConfig : IO Unit := do
  let tcb1 : TCB := { mkTcb 1 10 0 with timeSlice := 1, ipcState := .ready }
  let byPrioRt := (RHTable.empty 16 : RHTable Priority (List ThreadId))
    |>.insert ⟨10⟩ [⟨1⟩]
  let memberRt := (RHTable.empty 16 : RHTable ThreadId Unit)
    |>.insert ⟨1⟩ ()
  -- Use configDefaultTimeSlice := 12, deliberately different from default (5)
  let fst := { mkFrozenState [(⟨1⟩, .tcb tcb1)] with
    scheduler := {
      byPriority := freezeMap byPrioRt
      threadPriority := freezeMap (RHTable.empty 16)
      membership := freezeMap memberRt
      current := some ⟨1⟩
      activeDomain := ⟨0⟩
      domainTimeRemaining := 5
      domainSchedule := []
      domainScheduleIndex := 0
      configDefaultTimeSlice := 12
      replenishQueue := { entries := [], size := 0 }
    } }
  match frozenTimerTick fst with
  | .ok ((), fst') =>
      match frozenLookupTcb fst' ⟨1⟩ with
      | some tcb =>
          -- Must reset to 12 (the config value), NOT 5 (the old default)
          expect "TPH-006g time slice reset to custom config" (tcb.timeSlice == 12)
          expect "TPH-006h time slice uses config field" (tcb.timeSlice == fst.scheduler.configDefaultTimeSlice)
      | none => throw <| IO.userError "TCB missing after expiry"
  | .error e => throw <| IO.userError s!"custom config expiry should succeed: {toString e}"

-- ============================================================================
-- TPH-010: Commutativity Property
-- ============================================================================

/-- TPH-010: Commutativity — value update in builder then freeze produces
same result as freeze then frozen update.

This tests the conceptual property: for a value-only mutation (e.g., updating
a TCB's priority), the order of freeze vs. mutation doesn't matter for the
affected field's lookup result. -/
private def tph010_commutativity : IO Unit := do
  -- Path A: Build state → mutate TCB → freeze → lookup
  let ist := mkEmptyIntermediateState
  let tcb_v1 := KernelObject.tcb (mkTcb 1 5 0)
  let ist1 := Builder.createObject ist ⟨1⟩ tcb_v1
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  -- Mutate: update TCB priority to 10 (via re-insert)
  let tcb_v2 := KernelObject.tcb { mkTcb 1 10 0 with timeSlice := 3 }
  let ist2 := Builder.createObject ist1 ⟨1⟩ tcb_v2
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  let fssA := freeze ist2
  let objA := fssA.objects.get? ⟨1⟩

  -- Path B: Build state → freeze → mutate in frozen → lookup
  let fssB := freeze ist1
  let tcb_frozen_v2 : FrozenKernelObject := .tcb { mkTcb 1 10 0 with timeSlice := 3 }
  let fssB' := match fssB.objects.set ⟨1⟩ tcb_frozen_v2 with
    | some objs => { fssB with objects := objs }
    | none => fssB  -- should not happen
  let objB := fssB'.objects.get? ⟨1⟩

  -- Both paths should yield the same object type and key properties
  expect "TPH-010a both paths find object" (Option.isSome objA && Option.isSome objB)
  match objA, objB with
  | some a, some b =>
    expect "TPH-010b same object type" (FrozenKernelObject.objectType a == FrozenKernelObject.objectType b)
    match a, b with
    | FrozenKernelObject.tcb ta, FrozenKernelObject.tcb tb =>
      expect "TPH-010c same priority" (ta.priority == tb.priority)
      expect "TPH-010d same time slice" (ta.timeSlice == tb.timeSlice)
    | _, _ => throw <| IO.userError "expected TCBs"
  | _, _ => throw <| IO.userError "both should find object"

-- ============================================================================
-- TPH-012: Pre-Allocated Slot — Set None to Some in Frozen State
-- ============================================================================

/-- TPH-012: Simulate retype in frozen state by setting a pre-allocated
None slot to Some. In the frozen model, retype at runtime uses FrozenMap.set
on a key that was mapped to a None-initialized slot at freeze time. -/
private def tph012_preallocatedSlot : IO Unit := do
  -- Build a FrozenMap with 3 object slots — one starts as a "placeholder" TCB
  -- that we'll replace (simulating retype from none → typed object)
  let placeholderTcb := mkTcb 99 0 0  -- placeholder
  let realTcb := mkTcb 1 10 0
  let fst := mkFrozenState [
    (⟨1⟩, .tcb placeholderTcb),
    (⟨2⟩, .tcb (mkTcb 2 5 0)),
    (⟨3⟩, .endpoint { sendQ := {}, receiveQ := {} })]
  -- Verify pre-allocated slot exists
  expect "TPH-012a slot exists" (fst.objects.get? ⟨1⟩ |>.isSome)
  -- "Retype": replace placeholder with real object via FrozenMap.set
  match fst.objects.set ⟨1⟩ (.tcb realTcb) with
  | some objects' =>
    let fst' := { fst with objects := objects' }
    match fst'.objects.get? ⟨1⟩ with
    | some (.tcb tcb) =>
      expect "TPH-012b retyped priority" (tcb.priority == ⟨10⟩)
      expect "TPH-012c retyped tid" (tcb.tid == ⟨1⟩)
    | _ => throw <| IO.userError "expected TCB after retype"
    -- Other slots unaffected
    expect "TPH-012d slot 2 preserved" (fst'.objects.get? ⟨2⟩ |>.isSome)
    expect "TPH-012e slot 3 preserved" (fst'.objects.get? ⟨3⟩ |>.isSome)
  | none => throw <| IO.userError "set should succeed"

-- ============================================================================
-- TPH-014: RunQueue Operations in Frozen State
-- ============================================================================

/-- TPH-014a: Frozen schedule — select eligible thread from byPriority. -/
private def tph014a_frozenSchedule : IO Unit := do
  -- Set up frozen state with two threads in byPriority
  let tcb1 : TCB := { mkTcb 1 10 0 with ipcState := .ready }
  let tcb2 : TCB := { mkTcb 2 5 0 with ipcState := .ready }
  let byPrioRt := (RHTable.empty 16 : RHTable Priority (List ThreadId))
    |>.insert ⟨10⟩ [⟨1⟩]
    |>.insert ⟨5⟩ [⟨2⟩]
  let memberRt := (RHTable.empty 16 : RHTable ThreadId Unit)
    |>.insert ⟨1⟩ ()
    |>.insert ⟨2⟩ ()
  let fst := { mkFrozenState [(⟨1⟩, .tcb tcb1), (⟨2⟩, .tcb tcb2)] with
    scheduler := {
      byPriority := freezeMap byPrioRt
      threadPriority := freezeMap (RHTable.empty 16)
      membership := freezeMap memberRt
      current := none
      activeDomain := ⟨0⟩
      domainTimeRemaining := 5
      domainSchedule := []
      domainScheduleIndex := 0
      configDefaultTimeSlice := 5
      replenishQueue := { entries := [], size := 0 }
    } }
  match frozenSchedule fst with
  | .ok ((), fst') =>
      -- A thread should have been selected
      expect "TPH-014a thread selected" ((fst'.scheduler.current).isSome)
  | .error e => throw <| IO.userError s!"schedule should succeed: {toString e}"

/-- TPH-014b: Frozen yield — re-enqueue current and reschedule. -/
private def tph014b_frozenYield : IO Unit := do
  let tcb1 : TCB := { mkTcb 1 10 0 with ipcState := .ready }
  let byPrioRt := (RHTable.empty 16 : RHTable Priority (List ThreadId))
    |>.insert ⟨10⟩ [⟨1⟩]
  let memberRt := (RHTable.empty 16 : RHTable ThreadId Unit)
    |>.insert ⟨1⟩ ()
  let fst := { mkFrozenState [(⟨1⟩, .tcb tcb1)] with
    scheduler := {
      byPriority := freezeMap byPrioRt
      threadPriority := freezeMap (RHTable.empty 16)
      membership := freezeMap memberRt
      current := some ⟨1⟩
      activeDomain := ⟨0⟩
      domainTimeRemaining := 5
      domainSchedule := []
      domainScheduleIndex := 0
      configDefaultTimeSlice := 5
      replenishQueue := { entries := [], size := 0 }
    } }
  match frozenHandleYield fst with
  | .ok ((), fst') =>
      -- After yield: current was cleared, then schedule picked a thread
      -- Thread 1 should be re-selected (only eligible thread)
      expect "TPH-014b yield succeeded" true
  | .error e => throw <| IO.userError s!"yield should succeed: {toString e}"

/-- TPH-014c: Frozen schedule with no eligible threads — current stays none. -/
private def tph014c_scheduleNoEligible : IO Unit := do
  -- All threads blocked (not ready)
  let tcb1 : TCB := { mkTcb 1 10 0 with ipcState := .blockedOnReceive ⟨99⟩ }
  let byPrioRt := (RHTable.empty 16 : RHTable Priority (List ThreadId))
    |>.insert ⟨10⟩ [⟨1⟩]
  let memberRt := (RHTable.empty 16 : RHTable ThreadId Unit)
    |>.insert ⟨1⟩ ()
  let fst := { mkFrozenState [(⟨1⟩, .tcb tcb1)] with
    scheduler := {
      byPriority := freezeMap byPrioRt
      threadPriority := freezeMap (RHTable.empty 16)
      membership := freezeMap memberRt
      current := none
      activeDomain := ⟨0⟩
      domainTimeRemaining := 5
      domainSchedule := []
      domainScheduleIndex := 0
      configDefaultTimeSlice := 5
      replenishQueue := { entries := [], size := 0 }
    } }
  match frozenSchedule fst with
  | .ok ((), fst') =>
      expect "TPH-014c no thread selected" ((fst'.scheduler.current) == none)
  | .error e => throw <| IO.userError s!"should succeed: {toString e}"

-- ============================================================================
-- TPH-015 (WS-RC R3 / DEEP-BOOT-01): Boot VSpaceRoot threading
-- ============================================================================

/-- WS-RC R3 baseline: build a minimal `PlatformConfig` carrying the
    canonical RPi5 boot VSpaceRoot.  Empty `irqTable` and
    `initialObjects` keep the test scope narrow — we are exclusively
    exercising the new `installBootVSpaceRoot` step. -/
private def tph015BootConfig : PlatformConfig :=
  { irqTable := []
    initialObjects := []
    machineConfig := SeLe4n.defaultMachineConfig
    bootVSpaceRoot := some SeLe4n.Platform.RPi5.rpi5BootVSpaceRootEntry }

/-- TPH-015a: `bootFromPlatformChecked` succeeds on a config carrying
    the canonical RPi5 boot VSpaceRoot.  The empty-irq, empty-objects
    config trivially passes all gates; the new R3 gates
    (`bootVSpaceRootObjIdDistinct`, `bootVSpaceRootSafe`) succeed
    because the canonical root passes the boot-safety predicate and
    its ObjId does not collide with any (empty) initialObjects entry. -/
private def tph015a_bootSucceeds : IO Unit := do
  match bootFromPlatformChecked tph015BootConfig with
  | .ok _ => expect "TPH-015a boot succeeds with rpi5BootVSpaceRoot" true
  | .error e =>
      throw <| IO.userError s!"tph015a: bootFromPlatformChecked failed: {e}"

/-- TPH-015b: After a successful checked boot, the post-state object
    store contains a VSpaceRoot at the reserved boot ObjId.  This is
    the headline assertion of plan §7.3 R3.7: "post-boot the kernel
    state contains a VSpaceRoot ObjId entry". -/
private def tph015b_postBootHasVSpaceRoot : IO Unit := do
  match bootFromPlatformChecked tph015BootConfig with
  | .ok ist =>
      let oid := SeLe4n.Platform.RPi5.rpi5BootVSpaceRootObjId
      match ist.state.objects[oid]? with
      | some (KernelObject.vspaceRoot vsr) =>
          expect "TPH-015b post-boot objects has rpi5BootVSpaceRoot at reserved ObjId"
            (vsr.asid == SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot.asid)
      | some other =>
          throw <| IO.userError s!"tph015b: object at {repr oid} is not a VSpaceRoot: {repr other}"
      | none =>
          throw <| IO.userError "tph015b: no object at reserved boot VSpace ObjId"
  | .error e =>
      throw <| IO.userError s!"tph015b: bootFromPlatformChecked failed: {e}"

/-- TPH-015c: After a successful checked boot, the `wxExclusiveInvariant`
    holds for the post-state.  This validates that the boot VSpaceRoot's
    proven W^X compliance carries through to the runtime invariant
    surface — the headline correctness claim of WS-RC R3. -/
private def tph015c_postBootWxInvariantHolds : IO Unit := do
  match bootFromPlatformChecked tph015BootConfig with
  | .ok ist =>
      -- We cannot evaluate the invariant directly (it's a Prop), but
      -- we can witness its discharge by inspecting the boot VSpace
      -- root's mappings and checking each is wxCompliant — exactly
      -- what `wxExclusiveInvariant` quantifies over.
      let oid := SeLe4n.Platform.RPi5.rpi5BootVSpaceRootObjId
      match ist.state.objects[oid]? with
      | some (KernelObject.vspaceRoot vsr) =>
          let allWxCompliant : Bool :=
            vsr.mappings.fold true (fun acc _ entry => acc && entry.2.wxCompliant)
          expect "TPH-015c post-boot rpi5BootVSpaceRoot satisfies wxExclusiveInvariant"
            allWxCompliant
      | _ =>
          throw <| IO.userError "tph015c: no boot VSpaceRoot found"
  | .error e =>
      throw <| IO.userError s!"tph015c: bootFromPlatformChecked failed: {e}"

/-- TPH-015d: After a successful checked boot, the asidTable maps the
    boot VSpaceRoot's ASID to the reserved ObjId.  This validates that
    `installBootVSpaceRoot` correctly registers the ASID for downstream
    `resolveAsidRoot`-based VSpace operations. -/
private def tph015d_asidTableHasBootRoot : IO Unit := do
  match bootFromPlatformChecked tph015BootConfig with
  | .ok ist =>
      let asid := SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot.asid
      let oid := SeLe4n.Platform.RPi5.rpi5BootVSpaceRootObjId
      match ist.state.asidTable[asid]? with
      | some recordedOid =>
          expect "TPH-015d post-boot asidTable maps boot VSpace ASID to reserved ObjId"
            (recordedOid == oid)
      | none =>
          throw <| IO.userError "tph015d: asidTable does not register boot VSpace ASID"
  | .error e =>
      throw <| IO.userError s!"tph015d: bootFromPlatformChecked failed: {e}"

/-- TPH-015e: `bootVSpaceRoot = none` configs preserve the pre-R3
    behaviour: `bootFromPlatformChecked` matches `bootEnableInterruptsOp
    (bootFromPlatform _)` with no boot VSpaceRoot installed.  This is
    the equality-theorem regression for `bootFromPlatformChecked_eq_bootFromPlatform`. -/
private def tph015e_noBootVSpaceCompat : IO Unit := do
  let cfg : PlatformConfig :=
    { irqTable := [], initialObjects := [], machineConfig := SeLe4n.defaultMachineConfig
      bootVSpaceRoot := none }
  match bootFromPlatformChecked cfg with
  | .ok ist =>
      -- No VSpaceRoot in the post-boot state — verify by checking
      -- the reserved boot ObjId AND the entire object store size.
      let oid := SeLe4n.Platform.RPi5.rpi5BootVSpaceRootObjId
      let absent : Bool := match ist.state.objects[oid]? with
        | some (KernelObject.vspaceRoot _) => false
        | _ => true
      expect "TPH-015e bootVSpaceRoot = none yields no VSpace at reserved ObjId" absent
      -- Stronger: object store should be empty since initialObjects is empty.
      expect "TPH-015f bootVSpaceRoot = none yields empty object store"
        (ist.state.objects.size == 0)
  | .error e =>
      throw <| IO.userError s!"tph015e: bootFromPlatformChecked (no boot VSpace) failed: {e}"

/-- TPH-015f: ObjId collision rejection.  A config that places a
    boot VSpaceRoot at the same ObjId as an `initialObjects` entry
    must be rejected by the new `bootVSpaceRootObjIdDistinct` gate. -/
private def tph015f_objIdCollisionRejected : IO Unit := do
  -- Construct an initial object (a TCB) at the same ObjId as the
  -- canonical RPi5 boot VSpace (`rpi5BootVSpaceRootObjId`).  Per
  -- audit plan §7.3 R3.3, this collision must surface as a config
  -- error.  WS-RC R3 audit fix: tracked ObjIds are now ObjId 1 (not
  -- the reserved sentinel ObjId 0), so the test exercises a real
  -- non-sentinel collision.
  let tcb : KernelObject := KernelObject.tcb
    { tid := ⟨1⟩, priority := ⟨0⟩, domain := ⟨0⟩,
      cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩,
      ipcBuffer := (SeLe4n.VAddr.ofNat 0) }
  let entry : ObjectEntry := {
    id := SeLe4n.Platform.RPi5.rpi5BootVSpaceRootObjId
    obj := tcb
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }
  let cfg : PlatformConfig :=
    { irqTable := [], initialObjects := [entry],
      machineConfig := SeLe4n.defaultMachineConfig
      bootVSpaceRoot := some SeLe4n.Platform.RPi5.rpi5BootVSpaceRootEntry }
  match bootFromPlatformChecked cfg with
  | .ok _ =>
      throw <| IO.userError "tph015f: ObjId collision should be rejected, but boot succeeded"
  | .error _ =>
      expect "TPH-015g ObjId collision between initialObjects and bootVSpaceRoot rejected" true

/-- TPH-015i (audit fix for Issue #2; WS-BP BP3.2): the *kernel's* boot
    VSpaceRoot in `initialObjects` is rejected.  Since BP3.2 a configured
    VSpace root is admitted as a thread's address space — its ASID is
    registered as the runtime store registers one — but it must be a *user*
    root (`bootSafeUserVSpaceRootCheck`: a user ASID, no mappings), and the
    kernel's map is neither.  The retired `noVSpaceRootsInInitialObjects` gate
    refused this for a different reason (no ASID registration); the refusal
    survives it because the object is the wrong kind of root. -/
private def tph015i_vspaceRootInInitialObjectsRejected : IO Unit := do
  -- Place the canonical RPi5 boot VSpace in `initialObjects` (instead
  -- of in the dedicated `bootVSpaceRoot` field).  The user-root check
  -- must reject this misconfiguration.
  let entry : ObjectEntry := {
    id := SeLe4n.ObjId.ofNat 7  -- arbitrary non-sentinel ObjId
    obj := KernelObject.vspaceRoot SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => by
      cases h
      exact SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot_mappings_invExt }
  let cfg : PlatformConfig :=
    { irqTable := [], initialObjects := [entry],
      machineConfig := SeLe4n.defaultMachineConfig
      bootVSpaceRoot := none }
  match bootFromPlatformChecked cfg with
  | .ok _ =>
      throw <| IO.userError "tph015i: VSpaceRoot in initialObjects should be rejected, but boot succeeded"
  | .error _ =>
      expect "TPH-015h VSpaceRoot in initialObjects rejected (audit fix Issue #2)" true

/-- TPH-015j (audit fix for Issue #3): Sentinel ObjId for boot
    VSpaceRoot rejected.  The `bootVSpaceRootObjIdNonSentinel` gate
    forbids using `ObjId.sentinel` (= ObjId 0) for the boot VSpace
    since the sentinel is reserved as "unallocated" per H-06/WS-E3. -/
private def tph015j_sentinelBootVSpaceObjIdRejected : IO Unit := do
  -- Construct a boot VSpaceRoot entry at the reserved sentinel ObjId.
  let entry : SeLe4n.Platform.BootVSpaceRootEntry := {
    id := SeLe4n.ObjId.sentinel
    root := SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot
    hMappings := SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot_mappings_invExt }
  let cfg : PlatformConfig :=
    { irqTable := [], initialObjects := [],
      machineConfig := SeLe4n.defaultMachineConfig
      bootVSpaceRoot := some entry }
  match bootFromPlatformChecked cfg with
  | .ok _ =>
      throw <| IO.userError "tph015j: sentinel boot VSpace ObjId should be rejected, but boot succeeded"
  | .error _ =>
      expect "TPH-015i sentinel boot VSpace ObjId rejected (audit fix Issue #3)" true

/-- TPH-015k (audit fix): Boot-safety gate rejects malformed boot
    VSpaceRoot.  An empty-mappings root fails `bootSafeVSpaceRootCheck`
    because the non-empty conjunct is required (an empty L1 table
    cannot serve the kernel's first instruction fetch). -/
private def tph015k_unsafeBootVSpaceRejected : IO Unit := do
  -- Build a malformed root with empty mappings (size = 0).
  let unsafeRoot : VSpaceRoot :=
    { asid := SeLe4n.ASID.ofNat 0
      mappings := (SeLe4n.Kernel.RobinHood.RHTable.empty 16) }
  let entry : SeLe4n.Platform.BootVSpaceRootEntry := {
    id := SeLe4n.ObjId.ofNat 1
    root := unsafeRoot
    hMappings := SeLe4n.Kernel.RobinHood.RHTable.empty_invExt 16 (by omega) }
  let cfg : PlatformConfig :=
    { irqTable := [], initialObjects := [],
      machineConfig := SeLe4n.defaultMachineConfig
      bootVSpaceRoot := some entry }
  match bootFromPlatformChecked cfg with
  | .ok _ =>
      throw <| IO.userError "tph015k: unsafe boot VSpace (empty mappings) should be rejected, but boot succeeded"
  | .error _ =>
      expect "TPH-015j unsafe boot VSpace rejected by bootVSpaceRootSafe gate" true

/-- TPH-015l (third-audit fix for canonical-VAddr gap): Boot-safety
    gate rejects boot VSpaceRoots whose mappings contain a
    non-canonical virtual address (vaddr ≥ 2^48).  Defense-in-depth:
    on ARMv8-A hardware, vaddrs in `[2^48, 2^64 - 2^48)` translation-
    fault before the kernel can intercept them, so a config that
    leaks a non-canonical vaddr through the boot VSpace would crash
    the kernel before it could surface a runtime error. -/
private def tph015l_nonCanonicalVAddrRejected : IO Unit := do
  -- Construct a root with a single mapping at a non-canonical vaddr
  -- (2^48 is the first non-canonical address — it lies in the
  -- ARMv8-A reserved gap).  paddr stays within 2^44 so paddrBounded
  -- alone passes; the only failing conjunct is vaddrCanonical.
  let safePerms : PagePermissions :=
    { read := true, write := false, execute := false, user := false, cacheable := false }
  let nonCanonicalRoot : VSpaceRoot :=
    { asid := SeLe4n.ASID.ofNat 0
      mappings := (SeLe4n.Kernel.RobinHood.RHTable.empty 16
                    : SeLe4n.Kernel.RobinHood.RHTable VAddr (PAddr × PagePermissions)).insert
        (VAddr.ofNat (2^48)) (PAddr.ofNat 0x1000, safePerms) }
  let entry : SeLe4n.Platform.BootVSpaceRootEntry := {
    id := SeLe4n.ObjId.ofNat 1
    root := nonCanonicalRoot
    hMappings :=
      SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _
        (SeLe4n.Kernel.RobinHood.RHTable.empty_invExt 16 (by omega)) }
  let cfg : PlatformConfig :=
    { irqTable := [], initialObjects := [],
      machineConfig := SeLe4n.defaultMachineConfig
      bootVSpaceRoot := some entry }
  match bootFromPlatformChecked cfg with
  | .ok _ =>
      throw <| IO.userError "tph015l: non-canonical vaddr boot VSpace should be rejected, but boot succeeded"
  | .error _ =>
      expect "TPH-015k non-canonical vaddr boot VSpace rejected by vaddrCanonical conjunct" true

/-- TPH-015g (WS-BP BP3.2): the object sweep refuses the kernel's boot
    VSpaceRoot as a *configured* object — the runtime evaluation of
    `bootSafeObjectCheck_refuses_rpi5BootVSpaceRoot`.  The binding's root is
    admitted where it is installed (`bootVSpaceRootSafe`, TPH-015a); the sweep
    asks the thread's question, and the kernel's map is not a thread's. -/
private def tph015g_admissionWitness : IO Unit := do
  expect "TPH-015l bootSafeObjectCheck refuses rpi5BootVSpaceRoot as a configured object"
    (!bootSafeObjectCheck (KernelObject.vspaceRoot
      SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot))

/-- TPH-015h: Sim-platform parity.  The simulation boot VSpaceRoot passes
    the binding-root check (`bootSafeVSpaceRootCheck`) and — like the RPi5
    root — is refused by the configured-object sweep. -/
private def tph015h_simBootVSpaceRoot : IO Unit := do
  expect "TPH-015m simBootVSpaceRoot passes the binding-root check"
    (SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeVSpaceRootCheck
      SeLe4n.Platform.Sim.simBootVSpaceRoot)
  expect "TPH-015m bootSafeObjectCheck refuses simBootVSpaceRoot as a configured object"
    (!bootSafeObjectCheck (KernelObject.vspaceRoot
      SeLe4n.Platform.Sim.simBootVSpaceRoot))

/-- WS-BP BP3.2: an empty user VSpace root on `asid`, as a configured entry
    at `id`. -/
private def userRootEntry (id asid : Nat) : ObjectEntry :=
  { id := SeLe4n.ObjId.ofNat id
    obj := KernelObject.vspaceRoot
      { asid := SeLe4n.ASID.ofNat asid, mappings := SeLe4n.Kernel.RobinHood.RHTable.empty 16 }
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => by
      cases h; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt 16 (by omega) }

/-- WS-BP BP3.2: a config carrying the RPi5 binding root and `objs`. -/
private def withRpi5Root (objs : List ObjectEntry) : PlatformConfig :=
  { irqTable := [], initialObjects := objs,
    machineConfig := SeLe4n.defaultMachineConfig
    bootVSpaceRoot := some SeLe4n.Platform.RPi5.rpi5BootVSpaceRootEntry }

/-- TPH-015n (WS-BP BP3.2): a configured thread's VSpace root is admitted
    **and its ASID is registered** — the write whose absence was the whole
    reason the retired gate refused every configured root.  The binding's root
    keeps its own ASID alongside it. -/
private def tph015n_userVSpaceAdmittedAndRegistered : IO Unit := do
  match bootFromPlatformChecked (withRpi5Root [userRootEntry 9 1]) with
  | .error e => throw <| IO.userError s!"tph015n: user VSpace root refused: {e}"
  | .ok ist =>
      expect "TPH-015n configured user VSpace root admitted with its ASID registered"
        (ist.state.asidTable[SeLe4n.ASID.ofNat 1]? == some (SeLe4n.ObjId.ofNat 9))
      expect "TPH-015n binding root keeps ASID 0 beside it"
        (ist.state.asidTable[SeLe4n.ASID.ofNat 0]? ==
          some SeLe4n.Platform.RPi5.rpi5BootVSpaceRootObjId)

/-- TPH-015o (WS-BP BP3.2): two VSpace roots on one ASID are refused —
    between two configured roots, and between a configured root and the
    binding's.  A registration is an insert, so a collision would re-point
    the first root's ASID at the second. -/
private def tph015o_asidCollisionRefused : IO Unit := do
  expect "TPH-015o two configured roots on one ASID refused"
    (!(bootFromPlatformChecked (withRpi5Root [userRootEntry 9 1, userRootEntry 10 1])).isOk)
  expect "TPH-015o distinct ASIDs admitted (control)"
    ((bootFromPlatformChecked (withRpi5Root [userRootEntry 9 1, userRootEntry 10 2])).isOk)
  expect "TPH-015o configured root on the binding root's ASID refused"
    (!bootVSpaceAsidsDistinct
      { withRpi5Root [userRootEntry 9 1] with
        bootVSpaceRoot := some { SeLe4n.Platform.RPi5.rpi5BootVSpaceRootEntry with
          root := { SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot with
            asid := SeLe4n.ASID.ofNat 1 } } })

/-- TPH-015p (WS-BP BP3.2): a configured root on the kernel's ASID, or one
    carrying a mapping, is refused by the user-root check — the mapping because
    no boot check places the physical memory it names. -/
private def tph015p_userRootShapeRefused : IO Unit := do
  expect "TPH-015p configured root on ASID 0 refused"
    (!(bootFromPlatformChecked (withRpi5Root [userRootEntry 9 0])).isOk)
  let mapped : ObjectEntry :=
    { id := SeLe4n.ObjId.ofNat 9
      obj := KernelObject.vspaceRoot
        { asid := SeLe4n.ASID.ofNat 1
          mappings := (SeLe4n.Kernel.RobinHood.RHTable.empty 16
              : SeLe4n.Kernel.RobinHood.RHTable VAddr (PAddr × PagePermissions)).insert
            (VAddr.ofNat 0x1000)
            (PAddr.ofNat 0x80000,
              { read := true, write := false, execute := true, user := true,
                cacheable := true }) }
      hSlots := fun _ h => nomatch h
      hMappings := fun _ h => by
        cases h
        exact SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _
          (SeLe4n.Kernel.RobinHood.RHTable.empty_invExt 16 (by omega)) }
  expect "TPH-015p configured root carrying a mapping (here: the kernel image) refused"
    (!(bootFromPlatformChecked (withRpi5Root [mapped])).isOk)

end SeLe4n.Testing.TwoPhaseArchSuite

-- ============================================================================
-- Main test runner
-- ============================================================================

open SeLe4n.Testing.TwoPhaseArchSuite in
def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  Q9-A Two-Phase Architecture Integration Suite"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  IO.println "--- TPH-001: Builder Pipeline ---"
  tph001a_emptyBuilder
  tph001b_builderPipeline
  tph001c_builderIrq

  IO.println "--- TPH-003: Freeze Populated + Lookup Equiv ---"
  tph003_freezePopulated

  IO.println "--- TPH-005: Frozen IPC Send/Receive ---"
  tph005a_sendBlocks
  tph005b_receiveBlocks
  tph005c_callBlocksForReply

  IO.println "--- TPH-006: Frozen Scheduler Tick (Active) ---"
  tph006a_timerTickActive
  tph006b_timerTickExpiry
  tph006c_timerTickExpiryCustomConfig

  IO.println "--- TPH-010: Commutativity ---"
  tph010_commutativity

  IO.println "--- TPH-012: Pre-Allocated Slot Retype ---"
  tph012_preallocatedSlot

  IO.println "--- TPH-014: RunQueue Frozen Operations ---"
  tph014a_frozenSchedule
  tph014b_frozenYield
  tph014c_scheduleNoEligible

  IO.println "--- TPH-015: WS-RC R3 Boot VSpaceRoot Threading ---"
  tph015a_bootSucceeds
  tph015b_postBootHasVSpaceRoot
  tph015c_postBootWxInvariantHolds
  tph015d_asidTableHasBootRoot
  tph015e_noBootVSpaceCompat
  tph015f_objIdCollisionRejected
  tph015g_admissionWitness
  tph015h_simBootVSpaceRoot
  tph015i_vspaceRootInInitialObjectsRejected
  tph015n_userVSpaceAdmittedAndRegistered
  tph015o_asidCollisionRefused
  tph015p_userRootShapeRefused
  tph015j_sentinelBootVSpaceObjIdRejected
  tph015k_unsafeBootVSpaceRejected
  tph015l_nonCanonicalVAddrRejected

  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  All 27 two-phase architecture tests passed!"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
