-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.InterruptDispatch
import SeLe4n.Kernel.Architecture.ExceptionModel
import SeLe4n.Testing.Helpers
import SeLe4n.Testing.StateBuilder

/-! # AK3-C.5 / AK3-L / WS-RC R6.A: Interrupt Dispatch Regression Tests

Focused regression coverage for AK3-C (GIC EOI differentiation),
AK3-L (`eoiPending` audit trail), AN8-C (ack → EOI → handle ordering),
and **WS-RC R6.A** (DEEP-ARCH-03 — the formal Lean-level GIC bridge
from `ExceptionModel` to `InterruptDispatch`).

Exercises:

- Spurious INTIDs (≥ 1020): no EOI, no state change
- Out-of-range INTIDs ([224, 1020)): no handler dispatch at Lean layer,
  HAL handles EOI
- In-range INTIDs: handler runs, EOI emitted via `endOfInterrupt`
- `eoiPending` audit trail: populated on ack, drained on EOI, empty
  after round-trip
- **WS-RC R6.A**: `interruptDispatchSchedule` symbolic ordering
  (AN8-C `[.ack, .eoi, .handle]`); `classifyIrqInterruptId`
  consistency with `acknowledgeInterrupt`;
  `exception_irq_dispatches_via_interrupt_dispatch` bridge theorem
  reachability; `GicDispatchBridgeBundle` composition.
-/

open SeLe4n.Kernel.Architecture
open SeLe4n.Testing

namespace SeLe4n.Testing.InterruptDispatch

/-- T01: INTID ≥ 1020 → spurious; `acknowledgeInterrupt` returns
    `.error .spurious`. -/
def test_t01_ack_spurious : IO Unit := do
  match acknowledgeInterrupt 1023 with
  | .error .spurious =>
    IO.println "check passed [spurious threshold]"
  | .error (.outOfRange _) =>
    throw <| IO.userError "T01: expected spurious, got outOfRange"
  | .ok _ =>
    throw <| IO.userError "T01: expected spurious, got ok"

/-- T02: INTID in [224, 1020) → outOfRange; returns `.error .outOfRange n`
    with `n` matching the raw INTID. -/
def test_t02_ack_out_of_range : IO Unit := do
  match acknowledgeInterrupt 500 with
  | .error (.outOfRange n) =>
    expectCond "interrupt-dispatch" "outOfRange carries raw INTID" (n == 500)
  | .error .spurious =>
    throw <| IO.userError "T02: expected outOfRange, got spurious"
  | .ok _ =>
    throw <| IO.userError "T02: expected outOfRange, got ok"

/-- T03: INTID < 224 → `.ok intId`. -/
def test_t03_ack_handled : IO Unit := do
  match acknowledgeInterrupt 30 with
  | .ok intId =>
    expectCond "interrupt-dispatch" "handled INTID value" (intId.val == 30)
  | .error _ =>
    throw <| IO.userError "T03: expected .ok, got error"

/-- T04: INTID = 1020 (first spurious) → spurious, not outOfRange. -/
def test_t04_ack_boundary_spurious : IO Unit := do
  match acknowledgeInterrupt 1020 with
  | .error .spurious =>
    IO.println "check passed [1020 is spurious]"
  | _ =>
    throw <| IO.userError "T04: expected spurious at 1020"

/-- T05: INTID = 223 (last handled) → ok, not outOfRange. -/
def test_t05_ack_boundary_handled : IO Unit := do
  match acknowledgeInterrupt 223 with
  | .ok intId =>
    expectCond "interrupt-dispatch" "223 is still handled" (intId.val == 223)
  | _ =>
    throw <| IO.userError "T05: expected .ok at 223"

/-- T06: AK3-L — `ackInterruptAudit` prepends to `eoiPending`. -/
def test_t06_ack_audit_push : IO Unit := do
  let st : SeLe4n.Model.SystemState := default
  let st' := ackInterruptAudit st 42
  expectCond "interrupt-dispatch" "eoiPending has ack entry"
    (st'.machine.eoiPending == [42])

/-- T07: AK3-L — `endOfInterrupt` filters the INTID from `eoiPending`. -/
def test_t07_eoi_drains : IO Unit := do
  let st : SeLe4n.Model.SystemState := default
  let intId : InterruptId := ⟨30, by omega⟩
  let stAck := ackInterruptAudit st intId.val
  let stEoi := endOfInterrupt stAck intId
  expectCond "interrupt-dispatch" "EOI removes from pending"
    (30 ∉ stEoi.machine.eoiPending)

/-- T08: AK3-L — ack→EOI round trip with empty initial state → empty final
    state (kernel-exit invariant). -/
def test_t08_round_trip_empty : IO Unit := do
  let st : SeLe4n.Model.SystemState := default
  let intId : InterruptId := ⟨30, by omega⟩
  expectCond "interrupt-dispatch" "initial eoiPending empty"
    (st.machine.eoiPending == [])
  let stAck := ackInterruptAudit st intId.val
  let stEoi := endOfInterrupt stAck intId
  expectCond "interrupt-dispatch" "round-trip preserves empty eoiPending"
    (stEoi.machine.eoiPending == [])

/-- T09: AK3-C — `interruptDispatchSequence` for spurious returns state
    unchanged (no ack entry, no EOI). -/
def test_t09_dispatch_spurious_no_state_change : IO Unit := do
  let st : SeLe4n.Model.SystemState := default
  match interruptDispatchSequence st 1023 with
  | .ok ((), st') =>
    expectCond "interrupt-dispatch" "spurious: machine.eoiPending unchanged"
      (st'.machine.eoiPending == st.machine.eoiPending)
  | .error _ =>
    throw <| IO.userError "T09: dispatch of spurious returned error"

/-- T10: AK3-C — out-of-range INTID → dispatch returns `.ok` with state
    unchanged at Lean layer. -/
def test_t10_dispatch_out_of_range : IO Unit := do
  let st : SeLe4n.Model.SystemState := default
  match interruptDispatchSequence st 500 with
  | .ok ((), st') =>
    expectCond "interrupt-dispatch" "outOfRange: machine.eoiPending unchanged"
      (st'.machine.eoiPending == st.machine.eoiPending)
  | .error _ =>
    throw <| IO.userError "T10: dispatch of outOfRange returned error"

/-- T11: AN8-C (H-19) — round-trip property: after a successful dispatch
    of INTID 30 (the timer PPI, which routes to `timerTick`), the INTID
    is NOT present in `machine.eoiPending` in the final state. This is
    the AK3-L `eoiPendingEmpty` invariant exercised through the AN8-C
    `ack → EOI → handle` path; both pre- and post-AN8-C orderings
    satisfy it (because both emit EOI). The substantive ordering
    distinction is captured by the proof-layer theorem referenced in
    T13; this test additionally verifies the round-trip on the success
    branch (`timerTick` returns `.ok`). -/
def test_t11_eoi_before_handler : IO Unit := do
  let st : SeLe4n.Model.SystemState := default
  -- INTID 30 = `timerInterruptId`; `handleInterrupt` routes to
  -- `timerTick`, which succeeds on default state.
  match interruptDispatchSequence st 30 with
  | .ok ((), st') =>
    expectCond "interrupt-dispatch" "AN8-C: 30 not in final eoiPending (EOI fired)"
      (30 ∉ st'.machine.eoiPending)
  | .error _ =>
    throw <| IO.userError "T11: dispatch of 30 returned error"

/-- T12: AN8-C (H-19) — substantive ordering verification: pre-load the
    audit trail with a sentinel INTID, dispatch a different handled
    INTID, and verify the dispatched INTID is filtered while the
    sentinel survives. This proves `endOfInterrupt` ran on a state
    derived from `ackInterruptAudit` (the `endOfInterrupt → handler`
    path) — not the old `handler → endOfInterrupt` path which would
    have left the ack record visible to the handler. -/
def test_t12_eoi_filters_only_target_intid : IO Unit := do
  -- Build a state with a sentinel ack already pending. The sentinel
  -- is INTID 99 (a valid Fin 224 value not equal to the dispatched
  -- INTID 30). A correct EOI ordering filters only INTID 30 and
  -- leaves the sentinel.
  let st0 : SeLe4n.Model.SystemState := default
  let stSentinel := ackInterruptAudit st0 99
  expectCond "interrupt-dispatch" "T12 precondition: sentinel 99 in eoiPending"
    (99 ∈ stSentinel.machine.eoiPending)
  -- Dispatch INTID 30. Because no handler is registered, the sequence
  -- takes the error branch; under AN8-C this returns the post-EOI
  -- state directly. Under the OLD ordering, EOI would have been
  -- skipped on the error branch — so this test is a regression guard
  -- against any future revert to `ack → handle → EOI`.
  match interruptDispatchSequence stSentinel 30 with
  | .ok ((), st') =>
    expectCond "interrupt-dispatch" "T12: target INTID 30 filtered by EOI"
      (30 ∉ st'.machine.eoiPending)
    expectCond "interrupt-dispatch" "T12: sentinel INTID 99 preserved"
      (99 ∈ st'.machine.eoiPending)
  | .error _ =>
    throw <| IO.userError "T12: dispatch returned error unexpectedly"

/-- T13: AN8-C.5 (H-19) — type-level witness verifying the
    `interruptDispatchSequence_eoi_before_handler` theorem exists with
    its precise signature. The reference at parse time forces
    elaboration; if the theorem is renamed, removed, or its conclusion
    changes, this file fails to compile. -/
def test_t13_ordering_theorem_witness : IO Unit := do
  let _witness := @interruptDispatchSequence_eoi_before_handler
  IO.println "check passed [AN8-C.5 eoi_before_handler theorem elaborated]"

-- ----------------------------------------------------------------------------
-- WS-RC R6.A (DEEP-ARCH-03): GIC bridge regression tests
-- ----------------------------------------------------------------------------

/-- T14 (R6.A): `interruptDispatchSchedule` produces exactly the
    AN8-C canonical 3-step list `[.ack, .eoi, .handle]`. -/
def test_t14_schedule_canonical : IO Unit := do
  let id : InterruptId := ⟨30, by omega⟩
  let schedule := interruptDispatchSchedule id
  expectCond "interrupt-dispatch" "schedule has 3 ops"
    (schedule.length == 3)
  expectCond "interrupt-dispatch" "schedule is canonical [ack, eoi, handle]"
    (schedule = [InterruptOp.ack id, InterruptOp.eoi id, InterruptOp.handle id])

/-- T15 (R6.A): The schedule's HEAD is `.ack` — encodes the GIC-400
    §3.1 invariant that IAR read precedes all other GIC interactions. -/
def test_t15_schedule_head_is_ack : IO Unit := do
  let id : InterruptId := ⟨42, by omega⟩
  let schedule := interruptDispatchSchedule id
  match schedule with
  | InterruptOp.ack idHead :: _ =>
    expectCond "interrupt-dispatch" "head ack carries correct INTID"
      (idHead.val == 42)
  | _ =>
    throw <| IO.userError "T15: schedule head is not .ack"

/-- T16 (R6.A): AN8-C ordering — EOI precedes Handle in the schedule. -/
def test_t16_schedule_eoi_before_handle : IO Unit := do
  let id : InterruptId := ⟨123, by omega⟩
  let schedule := interruptDispatchSchedule id
  match schedule with
  | _ :: InterruptOp.eoi _ :: InterruptOp.handle _ :: [] =>
    IO.println "check passed [R6.A AN8-C eoi precedes handle]"
  | _ =>
    throw <| IO.userError "T16: schedule does not match [_, .eoi, .handle]"

/-- T17 (R6.A): `classifyIrqInterruptId` for a spurious INTID returns
    `none`. Mirrors `acknowledgeInterrupt`'s spurious arm. -/
def test_t17_classify_spurious : IO Unit := do
  match classifyIrqInterruptId 1023 with
  | none => IO.println "check passed [R6.A classify spurious → none]"
  | some _ =>
    throw <| IO.userError "T17: spurious INTID classified to some"

/-- T18 (R6.A): `classifyIrqInterruptId` for an out-of-range INTID
    (224..1019) returns `none`. -/
def test_t18_classify_out_of_range : IO Unit := do
  match classifyIrqInterruptId 500 with
  | none => IO.println "check passed [R6.A classify outOfRange → none]"
  | some _ =>
    throw <| IO.userError "T18: out-of-range INTID classified to some"

/-- T19 (R6.A): `classifyIrqInterruptId` for a valid INTID (0..223)
    returns `some intId` with the correct value. -/
def test_t19_classify_valid : IO Unit := do
  match classifyIrqInterruptId 30 with
  | some intId =>
    expectCond "interrupt-dispatch" "classify ok carries correct INTID"
      (intId.val == 30)
  | none =>
    throw <| IO.userError "T19: valid INTID classified to none"

/-- T20 (R6.A): Classification is consistent with `acknowledgeInterrupt`
    — `classifyIrqInterruptId rawIntId = some intId` iff
    `acknowledgeInterrupt rawIntId = .ok intId`. -/
def test_t20_classify_iff_acknowledge : IO Unit := do
  -- Valid INTID: both succeed with same value
  match classifyIrqInterruptId 30, acknowledgeInterrupt 30 with
  | some i1, .ok i2 =>
    expectCond "interrupt-dispatch" "classify/ack agree on valid INTID"
      (i1.val == i2.val)
  | _, _ =>
    throw <| IO.userError "T20a: classify/ack disagreed on 30"
  -- Spurious: both fail
  match classifyIrqInterruptId 1023, acknowledgeInterrupt 1023 with
  | none, .error .spurious =>
    IO.println "check passed [R6.A classify/ack agree on spurious]"
  | _, _ =>
    throw <| IO.userError "T20b: classify/ack disagreed on spurious"

/-- T21 (R6.A): Bridge theorem
    `exception_irq_dispatches_via_interrupt_dispatch` is reachable
    with its exact signature. Compile-time witness. -/
def test_t21_bridge_theorem_reachable : IO Unit := do
  let _witness := @exception_irq_dispatches_via_interrupt_dispatch
  IO.println "check passed [R6.A bridge theorem elaborated]"

/-- T22 (R6.A.3): `GicDispatchBridgeBundle` composition witness
    `architectureGicDispatchBridgeBundle` is reachable. -/
def test_t22_bridge_bundle_reachable : IO Unit := do
  let bundle : GicDispatchBridgeBundle := architectureGicDispatchBridgeBundle
  let id : InterruptId := ⟨30, by omega⟩
  -- Verify the bundle's fields produce the expected schedule.
  let schedCanonical := bundle.schedule_canonical id
  let _ : interruptDispatchSchedule id =
      [InterruptOp.ack id, InterruptOp.eoi id, InterruptOp.handle id] :=
    schedCanonical
  IO.println "check passed [R6.A.3 bridge bundle composition witness reachable]"

/-- T23 (R6.A): Architecture-invariant-family anchor theorem is
    reachable. -/
def test_t23_architecture_anchor : IO Unit := do
  let _marker := r6a_gicDispatchBridge_in_architectureInvariantFamily
  IO.println "check passed [R6.A architecture-invariant-family anchor]"

/-- Running entry. -/
def runAllTests : IO Unit := do
  IO.println "=== AK3-C + AK3-L + AN8-C + WS-RC R6.A InterruptDispatch regression suite ==="
  test_t01_ack_spurious
  test_t02_ack_out_of_range
  test_t03_ack_handled
  test_t04_ack_boundary_spurious
  test_t05_ack_boundary_handled
  test_t06_ack_audit_push
  test_t07_eoi_drains
  test_t08_round_trip_empty
  test_t09_dispatch_spurious_no_state_change
  test_t10_dispatch_out_of_range
  test_t11_eoi_before_handler
  test_t12_eoi_filters_only_target_intid
  test_t13_ordering_theorem_witness
  test_t14_schedule_canonical
  test_t15_schedule_head_is_ack
  test_t16_schedule_eoi_before_handle
  test_t17_classify_spurious
  test_t18_classify_out_of_range
  test_t19_classify_valid
  test_t20_classify_iff_acknowledge
  test_t21_bridge_theorem_reachable
  test_t22_bridge_bundle_reachable
  test_t23_architecture_anchor
  IO.println "=== All InterruptDispatch tests passed ==="

end SeLe4n.Testing.InterruptDispatch

open SeLe4n.Testing.InterruptDispatch

def main : IO Unit := runAllTests
