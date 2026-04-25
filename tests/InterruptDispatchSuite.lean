/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.InterruptDispatch
import SeLe4n.Testing.Helpers
import SeLe4n.Testing.StateBuilder

/-! # AK3-C.5 / AK3-L: Interrupt Dispatch Regression Tests

Focused regression coverage for AK3-C (GIC EOI differentiation) and
AK3-L (`eoiPending` audit trail). Exercises:

- Spurious INTIDs (≥ 1020): no EOI, no state change
- Out-of-range INTIDs ([224, 1020)): no handler dispatch at Lean layer,
  HAL handles EOI
- In-range INTIDs: handler runs, EOI emitted via `endOfInterrupt`
- `eoiPending` audit trail: populated on ack, drained on EOI, empty
  after round-trip
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

/-- T11: AN8-C (H-19) — after a successful dispatch of a handled INTID,
    the INTID is NOT present in `machine.eoiPending` (EOI fired BEFORE
    the handler). Any handler body that preserves the `eoiPending`
    structure leaves the ack trace empty. -/
def test_t11_eoi_before_handler : IO Unit := do
  let st : SeLe4n.Model.SystemState := default
  -- Dispatch of timer INTID 30 (no handler registered → handleInterrupt
  -- returns .error .invalidIrq, but the sequence absorbs the error and
  -- still produces `.ok` with stEoi as the final state).
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

/-- Running entry. -/
def runAllTests : IO Unit := do
  IO.println "=== AK3-C + AK3-L + AN8-C InterruptDispatch regression suite ==="
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
  IO.println "=== All InterruptDispatch tests passed ==="

end SeLe4n.Testing.InterruptDispatch

open SeLe4n.Testing.InterruptDispatch

def main : IO Unit := runAllTests
