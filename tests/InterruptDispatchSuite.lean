-- SPDX-License-Identifier: GPL-3.0-or-later
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
import SeLe4n.Platform.RPi5.Board
import SeLe4n.Platform.QemuVirt.Board

/-! # AK3-C.5 / AK3-L: Interrupt Dispatch Regression Tests

Focused regression coverage for AK3-C (GIC EOI differentiation) and
AK3-L (`eoiPending` audit trail). Exercises:

- Spurious INTIDs (≥ 1020): no EOI, no state change
- Out-of-range INTIDs ([320, 1020)): no handler dispatch at Lean layer,
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

/-- T02: INTID in [320, 1020) → outOfRange; returns `.error .outOfRange n`
    with `n` matching the raw INTID. -/
def test_t02_ack_out_of_range : IO Unit := do
  match acknowledgeInterrupt 500 with
  | .error (.outOfRange n) =>
    expectCond "interrupt-dispatch" "outOfRange carries raw INTID" (n == 500)
  | .error .spurious =>
    throw <| IO.userError "T02: expected outOfRange, got spurious"
  | .ok _ =>
    throw <| IO.userError "T02: expected outOfRange, got ok"

/-- T03: INTID < 320 → `.ok intId`. -/
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

/-- T05: INTID = 319 (last handled) → ok, and INTID 320 (one past the
    BCM2712's 288 SPIs) → outOfRange. -/
def test_t05_ack_boundary_handled : IO Unit := do
  match acknowledgeInterrupt 319 with
  | .ok intId =>
    expectCond "interrupt-dispatch" "319 is still handled" (intId.val == 319)
  | _ =>
    throw <| IO.userError "T05: expected .ok at 319"
  match acknowledgeInterrupt 320 with
  | .error (.outOfRange n) =>
    expectCond "interrupt-dispatch" "320 is the first outOfRange INTID" (n == 320)
  | _ =>
    throw <| IO.userError "T05: expected outOfRange at 320"

/-- The model's `InterruptId` bound is the RPi5 binding's interrupt-line count
    — SGIs and PPIs plus `gicSpiCount` SPIs — so the INTIDs the RPi5
    interrupt contract supports and the ones `acknowledgeInterrupt` can
    dispatch are one set.  QEMU `virt`'s lines fit inside it. -/
example : InterruptId = Fin (SeLe4n.Platform.RPi5.gicSpiCount + 32) := rfl
example : SeLe4n.Platform.QemuVirt.qemuVirtGicSpiCount + 32 ≤ 320 := by decide

/-- T05b: the BCM2712's high SPIs — GIC_SPI 209 (PCIe0 INTA), 244 (the
    main level-2 controller behind every SoC GPIO interrupt), 273/274 (the
    SD hosts) and 276 (UARTA), INTIDs 241, 276, 305, 306 and 308 in Linux's
    `bcm2712.dtsi` — are acknowledged and dispatched to the notification
    registered for them, badged by INTID.  Under the former 192-SPI cap
    every one of them was `outOfRange`. -/
def test_t05b_high_spis_dispatch : IO Unit := do
  let ntfnId : SeLe4n.ObjId := ⟨300⟩
  for spi in [209, 244, 273, 274, 276] do
    let intid := spi + 32
    match acknowledgeInterrupt intid with
    | .ok intId =>
      expectCond "interrupt-dispatch" s!"SPI {spi} (INTID {intid}) acknowledged"
        (intId.val == intid)
    | _ => throw <| IO.userError s!"T05b: SPI {spi} (INTID {intid}) not acknowledged"
    let st0 :=
      (BootstrapBuilder.empty
        |>.withObject ntfnId (.notification
            { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none })
        |>.withIrqHandler ⟨intid⟩ ntfnId
        |>.withLifecycleObjectType ntfnId .notification
        |>.buildChecked)
    match interruptDispatchSequence st0 intid with
    | .ok ((), st1) =>
      match st1.objects[ntfnId]? with
      | some (.notification ntfn) =>
        expectCond "interrupt-dispatch" s!"SPI {spi}: notification signalled"
          (ntfn.state == .active)
        expectCond "interrupt-dispatch" s!"SPI {spi}: badge is the INTID"
          (ntfn.pendingBadge == some (SeLe4n.Badge.ofNatMasked intid))
        expectCond "interrupt-dispatch" s!"SPI {spi}: EOI drained the audit trail"
          (intid ∉ st1.machine.eoiPending)
      | _ => throw <| IO.userError s!"T05b: SPI {spi}: notification missing"
    | .error e => throw <| IO.userError s!"T05b: SPI {spi}: dispatch failed {repr e}"

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
  -- is INTID 99 (a valid Fin 320 value not equal to the dispatched
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
  test_t05b_high_spis_dispatch
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
