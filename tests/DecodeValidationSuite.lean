/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.SyscallArgDecode
import SeLe4n.Testing.Helpers

open SeLe4n.Model

/-! # AK3-E + AK3-J: Decode-time validation regression tests

Focused coverage for the two decode wrapper functions introduced in AK3:

- `decodeVSpaceMapArgsChecked` (AK3-E / A-M01) — PA bounds check
- `decodeSchedContextConfigureArgsChecked` (AK3-J / A-M07) — priority,
  domain, budget, period validation

These wrappers are defense-in-depth — downstream paths also validate —
but the decode-time check prevents malformed arguments from flowing into
model analyses (e.g., NI proofs, CBS scheduler reasoning).
-/

open SeLe4n.Kernel.Architecture.SyscallArgDecode
open SeLe4n.Testing

namespace SeLe4n.Testing.DecodeValidation

/-- Helper: build a decode stub from raw register values. -/
def stubOf (vals : Array Nat) : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0
    msgInfo := { length := 0, extraCaps := 0, label := 0 }
    syscallId := .send
    msgRegs := vals.map (fun v => ⟨v⟩) }

/-- T01: AK3-E — checked decode rejects PA ≥ 2^44 (RPi5 physical limit)
    with `.addressOutOfBounds`. -/
def test_t01_checked_rejects_high_pa : IO Unit := do
  let maxASID := 65536
  let maxPA   := 2 ^ 44  -- BCM2712 / RPi5
  -- asid=1, vaddr=0x1000, paddr=2^44+1 (out of bounds), perms=1 (read-only)
  let stub := stubOf #[1, 0x1000, (2^44) + 1, 1]
  match decodeVSpaceMapArgsChecked stub maxASID maxPA with
  | .error .addressOutOfBounds =>
    IO.println "check passed [checked rejects PA ≥ 2^44]"
  | .error e =>
    throw <| IO.userError s!"T01: expected addressOutOfBounds, got {toString e}"
  | .ok _ =>
    throw <| IO.userError "T01: expected error, got ok"

/-- T02: AK3-E — checked decode accepts PA < 2^44. -/
def test_t02_checked_accepts_low_pa : IO Unit := do
  let maxASID := 65536
  let maxPA   := 2 ^ 44
  let stub := stubOf #[1, 0x1000, 0x2000, 1]
  match decodeVSpaceMapArgsChecked stub maxASID maxPA with
  | .ok args =>
    expectCond "decode-validation" "paddr in range" (args.paddr.toNat == 0x2000)
  | .error e =>
    throw <| IO.userError s!"T02: expected ok, got {toString e}"

/-- T03: AK3-E — boundary at exactly 2^44 is rejected (≥ maxPA). -/
def test_t03_checked_boundary_rejected : IO Unit := do
  let maxASID := 65536
  let maxPA   := 2 ^ 44
  let stub := stubOf #[1, 0x1000, 2^44, 1]
  match decodeVSpaceMapArgsChecked stub maxASID maxPA with
  | .error .addressOutOfBounds =>
    IO.println "check passed [PA = 2^44 rejected (≥ bound)]"
  | _ =>
    throw <| IO.userError "T03: expected addressOutOfBounds at boundary"

/-- T04: AK3-J — checked schedContextConfigure rejects priority > 255. -/
def test_t04_sc_rejects_high_priority : IO Unit := do
  -- budget=1000, period=10000, priority=256 (too high), deadline=5000, domain=0
  let stub := stubOf #[1000, 10000, 256, 5000, 0]
  match decodeSchedContextConfigureArgsChecked stub with
  | .error .invalidArgument =>
    IO.println "check passed [priority > 255 rejected]"
  | _ =>
    throw <| IO.userError "T04: expected invalidArgument for priority > 255"

/-- T05: AK3-J — checked schedContextConfigure rejects domain ≥ 16. -/
def test_t05_sc_rejects_high_domain : IO Unit := do
  let stub := stubOf #[1000, 10000, 100, 5000, 16]
  match decodeSchedContextConfigureArgsChecked stub with
  | .error .invalidArgument =>
    IO.println "check passed [domain ≥ 16 rejected]"
  | _ =>
    throw <| IO.userError "T05: expected invalidArgument for domain ≥ 16"

/-- T06: AK3-J — checked schedContextConfigure rejects budget = 0. -/
def test_t06_sc_rejects_zero_budget : IO Unit := do
  let stub := stubOf #[0, 10000, 100, 5000, 0]
  match decodeSchedContextConfigureArgsChecked stub with
  | .error .invalidArgument =>
    IO.println "check passed [budget = 0 rejected]"
  | _ =>
    throw <| IO.userError "T06: expected invalidArgument for budget = 0"

/-- T07: AK3-J — checked schedContextConfigure rejects period = 0. -/
def test_t07_sc_rejects_zero_period : IO Unit := do
  let stub := stubOf #[1000, 0, 100, 5000, 0]
  match decodeSchedContextConfigureArgsChecked stub with
  | .error .invalidArgument =>
    IO.println "check passed [period = 0 rejected]"
  | _ =>
    throw <| IO.userError "T07: expected invalidArgument for period = 0"

/-- T08: AK3-J — checked schedContextConfigure accepts valid args. -/
def test_t08_sc_accepts_valid : IO Unit := do
  -- budget=1000, period=10000, priority=100, deadline=5000, domain=1
  let stub := stubOf #[1000, 10000, 100, 5000, 1]
  match decodeSchedContextConfigureArgsChecked stub with
  | .ok args =>
    expectCond "decode-validation" "budget" (args.budget == 1000)
    expectCond "decode-validation" "period" (args.period == 10000)
    expectCond "decode-validation" "priority" (args.priority == 100)
    expectCond "decode-validation" "domain" (args.domain == 1)
  | .error e =>
    throw <| IO.userError s!"T08: expected ok, got {toString e}"

/-- T09: AK3-J — boundary: priority = 255 accepted, domain = 15 accepted. -/
def test_t09_sc_boundary_accepted : IO Unit := do
  let stub := stubOf #[1, 1, 255, 0, 15]
  match decodeSchedContextConfigureArgsChecked stub with
  | .ok args =>
    expectCond "decode-validation" "priority boundary" (args.priority == 255)
    expectCond "decode-validation" "domain boundary" (args.domain == 15)
  | .error _ =>
    throw <| IO.userError "T09: expected ok at boundary"

/-- Running entry. -/
def runAllTests : IO Unit := do
  IO.println "=== AK3-E + AK3-J Decode Validation regression suite ==="
  test_t01_checked_rejects_high_pa
  test_t02_checked_accepts_low_pa
  test_t03_checked_boundary_rejected
  test_t04_sc_rejects_high_priority
  test_t05_sc_rejects_high_domain
  test_t06_sc_rejects_zero_budget
  test_t07_sc_rejects_zero_period
  test_t08_sc_accepts_valid
  test_t09_sc_boundary_accepted
  IO.println "=== All decode validation tests passed ==="

end SeLe4n.Testing.DecodeValidation

open SeLe4n.Testing.DecodeValidation

def main : IO Unit := runAllTests
