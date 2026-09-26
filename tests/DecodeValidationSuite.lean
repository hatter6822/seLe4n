-- SPDX-License-Identifier: GPL-3.0-or-later
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

Focused coverage for the decode-time validation introduced in AK3:

- the VSpace map decode (AK3-E / A-M01).  WS-BP BP7.1 retired AK3-E's
  `decodeVSpaceMapArgsChecked`: MR2 is a frame capability address now, so
  there is no decoded physical address to bound — the bound applies to the
  resolved frame's `base` inside the production map wrapper.  T01–T03 pin the
  decode's new contract.
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

/-- T01: WS-BP BP7.1 — a value in MR2 above the physical-address window is a
    frame **capability address**, so the decode carries it rather than refusing
    it: the retired decode-time PA bound would have read it as an address. -/
def test_t01_high_mr2_is_a_capability_address : IO Unit := do
  let maxASID := 65536
  let stub := stubOf #[1, 0x1000, (2^44) + 1, 1]
  match decodeVSpaceMapArgs stub maxASID with
  | .ok args =>
    expectCond "decode-validation" "MR2 carried as a frame capability address"
      (args.frame == SeLe4n.CPtr.ofNat ((2^44) + 1))
  | .error e =>
    throw <| IO.userError s!"T01: expected ok, got {toString e}"

/-- T02: WS-BP BP7.1 — the decode carries MR2 verbatim as the frame capability
    address, beside the ASID, virtual address and permissions. -/
def test_t02_decode_carries_frame_cptr : IO Unit := do
  let maxASID := 65536
  let stub := stubOf #[1, 0x1000, 3, 1]
  match decodeVSpaceMapArgs stub maxASID with
  | .ok args =>
    expectCond "decode-validation" "frame cptr = MR2" (args.frame == SeLe4n.CPtr.ofNat 3)
    expectCond "decode-validation" "vaddr = MR1" (args.vaddr.toNat == 0x1000)
  | .error e =>
    throw <| IO.userError s!"T02: expected ok, got {toString e}"

/-- T03: the bound the decode still owns — a virtual address at exactly 2^48 is
    non-canonical and rejected with `.addressOutOfBounds`. -/
def test_t03_noncanonical_vaddr_boundary_rejected : IO Unit := do
  let maxASID := 65536
  let stub := stubOf #[1, 2^48, 3, 1]
  match decodeVSpaceMapArgs stub maxASID with
  | .error .addressOutOfBounds =>
    IO.println "check passed [VAddr = 2^48 rejected (non-canonical)]"
  | _ =>
    throw <| IO.userError "T03: expected addressOutOfBounds at the canonical boundary"

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
  test_t01_high_mr2_is_a_capability_address
  test_t02_decode_carries_frame_cptr
  test_t03_noncanonical_vaddr_boundary_rejected
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
