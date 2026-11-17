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
  decode-time physical-address bound, and WS-SX SX6.3 (D6) made the words
  seL4's `Page_Map` words (address, rights, attributes): there is no decoded
  physical address to bound — the bound applies to the resolved frame's
  `base` inside the production map wrapper.  T01–T03 pin the decode's
  contract.
- `decodeSchedContextConfigureArgsChecked` (AK3-J / A-M07) — budget and
  period validation in seL4-MCS's order; the extra-refills, badge and flags
  words are carried verbatim (WS-SX SX6.4)

These wrappers are defense-in-depth — downstream paths also validate —
but the decode-time check prevents malformed arguments from flowing into
model analyses (e.g., NI proofs, CBS scheduler reasoning).
-/

open SeLe4n.Kernel.Architecture.SyscallArgDecode
open SeLe4n.Testing
open SeLe4n.Kernel (configureMinBudget configureMaxPeriod)

namespace SeLe4n.Testing.DecodeValidation

/-- Helper: build a decode stub from raw register values. -/
def stubOf (vals : Array Nat) : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0
    msgInfo := { length := vals.size, extraCaps := 0, label := 0 }
    syscallId := .send
    msgRegs := vals.map (fun v => SeLe4n.RegValue.ofNat v) }

/-- T01: WS-SX SX6.3 (D6) — the map's words are seL4's address, rights and
    attributes, read verbatim: a word above the physical-address window is no
    address the decode reads, and none is refused at decode. -/
def test_t01_high_mr2_is_a_capability_address : IO Unit := do
  let stub := stubOf #[0x1000, 2, (2^44) + 1]
  match decodePageMapArgs stub with
  | .ok args =>
    expectCond "decode-validation" "MR2 carried as the attributes word"
      (args.attr == ((2^44) + 1 : Nat).toUInt64)
  | .error e =>
    throw <| IO.userError s!"T01: expected ok, got {toString e}"

/-- T02: the operands carry the invoked frame capability and the root's ASID
    beside the address (`vspaceMapArgsOfWords`). -/
def test_t02_decode_carries_frame_cptr : IO Unit := do
  match vspaceMapArgsOfWords ⟨0x1000, 2, 5⟩ ⟨1⟩ (SeLe4n.CPtr.ofNat 3) with
  | .ok args =>
    expectCond "decode-validation" "frame cptr = the invoked capability"
      (args.frame == SeLe4n.CPtr.ofNat 3)
    expectCond "decode-validation" "vaddr = MR0" (args.vaddr.toNat == 0x1000)
  | .error e =>
    throw <| IO.userError s!"T02: expected ok, got {toString e}"

/-- T03: a virtual address at exactly 2^48 is non-canonical and refused as
    seL4 refuses `vtop > USER_TOP`, `.invalidArgument 0`. -/
def test_t03_noncanonical_vaddr_boundary_rejected : IO Unit := do
  match vspaceMapArgsOfWords ⟨(2^48 : Nat).toUInt64, 2, 5⟩ ⟨1⟩ (SeLe4n.CPtr.ofNat 3) with
  | .error (.invalidArgument 0) =>
    IO.println "check passed [VAddr = 2^48 rejected (non-canonical)]"
  | _ =>
    throw <| IO.userError "T03: expected invalidArgument 0 at the canonical boundary"

/-- T04: AK3-J — checked schedContextConfigure rejects a budget above its
period with seL4-MCS's `RangeError(MIN_BUDGET, period)`. -/
def test_t04_sc_rejects_budget_above_period : IO Unit := do
  let stub := stubOf #[10001, 10000, 0, 0, 0]
  match decodeSchedContextConfigureArgsChecked stub with
  | .error (.rangeError lo hi) =>
    if lo == configureMinBudget && hi == 10000 then
      IO.println "check passed [budget above period rejected]"
    else
      throw <| IO.userError s!"T04: expected rangeError(min budget, period), got rangeError {lo} {hi}"
  | _ =>
    throw <| IO.userError "T04: expected rangeError for a budget above its period"

/-- T05: AK3-J — checked schedContextConfigure rejects a period above
`MAX_PERIOD` with `RangeError(MIN_BUDGET, MAX_PERIOD)`. -/
def test_t05_sc_rejects_period_above_max : IO Unit := do
  let stub := stubOf #[1000, configureMaxPeriod.toNat + 1, 0, 0, 0]
  match decodeSchedContextConfigureArgsChecked stub with
  | .error (.rangeError lo hi) =>
    if lo == configureMinBudget && hi == configureMaxPeriod then
      IO.println "check passed [period above MAX_PERIOD rejected]"
    else
      throw <| IO.userError s!"T05: expected rangeError(min budget, max period), got rangeError {lo} {hi}"
  | _ =>
    throw <| IO.userError "T05: expected rangeError for a period above MAX_PERIOD"

/-- T06: AK3-J — checked schedContextConfigure rejects budget = 0. -/
def test_t06_sc_rejects_zero_budget : IO Unit := do
  let stub := stubOf #[0, 10000, 0, 0, 0]
  match decodeSchedContextConfigureArgsChecked stub with
  | .error (.rangeError lo hi) =>
    if lo == configureMinBudget && hi == configureMaxPeriod then
      IO.println "check passed [budget = 0 rejected]"
    else
      throw <| IO.userError s!"T06: expected rangeError(min budget, max period), got rangeError {lo} {hi}"
  | _ =>
    throw <| IO.userError "T06: expected rangeError for budget = 0"

/-- T07: AK3-J — checked schedContextConfigure rejects period = 0. -/
def test_t07_sc_rejects_zero_period : IO Unit := do
  let stub := stubOf #[1000, 0, 0, 0, 0]
  match decodeSchedContextConfigureArgsChecked stub with
  | .error (.rangeError lo hi) =>
    if lo == configureMinBudget && hi == configureMaxPeriod then
      IO.println "check passed [period = 0 rejected]"
    else
      throw <| IO.userError s!"T07: expected rangeError(min budget, max period), got rangeError {lo} {hi}"
  | _ =>
    throw <| IO.userError "T07: expected rangeError for period = 0"

/-- T08: AK3-J — checked schedContextConfigure accepts valid args.  WS-SX
SX6.4: the words are seL4-MCS's `SchedControl_ConfigureFlags` layout (budget,
period, extra refills, badge, flags); the context is extra capability 0. -/
def test_t08_sc_accepts_valid : IO Unit := do
  let stub := stubOf #[1000, 10000, 2, 0xBEEF, 1]
  match decodeSchedContextConfigureArgsChecked stub with
  | .ok args =>
    expectCond "decode-validation" "budget" (args.budget == 1000)
    expectCond "decode-validation" "period" (args.period == 10000)
    expectCond "decode-validation" "extra refills" (args.extraRefills == 2)
    expectCond "decode-validation" "badge" (args.badge == 0xBEEF)
    expectCond "decode-validation" "flags" (args.flags == 1)
  | .error e =>
    throw <| IO.userError s!"T08: expected ok, got {toString e}"

/-- T09: AK3-J — boundary: budget = period = the least time accepted. -/
def test_t09_sc_boundary_accepted : IO Unit := do
  let stub := stubOf #[1, 1, 0, 0, 0]
  match decodeSchedContextConfigureArgsChecked stub with
  | .ok args =>
    expectCond "decode-validation" "budget boundary" (args.budget == 1)
    expectCond "decode-validation" "period boundary" (args.period == 1)
  | .error _ =>
    throw <| IO.userError "T09: expected ok at boundary"

/-- Words with high bits set: the badge and flags take any value
(seL4-MCS stores the badge word verbatim and reads only bit 0 of the flags). -/
def highBitParamWords : List Nat :=
  [ 4096 + 100 + 1 * 256          -- bit 12
  , 2^40 + 255 + 15 * 256         -- bit 40
  , 2^63 + 7                      -- the word's top bit
  , 2^64 - 1 ]                    -- every bit

/-- T10: WS-SX SX6.4 — the checked configure decode carries the badge and flags
words verbatim, whatever bits they set: no stray high bit is refused or
truncated. -/
def test_t10_sc_keeps_badge_and_flag_words : IO Unit := do
  for w in highBitParamWords do
    match decodeSchedContextConfigureArgsChecked (stubOf #[1000, 10000, 0, w, w]) with
    | .ok args =>
      expectCond "decode-validation" s!"badge word {w} kept" (args.badge == UInt64.ofNat w)
      expectCond "decode-validation" s!"flags word {w} kept" (args.flags == UInt64.ofNat w)
    | .error e => throw <| IO.userError s!"T10: expected ok for word {w}, got {toString e}"
  IO.println "check passed [badge and flag words carried verbatim]"

/-- T11: the register-routed decode (`decodeSchedContextConfigureArgsCheckedBy`,
read on machine words) carries the same words verbatim. -/
def test_t11_sc_word_reader_keeps_badge_and_flag_words : IO Unit := do
  let reader (w : Nat) : MsgRegReader := fun i =>
    match i with
    | 0 => .ok 1000 | 1 => .ok 10000 | 2 => .ok 0 | 3 => .ok (UInt64.ofNat w)
    | 4 => .ok (UInt64.ofNat w) | _ => .error .invalidMessageInfo
  for w in highBitParamWords do
    match decodeSchedContextConfigureArgsCheckedBy (reader w) with
    | .ok args =>
      expectCond "decode-validation" s!"word reader badge {w}" (args.badge == UInt64.ofNat w)
      expectCond "decode-validation" s!"word reader flags {w}" (args.flags == UInt64.ofNat w)
    | .error e => throw <| IO.userError s!"T11: expected ok for word {w}, got {toString e}"
  IO.println "check passed [word-read badge and flag words carried verbatim]"

/-- Running entry. -/
def runAllTests : IO Unit := do
  IO.println "=== AK3-E + AK3-J Decode Validation regression suite ==="
  test_t01_high_mr2_is_a_capability_address
  test_t02_decode_carries_frame_cptr
  test_t03_noncanonical_vaddr_boundary_rejected
  test_t04_sc_rejects_budget_above_period
  test_t05_sc_rejects_period_above_max
  test_t06_sc_rejects_zero_budget
  test_t07_sc_rejects_zero_period
  test_t08_sc_accepts_valid
  test_t09_sc_boundary_accepted
  test_t10_sc_keeps_badge_and_flag_words
  test_t11_sc_word_reader_keeps_badge_and_flag_words
  IO.println "=== All decode validation tests passed ==="

end SeLe4n.Testing.DecodeValidation

open SeLe4n.Testing.DecodeValidation

def main : IO Unit := runAllTests
