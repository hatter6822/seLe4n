-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.SyscallReturn
import SeLe4n.Kernel.InformationFlow.RefusalRecord

/-!
# Every routed syscall arm has a measured exerciser scenario

The heap gate's coverage check (`scripts/qemu_exerciser_lib.sh`, run by `lake env lean --run`).  The set of
arms is derived from the kernel's own router, never from a list: every syscall
number the ABI decodes (`SyscallId.all`, complete by `SyscallId.all_complete`)
and every message-info shape the router distinguishes (the length and
capability-count bits, every value of each) is routed by
`registerRoutedSyscall` on the default layout, as the routed entry
(`syscallEntryRoutedK`) routes a trapped thread's registers, and each result
is named by its constructor and the syscall its arm is handed.  The
declassifying syscalls, whose refusals the seam records
(`refusalSeamClass = .records`), each need a measured refusal too.

The evidence is the exerciser's: one line per measured round trip with the
syscall number and the message-info word it loaded (`x7`, `x1`), and the label
word it was answered with or `blocked`.  Each is routed by the same router.
The tool exits 1 when an arm has no measured round trip, when a round trip
routes to an arm the enumeration did not find (the enumeration would then be
incomplete: fail closed), or when a line cannot be read.

Input on standard input, one round trip per line: `<name> <x7> <x1> <label|blocked>`,
numbers in decimal or `0x` hexadecimal.
-/

namespace SeLe4n.Testing.ExerciserRouteCoverage

open SeLe4n SeLe4n.Model SeLe4n.Kernel
open SeLe4n.Kernel.Architecture.RegisterDecode

/-- The arm a route takes: its constructor, and the syscall the routed entry
hands that arm when the constructor carries one. -/
def routeArm : RegisterRoutedSyscall → String × Option SyscallId
  | .signal .. => ("signal", none)
  | .wait .. => ("wait", none)
  | .yield => ("yield", none)
  | .send .. => ("send", none)
  | .call .. => ("call", none)
  | .reply .. => ("reply", none)
  | .receive .. => ("receive", none)
  | .replyRecv .. => ("replyRecv", none)
  | .invoke sid _ => ("invoke", some sid)
  | .overflowOne sid _ => ("overflowOne", some sid)
  | .sendLong .. => ("sendLong", none)
  | .callLong .. => ("callLong", none)
  | .replyLong .. => ("replyLong", none)
  | .replyRecvLong .. => ("replyRecvLong", none)
  | .transferring sid _ _ => ("transferring", some sid)
  | .audited sid _ => ("audited", some sid)
  | .overflowed sid _ _ => ("overflowed", some sid)
  | .shortArgs sid _ => ("shortArgs", some sid)
  | .refused _ => ("refused", none)
  | .viaDecode => ("viaDecode", none)

/-- An arm's printed name. -/
def armName : String × Option SyscallId → String
  | (k, none) => k
  | (k, some sid) => s!"{k}/{toString sid}"

/-- The register file a round trip traps with: `x7` the syscall number, `x1`
the message-info word, every other register zero (the router reads no other
register to choose an arm). -/
def trapFile (x7 x1 : UInt64) : RegisterFile :=
  RegisterFile.ofWords fun i => if i = 7 then x7 else if i = 1 then x1 else 0

/-- The arm the routed entry takes for a round trip's `x7` and `x1`. -/
def armOf (x7 x1 : UInt64) : String × Option SyscallId :=
  routeArm (registerRoutedSyscall arm64DefaultLayout (trapFile x7 x1) 32)

/-- The message-info words the enumeration routes: every length and
capability-count field value (the low nine bits), the capabilities-unwrapped
bits set, and a label past the decode's bound. -/
def infoWords : List UInt64 :=
  (List.range 512).map UInt64.ofNat ++ [0xE00, 0xFFFFFFFFFFFFF000, 0xFFFFFFFFFFFFFFFF]

/-- **The arms**: every syscall number the ABI decodes, and one past the last,
routed with every message-info word of the enumeration. -/
def requiredArms : List (String × Option SyscallId) :=
  let numbers := (SyscallId.all.map fun s => s.toNat.toUInt64) ++ [SyscallId.encodingBound.toUInt64]
  (numbers.flatMap fun n => infoWords.map (armOf n)).eraseDups

/-- The syscalls whose refusals the seam records. -/
def recordingSyscalls : List SyscallId :=
  SyscallId.all.filter fun s => refusalSeamClass s == .records

/-- One round trip of the evidence. -/
structure Trip where
  name : String
  x7 : UInt64
  x1 : UInt64
  /-- The answer's label word, or `none` for a round trip that blocked. -/
  label : Option UInt64

/-- A number in decimal or `0x` hexadecimal. -/
def parseWord (s : String) : Option UInt64 :=
  if s.startsWith "0x" then
    (s.drop 2).foldl (fun acc c => acc.bind fun a =>
      if c.isDigit then some (a * 16 + (c.toNat - '0'.toNat))
      else if 'a' ≤ c ∧ c ≤ 'f' then some (a * 16 + (c.toNat - 'a'.toNat + 10))
      else none) (some 0) |>.bind fun n => if n < 2 ^ 64 ∧ s.length > 2 then some n.toUInt64 else none
  else s.toNat?.bind fun n => if n < 2 ^ 64 then some n.toUInt64 else none

def parseTrip (line : String) : Option Trip :=
  match line.splitOn " " |>.filter (· ≠ "") with
  | [name, x7, x1, label] => do
    let x7 ← parseWord x7
    let x1 ← parseWord x1
    let label ← if label == "blocked" then some none else (parseWord label).map some
    pure { name, x7, x1, label }
  | _ => none

/-- Is a label word an error frame's? (`errorLabelWord`: the error label in
the word's high bits, at or past `errorLabelBase`.) -/
def isErrorLabel (w : UInt64) : Bool := (w >>> 12).toNat ≥ SeLe4n.Kernel.Architecture.errorLabelBase

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut trips : Array Trip := #[]
  let mut failures : Array String := #[]
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAsciiEnd.toString
    if line.isEmpty then continue
    match parseTrip line with
    | some t => trips := trips.push t
    | none => failures := failures.push s!"unreadable evidence line: {line}"
  if trips.isEmpty then
    failures := failures.push "no measured round trip in the evidence"
  let required := requiredArms
  for t in trips do
    let arm := armOf t.x7 t.x1
    if !required.contains arm then
      failures := failures.push
        s!"{t.name}: routes to {armName arm}, an arm the enumeration did not find"
  for arm in required do
    if !trips.any (fun t => armOf t.x7 t.x1 == arm) then
      failures := failures.push s!"the arm {armName arm} has no measured round trip"
  for sid in recordingSyscalls do
    if !trips.any (fun t => t.x7 == sid.toNat.toUInt64 &&
        (t.label.map isErrorLabel).getD false) then
      failures := failures.push
        s!"{toString sid}: its refusal is recorded by the seam, and no measured round trip is refused"
  IO.println s!"exerciser route coverage: {required.length} arms, {trips.size} measured round trips"
  for f in failures do IO.eprintln s!"FAIL: {f}"
  return if failures.isEmpty then 0 else 1

end SeLe4n.Testing.ExerciserRouteCoverage

def main : IO UInt32 := SeLe4n.Testing.ExerciserRouteCoverage.main
