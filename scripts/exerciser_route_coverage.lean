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
import SeLe4n.Kernel.Architecture.SyscallSelect
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
operation it issued, the syscall word and the message-info word it loaded
(`x7`, `x1`), and the label word it was answered with or `blocked`.  The
operation is the one the kernel selects from the syscall, the invoked
capability's type and the label (`selectedOperationCode`); the words must be
the ones a user issues it with (`SyscallId.syscall`, `SyscallId.label?`), and
the router routes the operation at those words.
The tool exits 1 when an arm has no measured round trip, when a round trip
routes to an arm the enumeration did not find (the enumeration would then be
incomplete: fail closed), when a round trip's words are not its operation's,
or when a line cannot be read.

Input on standard input, one round trip per line: `<name> <op> <x7> <x1> <label|blocked>`,
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

/-- The register file a round trip traps with: `x7` the syscall word, `x1`
the message-info word, every other register zero (the router reads no other
register to choose an arm). -/
def trapFile (x7 x1 : UInt64) : RegisterFile :=
  RegisterFile.ofWords fun i => if i = 7 then x7 else if i = 1 then x1 else 0

/-- The arm the routed entry takes for a round trip's operation, `x7` and `x1`. -/
def armOf (op : Nat) (x7 x1 : UInt64) : String × Option SyscallId :=
  routeArm (registerRoutedSyscall op arm64DefaultLayout (trapFile x7 x1) 32)

/-- Are `x7` and `x1` the words a user issues operation `op` with: its
syscall's word, and its label when a label selects it?  The code past the last
operation (`SyscallId.encodingBound`, no operation selected) is issued as a
`Call`. -/
def wordsMatch (op : Nat) (x7 x1 : UInt64) : Bool :=
  match SyscallId.ofNat? op with
  | some sid =>
      x7 == sid.syscall.word &&
        (match sid.label? with
         | some l => msgInfoWordLabel x1 == l
         | none => true)
  | none => op == SyscallId.encodingBound && x7 == Syscall.call.word

/-- The message-info words the enumeration routes: every length and
capability-count field value (the low nine bits), the capabilities-unwrapped
bits set, and a label past the decode's bound. -/
def infoWords : List UInt64 :=
  (List.range 512).map UInt64.ofNat ++ [0xE00, 0xFFFFFFFFFFFFF000, 0xFFFFFFFFFFFFFFFF]

/-- **The arms**: every operation the kernel selects, and the code past the
last (no operation), routed at the words a user issues it with and every
message-info word of the enumeration. -/
def requiredArms : List (String × Option SyscallId) :=
  let ops := (SyscallId.all.map fun s => (s.toNat, s.syscall.word, s.msgInfoWithLabel)) ++
    [(SyscallId.encodingBound, Syscall.call.word, id)]
  (ops.flatMap fun (op, x7, info) => infoWords.map fun w => armOf op x7 (info w)).eraseDups

/-- The syscalls whose refusals the seam records. -/
def recordingSyscalls : List SyscallId :=
  SyscallId.all.filter fun s => refusalSeamClass s == .records

/-- One round trip of the evidence. -/
structure Trip where
  name : String
  op : Nat
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
  | [name, op, x7, x1, label] => do
    let op ← op.toNat?
    let x7 ← parseWord x7
    let x1 ← parseWord x1
    let label ← if label == "blocked" then some none else (parseWord label).map some
    pure { name, op, x7, x1, label }
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
    if !wordsMatch t.op t.x7 t.x1 then
      failures := failures.push
        s!"{t.name}: x7 {t.x7} and x1 {t.x1} are not the words operation {t.op} is issued with"
    let arm := armOf t.op t.x7 t.x1
    if !required.contains arm then
      failures := failures.push
        s!"{t.name}: routes to {armName arm}, an arm the enumeration did not find"
  for arm in required do
    if !trips.any (fun t => armOf t.op t.x7 t.x1 == arm) then
      failures := failures.push s!"the arm {armName arm} has no measured round trip"
  for sid in recordingSyscalls do
    if !trips.any (fun t => t.op == sid.toNat &&
        (t.label.map isErrorLabel).getD false) then
      failures := failures.push
        s!"{toString sid}: its refusal is recorded by the seam, and no measured round trip is refused"
  IO.println s!"exerciser route coverage: {required.length} arms, {trips.size} measured round trips"
  for f in failures do IO.eprintln s!"FAIL: {f}"
  return if failures.isEmpty then 0 else 1

end SeLe4n.Testing.ExerciserRouteCoverage

def main : IO UInt32 := SeLe4n.Testing.ExerciserRouteCoverage.main
