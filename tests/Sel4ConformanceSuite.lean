-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Testing.Sel4ConformanceTable
import SeLe4n.Testing.Helpers

/-!
# The seL4 conformance suite

Runs every row of `SeLe4n.Testing.Sel4Conformance`'s table against the kernel:
each label row against the label round trip, the selection, the decode's word
count and the return shape (`labelRowAgrees`); each syscall row against the
`Syscall` predicates and against the register reads of `decodeSyscallArgs`
over a frame whose registers all differ; each seL4 error against the error
frame seLe4n writes for it; and seL4's `messageInfoFromWord` clamp and the two
word-first decodes (the reply-capability mint's slots, the service register's
interface id) at a word `≥ 2 ^ 63`.
-/

namespace SeLe4n.Testing.Sel4ConformanceSuite

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Architecture.RegisterDecode
open SeLe4n.Kernel.Architecture.SyscallArgDecode
open SeLe4n.Testing.Sel4Conformance

private def tag : String := "sel4-conformance"

private def expect (label : String) (cond : Bool) : IO Unit :=
  expectCond tag label cond

/-- Every label row agrees with the kernel. -/
def runLabelRows : IO Unit := do
  for r in sel4LabelRows do
    expect s!"label {r.label} {r.name}" (labelRowAgrees r)
  let absent := sel4LabelRows.filter (fun r => r.status.op?.isNone)
  IO.println s!"{tag}: {sel4LabelRows.length} label rows, {absent.length} with no seLe4n operation"
  for r in absent do
    match r.status with
    | .absent owner => IO.println s!"{tag}:   absent label {r.label} {r.name} (owner {owner})"
    | _ => pure ()

/-- A frame whose registers x0–x8 hold distinct words, x7 the syscall's. -/
def frameFor (sys : Syscall) : RegisterFile :=
  (List.range 9).foldl (fun rf i =>
      writeReg rf ⟨i⟩ (if i == 7 then sys.word else i.toUInt64 + ((5 : UInt64) <<< 12)))
    (default : RegisterFile)

/-- Every syscall row agrees with the `Syscall` predicates, and the register
decode reads the registers the row names from where seL4 reads them. -/
def runSyscallRows : IO Unit := do
  for r in sel4SyscallRows do
    expect s!"syscall {r.name} predicates" (syscallRowAgrees r)
    let rf := frameFor r.sys
    match decodeSyscallArgs SyscallId.send.toNat arm64DefaultLayout rf with
    | .error _ => expect s!"syscall {r.name} decodes" false
    | .ok (d : SyscallDecodeResult) =>
      expect s!"syscall {r.name} x0 is the capability" (d.capAddr == CPtr.ofWord (readRegWord rf ⟨0⟩))
      expect s!"syscall {r.name} x1 is the message info"
        (d.msgInfo.label == 5 && d.msgInfo.length == 1)
      expect s!"syscall {r.name} x2-x5 are the message registers"
        (d.msgRegs.map (·.word) == #[readRegWord rf ⟨2⟩, readRegWord rf ⟨3⟩, readRegWord rf ⟨4⟩,
          readRegWord rf ⟨5⟩])
      expect s!"syscall {r.name} x6 is the reply register"
        (d.replyCPtr == CPtr.ofWord (readRegWord rf ⟨6⟩) && (r.regsRead.contains 6 || !r.canReply))
      expect s!"syscall {r.name} canReply from x7" (d.canReply == r.canReply)

/-- Each seL4 error has a seLe4n error whose payload is seL4's, and the error
frame carries it: `x0 = 0`, the code in `x1`'s label, the payload in x2–x5. -/
def runErrors : IO Unit := do
  let all : List Sel4Error := [.invalidArgument, .invalidCapability, .illegalOperation,
    .rangeError, .alignmentError, .failedLookup, .truncatedMessage, .deleteFirst,
    .revokeFirst, .notEnoughMemory]
  expect "seL4 codes 1-10" (all.map (·.code) == (List.range 10).map (· + 1))
  for e in all do
    let k := e.kernelError
    expect s!"error {e.code} payload words" (k.payloadLength == e.payloadWords)
    expect s!"error {e.code} label round trip" (ofErrorLabel? (errorLabel k) == some k.erasePayload)
    let f := errorFrame k false
    expect s!"error {e.code} frame" (f.x0 == 0 && f.x2 == k.payloadWord 0 && f.x3 == k.payloadWord 1)

/-- A decoded message of the given words. -/
private def decodedOf (regs : Array RegValue) : SyscallDecodeResult :=
  { capAddr := CPtr.ofNat 0, msgInfo := { length := regs.size, extraCaps := 0, label := 0 },
    syscallId := .send, msgRegs := regs }

/-- The full-width word the word-first decodes are tested at. -/
private def wideWord : UInt64 := ((1 : UInt64) <<< 63) + 5

/-- seL4's `messageInfoFromWord` (`include/api/types.h:83`) clamps a length
past 120 to 120 and refuses nothing; the word decode is the same. -/
def runMessageInfo : IO Unit := do
  for len in ([0, 1, 4, 5, 119, 120, 121, 127] : List Nat) do
    let w : UInt64 := ((7 : UInt64) <<< 12) ||| ((2 : UInt64) <<< 7) ||| len.toUInt64
    let ok : Bool := match decodeMsgInfoWord w with
      | .ok mi => mi.length == min len 120 && mi.label == 7 && mi.extraCaps == 2
      | .error _ => false
    expect s!"messageInfoFromWord length {len}" ok
  let allOnes : Bool := match decodeMsgInfoWord (0xFFFFFFFFFFFFFFFF : UInt64) with
    | .ok mi => mi.length == 120 && mi.extraCaps == 3 && mi.label == MessageInfo.maxLabel
    | .error _ => false
  expect "messageInfoFromWord all ones" allOnes

/-- The two word-first decodes at a word `≥ 2 ^ 63`: the reply-capability
mint's slots read as `windowWordBound`, a slot no CNode addresses, and the
service register's interface id is refused `invalidArgument 0`. -/
def runWordFirst : IO Unit := do
  expect "mintReplyCap wide source slot"
    (match decodeMintReplyCapArgs (decodedOf #[⟨wideWord⟩, ⟨3⟩]) with
      | .ok a => a.srcSlot.toNat == windowWordBound && a.dstSlot.toNat == 3
      | .error _ => false)
  expect "mintReplyCap wide destination slot"
    (match decodeMintReplyCapArgs (decodedOf #[⟨2⟩, ⟨wideWord⟩]) with
      | .ok a => a.srcSlot.toNat == 2 && a.dstSlot.toNat == windowWordBound
      | .error _ => false)
  expect "serviceRegister wide interface id"
    (match decodeServiceRegisterArgs (decodedOf #[⟨wideWord⟩, ⟨1⟩, ⟨8⟩, ⟨8⟩, ⟨0⟩]) with
      | .error (.invalidArgument 0) => true
      | _ => false)
  expect "serviceRegister interface id below the bound"
    (match decodeServiceRegisterArgs (decodedOf #[⟨9⟩, ⟨1⟩, ⟨8⟩, ⟨8⟩, ⟨0⟩]) with
      | .ok a => a.interfaceId.toNat == 9
      | _ => false)

end SeLe4n.Testing.Sel4ConformanceSuite

def main : IO Unit := do
  IO.println "=== Sel4ConformanceSuite (WS-SX SX8.1) ==="
  SeLe4n.Testing.Sel4ConformanceSuite.runLabelRows
  SeLe4n.Testing.Sel4ConformanceSuite.runSyscallRows
  SeLe4n.Testing.Sel4ConformanceSuite.runErrors
  SeLe4n.Testing.Sel4ConformanceSuite.runMessageInfo
  SeLe4n.Testing.Sel4ConformanceSuite.runWordFirst
  IO.println "=== Sel4ConformanceSuite PASSED ==="
