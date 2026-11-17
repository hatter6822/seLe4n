-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.SyscallArgDecode
import SeLe4n.Kernel.Architecture.IpcBufferRead
import SeLe4n.Testing.Helpers
import SeLe4n.Testing.StateBuilder

/-! # T-03/AC6-A: Dedicated Decoding Suite

Standalone test coverage for `RegisterDecode.lean` (Layer 1) and
`SyscallArgDecode.lean` (Layer 2). Previously, decode tests were
dispersed across NegativeStateSuite and OperationChainSuite.

**Layer 1** (RegisterDecode): `decodeSyscallCode`, `decodeMsgInfo`,
`decodeCapPtr`, `validateRegBound`, `decodeSyscallArgs`.

**Layer 2** (SyscallArgDecode): 20 per-syscall decode functions
organized by subsystem (CSpace, VSpace, Lifecycle, Service,
Notification, SchedContext, TCB). -/

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture.RegisterDecode
open SeLe4n.Kernel.Architecture.SyscallArgDecode
open SeLe4n.Kernel.Architecture.IpcBufferRead
open SeLe4n.Testing

namespace SeLe4n.Testing.DecodingSuite

private def tag : String := "decode"

private def expect (label : String) (cond : Bool) : IO Unit :=
  expectCond tag label cond

/-- Helper: check if an Except result equals .ok v using DecidableEq. -/
private def isOkEq [DecidableEq α] (r : Except ε α) (expected : α) : Bool :=
  match r with
  | .ok v => v == expected
  | .error _ => false

/-- Helper: check if an Except result is a specific error. -/
private def isErrEq [DecidableEq ε] (r : Except ε α) (expected : ε) : Bool :=
  match r with
  | .ok _ => false
  | .error e => e == expected

-- ============================================================================
-- Layer 1: RegisterDecode tests
-- ============================================================================

/-- RD-001: decodeSyscallCode — valid syscall IDs. -/
private def rd001_decodeSyscallCodeValid : IO Unit := do
  -- First valid: .send (0)
  let r0 := decodeSyscallCode 0
  expect "send=0" (isOkEq r0 .send)
  -- Middle: .serviceRegister (11)
  let r11 := decodeSyscallCode 11
  expect "serviceRegister=11" (isOkEq r11 .serviceRegister)
  -- Last valid: .tcbSetIPCBuffer (24)
  let r24 := decodeSyscallCode 24
  expect "tcbSetIPCBuffer=24" (isOkEq r24 .tcbSetIPCBuffer)
  -- WS-SM SM5.H.4: tcbSetAffinity=25
  let r25 := decodeSyscallCode 25
  expect "tcbSetAffinity=25" (isOkEq r25 .tcbSetAffinity)
  -- WS-SX SX6.5: 34 (the retired tcbSetFaultHandler) decodes to nothing —
  -- seL4-MCS's `TCB_SetSpace` installs the fault endpoint
  let r34 := decodeSyscallCode 34
  expect "retired=34" (isErrEq r34 .invalidSyscallNumber)
  -- WS-RR RR8.16: cspaceRevoke=35 (`seL4_CNode_Revoke`)
  let r35 := decodeSyscallCode 35
  expect "cspaceRevoke=35" (isOkEq r35 .cspaceRevoke)
  -- WS-BP BP7.1: untypedRetype=36 (`seL4_Untyped_Retype`, frames)
  let r36 := decodeSyscallCode 36
  expect "untypedRetype=36" (isOkEq r36 .untypedRetype)
  -- WS-SX SX7.1: 37, the untyped reset, is retired (seL4 resets inside Retype)
  let r37 := decodeSyscallCode 37
  expect "retired=37" (isErrEq r37 .invalidSyscallNumber)
  -- WS-BP BP7.1: tcbSetSpace=38 (seL4's `TCB_SetSpace`)
  let r38 := decodeSyscallCode 38
  expect "tcbSetSpace=38" (isOkEq r38 .tcbSetSpace)
  -- WS-SM SM7.D: vspaceUnifyInstruction=29 (the code-publication path)
  let r29 := decodeSyscallCode 29
  expect "vspaceUnifyInstruction=29" (isOkEq r29 .vspaceUnifyInstruction)
  -- WS-SM SM8.C: declassify=30 (the live declassification entry point)
  let r30 := decodeSyscallCode 30
  expect "declassify=30" (isOkEq r30 .declassify)
  -- WS-SM SM9.A: auditRead=31 / auditDrain=32 (the audit trail's reader and
  -- drain — the read side of the trail SM8.C mounted write-only)
  let r31 := decodeSyscallCode 31
  expect "auditRead=31" (isOkEq r31 .auditRead)
  let r32 := decodeSyscallCode 32
  expect "auditDrain=32" (isOkEq r32 .auditDrain)
  let r33 := decodeSyscallCode 33
  expect "declassifySignal=33" (isOkEq r33 .declassifySignal)

/-- RD-002: decodeSyscallCode — invalid values. -/
private def rd002_decodeSyscallCodeInvalid : IO Unit := do
  -- First invalid: 48 (WS-ZA ZA6.32 added irqHandlerAck at 44 and
  -- irqControlGet, irqHandlerSetNotification and irqHandlerClear at 45 to 47, ZA6.29
  -- schedContextYieldTo at 43, ZA6.9
  -- schedContextConsumed at 42, ZA4.3 yield at 41, WS-BP BP7.1 added
  -- pageTableMap at 39 and pageTableUnmap at 40, tcbSetSpace at 38 (37, the untyped reset, retired at WS-SX SX7.1)
  -- and untypedRetype at 36, on top of
  -- WS-RR RR8.16's cspaceRevoke at 35, the
  -- PR #887 review round's tcbSetFaultHandler at 34 (retired by WS-SX SX6.5), WS-SM SM9.C's
  -- declassifySignal at 33, SM9.A's auditRead at 31 and auditDrain at 32,
  -- SM8.C's declassify at 30, SM7.D's vspaceUnifyInstruction at 29 and
  -- PR #822 Phase H's mintReplyCap at 28)
  let r48 := decodeSyscallCode 48
  expect "invalid=48" (isErrEq r48 .invalidSyscallNumber)
  -- Large value
  let rLarge := decodeSyscallCode 999999
  expect "invalid=999999" (isErrEq rLarge .invalidSyscallNumber)

/-- RD-003: decodeSyscallCode — boundary edge 47/48 (WS-ZA ZA6.32:
irqHandlerClear=47 is the last valid). -/
private def rd003_decodeSyscallCodeBoundary : IO Unit := do
  let r38 := decodeSyscallCode 38
  let r39 := decodeSyscallCode 39
  let r40 := decodeSyscallCode 40
  let r41 := decodeSyscallCode 41
  let r42 := decodeSyscallCode 42
  let r43 := decodeSyscallCode 43
  let r44 := decodeSyscallCode 44
  let r45 := decodeSyscallCode 45
  let r46 := decodeSyscallCode 46
  let r47 := decodeSyscallCode 47
  let r48 := decodeSyscallCode 48
  expect "tcbSetSpace=38" (isOkEq r38 .tcbSetSpace)
  expect "pageTableMap=39" (isOkEq r39 .pageTableMap)
  expect "pageTableUnmap=40" (isOkEq r40 .pageTableUnmap)
  expect "boundary=41 ok (yield)" (isOkEq r41 .yield)
  expect "boundary=42 ok (schedContextConsumed)" (isOkEq r42 .schedContextConsumed)
  expect "boundary=43 ok (schedContextYieldTo)" (isOkEq r43 .schedContextYieldTo)
  expect "boundary=44 ok (irqHandlerAck)" (isOkEq r44 .irqHandlerAck)
  expect "irqControlGet=45" (isOkEq r45 .irqControlGet)
  expect "irqHandlerSetNotification=46" (isOkEq r46 .irqHandlerSetNotification)
  expect "boundary=47 ok (irqHandlerClear)" (isOkEq r47 .irqHandlerClear)
  expect "boundary=48 err" (!r48.isOk)

/-- RD-004: decodeMsgInfo — valid round-trip. -/
private def rd004_decodeMsgInfoValid : IO Unit := do
  let mi : MessageInfo := { length := 4, extraCaps := 2, label := 100 }
  let encoded := encodeMsgInfo mi
  let decoded := decodeMsgInfo encoded
  expect "round-trip" (isOkEq decoded mi)

/-- RD-005: decodeMsgInfo — boundary and overflow values. -/
private def rd005_decodeMsgInfoOverflow : IO Unit := do
  -- Boundary: length=120 (maxMessageRegisters) should succeed
  let miBoundary : MessageInfo := { length := 120, extraCaps := 0, label := 0 }
  let encodedBoundary := encodeMsgInfo miBoundary
  let decodedBoundary := decodeMsgInfo encodedBoundary
  expect "boundary length=120 ok" (isOkEq decodedBoundary miBoundary)
  -- Overflow: length=121 should fail
  -- length field is bits 0..6 (7 bits), extraCaps bits 7..8 (2 bits), label bits 9+
  let rawWithLength121 := 121  -- bits 0-6 = 121
  let result := decodeMsgInfo ⟨rawWithLength121⟩
  expect "overflow length" (!result.isOk)

/-- RD-006: decodeCapPtr — valid and boundary values. -/
private def rd006_decodeCapPtrValid : IO Unit := do
  -- Small value
  let r := decodeCapPtr ⟨42⟩
  expect "small value" (isOkEq r (CPtr.ofNat 42))
  -- Zero
  let r0 := decodeCapPtr ⟨0⟩
  expect "zero" (isOkEq r0 (CPtr.ofNat 0))

/-- RD-007: decodeCapPtr — a register holds a 64-bit word (`RegValue.word`,
WS-SX SX1.3), so a number past `2^64` reduces as the hardware register would
and the decode reads the reduced word; the top word decodes as itself. -/
private def rd007_decodeCapPtrOutOfRange : IO Unit := do
  let rHuge := decodeCapPtr (SeLe4n.RegValue.ofNat (2^64))
  expect "word64 wraps" (isOkEq rHuge (CPtr.ofNat 0))
  let rTop := decodeCapPtr ⟨0xFFFFFFFFFFFFFFFF⟩
  expect "top word" (isOkEq rTop (CPtr.ofNat (2^64 - 1)))

/-- RD-008: validateRegBound — valid and boundary values. -/
private def rd008_validateRegBound : IO Unit := do
  -- Valid: index 0 within bound 32
  let r0 := validateRegBound ⟨0⟩ 32
  expect "idx=0 bound=32 ok" r0.isOk
  -- Valid: last valid index (31)
  let r31 := validateRegBound ⟨31⟩ 32
  expect "idx=31 bound=32 ok" r31.isOk
  -- Invalid: index 32 (at bound)
  let r32 := validateRegBound ⟨32⟩ 32
  expect "idx=32 bound=32 err" (isErrEq r32 .invalidRegister)

/-- RD-009: decodeSyscallArgs — full integration with arm64DefaultLayout.
    Populates a RegisterFile with valid values in the ARM64 convention
    (x0=capPtr, x1=msgInfo, x2-x5=msgRegs, x7=syscallId) and verifies
    the complete decode pipeline produces the expected SyscallDecodeResult. -/
private def rd009_decodeSyscallArgsIntegration : IO Unit := do
  -- Build a RegisterFile with known values in the ARM64 positions
  let capPtrVal : Nat := 42
  let msgInfoVal : MessageInfo := { length := 2, extraCaps := 1, label := 7 }
  let syscallVal : SyscallId := .send  -- toNat = 0
  -- Construct register file: default (all zeros), then write specific registers
  let rf := (default : RegisterFile)
    |> (writeReg · ⟨0⟩ (encodeCapPtr (CPtr.ofNat capPtrVal)).val.toUInt64)   -- x0 = capPtr
    |> (writeReg · ⟨1⟩ (encodeMsgInfo msgInfoVal).val.toUInt64)               -- x1 = msgInfo
    |> (writeReg · ⟨2⟩ 100)                                    -- x2 = msgReg0
    |> (writeReg · ⟨3⟩ 200)                                    -- x3 = msgReg1
    |> (writeReg · ⟨4⟩ 300)                                    -- x4 = msgReg2
    |> (writeReg · ⟨5⟩ 400)                                    -- x5 = msgReg3
    |> (writeReg · ⟨7⟩ Syscall.send.word)                      -- x7 = seL4's Send
  let result := decodeSyscallArgs syscallVal.toNat arm64DefaultLayout rf 32
  expect "integration ok" result.isOk
  match result with
  | .ok dr =>
    expect "capAddr" (dr.capAddr.toNat == capPtrVal)
    expect "msgInfo length" (dr.msgInfo.length == 2)
    expect "msgInfo extraCaps" (dr.msgInfo.extraCaps == 1)
    expect "syscallId" (dr.syscallId == syscallVal)
    expect "msgRegs length" (dr.msgRegs.size == 4)
    expect "msgReg0" (dr.msgRegs[0]! == ⟨100⟩)
    expect "msgReg1" (dr.msgRegs[1]! == ⟨200⟩)
  | .error _ => expect "unexpected error" false

/-- RD-010: decodeSyscallArgs — insufficient regCount rejects. -/
private def rd010_decodeSyscallArgsInsufficientRegs : IO Unit := do
  let rf := (default : RegisterFile)
  -- regCount=5 means registers 0..4 are valid, but arm64DefaultLayout needs x7
  let result := decodeSyscallArgs SyscallId.send.toNat arm64DefaultLayout rf 5
  expect "insufficient regs" (!result.isOk)

/-- RD-011: extractMessageRegisters — boundary and truncation behavior. -/
private def rd011_extractMessageRegisters : IO Unit := do
  let regs : Array RegValue := #[⟨10⟩, ⟨20⟩, ⟨30⟩, ⟨40⟩]
  -- length=2: should extract only first 2 registers
  let mi2 : MessageInfo := { length := 2, extraCaps := 0, label := 0 }
  let r2 := extractMessageRegisters regs mi2
  expect "length=2 size" (r2.size == 2)
  expect "length=2 val0" (r2[0]! == ⟨10⟩)
  -- length=120 (maxMessageRegisters): bounded by array size (4)
  let mi120 : MessageInfo := { length := 120, extraCaps := 0, label := 0 }
  let r120 := extractMessageRegisters regs mi120
  expect "length=120 capped at array size" (r120.size == 4)
  -- length=0: should extract nothing
  let mi0 : MessageInfo := { length := 0, extraCaps := 0, label := 0 }
  let r0 := extractMessageRegisters regs mi0
  expect "length=0 empty" (r0.size == 0)

private def runRegisterDecodeTests : IO Unit := do
  IO.println "--- Layer 1: RegisterDecode ---"
  rd001_decodeSyscallCodeValid
  rd002_decodeSyscallCodeInvalid
  rd003_decodeSyscallCodeBoundary
  rd004_decodeMsgInfoValid
  rd005_decodeMsgInfoOverflow
  rd006_decodeCapPtrValid
  rd007_decodeCapPtrOutOfRange
  rd008_validateRegBound
  rd009_decodeSyscallArgsIntegration
  rd010_decodeSyscallArgsInsufficientRegs
  rd011_extractMessageRegisters

-- ============================================================================
-- Layer 2: SyscallArgDecode tests
-- ============================================================================

/-- Helper: create a SyscallDecodeResult stub with given message registers. -/
private def mkStub (regs : Array RegValue) : SyscallDecodeResult :=
  { capAddr := CPtr.ofNat 0
    msgInfo := { length := regs.size, extraCaps := 0, label := 0 }
    syscallId := .send
    msgRegs := regs }

-- CSpace family ---------------------------------------------------------------

/-- SAD-001: decodeCSpaceMintArgs — valid decode with 6 registers in seL4's
order: the destination index and depth, the source index and depth, the
rights word and the badge. -/
private def sad001_cspaceMint : IO Unit := do
  let stub := mkStub #[⟨10⟩, ⟨64⟩, ⟨20⟩, ⟨64⟩, ⟨7⟩, ⟨42⟩]
  let result := decodeCSpaceMintArgs stub
  expect "SAD-001a mint ok" result.isOk
  match result with
  | .ok args =>
    expect "SAD-001b srcIndex" (args.srcIndex.toNat == 20)
    expect "SAD-001c destIndex" (args.destIndex.toNat == 10)
    expect "SAD-001d badge" (args.badge.toNat == 42)
    expect "SAD-001e rights" (args.rights.bits == 7)
  | .error _ => expect "SAD-001 unexpected error" false

/-- SAD-002: decodeCSpaceMintArgs — insufficient registers (5). -/
private def sad002_cspaceMintInsufficient : IO Unit := do
  let stub := mkStub #[⟨10⟩, ⟨64⟩, ⟨20⟩, ⟨64⟩, ⟨7⟩]
  let result := decodeCSpaceMintArgs stub
  expect "SAD-002a mint insufficient" (!result.isOk)

/-- SAD-003: decodeCSpaceCopyArgs — valid decode with 5 registers in seL4's
order; a short message is refused, a rights word's bits past the rights are
ignored (seL4's `rightsFromWord`), and a depth past 64 reads as one
`lookupSlotForCNodeOp` refuses. -/
private def sad003_cspaceCopy : IO Unit := do
  let stub := mkStub #[⟨15⟩, ⟨64⟩, ⟨5⟩, ⟨3⟩, ⟨5⟩]
  let result := decodeCSpaceCopyArgs stub
  expect "SAD-003a copy ok" result.isOk
  match result with
  | .ok args =>
    expect "SAD-003b srcIndex" (args.srcIndex.toNat == 5)
    expect "SAD-003c destIndex" (args.destIndex.toNat == 15)
    expect "SAD-003e depths" (args.destDepth == 64 && args.srcDepth == 3)
    expect "SAD-003e2 rights mask" (args.rights.bits == 5)
  | .error _ => expect "SAD-003 unexpected error" false
  expect "SAD-003f copy short"
    (match decodeCSpaceCopyArgs (mkStub #[⟨15⟩, ⟨64⟩, ⟨5⟩, ⟨3⟩]) with
      | .error .truncatedMessage => true | _ => false)
  expect "SAD-003g copy bits past the rights ignored"
    (match decodeCSpaceCopyArgs (mkStub #[⟨15⟩, ⟨64⟩, ⟨5⟩, ⟨3⟩, ⟨0xFFFF_FFE5⟩]) with
      | .ok args => args.rights.bits == 5 | _ => false)
  expect "SAD-003h a wide depth reads out of range"
    (match decodeCSpaceCopyArgs (mkStub #[⟨15⟩, ⟨0xFFFF_FFFF_FFFF_FFFF⟩, ⟨5⟩, ⟨3⟩, ⟨5⟩]) with
      | .ok args => args.destDepth == 65 | _ => false)

/-- SAD-004: decodeCSpaceMoveArgs — valid decode of four words. -/
private def sad004_cspaceMove : IO Unit := do
  let stub := mkStub #[⟨3⟩, ⟨2⟩, ⟨8⟩, ⟨2⟩]
  let result := decodeCSpaceMoveArgs stub
  expect "SAD-004a move ok" result.isOk
  expect "SAD-004b move short"
    (match decodeCSpaceMoveArgs (mkStub #[⟨3⟩, ⟨2⟩, ⟨8⟩]) with
      | .error .truncatedMessage => true | _ => false)

/-- SAD-005: decodeCSpaceDeleteArgs — valid and insufficient. -/
private def sad005_cspaceDelete : IO Unit := do
  let stub1 := mkStub #[⟨7⟩]
  let result1 := decodeCSpaceDeleteArgs stub1
  expect "SAD-005a delete ok" result1.isOk
  let stub0 := mkStub #[]
  let result0 := decodeCSpaceDeleteArgs stub0
  expect "SAD-005b delete empty err" (!result0.isOk)

-- Lifecycle family -------------------------------------------------------------

/-- SAD-006: decodeUntypedRetypeArgs — valid decode of every kernel object
kind's seven seL4-shaped words (type, size, node index, node depth, node
offset, object count, then the model's object id word; WS-SX SX6.3). -/
private def sad006_untypedRetype : IO Unit := do
  for tag in [0, 1, 2, 3, 6, 7] do
    let stub := mkStub #[⟨tag⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, ⟨1⟩, ⟨100⟩]
    match decodeUntypedRetypeArgs stub with
    | .ok args =>
        expect s!"SAD-006a carve decode tag {tag}"
          (args.newType.toNat == tag.toNat && args.sizeBits == 1 && args.childId == ⟨100⟩ &&
            args.nodeOffset == 4 && args.numObjects == 1 && args.nodeDepth == 0)
    | .error _ => expect s!"SAD-006a carve decode tag {tag}" false
  expect "SAD-006b carve decode short err" (!(decodeUntypedRetypeArgs (mkStub #[⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, ⟨1⟩])).isOk)

/-- SAD-007: decodeUntypedRetypeArgs — invalid type tag. -/
private def sad007_untypedRetypeInvalidType : IO Unit := do
  let stub := mkStub #[⟨99⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, ⟨1⟩, ⟨100⟩]
  let result := decodeUntypedRetypeArgs stub
  expect "SAD-007a carve invalid type" (!result.isOk)

-- VSpace family ----------------------------------------------------------------

/-- SAD-008: decodePageMapArgs — seL4's three words, carried verbatim
(WS-SX SX6.3, D6: the frame is the invoked capability and the address space
extra capability 0, so no word names either). -/
private def sad008_vspaceMap : IO Unit := do
  let stub := mkStub #[⟨0x1000⟩, ⟨3⟩, ⟨5⟩]
  let result := decodePageMapArgs stub
  expect "SAD-008a page map ok" result.isOk
  expect "SAD-008b MR0..MR2 are the address, rights and attributes words"
    (match result with
     | .ok args => args.vaddr == 0x1000 && args.rights == 3 && args.attr == 5
     | .error _ => false)

/-- SAD-009: decodePageMapArgs — a message of two words is truncated. -/
private def sad009_vspaceMapInvalidAsid : IO Unit := do
  let stub := mkStub #[⟨0x1000⟩, ⟨3⟩]
  let result := decodePageMapArgs stub
  expect "SAD-009a page map two words truncated" (!result.isOk)

/-- SAD-010: vspaceMapArgsOfWords — non-canonical VAddr (>= 2^48) is seL4's
`InvalidArgument 0`. -/
private def sad010_vspaceMapNonCanonical : IO Unit := do
  let result := vspaceMapArgsOfWords ⟨(2^48 : Nat).toUInt64, 3, 5⟩ ⟨1⟩ (SeLe4n.CPtr.ofNat 2)
  expect "SAD-010a page map non-canonical"
    (match result with
     | .error (.invalidArgument 0) => true
     | _ => false)

/-- SAD-011: pagePermissionsOfWords — the words are total; read/write come from
the rights word and execute/cacheable from the attributes word. -/
private def sad011_vspaceMapInvalidPerms : IO Unit := do
  let p := pagePermissionsOfWords 0xFFFF 0
  expect "SAD-011a wide rights word read as CanRead|CanWrite"
    (p.read && p.write && p.execute && p.user && !p.cacheable)
  let q := pagePermissionsOfWords 2 5
  expect "SAD-011b read-only, cacheable, never executable"
    (q.read && !q.write && !q.execute && q.user && q.cacheable)

/-- SAD-012: decodeVSpaceUnmapArgs — valid and invalid ASID. -/
private def sad012_vspaceUnmap : IO Unit := do
  let stub := mkStub #[⟨1⟩, ⟨0x1000⟩]
  let result := decodeVSpaceUnmapArgs stub 65536
  expect "SAD-012a vspace unmap ok" result.isOk
  let stubBad := mkStub #[⟨65536⟩, ⟨0x1000⟩]
  let resultBad := decodeVSpaceUnmapArgs stubBad 65536
  expect "SAD-012b vspace unmap invalid ASID" (!resultBad.isOk)

-- Notification family ----------------------------------------------------------

/-- SAD-013: a signal decodes no argument — its badge is the capability's
(`Capability.signalBadge`, seL4's `capNtfnBadge`): the minted word for a
badged capability, zero for an unbadged one even when a stale word sits in
`badgeWord`. -/
private def sad013_notificationSignal : IO Unit := do
  let badged : Capability :=
    { target := .object ⟨7⟩, rights := AccessRightSet.ofList [.write],
      badgeWord := SeLe4n.Badge.ofWord 0x1, badged := true }
  let unbadged : Capability :=
    { target := .object ⟨7⟩, rights := AccessRightSet.ofList [.write] }
  let stale : Capability := { unbadged with badgeWord := SeLe4n.Badge.ofWord 0x5 }
  expect "SAD-013a badged cap signals its minted badge" (badged.signalBadge.word == 0x1)
  expect "SAD-013b unbadged cap signals badge 0" (unbadged.signalBadge.word == 0)
  expect "SAD-013c unbadged cap ignores a stale badge word" (stale.signalBadge.word == 0)

/-- SAD-014: decodeNotificationWaitArgs — always succeeds. -/
private def sad014_notificationWait : IO Unit := do
  let stub := mkStub #[]
  let result := decodeNotificationWaitArgs stub
  expect "SAD-014a notification wait ok" result.isOk

/-- SAD-015: decodeReplyRecvArgs — valid and insufficient. -/
private def sad015_replyRecv : IO Unit := do
  let stub := mkStub #[⟨42⟩]
  let result := decodeReplyRecvArgs stub
  expect "SAD-015a replyRecv ok" result.isOk
  let stubEmpty := mkStub #[]
  let resultEmpty := decodeReplyRecvArgs stubEmpty
  expect "SAD-015b replyRecv empty err" (!resultEmpty.isOk)

-- SchedContext family ----------------------------------------------------------

/-- SAD-016: decodeSchedContextConfigureArgs — valid decode with 5 registers
(seL4-MCS's budget, period, extra refills, badge, flags; WS-SX SX6.4). -/
private def sad016_schedContextConfigure : IO Unit := do
  let stub := mkStub #[⟨1000⟩, ⟨5000⟩, ⟨3⟩, ⟨128⟩, ⟨1⟩]
  let result := decodeSchedContextConfigureArgs stub
  expect "SAD-016a scConfigure ok" result.isOk
  match result with
  | .ok args =>
    expect "SAD-016b budget" (args.budget == 1000)
    expect "SAD-016c period" (args.period == 5000)
    expect "SAD-016d extra refills" (args.extraRefills == 3)
    expect "SAD-016e badge" (args.badge == 128)
    expect "SAD-016f flags" (args.flags == 1)
  | .error _ => expect "SAD-016 unexpected error" false

/-- SAD-017: decodeSchedContextConfigureArgs — insufficient registers (4). -/
private def sad017_schedContextConfigureInsufficient : IO Unit := do
  let stub := mkStub #[⟨1000⟩, ⟨5000⟩, ⟨0⟩, ⟨128⟩]
  let result := decodeSchedContextConfigureArgs stub
  expect "SAD-017a scConfigure insufficient" (!result.isOk)

/-- SAD-019: decodeSchedContextUnbindArgs — always succeeds. -/
private def sad019_schedContextUnbind : IO Unit := do
  let stub := mkStub #[]
  let result := decodeSchedContextUnbindArgs stub
  expect "SAD-019a scUnbind ok" result.isOk

-- TCB family -------------------------------------------------------------------

/-- SAD-020: decodeSuspendArgs / decodeResumeArgs — always succeed. -/
private def sad020_suspendResume : IO Unit := do
  let stub := mkStub #[]
  let rSus := decodeSuspendArgs stub
  expect "SAD-020a suspend ok" rSus.isOk
  let rRes := decodeResumeArgs stub
  expect "SAD-020b resume ok" rRes.isOk

/-- SAD-021: decodeSetPriorityArgs — valid and out-of-range. -/
private def sad021_setPriority : IO Unit := do
  let stub := mkStub #[⟨128⟩]
  let result := decodeSetPriorityArgs stub
  expect "SAD-021a setPriority ok" result.isOk
  match result with
  | .ok args => expect "SAD-021b priority value" (args.newPriority == 128)
  | .error _ => expect "SAD-021 unexpected error" false
  -- Boundary: 0xFF is valid
  let stubMax := mkStub #[⟨0xFF⟩]
  let resultMax := decodeSetPriorityArgs stubMax
  expect "SAD-021c setPriority max ok" resultMax.isOk
  -- Out of range: 0x100
  let stubOver := mkStub #[⟨0x100⟩]
  let resultOver := decodeSetPriorityArgs stubOver
  expect "SAD-021d setPriority overflow" (!resultOver.isOk)

/-- SAD-022: decodeSetMCPriorityArgs — valid and out-of-range. -/
private def sad022_setMCPriority : IO Unit := do
  let stub := mkStub #[⟨64⟩]
  let result := decodeSetMCPriorityArgs stub
  expect "SAD-022a setMCPriority ok" result.isOk
  -- Out of range: 0x100
  let stubOver := mkStub #[⟨0x100⟩]
  let resultOver := decodeSetMCPriorityArgs stubOver
  expect "SAD-022b setMCPriority overflow" (!resultOver.isOk)

/-- SAD-023: decodeSetIPCBufferArgs carries the address as given.  seL4's
`decodeSetIPCBuffer` checks the alignment in `checkValidIPCBuffer`, after the
frame capability, so the decode refuses nothing but a short message. -/
private def sad023_setIPCBuffer : IO Unit := do
  let aligned := decodeSetIPCBufferArgs (mkStub #[⟨1024 * 5⟩])
  expect "SAD-023a setIPCBuffer aligned decodes"
    (match aligned with | .ok a => a.bufferAddr.toNat == 1024 * 5 | .error _ => false)
  let misaligned := decodeSetIPCBufferArgs (mkStub #[⟨1024 * 5 + 1⟩])
  expect "SAD-023b setIPCBuffer misaligned decodes (the operation refuses it)"
    (match misaligned with | .ok a => a.bufferAddr.toNat == 1024 * 5 + 1 | .error _ => false)
  expect "SAD-023c setIPCBuffer empty message is truncated"
    (!(decodeSetIPCBufferArgs (mkStub #[])).isOk)

-- Service family ---------------------------------------------------------------

/-- SAD-024: decodeServiceRegisterArgs — valid with 5 registers. -/
private def sad024_serviceRegister : IO Unit := do
  let stub := mkStub #[⟨1⟩, ⟨10⟩, ⟨256⟩, ⟨256⟩, ⟨1⟩]
  let result := decodeServiceRegisterArgs stub
  expect "SAD-024a serviceRegister ok" result.isOk
  match result with
  | .ok args =>
    expect "SAD-024b methodCount" (args.methodCount == 10)
    expect "SAD-024c requiresGrant" args.requiresGrant
  | .error _ => expect "SAD-024 unexpected error" false

/-- SAD-025: decodeServiceRegisterArgs — insufficient registers (4). -/
private def sad025_serviceRegisterInsufficient : IO Unit := do
  let stub := mkStub #[⟨1⟩, ⟨10⟩, ⟨256⟩, ⟨256⟩]
  let result := decodeServiceRegisterArgs stub
  expect "SAD-025a serviceRegister insufficient" (!result.isOk)

/-- SAD-025-AK4B: decodeServiceRegisterArgs — AK4-B tightened validation.
    methodCount > MAX_METHOD_COUNT (1024) rejected with invalidArgument. -/
private def sad025ak4b_serviceRegisterBoundsRejected : IO Unit := do
  let stubMc := mkStub #[⟨1⟩, ⟨1025⟩, ⟨256⟩, ⟨256⟩, ⟨0⟩]
  expect "SAD-025-AK4B a methodCount>1024 rejected"
    (!(decodeServiceRegisterArgs stubMc).isOk)
  let stubMms := mkStub #[⟨1⟩, ⟨10⟩, ⟨961⟩, ⟨256⟩, ⟨0⟩]
  expect "SAD-025-AK4B b maxMessageSize>960 rejected"
    (!(decodeServiceRegisterArgs stubMms).isOk)
  let stubMrs := mkStub #[⟨1⟩, ⟨10⟩, ⟨256⟩, ⟨961⟩, ⟨0⟩]
  expect "SAD-025-AK4B c maxResponseSize>960 rejected"
    (!(decodeServiceRegisterArgs stubMrs).isOk)
  let stubGrant := mkStub #[⟨1⟩, ⟨10⟩, ⟨256⟩, ⟨256⟩, ⟨2⟩]
  expect "SAD-025-AK4B d requiresGrant>=2 rejected"
    (!(decodeServiceRegisterArgs stubGrant).isOk)
  -- Boundary valid (at max)
  let stubOk := mkStub #[⟨1⟩, ⟨1024⟩, ⟨960⟩, ⟨960⟩, ⟨1⟩]
  expect "SAD-025-AK4B e boundary valid"
    (decodeServiceRegisterArgs stubOk).isOk

-- Zero-register edge case ------------------------------------------------------

/-- SAD-027: All no-arg decode functions succeed with empty registers. -/
private def sad027_noArgDecoders : IO Unit := do
  let stub := mkStub #[]
  expect "SAD-027a notificationWait" (decodeNotificationWaitArgs stub).isOk
  expect "SAD-027b scUnbind" (decodeSchedContextUnbindArgs stub).isOk
  expect "SAD-027c suspend" (decodeSuspendArgs stub).isOk
  expect "SAD-027d resume" (decodeResumeArgs stub).isOk

/-- SAD-028: validateVSpaceMapPermsForMemoryKind — device+execute rejection.
    WS-BP BP7.1: the check reads a physical address and a permission set — the
    address is the resolved frame's `base`, not a decoded operand. -/
private def sad028_validateVSpaceMapPermsDeviceExec : IO Unit := do
  -- PagePermissions.ofNat: bit 0=read, 1=write, 2=execute, 3=user, 4=cacheable
  let pa := PAddr.ofNat 0x80000
  let deviceRegion : MemoryRegion :=
    { base := PAddr.ofNat 0x80000, size := 0x1000, kind := .device }
  -- Device + execute should be rejected
  let result := validateVSpaceMapPermsForMemoryKind pa { execute := true } [deviceRegion]
  expect "SAD-028a device+exec rejected" (!result.isOk)
  -- Device + no execute should be accepted
  let resultOk := validateVSpaceMapPermsForMemoryKind pa { read := true } [deviceRegion]
  expect "SAD-028b device+read ok" resultOk.isOk
  -- RAM + execute should be accepted
  let ramRegion : MemoryRegion :=
    { base := PAddr.ofNat 0x80000, size := 0x1000, kind := .ram }
  let resultRam := validateVSpaceMapPermsForMemoryKind pa { execute := true } [ramRegion]
  expect "SAD-028c ram+exec ok" resultRam.isOk

-- ============================================================================
-- AK4-A.7 (R-ABI-C01): IPC-buffer overflow merge regression tests
-- ============================================================================

/-- Helper: build a minimal SystemState with a TCB whose registers encode the
    given syscall and whose IPC buffer is in the frame at `ipcBufferPA`, its
    capability in the thread's buffer slot (where seL4's `lookupIPCBuffer`
    finds it). Memory is the default (zero-initialized).
    When `mapIpcBuffer = false`, the buffer slot is empty, so
    `ipcBufferReadMr` returns `.noIpcBuffer`; `deviceFrame` makes the frame
    device memory, which the lookup refuses too. -/
private def buildIpcDecodeState
    (syscallNum : Nat) (msgLen : Nat) (msgRegs : Array SeLe4n.RegValue)
    (ipcBufferVA : SeLe4n.VAddr := (SeLe4n.VAddr.ofNat 0x10000))
    (ipcBufferPA : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0x20000))
    (mapIpcBuffer : Bool := true) (deviceFrame : Bool := false) : SeLe4n.Model.SystemState :=
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let cnodeId : SeLe4n.ObjId := ⟨801⟩
  let vsId : SeLe4n.ObjId := ⟨802⟩
  let frameId : SeLe4n.ObjId := ⟨803⟩
  let bufCap : SeLe4n.Model.Capability :=
    { target := .object frameId,
      rights := SeLe4n.Model.AccessRightSet.ofList [.read, .write] }
  -- Construct MessageInfo word: bits 0..6 = length, bits 7..8 = extraCaps, bits 9+ = label
  let msgInfoRaw := msgLen
  let regFile : SeLe4n.RegName → SeLe4n.RegValue := fun r =>
    if r.val == 0 then ⟨0⟩                -- capPtr
    else if r.val == 1 then SeLe4n.RegValue.ofNat msgInfoRaw  -- msgInfo
    else if r.val == 7 then SeLe4n.RegValue.ofNat syscallNum  -- syscallId
    else if r.val == 2 then msgRegs[0]? |>.getD ⟨0⟩
    else if r.val == 3 then msgRegs[1]? |>.getD ⟨0⟩
    else if r.val == 4 then msgRegs[2]? |>.getD ⟨0⟩
    else if r.val == 5 then msgRegs[3]? |>.getD ⟨0⟩
    else ⟨0⟩
  let mappings : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.VAddr
                   (SeLe4n.PAddr × SeLe4n.Model.PagePermissions) :=
    if mapIpcBuffer then
      -- Key the mapping on the *page base*, as `VSpaceRoot.mapPage` does:
      -- `mappings` is an exact-key table whose keys are page bases, and
      -- translation resolves the containing page.  For a page-aligned buffer
      -- (the default) this is the buffer address itself; for an offset buffer
      -- it is the page that actually contains it.
      SeLe4n.Kernel.RobinHood.RHTable.ofList
        [(ipcBufferVA.pageBase, (ipcBufferPA, { read := true, write := true }))]
    else
      SeLe4n.Kernel.RobinHood.RHTable.ofList []
  let vsRoot : SeLe4n.Model.VSpaceRoot :=
    { asid := ⟨1⟩, mappings := mappings }
  let builder := BootstrapBuilder.empty
    |>.withObject tid.toObjId (.tcb {
        tid := tid, priority := ⟨50⟩, domain := ⟨0⟩,
        spaceCells := (SeLe4n.Model.TCB.spaceCellsOf cnodeId vsId).set 2
          (if mapIpcBuffer then some bufCap else none),
        ipcBuffer := ipcBufferVA,
        registerContext := SeLe4n.RegisterFile.withGprs 0x1000 0x8000 (fun i => (regFile ⟨i⟩).val.toUInt64)
    })
    |>.withObject cnodeId (.cnode (SeLe4n.Model.CNode.ofSlots 4 (SeLe4n.UniqueSlotMap.ofListWF [])))
    |>.withObject vsId (.vspaceRoot vsRoot)
    |>.withObject frameId (.frame { base := ipcBufferPA, isDevice := deviceFrame })
    |>.withLifecycleObjectType tid.toObjId .tcb
    |>.withLifecycleObjectType cnodeId .cnode
    |>.withLifecycleObjectType vsId .vspaceRoot
    |>.withLifecycleObjectType frameId .frame
    |>.withRunnable []
    |>.withCurrent (some tid)
  builder.build

/-- AK4-A-T01: 4-arg syscall (setPriority) decodes from inline regs —
    `overflowCount = 0` for `msgInfo.length = 1`. -/
private def ak4a01_shortPathNoOverflow : IO Unit := do
  let st := buildIpcDecodeState 21 1 #[⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let regs : SeLe4n.RegisterFile :=
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.registerContext
    | _ => default
  match decodeSyscallArgsFromState (21) st tid SeLe4n.arm64DefaultLayout
          regs 32 with
  | .ok decoded =>
    expect "ok" true
    expect "overflowCount=0" (decoded.overflowCount == 0)
    expect "msgRegs populated" (decoded.msgRegs.size ≥ 1)
  | .error _ => expect "decode failed" false

/-- AK4-A-T02: 5-arg serviceRegister merges MR[4] from IPC buffer.
    IPC-buffer memory is zero (default), so MR[4] = 0. Verifies that
    `overflowCount = 1` after merge. -/
private def ak4a02_serviceRegisterOverflow : IO Unit := do
  -- serviceRegister = syscallId 11, msgLen 5
  let st := buildIpcDecodeState 11 5 #[⟨1⟩, ⟨10⟩, ⟨256⟩, ⟨256⟩]
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let regs : SeLe4n.RegisterFile :=
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.registerContext
    | _ => default
  match decodeSyscallArgsFromState (11) st tid SeLe4n.arm64DefaultLayout
          regs 32 with
  | .ok decoded =>
    expect "decoded ok" true
    expect "overflowCount=1" (decoded.overflowCount == 1)
    expect "inlineCount=4" (decoded.inlineCount == 4)
    expect "msgRegs.size=5" (decoded.msgRegs.size == 5)
    expect "msgRegs[4].val=0" (decoded.msgRegs[4]!.val == 0)
  | .error _ => expect "decode failed" false

/-- AK4-A-T03: 5-arg schedContextConfigure with unmapped VA → the message is
    clamped to its four inline words (`clampToInline`), as seL4's
    `handleInvocation` clamps a message with no IPC buffer, so the configure is
    then short of its fifth argument.  Uses an IPC buffer address that is NOT
    in the VSpaceRoot mapping table. -/
private def ak4a03_scConfigureUnmappedFails : IO Unit := do
  -- Build a state where the IPC buffer VA is NOT mapped
  let st := buildIpcDecodeState 17 5 #[⟨1000⟩, ⟨5000⟩, ⟨128⟩, ⟨10000⟩]
              (mapIpcBuffer := false)
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let regs : SeLe4n.RegisterFile :=
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.registerContext
    | _ => default
  match decodeSyscallArgsFromState (17) st tid SeLe4n.arm64DefaultLayout
          regs 32 with
  | .ok decoded =>
    expect "clamped length=4" (decoded.msgInfo.length == 4)
    expect "clamped inlineCount=4" (decoded.inlineCount == 4)
    expect "clamped overflowCount=0" (decoded.overflowCount == 0)
    expect "clamped msgRegs.size=4" (decoded.msgRegs.size == 4)
    expect "clamped short of the fifth argument"
      (decoded.msgInfo.length < SeLe4n.Kernel.Architecture.SyscallArgDecode.truncationMinimum
        decoded.syscallId)
  | .error _ => expect "decode failed" false

/-- AK4-A-T04: 5-arg syscall with msgLen=0 → ignores IPC buffer → succeeds
    with inlineCount = msgRegs.size = 4, overflowCount = 0. -/
private def ak4a04_lengthZeroIgnoresIpcBuffer : IO Unit := do
  let st := buildIpcDecodeState 11 0 #[⟨1⟩, ⟨10⟩, ⟨256⟩, ⟨256⟩]
              (mapIpcBuffer := false)
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let regs : SeLe4n.RegisterFile :=
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.registerContext
    | _ => default
  match decodeSyscallArgsFromState (11) st tid SeLe4n.arm64DefaultLayout
          regs 32 with
  | .ok decoded =>
    expect "ok" true
    expect "overflowCount=0" (decoded.overflowCount == 0)
    expect "inlineCount=4" (decoded.inlineCount == 4)
  | .error _ => expect "decode failed" false

/-- A signal or a declassified signal reads no word past the inline registers
(`syscallReadsOverflow`), as seL4's `seL4_Signal` reads no message: one whose
message-info word names ten words decodes with no IPC buffer mapped, merges no
overflow word, and the router names a long signal a signal. -/
private def signalLongReadsNoIpcBuffer : IO Unit := do
  for sid in [SyscallId.notificationSignal, SyscallId.declassifySignal] do
    let st := buildIpcDecodeState sid.toNat 10 #[⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] (mapIpcBuffer := false)
    let tid : SeLe4n.ThreadId := ⟨800⟩
    let regs : SeLe4n.RegisterFile :=
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => tcb.registerContext
      | _ => default
    match decodeSyscallArgsFromState sid.toNat st tid SeLe4n.arm64DefaultLayout regs 32 with
    | .ok decoded =>
      expect s!"{sid}: a long message reads no overflow word" (decoded.overflowCount == 0)
      expect s!"{sid}: the inline registers alone" (decoded.msgRegs.size == 4)
    | .error _ => expect s!"{sid}: a long message decodes with no IPC buffer" false
    match registerRoutedSyscall sid.toNat SeLe4n.arm64DefaultLayout regs 32, sid with
    | .signal _, .notificationSignal => expect "a long signal routes as a signal" true
    | .audited s' _, .declassifySignal =>
      expect "a long declassified signal routes as audited" (s' == .declassifySignal)
    | _, _ => expect s!"{sid}: a long message takes its short route" false

/-- A receive, a wait, a yield and an invocation of at most four arguments (a
CNode move) read no word past the inline registers (`syscallReadsOverflow`), as seL4
reads only the words a syscall uses: one whose message-info word names ten
words decodes with no IPC buffer mapped, merges no overflow word, and the
router takes its short route. -/
private def shortReadersLongReadNoIpcBuffer : IO Unit := do
  for sid in [SyscallId.receive, SyscallId.notificationWait, SyscallId.yield,
      SyscallId.cspaceMove] do
    let st := buildIpcDecodeState sid.toNat 10 #[⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] (mapIpcBuffer := false)
    let tid : SeLe4n.ThreadId := ⟨800⟩
    let regs : SeLe4n.RegisterFile :=
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => tcb.registerContext
      | _ => default
    match decodeSyscallArgsFromState sid.toNat st tid SeLe4n.arm64DefaultLayout regs 32 with
    | .ok decoded =>
      expect s!"{sid}: a long message reads no overflow word" (decoded.overflowCount == 0)
      expect s!"{sid}: the inline registers alone" (decoded.msgRegs.size == 4)
    | .error _ => expect s!"{sid}: a long message decodes with no IPC buffer" false
    match registerRoutedSyscall sid.toNat SeLe4n.arm64DefaultLayout regs 32, sid with
    | .receive .., .receive => expect "a long receive routes as a receive" true
    | .wait _, .notificationWait => expect "a long wait routes as a wait" true
    | .yield, .yield => expect "a long yield routes as a yield" true
    | .invoke s' _, .cspaceMove => expect "a long move routes as an invocation" (s' == .cspaceMove)
    | _, _ => expect s!"{sid}: a long message takes its short route" false

/-- A long send whose IPC buffer the kernel cannot read is clamped to its four
inline words (`clampToInline`), as seL4's `handleInvocation` clamps a message
with no IPC buffer to `n_msgRegisters`, rather than refused. -/
private def longSendUnmappedClamps : IO Unit := do
  let st := buildIpcDecodeState SyscallId.send.toNat 10 #[⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩]
    (mapIpcBuffer := false)
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let regs : SeLe4n.RegisterFile :=
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.registerContext
    | _ => default
  match decodeSyscallArgsFromState SyscallId.send.toNat st tid SeLe4n.arm64DefaultLayout regs 32 with
  | .ok decoded =>
    expect "long send clamped to length 4" (decoded.msgInfo.length == 4)
    expect "long send clamped: no overflow word" (decoded.overflowCount == 0)
    expect "long send clamped: the inline registers" (decoded.msgRegs.size == 4)
  | .error _ => expect "a long send with no IPC buffer decodes clamped" false

/-- AK4-A-T05: `ipcBufferReadMr` bounds check — idx = maxOverflowSlots returns
    `.overflowIndexOutOfRange`. -/
private def ak4a05_ipcBufferOutOfRange : IO Unit := do
  let st := buildIpcDecodeState 11 5 #[⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let r := ipcBufferReadMr st tid SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots
  match r with
  | .ok _ => expect "unexpected success" false
  | .error e => expect "out-of-range rejected"
                        (e == .overflowIndexOutOfRange)

/-- AK4-A-T06: Size invariant — successful decode with overflow gives
    `msgRegs.size = inlineCount + overflowCount`. -/
private def ak4a06_sizeInvariant : IO Unit := do
  let st := buildIpcDecodeState 11 5 #[⟨1⟩, ⟨10⟩, ⟨256⟩, ⟨256⟩]
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let regs : SeLe4n.RegisterFile :=
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.registerContext
    | _ => default
  match decodeSyscallArgsFromState (11) st tid SeLe4n.arm64DefaultLayout
          regs 32 with
  | .ok decoded =>
    expect "size invariant"
      (decoded.msgRegs.size == decoded.inlineCount + decoded.overflowCount)
  | .error _ => expect "decode failed" false

/-- AK4-A-T07: Legacy `decodeSyscallArgs` still produces inlineCount = 4,
    overflowCount = 0 — backward compatibility preserved. -/
private def ak4a07_legacyBackwardCompat : IO Unit := do
  let regFile : SeLe4n.RegName → SeLe4n.RegValue := fun r =>
    if r.val == 7 then ⟨4⟩ else ⟨0⟩  -- syscallId=4 (cspaceMint)
  let rf : SeLe4n.RegisterFile := SeLe4n.RegisterFile.withGprs 0 0 (fun i => (regFile ⟨i⟩).val.toUInt64)
  match decodeSyscallArgs SyscallId.send.toNat SeLe4n.arm64DefaultLayout rf 32 with
  | .ok decoded =>
    expect "legacy ok" true
    expect "legacy inlineCount=4" (decoded.inlineCount == 4)
    expect "legacy overflowCount=0" (decoded.overflowCount == 0)
  | .error _ => expect "legacy failed" false

/-- Two overflow slots resolve through the same page.

    The regression gate for the page-granular translation fix.  Every slot
    beyond the zeroth sits at a *byte* offset from the buffer base, while
    `VSpaceRoot.mappings` is keyed by page base — so the pre-fix read looked up
    `ipcBuffer + 8` as if it were a mapping key, missed, and failed the whole
    decode with `invalidMessageInfo` against a correctly mapped buffer.  Only
    slot 0 ever worked, and only because its offset is zero, which is why the
    existing coverage (`overflowCount` 0 and 1) never saw it. -/
private def ipcBufferDecodeTwoOverflowSlots : IO Unit := do
  -- msgLen 6 = 4 inline + 2 overflow, so the decode reads slots 0 AND 1.
  let st := buildIpcDecodeState 11 6 #[⟨1⟩, ⟨10⟩, ⟨256⟩, ⟨256⟩]
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let regs : SeLe4n.RegisterFile :=
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.registerContext
    | _ => default
  match decodeSyscallArgsFromState (11) st tid SeLe4n.arm64DefaultLayout regs 32 with
  | .ok decoded =>
    expect "two overflow slots decode" true
    expect "overflowCount=2" (decoded.overflowCount == 2)
    expect "msgRegs.size=6" (decoded.msgRegs.size == 6)
  | .error _ => expect "two overflow slots decode (regression)" false

/-- The intra-page offset is carried through to the physical address.

    A buffer at a non-page-aligned virtual address resolves through its
    containing page, and the offset within that page must reach the physical
    read — otherwise every slot would read the page's first word.  The pre-fix
    read failed outright here (the address was not a mapping key). -/
private def ipcBufferReadCarriesIntraPageOffset : IO Unit := do
  -- Buffer 0x10 bytes into the mapped page at VA 0x10000 → PA 0x20000.
  let st := buildIpcDecodeState 11 5 #[⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
      (SeLe4n.VAddr.ofNat 0x10010) (SeLe4n.PAddr.ofNat 0x20000) true
  match ipcBufferReadMr st ⟨800⟩ 0 with
  | .ok _ => expect "a non-page-aligned IPC buffer resolves through its page" true
  | .error _ =>
    expect "a non-page-aligned IPC buffer resolves through its page" false
  -- A buffer in a device frame is no IPC buffer (seL4's `lookupIPCBuffer`
  -- refuses a device frame capability), and the read fails closed.
  let stDev := buildIpcDecodeState 11 5 #[⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
      (SeLe4n.VAddr.ofNat 0x10000) (SeLe4n.PAddr.ofNat 0x20000) true (deviceFrame := true)
  match ipcBufferReadMr stDev ⟨800⟩ 1 with
  | .ok _ => expect "a device-frame IPC buffer fails closed" false
  | .error e =>
    expect "a device-frame IPC buffer fails closed" (e == .noIpcBuffer)

/-- SAD-029: a sender's extra capability addresses are its IPC buffer's
`caps_or_badges` words (seL4's `lookupExtraCaps`), never message registers;
the count is capped at three and a thread whose buffer the kernel cannot read
names none. -/
private def sad029_senderExtraCapAddrs : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let st0 := buildIpcDecodeState 3 2 #[⟨10⟩, ⟨20⟩, ⟨30⟩, ⟨40⟩] (mapIpcBuffer := false)
  match st0.getTcb? tid with
  | none => throw <| IO.userError "SAD-029 fixture has no thread"
  | some tcb0 =>
    expect "SAD-029a no readable buffer, no addresses"
      (SeLe4n.Kernel.senderExtraCapAddrs st0 tcb0 2).isEmpty
    let st := SeLe4n.Testing.withSenderCapAddrs st0 tid #[CPtr.ofNat 30, CPtr.ofNat 40, CPtr.ofNat 50]
    match st.getTcb? tid with
    | none => throw <| IO.userError "SAD-029 fixture lost its thread"
    | some tcb =>
      let caps := SeLe4n.Kernel.senderExtraCapAddrs st tcb 2
      expect "SAD-029b two addresses" (caps.size == 2)
      expect "SAD-029c cap0 from caps_or_badges[0]" (caps[0]!.toNat == 30)
      expect "SAD-029d cap1 from caps_or_badges[1]" (caps[1]!.toNat == 40)
      expect "SAD-029e the count is capped at three"
        ((SeLe4n.Kernel.senderExtraCapAddrs st tcb 7).map (·.toNat) == #[30, 40, 50])

/-- Run AK4-A IPC-buffer merge regression tests. -/
private def runAk4aTests : IO Unit := do
  IO.println "--- AK4-A: IPC-buffer merge (R-ABI-C01) ---"
  ak4a01_shortPathNoOverflow
  ak4a02_serviceRegisterOverflow
  ak4a03_scConfigureUnmappedFails
  ak4a04_lengthZeroIgnoresIpcBuffer
  signalLongReadsNoIpcBuffer
  shortReadersLongReadNoIpcBuffer
  longSendUnmappedClamps
  ak4a05_ipcBufferOutOfRange
  ak4a06_sizeInvariant
  ak4a07_legacyBackwardCompat
  ipcBufferDecodeTwoOverflowSlots
  ipcBufferReadCarriesIntraPageOffset

private def runSyscallArgDecodeTests : IO Unit := do
  IO.println "--- Layer 2: SyscallArgDecode ---"
  -- CSpace
  sad001_cspaceMint
  sad002_cspaceMintInsufficient
  sad003_cspaceCopy
  sad004_cspaceMove
  sad005_cspaceDelete
  -- Lifecycle
  sad006_untypedRetype
  sad007_untypedRetypeInvalidType
  -- VSpace
  sad008_vspaceMap
  sad009_vspaceMapInvalidAsid
  sad010_vspaceMapNonCanonical
  sad011_vspaceMapInvalidPerms
  sad012_vspaceUnmap
  -- Notification
  sad013_notificationSignal
  sad014_notificationWait
  sad015_replyRecv
  -- SchedContext
  sad016_schedContextConfigure
  sad017_schedContextConfigureInsufficient
  sad019_schedContextUnbind
  -- TCB
  sad020_suspendResume
  sad021_setPriority
  sad022_setMCPriority
  sad023_setIPCBuffer
  -- Service
  sad024_serviceRegister
  sad025_serviceRegisterInsufficient
  sad025ak4b_serviceRegisterBoundsRejected
  -- Edge cases
  sad027_noArgDecoders
  -- Security-relevant validation
  sad028_validateVSpaceMapPermsDeviceExec
  sad029_senderExtraCapAddrs

end SeLe4n.Testing.DecodingSuite

def main : IO Unit := do
  IO.println "=== DecodingSuite (T-03/AC6-A, AK4-A) ==="
  SeLe4n.Testing.DecodingSuite.runRegisterDecodeTests
  SeLe4n.Testing.DecodingSuite.runSyscallArgDecodeTests
  SeLe4n.Testing.DecodingSuite.runAk4aTests
  IO.println "=== DecodingSuite PASSED (48 test cases / 109 assertions) ==="
