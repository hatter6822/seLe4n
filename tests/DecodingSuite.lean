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

**Layer 1** (RegisterDecode): `decodeSyscallId`, `decodeMsgInfo`,
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

/-- RD-001: decodeSyscallId — valid syscall IDs. -/
private def rd001_decodeSyscallIdValid : IO Unit := do
  -- First valid: .send (0)
  let r0 := decodeSyscallId ⟨0⟩
  expect "send=0" (isOkEq r0 .send)
  -- Middle: .serviceRegister (11)
  let r11 := decodeSyscallId ⟨11⟩
  expect "serviceRegister=11" (isOkEq r11 .serviceRegister)
  -- Last valid: .tcbSetIPCBuffer (24)
  let r24 := decodeSyscallId ⟨24⟩
  expect "tcbSetIPCBuffer=24" (isOkEq r24 .tcbSetIPCBuffer)

/-- RD-002: decodeSyscallId — invalid values. -/
private def rd002_decodeSyscallIdInvalid : IO Unit := do
  -- First invalid: 25
  let r25 := decodeSyscallId ⟨25⟩
  expect "invalid=25" (isErrEq r25 .invalidSyscallNumber)
  -- Large value
  let rLarge := decodeSyscallId ⟨999999⟩
  expect "invalid=999999" (isErrEq rLarge .invalidSyscallNumber)

/-- RD-003: decodeSyscallId — boundary edge 24/25. -/
private def rd003_decodeSyscallIdBoundary : IO Unit := do
  let r24 := decodeSyscallId ⟨24⟩
  let r25 := decodeSyscallId ⟨25⟩
  expect "boundary=24 ok" (r24.isOk)
  expect "boundary=25 err" (!r25.isOk)

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

/-- RD-007: decodeCapPtr — out-of-range (> 2^64). -/
private def rd007_decodeCapPtrOutOfRange : IO Unit := do
  -- Value exceeding 64-bit word
  let rHuge := decodeCapPtr ⟨2^64⟩
  expect "exceeds word64" (isErrEq rHuge .invalidCapPtr)

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
    |> (writeReg · ⟨0⟩ (encodeCapPtr (CPtr.ofNat capPtrVal)))   -- x0 = capPtr
    |> (writeReg · ⟨1⟩ (encodeMsgInfo msgInfoVal))               -- x1 = msgInfo
    |> (writeReg · ⟨2⟩ ⟨100⟩)                                    -- x2 = msgReg0
    |> (writeReg · ⟨3⟩ ⟨200⟩)                                    -- x3 = msgReg1
    |> (writeReg · ⟨4⟩ ⟨300⟩)                                    -- x4 = msgReg2
    |> (writeReg · ⟨5⟩ ⟨400⟩)                                    -- x5 = msgReg3
    |> (writeReg · ⟨7⟩ (encodeSyscallId syscallVal))             -- x7 = syscallNum
  let result := decodeSyscallArgs arm64DefaultLayout rf 32
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
  let result := decodeSyscallArgs arm64DefaultLayout rf 5
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
  rd001_decodeSyscallIdValid
  rd002_decodeSyscallIdInvalid
  rd003_decodeSyscallIdBoundary
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
    msgInfo := { length := 0, extraCaps := 0, label := 0 }
    syscallId := .send
    msgRegs := regs }

-- CSpace family ---------------------------------------------------------------

/-- SAD-001: decodeCSpaceMintArgs — valid decode with 4 registers. -/
private def sad001_cspaceMint : IO Unit := do
  let stub := mkStub #[⟨10⟩, ⟨20⟩, ⟨7⟩, ⟨42⟩]
  let result := decodeCSpaceMintArgs stub
  expect "SAD-001a mint ok" result.isOk
  match result with
  | .ok args =>
    expect "SAD-001b srcSlot" (args.srcSlot.toNat == 10)
    expect "SAD-001c dstSlot" (args.dstSlot.toNat == 20)
    expect "SAD-001d badge" (args.badge.toNat == 42)
  | .error _ => expect "SAD-001 unexpected error" false

/-- SAD-002: decodeCSpaceMintArgs — insufficient registers (3). -/
private def sad002_cspaceMintInsufficient : IO Unit := do
  let stub := mkStub #[⟨10⟩, ⟨20⟩, ⟨7⟩]
  let result := decodeCSpaceMintArgs stub
  expect "SAD-002a mint insufficient" (!result.isOk)

/-- SAD-003: decodeCSpaceCopyArgs — valid decode with 2 registers. -/
private def sad003_cspaceCopy : IO Unit := do
  let stub := mkStub #[⟨5⟩, ⟨15⟩]
  let result := decodeCSpaceCopyArgs stub
  expect "SAD-003a copy ok" result.isOk
  match result with
  | .ok args =>
    expect "SAD-003b srcSlot" (args.srcSlot.toNat == 5)
    expect "SAD-003c dstSlot" (args.dstSlot.toNat == 15)
  | .error _ => expect "SAD-003 unexpected error" false

/-- SAD-004: decodeCSpaceMoveArgs — valid decode. -/
private def sad004_cspaceMove : IO Unit := do
  let stub := mkStub #[⟨3⟩, ⟨8⟩]
  let result := decodeCSpaceMoveArgs stub
  expect "SAD-004a move ok" result.isOk

/-- SAD-005: decodeCSpaceDeleteArgs — valid and insufficient. -/
private def sad005_cspaceDelete : IO Unit := do
  let stub1 := mkStub #[⟨7⟩]
  let result1 := decodeCSpaceDeleteArgs stub1
  expect "SAD-005a delete ok" result1.isOk
  let stub0 := mkStub #[]
  let result0 := decodeCSpaceDeleteArgs stub0
  expect "SAD-005b delete empty err" (!result0.isOk)

-- Lifecycle family -------------------------------------------------------------

/-- SAD-006: decodeLifecycleRetypeArgs — valid decode with recognized type. -/
private def sad006_lifecycleRetype : IO Unit := do
  -- KernelObjectType tag 0 should be the first valid type
  let stub := mkStub #[⟨100⟩, ⟨0⟩, ⟨4096⟩]
  let result := decodeLifecycleRetypeArgs stub
  expect "SAD-006a retype ok" result.isOk

/-- SAD-007: decodeLifecycleRetypeArgs — invalid type tag. -/
private def sad007_lifecycleRetypeInvalidType : IO Unit := do
  let stub := mkStub #[⟨100⟩, ⟨999⟩, ⟨4096⟩]
  let result := decodeLifecycleRetypeArgs stub
  expect "SAD-007a retype invalid type" (!result.isOk)

-- VSpace family ----------------------------------------------------------------

/-- SAD-008: decodeVSpaceMapArgs — valid decode. -/
private def sad008_vspaceMap : IO Unit := do
  -- ASID < 65536, VAddr < 2^48, PAddr arbitrary, perms valid (< 32)
  -- AH3-C: Pass ARM64 default maxASID (65536) to parameterized decode
  let stub := mkStub #[⟨1⟩, ⟨0x1000⟩, ⟨0x2000⟩, ⟨1⟩]
  let result := decodeVSpaceMapArgs stub 65536
  expect "SAD-008a vspace map ok" result.isOk

/-- SAD-009: decodeVSpaceMapArgs — invalid ASID (>= 65536). -/
private def sad009_vspaceMapInvalidAsid : IO Unit := do
  let stub := mkStub #[⟨65536⟩, ⟨0x1000⟩, ⟨0x2000⟩, ⟨1⟩]
  let result := decodeVSpaceMapArgs stub 65536
  expect "SAD-009a vspace map invalid ASID" (!result.isOk)

/-- SAD-010: decodeVSpaceMapArgs — non-canonical VAddr (>= 2^48). -/
private def sad010_vspaceMapNonCanonical : IO Unit := do
  let stub := mkStub #[⟨1⟩, ⟨2^48⟩, ⟨0x2000⟩, ⟨1⟩]
  let result := decodeVSpaceMapArgs stub 65536
  expect "SAD-010a vspace map non-canonical" (!result.isOk)

/-- SAD-011: decodeVSpaceMapArgs — invalid permissions (>= 32). -/
private def sad011_vspaceMapInvalidPerms : IO Unit := do
  let stub := mkStub #[⟨1⟩, ⟨0x1000⟩, ⟨0x2000⟩, ⟨32⟩]
  let result := decodeVSpaceMapArgs stub 65536
  expect "SAD-011a vspace map invalid perms" (!result.isOk)

/-- SAD-012: decodeVSpaceUnmapArgs — valid and invalid ASID. -/
private def sad012_vspaceUnmap : IO Unit := do
  let stub := mkStub #[⟨1⟩, ⟨0x1000⟩]
  let result := decodeVSpaceUnmapArgs stub 65536
  expect "SAD-012a vspace unmap ok" result.isOk
  let stubBad := mkStub #[⟨65536⟩, ⟨0x1000⟩]
  let resultBad := decodeVSpaceUnmapArgs stubBad 65536
  expect "SAD-012b vspace unmap invalid ASID" (!resultBad.isOk)

-- Notification family ----------------------------------------------------------

/-- SAD-013: decodeNotificationSignalArgs — valid decode. -/
private def sad013_notificationSignal : IO Unit := do
  let stub := mkStub #[⟨0xFF⟩]
  let result := decodeNotificationSignalArgs stub
  expect "SAD-013a notification signal ok" result.isOk

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

/-- SAD-016: decodeSchedContextConfigureArgs — valid decode with 5 registers. -/
private def sad016_schedContextConfigure : IO Unit := do
  let stub := mkStub #[⟨1000⟩, ⟨5000⟩, ⟨128⟩, ⟨10000⟩, ⟨0⟩]
  let result := decodeSchedContextConfigureArgs stub
  expect "SAD-016a scConfigure ok" result.isOk
  match result with
  | .ok args =>
    expect "SAD-016b budget" (args.budget == 1000)
    expect "SAD-016c period" (args.period == 5000)
    expect "SAD-016d priority" (args.priority == 128)
  | .error _ => expect "SAD-016 unexpected error" false

/-- SAD-017: decodeSchedContextConfigureArgs — insufficient registers (4). -/
private def sad017_schedContextConfigureInsufficient : IO Unit := do
  let stub := mkStub #[⟨1000⟩, ⟨5000⟩, ⟨128⟩, ⟨10000⟩]
  let result := decodeSchedContextConfigureArgs stub
  expect "SAD-017a scConfigure insufficient" (!result.isOk)

/-- SAD-018: decodeSchedContextBindArgs — valid and insufficient. -/
private def sad018_schedContextBind : IO Unit := do
  let stub := mkStub #[⟨5⟩]
  let result := decodeSchedContextBindArgs stub
  expect "SAD-018a scBind ok" result.isOk
  let stubEmpty := mkStub #[]
  let resultEmpty := decodeSchedContextBindArgs stubEmpty
  expect "SAD-018b scBind empty err" (!resultEmpty.isOk)

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

/-- SAD-023: decodeSetIPCBufferArgs — valid (aligned) and invalid (misaligned). -/
private def sad023_setIPCBuffer : IO Unit := do
  -- Valid: 512-byte aligned address
  let stub := mkStub #[⟨512 * 10⟩]
  let result := decodeSetIPCBufferArgs stub
  expect "SAD-023a setIPCBuffer aligned ok" result.isOk
  -- Invalid: misaligned address
  let stubBad := mkStub #[⟨512 * 10 + 1⟩]
  let resultBad := decodeSetIPCBufferArgs stubBad
  expect "SAD-023b setIPCBuffer misaligned err" (!resultBad.isOk)

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

/-- SAD-026: decodeServiceRevokeArgs — valid and insufficient. -/
private def sad026_serviceRevoke : IO Unit := do
  let stub := mkStub #[⟨7⟩]
  let result := decodeServiceRevokeArgs stub
  expect "SAD-026a serviceRevoke ok" result.isOk
  let stubEmpty := mkStub #[]
  let resultEmpty := decodeServiceRevokeArgs stubEmpty
  expect "SAD-026b serviceRevoke empty err" (!resultEmpty.isOk)

-- Zero-register edge case ------------------------------------------------------

/-- SAD-027: All no-arg decode functions succeed with empty registers. -/
private def sad027_noArgDecoders : IO Unit := do
  let stub := mkStub #[]
  expect "SAD-027a notificationWait" (decodeNotificationWaitArgs stub).isOk
  expect "SAD-027b scUnbind" (decodeSchedContextUnbindArgs stub).isOk
  expect "SAD-027c suspend" (decodeSuspendArgs stub).isOk
  expect "SAD-027d resume" (decodeResumeArgs stub).isOk

/-- SAD-028: validateVSpaceMapPermsForMemoryKind — device+execute rejection. -/
private def sad028_validateVSpaceMapPermsDeviceExec : IO Unit := do
  -- PagePermissions.ofNat: bit 0=read, 1=write, 2=execute, 3=user, 4=cacheable
  -- Construct args with execute=true, placed in a device region
  let args : VSpaceMapArgs :=
    { asid := ASID.ofNat 1, vaddr := VAddr.ofNat 0x1000
      paddr := PAddr.ofNat 0x80000, perms := { execute := true } }
  let deviceRegion : MemoryRegion :=
    { base := PAddr.ofNat 0x80000, size := 0x1000, kind := .device }
  -- Device + execute should be rejected
  let result := validateVSpaceMapPermsForMemoryKind args [deviceRegion]
  expect "SAD-028a device+exec rejected" (!result.isOk)
  -- Device + no execute should be accepted
  let argsNoExec : VSpaceMapArgs :=
    { asid := ASID.ofNat 1, vaddr := VAddr.ofNat 0x1000
      paddr := PAddr.ofNat 0x80000, perms := { read := true } }
  let resultOk := validateVSpaceMapPermsForMemoryKind argsNoExec [deviceRegion]
  expect "SAD-028b device+read ok" resultOk.isOk
  -- RAM + execute should be accepted
  let ramRegion : MemoryRegion :=
    { base := PAddr.ofNat 0x80000, size := 0x1000, kind := .ram }
  let resultRam := validateVSpaceMapPermsForMemoryKind args [ramRegion]
  expect "SAD-028c ram+exec ok" resultRam.isOk

/-- SAD-029: decodeExtraCapAddrs — basic and truncation behavior. -/
private def sad029_decodeExtraCapAddrs : IO Unit := do
  -- Set up a stub with 4 msgRegs, length=2, extraCaps=2
  -- Extra caps start at index=length (2), so indices 2,3
  let stub : SyscallDecodeResult :=
    { capAddr := CPtr.ofNat 0
      msgInfo := { length := 2, extraCaps := 2, label := 0 }
      syscallId := .send
      msgRegs := #[⟨10⟩, ⟨20⟩, ⟨30⟩, ⟨40⟩] }
  let caps := decodeExtraCapAddrs stub
  expect "SAD-029a extraCaps count" (caps.size == 2)
  expect "SAD-029b cap0 value" (caps[0]!.toNat == 30)
  expect "SAD-029c cap1 value" (caps[1]!.toNat == 40)
  -- Truncation: extraCaps=2 but only 1 register available after length
  let stubShort : SyscallDecodeResult :=
    { capAddr := CPtr.ofNat 0
      msgInfo := { length := 2, extraCaps := 2, label := 0 }
      syscallId := .send
      msgRegs := #[⟨10⟩, ⟨20⟩, ⟨30⟩] }  -- only index 2 available, not 3
  let capsShort := decodeExtraCapAddrs stubShort
  expect "SAD-029d truncated to 1" (capsShort.size == 1)

-- ============================================================================
-- AK4-A.7 (R-ABI-C01): IPC-buffer overflow merge regression tests
-- ============================================================================

/-- Helper: build a minimal SystemState with a TCB whose registers encode the
    given syscall and whose IPC buffer resolves to PA=0 in a well-formed
    VSpaceRoot. Memory is the default (zero-initialized).
    When `mapIpcBuffer = false`, the VSpaceRoot contains no mapping, so
    `ipcBufferReadMr` returns `.ipcBufferVAddrUnmapped`. -/
private def buildIpcDecodeState
    (syscallNum : Nat) (msgLen : Nat) (msgRegs : Array SeLe4n.RegValue)
    (ipcBufferVA : SeLe4n.VAddr := (SeLe4n.VAddr.ofNat 0x10000))
    (ipcBufferPA : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat 0x20000))
    (mapIpcBuffer : Bool := true) : SeLe4n.Model.SystemState :=
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let cnodeId : SeLe4n.ObjId := ⟨801⟩
  let vsId : SeLe4n.ObjId := ⟨802⟩
  -- Construct MessageInfo word: bits 0..6 = length, bits 7..8 = extraCaps, bits 9+ = label
  let msgInfoRaw := msgLen
  let regFile : SeLe4n.RegName → SeLe4n.RegValue := fun r =>
    if r.val == 0 then ⟨0⟩                -- capPtr
    else if r.val == 1 then ⟨msgInfoRaw⟩  -- msgInfo
    else if r.val == 7 then ⟨syscallNum⟩  -- syscallId
    else if r.val == 2 then msgRegs[0]? |>.getD ⟨0⟩
    else if r.val == 3 then msgRegs[1]? |>.getD ⟨0⟩
    else if r.val == 4 then msgRegs[2]? |>.getD ⟨0⟩
    else if r.val == 5 then msgRegs[3]? |>.getD ⟨0⟩
    else ⟨0⟩
  let mappings : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.VAddr
                   (SeLe4n.PAddr × SeLe4n.Model.PagePermissions) :=
    if mapIpcBuffer then
      SeLe4n.Kernel.RobinHood.RHTable.ofList
        [(ipcBufferVA, (ipcBufferPA, { read := true, write := true }))]
    else
      SeLe4n.Kernel.RobinHood.RHTable.ofList []
  let vsRoot : SeLe4n.Model.VSpaceRoot :=
    { asid := ⟨1⟩, mappings := mappings }
  let builder := BootstrapBuilder.empty
    |>.withObject tid.toObjId (.tcb {
        tid := tid, priority := ⟨50⟩, domain := ⟨0⟩,
        cspaceRoot := cnodeId, vspaceRoot := vsId,
        ipcBuffer := ipcBufferVA, ipcState := .ready,
        registerContext := { pc := ⟨0x1000⟩, sp := ⟨0x8000⟩, gpr := regFile }
    })
    |>.withObject cnodeId (.cnode {
        depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
        slots := SeLe4n.Kernel.RobinHood.RHTable.ofList []
    })
    |>.withObject vsId (.vspaceRoot vsRoot)
    |>.withLifecycleObjectType tid.toObjId .tcb
    |>.withLifecycleObjectType cnodeId .cnode
    |>.withLifecycleObjectType vsId .vspaceRoot
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
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
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
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          regs 32 with
  | .ok decoded =>
    expect "decoded ok" true
    expect "overflowCount=1" (decoded.overflowCount == 1)
    expect "inlineCount=4" (decoded.inlineCount == 4)
    expect "msgRegs.size=5" (decoded.msgRegs.size == 5)
    expect "msgRegs[4].val=0" (decoded.msgRegs[4]!.val == 0)
  | .error _ => expect "decode failed" false

/-- AK4-A-T03: 5-arg schedContextConfigure with unmapped VA → fails with
    `.invalidMessageInfo`. Uses an IPC buffer address that is NOT in the
    VSpaceRoot mapping table. -/
private def ak4a03_scConfigureUnmappedFails : IO Unit := do
  -- Build a state where the IPC buffer VA is NOT mapped
  let st := buildIpcDecodeState 17 5 #[⟨1000⟩, ⟨5000⟩, ⟨128⟩, ⟨10000⟩]
              (mapIpcBuffer := false)
  let tid : SeLe4n.ThreadId := ⟨800⟩
  let regs : SeLe4n.RegisterFile :=
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.registerContext
    | _ => default
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          regs 32 with
  | .ok _ => expect "unexpected success" false
  | .error e =>
    expect "invalidMessageInfo" (e == .invalidMessageInfo)

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
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          regs 32 with
  | .ok decoded =>
    expect "ok" true
    expect "overflowCount=0" (decoded.overflowCount == 0)
    expect "inlineCount=4" (decoded.inlineCount == 4)
  | .error _ => expect "decode failed" false

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
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
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
  let rf : SeLe4n.RegisterFile := { pc := ⟨0⟩, sp := ⟨0⟩, gpr := regFile }
  match decodeSyscallArgs SeLe4n.arm64DefaultLayout rf 32 with
  | .ok decoded =>
    expect "legacy ok" true
    expect "legacy inlineCount=4" (decoded.inlineCount == 4)
    expect "legacy overflowCount=0" (decoded.overflowCount == 0)
  | .error _ => expect "legacy failed" false

/-- Run AK4-A IPC-buffer merge regression tests. -/
private def runAk4aTests : IO Unit := do
  IO.println "--- AK4-A: IPC-buffer merge (R-ABI-C01) ---"
  ak4a01_shortPathNoOverflow
  ak4a02_serviceRegisterOverflow
  ak4a03_scConfigureUnmappedFails
  ak4a04_lengthZeroIgnoresIpcBuffer
  ak4a05_ipcBufferOutOfRange
  ak4a06_sizeInvariant
  ak4a07_legacyBackwardCompat

private def runSyscallArgDecodeTests : IO Unit := do
  IO.println "--- Layer 2: SyscallArgDecode ---"
  -- CSpace
  sad001_cspaceMint
  sad002_cspaceMintInsufficient
  sad003_cspaceCopy
  sad004_cspaceMove
  sad005_cspaceDelete
  -- Lifecycle
  sad006_lifecycleRetype
  sad007_lifecycleRetypeInvalidType
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
  sad018_schedContextBind
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
  sad026_serviceRevoke
  -- Edge cases
  sad027_noArgDecoders
  -- Security-relevant validation
  sad028_validateVSpaceMapPermsDeviceExec
  sad029_decodeExtraCapAddrs

end SeLe4n.Testing.DecodingSuite

def main : IO Unit := do
  IO.println "=== DecodingSuite (T-03/AC6-A, AK4-A) ==="
  SeLe4n.Testing.DecodingSuite.runRegisterDecodeTests
  SeLe4n.Testing.DecodingSuite.runSyscallArgDecodeTests
  SeLe4n.Testing.DecodingSuite.runAk4aTests
  IO.println "=== DecodingSuite PASSED (48 test cases / 109 assertions) ==="
