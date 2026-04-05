/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.SyscallArgDecode
import SeLe4n.Testing.Helpers

/-! # T-03/AC6-A: Dedicated Decoding Suite

Standalone test coverage for `RegisterDecode.lean` (Layer 1) and
`SyscallArgDecode.lean` (Layer 2). Previously, decode tests were
dispersed across NegativeStateSuite and OperationChainSuite.

**Layer 1** (RegisterDecode): `decodeSyscallId`, `decodeMsgInfo`,
`decodeCapPtr`, `validateRegBound`, `decodeSyscallArgs`.

**Layer 2** (SyscallArgDecode): 17 per-syscall decode functions
organized by subsystem (CSpace, VSpace, Lifecycle, Service,
Notification, SchedContext, TCB). -/

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture.RegisterDecode
open SeLe4n.Kernel.Architecture.SyscallArgDecode
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
  expect "RD-001a send=0" (isOkEq r0 .send)
  -- Middle: .serviceRegister (11)
  let r11 := decodeSyscallId ⟨11⟩
  expect "RD-001b serviceRegister=11" (isOkEq r11 .serviceRegister)
  -- Last valid: .tcbSetIPCBuffer (24)
  let r24 := decodeSyscallId ⟨24⟩
  expect "RD-001c tcbSetIPCBuffer=24" (isOkEq r24 .tcbSetIPCBuffer)

/-- RD-002: decodeSyscallId — invalid values. -/
private def rd002_decodeSyscallIdInvalid : IO Unit := do
  -- First invalid: 25
  let r25 := decodeSyscallId ⟨25⟩
  expect "RD-002a invalid=25" (isErrEq r25 .invalidSyscallNumber)
  -- Large value
  let rLarge := decodeSyscallId ⟨999999⟩
  expect "RD-002b invalid=999999" (isErrEq rLarge .invalidSyscallNumber)

/-- RD-003: decodeSyscallId — boundary edge 24/25. -/
private def rd003_decodeSyscallIdBoundary : IO Unit := do
  let r24 := decodeSyscallId ⟨24⟩
  let r25 := decodeSyscallId ⟨25⟩
  expect "RD-003a boundary=24 ok" (r24.isOk)
  expect "RD-003b boundary=25 err" (!r25.isOk)

/-- RD-004: decodeMsgInfo — valid round-trip. -/
private def rd004_decodeMsgInfoValid : IO Unit := do
  let mi : MessageInfo := { length := 4, extraCaps := 2, label := 100 }
  let encoded := encodeMsgInfo mi
  let decoded := decodeMsgInfo encoded
  expect "RD-004a round-trip" (isOkEq decoded mi)

/-- RD-005: decodeMsgInfo — boundary and overflow values. -/
private def rd005_decodeMsgInfoOverflow : IO Unit := do
  -- Boundary: length=120 (maxMessageRegisters) should succeed
  let miBoundary : MessageInfo := { length := 120, extraCaps := 0, label := 0 }
  let encodedBoundary := encodeMsgInfo miBoundary
  let decodedBoundary := decodeMsgInfo encodedBoundary
  expect "RD-005a boundary length=120 ok" (isOkEq decodedBoundary miBoundary)
  -- Overflow: length=121 should fail
  -- length field is bits 0..6 (7 bits), extraCaps bits 7..8 (2 bits), label bits 9+
  let rawWithLength121 := 121  -- bits 0-6 = 121
  let result := decodeMsgInfo ⟨rawWithLength121⟩
  expect "RD-005b overflow length" (!result.isOk)

/-- RD-006: decodeCapPtr — valid and boundary values. -/
private def rd006_decodeCapPtrValid : IO Unit := do
  -- Small value
  let r := decodeCapPtr ⟨42⟩
  expect "RD-006a small value" (isOkEq r (CPtr.ofNat 42))
  -- Zero
  let r0 := decodeCapPtr ⟨0⟩
  expect "RD-006b zero" (isOkEq r0 (CPtr.ofNat 0))

/-- RD-007: decodeCapPtr — out-of-range (> 2^64). -/
private def rd007_decodeCapPtrOutOfRange : IO Unit := do
  -- Value exceeding 64-bit word
  let rHuge := decodeCapPtr ⟨2^64⟩
  expect "RD-007a exceeds word64" (isErrEq rHuge .invalidCapPtr)

/-- RD-008: validateRegBound — valid and boundary values. -/
private def rd008_validateRegBound : IO Unit := do
  -- Valid: index 0 within bound 32
  let r0 := validateRegBound ⟨0⟩ 32
  expect "RD-008a idx=0 bound=32 ok" r0.isOk
  -- Valid: last valid index (31)
  let r31 := validateRegBound ⟨31⟩ 32
  expect "RD-008b idx=31 bound=32 ok" r31.isOk
  -- Invalid: index 32 (at bound)
  let r32 := validateRegBound ⟨32⟩ 32
  expect "RD-008c idx=32 bound=32 err" (isErrEq r32 .invalidRegister)

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
  expect "RD-009a integration ok" result.isOk
  match result with
  | .ok dr =>
    expect "RD-009b capAddr" (dr.capAddr.toNat == capPtrVal)
    expect "RD-009c syscallId" (dr.syscallId == syscallVal)
    expect "RD-009d msgRegs length" (dr.msgRegs.size == 4)
    expect "RD-009e msgReg0" (dr.msgRegs[0]! == ⟨100⟩)
    expect "RD-009f msgReg1" (dr.msgRegs[1]! == ⟨200⟩)
  | .error _ => pure ()

/-- RD-010: decodeSyscallArgs — insufficient regCount rejects. -/
private def rd010_decodeSyscallArgsInsufficientRegs : IO Unit := do
  let rf := (default : RegisterFile)
  -- regCount=5 means registers 0..4 are valid, but arm64DefaultLayout needs x7
  let result := decodeSyscallArgs arm64DefaultLayout rf 5
  expect "RD-010a insufficient regs" (!result.isOk)

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
  | .error _ => pure ()

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
  | .error _ => pure ()

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
  let stub := mkStub #[⟨1⟩, ⟨0x1000⟩, ⟨0x2000⟩, ⟨1⟩]
  let result := decodeVSpaceMapArgs stub
  expect "SAD-008a vspace map ok" result.isOk

/-- SAD-009: decodeVSpaceMapArgs — invalid ASID (>= 65536). -/
private def sad009_vspaceMapInvalidAsid : IO Unit := do
  let stub := mkStub #[⟨65536⟩, ⟨0x1000⟩, ⟨0x2000⟩, ⟨1⟩]
  let result := decodeVSpaceMapArgs stub
  expect "SAD-009a vspace map invalid ASID" (!result.isOk)

/-- SAD-010: decodeVSpaceMapArgs — non-canonical VAddr (>= 2^48). -/
private def sad010_vspaceMapNonCanonical : IO Unit := do
  let stub := mkStub #[⟨1⟩, ⟨2^48⟩, ⟨0x2000⟩, ⟨1⟩]
  let result := decodeVSpaceMapArgs stub
  expect "SAD-010a vspace map non-canonical" (!result.isOk)

/-- SAD-011: decodeVSpaceMapArgs — invalid permissions (>= 32). -/
private def sad011_vspaceMapInvalidPerms : IO Unit := do
  let stub := mkStub #[⟨1⟩, ⟨0x1000⟩, ⟨0x2000⟩, ⟨32⟩]
  let result := decodeVSpaceMapArgs stub
  expect "SAD-011a vspace map invalid perms" (!result.isOk)

/-- SAD-012: decodeVSpaceUnmapArgs — valid and invalid ASID. -/
private def sad012_vspaceUnmap : IO Unit := do
  let stub := mkStub #[⟨1⟩, ⟨0x1000⟩]
  let result := decodeVSpaceUnmapArgs stub
  expect "SAD-012a vspace unmap ok" result.isOk
  let stubBad := mkStub #[⟨65536⟩, ⟨0x1000⟩]
  let resultBad := decodeVSpaceUnmapArgs stubBad
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
  | .error _ => pure ()

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
  | .error _ => pure ()
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
  | .error _ => pure ()

/-- SAD-025: decodeServiceRegisterArgs — insufficient registers (4). -/
private def sad025_serviceRegisterInsufficient : IO Unit := do
  let stub := mkStub #[⟨1⟩, ⟨10⟩, ⟨256⟩, ⟨256⟩]
  let result := decodeServiceRegisterArgs stub
  expect "SAD-025a serviceRegister insufficient" (!result.isOk)

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
  sad026_serviceRevoke
  -- Edge cases
  sad027_noArgDecoders

end SeLe4n.Testing.DecodingSuite

def main : IO Unit := do
  IO.println "=== DecodingSuite (T-03/AC6-A) ==="
  SeLe4n.Testing.DecodingSuite.runRegisterDecodeTests
  SeLe4n.Testing.DecodingSuite.runSyscallArgDecodeTests
  IO.println "=== DecodingSuite PASSED (37 tests) ==="
