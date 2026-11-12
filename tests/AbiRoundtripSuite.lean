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

/-! # AK4-G: End-to-end ABI round-trip regression suite

Simulates the Rust `sele4n-abi` encoder by writing message registers in the
same byte layout the production Rust wrappers produce, then decodes each
via the Lean kernel's `decodeSyscallArgsFromState` and per-syscall argument
decoders.

The suite closes the gap noted by the v0.29.0 audit:
> "No end-to-end test encoding via `sele4n-sys` wrappers and decoding via the
>  Lean kernel — would have caught R-ABI-C01 immediately."

**Coverage:** Two boundary scenarios per 5-arg syscall:
- `serviceRegister` (syscallId 11) — 5 args, MR[4] in IPC buffer overflow.
- `schedContextConfigure` (syscallId 17) — 5 args, MR[4] in IPC buffer.

Plus a representative 4-arg syscall (`cspaceMint`) and a 2-arg syscall
(`cspaceCopy`) exercising the short (no-overflow) path.
-/

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture.RegisterDecode
open SeLe4n.Kernel.Architecture.SyscallArgDecode
open SeLe4n.Kernel.Architecture.IpcBufferRead
open SeLe4n.Testing

namespace SeLe4n.Testing.AbiRoundtripSuite

private def tag : String := "abi-rt"

private def expect (label : String) (cond : Bool) : IO Unit :=
  expectCond tag label cond

/-- Encode a `UInt64` value into eight little-endian bytes, matching the byte
    layout of `rust/sele4n-abi/src/ipc_buffer.rs` (`#[repr(C)]` + `u64`). -/
private def encodeLittleEndian (v : UInt64) : Array UInt8 :=
  Id.run do
    let mut out : Array UInt8 := #[]
    for i in [:8] do
      out := out.push (((v >>> (i.toUInt64 * 8)) &&& 0xFF).toUInt8)
    pure out

/-- Build a SystemState whose current thread has its msg registers (x2..x5)
    populated from the inline Rust encoding and whose IPC buffer is mapped
    to a fresh page with the overflow words written where seL4's
    `seL4_IPCBuffer` holds them, `msg[4 + i]`. -/
private def buildAbiState
    (syscallId : Nat) (msgLen : Nat)
    (inlineRegs : Array UInt64) (overflowRegs : Array UInt64)
    : SeLe4n.Model.SystemState :=
  Id.run do
    let tid : SeLe4n.ThreadId := ⟨900⟩
    let cnodeId : SeLe4n.ObjId := ⟨901⟩
    let vsId : SeLe4n.ObjId := ⟨902⟩
    let ipcBufferVA : SeLe4n.VAddr := (SeLe4n.VAddr.ofNat (0x20_000))
    let ipcBufferPA : SeLe4n.PAddr := (SeLe4n.PAddr.ofNat (0x40_000))
    -- Encode each overflow u64 into bytes at the correct physical offset
    let mut mem : SeLe4n.Memory := fun _ => 0
    for i in [:overflowRegs.size] do
      let val := overflowRegs[i]!
      let bytes := encodeLittleEndian val
      for j in [:8] do
        let addr := SeLe4n.PAddr.ofNat (ipcBufferPA.toNat +
          (SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowBaseWord + i) * 8 + j)
        let b := bytes[j]!
        mem := fun a => if a == addr then b else mem a
    -- Register file populated per ARM64 layout: x2..x5 = inline regs.
    let regFile : SeLe4n.RegName → SeLe4n.RegValue := fun r =>
      if r.val == 0 then ⟨0⟩                       -- capPtr
      else if r.val == 1 then ⟨msgLen⟩             -- msgInfo (length field, low 7 bits)
      else if r.val == 7 then ⟨syscallId⟩          -- syscallId
      else if r.val == 2 then ⟨(inlineRegs[0]? |>.getD 0).toNat⟩
      else if r.val == 3 then ⟨(inlineRegs[1]? |>.getD 0).toNat⟩
      else if r.val == 4 then ⟨(inlineRegs[2]? |>.getD 0).toNat⟩
      else if r.val == 5 then ⟨(inlineRegs[3]? |>.getD 0).toNat⟩
      else ⟨0⟩
    let vsRoot : SeLe4n.Model.VSpaceRoot :=
      { asid := ⟨1⟩
        mappings := SeLe4n.Kernel.RobinHood.RHTable.ofList
          [(ipcBufferVA, (ipcBufferPA, { read := true, write := true }))] }
    let builder := BootstrapBuilder.empty
      |>.withObject tid.toObjId (.tcb {
          tid := tid, priority := ⟨50⟩, domain := ⟨0⟩,
          spaceCells := SeLe4n.Model.TCB.spaceCellsOf cnodeId vsId,
          ipcBuffer := ipcBufferVA,
          registerContext := SeLe4n.RegisterFile.withGprs 0x1000 0x8000 (fun i => (regFile ⟨i⟩).val.toUInt64)
      })
      |>.withObject cnodeId (.cnode (SeLe4n.Model.CNode.ofSlots 4 0 0 4 (SeLe4n.UniqueSlotMap.ofListWF [])))
      |>.withObject vsId (.vspaceRoot vsRoot)
      |>.withLifecycleObjectType tid.toObjId .tcb
      |>.withLifecycleObjectType cnodeId .cnode
      |>.withLifecycleObjectType vsId .vspaceRoot
      |>.withRunnable []
      |>.withCurrent (some tid)
    let st := builder.build
    pure { st with machine := { st.machine with memory := mem } }

/-- Helper: extract the current thread's register file from a built state. -/
private def regsOf (st : SeLe4n.Model.SystemState) (tid : SeLe4n.ThreadId)
    : SeLe4n.RegisterFile :=
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) => tcb.registerContext
  | _ => default

/-- AK4-G-T01: serviceRegister with 5 args — inline regs + 1 overflow from IPC buffer.
    Verifies the Rust-encoded message decodes successfully in Lean. -/
private def t01_service_register_full_abi : IO Unit := do
  let syscallId := 11  -- serviceRegister
  let msgLen := 5
  let inline : Array UInt64 := #[7, 10, 256, 128]           -- x2..x5
  let overflow : Array UInt64 := #[1]                        -- MR[4] = requiresGrant=1
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error e =>
    throw <| IO.userError s!"decode failed: {toString e}"
  | .ok decoded =>
    expect "overflowCount=1" (decoded.overflowCount == 1)
    expect "msgRegs.size=5" (decoded.msgRegs.size == 5)
    -- Now run the per-syscall decoder
    match decodeServiceRegisterArgs decoded with
    | .error e =>
      throw <| IO.userError s!"per-syscall decode failed: {toString e}"
    | .ok args =>
      expect "interfaceId=7" (args.interfaceId.toNat == 7)
      expect "methodCount=10" (args.methodCount == 10)
      expect "maxMessageSize=256" (args.maxMessageSize == 256)
      expect "maxResponseSize=128" (args.maxResponseSize == 128)
      expect "requiresGrant=true" args.requiresGrant

/-- AK4-G-T02: serviceRegister with methodCount > MAX → rejected.
    AK4-B tightened validation should fail the out-of-range methodCount. -/
private def t02_service_register_bounds_rejected : IO Unit := do
  let syscallId := 11
  let msgLen := 5
  let inline : Array UInt64 := #[7, 2048, 256, 128]  -- methodCount=2048 > 1024
  let overflow : Array UInt64 := #[0]
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error _ =>
    throw <| IO.userError "base decode unexpectedly failed"
  | .ok decoded =>
    match decodeServiceRegisterArgs decoded with
    | .error .invalidArgument =>
      expect "methodCount>MAX rejected" true
    | .error e =>
      throw <| IO.userError s!"expected invalidArgument, got {toString e}"
    | .ok _ =>
      throw <| IO.userError "expected error, got ok"

/-- AK4-G-T03: schedContextConfigure with 5 args — inline + 1 overflow. -/
private def t03_sched_context_configure_full_abi : IO Unit := do
  let syscallId := 17  -- schedContextConfigure
  let msgLen := 5
  -- WS-ZA ZA6.4: x2 = the context's cptr, x5 = priority 128 | domain 3 << 8
  let inline : Array UInt64 := #[7, 1000, 10000, 128 + 3 * 256]     -- x2..x5
  let overflow : Array UInt64 := #[5000]                      -- MR[4] = deadline=5000
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error e =>
    throw <| IO.userError s!"decode failed: {toString e}"
  | .ok decoded =>
    expect "overflowCount=1" (decoded.overflowCount == 1)
    match decodeSchedContextConfigureArgs decoded with
    | .error e =>
      throw <| IO.userError s!"per-syscall decode failed: {toString e}"
    | .ok args =>
      expect "context cptr=7" (args.scCPtr == SeLe4n.CPtr.ofNat 7)
      expect "budget=1000" (args.budget == 1000)
      expect "period=10000" (args.period == 10000)
      expect "priority=128" (args.priority == 128)
      expect "deadline=5000" (args.deadline == 5000)
      expect "domain=3" (args.domain == 3)

/-- AK4-G-T04: schedContextConfigure with domain > MAX → rejected.
    AK3-J / AK4-D tightened validation. -/
private def t04_sc_configure_domain_rejected : IO Unit := do
  let syscallId := 17
  let msgLen := 5
  let inline : Array UInt64 := #[7, 1000, 10000, 128 + 16 * 256]  -- domain=16 > MAX_DOMAIN=15
  let overflow : Array UInt64 := #[5000]
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error _ =>
    throw <| IO.userError "base decode unexpectedly failed"
  | .ok decoded =>
    match decodeSchedContextConfigureArgsChecked decoded with
    | .error _ =>
      expect "domain>MAX rejected" true
    | .ok _ =>
      throw <| IO.userError "expected error, got ok"

/-- AK4-G-T05: cspaceMint (5 words): a copy's four inline (the destination
index, the source root, the source index and the word of the depths and the
rights mask), and the badge from overflow slot 0. -/
private def t05_cspace_mint_no_overflow : IO Unit := do
  let syscallId := 4  -- cspaceMint
  let msgLen := 5
  -- destIndex 10, srcRoot 3, srcIndex 20, depths 64/64, rights r|w|g
  let inline : Array UInt64 := #[10, 3, 20, 0x07 * 65536 + 64 * 256 + 64]
  let overflow : Array UInt64 := #[42]                        -- MR[4] = badge=42
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error e =>
    throw <| IO.userError s!"decode failed: {toString e}"
  | .ok decoded =>
    expect "overflowCount=1" (decoded.overflowCount == 1)
    match decodeCSpaceMintArgs decoded with
    | .error e =>
      throw <| IO.userError s!"per-syscall decode failed: {toString e}"
    | .ok args =>
      expect "destIndex=10" (args.destIndex.toNat == 10)
      expect "srcRoot=3" (args.srcRoot.toNat == 3)
      expect "srcIndex=20" (args.srcIndex.toNat == 20)
      expect "depths=64" (args.destDepth == 64 && args.srcDepth == 64)
      expect "rights=7" (args.rights.bits == 7)
      expect "badge=42" (args.badge.toNat == 42)

/-- AK4-G-T06: cspaceMint whose word of the depths and the rights mask sets a
    bit past the mask (bit 21) → rejected. -/
private def t06_cspace_mint_rights_rejected : IO Unit := do
  let syscallId := 4
  let msgLen := 5
  let inline : Array UInt64 := #[10, 3, 20, 0x200000 + 64 * 256 + 64]
  let overflow : Array UInt64 := #[42]
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error _ =>
    throw <| IO.userError "base decode unexpectedly failed"
  | .ok decoded =>
    match decodeCSpaceMintArgs decoded with
    | .error .invalidArgument =>
      expect "stray bit past the mask rejected" true
    | .error e =>
      throw <| IO.userError s!"expected invalidArgument, got {toString e}"
    | .ok _ =>
      throw <| IO.userError "expected error, got ok"

/-- AK4-G-T07: cspaceCopy (4 words, all inline): the destination index, the
source root, the source index and the packed depths. -/
private def t07_cspace_copy_minimal : IO Unit := do
  let syscallId := 5  -- cspaceCopy
  let msgLen := 4
  let inline : Array UInt64 := #[2, 7, 1, 0x0D05]
  let overflow : Array UInt64 := #[]
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error e =>
    throw <| IO.userError s!"decode failed: {toString e}"
  | .ok decoded =>
    expect "overflowCount=0" (decoded.overflowCount == 0)
    match decodeCSpaceCopyArgs decoded with
    | .error e =>
      throw <| IO.userError s!"per-syscall decode failed: {toString e}"
    | .ok args =>
      expect "destIndex=2" (args.destIndex.toNat == 2)
      expect "srcRoot=7" (args.srcRoot.toNat == 7)
      expect "srcIndex=1" (args.srcIndex.toNat == 1)
      expect "destDepth=5" (args.destDepth == 5)
      expect "srcDepth=13" (args.srcDepth == 13)

/-- AK4-G-T08: size invariant — `msgRegs.size = inlineCount + overflowCount`
    across all decoded results. -/
private def t08_size_invariant_across_syscalls : IO Unit := do
  -- Check invariant for 5-arg service_register
  let st1 := buildAbiState 11 5 #[1, 10, 256, 128] #[1]
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st1 tid SeLe4n.arm64DefaultLayout
          (regsOf st1 tid) 32 with
  | .ok d =>
    expect "size-invariant serviceRegister"
      (d.msgRegs.size == d.inlineCount + d.overflowCount)
  | .error _ =>
    throw <| IO.userError "serviceRegister decode failed"
  -- Check invariant for 5-arg cspaceMint
  let st2 := buildAbiState 4 5 #[10, 3, 20, 0x07 * 65536 + 64 * 256 + 64] #[42]
  match decodeSyscallArgsFromState st2 tid SeLe4n.arm64DefaultLayout
          (regsOf st2 tid) 32 with
  | .ok d =>
    expect "size-invariant cspaceMint"
      (d.msgRegs.size == d.inlineCount + d.overflowCount)
  | .error _ =>
    throw <| IO.userError "cspaceMint decode failed"

/-- AK4-G-T09: serviceRegister with `requires_grant = 2` (neither 0 nor 1) →
    rejected with `.invalidMessageInfo` (AK4-B strict boolean parsing on the
    overflow MR[4] slot). Exercises the full state-aware decode + bounds
    validation path end-to-end. -/
private def t09_service_register_grant_strict : IO Unit := do
  let syscallId := 11
  let msgLen := 5
  let inline : Array UInt64 := #[7, 10, 256, 128]
  let overflow : Array UInt64 := #[2]  -- requires_grant=2 → reject
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error _ =>
    throw <| IO.userError "base decode unexpectedly failed"
  | .ok decoded =>
    match decodeServiceRegisterArgs decoded with
    | .error .invalidMessageInfo =>
      expect "requires_grant=2 rejected" true
    | .error e =>
      throw <| IO.userError s!"expected invalidMessageInfo, got {toString e}"
    | .ok _ =>
      throw <| IO.userError "expected error, got ok"

/-- AK4-G-T10: `ipcBufferReadMr` failure when the thread ID lookup fails.
    Uses a `tid` that does not exist in the object store — the helper returns
    `.threadNotFound`, and the decode clamps the 5-arg message to its four
    inline words (`clampToInline`), as seL4 clamps a message with no IPC
    buffer. -/
private def t10_unknown_tid_fails : IO Unit := do
  let syscallId := 11
  let msgLen := 5
  let inline : Array UInt64 := #[7, 10, 256, 128]
  let overflow : Array UInt64 := #[0]
  let st := buildAbiState syscallId msgLen inline overflow
  -- Use a non-existent tid for the decode call
  let bogusTid : SeLe4n.ThreadId := ⟨9999⟩
  match decodeSyscallArgsFromState st bogusTid SeLe4n.arm64DefaultLayout
          (regsOf st ⟨900⟩) 32 with
  | .ok decoded =>
    expect "unknown tid clamped to the inline words"
      (decoded.msgInfo.length == 4 && decoded.overflowCount == 0 &&
        decoded.msgRegs.size == 4)
  | .error e =>
    throw <| IO.userError s!"expected the clamped decode, got {toString e}"

private def runAll : IO Unit := do
  IO.println "=== AbiRoundtripSuite (AK4-G) ==="
  t01_service_register_full_abi
  t02_service_register_bounds_rejected
  t03_sched_context_configure_full_abi
  t04_sc_configure_domain_rejected
  t05_cspace_mint_no_overflow
  t06_cspace_mint_rights_rejected
  t07_cspace_copy_minimal
  t08_size_invariant_across_syscalls
  t09_service_register_grant_strict
  t10_unknown_tid_fails
  IO.println "=== AbiRoundtripSuite PASSED (10 scenarios / 27 assertions) ==="

end SeLe4n.Testing.AbiRoundtripSuite

def main : IO Unit := SeLe4n.Testing.AbiRoundtripSuite.runAll
