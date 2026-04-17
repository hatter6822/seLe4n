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
    to a fresh page with the overflow words written at
    `ipcBufferVA + mrIdx*8`. -/
private def buildAbiState
    (syscallId : Nat) (msgLen : Nat)
    (inlineRegs : Array UInt64) (overflowRegs : Array UInt64)
    : SeLe4n.Model.SystemState :=
  Id.run do
    let tid : SeLe4n.ThreadId := ⟨900⟩
    let cnodeId : SeLe4n.ObjId := ⟨901⟩
    let vsId : SeLe4n.ObjId := ⟨902⟩
    let ipcBufferVA : SeLe4n.VAddr := ⟨0x20_000⟩
    let ipcBufferPA : SeLe4n.PAddr := ⟨0x40_000⟩
    -- Encode each overflow u64 into bytes at the correct physical offset
    let mut mem : SeLe4n.Memory := fun _ => 0
    for i in [:overflowRegs.size] do
      let val := overflowRegs[i]!
      let bytes := encodeLittleEndian val
      for j in [:8] do
        let addr := SeLe4n.PAddr.ofNat (ipcBufferPA.toNat + i * 8 + j)
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
    throw <| IO.userError s!"AK4-G-T01 decode failed: {toString e}"
  | .ok decoded =>
    expect "T01a overflowCount=1" (decoded.overflowCount == 1)
    expect "T01b msgRegs.size=5" (decoded.msgRegs.size == 5)
    -- Now run the per-syscall decoder
    match decodeServiceRegisterArgs decoded with
    | .error e =>
      throw <| IO.userError s!"T01 per-syscall decode failed: {toString e}"
    | .ok args =>
      expect "T01c interfaceId=7" (args.interfaceId.toNat == 7)
      expect "T01d methodCount=10" (args.methodCount == 10)
      expect "T01e maxMessageSize=256" (args.maxMessageSize == 256)
      expect "T01f maxResponseSize=128" (args.maxResponseSize == 128)
      expect "T01g requiresGrant=true" args.requiresGrant

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
    throw <| IO.userError "T02 base decode unexpectedly failed"
  | .ok decoded =>
    match decodeServiceRegisterArgs decoded with
    | .error .invalidArgument =>
      expect "T02a methodCount>MAX rejected" true
    | .error e =>
      throw <| IO.userError s!"T02 expected invalidArgument, got {toString e}"
    | .ok _ =>
      throw <| IO.userError "T02 expected error, got ok"

/-- AK4-G-T03: schedContextConfigure with 5 args — inline + 1 overflow. -/
private def t03_sched_context_configure_full_abi : IO Unit := do
  let syscallId := 17  -- schedContextConfigure
  let msgLen := 5
  let inline : Array UInt64 := #[1000, 10000, 128, 5000]     -- x2..x5
  let overflow : Array UInt64 := #[3]                         -- MR[4] = domain=3
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error e =>
    throw <| IO.userError s!"AK4-G-T03 decode failed: {toString e}"
  | .ok decoded =>
    expect "T03a overflowCount=1" (decoded.overflowCount == 1)
    match decodeSchedContextConfigureArgs decoded with
    | .error e =>
      throw <| IO.userError s!"T03 per-syscall decode failed: {toString e}"
    | .ok args =>
      expect "T03b budget=1000" (args.budget == 1000)
      expect "T03c period=10000" (args.period == 10000)
      expect "T03d priority=128" (args.priority == 128)
      expect "T03e deadline=5000" (args.deadline == 5000)
      expect "T03f domain=3" (args.domain == 3)

/-- AK4-G-T04: schedContextConfigure with domain > MAX → rejected.
    AK3-J / AK4-D tightened validation. -/
private def t04_sc_configure_domain_rejected : IO Unit := do
  let syscallId := 17
  let msgLen := 5
  let inline : Array UInt64 := #[1000, 10000, 128, 5000]
  let overflow : Array UInt64 := #[16]  -- domain=16 > MAX_DOMAIN=15
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error _ =>
    throw <| IO.userError "T04 base decode unexpectedly failed"
  | .ok decoded =>
    match decodeSchedContextConfigureArgsChecked decoded with
    | .error _ =>
      expect "T04a domain>MAX rejected" true
    | .ok _ =>
      throw <| IO.userError "T04 expected error, got ok"

/-- AK4-G-T05: cspaceMint (4-arg) — inline regs only, no overflow. -/
private def t05_cspace_mint_no_overflow : IO Unit := do
  let syscallId := 4  -- cspaceMint
  let msgLen := 4
  let inline : Array UInt64 := #[10, 20, 0x07, 42]  -- srcSlot, dstSlot, rights=r|w|g, badge=42
  let overflow : Array UInt64 := #[]
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error e =>
    throw <| IO.userError s!"AK4-G-T05 decode failed: {toString e}"
  | .ok decoded =>
    expect "T05a overflowCount=0" (decoded.overflowCount == 0)
    match decodeCSpaceMintArgs decoded with
    | .error e =>
      throw <| IO.userError s!"T05 per-syscall decode failed: {toString e}"
    | .ok args =>
      expect "T05b srcSlot=10" (args.srcSlot.toNat == 10)
      expect "T05c dstSlot=20" (args.dstSlot.toNat == 20)
      expect "T05d badge=42" (args.badge.toNat == 42)

/-- AK4-G-T06: cspaceMint with rights > 0x1F → rejected.
    AK4-E tightened validation. -/
private def t06_cspace_mint_rights_rejected : IO Unit := do
  let syscallId := 4
  let msgLen := 4
  let inline : Array UInt64 := #[10, 20, 0x20, 42]  -- rights=0x20 > 0x1F
  let overflow : Array UInt64 := #[]
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error _ =>
    throw <| IO.userError "T06 base decode unexpectedly failed"
  | .ok decoded =>
    match decodeCSpaceMintArgs decoded with
    | .error .invalidArgument =>
      expect "T06a rights>0x1F rejected" true
    | .error e =>
      throw <| IO.userError s!"T06 expected invalidArgument, got {toString e}"
    | .ok _ =>
      throw <| IO.userError "T06 expected error, got ok"

/-- AK4-G-T07: cspaceCopy (2-arg) — shortest inline path. -/
private def t07_cspace_copy_minimal : IO Unit := do
  let syscallId := 5  -- cspaceCopy
  let msgLen := 2
  let inline : Array UInt64 := #[1, 2]
  let overflow : Array UInt64 := #[]
  let st := buildAbiState syscallId msgLen inline overflow
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
          (regsOf st tid) 32 with
  | .error e =>
    throw <| IO.userError s!"AK4-G-T07 decode failed: {toString e}"
  | .ok decoded =>
    expect "T07a overflowCount=0" (decoded.overflowCount == 0)
    match decodeCSpaceCopyArgs decoded with
    | .error e =>
      throw <| IO.userError s!"T07 per-syscall decode failed: {toString e}"
    | .ok args =>
      expect "T07b srcSlot=1" (args.srcSlot.toNat == 1)
      expect "T07c dstSlot=2" (args.dstSlot.toNat == 2)

/-- AK4-G-T08: size invariant — `msgRegs.size = inlineCount + overflowCount`
    across all decoded results. -/
private def t08_size_invariant_across_syscalls : IO Unit := do
  -- Check invariant for 5-arg service_register
  let st1 := buildAbiState 11 5 #[1, 10, 256, 128] #[1]
  let tid : SeLe4n.ThreadId := ⟨900⟩
  match decodeSyscallArgsFromState st1 tid SeLe4n.arm64DefaultLayout
          (regsOf st1 tid) 32 with
  | .ok d =>
    expect "T08a size-invariant serviceRegister"
      (d.msgRegs.size == d.inlineCount + d.overflowCount)
  | .error _ =>
    throw <| IO.userError "T08 serviceRegister decode failed"
  -- Check invariant for 4-arg cspaceMint
  let st2 := buildAbiState 4 4 #[10, 20, 0x07, 42] #[]
  match decodeSyscallArgsFromState st2 tid SeLe4n.arm64DefaultLayout
          (regsOf st2 tid) 32 with
  | .ok d =>
    expect "T08b size-invariant cspaceMint"
      (d.msgRegs.size == d.inlineCount + d.overflowCount)
  | .error _ =>
    throw <| IO.userError "T08 cspaceMint decode failed"

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
  IO.println "=== AbiRoundtripSuite PASSED (8 scenarios) ==="

end SeLe4n.Testing.AbiRoundtripSuite

def main : IO Unit := SeLe4n.Testing.AbiRoundtripSuite.runAll
