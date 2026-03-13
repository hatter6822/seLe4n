/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Testing.StateBuilder
import SeLe4n.Testing.InvariantChecks

set_option maxRecDepth 1024

open SeLe4n.Model

namespace SeLe4n.Testing

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"operation-chain check passed [{label}]"
  else
    throw <| IO.userError s!"operation-chain check failed [{label}]"

private def expectOkState
    (label : String)
    (actual : Except KernelError (α × SystemState)) : IO (α × SystemState) :=
  match actual with
  | .ok result => do
      IO.println s!"operation-chain transition passed [{label}]"
      pure result
  | .error err =>
      throw <| IO.userError s!"{label}: expected success, got {reprStr err}"

private def expectError
    (label : String)
    (actual : Except KernelError α)
    (expected : KernelError) : IO Unit :=
  match actual with
  | .error err =>
      if err = expected then
        IO.println s!"operation-chain error check passed [{label}]"
      else
        throw <| IO.userError s!"{label}: expected {reprStr expected}, got {reprStr err}"
  | .ok _ =>
      throw <| IO.userError s!"{label}: expected error {reprStr expected}, got success"

private def assertInvariants (label : String) (st : SystemState) : IO Unit :=
  assertStateInvariantsFor label st.objectIndex st

private def alwaysAllowServicePolicy : SeLe4n.Kernel.ServicePolicy := fun _ => true

private def buildSchedulerTopology
    (threadCount : Nat) (priority : Nat) (domains : Nat := 1) : SystemState :=
  let threads : List (SeLe4n.ObjId × KernelObject) :=
    (List.range threadCount).map fun i =>
      let dom := if domains = 0 then 0 else i % domains
      (⟨1000 + i⟩, .tcb {
        tid := ⟨1000 + i⟩
        priority := ⟨priority⟩
        deadline := ⟨i + 1⟩
        domain := ⟨dom⟩
        cspaceRoot := ⟨2000⟩
        vspaceRoot := ⟨3000⟩
        ipcBuffer := ⟨4096 + i * 4096⟩
        ipcState := .ready
      })
  let runnable : List SeLe4n.ThreadId := (List.range threadCount).map fun i => ⟨1000 + i⟩
  let builder := BootstrapBuilder.empty
    |>.withObject ⟨2000⟩ (.cnode { depth := 0, guardWidth := 0, guardValue := 0, radixWidth := 0, slots := {} })
    |>.withObject ⟨3000⟩ (.vspaceRoot { asid := ⟨1⟩, mappings := {} })
    |>.withRunnable runnable
  let builder := threads.foldl (fun b (oid, obj) => b.withObject oid obj) builder
  let st := builder.build
  if domains > 1 then
    { st with scheduler := { st.scheduler with activeDomain := ⟨0⟩ } }
  else
    st

private partial def scheduleNTimes
    (steps : Nat)
    (st : SystemState)
    (assertEvery : Nat := 0)
    (labelPrefix : String := "scheduler") : IO SystemState := do
  let rec loop (i : Nat) (cur : SystemState) : IO SystemState := do
    if i = steps then
      pure cur
    else
      let (_, cur') ← expectOkState s!"{labelPrefix}: schedule step {i}"
        (SeLe4n.Kernel.schedule cur)
      if assertEvery > 0 && i % assertEvery = 0 then
        assertInvariants s!"{labelPrefix}: invariants step {i}" cur'
      loop (i + 1) cur'
  loop 0 st

private def runRetypeMintRevokeChain : IO Unit := do
  let untypedId : SeLe4n.ObjId := ⟨40⟩
  let childId : SeLe4n.ObjId := ⟨41⟩
  let cnodeId : SeLe4n.ObjId := ⟨42⟩
  let authSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨0⟩ }
  let dstSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨1⟩ }
  let seed := BootstrapBuilder.empty
    |>.withObject untypedId (.untyped {
      regionBase := ⟨0x1000⟩
      regionSize := 4096
      watermark := 0
      children := []
      isDevice := false
    })
    |>.withObject cnodeId (.cnode {
      depth := 0
      guardWidth := 0
      guardValue := 0
      radixWidth := 0
      slots := Std.HashMap.ofList [
        (⟨0⟩, { target := .object untypedId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
      ]
    })
    |>.withLifecycleObjectType untypedId .untyped
    |>.withLifecycleObjectType cnodeId .cnode
    |>.withLifecycleCapabilityRef authSlot (.object untypedId)
    |>.build
  let (_, st1) ← expectOkState "chain1: retype from untyped"
    (SeLe4n.Kernel.retypeFromUntyped authSlot untypedId childId (.endpoint {}) 64 seed)
  let (_, st2) ← expectOkState "chain1: mint from retype result"
    (SeLe4n.Kernel.cspaceMintWithCdt authSlot dstSlot (AccessRightSet.ofList [.read]) none st1)
  let (report, st3) ← expectOkState "chain1: revoke minted subtree"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict authSlot st2)
  expect "chain1: strict revoke records deleted descendant"
    (report.deletedSlots = [dstSlot])
  assertInvariants "chain1: retype→mint→revoke" st3

private def runSendSendReceiveChain : IO Unit := do
  let epId : SeLe4n.ObjId := ⟨60⟩
  let msg1 : IpcMessage := { registers := #[1], caps := #[], badge := none }
  let msg2 : IpcMessage := { registers := #[2], caps := #[], badge := none }
  let seed :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject ⟨1⟩ (.tcb { tid := ⟨1⟩, priority := ⟨10⟩, domain := ⟨0⟩, cspaceRoot := ⟨2000⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨4096⟩, ipcState := .ready })
      |>.withObject ⟨2⟩ (.tcb { tid := ⟨2⟩, priority := ⟨10⟩, domain := ⟨0⟩, cspaceRoot := ⟨2000⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨8192⟩, ipcState := .ready })
      |>.withObject ⟨3⟩ (.tcb { tid := ⟨3⟩, priority := ⟨10⟩, domain := ⟨0⟩, cspaceRoot := ⟨2000⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨12288⟩, ipcState := .ready })
      |>.build)
  let (_, st1) ← expectOkState "chain2: send msg1"
    (SeLe4n.Kernel.endpointSendDual epId (SeLe4n.ThreadId.ofNat 1) msg1 seed)
  let (_, st2) ← expectOkState "chain2: send msg2"
    (SeLe4n.Kernel.endpointSendDual epId (SeLe4n.ThreadId.ofNat 2) msg2 st1)
  let (sender, st3) ← expectOkState "chain2: receive FIFO head"
    (SeLe4n.Kernel.endpointReceiveDual epId (SeLe4n.ThreadId.ofNat 3) st2)
  expect "chain2: first receive from sender tid=1" (sender = SeLe4n.ThreadId.ofNat 1)
  assertInvariants "chain2: send→send→receive" st3

private def runMapLookupUnmapLookupChain : IO Unit := do
  let asid : SeLe4n.ASID := ⟨2⟩
  let vaddr : SeLe4n.VAddr := ⟨0x4000⟩
  let paddr : SeLe4n.PAddr := ⟨0x9000⟩
  let seed := (BootstrapBuilder.empty |>.withObject ⟨70⟩ (.vspaceRoot { asid := asid, mappings := {} }) |>.build)
  let (_, st1) ← expectOkState "chain3: map page"
    ((SeLe4n.Kernel.Architecture.vspaceMapPage asid vaddr paddr) seed)
  let (pa, st2) ← expectOkState "chain3: lookup after map"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid vaddr st1)
  expect "chain3: lookup returns mapped paddr" (pa = paddr)
  let (_, st3) ← expectOkState "chain3: unmap page"
    ((SeLe4n.Kernel.Architecture.vspaceUnmapPage asid vaddr) st2)
  expectError "chain3: lookup after unmap"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid vaddr st3) .translationFault
  assertInvariants "chain3: map→lookup→unmap→lookup" st3

private def runServiceStartStopChain : IO Unit := do
  let baseSvc : ServiceId := ⟨80⟩
  let depSvc : ServiceId := ⟨81⟩
  let seed := BootstrapBuilder.empty
    |>.withObject ⟨80⟩ (.endpoint {})
    |>.withObject ⟨81⟩ (.endpoint {})
    |>.withService baseSvc {
      identity := { sid := baseSvc, backingObject := ⟨80⟩, owner := ⟨1⟩ }
      status := .stopped
      dependencies := []
      isolatedFrom := []
    }
    |>.withService depSvc {
      identity := { sid := depSvc, backingObject := ⟨81⟩, owner := ⟨1⟩ }
      status := .stopped
      dependencies := [baseSvc]
      isolatedFrom := []
    }
    |>.build
  let (_, st1) ← expectOkState "chain4: start base service"
    (SeLe4n.Kernel.serviceStart baseSvc alwaysAllowServicePolicy seed)
  let (_, st2) ← expectOkState "chain4: start dependent"
    (SeLe4n.Kernel.serviceStart depSvc alwaysAllowServicePolicy st1)
  let (_, st3) ← expectOkState "chain4: stop base service"
    (SeLe4n.Kernel.serviceStop baseSvc alwaysAllowServicePolicy st2)
  match st3.services[depSvc]? with
  | some entry => expect "chain4: dependent remains running" (entry.status = ServiceStatus.running)
  | none => throw <| IO.userError "chain4: dependent service disappeared"
  expectError "chain4: restart dependent denied while base stopped"
    (SeLe4n.Kernel.serviceRestart depSvc alwaysAllowServicePolicy alwaysAllowServicePolicy st3)
    .dependencyViolation

private def runCopyMoveDeleteChain : IO Unit := do
  let epId : SeLe4n.ObjId := ⟨90⟩
  let cnodeId : SeLe4n.ObjId := ⟨91⟩
  let src : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨0⟩ }
  let copyDst : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨1⟩ }
  let moveDst : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨2⟩ }
  let seed := BootstrapBuilder.empty
    |>.withObject epId (.endpoint {})
    |>.withObject cnodeId (.cnode {
      depth := 0
      guardWidth := 0
      guardValue := 0
      radixWidth := 0
      slots := Std.HashMap.ofList [
        (src.slot, { target := .object epId, rights := AccessRightSet.ofList [.read, .write], badge := none })
      ]
    })
    |>.withLifecycleObjectType epId .endpoint
    |>.withLifecycleObjectType cnodeId .cnode
    |>.withLifecycleCapabilityRef src (.object epId)
    |>.build
  let (_, st1) ← expectOkState "chain5: copy cap"
    (SeLe4n.Kernel.cspaceCopy src copyDst seed)
  let (_, st2) ← expectOkState "chain5: move copied cap"
    (SeLe4n.Kernel.cspaceMove copyDst moveDst st1)
  let (_, st3) ← expectOkState "chain5: delete moved cap"
    (SeLe4n.Kernel.cspaceDeleteSlot moveDst st2)
  expectError "chain5: moved slot deleted"
    (SeLe4n.Kernel.cspaceLookupSlot moveDst st3) .invalidCapability
  assertInvariants "chain5: copy→move→delete" st3

private def runNotificationSignalWaitChain : IO Unit := do
  let ntfnId : SeLe4n.ObjId := ⟨100⟩
  let seed := BootstrapBuilder.empty
    |>.withObject ntfnId (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
    |>.withObject ⟨1⟩ (.tcb { tid := ⟨1⟩, priority := ⟨10⟩, domain := ⟨0⟩, cspaceRoot := ⟨2000⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨4096⟩, ipcState := .ready })
    |>.build
  let (_, st1) ← expectOkState "chain6: signal badge 0x01"
    (SeLe4n.Kernel.notificationSignal ntfnId (SeLe4n.Badge.ofNat 0x01) seed)
  let (_, st2) ← expectOkState "chain6: signal badge 0x10"
    (SeLe4n.Kernel.notificationSignal ntfnId (SeLe4n.Badge.ofNat 0x10) st1)
  let (badge?, st3) ← expectOkState "chain6: wait consumes accumulated badge"
    (SeLe4n.Kernel.notificationWait ntfnId ⟨1⟩ st2)
  match badge? with
  | some badge =>
      expect "chain6: badge accumulates by OR" (badge = SeLe4n.Badge.ofNat 0x11)
  | none => throw <| IO.userError "chain6: expected accumulated badge"
  assertInvariants "chain6: signal→signal→wait" st3

private def runSchedulerStress : IO Unit := do
  let st16 := buildSchedulerTopology 16 100
  let final16 ← scheduleNTimes 50 st16 (assertEvery := 10) (labelPrefix := "stress16")
  assertInvariants "scheduler-stress-16" final16

  let stSamePrio := buildSchedulerTopology 8 100
  let (_, stFirst) ← expectOkState "same-priority first schedule" (SeLe4n.Kernel.schedule stSamePrio)
  let expectedCurrent := stFirst.scheduler.current
  let rec checkSame (n : Nat) : IO Unit := do
    if n = 0 then
      pure ()
    else
      let (_, stN) ← expectOkState s!"same-priority replay {n}" (SeLe4n.Kernel.schedule stSamePrio)
      expect s!"same-priority deterministic current choice replay {n}"
        (stN.scheduler.current = expectedCurrent)
      checkSame (n - 1)
  checkSame 20

  let stMultiDomain := buildSchedulerTopology 16 50 (domains := 4)
  let step1 ← scheduleNTimes 4 stMultiDomain (labelPrefix := "domain0")
  expect "multi-domain schedule keeps selected thread in active domain"
    (match step1.scheduler.current with
      | some tid =>
          match step1.objects[tid.toObjId]? with
          | some (.tcb tcb) => tcb.domain = step1.scheduler.activeDomain
          | _ => false
      | none => false)

private def runOperationChainChecks : IO Unit := do
  runRetypeMintRevokeChain
  runSendSendReceiveChain
  runMapLookupUnmapLookupChain
  runServiceStartStopChain
  runCopyMoveDeleteChain
  runNotificationSignalWaitChain
  runSchedulerStress

end SeLe4n.Testing

def main : IO Unit :=
  SeLe4n.Testing.runOperationChainChecks
