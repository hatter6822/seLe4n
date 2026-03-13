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
      IO.println s!"operation-chain check passed [{label}]"
      pure result
  | .error err =>
      throw <| IO.userError s!"{label}: expected success, got {reprStr err}"

private def runKernelState
    (label : String)
    (actual : Except KernelError (Unit × SystemState)) : IO SystemState :=
  match actual with
  | .ok (_, st) =>
      pure st
  | .error err =>
      throw <| IO.userError s!"{label}: expected success, got {reprStr err}"

private def expectError
    (label : String)
    (actual : Except KernelError α)
    (expected : KernelError) : IO Unit :=
  match actual with
  | .ok _ => throw <| IO.userError s!"{label}: expected {reprStr expected}, got success"
  | .error err =>
      if err = expected then
        IO.println s!"operation-chain check passed [{label}]"
      else
        throw <| IO.userError s!"{label}: expected {reprStr expected}, got {reprStr err}"

private def allowAll : SeLe4n.Kernel.ServicePolicy := fun _ => true

private def assertInvariants (label : String) (st : SystemState) : IO Unit :=
  assertStateInvariantsFor label st.objectIndex st

private def chain1RetypeMintRevoke : IO Unit := do
  let targetId : SeLe4n.ObjId := ⟨200⟩
  let cnodeId : SeLe4n.ObjId := ⟨201⟩
  let authSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨0⟩ }
  let dstSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨1⟩ }
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject targetId (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
      |>.withObject cnodeId (.cnode {
          depth := 0
          guardWidth := 0
          guardValue := 0
          radixWidth := 1
          slots := Std.HashMap.ofList [
            (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
          ]
        })
      |>.withLifecycleObjectType targetId .notification
      |>.withLifecycleObjectType cnodeId .cnode
      |>.withLifecycleCapabilityRef authSlot (.object targetId)
      |>.build)

  let (_, st1) ← expectOkState "chain1: lifecycleRetypeObject"
    (SeLe4n.Kernel.lifecycleRetypeObject authSlot targetId (.endpoint {}) st0)
  let (_, st2) ← expectOkState "chain1: cspaceMint"
    (SeLe4n.Kernel.cspaceMint authSlot dstSlot (AccessRightSet.ofList [.read]) none st1)
  let (_, st3) ← expectOkState "chain1: cspaceRevokeCdtStrict"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict dstSlot st2)
  assertInvariants "chain1: retype→mint→revoke" st3

private def chain2SendSendReceiveFifo : IO Unit := do
  let epId : SeLe4n.ObjId := ⟨210⟩
  let tid1 : SeLe4n.ThreadId := ⟨1⟩
  let tid2 : SeLe4n.ThreadId := ⟨2⟩
  let tid3 : SeLe4n.ThreadId := ⟨3⟩
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject tid1.toObjId (.tcb { tid := tid1, priority := ⟨40⟩, domain := ⟨0⟩, cspaceRoot := ⟨300⟩, vspaceRoot := ⟨310⟩, ipcBuffer := ⟨4096⟩, ipcState := .ready })
      |>.withObject tid2.toObjId (.tcb { tid := tid2, priority := ⟨39⟩, domain := ⟨0⟩, cspaceRoot := ⟨300⟩, vspaceRoot := ⟨310⟩, ipcBuffer := ⟨8192⟩, ipcState := .ready })
      |>.withObject tid3.toObjId (.tcb { tid := tid3, priority := ⟨38⟩, domain := ⟨0⟩, cspaceRoot := ⟨300⟩, vspaceRoot := ⟨310⟩, ipcBuffer := ⟨12288⟩, ipcState := .ready })
      |>.withRunnable [tid1, tid2, tid3]
      |>.build)
  let msg1 : IpcMessage := .empty
  let msg2 : IpcMessage := .empty
  let (_, st1) ← expectOkState "chain2: send msg1" (SeLe4n.Kernel.endpointSendDual epId tid1 msg1 st0)
  let (_, st2) ← expectOkState "chain2: send msg2" (SeLe4n.Kernel.endpointSendDual epId tid2 msg2 st1)
  let (sender, st3) ← expectOkState "chain2: receive" (SeLe4n.Kernel.endpointReceiveDual epId tid3 st2)
  expect "chain2: FIFO sender order" (sender = tid1)
  assertInvariants "chain2: send→send→receive" st3

private def chain3MapLookupUnmapLookup : IO Unit := do
  let asid : SeLe4n.ASID := ⟨2⟩
  let vaddr : SeLe4n.VAddr := ⟨4096⟩
  let paddr : SeLe4n.PAddr := ⟨12288⟩
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject ⟨220⟩ (.vspaceRoot { asid := asid, mappings := {} })
      |>.build)
  let (_, st1) ← expectOkState "chain3: map page"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asid vaddr paddr default st0)
  let (resolved, _) ← expectOkState "chain3: lookup after map"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid vaddr st1)
  expect "chain3: map/lookup roundtrip" (resolved = paddr)
  let (_, st2) ← expectOkState "chain3: unmap page"
    (SeLe4n.Kernel.Architecture.vspaceUnmapPage asid vaddr st1)
  assertInvariants "chain3: map→lookup→unmap" st2
  expectError "chain3: lookup after unmap"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid vaddr st2) .translationFault

private def chain4ServiceStartDependentStop : IO Unit := do
  let baseSid : ServiceId := ⟨230⟩
  let depSid : ServiceId := ⟨231⟩
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject ⟨500⟩ (.endpoint {})
      |>.withObject ⟨501⟩ (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
      |>.withService baseSid {
          identity := { sid := baseSid, backingObject := ⟨500⟩, owner := ⟨1⟩ }
          status := .stopped
          dependencies := []
          isolatedFrom := [] }
      |>.withService depSid {
          identity := { sid := depSid, backingObject := ⟨501⟩, owner := ⟨1⟩ }
          status := .stopped
          dependencies := [baseSid]
          isolatedFrom := [] }
      |>.build)
  let (_, st1) ← expectOkState "chain4: start base" (SeLe4n.Kernel.serviceStart baseSid allowAll st0)
  let (_, st2) ← expectOkState "chain4: start dependent" (SeLe4n.Kernel.serviceStart depSid allowAll st1)
  let (_, st3) ← expectOkState "chain4: stop base" (SeLe4n.Kernel.serviceStop baseSid allowAll st2)
  let depStatus := (st3.services[depSid]?).map ServiceGraphEntry.status
  expect "chain4: dependent remains running" (depStatus = some .running)
  expectError "chain4: restarting dependent while base stopped fails"
    (SeLe4n.Kernel.serviceRestart depSid allowAll allowAll st3) .dependencyViolation

private def chain5CopyMoveDelete : IO Unit := do
  let cnodeId : SeLe4n.ObjId := ⟨240⟩
  let target : SeLe4n.ObjId := ⟨241⟩
  let src : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨0⟩ }
  let copyDst : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨1⟩ }
  let moveDst : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨2⟩ }
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject target (.endpoint {})
      |>.withObject cnodeId (.cnode {
          depth := 0
          guardWidth := 0
          guardValue := 0
          radixWidth := 2
          slots := Std.HashMap.ofList [
            (⟨0⟩, { target := .object target, rights := AccessRightSet.ofList [.read, .write], badge := none })
          ]
        })
      |>.withLifecycleObjectType target .endpoint
      |>.withLifecycleObjectType cnodeId .cnode
      |>.build)
  let (_, st1) ← expectOkState "chain5: copy cap" (SeLe4n.Kernel.cspaceCopy src copyDst st0)
  let (_, st2) ← expectOkState "chain5: move copied cap" (SeLe4n.Kernel.cspaceMove copyDst moveDst st1)
  let (_, st3) ← expectOkState "chain5: delete moved cap" (SeLe4n.Kernel.cspaceDeleteSlot moveDst st2)
  assertInvariants "chain5: copy→move→delete" st3

private def chain6NotificationBadgeAccumulation : IO Unit := do
  let ntfnId : SeLe4n.ObjId := ⟨250⟩
  let waiter : SeLe4n.ThreadId := ⟨11⟩
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject ntfnId (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
      |>.withObject waiter.toObjId (.tcb {
          tid := waiter
          priority := ⟨20⟩
          domain := ⟨0⟩
          cspaceRoot := ⟨300⟩
          vspaceRoot := ⟨310⟩
          ipcBuffer := ⟨4096⟩
          ipcState := .ready
        })
      |>.withRunnable [waiter]
      |>.build)
  let (_, st1) ← expectOkState "chain6: signal badge 0x01"
    (SeLe4n.Kernel.notificationSignal ntfnId (SeLe4n.Badge.ofNat 0x01) st0)
  let (_, st2) ← expectOkState "chain6: signal badge 0x10"
    (SeLe4n.Kernel.notificationSignal ntfnId (SeLe4n.Badge.ofNat 0x10) st1)
  let (received, st3) ← expectOkState "chain6: wait"
    (SeLe4n.Kernel.notificationWait ntfnId waiter st2)
  expect "chain6: badge accumulation is bitwise OR"
    (received = some (SeLe4n.Badge.ofNat 0x11))
  assertInvariants "chain6: signal→signal→wait" st3

private def wsI4VspaceMultiAsidSharing : IO Unit := do
  let asid1 : SeLe4n.ASID := ⟨1⟩
  let asid2 : SeLe4n.ASID := ⟨2⟩
  let sharedPaddr : SeLe4n.PAddr := ⟨0x1000⟩
  let vaddr1 : SeLe4n.VAddr := ⟨0x2000⟩
  let vaddr2 : SeLe4n.VAddr := ⟨0x3000⟩
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject ⟨270⟩ (.vspaceRoot { asid := asid1, mappings := {} })
      |>.withObject ⟨271⟩ (.vspaceRoot { asid := asid2, mappings := {} })
      |>.build)

  let (_, st1) ← expectOkState "ws-i4 vspace: map shared page ASID1"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asid1 vaddr1 sharedPaddr default st0)
  let (_, st2) ← expectOkState "ws-i4 vspace: map shared page ASID2"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asid2 vaddr2 sharedPaddr default st1)
  let (lookupAsid1, st3) ← expectOkState "ws-i4 vspace: lookup ASID1 shared mapping"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid1 vaddr1 st2)
  let (lookupAsid2, st4) ← expectOkState "ws-i4 vspace: lookup ASID2 shared mapping"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid2 vaddr2 st3)
  expect "ws-i4 vspace: shared paddr visible in ASID1" (lookupAsid1 = sharedPaddr)
  expect "ws-i4 vspace: shared paddr visible in ASID2" (lookupAsid2 = sharedPaddr)

  let (_, st5) ← expectOkState "ws-i4 vspace: unmap ASID1 only"
    (SeLe4n.Kernel.Architecture.vspaceUnmapPage asid1 vaddr1 st4)
  expectError "ws-i4 vspace: ASID1 unmapped lookup faults"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid1 vaddr1 st5) .translationFault
  let (stillMappedAsid2, st6) ← expectOkState "ws-i4 vspace: ASID2 remains mapped"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid2 vaddr2 st5)
  expect "ws-i4 vspace: ASID2 mapping survives ASID1 unmap" (stillMappedAsid2 = sharedPaddr)

  let readOnly : PagePermissions := { read := true, write := false, execute := false, user := false, cacheable := true }
  let readWrite : PagePermissions := { read := true, write := true, execute := false, user := false, cacheable := true }
  let (_, st7) ← expectOkState "ws-i4 vspace: map read-only in ASID1"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asid1 vaddr1 sharedPaddr readOnly st6)
  let (_, st8) ← expectOkState "ws-i4 vspace: map read-write in ASID2"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asid2 ⟨0x3100⟩ sharedPaddr readWrite st7)
  let ((_, permsAsid1), st9) ← expectOkState "ws-i4 vspace: lookupFull ASID1 perms"
    (SeLe4n.Kernel.Architecture.vspaceLookupFull asid1 vaddr1 st8)
  let ((_, permsAsid2), st10) ← expectOkState "ws-i4 vspace: lookupFull ASID2 perms"
    (SeLe4n.Kernel.Architecture.vspaceLookupFull asid2 ⟨0x3100⟩ st9)
  expect "ws-i4 vspace: ASID1 keeps read-only permissions" (permsAsid1 = readOnly)
  expect "ws-i4 vspace: ASID2 keeps read-write permissions" (permsAsid2 = readWrite)
  expect "ws-i4 vspace: ASID1 mapping remains W^X compliant" permsAsid1.wxCompliant
  expect "ws-i4 vspace: ASID2 mapping remains W^X compliant" permsAsid2.wxCompliant
  assertInvariants "ws-i4 vspace: multi-asid sharing" st10

private def wsI4IpcInterleavedSends : IO Unit := do
  let epId : SeLe4n.ObjId := ⟨280⟩
  let senderA : SeLe4n.ThreadId := ⟨2801⟩
  let senderB : SeLe4n.ThreadId := ⟨2802⟩
  let senderC : SeLe4n.ThreadId := ⟨2803⟩
  let receiver : SeLe4n.ThreadId := ⟨2804⟩
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject senderA.toObjId (.tcb { tid := senderA, priority := ⟨50⟩, domain := ⟨0⟩, cspaceRoot := ⟨3800⟩, vspaceRoot := ⟨3900⟩, ipcBuffer := ⟨0x1000⟩, ipcState := .ready })
      |>.withObject senderB.toObjId (.tcb { tid := senderB, priority := ⟨49⟩, domain := ⟨0⟩, cspaceRoot := ⟨3800⟩, vspaceRoot := ⟨3900⟩, ipcBuffer := ⟨0x2000⟩, ipcState := .ready })
      |>.withObject senderC.toObjId (.tcb { tid := senderC, priority := ⟨48⟩, domain := ⟨0⟩, cspaceRoot := ⟨3800⟩, vspaceRoot := ⟨3900⟩, ipcBuffer := ⟨0x3000⟩, ipcState := .ready })
      |>.withObject receiver.toObjId (.tcb { tid := receiver, priority := ⟨47⟩, domain := ⟨0⟩, cspaceRoot := ⟨3800⟩, vspaceRoot := ⟨3900⟩, ipcBuffer := ⟨0x4000⟩, ipcState := .ready })
      |>.withRunnable [senderA, senderB, senderC, receiver]
      |>.build)

  let (_, st1) ← expectOkState "ws-i4 ipc: sender A enqueues"
    (SeLe4n.Kernel.endpointSendDual epId senderA .empty st0)
  let (_, st2) ← expectOkState "ws-i4 ipc: sender B enqueues"
    (SeLe4n.Kernel.endpointSendDual epId senderB .empty st1)
  let (_, st3) ← expectOkState "ws-i4 ipc: sender C enqueues"
    (SeLe4n.Kernel.endpointSendDual epId senderC .empty st2)
  let (firstSender, st4) ← expectOkState "ws-i4 ipc: first receive"
    (SeLe4n.Kernel.endpointReceiveDual epId receiver st3)
  let (secondSender, st5) ← expectOkState "ws-i4 ipc: second receive"
    (SeLe4n.Kernel.endpointReceiveDual epId receiver st4)
  let (thirdSender, st6) ← expectOkState "ws-i4 ipc: third receive"
    (SeLe4n.Kernel.endpointReceiveDual epId receiver st5)
  expect "ws-i4 ipc: FIFO first sender" (firstSender = senderA)
  expect "ws-i4 ipc: FIFO second sender" (secondSender = senderB)
  expect "ws-i4 ipc: FIFO third sender" (thirdSender = senderC)

  let (_, st7) ← expectOkState "ws-i4 ipc: interleaved send A"
    (SeLe4n.Kernel.endpointSendDual epId senderA .empty st6)
  let (senderAfterA, st8) ← expectOkState "ws-i4 ipc: interleaved receive after A"
    (SeLe4n.Kernel.endpointReceiveDual epId receiver st7)
  expect "ws-i4 ipc: interleaved receive returns A" (senderAfterA = senderA)
  let (_, st9) ← expectOkState "ws-i4 ipc: interleaved send B"
    (SeLe4n.Kernel.endpointSendDual epId senderB .empty st8)
  let (senderAfterB, st10) ← expectOkState "ws-i4 ipc: interleaved receive after B"
    (SeLe4n.Kernel.endpointReceiveDual epId receiver st9)
  expect "ws-i4 ipc: interleaved receive returns B" (senderAfterB = senderB)
  assertInvariants "ws-i4 ipc: interleaved send/receive" st10

private def wsI4LifecycleTransactionChains : IO Unit := do
  let cnodeId : SeLe4n.ObjId := ⟨290⟩
  let endpointId : SeLe4n.ObjId := ⟨291⟩
  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨0⟩ }
  let childSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨1⟩ }
  let grandchildSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨2⟩ }
  let extraSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := ⟨3⟩ }
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject endpointId (.endpoint {})
      |>.withObject cnodeId (.cnode {
          depth := 0
          guardWidth := 0
          guardValue := 0
          radixWidth := 4
          slots := Std.HashMap.ofList [
            (⟨0⟩, { target := .object endpointId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
          ]
        })
      |>.build)

  let (_, st1) ← expectOkState "ws-i4 lifecycle: mint root→child (attenuate grant)"
    (SeLe4n.Kernel.cspaceMintWithCdt rootSlot childSlot (AccessRightSet.ofList [.read, .write]) none st0)
  let (_, st2) ← expectOkState "ws-i4 lifecycle: mint child→grandchild (read-only)"
    (SeLe4n.Kernel.cspaceMintWithCdt childSlot grandchildSlot (AccessRightSet.ofList [.read]) none st1)
  let grandchildCap := SeLe4n.Model.SystemState.lookupSlotCap st2 grandchildSlot
  expect "ws-i4 lifecycle: grandchild rights are read-only"
    (grandchildCap.map (fun cap => cap.rights) = some (AccessRightSet.ofList [.read]))

  let grantGate : SeLe4n.Kernel.SyscallGate := {
    callerId := ⟨99⟩
    cspaceRoot := cnodeId
    capAddr := ⟨2⟩
    capDepth := 4
    requiredRight := .grant
  }
  expectError "ws-i4 lifecycle: grandchild cannot mint without grant"
    (SeLe4n.Kernel.apiCspaceMint grantGate grandchildSlot extraSlot
      (AccessRightSet.ofList [.read]) none st2)
    .illegalAuthority

  let (revokeReport, st3) ← expectOkState "ws-i4 lifecycle: strict revoke root"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict rootSlot st2)
  expect "ws-i4 lifecycle: strict revoke has no descendant deletion failures"
    (revokeReport.firstFailure = none)
  expect "ws-i4 lifecycle: strict revoke deleted exactly two descendants"
    (revokeReport.deletedSlots.length = 2)
  expect "ws-i4 lifecycle: strict revoke deleted child slot"
    (childSlot ∈ revokeReport.deletedSlots)
  expect "ws-i4 lifecycle: strict revoke deleted grandchild slot"
    (grandchildSlot ∈ revokeReport.deletedSlots)
  expect "ws-i4 lifecycle: child slot removed"
    (SeLe4n.Model.SystemState.lookupSlotCap st3 childSlot = none)
  expect "ws-i4 lifecycle: grandchild slot removed"
    (SeLe4n.Model.SystemState.lookupSlotCap st3 grandchildSlot = none)
  expect "ws-i4 lifecycle: child detached from CDT"
    (SeLe4n.Model.SystemState.lookupCdtNodeOfSlot st3 childSlot = none)
  expect "ws-i4 lifecycle: grandchild detached from CDT"
    (SeLe4n.Model.SystemState.lookupCdtNodeOfSlot st3 grandchildSlot = none)
  assertInvariants "ws-i4 lifecycle: cascading revoke" st3

private def buildParameterizedTopology
    (threadCount : Nat) (basePriority : Nat) (radix : Nat) (asidCount : Nat) : SystemState :=
  let threads : List (SeLe4n.ObjId × KernelObject) :=
    (List.range threadCount).map fun i =>
      let oid : SeLe4n.ObjId := ⟨1000 + i⟩
      (oid, .tcb {
        tid := ⟨1000 + i⟩
        priority := ⟨basePriority + i⟩
        domain := ⟨0⟩
        cspaceRoot := ⟨2000⟩
        vspaceRoot := ⟨3000⟩
        ipcBuffer := ⟨4096 + i * 4096⟩
        ipcState := .ready
      })
  let cnodeSlots : List (SeLe4n.Slot × Capability) :=
    (List.range threadCount).map fun i =>
      (⟨i⟩, { target := .object ⟨1000 + i⟩, rights := AccessRightSet.ofList [.read, .write], badge := none })
  let cnodeObj : KernelObject :=
    .cnode { depth := radix, guardWidth := 0, guardValue := 0, radixWidth := radix, slots := Std.HashMap.ofList cnodeSlots }
  let vspaceRoots : List (SeLe4n.ObjId × KernelObject) :=
    (List.range asidCount).map fun i =>
      let oid : SeLe4n.ObjId := ⟨3000 + i⟩
      (oid, .vspaceRoot { asid := ⟨i + 1⟩, mappings := {} })
  let allObjects := threads ++ [(⟨2000⟩, cnodeObj)] ++ vspaceRoots
  let runnableThreads : List SeLe4n.ThreadId :=
    (List.range threadCount).map fun i => ⟨1000 + i⟩
  let lifecycleTypes : List (SeLe4n.ObjId × KernelObjectType) :=
    (threads.map fun (oid, _) => (oid, .tcb)) ++ [(⟨2000⟩, .cnode)] ++ (vspaceRoots.map fun (oid, _) => (oid, .vspaceRoot))
  let builder := BootstrapBuilder.empty |>.withRunnable runnableThreads
  let builder := allObjects.foldl (fun b (oid, obj) => b.withObject oid obj) builder
  let builder := lifecycleTypes.foldl (fun b (oid, ty) => b.withLifecycleObjectType oid ty) builder
  builder.build

private partial def scheduleNTimes (n : Nat) (assertEvery : Nat) (st : SystemState) : IO SystemState := do
  if n = 0 then
    pure st
  else
    let step := if st.scheduler.current.isSome then SeLe4n.Kernel.handleYield st else SeLe4n.Kernel.schedule st
    let st' ← runKernelState s!"scheduler: schedule step {n}" step
    if assertEvery > 0 && n % assertEvery = 0 then
      assertInvariants s!"scheduler periodic invariant {n}" st'
    scheduleNTimes (n - 1) assertEvery st'

private def schedulerStressChecks : IO Unit := do
  let st16 := buildParameterizedTopology 16 10 4 1
  let st16Final ← scheduleNTimes 50 10 st16
  assertInvariants "scheduler-stress-16" st16Final

  let samePrioState :=
    (BootstrapBuilder.empty
      |>.withObject ⟨260⟩ (.cnode { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 1, slots := {} })
      |>.withObject ⟨3000⟩ (.vspaceRoot { asid := ⟨1⟩, mappings := {} })
      |>.withObject ⟨2600⟩ (.tcb { tid := ⟨2600⟩, priority := ⟨100⟩, domain := ⟨0⟩, cspaceRoot := ⟨260⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨4096⟩, ipcState := .ready })
      |>.withObject ⟨2601⟩ (.tcb { tid := ⟨2601⟩, priority := ⟨100⟩, domain := ⟨0⟩, cspaceRoot := ⟨260⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨8192⟩, ipcState := .ready })
      |>.withObject ⟨2602⟩ (.tcb { tid := ⟨2602⟩, priority := ⟨100⟩, domain := ⟨0⟩, cspaceRoot := ⟨260⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨12288⟩, ipcState := .ready })
      |>.withObject ⟨2603⟩ (.tcb { tid := ⟨2603⟩, priority := ⟨100⟩, domain := ⟨0⟩, cspaceRoot := ⟨260⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨16384⟩, ipcState := .ready })
      |>.withRunnable [⟨2600⟩, ⟨2601⟩, ⟨2602⟩, ⟨2603⟩]
      |>.build)
  let (_, stFirst) ← expectOkState "scheduler same-priority baseline" (SeLe4n.Kernel.schedule samePrioState)
  let baseline := stFirst.scheduler.current
  let mut consistent := true
  for _ in List.range 20 do
    match SeLe4n.Kernel.schedule samePrioState with
    | .ok (_, st') =>
        if st'.scheduler.current ≠ baseline then
          consistent := false
    | .error _ =>
        consistent := false
  expect "scheduler same-priority selection deterministic" consistent

  let domainThreads : List (SeLe4n.ObjId × KernelObject) :=
    (List.range 16).map fun i =>
      let tid : SeLe4n.ThreadId := ⟨4200 + i⟩
      let dom : SeLe4n.DomainId := ⟨i / 4⟩
      let vroot : SeLe4n.ObjId := ⟨4100 + (i / 4)⟩
      (tid.toObjId, .tcb {
        tid := tid
        priority := ⟨50 + i⟩
        domain := dom
        cspaceRoot := ⟨4000⟩
        vspaceRoot := vroot
        ipcBuffer := ⟨4096 + i * 4096⟩
        ipcState := .ready
      })
  let runnableDomainThreads : List SeLe4n.ThreadId :=
    (List.range 16).map fun i => ⟨4200 + i⟩
  let domainStateBaseBuilder :=
    (BootstrapBuilder.empty
      |>.withObject ⟨4000⟩ (.cnode { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 1, slots := {} })
      |>.withObject ⟨4100⟩ (.vspaceRoot { asid := ⟨4⟩, mappings := {} })
      |>.withObject ⟨4101⟩ (.vspaceRoot { asid := ⟨5⟩, mappings := {} })
      |>.withObject ⟨4102⟩ (.vspaceRoot { asid := ⟨6⟩, mappings := {} })
      |>.withObject ⟨4103⟩ (.vspaceRoot { asid := ⟨7⟩, mappings := {} })
      |>.withRunnable runnableDomainThreads)
  let domainStateBase :=
    (domainThreads.foldl (fun b (oid, obj) => b.withObject oid obj) domainStateBaseBuilder).build
  let domainState :=
    { domainStateBase with
      scheduler := { domainStateBase.scheduler with
        domainSchedule := [
          { domain := ⟨0⟩, length := 2 },
          { domain := ⟨1⟩, length := 2 },
          { domain := ⟨2⟩, length := 2 },
          { domain := ⟨3⟩, length := 2 }
        ]
        activeDomain := ⟨0⟩
        domainScheduleIndex := 0
        domainTimeRemaining := 2
      } }
  let mut st := domainState
  let mut isolated := true
  for _ in List.range 16 do
    let stSwitch ← runKernelState "scheduler domain switch" (SeLe4n.Kernel.switchDomain st)
    let stSched ← runKernelState "scheduler domain schedule" (SeLe4n.Kernel.schedule stSwitch)
    match stSched.scheduler.current with
    | none => pure ()
    | some tid =>
        match stSched.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            if tcb.domain ≠ stSched.scheduler.activeDomain then
              isolated := false
        | _ => isolated := false
    st := stSched
  expect "scheduler multi-domain isolation" isolated

private def runOperationChainSuite : IO Unit := do
  chain1RetypeMintRevoke
  chain2SendSendReceiveFifo
  chain3MapLookupUnmapLookup
  chain4ServiceStartDependentStop
  chain5CopyMoveDelete
  chain6NotificationBadgeAccumulation
  wsI4VspaceMultiAsidSharing
  wsI4IpcInterleavedSends
  wsI4LifecycleTransactionChains
  schedulerStressChecks
  IO.println "all WS-I3/WS-I4 operation-chain checks passed"

end SeLe4n.Testing

def main : IO Unit :=
  SeLe4n.Testing.runOperationChainSuite
