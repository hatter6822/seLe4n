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

private def chain7VSpaceMultiAsidSharedPage : IO Unit := do
  let asid1 : SeLe4n.ASID := ⟨31⟩
  let asid2 : SeLe4n.ASID := ⟨32⟩
  let vaddr1 : SeLe4n.VAddr := ⟨0x2000⟩
  let vaddr2 : SeLe4n.VAddr := ⟨0x3000⟩
  let paddr : SeLe4n.PAddr := ⟨0x1000⟩
  let roPerms : PagePermissions := { read := true, write := false, execute := false }
  let rwPerms : PagePermissions := { read := true, write := true, execute := false }
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject ⟨2700⟩ (.vspaceRoot { asid := asid1, mappings := {} })
      |>.withObject ⟨2701⟩ (.vspaceRoot { asid := asid2, mappings := {} })
      |>.build)

  let (_, st1) ← expectOkState "chain7: map shared page into asid1"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asid1 vaddr1 paddr default st0)
  let (_, st2) ← expectOkState "chain7: map shared page into asid2"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asid2 vaddr2 paddr default st1)
  let (asid1Resolved, st3) ← expectOkState "chain7: lookup asid1 shared page"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid1 vaddr1 st2)
  let (asid2Resolved, st4) ← expectOkState "chain7: lookup asid2 shared page"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid2 vaddr2 st3)
  expect "chain7: shared page lookup matches in asid1" (asid1Resolved = paddr)
  expect "chain7: shared page lookup matches in asid2" (asid2Resolved = paddr)

  let (_, st5) ← expectOkState "chain7: unmap shared page from asid1"
    (SeLe4n.Kernel.Architecture.vspaceUnmapPage asid1 vaddr1 st4)
  expectError "chain7: asid1 lookup faults after unmap"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid1 vaddr1 st5) .translationFault
  let (asid2StillMapped, st6) ← expectOkState "chain7: asid2 mapping survives asid1 unmap"
    (SeLe4n.Kernel.Architecture.vspaceLookup asid2 vaddr2 st5)
  expect "chain7: asid2 retains shared mapping" (asid2StillMapped = paddr)

  let (_, st7) ← expectOkState "chain7: remap asid1 as read-only"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asid1 vaddr1 paddr roPerms st6)
  let (_, st8) ← expectOkState "chain7: remap asid2 as read-write"
    (SeLe4n.Kernel.Architecture.vspaceUnmapPage asid2 vaddr2 st7)
  let (_, st9) ← expectOkState "chain7: map asid2 read-write permissions"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asid2 vaddr2 paddr rwPerms st8)
  let ((_, asid1Perms), st10) ← expectOkState "chain7: lookupFull asid1 perms"
    (SeLe4n.Kernel.Architecture.vspaceLookupFull asid1 vaddr1 st9)
  let ((_, asid2Perms), st11) ← expectOkState "chain7: lookupFull asid2 perms"
    (SeLe4n.Kernel.Architecture.vspaceLookupFull asid2 vaddr2 st10)
  expect "chain7: asid1 mapping is read-only" (asid1Perms = roPerms)
  expect "chain7: asid2 mapping is read-write" (asid2Perms = rwPerms)
  expect "chain7: asid1 permissions remain W^X-compliant" asid1Perms.wxCompliant
  expect "chain7: asid2 permissions remain W^X-compliant" asid2Perms.wxCompliant
  assertInvariants "chain7: multi-asid shared mapping semantics" st11

private def chain8IpcInterleavedSendOrdering : IO Unit := do
  let epId : SeLe4n.ObjId := ⟨2800⟩
  let tidA : SeLe4n.ThreadId := ⟨2810⟩
  let tidB : SeLe4n.ThreadId := ⟨2811⟩
  let tidC : SeLe4n.ThreadId := ⟨2812⟩
  let tidD : SeLe4n.ThreadId := ⟨2813⟩
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject tidA.toObjId (.tcb { tid := tidA, priority := ⟨40⟩, domain := ⟨0⟩, cspaceRoot := ⟨300⟩, vspaceRoot := ⟨310⟩, ipcBuffer := ⟨4096⟩, ipcState := .ready })
      |>.withObject tidB.toObjId (.tcb { tid := tidB, priority := ⟨39⟩, domain := ⟨0⟩, cspaceRoot := ⟨300⟩, vspaceRoot := ⟨310⟩, ipcBuffer := ⟨8192⟩, ipcState := .ready })
      |>.withObject tidC.toObjId (.tcb { tid := tidC, priority := ⟨38⟩, domain := ⟨0⟩, cspaceRoot := ⟨300⟩, vspaceRoot := ⟨310⟩, ipcBuffer := ⟨12288⟩, ipcState := .ready })
      |>.withObject tidD.toObjId (.tcb { tid := tidD, priority := ⟨37⟩, domain := ⟨0⟩, cspaceRoot := ⟨300⟩, vspaceRoot := ⟨310⟩, ipcBuffer := ⟨16384⟩, ipcState := .ready })
      |>.withRunnable [tidA, tidB, tidC, tidD]
      |>.build)

  let (_, st1) ← expectOkState "chain8: sender A enqueue" (SeLe4n.Kernel.endpointSendDual epId tidA .empty st0)
  let (_, st2) ← expectOkState "chain8: sender B enqueue" (SeLe4n.Kernel.endpointSendDual epId tidB .empty st1)
  let (_, st3) ← expectOkState "chain8: sender C enqueue" (SeLe4n.Kernel.endpointSendDual epId tidC .empty st2)
  let (firstSender, st4) ← expectOkState "chain8: receiver D dequeues first" (SeLe4n.Kernel.endpointReceiveDual epId tidD st3)
  let (secondSender, st5) ← expectOkState "chain8: receiver D dequeues second" (SeLe4n.Kernel.endpointReceiveDual epId tidD st4)
  let (thirdSender, st6) ← expectOkState "chain8: receiver D dequeues third" (SeLe4n.Kernel.endpointReceiveDual epId tidD st5)
  expect "chain8: FIFO #1 returns sender A" (firstSender = tidA)
  expect "chain8: FIFO #2 returns sender B" (secondSender = tidB)
  expect "chain8: FIFO #3 returns sender C" (thirdSender = tidC)
  let fifoEndpointObj := st6.objects[epId]?
  expect "chain8: endpoint send queue drained after FIFO receives"
    (match fifoEndpointObj with
     | some (.endpoint ep) => ep.sendQ.head = none && ep.sendQ.tail = none
     | _ => false)
  assertInvariants "chain8: three-sender FIFO ordering" st6

  let (_, st7) ← expectOkState "chain8: interleave sender A" (SeLe4n.Kernel.endpointSendDual epId tidA .empty st6)
  let (interleaveFirst, st8) ← expectOkState "chain8: interleave receiver gets A" (SeLe4n.Kernel.endpointReceiveDual epId tidD st7)
  let (_, st9) ← expectOkState "chain8: interleave sender B" (SeLe4n.Kernel.endpointSendDual epId tidB .empty st8)
  let (interleaveSecond, st10) ← expectOkState "chain8: interleave receiver gets B" (SeLe4n.Kernel.endpointReceiveDual epId tidD st9)
  expect "chain8: interleaved receive #1 sender A" (interleaveFirst = tidA)
  expect "chain8: interleaved receive #2 sender B" (interleaveSecond = tidB)
  let interleavedEndpointObj := st10.objects[epId]?
  expect "chain8: endpoint queues empty after interleaved receive"
    (match interleavedEndpointObj with
     | some (.endpoint ep) =>
         ep.sendQ.head = none && ep.sendQ.tail = none &&
         ep.receiveQ.head = none && ep.receiveQ.tail = none
     | _ => false)
  assertInvariants "chain8: interleaved send/receive queue integrity" st10

private def chain9LifecycleCascadingRevokeAndAttenuation : IO Unit := do
  let targetId : SeLe4n.ObjId := ⟨2900⟩
  let rootCNode : SeLe4n.ObjId := ⟨2901⟩
  let childCNode : SeLe4n.ObjId := ⟨2902⟩
  let grandCNode : SeLe4n.ObjId := ⟨2903⟩
  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := rootCNode, slot := ⟨0⟩ }
  let childSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := childCNode, slot := ⟨0⟩ }
  let grandSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := grandCNode, slot := ⟨0⟩ }
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject targetId (.endpoint {})
      |>.withObject rootCNode (.cnode {
          depth := 4
          guardWidth := 0
          guardValue := 0
          radixWidth := 4
          slots := Std.HashMap.ofList [
            (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
          ]
        })
      |>.withObject childCNode (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := {} })
      |>.withObject grandCNode (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := {} })
      |>.build)

  let (_, st1) ← expectOkState "chain9: mint root→child with CDT"
    (SeLe4n.Kernel.cspaceMintWithCdt rootSlot childSlot (AccessRightSet.ofList [.read, .write]) none st0)
  let (_, st2) ← expectOkState "chain9: mint child→grandchild with CDT"
    (SeLe4n.Kernel.cspaceMintWithCdt childSlot grandSlot (AccessRightSet.ofList [.read]) none st1)

  let childCap := SystemState.lookupSlotCap st2 childSlot
  let grandCap := SystemState.lookupSlotCap st2 grandSlot
  expect "chain9: child rights attenuated to read+write"
    (childCap.map Capability.rights = some (AccessRightSet.ofList [.read, .write]))
  expect "chain9: grandchild rights attenuated to read"
    (grandCap.map Capability.rights = some (AccessRightSet.ofList [.read]))

  expectError "chain9: grandchild cannot mint additional write right"
    (SeLe4n.Kernel.cspaceMint grandSlot { cnode := grandCNode, slot := ⟨1⟩ } (AccessRightSet.ofList [.read, .write]) none st2)
    .invalidCapability

  let noGrantGate : SeLe4n.Kernel.SyscallGate := {
    callerId := ⟨42⟩
    cspaceRoot := grandCNode
    capAddr := ⟨0⟩
    capDepth := 4
    requiredRight := .grant
  }
  expectError "chain9: grandchild syscall gate has no grant right"
    (SeLe4n.Kernel.syscallLookupCap noGrantGate st2)
    .illegalAuthority
  expectError "chain9: grandchild cannot apiCspaceMint without grant"
    (SeLe4n.Kernel.apiCspaceMint noGrantGate grandSlot { cnode := grandCNode, slot := ⟨1⟩ }
      (AccessRightSet.ofList [.read]) none st2)
    .illegalAuthority

  let (_, st3) ← expectOkState "chain9: revoke root cascades descendants"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict rootSlot st2)
  expect "chain9: child slot removed after root revoke"
    (SystemState.lookupSlotCap st3 childSlot = none)
  expect "chain9: grandchild slot removed after root revoke"
    (SystemState.lookupSlotCap st3 grandSlot = none)
  expect "chain9: child CDT node detached"
    (SystemState.lookupCdtNodeOfSlot st3 childSlot = none)
  expect "chain9: grandchild CDT node detached"
    (SystemState.lookupCdtNodeOfSlot st3 grandSlot = none)
  assertInvariants "chain9: cascading revoke and authority degradation" st3

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

-- ============================================================================
-- WS-J1-E: Register decode operation chains
-- ============================================================================

/-- WS-J1-E: Multi-syscall sequence via register decode path.
Exercises: decode → send, then decode → receive on same endpoint.
Verifies the full register-sourced authority chain across two syscalls. -/
private def chain10RegisterDecodeMultiSyscall : IO Unit := do
  -- Build state: two TCBs (sender=300, receiver=301), endpoint, CNode with caps
  let senderId : SeLe4n.ObjId := ⟨300⟩
  let receiverId : SeLe4n.ObjId := ⟨301⟩
  let epId : SeLe4n.ObjId := ⟨302⟩
  let cnodeId : SeLe4n.ObjId := ⟨303⟩
  -- CNode slot 0: write cap to endpoint (for send)
  -- CNode slot 1: read cap to endpoint (for receive)
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject senderId (.tcb {
        tid := ⟨300⟩
        priority := ⟨50⟩
        domain := ⟨0⟩
        cspaceRoot := cnodeId
        vspaceRoot := ⟨20⟩
        ipcBuffer := ⟨4096⟩
        ipcState := .ready
        registerContext := {  -- x0=0 (capPtr for slot 0), x1=0 (msgInfo), x7=0 (send)
          pc := ⟨0x1000⟩, sp := ⟨0x8000⟩,
          gpr := fun _ => ⟨0⟩ }  -- send syscall, capAddr=0
      })
      |>.withObject receiverId (.tcb {
        tid := ⟨301⟩
        priority := ⟨40⟩
        domain := ⟨0⟩
        cspaceRoot := cnodeId
        vspaceRoot := ⟨20⟩
        ipcBuffer := ⟨8192⟩
        ipcState := .ready
        registerContext := {  -- x0=1 (capPtr for slot 1), x1=0 (msgInfo), x7=1 (receive)
          pc := ⟨0x1000⟩, sp := ⟨0x8000⟩,
          gpr := fun r =>
            if r.val == 0 then ⟨1⟩       -- capAddr = CPtr 1 (receive cap)
            else if r.val == 7 then ⟨1⟩  -- syscallId = receive (1)
            else ⟨0⟩ }
      })
      |>.withObject epId (.endpoint {})
      |>.withObject cnodeId (.cnode {
        depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
        slots := Std.HashMap.ofList [
          (⟨0⟩, { target := .object epId, rights := AccessRightSet.ofList [.read, .write], badge := none }),
          (⟨1⟩, { target := .object epId, rights := AccessRightSet.ofList [.read], badge := none })
        ]
      })
      |>.withObject ⟨20⟩ (.vspaceRoot { asid := ⟨1⟩, mappings := {} })
      |>.withLifecycleObjectType senderId .tcb
      |>.withLifecycleObjectType receiverId .tcb
      |>.withLifecycleObjectType epId .endpoint
      |>.withLifecycleObjectType cnodeId .cnode
      |>.withLifecycleObjectType ⟨20⟩ .vspaceRoot
      |>.withRunnable [⟨301⟩]
      |>.withCurrent (some ⟨300⟩)
      |>.build)

  -- Step 1: Sender (current) does syscallEntry (send) → queues on endpoint
  let stAfterSend ← match SeLe4n.Kernel.syscallEntry SeLe4n.arm64DefaultLayout 32 st0 with
    | .ok (_, st') => pure st'
    | .error err => throw <| IO.userError s!"chain10 send failed: {reprStr err}"
  -- Verify sender queued on endpoint
  match stAfterSend.objects[epId]? with
  | some (.endpoint ep) =>
      expect "chain10 sender queued on endpoint" (ep.sendQ.head.isSome)
  | _ => throw <| IO.userError "chain10: endpoint not found after send"

  -- Verify sender's TCB is blocked on send
  match stAfterSend.objects[senderId]? with
  | some (.tcb senderTcb) =>
      expect "chain10 sender blocked on send" (senderTcb.ipcState == .blockedOnSend epId)
  | _ => throw <| IO.userError "chain10: sender TCB not found after send"

  -- Step 2: Dispatch receiver — remove from runQueue before making current
  let stRecv := { stAfterSend with scheduler := { stAfterSend.scheduler with
    current := some ⟨301⟩,
    runQueue := stAfterSend.scheduler.runQueue.remove ⟨301⟩ } }
  let stFinal ← match SeLe4n.Kernel.syscallEntry SeLe4n.arm64DefaultLayout 32 stRecv with
  | .ok (_, stAfterRecv) =>
      -- After receive, endpoint sendQ should be empty (sender was dequeued)
      match stAfterRecv.objects[epId]? with
      | some (.endpoint ep) =>
          expect "chain10 endpoint empty after receive" ep.sendQ.head.isNone
      | _ => throw <| IO.userError "chain10: endpoint not found after receive"
      pure stAfterRecv
  | .error err =>
      throw <| IO.userError s!"chain10 receive failed: {reprStr err}"

  assertInvariants "chain10-register-decode-multi-syscall" stFinal

/-- WS-J1-E: Register decode followed by IPC with message transfer.
Exercises: decode registers → send with badge → verify badge on endpoint. -/
private def chain11RegisterDecodeIpcTransfer : IO Unit := do
  let senderId : SeLe4n.ObjId := ⟨400⟩
  let epId : SeLe4n.ObjId := ⟨402⟩
  let cnodeId : SeLe4n.ObjId := ⟨403⟩
  let badgeVal : SeLe4n.Badge := ⟨0xBEEF⟩
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject senderId (.tcb {
        tid := ⟨400⟩
        priority := ⟨50⟩
        domain := ⟨0⟩
        cspaceRoot := cnodeId
        vspaceRoot := ⟨20⟩
        ipcBuffer := ⟨4096⟩
        ipcState := .ready
        registerContext := {  -- x0=0 (capPtr), x1=0 (msgInfo), x7=0 (send)
          pc := ⟨0x1000⟩, sp := ⟨0x8000⟩,
          gpr := fun _ => ⟨0⟩ }
      })
      |>.withObject epId (.endpoint {})
      |>.withObject cnodeId (.cnode {
        depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
        slots := Std.HashMap.ofList [
          (⟨0⟩, { target := .object epId,
                   rights := AccessRightSet.ofList [.read, .write],
                   badge := some badgeVal })
        ]
      })
      |>.withObject ⟨20⟩ (.vspaceRoot { asid := ⟨1⟩, mappings := {} })
      |>.withLifecycleObjectType senderId .tcb
      |>.withLifecycleObjectType epId .endpoint
      |>.withLifecycleObjectType cnodeId .cnode
      |>.withLifecycleObjectType ⟨20⟩ .vspaceRoot
      |>.withCurrent (some ⟨400⟩)
      |>.build)

  -- syscallEntry send: the badge from the CNode cap should be attached
  let stSend := st0
  let stFinal ← match SeLe4n.Kernel.syscallEntry SeLe4n.arm64DefaultLayout 32 stSend with
  | .ok (_, stAfter) =>
      -- Verify sender queued on endpoint
      match stAfter.objects[epId]? with
      | some (.endpoint ep) =>
          expect "chain11 sender queued on endpoint" ep.sendQ.head.isSome
      | _ => throw <| IO.userError "chain11: endpoint not found"
      -- Verify the badge from the cap was attached to the sender's pending message
      match stAfter.objects[senderId]? with
      | some (.tcb senderTcb) =>
          expect "chain11 sender blocked on send" (senderTcb.ipcState == .blockedOnSend epId)
          match senderTcb.pendingMessage with
          | some msg =>
              expect "chain11 badge attached to message" (msg.badge == some badgeVal)
              IO.println s!"operation-chain check passed [chain11 sender queued with badge: true]"
          | none => throw <| IO.userError "chain11: sender has no pending message"
      | _ => throw <| IO.userError "chain11: sender TCB not found"
      pure stAfter
  | .error err =>
      throw <| IO.userError s!"chain11 send failed: {reprStr err}"

  assertInvariants "chain11-register-decode-ipc-transfer" stFinal

-- ============================================================================
-- WS-M4/M-T02: Strict revocation stress tests
-- ============================================================================

-- Monadic fold helper for IO (List.foldlM not available in Lean 4.28.0)
private def ioFoldl {α β : Type} (f : α → β → IO α) (init : α) : List β → IO α
  | [] => pure init
  | x :: xs => do let acc ← f init x; ioFoldl f acc xs

private def chain12StrictRevocationDeepChain : IO Unit := do
  IO.println "\n--- WS-M4-B: cspaceRevokeCdtStrict stress tests ---"

  -- M4-B1 (SCN-REVOKE-STRICT-DEEP): Deep chain with 15 descendants
  -- Build a linear derivation chain: root → d1 → d2 → ... → d15
  let rootCn : SeLe4n.ObjId := ⟨3000⟩
  let targetId : SeLe4n.ObjId := ⟨3001⟩
  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := rootCn, slot := ⟨0⟩ }

  -- Create 15 descendant CNodes (IDs 3010..3024)
  let descCount := 15
  let descCnodes : List SeLe4n.ObjId := (List.range descCount).map fun i => ⟨3010 + i⟩
  let descSlots : List SeLe4n.Kernel.CSpaceAddr :=
    descCnodes.map fun cn => { cnode := cn, slot := ⟨0⟩ }

  -- Build state with root CNode and all descendant CNodes
  let builder0 := BootstrapBuilder.empty
    |>.withObject targetId (.endpoint {})
    |>.withObject rootCn (.cnode {
        depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
        slots := Std.HashMap.ofList [
          (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
        ] })
  let builder1 := descCnodes.foldl (fun b cn =>
    b.withObject cn (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := {} })) builder0
  let st0 := builder1.build

  -- Mint chain: root → d0 → d1 → ... → d14
  let mintPairs := descSlots.zipIdx
  let (stMinted, _) ← ioFoldl (fun (stAcc, prevSlotAcc) (dstSlot, i) => do
    let (_, stNext) ← expectOkState s!"M4-B1: mint descendant {i}"
      (SeLe4n.Kernel.cspaceMintWithCdt prevSlotAcc dstSlot (AccessRightSet.ofList [.read]) none stAcc)
    pure (stNext, dstSlot)
  ) (st0, rootSlot) mintPairs

  -- Verify all descendants have caps before revoke
  let descSlotsIdx := descSlots.zipIdx
  descSlotsIdx.forM fun (dstSlot, i) =>
    expect s!"M4-B1: descendant {i} has cap before revoke"
      (SystemState.lookupSlotCap stMinted dstSlot).isSome

  -- Revoke from root
  let (report, stRevoked) ← expectOkState "M4-B1 SCN-REVOKE-STRICT-DEEP: revoke deep chain"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict rootSlot stMinted)

  -- Verify all descendants deleted
  expect "M4-B1: all 15 descendants deleted"
    (report.deletedSlots.length = descCount)
  expect "M4-B1: no failure in deep chain"
    report.firstFailure.isNone

  descSlotsIdx.forM fun (dstSlot, i) => do
    expect s!"M4-B1: descendant {i} slot cleared after revoke"
      (SystemState.lookupSlotCap stRevoked dstSlot = none)
    expect s!"M4-B1: descendant {i} CDT node detached"
      (SystemState.lookupCdtNodeOfSlot stRevoked dstSlot = none)

  assertInvariants "M4-B1 deep chain revocation" stRevoked
  IO.println "operation-chain check passed [M4-B1 SCN-REVOKE-STRICT-DEEP: 15-descendant chain fully revoked]"

private def chain13StrictRevocationPartialFailure : IO Unit := do
  -- M4-B2 (SCN-REVOKE-STRICT-PARTIAL-FAIL): Partial failure mid-traversal
  -- Chain: root → child_ok1 → child_ok2 → child_bad (CNode deleted from objects)
  -- Expected: firstFailure populated with child_bad context, deletedSlots has ok1 + ok2
  let rootCn : SeLe4n.ObjId := ⟨3100⟩
  let targetId : SeLe4n.ObjId := ⟨3101⟩
  let okCn1 : SeLe4n.ObjId := ⟨3102⟩
  let okCn2 : SeLe4n.ObjId := ⟨3103⟩
  let badCn : SeLe4n.ObjId := ⟨3104⟩
  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := rootCn, slot := ⟨0⟩ }

  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject targetId (.endpoint {})
      |>.withObject rootCn (.cnode {
          depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := Std.HashMap.ofList [
            (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
          ] })
      |>.withObject okCn1 (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := {} })
      |>.withObject okCn2 (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := {} })
      |>.withObject badCn (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := {} })
      |>.build)

  -- Mint: root → ok1 → ok2 → bad
  let okSlot1 : SeLe4n.Kernel.CSpaceAddr := { cnode := okCn1, slot := ⟨0⟩ }
  let okSlot2 : SeLe4n.Kernel.CSpaceAddr := { cnode := okCn2, slot := ⟨0⟩ }
  let badSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := badCn, slot := ⟨0⟩ }
  let (_, st1) ← expectOkState "M4-B2: mint root→ok1"
    (SeLe4n.Kernel.cspaceMintWithCdt rootSlot okSlot1 (AccessRightSet.ofList [.read]) none st0)
  let (_, st2) ← expectOkState "M4-B2: mint ok1→ok2"
    (SeLe4n.Kernel.cspaceMintWithCdt okSlot1 okSlot2 (AccessRightSet.ofList [.read]) none st1)
  let (_, st3) ← expectOkState "M4-B2: mint ok2→bad"
    (SeLe4n.Kernel.cspaceMintWithCdt okSlot2 badSlot (AccessRightSet.ofList [.read]) none st2)

  -- Sabotage: remove badCn from objects so cspaceDeleteSlot will fail with objectNotFound
  let stSabotaged : SystemState := { st3 with objects := st3.objects.erase badCn }

  -- Revoke from root — should partially succeed
  let (report, stPartial) ← expectOkState "M4-B2 SCN-REVOKE-STRICT-PARTIAL-FAIL: revoke with sabotaged descendant"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict rootSlot stSabotaged)

  -- ok1 and ok2 should be deleted before failure
  expect "M4-B2: deletedSlots contains 2 successful deletions"
    (report.deletedSlots.length = 2)

  -- firstFailure should reference the bad node
  match report.firstFailure with
  | some failure =>
      expect "M4-B2: failure error is objectNotFound"
        (failure.error = .objectNotFound)
      expect "M4-B2: failure slot references badCn"
        (failure.offendingSlot = some badSlot)
      IO.println "operation-chain check passed [M4-B2 SCN-REVOKE-STRICT-PARTIAL-FAIL: partial failure captured]"
  | none =>
      throw <| IO.userError "M4-B2: expected firstFailure to be populated"

  -- ok1 and ok2 should be detached
  expect "M4-B2: ok1 CDT node detached"
    (SystemState.lookupCdtNodeOfSlot stPartial okSlot1 = none)
  expect "M4-B2: ok2 CDT node detached"
    (SystemState.lookupCdtNodeOfSlot stPartial okSlot2 = none)
  assertInvariants "M4-B2 partial failure" stPartial

private def chain14StrictRevocationBfsOrdering : IO Unit := do
  -- M4-B3 (SCN-REVOKE-STRICT-ORDER): Verify deletedSlots is in BFS traversal order
  -- Build a fan-out tree:  root → [A, B]
  --                         A → [C]
  --                         B → [D]
  -- BFS from root: A, B (children of root), then C (child of A), then D (child of B)
  -- deletedSlots should be [slotA, slotB, slotC, slotD]
  let rootCn : SeLe4n.ObjId := ⟨3200⟩
  let targetId : SeLe4n.ObjId := ⟨3201⟩
  let cnA : SeLe4n.ObjId := ⟨3202⟩
  let cnB : SeLe4n.ObjId := ⟨3203⟩
  let cnC : SeLe4n.ObjId := ⟨3204⟩
  let cnD : SeLe4n.ObjId := ⟨3205⟩
  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := rootCn, slot := ⟨0⟩ }
  let slotA : SeLe4n.Kernel.CSpaceAddr := { cnode := cnA, slot := ⟨0⟩ }
  let slotB : SeLe4n.Kernel.CSpaceAddr := { cnode := cnB, slot := ⟨0⟩ }
  let slotC : SeLe4n.Kernel.CSpaceAddr := { cnode := cnC, slot := ⟨0⟩ }
  let slotD : SeLe4n.Kernel.CSpaceAddr := { cnode := cnD, slot := ⟨0⟩ }

  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject targetId (.endpoint {})
      |>.withObject rootCn (.cnode {
          depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := Std.HashMap.ofList [
            (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
          ] })
      |>.withObject cnA (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := {} })
      |>.withObject cnB (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := {} })
      |>.withObject cnC (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := {} })
      |>.withObject cnD (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := {} })
      |>.build)

  -- Mint: root → A, root → B (fan-out from root)
  let (_, st1) ← expectOkState "M4-B3: mint root→A"
    (SeLe4n.Kernel.cspaceMintWithCdt rootSlot slotA (AccessRightSet.ofList [.read, .grant]) none st0)
  let (_, st2) ← expectOkState "M4-B3: mint root→B"
    (SeLe4n.Kernel.cspaceMintWithCdt rootSlot slotB (AccessRightSet.ofList [.read, .grant]) none st1)
  -- Mint: A → C, B → D
  let (_, st3) ← expectOkState "M4-B3: mint A→C"
    (SeLe4n.Kernel.cspaceMintWithCdt slotA slotC (AccessRightSet.ofList [.read]) none st2)
  let (_, st4) ← expectOkState "M4-B3: mint B→D"
    (SeLe4n.Kernel.cspaceMintWithCdt slotB slotD (AccessRightSet.ofList [.read]) none st3)

  let (report, stRevoked) ← expectOkState "M4-B3 SCN-REVOKE-STRICT-ORDER: revoke fan-out tree"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict rootSlot st4)

  expect "M4-B3: all 4 descendants deleted"
    (report.deletedSlots.length = 4)
  expect "M4-B3: no failure"
    report.firstFailure.isNone

  -- Verify BFS ordering: descendants of root come first (A, B), then their children (C, D)
  -- Note: BFS order depends on childrenOf which uses childMap (HashMap). The exact order
  -- of A vs B depends on insertion order in the childMap. Since addEdge prepends to the
  -- childMap list, B (added second) appears before A in childrenOf.
  -- BFS queue processing: [root] → children of root → [B, A] → children of B, then A
  -- → [A, D] → children of A → [D, C] → [C]
  -- So BFS order is: B, A, D, C → deletedSlots = [slotB, slotA, slotD, slotC]

  -- Rather than hardcoding exact order (which depends on HashMap internals),
  -- verify structural BFS property: children appear after their parents
  let slotList := report.deletedSlots
  -- Position finder: returns index of first occurrence or slotList.length (sentinel)
  let posOf (target : SeLe4n.Kernel.CSpaceAddr) : Nat :=
    slotList.zipIdx.foldl (fun acc (s, i) => if s == target && acc == slotList.length then i else acc) slotList.length
  let idxA := posOf slotA
  let idxB := posOf slotB
  let idxC := posOf slotC
  let idxD := posOf slotD

  -- All four must be present
  expect "M4-B3: slotA in deletedSlots" (idxA < slotList.length)
  expect "M4-B3: slotB in deletedSlots" (idxB < slotList.length)
  expect "M4-B3: slotC in deletedSlots" (idxC < slotList.length)
  expect "M4-B3: slotD in deletedSlots" (idxD < slotList.length)

  -- BFS property: parent before child
  expect "M4-B3: slotA before slotC (parent before child)" (idxA < idxC)
  expect "M4-B3: slotB before slotD (parent before child)" (idxB < idxD)

  -- All slots cleared
  [slotA, slotB, slotC, slotD].forM fun s => do
    expect s!"M4-B3: {reprStr s} cleared" (SystemState.lookupSlotCap stRevoked s = none)
    expect s!"M4-B3: {reprStr s} CDT detached" (SystemState.lookupCdtNodeOfSlot stRevoked s = none)

  assertInvariants "M4-B3 BFS ordering" stRevoked
  IO.println "operation-chain check passed [M4-B3 SCN-REVOKE-STRICT-ORDER: BFS parent-before-child verified]"

private def runOperationChainSuite : IO Unit := do
  chain1RetypeMintRevoke
  chain2SendSendReceiveFifo
  chain3MapLookupUnmapLookup
  chain4ServiceStartDependentStop
  chain5CopyMoveDelete
  chain6NotificationBadgeAccumulation
  chain7VSpaceMultiAsidSharedPage
  chain8IpcInterleavedSendOrdering
  chain9LifecycleCascadingRevokeAndAttenuation
  schedulerStressChecks
  chain10RegisterDecodeMultiSyscall
  chain11RegisterDecodeIpcTransfer
  chain12StrictRevocationDeepChain
  chain13StrictRevocationPartialFailure
  chain14StrictRevocationBfsOrdering
  IO.println "all WS-I3/WS-I4 operation-chain checks passed"

end SeLe4n.Testing

def main : IO Unit :=
  SeLe4n.Testing.runOperationChainSuite
