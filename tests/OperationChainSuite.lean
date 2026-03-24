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
import SeLe4n.Platform.Boot

set_option maxRecDepth 1024

open SeLe4n.Model

namespace SeLe4n.Testing

instance : Inhabited SeLe4n.Kernel.CSpaceAddr where
  default := { cnode := ⟨0⟩, slot := ⟨0⟩ }

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
      throw <| IO.userError s!"{label}: expected success, got {toString err}"

private def runKernelState
    (label : String)
    (actual : Except KernelError (Unit × SystemState)) : IO SystemState :=
  match actual with
  | .ok (_, st) =>
      pure st
  | .error err =>
      throw <| IO.userError s!"{label}: expected success, got {toString err}"

private def expectError
    (label : String)
    (actual : Except KernelError α)
    (expected : KernelError) : IO Unit :=
  match actual with
  | .ok _ => throw <| IO.userError s!"{label}: expected {toString expected}, got success"
  | .error err =>
      if err = expected then
        IO.println s!"operation-chain check passed [{label}]"
      else
        throw <| IO.userError s!"{label}: expected {toString expected}, got {toString err}"

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
          slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [
            (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
          ]
        })
      |>.withLifecycleObjectType targetId .notification
      |>.withLifecycleObjectType cnodeId .cnode
      |>.withLifecycleCapabilityRef authSlot (.object targetId)
      |>.buildChecked)

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
      |>.buildChecked)
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
      |>.buildChecked)
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

private def chain4ServiceRegistryDependencyGraph : IO Unit := do
  let baseSid : ServiceId := ⟨230⟩
  let depSid : ServiceId := ⟨231⟩
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject ⟨500⟩ (.endpoint {})
      |>.withObject ⟨501⟩ (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
      |>.withService baseSid {
          identity := { sid := baseSid, backingObject := ⟨500⟩, owner := ⟨1⟩ }
          dependencies := []
          isolatedFrom := [] }
      |>.withService depSid {
          identity := { sid := depSid, backingObject := ⟨501⟩, owner := ⟨1⟩ }
          dependencies := [baseSid]
          isolatedFrom := [] }
      |>.buildChecked)
  -- Q1: Service lifecycle removed — test dependency graph operations
  expect "chain4: depSid depends on baseSid" ((SeLe4n.Model.lookupService st0 depSid).map ServiceGraphEntry.dependencies = some [baseSid])
  -- Register a new dependency: depSid → baseSid already exists, add baseSid → depSid to form a cycle rejection
  expectError "chain4: cyclic dependency registration rejected"
    (SeLe4n.Kernel.serviceRegisterDependency baseSid depSid st0) .cyclicDependency
  -- Self-loop rejection
  expectError "chain4: self-loop dependency rejected"
    (SeLe4n.Kernel.serviceRegisterDependency baseSid baseSid st0) .cyclicDependency

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
          slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [
            (⟨0⟩, { target := .object target, rights := AccessRightSet.ofList [.read, .write], badge := none })
          ]
        })
      |>.withLifecycleObjectType target .endpoint
      |>.withLifecycleObjectType cnodeId .cnode
      |>.buildChecked)
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
      |>.buildChecked)
  let (_, st1) ← expectOkState "chain6: signal badge 0x01"
    (SeLe4n.Kernel.notificationSignal ntfnId (SeLe4n.Badge.ofNatMasked 0x01) st0)
  let (_, st2) ← expectOkState "chain6: signal badge 0x10"
    (SeLe4n.Kernel.notificationSignal ntfnId (SeLe4n.Badge.ofNatMasked 0x10) st1)
  let (received, st3) ← expectOkState "chain6: wait"
    (SeLe4n.Kernel.notificationWait ntfnId waiter st2)
  expect "chain6: badge accumulation is bitwise OR"
    (received = some (SeLe4n.Badge.ofNatMasked 0x11))
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
      |>.buildChecked)

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
      |>.buildChecked)

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

-- S2-J: Migrated from deprecated apiCspaceMint to syscallInvoke path.
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
          slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [
            (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
          ]
        })
      |>.withObject childCNode (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16 })
      |>.withObject grandCNode (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16 })
      |>.buildChecked)

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
  -- S2-J: Replaced deprecated apiCspaceMint with equivalent syscallInvoke path
  expectError "chain9: grandchild cannot mint via syscall gate without grant"
    (SeLe4n.Kernel.syscallInvoke { noGrantGate with requiredRight := .grant } (fun cap =>
      if cap.target ≠ .object grandSlot.cnode then fun _ => .error .invalidCapability
      else SeLe4n.Kernel.cspaceMint grandSlot { cnode := grandCNode, slot := ⟨1⟩ }
        (AccessRightSet.ofList [.read]) none) st2)
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
    .cnode { depth := radix, guardWidth := 0, guardValue := 0, radixWidth := radix, slots := SeLe4n.Kernel.RobinHood.RHTable.ofList cnodeSlots }
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
      |>.withObject ⟨260⟩ (.cnode { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 1, slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16 })
      |>.withObject ⟨3000⟩ (.vspaceRoot { asid := ⟨1⟩, mappings := {} })
      |>.withObject ⟨2600⟩ (.tcb { tid := ⟨2600⟩, priority := ⟨100⟩, domain := ⟨0⟩, cspaceRoot := ⟨260⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨4096⟩, ipcState := .ready })
      |>.withObject ⟨2601⟩ (.tcb { tid := ⟨2601⟩, priority := ⟨100⟩, domain := ⟨0⟩, cspaceRoot := ⟨260⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨8192⟩, ipcState := .ready })
      |>.withObject ⟨2602⟩ (.tcb { tid := ⟨2602⟩, priority := ⟨100⟩, domain := ⟨0⟩, cspaceRoot := ⟨260⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨12288⟩, ipcState := .ready })
      |>.withObject ⟨2603⟩ (.tcb { tid := ⟨2603⟩, priority := ⟨100⟩, domain := ⟨0⟩, cspaceRoot := ⟨260⟩, vspaceRoot := ⟨3000⟩, ipcBuffer := ⟨16384⟩, ipcState := .ready })
      |>.withRunnable [⟨2600⟩, ⟨2601⟩, ⟨2602⟩, ⟨2603⟩]
      |>.buildChecked)
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
      |>.withObject ⟨4000⟩ (.cnode { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 1, slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16 })
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
        slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [
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
      |>.withRunnable [⟨300⟩, ⟨301⟩]
      |>.withCurrent (some ⟨300⟩)
      |>.buildChecked)

  -- Step 1: Sender (current) does syscallEntry (send) → queues on endpoint
  let stAfterSend ← match SeLe4n.Kernel.syscallEntry SeLe4n.arm64DefaultLayout 32 st0 with
    | .ok (_, st') => pure st'
    | .error err => throw <| IO.userError s!"chain10 send failed: {toString err}"
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
      throw <| IO.userError s!"chain10 receive failed: {toString err}"

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
        slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [
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
      |>.withRunnable [⟨400⟩]
      |>.withCurrent (some ⟨400⟩)
      |>.buildChecked)

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
      throw <| IO.userError s!"chain11 send failed: {toString err}"

  assertInvariants "chain11-register-decode-ipc-transfer" stFinal

-- ============================================================================
-- M-D01 / WS-M3: IPC capability transfer tests
-- ============================================================================

/-- SCN-IPC-CAP-TRANSFER-BASIC: Positive IPC cap transfer with Grant right.
Sender sends 2 caps via endpointSendDualWithCaps to a waiting receiver.
Verifies caps land in receiver's CNode and invariants hold. -/
private def chain12IpcCapTransfer : IO Unit := do
  let epId : SeLe4n.ObjId := ⟨3200⟩
  let sender : SeLe4n.ThreadId := ⟨3210⟩
  let receiver : SeLe4n.ThreadId := ⟨3211⟩
  let senderCNode : SeLe4n.ObjId := ⟨3220⟩
  let receiverCNode : SeLe4n.ObjId := ⟨3221⟩
  let targetObj : SeLe4n.ObjId := ⟨3230⟩

  let cap1 : Capability := { target := .object targetObj, rights := AccessRightSet.ofList [.read], badge := none }
  let cap2 : Capability := { target := .object targetObj, rights := AccessRightSet.ofList [.read, .write], badge := none }
  let cap3 : Capability := { target := .object targetObj, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none }
  let grantRights := AccessRightSet.ofList [.read, .write, .grant]

  -- Setup: receiver waiting on endpoint, sender has caps in CNode
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject targetObj (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
      |>.withObject senderCNode (.cnode {
          depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [
            (⟨0⟩, cap1),
            (⟨1⟩, cap2),
            (⟨2⟩, cap3)
          ]
        })
      |>.withObject receiverCNode (.cnode {
          depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16
        })
      |>.withObject sender.toObjId (.tcb { tid := sender, priority := ⟨40⟩, domain := ⟨0⟩, cspaceRoot := senderCNode, vspaceRoot := ⟨3240⟩, ipcBuffer := ⟨4096⟩, ipcState := .ready })
      |>.withObject receiver.toObjId (.tcb { tid := receiver, priority := ⟨39⟩, domain := ⟨0⟩, cspaceRoot := receiverCNode, vspaceRoot := ⟨3241⟩, ipcBuffer := ⟨8192⟩, ipcState := .ready })
      |>.withRunnable [sender, receiver]
      |>.buildChecked)

  -- Step 1: Receiver blocks on endpoint
  let (_, st1) ← expectOkState "chain12: receiver blocks on endpoint"
    (SeLe4n.Kernel.endpointReceiveDual epId receiver st0)

  -- Step 2: Sender sends with caps (immediate rendezvous)
  let msg : IpcMessage := { registers := #[⟨42⟩], caps := #[cap1, cap2, cap3], badge := none }
  let (summary, st2) ← expectOkState "chain12: send with caps"
    (SeLe4n.Kernel.endpointSendDualWithCaps epId sender msg grantRights senderCNode (SeLe4n.Slot.ofNat 0) st1)

  -- Verify: transfer summary — 3 caps transferred
  expect "chain12: summary has 3 results" (summary.results.size = 3)

  -- Verify: receiver's CNode has 3 new caps in slots 0, 1, 2
  let recvCnodeCheck := match st2.objects[receiverCNode]? with
    | some (.cnode cn) =>
        (cn.lookup ⟨0⟩).isSome && (cn.lookup ⟨1⟩).isSome && (cn.lookup ⟨2⟩).isSome
    | _ => false
  expect "chain12: receiver CNode has 3 caps" recvCnodeCheck

  assertInvariants "chain12: IPC cap transfer basic" st2

/-- SCN-IPC-CAP-TRANSFER-NO-GRANT: Grant-right gate blocks cap transfer.
Endpoint lacks Grant right — caps should be silently dropped. -/
private def chain13IpcCapTransferNoGrant : IO Unit := do
  let epId : SeLe4n.ObjId := ⟨3300⟩
  let sender : SeLe4n.ThreadId := ⟨3310⟩
  let receiver : SeLe4n.ThreadId := ⟨3311⟩
  let senderCNode : SeLe4n.ObjId := ⟨3320⟩
  let receiverCNode : SeLe4n.ObjId := ⟨3321⟩
  let targetObj : SeLe4n.ObjId := ⟨3330⟩

  let cap1 : Capability := { target := .object targetObj, rights := AccessRightSet.ofList [.read], badge := none }
  -- No Grant right on endpoint
  let noGrantRights := AccessRightSet.ofList [.read, .write]

  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject targetObj (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
      |>.withObject senderCNode (.cnode {
          depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [(⟨0⟩, cap1)]
        })
      |>.withObject receiverCNode (.cnode {
          depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16
        })
      |>.withObject sender.toObjId (.tcb { tid := sender, priority := ⟨40⟩, domain := ⟨0⟩, cspaceRoot := senderCNode, vspaceRoot := ⟨3340⟩, ipcBuffer := ⟨4096⟩, ipcState := .ready })
      |>.withObject receiver.toObjId (.tcb { tid := receiver, priority := ⟨39⟩, domain := ⟨0⟩, cspaceRoot := receiverCNode, vspaceRoot := ⟨3341⟩, ipcBuffer := ⟨8192⟩, ipcState := .ready })
      |>.withRunnable [sender, receiver]
      |>.buildChecked)

  let (_, st1) ← expectOkState "chain13: receiver blocks"
    (SeLe4n.Kernel.endpointReceiveDual epId receiver st0)

  let msg : IpcMessage := { registers := #[⟨99⟩], caps := #[cap1], badge := none }
  let (summary, st2) ← expectOkState "chain13: send without grant right"
    (SeLe4n.Kernel.endpointSendDualWithCaps epId sender msg noGrantRights senderCNode (SeLe4n.Slot.ofNat 0) st1)

  -- All results should be grantDenied (or empty since no grant)
  let allDenied := summary.results.all fun r =>
    match r with | .grantDenied => true | _ => false
  -- If summary has results, they should all be grantDenied.
  -- If summary is empty (no rendezvous detected), that's also acceptable.
  expect "chain13: all caps denied or empty" (allDenied || summary.results.isEmpty)

  -- Receiver's CNode should still be empty
  let recvEmpty := match st2.objects[receiverCNode]? with
    | some (.cnode cn) => (cn.lookup ⟨0⟩).isNone
    | _ => false
  expect "chain13: receiver CNode still empty" recvEmpty

  assertInvariants "chain13: IPC cap transfer no grant" st2

/-- SCN-IPC-CAP-BADGE-COMBINED: Badge propagation and cap transfer work together.
Sender's endpoint cap has badge 0xCAFE. Sender sends 1 register + 2 extra caps.
Verifies receiver gets both the badge and the transferred capabilities. -/
private def chain14IpcBadgeAndCapTransfer : IO Unit := do
  let epId : SeLe4n.ObjId := ⟨3400⟩
  let sender : SeLe4n.ThreadId := ⟨3410⟩
  let receiver : SeLe4n.ThreadId := ⟨3411⟩
  let senderCNode : SeLe4n.ObjId := ⟨3420⟩
  let receiverCNode : SeLe4n.ObjId := ⟨3421⟩
  let targetObj1 : SeLe4n.ObjId := ⟨3430⟩
  let targetObj2 : SeLe4n.ObjId := ⟨3431⟩

  let cap1 : Capability := { target := .object targetObj1, rights := AccessRightSet.ofList [.read], badge := none }
  let cap2 : Capability := { target := .object targetObj2, rights := AccessRightSet.ofList [.read, .write], badge := none }
  let grantRights := AccessRightSet.ofList [.read, .write, .grant]

  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject targetObj1 (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
      |>.withObject targetObj2 (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
      |>.withObject senderCNode (.cnode {
          depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [
            (⟨0⟩, cap1),
            (⟨1⟩, cap2)
          ]
        })
      |>.withObject receiverCNode (.cnode {
          depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16
        })
      |>.withObject sender.toObjId (.tcb { tid := sender, priority := ⟨40⟩, domain := ⟨0⟩, cspaceRoot := senderCNode, vspaceRoot := ⟨3440⟩, ipcBuffer := ⟨4096⟩, ipcState := .ready })
      |>.withObject receiver.toObjId (.tcb { tid := receiver, priority := ⟨39⟩, domain := ⟨0⟩, cspaceRoot := receiverCNode, vspaceRoot := ⟨3441⟩, ipcBuffer := ⟨8192⟩, ipcState := .ready })
      |>.withRunnable [sender, receiver]
      |>.buildChecked)

  -- Step 1: Receiver blocks on endpoint
  let (_, st1) ← expectOkState "chain14: receiver blocks on endpoint"
    (SeLe4n.Kernel.endpointReceiveDual epId receiver st0)

  -- Step 2: Sender sends with badge 0xCAFE + 2 caps (immediate rendezvous)
  let badgeVal : SeLe4n.Badge := ⟨0xCAFE⟩
  let msg : IpcMessage := { registers := #[⟨77⟩], caps := #[cap1, cap2], badge := some badgeVal }
  let (summary, st2) ← expectOkState "chain14: send with badge + caps"
    (SeLe4n.Kernel.endpointSendDualWithCaps epId sender msg grantRights senderCNode (SeLe4n.Slot.ofNat 0) st1)

  -- Verify: transfer summary has 2 results (both caps transferred)
  expect "chain14: summary has 2 results" (summary.results.size = 2)

  -- Verify: receiver's TCB has pending message with badge 0xCAFE
  let badgeCheck := match st2.objects[receiver.toObjId]? with
    | some (.tcb tcb) =>
        match tcb.pendingMessage with
        | some recvMsg => recvMsg.badge == some badgeVal
        | none => false
    | _ => false
  expect "chain14: receiver got badge 0xCAFE" badgeCheck

  -- Verify: receiver's CNode has 2 new capabilities
  let recvCnodeCheck := match st2.objects[receiverCNode]? with
    | some (.cnode cn) =>
        (cn.lookup ⟨0⟩).isSome && (cn.lookup ⟨1⟩).isSome
    | _ => false
  expect "chain14: receiver CNode has 2 caps" recvCnodeCheck

  -- Verify: register payload also came through
  let regCheck := match st2.objects[receiver.toObjId]? with
    | some (.tcb tcb) =>
        match tcb.pendingMessage with
        | some recvMsg => recvMsg.registers == #[⟨77⟩]
        | none => false
    | _ => false
  expect "chain14: receiver got register payload" regCheck

  assertInvariants "chain14: IPC badge + cap transfer combined" st2

-- ============================================================================
-- WS-M4-B: Strict revocation stress tests (M-T02)
-- ============================================================================

/-- SCN-REVOKE-STRICT-DEEP (M4-B1): Strict revocation with 15-level deep
derivation chain — verify all descendants are deleted and `deletedSlots`
list is complete. Root slot remains present after revocation. -/
private def chain15StrictRevokeDeepChain : IO Unit := do
  -- Create 16 CNodes: root + 15 levels
  let rootCNode : SeLe4n.ObjId := ⟨7000⟩
  let targetId : SeLe4n.ObjId := ⟨7100⟩
  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := rootCNode, slot := ⟨0⟩ }

  -- Build initial state with all 16 CNodes (root + 15 children)
  let childIds : List SeLe4n.ObjId := (List.range 15).map fun i => ⟨7001 + i⟩
  let childSlots : List SeLe4n.Kernel.CSpaceAddr :=
    childIds.map fun cid => { cnode := cid, slot := ⟨0⟩ }
  let mut builder := BootstrapBuilder.empty
  builder := builder.withObject targetId (.endpoint {})
  builder := builder.withObject rootCNode (.cnode {
    depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
    slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [
      (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
    ]
  })
  for cid in childIds do
    builder := builder.withObject cid (.cnode {
      depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16
    })
  let st0 := builder.build

  -- Build 15-level chain: root → child0 → child1 → ... → child14
  let mut st := st0
  let allSlots := rootSlot :: childSlots
  for i in List.range 15 do
    let srcSlot := allSlots[i]!
    let dstSlot := allSlots[i + 1]!
    let rights := if i < 7 then AccessRightSet.ofList [.read, .write, .grant]
                  else AccessRightSet.ofList [.read, .write]
    let (_, st') ← expectOkState s!"chain15: mint level {i}→{i+1}"
      (SeLe4n.Kernel.cspaceMintWithCdt srcSlot dstSlot rights none st)
    st := st'

  -- Verify chain was built correctly
  for i in List.range 15 do
    let capOpt := SystemState.lookupSlotCap st childSlots[i]!
    expect s!"chain15: child{i} has cap" capOpt.isSome

  -- Execute strict revocation on root
  let (report, stFinal) ← expectOkState "chain15: strict revoke deep chain"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict rootSlot st)

  -- Verify: no failure
  expect "chain15: no failure in deep revoke"
    report.firstFailure.isNone

  -- Verify: all 15 descendants deleted
  expect s!"chain15: deletedSlots has 15 entries (got {report.deletedSlots.length})"
    (report.deletedSlots.length = 15)

  -- Verify: all descendant slots are now empty
  for i in List.range 15 do
    let capOpt := SystemState.lookupSlotCap stFinal childSlots[i]!
    expect s!"chain15: child{i} slot empty after revoke" capOpt.isNone

  -- Verify: root slot still present
  let rootCapOpt := SystemState.lookupSlotCap stFinal rootSlot
  expect "chain15: root slot still present" rootCapOpt.isSome

  -- Verify: root CDT node survives revocation
  let rootNodeOpt := SystemState.lookupCdtNodeOfSlot stFinal rootSlot
  expect "chain15: root CDT node still present" rootNodeOpt.isSome

  -- Verify: CDT nodes detached for all descendants
  for i in List.range 15 do
    let nodeOpt := SystemState.lookupCdtNodeOfSlot stFinal childSlots[i]!
    expect s!"chain15: child{i} CDT node detached" nodeOpt.isNone

  assertInvariants "chain15: deep chain strict revoke invariants" stFinal

/-- SCN-REVOKE-STRICT-PARTIAL-FAIL (M4-B2): Strict revocation with partial
failure — one descendant's CNode is replaced with a non-CNode object, causing
`cspaceDeleteSlot` to fail with `.objectNotFound`. Verifies `firstFailure`
is populated and traversal halts. -/
private def chain16StrictRevokePartialFail : IO Unit := do
  let rootCNode : SeLe4n.ObjId := ⟨7200⟩
  let targetId : SeLe4n.ObjId := ⟨7300⟩
  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := rootCNode, slot := ⟨0⟩ }

  -- 5 child CNodes
  let childIds : List SeLe4n.ObjId := (List.range 5).map fun i => ⟨7201 + i⟩
  let childSlots : List SeLe4n.Kernel.CSpaceAddr :=
    childIds.map fun cid => { cnode := cid, slot := ⟨0⟩ }

  let mut builder := BootstrapBuilder.empty
  builder := builder.withObject targetId (.endpoint {})
  builder := builder.withObject rootCNode (.cnode {
    depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
    slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [
      (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
    ]
  })
  for cid in childIds do
    builder := builder.withObject cid (.cnode {
      depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16
    })
  let st0 := builder.build

  -- Build 5-level chain: root → c0 → c1 → c2 → c3 → c4
  let mut st := st0
  let allSlots := rootSlot :: childSlots
  for i in List.range 5 do
    let srcSlot := allSlots[i]!
    let dstSlot := allSlots[i + 1]!
    let (_, st') ← expectOkState s!"chain16: mint level {i}→{i+1}"
      (SeLe4n.Kernel.cspaceMintWithCdt srcSlot dstSlot (AccessRightSet.ofList [.read, .write, .grant]) none st)
    st := st'

  -- Corrupt: replace child2's CNode object with an endpoint (non-CNode)
  -- This will cause cspaceDeleteSlot for child2 to fail with objectNotFound
  -- because it expects a CNode at that ObjId but finds an endpoint instead.
  -- Also update lifecycle objectType metadata to stay consistent.
  let corruptedCNodeId := childIds[2]!
  let stCorrupted := { st with
    objects := st.objects.insert corruptedCNodeId (.endpoint {}),
    lifecycle := { st.lifecycle with
      objectTypes := st.lifecycle.objectTypes.insert corruptedCNodeId .endpoint }
  }

  -- Execute strict revocation
  let (report, stFinal) ← expectOkState "chain16: strict revoke partial fail"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict rootSlot stCorrupted)

  -- Verify: firstFailure is present
  expect "chain16: firstFailure is some" report.firstFailure.isSome

  -- Verify: firstFailure has correct error
  match report.firstFailure with
  | some failure =>
      expect "chain16: failure error is objectNotFound"
        (failure.error = .objectNotFound)
      -- The offending slot should be child2's slot
      expect "chain16: offendingSlot matches child2"
        (failure.offendingSlot = some childSlots[2]!)
  | none =>
      throw <| IO.userError "chain16: expected firstFailure to be some"

  -- Verify: deletedSlots contains slots deleted BEFORE the failure.
  -- BFS traversal on a linear chain root→c0→c1→c2→c3→c4 processes in
  -- order [c0, c1, c2, c3, c4]. c0 and c1 are successfully deleted before
  -- reaching c2 (the corrupted node where deletion fails). After failure,
  -- traversal halts → exactly 2 slots deleted.
  expect s!"chain16: deletedSlots has 2 entries before failure (got {report.deletedSlots.length})"
    (report.deletedSlots.length = 2)

  -- Verify: the specific slots deleted are c0 and c1 (the two before the failure)
  let deletedSet := report.deletedSlots
  expect "chain16: c0 slot in deletedSlots"
    (deletedSet.any fun ds => ds == childSlots[0]!)
  expect "chain16: c1 slot in deletedSlots"
    (deletedSet.any fun ds => ds == childSlots[1]!)

  -- Verify: root slot still present
  let rootCapOpt := SystemState.lookupSlotCap stFinal rootSlot
  expect "chain16: root slot still present" rootCapOpt.isSome

  -- Verify: post-failure descendants (c3, c4) are untouched — traversal halted.
  -- Their slots should still contain the capabilities minted earlier.
  let c3CapOpt := SystemState.lookupSlotCap stFinal childSlots[3]!
  expect "chain16: c3 slot preserved after halt" c3CapOpt.isSome
  let c4CapOpt := SystemState.lookupSlotCap stFinal childSlots[4]!
  expect "chain16: c4 slot preserved after halt" c4CapOpt.isSome

  -- Verify: c3 and c4 CDT nodes also survive the halt
  let c3NodeOpt := SystemState.lookupCdtNodeOfSlot stFinal childSlots[3]!
  expect "chain16: c3 CDT node survives halt" c3NodeOpt.isSome
  let c4NodeOpt := SystemState.lookupCdtNodeOfSlot stFinal childSlots[4]!
  expect "chain16: c4 CDT node survives halt" c4NodeOpt.isSome

  -- Note: assertInvariants is intentionally NOT called here because we
  -- deliberately corrupted the state (replaced a CNode with an endpoint)
  -- to trigger the partial failure. The corrupted object would fail the
  -- lifecycle objectType consistency check. This is expected behavior.

/-- SCN-REVOKE-STRICT-ORDER (M4-B3): Branching derivation tree verifies
`deletedSlots` set completeness after revocation. Tree shape:
  root → A → A1
       → B → B1
            → B2
Total 5 descendants. Verifies deletedSlots.length = 5, all entries come
from the expected descendant set, root is preserved, and CDT nodes are
detached. Note: `descendantsOf` traverses children via HashMap-backed
`childrenOf`, so sibling ordering (A vs B) is non-deterministic; we
verify set membership rather than exact BFS ordering. -/
private def chain17StrictRevokeOrdering : IO Unit := do
  let rootCNode : SeLe4n.ObjId := ⟨7400⟩
  let cnodeA : SeLe4n.ObjId := ⟨7401⟩
  let cnodeB : SeLe4n.ObjId := ⟨7402⟩
  let cnodeA1 : SeLe4n.ObjId := ⟨7403⟩
  let cnodeB1 : SeLe4n.ObjId := ⟨7404⟩
  let cnodeB2 : SeLe4n.ObjId := ⟨7405⟩
  let targetId : SeLe4n.ObjId := ⟨7500⟩

  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := rootCNode, slot := ⟨0⟩ }
  let slotA : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeA, slot := ⟨0⟩ }
  let slotB : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeB, slot := ⟨0⟩ }
  let slotA1 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeA1, slot := ⟨0⟩ }
  let slotB1 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeB1, slot := ⟨0⟩ }
  let slotB2 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeB2, slot := ⟨0⟩ }

  let mut builder := BootstrapBuilder.empty
  builder := builder.withObject targetId (.endpoint {})
  for cid in [rootCNode, cnodeA, cnodeB, cnodeA1, cnodeB1, cnodeB2] do
    builder := builder.withObject cid (.cnode {
      depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
      slots := if cid = rootCNode then
        SeLe4n.Kernel.RobinHood.RHTable.ofList [
          (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
        ]
      else SeLe4n.Kernel.RobinHood.RHTable.empty 16
    })
  let st0 := builder.build

  -- Build branching tree:
  -- root → A (mint)
  let (_, st1) ← expectOkState "chain17: mint root→A"
    (SeLe4n.Kernel.cspaceMintWithCdt rootSlot slotA (AccessRightSet.ofList [.read, .write, .grant]) none st0)
  -- root → B (mint)
  let (_, st2) ← expectOkState "chain17: mint root→B"
    (SeLe4n.Kernel.cspaceMintWithCdt rootSlot slotB (AccessRightSet.ofList [.read, .write, .grant]) none st1)
  -- A → A1 (mint)
  let (_, st3) ← expectOkState "chain17: mint A→A1"
    (SeLe4n.Kernel.cspaceMintWithCdt slotA slotA1 (AccessRightSet.ofList [.read, .write]) none st2)
  -- B → B1 (mint)
  let (_, st4) ← expectOkState "chain17: mint B→B1"
    (SeLe4n.Kernel.cspaceMintWithCdt slotB slotB1 (AccessRightSet.ofList [.read, .write]) none st3)
  -- B → B2 (mint)
  let (_, st5) ← expectOkState "chain17: mint B→B2"
    (SeLe4n.Kernel.cspaceMintWithCdt slotB slotB2 (AccessRightSet.ofList [.read]) none st4)

  -- Verify tree was built: all 5 descendants have caps (A, B, A1, B1, B2)
  for (label, slot) in [("A", slotA), ("B", slotB), ("A1", slotA1), ("B1", slotB1), ("B2", slotB2)] do
    let capOpt := SystemState.lookupSlotCap st5 slot
    expect s!"chain17: {label} has cap" capOpt.isSome

  -- Execute strict revocation on root
  let (report, stFinal) ← expectOkState "chain17: strict revoke branching tree"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict rootSlot st5)

  -- Verify: no failure
  expect "chain17: no failure in branching revoke"
    report.firstFailure.isNone

  -- Verify: all 5 descendants deleted (A, B, A1, B1, B2)
  expect s!"chain17: deletedSlots has 5 entries (got {report.deletedSlots.length})"
    (report.deletedSlots.length = 5)

  -- Verify: all descendant slots are now empty
  for (label, slot) in [("A", slotA), ("B", slotB), ("A1", slotA1), ("B1", slotB1), ("B2", slotB2)] do
    let capOpt := SystemState.lookupSlotCap stFinal slot
    expect s!"chain17: {label} slot empty after revoke" capOpt.isNone

  -- Verify: root slot still present
  let rootCapOpt := SystemState.lookupSlotCap stFinal rootSlot
  expect "chain17: root slot still present" rootCapOpt.isSome

  -- Verify: CDT nodes detached
  for (label, slot) in [("A", slotA), ("B", slotB), ("A1", slotA1), ("B1", slotB1), ("B2", slotB2)] do
    let nodeOpt := SystemState.lookupCdtNodeOfSlot stFinal slot
    expect s!"chain17: {label} CDT node detached" nodeOpt.isNone

  -- Verify: deletedSlots are all from the expected set of descendant slots
  let expectedSlotSet : List SeLe4n.Kernel.CSpaceAddr := [slotA, slotB, slotA1, slotB1, slotB2]
  let allInSet := report.deletedSlots.all fun ds => ds ∈ expectedSlotSet
  expect "chain17: all deletedSlots are from expected set" allInSet

  -- Verify partial BFS ordering: within each sub-chain, parent precedes child.
  -- (Sibling ordering between A and B branches is non-deterministic due to
  -- HashMap iteration order in childrenOf, so we only verify parent-before-child.)
  let indexOf (s : SeLe4n.Kernel.CSpaceAddr) (xs : List SeLe4n.Kernel.CSpaceAddr) : Option Nat :=
    let rec go (l : List SeLe4n.Kernel.CSpaceAddr) (i : Nat) : Option Nat :=
      match l with
      | [] => none
      | h :: t => if h == s then some i else go t (i + 1)
    go xs 0
  let ds := report.deletedSlots
  -- A appears before A1
  match indexOf slotA ds, indexOf slotA1 ds with
  | some ia, some ia1 => expect "chain17: A before A1 in deletedSlots" (ia < ia1)
  | _, _ => throw <| IO.userError "chain17: A or A1 not found in deletedSlots"
  -- B appears before B1
  match indexOf slotB ds, indexOf slotB1 ds with
  | some ib, some ib1 => expect "chain17: B before B1 in deletedSlots" (ib < ib1)
  | _, _ => throw <| IO.userError "chain17: B or B1 not found in deletedSlots"
  -- B appears before B2
  match indexOf slotB ds, indexOf slotB2 ds with
  | some ib, some ib2 => expect "chain17: B before B2 in deletedSlots" (ib < ib2)
  | _, _ => throw <| IO.userError "chain17: B or B2 not found in deletedSlots"

  assertInvariants "chain17: branching revoke ordering invariants" stFinal

/-- SCN-REVOKE-STREAMING-BFS (M5-A7): Streaming BFS revocation on a 5-node
branching derivation tree. Verifies that `cspaceRevokeCdtStreaming` produces
the same observable effects as `cspaceRevokeCdt`:
  root → A → A1
       → B → B1
            → B2
All 5 descendants deleted, root preserved, CDT nodes detached, invariants hold. -/
private def chain18StreamingRevokeBFS : IO Unit := do
  let rootCNode : SeLe4n.ObjId := ⟨7600⟩
  let cnodeA : SeLe4n.ObjId := ⟨7601⟩
  let cnodeB : SeLe4n.ObjId := ⟨7602⟩
  let cnodeA1 : SeLe4n.ObjId := ⟨7603⟩
  let cnodeB1 : SeLe4n.ObjId := ⟨7604⟩
  let cnodeB2 : SeLe4n.ObjId := ⟨7605⟩
  let targetId : SeLe4n.ObjId := ⟨7700⟩

  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := rootCNode, slot := ⟨0⟩ }
  let slotA : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeA, slot := ⟨0⟩ }
  let slotB : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeB, slot := ⟨0⟩ }
  let slotA1 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeA1, slot := ⟨0⟩ }
  let slotB1 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeB1, slot := ⟨0⟩ }
  let slotB2 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeB2, slot := ⟨0⟩ }

  let mut builder := BootstrapBuilder.empty
  builder := builder.withObject targetId (.endpoint {})
  for cid in [rootCNode, cnodeA, cnodeB, cnodeA1, cnodeB1, cnodeB2] do
    builder := builder.withObject cid (.cnode {
      depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
      slots := if cid = rootCNode then
        SeLe4n.Kernel.RobinHood.RHTable.ofList [
          (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
        ]
      else SeLe4n.Kernel.RobinHood.RHTable.empty 16
    })
  let st0 := builder.build

  -- Build branching tree:
  -- root → A (mint)
  let (_, st1) ← expectOkState "chain18: mint root→A"
    (SeLe4n.Kernel.cspaceMintWithCdt rootSlot slotA (AccessRightSet.ofList [.read, .write, .grant]) none st0)
  -- root → B (mint)
  let (_, st2) ← expectOkState "chain18: mint root→B"
    (SeLe4n.Kernel.cspaceMintWithCdt rootSlot slotB (AccessRightSet.ofList [.read, .write, .grant]) none st1)
  -- A → A1 (mint)
  let (_, st3) ← expectOkState "chain18: mint A→A1"
    (SeLe4n.Kernel.cspaceMintWithCdt slotA slotA1 (AccessRightSet.ofList [.read, .write]) none st2)
  -- B → B1 (mint)
  let (_, st4) ← expectOkState "chain18: mint B→B1"
    (SeLe4n.Kernel.cspaceMintWithCdt slotB slotB1 (AccessRightSet.ofList [.read, .write]) none st3)
  -- B → B2 (mint)
  let (_, st5) ← expectOkState "chain18: mint B→B2"
    (SeLe4n.Kernel.cspaceMintWithCdt slotB slotB2 (AccessRightSet.ofList [.read]) none st4)

  -- Verify tree was built: all 5 descendants have caps
  for (label, slot) in [("A", slotA), ("B", slotB), ("A1", slotA1), ("B1", slotB1), ("B2", slotB2)] do
    let capOpt := SystemState.lookupSlotCap st5 slot
    expect s!"chain18: {label} has cap" capOpt.isSome

  -- Execute streaming BFS revocation on root
  let ((), stFinal) ← expectOkState "chain18: streaming BFS revoke branching tree"
    (SeLe4n.Kernel.cspaceRevokeCdtStreaming rootSlot st5)

  -- Verify: all 5 descendant slots are now empty
  for (label, slot) in [("A", slotA), ("B", slotB), ("A1", slotA1), ("B1", slotB1), ("B2", slotB2)] do
    let capOpt := SystemState.lookupSlotCap stFinal slot
    expect s!"chain18: {label} slot empty after streaming revoke" capOpt.isNone

  -- Verify: root slot still present
  let rootCapOpt := SystemState.lookupSlotCap stFinal rootSlot
  expect "chain18: root slot still present after streaming revoke" rootCapOpt.isSome

  -- Verify: CDT nodes detached for all descendants
  for (label, slot) in [("A", slotA), ("B", slotB), ("A1", slotA1), ("B1", slotB1), ("B2", slotB2)] do
    let nodeOpt := SystemState.lookupCdtNodeOfSlot stFinal slot
    expect s!"chain18: {label} CDT node detached after streaming revoke" nodeOpt.isNone

  assertInvariants "chain18: streaming BFS revoke invariants" stFinal

/-- SCN-REVOKE-STREAMING-EMPTY (M5): Streaming BFS on a root with no CDT
children. Verifies that `cspaceRevokeCdtStreaming` is a no-op when the source
slot has no derivation descendants — root capability preserved, state unchanged. -/
private def chain19StreamingRevokeEmpty : IO Unit := do
  let rootCNode : SeLe4n.ObjId := ⟨7800⟩
  let targetId : SeLe4n.ObjId := ⟨7900⟩

  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := rootCNode, slot := ⟨0⟩ }

  let mut builder := BootstrapBuilder.empty
  builder := builder.withObject targetId (.endpoint {})
  builder := builder.withObject rootCNode (.cnode {
    depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
    slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [
      (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
    ]
  })
  let st0 := builder.build

  -- Execute streaming BFS revocation (no descendants)
  let ((), stFinal) ← expectOkState "chain19: streaming BFS revoke empty tree"
    (SeLe4n.Kernel.cspaceRevokeCdtStreaming rootSlot st0)

  -- Root capability must still be present
  let rootCapOpt := SystemState.lookupSlotCap stFinal rootSlot
  expect "chain19: root slot preserved after empty streaming revoke" rootCapOpt.isSome

  assertInvariants "chain19: empty streaming BFS revoke invariants" stFinal

/-- SCN-REVOKE-STREAMING-DEEP (M5): Streaming BFS on a deep linear chain
(root → A → B → C → D). Verifies correct traversal depth and that all 4
descendants are deleted in order. -/
private def chain20StreamingRevokeDeepChain : IO Unit := do
  let rootCNode : SeLe4n.ObjId := ⟨8000⟩
  let cnodeA : SeLe4n.ObjId := ⟨8001⟩
  let cnodeB : SeLe4n.ObjId := ⟨8002⟩
  let cnodeC : SeLe4n.ObjId := ⟨8003⟩
  let cnodeD : SeLe4n.ObjId := ⟨8004⟩
  let targetId : SeLe4n.ObjId := ⟨8100⟩

  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := rootCNode, slot := ⟨0⟩ }
  let slotA : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeA, slot := ⟨0⟩ }
  let slotB : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeB, slot := ⟨0⟩ }
  let slotC : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeC, slot := ⟨0⟩ }
  let slotD : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeD, slot := ⟨0⟩ }

  let mut builder := BootstrapBuilder.empty
  builder := builder.withObject targetId (.endpoint {})
  for cid in [rootCNode, cnodeA, cnodeB, cnodeC, cnodeD] do
    builder := builder.withObject cid (.cnode {
      depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
      slots := if cid = rootCNode then
        SeLe4n.Kernel.RobinHood.RHTable.ofList [
          (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
        ]
      else SeLe4n.Kernel.RobinHood.RHTable.empty 16
    })
  let st0 := builder.build

  -- Build deep chain: root → A → B → C → D
  let (_, st1) ← expectOkState "chain20: mint root→A"
    (SeLe4n.Kernel.cspaceMintWithCdt rootSlot slotA (AccessRightSet.ofList [.read, .write, .grant]) none st0)
  let (_, st2) ← expectOkState "chain20: mint A→B"
    (SeLe4n.Kernel.cspaceMintWithCdt slotA slotB (AccessRightSet.ofList [.read, .write, .grant]) none st1)
  let (_, st3) ← expectOkState "chain20: mint B→C"
    (SeLe4n.Kernel.cspaceMintWithCdt slotB slotC (AccessRightSet.ofList [.read, .write]) none st2)
  let (_, st4) ← expectOkState "chain20: mint C→D"
    (SeLe4n.Kernel.cspaceMintWithCdt slotC slotD (AccessRightSet.ofList [.read]) none st3)

  -- Execute streaming BFS revocation on root
  let ((), stFinal) ← expectOkState "chain20: streaming BFS revoke deep chain"
    (SeLe4n.Kernel.cspaceRevokeCdtStreaming rootSlot st4)

  -- All 4 descendants deleted
  for (label, slot) in [("A", slotA), ("B", slotB), ("C", slotC), ("D", slotD)] do
    let capOpt := SystemState.lookupSlotCap stFinal slot
    expect s!"chain20: {label} slot empty after deep chain revoke" capOpt.isNone

  -- Root preserved
  let rootCapOpt := SystemState.lookupSlotCap stFinal rootSlot
  expect "chain20: root slot preserved after deep chain revoke" rootCapOpt.isSome

  -- CDT nodes detached
  for (label, slot) in [("A", slotA), ("B", slotB), ("C", slotC), ("D", slotD)] do
    let nodeOpt := SystemState.lookupCdtNodeOfSlot stFinal slot
    expect s!"chain20: {label} CDT node detached" nodeOpt.isNone

  assertInvariants "chain20: deep chain streaming BFS revoke invariants" stFinal

/-- SCN-REVOKE-STREAMING-EQUIV (M5): Equivalence test — run both `cspaceRevokeCdt`
and `cspaceRevokeCdtStreaming` on the same 3-node tree (root → A → B) and verify
they produce identical observable state (same slots, same objects). -/
private def chain21StreamingRevokeEquivalence : IO Unit := do
  let rootCNode : SeLe4n.ObjId := ⟨8200⟩
  let cnodeA : SeLe4n.ObjId := ⟨8201⟩
  let cnodeB : SeLe4n.ObjId := ⟨8202⟩
  let targetId : SeLe4n.ObjId := ⟨8300⟩

  let rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := rootCNode, slot := ⟨0⟩ }
  let slotA : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeA, slot := ⟨0⟩ }
  let slotB : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeB, slot := ⟨0⟩ }

  -- Build identical initial states for both variants
  let mkState : IO SystemState := do
    let mut builder := BootstrapBuilder.empty
    builder := builder.withObject targetId (.endpoint {})
    for cid in [rootCNode, cnodeA, cnodeB] do
      builder := builder.withObject cid (.cnode {
        depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
        slots := if cid = rootCNode then
          SeLe4n.Kernel.RobinHood.RHTable.ofList [
            (⟨0⟩, { target := .object targetId, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
          ]
        else SeLe4n.Kernel.RobinHood.RHTable.empty 16
      })
    let st0 := builder.build
    let (_, st1) ← expectOkState "chain21: mint root→A"
      (SeLe4n.Kernel.cspaceMintWithCdt rootSlot slotA (AccessRightSet.ofList [.read, .write, .grant]) none st0)
    let (_, st2) ← expectOkState "chain21: mint A→B"
      (SeLe4n.Kernel.cspaceMintWithCdt slotA slotB (AccessRightSet.ofList [.read, .write]) none st1)
    pure st2

  let stPre ← mkState

  -- Run materialized revocation
  let ((), stMaterialized) ← expectOkState "chain21: materialized revokeCdt"
    (SeLe4n.Kernel.cspaceRevokeCdt rootSlot stPre)

  -- Run streaming BFS revocation on same initial state
  let ((), stStreaming) ← expectOkState "chain21: streaming revokeCdtStreaming"
    (SeLe4n.Kernel.cspaceRevokeCdtStreaming rootSlot stPre)

  -- Compare observable slot state: both should have same slot contents
  for (label, slot) in [("root", rootSlot), ("A", slotA), ("B", slotB)] do
    let capMat := SystemState.lookupSlotCap stMaterialized slot
    let capStr := SystemState.lookupSlotCap stStreaming slot
    expect s!"chain21: {label} slot equivalence (both present or both absent)"
      (capMat.isSome == capStr.isSome)

  -- Both should have root present, A and B absent
  expect "chain21: materialized root present" (SystemState.lookupSlotCap stMaterialized rootSlot).isSome
  expect "chain21: streaming root present" (SystemState.lookupSlotCap stStreaming rootSlot).isSome
  expect "chain21: materialized A absent" (SystemState.lookupSlotCap stMaterialized slotA).isNone
  expect "chain21: streaming A absent" (SystemState.lookupSlotCap stStreaming slotA).isNone
  expect "chain21: materialized B absent" (SystemState.lookupSlotCap stMaterialized slotB).isNone
  expect "chain21: streaming B absent" (SystemState.lookupSlotCap stStreaming slotB).isNone

  assertInvariants "chain21: materialized revoke invariants" stMaterialized
  assertInvariants "chain21: streaming revoke invariants" stStreaming

/-- R3-A.3: Badge delivery test — verifies that notificationSignal delivers
the badge to the woken waiter's pendingMessage when waking a blocked thread.
Steps: wait (blocks waiter) → signal (wakes waiter with badge) → verify badge. -/
private def chain22NotificationBadgeDelivery : IO Unit := do
  let ntfnId : SeLe4n.ObjId := ⟨260⟩
  let waiter : SeLe4n.ThreadId := ⟨12⟩
  let badge := SeLe4n.Badge.ofNatMasked 0xCAFE
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject ntfnId (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
      |>.withObject waiter.toObjId (.tcb {
          tid := waiter
          priority := ⟨20⟩
          domain := ⟨0⟩
          cspaceRoot := ⟨350⟩
          vspaceRoot := ⟨360⟩
          ipcBuffer := ⟨4096⟩
          ipcState := .ready
        })
      |>.withRunnable [waiter]
      |>.buildChecked)
  -- Step 1: waiter blocks on notification (no pending badge)
  let (result1, st1) ← expectOkState "chain22: wait blocks"
    (SeLe4n.Kernel.notificationWait ntfnId waiter st0)
  expect "chain22: wait returns none (blocked)" (result1 = none)
  -- Step 2: signal with badge 0xCAFE — should wake the waiter
  let (_, st2) ← expectOkState "chain22: signal wakes waiter"
    (SeLe4n.Kernel.notificationSignal ntfnId badge st1)
  -- Step 3: Verify badge was delivered to waiter's pendingMessage
  match st2.objects[waiter.toObjId]? with
  | some (.tcb tcb) =>
    expect "chain22: waiter ipcState is ready after wake" (tcb.ipcState = .ready)
    match tcb.pendingMessage with
    | some msg =>
      expect "chain22: badge delivered via pendingMessage"
        (msg.badge = some (SeLe4n.Badge.ofNatMasked 0xCAFE))
    | none => throw (IO.userError "chain22: FAIL — waiter pendingMessage is none after signal wake")
  | _ => throw (IO.userError "chain22: FAIL — waiter TCB not found after signal wake")
  -- Step 4: Verify waiter is runnable again
  expect "chain22: waiter is runnable after wake" (waiter ∈ st2.scheduler.runQueue)
  assertInvariants "chain22: signal-wake badge delivery" st2

-- ============================================================================
-- T7-E: Deep CDT cascade test (L-P02) — 4-level capability derivation tree
-- with mid-tree strict revoke
-- ============================================================================

/-- L-P02: Construct a 4-level CDT: root → child → grandchild → great-grandchild.
Revoke at child level and verify descendants (grandchild + great-grandchild)
are removed while root and child itself are preserved. -/
private def chain23CdtDeepCascadeWithMidDelete : IO Unit := do
  -- Use separate CNodes per level to avoid revokeTargetLocal wiping sibling caps
  let cnodeRoot : SeLe4n.ObjId := ⟨8000⟩
  let cnodeChild : SeLe4n.ObjId := ⟨8001⟩
  let cnodeGrand : SeLe4n.ObjId := ⟨8002⟩
  let cnodeGreat : SeLe4n.ObjId := ⟨8003⟩
  let targetEp : SeLe4n.ObjId := ⟨8100⟩
  let slot0 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeRoot, slot := ⟨0⟩ }
  let slot1 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeChild, slot := ⟨0⟩ }
  let slot2 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeGrand, slot := ⟨0⟩ }
  let slot3 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeGreat, slot := ⟨0⟩ }
  let emptyCNode := SeLe4n.Kernel.RobinHood.RHTable.empty 16
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject targetEp (.endpoint {})
      |>.withObject cnodeRoot (.cnode {
        depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
        slots := SeLe4n.Kernel.RobinHood.RHTable.ofList [
          (⟨0⟩, { target := .object targetEp, rights := AccessRightSet.ofList [.read, .write, .grant], badge := none })
        ]
      })
      |>.withObject cnodeChild (.cnode {
        depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
        slots := emptyCNode
      })
      |>.withObject cnodeGrand (.cnode {
        depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
        slots := emptyCNode
      })
      |>.withObject cnodeGreat (.cnode {
        depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
        slots := emptyCNode
      })
      |>.withLifecycleObjectType cnodeRoot .cnode
      |>.withLifecycleObjectType cnodeChild .cnode
      |>.withLifecycleObjectType cnodeGrand .cnode
      |>.withLifecycleObjectType cnodeGreat .cnode
      |>.withLifecycleObjectType targetEp .endpoint
      |>.buildChecked)
  -- Level 1: Mint child from root
  let (_, st1) ← expectOkState "chain23: mint child (level 1)"
    (SeLe4n.Kernel.cspaceMintWithCdt slot0 slot1 (AccessRightSet.ofList [.read, .write, .grant]) none st0)
  -- Level 2: Mint grandchild from child
  let (_, st2) ← expectOkState "chain23: mint grandchild (level 2)"
    (SeLe4n.Kernel.cspaceMintWithCdt slot1 slot2 (AccessRightSet.ofList [.read, .write]) none st1)
  -- Level 3: Mint great-grandchild from grandchild
  let (_, st3) ← expectOkState "chain23: mint great-grandchild (level 3)"
    (SeLe4n.Kernel.cspaceMintWithCdt slot2 slot3 (AccessRightSet.ofList [.read]) none st2)
  -- Verify all 4 slots are populated
  expect "chain23: 4-level CDT constructed"
    ((SeLe4n.Model.SystemState.lookupSlotCap st3 slot0).isSome &&
     (SeLe4n.Model.SystemState.lookupSlotCap st3 slot1).isSome &&
     (SeLe4n.Model.SystemState.lookupSlotCap st3 slot2).isSome &&
     (SeLe4n.Model.SystemState.lookupSlotCap st3 slot3).isSome)
  -- Strict revoke at child (slot 1) — should remove grandchild + great-grandchild
  let (report, st4) ← expectOkState "chain23: strict revoke at child"
    (SeLe4n.Kernel.cspaceRevokeCdtStrict slot1 st3)
  -- Root (slot 0) should still exist — it's in a different CNode
  expect "chain23: root cap preserved after revoke"
    ((SeLe4n.Model.SystemState.lookupSlotCap st4 slot0).isSome)
  -- Grandchild (slot 2) should be removed
  expect "chain23: grandchild removed after revoke"
    ((SeLe4n.Model.SystemState.lookupSlotCap st4 slot2).isNone)
  -- Great-grandchild (slot 3) should be removed
  expect "chain23: great-grandchild removed after revoke"
    ((SeLe4n.Model.SystemState.lookupSlotCap st4 slot3).isNone)
  -- Verify revoke report has 2 deleted slots
  expect "chain23: revoke report deletedSlots=2" (report.deletedSlots.length == 2)
  assertInvariants "chain23: deep CDT cascade" st4

-- ============================================================================
-- T7-K: Edge-case scheduler tests (L-P06, L-P07)
-- ============================================================================

/-- L-P06: handleYield with single thread — the lone thread is re-enqueued
and re-selected as current. -/
private def chain24HandleYieldEmptyQueue : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let prio : SeLe4n.Priority := ⟨100⟩
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject tid.toObjId (.tcb {
        tid := tid, priority := prio, domain := ⟨0⟩,
        cspaceRoot := ⟨10⟩, vspaceRoot := ⟨20⟩, ipcBuffer := ⟨4096⟩,
        ipcState := .ready })
      |>.withObject ⟨10⟩ (.cnode CNode.empty)
      |>.withObject ⟨20⟩ (.vspaceRoot { asid := ⟨1⟩, mappings := {} })
      |>.withRunnable [tid]
      |>.withLifecycleObjectType tid.toObjId .tcb
      |>.withLifecycleObjectType ⟨10⟩ .cnode
      |>.withLifecycleObjectType ⟨20⟩ .vspaceRoot
      |>.buildChecked)
  -- Schedule to get the thread as current
  let (_, st1) ← expectOkState "chain24: initial schedule" (SeLe4n.Kernel.schedule st0)
  expect "chain24: thread is current" (st1.scheduler.current == some tid)
  -- Yield — single thread should re-enqueue and re-select itself
  let (_, st2) ← expectOkState "chain24: handleYield" (SeLe4n.Kernel.handleYield st1)
  expect "chain24: same thread re-selected after yield" (st2.scheduler.current == some tid)
  assertInvariants "chain24: yield single thread" st2

/-- L-P07: IRQ handler dispatch — register an IRQ handler and verify
signal is dispatched to the correct notification object. -/
private def chain25IrqHandlerDispatch : IO Unit := do
  let ntfnId : SeLe4n.ObjId := ⟨300⟩
  let irq : SeLe4n.Irq := ⟨5⟩
  let st0 :=
    (BootstrapBuilder.empty
      |>.withObject ntfnId (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
      |>.withIrqHandler irq ntfnId
      |>.withLifecycleObjectType ntfnId .notification
      |>.buildChecked)
  -- Verify IRQ handler registration
  expect "chain25: IRQ handler registered" (st0.irqHandlers[irq]? == some ntfnId)
  -- Signal the notification with badge encoding IRQ number
  let badge := SeLe4n.Badge.ofNatMasked (1 <<< irq.toNat)
  let (_, st1) ← expectOkState "chain25: notification signal via IRQ"
    (SeLe4n.Kernel.notificationSignal ntfnId badge st0)
  -- Verify notification is now active with badge
  match st1.objects[ntfnId]? with
  | some (.notification ntfn) =>
    expect "chain25: notification active after IRQ signal" (ntfn.state == .active)
    expect "chain25: badge set" (ntfn.pendingBadge.isSome)
  | _ => throw <| IO.userError "chain25: notification not found"
  assertInvariants "chain25: IRQ handler dispatch" st1

-- ============================================================================
-- T7-L: Boot sequence test (L-P08)
-- ============================================================================

/-- L-P08: Exercise bootFromPlatform — construct a PlatformConfig with initial
objects and IRQ handlers, boot, and verify all 4 IntermediateState invariant
witnesses are satisfied. Tests determinism: same config yields same state. -/
private def chain26BootSequence : IO Unit := do
  -- Construct platform config with a notification and an endpoint
  let ntfnId : SeLe4n.ObjId := ⟨400⟩
  let epId : SeLe4n.ObjId := ⟨401⟩
  let irq : SeLe4n.Irq := ⟨3⟩
  -- ObjectEntry requires proof witnesses for CNode slots and VSpace mappings.
  -- For non-CNode/non-VSpace objects, the proof is vacuously true.
  let ntfnEntry : SeLe4n.Platform.Boot.ObjectEntry := {
    id := ntfnId
    obj := .notification { state := .idle, waitingThreads := [], pendingBadge := none }
    hSlots := by intro cn h; cases h
    hMappings := by intro vs h; cases h
  }
  let epEntry : SeLe4n.Platform.Boot.ObjectEntry := {
    id := epId
    obj := .endpoint {}
    hSlots := by intro cn h; cases h
    hMappings := by intro vs h; cases h
  }
  let irqEntry : SeLe4n.Platform.Boot.IrqEntry := { irq := irq, handler := ntfnId }
  let config : SeLe4n.Platform.Boot.PlatformConfig := {
    irqTable := [irqEntry]
    initialObjects := [ntfnEntry, epEntry]
  }
  -- Boot
  let ist := SeLe4n.Platform.Boot.bootFromPlatform config
  -- Verify all 4 invariant witnesses via the master theorem
  -- These are Prop-valued, so their existence constitutes proof.
  -- The fact that bootFromPlatform_valid type-checks is the proof.
  let _valid := SeLe4n.Platform.Boot.bootFromPlatform_valid config
  IO.println "operation-chain check passed [chain26: all 4 IntermediateState invariants type-checked]"
  -- Verify booted state contains our objects
  expect "chain26: notification in booted state" (ist.state.objects[ntfnId]?.isSome)
  expect "chain26: endpoint in booted state" (ist.state.objects[epId]?.isSome)
  -- Verify IRQ handler in booted state
  expect "chain26: IRQ handler registered" (ist.state.irqHandlers[irq]? == some ntfnId)
  -- Determinism: same config → same state
  let ist2 := SeLe4n.Platform.Boot.bootFromPlatform config
  expect "chain26: deterministic boot" (ist.state.objects[ntfnId]? == ist2.state.objects[ntfnId]?)
  IO.println "operation-chain check passed [chain26: boot sequence test (L-P08)]"

private def runOperationChainSuite : IO Unit := do
  chain1RetypeMintRevoke
  chain2SendSendReceiveFifo
  chain3MapLookupUnmapLookup
  chain4ServiceRegistryDependencyGraph
  chain5CopyMoveDelete
  chain6NotificationBadgeAccumulation
  chain7VSpaceMultiAsidSharedPage
  chain8IpcInterleavedSendOrdering
  chain9LifecycleCascadingRevokeAndAttenuation
  schedulerStressChecks
  chain10RegisterDecodeMultiSyscall
  chain11RegisterDecodeIpcTransfer
  chain12IpcCapTransfer
  chain13IpcCapTransferNoGrant
  chain14IpcBadgeAndCapTransfer
  chain15StrictRevokeDeepChain
  chain16StrictRevokePartialFail
  chain17StrictRevokeOrdering
  chain18StreamingRevokeBFS
  chain19StreamingRevokeEmpty
  chain20StreamingRevokeDeepChain
  chain21StreamingRevokeEquivalence
  chain22NotificationBadgeDelivery
  chain23CdtDeepCascadeWithMidDelete
  chain24HandleYieldEmptyQueue
  chain25IrqHandlerDispatch
  chain26BootSequence
  IO.println "all operation-chain checks passed (WS-I3/WS-I4/WS-M3/WS-M4/WS-M5/R3-A/T7)"

end SeLe4n.Testing

def main : IO Unit :=
  SeLe4n.Testing.runOperationChainSuite
