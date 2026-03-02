import SeLe4n
import SeLe4n.Testing.RuntimeContractFixtures
import SeLe4n.Testing.StateBuilder
import SeLe4n.Testing.InvariantChecks

open SeLe4n.Model

namespace SeLe4n.Testing

/-- WS-G4: Helper to build a RunQueue from a list of ThreadIds with default priority 0. -/
private def mkRunQueue (tids : List SeLe4n.ThreadId) : SeLe4n.Kernel.RunQueue :=
  SeLe4n.Kernel.RunQueue.ofList (tids.map (fun tid => (tid, ⟨0⟩)))

def rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 0 }
def rootPath : SeLe4n.Kernel.CSpacePathAddr := { cnode := 10, cptr := 0, depth := 0 }
def rootPathAlias : SeLe4n.Kernel.CSpacePathAddr := { cnode := 10, cptr := 1, depth := 0 }
def lifecycleAuthSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 5 }
def mintedSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 11, slot := 3 }
def siblingSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 11, slot := 4 }
def demoEndpoint : SeLe4n.ObjId := 30
def demoNotification : SeLe4n.ObjId := 31
def demoUntyped : SeLe4n.ObjId := 40
def untypedAuthSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 6 }

def svcDb : ServiceId := 100
def svcApi : ServiceId := 101
def svcDenied : ServiceId := 102
def svcBroken : ServiceId := 103
def svcRestart : ServiceId := 104
def svcRestartBroken : ServiceId := 105

def bootstrapInvariantObjectIds : List SeLe4n.ObjId :=
  [1, 10, 11, 12, 20, demoEndpoint, demoNotification, demoUntyped]

def bootstrapServiceIds : List ServiceId :=
  [svcDb, svcApi, svcDenied, svcBroken, svcRestart, svcRestartBroken]

def bootstrapState : SystemState :=
  (SeLe4n.Testing.BootstrapBuilder.empty
    |>.withObject 1 (.tcb {
      tid := 1
      priority := 100
      domain := 0
      cspaceRoot := 10
      vspaceRoot := 20
      ipcBuffer := 4096
      ipcState := .ready
    })
    |>.withObject 10 (.cnode {
      guard := 0
      radix := 0
      slots := Std.HashMap.ofList
        [ (0, {
            target := .object 1
            rights := [.read, .write, .grant]
            badge := none
          }),
          (5, {
            target := .object 12
            rights := [.read, .write]
            badge := none
          }),
          (6, {
            target := .object demoUntyped
            rights := [.read, .write]
            badge := none
          }) ]
    })
    |>.withObject 12 (.tcb {
      tid := 12
      priority := 10
      domain := 0
      cspaceRoot := 10
      vspaceRoot := 20
      ipcBuffer := 8192
      ipcState := .ready
    })
    |>.withObject 11 (.cnode CNode.empty)
    |>.withObject 20 (.vspaceRoot { asid := 1, mappings := {} })
    |>.withObject demoEndpoint (.endpoint { state := .idle, queue := [], waitingReceiver := none })
    |>.withObject demoNotification (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
    |>.withObject demoUntyped (.untyped {
      regionBase := 0x100000
      regionSize := 16384
      watermark := 0
      children := []
      isDevice := false
    })
    |>.withService svcDb {
      identity := { sid := svcDb, backingObject := 12, owner := 10 }
      status := .running
      dependencies := []
      isolatedFrom := []
    }
    |>.withService svcApi {
      identity := { sid := svcApi, backingObject := 1, owner := 10 }
      status := .stopped
      dependencies := [svcDb]
      isolatedFrom := [svcDenied]
    }
    |>.withService svcDenied {
      identity := { sid := svcDenied, backingObject := 1, owner := 10 }
      status := .stopped
      dependencies := []
      isolatedFrom := []
    }
    |>.withService svcBroken {
      identity := { sid := svcBroken, backingObject := 1, owner := 10 }
      status := .stopped
      dependencies := [999]
      isolatedFrom := []
    }
    |>.withService svcRestart {
      identity := { sid := svcRestart, backingObject := 12, owner := 10 }
      status := .running
      dependencies := [svcDb]
      isolatedFrom := []
    }
    |>.withService svcRestartBroken {
      identity := { sid := svcRestartBroken, backingObject := 12, owner := 10 }
      status := .running
      dependencies := [999]
      isolatedFrom := []
    }
    |>.withRunnable [1, 12]
    |>.withLifecycleObjectType 1 .tcb
    |>.withLifecycleObjectType 10 .cnode
    |>.withLifecycleObjectType 12 .tcb
    |>.withLifecycleObjectType 11 .cnode
    |>.withLifecycleObjectType 20 .vspaceRoot
    |>.withLifecycleObjectType demoEndpoint .endpoint
    |>.withLifecycleObjectType demoNotification .notification
    |>.withLifecycleObjectType demoUntyped .untyped
    |>.withLifecycleCapabilityRef rootSlot (.object 1)
    |>.withLifecycleCapabilityRef lifecycleAuthSlot (.object 12)
    |>.withLifecycleCapabilityRef untypedAuthSlot (.object demoUntyped)
  ).build

private def runCapabilityAndArchitectureTrace (st1 : SystemState) : IO Unit := do
  match SeLe4n.Kernel.Architecture.adapterAdvanceTimer runtimeContractAcceptAll 2 st1 with
  | .error err => IO.println s!"adapter timer success path error: {reprStr err}"
  | .ok (_, stTimer) =>
      IO.println s!"adapter timer success path value: {reprStr stTimer.machine.timer}"
  match SeLe4n.Kernel.Architecture.adapterAdvanceTimer runtimeContractAcceptAll 0 st1 with
  | .error err => IO.println s!"adapter timer invalid-context branch: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected adapter timer success with zero ticks"
  match SeLe4n.Kernel.Architecture.adapterAdvanceTimer runtimeContractDenyAll 1 st1 with
  | .error err => IO.println s!"adapter timer unsupported branch: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected adapter timer success under denied contract"
  match SeLe4n.Kernel.Architecture.adapterReadMemory runtimeContractDenyAll 0 st1 with
  | .error err => IO.println s!"adapter read denied branch: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected adapter read success under denied contract"
  match SeLe4n.Kernel.Architecture.adapterReadMemory runtimeContractAcceptAll 4096 st1 with
  | .error err => IO.println s!"adapter read success path error: {reprStr err}"
  | .ok (byte, _) =>
      IO.println s!"adapter read success path byte: {reprStr byte}"
  match SeLe4n.Kernel.Architecture.vspaceMapPage 1 4096 8192 st1 with
  | .error err => IO.println s!"vspace map error: {reprStr err}"
  | .ok (_, stV1) =>
      match SeLe4n.Kernel.Architecture.vspaceLookup 1 4096 stV1 with
      | .error err => IO.println s!"vspace lookup error: {reprStr err}"
      | .ok (paddr, stV2) =>
          IO.println s!"vspace lookup mapped paddr: {paddr.toNat}"
          match SeLe4n.Kernel.Architecture.vspaceUnmapPage 1 4096 stV2 with
          | .error err => IO.println s!"vspace unmap error: {reprStr err}"
          | .ok (_, stV3) =>
              match SeLe4n.Kernel.Architecture.vspaceLookup 1 4096 stV3 with
              | .error err => IO.println s!"vspace lookup after unmap branch: {reprStr err}"
              | .ok (resolved, _) => IO.println s!"unexpected vspace lookup after unmap: {reprStr resolved}"
  match SeLe4n.Kernel.Architecture.adapterWriteRegister runtimeContractAcceptAll 7 99 st1 with
  | .error err => IO.println s!"adapter register write success path error: {reprStr err}"
  | .ok (_, stReg) =>
      IO.println s!"adapter register write success path value: {reprStr <| SeLe4n.readReg stReg.machine.regs 7}"
  match SeLe4n.Kernel.Architecture.adapterWriteRegister runtimeContractDenyAll 7 99 st1 with
  | .error err => IO.println s!"adapter register write unsupported branch: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected adapter register write success under denied contract"

private def runServiceAndStressTrace (st1 : SystemState) : IO Unit := do
  let allowAll : SeLe4n.Kernel.ServicePolicy := fun _ => true
  let denyAll : SeLe4n.Kernel.ServicePolicy := fun _ => false
  match SeLe4n.Kernel.serviceStart svcApi allowAll st1 with
  | .error err => IO.println s!"service start api error: {reprStr err}"
  | .ok (_, stServiceStart) =>
      IO.println s!"service start api status: {reprStr <| (SeLe4n.Model.lookupService stServiceStart svcApi).map ServiceGraphEntry.status}"
  match SeLe4n.Kernel.serviceStart svcDenied denyAll st1 with
  | .error err => IO.println s!"service start denied branch: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected service start success under denied policy"
  match SeLe4n.Kernel.serviceStart svcBroken allowAll st1 with
  | .error err => IO.println s!"service start dependency branch: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected service start success with unsatisfied dependencies"
  match SeLe4n.Kernel.serviceRestartChecked SeLe4n.Kernel.defaultLabelingContext svcApi svcRestart allowAll allowAll st1 with
  | .error err => IO.println s!"service restart error: {reprStr err}"
  | .ok (_, stRestarted) =>
      IO.println s!"service restart status: {reprStr <| (SeLe4n.Model.lookupService stRestarted svcRestart).map ServiceGraphEntry.status}"
  match SeLe4n.Kernel.serviceStop svcRestart denyAll st1 with
  | .error err => IO.println s!"service stop denied branch: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected service stop success under denied policy"
  match SeLe4n.Kernel.serviceStop svcApi allowAll st1 with
  | .error err => IO.println s!"service stop illegal-state branch: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected service stop success from stopped state"
  match SeLe4n.Kernel.serviceRestartChecked SeLe4n.Kernel.defaultLabelingContext svcApi svcRestart denyAll allowAll st1 with
  | .error err => IO.println s!"service restart stop-stage failure: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected service restart success when stop policy denies"
  match SeLe4n.Kernel.serviceRestartChecked SeLe4n.Kernel.defaultLabelingContext svcApi svcRestartBroken allowAll allowAll st1 with
  | .error err => IO.println s!"service restart start-stage failure: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected service restart success with broken dependencies"
  IO.println s!"service isolation api↔denied: {reprStr <| SeLe4n.Model.hasIsolationEdge st1 svcApi svcDenied}"
  IO.println s!"service isolation api↔db: {reprStr <| SeLe4n.Model.hasIsolationEdge st1 svcApi svcDb}"

  let deepRadixCNode : CNode := {
    guard := 3
    radix := 12
    slots := Std.HashMap.ofList [
      (1, { target := .object 1, rights := [.read], badge := none }),
      (1024, { target := .object 12, rights := [.read, .write], badge := none })
    ]
  }
  let stDeepCNode : SystemState :=
    { st1 with
      objects := st1.objects.insert 200 (.cnode deepRadixCNode)
    }
  IO.println s!"deep cnode radix fixture: {reprStr <| (stDeepCNode.objects[(200 : SeLe4n.ObjId)]?).map (fun obj => match obj with | KernelObject.cnode cn => cn.radix | _ => 0)}"
  match SeLe4n.Kernel.cspaceLookupPath { cnode := 200, cptr := 13312, depth := 14 } stDeepCNode with
  | .error err => IO.println s!"deep cnode path lookup error: {reprStr err}"
  | .ok (cap, _) => IO.println s!"deep cnode path lookup rights: {reprStr cap.rights}"
  match SeLe4n.Kernel.cspaceLookupPath { cnode := 200, cptr := 1024, depth := 4 } stDeepCNode with
  | .error err => IO.println s!"deep cnode path bad-depth branch: {reprStr err}"
  | .ok (cap, _) => IO.println s!"unexpected deep cnode path bad-depth success: {reprStr cap}"
  match SeLe4n.Kernel.cspaceLookupPath { cnode := 200, cptr := 9216, depth := 14 } stDeepCNode with
  | .error err => IO.println s!"deep cnode path guard-mismatch branch: {reprStr err}"
  | .ok (cap, _) => IO.println s!"unexpected deep cnode path guard success: {reprStr cap}"

  let largeRunnable : List SeLe4n.ThreadId :=
    [1, 12]
  let stLargeQueue : SystemState :=
    { st1 with scheduler := { st1.scheduler with runQueue := mkRunQueue largeRunnable, current := none } }
  IO.println s!"large runnable queue length: {reprStr stLargeQueue.scheduler.runnable.length}"
  match SeLe4n.Kernel.schedule stLargeQueue with
  | .error err => IO.println s!"large queue schedule error: {reprStr err}"
  | .ok (_, stLargeScheduled) =>
      IO.println s!"large queue scheduled current: {reprStr (stLargeScheduled.scheduler.current.map SeLe4n.ThreadId.toNat)}"

  -- WS-G7: multi-endpoint test migrated to dual-queue operations
  let stMultiEndpoint : SystemState :=
    { st1 with
      objects := st1.objects.insert demoEndpoint (.endpoint { state := .idle, queue := [], waitingReceiver := none })
        |>.insert 31 (.endpoint { state := .idle, queue := [], waitingReceiver := none })
    }
  match SeLe4n.Kernel.endpointSendDualChecked SeLe4n.Kernel.defaultLabelingContext demoEndpoint 1 .empty stMultiEndpoint with
  | .error err => IO.println s!"multi-endpoint send A error: {reprStr err}"
  | .ok (_, stEp1) =>
      match SeLe4n.Kernel.endpointSendDualChecked SeLe4n.Kernel.defaultLabelingContext 31 12 .empty stEp1 with
      | .error err => IO.println s!"multi-endpoint send B error: {reprStr err}"
      | .ok (_, stEp2) =>
          match SeLe4n.Kernel.endpointReceiveDual demoEndpoint 12 stEp2 with
          | .error err => IO.println s!"multi-endpoint receive A error: {reprStr err}"
          | .ok (senderA, stEp3) =>
              match SeLe4n.Kernel.endpointReceiveDual 31 1 stEp3 with
              | .error err => IO.println s!"multi-endpoint receive B error: {reprStr err}"
              | .ok (senderB, _) =>
                  IO.println s!"multi-endpoint receive senders: {senderA}, {senderB}"

  let chainRoot : ServiceId := 205
  let chainL4 : ServiceId := 204
  let chainL3 : ServiceId := 203
  let chainL2 : ServiceId := 202
  let chainL1 : ServiceId := 201
  let chainTop : ServiceId := 200
  let stServiceChain : SystemState :=
    { st1 with
      services := fun sid =>
        if sid = chainRoot then
          some {
            identity := { sid := chainRoot, backingObject := 12, owner := 10 }
            status := .running
            dependencies := []
            isolatedFrom := []
          }
        else if sid = chainL4 then
          some {
            identity := { sid := chainL4, backingObject := 12, owner := 10 }
            status := .running
            dependencies := [chainRoot]
            isolatedFrom := []
          }
        else if sid = chainL3 then
          some {
            identity := { sid := chainL3, backingObject := 12, owner := 10 }
            status := .running
            dependencies := [chainL4]
            isolatedFrom := []
          }
        else if sid = chainL2 then
          some {
            identity := { sid := chainL2, backingObject := 12, owner := 10 }
            status := .running
            dependencies := [chainL3]
            isolatedFrom := []
          }
        else if sid = chainL1 then
          some {
            identity := { sid := chainL1, backingObject := 12, owner := 10 }
            status := .running
            dependencies := [chainL2]
            isolatedFrom := []
          }
        else if sid = chainTop then
          some {
            identity := { sid := chainTop, backingObject := 12, owner := 10 }
            status := .stopped
            dependencies := [chainL1]
            isolatedFrom := []
          }
        else
          st1.services sid
    }
  match SeLe4n.Kernel.serviceStart chainTop allowAll stServiceChain with
  | .error err => IO.println s!"service dependency chain start error: {reprStr err}"
  | .ok (_, stChainStarted) =>
      IO.println s!"service dependency chain depth-5 start status: {reprStr <| (SeLe4n.Model.lookupService stChainStarted chainTop).map ServiceGraphEntry.status}"

  match SeLe4n.Kernel.Architecture.adapterReadMemory runtimeContractAcceptAll 0 st1 with
  | .error err => IO.println s!"boundary memory low-address error: {reprStr err}"
  | .ok (byte, _) => IO.println s!"boundary memory low-address byte: {reprStr byte}"
  match SeLe4n.Kernel.Architecture.adapterReadMemory runtimeContractAcceptAll 18446744073709551615 st1 with
  | .error err => IO.println s!"boundary memory high-address error: {reprStr err}"
  | .ok (byte, _) => IO.println s!"boundary memory high-address byte: {reprStr byte}"

private def runLifecycleAndEndpointTrace (st1 : SystemState) : IO Unit := do
  match SeLe4n.Kernel.lifecycleRetypeObject rootSlot 12
      (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st1 with
  | .error err =>
      IO.println s!"lifecycle retype unauthorized branch: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected lifecycle retype success with wrong authority"
  let stIllegalState : SystemState :=
    { st1 with
      lifecycle := {
        st1.lifecycle with
          objectTypes := st1.lifecycle.objectTypes.insert 12 .endpoint
      }
    }
  match SeLe4n.Kernel.lifecycleRetypeObject lifecycleAuthSlot 12
      (.endpoint { state := .idle, queue := [], waitingReceiver := none }) stIllegalState with
  | .error err => IO.println s!"lifecycle retype illegal-state branch: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected lifecycle retype success under stale metadata"
  match SeLe4n.Kernel.lifecycleRetypeObject lifecycleAuthSlot 12
      (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st1 with
  | .error err => IO.println s!"lifecycle retype error: {reprStr err}"
  | .ok (_, stLifecycle) =>
      IO.println s!"lifecycle retype success object kind: {reprStr <| (stLifecycle.objects[(12 : SeLe4n.ObjId)]?).map KernelObject.objectType}"
  match SeLe4n.Kernel.cspaceMintChecked SeLe4n.Kernel.defaultLabelingContext rootSlot mintedSlot [.read] none st1 with
  | .error err => IO.println s!"cspace mint error: {reprStr err}"
  | .ok (_, st2) =>
      match SeLe4n.Kernel.cspaceMintChecked SeLe4n.Kernel.defaultLabelingContext rootSlot siblingSlot [.read] none st2 with
      | .error err => IO.println s!"sibling mint error: {reprStr err}"
      | .ok (_, st3) =>
          IO.println "created sibling cap with the same target"
          match SeLe4n.Kernel.lifecycleRevokeDeleteRetype mintedSlot mintedSlot 12
              (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st3 with
          | .error err =>
              IO.println s!"composed transition alias guard (expected error): {reprStr err}"
          | .ok _ =>
              IO.println "unexpected composed transition success with aliased authority/cleanup"
          match SeLe4n.Kernel.lifecycleRevokeDeleteRetype rootSlot mintedSlot 12
              (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st3 with
          | .error err =>
              IO.println s!"composed transition unauthorized branch: {reprStr err}"
          | .ok _ =>
              IO.println "unexpected composed transition success with wrong authority"
          match SeLe4n.Kernel.lifecycleRevokeDeleteRetype lifecycleAuthSlot mintedSlot 12
              (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st3 with
          | .error err => IO.println s!"composed transition error: {reprStr err}"
          | .ok (_, st5) =>
              IO.println "composed revoke/delete/retype success"
              match SeLe4n.Kernel.cspaceLookupSlot siblingSlot st5 with
              | .error err => IO.println s!"post-revoke sibling lookup: {reprStr err}"
              | .ok (cap, _) =>
                  IO.println s!"unexpected sibling cap after revoke: {reprStr cap}"
              match SeLe4n.Kernel.cspaceLookupSlot mintedSlot st5 with
              | .error err => IO.println s!"post-delete lookup (expected error): {reprStr err}"
              | .ok (cap, _) =>
                  IO.println s!"unexpected cap after delete: {reprStr cap}"
              -- WS-G7: handshake + send-queue test using dual-queue operations
              -- Use st3 (pre-retype) where both TCBs (1, 12) still exist
              match SeLe4n.Kernel.endpointReceiveDual demoEndpoint 12 st3 with
                  | .error err => IO.println s!"endpoint await-receive error: {reprStr err}"
                  | .ok (_, st6) =>
                      match SeLe4n.Kernel.endpointSendDualChecked SeLe4n.Kernel.defaultLabelingContext demoEndpoint 1 .empty st6 with
                      | .error err => IO.println s!"endpoint handshake send error: {reprStr err}"
                      | .ok (_, st7) =>
                          IO.println "handshake send matched waiting receiver"
                          -- Sender blocks (no receiver waiting), then receiver dequeues
                          match SeLe4n.Kernel.endpointSendDualChecked SeLe4n.Kernel.defaultLabelingContext demoEndpoint 1 .empty st7 with
                          | .error err => IO.println s!"endpoint send #1 error: {reprStr err}"
                          | .ok (_, st8) =>
                              IO.println "queued sender on endpoint"
                              match SeLe4n.Kernel.endpointReceiveDual demoEndpoint 12 st8 with
                              | .error err => IO.println s!"endpoint receive #1 error: {reprStr err}"
                              | .ok (sender1, st9) =>
                                  IO.println s!"endpoint receive #1 sender: {sender1}"
                                  match SeLe4n.Kernel.notificationWait demoNotification 1 st9 with
                                  | .error err => IO.println s!"notification wait #1 error: {reprStr err}"
                                  | .ok (badge, st10) =>
                                      IO.println s!"notification wait #1 result: {reprStr badge}"
                                      match SeLe4n.Kernel.notificationSignal demoNotification 99 st10 with
                                      | .error err => IO.println s!"notification signal #1 error: {reprStr err}"
                                      | .ok (_, st11) =>
                                          match SeLe4n.Kernel.notificationSignal demoNotification 123 st11 with
                                          | .error err => IO.println s!"notification signal #2 error: {reprStr err}"
                                          | .ok (_, st12) =>
                                              match SeLe4n.Kernel.notificationWait demoNotification 1 st12 with
                                              | .error err => IO.println s!"notification wait #2 error: {reprStr err}"
                                              | .ok (badge2, _) =>
                                                  IO.println s!"notification wait #2 result: {reprStr badge2}"
      match SeLe4n.Kernel.cspaceLookupSlot mintedSlot st2 with
      | .error err => IO.println s!"cspace lookup error: {reprStr err}"
      | .ok (cap, _) =>
          IO.println s!"minted cap rights: {reprStr cap.rights}"

-- ============================================================================
-- WS-E4: Capability/IPC completion trace scenarios
-- ============================================================================

/-- WS-E4 test: H-02 guard, cspaceCopy, dual-queue, reply operations -/
private def runCapabilityIpcTrace (st1 : SystemState) : IO Unit := do
  -- H-02: Try inserting into occupied slot (slot 0 already has a cap)
  let occSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 0 }
  let testCap : Capability := { target := .object 1, rights := [.read], badge := none }
  match SeLe4n.Kernel.cspaceInsertSlot occSlot testCap st1 with
  | .error err => IO.println s!"H-02 occupied slot guard: {reprStr err}"
  | .ok _ => IO.println "unexpected: H-02 guard did not reject occupied slot"
  -- C-02: cspaceCopy from rootSlot to a fresh destination
  let copyDst : SeLe4n.Kernel.CSpaceAddr := { cnode := 11, slot := 7 }
  match SeLe4n.Kernel.cspaceCopy rootSlot copyDst st1 with
  | .error err => IO.println s!"cspaceCopy error: {reprStr err}"
  | .ok (_, stCopy) =>
      match SeLe4n.Kernel.cspaceLookupSlot copyDst stCopy with
      | .error err => IO.println s!"cspaceCopy lookup error: {reprStr err}"
      | .ok (copiedCap, _) =>
          IO.println s!"cspaceCopy target matches: {copiedCap.target == testCap.target}"
  -- M-01: Dual-queue endpoint send/receive
  let dualEpId : SeLe4n.ObjId := demoEndpoint
  -- Set up fresh state with idle endpoint for dual-queue test
  let dualEp : KernelObject := .endpoint {
    state := .idle, queue := [], waitingReceiver := none,
    sendQ := {}, receiveQ := {} }
  let stDual : SystemState := { st1 with objects := st1.objects.insert dualEpId dualEp }
  match SeLe4n.Kernel.endpointSendDual dualEpId 1 .empty stDual with
  | .error err => IO.println s!"endpointSendDual error: {reprStr err}"
  | .ok (_, stSent) =>
      match (stSent.objects[dualEpId]?) with
      | some (.endpoint ep) =>
          IO.println s!"dual-queue sender blocked on sendQ non-empty: {ep.sendQ.head.isSome}"
      | _ => IO.println "dual-queue endpoint missing after send"
  -- M-12: Reply operation
  -- Create a state with a thread blocked on reply
  let replyTarget : SeLe4n.ThreadId := 1
  let replyTcb : KernelObject := .tcb {
    tid := replyTarget, priority := 100, domain := 0,
    cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 4096,
    ipcState := .blockedOnReply demoEndpoint }
  let replySched := { st1.scheduler with
    runQueue := st1.scheduler.runQueue.remove replyTarget }
  let stReply : SystemState := { st1 with objects := st1.objects.insert replyTarget.toObjId replyTcb, scheduler := replySched }
  match SeLe4n.Kernel.endpointReply replyTarget .empty stReply with
  | .error err => IO.println s!"endpointReply error: {reprStr err}"
  | .ok (_, stReplied) =>
      let unblocked := stReplied.scheduler.runnable.any (· == replyTarget)
      IO.println s!"endpointReply unblocked target: {unblocked}"

-- ============================================================================
-- WS-E6: Model completeness trace scenarios
-- ============================================================================

/-- WS-E6 test: M-03 EDF tie-breaking, M-04 time-slice preemption, M-05 domain scheduling -/
private def runSchedulerTimingDomainTrace (st1 : SystemState) : IO Unit := do
  -- M-03: EDF tie-breaking — two threads at same priority, different deadlines
  let edfTcbA : KernelObject := .tcb {
    tid := 1, priority := 100, domain := 0,
    cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 4096,
    ipcState := .ready, deadline := 50 }
  let edfTcbB : KernelObject := .tcb {
    tid := 12, priority := 100, domain := 0,
    cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 8192,
    ipcState := .ready, deadline := 30 }
  let stEdf : SystemState := { st1 with
    objects := st1.objects.insert 1 edfTcbA |>.insert 12 edfTcbB,
    scheduler := { st1.scheduler with runQueue := mkRunQueue [1, 12], current := none } }
  match SeLe4n.Kernel.chooseThread stEdf with
  | .error err => IO.println s!"EDF choose error: {reprStr err}"
  | .ok (chosen, _) =>
      IO.println s!"EDF tie-break chosen thread: {reprStr (chosen.map SeLe4n.ThreadId.toNat)}"

  -- M-04: Time-slice preemption — tick down until expiry triggers reschedule
  let tickTcb : KernelObject := .tcb {
    tid := 1, priority := 100, domain := 0,
    cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 4096,
    ipcState := .ready, timeSlice := 2 }
  let stTick : SystemState := { st1 with
    objects := st1.objects.insert 1 tickTcb,
    scheduler := { st1.scheduler with runQueue := mkRunQueue [1, 12], current := some 1 } }
  match SeLe4n.Kernel.timerTick stTick with
  | .error err => IO.println s!"timer tick decrement error: {reprStr err}"
  | .ok ((), stTicked) =>
      -- After one tick with timeSlice=2, slice becomes 1 (decrement path)
      match (stTicked.objects[SeLe4n.ThreadId.toObjId 1]? : Option KernelObject) with
      | some (KernelObject.tcb tcb) =>
          IO.println s!"timer tick remaining slice: {tcb.timeSlice}"
      | _ => IO.println "timer tick: thread not found after tick"
  -- Now tick again — this should trigger expiry and reschedule
  let expiryTcb : KernelObject := .tcb {
    tid := 1, priority := 100, domain := 0,
    cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 4096,
    ipcState := .ready, timeSlice := 1 }
  let stExpiry : SystemState := { st1 with
    objects := st1.objects.insert 1 expiryTcb,
    scheduler := { st1.scheduler with runQueue := mkRunQueue [1, 12], current := some 1 } }
  match SeLe4n.Kernel.timerTick stExpiry with
  | .error err => IO.println s!"timer tick expiry error: {reprStr err}"
  | .ok ((), stExpired) =>
      IO.println s!"timer tick expiry rescheduled current: {reprStr (stExpired.scheduler.current.map SeLe4n.ThreadId.toNat)}"
      match (stExpired.objects[SeLe4n.ThreadId.toObjId 1]? : Option KernelObject) with
      | some (KernelObject.tcb tcb) =>
          IO.println s!"timer tick expiry reset slice: {tcb.timeSlice}"
      | _ => IO.println "timer tick expiry: thread not found"

  -- M-05: Domain scheduling — switch domain and verify active domain changes
  let domSchedule : List DomainScheduleEntry :=
    [{ domain := 0, length := 3 }, { domain := 1, length := 5 }]
  let stDom : SystemState := { st1 with
    scheduler := { st1.scheduler with
      runQueue := mkRunQueue [1, 12], current := some 1,
      activeDomain := 0, domainTimeRemaining := 1,
      domainSchedule := domSchedule, domainScheduleIndex := 0 } }
  match SeLe4n.Kernel.switchDomain stDom with
  | .error err => IO.println s!"domain switch error: {reprStr err}"
  | .ok ((), stSwitched) =>
      IO.println s!"domain switch active domain: {stSwitched.scheduler.activeDomain.toNat}"
      IO.println s!"domain switch time remaining: {stSwitched.scheduler.domainTimeRemaining}"

-- ============================================================================
-- WS-F1: IPC message transfer verification trace scenarios
-- ============================================================================

/-- WS-F1 test: dual-queue message transfer, rendezvous, call/reply roundtrip. -/
private def runIpcMessageTransferTrace (st1 : SystemState) : IO Unit := do
  -- F1-01: Send with payload → receiver dequeues → message in receiver TCB
  let epId : SeLe4n.ObjId := demoEndpoint
  let senderId : SeLe4n.ThreadId := 1
  let receiverId : SeLe4n.ThreadId := 12
  let testMsg : IpcMessage := { registers := [42, 7], caps := [], badge := some ⟨123⟩ }
  -- Fresh endpoint for dual-queue test
  let ep0 : KernelObject := .endpoint {
    state := .idle, queue := [], waitingReceiver := none,
    sendQ := {}, receiveQ := {} }
  let st0 : SystemState := { st1 with objects := st1.objects.insert epId ep0 }
  -- Sender sends (no receiver queued → sender blocks with message)
  match SeLe4n.Kernel.endpointSendDual epId senderId testMsg st0 with
  | .error err => IO.println s!"F1-01 send error: {reprStr err}"
  | .ok (_, stSent) =>
      -- Verify sender has pending message
      let senderHasMsg := match SeLe4n.Kernel.lookupTcb stSent senderId with
        | some tcb => tcb.pendingMessage.isSome
        | none => false
      IO.println s!"message sender has pending: {senderHasMsg}"
      -- Receiver dequeues sender → message transferred to receiver
      match SeLe4n.Kernel.endpointReceiveDual epId receiverId stSent with
      | .error err => IO.println s!"F1-01 receive error: {reprStr err}"
      | .ok (_, stRecv) =>
          let recvMsg := match SeLe4n.Kernel.lookupTcb stRecv receiverId with
            | some tcb => tcb.pendingMessage
            | none => none
          let msgRegs := match recvMsg with
            | some m => m.registers
            | none => []
          IO.println s!"message transfer registers: {reprStr msgRegs}"
          let msgBadge := match recvMsg with
            | some m => m.badge
            | none => none
          IO.println s!"message transfer badge: {reprStr msgBadge}"
          -- Verify sender's pending message was cleared
          let senderCleared := match SeLe4n.Kernel.lookupTcb stRecv senderId with
            | some tcb => tcb.pendingMessage.isNone
            | none => false
          IO.println s!"message sender cleared after transfer: {senderCleared}"
  -- F1-02: Rendezvous path — receiver waits first, then send delivers directly
  let ep1 : KernelObject := .endpoint {
    state := .idle, queue := [], waitingReceiver := none,
    sendQ := {}, receiveQ := {} }
  let stR : SystemState := { st1 with objects := st1.objects.insert epId ep1 }
  -- Receiver blocks first (no sender waiting → receiver enqueued)
  match SeLe4n.Kernel.endpointReceiveDual epId receiverId stR with
  | .error err => IO.println s!"F1-02 receive-first error: {reprStr err}"
  | .ok (_, stWait) =>
      -- Sender sends with message (receiver queued → rendezvous)
      let rendezvousMsg : IpcMessage := { registers := [99], caps := [], badge := none }
      match SeLe4n.Kernel.endpointSendDual epId senderId rendezvousMsg stWait with
      | .error err => IO.println s!"F1-02 send error: {reprStr err}"
      | .ok (_, stRend) =>
          let rendMsg := match SeLe4n.Kernel.lookupTcb stRend receiverId with
            | some tcb => tcb.pendingMessage
            | none => none
          let rendRegs := match rendMsg with
            | some m => m.registers
            | none => []
          IO.println s!"rendezvous delivery registers: {reprStr rendRegs}"
  -- F1-03: Call + Reply roundtrip with message payload
  let ep2 : KernelObject := .endpoint {
    state := .idle, queue := [], waitingReceiver := none,
    sendQ := {}, receiveQ := {} }
  let stC : SystemState := { st1 with objects := st1.objects.insert epId ep2 }
  -- Receiver waits first
  match SeLe4n.Kernel.endpointReceiveDual epId receiverId stC with
  | .error err => IO.println s!"F1-03 receive error: {reprStr err}"
  | .ok (_, stWait2) =>
      -- Caller calls with message
      let callMsg : IpcMessage := { registers := [10, 20, 30], caps := [], badge := some ⟨456⟩ }
      match SeLe4n.Kernel.endpointCall epId senderId callMsg stWait2 with
      | .error err => IO.println s!"F1-03 call error: {reprStr err}"
      | .ok (_, stCalled) =>
          -- Verify caller is blocked on reply
          let callerBlocked := match SeLe4n.Kernel.lookupTcb stCalled senderId with
            | some tcb => match tcb.ipcState with
              | .blockedOnReply _ => true
              | _ => false
            | none => false
          IO.println s!"call/reply caller blocked: {callerBlocked}"
          -- Reply with response message
          let replyMsg : IpcMessage := { registers := [100, 200], caps := [], badge := none }
          match SeLe4n.Kernel.endpointReply senderId replyMsg stCalled with
          | .error err => IO.println s!"F1-03 reply error: {reprStr err}"
          | .ok (_, stReplied) =>
              let replyResult := match SeLe4n.Kernel.lookupTcb stReplied senderId with
                | some tcb => tcb.pendingMessage
                | none => none
              let replyRegs := match replyResult with
                | some m => m.registers
                | none => []
              IO.println s!"call/reply response registers: {reprStr replyRegs}"

-- ============================================================================
-- WS-F2: Untyped memory model trace scenarios
-- ============================================================================

/-- WS-F2 test: retypeFromUntyped success, watermark advance, region-exhausted error,
type-mismatch error, device restriction error. -/
private def runUntypedMemoryTrace (st1 : SystemState) : IO Unit := do
  -- F2-01: Successful retype from untyped — carve a new endpoint from the untyped region
  let childEp : SeLe4n.ObjId := 50
  let newEp : KernelObject := .endpoint { state := .idle, queue := [], waitingReceiver := none }
  let epAllocSize : Nat := SeLe4n.Kernel.objectTypeAllocSize .endpoint
  match SeLe4n.Kernel.retypeFromUntyped untypedAuthSlot demoUntyped childEp newEp epAllocSize st1 with
  | .error err => IO.println s!"retype-from-untyped success path error: {reprStr err}"
  | .ok (_, stRetyped) =>
      IO.println s!"retype-from-untyped success object kind: {reprStr <| (stRetyped.objects[childEp]?).map KernelObject.objectType}"
      -- Check watermark advanced
      match stRetyped.objects[demoUntyped]? with
      | some (.untyped ut) =>
          IO.println s!"untyped watermark after retype: {ut.watermark}"
          IO.println s!"untyped children count: {ut.children.length}"
      | _ => IO.println "untyped object missing after retype"
      -- F2-02: Retype a second object (TCB) from the same untyped
      let childTcb : SeLe4n.ObjId := 51
      let newTcb : KernelObject := .tcb {
        tid := 51, priority := 50, domain := 0,
        cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 12288,
        ipcState := .ready }
      let tcbAllocSize : Nat := SeLe4n.Kernel.objectTypeAllocSize .tcb
      match SeLe4n.Kernel.retypeFromUntyped untypedAuthSlot demoUntyped childTcb newTcb tcbAllocSize stRetyped with
      | .error err => IO.println s!"retype-from-untyped second alloc error: {reprStr err}"
      | .ok (_, stRetyped2) =>
          match stRetyped2.objects[demoUntyped]? with
          | some (.untyped ut2) =>
              IO.println s!"untyped watermark after second retype: {ut2.watermark}"
          | _ => IO.println "untyped object missing after second retype"
  -- F2-03: Type mismatch — try retypeFromUntyped on a TCB (not an untyped)
  match SeLe4n.Kernel.retypeFromUntyped lifecycleAuthSlot 12 50 newEp epAllocSize st1 with
  | .error err => IO.println s!"retype-from-untyped type-mismatch branch: {reprStr err}"
  | .ok _ => IO.println "unexpected retype-from-untyped success on non-untyped object"
  -- F2-04: Region exhausted — try to allocate more than available
  let hugeAllocSize : Nat := 999999
  match SeLe4n.Kernel.retypeFromUntyped untypedAuthSlot demoUntyped 52 newEp hugeAllocSize st1 with
  | .error err => IO.println s!"retype-from-untyped region-exhausted branch: {reprStr err}"
  | .ok _ => IO.println "unexpected retype-from-untyped success with oversized allocation"
  -- F2-05: Object not found — try retypeFromUntyped on nonexistent ObjId
  match SeLe4n.Kernel.retypeFromUntyped untypedAuthSlot 999 50 newEp epAllocSize st1 with
  | .error err => IO.println s!"retype-from-untyped not-found branch: {reprStr err}"
  | .ok _ => IO.println "unexpected retype-from-untyped success on missing object"
  -- F2-06: Device restriction — create a device untyped and try to retype a TCB from it
  let deviceUntypedId : SeLe4n.ObjId := 41
  let stDevice : SystemState :=
    { st1 with
      objects := st1.objects.insert deviceUntypedId (.untyped {
          regionBase := 0x200000, regionSize := 8192,
          watermark := 0, children := [], isDevice := true })
        |>.insert 10 (.cnode {
          guard := 0, radix := 0,
          slots := Std.HashMap.ofList [
            (0, { target := .object 1, rights := [.read, .write, .grant], badge := none }),
            (5, { target := .object 12, rights := [.read, .write], badge := none }),
            (6, { target := .object demoUntyped, rights := [.read, .write], badge := none }),
            (7, { target := .object deviceUntypedId, rights := [.read, .write], badge := none }) ] }) }
  let devAuthSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 7 }
  let devTcb : KernelObject := .tcb {
    tid := 53, priority := 50, domain := 0,
    cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 16384,
    ipcState := .ready }
  match SeLe4n.Kernel.retypeFromUntyped devAuthSlot deviceUntypedId 53 devTcb 1024 stDevice with
  | .error err => IO.println s!"retype-from-untyped device-restriction branch: {reprStr err}"
  | .ok _ => IO.println "unexpected retype-from-untyped success on device untyped"
  -- F2-07: Wrong authority — use a cap that targets the wrong object
  match SeLe4n.Kernel.retypeFromUntyped rootSlot demoUntyped 54 newEp epAllocSize st1 with
  | .error err => IO.println s!"retype-from-untyped wrong-authority branch: {reprStr err}"
  | .ok _ => IO.println "unexpected retype-from-untyped success with wrong authority"
  -- F2-08: Alloc size too small — try allocSize=1 for an endpoint (needs 64)
  match SeLe4n.Kernel.retypeFromUntyped untypedAuthSlot demoUntyped 55 newEp 1 st1 with
  | .error err => IO.println s!"retype-from-untyped alloc-size-too-small branch: {reprStr err}"
  | .ok _ => IO.println "unexpected retype-from-untyped success with undersized allocation"

def runMainTraceFrom (st1 : SystemState) : IO Unit := do
  assertStateInvariantsFor "main trace entry" bootstrapInvariantObjectIds st1 bootstrapServiceIds
  match SeLe4n.Kernel.cspaceLookupSlot rootSlot st1 with
  | .error err => IO.println s!"source lookup error: {reprStr err}"
  | .ok (srcCap, _) =>
      IO.println s!"source cap rights before mint: {reprStr srcCap.rights}"
  match SeLe4n.Kernel.cspaceLookupPath rootPath st1 with
  | .error err => IO.println s!"source path lookup error: {reprStr err}"
  | .ok (srcCap, _) => IO.println s!"source path lookup rights: {reprStr srcCap.rights}"
  match SeLe4n.Kernel.cspaceLookupPath rootPathAlias st1 with
  | .error err => IO.println s!"source path alias branch error: {reprStr err}"
  | .ok (srcCap, _) => IO.println s!"source path alias lookup rights: {reprStr srcCap.rights}"

  runCapabilityAndArchitectureTrace st1
  runServiceAndStressTrace st1
  runLifecycleAndEndpointTrace st1
  runCapabilityIpcTrace st1
  runIpcMessageTransferTrace st1
  runSchedulerTimingDomainTrace st1
  runUntypedMemoryTrace st1

-- ============================================================================
-- M-10 Parameterized test topology builder (WS-E1)
-- ============================================================================

/-- Build a topology with `threadCount` threads at varying priorities, a CNode with
the given `radix`, `asidCount` VSpace roots with distinct ASIDs, an endpoint,
a notification, and `svcCount` services with a linear dependency chain. -/
private def buildParameterizedTopology
    (threadCount : Nat) (basePriority : Nat) (radix : Nat) (asidCount : Nat)
    (svcCount : Nat := 0) : SystemState :=
  let threads : List (SeLe4n.ObjId × KernelObject) :=
    (List.range threadCount).map fun i =>
      let oid : SeLe4n.ObjId := ⟨1000 + i⟩
      (oid, .tcb {
        tid := ⟨1000 + i⟩
        priority := ⟨basePriority + i * 10⟩
        domain := ⟨0⟩
        cspaceRoot := ⟨2000⟩
        vspaceRoot := ⟨3000⟩
        ipcBuffer := ⟨4096 + i * 4096⟩
        ipcState := .ready
      })
  let cnodeSlots : List (SeLe4n.Slot × Capability) :=
    (List.range threadCount).map fun i =>
      (⟨i⟩, { target := .object ⟨1000 + i⟩, rights := [.read, .write], badge := none })
  let cnodeObj : KernelObject := .cnode { guard := 0, radix := radix, slots := Std.HashMap.ofList cnodeSlots }
  let vspaceRoots : List (SeLe4n.ObjId × KernelObject) :=
    (List.range asidCount).map fun i =>
      let oid : SeLe4n.ObjId := ⟨3000 + i⟩
      (oid, .vspaceRoot { asid := ⟨i + 1⟩, mappings := {} })
  -- Add an idle endpoint and an idle notification for IPC invariant coverage.
  let ipcObjects : List (SeLe4n.ObjId × KernelObject) :=
    [ (⟨4000⟩, .endpoint { state := .idle, queue := [], waitingReceiver := none })
    , (⟨4001⟩, .notification { state := .idle, waitingThreads := [], pendingBadge := none })
    ]
  let allObjects := threads ++ [(⟨2000⟩, cnodeObj)] ++ vspaceRoots ++ ipcObjects
  let runnableThreads : List SeLe4n.ThreadId :=
    (List.range threadCount).map fun i => ⟨1000 + i⟩
  let lifecycleTypes : List (SeLe4n.ObjId × KernelObjectType) :=
    (threads.map fun (oid, _) => (oid, .tcb))
      ++ [(⟨2000⟩, .cnode)]
      ++ (vspaceRoots.map fun (oid, _) => (oid, .vspaceRoot))
      ++ [(⟨4000⟩, .endpoint), (⟨4001⟩, .notification)]
  -- Build a linear service dependency chain: svc0 → svc1 → ... → svc(n-1) (acyclic).
  let serviceEntries : List (ServiceId × ServiceGraphEntry) :=
    (List.range svcCount).map fun i =>
      let sid : ServiceId := ⟨5000 + i⟩
      let deps := if i + 1 < svcCount then [⟨5000 + i + 1⟩] else []
      (sid, { identity := { sid := sid, backingObject := ⟨5000 + i⟩, owner := ⟨1000⟩ },
              status := .running, dependencies := deps, isolatedFrom := [] })
  let builder := BootstrapBuilder.empty
    |>.withRunnable runnableThreads
  let builder := allObjects.foldl (fun b (oid, obj) => b.withObject oid obj) builder
  let builder := lifecycleTypes.foldl (fun b (oid, ty) => b.withLifecycleObjectType oid ty) builder
  let builder := serviceEntries.foldl (fun b (sid, entry) => b.withService sid entry) builder
  builder.build

/-- Exercise invariant checks over a parameterized topology configuration. -/
private def runParameterizedTopologyCheck
    (label : String) (threadCount : Nat) (basePriority : Nat) (radix : Nat) (asidCount : Nat)
    (svcCount : Nat := 0) : IO Unit := do
  let st := buildParameterizedTopology threadCount basePriority radix asidCount svcCount
  let allIds := st.objectIndex
  let svcIds : List ServiceId := (List.range svcCount).map fun i => ⟨5000 + i⟩
  let checks := stateInvariantChecksFor allIds st svcIds
  let failures := checks.filterMap fun (name, ok) => if ok then none else some name
  if failures.isEmpty then
    IO.println s!"parameterized topology ok: {label} (threads={threadCount} prio={basePriority} radix={radix} asids={asidCount} svcs={svcCount})"
  else
    throw <| IO.userError s!"{label}: parameterized topology invariant check failed: {reprStr failures}"

/-- M-10: run at least 3 distinct configurations per subsystem to supplement hardcoded fixtures. -/
private def runParameterizedTopologies : IO Unit := do
  -- Configuration 1: single thread, minimal radix, single ASID, 1 service
  runParameterizedTopologyCheck "minimal" 1 50 4 1 1
  -- Configuration 2: four threads, varied priorities, medium radix, two ASIDs, 2-service chain
  runParameterizedTopologyCheck "medium" 4 10 8 2 2
  -- Configuration 3: eight threads, high priority base, large radix, four ASIDs, 4-service chain
  runParameterizedTopologyCheck "large" 8 100 16 4 4

def runMainTrace : IO Unit := do
  assertStateInvariantsFor "bootstrap state" bootstrapInvariantObjectIds bootstrapState bootstrapServiceIds
  match SeLe4n.Kernel.schedule bootstrapState with
  | .error err => IO.println s!"scheduler error: {reprStr err}"
  | .ok (_, st1) =>
      assertStateInvariantsFor "post-schedule" bootstrapInvariantObjectIds st1 bootstrapServiceIds
      IO.println s!"scheduled thread: {reprStr (st1.scheduler.current.map SeLe4n.ThreadId.toNat)}"
      runMainTraceFrom st1
  runParameterizedTopologies

end SeLe4n.Testing
