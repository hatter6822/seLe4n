import SeLe4n
import SeLe4n.Testing.RuntimeContractFixtures
import SeLe4n.Testing.StateBuilder
import SeLe4n.Testing.InvariantChecks

open SeLe4n.Model

namespace SeLe4n.Testing

def rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 0 }
def rootPath : SeLe4n.Kernel.CSpacePathAddr := { cnode := 10, cptr := 0, depth := 0 }
def rootPathAlias : SeLe4n.Kernel.CSpacePathAddr := { cnode := 10, cptr := 1, depth := 0 }
def lifecycleAuthSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 5 }
def mintedSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 11, slot := 3 }
def siblingSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 11, slot := 4 }
def demoEndpoint : SeLe4n.ObjId := 30
def demoNotification : SeLe4n.ObjId := 31

def permissiveLabelingContext : SeLe4n.Kernel.LabelingContext :=
  { objectLabelOf := fun _ => SeLe4n.Kernel.SecurityLabel.publicLabel
    threadLabelOf := fun _ => SeLe4n.Kernel.SecurityLabel.publicLabel
    endpointLabelOf := fun _ => SeLe4n.Kernel.SecurityLabel.publicLabel
    serviceLabelOf := fun _ => SeLe4n.Kernel.SecurityLabel.publicLabel }

def svcDb : ServiceId := 100
def svcApi : ServiceId := 101
def svcDenied : ServiceId := 102
def svcBroken : ServiceId := 103
def svcRestart : ServiceId := 104
def svcRestartBroken : ServiceId := 105

def bootstrapInvariantObjectIds : List SeLe4n.ObjId :=
  [1, 2, 10, 11, 12, 20, demoEndpoint, demoNotification, 200]

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
      slots :=
        [ (0, {
            target := .object 1
            rights := [.read, .write, .grant]
            badge := none
          }),
          (5, {
            target := .object 12
            rights := [.read, .write]
            badge := none
          }) ]
    })
    |>.withObject 2 (.tcb {
      tid := 2
      priority := 50
      domain := 0
      cspaceRoot := 10
      vspaceRoot := 20
      ipcBuffer := 6144
      ipcState := .ready
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
    |>.withObject 20 (.vspaceRoot { asid := 1, mappings := [] })
    |>.withObject demoEndpoint (.endpoint { state := .idle, queue := [], waitingReceiver := none })
    |>.withObject demoNotification (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
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
    |>.withRunnable [1, 2, 12]
    |>.withLifecycleObjectType 1 .tcb
    |>.withLifecycleObjectType 2 .tcb
    |>.withLifecycleObjectType 10 .cnode
    |>.withLifecycleObjectType 12 .tcb
    |>.withLifecycleObjectType 11 .cnode
    |>.withLifecycleObjectType 20 .vspaceRoot
    |>.withLifecycleObjectType demoEndpoint .endpoint
    |>.withLifecycleObjectType demoNotification .notification
    |>.withLifecycleCapabilityRef rootSlot (.object 1)
    |>.withLifecycleCapabilityRef lifecycleAuthSlot (.object 12)
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
  match SeLe4n.Kernel.serviceRestartChecked permissiveLabelingContext svcApi svcRestart allowAll allowAll st1 with
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
  match SeLe4n.Kernel.serviceRestartChecked permissiveLabelingContext svcApi svcRestart denyAll allowAll st1 with
  | .error err => IO.println s!"service restart stop-stage failure: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected service restart success when stop policy denies"
  match SeLe4n.Kernel.serviceRestartChecked permissiveLabelingContext svcApi svcRestartBroken allowAll allowAll st1 with
  | .error err => IO.println s!"service restart start-stage failure: {reprStr err}"
  | .ok _ =>
      IO.println "unexpected service restart success with broken dependencies"
  IO.println s!"service isolation api↔denied: {reprStr <| SeLe4n.Model.hasIsolationEdge st1 svcApi svcDenied}"
  IO.println s!"service isolation api↔db: {reprStr <| SeLe4n.Model.hasIsolationEdge st1 svcApi svcDb}"

  let deepRadixCNode : CNode := {
    guard := 3
    radix := 12
    slots := [
      (1, { target := .object 1, rights := [.read], badge := none }),
      (1024, { target := .object 12, rights := [.read, .write], badge := none })
    ]
  }
  let stDeepCNode : SystemState :=
    { st1 with
      objects := fun oid =>
        if oid = 200 then some (.cnode deepRadixCNode) else st1.objects oid
    }
  IO.println s!"deep cnode radix fixture: {reprStr <| (stDeepCNode.objects 200).map (fun obj => match obj with | .cnode cn => cn.radix | _ => 0)}"
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
    { st1 with scheduler := { st1.scheduler with runnable := largeRunnable, current := none } }
  IO.println s!"large runnable queue length: {reprStr stLargeQueue.scheduler.runnable.length}"
  match SeLe4n.Kernel.schedule stLargeQueue with
  | .error err => IO.println s!"large queue schedule error: {reprStr err}"
  | .ok (_, stLargeScheduled) =>
      IO.println s!"large queue scheduled current: {reprStr (stLargeScheduled.scheduler.current.map SeLe4n.ThreadId.toNat)}"

  let stMultiEndpoint : SystemState :=
    { st1 with
      objects := fun oid =>
        if oid = demoEndpoint then some (.endpoint { state := .idle, queue := [], waitingReceiver := none })
        else if oid = 31 then some (.endpoint { state := .idle, queue := [], waitingReceiver := none })
        else if oid = 4 then some (.tcb {
          tid := 4
          priority := 20
          domain := 0
          cspaceRoot := 10
          vspaceRoot := 20
          ipcBuffer := 4096
          ipcState := .ready
        })
        else if oid = 5 then some (.tcb {
          tid := 5
          priority := 20
          domain := 0
          cspaceRoot := 10
          vspaceRoot := 20
          ipcBuffer := 4096
          ipcState := .ready
        })
        else st1.objects oid
    }
  match SeLe4n.Kernel.endpointSendChecked permissiveLabelingContext demoEndpoint 4 stMultiEndpoint with
  | .error err => IO.println s!"multi-endpoint send A error: {reprStr err}"
  | .ok (_, stEp1) =>
      match SeLe4n.Kernel.endpointSendChecked permissiveLabelingContext 31 5 stEp1 with
      | .error err => IO.println s!"multi-endpoint send B error: {reprStr err}"
      | .ok (_, stEp2) =>
          match SeLe4n.Kernel.endpointReceive demoEndpoint stEp2 with
          | .error err => IO.println s!"multi-endpoint receive A error: {reprStr err}"
          | .ok (senderA, stEp3) =>
              match SeLe4n.Kernel.endpointReceive 31 stEp3 with
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
          objectTypes := fun oid =>
            if oid = 12 then some .endpoint else st1.lifecycle.objectTypes oid
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
      IO.println s!"lifecycle retype success object kind: {reprStr <| (stLifecycle.objects 12).map KernelObject.objectType}"
  match SeLe4n.Kernel.cspaceMintChecked permissiveLabelingContext rootSlot mintedSlot [.read] none st1 with
  | .error err => IO.println s!"cspace mint error: {reprStr err}"
  | .ok (_, st2) =>
      match SeLe4n.Kernel.cspaceMintChecked permissiveLabelingContext rootSlot siblingSlot [.read] none st2 with
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
              match SeLe4n.Kernel.endpointAwaitReceive demoEndpoint 2 st5 with
                  | .error err => IO.println s!"endpoint await-receive error: {reprStr err}"
                  | .ok (_, st6) =>
                      match SeLe4n.Kernel.endpointSendChecked permissiveLabelingContext demoEndpoint 1 st6 with
                      | .error err => IO.println s!"endpoint handshake send error: {reprStr err}"
                      | .ok (_, st7) =>
                          IO.println "handshake send matched waiting receiver"
                          match SeLe4n.Kernel.endpointSendChecked permissiveLabelingContext demoEndpoint 1 st7 with
                          | .error err => IO.println s!"endpoint send #1 error: {reprStr err}"
                          | .ok (_, st8) =>
                              match SeLe4n.Kernel.endpointSendChecked permissiveLabelingContext demoEndpoint 2 st8 with
                              | .error err => IO.println s!"endpoint send #2 error: {reprStr err}"
                              | .ok (_, st9) =>
                                  IO.println "queued two senders on endpoint"
                                  match SeLe4n.Kernel.endpointReceive demoEndpoint st9 with
                                  | .error err => IO.println s!"endpoint receive #1 error: {reprStr err}"
                                  | .ok (sender1, st10) =>
                                      IO.println s!"endpoint receive #1 sender: {sender1}"
                                      match SeLe4n.Kernel.endpointReceive demoEndpoint st10 with
                                      | .error err => IO.println s!"endpoint receive #2 error: {reprStr err}"
                                      | .ok (sender2, st11) =>
                                          IO.println s!"endpoint receive #2 sender: {sender2}"
                                          match SeLe4n.Kernel.endpointReceive demoEndpoint st11 with
                                          | .error err =>
                                              IO.println s!"endpoint receive #3 (expected mismatch): {reprStr err}"
                                          | .ok (sender3, _) =>
                                                IO.println s!"unexpected endpoint receive #3 sender: {sender3}"
                                          match SeLe4n.Kernel.notificationWait demoNotification 2 st11 with
                                          | .error err => IO.println s!"notification wait #1 error: {reprStr err}"
                                          | .ok (badge, st12) =>
                                              IO.println s!"notification wait #1 result: {reprStr badge}"
                                              match SeLe4n.Kernel.notificationSignal demoNotification 99 st12 with
                                              | .error err => IO.println s!"notification signal #1 error: {reprStr err}"
                                              | .ok (_, st13) =>
                                                  match SeLe4n.Kernel.notificationSignal demoNotification 123 st13 with
                                                  | .error err => IO.println s!"notification signal #2 error: {reprStr err}"
                                                  | .ok (_, st14) =>
                                                      match SeLe4n.Kernel.notificationWait demoNotification 2 st14 with
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
private def runWsE4Trace (st1 : SystemState) : IO Unit := do
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
    sendQueue := [], receiveQueue := [] }
  let dualObjects : SeLe4n.ObjId → Option KernelObject := fun oid =>
    if oid = dualEpId then some dualEp else st1.objects oid
  let stDual : SystemState := { st1 with objects := dualObjects }
  match SeLe4n.Kernel.endpointSendDual dualEpId 1 stDual with
  | .error err => IO.println s!"endpointSendDual error: {reprStr err}"
  | .ok (_, stSent) =>
      match (stSent.objects dualEpId) with
      | some (.endpoint ep) =>
          IO.println s!"dual-queue sender blocked on sendQueue: {!ep.sendQueue.isEmpty}"
      | _ => IO.println "dual-queue endpoint missing after send"
  -- M-12: Reply operation
  -- Create a state with a thread blocked on reply
  let replyTarget : SeLe4n.ThreadId := 1
  let replyTcb : KernelObject := .tcb {
    tid := replyTarget, priority := 100, domain := 0,
    cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 4096,
    ipcState := .blockedOnReply demoEndpoint }
  let replyObjects : SeLe4n.ObjId → Option KernelObject := fun oid =>
    if oid = replyTarget.toObjId then some replyTcb else st1.objects oid
  let replySched := { st1.scheduler with
    runnable := st1.scheduler.runnable.filter (· != replyTarget) }
  let stReply : SystemState := { st1 with objects := replyObjects, scheduler := replySched }
  match SeLe4n.Kernel.endpointReply replyTarget stReply with
  | .error err => IO.println s!"endpointReply error: {reprStr err}"
  | .ok (_, stReplied) =>
      let unblocked := stReplied.scheduler.runnable.any (· == replyTarget)
      IO.println s!"endpointReply unblocked target: {unblocked}"

-- ============================================================================
-- WS-E6: Model completeness trace scenarios
-- ============================================================================

/-- WS-E6 test: M-03 EDF tie-breaking, M-04 time-slice preemption, M-05 domain scheduling -/
private def runWsE6Trace (st1 : SystemState) : IO Unit := do
  -- M-03: EDF tie-breaking — two threads at same priority, different deadlines
  let edfTcbA : KernelObject := .tcb {
    tid := 1, priority := 100, domain := 0,
    cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 4096,
    ipcState := .ready, deadline := 50 }
  let edfTcbB : KernelObject := .tcb {
    tid := 12, priority := 100, domain := 0,
    cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 8192,
    ipcState := .ready, deadline := 30 }
  let edfObjects : SeLe4n.ObjId → Option KernelObject := fun oid =>
    if oid = 1 then some edfTcbA
    else if oid = 12 then some edfTcbB
    else st1.objects oid
  let stEdf : SystemState := { st1 with
    objects := edfObjects,
    scheduler := { st1.scheduler with runnable := [1, 12], current := none } }
  match SeLe4n.Kernel.chooseThread stEdf with
  | .error err => IO.println s!"EDF choose error: {reprStr err}"
  | .ok (chosen, _) =>
      IO.println s!"EDF tie-break chosen thread: {reprStr (chosen.map SeLe4n.ThreadId.toNat)}"

  -- M-04: Time-slice preemption — tick down until expiry triggers reschedule
  let tickTcb : KernelObject := .tcb {
    tid := 1, priority := 100, domain := 0,
    cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 4096,
    ipcState := .ready, timeSlice := 2 }
  let tickObjects : SeLe4n.ObjId → Option KernelObject := fun oid =>
    if oid = 1 then some tickTcb else st1.objects oid
  let stTick : SystemState := { st1 with
    objects := tickObjects,
    scheduler := { st1.scheduler with runnable := [1, 12], current := some 1 } }
  match SeLe4n.Kernel.timerTick stTick with
  | .error err => IO.println s!"timer tick decrement error: {reprStr err}"
  | .ok ((), stTicked) =>
      -- After one tick with timeSlice=2, slice becomes 1 (decrement path)
      match stTicked.objects (SeLe4n.ThreadId.toObjId 1) with
      | some (.tcb tcb) =>
          IO.println s!"timer tick remaining slice: {tcb.timeSlice}"
      | _ => IO.println "timer tick: thread not found after tick"
  -- Now tick again — this should trigger expiry and reschedule
  let expiryTcb : KernelObject := .tcb {
    tid := 1, priority := 100, domain := 0,
    cspaceRoot := 10, vspaceRoot := 20, ipcBuffer := 4096,
    ipcState := .ready, timeSlice := 1 }
  let expiryObjects : SeLe4n.ObjId → Option KernelObject := fun oid =>
    if oid = 1 then some expiryTcb else st1.objects oid
  let stExpiry : SystemState := { st1 with
    objects := expiryObjects,
    scheduler := { st1.scheduler with runnable := [1, 12], current := some 1 } }
  match SeLe4n.Kernel.timerTick stExpiry with
  | .error err => IO.println s!"timer tick expiry error: {reprStr err}"
  | .ok ((), stExpired) =>
      IO.println s!"timer tick expiry rescheduled current: {reprStr (stExpired.scheduler.current.map SeLe4n.ThreadId.toNat)}"
      match stExpired.objects (SeLe4n.ThreadId.toObjId 1) with
      | some (.tcb tcb) =>
          IO.println s!"timer tick expiry reset slice: {tcb.timeSlice}"
      | _ => IO.println "timer tick expiry: thread not found"

  -- M-05: Domain scheduling — switch domain and verify active domain changes
  let domSchedule : List DomainScheduleEntry :=
    [{ domain := 0, length := 3 }, { domain := 1, length := 5 }]
  let stDom : SystemState := { st1 with
    scheduler := { st1.scheduler with
      runnable := [1, 12], current := some 1,
      activeDomain := 0, domainTimeRemaining := 1,
      domainSchedule := domSchedule, domainScheduleIndex := 0 } }
  match SeLe4n.Kernel.switchDomain stDom with
  | .error err => IO.println s!"domain switch error: {reprStr err}"
  | .ok ((), stSwitched) =>
      IO.println s!"domain switch active domain: {stSwitched.scheduler.activeDomain.toNat}"
      IO.println s!"domain switch time remaining: {stSwitched.scheduler.domainTimeRemaining}"

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
  runWsE4Trace st1
  runWsE6Trace st1

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
  let cnodeObj : KernelObject := .cnode { guard := 0, radix := radix, slots := cnodeSlots }
  let vspaceRoots : List (SeLe4n.ObjId × KernelObject) :=
    (List.range asidCount).map fun i =>
      let oid : SeLe4n.ObjId := ⟨3000 + i⟩
      (oid, .vspaceRoot { asid := ⟨i + 1⟩, mappings := [] })
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
