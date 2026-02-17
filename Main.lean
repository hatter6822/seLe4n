import SeLe4n
import SeLe4n.Testing.RuntimeContractFixtures

open SeLe4n.Model

def rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 0 }
def lifecycleAuthSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 5 }
def mintedSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 11, slot := 3 }
def siblingSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 11, slot := 4 }
def demoEndpoint : SeLe4n.ObjId := 30
def svcDb : ServiceId := 100
def svcApi : ServiceId := 101
def svcDenied : ServiceId := 102
def svcBroken : ServiceId := 103
def svcRestart : ServiceId := 104
def svcRestartBroken : ServiceId := 105

/-- Demonstrate a tiny executable path through scheduler + CSpace + IPC transitions.

The original scheduler/CSpace/M3 queue-delivery sequence is preserved, and the M3.5
waiting-receiver handshake story is appended before replaying the queued-sender receive path. -/
def bootstrapState : SystemState :=
  { (default : SystemState) with
    objects := fun oid =>
      if oid = 1 then
        some (.tcb {
          tid := 1
          priority := 100
          domain := 0
          cspaceRoot := 10
          vspaceRoot := 20
          ipcBuffer := 4096
          ipcState := .ready
        })
      else if oid = 10 then
        some (.cnode {
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
      else if oid = 12 then
        some (.tcb {
          tid := 12
          priority := 10
          domain := 0
          cspaceRoot := 10
          vspaceRoot := 20
          ipcBuffer := 8192
          ipcState := .ready
        })
      else if oid = 11 then
        some (.cnode CNode.empty)
      else if oid = 20 then
        some (.vspaceRoot { asid := 1, mappings := [] })
      else if oid = demoEndpoint then
        some (.endpoint { state := .idle, queue := [], waitingReceiver := none })
      else
        none
    services := fun sid =>
      if sid = svcDb then
        some {
          identity := { sid := svcDb, backingObject := 12, owner := 10 }
          status := .running
          dependencies := []
          isolatedFrom := []
        }
      else if sid = svcApi then
        some {
          identity := { sid := svcApi, backingObject := 1, owner := 10 }
          status := .stopped
          dependencies := [svcDb]
          isolatedFrom := [svcDenied]
        }
      else if sid = svcDenied then
        some {
          identity := { sid := svcDenied, backingObject := 1, owner := 10 }
          status := .stopped
          dependencies := []
          isolatedFrom := []
        }
      else if sid = svcBroken then
        some {
          identity := { sid := svcBroken, backingObject := 1, owner := 10 }
          status := .stopped
          dependencies := [999]
          isolatedFrom := []
        }
      else if sid = svcRestart then
        some {
          identity := { sid := svcRestart, backingObject := 12, owner := 10 }
          status := .running
          dependencies := [svcDb]
          isolatedFrom := []
        }
      else if sid = svcRestartBroken then
        some {
          identity := { sid := svcRestartBroken, backingObject := 12, owner := 10 }
          status := .running
          dependencies := [999]
          isolatedFrom := []
        }
      else
        none
    scheduler := { runnable := [1, 2], current := none }
    lifecycle := {
      objectTypes := fun oid =>
        if oid = 1 then some .tcb
        else if oid = 10 then some .cnode
        else if oid = 12 then some .tcb
        else if oid = 11 then some .cnode
        else if oid = 20 then some .vspaceRoot
        else if oid = demoEndpoint then some .endpoint
        else none
      capabilityRefs := fun ref =>
        if ref = rootSlot then some (.object 1)
        else if ref = lifecycleAuthSlot then some (.object 12)
        else none
    }
  }





def main : IO Unit := do
  match SeLe4n.Kernel.schedule bootstrapState with
  | .error err => IO.println s!"scheduler error: {reprStr err}"
  | .ok (_, st1) =>
      IO.println s!"scheduled thread: {reprStr (st1.scheduler.current.map SeLe4n.ThreadId.toNat)}"
      match SeLe4n.Kernel.cspaceLookupSlot rootSlot st1 with
      | .error err => IO.println s!"source lookup error: {reprStr err}"
      | .ok (srcCap, _) =>
          IO.println s!"source cap rights before mint: {reprStr srcCap.rights}"
      match SeLe4n.Kernel.Architecture.adapterAdvanceTimer SeLe4n.Testing.runtimeContractAcceptAll 2 st1 with
      | .error err => IO.println s!"adapter timer success path error: {reprStr err}"
      | .ok (_, stTimer) =>
          IO.println s!"adapter timer success path value: {reprStr stTimer.machine.timer}"
      match SeLe4n.Kernel.Architecture.adapterAdvanceTimer SeLe4n.Testing.runtimeContractAcceptAll 0 st1 with
      | .error err => IO.println s!"adapter timer invalid-context branch: {reprStr err}"
      | .ok _ =>
          IO.println "unexpected adapter timer success with zero ticks"
      match SeLe4n.Kernel.Architecture.adapterAdvanceTimer SeLe4n.Testing.runtimeContractDenyAll 1 st1 with
      | .error err => IO.println s!"adapter timer unsupported branch: {reprStr err}"
      | .ok _ =>
          IO.println "unexpected adapter timer success under denied contract"
      match SeLe4n.Kernel.Architecture.adapterReadMemory SeLe4n.Testing.runtimeContractDenyAll 0 st1 with
      | .error err => IO.println s!"adapter read denied branch: {reprStr err}"
      | .ok _ =>
          IO.println "unexpected adapter read success under denied contract"
      match SeLe4n.Kernel.Architecture.adapterReadMemory SeLe4n.Testing.runtimeContractAcceptAll 0 st1 with
      | .error err => IO.println s!"adapter read success path error: {reprStr err}"
      | .ok (byte, _) =>
          IO.println s!"adapter read success path byte: {reprStr byte}"

      match SeLe4n.Kernel.Architecture.vspaceMapPage 1 4096 8192 st1 with
      | .error err => IO.println s!"vspace map error: {reprStr err}"
      | .ok (_, stV1) =>
          match SeLe4n.Kernel.Architecture.vspaceLookup 1 4096 stV1 with
          | .error err => IO.println s!"vspace lookup error: {reprStr err}"
          | .ok (paddr, stV2) =>
              IO.println s!"vspace lookup mapped paddr: {reprStr paddr}"
              match SeLe4n.Kernel.Architecture.vspaceUnmapPage 1 4096 stV2 with
              | .error err => IO.println s!"vspace unmap error: {reprStr err}"
              | .ok (_, stV3) =>
                  match SeLe4n.Kernel.Architecture.vspaceLookup 1 4096 stV3 with
                  | .error err => IO.println s!"vspace lookup after unmap branch: {reprStr err}"
                  | .ok (resolved, _) => IO.println s!"unexpected vspace lookup after unmap: {reprStr resolved}"
      match SeLe4n.Kernel.Architecture.adapterWriteRegister SeLe4n.Testing.runtimeContractAcceptAll 7 99 st1 with
      | .error err => IO.println s!"adapter register write success path error: {reprStr err}"
      | .ok (_, stReg) =>
          IO.println s!"adapter register write success path value: {reprStr <| SeLe4n.readReg stReg.machine.regs 7}"
      match SeLe4n.Kernel.Architecture.adapterWriteRegister SeLe4n.Testing.runtimeContractDenyAll 7 99 st1 with
      | .error err => IO.println s!"adapter register write unsupported branch: {reprStr err}"
      | .ok _ =>
          IO.println "unexpected adapter register write success under denied contract"
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
      match SeLe4n.Kernel.serviceRestart svcRestart allowAll allowAll st1 with
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
      match SeLe4n.Kernel.serviceRestart svcRestart denyAll allowAll st1 with
      | .error err => IO.println s!"service restart stop-stage failure: {reprStr err}"
      | .ok _ =>
          IO.println "unexpected service restart success when stop policy denies"
      match SeLe4n.Kernel.serviceRestart svcRestartBroken allowAll allowAll st1 with
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

      let largeRunnable : List SeLe4n.ThreadId :=
        (List.range 12).map (fun i => SeLe4n.ThreadId.ofNat (i + 1))
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
            else st1.objects oid
        }
      match SeLe4n.Kernel.endpointSend demoEndpoint 4 stMultiEndpoint with
      | .error err => IO.println s!"multi-endpoint send A error: {reprStr err}"
      | .ok (_, stEp1) =>
          match SeLe4n.Kernel.endpointSend 31 5 stEp1 with
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

      match SeLe4n.Kernel.Architecture.adapterReadMemory SeLe4n.Testing.runtimeContractAcceptAll 0 st1 with
      | .error err => IO.println s!"boundary memory low-address error: {reprStr err}"
      | .ok (byte, _) => IO.println s!"boundary memory low-address byte: {reprStr byte}"
      match SeLe4n.Kernel.Architecture.adapterReadMemory SeLe4n.Testing.runtimeContractAcceptAll 18446744073709551615 st1 with
      | .error err => IO.println s!"boundary memory high-address error: {reprStr err}"
      | .ok (byte, _) => IO.println s!"boundary memory high-address byte: {reprStr byte}"

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
      match SeLe4n.Kernel.cspaceMint rootSlot mintedSlot [.read] none st1 with
      | .error err => IO.println s!"cspace mint error: {reprStr err}"
      | .ok (_, st2) =>
          match SeLe4n.Kernel.cspaceMint rootSlot siblingSlot [.read] none st2 with
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
                          match SeLe4n.Kernel.endpointSend demoEndpoint 1 st6 with
                          | .error err => IO.println s!"endpoint handshake send error: {reprStr err}"
                          | .ok (_, st7) =>
                              IO.println "handshake send matched waiting receiver"
                              match SeLe4n.Kernel.endpointSend demoEndpoint 1 st7 with
                              | .error err => IO.println s!"endpoint send #1 error: {reprStr err}"
                              | .ok (_, st8) =>
                                  match SeLe4n.Kernel.endpointSend demoEndpoint 2 st8 with
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
          match SeLe4n.Kernel.cspaceLookupSlot mintedSlot st2 with
          | .error err => IO.println s!"cspace lookup error: {reprStr err}"
          | .ok (cap, _) =>
              IO.println s!"minted cap rights: {reprStr cap.rights}"
