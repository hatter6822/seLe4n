import SeLe4n

open SeLe4n.Model

def rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 0 }
def lifecycleAuthSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 5 }
def mintedSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 11, slot := 3 }
def siblingSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 11, slot := 4 }
def demoEndpoint : SeLe4n.ObjId := 30

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
      else if oid = demoEndpoint then
        some (.endpoint { state := .idle, queue := [], waitingReceiver := none })
      else
        none
    scheduler := { runnable := [1, 2], current := none }
    lifecycle := {
      objectTypes := fun oid =>
        if oid = 1 then some .tcb
        else if oid = 10 then some .cnode
        else if oid = 12 then some .tcb
        else if oid = 11 then some .cnode
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
      IO.println s!"scheduled thread: {reprStr st1.scheduler.current}"
      match SeLe4n.Kernel.cspaceLookupSlot rootSlot st1 with
      | .error err => IO.println s!"source lookup error: {reprStr err}"
      | .ok (srcCap, _) =>
          IO.println s!"source cap rights before mint: {reprStr srcCap.rights}"
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
