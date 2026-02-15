import SeLe4n

open SeLe4n.Model

def rootSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := 10, slot := 0 }
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
              }) ]
        })
      else if oid = 11 then
        some (.cnode CNode.empty)
      else if oid = demoEndpoint then
        some (.endpoint { state := .idle, queue := [], waitingReceiver := none })
      else
        none
    scheduler := { runnable := [1, 2], current := none }
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
      match SeLe4n.Kernel.cspaceMint rootSlot mintedSlot [.read] none st1 with
      | .error err => IO.println s!"cspace mint error: {reprStr err}"
      | .ok (_, st2) =>
          match SeLe4n.Kernel.cspaceMint rootSlot siblingSlot [.read] none st2 with
          | .error err => IO.println s!"sibling mint error: {reprStr err}"
          | .ok (_, st3) =>
              IO.println "created sibling cap with the same target"
              match SeLe4n.Kernel.cspaceRevoke mintedSlot st3 with
              | .error err => IO.println s!"cspace revoke error: {reprStr err}"
              | .ok (_, st4) =>
                  match SeLe4n.Kernel.cspaceLookupSlot siblingSlot st4 with
                  | .error err => IO.println s!"post-revoke sibling lookup: {reprStr err}"
                  | .ok (cap, _) =>
                      IO.println s!"unexpected sibling cap after revoke: {reprStr cap}"
                  match SeLe4n.Kernel.cspaceDeleteSlot mintedSlot st4 with
                  | .error err => IO.println s!"cspace delete error: {reprStr err}"
                  | .ok (_, st5) =>
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
