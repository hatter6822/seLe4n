import SeLe4n
import SeLe4n.Testing.StateBuilder

open SeLe4n.Model

namespace SeLe4n.Testing

private def endpointId : SeLe4n.ObjId := 40
private def cnodeId : SeLe4n.ObjId := 10
private def wrongTypeId : SeLe4n.ObjId := 99
private def sendEmptyEndpointId : SeLe4n.ObjId := 41
private def asidPrimary : SeLe4n.ASID := 2
private def vaddrPrimary : SeLe4n.VAddr := 4096
private def paddrPrimary : SeLe4n.PAddr := 12288

private def slot0 : SeLe4n.Kernel.CSpaceAddr := { cnode := cnodeId, slot := 0 }
private def badSlot : SeLe4n.Kernel.CSpaceAddr := { cnode := wrongTypeId, slot := 0 }

private def baseState : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none })
    |>.withObject cnodeId (.cnode {
      guard := 0
      radix := 0
      slots := [
        (0, {
          target := .object endpointId
          rights := [.read, .write]
          badge := none
        })
      ]
    })
    |>.withObject wrongTypeId (.endpoint { state := .idle, queue := [], waitingReceiver := none })
    |>.withObject sendEmptyEndpointId (.endpoint { state := .send, queue := [], waitingReceiver := none })
    |>.withObject 20 (.vspaceRoot { asid := asidPrimary, mappings := [] })
    |>.withLifecycleObjectType endpointId .endpoint
    |>.withLifecycleObjectType cnodeId .cnode
    |>.withLifecycleObjectType wrongTypeId .endpoint
    |>.withLifecycleObjectType sendEmptyEndpointId .endpoint
    |>.withLifecycleObjectType 20 .vspaceRoot
    |>.withLifecycleCapabilityRef slot0 (.object endpointId)
    |>.build)

private def expectError
    (label : String)
    (actual : Except KernelError α)
    (expected : KernelError) : IO Unit :=
  match actual with
  | .ok _ =>
      throw <| IO.userError s!"{label}: expected error {reprStr expected}, got success"
  | .error err =>
      if err = expected then
        IO.println s!"negative check passed [{label}]: {reprStr err}"
      else
        throw <| IO.userError s!"{label}: expected {reprStr expected}, got {reprStr err}"

private def expectOk
    (label : String)
    (actual : Except KernelError α) : IO α :=
  match actual with
  | .ok value => do
      IO.println s!"positive check passed [{label}]"
      pure value
  | .error err =>
      throw <| IO.userError s!"{label}: expected success, got {reprStr err}"

private def runNegativeChecks : IO Unit := do
  expectError "lookup wrong object type"
    (SeLe4n.Kernel.cspaceLookupSlot badSlot baseState)
    .objectNotFound

  expectError "endpoint receive idle-state mismatch"
    (SeLe4n.Kernel.endpointReceive endpointId baseState)
    .endpointStateMismatch

  expectError "endpoint receive send-state empty queue"
    (SeLe4n.Kernel.endpointReceive sendEmptyEndpointId baseState)
    .endpointQueueEmpty

  expectError "vspace lookup missing asid"
    (SeLe4n.Kernel.Architecture.vspaceLookup 99 vaddrPrimary baseState)
    .asidNotBound

  let (_, stMapped) ← expectOk "vspace map initial"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asidPrimary vaddrPrimary paddrPrimary baseState)

  expectError "vspace duplicate map conflict"
    (SeLe4n.Kernel.Architecture.vspaceMapPage asidPrimary vaddrPrimary paddrPrimary stMapped)
    .mappingConflict

  let (_, stAwait) ← expectOk "await receive handshake seed"
    (SeLe4n.Kernel.endpointAwaitReceive endpointId (SeLe4n.ThreadId.ofNat 7) baseState)

  expectError "await receive second waiter mismatch"
    (SeLe4n.Kernel.endpointAwaitReceive endpointId (SeLe4n.ThreadId.ofNat 8) stAwait)
    .endpointStateMismatch

  let malformedSched : SystemState :=
    (BootstrapBuilder.empty
      |>.withRunnable [SeLe4n.ThreadId.ofNat 77]
      |>.withCurrent none
      |>.build)
  let (_, stScheduled) ← expectOk "schedule malformed runnable target"
    (SeLe4n.Kernel.schedule malformedSched)
  if stScheduled.scheduler.current = none then
    IO.println "negative check passed [scheduler invalid runnable fallback]: current = none"
  else
    throw <| IO.userError "scheduler invalid runnable fallback expected current = none"

end SeLe4n.Testing

def main : IO Unit :=
  SeLe4n.Testing.runNegativeChecks
