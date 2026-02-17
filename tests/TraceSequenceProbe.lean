import SeLe4n

open SeLe4n.Model

namespace SeLe4n.Testing

inductive ProbeOp where
  | send
  | awaitReceive
  | receive
  deriving Repr

def probeEndpointId : SeLe4n.ObjId := 300

def probeBaseState : SystemState :=
  { (default : SystemState) with
    objects := fun oid =>
      if oid = probeEndpointId then
        some (.endpoint { state := .idle, queue := [], waitingReceiver := none })
      else
        none
  }

def nextRand (x : Nat) : Nat :=
  (1664525 * x + 1013904223) % 4294967296

def pickOp (x : Nat) : ProbeOp :=
  match x % 3 with
  | 0 => .send
  | 1 => .awaitReceive
  | _ => .receive

def pickThreadId (x : Nat) : SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofNat ((x % 8) + 1)

def endpointConsistencyHolds (ep : Endpoint) : Bool :=
  match ep.state, ep.queue.isEmpty, ep.waitingReceiver.isSome with
  | .idle, true, false => true
  | .send, false, false => true
  | .receive, true, true => true
  | _, _, _ => false

def checkEndpointConsistency (st : SystemState) : Except String Unit :=
  match st.objects probeEndpointId with
  | some (.endpoint ep) =>
      if endpointConsistencyHolds ep then
        .ok ()
      else
        .error s!"endpoint invariant mismatch: state={reprStr ep.state}, queue={reprStr ep.queue}, waitingReceiver={reprStr ep.waitingReceiver}"
  | some obj => .error s!"probe endpoint object changed unexpectedly: {reprStr obj}"
  | none => .error "probe endpoint object missing"

def stepOp (op : ProbeOp) (tid : SeLe4n.ThreadId) (st : SystemState) : SystemState :=
  match op with
  | .send =>
      match SeLe4n.Kernel.endpointSend probeEndpointId tid st with
      | .ok (_, st') => st'
      | .error _ => st
  | .awaitReceive =>
      match SeLe4n.Kernel.endpointAwaitReceive probeEndpointId tid st with
      | .ok (_, st') => st'
      | .error _ => st
  | .receive =>
      match SeLe4n.Kernel.endpointReceive probeEndpointId st with
      | .ok (_, st') => st'
      | .error _ => st

partial def runProbeLoop (steps : Nat) (seed : Nat) (st : SystemState) : Except String Unit := do
  checkEndpointConsistency st
  if steps = 0 then
    .ok ()
  else
    let next := nextRand seed
    let op := pickOp next
    let tid := pickThreadId next
    let st' := stepOp op tid st
    runProbeLoop (steps - 1) next st'

def runProbe (seed : Nat) (steps : Nat) : Except String Unit :=
  runProbeLoop steps seed probeBaseState

end SeLe4n.Testing

private def parseNatArg (value : String) (fallback : Nat) : Nat :=
  match value.toNat? with
  | some n => n
  | none => fallback

def main (args : List String) : IO Unit := do
  let seed := parseNatArg (args.getD 0 "7") 7
  let steps := parseNatArg (args.getD 1 "250") 250
  match SeLe4n.Testing.runProbe seed steps with
  | .ok _ =>
      IO.println s!"trace sequence probe passed: seed={seed}, steps={steps}"
  | .error msg =>
      throw <| IO.userError s!"trace sequence probe failed: seed={seed}, steps={steps}, detail={msg}"
