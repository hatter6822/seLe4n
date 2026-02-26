import SeLe4n
import SeLe4n.Testing.InvariantChecks

open SeLe4n.Model

namespace SeLe4n.Testing

inductive ProbeOp where
  | send
  | awaitReceive
  | receive
  deriving Repr

def probeEndpointId : SeLe4n.ObjId := 300

def probeThreadIds (threadCount : Nat) : List SeLe4n.ObjId :=
  List.range threadCount |>.map fun n => SeLe4n.ObjId.ofNat (n + 1)

def probeBaseState (threadCount : Nat) : SystemState :=
  { (default : SystemState) with
    objects := fun oid =>
      if oid = probeEndpointId then
        some (.endpoint { state := .idle, queue := [], waitingReceiver := none })
      else if oid.toNat ≥ 1 ∧ oid.toNat ≤ threadCount then
        some (.tcb { tid := SeLe4n.ThreadId.ofNat oid.toNat
                   , priority := 0
                   , domain := default
                   , cspaceRoot := default
                   , vspaceRoot := default
                   , ipcBuffer := default
                   , ipcState := .ready })
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

def pickThreadId (threadCount : Nat) (x : Nat) : SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofNat ((x % threadCount) + 1)

def endpointConsistencyHolds (ep : Endpoint) : Bool :=
  match ep.state, ep.queue.isEmpty, ep.waitingReceiver.isSome with
  | .idle, true, false => true
  | .send, false, false => true
  | .receive, true, true => true
  | _, _, _ => false

def probeInvariantObjectIds (threadCount : Nat) : List SeLe4n.ObjId :=
  probeThreadIds threadCount ++ [probeEndpointId]

def checkStateInvariants (threadCount : Nat) (st : SystemState) : Except String Unit :=
  let failures := (stateInvariantChecksFor (probeInvariantObjectIds threadCount) st).filterMap fun (label, ok) => if ok then none else some label
  if failures.isEmpty then
    .ok ()
  else
    .error s!"state invariant mismatch: {reprStr failures}"

def checkEndpointConsistency (st : SystemState) : Except String Unit :=
  match st.objects probeEndpointId with
  | some (.endpoint ep) =>
      if endpointConsistencyHolds ep then
        .ok ()
      else
        .error s!"endpoint invariant mismatch: state={reprStr ep.state}, queue={reprStr ep.queue}, waitingReceiver={reprStr ep.waitingReceiver}"
  | some obj => .error s!"probe endpoint object changed unexpectedly: {reprStr obj}"
  | none => .error "probe endpoint object missing"

/-- Outcome of a single probe step, distinguishing actual mutations from expected failures
and unexpected failures. -/
inductive StepOutcome where
  | mutated (st' : SystemState)
  | expectedFailure (err : KernelError)
  | unexpectedFailure (err : KernelError) (detail : String)

/-- Classify a KernelError as expected or unexpected for the probe context.

Expected errors: state-mismatch and empty-queue errors are normal when the random
operation doesn't match the current endpoint state machine position.

Unexpected errors: objectNotFound and invalidCapability should never occur because
the probe operates on a known endpoint object at a fixed ObjId. -/
def classifyError (op : ProbeOp) (err : KernelError) : StepOutcome :=
  match err with
  | .endpointStateMismatch => .expectedFailure err
  | .endpointQueueEmpty => .expectedFailure err
  | .objectNotFound =>
      .unexpectedFailure err s!"objectNotFound during {reprStr op}: probe endpoint (oid={probeEndpointId}) should always exist"
  | .invalidCapability =>
      .unexpectedFailure err s!"invalidCapability during {reprStr op}: probe endpoint (oid={probeEndpointId}) should be an endpoint object"
  | other =>
      .unexpectedFailure other s!"unexpected error {reprStr other} during {reprStr op}"

/-- Execute one probe operation with error-aware classification.

Unlike the original `stepOp` which silently returned unchanged state on any error,
this function classifies each error and returns a structured outcome. -/
def stepOp (op : ProbeOp) (tid : SeLe4n.ThreadId) (st : SystemState) : StepOutcome :=
  match op with
  | .send =>
      match SeLe4n.Kernel.endpointSend probeEndpointId tid st with
      | .ok (_, st') => .mutated st'
      | .error err => classifyError .send err
  | .awaitReceive =>
      match SeLe4n.Kernel.endpointAwaitReceive probeEndpointId tid st with
      | .ok (_, st') => .mutated st'
      | .error err => classifyError .awaitReceive err
  | .receive =>
      match SeLe4n.Kernel.endpointReceive probeEndpointId st with
      | .ok (_, st') => .mutated st'
      | .error err => classifyError .receive err

/-- Accumulated probe statistics for reporting. -/
structure ProbeStats where
  totalSteps : Nat
  mutations : Nat
  expectedFailures : Nat
  unexpectedFailures : List String
  deriving Repr

instance : Inhabited ProbeStats where
  default := { totalSteps := 0, mutations := 0, expectedFailures := 0, unexpectedFailures := [] }

partial def runProbeLoop (threadCount : Nat) (steps : Nat) (seed : Nat) (st : SystemState)
    (stats : ProbeStats) : Except String (ProbeStats × SystemState) := do
  checkEndpointConsistency st
  checkStateInvariants threadCount st
  if steps = 0 then
    .ok (stats, st)
  else
    let next := nextRand seed
    let op := pickOp next
    let tid := pickThreadId threadCount next
    let stats' := { stats with totalSteps := stats.totalSteps + 1 }
    match stepOp op tid st with
    | .mutated st' =>
        -- Invariant checks run here on the ACTUALLY MUTATED state
        runProbeLoop threadCount (steps - 1) next st' { stats' with mutations := stats'.mutations + 1 }
    | .expectedFailure _ =>
        -- State unchanged; skip redundant invariant re-check on the no-op state
        runProbeLoop threadCount (steps - 1) next st { stats' with expectedFailures := stats'.expectedFailures + 1 }
    | .unexpectedFailure _ detail =>
        -- Record the unexpected failure but continue probing to collect all failures
        let stats'' := { stats' with unexpectedFailures := stats'.unexpectedFailures ++ [detail] }
        runProbeLoop threadCount (steps - 1) next st stats''

/-- Derive thread count from seed. Range: 2–16 (at least 2 for sender/receiver IPC). -/
def pickThreadCount (seed : Nat) : Nat :=
  (seed % 15) + 2

def runProbe (seed : Nat) (steps : Nat) : Except String (ProbeStats × Nat) := do
  let threadCount := pickThreadCount seed
  let (stats, _) ← runProbeLoop threadCount steps seed (probeBaseState threadCount) default
  -- After the loop, report any unexpected failures as a probe failure
  if stats.unexpectedFailures.isEmpty then
    .ok (stats, threadCount)
  else
    .error s!"probe completed with {stats.unexpectedFailures.length} unexpected failure(s): {reprStr stats.unexpectedFailures}"

end SeLe4n.Testing

private def parseNatArg (value : String) (fallback : Nat) : Nat :=
  match value.toNat? with
  | some n => n
  | none => fallback

def main (args : List String) : IO Unit := do
  let seed := parseNatArg (args.getD 0 "7") 7
  let steps := parseNatArg (args.getD 1 "250") 250
  match SeLe4n.Testing.runProbe seed steps with
  | .ok (stats, threadCount) =>
      IO.println s!"trace sequence probe passed: seed={seed}, steps={steps}, threads={threadCount}, mutations={stats.mutations}, expectedFailures={stats.expectedFailures}, unexpectedFailures=0"
  | .error msg =>
      throw <| IO.userError s!"trace sequence probe failed: seed={seed}, steps={steps}, detail={msg}"
