/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Testing.InvariantChecks

open SeLe4n.Model

namespace SeLe4n.Testing

/-- WS-F7/D2b: Expanded probe operation set covering IPC, notification,
scheduler, and capability families. -/
inductive ProbeOp where
  | send
  | awaitReceive
  | receive
  | notifySignal
  | notifyWait
  | scheduleOp
  | capLookup
  deriving Repr

def probeEndpointId : SeLe4n.ObjId := SeLe4n.ObjId.ofNat 300
/-- WS-F7/D2a: Fixed notification object for probe notification operations. -/
def probeNotificationId : SeLe4n.ObjId := SeLe4n.ObjId.ofNat 301
/-- WS-F7/D2c: Fixed CNode object for probe capability lookup operations. -/
def probeCNodeId : SeLe4n.ObjId := SeLe4n.ObjId.ofNat 302

def probeThreadIds (threadCount : Nat) : List SeLe4n.ObjId :=
  List.range threadCount |>.map fun n => SeLe4n.ObjId.ofNat (n + 1)

/-- WS-F7/D2a-D2c: Probe base state now includes an endpoint, a notification
object, and a CNode with per-thread capability slots for expanded coverage. -/
def probeBaseState (threadCount : Nat) : SystemState :=
  let threadEntries := (List.range threadCount).map fun n =>
    let tid := n + 1
    (SeLe4n.ObjId.ofNat tid, KernelObject.tcb {
      tid := SeLe4n.ThreadId.ofNat tid, priority := SeLe4n.Priority.ofNat 0, domain := default,
      cspaceRoot := probeCNodeId, vspaceRoot := default, ipcBuffer := default,
      ipcState := .ready })
  -- WS-F7/D2c: CNode with one slot per thread targeting the endpoint
  let cnodeSlots : List (SeLe4n.Slot × Capability) :=
    (List.range threadCount).map fun n =>
      (⟨n⟩, { target := .object probeEndpointId,
               rights := AccessRightSet.ofList [.read, .write],
               badge := none })
  let cnodeObj : KernelObject := .cnode {
    depth := 8, guardWidth := 0, guardValue := 0, radixWidth := 8,
    slots := SeLe4n.Kernel.RobinHood.RHTable.ofList cnodeSlots }
  let allEntries :=
    (probeEndpointId, KernelObject.endpoint {}) ::
    (probeNotificationId, KernelObject.notification {
      state := .idle, waitingThreads := [], pendingBadge := none }) ::
    (probeCNodeId, cnodeObj) ::
    threadEntries
  let runnableThreads : List SeLe4n.ThreadId :=
    (List.range threadCount).map fun n => ⟨n + 1⟩
  { (default : SystemState) with
    objects := SeLe4n.Kernel.RobinHood.RHTable.ofList allEntries
    objectIndex := allEntries.map Prod.fst
    objectIndexSet := SeLe4n.Kernel.RobinHood.RHSet.ofList (allEntries.map Prod.fst)
    scheduler := { (default : SchedulerState) with
      runQueue := SeLe4n.Kernel.RunQueue.ofList (runnableThreads.map (fun tid => (tid, ⟨0⟩)))
    }
  }

def nextRand (x : Nat) : Nat :=
  (1664525 * x + 1013904223) % 4294967296

/-- WS-F7/D2e: Distribute across 7 operations (was 3). -/
def pickOp (x : Nat) : ProbeOp :=
  match x % 7 with
  | 0 => .send
  | 1 => .awaitReceive
  | 2 => .receive
  | 3 => .notifySignal
  | 4 => .notifyWait
  | 5 => .scheduleOp
  | _ => .capLookup

def pickThreadId (threadCount : Nat) (x : Nat) : SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofNat ((x % threadCount) + 1)

/-- WS-H12a: Endpoint consistency check using dual-queue fields only.
An endpoint is consistent if sendQ and receiveQ have matching head/tail emptiness. -/
def endpointConsistencyHolds (ep : Endpoint) : Bool :=
  -- Head and tail agree on emptiness for both queues
  (ep.sendQ.head.isNone == ep.sendQ.tail.isNone) &&
  (ep.receiveQ.head.isNone == ep.receiveQ.tail.isNone)

/-- WS-F7/D2f: Object ID inventory includes endpoint, notification, and CNode. -/
def probeInvariantObjectIds (threadCount : Nat) : List SeLe4n.ObjId :=
  probeThreadIds threadCount ++ [probeEndpointId, probeNotificationId, probeCNodeId]

def checkStateInvariants (threadCount : Nat) (st : SystemState) : Except String Unit :=
  let failures := (stateInvariantChecksFor (probeInvariantObjectIds threadCount) st).filterMap fun (label, ok) => if ok then none else some label
  if failures.isEmpty then
    .ok ()
  else
    .error s!"state invariant mismatch: {toString failures}"

def checkEndpointConsistency (st : SystemState) : Except String Unit := do
  match st.objects[probeEndpointId]? with
  | some (.endpoint ep) =>
      if endpointConsistencyHolds ep then
        .ok ()
      else
        .error s!"endpoint invariant mismatch: sendQ={toString ep.sendQ}, receiveQ={toString ep.receiveQ}"
  | some obj => .error s!"probe endpoint object changed unexpectedly: {toString obj}"
  | none => .error "probe endpoint object missing"
  -- WS-F7: verify notification object still exists and has valid state
  match st.objects[probeNotificationId]? with
  | some (.notification _) => .ok ()
  | some obj => .error s!"probe notification object changed unexpectedly: {toString obj}"
  | none => .error "probe notification object missing"

/-- Outcome of a single probe step, distinguishing actual mutations from expected failures
and unexpected failures. -/
inductive StepOutcome where
  | mutated (st' : SystemState)
  | expectedFailure (err : KernelError)
  | unexpectedFailure (err : KernelError) (detail : String)

/-- Classify a KernelError as expected or unexpected for the probe context.

Expected errors: state-mismatch, empty-queue, alreadyWaiting, and scheduler
invariant violations are normal when the random operation doesn't match the
current state machine position.

Unexpected errors: objectNotFound and invalidCapability should never occur because
the probe operates on known objects at fixed ObjIds. -/
def classifyError (op : ProbeOp) (err : KernelError) : StepOutcome :=
  match err with
  | .endpointStateMismatch => .expectedFailure err
  | .endpointQueueEmpty => .expectedFailure err
  | .alreadyWaiting => .expectedFailure err
  -- WS-F7: scheduler may fail if no runnable thread in active domain
  | .schedulerInvariantViolation => .expectedFailure err
  -- WS-F7: invalidCapability is expected for capLookup on empty slots
  | .invalidCapability =>
      match op with
      | .capLookup => .expectedFailure err
      | _ => .unexpectedFailure err s!"invalidCapability during {toString op}: probe objects should be correctly typed"
  | .objectNotFound =>
      match op with
      -- capLookup on a non-existent CNode slot returns objectNotFound
      | .capLookup => .expectedFailure err
      | _ => .unexpectedFailure err s!"objectNotFound during {toString op}: probe objects should always exist"
  | other =>
      .unexpectedFailure other s!"unexpected error {toString other} during {toString op}"

/-- Execute one probe operation with error-aware classification.

WS-F7/D2d: Extended to cover 7 operation families (was 3). Each new operation
uses the fixed probe objects (endpoint, notification, CNode) and classifies
errors as expected or unexpected based on the operation semantics.

Guard: IPC and notification operations that modify thread ipcState are skipped
when the target thread is already blocked. In a real kernel, blocked threads
cannot initiate new operations; without this guard the random probe would
create inconsistent state (e.g., a thread on a notification waiting list with
ipcState changed by a subsequent endpoint send). -/
def stepOp (op : ProbeOp) (tid : SeLe4n.ThreadId) (st : SystemState) : StepOutcome :=
  -- Guard: skip state-modifying IPC ops on already-blocked threads
  let threadBlocked := match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.ipcState != .ready
    | _ => false
  match op with
  -- WS-G7: migrated to dual-queue operations
  | .send =>
      if threadBlocked == true then .expectedFailure .endpointStateMismatch
      else match SeLe4n.Kernel.endpointSendDualChecked SeLe4n.Kernel.defaultLabelingContext probeEndpointId tid .empty st with
      | .ok (_, st') => .mutated st'
      | .error err => classifyError .send err
  | .awaitReceive =>
      if threadBlocked == true then .expectedFailure .endpointStateMismatch
      else match SeLe4n.Kernel.endpointReceiveDual probeEndpointId tid st with
      | .ok (_, st') => .mutated st'
      | .error err => classifyError .awaitReceive err
  | .receive =>
      if threadBlocked == true then .expectedFailure .endpointStateMismatch
      else match SeLe4n.Kernel.endpointReceiveDual probeEndpointId tid st with
      | .ok (_, st') => .mutated st'
      | .error err => classifyError .receive err
  -- WS-F7/D2d: Notification signal — wake a waiter or accumulate badge
  -- (signal does not modify the signalling thread's state, so no guard needed)
  | .notifySignal =>
      let badge := SeLe4n.Badge.ofNatMasked (tid.toNat * 7 + 1)
      match SeLe4n.Kernel.notificationSignal probeNotificationId badge st with
      | .ok (_, st') => .mutated st'
      | .error err => classifyError .notifySignal err
  -- WS-F7/D2d: Notification wait — consume badge or block caller
  | .notifyWait =>
      if threadBlocked == true then .expectedFailure .alreadyWaiting
      else match SeLe4n.Kernel.notificationWait probeNotificationId tid st with
      | .ok (_, st') => .mutated st'
      | .error err => classifyError .notifyWait err
  -- WS-F7/D2d: Schedule — pick best runnable thread in active domain
  | .scheduleOp =>
      match SeLe4n.Kernel.schedule st with
      | .ok (_, st') => .mutated st'
      | .error err => classifyError .scheduleOp err
  -- WS-F7/D2d: Capability lookup — exercise CSpace resolution
  | .capLookup =>
      let addr : SeLe4n.Kernel.CSpaceAddr := { cnode := probeCNodeId, slot := ⟨tid.toNat % 16⟩ }
      match SeLe4n.Kernel.cspaceLookupSlot addr st with
      | .ok (_, st') => .mutated st'
      | .error err => classifyError .capLookup err

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
    .error s!"probe completed with {stats.unexpectedFailures.length} unexpected failure(s): {toString stats.unexpectedFailures}"

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
