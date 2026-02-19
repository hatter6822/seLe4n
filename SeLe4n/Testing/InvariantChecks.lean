import SeLe4n

open SeLe4n.Model

namespace SeLe4n.Testing

private def endpointQueueWellFormedB (ep : Endpoint) : Bool :=
  match ep.state with
  | .idle => ep.queue.isEmpty && !ep.waitingReceiver.isSome
  | .send => !ep.queue.isEmpty && !ep.waitingReceiver.isSome
  | .receive => ep.queue.isEmpty && ep.waitingReceiver.isSome

private def endpointObjectValidB (ep : Endpoint) : Bool :=
  match ep.waitingReceiver with
  | none => ep.state != .receive
  | some _ => ep.state == .receive

private def notificationQueueWellFormedB (ntfn : Notification) : Bool :=
  match ntfn.state with
  | .idle => ntfn.waitingThreads.isEmpty && !ntfn.pendingBadge.isSome
  | .waiting => !ntfn.waitingThreads.isEmpty && !ntfn.pendingBadge.isSome
  | .active => ntfn.waitingThreads.isEmpty && ntfn.pendingBadge.isSome

private def schedulerQueueCurrentConsistentB (st : SystemState) : Bool :=
  match st.scheduler.current with
  | none => true
  | some tid => tid ∈ st.scheduler.runnable

private def schedulerRunQueueUniqueB (st : SystemState) : Bool :=
  st.scheduler.runnable.Nodup

private def currentThreadValidB (st : SystemState) : Bool :=
  match st.scheduler.current with
  | none => true
  | some tid =>
      match st.objects tid.toObjId with
      | some (.tcb _) => true
      | _ => false

def stateInvariantChecksFor (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  let schedulerChecks : List (String × Bool) :=
    [ ("scheduler queue/current consistency", schedulerQueueCurrentConsistentB st)
    , ("scheduler runnable queue uniqueness", schedulerRunQueueUniqueB st)
    , ("scheduler current thread validity", currentThreadValidB st)
    ]
  let runnableChecks : List (String × Bool) :=
    st.scheduler.runnable.map fun tid =>
      let label := s!"runnable thread resolves to ready TCB: tid={tid.toNat}"
      let ok :=
        match st.objects tid.toObjId with
        | some (.tcb tcb) => tcb.ipcState == .ready
        | _ => false
      (label, ok)
  let endpointAndNotificationChecks : List (String × Bool) :=
    objectIds.foldr (fun oid acc =>
      match st.objects oid with
      | some (.endpoint ep) =>
          (s!"endpoint queue/state invariant: oid={oid}", endpointQueueWellFormedB ep) ::
          (s!"endpoint waiter/state invariant: oid={oid}", endpointObjectValidB ep) :: acc
      | some (.notification ntfn) =>
          (s!"notification queue/state invariant: oid={oid}", notificationQueueWellFormedB ntfn) :: acc
      | _ => acc) []
  schedulerChecks ++ runnableChecks ++ endpointAndNotificationChecks

/--
Fallback invariant check surface for callers without an explicit object-id inventory.
The bounded discovery window is intentionally finite and should be replaced by
`stateInvariantChecksFor` at call sites that can provide exact fixture IDs.
-/
def stateInvariantChecks (st : SystemState) : List (String × Bool) :=
  let defaultIds := (List.range 512).map SeLe4n.ObjId.ofNat
  stateInvariantChecksFor defaultIds st

private def failedChecks (checks : List (String × Bool)) : List String :=
  checks.filterMap fun (label, ok) => if ok then none else some label

def assertStateInvariantsFor (label : String) (objectIds : List SeLe4n.ObjId) (st : SystemState) : IO Unit := do
  let failures := failedChecks (stateInvariantChecksFor objectIds st)
  if failures.isEmpty then
    pure ()
  else
    throw <| IO.userError s!"{label}: invariant checks failed: {reprStr failures}"

def assertStateInvariants (label : String) (st : SystemState) : IO Unit :=
  assertStateInvariantsFor label ((List.range 512).map SeLe4n.ObjId.ofNat) st

end SeLe4n.Testing
