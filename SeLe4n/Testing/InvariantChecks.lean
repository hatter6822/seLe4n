import SeLe4n

open SeLe4n.Model

namespace SeLe4n.Testing

private def endpointQueueWellFormedB (ep : Endpoint) : Bool :=
  match ep.state with
  | .idle => ep.sendQueue.isEmpty && ep.receiveQueue.isEmpty
  | .send => !ep.sendQueue.isEmpty && ep.pendingMessages.length == ep.sendQueue.length
  | .receive => !ep.receiveQueue.isEmpty && ep.sendQueue.isEmpty

private def endpointObjectValidB (ep : Endpoint) : Bool :=
  match ep.state with
  | .idle => ep.sendQueue.isEmpty && ep.receiveQueue.isEmpty
  | .send => !ep.sendQueue.isEmpty
  | .receive => !ep.receiveQueue.isEmpty

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

/-- M-11 CSpace coherency: every CNode slot whose capability targets an object has that
object present in the object store. -/
private def cspaceSlotCoherencyChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    match st.objects oid with
    | some (.cnode cn) =>
        cn.slots.foldr (fun (slot, cap) inner =>
          let ok := match cap.target with
            | .object targetId => (st.objects targetId).isSome
            | .cnodeSlot cnId _ => (st.objects cnId).isSome
          (s!"cspace slot target backed: oid={oid} slot={slot}", ok) :: inner) acc
    | _ => acc) []

/-- M-11 Capability rights attenuation: minted (badge-carrying) capabilities must have
rights that are a subset of the source capability's rights. Since the source is not
tracked at runtime, we validate that badge-carrying caps have non-empty rights and
rights belong to the canonical set. This is a conservative structural check. -/
private def capabilityRightsStructuralChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    match st.objects oid with
    | some (.cnode cn) =>
        cn.slots.foldr (fun (slot, cap) inner =>
          let ok := match cap.badge with
            | some _ => !cap.rights.isEmpty
            | none => true
          (s!"capability badge implies non-empty rights: oid={oid} slot={slot}", ok) :: inner) acc
    | _ => acc) []

/-- M-11 Lifecycle metadata consistency: when lifecycle objectType metadata is present
for a materialized object, it must agree with the actual object type. -/
private def lifecycleMetadataChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    match st.objects oid, st.lifecycle.objectTypes oid with
    | some obj, some metaTy =>
        (s!"lifecycle objectType metadata consistent: oid={oid}", metaTy == obj.objectType) :: acc
    | _, _ => acc) []

/-- M-11 Service graph acyclicity: no service has a dependency path back to itself.
Uses bounded BFS from each direct dependency back to the service under test. -/
private def serviceGraphAcyclicityChecks (serviceIds : List ServiceId) (st : SystemState) (fuel : Nat) : List (String × Bool) :=
  serviceIds.map fun sid =>
    let deps := match lookupService st sid with
      | some svc => svc.dependencies
      | none => []
    let hasCycle := deps.any fun dep =>
      SeLe4n.Kernel.serviceHasPathTo st dep sid fuel
    (s!"service graph acyclic: sid={sid}", !hasCycle)

/-- M-11 VSpace ASID uniqueness: no two VSpace root objects share the same ASID. -/
private def vspaceAsidUniquenessChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  let roots : List (SeLe4n.ObjId × SeLe4n.ASID) := objectIds.filterMap fun oid =>
    match st.objects oid with
    | some (.vspaceRoot root) => some (oid, root.asid)
    | _ => none
  roots.map fun (oid, asid) =>
    let duplicates := roots.filter fun (oid', asid') => asid' == asid && oid' != oid
    (s!"vspace ASID unique: oid={oid} asid={asid.toNat}", duplicates.isEmpty)

def stateInvariantChecksFor (objectIds : List SeLe4n.ObjId) (st : SystemState)
    (serviceIds : List ServiceId := []) : List (String × Bool) :=
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
  let fuel := objectIds.length + 256
  schedulerChecks ++ runnableChecks ++ endpointAndNotificationChecks
    ++ cspaceSlotCoherencyChecks objectIds st
    ++ capabilityRightsStructuralChecks objectIds st
    ++ lifecycleMetadataChecks objectIds st
    ++ serviceGraphAcyclicityChecks serviceIds st fuel
    ++ vspaceAsidUniquenessChecks objectIds st

/--
Fallback invariant check surface for callers without an explicit object-id inventory.
Discovers materialized objects from `st.objectIndex` (the finite object store's
monotonic ID list) rather than scanning a hardcoded range.  See audit finding
F-10 and WS-D5.
-/
def stateInvariantChecks (st : SystemState) : List (String × Bool) :=
  stateInvariantChecksFor st.objectIndex st

private def failedChecks (checks : List (String × Bool)) : List String :=
  checks.filterMap fun (label, ok) => if ok then none else some label

def assertStateInvariantsFor (label : String) (objectIds : List SeLe4n.ObjId) (st : SystemState)
    (serviceIds : List ServiceId := []) : IO Unit := do
  let failures := failedChecks (stateInvariantChecksFor objectIds st serviceIds)
  if failures.isEmpty then
    pure ()
  else
    throw <| IO.userError s!"{label}: invariant checks failed: {reprStr failures}"

def assertStateInvariants (label : String) (st : SystemState) : IO Unit :=
  assertStateInvariantsFor label st.objectIndex st

end SeLe4n.Testing
