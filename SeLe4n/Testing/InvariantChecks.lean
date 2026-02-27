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

private def lookupQueueTcbB (st : SystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  match st.objects tid.toObjId with
  | some (.tcb tcb) => some tcb
  | _ => none

private partial def intrusiveQueueReachable
    (st : SystemState)
    (tail : SeLe4n.ThreadId)
    (expectedPrev : Option SeLe4n.ThreadId)
    (expectedPPrev : Option QueuePPrev)
    (cursor : Option SeLe4n.ThreadId)
    (visited : List SeLe4n.ThreadId)
    (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      match cursor with
      | none => false
      | some tid =>
          if tid ∈ visited then
            false
          else
            match lookupQueueTcbB st tid with
            | none => false
            | some tcb =>
                if tcb.queuePrev != expectedPrev || tcb.queuePPrev != expectedPPrev then
                  false
                else if tid == tail then
                  tcb.queueNext.isNone
                else
                  match tcb.queueNext with
                  | none => false
                  | some nextTid =>
                      intrusiveQueueReachable st tail (some tid) (some (.tcbNext tid)) (some nextTid) (tid :: visited) fuel

private def intrusiveQueueWellFormedB (st : SystemState) (q : IntrusiveQueue) : Bool :=
  match q.head, q.tail with
  | none, none => true
  | some head, some tail =>
      match lookupQueueTcbB st head, lookupQueueTcbB st tail with
      | some headTcb, some tailTcb =>
          headTcb.queuePrev.isNone
            && headTcb.queuePPrev = some .endpointHead
            && tailTcb.queueNext.isNone
            && intrusiveQueueReachable st tail none (some .endpointHead) (some head) [] (st.objectIndex.length + 1)
      | _, _ => false
  | _, _ => false

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
            | .replyCap tid => (st.objects tid.toObjId).isSome
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
          (s!"endpoint intrusive sendQ invariant: oid={oid}", intrusiveQueueWellFormedB st ep.sendQ) ::
          (s!"endpoint intrusive receiveQ invariant: oid={oid}", intrusiveQueueWellFormedB st ep.receiveQ) ::
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
