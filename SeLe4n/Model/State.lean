import SeLe4n.Machine
import SeLe4n.Model.Object

namespace SeLe4n.Model

inductive KernelError where
  | invalidCapability
  | objectNotFound
  | illegalState
  | illegalAuthority
  | policyDenied
  | dependencyViolation
  | schedulerInvariantViolation
  | endpointStateMismatch
  | endpointQueueEmpty
  | asidNotBound
  | vspaceRootInvalid
  | mappingConflict
  | translationFault
  | flowDenied
  | alreadyWaiting
  | cyclicDependency
  | notImplemented
  | targetSlotOccupied   -- WS-E4/H-02: insert into occupied slot
  | replyCapInvalid      -- WS-E4/M-12: reply target not in blockedOnReply state
  deriving Repr, DecidableEq

/-- WS-E6/M-05: Scheduler state with domain scheduling support.

`activeDomain` tracks the currently executing scheduling domain. In seL4, the
kernel partitions CPU time into fixed-length domain slots — only threads whose
`TCB.domain` matches `activeDomain` are eligible for scheduling within the
current slot. `domainTicks` counts remaining ticks in the current domain slot;
when exhausted, the scheduler rotates to the next domain.

The `domainSchedule` list defines the round-robin domain rotation order with
per-domain tick budgets. When `domainTicks` reaches 0, the scheduler advances
to the next `(DomainId, tickBudget)` entry in the schedule. -/
structure SchedulerState where
  runnable : List SeLe4n.ThreadId
  current : Option SeLe4n.ThreadId
  activeDomain : SeLe4n.DomainId := 0              -- WS-E6/M-05
  domainTicks : Nat := 5                            -- WS-E6/M-05
  domainSchedule : List (SeLe4n.DomainId × Nat) := [(0, 5)] -- WS-E6/M-05
  domainScheduleIndex : Nat := 0                    -- WS-E6/M-05
  deriving Repr, DecidableEq

/-- Architecture-neutral address of a capability slot inside a CNode object. -/
structure SlotRef where
  cnode : SeLe4n.ObjId
  slot : SeLe4n.Slot
  deriving Repr, DecidableEq

/-- Lifecycle metadata required by the first M4-A transition story.

`objectTypes` keeps object-store identity explicit, while `capabilityRefs` records the target
named by each populated capability slot reference. -/
structure LifecycleMetadata where
  objectTypes : SeLe4n.ObjId → Option KernelObjectType
  capabilityRefs : SlotRef → Option CapTarget

/-- WS-E6/F-17/L-05: Global kernel system state.

**O(n) data-structure design decision (F-17):** The `objects` field is a pure
function `ObjId → Option KernelObject` and `objectIndex` is a `List ObjId`.
Both are O(n) structures — lookup is O(1) but discovery (iterating all objects)
is O(n) via the index list. This is an intentional modeling choice:

- **Clarity over performance.** Pure functions are trivially referentially
  transparent, making equational reasoning and `simp`-based proof automation
  straightforward. A `HashMap` or balanced tree would complicate proofs
  without improving the model's expressiveness.
- **Bounded scope.** The model targets proof-level reasoning, not runtime
  efficiency. Test topologies use ≤100 objects; proof obligations never
  iterate the full store.
- **Migration path.** If performance becomes a concern for large executable
  simulations, `objects` can be replaced with `Std.HashMap ObjId KernelObject`
  and `objectIndex` with `Std.HashSet ObjId`. All theorem statements reference
  the function interface (`st.objects id = some obj`), so the migration is
  local to the state representation.

**Monotonic objectIndex (L-05):** `objectIndex` grows monotonically —
`storeObject` appends new IDs but never removes them. This is intentional:

- The index serves as a *discovery set* for bounded iteration (VSpace ASID
  resolution, runtime invariant checks). Monotonic growth ensures that every
  object ever stored remains discoverable.
- Pruning would require a garbage-collection pass to identify unreachable
  objects, adding complexity without proof benefit. The seL4 kernel itself
  does not garbage-collect untyped memory — retype/revoke are explicit.
- The `objectIndex` list may contain IDs whose `objects` mapping has been
  overwritten (type-changed via retype). This is safe because consumers
  always re-check `st.objects id` after discovery. -/
structure SystemState where
  machine : SeLe4n.MachineState
  objects : SeLe4n.ObjId → Option KernelObject
  objectIndex : List SeLe4n.ObjId
  services : ServiceId → Option ServiceGraphEntry
  scheduler : SchedulerState
  irqHandlers : SeLe4n.Irq → Option SeLe4n.ObjId
  lifecycle : LifecycleMetadata
  cdt : CapDerivationTree := .empty   -- WS-E4/C-03: Capability Derivation Tree

/-- Abstract owner identity for a slot in this model: the containing CNode object id. -/
abbrev CSpaceOwner := SeLe4n.ObjId

instance : Inhabited SchedulerState where
  default := { runnable := [], current := none }

instance : Inhabited SystemState where
  default := {
    machine := default
    objects := fun _ => none
    objectIndex := []
    services := fun _ => none
    scheduler := default
    irqHandlers := fun _ => none
    lifecycle := {
      objectTypes := fun _ => none
      capabilityRefs := fun _ => none
    }
    cdt := .empty
  }

abbrev Kernel := SeLe4n.KernelM SystemState KernelError

def lookupObject (id : SeLe4n.ObjId) : Kernel KernelObject :=
  fun st =>
    match st.objects id with
    | none => .error .objectNotFound
    | some obj => .ok (obj, st)

/-- Read a typed VSpace-root object from the global object store. -/
def lookupVSpaceRoot (id : SeLe4n.ObjId) : Kernel VSpaceRoot :=
  fun st =>
    match st.objects id with
    | some (.vspaceRoot root) => .ok (root, st)
    | some _ => .error .vspaceRootInvalid
    | none => .error .objectNotFound

/-- Replace the object stored at `id` with `obj`. -/
def storeObject (id : SeLe4n.ObjId) (obj : KernelObject) : Kernel Unit :=
  fun st =>
    let objects' : SeLe4n.ObjId → Option KernelObject :=
      fun oid => if oid = id then some obj else st.objects oid
    let lifecycle' : LifecycleMetadata :=
      {
        st.lifecycle with
          objectTypes := fun oid => if oid = id then some obj.objectType else st.lifecycle.objectTypes oid
          capabilityRefs := fun ref =>
            if ref.cnode = id then
              match obj with
              | .cnode cn => (cn.lookup ref.slot).map Capability.target
              | _ => none
            else
              st.lifecycle.capabilityRefs ref
      }
    let objectIndex' := if id ∈ st.objectIndex then st.objectIndex else id :: st.objectIndex
    .ok ((), { st with objects := objects', objectIndex := objectIndex', lifecycle := lifecycle' })

/-- Record or clear a slot-to-target lifecycle reference mapping. -/
def storeCapabilityRef (ref : SlotRef) (target : Option CapTarget) : Kernel Unit :=
  fun st =>
    let lifecycle' : LifecycleMetadata :=
      {
        st.lifecycle with
          capabilityRefs := fun ref' => if ref' = ref then target else st.lifecycle.capabilityRefs ref'
      }
    .ok ((), { st with lifecycle := lifecycle' })

/-- Pure state update that clears a finite list of slot-reference mappings. -/
def clearCapabilityRefsState : List SlotRef → SystemState → SystemState
  | [], st => st
  | ref :: refs, st =>
      clearCapabilityRefsState refs {
        st with
          lifecycle := {
            st.lifecycle with
              capabilityRefs := fun ref' => if ref' = ref then none else st.lifecycle.capabilityRefs ref'
          }
      }

/-- Clear a finite list of slot-reference mappings. -/
def clearCapabilityRefs (refs : List SlotRef) : Kernel Unit :=
  fun st => .ok ((), clearCapabilityRefsState refs st)

def setCurrentThread (tid : Option SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    let sched := { st.scheduler with current := tid }
    .ok ((), { st with scheduler := sched })

/-- Read one service graph entry. -/
def lookupService (st : SystemState) (sid : ServiceId) : Option ServiceGraphEntry :=
  st.services sid

/-- Determine whether `sid` lists `dependency` as a declared dependency edge. -/
def hasServiceDependency (st : SystemState) (sid dependency : ServiceId) : Bool :=
  match lookupService st sid with
  | some svc => dependency ∈ svc.dependencies
  | none => false

/-- Determine whether two services are explicitly isolated from one another. -/
def hasIsolationEdge (st : SystemState) (lhs rhs : ServiceId) : Bool :=
  match lookupService st lhs, lookupService st rhs with
  | some lhsSvc, some rhsSvc => rhs ∈ lhsSvc.isolatedFrom || lhs ∈ rhsSvc.isolatedFrom
  | _, _ => false

/-- A service is runnable only when all declared dependencies are currently `running`. -/
def dependenciesSatisfied (st : SystemState) (sid : ServiceId) : Bool :=
  match lookupService st sid with
  | none => false
  | some svc =>
      svc.dependencies.all (fun dep =>
        match lookupService st dep with
        | some depSvc => depSvc.status = .running
        | none => false)

/-- Deterministic pure state helper: replace one service graph entry. -/
def storeServiceState (sid : ServiceId) (entry : ServiceGraphEntry) (st : SystemState) : SystemState :=
  {
    st with
      services := fun sid' => if sid' = sid then some entry else st.services sid'
  }

/-- Deterministic pure state helper: update only the status of an existing service. -/
def setServiceStatusState (sid : ServiceId) (status : ServiceStatus) (st : SystemState) : SystemState :=
  match lookupService st sid with
  | none => st
  | some svc => storeServiceState sid { svc with status := status } st

theorem storeServiceState_lookup_eq
    (st : SystemState)
    (sid : ServiceId)
    (entry : ServiceGraphEntry) :
    lookupService (storeServiceState sid entry st) sid = some entry := by
  simp [lookupService, storeServiceState]

theorem storeServiceState_lookup_ne
    (st : SystemState)
    (sid sid' : ServiceId)
    (entry : ServiceGraphEntry)
    (hNe : sid' ≠ sid) :
    lookupService (storeServiceState sid entry st) sid' = lookupService st sid' := by
  simp [lookupService, storeServiceState, hNe]

theorem setServiceStatusState_lookup_eq
    (st : SystemState)
    (sid : ServiceId)
    (status : ServiceStatus)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st sid = some svc) :
    lookupService (setServiceStatusState sid status st) sid = some { svc with status := status } := by
  simp [setServiceStatusState, hSvc, storeServiceState_lookup_eq]

theorem setServiceStatusState_preserves_objects
    (st : SystemState)
    (sid : ServiceId)
    (status : ServiceStatus) :
    (setServiceStatusState sid status st).objects = st.objects := by
  unfold setServiceStatusState lookupService
  cases hSvc : st.services sid <;> simp [storeServiceState]

theorem storeObject_preserves_services
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.services = st.services := by
  unfold storeObject at hStore
  cases hStore
  rfl

theorem storeCapabilityRef_preserves_scheduler
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeCapabilityRef at hStep
  simp at hStep
  cases hStep
  rfl

theorem storeCapabilityRef_preserves_services
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.services = st.services := by
  unfold storeCapabilityRef at hStep
  simp at hStep
  cases hStep
  rfl

theorem storeCapabilityRef_preserves_objects
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.objects = st.objects := by
  unfold storeCapabilityRef at hStep
  simp at hStep
  cases hStep
  rfl

theorem clearCapabilityRefsState_preserves_objects
    (refs : List SlotRef)
    (st : SystemState) :
    (clearCapabilityRefsState refs st).objects = st.objects := by
  induction refs generalizing st with
  | nil => rfl
  | cons ref refs ih =>
      simpa [clearCapabilityRefsState] using
        ih {
          st with
            lifecycle := {
              st.lifecycle with
                capabilityRefs := fun ref' => if ref' = ref then none else st.lifecycle.capabilityRefs ref'
            }
        }

theorem clearCapabilityRefs_preserves_objects
    (st st' : SystemState)
    (refs : List SlotRef)
    (hStep : clearCapabilityRefs refs st = .ok ((), st')) :
    st'.objects = st.objects := by
  unfold clearCapabilityRefs at hStep
  cases hStep
  simpa using clearCapabilityRefsState_preserves_objects refs st

theorem clearCapabilityRefsState_preserves_scheduler
    (refs : List SlotRef)
    (st : SystemState) :
    (clearCapabilityRefsState refs st).scheduler = st.scheduler := by
  induction refs generalizing st with
  | nil => rfl
  | cons ref refs ih =>
      simpa [clearCapabilityRefsState] using
        ih {
          st with
            lifecycle := {
              st.lifecycle with
                capabilityRefs := fun ref' => if ref' = ref then none else st.lifecycle.capabilityRefs ref'
            }
        }

theorem clearCapabilityRefsState_preserves_services
    (refs : List SlotRef)
    (st : SystemState) :
    (clearCapabilityRefsState refs st).services = st.services := by
  induction refs generalizing st with
  | nil => rfl
  | cons ref refs ih =>
      simpa [clearCapabilityRefsState] using
        ih {
          st with
            lifecycle := {
              st.lifecycle with
                capabilityRefs := fun ref' => if ref' = ref then none else st.lifecycle.capabilityRefs ref'
            }
        }

theorem clearCapabilityRefsState_lookupService
    (refs : List SlotRef)
    (st : SystemState)
    (sid : ServiceId) :
    lookupService (clearCapabilityRefsState refs st) sid = lookupService st sid := by
  simp [lookupService, clearCapabilityRefsState_preserves_services]

theorem storeCapabilityRef_lookup_eq
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.lifecycle.capabilityRefs ref = target := by
  unfold storeCapabilityRef at hStep
  simp at hStep
  cases hStep
  simp


theorem storeObject_objects_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects id = some obj := by
  unfold storeObject at hStore
  cases hStore
  simp

theorem storeObject_objects_ne
    (st st' : SystemState)
    (id oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hNe : oid ≠ id)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  unfold storeObject at hStore
  cases hStore
  simp [hNe]

theorem storeObject_scheduler_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeObject at hStore
  cases hStore
  rfl

theorem storeObject_irqHandlers_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.irqHandlers = st.irqHandlers := by
  unfold storeObject at hStore
  cases hStore
  rfl

theorem storeObject_machine_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold storeObject at hStore
  cases hStore
  rfl

-- WS-E4/C-03: storeObject preserves the CDT (it only touches objects/lifecycle/index)
theorem storeObject_cdt_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.cdt = st.cdt := by
  unfold storeObject at hStore
  cases hStore
  rfl

theorem storeObject_updates_objectTypeMeta
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    st'.lifecycle.objectTypes oid = some obj.objectType := by
  unfold storeObject at hStep
  simp at hStep
  cases hStep
  simp

namespace SystemState

/-- Read a CNode object from the global object store. -/
def lookupCNode (st : SystemState) (id : SeLe4n.ObjId) : Option CNode :=
  match st.objects id with
  | some (.cnode cn) => some cn
  | _ => none

/-- Read a capability from a typed slot reference. -/
def lookupSlotCap (st : SystemState) (ref : SlotRef) : Option Capability :=
  match lookupCNode st ref.cnode with
  | none => none
  | some cn => cn.lookup ref.slot

/-- The modeled owner of a slot is its containing CNode. -/
def ownerOfSlot (ref : SlotRef) : CSpaceOwner :=
  ref.cnode

/-- Logical ownership relation for occupied slots. -/
def ownsSlot (st : SystemState) (owner : CSpaceOwner) (ref : SlotRef) : Prop :=
  owner = ownerOfSlot ref ∧ ∃ cap, lookupSlotCap st ref = some cap

/-- Enumerate all concrete capability entries held by one modeled owner CNode. -/
def ownedSlots (st : SystemState) (owner : CSpaceOwner) : List (SeLe4n.Slot × Capability) :=
  match lookupCNode st owner with
  | some cn => cn.slots
  | none => []

/-- Lifecycle metadata view of object identity typing. -/
def lookupObjectTypeMeta (st : SystemState) (id : SeLe4n.ObjId) : Option KernelObjectType :=
  st.lifecycle.objectTypes id

/-- Lifecycle metadata view of capability slot reference mapping. -/
def lookupCapabilityRefMeta (st : SystemState) (ref : SlotRef) : Option CapTarget :=
  st.lifecycle.capabilityRefs ref

/-- `lookupSlotCap` is determined entirely by the object store. -/
theorem lookupSlotCap_eq_of_objects_eq
    (st₁ st₂ : SystemState)
    (ref : SlotRef)
    (hObj : st₁.objects = st₂.objects) :
    lookupSlotCap st₁ ref = lookupSlotCap st₂ ref := by
  simp [lookupSlotCap, lookupCNode, hObj]

/-- Object-type lifecycle metadata is exact for every object-store id. -/
def objectTypeMetadataConsistent (st : SystemState) : Prop :=
  ∀ oid, lookupObjectTypeMeta st oid = (st.objects oid).map KernelObject.objectType

/-- Capability-reference lifecycle metadata is exact for every slot reference. -/
def capabilityRefMetadataConsistent (st : SystemState) : Prop :=
  ∀ ref, lookupCapabilityRefMeta st ref = (lookupSlotCap st ref).map Capability.target

/-- M4-A state-model metadata consistency bundle. -/
def lifecycleMetadataConsistent (st : SystemState) : Prop :=
  objectTypeMetadataConsistent st ∧ capabilityRefMetadataConsistent st

theorem lookupSlotCap_eq_none_of_lookupCNode_eq_none
    (st : SystemState)
    (ref : SlotRef)
    (hNone : lookupCNode st ref.cnode = none) :
    lookupSlotCap st ref = none := by
  simp [lookupSlotCap, hNone]

theorem ownsSlot_iff
    (st : SystemState)
    (owner : CSpaceOwner)
    (ref : SlotRef) :
    ownsSlot st owner ref ↔
      owner = ref.cnode ∧ ∃ cap, lookupSlotCap st ref = some cap := by
  simp [ownsSlot, ownerOfSlot]

theorem ownedSlots_eq_nil_of_lookupCNode_eq_none
    (st : SystemState)
    (owner : CSpaceOwner)
    (hNone : lookupCNode st owner = none) :
    ownedSlots st owner = [] := by
  simp [ownedSlots, hNone]

end SystemState

theorem storeObject_preserves_objectTypeMetadataConsistent
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hConsistent : SystemState.objectTypeMetadataConsistent st)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.objectTypeMetadataConsistent st' := by
  intro oid'
  unfold storeObject at hStep
  cases hStep
  by_cases hEq : oid' = oid
  · subst hEq
    simp [SystemState.lookupObjectTypeMeta]
  · simpa [SystemState.lookupObjectTypeMeta, hEq] using hConsistent oid'

theorem storeObject_preserves_capabilityRefMetadataConsistent
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hConsistent : SystemState.capabilityRefMetadataConsistent st)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.capabilityRefMetadataConsistent st' := by
  intro ref
  unfold storeObject at hStep
  cases hStep
  by_cases hEq : ref.cnode = oid
  · subst hEq
    cases obj <;> simp [SystemState.lookupCapabilityRefMeta, SystemState.lookupSlotCap,
      SystemState.lookupCNode]
  · simpa [SystemState.lookupCapabilityRefMeta, SystemState.lookupSlotCap,
      SystemState.lookupCNode, hEq] using hConsistent ref

theorem storeObject_preserves_lifecycleMetadataConsistent
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hConsistent : SystemState.lifecycleMetadataConsistent st)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.lifecycleMetadataConsistent st' := by
  rcases hConsistent with ⟨hObjType, hCapRef⟩
  exact ⟨storeObject_preserves_objectTypeMetadataConsistent st st' oid obj hObjType hStep,
    storeObject_preserves_capabilityRefMetadataConsistent st st' oid obj hCapRef hStep⟩

-- ============================================================================
-- L-06/WS-E3: Default SystemState initialization proof
-- ============================================================================

/-- L-06/WS-E3: The default (empty) `SystemState` satisfies `lifecycleMetadataConsistent`.
Both metadata maps return `none` for all inputs, and `objects` returns `none`
for all IDs, so the consistency conditions hold trivially. This provides the
base case for invariant induction — the system starts in a valid state. -/
theorem default_systemState_lifecycleConsistent :
    SystemState.lifecycleMetadataConsistent (default : SystemState) := by
  constructor
  · intro oid
    show (default : SystemState).lifecycle.objectTypes oid =
      Option.map KernelObject.objectType ((default : SystemState).objects oid)
    rfl
  · intro ref
    show (default : SystemState).lifecycle.capabilityRefs ref =
      ((SystemState.lookupSlotCap (default : SystemState) ref).map Capability.target)
    simp only [SystemState.lookupSlotCap, SystemState.lookupCNode]
    rfl

-- ============================================================================
-- M-09/WS-E3: storeObject metadata sync correctness for type-changing stores
-- ============================================================================

/-- M-09/WS-E3: `storeObject` correctly synchronizes lifecycle metadata even when
the stored object changes the type at `oid`. After storing, the metadata at `oid`
reflects the new object's type, regardless of what was stored previously. -/
theorem storeObject_metadata_sync_type_change
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    st'.lifecycle.objectTypes oid = some obj.objectType := by
  unfold storeObject at hStep
  cases hStep
  simp

/-- M-09/WS-E3: `storeObject` correctly synchronizes capability-reference metadata
when the stored object changes from a CNode to a non-CNode (or vice versa).
After storing a non-CNode, all capability references pointing into `oid` are
cleared; after storing a CNode, they reflect the new CNode's slot contents.

This closes the metadata sync hazard: for type-changing stores (e.g., replacing
a CNode with a TCB), `storeObject` correctly clears all capability-reference
metadata for the replaced CNode's slots (the `| _ => none` branch), maintaining
the invariant that metadata reflects the actual object store. -/
theorem storeObject_metadata_sync_capref_at_stored
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (slot : SeLe4n.Slot)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.lookupCapabilityRefMeta st' { cnode := oid, slot := slot } =
      match obj with
      | .cnode cn => (cn.lookup slot).map Capability.target
      | _ => none := by
  unfold storeObject at hStep
  cases hStep
  cases obj <;> simp [SystemState.lookupCapabilityRefMeta]

end SeLe4n.Model
