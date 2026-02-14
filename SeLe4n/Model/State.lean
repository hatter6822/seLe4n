import SeLe4n.Machine
import SeLe4n.Model.Object

namespace SeLe4n.Model

inductive KernelError where
  | invalidCapability
  | objectNotFound
  | schedulerInvariantViolation
  | notImplemented
  deriving Repr, DecidableEq

structure SchedulerState where
  runnable : List SeLe4n.ThreadId
  current : Option SeLe4n.ThreadId
  deriving Repr, DecidableEq

structure SystemState where
  machine : SeLe4n.MachineState
  objects : SeLe4n.ObjId → Option KernelObject
  scheduler : SchedulerState
  irqHandlers : SeLe4n.Irq → Option SeLe4n.ObjId

/-- Architecture-neutral address of a capability slot inside a CNode object. -/
structure SlotRef where
  cnode : SeLe4n.ObjId
  slot : SeLe4n.Slot
  deriving Repr, DecidableEq

/-- Abstract owner identity for a slot in this model: the containing CNode object id. -/
abbrev CSpaceOwner := SeLe4n.ObjId

instance : Inhabited SchedulerState where
  default := { runnable := [], current := none }

instance : Inhabited SystemState where
  default := {
    machine := default
    objects := fun _ => none
    scheduler := default
    irqHandlers := fun _ => none
  }

abbrev Kernel := SeLe4n.KernelM SystemState KernelError

def lookupObject (id : SeLe4n.ObjId) : Kernel KernelObject :=
  fun st =>
    match st.objects id with
    | none => .error .objectNotFound
    | some obj => .ok (obj, st)

/-- Replace the object stored at `id` with `obj`. -/
def storeObject (id : SeLe4n.ObjId) (obj : KernelObject) : Kernel Unit :=
  fun st =>
    let objects' : SeLe4n.ObjId → Option KernelObject :=
      fun oid => if oid = id then some obj else st.objects oid
    .ok ((), { st with objects := objects' })

def setCurrentThread (tid : Option SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    let sched := { st.scheduler with current := tid }
    .ok ((), { st with scheduler := sched })

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

end SeLe4n.Model
