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

def setCurrentThread (tid : Option SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    let sched := { st.scheduler with current := tid }
    .ok ((), { st with scheduler := sched })

end SeLe4n.Model
