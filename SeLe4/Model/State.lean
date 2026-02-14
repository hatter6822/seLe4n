import SeLe4.Machine
import SeLe4.Model.Object

namespace SeLe4.Model

inductive KernelError where
  | invalidCapability
  | objectNotFound
  | schedulerInvariantViolation
  | notImplemented
  deriving Repr, DecidableEq

structure SchedulerState where
  runnable : List SeLe4.ThreadId
  current : Option SeLe4.ThreadId
  deriving Repr, DecidableEq

structure SystemState where
  machine : SeLe4.MachineState
  objects : SeLe4.ObjId → Option KernelObject
  scheduler : SchedulerState
  irqHandlers : SeLe4.Irq → Option SeLe4.ObjId

instance : Inhabited SchedulerState where
  default := { runnable := [], current := none }

instance : Inhabited SystemState where
  default := {
    machine := default
    objects := fun _ => none
    scheduler := default
    irqHandlers := fun _ => none
  }

abbrev Kernel := SeLe4.KernelM SystemState KernelError

def lookupObject (id : SeLe4.ObjId) : Kernel KernelObject :=
  fun st =>
    match st.objects id with
    | none => .error .objectNotFound
    | some obj => .ok (obj, st)

def setCurrentThread (tid : Option SeLe4.ThreadId) : Kernel Unit :=
  fun st =>
    let sched := { st.scheduler with current := tid }
    .ok ((), { st with scheduler := sched })

end SeLe4.Model
