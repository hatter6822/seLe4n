import SeLe4n

open SeLe4n.Model

namespace SeLe4n.Testing

/-- Deterministic lookup helper used by the bootstrap-state builder DSL. -/
def listLookup {α : Type} [DecidableEq α] {β : Type} (entries : List (α × β)) (key : α) : Option β :=
  (entries.find? (fun entry => entry.fst = key)).map Prod.snd

/--
Testing DSL for composing bootstrap states from finite override tables.

Later entries win because DSL combinators prepend to each list.
-/
structure BootstrapBuilder where
  machine : SeLe4n.MachineState := default
  objects : List (SeLe4n.ObjId × KernelObject) := []
  services : List (ServiceId × ServiceGraphEntry) := []
  runnable : List SeLe4n.ThreadId := []
  current : Option SeLe4n.ThreadId := none
  irqHandlers : List (SeLe4n.Irq × SeLe4n.ObjId) := []
  lifecycleObjectTypes : List (SeLe4n.ObjId × KernelObjectType) := []
  lifecycleCapabilityRefs : List (SeLe4n.Model.SlotRef × CapTarget) := []

namespace BootstrapBuilder

def empty : BootstrapBuilder := {}

def withObject (builder : BootstrapBuilder) (oid : SeLe4n.ObjId) (obj : KernelObject) : BootstrapBuilder :=
  { builder with objects := (oid, obj) :: builder.objects }

def withService
    (builder : BootstrapBuilder)
    (sid : ServiceId)
    (entry : ServiceGraphEntry) : BootstrapBuilder :=
  { builder with services := (sid, entry) :: builder.services }

def withRunnable (builder : BootstrapBuilder) (queue : List SeLe4n.ThreadId) : BootstrapBuilder :=
  { builder with runnable := queue }

def withCurrent (builder : BootstrapBuilder) (tid : Option SeLe4n.ThreadId) : BootstrapBuilder :=
  { builder with current := tid }

def withIrqHandler
    (builder : BootstrapBuilder)
    (irq : SeLe4n.Irq)
    (oid : SeLe4n.ObjId) : BootstrapBuilder :=
  { builder with irqHandlers := (irq, oid) :: builder.irqHandlers }

def withLifecycleObjectType
    (builder : BootstrapBuilder)
    (oid : SeLe4n.ObjId)
    (objTy : KernelObjectType) : BootstrapBuilder :=
  { builder with lifecycleObjectTypes := (oid, objTy) :: builder.lifecycleObjectTypes }

def withLifecycleCapabilityRef
    (builder : BootstrapBuilder)
    (ref : SeLe4n.Model.SlotRef)
    (target : CapTarget) : BootstrapBuilder :=
  { builder with lifecycleCapabilityRefs := (ref, target) :: builder.lifecycleCapabilityRefs }

def withMachine (builder : BootstrapBuilder) (machine : SeLe4n.MachineState) : BootstrapBuilder :=
  { builder with machine := machine }

/-- Materialize a full `SystemState` from the builder tables. -/
def build (builder : BootstrapBuilder) : SystemState :=
  {
    machine := builder.machine
    objects := listLookup builder.objects
    services := listLookup builder.services
    scheduler := {
      runnable := builder.runnable
      current := builder.current
    }
    irqHandlers := listLookup builder.irqHandlers
    lifecycle := {
      objectTypes := listLookup builder.lifecycleObjectTypes
      capabilityRefs := listLookup builder.lifecycleCapabilityRefs
    }
  }

end BootstrapBuilder

end SeLe4n.Testing
