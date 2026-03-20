/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

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

/-- Extract the actual TCB priority for a thread from the builder's object list.
    Falls back to Priority 0 if the thread has no TCB entry. -/
private def lookupThreadPriority (objects : List (SeLe4n.ObjId × KernelObject)) (tid : SeLe4n.ThreadId) : SeLe4n.Priority :=
  match objects.find? (fun (oid, _) => oid == tid.toObjId) with
  | some (_, .tcb tcb) => tcb.priority
  | _ => ⟨0⟩

/-- Materialize a full `SystemState` from the builder tables. -/
def build (builder : BootstrapBuilder) : SystemState :=
  {
    machine := builder.machine
    objects := Std.HashMap.ofList builder.objects
    objectIndex := builder.objects.map Prod.fst
    objectIndexSet := Std.HashSet.ofList (builder.objects.map Prod.fst)
    services := Std.HashMap.ofList builder.services
    scheduler := {
      -- WS-G4 fix: use actual TCB priorities for RunQueue bucketing
      runQueue := SeLe4n.Kernel.RunQueue.ofList (builder.runnable.map (fun tid =>
        (tid, lookupThreadPriority builder.objects tid)))
      current := builder.current
    }
    irqHandlers := Std.HashMap.ofList builder.irqHandlers
    lifecycle := {
      objectTypes := Std.HashMap.ofList builder.lifecycleObjectTypes
      capabilityRefs := Std.HashMap.ofList builder.lifecycleCapabilityRefs
    }
    -- WS-G3/F-P06: Populate ASID table from VSpaceRoot objects
    asidTable := Std.HashMap.ofList (builder.objects.filterMap fun (oid, obj) =>
      match obj with
      | .vspaceRoot root => some (root.asid, oid)
      | _ => none)
  }

end BootstrapBuilder

end SeLe4n.Testing
