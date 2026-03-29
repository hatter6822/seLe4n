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
    objects := SeLe4n.Kernel.RobinHood.RHTable.ofList builder.objects
    objectIndex := builder.objects.map Prod.fst
    objectIndexSet := SeLe4n.Kernel.RobinHood.RHSet.ofList (builder.objects.map Prod.fst)
    services := SeLe4n.Kernel.RobinHood.RHTable.ofList builder.services
    scheduler := {
      -- WS-G4 fix: use actual TCB priorities for RunQueue bucketing
      runQueue := SeLe4n.Kernel.RunQueue.ofList (builder.runnable.map (fun tid =>
        (tid, lookupThreadPriority builder.objects tid)))
      current := builder.current
    }
    irqHandlers := SeLe4n.Kernel.RobinHood.RHTable.ofList builder.irqHandlers
    lifecycle := {
      objectTypes := SeLe4n.Kernel.RobinHood.RHTable.ofList builder.lifecycleObjectTypes
      capabilityRefs := SeLe4n.Kernel.RobinHood.RHTable.ofList builder.lifecycleCapabilityRefs
    }
    -- WS-G3/F-P06: Populate ASID table from VSpaceRoot objects
    asidTable := SeLe4n.Kernel.RobinHood.RHTable.ofList (builder.objects.filterMap fun (oid, obj) =>
      match obj with
      | .vspaceRoot root => some (root.asid, oid)
      | _ => none)
  }

/-- S2-F: Build a `SystemState` with post-construction invariant validation.
    Returns the state or throws if structural invariants are violated.
    Validates (runtime approximation of formal Builder invariants):
    1. No duplicate object IDs
    2. Lifecycle objectTypes reference existing objects with correct type tags
    3. Scheduler runnable threads reference existing TCB objects
    4. CNode slot table capacity bounds (4 ≤ capacity, size < capacity)
    5. IRQ handlers reference existing objects
    6. Lifecycle capabilityRefs reference existing CNode objects
    7. VSpaceRoot ASID uniqueness (no two VSpaceRoots share an ASID)
    8. Current thread (if set) is in the runnable list -/
def buildValidated (builder : BootstrapBuilder) : Except String SystemState :=
  let st := builder.build
  let oids := builder.objects.map Prod.fst
  let uniqueOids := oids.eraseDups
  -- W5-D: Each check includes its number for debuggability
  -- Check 1: No duplicate object IDs in builder input
  if oids.length ≠ uniqueOids.length then
    .error s!"BuilderTestState check 1 failed: duplicate object IDs (got {oids.length} entries, {uniqueOids.length} unique)"
  -- Check 2: Lifecycle objectTypes reference existing objects with correct type
  else if builder.lifecycleObjectTypes.any (fun (oid, _) => !oids.contains oid) then
    let bad := builder.lifecycleObjectTypes.filter (fun (oid, _) => !oids.contains oid)
    .error s!"BuilderTestState check 2a failed: lifecycleObjectTypes references non-existent object ID(s): {bad.map Prod.fst}"
  else if builder.lifecycleObjectTypes.any (fun (oid, ty) =>
    match builder.objects.find? (fun (o, _) => o == oid) with
    | some (_, obj) => obj.objectType != ty
    | none => true) then
    .error "BuilderTestState check 2b failed: lifecycleObjectTypes type tag mismatch with actual object"
  -- Check 3: Runnable threads reference existing TCB objects
  else if builder.runnable.any (fun tid =>
    !builder.objects.any (fun (oid, obj) =>
      oid.toNat = tid.toNat && match obj with | .tcb _ => true | _ => false)) then
    let bad := builder.runnable.filter (fun tid =>
      !builder.objects.any (fun (oid, obj) =>
        oid.toNat = tid.toNat && match obj with | .tcb _ => true | _ => false))
    .error s!"BuilderTestState check 3 failed: runnable thread(s) do not reference existing TCB(s): {bad}"
  -- Check 4: CNode slot table capacity bounds
  else if builder.objects.any (fun (_, obj) =>
    match obj with
    | .cnode cn => cn.slots.capacity < 4 || cn.slots.size >= cn.slots.capacity
    | _ => false) then
    .error "BuilderTestState check 4 failed: CNode slots violate capacity bounds (need 4 ≤ capacity, size < capacity)"
  -- Check 5: IRQ handlers reference existing objects
  else if builder.irqHandlers.any (fun (_, oid) => !oids.contains oid) then
    .error "BuilderTestState check 5 failed: IRQ handler references non-existent object"
  -- Check 6: Lifecycle capabilityRefs reference existing CNode objects
  else if builder.lifecycleCapabilityRefs.any (fun (ref, _) =>
    !builder.objects.any (fun (oid, obj) =>
      oid == ref.cnode && match obj with | .cnode _ => true | _ => false)) then
    .error "BuilderTestState check 6 failed: capabilityRef references non-existent CNode"
  -- Check 7: VSpaceRoot ASID uniqueness
  else
    let asids := builder.objects.filterMap (fun (_, obj) =>
      match obj with | .vspaceRoot vs => some vs.asid | _ => none)
    let uniqueAsids := asids.eraseDups
    if asids.length ≠ uniqueAsids.length then
      .error "BuilderTestState check 7 failed: duplicate ASIDs across VSpaceRoot objects"
    -- Check 8: Dequeue-on-dispatch (WS-H12b) — current thread must NOT be in
    -- the runnable list. The scheduler removes the dispatched thread from the
    -- run queue before setting it as current. If current is set AND also in
    -- runnable, the state violates queueCurrentConsistent.
    else match builder.current with
    | some tid =>
      if builder.runnable.any (fun t => t.toNat == tid.toNat) then
        .error s!"BuilderTestState check 8 failed: current thread {tid.toNat} must not be in runnable list (dequeue-on-dispatch, WS-H12b)"
      else .ok st
    | none => .ok st

/-- S2-F: Build a `SystemState` with invariant validation, panicking on failure.
    Drop-in replacement for `build` that catches structural violations at test time.
    Use this for new test states instead of `build` to ensure test states satisfy
    the same structural invariants as the formal Builder. -/
def buildChecked (builder : BootstrapBuilder) : SystemState :=
  match builder.buildValidated with
  | .ok st => st
  | .error msg => panic! s!"BootstrapBuilder.buildChecked: {msg}"

end BootstrapBuilder

end SeLe4n.Testing
