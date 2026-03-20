/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.Builder

/-!
# Q3-C: Boot Sequence — IntermediateState from Platform Configuration

The boot sequence constructs an `IntermediateState` from a `PlatformConfig`,
starting from `mkEmptyIntermediateState` and applying builder operations.

## Determinism

`bootFromPlatform` is a pure function: the same `PlatformConfig` always
yields the same `IntermediateState`. This is required for reproducible booting
and is guaranteed by the deterministic semantics of all builder operations.
-/

namespace SeLe4n.Platform.Boot

open SeLe4n.Model
open SeLe4n.Model.Builder
open SeLe4n.Kernel.RobinHood

/-- Q3-C: An IRQ entry for platform boot configuration: an IRQ line and the
ObjId of its handler notification object. -/
structure IrqEntry where
  irq : SeLe4n.Irq
  handler : SeLe4n.ObjId
  deriving Repr, DecidableEq

/-- Q3-C: An initial object entry for platform boot: an ObjId and the kernel
object to store, along with proof obligations that CNodes have valid slots
and VSpaceRoots have valid mappings. -/
structure ObjectEntry where
  id : SeLe4n.ObjId
  obj : KernelObject
  hSlots : ∀ cn, obj = KernelObject.cnode cn → cn.slotsUnique
  hMappings : ∀ vs, obj = KernelObject.vspaceRoot vs → vs.mappings.invExt

/-- Q3-C: Platform boot configuration — IRQ table and initial objects.

This is the minimal configuration needed to construct a valid
`IntermediateState` during boot. Platform-specific details (memory layout,
device tree, etc.) are handled by `PlatformBinding` instances. -/
structure PlatformConfig where
  irqTable : List IrqEntry
  initialObjects : List ObjectEntry

/-- Q3-C: Fold IRQ entries into the builder state. -/
def foldIrqs (irqs : List IrqEntry) (ist : IntermediateState)
    : IntermediateState :=
  irqs.foldl (fun acc entry => registerIrq acc entry.irq entry.handler) ist

/-- Q3-C: Fold initial objects into the builder state. -/
def foldObjects (objs : List ObjectEntry) (ist : IntermediateState)
    : IntermediateState :=
  objs.foldl (fun acc entry =>
    createObject acc entry.id entry.obj entry.hSlots entry.hMappings) ist

/-- Q3-C: Construct an `IntermediateState` from platform configuration.

Starts from the empty state and applies:
1. IRQ handler registrations (via `Builder.registerIrq`)
2. Initial object insertions (via `Builder.createObject`)

The result carries all four IntermediateState invariant witnesses. -/
def bootFromPlatform (config : PlatformConfig) : IntermediateState :=
  let initial := mkEmptyIntermediateState
  let withIrqs := foldIrqs config.irqTable initial
  foldObjects config.initialObjects withIrqs

/-- Q3-C: Determinism — same config yields same state. -/
theorem bootFromPlatform_deterministic (config : PlatformConfig) :
    bootFromPlatform config = bootFromPlatform config := rfl

/-- Q3-C: Boot from empty config yields the empty IntermediateState. -/
theorem bootFromPlatform_empty :
    bootFromPlatform { irqTable := [], initialObjects := [] } =
    mkEmptyIntermediateState := rfl

/-- Q3-C: The booted state satisfies allTablesInvExt. -/
theorem bootFromPlatform_allTablesInvExt (config : PlatformConfig) :
    (bootFromPlatform config).state.allTablesInvExt :=
  (bootFromPlatform config).hAllTables

/-- Q3-C: The booted state satisfies per-object CNode slots invariant. -/
theorem bootFromPlatform_perObjectSlots (config : PlatformConfig) :
    perObjectSlotsInvariant (bootFromPlatform config).state :=
  (bootFromPlatform config).hPerObjectSlots

/-- Q3-C: The booted state satisfies per-object VSpaceRoot mappings invariant. -/
theorem bootFromPlatform_perObjectMappings (config : PlatformConfig) :
    perObjectMappingsInvariant (bootFromPlatform config).state :=
  (bootFromPlatform config).hPerObjectMappings

/-- Q3-C: The booted state satisfies lifecycle metadata consistency. -/
theorem bootFromPlatform_lifecycleConsistent (config : PlatformConfig) :
    SystemState.lifecycleMetadataConsistent (bootFromPlatform config).state :=
  (bootFromPlatform config).hLifecycleConsistent

/-- Q3-C: Master validity theorem — boot produces a fully valid state. -/
theorem bootFromPlatform_valid (config : PlatformConfig) :
    let ist := bootFromPlatform config
    ist.state.allTablesInvExt ∧
    perObjectSlotsInvariant ist.state ∧
    perObjectMappingsInvariant ist.state ∧
    SystemState.lifecycleMetadataConsistent ist.state :=
  ⟨bootFromPlatform_allTablesInvExt config,
   bootFromPlatform_perObjectSlots config,
   bootFromPlatform_perObjectMappings config,
   bootFromPlatform_lifecycleConsistent config⟩

end SeLe4n.Platform.Boot
