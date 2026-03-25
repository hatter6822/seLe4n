/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.Builder
import SeLe4n.Model.FreezeProofs
import SeLe4n.Kernel.API

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

-- U6-E (U-M12): Duplicate IRQ detection.
-- `registerIrq` uses `RHTable.insert` (last-wins on duplicate keys).
-- `irqsUnique` detects duplicates so callers can validate boot configs.

private def irqKeysNoDup : List SeLe4n.Irq → Bool
  | [] => true
  | k :: rest => !rest.any (· == k) && irqKeysNoDup rest

def irqsUnique (irqs : List IrqEntry) : Bool :=
  irqKeysNoDup (irqs.map (·.irq))

-- U6-F (U-M13): Duplicate object ID detection.
-- `createObject` uses `RHTable.insert` (last-wins, losing earlier objects).
-- `objectIdsUnique` detects duplicates to prevent silent data loss.

private def objIdKeysNoDup : List SeLe4n.ObjId → Bool
  | [] => true
  | k :: rest => !rest.any (· == k) && objIdKeysNoDup rest

def objectIdsUnique (objs : List ObjectEntry) : Bool :=
  objIdKeysNoDup (objs.map (·.id))

/-- Q3-C: Fold IRQ entries into the builder state.

    **U6-E (U-M12) — Duplicate IRQ semantics**: `registerIrq` uses
    `RHTable.insert` which implements last-wins on duplicate keys. If the same
    INTID appears multiple times in `irqs`, only the final handler is retained.
    Use `irqsUnique` to validate before folding if duplicate detection is
    required. -/
def foldIrqs (irqs : List IrqEntry) (ist : IntermediateState)
    : IntermediateState :=
  irqs.foldl (fun acc entry => registerIrq acc entry.irq entry.handler) ist

/-- Q3-C: Fold initial objects into the builder state.

    **U6-F (U-M13) — Duplicate object ID semantics**: `createObject` uses
    `RHTable.insert` which implements last-wins on duplicate keys. If the same
    ObjId appears multiple times in `objs`, only the final object is retained
    and earlier objects are silently lost. Use `objectIdsUnique` to validate
    before folding to prevent silent object loss. -/
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

/-- U6-E: Empty IRQ list has no duplicates. -/
theorem irqsUnique_empty : irqsUnique [] = true := by
  decide

/-- U6-F: Empty object list has no duplicates. -/
theorem objectIdsUnique_empty : objectIdsUnique [] = true := by
  decide

/-- U6-E/F: A well-formed PlatformConfig has unique IRQs and unique object IDs. -/
def PlatformConfig.wellFormed (config : PlatformConfig) : Bool :=
  irqsUnique config.irqTable && objectIdsUnique config.initialObjects

/-- U6-E/F: Empty config is well-formed. -/
theorem PlatformConfig.wellFormed_empty :
    PlatformConfig.wellFormed { irqTable := [], initialObjects := [] } = true := by
  decide

/-- U6-E/F: Checked boot — rejects configs with duplicate IRQs or object IDs.

    This is the enforcement variant of `bootFromPlatform`. It validates
    `PlatformConfig.wellFormed` before proceeding, returning an error if
    duplicate IRQ registrations or object IDs are detected. This prevents
    silent last-wins overwrites that could lose kernel objects or IRQ handlers.

    Use `bootFromPlatform` directly only when the config is known-valid
    (e.g., constructed programmatically with uniqueness guarantees). -/
def bootFromPlatformChecked (config : PlatformConfig) :
    Except String IntermediateState :=
  if config.wellFormed then
    .ok (bootFromPlatform config)
  else if ¬ irqsUnique config.irqTable then
    .error "boot: duplicate IRQ registration detected in platform config"
  else
    .error "boot: duplicate object ID detected in platform config"

/-- U6-E/F: Checked boot agrees with unchecked boot on well-formed configs. -/
theorem bootFromPlatformChecked_eq_bootFromPlatform (config : PlatformConfig)
    (hWf : config.wellFormed = true) :
    bootFromPlatformChecked config = .ok (bootFromPlatform config) := by
  simp [bootFromPlatformChecked, hWf]

/-- U6-E/F: Checked boot rejects configs that are not well-formed. -/
theorem bootFromPlatformChecked_rejects_invalid (config : PlatformConfig)
    (hNotWf : config.wellFormed = false) :
    (bootFromPlatformChecked config).isOk = false := by
  simp [bootFromPlatformChecked, hNotWf]
  split <;> rfl

-- ============================================================================
-- U6-G (U-M15): Boot-to-Runtime Invariant Bridge
-- ============================================================================

/-! ### U6-G: Boot-to-Runtime Invariant Bridge

The invariant bridge connects boot-time validity (`bootFromPlatform_valid`)
to runtime invariants (`proofLayerInvariantBundle`) through the freeze
transformation. Three intermediate composition lemmas:

1. **Boot→Intermediate**: `bootFromPlatform_valid` establishes 4 structural
   invariants. The empty-config case establishes the full runtime bundle
   because `mkEmptyIntermediateState.state = default`.

2. **Intermediate→Frozen**: `freeze_preserves_invariants` transfers the
   API invariant bundle across freeze (existential witness).

3. **Frozen→Runtime**: `apiInvariantBundle_frozenDirect` provides a
   non-existential frozen invariant suitable for FrozenOps.

The end-to-end bridge for the empty config is fully proved. For general
configs, the gap is that builder operations (`registerIrq`, `createObject`)
only preserve 4 structural invariants, not the full 9-component
`proofLayerInvariantBundle`. Extending to general configs requires proving
that each builder operation preserves all 9 components — deferred to WS-V
where the full runtime semantics are exercised on hardware.
-/

/-- U6-G Step 1: Boot from empty config produces the default state. -/
theorem bootFromPlatform_empty_state :
    (bootFromPlatform { irqTable := [], initialObjects := [] }).state =
    (default : SystemState) := rfl

/-- U6-G Step 2: The default state satisfies the full runtime invariant bundle.
    This follows from the existing `apiInvariantBundle_default`. -/
theorem emptyBoot_proofLayerInvariantBundle :
    SeLe4n.Kernel.Architecture.proofLayerInvariantBundle
      (bootFromPlatform { irqTable := [], initialObjects := [] }).state :=
  bootFromPlatform_empty_state ▸ SeLe4n.Kernel.apiInvariantBundle_default

/-- U6-G Step 3: Freeze preserves the API invariant bundle.
    If the builder-phase state satisfies `apiInvariantBundle`, then the
    frozen state satisfies `apiInvariantBundle_frozen`. -/
theorem emptyBoot_freeze_preserves :
    SeLe4n.Model.apiInvariantBundle_frozen
      (SeLe4n.Model.freeze
        (bootFromPlatform { irqTable := [], initialObjects := [] })) :=
  SeLe4n.Model.freeze_preserves_invariants _ emptyBoot_proofLayerInvariantBundle

/-- U6-G End-to-end bridge (empty config): booting from empty config, then
    freezing, produces a frozen state satisfying the API invariant bundle.

    This is the base-case bridge theorem. It composes:
    1. `bootFromPlatform_empty_state` (boot produces default state)
    2. `apiInvariantBundle_default` (default satisfies full bundle)
    3. `freeze_preserves_invariants` (freeze transfers the bundle)

    For general configs, the bridge requires extending builder operations
    to preserve all 9 components of `proofLayerInvariantBundle` (not just
    the 4 structural invariants). This is tracked for WS-V. -/
theorem bootToRuntime_invariantBridge_empty :
    let ist := bootFromPlatform { irqTable := [], initialObjects := [] }
    SeLe4n.Kernel.Architecture.proofLayerInvariantBundle ist.state ∧
    SeLe4n.Model.apiInvariantBundle_frozen (SeLe4n.Model.freeze ist) :=
  ⟨emptyBoot_proofLayerInvariantBundle, emptyBoot_freeze_preserves⟩

end SeLe4n.Platform.Boot
