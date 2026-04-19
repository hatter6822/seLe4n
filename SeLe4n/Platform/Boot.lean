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
open SeLe4n.Kernel

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
device tree, etc.) are handled by `PlatformBinding` instances. Machine
hardware parameters (PA width, register width, etc.) are configured
separately via `applyMachineConfig` after boot.

AH2-E: `machineConfig` field added so `bootFromPlatform` can automatically
apply machine configuration without requiring a separate manual call.
Defaults to `defaultMachineConfig` for backward compatibility. -/
structure PlatformConfig where
  irqTable : List IrqEntry
  initialObjects : List ObjectEntry
  machineConfig : MachineConfig := defaultMachineConfig

-- V7-I: O(n) duplicate detection via HashSet accumulation.
-- Replaces the O(n²) per-element `List.any` scan with a single-pass fold.
-- Note: `Std.HashSet` is opaque to Lean's kernel; for non-empty lists, proofs
-- about these functions may require `native_decide`.  For empty-list base
-- cases the `go` function reduces without touching HashSet, so `decide`
-- suffices.  See `listAllDistinct` below for a fully transparent alternative.
-- AF3-E: `natKeysNoDup` uses opaque `Std.HashSet` for O(n) runtime
-- checking. The transparent O(n²) alternative `listAllDistinct` (below)
-- is usable by `decide` but too slow for large key sets. Boot-time
-- callers use `natKeysNoDup` for runtime speed; proofs requiring
-- kernel-evaluable noDup should use `listAllDistinct`.
private def natKeysNoDup (keys : List Nat) : Bool :=
  let rec go : List Nat → Std.HashSet Nat → Bool
    | [], _ => true
    | k :: rest, seen =>
      if seen.contains k then false
      else go rest (seen.insert k)
  go keys {}

/-- X2-F: Transparent O(n²) duplicate detection for kernel-evaluable proofs.
    Checks that no element appears later in the list. Unlike `natKeysNoDup`
    (which uses opaque `Std.HashSet`), this function is fully transparent to
    Lean's kernel, enabling `decide` instead of `native_decide` in proofs.
    O(n²) is acceptable for boot-time lists (typically ≤100 entries). -/
private def listAllDistinct [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && listAllDistinct xs

/-- X2-F: Transparent variant of `irqsUnique` for kernel-evaluable proofs. -/
def irqsUniqueTransparent (irqs : List IrqEntry) : Bool :=
  listAllDistinct (irqs.map (·.irq.toNat))

/-- X2-F: Transparent variant of `objectIdsUnique` for kernel-evaluable proofs. -/
def objectIdsUniqueTransparent (objs : List ObjectEntry) : Bool :=
  listAllDistinct (objs.map (·.id.toNat))

-- U6-E (U-M12): Duplicate IRQ detection.
-- `registerIrq` uses `RHTable.insert` (last-wins on duplicate keys).
-- `irqsUnique` detects duplicates so callers can validate boot configs.
-- V7-I: O(n) via HashSet, replacing O(n²) naive scan.

def irqsUnique (irqs : List IrqEntry) : Bool :=
  natKeysNoDup (irqs.map (·.irq.toNat))

-- U6-F (U-M13): Duplicate object ID detection.
-- `createObject` uses `RHTable.insert` (last-wins, losing earlier objects).
-- `objectIdsUnique` detects duplicates to prevent silent data loss.
-- V7-I: O(n) via HashSet, replacing O(n²) naive scan.

def objectIdsUnique (objs : List ObjectEntry) : Bool :=
  natKeysNoDup (objs.map (·.id.toNat))

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

-- ============================================================================
-- X2-D: Post-boot machine configuration
-- (AH2-E/F: Moved before bootFromPlatform so it can be called during boot)
-- ============================================================================

/-- X2-D: Apply platform-specific machine configuration to a booted state.
    Sets `physicalAddressWidth` from the platform's `MachineConfig`, ensuring
    runtime PA bounds checks use the correct hardware limit.

    This is a pure machine-state update: it modifies only `state.machine` and
    preserves all kernel-object, scheduler, capability, and CDT state. All
    IntermediateState invariant witnesses carry forward because they do not
    depend on `MachineState` fields.

    AG3-B (P-04): Copies all `MachineConfig` fields to machine state:
    `physicalAddressWidth`, `registerWidth`, `virtualAddressWidth`,
    `pageSize`, `maxASID`, `memoryMap`, `registerCount`. Invariant
    witnesses thread through unchanged because none depend on machine
    metadata fields. -/
def applyMachineConfig (ist : IntermediateState) (config : MachineConfig) :
    IntermediateState where
  state := { ist.state with
    machine := { ist.state.machine with
      physicalAddressWidth := config.physicalAddressWidth
      registerWidth := config.registerWidth
      virtualAddressWidth := config.virtualAddressWidth
      pageSize := config.pageSize
      maxASID := config.maxASID
      memoryMap := config.memoryMap
      registerCount := config.registerCount } }
  hAllTables := ist.hAllTables
  hPerObjectSlots := ist.hPerObjectSlots
  hPerObjectMappings := ist.hPerObjectMappings
  hLifecycleConsistent := ist.hLifecycleConsistent

/-- X2-D: `applyMachineConfig` preserves the scheduler state unchanged. -/
theorem applyMachineConfig_scheduler_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.scheduler = ist.state.scheduler := rfl

/-- X2-D: `applyMachineConfig` preserves the object store unchanged. -/
theorem applyMachineConfig_objects_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.objects = ist.state.objects := rfl

/-- X2-D: `applyMachineConfig` sets `physicalAddressWidth` from config. -/
theorem applyMachineConfig_physicalAddressWidth (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.machine.physicalAddressWidth =
    config.physicalAddressWidth := rfl

/-- AG3-B: `applyMachineConfig` sets `registerWidth` from config. -/
theorem applyMachineConfig_registerWidth (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.machine.registerWidth =
    config.registerWidth := rfl

/-- AG3-B: `applyMachineConfig` sets `virtualAddressWidth` from config. -/
theorem applyMachineConfig_virtualAddressWidth (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.machine.virtualAddressWidth =
    config.virtualAddressWidth := rfl

/-- AG3-B: `applyMachineConfig` sets `pageSize` from config. -/
theorem applyMachineConfig_pageSize (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.machine.pageSize =
    config.pageSize := rfl

/-- AG3-B: `applyMachineConfig` sets `maxASID` from config. -/
theorem applyMachineConfig_maxASID (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.machine.maxASID =
    config.maxASID := rfl

/-- AG3-B: `applyMachineConfig` sets `memoryMap` from config. -/
theorem applyMachineConfig_memoryMap (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.machine.memoryMap =
    config.memoryMap := rfl

/-- AG3-B: `applyMachineConfig` sets `registerCount` from config. -/
theorem applyMachineConfig_registerCount (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.machine.registerCount =
    config.registerCount := rfl

/-- AH2-F: `applyMachineConfig` preserves CDT. -/
theorem applyMachineConfig_cdt_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.cdt = ist.state.cdt := rfl

/-- AH2-F: `applyMachineConfig` preserves services. -/
theorem applyMachineConfig_services_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.services = ist.state.services := rfl

/-- AH2-F: `applyMachineConfig` preserves serviceRegistry. -/
theorem applyMachineConfig_serviceRegistry_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.serviceRegistry = ist.state.serviceRegistry := rfl

/-- AH2-F: `applyMachineConfig` preserves interfaceRegistry. -/
theorem applyMachineConfig_interfaceRegistry_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.interfaceRegistry = ist.state.interfaceRegistry := rfl

/-- AH2-F: `applyMachineConfig` preserves asidTable. -/
theorem applyMachineConfig_asidTable_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.asidTable = ist.state.asidTable := rfl

/-- AH2-F: `applyMachineConfig` preserves TLB state. -/
theorem applyMachineConfig_tlb_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.tlb = ist.state.tlb := rfl

/-- AH2-F: `applyMachineConfig` preserves lifecycle metadata. -/
theorem applyMachineConfig_lifecycle_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.lifecycle = ist.state.lifecycle := rfl

/-- AH2-F: `applyMachineConfig` preserves cdtNodeSlot. -/
theorem applyMachineConfig_cdtNodeSlot_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.cdtNodeSlot = ist.state.cdtNodeSlot := rfl

/-- AH2-F: `applyMachineConfig` preserves machine state (only modifies config fields). -/
theorem applyMachineConfig_machine_fields (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.machine.regs = ist.state.machine.regs ∧
    (applyMachineConfig ist config).state.machine.memory = ist.state.machine.memory ∧
    (applyMachineConfig ist config).state.machine.timer = ist.state.machine.timer ∧
    (applyMachineConfig ist config).state.machine.systemRegisters = ist.state.machine.systemRegisters ∧
    (applyMachineConfig ist config).state.machine.interruptsEnabled = ist.state.machine.interruptsEnabled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Q3-C: Construct an `IntermediateState` from platform configuration.

Starts from the empty state and applies:
1. IRQ handler registrations (via `Builder.registerIrq`)
2. Initial object insertions (via `Builder.createObject`)
3. Machine configuration application (via `applyMachineConfig`) — AH2-F

The result carries all four IntermediateState invariant witnesses.

AF3-F (AF-44): Currently accepts empty `PlatformConfig` without
validation. Use `bootFromPlatformChecked` for production boot paths,
which validates `PlatformConfig.wellFormed` and rejects duplicates.
Minimum-configuration validation (e.g., at least one initial thread,
valid scheduler state) is deferred to WS-V. -/
def bootFromPlatform (config : PlatformConfig) : IntermediateState :=
  let initial := mkEmptyIntermediateState
  let withIrqs := foldIrqs config.irqTable initial
  let withObjects := foldObjects config.initialObjects withIrqs
  -- AH2-F: Integrate machine config into boot pipeline to prevent
  -- PA width misconfiguration (M-03/L-16). Previously callers had to
  -- manually chain `applyMachineConfig` after boot.
  applyMachineConfig withObjects config.machineConfig

/-- V5-C/W4-E (M-DEF-3/L-15): **Deprecated** — use `bootFromPlatformChecked`
    for production boot paths. This function silently uses last-wins semantics
    on duplicate IRQs or object IDs, which can cause silent data loss if the
    same ObjId appears multiple times in the platform configuration.

    `bootFromPlatformChecked` validates `PlatformConfig.wellFormed` and returns
    an explicit error on duplicates, preventing silent overwrites.

    **Retained for**: backward compatibility with existing proofs and test code
    that exercises invalid-state scenarios (e.g., `NegativeStateSuite`). New
    boot paths should always use the checked variant. -/
abbrev bootFromPlatformUnchecked := bootFromPlatform

/-- Q3-C: Boot from empty config yields the empty IntermediateState. -/
theorem bootFromPlatform_empty :
    bootFromPlatform { irqTable := [], initialObjects := [] } =
    mkEmptyIntermediateState := rfl

/-- Q3-C: The booted state satisfies allTablesInvExtK. -/
theorem bootFromPlatform_allTablesInvExtK (config : PlatformConfig) :
    (bootFromPlatform config).state.allTablesInvExtK :=
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
    ist.state.allTablesInvExtK ∧
    perObjectSlotsInvariant ist.state ∧
    perObjectMappingsInvariant ist.state ∧
    SystemState.lifecycleMetadataConsistent ist.state :=
  ⟨bootFromPlatform_allTablesInvExtK config,
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

/-- X2-F: Transparent empty IRQ uniqueness — fully kernel-evaluable. -/
theorem irqsUniqueTransparent_empty : irqsUniqueTransparent [] = true := by
  decide

/-- X2-F: Transparent empty object ID uniqueness — fully kernel-evaluable. -/
theorem objectIdsUniqueTransparent_empty : objectIdsUniqueTransparent [] = true := by
  decide

-- ============================================================================
-- AJ3-C (M-16): bootSafeObjectCheck — Bool mirror of bootSafeObject
-- ============================================================================

/-- AJ3-C (M-16): Bool-valued runtime check for boot-safe objects.
    Validates structural boot safety constraints that can be checked at
    runtime. Used by `bootFromPlatformChecked` to reject invalid objects.

    **Coverage**: Checks all `bootSafeObject` conjuncts except CNode badge
    validity. Badge validity requires iterating over all CNode slot entries
    with a `get? → toList` bridge that would add complexity for a property
    that is vacuously true for empty boot-config CNodes. Badge validity
    remains checked at the Prop level via `bootFromPlatform_proofLayerInvariantBundle_general`. -/
def bootSafeObjectCheck (obj : KernelObject) : Bool :=
  match obj with
  | .endpoint ep =>
    ep.sendQ.head.isNone && ep.sendQ.tail.isNone &&
    ep.receiveQ.head.isNone && ep.receiveQ.tail.isNone
  | .notification notif =>
    decide (notif.state = .idle) && notif.waitingThreads.isEmpty &&
    notif.pendingBadge.isNone
  | .cnode cn =>
    decide (cn.slots.size ≤ cn.slotCount) &&
    decide (cn.depth ≤ maxCSpaceDepth) &&
    decide (cn.bitsConsumed > 0 → cn.bitsConsumed ≤ cn.depth ∧ 0 < cn.bitsConsumed ∧ cn.guardBounded)
  | .tcb tcb =>
    tcb.pendingMessage.isNone && decide (tcb.ipcState = .ready) &&
    tcb.queueNext.isNone && tcb.queuePrev.isNone &&
    tcb.timeoutBudget.isNone &&
    decide (tcb.schedContextBinding = .unbound)
  | .vspaceRoot _ => false
  | .untyped _ => true
  | .schedContext sc =>
    sc.period.isPositive &&
    decide (sc.budget.val ≤ sc.period.val) &&
    decide (sc.budgetRemaining.val ≤ sc.budget.val) &&
    decide (sc.replenishments.length ≤ maxReplenishments) &&
    sc.replenishments.all (fun r => decide (r.amount.val > 0)) &&
    sc.replenishments.all (fun r => decide (r.amount.val ≤ sc.budget.val)) &&
    sc.boundThread.isNone

set_option maxHeartbeats 400000 in
/-- AJ3-C (M-16): Partial soundness bridge — `bootSafeObjectCheck = true` implies
    the structural conjuncts of `bootSafeObject` (all except CNode badge validity).
    Badge validity is a Prop-level guarantee discharged by the boot invariant
    bridge theorem `bootFromPlatform_proofLayerInvariantBundle_general`. -/
theorem bootSafeObjectCheck_sound_structural (obj : KernelObject)
    (h : bootSafeObjectCheck obj = true) :
    -- Endpoints: empty queues
    (∀ ep, obj = .endpoint ep →
      ep.sendQ.head = none ∧ ep.sendQ.tail = none ∧
      ep.receiveQ.head = none ∧ ep.receiveQ.tail = none) ∧
    -- Notifications: idle + empty
    (∀ notif, obj = .notification notif →
      notif.state = .idle ∧ notif.waitingThreads = [] ∧ notif.pendingBadge = none) ∧
    -- CNodes: structural (excluding badge validity)
    (∀ cn, obj = .cnode cn →
      cn.slotCountBounded ∧ cn.depth ≤ maxCSpaceDepth ∧
      (cn.bitsConsumed > 0 → cn.wellFormed)) ∧
    -- TCBs: clean boot state
    (∀ tcb, obj = .tcb tcb →
      tcb.pendingMessage = none ∧ tcb.ipcState = .ready ∧
      tcb.queueNext = none ∧ tcb.queuePrev = none ∧
      tcb.timeoutBudget = none ∧
      tcb.schedContextBinding = .unbound) ∧
    -- VSpaceRoots: excluded
    (∀ vs, obj ≠ .vspaceRoot vs) ∧
    -- SchedContexts: well-formed and unbound
    (∀ sc, obj = .schedContext sc →
      schedContextWellFormed sc ∧ sc.boundThread = none) := by
  -- Discharge each constructor case. Non-matching constructors produce absurd
  -- injection hypotheses, discharged by `intro _ h; cases h`.
  cases obj with
  | endpoint ep =>
    simp only [bootSafeObjectCheck, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨fun _ he => by injection he; subst_vars; exact ⟨Option.eq_none_of_isNone h1, Option.eq_none_of_isNone h2, Option.eq_none_of_isNone h3, Option.eq_none_of_isNone h4⟩,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he⟩
  | notification notif =>
    simp only [bootSafeObjectCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨fun _ he => by injection he, fun _ he => by injection he; subst_vars; exact ⟨h1, List.isEmpty_iff.mp h2, Option.eq_none_of_isNone h3⟩,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he⟩
  | cnode cn =>
    simp only [bootSafeObjectCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hSlots, hDepth⟩, hWf⟩ := h
    exact ⟨fun _ he => by injection he, fun _ he => by injection he,
           fun c hc => by injection hc; subst_vars; exact ⟨hSlots, hDepth, hWf⟩,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he⟩
  | tcb tcb =>
    simp only [bootSafeObjectCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    exact ⟨fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he,
           fun _ he => by injection he; subst_vars; exact ⟨Option.eq_none_of_isNone h1, h2, Option.eq_none_of_isNone h3, Option.eq_none_of_isNone h4, Option.eq_none_of_isNone h5, h6⟩,
           fun _ he => by injection he, fun _ he => by injection he⟩
  | vspaceRoot _ =>
    simp [bootSafeObjectCheck] at h
  | untyped _ =>
    exact ⟨fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he⟩
  | schedContext sc =>
    simp only [bootSafeObjectCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hPeriod, hBudgetPeriod⟩, hRemaining⟩, hRepLen⟩, hRepPos⟩, hRepBound⟩, hUnbound⟩ := h
    refine ⟨fun _ he => by injection he, fun _ he => by injection he,
            fun _ he => by injection he, fun _ he => by injection he,
            fun _ he => by injection he, fun s hs => ?_⟩
    injection hs; subst_vars
    constructor
    · unfold schedContextWellFormed
      refine ⟨⟨hPeriod, hBudgetPeriod, hRemaining, hRepLen⟩, ⟨hRemaining, hBudgetPeriod⟩,
              ⟨hRepLen, ?_⟩, ?_⟩
      · intro r hr; exact decide_eq_true_eq.mp (List.all_eq_true.mp hRepPos r hr)
      · intro r hr; exact decide_eq_true_eq.mp (List.all_eq_true.mp hRepBound r hr)
    · exact Option.eq_none_of_isNone hUnbound

/-- U6-E/F: Checked boot — rejects configs with duplicate IRQs, duplicate object
    IDs, or unsafe initial objects.

    V5-C (M-DEF-3): **Recommended boot entry point.** This is the enforcement
    variant of `bootFromPlatform`. It validates `PlatformConfig.wellFormed`
    (uniqueness) AND `bootSafeObjectCheck` (object-level semantic safety) before
    proceeding. Returns an error if validation fails.

    AJ3-C (M-16): Added `bootSafeObjectCheck` validation. A config with unique
    IDs but invalid object states (e.g., endpoint with non-empty queues, TCB with
    `ipcState != .ready`) is now rejected.

    Use `bootFromPlatformUnchecked` (alias for `bootFromPlatform`) only when
    the config is known-valid (e.g., constructed programmatically with
    uniqueness guarantees). All new boot paths should use this function. -/
def bootFromPlatformChecked (config : PlatformConfig) :
    Except String IntermediateState :=
  if config.wellFormed then
    if config.initialObjects.all (fun entry => bootSafeObjectCheck entry.obj) then
      .ok (bootFromPlatform config)
    else
      .error "boot: object fails bootSafe check (invalid state for boot)"
  else if ¬ irqsUnique config.irqTable then
    .error "boot: duplicate IRQ registration detected in platform config"
  else
    .error "boot: duplicate object ID detected in platform config"

/-- U6-E/F/AJ3-C: Checked boot agrees with unchecked boot on well-formed +
    boot-safe configs. -/
theorem bootFromPlatformChecked_eq_bootFromPlatform (config : PlatformConfig)
    (hWf : config.wellFormed = true)
    (hSafe : config.initialObjects.all (fun entry => bootSafeObjectCheck entry.obj) = true) :
    bootFromPlatformChecked config = .ok (bootFromPlatform config) := by
  simp [bootFromPlatformChecked, hWf, hSafe]

/-- U6-E/F: Checked boot rejects configs that are not well-formed. -/
theorem bootFromPlatformChecked_rejects_invalid (config : PlatformConfig)
    (hNotWf : config.wellFormed = false) :
    (bootFromPlatformChecked config).isOk = false := by
  simp [bootFromPlatformChecked, hNotWf]
  split <;> rfl

/-- AJ3-C: Empty config trivially passes bootSafe check. -/
theorem bootSafeObjectCheck_empty_config :
    ([] : List ObjectEntry).all (fun entry => bootSafeObjectCheck entry.obj) = true := by
  rfl

/-- AG1-D: Boot with duplicate detection warnings.

Provides a middle ground between the silent `bootFromPlatform` (last-wins, no
feedback) and the rejecting `bootFromPlatformChecked` (fails on duplicates).
Returns the booted `IntermediateState` alongside a list of warning strings
describing any detected duplicates.

This is useful for development and debugging: the boot always succeeds (like
`bootFromPlatform`), but callers can inspect warnings to detect configuration
issues. Production boot paths should still use `bootFromPlatformChecked`.

**Warning categories**:
- Duplicate IRQ INTIDs: "duplicate IRQ: INTID {n} (last-wins)"
- Duplicate object IDs: "duplicate object ID: {n} (last-wins)" -/
def bootFromPlatformWithWarnings (config : PlatformConfig)
    : IntermediateState × List String :=
  let irqWarnings := if irqsUnique config.irqTable then []
    else config.irqTable.foldl (fun (acc : List Nat × List String) entry =>
      if entry.irq.toNat ∈ acc.1 then
        (acc.1, acc.2 ++ [s!"duplicate IRQ: INTID {entry.irq.toNat} (last-wins)"])
      else
        (entry.irq.toNat :: acc.1, acc.2)
    ) ([], []) |>.2
  let objWarnings := if objectIdsUnique config.initialObjects then []
    else config.initialObjects.foldl (fun (acc : List Nat × List String) entry =>
      if entry.id.toNat ∈ acc.1 then
        (acc.1, acc.2 ++ [s!"duplicate object ID: {entry.id.toNat} (last-wins)"])
      else
        (entry.id.toNat :: acc.1, acc.2)
    ) ([], []) |>.2
  (bootFromPlatform config, irqWarnings ++ objWarnings)

/-- AG1-D: `bootFromPlatformWithWarnings` returns no warnings on well-formed configs. -/
theorem bootFromPlatformWithWarnings_wellFormed_no_warnings (config : PlatformConfig)
    (hWf : config.wellFormed = true) :
    (bootFromPlatformWithWarnings config).2 = [] := by
  simp [bootFromPlatformWithWarnings]
  constructor
  · -- irqsUnique holds when wellFormed
    have : irqsUnique config.irqTable = true := by
      unfold PlatformConfig.wellFormed at hWf; simp [Bool.and_eq_true] at hWf; exact hWf.1
    simp [this]
  · -- objectIdsUnique holds when wellFormed
    have : objectIdsUnique config.initialObjects = true := by
      unfold PlatformConfig.wellFormed at hWf; simp [Bool.and_eq_true] at hWf; exact hWf.2
    simp [this]

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
only preserve 4 structural invariants, not the full 10-component
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
    the 4 structural invariants). V4-A extends this to general configs. -/
theorem bootToRuntime_invariantBridge_empty :
    let ist := bootFromPlatform { irqTable := [], initialObjects := [] }
    SeLe4n.Kernel.Architecture.proofLayerInvariantBundle ist.state ∧
    SeLe4n.Model.apiInvariantBundle_frozen (SeLe4n.Model.freeze ist) :=
  ⟨emptyBoot_proofLayerInvariantBundle, emptyBoot_freeze_preserves⟩

/- Boot-to-Runtime Invariant Bridge — Known Limitation (AE5-D/U-21/PLT-01)

   `bootToRuntime_invariantBridge_empty` proves the full 10-component
   `proofLayerInvariantBundle` holds after booting with an empty
   PlatformConfig. For non-empty configs (real hardware with IRQ tables,
   pre-allocated objects), the full bundle is NOT proven to hold.

   The checked boot path `bootFromPlatformChecked` validates per-object
   well-formedness and uniqueness, but does not prove the resulting state
   satisfies all 10 runtime invariants simultaneously.

   Remediation deferred to WS-V (hardware binding). When RPi5 boot is
   implemented, either:
   (a) Prove `bootToRuntime_invariantBridge` for arbitrary well-formed
       PlatformConfig, or
   (b) Add a post-boot runtime invariant validation pass that asserts all
       10 invariants hold before enabling syscall dispatch.

   AI6-B (M-07): Proven for empty PlatformConfig only. General config
   bridge requires a `bootSafe` predicate ensuring per-object well-formedness
   and inter-object consistency (endpoint queue references, CDT edges, etc.).
   The `bootFromPlatformChecked` variant (Boot.lean:370) validates structural
   per-object constraints but does not compose them into the full runtime
   invariant bundle. -/

-- ============================================================================
-- V4-A1: Builder Operation × Invariant Component Interaction Matrix
-- ============================================================================

/-! ### V4-A1: Interaction Matrix

The following matrix documents which builder operations affect which
invariant components of `proofLayerInvariantBundle`. Each cell is either
"vacuous" (operation doesn't modify fields read by that component) or
"substantive" (proof of preservation required).

| Component \ Operation       | registerIrq | createObject |
|-----------------------------|-------------|--------------|
| 1. schedulerInvariantFull   | vacuous     | vacuous      |
| 2. capabilityInvariantBundle| vacuous     | vacuous†     |
| 3. coreIpcInvariantBundle   | vacuous     | vacuous      |
| 4. ipcSchedCoupling         | vacuous     | vacuous      |
| 5. lifecycleInvariantBundle | vacuous     | substantive  |
| 6. serviceLifecycleCapBundle| vacuous     | vacuous†     |
| 7. vspaceInvariantBundle    | vacuous     | vacuous†     |
| 8. crossSubsystemInvariant  | vacuous     | vacuous†     |
| 9. tlbConsistent            | vacuous     | vacuous      |
| 10. schedInvariantExtended  | vacuous     | vacuous†     |

† The component reads `objects`, which `createObject` modifies. However, the
  component's predicates are quantified over OTHER state fields (scheduler
  queues, CDT edges, service registry, ASID table) that are UNCHANGED by
  `createObject`. Since the quantification domain is unchanged and existing
  objects are unmodified, preservation is a frame argument. The new object
  is only reachable through the modified `objects` table and doesn't appear
  in any quantification domain (no scheduler membership, no CDT parent, no
  service backing, no ASID mapping).

**Key insight**: `registerIrq` modifies only `irqHandlers`, which no invariant
component reads. `createObject` modifies `objects`, `objectIndex`,
`objectIndexSet`, and `lifecycle.objectTypes`. All 9 components are preserved
because either they don't read the modified fields, or they quantify over
state structures (queues, CDT, registries) that are unmodified.

Note: `lifecycleInvariantBundle` component 5 is "substantive" because it
directly relates `objects` to `lifecycle.objectTypes`, both of which are
modified. The proof shows that the new entry is consistent.
-/

-- ============================================================================
-- V4-A2: registerIrq preserves proofLayerInvariantBundle
-- ============================================================================

/-! ### V4-A2: registerIrq Frame Lemma

`registerIrq` only modifies `st.irqHandlers`. All 9 components of
`proofLayerInvariantBundle` are independent of `irqHandlers`:

- Components 1–8 read scheduler, objects, CDT, services, serviceRegistry,
  interfaceRegistry, asidTable, lifecycle, and TLB — none of which include
  `irqHandlers`.
- Component 9 (`tlbConsistent`) reads TLB entries and objects/asidTable.

Therefore all 9 components are trivially preserved. -/

/-- V4-A2: The state produced by `registerIrq` has identical fields to the
    input state, except for `irqHandlers`. This is the core frame lemma. -/
private theorem registerIrq_state_fields_eq (ist : IntermediateState)
    (irq : SeLe4n.Irq) (handler : SeLe4n.ObjId) :
    let st := ist.state
    let st' := (registerIrq ist irq handler).state
    st'.scheduler = st.scheduler ∧
    st'.objects = st.objects ∧
    st'.cdt = st.cdt ∧
    st'.services = st.services ∧
    st'.serviceRegistry = st.serviceRegistry ∧
    st'.interfaceRegistry = st.interfaceRegistry ∧
    st'.asidTable = st.asidTable ∧
    st'.lifecycle = st.lifecycle ∧
    st'.tlb = st.tlb ∧
    st'.machine = st.machine ∧
    st'.objectIndex = st.objectIndex ∧
    st'.objectIndexSet = st.objectIndexSet := by
  simp [registerIrq]

-- ============================================================================
-- V4-A2–A7: Per-operation and boot-state frame lemmas
-- ============================================================================

/-! ### V4-A2–A8: Boot state invariant proofs

**Strategy**: Rather than proving per-operation frame lemmas that transfer
`proofLayerInvariantBundle` through each builder operation (which requires
deep unfolding of 9×N invariant components), we prove the result directly:
the post-boot state satisfies the full 10-component bundle.

The key insight is that `bootFromPlatform` only modifies 4 fields from
default: `objects`, `irqHandlers`, `objectIndex`/`objectIndexSet`, and
`lifecycle.objectTypes`. All other state fields remain at their default
values. Since:

1. **Scheduler** is default (empty queues, no current thread) →
   scheduler invariants hold vacuously
2. **CDT** is default (no edges) → CDT/capability derivation invariants
   hold vacuously
3. **Services/serviceRegistry/interfaceRegistry** are default →
   service invariants hold vacuously
4. **AsidTable** is default → ASID invariants hold vacuously
5. **TLB** is default → TLB consistency holds trivially
6. **IPC state** (endpoint queues, notifications) — fresh objects from
   boot have no queue membership, no blocking threads → IPC invariants
   hold vacuously

The proof chains through: (a) boot preserves default on non-modified fields,
(b) each invariant component depends only on fields that are either default
or satisfy the boot preconditions.
-/

-- Step 1: Per-field preservation for registerIrq
@[simp] private theorem registerIrq_scheduler (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.scheduler = ist.state.scheduler := rfl
@[simp] private theorem registerIrq_cdt (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.cdt = ist.state.cdt := rfl
@[simp] private theorem registerIrq_services (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.services = ist.state.services := rfl
@[simp] private theorem registerIrq_serviceRegistry (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.serviceRegistry = ist.state.serviceRegistry := rfl
@[simp] private theorem registerIrq_interfaceRegistry (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.interfaceRegistry = ist.state.interfaceRegistry := rfl
@[simp] private theorem registerIrq_asidTable (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.asidTable = ist.state.asidTable := rfl
@[simp] private theorem registerIrq_tlb (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.tlb = ist.state.tlb := rfl
@[simp] private theorem registerIrq_machine (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.machine = ist.state.machine := rfl
@[simp] private theorem registerIrq_objects (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.objects = ist.state.objects := rfl
@[simp] private theorem registerIrq_lifecycle (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.lifecycle = ist.state.lifecycle := rfl
@[simp] private theorem registerIrq_objectIndex (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.objectIndex = ist.state.objectIndex := rfl
@[simp] private theorem registerIrq_objectIndexSet (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.objectIndexSet = ist.state.objectIndexSet := rfl
@[simp] private theorem registerIrq_cdtNodeSlot (ist : IntermediateState) irq handler :
    (registerIrq ist irq handler).state.cdtNodeSlot = ist.state.cdtNodeSlot := rfl

-- Step 2: Per-field preservation for createObject
@[simp] private theorem createObject_scheduler (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.scheduler = ist.state.scheduler := rfl
@[simp] private theorem createObject_cdt (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.cdt = ist.state.cdt := rfl
@[simp] private theorem createObject_services (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.services = ist.state.services := rfl
@[simp] private theorem createObject_serviceRegistry (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.serviceRegistry = ist.state.serviceRegistry := rfl
@[simp] private theorem createObject_interfaceRegistry (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.interfaceRegistry = ist.state.interfaceRegistry := rfl
@[simp] private theorem createObject_asidTable (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.asidTable = ist.state.asidTable := rfl
@[simp] private theorem createObject_tlb (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.tlb = ist.state.tlb := rfl
@[simp] private theorem createObject_machine (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.machine = ist.state.machine := rfl
@[simp] private theorem createObject_capabilityRefs (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.lifecycle.capabilityRefs =
    ist.state.lifecycle.capabilityRefs := rfl
@[simp] private theorem createObject_irqHandlers (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.irqHandlers = ist.state.irqHandlers := rfl
@[simp] private theorem createObject_cdtNodeSlot (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.cdtNodeSlot = ist.state.cdtNodeSlot := rfl
@[simp] private theorem createObject_objects (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.objects = ist.state.objects.insert id obj := rfl

-- Step 3: Fold-level field preservation (foldIrqs)
private theorem foldIrqs_scheduler (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.scheduler = ist.state.scheduler := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons e rest ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_cdt (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.cdt = ist.state.cdt := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_objects (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.objects = ist.state.objects := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_services (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.services = ist.state.services := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_serviceRegistry (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.serviceRegistry = ist.state.serviceRegistry := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_interfaceRegistry (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.interfaceRegistry = ist.state.interfaceRegistry := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_asidTable (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.asidTable = ist.state.asidTable := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_tlb (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.tlb = ist.state.tlb := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_machine (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.machine = ist.state.machine := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_lifecycle (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.lifecycle = ist.state.lifecycle := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_objectIndex (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.objectIndex = ist.state.objectIndex := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_objectIndexSet (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.objectIndexSet = ist.state.objectIndexSet := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_cdtNodeSlot (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.cdtNodeSlot = ist.state.cdtNodeSlot := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

-- Step 4: Fold-level field preservation (foldObjects)
private theorem foldObjects_scheduler (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.scheduler = ist.state.scheduler := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_cdt (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.cdt = ist.state.cdt := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_services (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.services = ist.state.services := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_serviceRegistry (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.serviceRegistry = ist.state.serviceRegistry := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_interfaceRegistry (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.interfaceRegistry = ist.state.interfaceRegistry := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_asidTable (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.asidTable = ist.state.asidTable := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_tlb (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.tlb = ist.state.tlb := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_machine (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.machine = ist.state.machine := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_capabilityRefs (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.lifecycle.capabilityRefs =
    ist.state.lifecycle.capabilityRefs := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_irqHandlers (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.irqHandlers = ist.state.irqHandlers := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_cdtNodeSlot (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.cdtNodeSlot = ist.state.cdtNodeSlot := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

-- Bridge lemma: mkEmptyIntermediateState.state = default
private theorem mkEmpty_state_eq_default :
    mkEmptyIntermediateState.state = (default : SystemState) := rfl

-- Step 5: Boot-level field preservation (compose foldIrqs + foldObjects)
/-- V4-A2/A4/A7: The post-boot state preserves scheduler from default. -/
theorem bootFromPlatform_scheduler_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.scheduler =
    (default : SystemState).scheduler := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_scheduler_eq, foldObjects_scheduler, foldIrqs_scheduler, mkEmpty_state_eq_default]

/-- V4-A2/A4: The post-boot state preserves CDT from default. -/
theorem bootFromPlatform_cdt_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.cdt =
    (default : SystemState).cdt := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_cdt_eq, foldObjects_cdt, foldIrqs_cdt, mkEmpty_state_eq_default]

/-- V4-A3: The post-boot state preserves services from default. -/
theorem bootFromPlatform_services_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.services =
    (default : SystemState).services := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_services_eq, foldObjects_services, foldIrqs_services, mkEmpty_state_eq_default]

/-- V4-A3: The post-boot state preserves serviceRegistry from default. -/
theorem bootFromPlatform_serviceRegistry_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.serviceRegistry =
    (default : SystemState).serviceRegistry := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_serviceRegistry_eq, foldObjects_serviceRegistry, foldIrqs_serviceRegistry, mkEmpty_state_eq_default]

/-- V4-A3: The post-boot state preserves interfaceRegistry from default. -/
theorem bootFromPlatform_interfaceRegistry_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.interfaceRegistry =
    (default : SystemState).interfaceRegistry := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_interfaceRegistry_eq, foldObjects_interfaceRegistry, foldIrqs_interfaceRegistry, mkEmpty_state_eq_default]

/-- V4-A6: The post-boot state preserves asidTable from default. -/
theorem bootFromPlatform_asidTable_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.asidTable =
    (default : SystemState).asidTable := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_asidTable_eq, foldObjects_asidTable, foldIrqs_asidTable, mkEmpty_state_eq_default]

/-- V4-A7: The post-boot state preserves TLB from default. -/
theorem bootFromPlatform_tlb_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.tlb =
    (default : SystemState).tlb := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_tlb_eq, foldObjects_tlb, foldIrqs_tlb, mkEmpty_state_eq_default]

/-- AH2-F: After boot, machine config-set fields come from `config.machineConfig`.
    This replaces the pre-AH2 `bootFromPlatform_machine_eq` which stated the
    machine state was always default — that is no longer true since `bootFromPlatform`
    now integrates `applyMachineConfig`. -/
theorem bootFromPlatform_machine_physicalAddressWidth (config : PlatformConfig) :
    (bootFromPlatform config).state.machine.physicalAddressWidth =
    config.machineConfig.physicalAddressWidth := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_physicalAddressWidth]

/-- AH2-F: Non-config machine fields (regs, memory, timer, systemRegisters,
    interruptsEnabled) are preserved from default after boot.

    AK7-K (F-L4 / LOW) — boot interrupt-enable window: the Lean model's
    `bootFromPlatform` does NOT enable interrupts. The default
    `MachineState.interruptsEnabled = false` (AJ3-E) is preserved through
    boot, matching ARM64 reset state. On real hardware the Rust HAL boot
    sequence (`sele4n-hal/src/boot.rs` `rust_boot_main`) enables
    interrupts in **Phase 3** (after GIC init + timer programming) via
    `interrupts::enable_irq()`. Between MMU enable (Phase 1) and GIC init
    (Phase 3) the kernel runs with IRQs masked — this is the
    interrupt-enable window. `tests/InterruptDispatchSuite.lean` covers
    the Lean-side interrupt path; the Phase 3 enable is a HAL-layer
    obligation. -/
theorem bootFromPlatform_machine_non_config_fields (config : PlatformConfig) :
    (bootFromPlatform config).state.machine.regs = (default : SystemState).machine.regs ∧
    (bootFromPlatform config).state.machine.memory = (default : SystemState).machine.memory ∧
    (bootFromPlatform config).state.machine.timer = (default : SystemState).machine.timer ∧
    (bootFromPlatform config).state.machine.systemRegisters = (default : SystemState).machine.systemRegisters ∧
    (bootFromPlatform config).state.machine.interruptsEnabled = (default : SystemState).machine.interruptsEnabled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (show _ = _; unfold bootFromPlatform; simp [applyMachineConfig, foldObjects_machine, foldIrqs_machine, mkEmpty_state_eq_default])

/-- Fold-level: foldIrqs preserves capabilityRefs. -/
private theorem foldIrqs_capabilityRefs (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.lifecycle.capabilityRefs =
    ist.state.lifecycle.capabilityRefs := by
  have h := foldIrqs_lifecycle irqs ist
  exact congrArg (·.capabilityRefs) h

/-- V4-A5: The post-boot state preserves capabilityRefs from default. -/
private theorem applyMachineConfig_capabilityRefs_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.lifecycle.capabilityRefs =
    ist.state.lifecycle.capabilityRefs := rfl

theorem bootFromPlatform_capabilityRefs_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.lifecycle.capabilityRefs =
    (default : SystemState).lifecycle.capabilityRefs := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_capabilityRefs_eq, foldObjects_capabilityRefs, foldIrqs_capabilityRefs]
  rw [show mkEmptyIntermediateState.state.lifecycle.capabilityRefs =
        (default : SystemState).lifecycle.capabilityRefs from rfl]

/-- V4-A5b: The post-boot state preserves cdtNodeSlot from default. -/
theorem bootFromPlatform_cdtNodeSlot_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.cdtNodeSlot =
    (default : SystemState).cdtNodeSlot := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_cdtNodeSlot_eq, foldObjects_cdtNodeSlot, foldIrqs_cdtNodeSlot, mkEmpty_state_eq_default]

-- ============================================================================
-- V4-A4/A8: Boot-safe object predicate
-- ============================================================================

/-- V4-A4: A kernel object is "boot-safe" if it satisfies invariant
    preconditions for a freshly-booted state. During boot, there are no
    scheduler queues, no CDT edges, no service registrations, and no
    ASID mappings. Objects must satisfy IPC, queue, and structural
    constraints for the full 10-component `proofLayerInvariantBundle`.

    M-04/AH5-A/AI6-B(M-11): **Design rationale — VSpaceRoot exclusion**. VSpaceRoots are
    excluded from `bootSafeObject` because ASID table registration
    (`asidTable.insert asid id` in `storeObject`) requires a fully initialized
    ASID manager, which is not available during the builder-phase boot sequence.
    The boot pipeline constructs an `IntermediateState` that does not yet
    contain ASID pool infrastructure.

    **Tradeoff**: All address spaces must be configured post-boot via `vspaceMap`
    syscalls. This prevents pre-populating address space mappings during boot.

    **Integration timeline**: VSpaceRoot boot support is planned for WS-V when
    the ASID manager is wired into the `IntermediateState` builder operations.
    The `AsidManager` type and `asidPoolUnique` invariant (AsidManager.lean)
    provide the foundation — the missing piece is builder-phase ASID pool
    integration. -/
def bootSafeObject (obj : KernelObject) : Prop :=
  -- Endpoints must have empty queues (no thread references)
  (∀ ep, obj = .endpoint ep →
    ep.sendQ.head = none ∧ ep.sendQ.tail = none ∧
    ep.receiveQ.head = none ∧ ep.receiveQ.tail = none) ∧
  -- Notifications must be idle with empty wait lists and no pending badge
  (∀ notif, obj = .notification notif →
    notif.state = .idle ∧ notif.waitingThreads = [] ∧ notif.pendingBadge = none) ∧
  -- CNodes must satisfy slot-count bound, depth consistency, and badge validity
  (∀ cn, obj = .cnode cn →
    cn.slotCountBounded ∧ cn.depth ≤ maxCSpaceDepth ∧
    (cn.bitsConsumed > 0 → cn.wellFormed) ∧
    (∀ slot cap badge, cn.lookup slot = some cap →
      cap.badge = some badge → badge.valid)) ∧
  -- TCBs must have clean boot state: no pending messages, ready IPC state,
  -- no queue links (queueNext/queuePrev = none), no timeout budget
  (∀ tcb, obj = .tcb tcb →
    tcb.pendingMessage = none ∧ tcb.ipcState = .ready ∧
    tcb.queueNext = none ∧ tcb.queuePrev = none ∧
    tcb.timeoutBudget = none ∧
    tcb.schedContextBinding = .unbound) ∧
  -- VSpaceRoots excluded (require asidTable registration not available at boot)
  (∀ vs, obj ≠ .vspaceRoot vs) ∧
  -- Z9-I: SchedContexts must be well-formed and unbound at boot
  (∀ sc, obj = .schedContext sc →
    schedContextWellFormed sc ∧ sc.boundThread = none)

/-- V4-A4: A PlatformConfig is boot-safe if all initial objects satisfy
    boot safety constraints. This is the standard precondition for
    extending the invariant bridge to non-empty configs. -/
def PlatformConfig.bootSafe (config : PlatformConfig) : Prop :=
  ∀ entry, entry ∈ config.initialObjects → bootSafeObject entry.obj

-- ============================================================================
-- V4-A4b: Boot-safe object bridge — connect boot state objects to bootSafe
-- ============================================================================

/-- V4-A4b: Every object in the fold result is either from the base state or
    from one of the folded entries. Combined with bootSafe, this shows all
    post-boot objects satisfy bootSafeObject. -/
private theorem foldObjects_objects_bootSafe
    (objs : List ObjectEntry) :
    ∀ (ist : IntermediateState),
    (∀ (oid : SeLe4n.ObjId) (obj : KernelObject), ist.state.objects[oid]? = some obj → bootSafeObject obj) →
    (∀ e, e ∈ objs → bootSafeObject e.obj) →
    ∀ (oid : SeLe4n.ObjId) (obj : KernelObject), (foldObjects objs ist).state.objects[oid]? = some obj →
    bootSafeObject obj := by
  induction objs with
  | nil => intro ist hBase _; exact hBase
  | cons e rest ih =>
    intro ist hBase hObjs
    have heSafe : bootSafeObject e.obj := hObjs e (List.mem_cons_self ..)
    have hRestSafe : ∀ e', e' ∈ rest → bootSafeObject e'.obj :=
      fun e' hMem => hObjs e' (List.mem_cons_of_mem _ hMem)
    have hNewBase : ∀ (oid : SeLe4n.ObjId) (obj' : KernelObject), (createObject ist e.id e.obj e.hSlots e.hMappings).state.objects[oid]? = some obj' → bootSafeObject obj' := by
      intro oid₂ obj₂ hLookup₂
      have hObjInvExt : ist.state.objects.invExt := ist.hAllTables.1.1
      simp only [createObject_objects, RHTable_getElem?_eq_get?] at hLookup₂
      by_cases hEq : e.id = oid₂
      · subst hEq
        rw [RHTable.getElem?_insert_self ist.state.objects e.id e.obj hObjInvExt] at hLookup₂
        cases hLookup₂; exact heSafe
      · have hNe : ¬((e.id == oid₂) = true) := by intro heq; exact hEq (eq_of_beq heq)
        rw [RHTable.getElem?_insert_ne ist.state.objects e.id oid₂ e.obj hNe hObjInvExt] at hLookup₂
        exact hBase oid₂ obj₂ (by simp only [RHTable_getElem?_eq_get?]; exact hLookup₂)
    exact ih (createObject ist e.id e.obj e.hSlots e.hMappings) hNewBase hRestSafe

/-- V4-A4b: Every object in the post-boot state satisfies bootSafeObject. -/
private theorem bootFromPlatform_objects_bootSafe
    (config : PlatformConfig) (hSafe : config.bootSafe) :
    ∀ (oid : SeLe4n.ObjId) (obj : KernelObject), (bootFromPlatform config).state.objects[oid]? = some obj →
    bootSafeObject obj := by
  unfold bootFromPlatform
  apply foldObjects_objects_bootSafe
  · -- Base: after foldIrqs, objects = mkEmpty objects = empty → vacuous
    intro oid obj hLookup
    rw [foldIrqs_objects] at hLookup
    have hEmpty : mkEmptyIntermediateState.state.objects[oid]? = none := by
      rw [mkEmpty_state_eq_default]; exact RHTable_get?_empty 16 (by omega)
    rw [hEmpty] at hLookup; exact absurd hLookup (by simp)
  · exact hSafe

-- ============================================================================
-- V4-A8: Composition — proofLayerInvariantBundle for general configs
-- ============================================================================

/-! ### V4-A8: General Boot Invariant Bridge

The composition theorem shows that for ANY `PlatformConfig`, the post-boot
state satisfies all 9 components of `proofLayerInvariantBundle`. The proof
uses the field preservation theorems to rewrite each component's state
references back to the default state where the component is already proved.

The key technical mechanism: each invariant component reads only fields that
are either (a) unchanged from default (scheduler, CDT, services, registries,
ASID table, TLB, machine, capabilityRefs) or (b) irrelevant to the component.
By rewriting the post-boot state's fields to default values, we reduce each
component to the already-proved `default_*` case.
-/

/-- V4-A8: The post-boot state from any config satisfies
    `proofLayerInvariantBundle`. This is the general boot invariant bridge.

    All 9 components are proved by showing the post-boot state is equivalent
    to the default state on the fields each component reads:

    1. schedulerInvariantBundleFull — scheduler is default
    2. capabilityInvariantBundle — CDT is empty, objects.invExt from builder
    3. coreIpcInvariantBundle — scheduler+CDT+IPC queues all default
    4. ipcSchedulerCouplingInvariantBundle — scheduler default, no blocking
    5. lifecycleInvariantBundle — metadata consistent from builder
    6. serviceLifecycleCapabilityInvariantBundle — services empty
    7. vspaceInvariantBundle — asidTable empty, no ASID mappings
    8. crossSubsystemInvariant — registries empty, no stale refs
    9. tlbConsistent — TLB is default (empty)
-/
theorem bootFromPlatform_proofLayerInvariantBundle_general
    (config : PlatformConfig) (hSafe : config.bootSafe) :
    Architecture.proofLayerInvariantBundle
      (bootFromPlatform config).state := by
  -- The post-boot state equals default on all fields that the 9 invariant
  -- components read, so we can transport the default proof.
  -- Since bootFromPlatform_empty_state shows the empty config case is rfl,
  -- and the non-empty config only adds objects/irqHandlers (neither of which
  -- affects the invariant components' relevant fields), the proof is:
  -- show the post-boot state and default state agree on all invariant-read fields,
  -- then apply the default bundle proof.
  -- Field preservation facts
  have hSch := bootFromPlatform_scheduler_eq config
  have hCdt := bootFromPlatform_cdt_eq config
  have hSvc := bootFromPlatform_services_eq config
  have hSvcR := bootFromPlatform_serviceRegistry_eq config
  have hIfR := bootFromPlatform_interfaceRegistry_eq config
  have hAsid := bootFromPlatform_asidTable_eq config
  have hTlb := bootFromPlatform_tlb_eq config
  -- Builder structural invariants
  have hSlots := (bootFromPlatform config).hPerObjectSlots
  have hAllTables := (bootFromPlatform config).hAllTables
  -- Scheduler sub-field facts
  have hCur : (bootFromPlatform config).state.scheduler.current = none := by
    rw [hSch]; decide
  have hRun : (bootFromPlatform config).state.scheduler.runnable = [] := by
    rw [hSch]; decide
  have hRQflat : (bootFromPlatform config).state.scheduler.runQueue.flat = [] := by
    rw [hSch]; decide
  -- 1. schedulerInvariantBundleFull
  have h1 : schedulerInvariantBundleFull (bootFromPlatform config).state := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [queueCurrentConsistent, hSch]
    · show (bootFromPlatform config).state.scheduler.runnable.Nodup
      rw [hRun]; exact List.nodup_nil
    · unfold currentThreadValid; rw [hCur]; trivial
    · intro tid hMem; rw [hRun] at hMem; simp at hMem
    · unfold currentTimeSlicePositive; rw [hCur]; trivial
    · unfold edfCurrentHasEarliestDeadline; rw [hCur]; trivial
    · unfold contextMatchesCurrent; rw [hCur]; trivial
    · intro tid hMem; rw [hRun] at hMem; simp at hMem
    · intro tid hMem
      have hInFlat := (RunQueue.mem_toList_iff_mem _ tid).mpr hMem
      simp [RunQueue.toList, hRQflat] at hInFlat
    · -- V5-H: domainTimeRemainingPositive — boot scheduler is default, DTR = 5
      unfold domainTimeRemainingPositive; rw [hSch]; decide
    · -- X2-A: domainScheduleEntriesPositive — boot scheduler has empty domainSchedule
      intro e hMem
      have hDS : (bootFromPlatform config).state.scheduler.domainSchedule = [] := by
        rw [hSch]; decide
      rw [hDS] at hMem; simp at hMem
  -- Boot-safe object bridge and shared helpers
  have hBS := bootFromPlatform_objects_bootSafe config hSafe
  have hCdtNS := bootFromPlatform_cdtNodeSlot_eq config
  -- No VSpaceRoots in boot state (bootSafe excludes them)
  have hNoVSpace : ∀ oid vs,
      (bootFromPlatform config).state.objects[oid]? ≠ some (KernelObject.vspaceRoot vs) :=
    fun oid vs hObj => (hBS oid _ hObj).2.2.2.2.1 vs rfl
  -- lookupService returns none (services empty)
  have hLookupSvcNone : ∀ sid,
      lookupService (bootFromPlatform config).state sid = none := by
    intro sid; unfold lookupService; rw [hSvc]
    exact RHTable_get?_empty 16 (by omega)
  -- 2. capabilityInvariantBundle
  have hCapBundle : capabilityInvariantBundle (bootFromPlatform config).state := by
    refine ⟨hSlots, ?_, ?_, ?_, ?_, ?_, hAllTables.1.1⟩
    · -- cspaceLookupSound
      intro cnodeId cn slot cap hObj hLookupSlot
      show SystemState.lookupSlotCap _ _ = some cap
      unfold SystemState.lookupSlotCap SystemState.lookupCNode; rw [hObj]; exact hLookupSlot
    · -- cspaceSlotCountBounded
      intro cnodeId cn hObj
      exact ((hBS cnodeId _ hObj).2.2.1 cn rfl).1
    · -- cdtCompleteness: cdtNodeSlot is empty
      intro nodeId ref hLookup; rw [hCdtNS] at hLookup
      have : (default : SystemState).cdtNodeSlot[nodeId]? = none := by
        simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
      rw [this] at hLookup; exact absurd hLookup (by simp)
    · -- cdtAcyclicity: CDT is default (empty)
      show (bootFromPlatform config).state.cdt.edgeWellFounded
      rw [hCdt]; exact CapDerivationTree.empty_edgeWellFounded
    · -- cspaceDepthConsistent
      intro cnodeId cn hObj
      have hCN := (hBS cnodeId _ hObj).2.2.1 cn rfl
      exact ⟨hCN.2.1, hCN.2.2.1⟩
  -- 5. lifecycleInvariantBundle
  have hLifeBundle : lifecycleInvariantBundle (bootFromPlatform config).state :=
    lifecycleInvariantBundle_of_metadata_consistent _
      (bootFromPlatform config).hLifecycleConsistent
  -- 3. ipcInvariantFull (16 sub-components, AJ1-B: +blockedOnReplyHasTarget)
  have hIpcFull : ipcInvariantFull (bootFromPlatform config).state := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ipcInvariant: notifications well-formed
      intro oid ntfn hObj
      have hNtfn := (hBS oid _ hObj).2.1 ntfn rfl
      show notificationInvariant ntfn
      unfold notificationInvariant notificationQueueWellFormed
      rw [hNtfn.1]; exact ⟨hNtfn.2.1, hNtfn.2.2⟩
    · -- dualQueueSystemInvariant
      refine ⟨?_, ?_, ?_⟩
      · -- all endpoints have well-formed queues
        intro epId ep hObj
        have hEp := (hBS epId _ hObj).1 ep rfl
        show dualQueueEndpointWellFormed epId (bootFromPlatform config).state
        unfold dualQueueEndpointWellFormed; rw [hObj]
        constructor
        · -- sendQ well-formed
          unfold intrusiveQueueWellFormed
          refine ⟨⟨fun _ => ?_, fun _ => ?_⟩, ?_, ?_⟩
          · exact hEp.2.1
          · exact hEp.1
          · intro hd hH; rw [hEp.1] at hH; exact absurd hH (by simp)
          · intro tl hT; rw [hEp.2.1] at hT; exact absurd hT (by simp)
        · -- receiveQ well-formed
          unfold intrusiveQueueWellFormed
          refine ⟨⟨fun _ => ?_, fun _ => ?_⟩, ?_, ?_⟩
          · exact hEp.2.2.2
          · exact hEp.2.2.1
          · intro hd hH; rw [hEp.2.2.1] at hH; exact absurd hH (by simp)
          · intro tl hT; rw [hEp.2.2.2] at hT; exact absurd hT (by simp)
      · -- tcbQueueLinkIntegrity
        constructor
        · intro a tcbA hObj b hNext
          have hTcb := (hBS a.toObjId _ hObj).2.2.2.1 tcbA rfl
          rw [hTcb.2.2.1] at hNext; exact absurd hNext (by simp)
        · intro b tcbB hObj a hPrev
          have hTcb := (hBS b.toObjId _ hObj).2.2.2.1 tcbB rfl
          rw [hTcb.2.2.2.1] at hPrev; exact absurd hPrev (by simp)
      · -- tcbQueueChainAcyclic: all boot TCBs have queueNext = none
        exact tcbQueueChainAcyclic_of_allNextNone (fun tid tcb hObj => by
          exact ((hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl).2.2.1)
    · -- allPendingMessagesBounded
      intro tid tcb msg hObj hPend
      have hTcb := (hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl
      rw [hTcb.1] at hPend; exact absurd hPend (by simp)
    · -- badgeWellFormed
      constructor
      · -- notificationBadgesWellFormed
        intro oid ntfn badge hObj hBadge
        have hNtfn := (hBS oid _ hObj).2.1 ntfn rfl
        rw [hNtfn.2.2] at hBadge; exact absurd hBadge (by simp)
      · -- capabilityBadgesWellFormed
        intro oid cn slot cap badge hObj hSlotLookup hBadge
        have hCN := (hBS oid _ hObj).2.2.1 cn rfl
        exact hCN.2.2.2 slot cap badge hSlotLookup hBadge
    · -- waitingThreadsPendingMessageNone
      intro tid tcb hObj
      have hTcb := (hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl
      rw [hTcb.2.1]; trivial
    · -- endpointQueueNoDup
      intro oid ep hObj
      have hEp := (hBS oid _ hObj).1 ep rfl
      constructor
      · intro tid tcb hTcbObj
        have hTcb := (hBS tid.toObjId _ hTcbObj).2.2.2.1 tcb rfl
        rw [hTcb.2.2.1]; simp
      · left; exact hEp.1
    · -- ipcStateQueueMembershipConsistent
      intro tid tcb hObj
      have hTcb := (hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl
      rw [hTcb.2.1]; trivial
    · -- queueNextBlockingConsistent
      intro a b tcbA tcbB hObjA _ hNext
      have hTcb := (hBS a.toObjId _ hObjA).2.2.2.1 tcbA rfl
      rw [hTcb.2.2.1] at hNext; exact absurd hNext (by simp)
    · -- queueHeadBlockedConsistent
      intro epId ep hd tcb hObjEp _
      have hEp := (hBS epId _ hObjEp).1 ep rfl
      constructor
      · intro hRecv; rw [hEp.2.2.1] at hRecv; exact absurd hRecv (by simp)
      · intro hSend; rw [hEp.1] at hSend; exact absurd hSend (by simp)
    · -- blockedThreadTimeoutConsistent
      intro tid tcb scId hObj hTimeout
      have hTcb := (hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl
      rw [hTcb.2.2.2.2.1] at hTimeout; exact absurd hTimeout (by simp)
    · -- Z7: donationChainAcyclic (vacuous: boot TCBs have .unbound binding)
      intro tid1 _ tcb1 _ _ _ h1 _ hB1 _
      have hTcb1 := (hBS tid1.toObjId _ h1).2.2.2.1 tcb1 rfl
      rw [hTcb1.2.2.2.2.2] at hB1; cases hB1
    · -- Z7: donationOwnerValid (vacuous: no donated bindings at boot)
      intro tid tcb _ _ h hBinding
      have hTcb := (hBS tid.toObjId _ h).2.2.2.1 tcb rfl
      rw [hTcb.2.2.2.2.2] at hBinding; cases hBinding
    · -- Z7: passiveServerIdle (boot TCBs have ipcState = .ready)
      intro tid tcb h _ _ _
      have hTcb := (hBS tid.toObjId _ h).2.2.2.1 tcb rfl
      left; exact hTcb.2.1
    · -- Z7: donationBudgetTransfer (vacuous: all TCBs have .unbound → scId? = none)
      intro tid1 _ tcb1 _ _ h1 _ _ hB1 _
      have hTcb1 := (hBS tid1.toObjId _ h1).2.2.2.1 tcb1 rfl
      simp [hTcb1.2.2.2.2.2, SchedContextBinding.scId?] at hB1
    · -- AG1-C: uniqueWaiters (boot notifications have empty waitingThreads)
      intro oid ntfn hObj
      have hNtfn := (hBS oid _ hObj).2.1 ntfn rfl
      rw [hNtfn.2.1]; exact .nil
    · -- AJ1-B: blockedOnReplyHasTarget (boot TCBs have ipcState = .ready)
      intro tid tcb _ _ hObj hIpc
      have hTcb := (hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl
      rw [hTcb.2.1] at hIpc; cases hIpc
  -- 4. ipcSchedulerCouplingInvariantBundle
  have hCouplingBundle : ipcSchedulerCouplingInvariantBundle
      (bootFromPlatform config).state := by
    refine ⟨⟨h1.1, hCapBundle, hIpcFull⟩, ?_, ?_, ?_⟩
    · -- ipcSchedulerCoherenceComponent (6 predicates, all vacuous: runnable = [])
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- runnableThreadIpcReady: tid ∈ runnable → ... (runnable = [])
        intro tid tcb _ hMem; rw [hRun] at hMem; simp at hMem
      · -- blockedOnSendNotRunnable
        intro tid tcb _ _ _; rw [hRun]; simp
      · -- blockedOnReceiveNotRunnable
        intro tid tcb _ _ _; rw [hRun]; simp
      · -- blockedOnCallNotRunnable
        intro tid tcb _ _ _; rw [hRun]; simp
      · -- blockedOnReplyNotRunnable
        intro tid tcb _ _ _ _; rw [hRun]; simp
      · -- blockedOnNotificationNotRunnable
        intro tid tcb _ _ _; rw [hRun]; simp
    · -- contextMatchesCurrent
      unfold contextMatchesCurrent; rw [hCur]; trivial
    · -- currentThreadDequeueCoherent (current = none → True)
      refine ⟨?_, ?_, ?_⟩
      · unfold currentThreadIpcReady; rw [hCur]; trivial
      · unfold currentNotEndpointQueueHead; rw [hCur]; trivial
      · unfold currentNotOnNotificationWaitList; rw [hCur]; trivial
  -- 6. serviceLifecycleCapabilityInvariantBundle
  have hServiceBundle : serviceLifecycleCapabilityInvariantBundle
      (bootFromPlatform config).state := by
    apply serviceLifecycleCapabilityInvariantBundle_of_components
    · -- servicePolicySurfaceInvariant (services empty → vacuous)
      intro sid svc hLookupSvc
      rw [hLookupSvcNone] at hLookupSvc; exact absurd hLookupSvc (by simp)
    · exact hLifeBundle
    · exact hCapBundle
    · -- registryInvariant (serviceRegistry empty → vacuous)
      constructor <;> {
        intro sid reg hLookup; rw [hSvcR] at hLookup
        have : (default : SystemState).serviceRegistry[sid]? = none := by
          simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
        rw [this] at hLookup; exact absurd hLookup (by simp)
      }
  -- 7. vspaceInvariantBundle (no VSpaceRoots → all vacuously true)
  have hVspaceBundle : Architecture.vspaceInvariantBundle
      (bootFromPlatform config).state := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro oid₁ _ _ _ hObj₁; exact absurd hObj₁ (hNoVSpace oid₁ _)
    · intro oid root hObj; exact absurd hObj (hNoVSpace oid _)
    · constructor
      · intro asid oid hLookup; rw [hAsid] at hLookup
        have : (default : SystemState).asidTable[asid]? = none := by
          simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
        rw [this] at hLookup; exact absurd hLookup (by simp)
      · intro oid root hObj; exact absurd hObj (hNoVSpace oid _)
    · intro oid root _ _ _ hObj; exact absurd hObj (hNoVSpace oid _)
    · intro oid root _ _ _ hObj; exact absurd hObj (hNoVSpace oid _)
    · intro oidA _ _ _ hObjA; exact absurd hObjA (hNoVSpace oidA _)
    · intro oid root _ _ _ hObj; exact absurd hObj (hNoVSpace oid _)
  -- 8. crossSubsystemInvariant (Z9-D + AE5-C + AF1-B + AM4-A: 11 predicates)
  have hCrossBundle : crossSubsystemInvariant (bootFromPlatform config).state := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- registryEndpointValid
      intro sid reg hLookup; rw [hSvcR] at hLookup
      have : (default : SystemState).serviceRegistry[sid]? = none := by
        simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
      rw [this] at hLookup; exact absurd hLookup (by simp)
    · -- AE5-C: registryInterfaceValid
      intro sid reg hLookup; rw [hSvcR] at hLookup
      have : (default : SystemState).serviceRegistry[sid]? = none := by
        simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
      rw [this] at hLookup; exact absurd hLookup (by simp)
    · -- registryDependencyConsistent
      intro sid entry hLookup; rw [hSvc] at hLookup
      have : (default : SystemState).services[sid]? = none := by
        simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
      rw [this] at hLookup; exact absurd hLookup (by simp)
    · -- noStaleEndpointQueueReferences
      intro oid ep hObj
      have hEp := (hBS oid _ hObj).1 ep rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro tid hH; rw [hEp.1] at hH; exact absurd hH (by simp)
      · intro tid hH; rw [hEp.2.1] at hH; exact absurd hH (by simp)
      · intro tid hH; rw [hEp.2.2.1] at hH; exact absurd hH (by simp)
      · intro tid hH; rw [hEp.2.2.2] at hH; exact absurd hH (by simp)
      · -- sendQ interior: head = none ⇒ collectQueueMembers returns some []
        intro members hMem tid hIn
        rw [hEp.1, collectQueueMembers_none] at hMem; cases hMem; simp at hIn
      · -- receiveQ interior: head = none ⇒ collectQueueMembers returns some []
        intro members hMem tid hIn
        rw [hEp.2.2.1, collectQueueMembers_none] at hMem; cases hMem; simp at hIn
    · -- noStaleNotificationWaitReferences
      intro oid notif hObj tid hMem
      have hNtfn := (hBS oid _ hObj).2.1 notif rfl
      rw [hNtfn.2.1] at hMem; simp at hMem
    · -- serviceGraphInvariant
      constructor
      · -- serviceDependencyAcyclic
        intro sid hPath
        cases hPath with
        | single h =>
          obtain ⟨svc, hL, _⟩ := h
          rw [hLookupSvcNone] at hL; exact absurd hL (by simp)
        | cons h _ =>
          obtain ⟨svc, hL, _⟩ := h
          rw [hLookupSvcNone] at hL; exact absurd hL (by simp)
      · -- serviceCountBounded
        refine ⟨[], ⟨List.nodup_nil, ?_, ?_⟩, ?_⟩
        · intro sid hLookup; exact absurd (hLookupSvcNone sid) hLookup
        · intro sid hMem; contradiction
        · simp [serviceBfsFuel]
    · -- Z9-A: schedContextStoreConsistent — all TCBs have .unbound binding at boot
      intro tid tcb hObj scId hBinding
      have hTcbProps := (hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl
      rw [hTcbProps.2.2.2.2.2] at hBinding
      simp [SchedContextBinding.scId?] at hBinding
    · -- Z9-B: schedContextNotDualBound — all TCBs have .unbound at boot, so no scId matches
      intro tid₁ tid₂ tcb₁ tcb₂ scId h₁ h₂ hB₁ hB₂
      have hTcb₁ := (hBS tid₁.toObjId _ h₁).2.2.2.1 tcb₁ rfl
      rw [hTcb₁.2.2.2.2.2] at hB₁
      simp [SchedContextBinding.scId?] at hB₁
    · -- Z9-C: schedContextRunQueueConsistent — empty runnable list at boot
      intro tid hMem; rw [hRun] at hMem; simp at hMem
    · -- AF1-B7: blockingAcyclic — all TCBs have ipcState = .ready at boot
      intro tid hMem
      -- blockingChain uses fuel = objectIndex.length. If fuel = 0, chain = [].
      -- If fuel > 0, use step lemma: chain = match blockingServer tid with ...
      -- All boot TCBs have .ready ipcState → blockingServer = none → chain = []
      cases hF : (bootFromPlatform config).state.objectIndex.length with
      | zero =>
        have : PriorityInheritance.blockingChain (bootFromPlatform config).state tid 0 = [] := rfl
        rw [show (bootFromPlatform config).state.objectIndex.length = 0 from hF] at hMem
        rw [this] at hMem; simp at hMem
      | succ n =>
        rw [show (bootFromPlatform config).state.objectIndex.length = n + 1 from hF] at hMem
        rw [PriorityInheritance.blockingChain_step] at hMem
        -- Show blockingServer returns none for tid at boot
        have hServer : PriorityInheritance.blockingServer (bootFromPlatform config).state tid = none := by
          cases hObj : (bootFromPlatform config).state.objects[tid.toObjId]? with
          | none => simp [PriorityInheritance.blockingServer, hObj]
          | some obj =>
            cases obj with
            | tcb tcb =>
              have hReady := (hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl |>.2.1
              simp [PriorityInheritance.blockingServer, hObj, hReady]
            | _ => simp [PriorityInheritance.blockingServer, hObj]
        simp [hServer] at hMem
    · -- AM4-F (AL6-C.hygiene): lifecycleObjectTypeLockstep at boot.
      -- `bootFromPlatform_lifecycleConsistent` already witnesses
      -- `objectTypeMetadataConsistent`, which is semantically stronger
      -- than (and directly implies) the lockstep predicate.
      intro oid obj hObj
      have hMeta := (bootFromPlatform_lifecycleConsistent config).1
      -- objectTypeMetadataConsistent: ∀ oid, lookupObjectTypeMeta st oid
      --   = (st.objects[oid]?).map KernelObject.objectType
      -- With hObj : st.objects[oid]? = some obj, the RHS is
      -- `some obj.objectType`, matching the lockstep goal.
      have := hMeta oid
      simp [SystemState.lookupObjectTypeMeta, hObj] at this
      exact this
  -- 9. tlbConsistent
  have hTlbBundle : Architecture.tlbConsistent (bootFromPlatform config).state
      (bootFromPlatform config).state.tlb := by
    rw [hTlb]; exact Architecture.tlbConsistent_empty _
  -- 10. schedulerInvariantBundleExtended (Z9-G: SchedContext invariants at boot)
  have hExtBundle : schedulerInvariantBundleExtended (bootFromPlatform config).state := by
    refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- budgetPositive: empty runnable list at boot
      intro tid hMem; rw [hRun] at hMem; simp at hMem
    · -- currentBudgetPositive: current = none at boot
      simp [currentBudgetPositive, hCur]
    · -- schedContextsWellFormed: boot-safe SchedContexts are well-formed (Z9-I)
      intro oid sc hObj
      exact ((hBS oid _ hObj).2.2.2.2.2 sc rfl).1
    · -- replenishQueueValid: default scheduler has empty queue
      simp only [replenishQueueValid, hSch]
      exact ⟨empty_sorted, empty_sizeConsistent⟩
    · -- schedContextBindingConsistent: all TCBs have .unbound at boot
      constructor
      · intro tid tcb hTcb scId hBound
        have hTcbProps := (hBS tid.toObjId _ hTcb).2.2.2.1 tcb rfl
        rw [hTcbProps.2.2.2.2.2] at hBound; cases hBound
      · intro scId sc hSc tid hBound
        -- At boot, all SchedContexts have boundThread = none (Z9-I bootSafeObject)
        have hNone := ((hBS scId.toObjId _ hSc).2.2.2.2.2 sc rfl).2
        rw [hNone] at hBound; cases hBound
    · -- effectiveParamsMatchRunQueue: empty runQueue at boot
      intro tid hMem
      have hFlat : (bootFromPlatform config).state.scheduler.runQueue.flat = [] := by
        rw [hSch]; decide
      have hInFlat := (RunQueue.mem_toList_iff_mem _ tid).mpr hMem
      simp [RunQueue.toList, hFlat] at hInFlat
    · -- boundThreadDomainConsistent: all TCBs have .unbound at boot
      intro tid scId
      show match (bootFromPlatform config).state.objects[tid.toObjId]? with
        | some (.tcb tcb) => tcb.schedContextBinding = .bound scId → _ | _ => True
      cases hLookup : (bootFromPlatform config).state.objects[tid.toObjId]? with
      | none => trivial
      | some obj =>
        cases obj with
        | tcb tcb =>
          intro hBound
          have hTcbProps := (hBS tid.toObjId _ hLookup).2.2.2.1 tcb rfl
          rw [hTcbProps.2.2.2.2.2] at hBound; cases hBound
        | _ => trivial
  -- AG7-D: notificationWaiterConsistent — boot notifications have empty waitingThreads
  have hNtfnWaiter : notificationWaiterConsistent (bootFromPlatform config).state := by
    intro oid ntfn tid hObj hMem
    have hNtfn := (hBS oid _ hObj).2.1 ntfn rfl
    rw [hNtfn.2.1] at hMem; simp at hMem
  -- Compose all 11 components
  exact ⟨h1, hCapBundle, ⟨h1.1, hCapBundle, hIpcFull⟩, hCouplingBundle,
         hLifeBundle, hServiceBundle, hVspaceBundle, hCrossBundle, hTlbBundle, hExtBundle,
         hNtfnWaiter⟩

-- ============================================================================
-- V4-A9: End-to-end bridge for general configs
-- ============================================================================

/-- V4-A9: End-to-end boot-to-runtime invariant bridge for general configs.
    Composes V4-A8 (boot → proofLayerInvariantBundle) with freeze_preserves. -/
theorem bootToRuntime_invariantBridge_general (config : PlatformConfig)
    (hSafe : config.bootSafe) :
    let ist := bootFromPlatform config
    Architecture.proofLayerInvariantBundle ist.state ∧
    SeLe4n.Model.apiInvariantBundle_frozen (SeLe4n.Model.freeze ist) :=
  ⟨bootFromPlatform_proofLayerInvariantBundle_general config hSafe,
   SeLe4n.Model.freeze_preserves_invariants _
     (bootFromPlatform_proofLayerInvariantBundle_general config hSafe)⟩

end SeLe4n.Platform.Boot
