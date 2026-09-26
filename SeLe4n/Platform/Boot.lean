-- SPDX-License-Identifier: GPL-3.0-or-later
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
-- WS-SM SM5.E: idle-thread identities (`idleThreadId` etc.) moved upstream so
-- the per-core dispatcher can reference them; the boot installers below consume
-- them.  Explicit import (also reachable transitively via `Kernel.API`).
import SeLe4n.Kernel.Scheduler.IdleThread
-- v0.35.68: the production boot's idle install IS the kernel model's enqueue —
-- `enqueueIdleThread` below runs `enqueueIdleThreadOnCore` on the intermediate
-- state's `state`, so the module holding that operation sits upstream of here.
import SeLe4n.Kernel.Scheduler.Operations.IdleEnqueue
-- WS-RC R3 (DEEP-BOOT-01): boot-VSpaceRoot threading reaches into the
-- canonical RPi5 boot root + boot-safety predicate so that
-- `bootSafeObjectCheck` can admit a well-formed boot VSpaceRoot.
-- `Platform.Contract` provides the lightweight `BootVSpaceRootEntry`
-- structure so platform bindings (RPi5, sim) can expose the optional
-- canonical boot VSpaceRoot from the typeclass.
import SeLe4n.Platform.Contract
import SeLe4n.Platform.Boot.MemoryCoverage
import SeLe4n.Platform.DeviceTree
import SeLe4n.Platform.RPi5.VSpaceBoot

/-!
# Q3-C: Boot Sequence — IntermediateState from Platform Configuration

The boot sequence constructs an `IntermediateState` from a `PlatformConfig`,
starting from `mkEmptyIntermediateState` and applying builder operations.

## Determinism

`bootFromPlatform` is a pure function: the same `PlatformConfig` always
yields the same `IntermediateState`. This is required for reproducible booting
and is guaranteed by the deterministic semantics of all builder operations.

## AN7-F (PLT-L batch) — semantic and hygiene notes

* **Last-wins semantics on duplicates** — `bootFromPlatform` uses
  `foldIrqs` / `foldObjects` with `HashMap.insert` semantics, so duplicate
  IRQ lines or ObjIds in the config see the LAST entry retained.  This is
  intentional (matches seL4's reference C kernel) but can cause silent
  data loss if the config is malformed.  Production callers MUST use
  `bootFromPlatformChecked`, which validates `PlatformConfig.wellFormed`
  (O(n) duplicate detection via `natKeysNoDup`) and returns `.error` on
  any duplicate.
* **Datasheet reference freshness** — BCM2712 constants in
  `SeLe4n/Platform/RPi5/Board.lean` are snapshotted from publicly-available
  Raspberry Pi Ltd documentation as of the v0.30.x release cut.  A CI
  hygiene check (`scripts/check_bcm2712_freshness.sh`) warns when the
  datasheet-reference marker in `Board.lean` is older than one calendar
  year.  Annual re-verification is logged in the CHANGELOG.
* **`Main.lean` no-op** — the smoke trace harness does NOT exercise the
  boot path; adding `bootFromPlatform`-related probes there is not
  expected and no such probe is present.
-/

namespace SeLe4n.Platform.Boot

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)
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

/-- **WS-RC R3 (DEEP-BOOT-01)**: Boot VSpaceRoot entry alias.

    The structure itself lives in `Platform.Contract` so platform
    bindings can expose it without pulling in the heavier
    `Platform.Boot` dependency.  This `abbrev` re-exports the type
    under the boot pipeline's namespace so existing call sites
    (`PlatformConfig.bootVSpaceRoot`, `installBootVSpaceRoot`,
    `bootFromPlatformChecked_admits_bootVSpace`) keep their existing
    naming. -/
abbrev BootVSpaceRootEntry := SeLe4n.Platform.BootVSpaceRootEntry

/-- Q3-C: Platform boot configuration — IRQ table and initial objects.

This is the minimal configuration needed to construct a valid
`IntermediateState` during boot. Platform-specific details (memory layout,
device tree, etc.) are handled by `PlatformBinding` instances. Machine
hardware parameters (PA width, register width, etc.) are configured
separately via `applyMachineConfig` after boot.

AH2-E: `machineConfig` field added so `bootFromPlatform` can automatically
apply machine configuration without requiring a separate manual call.
Defaults to `defaultMachineConfig` for backward compatibility.

WS-RC R3 (DEEP-BOOT-01): `bootVSpaceRoot` field added so platform
bindings (RPi5 in particular) can thread the canonical, W^X-compliant
boot VSpaceRoot through the boot pipeline.  Defaults to `none` to
preserve backward compatibility for empty/sim configs that exercise the
hardware-free trace harness. -/
structure PlatformConfig where
  irqTable : List IrqEntry
  initialObjects : List ObjectEntry
  machineConfig : MachineConfig := defaultMachineConfig
  bootVSpaceRoot : Option BootVSpaceRootEntry := none

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

/-- **WS-BP BP3.3**: the hash-set scan answers exactly what the transparent
    scan answers, from any starting set — the scan is `listAllDistinct` of the
    keys, and none of them already seen. -/
private theorem natKeysNoDup_go_eq (keys : List Nat) (seen : Std.HashSet Nat) :
    natKeysNoDup.go keys seen =
      (listAllDistinct keys && keys.all (fun k => !seen.contains k)) := by
  induction keys generalizing seen with
  | nil => rfl
  | cons k rest ih =>
      simp only [natKeysNoDup.go, listAllDistinct, List.all_cons]
      by_cases h : seen.contains k
      · simp [h]
      · simp only [h, Bool.false_eq_true, ↓reduceIte, ih, Std.HashSet.contains_insert]
        cases hr : rest.contains k <;> simp_all
        all_goals grind

/-- **WS-BP BP3.3**: the boot's O(n) duplicate check is the transparent O(n²)
    one.  `natKeysNoDup` is what the boot *runs*; `listAllDistinct` is what a
    kernel-evaluated proof can reduce, since `Std.HashSet` is opaque to it.  The
    equation is what lets a concrete configuration's `wellFormed` be decided by
    evaluation rather than asserted. -/
private theorem natKeysNoDup_eq_listAllDistinct (keys : List Nat) :
    natKeysNoDup keys = listAllDistinct keys := by
  rw [natKeysNoDup, natKeysNoDup_go_eq]
  simp

/-- **WS-BP BP3.3**: `irqsUnique` is its transparent variant. -/
theorem irqsUnique_eq_transparent (irqs : List IrqEntry) :
    irqsUnique irqs = irqsUniqueTransparent irqs :=
  natKeysNoDup_eq_listAllDistinct _

/-- **WS-BP BP3.3**: `objectIdsUnique` is its transparent variant. -/
theorem objectIdsUnique_eq_transparent (objs : List ObjectEntry) :
    objectIdsUnique objs = objectIdsUniqueTransparent objs :=
  natKeysNoDup_eq_listAllDistinct _

/-- Q3-C: Fold IRQ entries into the builder state.

    **U6-E (U-M12) — Duplicate IRQ semantics**: `registerIrq` uses
    `RHTable.insert` which implements last-wins on duplicate keys. If the same
    INTID appears multiple times in `irqs`, only the final handler is retained.
    Use `irqsUnique` to validate before folding if duplicate detection is
    required. -/
def foldIrqs (irqs : List IrqEntry) (ist : IntermediateState)
    : IntermediateState :=
  irqs.foldl (fun acc entry => registerIrq acc entry.irq entry.handler) ist

/-- **WS-BP BP3.2**: the `asidTable` an object's boot install leaves — the
    table with the object's ASID registered at its id when the object is a
    VSpace root, and unchanged otherwise.

    The runtime `storeObject` registers a `.vspaceRoot`'s ASID whenever it
    stores one; `Builder.createObject` does not, which is why the boot used to
    refuse every VSpace root in `initialObjects` (`noVSpaceRootsInInitialObjects`,
    retired at BP3.2).  Refusing the object was the wrong remedy for a builder
    that omitted a write: a root task needs an address space of its own, and
    the only VSpace the boot could install was the kernel's.  So every boot
    install of an object — the binding's VSpace root (`installBootVSpaceRoot`)
    and each configured object (`foldObjects`) — is `createBootObject`, and the
    boot refuses a configuration whose ASIDs collide (`bootVSpaceAsidsDistinct`),
    since an insert on a repeated key would re-point the first root's ASID at
    the second. -/
def bootEntryAsidTable (tbl : RHTable SeLe4n.ASID SeLe4n.ObjId) (entry : ObjectEntry) :
    RHTable SeLe4n.ASID SeLe4n.ObjId :=
  match entry.obj with
  | .vspaceRoot vsr => tbl.insert vsr.asid entry.id
  | _ => tbl

/-- **WS-BP BP3.5**: the ASID an entry registers — its root's, if it is a
    VSpace root.  One definition for the two places that ask: the boot's ASID
    gate (`bootVSpaceAsids`) and the proof that the table the boot builds is
    consistent with its roots, so the list the gate checks is the list the
    proof consumes. -/
def bootEntryAsid? (entry : ObjectEntry) : Option SeLe4n.ASID :=
  match entry.obj with
  | .vspaceRoot vsr => some vsr.asid
  | _ => none

/-- **WS-BP BP3.2**: the ASID registration keeps the table's extension
    invariant. -/
theorem bootEntryAsidTable_invExtK (tbl : RHTable SeLe4n.ASID SeLe4n.ObjId)
    (entry : ObjectEntry) (h : tbl.invExtK) : (bootEntryAsidTable tbl entry).invExtK := by
  unfold bootEntryAsidTable
  split
  · exact RHTable.insert_preserves_invExtK _ _ _ h
  · exact h

/-- **WS-BP BP3.2**: install one configured object — `Builder.createObject`,
    and for a VSpace root the ASID registration the runtime store performs
    (`bootEntryAsidTable`).  The one step `foldObjects` takes per entry and the
    whole of `installBootVSpaceRoot`, so every object the boot installs is
    installed the way the kernel stores one. -/
def createBootObject (ist : IntermediateState) (entry : ObjectEntry) : IntermediateState :=
  let created := createObject ist entry.id entry.obj entry.hSlots entry.hMappings
  { state := { created.state with
      asidTable := bootEntryAsidTable created.state.asidTable entry }
    hAllTables := by
      have h := created.hAllTables
      unfold SystemState.allTablesInvExtK at h ⊢
      refine ⟨h.1, h.2.1,
              bootEntryAsidTable_invExtK _ _ h.2.2.1,
              h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
              h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
              h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
              h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
              h.2.2.2.2.2.2.2.2.2.2.2.2.1,
              h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
              h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
              h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
    hPerObjectSlots := fun oid cn hLookup => created.hPerObjectSlots oid cn hLookup
    hPerObjectMappings := fun oid vs hLookup => created.hPerObjectMappings oid vs hLookup
    hLifecycleConsistent := created.hLifecycleConsistent }

/-- Q3-C: Fold initial objects into the builder state.

    **U6-F (U-M13) — Duplicate object ID semantics**: `createObject` uses
    `RHTable.insert` which implements last-wins on duplicate keys. If the same
    ObjId appears multiple times in `objs`, only the final object is retained
    and earlier objects are silently lost. Use `objectIdsUnique` to validate
    before folding to prevent silent object loss.

    **WS-BP BP3.2**: each entry is installed by `createBootObject`, so a
    configured VSpace root has its ASID registered as the runtime store would
    register it. -/
def foldObjects (objs : List ObjectEntry) (ist : IntermediateState)
    : IntermediateState :=
  objs.foldl createBootObject ist

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
      registerCount := config.registerCount
      -- PR #889 review round 20: the declared PE count travels with the rest
      -- of the machine description, so the live affinity check can read it.
      declaredCoreCount := config.declaredCoreCount } }
  hAllTables := ist.hAllTables
  hPerObjectSlots := ist.hPerObjectSlots
  hPerObjectMappings := ist.hPerObjectMappings
  hLifecycleConsistent := ist.hLifecycleConsistent

/-- AK9-F (P-M05): Gated variant of `applyMachineConfig` that validates the
    supplied `MachineConfig` BEFORE applying. Rejects configs that would
    produce an inconsistent runtime state:

    1. `MachineConfig.wellFormed` (Machine.lean) — positive region sizes,
       pairwise non-overlap, page size a positive power of two, positive
       widths, regions fitting within the PA space.
    2. `config.physicalAddressWidth ≤ 52` (ARMv8 LPA maximum).
    3. `config.pageSize` a positive power of two (subsumed by `wellFormed`
       but explicit gate makes the invariant readable at call sites).

    Returns `.error` with a descriptive message on failure. Successful
    calls agree with `applyMachineConfig` (same state construction). -/
def applyMachineConfigChecked (ist : IntermediateState) (config : MachineConfig) :
    Except String IntermediateState :=
  if !config.wellFormed then
    .error "applyMachineConfig: MachineConfig fails well-formedness (AK9-F / P-M05)"
  else if !(config.physicalAddressWidth ≤ 52) then
    .error s!"applyMachineConfig: physicalAddressWidth {config.physicalAddressWidth} > 52 (ARMv8 LPA max) (AK9-F / P-M05)"
  else
    .ok (applyMachineConfig ist config)

/-- AK9-F: Successful `applyMachineConfigChecked` agrees with unchecked. -/
theorem applyMachineConfigChecked_eq_applyMachineConfig
    (ist : IntermediateState) (config : MachineConfig)
    (hWf : config.wellFormed = true)
    (hPa : config.physicalAddressWidth ≤ 52) :
    applyMachineConfigChecked ist config = .ok (applyMachineConfig ist config) := by
  simp [applyMachineConfigChecked, hWf, hPa]

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

/-- **PR #889 review round 20**: `applyMachineConfig` sets `declaredCoreCount`
    from config — the first link in the chain that carries a binding's PE count
    into the live state the affinity transition reads. -/
theorem applyMachineConfig_declaredCoreCount (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.machine.declaredCoreCount =
    config.declaredCoreCount := rfl

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

/-- WS-SM SM7.B: `applyMachineConfig` preserves TLB-shootdown state. -/
theorem applyMachineConfig_tlbShootdown_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.tlbShootdown = ist.state.tlbShootdown := rfl

/-- WS-SM SM7.C: `applyMachineConfig` preserves the per-core TLB views. -/
theorem applyMachineConfig_perCoreTlb_eq (ist : IntermediateState) (config : MachineConfig) :
    (applyMachineConfig ist config).state.perCoreTlb = ist.state.perCoreTlb := rfl

/-- WS-SM SM7.D: `applyMachineConfig` preserves the per-core instruction
caches. -/
theorem applyMachineConfig_perCoreICache_eq (ist : IntermediateState)
    (config : MachineConfig) :
    (applyMachineConfig ist config).state.perCoreICache = ist.state.perCoreICache := rfl

/-- WS-SM SM7.D.1: `applyMachineConfig` preserves the instruction-cache
emission ledger. -/
theorem applyMachineConfig_pendingIcacheMaintenance_eq (ist : IntermediateState)
    (config : MachineConfig) :
    (applyMachineConfig ist config).state.pendingIcacheMaintenance =
      ist.state.pendingIcacheMaintenance := rfl

/-- WS-SM SM8.C.8: `applyMachineConfig` preserves the declassification audit
trail — boot configures hardware, it never declassifies. -/
theorem applyMachineConfig_declassificationAuditLog_eq (ist : IntermediateState)
    (config : MachineConfig) :
    (applyMachineConfig ist config).state.declassificationAuditLog =
      ist.state.declassificationAuditLog := rfl

/-- WS-SM SM9.A.1a: `applyMachineConfig` preserves the declassification audit
epoch — boot drains nothing, so no timestamp offset moves. -/
theorem applyMachineConfig_declassificationAuditEpoch_eq (ist : IntermediateState)
    (config : MachineConfig) :
    (applyMachineConfig ist config).state.declassificationAuditEpoch =
      ist.state.declassificationAuditEpoch := rfl

/-- WS-SM SM9.B.7: `applyMachineConfig` preserves the declassification refusal
ledger — boot issues no syscalls, so nothing is refused. -/
theorem applyMachineConfig_declassificationRefusals_eq (ist : IntermediateState)
    (config : MachineConfig) :
    (applyMachineConfig ist config).state.declassificationRefusals =
      ist.state.declassificationRefusals := rfl

/-- WS-SM SM9.D.5: `applyMachineConfig` preserves the declassification taint
side table — boot performs no declassification and moves no message, so no
object acquires provenance. -/
theorem applyMachineConfig_declassificationTaint_eq (ist : IntermediateState)
    (config : MachineConfig) :
    (applyMachineConfig ist config).state.declassificationTaint =
      ist.state.declassificationTaint := rfl

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

-- ============================================================================
-- AK9-G (P-M06): Interrupts Re-Enable Mirror (HAL Phase 3)
-- ============================================================================

/-- AK9-G (P-M06): Lean model mirror of the Rust HAL Phase-3 interrupt
    re-enable step. The HAL boot sequence
    (`sele4n-hal/src/boot.rs::rust_boot_main`) re-enables IRQs AFTER the
    GIC-400 distributor / CPU interface / timer are fully programmed. The
    Lean model's `MachineState.interruptsEnabled` default is `false` (per
    AJ3-E), matching the ARM64 reset state — so without this step the Lean
    trace would stay at `interruptsEnabled = false` indefinitely, diverging
    from the post-boot hardware state.

    This operation ONLY flips the `interruptsEnabled` flag; all other
    machine-state and IntermediateState fields are preserved. It is a pure
    function (no Kernel monad), intended to be composed in the boot
    pipeline after GIC + timer setup in the full hardware path.

    AI6-C (M-17) context: A full HAL-parity boot sequence additionally
    issues TLB/ASID maintenance — recorded here as a post-1.0 hardening
    candidate; registered in `docs/REGISTERED_DEBT.md`
    (Registered debt index, C.1). This step (AK9-G)
    closes the smaller, isolable divergence identified by P-M06. -/
def bootEnableInterruptsOp (ist : IntermediateState) : IntermediateState where
  state := { ist.state with
    machine := enableInterrupts ist.state.machine }
  hAllTables := ist.hAllTables
  hPerObjectSlots := ist.hPerObjectSlots
  hPerObjectMappings := ist.hPerObjectMappings
  hLifecycleConsistent := ist.hLifecycleConsistent

/-- AK9-G: After `bootEnableInterruptsOp`, the machine reports IRQs enabled. -/
theorem bootEnableInterruptsOp_interruptsEnabled (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.machine.interruptsEnabled = true := rfl

/-- AK9-G: `bootEnableInterruptsOp` only modifies `interruptsEnabled`. -/
theorem bootEnableInterruptsOp_machine_frame (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.machine.regs = ist.state.machine.regs ∧
    (bootEnableInterruptsOp ist).state.machine.memory = ist.state.machine.memory ∧
    (bootEnableInterruptsOp ist).state.machine.timer = ist.state.machine.timer ∧
    (bootEnableInterruptsOp ist).state.machine.systemRegisters =
      ist.state.machine.systemRegisters :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- AK9-G: `bootEnableInterruptsOp` preserves non-machine state. -/
theorem bootEnableInterruptsOp_objects_eq (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.objects = ist.state.objects := rfl

/-- AK9-G: `bootEnableInterruptsOp` preserves scheduler. -/
theorem bootEnableInterruptsOp_scheduler_eq (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.scheduler = ist.state.scheduler := rfl

/-- AK9-G: `bootEnableInterruptsOp` preserves the lifecycle metadata. -/
theorem bootEnableInterruptsOp_lifecycle_eq (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.lifecycle = ist.state.lifecycle := rfl

/-- AK9-G: `bootEnableInterruptsOp` preserves the IRQ handler table. -/
theorem bootEnableInterruptsOp_irqHandlers_eq (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.irqHandlers = ist.state.irqHandlers := rfl

/-- AK9-G: `bootEnableInterruptsOp` preserves the service registry. -/
theorem bootEnableInterruptsOp_serviceRegistry_eq (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.serviceRegistry = ist.state.serviceRegistry := rfl

/-- AK9-G: `bootEnableInterruptsOp` preserves the ASID table. -/
theorem bootEnableInterruptsOp_asidTable_eq (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.asidTable = ist.state.asidTable := rfl

/-- AK9-G: `bootEnableInterruptsOp` preserves the TLB shadow. -/
theorem bootEnableInterruptsOp_tlb_eq (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.tlb = ist.state.tlb := rfl

/-- AK9-G: `bootEnableInterruptsOp` preserves the object index. -/
theorem bootEnableInterruptsOp_objectIndex_eq (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.objectIndex = ist.state.objectIndex := rfl

/-- AK9-G: `bootEnableInterruptsOp` preserves machine.physicalAddressWidth. -/
theorem bootEnableInterruptsOp_physicalAddressWidth_eq (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.machine.physicalAddressWidth =
      ist.state.machine.physicalAddressWidth := rfl

/-- **PR #889 review round 20**: `bootEnableInterruptsOp` preserves the declared
    PE count — it writes `interruptsEnabled` and nothing else. -/
theorem bootEnableInterruptsOp_declaredCoreCount_eq (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.machine.declaredCoreCount =
      ist.state.machine.declaredCoreCount := rfl

/-- AK9-G: `bootEnableInterruptsOp` preserves machine.memoryMap. -/
theorem bootEnableInterruptsOp_memoryMap_eq (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.machine.memoryMap =
      ist.state.machine.memoryMap := rfl

-- ============================================================================
-- WS-RC R3 (DEEP-BOOT-01) — installBootVSpaceRoot builder operation
-- ============================================================================

/-- **WS-RC R3 (DEEP-BOOT-01)**: Install a boot VSpaceRoot into the
    builder state.

    Composes `Builder.createObject` (object-store insertion + lifecycle
    metadata bookkeeping + objectIndex maintenance) with an `asidTable`
    update that registers the VSpaceRoot's ASID, mirroring the runtime
    `storeObject` semantics for VSpaceRoot inserts.  Without the
    `asidTable` update, downstream VSpace operations
    (`resolveAsidRoot`, etc.) would fail to find the boot root by ASID.

    **Precondition** — `vsr.mappings.invExt` (Robin Hood load-factor +
    key-uniqueness invariants on the page-mapping table).  This is
    guaranteed by every well-formed boot root because boot roots are
    constructed via sequential `RHTable.insert` operations starting
    from `RHTable.empty`, which preserve `invExt` at every step.

    The four `IntermediateState` invariant witnesses thread through
    cleanly: `hAllTables` is updated by composing the existing
    `createObject` proof with `RHTable.insert_preserves_invExtK` for
    the new `asidTable` entry; `hPerObjectSlots`, `hPerObjectMappings`,
    and `hLifecycleConsistent` carry over because the `asidTable`
    update only touches a field that none of these invariants
    quantify over. -/
def installBootVSpaceRoot (ist : IntermediateState)
    (id : SeLe4n.ObjId) (vsr : VSpaceRoot)
    (hMappings : vsr.mappings.invExt)
    : IntermediateState :=
  createBootObject ist
    { id := id, obj := KernelObject.vspaceRoot vsr
      hSlots := fun _ hEq => by cases hEq
      hMappings := fun vs hEq => by cases hEq; exact hMappings }

/-- **WS-RC R3**: `installBootVSpaceRoot` registers `vsr` in the object
    store at `id`.  Witnesses the post-state object-store entry for
    downstream lookup proofs (e.g., the `bootFromPlatformChecked`
    regression test in `TwoPhaseArchSuite`). -/
theorem installBootVSpaceRoot_objects_lookup
    (ist : IntermediateState) (id : SeLe4n.ObjId) (vsr : VSpaceRoot)
    (hMappings : vsr.mappings.invExt) :
    (installBootVSpaceRoot ist id vsr hMappings).state.objects[id]? =
      some (KernelObject.vspaceRoot vsr) := by
  -- After `createObject`, the object store has `id ↦ KernelObject.vspaceRoot vsr`.
  -- The asidTable update does not touch `objects`, so the post-state
  -- objects table is `ist.state.objects.insert id (KernelObject.vspaceRoot vsr)`.
  show (ist.state.objects.insert id (KernelObject.vspaceRoot vsr))[id]? =
    some (KernelObject.vspaceRoot vsr)
  have hObjK : ist.state.objects.invExtK := ist.hAllTables.1
  exact RHTable.getElem?_insert_self ist.state.objects id _ hObjK.1

/-- **WS-RR RR5.13** (PR #889 review): `installBootVSpaceRoot` frames every
    *other* object-store slot — the companion of `installBootVSpaceRoot_objects_lookup`
    that the idle-slot freshness and thread-state proofs walk through. -/
theorem installBootVSpaceRoot_objects_ne
    (ist : IntermediateState) (id : SeLe4n.ObjId) (vsr : VSpaceRoot)
    (hMappings : vsr.mappings.invExt) (oid : SeLe4n.ObjId) (h : id ≠ oid) :
    (installBootVSpaceRoot ist id vsr hMappings).state.objects[oid]? =
      ist.state.objects[oid]? := by
  show (ist.state.objects.insert id (KernelObject.vspaceRoot vsr))[oid]? = _
  have hObjK : ist.state.objects.invExtK := ist.hAllTables.1
  have hNe : ¬((id == oid) = true) := fun heq => h (eq_of_beq heq)
  exact RHTable.getElem?_insert_ne ist.state.objects id oid _ hNe hObjK.1

/-- **WS-RC R3**: `installBootVSpaceRoot` registers the VSpaceRoot's
    ASID in `asidTable` at the boot root's ObjId.  Witnesses the
    post-state ASID resolution path. -/
theorem installBootVSpaceRoot_asidTable_lookup
    (ist : IntermediateState) (id : SeLe4n.ObjId) (vsr : VSpaceRoot)
    (hMappings : vsr.mappings.invExt) :
    (installBootVSpaceRoot ist id vsr hMappings).state.asidTable[vsr.asid]? =
      some id := by
  -- The asidTable was previously unchanged by `createObject`, so the
  -- post-state asidTable is `ist.state.asidTable.insert vsr.asid id`.
  show (ist.state.asidTable.insert vsr.asid id)[vsr.asid]? = some id
  have hAsidK : ist.state.asidTable.invExtK := ist.hAllTables.2.2.1
  exact RHTable.getElem?_insert_self _ vsr.asid id hAsidK.1

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
valid scheduler state) is recorded as a post-1.0 hardening candidate;
registered in `docs/REGISTERED_DEBT.md` (Registered debt index, C.1).

WS-RC R3 (DEEP-BOOT-01): The unchecked path deliberately does NOT
install `config.bootVSpaceRoot`.  Boot VSpaceRoot threading is
performed only by `bootFromPlatformChecked`, which composes the
unchecked fold with `installBootVSpaceRoot` after gate validation.
This split keeps all pre-R3 invariant-bridge proofs about
`bootFromPlatform` intact (they assume no VSpaceRoots in the
post-state) and concentrates the new boot-VSpace machinery in the
gated boot path.  See `bootFromPlatformChecked_eq_bootFromPlatform`
(when `bootVSpaceRoot = none`) and
`bootFromPlatformChecked_admits_bootVSpace` (when
`bootVSpaceRoot = some _`) for the bridging theorems. -/
def bootFromPlatform (config : PlatformConfig) : IntermediateState :=
  let initial := mkEmptyIntermediateState
  let withIrqs := foldIrqs config.irqTable initial
  let withObjects := foldObjects config.initialObjects withIrqs
  -- AH2-F: Integrate machine config into boot pipeline to prevent
  -- PA width misconfiguration (M-03/L-16). Previously callers had to
  -- manually chain `applyMachineConfig` after boot.
  applyMachineConfig withObjects config.machineConfig

/-- V5-C/W4-E (M-DEF-3/L-15) + AN7-D.1 (PLT-M01): **Deprecated** — use
    `bootFromPlatformChecked` for production boot paths. This function
    silently uses last-wins semantics on duplicate IRQs or object IDs,
    which can cause silent data loss if the same ObjId appears multiple
    times in the platform configuration.

    `bootFromPlatformChecked` validates `PlatformConfig.wellFormed` and
    returns an explicit error on duplicates, preventing silent overwrites.

    **Retained for**: backward compatibility with legacy test code exercising
    invalid-state scenarios.  The canonical test-path alias now lives at
    `SeLe4n.Testing.Deprecated.bootFromPlatformUnchecked` — new test code
    MUST use that namespaced form so the `@[deprecated]` attribute below
    does not leak deprecation warnings into production call sites that
    only reference `bootFromPlatform` / `bootFromPlatformChecked`. -/
@[deprecated "AN7-D.1 (PLT-M01): use bootFromPlatformChecked for production paths. Test code that needs the unchecked form must import SeLe4n.Testing.Deprecated.bootFromPlatformUnchecked, which makes the test-only intent explicit." (since := "0.30.8")]
abbrev bootFromPlatformUnchecked := bootFromPlatform

/-- AK9-G (P-M06): Full HAL-parity boot — `bootFromPlatform` followed by the
    `bootEnableInterruptsOp` step that mirrors the Rust HAL Phase-3 IRQ
    re-enable after GIC + timer initialization. The result has
    `interruptsEnabled = true`, matching the post-boot hardware state.

    The pre-interrupts boot continues to be available via `bootFromPlatform`
    for contexts (negative-state tests, boot-invariant bridge proofs) that
    specifically need the reset-state `interruptsEnabled = false`. -/
def bootFromPlatformWithInterrupts (config : PlatformConfig) : IntermediateState :=
  bootEnableInterruptsOp (bootFromPlatform config)

/-- AK9-G: Full HAL-parity boot produces an IntermediateState with interrupts
    enabled, matching the post-boot Rust HAL state. -/
theorem bootFromPlatformWithInterrupts_interruptsEnabled (config : PlatformConfig) :
    (bootFromPlatformWithInterrupts config).state.machine.interruptsEnabled = true := rfl

/-- AK9-G: Non-machine state of `bootFromPlatformWithInterrupts` matches
    `bootFromPlatform` (the interrupts step only flips the machine flag). -/
theorem bootFromPlatformWithInterrupts_objects_eq (config : PlatformConfig) :
    (bootFromPlatformWithInterrupts config).state.objects =
    (bootFromPlatform config).state.objects := rfl

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
theorem bootFromPlatform_objectTypeMetadataConsistent (config : PlatformConfig) :
    SystemState.objectTypeMetadataConsistent (bootFromPlatform config).state :=
  (bootFromPlatform config).hLifecycleConsistent

/-- Q3-C: Master validity theorem — boot produces a fully valid state. -/
theorem bootFromPlatform_valid (config : PlatformConfig) :
    let ist := bootFromPlatform config
    ist.state.allTablesInvExtK ∧
    perObjectSlotsInvariant ist.state ∧
    perObjectMappingsInvariant ist.state ∧
    SystemState.objectTypeMetadataConsistent ist.state :=
  ⟨bootFromPlatform_allTablesInvExtK config,
   bootFromPlatform_perObjectSlots config,
   bootFromPlatform_perObjectMappings config,
   bootFromPlatform_objectTypeMetadataConsistent config⟩

/-- U6-E: Empty IRQ list has no duplicates. -/
theorem irqsUnique_empty : irqsUnique [] = true := by
  decide

/-- U6-F: Empty object list has no duplicates. -/
theorem objectIdsUnique_empty : objectIdsUnique [] = true := by
  decide

/-- PR #889 review round 8: the fields of a boot **endpoint** that can hold a
    thread id — the two intrusive queues' heads and tails.  Destructured by the
    constructor so that a new `Endpoint` field fails this definition and has to
    be classified. -/
def endpointReferencesReservedIdleSlot (ep : Endpoint) : Bool :=
  match ep with
  | ⟨sendQ, receiveQ, _lock⟩ =>
    sendQ.head.any SeLe4n.Kernel.isIdleThreadId ||
    sendQ.tail.any SeLe4n.Kernel.isIdleThreadId ||
    receiveQ.head.any SeLe4n.Kernel.isIdleThreadId ||
    receiveQ.tail.any SeLe4n.Kernel.isIdleThreadId

/-- PR #889 review round 8: a boot **notification**'s waiters and (round 4) its
    bound TCB — a boot notification pre-bound to an idle thread would be
    materialised into a one-sided binding: the idle TCB comes up with
    `boundNotification = none`, a later bind fails on the notification side,
    and no capability can reach the idle TCB to clear it. -/
def notificationReferencesReservedIdleSlot (notif : Notification) : Bool :=
  match notif with
  | ⟨_state, waitingThreads, _pendingBadge, boundTCB, _lock⟩ =>
    !waitingThreads.all (fun t => !SeLe4n.Kernel.isIdleThreadId t) ||
    boundTCB.any SeLe4n.Kernel.isIdleThreadId

/-- PR #889 review round 8: a boot **CNode**'s capabilities, by their targets
    (`capTargetsReservedIdleObject`). -/
def cnodeReferencesReservedIdleSlot (cn : CNode) : Bool :=
  match cn with
  | ⟨_depth, _guardWidth, _guardValue, _radixWidth, slots, _lock⟩ =>
    slots.toList.any (fun s => SeLe4n.Kernel.capTargetsReservedIdleObject s.2)

/-- PR #889 review round 8: every field of a boot **TCB** that can hold an
    object, thread, scheduling-context or reply id, classified one by one.

    The constructor pattern is the pin: the TCB arm was extended in review
    rounds 2, 4, 7 and 8 — the queue links, the SchedContext references and
    the donation owner, the TCB's own `tid`, and then `queuePPrev`, whose
    `.tcbNext` payload is a thread id the projection-based arm never read —
    because a hand-written field list cannot see the field it omits.  Adding
    a field to `TCB` now fails this definition with an arity error, and the
    author says where the new field stands.  What each field holds:

    * `tid` (round 7) — the TCB's own identity, which `cleanupTcbReferences`
      reads back; `cspaceRoot`, `vspaceRoot`, `boundNotification` — object
      ids; `queuePrev`, `queueNext` and `queuePPrev`'s `.tcbNext` — thread
      ids (a stale `queuePPrev` also makes `endpointQueueEnqueue` refuse the
      otherwise detached thread with `.illegalState`, so the boot-safety
      check requires all three links empty); `pendingMessage` — carried
      capabilities, by their targets; `schedContextBinding`,
      `timeoutBudget` — SchedContext ids and the donation owner;
      `replyObject`, `pendingReceiveReply` — reply object ids.
    * `priority`, `domain`, `ipcBuffer` (a virtual address), `ipcState`,
      `threadState`, `timeSlice`, `deadline`, `registerContext`,
      `faultHandler` (a CPtr into the thread's own CSpace, not an id),
      `maxControlledPriority`, `pipBoost`, `timedOut`, `lock`,
      `cpuAffinity` (a core) and `pendingFault` (addresses, syndromes and a
      register window) hold no id. -/
def tcbReferencesReservedIdleSlot (tcb : TCB) : Bool :=
  match tcb with
  | ⟨tid, _priority, _domain, cspaceRoot, vspaceRoot, _ipcBuffer, _ipcState, _threadState,
     _timeSlice, _deadline, queuePrev, queuePPrev, queueNext, pendingMessage, _registerContext,
     _faultHandler, boundNotification, schedContextBinding, timeoutBudget,
     _maxControlledPriority, _pipBoost, _timedOut, _lock, _cpuAffinity, replyObject,
     pendingReceiveReply, _pendingFault⟩ =>
    SeLe4n.Kernel.isIdleThreadId tid ||
    SeLe4n.Kernel.isIdleObjId cspaceRoot || SeLe4n.Kernel.isIdleObjId vspaceRoot ||
    boundNotification.any SeLe4n.Kernel.isIdleObjId ||
    queueNext.any SeLe4n.Kernel.isIdleThreadId ||
    queuePrev.any SeLe4n.Kernel.isIdleThreadId ||
    (match queuePPrev with
     | some (.tcbNext prev) => SeLe4n.Kernel.isIdleThreadId prev
     | _ => false) ||
    pendingMessage.any (fun msg =>
      msg.caps.any (fun tc => SeLe4n.Kernel.capTargetsReservedIdleObject tc.cap)) ||
    timeoutBudget.any (fun sc => SeLe4n.Kernel.isIdleObjId sc.toObjId) ||
    (match schedContextBinding with
     | .unbound => false
     | .bound scId => SeLe4n.Kernel.isIdleObjId scId.toObjId
     | .donated scId owner =>
       SeLe4n.Kernel.isIdleObjId scId.toObjId || SeLe4n.Kernel.isIdleThreadId owner) ||
    replyObject.any (fun rid => SeLe4n.Kernel.isIdleObjId rid.toObjId) ||
    pendingReceiveReply.any (fun rid => SeLe4n.Kernel.isIdleObjId rid.toObjId)

/-- PR #889 review round 8: the TCB reference check in projection form —
    the same Boolean, read off the fields rather than the constructor.  Proved
    by `rfl` (structure eta), so proofs can rewrite with it cheaply: Lean's
    equation lemmas for a 27-field constructor match are expensive to
    generate, and `simp only [tcbReferencesReservedIdleSlot]` timed out where
    this rewrite does not. -/
theorem tcbReferencesReservedIdleSlot_def (tcb : TCB) :
    tcbReferencesReservedIdleSlot tcb =
      (SeLe4n.Kernel.isIdleThreadId tcb.tid ||
       SeLe4n.Kernel.isIdleObjId tcb.cspaceRoot || SeLe4n.Kernel.isIdleObjId tcb.vspaceRoot ||
       tcb.boundNotification.any SeLe4n.Kernel.isIdleObjId ||
       tcb.queueNext.any SeLe4n.Kernel.isIdleThreadId ||
       tcb.queuePrev.any SeLe4n.Kernel.isIdleThreadId ||
       (match tcb.queuePPrev with
        | some (.tcbNext prev) => SeLe4n.Kernel.isIdleThreadId prev
        | _ => false) ||
       tcb.pendingMessage.any (fun msg =>
         msg.caps.any (fun tc => SeLe4n.Kernel.capTargetsReservedIdleObject tc.cap)) ||
       tcb.timeoutBudget.any (fun sc => SeLe4n.Kernel.isIdleObjId sc.toObjId) ||
       (match tcb.schedContextBinding with
        | .unbound => false
        | .bound scId => SeLe4n.Kernel.isIdleObjId scId.toObjId
        | .donated scId owner =>
          SeLe4n.Kernel.isIdleObjId scId.toObjId || SeLe4n.Kernel.isIdleThreadId owner) ||
       tcb.replyObject.any (fun rid => SeLe4n.Kernel.isIdleObjId rid.toObjId) ||
       tcb.pendingReceiveReply.any (fun rid => SeLe4n.Kernel.isIdleObjId rid.toObjId)) :=
  rfl

/-- PR #889 review round 8: a **VSpace root** — an ASID, a virtual-to-physical
    map and a lock — holds no object, thread or scheduling-context id.  The
    answer is by inspection of the constructor's fields, and the pattern fails
    when a field is added. -/
def vspaceRootReferencesReservedIdleSlot (vsr : VSpaceRoot) : Bool :=
  match vsr with
  | ⟨_asid, _mappings, _lock⟩ => false

/-- **WS-BP BP7.1**: a **frame** — a physical address, a memory kind and a lock —
    holds no object, thread or scheduling-context id.  By inspection of the
    constructor's fields, pinned by arity like the VSpace root above. -/
def frameReferencesReservedIdleSlot (f : FrameObject) : Bool :=
  match f with
  | ⟨_base, _isDevice, _lock⟩ => false

/-- PR #889 review round 8 (the round-6 check, pinned by arity): a boot
    **untyped** whose allocation record names an idle slot as a child, or whose
    ancestry names one as its parent, would keep user-supplied metadata about
    an object the idle fold materialises — the retype and revoke paths read
    both. -/
def untypedReferencesReservedIdleSlot (ut : UntypedObject) : Bool :=
  match ut with
  | ⟨_regionBase, _regionSize, _watermark, children, _isDevice, parent, _lock⟩ =>
    children.any (fun child => SeLe4n.Kernel.isIdleObjId child.objId) ||
    parent.any SeLe4n.Kernel.isIdleObjId

/-- PR #889 review round 8: a boot **SchedContext**'s own id (`scId`, which
    `replenishScOnCore` keys the replenishment queue by), its bound thread and
    — since WS-OD OD2.1 — its reply-stack head (`scReply`, a Reply object id).
    Budgets, periods, priorities and replenishment entries hold no id. -/
def schedContextReferencesReservedIdleSlot (sc : SchedContext) : Bool :=
  match sc with
  | ⟨scId, _budget, _period, _priority, _deadline, _domain, _budgetRemaining, _periodStart,
     _replenishments, boundThread, scReply, donationOrigin, _isActive, _lock⟩ =>
    SeLe4n.Kernel.isIdleObjId scId.toObjId ||
    boundThread.any SeLe4n.Kernel.isIdleThreadId ||
    scReply.any (fun rid => SeLe4n.Kernel.isIdleObjId rid.toObjId) ||
    -- **WS-HP HP10.3**: and the recorded reservation origin, which is a
    -- `ThreadId` and so can name a reserved idle thread exactly as `boundThread`
    -- can.  Classified here because the constructor destructuring above refused
    -- to elaborate until it was -- the PR #889 round-8 pin doing its job.
    donationOrigin.any SeLe4n.Kernel.isIdleThreadId

/-- PR #889 review round 8: a boot **Reply**'s own id, its blocked caller and its
    two reply-stack links — `prev` (a reply object id the round-6 arm did not
    read) and, since WS-OD `v0.35.4`, `next`, which names either the frame above
    (a reply object id) or the scheduling context this frame heads. -/
def replyReferencesReservedIdleSlot (r : Reply) : Bool :=
  match r with
  | ⟨replyId, caller, prev, next, _lock⟩ =>
    SeLe4n.Kernel.isIdleObjId replyId.toObjId ||
    caller.any SeLe4n.Kernel.isIdleThreadId ||
    prev.any (fun p => SeLe4n.Kernel.isIdleObjId p.toObjId) ||
    next.any (fun
      | .frame above => SeLe4n.Kernel.isIdleObjId above.toObjId
      | .head sc => SeLe4n.Kernel.isIdleObjId sc.toObjId)

/-- PR #889 review round 2: does a boot object **reference** a reserved idle
    slot?  A config entry at an ordinary id can still name an idle thread in
    a queue link, a capability, a binding or a donation record, and the
    checked boot would then materialise an idle thread already reachable
    from user-supplied state — a `.tcbSuspend` through a boot CNode's
    capability, or a stale queue link, would remove the thread the no-stall
    guarantee rests on before the first instruction runs.  The reservation
    therefore refuses references as well as occupancy.

    Total over `KernelObject`, so a new kind must say where it stands — and,
    since review round 8, total over every kind's **fields** as well: each
    arm delegates to a per-kind helper that destructures the constructor, so
    a field added to any kernel object fails the helper with an arity error
    rather than defaulting to "unread".  The round-8 finding was exactly that
    default: `queuePPrev`'s `.tcbNext` payload is a thread id, and a TCB arm
    listing fields by hand had never named it (rounds 2, 4, 6 and 7 each
    extended the same list).  The sweep that pinned the arity also found the
    id-carrying fields the list still omitted — a reply's `prev` link, the
    two reply references and the carried capabilities of a TCB, and the own
    ids of a SchedContext and a Reply. -/
def bootObjectReferencesReservedIdleSlot (obj : KernelObject) : Bool :=
  match obj with
  | .endpoint ep => endpointReferencesReservedIdleSlot ep
  | .notification notif => notificationReferencesReservedIdleSlot notif
  | .cnode cn => cnodeReferencesReservedIdleSlot cn
  | .tcb tcb => tcbReferencesReservedIdleSlot tcb
  | .vspaceRoot vsr => vspaceRootReferencesReservedIdleSlot vsr
  | .untyped ut => untypedReferencesReservedIdleSlot ut
  | .schedContext sc => schedContextReferencesReservedIdleSlot sc
  | .reply r => replyReferencesReservedIdleSlot r
  | .frame f => frameReferencesReservedIdleSlot f

/-- **WS-RR RR5.13** (PR #889 review): the per-core idle object slots
    `[idleThreadIdBase, idleThreadIdBase + numCores)` are **reserved** — no
    `initialObjects` entry and no boot VSpace root may occupy one, and (review
    round 2) no `initialObjects` entry may *reference* one
    (`bootObjectReferencesReservedIdleSlot`).  A config that fails this is
    refused with its own diagnostic (`bootFromPlatformChecked`), not as a
    duplicate object id.

    The production boot (`bootFromPlatformCheckedWithIdleThreads`) installs an
    idle TCB at every one of those slots through the kernel model's own enqueue
    (`enqueueIdleThreadOnCore`, a store), whose insert *overwrites* on key
    collision.  Without this check an otherwise valid
    config that placed an object there was accepted by the checked boot and then
    silently lost that object to the idle fold — the preservation theorem
    (`bootFromPlatformCheckedWithIdleThreads_preserves_platform_objects`) was
    true only under an `idleSlotsFreshAt` hypothesis nothing on the live path
    discharged.  Folded into `PlatformConfig.wellFormed` so it is decided on the
    one validation path every boot entry shares, and so a successful checked
    boot *implies* the freshness that theorem needs
    (`bootFromPlatformChecked_ok_idleSlotsFreshAt`).

    **The reservation is model-wide, not binding-wide** (PR #889 review round
    5).  It covers `[idleThreadIdBase, idleThreadIdBase + numCores)` for the
    model's `numCores`, not for the `coreCount` a binding declares, although
    the checked platform boot installs idle threads on the declared cores only
    (`bootFromPlatformCheckedWithIdleThreadsFor`).  The ids belong to the
    **model**: every per-core structure is `numCores` wide whatever a binding
    declares, the per-core dispatcher names `idleThreadId c` for every model
    core, and `syscallResolveCap` decides the reservation on the kernel state
    alone — which carries no binding, so a chokepoint parameterised by the
    declared cores would answer from state the kernel does not have.  Leaving
    an undeclared core's slot open would make it the one model core whose idle
    id could resolve to a config object: usable through a capability, and
    dispatchable by a core that is never brought up.  The cost is three object
    ids out of a 64-bit space on a single-core binding.  An undeclared core's
    slot is therefore *absent* after the declared-cores boot, never free
    (`bootFromPlatformCheckedWithIdleThreadsFor_undeclared_idle_absent`). -/
def idleSlotsReserved (config : PlatformConfig) : Bool :=
  config.initialObjects.all (fun entry =>
    !isIdleObjId entry.id && !bootObjectReferencesReservedIdleSlot entry.obj) &&
  (match config.bootVSpaceRoot with
   | none => true
   | some entry => !isIdleObjId entry.id)

/-- PR #889 review round 7: every boot TCB's **embedded identity is its own
    slot** — `tcb.tid.toObjId = entry.id` for every `.tcb` entry.

    A `TCB` carries its `ThreadId`, and the object store is keyed by `ObjId`;
    `getTcb? tid` reads `objects[tid.toObjId]`, and the lifecycle paths that
    take a TCB *object* read its `tid` back to find it in the queues
    (`cleanupTcbReferences`).  Nothing at boot related the two: a config could
    store, at ordinary id `9`, a TCB whose `tid` was `idleThreadId 0`, and a
    later retype of object `9` would dequeue idle `0` — the no-stall guarantee
    defeated through a field no reservation read, and no capability to the idle
    object needed.  Requiring the identity to be the slot is the relation
    itself, not the idle instance of it: with it, a TCB's `tid` names an object
    the config placed at that id, so every id-keyed lookup and every
    tid-keyed walk agree on which thread a boot TCB is.  The idle case follows
    (`idleSlotsReserved_no_idle_tid`), and the reference check reads `tid`
    directly as well, so the two refusals name different faults. -/
def tcbIdentitiesMatchSlots (config : PlatformConfig) : Bool :=
  config.initialObjects.all (fun entry =>
    match entry.obj with
    | .tcb tcb => tcb.tid.toObjId == entry.id
    | _ => true)

/-- PR #889 review round 8 (the round-7 relation, swept across the kinds that
    carry their own id): every boot **SchedContext** is stored under its own
    `scId` — `replenishScOnCore` keys the per-core replenishment queue by
    `sc.scId`, and `getSchedContext?` resolves that key to
    `objects[scId.toObjId]`, so a SchedContext at slot `9` carrying
    `scId = 12` would have its budget replenished on whatever object `12`
    is. -/
def schedContextIdentitiesMatchSlots (config : PlatformConfig) : Bool :=
  config.initialObjects.all (fun entry =>
    match entry.obj with
    | .schedContext sc => sc.scId.toObjId == entry.id
    | _ => true)

/-- PR #889 review round 8: every boot **Reply** is stored under its own
    `replyId` — the sentinel `replyId` marks `Reply.empty` for the observer
    projection, and a reply's identity is the slot the reply capability
    names. -/
def replyIdentitiesMatchSlots (config : PlatformConfig) : Bool :=
  config.initialObjects.all (fun entry =>
    match entry.obj with
    | .reply r => r.replyId.toObjId == entry.id
    | _ => true)

/-- PR #889 review round 8: the fourth `wellFormed` conjunct — every object
    that carries its own id is stored under it.  Round 7 stated it for TCBs;
    a SchedContext and a Reply carry theirs too, and each is read back by a
    live path (`replenishScOnCore` keys by `scId`; the observer projection
    classifies a Reply by `replyId`). -/
def embeddedIdentitiesMatchSlots (config : PlatformConfig) : Bool :=
  tcbIdentitiesMatchSlots config && schedContextIdentitiesMatchSlots config &&
    replyIdentitiesMatchSlots config

/-- **`v0.35.187`**: per entry, the three per-kind checks together are the shared
question — each is that question restricted to one kind and vacuous on the
others. -/
private theorem entryIdentity_iff (entry : ObjectEntry) :
    entry.obj.embeddedIdentityMatches entry.id = true ↔
      (((match entry.obj with | .tcb t => t.tid.toObjId == entry.id | _ => true) = true) ∧
       ((match entry.obj with
         | .schedContext sc => sc.scId.toObjId == entry.id | _ => true) = true) ∧
       ((match entry.obj with
         | .reply r => r.replyId.toObjId == entry.id | _ => true) = true)) := by
  cases entry.obj <;> simp [KernelObject.embeddedIdentityMatches]

/-- **`v0.35.187`: the boot check and the retype guard ask ONE question.**

`KernelObject.embeddedIdentityMatches` is that question — *is this object's own
embedded identity the key it is stored at* — and it is what
`retypeReplacementAdmissible` reads at the runtime.  This theorem says the
boot's three-way conjunction above is the same predicate, applied per entry.

Stated rather than substituted into the definitions: the three per-kind checks
have their own consumers and their own place in `wellFormedConjuncts`'s
diagnostic, so collapsing them would rename a boot fault.  What matters is that
the two artefacts cannot drift about *what the question is*, and a theorem says
that where a shared spelling would only suggest it. -/
theorem embeddedIdentitiesMatchSlots_iff (config : PlatformConfig) :
    embeddedIdentitiesMatchSlots config = true ↔
      ∀ entry ∈ config.initialObjects,
        entry.obj.embeddedIdentityMatches entry.id = true := by
  simp only [embeddedIdentitiesMatchSlots, tcbIdentitiesMatchSlots,
    schedContextIdentitiesMatchSlots, replyIdentitiesMatchSlots,
    Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨hT, hS⟩, hR⟩ entry hMem
    exact (entryIdentity_iff entry).mpr ⟨hT entry hMem, hS entry hMem, hR entry hMem⟩
  · intro h
    exact ⟨⟨fun e hM => ((entryIdentity_iff e).mp (h e hM)).1,
            fun e hM => ((entryIdentity_iff e).mp (h e hM)).2.1⟩,
           fun e hM => ((entryIdentity_iff e).mp (h e hM)).2.2⟩

/-- PR #889 review round 18: the fifth `wellFormed` conjunct — the config
    leaves room for everything a successful boot installs beyond it.

    A boot state holds one object per `initialObjects` entry, at most one boot
    VSpace root, and — since WS-RR RR5.13 — one idle TCB per core.  Nothing
    bounded that: a config with 65 533 objects and a boot root satisfies every
    other conjunct, boots, and the idle fold takes the object index to 65 537,
    past `maxObjects` — so a *successful production boot* produced a state
    violating `objectIndexBounded`, the invariant `retypeFromUntyped` enforces
    at every later allocation.  The headroom is `numCores`, not the binding's
    `coreCount`: the idle slots are reserved model-wide, so the budget must
    hold for any binding this config could boot on. -/
def objectBudgetRespected (config : PlatformConfig) : Bool :=
  config.initialObjects.length + 1 + SeLe4n.Kernel.Concurrency.numCores ≤ maxObjects

/-- PR #889 review round 19: the object budget's own boot diagnostic.  Round 18
    added the conjunct without a branch in `bootFromPlatformChecked`'s error
    cascade, so a config whose only fault was its *size* fell through to the
    embedded-identity message — naming a fault it does not have.  A plain
    literal rather than an interpolation: the cascade's arms are scrutinised by
    `split` in the downstream `_ok_` results, and a `toString` application there
    defeats the dependent elimination. -/
def objectBudgetBootError : String :=
  "boot: platform config leaves no object-index room for the boot VSpace root and the " ++
    "per-core idle threads (initialObjects + 1 + numCores must not exceed maxObjects) " ++
    "(PR #889 review rounds 18 and 19)"

/-- The first `wellFormed` conjunct's diagnostic. -/
def irqDuplicateBootError : String :=
  "boot: duplicate IRQ registration detected in platform config"

/-- The second's. -/
def objectIdDuplicateBootError : String :=
  "boot: duplicate object ID detected in platform config"

/-- The third's (PR #889 review round 2). -/
def idleSlotReservationBootError : String :=
  "boot: platform config occupies or references a reserved per-core idle slot " ++
    "(WS-RR RR5.13 / PR #889 review)"

/-- The fourth's (PR #889 review rounds 7 and 8). -/
def embeddedIdentityBootError : String :=
  "boot: an entry's embedded identity (a TCB's thread id, a SchedContext's id or a " ++
    "Reply's id) is not its own object id (PR #889 review rounds 7 and 8)"

/-- Returned only where no conjunct fails, which `wellFormedDiagnostic_reports_a_fault`
    shows the refusal path never reaches. -/
def wellFormedNoFaultBootError : String :=
  "boot: platform config rejected with no failing well-formedness conjunct (unreachable)"

/-- **PR #889 review round 23**: the refusal for a configuration that declares
no PEs, or more than the model has.  A plain constant, like its siblings: the
error arms are scrutinised structurally by `split`, and an interpolation where
the dependent elimination expects a literal fails. -/
def declaredCoreCountBootError : String :=
  "PlatformConfig.machineConfig.declaredCoreCount must be between 1 and numCores"

/-- **PR #889 review round 23**: the configuration declares between one and
`numCores` PEs.

`MachineConfig.declaredCoreCount` had an upper bound only — round 22's
`declaredCoresOfConfig` clamps a too-large count to `allCores`, and said nothing
about zero.  At zero the derivation yields the *empty* core list, so the boot
installs no idle thread on any core and enqueues no runnable fallback, while
`bootAffinitiesDeclared []` is satisfied by any config whose TCBs are unpinned.
Such a boot returns `.ok` and its first scheduling point finds `currentOnCore`
empty on every core with nothing to select — the machine is not merely narrow,
it has nowhere to run.

`numCores_pos` makes the range non-empty, so this refuses exactly the degenerate
count and nothing a real deployment declares.  The upper bound is stated here
too rather than left to the clamp: a config asking for more PEs than the model
has is a mistake worth a diagnostic, not something to silently widen. -/
def declaredCoreCountInRange (config : PlatformConfig) : Bool :=
  0 < config.machineConfig.declaredCoreCount &&
    config.machineConfig.declaredCoreCount ≤ SeLe4n.Kernel.Concurrency.numCores

/-- AK8-A (WS-AK / C-M01): Cross-untyped physical-region disjointness for
boot configs. For any two distinct `.untyped` entries in `initialObjects`
where **neither is a direct child of the other**, their physical ranges
must not overlap.

The `children` side-conditions mirror the runtime
`Kernel.untypedRegionsDisjoint` invariant so a config-level witness
transports cleanly to the runtime post-state. At boot, configurations
typically list only top-level untypeds (no `children`), so the
side-conditions are vacuous and this reduces to pairwise region
disjointness across the whole untyped set — the case the audit §C-M01
finding was motivating.

This mirrors the existing `mmioRegionDisjointCheck` pattern (which validates
MMIO region disjointness at boot) and is the config-level precondition that
discharges the runtime `Kernel.untypedRegionsDisjoint` invariant. -/
def PlatformConfig.untypedRegionsDisjoint (config : PlatformConfig) : Prop :=
  ∀ (e₁ e₂ : ObjectEntry) (ut₁ ut₂ : UntypedObject),
    e₁ ∈ config.initialObjects →
    e₂ ∈ config.initialObjects →
    e₁.id ≠ e₂.id →
    e₁.obj = .untyped ut₁ →
    e₂.obj = .untyped ut₂ →
    (∀ c ∈ ut₁.children, c.objId ≠ e₂.id) →
    (∀ c ∈ ut₂.children, c.objId ≠ e₁.id) →
    ut₁.regionBase.val + ut₁.regionSize ≤ ut₂.regionBase.val ∨
    ut₂.regionBase.val + ut₂.regionSize ≤ ut₁.regionBase.val

/-- AK8-A: Empty config trivially satisfies `untypedRegionsDisjoint`. -/
theorem PlatformConfig.untypedRegionsDisjoint_empty :
    PlatformConfig.untypedRegionsDisjoint { irqTable := [], initialObjects := [] } := by
  intro _ _ _ _ hMem _ _ _ _ _ _; exact absurd hMem (by simp)

/-- **WS-BP BP3.2**: the kind of memory an untyped of this flavour may
    describe — device memory for a device untyped, RAM otherwise. -/
def untypedRegionKind (ut : UntypedObject) : MemoryKind :=
  if ut.isDevice then .device else .ram

/-- **WS-BP BP3.2**: the untyped lies inside one region the machine declares,
    of its own kind. -/
def untypedWithinDeclaredRegion (mc : MachineConfig) (ut : UntypedObject) : Bool :=
  mc.memoryMap.any (fun r =>
    r.kind == untypedRegionKind ut &&
      decide (r.base.toNat ≤ ut.regionBase.toNat) &&
      decide (ut.regionBase.toNat + ut.regionSize ≤ r.endAddr))

/-- **WS-BP BP3.2**: the untyped overlaps nothing the kernel keeps for
    itself (`MachineConfig.kernelReserved`). -/
def untypedClearOfKernel (mc : MachineConfig) (ut : UntypedObject) : Bool :=
  mc.kernelReserved.all (fun k =>
    decide (ut.regionBase.toNat + ut.regionSize ≤ k.base.toNat) ||
      decide (k.endAddr ≤ ut.regionBase.toNat))

/-- **WS-BP BP3.2**: two entries do not describe overlapping untyped memory —
    vacuous unless both are untypeds, and for one entry compared with
    itself. -/
def untypedEntriesDisjoint (e₁ e₂ : ObjectEntry) : Bool :=
  match e₁.obj, e₂.obj with
  | .untyped u₁, .untyped u₂ =>
      e₁.id == e₂.id ||
        decide (u₁.regionBase.val + u₁.regionSize ≤ u₂.regionBase.val) ||
        decide (u₂.regionBase.val + u₂.regionSize ≤ u₁.regionBase.val)
  | _, _ => true

/-- **WS-BP BP3.2**: the seventh `wellFormed` conjunct — **a boot untyped
    describes only memory it may.**

    An untyped is authority over physical memory: its holder retypes it into
    frames, page tables and kernel objects.  `bootSafeUntypedCheck` reads the
    carve state, never the extent, by design, and before this conjunct
    nothing else read an untyped's extent, so a configuration could hand the root task an untyped
    over the kernel's own image, a normal untyped over the GIC's registers, one
    over RAM the board does not have, or two untypeds over one range — each a
    route to memory the kernel never meant to give out.  seL4's boot derives
    the root task's untypeds from free memory with the kernel image removed;
    this kernel takes them from the integrator's configuration, so it refuses
    the configurations seL4's derivation cannot produce.  Three conditions:

    * **inside one declared region of its own kind** — a normal untyped in
      `.ram`, a device untyped in `.device` (`untypedWithinDeclaredRegion`);
    * **clear of the kernel's reserved extent** (`untypedClearOfKernel`, over
      the bound machine configuration's `kernelReserved`);
    * **disjoint from every other boot untyped** (`untypedEntriesDisjoint`) —
      the runtime check of the config-level `untypedRegionsDisjoint` the proof
      bridge takes as a hypothesis, which nothing on the live path decided
      before (`untypedPlacementRespected_untypedRegionsDisjoint`).

    Registered at `v0.36.2` in `docs/REGISTERED_DEBT.md` table B and closed
    here.  Not attacker-reachable — untypeds come only from the integrator's
    compiled configuration — so it closes a misconfiguration class and a model
    gap against seL4, not an exploit. -/
def untypedPlacementRespected (config : PlatformConfig) : Bool :=
  config.initialObjects.all (fun e =>
    match e.obj with
    | .untyped ut =>
        untypedWithinDeclaredRegion config.machineConfig ut &&
          untypedClearOfKernel config.machineConfig ut
    | _ => true) &&
  config.initialObjects.all (fun e₁ =>
    config.initialObjects.all (fun e₂ => untypedEntriesDisjoint e₁ e₂))

/-- The seventh conjunct's diagnostic. -/
def untypedPlacementBootError : String :=
  "boot: an untyped lies outside every declared region of its kind, overlaps the " ++
    "kernel's reserved extent, or overlaps another boot untyped (WS-BP BP3.2)"

/-- **WS-BP BP3.2**: the runtime conjunct decides the config-level
    disjointness the proof bridge takes as a hypothesis — strictly more, since
    it ignores the `children` carve-out the Prop grants a parent and its direct
    child (a boot untyped has no children to carve). -/
theorem untypedPlacementRespected_untypedRegionsDisjoint (config : PlatformConfig)
    (h : untypedPlacementRespected config = true) : config.untypedRegionsDisjoint := by
  intro e₁ e₂ u₁ u₂ h₁ h₂ hNe hO₁ hO₂ _ _
  simp only [untypedPlacementRespected, Bool.and_eq_true, List.all_eq_true] at h
  have hPair := h.2 e₁ h₁ e₂ h₂
  simp only [untypedEntriesDisjoint, hO₁, hO₂, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hPair
  rcases hPair with (hId | hLe) | hLe
  · exact absurd hId hNe
  · exact Or.inl hLe
  · exact Or.inr hLe

/-- U6-E/F: A well-formed PlatformConfig has unique IRQs, unique object IDs,
    (WS-RR RR5.13, PR #889 review) keeps the per-core idle slots free,
    (PR #889 review rounds 7 and 8) stores every TCB, SchedContext and Reply
    under its own id, (round 18) leaves object-index room for the boot
    root and the per-core idle threads, (round 23) declares between one and
    `numCores` PEs, and (WS-BP BP3.2) places every boot untyped over memory it
    may describe. -/
def PlatformConfig.wellFormed (config : PlatformConfig) : Bool :=
  irqsUnique config.irqTable && objectIdsUnique config.initialObjects &&
    idleSlotsReserved config && embeddedIdentitiesMatchSlots config &&
    objectBudgetRespected config && declaredCoreCountInRange config &&
    untypedPlacementRespected config

/-- **PR #889 review round 23**: a well-formed config declares at least one PE
    and no more than the model has.  Zero is what this refuses: the derivation
    would hand the boot an empty core list, so no core would get an idle thread
    and the first scheduling point would find nothing to select anywhere. -/
theorem PlatformConfig.wellFormed_declaredCoreCountInRange (config : PlatformConfig)
    (h : config.wellFormed = true) : declaredCoreCountInRange config = true := by
  simp_all only [PlatformConfig.wellFormed, Bool.and_eq_true]

/-- **WS-BP BP3.2**: a well-formed config places every boot untyped over
    memory it may describe. -/
theorem PlatformConfig.wellFormed_untypedPlacementRespected (config : PlatformConfig)
    (h : config.wellFormed = true) : untypedPlacementRespected config = true := by
  simp_all only [PlatformConfig.wellFormed, Bool.and_eq_true]

/-- **WS-BP BP3.2**: ...so a well-formed config discharges the proof bridge's
    untyped-disjointness hypothesis. -/
theorem PlatformConfig.wellFormed_untypedRegionsDisjoint (config : PlatformConfig)
    (h : config.wellFormed = true) : config.untypedRegionsDisjoint :=
  untypedPlacementRespected_untypedRegionsDisjoint config
    (config.wellFormed_untypedPlacementRespected h)

/-- PR #889 review round 18: a well-formed config leaves room for the boot
    root and the idle threads. -/
theorem PlatformConfig.wellFormed_objectBudgetRespected (config : PlatformConfig)
    (h : config.wellFormed = true) : objectBudgetRespected config = true := by
  simp_all only [PlatformConfig.wellFormed, Bool.and_eq_true]

/-- PR #889 review round 19 (maintainer follow-up): the `wellFormed` conjuncts
    paired with the diagnostic each one owns.

    The `else if` cascade this replaces was a *second* enumeration of the same
    conjuncts, and the two drifted twice: round 2 found `idleSlotsReserved`
    reported as a duplicate object id, and round 19 found
    `objectBudgetRespected` reported as an embedded-identity mismatch — each
    time because a conjunct was added to `wellFormed` and not to the cascade.
    One list read by both cannot drift that way, `wellFormed_eq_all_conjuncts`
    fails to elaborate if a conjunct is added to only one of them, and the
    refusal's *depth* is no longer encoded in five downstream tactic scripts. -/
def wellFormedConjuncts (config : PlatformConfig) : List (Bool × String) :=
  [(irqsUnique config.irqTable, irqDuplicateBootError),
   (objectIdsUnique config.initialObjects, objectIdDuplicateBootError),
   (idleSlotsReserved config, idleSlotReservationBootError),
   (embeddedIdentitiesMatchSlots config, embeddedIdentityBootError),
   (objectBudgetRespected config, objectBudgetBootError),
   (declaredCoreCountInRange config, declaredCoreCountBootError),
   (untypedPlacementRespected config, untypedPlacementBootError)]

/-- The first conjunct `config` fails, reported in its own words. -/
def wellFormedDiagnostic (config : PlatformConfig) : String :=
  match (wellFormedConjuncts config).find? (fun row => !row.1) with
  | some row => row.2
  | none => wellFormedNoFaultBootError

/-- The pin: `wellFormed` and the diagnostic list enumerate the same conjuncts.
    A conjunct added to one and not the other fails here. -/
theorem wellFormed_eq_all_conjuncts (config : PlatformConfig) :
    config.wellFormed = (wellFormedConjuncts config).all (·.1) := by
  simp [PlatformConfig.wellFormed, wellFormedConjuncts, Bool.and_assoc]

/-- A refused config always has a failing conjunct to name, so the refusal path
    never returns `wellFormedNoFaultBootError`. -/
theorem wellFormedDiagnostic_reports_a_fault (config : PlatformConfig)
    (h : config.wellFormed = false) :
    ((wellFormedConjuncts config).find? (fun row => !row.1)).isSome = true := by
  rw [wellFormed_eq_all_conjuncts] at h
  cases hFind : (wellFormedConjuncts config).find? (fun row => !row.1) with
  | some _ => rfl
  | none =>
      rw [List.find?_eq_none] at hFind
      have hAll : ((wellFormedConjuncts config).all (·.1)) = true := by
        simp only [List.all_eq_true]
        intro row hRow
        simpa using hFind row hRow
      rw [hAll] at h
      exact absurd h (by simp)

/-- **PR #889 review round 23**: a well-formed config has a duplicate-free IRQ
    table.  Added to complete the accessor family: the two call sites that
    needed this fact were writing their own projection path into the
    conjunction, which is the thing that breaks every time a conjunct is
    added. -/
theorem PlatformConfig.wellFormed_irqsUnique (config : PlatformConfig)
    (h : config.wellFormed = true) : irqsUnique config.irqTable = true := by
  simp_all only [PlatformConfig.wellFormed, Bool.and_eq_true]

/-- **PR #889 review round 23**: ...and duplicate-free object ids. -/
theorem PlatformConfig.wellFormed_objectIdsUnique (config : PlatformConfig)
    (h : config.wellFormed = true) : objectIdsUnique config.initialObjects = true := by
  simp_all only [PlatformConfig.wellFormed, Bool.and_eq_true]

/-- **WS-RR RR5.13**: a well-formed config reserves the idle slots. -/
theorem PlatformConfig.wellFormed_idleSlotsReserved (config : PlatformConfig)
    (h : config.wellFormed = true) : idleSlotsReserved config = true := by
  simp_all only [PlatformConfig.wellFormed, Bool.and_eq_true]

/-- PR #889 review round 8: a well-formed config stores every id-carrying
    object under its own id. -/
theorem PlatformConfig.wellFormed_embeddedIdentitiesMatchSlots (config : PlatformConfig)
    (h : config.wellFormed = true) : embeddedIdentitiesMatchSlots config = true := by
  simp_all only [PlatformConfig.wellFormed, Bool.and_eq_true]

/-- PR #889 review round 7: a well-formed config stores every TCB under its
    own thread id. -/
theorem PlatformConfig.wellFormed_tcbIdentitiesMatchSlots (config : PlatformConfig)
    (h : config.wellFormed = true) : tcbIdentitiesMatchSlots config = true :=
  ((Bool.and_eq_true _ _).mp
    ((Bool.and_eq_true _ _).mp (config.wellFormed_embeddedIdentitiesMatchSlots h)).1).1

/-- PR #889 review round 8: a well-formed config stores every SchedContext
    under its own id. -/
theorem PlatformConfig.wellFormed_schedContextIdentitiesMatchSlots (config : PlatformConfig)
    (h : config.wellFormed = true) : schedContextIdentitiesMatchSlots config = true :=
  ((Bool.and_eq_true _ _).mp
    ((Bool.and_eq_true _ _).mp (config.wellFormed_embeddedIdentitiesMatchSlots h)).1).2

/-- PR #889 review round 8: a well-formed config stores every Reply under its
    own id. -/
theorem PlatformConfig.wellFormed_replyIdentitiesMatchSlots (config : PlatformConfig)
    (h : config.wellFormed = true) : replyIdentitiesMatchSlots config = true :=
  ((Bool.and_eq_true _ _).mp (config.wellFormed_embeddedIdentitiesMatchSlots h)).2

/-- PR #889 review round 7: the identity relation, entry by entry. -/
theorem tcbIdentitiesMatchSlots_tid_eq (config : PlatformConfig)
    (h : tcbIdentitiesMatchSlots config = true) :
    ∀ e ∈ config.initialObjects, ∀ tcb : TCB, e.obj = .tcb tcb → tcb.tid.toObjId = e.id := by
  intro e he tcb hObj
  have hE := List.all_eq_true.mp h e he
  simp only [hObj, beq_iff_eq] at hE
  exact hE

/-- PR #889 review round 8: the SchedContext identity relation, entry by entry. -/
theorem schedContextIdentitiesMatchSlots_scId_eq (config : PlatformConfig)
    (h : schedContextIdentitiesMatchSlots config = true) :
    ∀ e ∈ config.initialObjects, ∀ sc : SchedContext,
      e.obj = .schedContext sc → sc.scId.toObjId = e.id := by
  intro e he sc hObj
  have hE := List.all_eq_true.mp h e he
  simp only [hObj, beq_iff_eq] at hE
  exact hE

/-- PR #889 review round 8: the Reply identity relation, entry by entry. -/
theorem replyIdentitiesMatchSlots_replyId_eq (config : PlatformConfig)
    (h : replyIdentitiesMatchSlots config = true) :
    ∀ e ∈ config.initialObjects, ∀ r : Reply,
      e.obj = .reply r → r.replyId.toObjId = e.id := by
  intro e he r hObj
  have hE := List.all_eq_true.mp h e he
  simp only [hObj, beq_iff_eq] at hE
  exact hE

/-- **WS-RR RR5.13**: no config object sits in an idle slot under the reservation. -/
theorem idleSlotsReserved_initialObjects (config : PlatformConfig)
    (h : idleSlotsReserved config = true) :
    ∀ e ∈ config.initialObjects, isIdleObjId e.id = false := by
  intro e he
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  have hE := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp h1 e he)
  simpa using hE.1

/-- PR #889 review round 2: no config object references an idle slot under the
    reservation. -/
theorem idleSlotsReserved_no_idle_references (config : PlatformConfig)
    (h : idleSlotsReserved config = true) :
    ∀ e ∈ config.initialObjects, bootObjectReferencesReservedIdleSlot e.obj = false := by
  intro e he
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  have hE := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp h1 e he)
  simpa using hE.2

/-- PR #889 review round 7: no boot TCB's own identity is an idle thread's —
    the first disjunct of the reference check's TCB arm. -/
theorem idleSlotsReserved_no_idle_tid (config : PlatformConfig)
    (h : idleSlotsReserved config = true) :
    ∀ e ∈ config.initialObjects, ∀ tcb : TCB, e.obj = .tcb tcb →
      SeLe4n.Kernel.isIdleThreadId tcb.tid = false := by
  intro e he tcb hObj
  have hRef := idleSlotsReserved_no_idle_references config h e he
  rw [hObj] at hRef
  simp only [bootObjectReferencesReservedIdleSlot, tcbReferencesReservedIdleSlot_def,
    Bool.or_eq_false_iff, and_assoc] at hRef
  exact hRef.1

/-- PR #889 review round 8: no boot TCB's `queuePPrev` names an idle thread —
    the link the projection-based arm never read. -/
theorem idleSlotsReserved_no_idle_queuePPrev (config : PlatformConfig)
    (h : idleSlotsReserved config = true) :
    ∀ e ∈ config.initialObjects, ∀ tcb : TCB, e.obj = .tcb tcb →
      ∀ prev, tcb.queuePPrev = some (.tcbNext prev) →
        SeLe4n.Kernel.isIdleThreadId prev = false := by
  intro e he tcb hObj prev hPrev
  have hRef := idleSlotsReserved_no_idle_references config h e he
  rw [hObj] at hRef
  simp only [bootObjectReferencesReservedIdleSlot, tcbReferencesReservedIdleSlot_def,
    Bool.or_eq_false_iff, and_assoc] at hRef
  have hLink := hRef.2.2.2.2.2.2.1
  rw [hPrev] at hLink
  exact hLink

/-- **WS-RR RR5.13**: the boot VSpace root, when present, is not in an idle slot
    under the reservation. -/
theorem idleSlotsReserved_bootVSpaceRoot (config : PlatformConfig)
    (h : idleSlotsReserved config = true) (entry : BootVSpaceRootEntry)
    (hSome : config.bootVSpaceRoot = some entry) : isIdleObjId entry.id = false := by
  have h2 := ((Bool.and_eq_true _ _).mp h).2
  rw [hSome] at h2
  simpa using h2

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

/-! ### The per-kind boot-safety checks, pinned by constructor arity

PR #889 review round 8 (the sweep the reservation's fix implies).  The
reservation's TCB arm and this check's TCB arm were the same shape — a
hand-written list of fields — and the review found `queuePPrev` missing from
**both**.  Pinning one list and leaving its sibling is exactly the "fix applied
at one site and not its siblings" this project keeps re-learning, so each arm
below destructures its constructor: the pattern names every field (the ones the
check does not constrain as `_`), so a field added to any kernel object fails
this file with an arity error until the author says whether a boot object may
carry it.

The bodies are unchanged; each is restated in projection form by a `…_def`
lemma proved by `rfl` (structure eta), because a `simp only` that unfolds a
27-field constructor match times out at `whnf` while the rewrite does not.

`.vspaceRoot` is the one arm with no pin, and needs none: it passes the whole
object to `bootSafeVSpaceRootCheck`, so there is no enumeration here to drift —
a new `VSpaceRoot` field is that checker's to classify, in its own module. -/

/-- A boot **endpoint** is inert: both intrusive queues empty. -/
def bootSafeEndpointCheck (ep : Endpoint) : Bool :=
  match ep with
  | ⟨_sendQ, _receiveQ, _lock⟩ =>
    ep.sendQ.head.isNone && ep.sendQ.tail.isNone &&
    ep.receiveQ.head.isNone && ep.receiveQ.tail.isNone

@[simp] theorem bootSafeEndpointCheck_def (ep : Endpoint) :
    bootSafeEndpointCheck ep =
      (ep.sendQ.head.isNone && ep.sendQ.tail.isNone &&
       ep.receiveQ.head.isNone && ep.receiveQ.tail.isNone) := rfl

/-- A boot **notification** is idle, unwaited and unbadged.  `boundTCB` is
    unconstrained here — a boot notification may be pre-bound to a config
    thread; what it may not be bound to is an idle thread, which is the
    reservation's `notificationReferencesReservedIdleSlot`. -/
def bootSafeNotificationCheck (notif : Notification) : Bool :=
  match notif with
  | ⟨_state, _waitingThreads, _pendingBadge, _boundTCB, _lock⟩ =>
    decide (notif.state = .idle) && notif.waitingThreads.isEmpty &&
    notif.pendingBadge.isNone

@[simp] theorem bootSafeNotificationCheck_def (notif : Notification) :
    bootSafeNotificationCheck notif =
      (decide (notif.state = .idle) && notif.waitingThreads.isEmpty &&
       notif.pendingBadge.isNone) := rfl

/-- **WS-BP BP3.5**: a boot **capability** carries a valid badge if it carries
    one, and is not a reply capability.

    Both are clauses of `bootSafeObject`'s CNode arm, and until BP3.5 neither
    was checked: the runtime sweep checked a CNode's shape and nothing about
    what its slots hold, so a configuration whose CNode held a reply capability
    — which can only dangle at boot, since reply capabilities are minted at
    runtime from retyped Reply objects — or an out-of-range badge passed the
    checked boot, and the state it installed violated the capability bundle's
    `replyCapPointsToValidReply` and `capabilityBadgesWellFormed`.  The
    Prop-level predicate stated the rule and the validator did not enforce it;
    the proof bridge assumed it (`PlatformConfig.bootSafe`) and the production
    boot never established it.  Now the check decides it, per capability. -/
def bootSafeCapCheck (cap : Capability) : Bool :=
  (match cap.badge with
   | some b => b.isValid
   | none => true) &&
  (match cap.target with
   | .replyCap _ => false
   | _ => true)

/-- A boot **CNode** is structurally well-formed, and every capability it holds
    passes `bootSafeCapCheck`.  The structural conditions are over derived
    projections (`slotCount`, `bitsConsumed`, `guardBounded`), which the
    pattern's fields determine; the per-capability condition is a fold over the
    slots, read back per lookup by `RHTable.fold_and_true_of_get?`. -/
def bootSafeCnodeCheck (cn : CNode) : Bool :=
  match cn with
  | ⟨_depth, _guardWidth, _guardValue, _radixWidth, _slots, _lock⟩ =>
    decide (cn.slots.size ≤ cn.slotCount) &&
    decide (cn.depth ≤ maxCSpaceDepth) &&
    decide (cn.bitsConsumed > 0 → cn.bitsConsumed ≤ cn.depth ∧ 0 < cn.bitsConsumed ∧ cn.guardBounded) &&
    cn.slots.fold true (fun acc _ cap => acc && bootSafeCapCheck cap)

@[simp] theorem bootSafeCnodeCheck_def (cn : CNode) :
    bootSafeCnodeCheck cn =
      (decide (cn.slots.size ≤ cn.slotCount) &&
       decide (cn.depth ≤ maxCSpaceDepth) &&
       decide (cn.bitsConsumed > 0 →
         cn.bitsConsumed ≤ cn.depth ∧ 0 < cn.bitsConsumed ∧ cn.guardBounded) &&
       cn.slots.fold true (fun acc _ cap => acc && bootSafeCapCheck cap)) := rfl

/-- **WS-BP BP3.5**: what a passed CNode check says of each capability. -/
theorem bootSafeCnodeCheck_caps {cn : CNode}
    (hFold : cn.slots.fold true (fun acc _ cap => acc && bootSafeCapCheck cap) = true)
    {slot : SeLe4n.Slot} {cap : Capability} (hLookup : cn.lookup slot = some cap) :
    (∀ badge, cap.badge = some badge → badge.valid) ∧
    (∀ rid, cap.target ≠ .replyCap rid) := by
  have hc := SeLe4n.Kernel.RobinHood.RHTable.fold_and_true_of_get? cn.slots.table
    (fun _ cap => bootSafeCapCheck cap) hFold hLookup
  unfold bootSafeCapCheck at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hBadge, hTarget⟩ := hc
  refine ⟨fun badge hB => ?_, fun rid hT => ?_⟩
  · rw [hB] at hBadge
    simpa [SeLe4n.Badge.isValid, SeLe4n.Badge.valid] using hBadge
  · rw [hT] at hTarget
    cases hTarget

/-- A boot **TCB** is detached and inactive: no pending message, ready IPC
    state, all three queue links empty (PR #889 review round 8 for
    `queuePPrev` — `endpointQueueEnqueue` refuses a node whose `queuePPrev` is
    set as already queued, so a boot TCB carrying one could never block on an
    endpoint), no timeout budget, no SchedContext binding, no reply
    references, and `threadState = .Inactive` (it is neither current nor
    queued, so `inferThreadState` classifies it `.Inactive` and the stored
    field must agree, or the checked boot installs a `threadStateConsistent`
    violation).

    Unconstrained, and why: the scheduling parameters (`priority`, `domain`,
    `timeSlice`, `deadline`, `maxControlledPriority`, `cpuAffinity`) and the
    address-space fields (`cspaceRoot`, `vspaceRoot`, `ipcBuffer`,
    `boundNotification`, `faultHandler`) are the deployment's to choose;
    `tid` is pinned to the slot by `PlatformConfig.wellFormed`; `pipBoost`,
    `timedOut`, `registerContext`, `lock` and `pendingFault` are zero-valued
    by their own defaults and a config that sets them describes a thread mid
    flight, which `threadState = .Inactive` already excludes. -/
def bootSafeTcbCheck (tcb : TCB) : Bool :=
  match tcb with
  | ⟨_tid, _priority, _domain, _cspaceRoot, _vspaceRoot, _ipcBuffer, _ipcState, _threadState,
     _timeSlice, _deadline, _queuePrev, _queuePPrev, _queueNext, _pendingMessage,
     _registerContext, _faultHandler, _boundNotification, _schedContextBinding, _timeoutBudget,
     _maxControlledPriority, _pipBoost, _timedOut, _lock, _cpuAffinity, _replyObject,
     _pendingReceiveReply, _pendingFault⟩ =>
    tcb.pendingMessage.isNone && decide (tcb.ipcState = .ready) &&
    tcb.queueNext.isNone && tcb.queuePrev.isNone && tcb.queuePPrev.isNone &&
    tcb.timeoutBudget.isNone &&
    decide (tcb.schedContextBinding = .unbound) &&
    tcb.replyObject.isNone &&
    tcb.pendingReceiveReply.isNone &&
    decide (tcb.threadState = .Inactive)

@[simp] theorem bootSafeTcbCheck_def (tcb : TCB) :
    bootSafeTcbCheck tcb =
      (tcb.pendingMessage.isNone && decide (tcb.ipcState = .ready) &&
       tcb.queueNext.isNone && tcb.queuePrev.isNone && tcb.queuePPrev.isNone &&
       tcb.timeoutBudget.isNone &&
       decide (tcb.schedContextBinding = .unbound) &&
       tcb.replyObject.isNone &&
       tcb.pendingReceiveReply.isNone &&
       decide (tcb.threadState = .Inactive)) := rfl

/-- A boot **untyped** region is *pristine*: nothing has been carved from it
    and it descends from nothing.  `watermark = 0` and `children = []`,
    because a watermark with no children misreports the region's free space
    and a child names an object the boot never carved; `parent = none`,
    because a boot untyped is top-level by definition — `parent` is what
    `untypedAncestorRegionsDisjoint` walks, and a config-supplied ancestor is
    a chain the boot did not build.  Its region and device flag are the
    deployment's description of memory it owns (bounded by
    `untypedPlacementRespected`), what it may *not* record is a reserved idle
    slot (`untypedReferencesReservedIdleSlot`), and `lock` is unheld by its
    own default, as every boot object's is.  The pattern is the pin: a new
    field is classified here rather than inheriting an accept.

    Until the `v0.36.2` audit this arm was `true` — the one boot object whose
    record the check read no field of — while `UntypedObject`'s own documented
    invariant `watermark ≤ regionSize` was established nowhere at boot. -/
def bootSafeUntypedCheck (ut : UntypedObject) : Bool :=
  match ut with
  | ⟨_regionBase, _regionSize, _watermark, _children, _isDevice, _parent, _lock⟩ =>
    ut.watermark == 0 && ut.children.isEmpty && ut.parent.isNone

@[simp] theorem bootSafeUntypedCheck_def (ut : UntypedObject) :
    bootSafeUntypedCheck ut =
      (ut.watermark == 0 && ut.children.isEmpty && ut.parent.isNone) := rfl

/-- A boot **SchedContext** has a well-formed CBS budget, no bound thread and
    (WS-OD OD2.1) an empty reply stack.  `scId` is pinned to the slot by
    `PlatformConfig.wellFormed`; `priority`, `deadline`, `domain`, `periodStart`
    and `isActive` are the deployment's.

    `scReply` is refused for the same reason `bootSafeReplyCheck` refuses a
    boot Reply's stack links: a head names a Reply that must be *on* this
    context's stack (`Reply.next = some (.head scId)`), and every admissible boot
    Reply is inert — so a config-supplied head could only dangle, installing a
    `donationChainWellFormed` violation before the first instruction runs. -/
def bootSafeSchedContextCheck (sc : SchedContext) : Bool :=
  match sc with
  | ⟨_scId, _budget, _period, _priority, _deadline, _domain, _budgetRemaining, _periodStart,
     _replenishments, _boundThread, _scReply, _donationOrigin, _isActive, _lock⟩ =>
    sc.period.isPositive &&
    decide (sc.budget.val ≤ sc.period.val) &&
    decide (sc.budgetRemaining.val ≤ sc.budget.val) &&
    decide (sc.replenishments.length ≤ maxReplenishments) &&
    sc.replenishments.all (fun r => decide (r.amount.val > 0)) &&
    sc.replenishments.all (fun r => decide (r.amount.val ≤ sc.budget.val)) &&
    sc.boundThread.isNone &&
    sc.scReply.isNone &&
    -- **WS-HP HP10.3**: and no recorded reservation origin.  The origin names the
    -- thread a loan came from, and a boot state has made no loan -- every
    -- admissible boot SchedContext is unbound with an empty reply stack, so a
    -- config-supplied origin could only name a loan that does not exist.
    sc.donationOrigin.isNone

@[simp] theorem bootSafeSchedContextCheck_def (sc : SchedContext) :
    bootSafeSchedContextCheck sc =
      (sc.period.isPositive &&
       decide (sc.budget.val ≤ sc.period.val) &&
       decide (sc.budgetRemaining.val ≤ sc.budget.val) &&
       decide (sc.replenishments.length ≤ maxReplenishments) &&
       sc.replenishments.all (fun r => decide (r.amount.val > 0)) &&
       sc.replenishments.all (fun r => decide (r.amount.val ≤ sc.budget.val)) &&
       sc.boundThread.isNone &&
       sc.scReply.isNone &&
       sc.donationOrigin.isNone) := rfl

/-- WS-SM SM6.D: a boot **Reply** is inert — no blocked caller, no donated SC,
    no `prev` link.  `replyId` is pinned to the slot by
    `PlatformConfig.wellFormed`. -/
def bootSafeReplyCheck (r : Reply) : Bool :=
  match r with
  | ⟨_replyId, _caller, _prev, _next, _lock⟩ => r.isFree

@[simp] theorem bootSafeReplyCheck_def (r : Reply) :
    bootSafeReplyCheck r = (r.caller.isNone && r.prev.isNone && r.next.isNone) := rfl

/-- AJ3-C (M-16): Bool-valued runtime check for boot-safe objects.
    Validates structural boot safety constraints that can be checked at
    runtime. Used by `bootFromPlatformChecked` to reject invalid objects.

    **Coverage**: every `bootSafeObject` conjunct (`bootSafeObjectCheck_sound`).
    Until WS-BP BP3.5 the CNode arm skipped the two clauses about what a slot
    holds — a valid badge and no reply capability — on the stated ground that
    boot CNodes are empty and the clauses were "checked at the Prop level" by
    the boot bridge.  Neither held: a deployment's CNodes hold its threads'
    capabilities, and the bridge assumed the clauses rather than checking
    them.  `bootSafeCapCheck` decides both.

    **WS-RC R3 (DEEP-BOOT-01)**: VSpaceRoots are now admitted iff they
    pass `Platform.RPi5.VSpaceBoot.bootSafeVSpaceRootCheck` (asid bounded,
    every mapping W^X compliant, at least one mapping present, every
    physical address fits within the BCM2712 44-bit PA space, and — per
    the third-audit hardening — every virtual address is canonical
    (< 2^48)).  Previously the boot path rejected ALL VSpaceRoots,
    rendering the proven-W^X-compliant `rpi5BootVSpaceRoot` data
    structure inert at runtime.

    **WS-BP BP3.2**: a VSpace root in `initialObjects` is a *thread's* address
    space, not the binding's, so it is checked by
    `bootSafeUserVSpaceRootCheck` — a user ASID and no mappings — while the
    binding's root keeps `bootSafeVSpaceRootCheck` (`bootVSpaceRootSafe`).  The
    arm used to name the kernel root's check, and was dead: the retired
    `noVSpaceRootsInInitialObjects` gate refused every configured VSpace root
    before the arm could admit one. -/
def bootSafeObjectCheck (obj : KernelObject) : Bool :=
  match obj with
  | .endpoint ep => bootSafeEndpointCheck ep
  | .notification notif => bootSafeNotificationCheck notif
  | .cnode cn => bootSafeCnodeCheck cn
  | .tcb tcb => bootSafeTcbCheck tcb
  | .vspaceRoot vsr =>
    SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeUserVSpaceRootCheck vsr
  | .untyped ut => bootSafeUntypedCheck ut
  | .schedContext sc => bootSafeSchedContextCheck sc
  | .reply r => bootSafeReplyCheck r
  -- **WS-BP BP7.1: a configured frame is refused.**  A frame is authority over
  -- the page at its `base`, so admitting one would hand whoever holds its
  -- capability memory no boot check has placed — the same hazard
  -- `untypedPlacementRespected` closes for untypeds, which is why frames are
  -- carved from those untypeds rather than configured beside them.  A
  -- deployment that needs frames at boot (a root task's image) widens this
  -- with a placement check of its own, never by admitting them unchecked.
  | .frame _ => false

set_option maxHeartbeats 400000 in
/-- AJ3-C (M-16), completed at **WS-BP BP3.5**: `bootSafeObjectCheck = true`
    implies every conjunct of `bootSafeObject` — the conclusion below is that
    predicate's body, stated here because the predicate is defined further down.

    It was `bootSafeObjectCheck_sound_structural` until BP3.5, and partial: the
    CNode arm concluded the three structural clauses and not the two about what
    the slots hold, with a docstring saying badge validity was "discharged by
    the boot invariant bridge".  It was not — that bridge *assumed* it — so the
    production boot installed CNodes no theorem had checked.  `bootSafeCapCheck`
    decides both clauses, and this theorem is now whole. -/
private theorem bootSafeObjectCheck_sound_core (obj : KernelObject)
    (h : bootSafeObjectCheck obj = true) :
    -- Endpoints: empty queues
    (∀ ep, obj = .endpoint ep →
      ep.sendQ.head = none ∧ ep.sendQ.tail = none ∧
      ep.receiveQ.head = none ∧ ep.receiveQ.tail = none) ∧
    -- Notifications: idle + empty
    -- WS-RC R4.C: `.val = []` references the underlying List projection.
    (∀ notif, obj = .notification notif →
      notif.state = .idle ∧ notif.waitingThreads.val = [] ∧ notif.pendingBadge = none) ∧
    -- CNodes: structural, and (WS-BP BP3.5) every held capability's badge is
    -- valid and none is a reply capability
    (∀ cn, obj = .cnode cn →
      cn.slotCountBounded ∧ cn.depth ≤ maxCSpaceDepth ∧
      (cn.bitsConsumed > 0 → cn.wellFormed) ∧
      (∀ slot cap badge, cn.lookup slot = some cap →
        cap.badge = some badge → badge.valid) ∧
      (∀ slot cap rid, cn.lookup slot = some cap →
        cap.target ≠ .replyCap rid)) ∧
    -- TCBs: clean boot state
    -- PR #822: a boot TCB carries no reply object.
    (∀ tcb, obj = .tcb tcb →
      tcb.pendingMessage = none ∧ tcb.ipcState = .ready ∧
      tcb.queueNext = none ∧ tcb.queuePrev = none ∧ tcb.queuePPrev = none ∧
      tcb.timeoutBudget = none ∧
      tcb.schedContextBinding = .unbound ∧
      tcb.replyObject = none ∧
      tcb.pendingReceiveReply = none ∧
      tcb.threadState = .Inactive) ∧
    -- WS-BP BP3.2: a configured VSpaceRoot is a thread's — admitted iff
    -- bootSafeUserVSpaceRoot (a user ASID, no mappings)
    (∀ vs, obj = .vspaceRoot vs →
      SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeUserVSpaceRoot vs) ∧
    -- SchedContexts: well-formed, unbound, and (WS-OD OD2.1) with an empty
    -- reply stack
    (∀ sc, obj = .schedContext sc →
      schedContextWellFormed sc ∧ sc.boundThread = none ∧ sc.scReply = none ∧
      -- **WS-HP HP10.3**: and no recorded reservation origin.
      sc.donationOrigin = none) ∧
    -- WS-SM SM6.D / PR #822: a boot Reply is inert — no blocked caller and no
    -- reply-stack link in either direction.
    (∀ r, obj = .reply r →
      r.caller = none ∧ r.prev = none ∧ r.next = none) ∧
    -- The `v0.36.2` audit: a boot untyped is pristine — nothing carved, no
    -- ancestry.
    (∀ ut, obj = .untyped ut →
      ut.watermark = 0 ∧ ut.children = [] ∧ ut.parent = none) := by
  -- Discharge each constructor case. Non-matching constructors produce absurd
  -- injection hypotheses, discharged by `intro _ h; cases h`.
  cases obj with
  | endpoint ep =>
    simp only [bootSafeObjectCheck, bootSafeEndpointCheck_def, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨fun _ he => by injection he; subst_vars; exact ⟨Option.eq_none_of_isNone h1, Option.eq_none_of_isNone h2, Option.eq_none_of_isNone h3, Option.eq_none_of_isNone h4⟩,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he⟩
  | notification notif =>
    simp only [bootSafeObjectCheck, bootSafeNotificationCheck_def, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨fun _ he => by injection he, fun _ he => by injection he; subst_vars; exact ⟨h1, List.isEmpty_iff.mp h2, Option.eq_none_of_isNone h3⟩,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he⟩
  | cnode cn =>
    simp only [bootSafeObjectCheck, bootSafeCnodeCheck_def, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨hSlots, hDepth⟩, hWf⟩, hCaps⟩ := h
    exact ⟨fun _ he => by injection he, fun _ he => by injection he,
           fun c hc => by
             injection hc; subst_vars
             exact ⟨hSlots, hDepth, hWf,
               fun _ _ badge hL hB => (bootSafeCnodeCheck_caps hCaps hL).1 badge hB,
               fun _ _ rid hL => (bootSafeCnodeCheck_caps hCaps hL).2 rid⟩,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he⟩
  | tcb tcb =>
    simp only [bootSafeObjectCheck, bootSafeTcbCheck_def, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h4b⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
    exact ⟨fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he,
           fun _ he => by injection he; subst_vars; exact ⟨Option.eq_none_of_isNone h1, h2, Option.eq_none_of_isNone h3, Option.eq_none_of_isNone h4, Option.eq_none_of_isNone h4b, Option.eq_none_of_isNone h5, h6, Option.eq_none_of_isNone h7, Option.eq_none_of_isNone h8, h9⟩,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he⟩
  | vspaceRoot vsr =>
    -- WS-BP BP3.2: bootSafeObjectCheck for VSpaceRoot reduces to
    -- `bootSafeUserVSpaceRootCheck vsr = true`, iff `bootSafeUserVSpaceRoot vsr`.
    simp only [bootSafeObjectCheck] at h
    have hBoot := (SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeUserVSpaceRootCheck_iff vsr).mp h
    exact ⟨fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he,
           fun v hv => by injection hv; subst_vars; exact hBoot,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he⟩
  | untyped ut =>
    -- The `v0.36.2` audit: the check's `.untyped` arm reads the carve state;
    -- thread its three conjuncts to the `.untyped` conclusion clause.
    simp only [bootSafeObjectCheck, bootSafeUntypedCheck_def, Bool.and_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨hWatermark, hChildren⟩, hParent⟩ := h
    exact ⟨fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he,
           fun _ he => by injection he; subst_vars; exact ⟨hWatermark, List.isEmpty_iff.mp hChildren, Option.eq_none_of_isNone hParent⟩⟩
  | reply r =>
    -- WS-SM SM6.D / PR #822: the check's `.reply` arm verifies the three
    -- inert-Reply fields; thread them to the `.reply` conclusion clause.
    simp only [bootSafeObjectCheck, bootSafeReplyCheck_def, Bool.and_eq_true] at h
    obtain ⟨⟨hCaller, hDonated⟩, hPrev⟩ := h
    exact ⟨fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he, fun _ he => by injection he,
           fun _ he => by injection he; subst_vars; exact ⟨Option.eq_none_of_isNone hCaller, Option.eq_none_of_isNone hDonated, Option.eq_none_of_isNone hPrev⟩,
           fun _ he => by injection he⟩
  | schedContext sc =>
    simp only [bootSafeObjectCheck, bootSafeSchedContextCheck_def, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hPeriod, hBudgetPeriod⟩, hRemaining⟩, hRepLen⟩, hRepPos⟩, hRepBound⟩,
      hUnbound⟩, hNoReplyStack⟩, hNoOrigin⟩ := h
    refine ⟨fun _ he => by injection he, fun _ he => by injection he,
            fun _ he => by injection he, fun _ he => by injection he,
            fun _ he => by injection he, fun s hs => ?_,
            fun _ he => by injection he, fun _ he => by injection he⟩
    injection hs; subst_vars
    refine ⟨?_, Option.eq_none_of_isNone hUnbound, Option.eq_none_of_isNone hNoReplyStack,
            Option.eq_none_of_isNone hNoOrigin⟩
    unfold schedContextWellFormed
    refine ⟨⟨hPeriod, hBudgetPeriod, hRemaining, hRepLen⟩, ⟨hRemaining, hBudgetPeriod⟩,
            ⟨hRepLen, ?_⟩, ?_⟩
    · intro r hr; exact decide_eq_true_eq.mp (List.all_eq_true.mp hRepPos r hr)
    · intro r hr; exact decide_eq_true_eq.mp (List.all_eq_true.mp hRepBound r hr)
  | frame _ =>
    -- WS-BP BP7.1: the check refuses every configured frame.
    simp [bootSafeObjectCheck] at h

/-- **WS-BP BP7.1**: `bootSafeObjectCheck` refuses every frame — the executable
half of `bootSafeObject`'s last conjunct. -/
theorem bootSafeObjectCheck_not_frame (obj : KernelObject)
    (h : bootSafeObjectCheck obj = true) : ∀ f, obj ≠ .frame f := by
  intro f hf; subst hf; simp [bootSafeObjectCheck] at h

/-- AJ3-C (M-16), completed at **WS-BP BP3.5**, and at **WS-BP BP7.1** for the
    frame refusal: `bootSafeObjectCheck = true` implies every conjunct of
    `bootSafeObject` — the conclusion is that predicate's body, stated here
    because the predicate is defined further down. -/
theorem bootSafeObjectCheck_sound (obj : KernelObject)
    (h : bootSafeObjectCheck obj = true) :
    (∀ ep, obj = .endpoint ep →
      ep.sendQ.head = none ∧ ep.sendQ.tail = none ∧
      ep.receiveQ.head = none ∧ ep.receiveQ.tail = none) ∧
    (∀ notif, obj = .notification notif →
      notif.state = .idle ∧ notif.waitingThreads.val = [] ∧ notif.pendingBadge = none) ∧
    (∀ cn, obj = .cnode cn →
      cn.slotCountBounded ∧ cn.depth ≤ maxCSpaceDepth ∧
      (cn.bitsConsumed > 0 → cn.wellFormed) ∧
      (∀ slot cap badge, cn.lookup slot = some cap →
        cap.badge = some badge → badge.valid) ∧
      (∀ slot cap rid, cn.lookup slot = some cap →
        cap.target ≠ .replyCap rid)) ∧
    (∀ tcb, obj = .tcb tcb →
      tcb.pendingMessage = none ∧ tcb.ipcState = .ready ∧
      tcb.queueNext = none ∧ tcb.queuePrev = none ∧ tcb.queuePPrev = none ∧
      tcb.timeoutBudget = none ∧
      tcb.schedContextBinding = .unbound ∧
      tcb.replyObject = none ∧
      tcb.pendingReceiveReply = none ∧
      tcb.threadState = .Inactive) ∧
    (∀ vs, obj = .vspaceRoot vs →
      SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeUserVSpaceRoot vs) ∧
    (∀ sc, obj = .schedContext sc →
      schedContextWellFormed sc ∧ sc.boundThread = none ∧ sc.scReply = none ∧
      sc.donationOrigin = none) ∧
    (∀ r, obj = .reply r →
      r.caller = none ∧ r.prev = none ∧ r.next = none) ∧
    (∀ ut, obj = .untyped ut →
      ut.watermark = 0 ∧ ut.children = [] ∧ ut.parent = none) ∧
    (∀ f, obj ≠ .frame f) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := bootSafeObjectCheck_sound_core obj h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, bootSafeObjectCheck_not_frame obj h⟩

-- ============================================================================
-- WS-RC R3 (DEEP-BOOT-01) — Boot-safety admission witness theorems
-- ============================================================================

/-- **WS-BP BP3.2**: the object sweep **refuses** the kernel's own boot root
    as a configured object — its ASID is the kernel's, and it maps the kernel.

    This replaces `bootSafeObjectCheck_admits_rpi5BootVSpaceRoot` (WS-RC R3),
    which stated the opposite and was true only while the sweep's `.vspaceRoot`
    arm was dead code behind a gate refusing every configured VSpace root.  With
    that gate retired the arm is live and asks the *thread's* question
    (`bootSafeUserVSpaceRootCheck`); the binding's root is checked where it is
    installed (`bootVSpaceRootSafe`).  The refusal is the point: a
    configuration cannot hand a thread the kernel's translation map. -/
theorem bootSafeObjectCheck_refuses_rpi5BootVSpaceRoot :
    bootSafeObjectCheck
        (KernelObject.vspaceRoot SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot) =
      false := by
  unfold bootSafeObjectCheck
  exact SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot_not_bootSafeUser


-- ============================================================================
-- AK9-C (P-M01): IRQ Handler Existence Validation
-- ============================================================================

/-- AK9-C (P-M01): Check that each declared `IrqEntry.handler` ObjId refers to
    a **notification** object present in `PlatformConfig.initialObjects`.

    The seL4 IRQ delivery model requires that the handler ObjId resolves to a
    notification kernel object: the GIC dispatch sequence signals the bound
    notification on interrupt delivery (`notificationSignal`), and user-space
    drivers register via notification capabilities. A handler ObjId resolving
    to any other kind (thread, endpoint, CNode, VSpaceRoot, SchedContext,
    Untyped) would be a boot configuration error — the runtime dispatch
    would fail or silently no-op on every interrupt.

    Returns `true` iff every IRQ's `handler` ObjId appears in `initialObjects`
    with variant `.notification _`. -/
def irqHandlersReferenceNotifications (config : PlatformConfig) : Bool :=
  config.irqTable.all fun irq =>
    match config.initialObjects.find? (fun entry => entry.id == irq.handler) with
    | some entry =>
      match entry.obj with
      | .notification _ => true
      | _ => false
    | none => false

/-- AK9-C: Empty IRQ table trivially satisfies handler-reference check. -/
theorem irqHandlersReferenceNotifications_empty_irqs
    (objs : List ObjectEntry) :
    irqHandlersReferenceNotifications { irqTable := [], initialObjects := objs } = true := by
  unfold irqHandlersReferenceNotifications; rfl

-- ============================================================================
-- WS-RC R3 (DEEP-BOOT-01) — bootVSpaceRoot config-level gates
-- ============================================================================

/-- **WS-RC R3 (DEEP-BOOT-01)**: Boot-VSpaceRoot ObjId distinctness gate.
    Returns `true` iff the boot VSpaceRoot entry (if any) carries an
    ObjId that does not collide with any entry in `initialObjects`.

    The collision check is necessary because `installBootVSpaceRoot`
    runs AFTER the `foldObjects` step.  Without this gate, a colliding
    ObjId would silently overwrite the prior `initialObjects` entry
    (last-wins on `RHTable.insert`), losing kernel state.  Returns
    `true` vacuously when `bootVSpaceRoot = none`. -/
def bootVSpaceRootObjIdDistinct (config : PlatformConfig) : Bool :=
  match config.bootVSpaceRoot with
  | none => true
  | some entry =>
      ! config.initialObjects.any (fun e => e.id == entry.id)

/-- **WS-RC R3 (DEEP-BOOT-01)**: Boot-VSpaceRoot boot-safety gate.
    Returns `true` iff the boot VSpaceRoot entry (if any) passes the
    runtime-decidable `bootSafeVSpaceRootCheck`.  Returns `true`
    vacuously when `bootVSpaceRoot = none`. -/
def bootVSpaceRootSafe (config : PlatformConfig) : Bool :=
  match config.bootVSpaceRoot with
  | none => true
  | some entry =>
      SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeVSpaceRootCheck entry.root

/-- **WS-RC R3**: Empty/no-boot-VSpace config trivially passes ObjId
    distinctness. -/
theorem bootVSpaceRootObjIdDistinct_none
    (config : PlatformConfig) (h : config.bootVSpaceRoot = none) :
    bootVSpaceRootObjIdDistinct config = true := by
  unfold bootVSpaceRootObjIdDistinct; rw [h]

/-- **WS-RC R3**: Empty/no-boot-VSpace config trivially passes boot-safety. -/
theorem bootVSpaceRootSafe_none
    (config : PlatformConfig) (h : config.bootVSpaceRoot = none) :
    bootVSpaceRootSafe config = true := by
  unfold bootVSpaceRootSafe; rw [h]

/-- **WS-BP BP3.2**: the ASID of every VSpace root the checked boot installs —
    each configured root's (`initialObjects`, in order) and then the binding's
    (`bootVSpaceRoot`). -/
def bootVSpaceAsids (config : PlatformConfig) : List SeLe4n.ASID :=
  config.initialObjects.filterMap bootEntryAsid? ++
  (match config.bootVSpaceRoot with
   | none => []
   | some entry => [entry.root.asid])

/-- **WS-BP BP3.2**: no two VSpace roots the boot installs share an ASID.

    Every boot install of a VSpace root registers its ASID
    (`createBootObject`), and a registration is an `RHTable.insert`: on a
    repeated key it re-points the ASID at the later root, so the earlier root
    would sit in the object store unreachable by `resolveAsidRoot` and a TLB
    tagged with its ASID would be read as the other's.  The runtime refuses a
    second root on a live ASID (the ASID manager allocates), and this is the
    boot's refusal of the same thing.

    **What it replaced.**  `noVSpaceRootsInInitialObjects` (WS-RC R3) refused
    *every* configured VSpace root, because `Builder.createObject` did not
    register an ASID and a root installed without one violates
    `asidTableConsistent`.  That was a refusal standing in for a missing write:
    with the write made (`bootEntryAsidTable`), the one remaining way a
    configured root can break the table is a collision, which is what this
    refuses.  A tombstone for the retired gate: the thread's own root is checked
    by `bootSafeUserVSpaceRootCheck` in the object sweep, the binding's by
    `bootVSpaceRootSafe`. -/
def bootVSpaceAsidsDistinct (config : PlatformConfig) : Bool :=
  decide (bootVSpaceAsids config).Nodup

/-- **WS-BP BP3.2**: a configuration installing no VSpace root but the
    binding's passes the ASID gate. -/
theorem bootVSpaceAsidsDistinct_of_no_configured_roots (config : PlatformConfig)
    (h : ∀ e ∈ config.initialObjects, ∀ vs, e.obj ≠ KernelObject.vspaceRoot vs) :
    bootVSpaceAsidsDistinct config = true := by
  have hNil : config.initialObjects.filterMap bootEntryAsid? = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro e hMem
    unfold bootEntryAsid?
    cases hObj : e.obj with
    | vspaceRoot vs => exact absurd hObj (h e hMem vs)
    | _ => rfl
  unfold bootVSpaceAsidsDistinct bootVSpaceAsids
  rw [hNil]
  cases config.bootVSpaceRoot <;> simp

/-- **WS-BP BP3.2**: an empty configuration passes the ASID gate. -/
theorem bootVSpaceAsidsDistinct_empty (config : PlatformConfig)
    (h : config.initialObjects = []) :
    bootVSpaceAsidsDistinct config = true :=
  bootVSpaceAsidsDistinct_of_no_configured_roots config (by simp [h])

/-- **WS-RC R3 — security/correctness audit fix**: gate forbidding the
    boot VSpaceRoot ObjId from being the reserved `ObjId.sentinel`
    value (`⟨0⟩` per Prelude.lean H-06/WS-E3 — meaning "unallocated").

    Defense-in-depth: the canonical `rpi5BootVSpaceRootEntry` and
    `simBootVSpaceRootEntry` use ObjId 1 (non-sentinel), but a
    third-party `BootVSpaceRootEntry` constructed via the public API
    could use the sentinel.  This gate catches such misuse at the
    boot pipeline. -/
def bootVSpaceRootObjIdNonSentinel (config : PlatformConfig) : Bool :=
  match config.bootVSpaceRoot with
  | none => true
  | some entry => ! entry.id.isReserved

/-- **WS-RC R3**: Empty/no-boot-VSpace config trivially passes the
    non-sentinel check. -/
theorem bootVSpaceRootObjIdNonSentinel_none
    (config : PlatformConfig) (h : config.bootVSpaceRoot = none) :
    bootVSpaceRootObjIdNonSentinel config = true := by
  unfold bootVSpaceRootObjIdNonSentinel; rw [h]

/-- U6-E/F: Checked boot — rejects configs with duplicate IRQs, duplicate object
    IDs, or unsafe initial objects.

    V5-C (M-DEF-3): **Recommended boot entry point.** This is the enforcement
    variant of `bootFromPlatform`. It validates `PlatformConfig.wellFormed`
    (uniqueness) AND `bootSafeObjectCheck` (object-level semantic safety) before
    proceeding. Returns an error if validation fails.

    AJ3-C (M-16): Added `bootSafeObjectCheck` validation. A config with unique
    IDs but invalid object states (e.g., endpoint with non-empty queues, TCB with
    `ipcState != .ready`) is now rejected.

    AK9-C (P-M01): Added `irqHandlersReferenceNotifications` validation.
    Every IRQ's handler ObjId must refer to a notification object in
    `initialObjects`.

    Use `SeLe4n.Testing.Deprecated.bootFromPlatformUnchecked` (alias for
    `bootFromPlatform`) only when the config is known-valid — e.g., test
    fixtures constructed programmatically with uniqueness guarantees.  The
    `Testing.Deprecated` namespace prevents production code from importing
    the unchecked form by accident (AN7-D.1 / PLT-M01).  All new boot paths
    should use this function. -/
def bootFromPlatformChecked (config : PlatformConfig) :
    Except String IntermediateState :=
  if config.wellFormed then
    if config.initialObjects.all (fun entry => bootSafeObjectCheck entry.obj) then
      -- WS-BP BP3.2: every VSpace root the boot installs registers its
      -- ASID (`createBootObject`), so the one way a configured root can
      -- break the ASID table is a collision — refused here.  This gate
      -- replaced WS-RC R3's refusal of every configured VSpace root.
      if bootVSpaceAsidsDistinct config then
        -- AK9-C (P-M01): Validate that every IRQ handler ObjId references a
        -- notification object in the config. This is verified as a final step
        -- after the per-object bootSafe check so the error message identifies
        -- the specific misconfiguration.
        if irqHandlersReferenceNotifications config then
          -- AK9-F (P-M05): Validate MachineConfig well-formedness + PA width
          -- bound (ARMv8 LPA max = 52). Prevents the production boot path
          -- from silently accepting a malformed MachineConfig that would leave
          -- the runtime in an inconsistent state (region overlap, non-power-of-
          -- two page size, PA width > 52).
          if config.machineConfig.wellFormed then
            if config.machineConfig.physicalAddressWidth ≤ 52 then
              -- WS-RC R3 (DEEP-BOOT-01): Validate boot-VSpaceRoot
              -- entry (if present): the ObjId must not collide with
              -- any `initialObjects` entry, must not be the
              -- reserved sentinel value, and the root must satisfy
              -- the runtime-decidable boot-safety predicate.
              if bootVSpaceRootObjIdDistinct config then
                if bootVSpaceRootObjIdNonSentinel config then
                  if bootVSpaceRootSafe config then
                    -- AK9-G (P-M06): Enable interrupts at the end of the
                    -- checked boot path, mirroring the Rust HAL Phase-3
                    -- IRQ re-enable after GIC + timer initialization.
                    -- The runtime begins with `interruptsEnabled = true`,
                    -- matching post-HAL hardware state.  The raw
                    -- `bootFromPlatform` pre-interrupts image is still
                    -- accessible (callers can inspect it by composing
                    -- `bootFromPlatform` directly) for negative-state or
                    -- boot-invariant-bridge contexts.
                    --
                    -- WS-RC R3 (DEEP-BOOT-01): When `bootVSpaceRoot`
                    -- carries an entry, install it via
                    -- `installBootVSpaceRoot` AFTER the standard fold
                    -- but BEFORE the interrupts step.  The install
                    -- registers the ASID in `asidTable` so subsequent
                    -- VSpace operations (`resolveAsidRoot`, etc.) can
                    -- find the boot root via the standard lookup path.
                    let basePost := bootFromPlatform config
                    let withBootVSpace : IntermediateState :=
                      match config.bootVSpaceRoot with
                      | none => basePost
                      | some entry =>
                          installBootVSpaceRoot basePost entry.id entry.root entry.hMappings
                    .ok (bootEnableInterruptsOp withBootVSpace)
                  else
                    .error "boot: bootVSpaceRoot fails boot-safety check (W^X / asid / paddr / non-empty mappings) (WS-RC R3 / DEEP-BOOT-01)"
                else
                  .error "boot: bootVSpaceRoot uses reserved ObjId.sentinel (WS-RC R3 / DEEP-BOOT-01 audit fix; H-06/WS-E3 sentinel is reserved as 'unallocated')"
              else
                .error "boot: bootVSpaceRoot ObjId collides with an initialObjects entry (WS-RC R3 / DEEP-BOOT-01)"
            else
              .error s!"boot: MachineConfig.physicalAddressWidth {config.machineConfig.physicalAddressWidth} > 52 (ARMv8 LPA max) (AK9-F / P-M05)"
          else
            .error "boot: MachineConfig fails well-formedness (AK9-F / P-M05)"
        else
          .error "boot: IRQ handler does not reference a notification object in initialObjects (AK9-C)"
      else
        .error "boot: two VSpace roots the boot installs share an ASID (WS-BP BP3.2)"
    else
      .error "boot: object fails bootSafe check (invalid state for boot)"
  else
    -- PR #889 review round 19 (maintainer follow-up): one branch, reading the
    -- conjunct list that `wellFormed` is pinned against.  The five-deep `else
    -- if` chain this replaces was the second enumeration that kept drifting.
    .error (wellFormedDiagnostic config)

/-- U6-E/F/AJ3-C/AK9-C/AK9-F/AK9-G + WS-RC R3: Checked boot agrees with
    `bootFromPlatformWithInterrupts` on well-formed, boot-safe,
    IRQ-handler-valid, MachineConfig-valid, PA-width-valid configs that
    do NOT install a boot VSpaceRoot.

    Precondition chain: `config.wellFormed` (AJ3-C)
    ∧ all objects are boot-safe (AJ3-C)
    ∧ every IRQ handler references a notification (AK9-C)
    ∧ `config.machineConfig.wellFormed` (AK9-F / P-M05)
    ∧ `config.machineConfig.physicalAddressWidth ≤ 52` (AK9-F / P-M05)
    ∧ `config.bootVSpaceRoot = none` (WS-RC R3 / DEEP-BOOT-01).

    The trailing precondition restricts the equality to the
    no-boot-VSpace case.  Configs that install a boot VSpaceRoot
    (RPi5 production binding) are covered by the sibling
    `bootFromPlatformChecked_admits_bootVSpace` theorem.  This split
    follows the implementation plan §7.4 R3.6: "If the unchecked
    function does not admit the root, the equality theorem becomes a
    conditional implication."

    Conclusion emits the post-interrupts state (AK9-G / P-M06) that
    the production path produces. -/
theorem bootFromPlatformChecked_eq_bootFromPlatform (config : PlatformConfig)
    (hWf : config.wellFormed = true)
    (hSafe : config.initialObjects.all (fun entry => bootSafeObjectCheck entry.obj) = true)
    (hAsids : bootVSpaceAsidsDistinct config = true)
    (hIrq : irqHandlersReferenceNotifications config = true)
    (hMc : config.machineConfig.wellFormed = true)
    (hPa : config.machineConfig.physicalAddressWidth ≤ 52)
    (hNoBootVSpace : config.bootVSpaceRoot = none) :
    bootFromPlatformChecked config =
      .ok (bootEnableInterruptsOp (bootFromPlatform config)) := by
  have hDistinct : bootVSpaceRootObjIdDistinct config = true :=
    bootVSpaceRootObjIdDistinct_none config hNoBootVSpace
  have hNonSentinel : bootVSpaceRootObjIdNonSentinel config = true :=
    bootVSpaceRootObjIdNonSentinel_none config hNoBootVSpace
  have hSafeBVR : bootVSpaceRootSafe config = true :=
    bootVSpaceRootSafe_none config hNoBootVSpace
  simp [bootFromPlatformChecked, hWf, hSafe, hAsids, hIrq, hMc, hPa,
        hDistinct, hNonSentinel, hSafeBVR, hNoBootVSpace]

/-- **WS-RC R3 (DEEP-BOOT-01)**: Checked boot with a boot VSpaceRoot
    threads `installBootVSpaceRoot` between the standard fold and the
    interrupts-enable step.  Sibling theorem to
    `bootFromPlatformChecked_eq_bootFromPlatform` for the
    `bootVSpaceRoot = some _` case.

    Precondition chain mirrors `bootFromPlatformChecked_eq_bootFromPlatform`
    plus the two new R3 gates: `bootVSpaceRootObjIdDistinct` and
    `bootVSpaceRootSafe`. -/
theorem bootFromPlatformChecked_admits_bootVSpace (config : PlatformConfig)
    (hWf : config.wellFormed = true)
    (hSafe : config.initialObjects.all (fun entry => bootSafeObjectCheck entry.obj) = true)
    (hAsids : bootVSpaceAsidsDistinct config = true)
    (hIrq : irqHandlersReferenceNotifications config = true)
    (hMc : config.machineConfig.wellFormed = true)
    (hPa : config.machineConfig.physicalAddressWidth ≤ 52)
    (hDistinct : bootVSpaceRootObjIdDistinct config = true)
    (hNonSentinel : bootVSpaceRootObjIdNonSentinel config = true)
    (hSafeBVR : bootVSpaceRootSafe config = true)
    (entry : BootVSpaceRootEntry)
    (hEntry : config.bootVSpaceRoot = some entry) :
    bootFromPlatformChecked config =
      .ok (bootEnableInterruptsOp
        (installBootVSpaceRoot (bootFromPlatform config)
          entry.id entry.root entry.hMappings)) := by
  simp [bootFromPlatformChecked, hWf, hSafe, hAsids, hIrq, hMc, hPa,
        hDistinct, hNonSentinel, hSafeBVR, hEntry]

/-- AK9-C: Successful checked boot implies IRQ handlers reference notifications.
    If `bootFromPlatformChecked` returns `.ok`, the `irqHandlersReferenceNotifications`
    predicate was true — a key witness for downstream interrupt dispatch proofs.

    WS-RC R3 audit fix: traverse the ASID gate (`bootVSpaceAsidsDistinct`, WS-BP BP3.2)
    gate that precedes `irqHandlersReferenceNotifications`. -/
theorem bootFromPlatformChecked_ok_implies_irqHandlersValid (config : PlatformConfig)
    (ist : IntermediateState)
    (hOk : bootFromPlatformChecked config = .ok ist) :
    irqHandlersReferenceNotifications config = true := by
  unfold bootFromPlatformChecked at hOk
  split at hOk
  · split at hOk
    · split at hOk
      · split at hOk
        · rename_i hIrq; exact hIrq
        · cases hOk
      · cases hOk
    · cases hOk
  · cases hOk

/-- AK9-F (P-M05): Successful checked boot implies `MachineConfig.wellFormed`.

    WS-RC R3 audit fix: traverse the ASID gate (`bootVSpaceAsidsDistinct`, WS-BP BP3.2)
    gate that precedes `machineConfig.wellFormed`. -/
theorem bootFromPlatformChecked_ok_implies_machineConfigWellFormed
    (config : PlatformConfig) (ist : IntermediateState)
    (hOk : bootFromPlatformChecked config = .ok ist) :
    config.machineConfig.wellFormed = true := by
  unfold bootFromPlatformChecked at hOk
  split at hOk
  · split at hOk
    · split at hOk
      · split at hOk
        · split at hOk
          · rename_i hMc
            -- pull the Bool out of the if-condition
            exact (by
              rcases hMcB : config.machineConfig.wellFormed with _ | _
              · simp [hMcB] at hMc
              · rfl)
          · cases hOk
        · cases hOk
      · cases hOk
    · cases hOk
  · cases hOk

/-- AK9-F (P-M05): Successful checked boot implies `physicalAddressWidth ≤ 52`.

    WS-RC R3 audit fix: traverse the ASID gate (`bootVSpaceAsidsDistinct`, WS-BP BP3.2)
    gate that precedes `physicalAddressWidth`. -/
theorem bootFromPlatformChecked_ok_implies_physicalAddressWidth_bound
    (config : PlatformConfig) (ist : IntermediateState)
    (hOk : bootFromPlatformChecked config = .ok ist) :
    config.machineConfig.physicalAddressWidth ≤ 52 := by
  unfold bootFromPlatformChecked at hOk
  split at hOk
  · split at hOk
    · split at hOk
      · split at hOk
        · split at hOk
          · split at hOk
            · rename_i hPa; exact hPa
            · cases hOk
          · cases hOk
        · cases hOk
      · cases hOk
    · cases hOk
  · cases hOk

/-- AK9-G (P-M06): Successful checked boot produces a state with interrupts
    enabled. Matches the post-HAL hardware state.

    WS-RC R3: Updated to traverse the four new boot-VSpace gates
    (`bootVSpaceAsidsDistinct`, `bootVSpaceRootObjIdDistinct`,
    `bootVSpaceRootObjIdNonSentinel`, `bootVSpaceRootSafe`) and the
    inner `match` on `config.bootVSpaceRoot`. -/
theorem bootFromPlatformChecked_ok_interruptsEnabled (config : PlatformConfig)
    (ist : IntermediateState)
    (hOk : bootFromPlatformChecked config = .ok ist) :
    ist.state.machine.interruptsEnabled = true := by
  unfold bootFromPlatformChecked at hOk
  split at hOk
  · split at hOk
    · split at hOk
      · split at hOk
        · split at hOk
          · split at hOk
            · split at hOk
              · split at hOk
                · split at hOk
                  · -- All gates pass; case on bootVSpaceRoot
                    split at hOk
                    · -- bootVSpaceRoot = none
                      cases hOk
                      exact bootEnableInterruptsOp_interruptsEnabled _
                    · -- bootVSpaceRoot = some entry
                      cases hOk
                      exact bootEnableInterruptsOp_interruptsEnabled _
                  · cases hOk
                · cases hOk
              · cases hOk
            · cases hOk
          · cases hOk
        · cases hOk
      · cases hOk
    · cases hOk
  · cases hOk

/-- U6-E/F: Checked boot rejects configs that are not well-formed. -/
theorem bootFromPlatformChecked_rejects_invalid (config : PlatformConfig)
    (hNotWf : config.wellFormed = false) :
    (bootFromPlatformChecked config).isOk = false := by
  simp [bootFromPlatformChecked, hNotWf]
  rfl

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
      exact PlatformConfig.wellFormed_irqsUnique config hWf
    simp [this]
  · -- objectIdsUnique holds when wellFormed
    have : objectIdsUnique config.initialObjects = true := by
      exact PlatformConfig.wellFormed_objectIdsUnique config hWf
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
only preserve 4 structural invariants, not the full 12-component
`proofLayerInvariantBundle`. Extending to general configs requires proving
that each builder operation preserves all 12 components — recorded as a
post-1.0 hardening candidate; registered in `docs/REGISTERED_DEBT.md`
(Registered debt index, C.1).
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
    to preserve all 12 components of `proofLayerInvariantBundle` (not just
    the 4 structural invariants). V4-A extends this to general configs. -/
theorem bootToRuntime_invariantBridge_empty :
    let ist := bootFromPlatform { irqTable := [], initialObjects := [] }
    SeLe4n.Kernel.Architecture.proofLayerInvariantBundle ist.state ∧
    SeLe4n.Model.apiInvariantBundle_frozen (SeLe4n.Model.freeze ist) :=
  ⟨emptyBoot_proofLayerInvariantBundle, emptyBoot_freeze_preserves⟩

/- Boot-to-Runtime Invariant Bridge — Known Limitation (AE5-D/U-21/PLT-01)

   `bootToRuntime_invariantBridge_empty` proves the full 12-component
   `proofLayerInvariantBundle` holds after booting with an empty
   PlatformConfig. For non-empty configs (real hardware with IRQ tables,
   pre-allocated objects), the full bundle is NOT proven to hold.

   The checked boot path `bootFromPlatformChecked` validates per-object
   well-formedness and uniqueness, but does not prove the resulting state
   satisfies all 12 runtime invariants simultaneously.

   Remediation closed by AN9 (hardware binding, DEF-A-M04 / DEF-A-M06 /
   DEF-A-M08 / DEF-A-M09) per WS-AN's closure (`docs/REGISTERED_DEBT.md`,
   workstream registry). When RPi5 boot is fully wired, either:
   (a) Prove `bootToRuntime_invariantBridge` for arbitrary well-formed
       PlatformConfig, or
   (b) Add a post-boot runtime invariant validation pass that asserts all
       12 invariants hold before enabling syscall dispatch.

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
| 11. notificationWaiterCons. | vacuous     | vacuous†     |
| 12. pendingBounded (SM7.B)  | vacuous     | vacuous      |

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
`objectIndexSet`, and `lifecycle.objectTypes`. All 12 components are preserved
because either they don't read the modified fields, or they quantify over
state structures (queues, CDT, registries, shootdown queues) that are
unmodified.

Note: `lifecycleInvariantBundle` component 5 is "substantive" because it
directly relates `objects` to `lifecycle.objectTypes`, both of which are
modified. The proof shows that the new entry is consistent.
-/

-- ============================================================================
-- V4-A2: registerIrq preserves proofLayerInvariantBundle
-- ============================================================================

/-! ### V4-A2: registerIrq Frame Lemma

`registerIrq` only modifies `st.irqHandlers`. All 12 components of
`proofLayerInvariantBundle` are independent of `irqHandlers`:

- Components 1–8 read scheduler, objects, CDT, services, serviceRegistry,
  interfaceRegistry, asidTable, lifecycle, and TLB — none of which include
  `irqHandlers`.
- Component 9 (`tlbConsistent`) reads TLB entries and objects/asidTable.
- Components 10–11 read scheduler/objects; component 12 (`pendingBounded`,
  WS-SM SM7.B) reads only `tlbShootdown`.

Therefore all 12 components are trivially preserved. -/

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
@[simp] private theorem createObject_irqHandlers (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.irqHandlers = ist.state.irqHandlers := rfl
@[simp] private theorem createObject_cdtNodeSlot (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.cdtNodeSlot = ist.state.cdtNodeSlot := rfl
@[simp] private theorem createObject_objects (ist : IntermediateState) id obj hS hM :
    (createObject ist id obj hS hM).state.objects = ist.state.objects.insert id obj := rfl

-- Step 2b (WS-BP BP3.2): per-field preservation for `createBootObject` — every
-- field but `asidTable` is `createObject`'s, and that one is `bootEntryAsidTable`.
@[simp] private theorem createBootObject_scheduler (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.scheduler = ist.state.scheduler := rfl
@[simp] private theorem createBootObject_cdt (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.cdt = ist.state.cdt := rfl
@[simp] private theorem createBootObject_services (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.services = ist.state.services := rfl
@[simp] private theorem createBootObject_serviceRegistry (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.serviceRegistry = ist.state.serviceRegistry := rfl
@[simp] private theorem createBootObject_interfaceRegistry (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.interfaceRegistry = ist.state.interfaceRegistry := rfl
@[simp] private theorem createBootObject_tlb (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.tlb = ist.state.tlb := rfl
@[simp] private theorem createBootObject_machine (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.machine = ist.state.machine := rfl
@[simp] private theorem createBootObject_irqHandlers (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.irqHandlers = ist.state.irqHandlers := rfl
@[simp] private theorem createBootObject_cdtNodeSlot (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.cdtNodeSlot = ist.state.cdtNodeSlot := rfl
@[simp] private theorem createBootObject_tlbShootdown (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.tlbShootdown = ist.state.tlbShootdown := rfl
@[simp] private theorem createBootObject_perCoreTlb (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.perCoreTlb = ist.state.perCoreTlb := rfl
@[simp] private theorem createBootObject_perCoreICache (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.perCoreICache = ist.state.perCoreICache := rfl
@[simp] private theorem createBootObject_pendingIcacheMaintenance (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.pendingIcacheMaintenance = ist.state.pendingIcacheMaintenance := rfl
@[simp] private theorem createBootObject_declassificationAuditLog (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.declassificationAuditLog = ist.state.declassificationAuditLog := rfl
@[simp] private theorem createBootObject_declassificationAuditEpoch (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.declassificationAuditEpoch = ist.state.declassificationAuditEpoch := rfl
@[simp] private theorem createBootObject_declassificationRefusals (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.declassificationRefusals = ist.state.declassificationRefusals := rfl
@[simp] private theorem createBootObject_declassificationTaint (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.declassificationTaint = ist.state.declassificationTaint := rfl
@[simp] private theorem createBootObject_objects (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.objects = ist.state.objects.insert e.id e.obj := rfl
@[simp] private theorem createBootObject_asidTable (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.asidTable = bootEntryAsidTable ist.state.asidTable e := rfl

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

private theorem foldIrqs_tlbShootdown (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.tlbShootdown = ist.state.tlbShootdown := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_perCoreTlb (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.perCoreTlb = ist.state.perCoreTlb := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_perCoreICache (irqs : List IrqEntry) (ist : IntermediateState) :
    (foldIrqs irqs ist).state.perCoreICache = ist.state.perCoreICache := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_pendingIcacheMaintenance (irqs : List IrqEntry)
    (ist : IntermediateState) :
    (foldIrqs irqs ist).state.pendingIcacheMaintenance =
      ist.state.pendingIcacheMaintenance := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_declassificationAuditLog (irqs : List IrqEntry)
    (ist : IntermediateState) :
    (foldIrqs irqs ist).state.declassificationAuditLog =
      ist.state.declassificationAuditLog := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_declassificationAuditEpoch (irqs : List IrqEntry)
    (ist : IntermediateState) :
    (foldIrqs irqs ist).state.declassificationAuditEpoch =
      ist.state.declassificationAuditEpoch := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_declassificationRefusals (irqs : List IrqEntry)
    (ist : IntermediateState) :
    (foldIrqs irqs ist).state.declassificationRefusals =
      ist.state.declassificationRefusals := by
  induction irqs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldIrqs, List.foldl] at ih ⊢; exact ih _

private theorem foldIrqs_declassificationTaint (irqs : List IrqEntry)
    (ist : IntermediateState) :
    (foldIrqs irqs ist).state.declassificationTaint =
      ist.state.declassificationTaint := by
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

/-- **WS-BP BP3.2**: the fold leaves `asidTable` alone when it installs no
    VSpace root — which is the only case the proof-layer bridge below covers
    (`bootFromPlatform_proofLayerInvariantBundle_general`'s
    `hNoVSpaceInInitial`). -/
private theorem foldObjects_asidTable (objs : List ObjectEntry) (ist : IntermediateState)
    (hNoVSpace : ∀ e ∈ objs, ∀ vs, e.obj ≠ KernelObject.vspaceRoot vs) :
    (foldObjects objs ist).state.asidTable = ist.state.asidTable := by
  induction objs generalizing ist with
  | nil => rfl
  | cons e rest ih =>
      have hStep : (createBootObject ist e).state.asidTable = ist.state.asidTable := by
        rw [createBootObject_asidTable]; unfold bootEntryAsidTable
        split
        · rename_i vs hObj
          exact absurd hObj (hNoVSpace e (List.mem_cons_self ..) vs)
        · rfl
      show (foldObjects rest (createBootObject ist e)).state.asidTable = _
      rw [ih _ (fun e' h => hNoVSpace e' (List.mem_cons_of_mem _ h)), hStep]

private theorem foldObjects_tlb (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.tlb = ist.state.tlb := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_tlbShootdown (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.tlbShootdown = ist.state.tlbShootdown := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_perCoreTlb (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.perCoreTlb = ist.state.perCoreTlb := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_perCoreICache (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.perCoreICache = ist.state.perCoreICache := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_pendingIcacheMaintenance (objs : List ObjectEntry)
    (ist : IntermediateState) :
    (foldObjects objs ist).state.pendingIcacheMaintenance =
      ist.state.pendingIcacheMaintenance := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_declassificationAuditLog (objs : List ObjectEntry)
    (ist : IntermediateState) :
    (foldObjects objs ist).state.declassificationAuditLog =
      ist.state.declassificationAuditLog := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_declassificationAuditEpoch (objs : List ObjectEntry)
    (ist : IntermediateState) :
    (foldObjects objs ist).state.declassificationAuditEpoch =
      ist.state.declassificationAuditEpoch := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_declassificationRefusals (objs : List ObjectEntry)
    (ist : IntermediateState) :
    (foldObjects objs ist).state.declassificationRefusals =
      ist.state.declassificationRefusals := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_declassificationTaint (objs : List ObjectEntry)
    (ist : IntermediateState) :
    (foldObjects objs ist).state.declassificationTaint =
      ist.state.declassificationTaint := by
  induction objs generalizing ist with
  | nil => rfl
  | cons _ _ ih => simp [foldObjects, List.foldl] at ih ⊢; exact ih _

private theorem foldObjects_machine (objs : List ObjectEntry) (ist : IntermediateState) :
    (foldObjects objs ist).state.machine = ist.state.machine := by
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

-- ============================================================================
-- WS-SM SM4.G: per-core idle-thread identities (plan §3.7)
-- ============================================================================
--
-- WS-SM SM5.E: the idle-thread *identities* (`idleThreadIdBase`, `idleThreadId`,
-- and the injectivity witnesses `idleThreadId_injective` / `_ne` /
-- `_toObjId_ne`) were moved upstream to `SeLe4n.Kernel.Scheduler.IdleThread`
-- (namespace `SeLe4n.Kernel`) so the per-core dispatcher `scheduleEffectiveOnCore`
-- (`Scheduler/Operations/Core.lean`, upstream of `Platform.Boot`) can run a
-- core's idle thread.  v0.35.68 moved the idle *TCB* there too
-- (`createIdleThread`, `queuedIdleThread`, and their field lemmas), because the
-- kernel model's enqueue (`enqueueIdleThreadOnCore`,
-- `Scheduler/Operations/IdleEnqueue.lean`) builds the TCB it stores and is now
-- what the production boot runs.  All of it resolves unqualified here via
-- `open SeLe4n.Kernel`.  Only the boot *installers* (`installIdleThread`,
-- `bootFromPlatformWithIdleThreads`, `enqueueIdleThread`) stay below — they
-- carry the `IntermediateState` witnesses through the write.

-- ============================================================================
-- WS-SM SM4.E.2: SMP-shape boot witness (replaces the retired
-- CrossSubsystem.bootFromPlatform_singleCore_witness)
-- ============================================================================

/-- **WS-SM SM4.E.2** (plan §3.8): substantive per-core boot witness — at
    boot, **every** core's current-thread slot is `none`, not just the boot
    core's.  This is the genuine SMP shape of `bootFromPlatform`'s scheduler
    after the SM4.B path-a `Vector` replacement: the freshly-booted scheduler
    holds no running thread on any of the `Concurrency.numCores` cores.

    Proved by transporting `bootFromPlatform`'s scheduler to the default
    scheduler (`bootFromPlatform_scheduler_eq`) and reading the per-core
    initialisation witness (`Model.default_state_perCoreInitialized`, the
    SM4.B.9 theorem).  Non-vacuous: it pins the actual boot value, not merely
    the `Option`-inhabitation tautology.

    This is the non-vacuous content behind the forward-compatible
    `bootFromPlatform_smp_witness` below, and it is the `sourceTheorem` that
    the AN12-B inventory entry `bootFromPlatform_currentCore_is_zero_smpLatent`
    points at after SM4.E.

    When WS-SM SM4.G (per-core idle-thread bootstrap, plan §3.7) lands, the
    *current-state* fact this theorem records evolves into
    `bootFromPlatform_all_cores_have_idle`
    (`currentOnCore c = some (idleThreadId c)`); the disjunctive
    `bootFromPlatform_smp_witness` below survives that change unchanged. -/
theorem bootFromPlatform_smp_currentAllNone
    (config : PlatformConfig) (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (bootFromPlatform config).state.scheduler.currentOnCore c = none := by
  rw [bootFromPlatform_scheduler_eq]
  exact (default_state_perCoreInitialized c).1

/-- **WS-SM SM4.E.2 / SM4.G** (plan §3.8 / §4.3): the SMP-shape boot witness
    that replaces the retired `SeLe4n.Kernel.bootFromPlatform_singleCore_witness`
    (SM4.E.1).

    The single-core witness only characterised the boot core's slot
    (`currentOnCore bootCoreId`).  SM4.B (v0.31.12) flipped
    `SchedulerState.current` to a per-core `Vector (Option ThreadId)
    Concurrency.numCores`, so the structural property worth witnessing is now
    the **per-core** one: for *every* core `c`, the boot scheduler's
    current-thread slot is either `none` (no thread bootstrapped yet) or
    `some (idleThreadId c)` — the core's **own idle thread**, never an
    arbitrary thread.  The `∀ c : CoreId` quantification proves
    `SchedulerState.current` is a per-core map (which the single slot could
    not express).

    **Non-vacuous shape (SM4.G).**  Naming `idleThreadId c` in the `some`
    disjunct makes this a genuine constraint, not the `Option`-inhabitation
    tautology `none ∨ ∃ tid, = some tid`: it *excludes* `current = some t` for
    any non-idle `t`.  Today the `none` disjunct holds on `bootFromPlatform`
    (witnessed substantively by `bootFromPlatform_smp_currentAllNone`); the
    `bootFromPlatformWithIdleThreads` boot path installs the idle threads and
    takes the `some (idleThreadId c)` disjunct (witnessed by
    `bootFromPlatformWithIdleThreads_all_cores_have_idle`).  The statement is
    identical on both paths, so this witness is **forward-compatible** and
    never needs a second retirement.  It is the `sourceTheorem` of the AN12-B
    inventory entry `architecture_singleCoreOnly_smpLatent` and the `anchor`
    of the `smpRetiredInventory` entry for `Architecture.ArchAssumption`. -/
theorem bootFromPlatform_smp_witness
    (config : PlatformConfig) (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (bootFromPlatform config).state.scheduler.currentOnCore c = none ∨
      (bootFromPlatform config).state.scheduler.currentOnCore c = some (idleThreadId c) :=
  Or.inl (bootFromPlatform_smp_currentAllNone config c)

-- ============================================================================
-- WS-SM SM4.G: per-core idle-thread bootstrap (plan §3.7)
-- ============================================================================

-- The idle TCB (`createIdleThread`, the dispatched form; `queuedIdleThread`, the
-- enqueued form) is defined in `SeLe4n.Kernel.Scheduler.IdleThread` since
-- v0.35.68 — see the banner above.

/-- **WS-SM SM4.G** (plan §3.7): install core `c`'s idle thread into a boot
    `IntermediateState` — create the idle TCB in the object store (via the
    builder, so every structural invariant carries forward exactly as for
    `installBootVSpaceRoot`) and set the scheduler's per-core current slot to
    the idle thread.

    The `.tcb` object discharges both `createObject` obligations vacuously
    (`.tcb _` is neither a `.cnode` nor a `.vspaceRoot`).  The scheduler
    `setCurrentOnCore` update does not touch `objects` / `cdt` / `lifecycle`,
    so the `IntermediateState` invariant witnesses forward unchanged (the
    `applyMachineConfig` pattern — they do not depend on scheduler fields). -/
def installIdleThread (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) : IntermediateState :=
  let withTcb : IntermediateState :=
    Builder.createObject ist (idleThreadId c).toObjId
      (KernelObject.tcb (createIdleThread c))
      (fun _ hEq => by cases hEq) (fun _ hEq => by cases hEq)
  { state := { withTcb.state with
      scheduler := withTcb.state.scheduler.setCurrentOnCore c (some (idleThreadId c)) }
    hAllTables := withTcb.hAllTables
    hPerObjectSlots := withTcb.hPerObjectSlots
    hPerObjectMappings := withTcb.hPerObjectMappings
    hLifecycleConsistent := withTcb.hLifecycleConsistent }

/-- **WS-SM SM4.G**: `installIdleThread` inserts the idle TCB into the object
    store (definitional — the scheduler-update record update leaves `objects`
    untouched). -/
theorem installIdleThread_objects (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (installIdleThread ist c).state.objects =
      ist.state.objects.insert (idleThreadId c).toObjId
        (KernelObject.tcb (createIdleThread c)) := rfl

/-- **WS-SM SM4.G**: `installIdleThread` sets core `c`'s current slot
    (definitional — `createObject` preserves the scheduler). -/
theorem installIdleThread_scheduler (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (installIdleThread ist c).state.scheduler =
      ist.state.scheduler.setCurrentOnCore c (some (idleThreadId c)) := rfl

/-- **WS-SM SM4.G**: after installing core `c`'s idle thread, `c`'s current
    slot reads the idle thread. -/
theorem installIdleThread_currentOnCore_self (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (installIdleThread ist c).state.scheduler.currentOnCore c = some (idleThreadId c) := by
  rw [installIdleThread_scheduler]
  exact SchedulerState.setCurrentOnCore_currentOnCore_self _ _ _

/-- **WS-SM SM4.G**: installing core `c`'s idle thread frames any *other*
    core `c'`'s current slot. -/
theorem installIdleThread_currentOnCore_ne (ist : IntermediateState)
    (c c' : SeLe4n.Kernel.Concurrency.CoreId) (h : c ≠ c') :
    (installIdleThread ist c).state.scheduler.currentOnCore c' =
      ist.state.scheduler.currentOnCore c' := by
  rw [installIdleThread_scheduler]
  exact SchedulerState.setCurrentOnCore_currentOnCore_ne _ c c' _ h

/-- **WS-SM SM4.G**: after installing core `c`'s idle thread, its object-store
    slot holds the idle TCB. -/
theorem installIdleThread_objects_self (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (installIdleThread ist c).state.objects[(idleThreadId c).toObjId]? =
      some (KernelObject.tcb (createIdleThread c)) := by
  rw [installIdleThread_objects]
  have hObjK : ist.state.objects.invExtK := ist.hAllTables.1
  exact RHTable.getElem?_insert_self ist.state.objects (idleThreadId c).toObjId _ hObjK.1

/-- **WS-SM SM4.G**: installing core `c`'s idle thread frames the object-store
    slot of any *distinct* ObjId. -/
theorem installIdleThread_objects_ne (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (oid : SeLe4n.ObjId)
    (h : (idleThreadId c).toObjId ≠ oid) :
    (installIdleThread ist c).state.objects[oid]? = ist.state.objects[oid]? := by
  rw [installIdleThread_objects]
  have hObjK : ist.state.objects.invExtK := ist.hAllTables.1
  have hNe : ¬(((idleThreadId c).toObjId == oid) = true) := fun heq => h (eq_of_beq heq)
  exact RHTable.getElem?_insert_ne ist.state.objects (idleThreadId c).toObjId oid _ hNe hObjK.1

/-- **WS-SM SM4.G** (plan §3.7): the SMP boot path — `bootFromPlatform`
    followed by installing a per-core idle thread on every core in
    `allCores`.  Each core's current slot becomes its own idle thread; the
    object store gains the per-core idle TCBs.  This is the path on which the
    `some (idleThreadId c)` disjunct of `bootFromPlatform_smp_witness` is the
    live one (witnessed by `bootFromPlatformWithIdleThreads_all_cores_have_idle`).

    Defined as a wrapper (analogous to `bootFromPlatformWithInterrupts`) so the
    base `bootFromPlatform` — and its entire verified invariant surface — is
    left unchanged.

    **SM5 integration scope (WS-RR RR5: two of the three closed).**  This
    wrapper was forward-looking infrastructure with no production caller, and
    its docstring named three consequences deferred to SM5.  RR5 closed the
    first two — through a *different* operation, for a reason worth recording:

    1. **Not on the checked boot path — CLOSED at RR5.14, and not by this
       wrapper.**  The production entry is now
       `bootFromPlatformCheckedWithIdleThreads`, which folds `enqueueIdleThread`
       rather than `installIdleThread`.  The difference is load-bearing: this
       wrapper points each core's *current* slot at its idle thread without
       putting it on any run queue, so on the state it produces
       `idleThreadEnqueuedOnCore` — the premise
       `chooseThreadOnCore_always_succeeds` consumes and `schedulerNoStall_smp`
       takes by hypothesis — is **false on every core**, and dispatching a
       thread that is also queued would violate `queueCurrentConsistent`.
       Enqueue-without-dispatch is the correct boot posture; this wrapper
       remains the SM4.G install-and-dispatch form and is not production.
    2. **Boot-core-only thread-state inference — CLOSED at RR5.10.**
       `Scheduler.Operations.Core.inferThreadState` / `syncThreadStates` read
       only `currentOnCore bootCoreId` / `runQueueOnCore bootCoreId`, so a
       *secondary* core's idle TCB (created `.Running`) would be re-inferred as
       `.Inactive` by a sync, even though that core's own slot points at it.
       They now ask every core (`threadRunningOnSomeCore` /
       `threadQueuedOnSomeCore`), conservatively on every state the old
       definition classified
       (`inferThreadState_eq_bootCore_of_secondaries_quiescent`).
    3. **Idle TCBs are not `KernelObject.wellFormed`.**  `createIdleThread`
       uses `ObjId.sentinel` for `cspaceRoot` / `vspaceRoot` (idle runs in
       kernel context with no user caps — seL4 idle-thread semantics), so the
       idle TCB fails `KernelObject.wellFormed` (which requires both roots to
       resolve).  That predicate is a **retype-time precondition**
       (`Lifecycle/Operations/RetypeWrappers.lean`), **not** a global
       invariant, and idle TCBs are builder-installed — never retyped — so
       there is **no current contract violation** and no system invariant is
       broken.  SM5, when wiring idle through any `wellFormed`-checked path,
       either installs valid idle roots or formalises an explicit idle-thread
       exemption in `KernelObject.wellFormed`. -/
def bootFromPlatformWithIdleThreads (config : PlatformConfig) : IntermediateState :=
  SeLe4n.Kernel.Concurrency.allCores.foldl installIdleThread (bootFromPlatform config)

/-- **WS-SM SM4.G**: folding `installIdleThread` over a list of cores all
    distinct from `c` frames core `c`'s current slot. -/
theorem foldl_installIdleThread_currentOnCore_frame
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (h : ∀ c' ∈ L, c' ≠ c) :
    (L.foldl installIdleThread ist).state.scheduler.currentOnCore c =
      ist.state.scheduler.currentOnCore c := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (installIdleThread ist x) (fun c' hc' => h c' (List.mem_cons.mpr (Or.inr hc')))]
    exact installIdleThread_currentOnCore_ne ist x c (h x (List.mem_cons.mpr (Or.inl rfl)))

/-- **WS-SM SM4.G**: folding `installIdleThread` over a list of cores all
    distinct from `c` frames core `c`'s idle-object slot. -/
theorem foldl_installIdleThread_objects_frame
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (h : ∀ c' ∈ L, c' ≠ c) :
    (L.foldl installIdleThread ist).state.objects[(idleThreadId c).toObjId]? =
      ist.state.objects[(idleThreadId c).toObjId]? := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (installIdleThread ist x) (fun c' hc' => h c' (List.mem_cons.mpr (Or.inr hc')))]
    exact installIdleThread_objects_ne ist x (idleThreadId c).toObjId
      (idleThreadId_toObjId_ne (h x (List.mem_cons.mpr (Or.inl rfl))))

/-- **WS-SM SM4.G**: folding `installIdleThread` over a `Nodup` list `L`
    containing `c` installs `c`'s idle thread — both the per-core current slot
    and the object-store entry hold the idle thread after the whole fold.
    `c`'s install step is preserved by every later step (which targets a
    distinct core, by `Nodup`), via the two frame lemmas. -/
theorem foldl_installIdleThread_installs
    (c : SeLe4n.Kernel.Concurrency.CoreId) (L : List SeLe4n.Kernel.Concurrency.CoreId)
    (ist : IntermediateState) :
    L.Nodup → c ∈ L →
    (L.foldl installIdleThread ist).state.scheduler.currentOnCore c = some (idleThreadId c) ∧
    (L.foldl installIdleThread ist).state.objects[(idleThreadId c).toObjId]? =
      some (KernelObject.tcb (createIdleThread c)) := by
  induction L generalizing ist with
  | nil => intro _ hc; exact (List.not_mem_nil hc).elim
  | cons x xs ih =>
    intro hnd hc
    simp only [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hc with hxc | hxs
    · -- `c = x`: installed by the head step; the (distinct) tail frames it.
      subst hxc
      have hframe : ∀ c' ∈ xs, c' ≠ c := fun c' hc' heq => hnd.1 (heq ▸ hc')
      refine ⟨?_, ?_⟩
      · rw [foldl_installIdleThread_currentOnCore_frame xs (installIdleThread ist c) c hframe]
        exact installIdleThread_currentOnCore_self ist c
      · rw [foldl_installIdleThread_objects_frame xs (installIdleThread ist c) c hframe]
        exact installIdleThread_objects_self ist c
    · -- `c ∈ xs`: the tail fold installs it (induction hypothesis).
      exact ih (installIdleThread ist x) hnd.2 hxs

/-- **WS-SM SM4.G** (plan §3.7, Theorem 3.7.1): on the SMP boot path, **every**
    core's current slot holds its own idle thread and the idle TCB is present
    in the object store.  This is the fully-substantive `some (idleThreadId c)`
    witness — the live branch of `bootFromPlatform_smp_witness` on the
    idle-thread boot path.  Holds unconditionally (the per-core idle ObjIds are
    distinct by `idleThreadId_injective`, and `createObject`'s insert makes the
    idle TCB present regardless of the base config). -/
theorem bootFromPlatformWithIdleThreads_all_cores_have_idle (config : PlatformConfig)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (bootFromPlatformWithIdleThreads config).state.scheduler.currentOnCore c =
        some (idleThreadId c) ∧
    (bootFromPlatformWithIdleThreads config).state.objects[(idleThreadId c).toObjId]? =
      some (KernelObject.tcb (createIdleThread c)) := by
  unfold bootFromPlatformWithIdleThreads
  exact foldl_installIdleThread_installs c SeLe4n.Kernel.Concurrency.allCores
    (bootFromPlatform config) SeLe4n.Kernel.Concurrency.allCores_nodup (List.mem_finRange c)

/-- **WS-SM SM4.G** (plan §3.7): the per-core idle `ObjId` slots are *fresh*
    (unoccupied) in intermediate state `ist` — no object already lives at any
    idle thread's `ObjId`.  This is the precondition under which the idle-thread
    install is purely additive (overwrites nothing): `createObject` uses
    `RHTable.insert`, which overwrites on key collision, so installing an idle
    thread at an already-occupied slot would silently clobber the prior object.
    The canonical platforms discharge `idleSlotsFreshAt` because their config
    objects live below `idleThreadIdBase` (witnessed generally by
    `idleSlotsFreshAt_of_initialObjects_below_base`). -/
def idleSlotsFreshAt (ist : IntermediateState) : Prop :=
  ∀ c : SeLe4n.Kernel.Concurrency.CoreId,
    ist.state.objects[(idleThreadId c).toObjId]? = none

/-- **WS-SM SM4.G**: folding `installIdleThread` over a list of cores frames any
    `ObjId` `oid` distinct from *every* idle slot the fold touches.  Generalises
    `foldl_installIdleThread_objects_frame` (which fixed `oid` to a particular
    core's idle slot) to an arbitrary non-idle `oid`. -/
theorem foldl_installIdleThread_objects_frame_of_not_idle
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (oid : SeLe4n.ObjId)
    (h : ∀ c' ∈ L, (idleThreadId c').toObjId ≠ oid) :
    (L.foldl installIdleThread ist).state.objects[oid]? = ist.state.objects[oid]? := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (installIdleThread ist x) (fun c' hc' => h c' (List.mem_cons.mpr (Or.inr hc')))]
    exact installIdleThread_objects_ne ist x oid (h x (List.mem_cons.mpr (Or.inl rfl)))

/-- **WS-SM SM4.G** (plan §3.7): under `idleSlotsFreshAt`, the idle-thread
    install fold preserves *every* platform object — no platform object is
    silently overwritten by an idle TCB.  This substantiates the
    `idleThreadIdBase` disjointness rationale: when the platform config's objects
    do not occupy any idle slot (the canonical case, since config objects live
    below the 16-bit `idleThreadIdBase`), the idle install is purely additive.
    Without freshness the install theorems still hold (`…_all_cores_have_idle`
    is unconditional), but a config object placed in the idle range would be
    clobbered — which this theorem's hypothesis rules out. -/
theorem bootFromPlatformWithIdleThreads_preserves_platform_objects
    (config : PlatformConfig)
    (hFresh : idleSlotsFreshAt (bootFromPlatform config))
    (oid : SeLe4n.ObjId) (o : KernelObject)
    (hPlat : (bootFromPlatform config).state.objects[oid]? = some o) :
    (bootFromPlatformWithIdleThreads config).state.objects[oid]? = some o := by
  unfold bootFromPlatformWithIdleThreads
  rw [foldl_installIdleThread_objects_frame_of_not_idle SeLe4n.Kernel.Concurrency.allCores
    (bootFromPlatform config) oid (fun c' _ hEq => ?_)]
  · exact hPlat
  · -- If `oid` were an idle slot, freshness (`= none`) would contradict `hPlat`.
    have hAt : (bootFromPlatform config).state.objects[(idleThreadId c').toObjId]? = some o := by
      rw [hEq]; exact hPlat
    rw [hFresh c'] at hAt
    simp at hAt

/-- **WS-SM SM4.G**: `installIdleThread` (via `setCurrentOnCore`) frames every
    core's run queue — idle install only writes current slots. -/
theorem installIdleThread_runQueueOnCore (ist : IntermediateState)
    (c c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (installIdleThread ist c).state.scheduler.runQueueOnCore c' =
      ist.state.scheduler.runQueueOnCore c' := by
  rw [installIdleThread_scheduler]
  exact SchedulerState.setCurrentOnCore_runQueueOnCore _ _ _ _

/-- **WS-SM SM4.G**: the idle-thread install fold frames every core's run
    queue. -/
theorem foldl_installIdleThread_runQueueOnCore
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (L.foldl installIdleThread ist).state.scheduler.runQueueOnCore c =
      ist.state.scheduler.runQueueOnCore c := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (installIdleThread ist x)]
    exact installIdleThread_runQueueOnCore ist x c

/-- **WS-SM SM4.G**: the SMP idle-thread boot path leaves the boot-core run
    queue empty (idle threads are dispatched as `current`, not enqueued — the
    dequeue-on-dispatch discipline `queueCurrentConsistent` encodes). -/
theorem bootFromPlatformWithIdleThreads_runnable_nil (config : PlatformConfig) :
    (bootFromPlatformWithIdleThreads config).state.scheduler.runnable = [] := by
  show ((bootFromPlatformWithIdleThreads config).state.scheduler.runQueueOnCore
        SeLe4n.Kernel.Concurrency.bootCoreId).toList = []
  unfold bootFromPlatformWithIdleThreads
  rw [foldl_installIdleThread_runQueueOnCore, bootFromPlatform_scheduler_eq]
  have h : (default : SystemState).scheduler.runQueueOnCore
      SeLe4n.Kernel.Concurrency.bootCoreId = SeLe4n.Kernel.RunQueue.empty :=
    (default_state_perCoreInitialized SeLe4n.Kernel.Concurrency.bootCoreId).2.1
  rw [h]
  exact SeLe4n.Kernel.RunQueue.toList_empty

/-- **WS-SM SM4.G**: soundness of the idle-thread boot path — the installed
    state satisfies the scheduler invariant bundle.  The boot-core current
    thread is the idle thread, which is a valid TCB in the object store
    (`currentThreadValid`), is not in the (empty) run queue
    (`queueCurrentConsistent` / dequeue-on-dispatch), and the empty run queue
    is duplicate-free (`runQueueUnique`).  Confirms that installing an idle
    thread as `current` yields a scheduler-valid state — no dangling current
    reference, no double-scheduling. -/
theorem bootFromPlatformWithIdleThreads_schedulerInvariantBundle (config : PlatformConfig) :
    SeLe4n.Kernel.schedulerInvariantBundle (bootFromPlatformWithIdleThreads config).state := by
  have hCur := bootFromPlatformWithIdleThreads_all_cores_have_idle config
    SeLe4n.Kernel.Concurrency.bootCoreId
  have hNil := bootFromPlatformWithIdleThreads_runnable_nil config
  refine ⟨?_, ?_, ?_⟩
  · -- queueCurrentConsistent: idle thread is not in the (empty) run queue.
    simp only [SeLe4n.Kernel.queueCurrentConsistent, hCur.1, hNil, List.not_mem_nil,
      not_false_eq_true]
  · -- runQueueUnique: the empty run queue is duplicate-free.
    simp only [SeLe4n.Kernel.runQueueUnique, hNil, List.nodup_nil]
  · -- currentThreadValid: the idle thread resolves to a TCB in the store.
    simp only [SeLe4n.Kernel.currentThreadValid, hCur.1]
    exact ⟨createIdleThread SeLe4n.Kernel.Concurrency.bootCoreId, hCur.2⟩

/-- **WS-SM SM4.G**: the idle-thread boot path preserves the four structural
    boot invariants — the idle TCBs are added via `Builder.createObject`,
    exactly as platform objects, so `allTablesInvExtK`, per-object CNode slots,
    per-object VSpace mappings, and lifecycle metadata all carry forward
    (the `IntermediateState` witnesses thread through the scheduler update by
    defeq).  Mirrors `bootFromPlatform_valid`. -/
theorem bootFromPlatformWithIdleThreads_valid (config : PlatformConfig) :
    let ist := bootFromPlatformWithIdleThreads config
    ist.state.allTablesInvExtK ∧
    perObjectSlotsInvariant ist.state ∧
    perObjectMappingsInvariant ist.state ∧
    SystemState.objectTypeMetadataConsistent ist.state :=
  ⟨(bootFromPlatformWithIdleThreads config).hAllTables,
   (bootFromPlatformWithIdleThreads config).hPerObjectSlots,
   (bootFromPlatformWithIdleThreads config).hPerObjectMappings,
   (bootFromPlatformWithIdleThreads config).hLifecycleConsistent⟩

/-- **WS-SM SM4.G**: `installIdleThread` frames the machine state (it touches
    only `objects` and the scheduler's current slot — `applyMachineConfig`
    pattern). -/
theorem installIdleThread_machine (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (installIdleThread ist c).state.machine = ist.state.machine := rfl

/-- **WS-SM SM4.G**: the install fold frames the machine state. -/
theorem foldl_installIdleThread_machine
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState) :
    (L.foldl installIdleThread ist).state.machine = ist.state.machine := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (installIdleThread ist x)]
    exact installIdleThread_machine ist x

/-- **WS-SM SM4.G**: the install fold frames every core's domain-time-remaining
    slot (idle install writes only the current slot). -/
theorem foldl_installIdleThread_domainTimeRemainingOnCore
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (L.foldl installIdleThread ist).state.scheduler.domainTimeRemainingOnCore c =
      ist.state.scheduler.domainTimeRemainingOnCore c := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (installIdleThread ist x), installIdleThread_scheduler]
    exact SchedulerState.setCurrentOnCore_domainTimeRemainingOnCore _ _ _ _

/-- **WS-SM SM4.G**: the install fold frames every core's active-domain slot. -/
theorem foldl_installIdleThread_activeDomainOnCore
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (L.foldl installIdleThread ist).state.scheduler.activeDomainOnCore c =
      ist.state.scheduler.activeDomainOnCore c := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (installIdleThread ist x), installIdleThread_scheduler]
    exact SchedulerState.setCurrentOnCore_activeDomainOnCore _ _ _ _

/-- **WS-SM SM4.G**: the install fold frames the (system-wide) domain
    schedule. -/
theorem foldl_installIdleThread_domainSchedule
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState) :
    (L.foldl installIdleThread ist).state.scheduler.domainSchedule =
      ist.state.scheduler.domainSchedule := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (installIdleThread ist x), installIdleThread_scheduler]
    exact SchedulerState.setCurrentOnCore_domainSchedule _ _ _

-- ============================================================================
-- WS-RR RR5.11: the idle **run-queue** enqueue, at `IntermediateState` level
-- ============================================================================

/-- **WS-RR RR5.11**: install core `c`'s idle TCB into a boot `IntermediateState`
    and **enqueue it on core `c`'s own run queue** — by running the kernel
    model's own enqueue, `enqueueIdleThreadOnCore`
    (`Scheduler/Operations/IdleEnqueue.lean`), on the intermediate state's
    `state`, and carrying the four structural witnesses through it with that
    operation's own preservation theorems.

    **One body, not two** (`v0.35.68`).  Until then this was a second
    implementation of the same operation — `Builder.createObject` for the TCB
    and a hand-written run-queue write — held to the kernel model's by a
    docstring sentence ("mirrors `enqueueIdleThreadOnCore` … definitionally
    parallel"), which was true of `objects` and the run queue and false of the
    bookkeeping: the builder skips `asidTable`, the store (`withObjectStored`)
    maintains it — and, until `v0.35.78` retired it, the capability-reference
    table too.  On a successful checked boot the ASID write is inert — an idle
    slot is fresh (`bootFromPlatformChecked_ok_idleSlotsFreshAt`) — so the
    derivation
    changes no boot state, which is exactly the case in which a derivation is
    taken rather than a pin.  `enqueueIdleThread_state` is the definitional
    equation; every frame below is an instance of the kernel model's.

    The operation `installIdleThread` is not this.  That one creates the idle
    TCB and points core `c`'s *current* slot at it; it never touches
    `runQueueOnCore`, so on the state it produces `idleThreadEnqueuedOnCore` —
    the premise `chooseThreadOnCore_always_succeeds` consumes and
    `schedulerNoStall_smp` takes by hypothesis — is **false** on every core.

    **It deliberately does not write `currentOnCore`.**  Writing both would make
    the boot state violate `queueCurrentConsistent`, which says a core's current
    thread is *not* also queued — the dequeue-on-dispatch discipline.  Enqueuing
    without dispatching is the correct boot posture: every core comes up with a
    dispatchable idle thread waiting, and the core's first scheduling point
    (`chooseThreadOnCore`, reached from its bring-up reschedule or its first
    timer tick) selects it, dequeues it and sets `current`.  The alternative —
    dispatching idle at boot without enqueuing it — is what `installIdleThread`
    does, and it is exactly the state on which the no-stall premise fails.

    The stored TCB is the **queued** form `queuedIdleThread`, whose `threadState`
    is `.Ready`, because a thread on a run queue and in no current slot is what
    the classification calls `.Ready` (PR #889 review). -/
def enqueueIdleThread (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) : IntermediateState where
  state := enqueueIdleThreadOnCore ist.state c
  hAllTables := enqueueIdleThreadOnCore_preserves_allTablesInvExtK ist.state c ist.hAllTables
  hPerObjectSlots := enqueueIdleThreadOnCore_preserves_perObjectSlotsInvariant ist.state c
    ist.hAllTables.1.1 ist.hPerObjectSlots
  hPerObjectMappings := enqueueIdleThreadOnCore_preserves_perObjectMappingsInvariant ist.state c
    ist.hAllTables.1.1 ist.hPerObjectMappings
  hLifecycleConsistent := enqueueIdleThreadOnCore_preserves_objectTypeMetadataConsistent
    ist.state c ist.hAllTables ist.hLifecycleConsistent

/-- **v0.35.68** (the derivation, pinned): the boot's idle install *is* the
    kernel model's enqueue on the intermediate state's `state`.  Definitional —
    and decisive: a second body here, however faithfully it mirrored the
    kernel model's, would not be `rfl` to it. -/
theorem enqueueIdleThread_state (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (enqueueIdleThread ist c).state = enqueueIdleThreadOnCore ist.state c := rfl

/-- **WS-RR RR5.11** (frame): the enqueue's object-store write — the kernel
    model's `enqueueIdleThreadOnCore_objects`, at the boot's state. -/
theorem enqueueIdleThread_objects (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (enqueueIdleThread ist c).state.objects =
      ist.state.objects.insert (idleThreadId c).toObjId
        (KernelObject.tcb (queuedIdleThread c)) :=
  enqueueIdleThreadOnCore_objects ist.state c

/-- **WS-RR RR5.11** (frame): the enqueue's scheduler write — the kernel model's
    `enqueueIdleThreadOnCore_scheduler`, at the boot's state. -/
theorem enqueueIdleThread_scheduler (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (enqueueIdleThread ist c).state.scheduler =
      ist.state.scheduler.setRunQueueOnCore c
        (((ist.state.scheduler.runQueueOnCore c).remove (idleThreadId c)).insert
          (idleThreadId c) (queuedIdleThread c).priority) :=
  enqueueIdleThreadOnCore_scheduler ist.state c

/-- **WS-RR RR5.11**: after the enqueue, core `c`'s run queue is the old one with
    idle `c` inserted at priority `0`. -/
theorem enqueueIdleThread_runQueueOnCore_self (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (enqueueIdleThread ist c).state.scheduler.runQueueOnCore c =
      ((ist.state.scheduler.runQueueOnCore c).remove (idleThreadId c)).insert
        (idleThreadId c) (queuedIdleThread c).priority :=
  enqueueIdleThreadOnCore_runQueueOnCore_self ist.state c

/-- **WS-RR RR5.11** (cross-core frame, the analogue of
    `installIdleThread_currentOnCore_ne`): enqueuing idle `c` leaves every
    *other* core's run queue untouched — core `c`'s idle thread never appears on
    core `c'`'s queue.  Together with `idleThread_core_locality` this is what
    keeps the per-core affinity invariant true of the boot state. -/
theorem enqueueIdleThread_runQueueOnCore_ne (ist : IntermediateState)
    (c c' : SeLe4n.Kernel.Concurrency.CoreId) (h : c ≠ c') :
    (enqueueIdleThread ist c).state.scheduler.runQueueOnCore c' =
      ist.state.scheduler.runQueueOnCore c' :=
  enqueueIdleThreadOnCore_runQueueOnCore_ne ist.state c c' h

/-- **WS-RR RR5.11** (frame): the enqueue writes no core's *current* slot.  This
    is the frame that keeps `queueCurrentConsistent` true of the boot state — see
    the definition's docstring for why enqueuing without dispatching is the
    correct boot posture. -/
theorem enqueueIdleThread_currentOnCore (ist : IntermediateState)
    (c c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (enqueueIdleThread ist c).state.scheduler.currentOnCore c' =
      ist.state.scheduler.currentOnCore c' :=
  enqueueIdleThreadOnCore_currentOnCore ist.state c c'

/-- **WS-RR RR5.11** (frame): the enqueue writes no core's active domain. -/
theorem enqueueIdleThread_activeDomainOnCore (ist : IntermediateState)
    (c c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (enqueueIdleThread ist c).state.scheduler.activeDomainOnCore c' =
      ist.state.scheduler.activeDomainOnCore c' :=
  enqueueIdleThreadOnCore_activeDomainOnCore ist.state c c'

/-- **WS-RR RR5.11** (frame): the enqueue frames the machine state. -/
theorem enqueueIdleThread_machine (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (enqueueIdleThread ist c).state.machine = ist.state.machine :=
  enqueueIdleThreadOnCore_machine ist.state c

/-- **WS-RR RR5.11**: after the enqueue, core `c`'s idle slot holds the idle
    TCB — the analogue of `installIdleThread_objects_self`. -/
theorem enqueueIdleThread_objects_self (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (enqueueIdleThread ist c).state.objects[(idleThreadId c).toObjId]? =
      some (KernelObject.tcb (queuedIdleThread c)) :=
  enqueueIdleThreadOnCore_objects_self ist.state c ist.hAllTables.1.1

/-- **WS-RR RR5.11**: the enqueue frames the object-store slot of any *distinct*
    ObjId — the analogue of `installIdleThread_objects_ne`. -/
theorem enqueueIdleThread_objects_ne (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (oid : SeLe4n.ObjId)
    (h : (idleThreadId c).toObjId ≠ oid) :
    (enqueueIdleThread ist c).state.objects[oid]? = ist.state.objects[oid]? :=
  enqueueIdleThreadOnCore_objects_ne ist.state c oid ist.hAllTables.1.1 h

/-- **WS-RR RR5.11** (fold frame): folding `enqueueIdleThread` over a list of
    cores all distinct from `c` frames core `c`'s run queue. -/
theorem foldl_enqueueIdleThread_runQueueOnCore_frame
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (h : ∀ c' ∈ L, c' ≠ c) :
    (L.foldl enqueueIdleThread ist).state.scheduler.runQueueOnCore c =
      ist.state.scheduler.runQueueOnCore c := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (enqueueIdleThread ist x) (fun c' hc' => h c' (List.mem_cons.mpr (Or.inr hc')))]
    exact enqueueIdleThread_runQueueOnCore_ne ist x c (h x (List.mem_cons.mpr (Or.inl rfl)))

/-- **WS-RR RR5.11** (fold frame): the fold frames core `c`'s idle object slot
    when no step targets `c`. -/
theorem foldl_enqueueIdleThread_objects_frame
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (h : ∀ c' ∈ L, c' ≠ c) :
    (L.foldl enqueueIdleThread ist).state.objects[(idleThreadId c).toObjId]? =
      ist.state.objects[(idleThreadId c).toObjId]? := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (enqueueIdleThread ist x) (fun c' hc' => h c' (List.mem_cons.mpr (Or.inr hc')))]
    exact enqueueIdleThread_objects_ne ist x (idleThreadId c).toObjId
      (idleThreadId_toObjId_ne (h x (List.mem_cons.mpr (Or.inl rfl))))

/-- **WS-RR RR5.11** (fold frame): the fold writes no core's current slot, at
    any length.  This is what carries `queueCurrentConsistent` through the whole
    boot install — see `enqueueIdleThread`'s docstring. -/
theorem foldl_enqueueIdleThread_currentOnCore
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (L.foldl enqueueIdleThread ist).state.scheduler.currentOnCore c =
      ist.state.scheduler.currentOnCore c := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (enqueueIdleThread ist x)]
    exact enqueueIdleThread_currentOnCore ist x c

/-- **WS-RR RR5.11** (fold frame): the fold writes no core's active domain. -/
theorem foldl_enqueueIdleThread_activeDomainOnCore
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (L.foldl enqueueIdleThread ist).state.scheduler.activeDomainOnCore c =
      ist.state.scheduler.activeDomainOnCore c := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (enqueueIdleThread ist x)]
    exact enqueueIdleThread_activeDomainOnCore ist x c

/-- **WS-RR RR5.11** (fold frame): the fold frames the machine state. -/
theorem foldl_enqueueIdleThread_machine
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState) :
    (L.foldl enqueueIdleThread ist).state.machine = ist.state.machine := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (enqueueIdleThread ist x)]
    exact enqueueIdleThread_machine ist x

/-- **WS-RR RR5.11** (fold frame): the fold frames any `ObjId` distinct from
    every idle slot it touches.  Generalises `foldl_enqueueIdleThread_objects_frame`
    to an arbitrary non-idle key, and is what shows the enqueue is purely
    additive over the platform's own objects. -/
theorem foldl_enqueueIdleThread_objects_frame_of_not_idle
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (oid : SeLe4n.ObjId)
    (h : ∀ c' ∈ L, (idleThreadId c').toObjId ≠ oid) :
    (L.foldl enqueueIdleThread ist).state.objects[oid]? = ist.state.objects[oid]? := by
  induction L generalizing ist with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (enqueueIdleThread ist x) (fun c' hc' => h c' (List.mem_cons.mpr (Or.inr hc')))]
    exact enqueueIdleThread_objects_ne ist x oid (h x (List.mem_cons.mpr (Or.inl rfl)))

/-- **WS-RR RR8.16** (the fold at an arbitrary key): every object the fold's store
    holds is either the pre-fold store's object at that key or one of the idle TCBs
    the fold installs.

    The three lemmas above frame a key the fold does not touch; this one says what
    the fold *can* leave there, which is what a per-TCB statement about the
    production boot state needs — a case analysis over one key, with no `Nodup`
    hypothesis, because it asserts nothing about *which* core's idle thread a
    matching key belongs to. -/
theorem foldl_enqueueIdleThread_objects_cases
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (oid : SeLe4n.ObjId) (obj : KernelObject)
    (h : (L.foldl enqueueIdleThread ist).state.objects[oid]? = some obj) :
    ist.state.objects[oid]? = some obj ∨
      ∃ c ∈ L, obj = KernelObject.tcb (queuedIdleThread c) := by
  induction L generalizing ist with
  | nil => exact Or.inl h
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    rcases ih (enqueueIdleThread ist x) h with hStep | ⟨c, hc, hEq⟩
    · by_cases hKey : (idleThreadId x).toObjId = oid
      · subst hKey
        rw [enqueueIdleThread_objects_self ist x] at hStep
        exact Or.inr ⟨x, List.mem_cons_self .., by injection hStep with hStep; exact hStep.symm⟩
      · rw [enqueueIdleThread_objects_ne ist x oid hKey] at hStep
        exact Or.inl hStep
    · exact Or.inr ⟨c, List.mem_cons.mpr (Or.inr hc), hEq⟩

/-- **WS-RR RR5.11** (the fold's payoff, mirroring
    `foldl_installIdleThread_installs`): folding `enqueueIdleThread` over a
    `Nodup` list containing `c` leaves core `c`'s idle thread **on core `c`'s own
    run queue** and **in the object store**.  `c`'s step establishes both; every
    later step targets a distinct core (by `Nodup`) and frames them. -/
theorem foldl_enqueueIdleThread_installs
    (c : SeLe4n.Kernel.Concurrency.CoreId) (L : List SeLe4n.Kernel.Concurrency.CoreId)
    (ist : IntermediateState) :
    L.Nodup → c ∈ L →
    idleThreadId c ∈
      ((L.foldl enqueueIdleThread ist).state.scheduler.runQueueOnCore c).toList ∧
    (L.foldl enqueueIdleThread ist).state.objects[(idleThreadId c).toObjId]? =
      some (KernelObject.tcb (queuedIdleThread c)) := by
  induction L generalizing ist with
  | nil => intro _ hc; exact (List.not_mem_nil hc).elim
  | cons x xs ih =>
    intro hnd hc
    simp only [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hc with hxc | hxs
    · -- `c = x`: enqueued by the head step; the (distinct) tail frames it.
      subst hxc
      have hframe : ∀ c' ∈ xs, c' ≠ c := fun c' hc' heq => hnd.1 (heq ▸ hc')
      refine ⟨?_, ?_⟩
      · rw [foldl_enqueueIdleThread_runQueueOnCore_frame xs (enqueueIdleThread ist c) c hframe,
          enqueueIdleThread_runQueueOnCore_self, SeLe4n.Kernel.RunQueue.mem_toList_iff_mem]
        exact (SeLe4n.Kernel.RunQueue.mem_insert _ _ _ _).mpr (Or.inr rfl)
      · rw [foldl_enqueueIdleThread_objects_frame xs (enqueueIdleThread ist c) c hframe]
        exact enqueueIdleThread_objects_self ist c
    · -- `c ∈ xs`: the tail fold enqueues it (induction hypothesis).
      exact ih (enqueueIdleThread ist x) hnd.2 hxs

/-- **WS-RR RR5.12** (the fold's equation): folding `enqueueIdleThread` over a
    `Nodup` list containing `c` yields, on core `c`, **exactly** the pre-fold
    queue with idle `c` re-enqueued at its priority — `c`'s own step, framed by
    every other step (which targets a distinct core, by `Nodup`).

    `foldl_enqueueIdleThread_installs` is this equation's membership corollary.
    The equation itself is what the boot-state characterisation
    (`bootFromPlatformCheckedWithIdleThreads_runQueueOnCore_eq`) needs: from it,
    what the boot queue *is* — and so every structural fact the scheduler's
    selection theorems require of it — is a computation on a known queue rather
    than a hypothesis about an unknown one. -/
theorem foldl_enqueueIdleThread_runQueueOnCore_eq
    (c : SeLe4n.Kernel.Concurrency.CoreId) (L : List SeLe4n.Kernel.Concurrency.CoreId)
    (ist : IntermediateState) :
    L.Nodup → c ∈ L →
    (L.foldl enqueueIdleThread ist).state.scheduler.runQueueOnCore c =
      ((ist.state.scheduler.runQueueOnCore c).remove (idleThreadId c)).insert
        (idleThreadId c) (queuedIdleThread c).priority := by
  induction L generalizing ist with
  | nil => intro _ hc; exact (List.not_mem_nil hc).elim
  | cons x xs ih =>
    intro hnd hc
    simp only [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hc with hxc | hxs
    · -- `c = x`: the head step writes the queue; the (distinct) tail frames it.
      subst hxc
      have hframe : ∀ c' ∈ xs, c' ≠ c := fun c' hc' heq => hnd.1 (heq ▸ hc')
      rw [foldl_enqueueIdleThread_runQueueOnCore_frame xs (enqueueIdleThread ist c) c hframe,
        enqueueIdleThread_runQueueOnCore_self]
    · -- `c ∈ xs`: the head step targets `x ≠ c` and frames `c`'s queue; the tail
      -- fold writes it (induction hypothesis).
      have hxc : x ≠ c := fun heq => hnd.1 (heq ▸ hxs)
      rw [ih (enqueueIdleThread ist x) hnd.2 hxs, enqueueIdleThread_runQueueOnCore_ne ist x c hxc]

-- ============================================================================
-- WS-RR RR5.13: the checked boot entry that enqueues per-core idle threads
-- ============================================================================

/-- **WS-RR RR5.13**: the production boot entry — `bootFromPlatformChecked`
    followed by a per-core idle enqueue on every core in `allCores`.

    **A thin composition, deliberately.**  The alternative was to mutate
    `bootFromPlatformChecked`'s own base from `bootFromPlatform config` to the
    idle-installing variant.  That would have broken the seven results that
    characterize the checked boot in terms of `bootFromPlatform config`
    (`_eq_bootFromPlatform`, `_admits_bootVSpace`, `_ok_implies_irqHandlersValid`,
    `_ok_implies_machineConfigWellFormed`, `_ok_implies_physicalAddressWidth_bound`,
    `_ok_interruptsEnabled`, `_rejects_invalid`) — either failing to compile or,
    worse, continuing to compile while no longer covering the live path.  As a
    composition they stay true verbatim and this entry's own chain is *derived*
    from them (`bootFromPlatformCheckedWithIdleThreads_map_ok` and the results
    below), which is what let RR5.13 and RR5.14 land as separate cuts.

    **One validation path, not two.**  Every well-formedness decision is
    `bootFromPlatformChecked`'s; this entry adds no check of its own and rejects
    exactly what that one rejects
    (`bootFromPlatformCheckedWithIdleThreads_rejects_invalid`).  A second
    `PlatformConfig` validator would be the `trap.rs` two-classifiers defect in
    miniature. -/
def bootFromPlatformCheckedWithIdleThreads (config : PlatformConfig) :
    Except String IntermediateState :=
  (bootFromPlatformChecked config).map fun ist =>
    SeLe4n.Kernel.Concurrency.allCores.foldl enqueueIdleThread ist

/-- **PR #889 review round 15**: the boot error for a configured thread pinned
    to a core the platform does not declare. -/
def undeclaredAffinityBootError : String :=
  "boot: a configured TCB's cpuAffinity names a core the platform does not " ++
  "declare (PR #889 review round 15)"

/-- **PR #889 review round 15**: does this TCB's `cpuAffinity` name a core the
    platform **declares**?

    `cpuAffinity = none` is fine: `determineTargetCore` routes such a thread to
    `bootCoreId`, which every binding declares (`coreCount ≥ 1`).  A `some c`
    with `c` outside the declared list is not: nothing rejects it today, the
    boot succeeds, and the first `tcbResume`/wake reads the affinity through
    `determineTargetCore` and enqueues the thread on a PE that does not exist —
    reporting success, possibly firing an SGI at it, and stranding the thread
    permanently.

    Destructured like `bootSafeTcbCheck`, so a new TCB field must be classified
    rather than silently ignored (the round-8 arity discipline). -/
def tcbAffinityDeclared (cores : List SeLe4n.Kernel.Concurrency.CoreId) (tcb : TCB) : Bool :=
  match tcb with
  | ⟨_tid, _priority, _domain, _cspaceRoot, _vspaceRoot, _ipcBuffer, _ipcState, _threadState,
     _timeSlice, _deadline, _queuePrev, _queuePPrev, _queueNext, _pendingMessage,
     _registerContext, _faultHandler, _boundNotification, _schedContextBinding, _timeoutBudget,
     _maxControlledPriority, _pipBoost, _timedOut, _lock, _cpuAffinity, _replyObject,
     _pendingReceiveReply, _pendingFault⟩ =>
    match tcb.cpuAffinity with
    | some c => cores.contains c
    | none   => true

@[simp] theorem tcbAffinityDeclared_def
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (tcb : TCB) :
    tcbAffinityDeclared cores tcb =
      (match tcb.cpuAffinity with
       | some c => cores.contains c
       | none   => true) := rfl

/-- **PR #889 review round 15**: only a TCB carries an affinity; every other
    kernel object is declared-core-agnostic. -/
def objectAffinityDeclared
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (obj : KernelObject) : Bool :=
  match obj with
  | .tcb tcb => tcbAffinityDeclared cores tcb
  | _ => true

/-- **PR #889 review round 15**: every configured TCB is pinned to a core the
    platform declares, or to none at all. -/
def bootAffinitiesDeclared
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig) : Bool :=
  config.initialObjects.all fun entry => objectAffinityDeclared cores entry.obj

/-- **PR #889 review round 15**: on the model's full core list the check is
    vacuous — every `CoreId` is a member of `allCores`. -/
@[simp] theorem bootAffinitiesDeclared_allCores (config : PlatformConfig) :
    bootAffinitiesDeclared SeLe4n.Kernel.Concurrency.allCores config = true := by
  unfold bootAffinitiesDeclared
  apply List.all_eq_true.mpr
  intro entry _
  unfold objectAffinityDeclared
  cases entry.obj with
  | tcb tcb =>
    simp only [tcbAffinityDeclared_def]
    cases hAff : tcb.cpuAffinity with
    | none => rfl
    | some c =>
      simp [SeLe4n.Kernel.Concurrency.mem_allCores c]
  | _ => rfl

-- ============================================================================
-- WS-BP BP7.10 — the boot's gates that do not read memory extents
-- ============================================================================

/-- **WS-BP BP7.10**: an untyped with its physical extent forgotten — every
    other field (the carve state, the children, the parent, the device flag)
    kept. -/
def untypedWithoutExtent (ut : UntypedObject) : UntypedObject :=
  { ut with regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 0 }

/-- **WS-BP BP7.10**: a kernel object with its untyped extent forgotten, and
    every other object unchanged. -/
def objectWithoutUntypedExtent : KernelObject → KernelObject
  | .untyped ut => .untyped (untypedWithoutExtent ut)
  | obj => obj

theorem objectWithoutUntypedExtent_eq_cnode {obj : KernelObject} {cn : CNode}
    (h : objectWithoutUntypedExtent obj = .cnode cn) : obj = .cnode cn := by
  cases obj <;> first | exact h | cases h

theorem objectWithoutUntypedExtent_eq_vspaceRoot {obj : KernelObject} {vs : VSpaceRoot}
    (h : objectWithoutUntypedExtent obj = .vspaceRoot vs) : obj = .vspaceRoot vs := by
  cases obj <;> first | exact h | cases h

/-- **WS-BP BP7.10**: a boot entry with its untyped extent forgotten. -/
def ObjectEntry.withoutUntypedExtent (e : ObjectEntry) : ObjectEntry where
  id := e.id
  obj := objectWithoutUntypedExtent e.obj
  hSlots := fun cn h => e.hSlots cn (objectWithoutUntypedExtent_eq_cnode h)
  hMappings := fun vs h => e.hMappings vs (objectWithoutUntypedExtent_eq_vspaceRoot h)

/-- **WS-BP BP7.10**: a configuration with every untyped's extent and the
memory map forgotten.

What it is for: every gate of the checked boot but two reads a configuration
only through this projection — the object ids, kinds and non-extent fields,
the IRQ table, the boot root, the PE count and the address width.  The two
that read what it forgets are the untyped placement (`untypedPlacementRespected`)
and the machine configuration's own well-formedness.  So a deployment whose
untyped extents and memory map are read off a board's account passes every
other gate on every account exactly when it passes them on one — which is how
the RPi5 deployment's gates, decided by evaluation on the five RAM variants,
hold at every first-gigabyte top the firmware may report (WS-BP BP7.10,
`rpi5BoundPlatformConfigAt_withoutExtents`). -/
def PlatformConfig.withoutExtents (c : PlatformConfig) : PlatformConfig :=
  { c with
    initialObjects := c.initialObjects.map ObjectEntry.withoutUntypedExtent
    machineConfig := { c.machineConfig with memoryMap := [] } }

@[simp] theorem ObjectEntry.withoutUntypedExtent_id (e : ObjectEntry) :
    e.withoutUntypedExtent.id = e.id := rfl

@[simp] theorem ObjectEntry.withoutUntypedExtent_obj (e : ObjectEntry) :
    e.withoutUntypedExtent.obj = objectWithoutUntypedExtent e.obj := rfl

private theorem all_withoutUntypedExtent {f : ObjectEntry → Bool} (objs : List ObjectEntry)
    (hf : ∀ e, f e.withoutUntypedExtent = f e) :
    (objs.map ObjectEntry.withoutUntypedExtent).all f = objs.all f := by
  rw [List.all_map]
  congr 1
  funext e
  exact hf e

theorem irqsUnique_withoutExtents (c : PlatformConfig) :
    irqsUnique c.withoutExtents.irqTable = irqsUnique c.irqTable := rfl

theorem objectIdsUnique_withoutExtents (c : PlatformConfig) :
    objectIdsUnique c.withoutExtents.initialObjects = objectIdsUnique c.initialObjects := by
  unfold objectIdsUnique PlatformConfig.withoutExtents
  simp only [List.map_map]
  rfl

theorem idleSlotsReserved_withoutExtents (c : PlatformConfig) :
    idleSlotsReserved c.withoutExtents = idleSlotsReserved c := by
  unfold idleSlotsReserved PlatformConfig.withoutExtents
  simp only
  rw [all_withoutUntypedExtent]
  intro e
  simp only [ObjectEntry.withoutUntypedExtent_id, ObjectEntry.withoutUntypedExtent_obj]
  cases e.obj <;> rfl

theorem embeddedIdentitiesMatchSlots_withoutExtents (c : PlatformConfig) :
    embeddedIdentitiesMatchSlots c.withoutExtents = embeddedIdentitiesMatchSlots c := by
  unfold embeddedIdentitiesMatchSlots tcbIdentitiesMatchSlots schedContextIdentitiesMatchSlots
    replyIdentitiesMatchSlots PlatformConfig.withoutExtents
  simp only
  rw [all_withoutUntypedExtent, all_withoutUntypedExtent, all_withoutUntypedExtent] <;>
    (intro e
     simp only [ObjectEntry.withoutUntypedExtent_id, ObjectEntry.withoutUntypedExtent_obj]
     cases e.obj <;> rfl)

theorem objectBudgetRespected_withoutExtents (c : PlatformConfig) :
    objectBudgetRespected c.withoutExtents = objectBudgetRespected c := by
  unfold objectBudgetRespected PlatformConfig.withoutExtents
  simp only [List.length_map]

theorem declaredCoreCountInRange_withoutExtents (c : PlatformConfig) :
    declaredCoreCountInRange c.withoutExtents = declaredCoreCountInRange c := rfl

theorem bootSafe_withoutExtents (c : PlatformConfig) :
    c.withoutExtents.initialObjects.all (fun entry => bootSafeObjectCheck entry.obj) =
      c.initialObjects.all (fun entry => bootSafeObjectCheck entry.obj) := by
  unfold PlatformConfig.withoutExtents
  simp only
  rw [all_withoutUntypedExtent]
  intro e
  simp only [ObjectEntry.withoutUntypedExtent_obj]
  cases e.obj <;> rfl

theorem bootVSpaceAsidsDistinct_withoutExtents (c : PlatformConfig) :
    bootVSpaceAsidsDistinct c.withoutExtents = bootVSpaceAsidsDistinct c := by
  unfold bootVSpaceAsidsDistinct bootVSpaceAsids PlatformConfig.withoutExtents
  simp only [List.filterMap_map]
  have : (bootEntryAsid? ∘ ObjectEntry.withoutUntypedExtent) = bootEntryAsid? := by
    funext e
    simp only [Function.comp_apply]
    unfold bootEntryAsid?
    simp only [ObjectEntry.withoutUntypedExtent_obj]
    cases e.obj <;> rfl
  rw [this]

theorem irqHandlersReferenceNotifications_withoutExtents (c : PlatformConfig) :
    irqHandlersReferenceNotifications c.withoutExtents = irqHandlersReferenceNotifications c := by
  unfold irqHandlersReferenceNotifications PlatformConfig.withoutExtents
  simp only [List.find?_map]
  congr 1
  funext irq
  have hComp : ((fun entry : ObjectEntry => entry.id == irq.handler) ∘
      ObjectEntry.withoutUntypedExtent) = (fun entry => entry.id == irq.handler) := rfl
  rw [hComp]
  cases c.initialObjects.find? (fun entry => entry.id == irq.handler) with
  | none => rfl
  | some e =>
      simp only [Option.map_some, ObjectEntry.withoutUntypedExtent_obj]
      cases e.obj <;> rfl

theorem bootVSpaceRootObjIdDistinct_withoutExtents (c : PlatformConfig) :
    bootVSpaceRootObjIdDistinct c.withoutExtents = bootVSpaceRootObjIdDistinct c := by
  unfold bootVSpaceRootObjIdDistinct PlatformConfig.withoutExtents
  simp only [List.any_map]
  rfl

theorem bootVSpaceRootObjIdNonSentinel_withoutExtents (c : PlatformConfig) :
    bootVSpaceRootObjIdNonSentinel c.withoutExtents = bootVSpaceRootObjIdNonSentinel c := rfl

theorem bootVSpaceRootSafe_withoutExtents (c : PlatformConfig) :
    bootVSpaceRootSafe c.withoutExtents = bootVSpaceRootSafe c := rfl

theorem bootAffinitiesDeclared_withoutExtents (cores : List SeLe4n.Kernel.Concurrency.CoreId)
    (c : PlatformConfig) :
    bootAffinitiesDeclared cores c.withoutExtents = bootAffinitiesDeclared cores c := by
  unfold bootAffinitiesDeclared PlatformConfig.withoutExtents
  simp only
  rw [all_withoutUntypedExtent]
  intro e
  simp only [ObjectEntry.withoutUntypedExtent_obj]
  cases e.obj <;> rfl

theorem physicalAddressWidth_withoutExtents (c : PlatformConfig) :
    c.withoutExtents.machineConfig.physicalAddressWidth = c.machineConfig.physicalAddressWidth :=
  rfl

/-- **WS-BP BP7.10**: well-formedness transfers along the projection, given the
    one conjunct it forgets — so a configuration agreeing with a well-formed
    one on everything but its extents is well-formed exactly when its own
    untypeds are placed. -/
theorem PlatformConfig.wellFormed_of_withoutExtents (c c' : PlatformConfig)
    (hEq : c.withoutExtents = c'.withoutExtents) (hWf : c'.wellFormed = true)
    (hPlace : untypedPlacementRespected c = true) : c.wellFormed = true := by
  have h1 := irqsUnique_withoutExtents c
  have h2 := objectIdsUnique_withoutExtents c
  have h3 := idleSlotsReserved_withoutExtents c
  have h4 := embeddedIdentitiesMatchSlots_withoutExtents c
  have h5 := objectBudgetRespected_withoutExtents c
  have h6 := declaredCoreCountInRange_withoutExtents c
  rw [hEq, irqsUnique_withoutExtents] at h1
  rw [hEq, objectIdsUnique_withoutExtents] at h2
  rw [hEq, idleSlotsReserved_withoutExtents] at h3
  rw [hEq, embeddedIdentitiesMatchSlots_withoutExtents] at h4
  rw [hEq, objectBudgetRespected_withoutExtents] at h5
  rw [hEq, declaredCoreCountInRange_withoutExtents] at h6
  unfold PlatformConfig.wellFormed at hWf ⊢
  simp only [Bool.and_eq_true] at hWf ⊢
  obtain ⟨⟨⟨⟨⟨⟨w1, w2⟩, w3⟩, w4⟩, w5⟩, w6⟩, _⟩ := hWf
  exact ⟨⟨⟨⟨⟨⟨h1 ▸ w1, h2 ▸ w2⟩, h3 ▸ w3⟩, h4 ▸ w4⟩, h5 ▸ w5⟩, h6 ▸ w6⟩, hPlace⟩

/-- PR #889 review round 3: the idle enqueue over a **declared** core list — the
    cores a platform binding says exist (`PlatformBinding.declaredCores`), rather than
    the model's `allCores`.  A single-core binding (`SimSingleCorePlatform`,
    `coreCount = 1`) booted through the all-cores form came up with idle TCBs
    and runnable queues on three cores the binding does not have, and reserved
    their slots; the binding's topology never reached the boot.  On the full
    core count the two forms coincide definitionally
    (`bootFromPlatformCheckedWithIdleThreadsFor_allCores`), which is the RPi5
    case (`rpi5_cores_eq_allCores`), so every all-cores theorem is a theorem of
    the hardware boot.  Same validation, same rejections: the checked boot is
    the one validation path, and the fold adds none. -/
def bootFromPlatformCheckedWithIdleThreadsFor
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig) :
    Except String IntermediateState :=
  (bootFromPlatformChecked config).bind fun ist =>
    if bootAffinitiesDeclared cores config then
      .ok (cores.foldl enqueueIdleThread ist)
    else
      .error undeclaredAffinityBootError

/-- PR #889 review round 3: on every core the declared-list form **is** the
    all-cores form. -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_allCores (config : PlatformConfig) :
    bootFromPlatformCheckedWithIdleThreadsFor SeLe4n.Kernel.Concurrency.allCores config =
      bootFromPlatformCheckedWithIdleThreads config := by
  unfold bootFromPlatformCheckedWithIdleThreadsFor bootFromPlatformCheckedWithIdleThreads
  cases bootFromPlatformChecked config with
  | error e => rfl
  | ok ist => simp [Except.bind, Except.map, bootAffinitiesDeclared_allCores]

/-- PR #889 review round 3: the declared-list form rejects exactly what the
    checked boot rejects, whatever the list. -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_rejects_invalid
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig) (e : String)
    (h : bootFromPlatformChecked config = .error e) :
    bootFromPlatformCheckedWithIdleThreadsFor cores config = .error e := by
  unfold bootFromPlatformCheckedWithIdleThreadsFor
  rw [h]
  rfl

/-- PR #889 review round 5: on a successful checked boot the declared-list form
    is the fold over the declared cores, and nothing else. -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_map_ok
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist)
    (hAff : bootAffinitiesDeclared cores config = true) :
    bootFromPlatformCheckedWithIdleThreadsFor cores config =
      .ok (cores.foldl enqueueIdleThread ist) := by
  unfold bootFromPlatformCheckedWithIdleThreadsFor
  rw [h]
  simp [Except.bind, hAff]

/-- **PR #889 review round 15**: a **successful** boot's configured threads are
    all pinned to cores the platform declares, so `determineTargetCore` on any
    of them names a PE the platform has.

    Nothing rejected an undeclared affinity before: the boot succeeded, and the
    first `tcbResume` or wake enqueued the thread on a core that does not
    exist — reporting success, possibly firing an SGI at it, and stranding the
    thread permanently.  `bootSafeTcbCheck` cannot decide this: the declared
    core set is the *binding's*, and the checked boot is binding-agnostic by
    design (one validation path).  So the check lives where the core list
    arrives. -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_ok_affinitiesDeclared
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok ist) :
    bootAffinitiesDeclared cores config = true := by
  cases hAff : bootAffinitiesDeclared cores config with
  | true => rfl
  | false =>
    exfalso
    cases hChecked : bootFromPlatformChecked config with
    | error e =>
      rw [bootFromPlatformCheckedWithIdleThreadsFor_rejects_invalid cores config e hChecked] at h
      cases h
    | ok base =>
      unfold bootFromPlatformCheckedWithIdleThreadsFor at h
      rw [hChecked] at h
      simp [Except.bind, hAff] at h

/-- **PR #889 review round 15**: the contrapositive, as the refusal — a config
    pinning a thread to an undeclared core produces no state at all, so the
    caller never reaches `initialiseKernelState`. -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_undeclared_affinity_refused
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (hAff : bootAffinitiesDeclared cores config = false)
    (ist : IntermediateState) :
    bootFromPlatformCheckedWithIdleThreadsFor cores config ≠ .ok ist := by
  intro h
  have hTrue := bootFromPlatformCheckedWithIdleThreadsFor_ok_affinitiesDeclared cores config ist h
  rw [hAff] at hTrue
  cases hTrue


/-- PR #889 review round 3: are the labeling's **declared separation witnesses**
    installed threads of `st`?  `isInsecureDefaultContext` decides that the
    labeling separates two admissible *ids*; it cannot see whether either id is
    a thread the deployment actually creates, so a boot whose every live thread
    sits on one side of the boundary — the empty config's, whose only TCBs are
    the idle threads — was admitted with a partition that separated nothing
    running.  The boot wrapper refuses such a boot before committing anything
    (`uninstalledSeparationWitnessBootError`).  A labeling with no declared
    witness fails closed here too, though the guard has already refused it. -/
def declaredWitnessesInstalled (st : SystemState) (ctx : LabelingContext) : Bool :=
  match ctx.separatedThreads with
  | none => false
  | some (lo, hi) => (st.getTcb? lo).isSome && (st.getTcb? hi).isSome

/-- **WS-RR RR5.13**: `installBootVSpaceRoot` frames the scheduler — it writes
    the object store and `asidTable`, neither of which the scheduler reads.
    Definitional, and the missing step in
    `bootFromPlatformChecked_ok_scheduler_eq`'s boot-VSpace arm. -/
theorem installBootVSpaceRoot_scheduler
    (ist : IntermediateState) (id : SeLe4n.ObjId) (vsr : VSpaceRoot)
    (hMappings : vsr.mappings.invExt) :
    (installBootVSpaceRoot ist id vsr hMappings).state.scheduler = ist.state.scheduler := rfl

/-- **WS-RR RR5.13**: whatever a successful checked boot returns, its scheduler
    is the default one.

    Neither of the two things the checked boot adds over `bootFromPlatform`
    touches the scheduler: `installBootVSpaceRoot` writes the object store and
    `asidTable`, and `bootEnableInterruptsOp` writes `machine`.  Stated over the
    `.ok` *result* rather than over the seven well-formedness hypotheses
    `bootFromPlatformChecked_eq_bootFromPlatform` takes, because that is the form
    the idle entry's callers have: they hold a successful boot, not a proof that
    the config passes each gate. -/
theorem bootFromPlatformChecked_ok_scheduler_eq (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    ist.state.scheduler = (default : SystemState).scheduler := by
  unfold bootFromPlatformChecked at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · split at h
            · split at h
              · split at h
                · split at h
                  · -- All gates pass; case on `bootVSpaceRoot`.
                    split at h
                    · -- `bootVSpaceRoot = none`: the base fold's scheduler.
                      cases h
                      rw [bootEnableInterruptsOp_scheduler_eq]
                      exact bootFromPlatform_scheduler_eq config
                    · -- `bootVSpaceRoot = some entry`: the install frames it.
                      cases h
                      rw [bootEnableInterruptsOp_scheduler_eq,
                        installBootVSpaceRoot_scheduler]
                      exact bootFromPlatform_scheduler_eq config
                  · cases h
                · cases h
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **WS-RR RR5.13** (PR #889 review): what a successful checked boot **is**.

    Every gate passed — the two the results below read are the config's
    well-formedness (which now carries the idle-slot reservation) and the
    per-object boot-safety check — and the state is the interrupt-enabled image
    of the plain boot, with the boot VSpace root installed when the config
    carries one.  Stated once so the freshness and thread-state results derive
    from it instead of each re-walking the checked boot's ten gates. -/
theorem bootFromPlatformChecked_ok_shape (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    config.wellFormed = true ∧
    config.initialObjects.all (fun entry => bootSafeObjectCheck entry.obj) = true ∧
    ((config.bootVSpaceRoot = none ∧ ist = bootEnableInterruptsOp (bootFromPlatform config)) ∨
      ∃ entry, config.bootVSpaceRoot = some entry ∧
        ist = bootEnableInterruptsOp
          (installBootVSpaceRoot (bootFromPlatform config) entry.id entry.root entry.hMappings)) := by
  unfold bootFromPlatformChecked at h
  split at h
  · rename_i hWf
    split at h
    · rename_i hSafe
      split at h
      · split at h
        · split at h
          · split at h
            · split at h
              · split at h
                · split at h
                  · split at h
                    · rename_i hNone
                      cases h
                      exact ⟨hWf, hSafe, Or.inl ⟨hNone, rfl⟩⟩
                    · rename_i entry hSome
                      cases h
                      exact ⟨hWf, hSafe, Or.inr ⟨entry, hSome, rfl⟩⟩
                  · cases h
                · cases h
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-! ### The object-capacity invariant of a successful boot (PR #889 review round 18)

`objectIndexBounded` is the allocation-boundary invariant `retypeFromUntyped`
enforces, and nothing in the boot path established it: the checked boot did not
bound the object count, and the idle fold — live since WS-RR RR5.13 — adds one
entry per core on top of whatever the config brought.  The chain below derives
the count from the config, so `objectBudgetRespected` (the fifth `wellFormed`
conjunct) is what makes a successful boot bounded. -/

/-- `createObject` prepends at most one entry: an id already present leaves the
    index alone. -/
theorem createObject_objectIndex_length_le (ist : IntermediateState)
    (id : SeLe4n.ObjId) (obj : KernelObject)
    (hSlots : ∀ cn, obj = KernelObject.cnode cn → cn.slotsUnique)
    (hMappings : ∀ vs, obj = KernelObject.vspaceRoot vs → vs.mappings.invExt) :
    (Builder.createObject ist id obj hSlots hMappings).state.objectIndex.length ≤
      ist.state.objectIndex.length + 1 := by
  unfold Builder.createObject
  by_cases h : ist.state.objectIndexSet.contains id
  · simp [h]
  · simp [h]

/-- **WS-BP BP3.2**: a boot install adds at most one index entry — the ASID
    registration writes `asidTable` only. -/
theorem createBootObject_objectIndex_length_le (ist : IntermediateState) (e : ObjectEntry) :
    (createBootObject ist e).state.objectIndex.length ≤ ist.state.objectIndex.length + 1 :=
  createObject_objectIndex_length_le ist e.id e.obj e.hSlots e.hMappings

/-- Folding the config's objects adds at most one index entry each. -/
theorem foldObjects_objectIndex_length_le (objs : List ObjectEntry)
    (ist : IntermediateState) :
    (foldObjects objs ist).state.objectIndex.length ≤
      ist.state.objectIndex.length + objs.length := by
  unfold foldObjects
  induction objs generalizing ist with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      refine Nat.le_trans (ih _) ?_
      have := createBootObject_objectIndex_length_le ist entry
      omega

/-- The raw boot installs one index entry per config object at most. -/
theorem bootFromPlatform_objectIndex_length_le (config : PlatformConfig) :
    (bootFromPlatform config).state.objectIndex.length ≤ config.initialObjects.length := by
  have hEmpty : (foldIrqs config.irqTable mkEmptyIntermediateState).state.objectIndex = [] := by
    rw [foldIrqs_objectIndex]; rfl
  have := foldObjects_objectIndex_length_le config.initialObjects
    (foldIrqs config.irqTable mkEmptyIntermediateState)
  rw [hEmpty] at this
  simpa [bootFromPlatform, applyMachineConfig] using this

/-- Enabling interrupts touches `machine` only. -/
@[simp] theorem bootEnableInterruptsOp_objectIndex (ist : IntermediateState) :
    (bootEnableInterruptsOp ist).state.objectIndex = ist.state.objectIndex := rfl

/-- A successful checked boot holds one entry per config object, plus at most
    the boot VSpace root. -/
theorem bootFromPlatformChecked_ok_objectIndex_length_le (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    ist.state.objectIndex.length ≤ config.initialObjects.length + 1 := by
  obtain ⟨_, _, hShape⟩ := bootFromPlatformChecked_ok_shape config ist h
  have hBase := bootFromPlatform_objectIndex_length_le config
  rcases hShape with ⟨_, hEq⟩ | ⟨entry, _, hEq⟩
  · subst hEq; simpa using Nat.le_trans hBase (Nat.le_succ _)
  · subst hEq
    simp only [bootEnableInterruptsOp_objectIndex, installBootVSpaceRoot]
    exact Nat.le_trans (createBootObject_objectIndex_length_le _ _) (by omega)

/-- **PR #889 review round 20**: the unchecked boot installs the config's
    declared PE count.  `applyMachineConfig` is the only writer of `machine`
    on this path, and the two folds beneath it leave `machine` alone. -/
theorem bootFromPlatform_machine_declaredCoreCount (config : PlatformConfig) :
    (bootFromPlatform config).state.machine.declaredCoreCount =
    config.machineConfig.declaredCoreCount := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_declaredCoreCount]

/-- **PR #889 review round 20**: ...and the checked boot's two shapes preserve
    it — `installBootVSpaceRoot` writes the object store and the ASID table,
    `bootEnableInterruptsOp` writes one machine flag, neither touches the PE
    count. -/
theorem bootFromPlatformChecked_ok_declaredCoreCount (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    ist.state.machine.declaredCoreCount = config.machineConfig.declaredCoreCount := by
  obtain ⟨_, _, hShape⟩ := bootFromPlatformChecked_ok_shape config ist h
  rcases hShape with ⟨_, hEq⟩ | ⟨entry, _, hEq⟩
  · subst hEq
    rw [bootEnableInterruptsOp_declaredCoreCount_eq]
    exact bootFromPlatform_machine_declaredCoreCount config
  · subst hEq
    rw [bootEnableInterruptsOp_declaredCoreCount_eq]
    show (bootFromPlatform config).state.machine.declaredCoreCount = _
    exact bootFromPlatform_machine_declaredCoreCount config

/-- The idle enqueue adds at most one index entry: it stores one TCB, and the
    run-queue write beside it leaves the object index alone. -/
theorem enqueueIdleThread_objectIndex_length_le (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (enqueueIdleThread ist c).state.objectIndex.length ≤ ist.state.objectIndex.length + 1 :=
  enqueueIdleThreadOnCore_objectIndex_length_le ist.state c

/-- ...so the fold adds at most one per core. -/
theorem foldl_enqueueIdleThread_objectIndex_length_le
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState) :
    (cores.foldl enqueueIdleThread ist).state.objectIndex.length ≤
      ist.state.objectIndex.length + cores.length := by
  induction cores generalizing ist with
  | nil => simp
  | cons c rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      refine Nat.le_trans (ih _) ?_
      have := enqueueIdleThread_objectIndex_length_le ist c
      omega

/-- **PR #889 review round 18**: a successful production boot satisfies
    `objectIndexBounded`.

    The budget conjunct reserves `numCores` slots, so any core list no longer
    than the model's — every binding's, by `PlatformBinding.coreCountLe` —
    leaves the object index inside `maxObjects`. -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_objectIndexBounded
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (hCores : cores.length ≤ SeLe4n.Kernel.Concurrency.numCores)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok ist) :
    objectIndexBounded ist.state := by
  unfold bootFromPlatformCheckedWithIdleThreadsFor at h
  cases hBase : bootFromPlatformChecked config with
  | error e => rw [hBase] at h; simp [Except.bind] at h
  | ok base =>
      rw [hBase] at h
      simp only [Except.bind] at h
      by_cases hAff : bootAffinitiesDeclared cores config
      · simp only [hAff, if_true] at h
        obtain ⟨hWf, _, _⟩ := bootFromPlatformChecked_ok_shape config base hBase
        have hBudget := PlatformConfig.wellFormed_objectBudgetRespected config hWf
        unfold objectBudgetRespected at hBudget
        have hBudget' : config.initialObjects.length + 1 +
            SeLe4n.Kernel.Concurrency.numCores ≤ maxObjects := by
          simpa using decide_eq_true_eq.mp hBudget
        have hChecked := bootFromPlatformChecked_ok_objectIndex_length_le config base hBase
        have hFold := foldl_enqueueIdleThread_objectIndex_length_le cores base
        have hIst : ist = cores.foldl enqueueIdleThread base := by
          simpa using h.symm
        subst hIst
        unfold objectIndexBounded
        omega
      · simp [hAff] at h

/-- The all-cores production boot is bounded: `allCores` has exactly `numCores`
    members, which is the headroom the budget conjunct reserves. -/
theorem bootFromPlatformCheckedWithIdleThreads_objectIndexBounded (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist) :
    objectIndexBounded ist.state := by
  refine bootFromPlatformCheckedWithIdleThreadsFor_objectIndexBounded
    SeLe4n.Kernel.Concurrency.allCores config ist ?_ ?_
  · simp [SeLe4n.Kernel.Concurrency.allCores]
  · rw [bootFromPlatformCheckedWithIdleThreadsFor_allCores]; exact h

/-- **WS-RR RR5.13**: the composition's shape — a successful checked boot yields
    a successful idle boot whose state is the fold, and nothing else does.  Every
    result below is derived through this rather than restated. -/
theorem bootFromPlatformCheckedWithIdleThreads_map_ok (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    bootFromPlatformCheckedWithIdleThreads config =
      .ok (SeLe4n.Kernel.Concurrency.allCores.foldl enqueueIdleThread ist) := by
  unfold bootFromPlatformCheckedWithIdleThreads
  rw [h]
  rfl

/-- **WS-RR RR5.13**: the idle boot entry rejects exactly what the checked boot
    rejects — the "one validation path" property, machine-checked. -/
theorem bootFromPlatformCheckedWithIdleThreads_rejects_invalid (config : PlatformConfig)
    (e : String) (h : bootFromPlatformChecked config = .error e) :
    bootFromPlatformCheckedWithIdleThreads config = .error e := by
  unfold bootFromPlatformCheckedWithIdleThreads
  rw [h]
  rfl

/-- **WS-RR RR5.13**: and it succeeds exactly when the checked boot succeeds, so
    the two entries agree on *acceptance* as well as on rejection. -/
theorem bootFromPlatformCheckedWithIdleThreads_isOk_iff (config : PlatformConfig) :
    (bootFromPlatformCheckedWithIdleThreads config).toOption.isSome =
      (bootFromPlatformChecked config).toOption.isSome := by
  unfold bootFromPlatformCheckedWithIdleThreads
  cases bootFromPlatformChecked config <;> rfl

/-- **WS-RR RR5.13**: the machine configuration the checked boot established
    survives the idle enqueue — the enqueue writes only the object store and the
    per-core run queues, so every `machine`-level result of
    `bootFromPlatformChecked` (interrupts enabled, the physical-address-width
    bound, machine well-formedness) transports to this entry unchanged. -/
theorem bootFromPlatformCheckedWithIdleThreads_machine (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    ∀ ist', bootFromPlatformCheckedWithIdleThreads config = .ok ist' →
      ist'.state.machine = ist.state.machine := by
  intro ist' h'
  rw [bootFromPlatformCheckedWithIdleThreads_map_ok config ist h] at h'
  injection h' with h'
  rw [← h']
  exact foldl_enqueueIdleThread_machine _ ist

/-- **PR #889 review round 20**: the production boot state carries the config's
    declared PE count, whichever core list the binding supplies.

    This is the link that makes `PlatformBinding.declaredCoreCountAgrees`
    operative: the boot enforces the binding's `coreCount`
    (`bootAffinitiesDeclared`, round 15), while the live affinity transition
    reads `SystemState.machine.declaredCoreCount`, because a kernel transition
    sees the machine and not the binding.  With the obligation discharged by
    every binding, the two are the same number on any state this entry
    produces. -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_declaredCoreCount
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist' : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok ist') :
    ist'.state.machine.declaredCoreCount = config.machineConfig.declaredCoreCount := by
  unfold bootFromPlatformCheckedWithIdleThreadsFor at h
  cases hChecked : bootFromPlatformChecked config with
  | error e => rw [hChecked] at h; simp [Except.bind] at h
  | ok ist =>
      rw [hChecked] at h
      simp only [Except.bind] at h
      split at h
      · injection h with h
        rw [← h, foldl_enqueueIdleThread_machine]
        exact bootFromPlatformChecked_ok_declaredCoreCount config ist hChecked
      · cases h

/-- **WS-RR RR5.13**: every core's current slot is still `none` after the idle
    enqueue.

    This is the fact that keeps `queueCurrentConsistent` — and its per-core
    form — true of the production boot state, and it is why the entry enqueues
    rather than dispatching: a core whose current slot pointed at an idle thread
    *also* on its run queue would violate the dequeue-on-dispatch discipline from
    the first instruction.  Each core's first scheduling point dispatches idle
    out of the queue. -/
theorem bootFromPlatformCheckedWithIdleThreads_currentAllNone (config : PlatformConfig)
    (ist' : IntermediateState) (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist')
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    ist'.state.scheduler.currentOnCore c = none := by
  unfold bootFromPlatformCheckedWithIdleThreads at h
  cases hChecked : bootFromPlatformChecked config with
  | error e => rw [hChecked] at h; simp [Except.map] at h
  | ok ist =>
      rw [hChecked] at h
      injection h with h
      rw [← h, foldl_enqueueIdleThread_currentOnCore,
        bootFromPlatformChecked_ok_scheduler_eq config ist hChecked]
      exact (default_state_perCoreInitialized c).1

/-- **WS-RR RR5.12**: the boot state's per-core idle facts, in the form the
    discharge predicate needs — for **every** core, the idle thread is on that
    core's own run queue, its TCB is in the object store, and the core's active
    domain is the idle thread's domain `⟨0⟩`.

    These are the three conjuncts of `idleThreadEnqueuedOnCore`
    (`Scheduler/Operations/PerCoreIdle.lean`), stated here — in production —
    because the operation is production; the composed statement, and the
    `chooseThreadOnCore_always_succeeds` corollary it discharges, live beside the
    predicate in the staged scheduler layer.

    Each conjunct comes from a different place, exactly as the plan's row
    describes: run-queue membership and object-store presence from
    `foldl_enqueueIdleThread_installs`, and the domain match from
    `queuedIdleThread`'s domain field composed with
    `foldl_enqueueIdleThread_activeDomainOnCore` over the boot scheduler's
    per-core initialization. -/
theorem bootFromPlatformCheckedWithIdleThreads_idle_available (config : PlatformConfig)
    (ist' : IntermediateState) (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist')
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    idleThreadId c ∈ (ist'.state.scheduler.runQueueOnCore c).toList ∧
    ist'.state.objects[(idleThreadId c).toObjId]? =
      some (KernelObject.tcb (queuedIdleThread c)) ∧
    ist'.state.scheduler.activeDomainOnCore c = ⟨0⟩ := by
  unfold bootFromPlatformCheckedWithIdleThreads at h
  cases hChecked : bootFromPlatformChecked config with
  | error e => rw [hChecked] at h; simp [Except.map] at h
  | ok ist =>
      rw [hChecked] at h
      injection h with h
      subst h
      have hInstalls := foldl_enqueueIdleThread_installs c
        SeLe4n.Kernel.Concurrency.allCores ist
        SeLe4n.Kernel.Concurrency.allCores_nodup
        (SeLe4n.Kernel.Concurrency.mem_allCores c)
      refine ⟨hInstalls.1, hInstalls.2, ?_⟩
      rw [foldl_enqueueIdleThread_activeDomainOnCore,
        bootFromPlatformChecked_ok_scheduler_eq config ist hChecked]
      exact (default_state_perCoreInitialized c).2.2.2.1

/-- **WS-RR RR5.12** (the boot queue, characterised): on **every** core, the
    production boot state's run queue is exactly the empty queue with that core's
    idle thread enqueued at its priority.

    The checked boot leaves the default scheduler
    (`bootFromPlatformChecked_ok_scheduler_eq`), whose queues are all empty
    (`default_state_perCoreInitialized`), and the fold writes each core's queue
    once (`foldl_enqueueIdleThread_runQueueOnCore_eq`).  Everything the
    scheduler's selection theorems need of the boot queue — that it is
    well-formed, that its members resolve, that idle is on it and nothing else
    is — is a corollary of this one equation, which is why none of it has to be
    assumed of the state the kernel boots into. -/
theorem bootFromPlatformCheckedWithIdleThreads_runQueueOnCore_eq (config : PlatformConfig)
    (ist' : IntermediateState) (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist')
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    ist'.state.scheduler.runQueueOnCore c =
      ((SeLe4n.Kernel.RunQueue.empty.remove (idleThreadId c)).insert
        (idleThreadId c) (queuedIdleThread c).priority) := by
  unfold bootFromPlatformCheckedWithIdleThreads at h
  cases hChecked : bootFromPlatformChecked config with
  | error e => rw [hChecked] at h; simp [Except.map] at h
  | ok ist =>
      rw [hChecked] at h
      injection h with h
      subst h
      have hEmpty : ist.state.scheduler.runQueueOnCore c = SeLe4n.Kernel.RunQueue.empty := by
        rw [bootFromPlatformChecked_ok_scheduler_eq config ist hChecked]
        exact (default_state_perCoreInitialized c).2.1
      rw [foldl_enqueueIdleThread_runQueueOnCore_eq c SeLe4n.Kernel.Concurrency.allCores ist
        SeLe4n.Kernel.Concurrency.allCores_nodup (SeLe4n.Kernel.Concurrency.mem_allCores c),
        hEmpty]

/-- **WS-RR RR5.12**: the boot run queue on core `c` holds that core's idle
    thread and **nothing else** — the negative half of
    `bootFromPlatformCheckedWithIdleThreads_idle_available`.  No thread the
    platform config names is runnable at boot: every one of them waits for a
    resume, a wake or a dispatch that the model's transitions account for. -/
theorem bootFromPlatformCheckedWithIdleThreads_mem_runQueueOnCore_iff (config : PlatformConfig)
    (ist' : IntermediateState) (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist')
    (c : SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId) :
    tid ∈ (ist'.state.scheduler.runQueueOnCore c).toList ↔ tid = idleThreadId c := by
  rw [bootFromPlatformCheckedWithIdleThreads_runQueueOnCore_eq config ist' h c,
    SeLe4n.Kernel.RunQueue.mem_toList_iff_mem, SeLe4n.Kernel.RunQueue.mem_insert,
    SeLe4n.Kernel.RunQueue.mem_remove]
  constructor
  · rintro (⟨hEmpty, _⟩ | hEq)
    · exact (SeLe4n.Kernel.RunQueue.not_mem_empty tid hEmpty).elim
    · exact hEq
  · intro hEq
    exact Or.inr hEq

/-- **WS-RR RR5.12**: the boot run queue is well-formed on every core — the
    empty queue is (`RunQueue.empty_wellFormed`) and one `remove`/`insert` pair
    preserves it.

    This is one of the two structural premises `chooseThreadOnCore_always_succeeds`
    consumes.  Until it was proved here, the staged corollary
    `bootFromPlatformCheckedWithIdleThreads_chooseThreadOnCore_succeeds` took it
    by hypothesis, so the no-stall chain still rested on an assumption about the
    very state RR5.12 exists to discharge it from. -/
theorem bootFromPlatformCheckedWithIdleThreads_runQueueOnCore_wellFormed (config : PlatformConfig)
    (ist' : IntermediateState) (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist')
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (ist'.state.scheduler.runQueueOnCore c).wellFormed := by
  rw [bootFromPlatformCheckedWithIdleThreads_runQueueOnCore_eq config ist' h c]
  exact SeLe4n.Kernel.RunQueue.insert_preserves_wellFormed _
    (SeLe4n.Kernel.RunQueue.remove_preserves_wellFormed _
      SeLe4n.Kernel.RunQueue.empty_wellFormed _) _ _

/-- **WS-RR RR5.12**: every thread on a boot run queue resolves to a TCB — the
    other structural premise of `chooseThreadOnCore_always_succeeds`, which is
    `runnableThreadsAreTCBsOnCore` (`Scheduler/Invariant/PerCore.lean`) stated
    unfolded, because that module is not in this one's import closure; the staged
    scheduler layer restates it under its name.  Immediate from the two facts
    above: the only member is idle `c`, and its TCB is in the store. -/
theorem bootFromPlatformCheckedWithIdleThreads_runnable_resolve (config : PlatformConfig)
    (ist' : IntermediateState) (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist')
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    ∀ tid, tid ∈ (ist'.state.scheduler.runQueueOnCore c).toList →
      ∃ tcb : TCB, ist'.state.getTcb? tid = some tcb := by
  intro tid hMem
  rw [bootFromPlatformCheckedWithIdleThreads_mem_runQueueOnCore_iff config ist' h c] at hMem
  subst hMem
  refine ⟨queuedIdleThread c, ?_⟩
  simp only [SystemState.getTcb?]
  rw [(bootFromPlatformCheckedWithIdleThreads_idle_available config ist' h c).2.1]

-- ============================================================================
-- PR #889 review: every platform binding's labeling is `LabelingContextValid`
-- ============================================================================

/-- **WS-RR RR5.1** (PR #889 review): the labeling **any** platform binding
    installs is `LabelingContextValid` — thread/object coherence, its
    observability corollary and non-triviality — because the binding carries the
    `DeploymentLabeling` source and `PlatformBinding.labeling` is the
    constructor's output on it (`deploymentLabelingContext_valid`).

    This is what the boot-time guard cannot decide: `isInsecureDefaultContext`
    evaluates non-triviality alone, so a binding that stored a bare context the
    guard admits could still have labelled a thread and its own TCB object
    incompatibly, and the non-interference theorems would have stopped applying
    to that deployment without any check noticing.  Stated here, beside the
    boot, rather than in `Platform/Contract.lean`, because the validity
    predicate lives in the information-flow invariant surface that the contract
    module does not import. -/
theorem _root_.SeLe4n.Platform.PlatformBinding.labeling_valid
    (platform : Type) [SeLe4n.Platform.PlatformBinding platform] :
    LabelingContextValid (SeLe4n.Platform.PlatformBinding.labeling (platform := platform)) :=
  deploymentLabelingContext_valid _

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

/-- V4-A6: The post-boot state preserves asidTable from default — when the
    config installs no VSpace root (WS-BP BP3.2: one it does install has its
    ASID registered, as the runtime store registers it). -/
theorem bootFromPlatform_asidTable_eq (config : PlatformConfig)
    (hNoVSpace : ∀ e ∈ config.initialObjects, ∀ vs, e.obj ≠ KernelObject.vspaceRoot vs) :
    (bootFromPlatform config).state.asidTable =
    (default : SystemState).asidTable := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_asidTable_eq, foldObjects_asidTable _ _ hNoVSpace, foldIrqs_asidTable,
    mkEmpty_state_eq_default]

/-- V4-A7: The post-boot state preserves TLB from default. -/
theorem bootFromPlatform_tlb_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.tlb =
    (default : SystemState).tlb := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_tlb_eq, foldObjects_tlb, foldIrqs_tlb, mkEmpty_state_eq_default]

/-- WS-SM SM7.B: The post-boot state preserves TLB-shootdown state from
    default — boot never posts a shootdown descriptor, so the post-boot
    shootdown state is the quiescent `TlbShootdownState.initial`. -/
theorem bootFromPlatform_tlbShootdown_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.tlbShootdown =
    (default : SystemState).tlbShootdown := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_tlbShootdown_eq, foldObjects_tlbShootdown, foldIrqs_tlbShootdown,
      mkEmpty_state_eq_default]

/-- WS-SM SM7.C: after boot, every core's TLB view is the empty default —
boot never fills a TLB (it operates on page tables directly), so the
post-boot per-core TLB state is the quiescent `Vector.replicate numCores
TlbState.empty`.  Mirrors `bootFromPlatform_tlbShootdown_eq`. -/
theorem bootFromPlatform_perCoreTlb_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.perCoreTlb =
    (default : SystemState).perCoreTlb := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_perCoreTlb_eq, foldObjects_perCoreTlb, foldIrqs_perCoreTlb,
      mkEmpty_state_eq_default]

/-- WS-SM SM7.D: after boot, every core's instruction cache is the cold default
— boot loads objects and page tables but executes no user instructions through
them, so no line is filled.  The instruction-side twin of
`bootFromPlatform_perCoreTlb_eq`. -/
theorem bootFromPlatform_perCoreICache_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.perCoreICache =
    (default : SystemState).perCoreICache := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_perCoreICache_eq, foldObjects_perCoreICache,
      foldIrqs_perCoreICache, mkEmpty_state_eq_default]

/-- WS-SM SM7.D.1: boot owes no instruction-cache maintenance — it fills no
cache and destroys no mapping, so the emission ledger is the empty default.
(When the boot image itself becomes real memory, the *data*-side clean to the
Point of Unification lands with SM10.1 — see the SM7.D obligation registered in
`Architecture/CacheModel.lean`.) -/
theorem bootFromPlatform_pendingIcacheMaintenance_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.pendingIcacheMaintenance =
    (default : SystemState).pendingIcacheMaintenance := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_pendingIcacheMaintenance_eq,
      foldObjects_pendingIcacheMaintenance, foldIrqs_pendingIcacheMaintenance,
      mkEmpty_state_eq_default]

/-- WS-SM SM8.C.8: boot declassifies nothing, so the audit trail after boot is
the empty default.  The general bridge carrying `default_auditLogBounded` (the
16th `proofLayerInvariantBundle` conjunct) from the default state to any
platform-booted one. -/
theorem bootFromPlatform_declassificationAuditLog_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.declassificationAuditLog =
    (default : SystemState).declassificationAuditLog := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_declassificationAuditLog_eq,
      foldObjects_declassificationAuditLog, foldIrqs_declassificationAuditLog,
      mkEmpty_state_eq_default]

/-- WS-SM SM9.A.1a: boot drains nothing, so the audit epoch after boot is the
zero default.  Together with `bootFromPlatform_declassificationAuditLog_eq`
this is what makes a platform-booted trail well-formed *at its epoch* — the
0-anchored SM8.C predicate is the boot instance rather than an invariant that
happens to hold. -/
theorem bootFromPlatform_declassificationAuditEpoch_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.declassificationAuditEpoch =
    (default : SystemState).declassificationAuditEpoch := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_declassificationAuditEpoch_eq,
      foldObjects_declassificationAuditEpoch, foldIrqs_declassificationAuditEpoch,
      mkEmpty_state_eq_default]

/-- WS-SM SM9.B.7: boot refuses nothing, so the refusal ledger after boot is the
empty default.  The general bridge that makes "a platform-booted system has
recorded no declassification attempt" a fact about *any* configuration rather
than only about the default state — which is what a monitor's first read
depends on to distinguish a quiet system from an unexamined one. -/
theorem bootFromPlatform_declassificationRefusals_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.declassificationRefusals =
    (default : SystemState).declassificationRefusals := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_declassificationRefusals_eq,
      foldObjects_declassificationRefusals, foldIrqs_declassificationRefusals,
      mkEmpty_state_eq_default]

/-- WS-SM SM9.D.5: boot leaves every object untainted, so the taint side table
after boot is the empty default.  The general bridge that makes "a
platform-booted system carries no declassification provenance" a fact about
*any* configuration rather than only about the default state — which is what
the causal detector's base case rests on: a chain reported on a freshly booted
system must have been produced by the run, not inherited from the image. -/
theorem bootFromPlatform_declassificationTaint_eq (config : PlatformConfig) :
    (bootFromPlatform config).state.declassificationTaint =
    (default : SystemState).declassificationTaint := by
  show _ = _; unfold bootFromPlatform
  rw [applyMachineConfig_declassificationTaint_eq,
      foldObjects_declassificationTaint, foldIrqs_declassificationTaint,
      mkEmpty_state_eq_default]

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
    interruptsEnabled) are preserved from default after `bootFromPlatform`
    (the unchecked / pre-interrupts boot image).

    AK7-K (F-L4 / LOW) — boot interrupt-enable window: the Lean model's
    `bootFromPlatform` does NOT enable interrupts. The default
    `MachineState.interruptsEnabled = false` (AJ3-E) is preserved through
    boot, matching ARM64 reset state. On real hardware the Rust HAL boot
    sequence (`sele4n-hal/src/boot.rs` `rust_boot_main`) enables
    interrupts in **Phase 3** (after GIC init + timer programming) via
    `interrupts::enable_irq()`. Between MMU enable (Phase 1) and GIC init
    (Phase 3) the kernel runs with IRQs masked — this is the
    interrupt-enable window. `tests/InterruptDispatchSuite.lean` covers
    the Lean-side interrupt path.

    AK9-G (P-M06): The HAL Phase-3 enable is now MIRRORED in the Lean
    model's checked boot path: `bootFromPlatformChecked` invokes
    `bootEnableInterruptsOp` at the end of its ok-branch, so successful
    checked boots emit `interruptsEnabled = true`. See
    `bootFromPlatformChecked_ok_interruptsEnabled`. The plain
    `bootFromPlatform` retains `interruptsEnabled = false` for
    negative-state / boot-invariant-bridge contexts that need the
    reset-state semantics. -/
theorem bootFromPlatform_machine_non_config_fields (config : PlatformConfig) :
    (bootFromPlatform config).state.machine.regs = (default : SystemState).machine.regs ∧
    (bootFromPlatform config).state.machine.memory = (default : SystemState).machine.memory ∧
    (bootFromPlatform config).state.machine.timer = (default : SystemState).machine.timer ∧
    (bootFromPlatform config).state.machine.systemRegisters = (default : SystemState).machine.systemRegisters ∧
    (bootFromPlatform config).state.machine.interruptsEnabled = (default : SystemState).machine.interruptsEnabled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (show _ = _; unfold bootFromPlatform; simp [applyMachineConfig, foldObjects_machine, foldIrqs_machine, mkEmpty_state_eq_default, MachineState.regs, MachineState.regsOnCore])

/-- **WS-SM SM4.G**: the idle-thread boot state's boot-core current thread is in
    the active domain — the idle thread's domain `⟨0⟩` equals the boot active
    domain `⟨0⟩` (so the idle thread is legitimately schedulable, not stranded
    in a foreign domain).  This is the `currentThreadInActiveDomain` conjunct of
    the *extended* scheduler bundle, established for the idle-thread state (the
    plain `bootFromPlatform` discharges it vacuously via `current = none`; the
    idle path discharges it substantively via the idle TCB's domain). -/
theorem bootFromPlatformWithIdleThreads_currentThreadInActiveDomain (config : PlatformConfig) :
    SeLe4n.Kernel.currentThreadInActiveDomain (bootFromPlatformWithIdleThreads config).state := by
  have hCur := bootFromPlatformWithIdleThreads_all_cores_have_idle config
    SeLe4n.Kernel.Concurrency.bootCoreId
  have hAD : (bootFromPlatformWithIdleThreads config).state.scheduler.activeDomainOnCore
      SeLe4n.Kernel.Concurrency.bootCoreId = ⟨0⟩ := by
    unfold bootFromPlatformWithIdleThreads
    rw [foldl_installIdleThread_activeDomainOnCore, bootFromPlatform_scheduler_eq]
    exact (default_state_perCoreInitialized SeLe4n.Kernel.Concurrency.bootCoreId).2.2.2.1
  simp only [SeLe4n.Kernel.currentThreadInActiveDomain, hCur.1, hCur.2, hAD]
  rfl

/-- **WS-SM SM4.G**: the idle-thread boot state satisfies the **full** scheduler
    invariant bundle (all 9 conjuncts), not merely the base triad — the stronger
    soundness claim that the installed idle-thread state is a fully scheduler-valid
    boot state.  The `∀ tid ∈ runnable` conjuncts (`timeSlicePositive`,
    `edfCurrentHasEarliestDeadline`'s inner quantifier, `runnableThreadsAreTCBs`,
    `schedulerPriorityMatch`) hold vacuously (empty run queue);
    `currentTimeSlicePositive` via the idle TCB's `timeSlice = 5`;
    `contextMatchesCurrent` because the boot machine registers and the idle TCB's
    `registerContext` are both the default `RegisterFile`
    (`bootFromPlatform_machine_non_config_fields`); `domainTimeRemainingPositive`
    via the default `5`; `domainScheduleEntriesPositive` vacuously (empty domain
    schedule).  Unlike the plain `bootFromPlatform` Full bundle (which discharges
    every current-thread conjunct vacuously via `current = none`), the idle path
    discharges `currentTimeSlicePositive` / `contextMatchesCurrent` substantively
    against the live idle TCB. -/
theorem bootFromPlatformWithIdleThreads_schedulerInvariantBundleFull (config : PlatformConfig) :
    SeLe4n.Kernel.schedulerInvariantBundleFull (bootFromPlatformWithIdleThreads config).state := by
  have hCur := bootFromPlatformWithIdleThreads_all_cores_have_idle config
    SeLe4n.Kernel.Concurrency.bootCoreId
  have hNil := bootFromPlatformWithIdleThreads_runnable_nil config
  have hRegs : (bootFromPlatformWithIdleThreads config).state.machine.regs =
      (default : SystemState).machine.regs := by
    have hm : (bootFromPlatformWithIdleThreads config).state.machine =
        (bootFromPlatform config).state.machine := by
      unfold bootFromPlatformWithIdleThreads; exact foldl_installIdleThread_machine _ _
    rw [hm]; exact (bootFromPlatform_machine_non_config_fields config).1
  have hDTR : (bootFromPlatformWithIdleThreads config).state.scheduler.domainTimeRemainingOnCore
      SeLe4n.Kernel.Concurrency.bootCoreId = 5 := by
    unfold bootFromPlatformWithIdleThreads
    rw [foldl_installIdleThread_domainTimeRemainingOnCore, bootFromPlatform_scheduler_eq]
    exact (default_state_perCoreInitialized SeLe4n.Kernel.Concurrency.bootCoreId).2.2.2.2.1
  have hDS : (bootFromPlatformWithIdleThreads config).state.scheduler.domainSchedule = [] := by
    unfold bootFromPlatformWithIdleThreads
    rw [foldl_installIdleThread_domainSchedule, bootFromPlatform_scheduler_eq]
    decide
  refine ⟨bootFromPlatformWithIdleThreads_schedulerInvariantBundle config,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- timeSlicePositive (vacuous: empty run queue)
    intro tid hMem
    rw [hNil] at hMem
    exact (List.not_mem_nil hMem).elim
  · -- currentTimeSlicePositive (idle TCB timeSlice = 5 > 0)
    simp only [SeLe4n.Kernel.currentTimeSlicePositive, hCur.1, hCur.2]
    decide
  · -- edfCurrentHasEarliestDeadline (vacuous inner: empty run queue)
    simp only [SeLe4n.Kernel.edfCurrentHasEarliestDeadline, hCur.1, hCur.2]
    intro tid hMem
    rw [hNil] at hMem
    exact (List.not_mem_nil hMem).elim
  · -- contextMatchesCurrent (machine.regs = default = idle.registerContext)
    exact SeLe4n.Kernel.contextMatchesCurrent_of_regs_eq hCur.1 hCur.2 (hRegs.trans rfl)
  · -- runnableThreadsAreTCBs (vacuous: empty run queue)
    intro tid hMem
    rw [hNil] at hMem
    exact (List.not_mem_nil hMem).elim
  · -- schedulerPriorityMatch (vacuous: empty run queue / empty bucket index)
    intro tid hMem
    have hFlat : tid ∈ (bootFromPlatformWithIdleThreads config).state.scheduler.runnable :=
      (SeLe4n.Kernel.RunQueue.mem_toList_iff_mem _ tid).mpr hMem
    rw [hNil] at hFlat
    exact (List.not_mem_nil hFlat).elim
  · -- domainTimeRemainingPositive (= 5 > 0)
    unfold SeLe4n.Kernel.domainTimeRemainingPositive
    rw [hDTR]
    decide
  · -- domainScheduleEntriesPositive (vacuous: empty domain schedule)
    intro e he
    rw [hDS] at he
    exact (List.not_mem_nil he).elim

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

    **WS-RC R3 (DEEP-BOOT-01)**: VSpaceRoots are now admitted iff they
    satisfy `Platform.RPi5.VSpaceBoot.bootSafeVSpaceRoot` (asid bounded,
    every mapping W^X compliant, at least one mapping present, every
    physical address fits within the BCM2712 44-bit PA space, and — per
    the third-audit hardening — every virtual address is canonical
    (< 2^48)).  The `installBootVSpaceRoot` builder operation (defined
    above) registers the boot VSpaceRoot's ASID in `asidTable` so
    subsequent VSpace operations can resolve it via the standard
    `resolveAsidRoot` path.  Previously this clause was
    `(∀ vs, obj ≠ .vspaceRoot vs)`, rendering the proven-W^X-compliant
    `rpi5BootVSpaceRoot` data structure inert at boot time.

    See `SeLe4n/Platform/RPi5/VSpaceBoot.lean` for the substantive
    well-formedness predicates and the
    `rpi5BootVSpaceRoot_bootSafe` discharge witness. -/
def bootSafeObject (obj : KernelObject) : Prop :=
  -- Endpoints must have empty queues (no thread references)
  (∀ ep, obj = .endpoint ep →
    ep.sendQ.head = none ∧ ep.sendQ.tail = none ∧
    ep.receiveQ.head = none ∧ ep.receiveQ.tail = none) ∧
  -- Notifications must be idle with empty wait lists and no pending badge
  -- WS-RC R4.C: `.val = []` references the underlying List projection.
  (∀ notif, obj = .notification notif →
    notif.state = .idle ∧ notif.waitingThreads.val = [] ∧ notif.pendingBadge = none) ∧
  -- CNodes must satisfy slot-count bound, depth consistency, and badge validity
  -- WS-SM SM6.D / PR #822 Phase H (#1.a): a boot CNode holds no reply capabilities —
  -- reply caps are minted at runtime (`mintReplyCap`) from retyped Reply objects, never
  -- planted at boot, so a boot reply cap could only dangle.  This makes the
  -- `replyCapPointsToValidReply` conjunct of `capabilityInvariantBundle` vacuously true
  -- for the boot state.
  (∀ cn, obj = .cnode cn →
    cn.slotCountBounded ∧ cn.depth ≤ maxCSpaceDepth ∧
    (cn.bitsConsumed > 0 → cn.wellFormed) ∧
    (∀ slot cap badge, cn.lookup slot = some cap →
      cap.badge = some badge → badge.valid) ∧
    (∀ slot cap rid, cn.lookup slot = some cap →
      cap.target ≠ .replyCap rid)) ∧
  -- TCBs must have clean boot state: no pending messages, ready IPC state,
  -- no queue links (queueNext/queuePrev/queuePPrev = none, PR #889 review
  -- round 8 for the third), no timeout budget
  (∀ tcb, obj = .tcb tcb →
    tcb.pendingMessage = none ∧ tcb.ipcState = .ready ∧
    tcb.queueNext = none ∧ tcb.queuePrev = none ∧ tcb.queuePPrev = none ∧
    tcb.timeoutBudget = none ∧
    tcb.schedContextBinding = .unbound ∧
    tcb.replyObject = none ∧
    tcb.pendingReceiveReply = none ∧
    -- PR #889 review: neither current nor queued at boot ⟹ `.Inactive`.
    tcb.threadState = .Inactive) ∧
  -- WS-BP BP3.2: a configured VSpaceRoot is a thread's — admitted iff
  -- bootSafeUserVSpaceRoot (a user ASID, no mappings)
  (∀ vs, obj = .vspaceRoot vs →
    SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeUserVSpaceRoot vs) ∧
  -- Z9-I: SchedContexts must be well-formed and unbound at boot, and — WS-OD
  -- OD2.1 — must head no reply stack: every admissible boot Reply is inert,
  -- so a config-supplied `scReply` could only dangle.
  --
  -- **WS-HP HP10.3, corrected at `v0.35.97`**: and no recorded reservation
  -- origin.  HP10.3 added that conjunct to the Bool mirror
  -- (`bootSafeSchedContextCheck`) and to the soundness bridge
  -- (`bootSafeObjectCheck_sound`, then `…_sound_structural`) and **not here**, so this
  -- Prop-level API — the one the post-boot safety theorems are stated over —
  -- certified a configuration the live validator rejects, carrying a loan
  -- history no boot state can have made.  One question, two answers, with the
  -- executable side the stricter: the direction that reads as coverage.
  (∀ sc, obj = .schedContext sc →
    schedContextWellFormed sc ∧ sc.boundThread = none ∧ sc.scReply = none ∧
      sc.donationOrigin = none) ∧
  -- WS-SM SM6.D: a boot Reply is inert — no blocked caller and no reply-stack
  -- link in either direction.
  (∀ r, obj = .reply r →
    r.caller = none ∧ r.prev = none ∧ r.next = none) ∧
  -- The `v0.36.2` audit: a boot untyped is pristine — nothing carved from it
  -- and no ancestry.  The one boot object this predicate had no clause for,
  -- while `bootSafeUntypedCheck` accepted every record: a configuration could
  -- ship `watermark = regionSize` (nothing retypeable) or `children` naming
  -- objects that do not exist, and no theorem was false because none read
  -- these fields.  Stated at the end so every positional projection into
  -- this conjunction is unchanged.
  (∀ ut, obj = .untyped ut →
    ut.watermark = 0 ∧ ut.children = [] ∧ ut.parent = none) ∧
  -- **WS-BP BP7.1**: and no boot object is a frame.  A frame is authority over
  -- the page at its `base`; the executable check refuses every configured one
  -- (`bootSafeObjectCheck`'s `.frame` arm), and this is that refusal's Prop
  -- side, stated in the same cut so the two cannot answer differently.
  (∀ f, obj ≠ .frame f)

/-- V4-A4: A PlatformConfig is boot-safe if all initial objects satisfy
    boot safety constraints. This is the standard precondition for
    extending the invariant bridge to non-empty configs. -/
def PlatformConfig.bootSafe (config : PlatformConfig) : Prop :=
  ∀ entry, entry ∈ config.initialObjects → bootSafeObject entry.obj

/-- **WS-BP BP3.2**: the Prop-level mirror of
    `bootSafeObjectCheck_refuses_rpi5BootVSpaceRoot` — the kernel's boot root is
    not a boot-safe *configured* object, since its ASID is the kernel's.
    Replaces `bootSafeObject_admits_rpi5BootVSpaceRoot` (WS-RC R3). -/
theorem not_bootSafeObject_rpi5BootVSpaceRoot :
    ¬ bootSafeObject
        (KernelObject.vspaceRoot
          SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot) := by
  intro h
  have hUser := h.2.2.2.2.1 _ rfl
  rw [← SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeUserVSpaceRootCheck_iff,
    SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot_not_bootSafeUser] at hUser
  exact Bool.false_ne_true hUser

-- ============================================================================
-- WS-BP BP3.5: the shape of every object a boot installs
-- ============================================================================

/-- **WS-BP BP3.5**: what the proof-layer invariant bundle reads of an object
    in a freshly booted state.  `bootSafeObject` with two arms widened to admit
    the two kinds of object the *checked* boot installs beyond the
    configuration:

    * **A TCB may be queued.**  The per-core idle threads the boot enqueues
      are `.Ready` where a configured thread is `.Inactive`, so the TCB arm
      drops the thread-state clause — which no bundle conjunct reads — and
      keeps the nine clean-state fields every conjunct does.
    * **A VSpace root may map.**  The binding's boot root maps the kernel,
      where a thread's maps nothing, so the VSpace arm asks only the three
      per-mapping facts the bundle reads (`bootVSpaceRootMappingsSafe`); the
      ASID facts are the table's, stated separately.

    The arms sit at `bootSafeObject`'s positions, so a projection written
    against one reads the same field of the other. -/
def bootObjectShape (obj : KernelObject) : Prop :=
  (∀ ep, obj = .endpoint ep →
    ep.sendQ.head = none ∧ ep.sendQ.tail = none ∧
    ep.receiveQ.head = none ∧ ep.receiveQ.tail = none) ∧
  (∀ notif, obj = .notification notif →
    notif.state = .idle ∧ notif.waitingThreads.val = [] ∧ notif.pendingBadge = none) ∧
  (∀ cn, obj = .cnode cn →
    cn.slotCountBounded ∧ cn.depth ≤ maxCSpaceDepth ∧
    (cn.bitsConsumed > 0 → cn.wellFormed) ∧
    (∀ slot cap badge, cn.lookup slot = some cap →
      cap.badge = some badge → badge.valid) ∧
    (∀ slot cap rid, cn.lookup slot = some cap →
      cap.target ≠ .replyCap rid)) ∧
  (∀ tcb, obj = .tcb tcb →
    tcb.pendingMessage = none ∧ tcb.ipcState = .ready ∧
    tcb.queueNext = none ∧ tcb.queuePrev = none ∧ tcb.queuePPrev = none ∧
    tcb.timeoutBudget = none ∧
    tcb.schedContextBinding = .unbound ∧
    tcb.replyObject = none ∧
    tcb.pendingReceiveReply = none) ∧
  (∀ vs, obj = .vspaceRoot vs →
    SeLe4n.Platform.RPi5.VSpaceBoot.bootVSpaceRootMappingsSafe vs) ∧
  (∀ sc, obj = .schedContext sc →
    schedContextWellFormed sc ∧ sc.boundThread = none ∧ sc.scReply = none ∧
      sc.donationOrigin = none) ∧
  (∀ r, obj = .reply r →
    r.caller = none ∧ r.prev = none ∧ r.next = none)

/-- **WS-BP BP3.5**: a boot-safe configured object has the boot shape.  A
    configured VSpace root is a thread's, which maps nothing; reading that per
    lookup needs its mapping table's `invExt`, which every object entry
    carries. -/
theorem bootSafeObject_bootObjectShape {obj : KernelObject} (h : bootSafeObject obj)
    (hMappings : ∀ vs, obj = .vspaceRoot vs → vs.mappings.invExt) :
    bootObjectShape obj :=
  ⟨h.1, h.2.1, h.2.2.1,
   fun tcb hEq =>
     let t := h.2.2.2.1 tcb hEq
     ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
      t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1⟩,
   fun vs hEq =>
     SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeUserVSpaceRoot_mappingsSafe
       (h.2.2.2.2.1 vs hEq) (hMappings vs hEq),
   h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- **WS-BP BP3.5**: the binding's boot root has the boot shape — every arm
    but the VSpace one is vacuous, and that one is its checks read per
    mapping. -/
theorem bootSafeVSpaceRoot_bootObjectShape {vs : VSpaceRoot}
    (h : SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeVSpaceRoot vs) :
    bootObjectShape (.vspaceRoot vs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro x hx <;> cases hx
  exact SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeVSpaceRoot_mappingsSafe h

/-- **WS-BP BP3.5**: an enqueued idle TCB has the boot shape — it is
    `createIdleThread`'s structure defaults with `threadState := .Ready`, and
    every clean-state field the TCB arm reads is a default. -/
theorem queuedIdleThread_bootObjectShape (c : SeLe4n.Kernel.Concurrency.CoreId) :
    bootObjectShape (.tcb (queuedIdleThread c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro x hx <;> cases hx
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
    have hNewBase : ∀ (oid : SeLe4n.ObjId) (obj' : KernelObject), (createBootObject ist e).state.objects[oid]? = some obj' → bootSafeObject obj' := by
      intro oid₂ obj₂ hLookup₂
      have hObjInvExt : ist.state.objects.invExt := ist.hAllTables.1.1
      simp only [createBootObject_objects, RHTable_getElem?_eq_get?] at hLookup₂
      by_cases hEq : e.id = oid₂
      · subst hEq
        rw [RHTable.getElem?_insert_self ist.state.objects e.id e.obj hObjInvExt] at hLookup₂
        cases hLookup₂; exact heSafe
      · have hNe : ¬((e.id == oid₂) = true) := by intro heq; exact hEq (eq_of_beq heq)
        rw [RHTable.getElem?_insert_ne ist.state.objects e.id oid₂ e.obj hNe hObjInvExt] at hLookup₂
        exact hBase oid₂ obj₂ (by simp only [RHTable_getElem?_eq_get?]; exact hLookup₂)
    exact ih (createBootObject ist e) hNewBase hRestSafe

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
-- AK8-A (C-M01): Untyped-region reachability through boot fold
-- ============================================================================

/-- AK8-A: Reachability lemma — any object in the fold result either came from
one of the entries or was in the base state. Proven by induction on the entry
list, using `createObject_objects` to track each `insert`. -/
private theorem foldObjects_objects_reachable
    (objs : List ObjectEntry) :
    ∀ (ist : IntermediateState) (oid : SeLe4n.ObjId) (obj : KernelObject),
    (foldObjects objs ist).state.objects[oid]? = some obj →
    (∃ e ∈ objs, e.id = oid ∧ e.obj = obj) ∨
    ist.state.objects[oid]? = some obj := by
  induction objs with
  | nil => intro ist oid obj h; exact Or.inr h
  | cons e rest ih =>
    intro ist oid obj hLookup
    have hInvExt : ist.state.objects.invExt := ist.hAllTables.1.1
    rcases ih (createBootObject ist e) oid obj hLookup with
      ⟨e', hMem, hId, hObj⟩ | hBase
    · -- Entry e' is in rest; lift membership to (e :: rest)
      exact Or.inl ⟨e', List.mem_cons_of_mem _ hMem, hId, hObj⟩
    · -- Reached base via createBootObject; case-split on whether oid = e.id
      simp only [createBootObject_objects, RHTable_getElem?_eq_get?] at hBase
      by_cases hEq : e.id = oid
      · subst hEq
        rw [RHTable.getElem?_insert_self ist.state.objects e.id e.obj hInvExt] at hBase
        cases hBase; exact Or.inl ⟨e, List.mem_cons_self .., rfl, rfl⟩
      · have hNe : ¬((e.id == oid) = true) := by
          intro heq; exact hEq (eq_of_beq heq)
        rw [RHTable.getElem?_insert_ne ist.state.objects e.id oid e.obj hNe hInvExt] at hBase
        exact Or.inr (by simp only [RHTable_getElem?_eq_get?]; exact hBase)

/-- **WS-SM SM4.G** (plan §3.7): canonical-platform discharge of
    `idleSlotsFreshAt`.  When every config object's `ObjId` lies below
    `idleThreadIdBase` (the 16-bit ObjId space the canonical platforms — RPi5,
    Sim — assign their objects from), no config object occupies an idle slot
    (every idle slot's value is `idleThreadIdBase + c.val ≥ idleThreadIdBase`),
    so the boot state's idle slots are all empty.  This makes the
    `idleThreadIdBase` disjointness rationale a *proven* property and is the
    hypothesis-discharge for
    `bootFromPlatformWithIdleThreads_preserves_platform_objects`. -/
theorem idleSlotsFreshAt_of_initialObjects_below_base
    (config : PlatformConfig)
    (hBelow : ∀ e ∈ config.initialObjects, e.id.val < idleThreadIdBase) :
    idleSlotsFreshAt (bootFromPlatform config) := by
  intro c
  -- Every idle slot's ObjId value is ≥ idleThreadIdBase.
  have hGe : idleThreadIdBase ≤ (idleThreadId c).toObjId.val := by
    show idleThreadIdBase ≤ idleThreadIdBase + c.val
    exact Nat.le_add_right _ _
  cases hLook : (bootFromPlatform config).state.objects[(idleThreadId c).toObjId]? with
  | none => rfl
  | some o =>
    exfalso
    -- `applyMachineConfig` preserves objects; trace the lookup into `foldObjects`.
    have hLook' : (foldObjects config.initialObjects
        (foldIrqs config.irqTable mkEmptyIntermediateState)).state.objects[(idleThreadId c).toObjId]? =
          some o := by
      have hb := hLook
      unfold bootFromPlatform at hb
      rwa [applyMachineConfig_objects_eq] at hb
    rcases foldObjects_objects_reachable config.initialObjects _ _ _ hLook' with
      ⟨e, hMem, hId, _hObj⟩ | hBase
    · -- A config object lives at the idle slot ⟹ its id ≥ base, contradicting hBelow.
      have hlt : (idleThreadId c).toObjId.val < idleThreadIdBase := hId ▸ hBelow e hMem
      omega
    · -- The base (foldIrqs over the empty intermediate state) has no objects.
      rw [foldIrqs_objects, mkEmpty_state_eq_default] at hBase
      have hEmpty : (default : SystemState).objects[(idleThreadId c).toObjId]? = none := by
        simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
      rw [hEmpty] at hBase
      simp at hBase

/-- **WS-RR RR5.13** (PR #889 review): the reservation `PlatformConfig.wellFormed`
    now decides is exactly what `idleSlotsFreshAt` needs — a config that keeps
    its objects out of the idle slots boots into a state whose idle slots are
    empty.  Generalises `idleSlotsFreshAt_of_initialObjects_below_base` (whose
    hypothesis, that every object sits *below* the idle range, is sufficient
    but not necessary) to the decided predicate. -/
theorem idleSlotsFreshAt_of_idleSlotsReserved
    (config : PlatformConfig) (h : idleSlotsReserved config = true) :
    idleSlotsFreshAt (bootFromPlatform config) := by
  have hObjs := idleSlotsReserved_initialObjects config h
  intro c
  cases hLook : (bootFromPlatform config).state.objects[(idleThreadId c).toObjId]? with
  | none => rfl
  | some o =>
    exfalso
    have hLook' : (foldObjects config.initialObjects
        (foldIrqs config.irqTable mkEmptyIntermediateState)).state.objects[(idleThreadId c).toObjId]? =
          some o := by
      have hb := hLook
      unfold bootFromPlatform at hb
      rwa [applyMachineConfig_objects_eq] at hb
    rcases foldObjects_objects_reachable config.initialObjects _ _ _ hLook' with
      ⟨e, hMem, hId, _hObj⟩ | hBase
    · exact idleThreadId_toObjId_ne_of_not_isIdleObjId e.id (hObjs e hMem) c hId.symm
    · rw [foldIrqs_objects, mkEmpty_state_eq_default] at hBase
      have hEmpty : (default : SystemState).objects[(idleThreadId c).toObjId]? = none := by
        simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
      rw [hEmpty] at hBase
      simp at hBase

/-- AK8-A: If the base-state has no untyped objects and the config satisfies
`untypedRegionsDisjoint`, the post-boot object store satisfies the runtime
`untypedRegionsDisjoint` invariant. Uses `foldObjects_objects_reachable` to
trace each post-boot untyped back to its entry, then discharges via the
config-level disjointness. -/
private theorem bootFromPlatform_untypedRegionsDisjoint
    (config : PlatformConfig)
    (hUntypedDisj : config.untypedRegionsDisjoint) :
    Kernel.untypedRegionsDisjoint (bootFromPlatform config).state := by
  intro oid₁ oid₂ ut₁ ut₂ h₁ h₂ hNe hChildren₁ hChildren₂
  unfold bootFromPlatform at h₁ h₂
  -- Trace oid₁'s untyped back to initialObjects.
  rcases foldObjects_objects_reachable config.initialObjects
    (foldIrqs config.irqTable mkEmptyIntermediateState) oid₁ _ h₁ with
    ⟨e₁, hMem₁, hId₁, hObj₁⟩ | hBase₁
  · -- oid₁ came from entry e₁ ∈ initialObjects.
    rcases foldObjects_objects_reachable config.initialObjects
      (foldIrqs config.irqTable mkEmptyIntermediateState) oid₂ _ h₂ with
      ⟨e₂, hMem₂, hId₂, hObj₂⟩ | hBase₂
    · -- Both oid₁ and oid₂ from entries.
      -- e₁.id = oid₁ ≠ oid₂ = e₂.id, so e₁.id ≠ e₂.id.
      have hIdNe : e₁.id ≠ e₂.id := by rw [hId₁, hId₂]; exact hNe
      -- Transport the children-exclusion hypotheses from post-boot ObjIds
      -- (oid₁ / oid₂) to entry-level IDs (e₁.id / e₂.id) via hId₁ / hId₂.
      have hChildrenE₁ : ∀ c ∈ ut₁.children, c.objId ≠ e₂.id := by
        intro c hc; rw [hId₂]; exact hChildren₁ c hc
      have hChildrenE₂ : ∀ c ∈ ut₂.children, c.objId ≠ e₁.id := by
        intro c hc; rw [hId₁]; exact hChildren₂ c hc
      exact hUntypedDisj e₁ e₂ ut₁ ut₂ hMem₁ hMem₂ hIdNe hObj₁ hObj₂ hChildrenE₁ hChildrenE₂
    · -- oid₂ in foldIrqs base — but foldIrqs doesn't touch objects, and base is empty.
      rw [foldIrqs_objects] at hBase₂
      have hEmpty : mkEmptyIntermediateState.state.objects[oid₂]? = none := by
        rw [mkEmpty_state_eq_default]; exact RHTable_get?_empty 16 (by omega)
      rw [hEmpty] at hBase₂; exact absurd hBase₂ (by simp)
  · -- oid₁ in foldIrqs base — impossible.
    rw [foldIrqs_objects] at hBase₁
    have hEmpty : mkEmptyIntermediateState.state.objects[oid₁]? = none := by
      rw [mkEmpty_state_eq_default]; exact RHTable_get?_empty 16 (by omega)
    rw [hEmpty] at hBase₁; exact absurd hBase₁ (by simp)

-- ============================================================================
-- V4-A8: Composition — proofLayerInvariantBundle for general configs
-- ============================================================================

/-! ### V4-A8: General Boot Invariant Bridge

The composition theorem shows that for ANY `PlatformConfig`, the post-boot
state satisfies all sixteen components of `proofLayerInvariantBundle`.

**WS-BP BP3.5**: the argument is stated once, over a *boot-shaped* state
(`proofLayerInvariantBundle_of_bootShape`): every object satisfies
`bootObjectShape`, the untouched fields are their defaults
(`bootQuiescentFields`), the ASID table is consistent with the roots, and the
scheduler supplies its own run-queue facts.  The unchecked boot and the
production boot are its two instances.
-/

/-- **WS-BP BP3.5**: the fields a freshly booted state leaves at their defaults
    — the capability derivation tree, the service registries, every TLB and
    instruction-cache view, the shootdown state and the audit trail.  Boot
    writes none of them: it installs objects, registers ASIDs and enqueues the
    idle threads, and each of those is framed here. -/
def bootQuiescentFields (st : SystemState) : Prop :=
  st.cdt = (default : SystemState).cdt ∧
  st.cdtNodeSlot = (default : SystemState).cdtNodeSlot ∧
  st.services = (default : SystemState).services ∧
  st.serviceRegistry = (default : SystemState).serviceRegistry ∧
  st.tlb = (default : SystemState).tlb ∧
  st.tlbShootdown = (default : SystemState).tlbShootdown ∧
  st.perCoreTlb = (default : SystemState).perCoreTlb ∧
  st.perCoreICache = (default : SystemState).perCoreICache ∧
  st.declassificationAuditLog = (default : SystemState).declassificationAuditLog

/-- **WS-BP BP3.5**: **the proof-layer invariant bundle of any boot-shaped
    state** — one argument for every boot this tree has, stated over what a
    boot leaves rather than over one boot's construction.

    What a boot leaves splits cleanly.  The **objects** are boot-shaped
    (`bootObjectShape`): every conjunct that quantifies over the object store
    — the capability, IPC, lifecycle, service, cross-subsystem and
    SchedContext halves, and the VSpace bundle's per-mapping half — is derived
    here from that shape alone.  The **ASID table** is consistent with the
    roots, which is the VSpace bundle's other half (uniqueness and cross-ASID
    isolation both follow from it).  The **scheduler** facts that read the
    run queue are the scheduler's, supplied by the boot that built it, since
    only it knows what it enqueued; every object-side question about a queued
    thread — its IPC readiness, its budget, its binding — is again the shape's.
    And the **untouched fields** are their defaults (`bootQuiescentFields`).

    `bootFromPlatform_proofLayerInvariantBundle_general` (the unchecked boot,
    empty scheduler) and `bootFromPlatformCheckedWithIdleThreadsFor_proofLayerInvariantBundle`
    (the production boot: checked, VSpace roots installed, idle threads
    enqueued) are its two instances; the proof lived inside the first until
    the second needed it, and a second copy of it would be two answers to one
    question. -/
theorem proofLayerInvariantBundle_of_bootShape (ist : IntermediateState)
    (hShape : ∀ (oid : SeLe4n.ObjId) (obj : KernelObject),
      ist.state.objects[oid]? = some obj → bootObjectShape obj)
    (hFields : bootQuiescentFields ist.state)
    (hAsidTable : Architecture.asidTableConsistent ist.state)
    (hUntyped : Kernel.untypedRegionsDisjoint ist.state)
    (hSched : schedulerInvariantBundleFull ist.state)
    (hCur : ist.state.scheduler.currentOnCore bootCoreId = none)
    (hReplenish : replenishQueueValid ist.state)
    (hEffective : effectiveParamsMatchRunQueue ist.state) :
    Architecture.proofLayerInvariantBundle ist.state := by
  obtain ⟨hCdt, hCdtNS, hSvc, hSvcR, hTlb, hShoot, hPerCoreTlb, hPerCoreICache,
    hAudit⟩ := hFields
  have hAllTables := ist.hAllTables
  have hBS := hShape
  have h1 := hSched
  -- lookupService returns none (services empty)
  have hLookupSvcNone : ∀ sid,
      lookupService ist.state sid = none := by
    intro sid; unfold lookupService; rw [hSvc]
    exact RHTable_get?_empty 16 (by omega)
  -- 2. capabilityInvariantBundle
  have hCapBundle : capabilityInvariantBundle ist.state := by
    -- WS-RC R4.A.6: bundle has 6 conjuncts (cspaceSlotUnique dropped).
    -- The per-CNode `slotsUnique` invariant is carried structurally on every
    -- `UniqueSlotMap` value; the builder-phase `hSlots` witness is preserved
    -- by the boot path for backward compatibility but no longer flows through
    -- this bundle.
    refine ⟨?_, ?_, ?_, ?_, ?_, hAllTables.1.1, ?_⟩
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
      show ist.state.cdt.edgeWellFounded
      rw [hCdt]; exact CapDerivationTree.empty_edgeWellFounded
    · -- cspaceDepthConsistent
      intro cnodeId cn hObj
      have hCN := (hBS cnodeId _ hObj).2.2.1 cn rfl
      exact ⟨hCN.2.1, hCN.2.2.1⟩
    · -- replyCapPointsToValidReply: boot CNodes hold no reply caps (`bootSafeObject`),
      -- so the reply-cap hypothesis is contradicted and the conjunct is vacuous.
      intro oid cn slot cap rid hObj hLookupSlot hTgt
      exact absurd hTgt (((hBS oid _ hObj).2.2.1 cn rfl).2.2.2.2 slot cap rid hLookupSlot)
  -- 5. lifecycleInvariantBundle
  have hLifeBundle : lifecycleInvariantBundle ist.state :=
    ist.hLifecycleConsistent
  -- 3. ipcInvariantFull (WS-RC R4.C.7: 15 sub-components after uniqueWaiters retirement)
  have hIpcFull : ipcInvariantFull ist.state := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ipcInvariant: notifications well-formed
      intro oid ntfn hObj
      have hNtfn := (hBS oid _ hObj).2.1 ntfn rfl
      show notificationInvariant ntfn
      unfold notificationInvariant notificationQueueWellFormed
      rw [hNtfn.1]; exact ⟨hNtfn.2.1, hNtfn.2.2⟩
    · -- dualQueueSystemInvariant
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- all endpoints have well-formed queues
        intro epId ep hObj
        have hEp := (hBS epId _ hObj).1 ep rfl
        show dualQueueEndpointWellFormed epId ist.state
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
      · -- WS-RR RR8.3: the pairing.  `bootSafeObjectCheck` admits a TCB only
        -- with all three queue links empty, which is what the strengthened
        -- `none` arm asks (`v0.35.99`): carrying no `queuePPrev` is the claim
        -- that the thread is on no queue, so its `queuePrev` is part of the
        -- claim rather than unconstrained.
        intro tid tcb hObj
        exact TCB.queuePPrevAgreesWithPrev_of_pprev_none
          ((hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl).2.2.2.2.1
          ((hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl).2.2.2.1
      · -- **PR #897 review (`v0.35.106`)**: head-disjointness is vacuous on the
        -- boot state, whose endpoints `bootSafeObjectCheck` admits only with both
        -- queues empty — so no endpoint has a head to collide.
        intro epA _ eA _ hd recvA _ hEpA _ hA _
        have hEp := (hBS epA _ hEpA).1 eA rfl
        cases recvA with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at hA
            rw [hEp.1] at hA; exact absurd hA (by simp)
        | true =>
            simp only [↓reduceIte] at hA
            rw [hEp.2.2.1] at hA; exact absurd hA (by simp)
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
        exact hCN.2.2.2.1 slot cap badge hSlotLookup hBadge
    · -- blockedThreadsPendingMessageConsistent
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
      rw [hTcb.2.2.2.2.2.1] at hTimeout; exact absurd hTimeout (by simp)
    · -- Z7: donationChainAcyclic (vacuous: boot TCBs have .unbound binding)
      intro tid1 _ tcb1 _ _ _ h1 _ hB1 _
      have hTcb1 := (hBS tid1.toObjId _ h1).2.2.2.1 tcb1 rfl
      rw [hTcb1.2.2.2.2.2.2.1] at hB1; cases hB1
    · -- Z7: donationOwnerValid (vacuous: no donated bindings at boot)
      intro tid tcb _ _ h hBinding
      have hTcb := (hBS tid.toObjId _ h).2.2.2.1 tcb rfl
      rw [hTcb.2.2.2.2.2.2.1] at hBinding; cases hBinding
    · -- Z7: passiveServerIdle (boot TCBs have ipcState = .ready)
      intro tid tcb h _ _ _
      have hTcb := (hBS tid.toObjId _ h).2.2.2.1 tcb rfl
      left; exact hTcb.2.1
    · -- Z7: donationBudgetTransfer (vacuous: all TCBs have .unbound → scId? = none)
      intro tid1 _ tcb1 _ _ h1 _ _ hB1 _
      have hTcb1 := (hBS tid1.toObjId _ h1).2.2.2.1 tcb1 rfl
      simp [hTcb1.2.2.2.2.2.2.1, SchedContextBinding.scId?] at hB1
    · -- AJ1-B: blockedOnReplyHasTarget (boot TCBs have ipcState = .ready)
      intro tid tcb _ _ hObj hIpc
      have hTcb := (hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl
      rw [hTcb.2.1] at hIpc; cases hIpc
    · -- WS-SM SM6.D (PR #822): replyCallerLinkage (16th, vacuous — boot TCBs have
      -- replyObject = none and boot Replies have caller = none) ∧
      -- pendingReceiveReplyWellFormed (17th, vacuous — boot TCBs have
      -- pendingReceiveReply = none).
      refine ⟨⟨⟨fun tid tcb rid hObj hRep => ?_, fun rid r tid hObj hCaller => ?_⟩,
         fun tid tcb ep rt hObj hIpc => ?_⟩,
        ⟨fun tid tcb rid hObj hRep => ?_,
         fun tid₁ _ tcb₁ _ _ hObj₁ _ hRep₁ _ => ?_⟩,
        fun tidA _ tcbA _ _ _ _ hA _ hBA _ => ?_,
        ?_,
        ?_⟩
      · have hTcb := (hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl
        rw [hTcb.2.2.2.2.2.2.2.1] at hRep; cases hRep
      · have hR := (hBS rid.toObjId _ hObj).2.2.2.2.2.2 r rfl
        rw [hR.1] at hCaller; cases hCaller
      · -- WS-SM SM6.D (#7.4): replyCallerLinkage third clause (vacuous — boot TCBs
        -- have ipcState = .ready, never .blockedOnReply, so no caller needs a reply).
        have hTcb := (hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl
        rw [hTcb.2.1] at hIpc; cases hIpc
      · have hObjRaw := (SystemState.getTcb?_eq_some_iff _ tid tcb).mp hObj
        have hTcb := (hBS tid.toObjId _ hObjRaw).2.2.2.1 tcb rfl
        rw [hTcb.2.2.2.2.2.2.2.2] at hRep; cases hRep
      · -- pendingReceiveReplyWellFormed uniqueness (17th.2): boot TCBs carry no stash.
        have hObjRaw := (SystemState.getTcb?_eq_some_iff _ tid₁ tcb₁).mp hObj₁
        have hTcb := (hBS tid₁.toObjId _ hObjRaw).2.2.2.1 tcb₁ rfl
        rw [hTcb.2.2.2.2.2.2.2.2] at hRep₁; cases hRep₁
      · -- IPC de-threading D6: donationOwnerUnique (18th, vacuous — boot TCBs are .unbound).
        have hTcb := (hBS tidA.toObjId _ hA).2.2.2.1 tcbA rfl
        rw [hTcb.2.2.2.2.2.2.1] at hBA; cases hBA
      · -- IPC de-threading D4 (Finding F-2): endpointQueueTailBlockedConsistent (19th, vacuous —
        -- boot endpoints have empty send/receive queues).
        intro epId ep tl tcb hObjEp _
        have hEp := (hBS epId _ hObjEp).1 ep rfl
        constructor
        · intro hRecv; rw [hEp.2.2.2] at hRecv; exact absurd hRecv (by simp)
        · intro hSend; rw [hEp.2.1] at hSend; exact absurd hSend (by simp)
      · -- IPC de-threading D4 Slice 2c: queueNextTargetBlocked (20th, vacuous — boot TCBs
        -- have queueNext = none, so no link antecedent can hold).
        intro a b tcbA tcbB hObjA _ hNext
        have hTcb := (hBS a.toObjId _ hObjA).2.2.2.1 tcbA rfl
        rw [hTcb.2.2.1] at hNext; exact absurd hNext (by simp)
  -- 4. ipcSchedulerCouplingInvariantBundle
  have hCouplingBundle : ipcSchedulerCouplingInvariantBundle
      ist.state := by
    refine ⟨⟨h1.1, hCapBundle, hIpcFull⟩, ?_, ?_, ?_⟩
    · -- ipcSchedulerCoherenceComponent: every boot TCB is IPC-ready, so the
      -- runnable half holds of whatever the run queue holds and the five
      -- blocked halves are vacuous.
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro tid tcb hObj _
        exact ((hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl).2.1
      · intro tid tcb _ hObj hIpc
        rw [((hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl).2.1] at hIpc; cases hIpc
      · intro tid tcb _ hObj hIpc
        rw [((hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl).2.1] at hIpc; cases hIpc
      · intro tid tcb _ hObj hIpc
        rw [((hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl).2.1] at hIpc; cases hIpc
      · intro tid tcb _ _ hObj hIpc
        rw [((hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl).2.1] at hIpc; cases hIpc
      · intro tid tcb _ hObj hIpc
        rw [((hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl).2.1] at hIpc; cases hIpc
    · -- contextMatchesCurrent
      unfold contextMatchesCurrent; rw [hCur]; trivial
    · -- currentThreadDequeueCoherent (current = none → True)
      refine ⟨?_, ?_, ?_⟩
      · unfold currentThreadIpcReady; rw [hCur]; trivial
      · unfold currentNotEndpointQueueHead; rw [hCur]; trivial
      · unfold currentNotOnNotificationWaitList; rw [hCur]; trivial
  -- 6. serviceLifecycleCapabilityInvariantBundle
  have hServiceBundle : serviceLifecycleCapabilityInvariantBundle
      ist.state := by
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
  -- 7. vspaceInvariantBundle (WS-BP BP3.5): the ASID half is the table's
  -- consistency — two roots on one ASID would be registered at one key, so the
  -- table's completeness names them the same object — and the three
  -- per-mapping conjuncts are each root's shape.
  have hAsidUnique : Architecture.vspaceAsidRootsUnique ist.state := by
    intro oid₁ oid₂ root₁ root₂ h₁ h₂ hEq
    have t₁ := hAsidTable.2 oid₁ root₁ h₁
    have t₂ := hAsidTable.2 oid₂ root₂ h₂
    rw [hEq, t₂] at t₁
    exact (Option.some.inj t₁).symm
  have hVspaceBundle : Architecture.vspaceInvariantBundle
      ist.state := by
    refine ⟨hAsidUnique, ?_, hAsidTable, ?_, ?_, ?_, ?_⟩
    · intro oid root _; exact VSpaceRoot.noVirtualOverlap_trivial root
    · intro oid root v p perms hObj hMap
      exact ((hBS oid _ hObj).2.2.2.2.1 root rfl v p perms hMap).1
    · intro oid root v p perms hObj hMap
      exact ((hBS oid _ hObj).2.2.2.2.1 root rfl v p perms hMap).2.1
    · intro oidA oidB rootA rootB hA hB hNe hEq
      exact hNe (hAsidUnique oidA oidB rootA rootB hA hB hEq)
    · intro oid root v p perms hObj hMap
      exact ((hBS oid _ hObj).2.2.2.2.1 root rfl v p perms hMap).2.2
  -- 8. crossSubsystemInvariant (Z9-D + AE5-C + AF1-B + AM4-A + AK8-A: 12 predicates)
  have hCrossBundle : crossSubsystemInvariant ist.state := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      -- WS-RC R4.C: hMem : tid ∈ notif.waitingThreads is `tid ∈ .val` via Membership.
      have hMemVal : tid ∈ notif.waitingThreads.val := hMem
      rw [hNtfn.2.1] at hMemVal; simp at hMemVal
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
      rw [hTcbProps.2.2.2.2.2.2.1] at hBinding
      simp [SchedContextBinding.scId?] at hBinding
    · -- Z9-B: schedContextNotDualBound — all TCBs have .unbound at boot, so no scId matches
      intro tid₁ tid₂ tcb₁ tcb₂ scId h₁ h₂ hB₁ hB₂
      have hTcb₁ := (hBS tid₁.toObjId _ h₁).2.2.2.1 tcb₁ rfl
      rw [hTcb₁.2.2.2.2.2.2.1] at hB₁
      simp [SchedContextBinding.scId?] at hB₁
    · -- Z9-C: schedContextRunQueueConsistent — every boot TCB is `.unbound`,
      -- so no runnable thread names a scheduling context.
      intro tid _ tcb hObj scId hBinding
      rw [((hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl).2.2.2.2.2.2.1] at hBinding
      simp [SchedContextBinding.scId?] at hBinding
    · -- AF1-B7: blockingAcyclic — all TCBs have ipcState = .ready at boot
      intro tid hMem
      -- blockingChain uses fuel = objectIndex.length. If fuel = 0, chain = [].
      -- If fuel > 0, use step lemma: chain = match blockingServer tid with ...
      -- All boot TCBs have .ready ipcState → blockingServer = none → chain = []
      cases hF : ist.state.objectIndex.length with
      | zero =>
        have : PriorityInheritance.blockingChain ist.state tid 0 = [] := rfl
        rw [show ist.state.objectIndex.length = 0 from hF] at hMem
        rw [this] at hMem; simp at hMem
      | succ n =>
        rw [show ist.state.objectIndex.length = n + 1 from hF] at hMem
        rw [PriorityInheritance.blockingChain_step] at hMem
        -- Show blockingServer returns none for tid at boot
        have hServer : PriorityInheritance.blockingServer ist.state tid = none := by
          -- The split stays over the store because `hBS` is a whole-store
          -- boot-shape fact keyed by `ObjId`; `blockingServer` now reads
          -- `getTcb?`, so the accessor is unfolded to meet it.
          cases hObj : ist.state.objects[tid.toObjId]? with
          | none => simp [PriorityInheritance.blockingServer, SystemState.getTcb?, hObj]
          | some obj =>
            cases obj with
            | tcb tcb =>
              have hReady := (hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl |>.2.1
              simp [PriorityInheritance.blockingServer, SystemState.getTcb?, hObj, hReady]
            | _ => simp [PriorityInheritance.blockingServer, SystemState.getTcb?, hObj]
        simp [hServer] at hMem
    · -- AM4-F (AL6-C.hygiene): lifecycleObjectTypeLockstep at boot.
      -- The builder's `hLifecycleConsistent` already witnesses
      -- `objectTypeMetadataConsistent`, which is semantically stronger
      -- than (and directly implies) the lockstep predicate.
      intro oid obj hObj
      have hMeta := ist.hLifecycleConsistent
      -- objectTypeMetadataConsistent: ∀ oid, lookupObjectTypeMeta st oid
      --   = (st.objects[oid]?).map KernelObject.objectType
      -- With hObj : st.objects[oid]? = some obj, the RHS is
      -- `some obj.objectType`, matching the lockstep goal.
      have := hMeta oid
      simp [SystemState.lookupObjectTypeMeta, hObj] at this
      exact this
    · -- AK8-A (C-M01): untypedRegionsDisjoint at boot.
      -- Discharged via the config-level `untypedRegionsDisjoint` precondition
      -- (passed as `hUntypedDisj`) plus the `foldObjects_objects_reachable`
      -- lemma which traces every post-boot untyped back to its entry.
      exact hUntyped
  -- 9. tlbConsistent
  have hTlbBundle : Architecture.tlbConsistent ist.state
      ist.state.tlb := by
    rw [hTlb]; exact Architecture.tlbConsistent_empty _
  -- 10. schedulerInvariantBundleExtended (Z9-G: SchedContext invariants at boot)
  have hExtBundle : schedulerInvariantBundleExtended ist.state := by
    refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- budgetPositive: every boot TCB is `.unbound`, whose budget arm is `True`.
      intro tid _
      cases hGet : ist.state.getTcb? tid with
      | none => trivial
      | some tcb =>
        have hObj := (SystemState.getTcb?_eq_some_iff _ tid tcb).mp hGet
        simp only [((hBS tid.toObjId _ hObj).2.2.2.1 tcb rfl).2.2.2.2.2.2.1]
    · -- currentBudgetPositive: current = none at boot
      simp [currentBudgetPositive, hCur]
    · -- schedContextsWellFormed: boot-safe SchedContexts are well-formed (Z9-I)
      intro oid sc hObj
      exact ((hBS oid _ hObj).2.2.2.2.2.1 sc rfl).1
    · exact hReplenish
    · -- schedContextBindingConsistent: all TCBs have .unbound at boot
      constructor
      · intro tid tcb hTcb scId hBound
        have hTcbProps := (hBS tid.toObjId _ hTcb).2.2.2.1 tcb rfl
        rw [hTcbProps.2.2.2.2.2.2.1] at hBound; cases hBound
      · intro scId sc hSc tid hBound
        -- At boot, all SchedContexts have boundThread = none (Z9-I bootSafeObject)
        have hNone := ((hBS scId.toObjId _ hSc).2.2.2.2.2.1 sc rfl).2.1
        rw [hNone] at hBound; cases hBound
    · exact hEffective
    · -- boundThreadDomainConsistent: all TCBs have .unbound at boot
      intro tid scId
      show match ist.state.objects[tid.toObjId]? with
        | some (.tcb tcb) => tcb.schedContextBinding = .bound scId → _ | _ => True
      cases hLookup : ist.state.objects[tid.toObjId]? with
      | none => trivial
      | some obj =>
        cases obj with
        | tcb tcb =>
          intro hBound
          have hTcbProps := (hBS tid.toObjId _ hLookup).2.2.2.1 tcb rfl
          rw [hTcbProps.2.2.2.2.2.2.1] at hBound; cases hBound
        | _ => trivial
  -- AG7-D: notificationWaiterConsistent — boot notifications have empty waitingThreads
  have hNtfnWaiter : notificationWaiterConsistent ist.state := by
    intro oid ntfn tid hObj hMem
    have hNtfn := (hBS oid _ hObj).2.1 ntfn rfl
    -- WS-RC R4.C: hMem : tid ∈ ntfn.waitingThreads via Membership instance.
    have hMemVal : tid ∈ ntfn.waitingThreads.val := hMem
    rw [hNtfn.2.1] at hMemVal; simp at hMemVal
  -- 12. pendingBounded (WS-SM SM7.B): boot never posts a shootdown descriptor,
  -- so the post-boot shootdown state is the quiescent default.
  have hPBBundle : SeLe4n.Kernel.Architecture.pendingBounded
      ist.state.tlbShootdown := by
    rw [hShoot]; exact SeLe4n.Model.default_tlbShootdown_pendingBounded
  -- 13. tlbInvalidationConsistent_perCore (WS-SM SM7.C): boot never fills a
  -- TLB, so every core's view is the empty default — vacuously consistent.
  have hPerCoreTlbBundle : SeLe4n.Kernel.Architecture.tlbInvalidationConsistent_perCore
      ist.state := by
    intro c e he
    have hview : SeLe4n.Kernel.Architecture.tlbOnCore ist.state c
        = SeLe4n.Model.TlbState.empty := by
      unfold SeLe4n.Kernel.Architecture.tlbOnCore
      rw [hPerCoreTlb]; exact SeLe4n.Model.default_perCoreTlb c
    rw [hview] at he; simp [SeLe4n.Model.TlbState.empty] at he
  -- 14. icacheCoherent_perCore (WS-SM SM7.D): boot fills no instruction cache
  -- (it loads objects and page tables, it does not execute through them), so
  -- every core's view is the cold default — vacuously coherent.
  have hPerCoreICacheBundle : SeLe4n.Kernel.Architecture.icacheCoherent_perCore
      ist.state := by
    intro c l hl
    have hview : SeLe4n.Kernel.Architecture.icacheOnCore ist.state c
        = SeLe4n.Model.ICacheState.empty := by
      unfold SeLe4n.Kernel.Architecture.icacheOnCore
      rw [hPerCoreICache]; exact SeLe4n.Model.default_perCoreICache c
    rw [hview] at hl; simp [SeLe4n.Model.ICacheState.empty] at hl
  -- 15. ackBounded (WS-SM SM7.F.3, PR #854 review): boot opens no round, so
  -- the post-boot shootdown state is the quiescent default — every slot and
  -- the round counter `0`.
  have hAckBounded : SeLe4n.Kernel.Architecture.ackBounded
      ist.state.tlbShootdown := by
    rw [hShoot]; exact SeLe4n.Model.default_tlbShootdown_ackBounded
  -- 16. auditLogBounded (WS-SM SM8.C.8): boot declassifies nothing, so the
  -- post-boot audit trail is the empty default — trivially within capacity.
  have hAuditBounded : SeLe4n.Kernel.auditLogBounded
      ist.state.declassificationAuditLog := by
    rw [hAudit]
    exact SeLe4n.Model.default_auditLogBounded
  -- Compose all 16 components
  exact ⟨h1, hCapBundle, ⟨h1.1, hCapBundle, hIpcFull⟩, hCouplingBundle,
         hLifeBundle, hServiceBundle, hVspaceBundle, hCrossBundle, hTlbBundle, hExtBundle,
         hNtfnWaiter, hPBBundle, hPerCoreTlbBundle, hPerCoreICacheBundle, hAckBounded,
         hAuditBounded⟩

/-- V4-A8: The post-boot state from any config satisfies
    `proofLayerInvariantBundle` — the unchecked boot's instance of
    `proofLayerInvariantBundle_of_bootShape` (WS-BP BP3.5).  Its objects are
    the boot-safe configured objects, its scheduler is the default (so every
    run-queue fact holds of an empty queue), and with no configured VSpace
    root its ASID table is the empty default, consistent vacuously. -/
theorem bootFromPlatform_proofLayerInvariantBundle_general
    (config : PlatformConfig) (hSafe : config.bootSafe)
    (hUntypedDisj : config.untypedRegionsDisjoint)
    -- WS-RC R3 (DEEP-BOOT-01): Boot VSpaceRoots are introduced via the
    -- dedicated `installBootVSpaceRoot` builder operation (extending
    -- `bootFromPlatformChecked`), NOT through `initialObjects`.  This
    -- precondition restricts the present (unchecked) bridge theorem to
    -- VSpace-clean configs — `bootFromPlatform` itself does NOT install
    -- a boot VSpaceRoot, so its post-state is necessarily VSpace-free
    -- when `initialObjects` is also VSpace-free.  The checked boot, which
    -- installs roots, has its own theorem since WS-BP BP3.5:
    -- `bootFromPlatformCheckedWithIdleThreadsFor_proofLayerInvariantBundle`.
    (hNoVSpaceInInitial :
      ∀ entry, entry ∈ config.initialObjects → ∀ vs,
        entry.obj ≠ KernelObject.vspaceRoot vs) :
    Architecture.proofLayerInvariantBundle
      (bootFromPlatform config).state := by
  have hSch := bootFromPlatform_scheduler_eq config
  -- Scheduler sub-field facts
  have hCur : ((bootFromPlatform config).state.scheduler.currentOnCore bootCoreId) = none := by
    rw [hSch]; decide
  have hRun : (bootFromPlatform config).state.scheduler.runnable = [] := by
    rw [hSch]; decide
  have hRQflat : ((bootFromPlatform config).state.scheduler.runQueueOnCore bootCoreId).flat = [] := by
    rw [hSch]; decide
  -- 1. schedulerInvariantBundleFull
  have h1 : schedulerInvariantBundleFull (bootFromPlatform config).state := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [queueCurrentConsistent, hCur]
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
  -- WS-RC R3 (DEEP-BOOT-01): No VSpaceRoots in boot state.  With R3.1
  -- admitting boot-safe VSpaceRoots into the `bootSafeObject` predicate,
  -- absurdity is no longer immediate from the bootSafe witness; instead
  -- we trace any post-boot VSpaceRoot back to `initialObjects` via
  -- `foldObjects_objects_reachable` and contradict `hNoVSpaceInInitial`.
  have hNoVSpace : ∀ (oid : SeLe4n.ObjId) (vs : VSpaceRoot),
      (bootFromPlatform config).state.objects.get? oid ≠
        some (KernelObject.vspaceRoot vs) := by
    intro oid vs hObj
    -- Trace the post-boot lookup back to initialObjects.
    unfold bootFromPlatform at hObj
    -- applyMachineConfig preserves objects.
    rw [applyMachineConfig_objects_eq] at hObj
    have hObj' : (foldObjects config.initialObjects
        (foldIrqs config.irqTable mkEmptyIntermediateState)).state.objects[oid]? =
          some (KernelObject.vspaceRoot vs) := by
      simp only [RHTable_getElem?_eq_get?]; exact hObj
    rcases foldObjects_objects_reachable config.initialObjects
        (foldIrqs config.irqTable mkEmptyIntermediateState) oid _ hObj' with
      ⟨entry, hMem, _hId, hObjEq⟩ | hBase
    · -- Entry came from initialObjects with `entry.obj = .vspaceRoot vs`.
      exact hNoVSpaceInInitial entry hMem vs (by rw [hObjEq])
    · -- Base state: `foldIrqs` over the empty intermediate state has no objects.
      rw [foldIrqs_objects, mkEmpty_state_eq_default] at hBase
      have hEmpty : (default : SystemState).objects[oid]? = none := by
        simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
      rw [hEmpty] at hBase; exact absurd hBase (by simp)
  refine proofLayerInvariantBundle_of_bootShape (bootFromPlatform config) ?_
    ⟨bootFromPlatform_cdt_eq config, bootFromPlatform_cdtNodeSlot_eq config,
     bootFromPlatform_services_eq config, bootFromPlatform_serviceRegistry_eq config,
     bootFromPlatform_tlb_eq config, bootFromPlatform_tlbShootdown_eq config,
     bootFromPlatform_perCoreTlb_eq config, bootFromPlatform_perCoreICache_eq config,
     bootFromPlatform_declassificationAuditLog_eq config⟩
    ?_ (bootFromPlatform_untypedRegionsDisjoint config hUntypedDisj) h1 hCur ?_ ?_
  · -- Every object is a boot-safe configured object.
    intro oid obj hObj
    refine bootSafeObject_bootObjectShape (bootFromPlatform_objects_bootSafe config hSafe oid obj hObj) ?_
    intro vs hEq
    subst hEq
    exact (bootFromPlatform config).hPerObjectMappings oid vs hObj
  · -- No root, and an empty table: consistent vacuously in both directions.
    have hAsid := bootFromPlatform_asidTable_eq config
      (fun e hMem vs => hNoVSpaceInInitial e hMem vs)
    constructor
    · intro asid oid hLookup; rw [hAsid] at hLookup
      have : (default : SystemState).asidTable[asid]? = none := by
        simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
      rw [this] at hLookup; exact absurd hLookup (by simp)
    · intro oid root hObj; exact absurd hObj (hNoVSpace oid _)
  · -- replenishQueueValid: the default scheduler's queues are empty.
    simp only [replenishQueueValid, hSch]
    exact ⟨empty_sorted, empty_sizeConsistent⟩
  · -- effectiveParamsMatchRunQueue: the default run queue is empty.
    intro tid hMem
    have hFlat : ((bootFromPlatform config).state.scheduler.runQueueOnCore bootCoreId).flat = [] := by
      rw [hSch]; decide
    have hInFlat := (RunQueue.mem_toList_iff_mem _ tid).mpr hMem
    simp [RunQueue.toList, hFlat] at hInFlat

-- ============================================================================
-- V4-A9: End-to-end bridge for general configs
-- ============================================================================

/-- V4-A9: End-to-end boot-to-runtime invariant bridge for general configs.
    Composes V4-A8 (boot → proofLayerInvariantBundle) with freeze_preserves.

    AK8-A: Requires the additional config-level precondition
    `config.untypedRegionsDisjoint` to establish the 12th conjunct of
    `crossSubsystemInvariant`.

    WS-RC R3 (DEEP-BOOT-01): Threads the new `hNoVSpaceInInitial`
    precondition through the bridge composition.  The bridge covers
    configs whose `initialObjects` carry no VSpace root — since WS-BP BP3.2
    the checked boot *admits* a configured thread's root (registering its
    ASID; `bootVSpaceAsidsDistinct` refuses a collision), so a config that
    carries one, like the RPi5 deployment's, is outside this bridge, as a
    config carrying a binding root already was.  Binding roots are installed by
    `installBootVSpaceRoot` consumed by the gated boot path
    `bootFromPlatformChecked` via the dedicated
    `PlatformConfig.bootVSpaceRoot` field.  **The production boot has its own
    bridge since WS-BP BP3.5**: `bootToRuntime_invariantBridge_checked`, over
    the checked, idle-enqueued boot of any configuration the checked boot
    accepts — roots installed — which is the boot the hardware runs.  This one
    stays for the unchecked boot and the fixtures built on it. -/
theorem bootToRuntime_invariantBridge_general (config : PlatformConfig)
    (hSafe : config.bootSafe) (hUntypedDisj : config.untypedRegionsDisjoint)
    (hNoVSpaceInInitial :
      ∀ entry, entry ∈ config.initialObjects → ∀ vs,
        entry.obj ≠ KernelObject.vspaceRoot vs) :
    let ist := bootFromPlatform config
    Architecture.proofLayerInvariantBundle ist.state ∧
    SeLe4n.Model.apiInvariantBundle_frozen (SeLe4n.Model.freeze ist) :=
  ⟨bootFromPlatform_proofLayerInvariantBundle_general config hSafe hUntypedDisj
     hNoVSpaceInInitial,
   SeLe4n.Model.freeze_preserves_invariants _
     (bootFromPlatform_proofLayerInvariantBundle_general config hSafe hUntypedDisj
        hNoVSpaceInInitial)⟩

-- ============================================================================
-- WS-RR RR5.13 / PR #889 review: results that read the object store through
-- `foldObjects_objects_reachable`, placed after it
-- ============================================================================

/-- **WS-RR RR5.13** (PR #889 review): a successful checked boot's idle slots are
    **empty** — the hypothesis `bootFromPlatformCheckedWithIdleThreads_preserves_platform_objects`
    used to take is now a consequence of the boot succeeding, because the
    reservation is decided on the validation path. -/
theorem bootFromPlatformChecked_ok_idleSlotsFreshAt (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    idleSlotsFreshAt ist := by
  obtain ⟨hWf, _, hShape⟩ := bootFromPlatformChecked_ok_shape config ist h
  have hRes := PlatformConfig.wellFormed_idleSlotsReserved config hWf
  have hFresh := idleSlotsFreshAt_of_idleSlotsReserved config hRes
  intro c
  rcases hShape with ⟨_, rfl⟩ | ⟨entry, hSome, rfl⟩
  · rw [bootEnableInterruptsOp_objects_eq]
    exact hFresh c
  · rw [bootEnableInterruptsOp_objects_eq]
    have hVs := idleSlotsReserved_bootVSpaceRoot config hRes entry hSome
    rw [installBootVSpaceRoot_objects_ne _ _ _ _ _
      (idleThreadId_toObjId_ne_of_not_isIdleObjId entry.id hVs c).symm]
    exact hFresh c

/-- **WS-RR RR5.13** (purely additive): the idle enqueue overwrites **no**
    platform object.

    `Builder.createObject` inserts, and `RHTable.insert` overwrites on key
    collision, so a config object placed in the idle `ObjId` range would be
    silently clobbered by the boot fold.  The first cut of this theorem took an
    `idleSlotsFreshAt` hypothesis that nothing on the live path discharged (PR
    #889 review); the reservation is now part of `PlatformConfig.wellFormed`,
    so a successful checked boot *is* fresh
    (`bootFromPlatformChecked_ok_idleSlotsFreshAt`) and the theorem takes
    nothing beyond the two boots.

    Stated over the *checked* boot's own base rather than `bootFromPlatform`'s so
    it composes with a caller holding a successful boot, which is the form the
    production wrapper has.  The enqueue theorems above hold unconditionally;
    this one is what says the addition is not also a removal. -/
theorem bootFromPlatformCheckedWithIdleThreads_preserves_platform_objects
    (config : PlatformConfig) (ist ist' : IntermediateState)
    (hChecked : bootFromPlatformChecked config = .ok ist)
    (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist')
    (oid : SeLe4n.ObjId) (o : KernelObject)
    (hPlat : ist.state.objects[oid]? = some o) :
    ist'.state.objects[oid]? = some o := by
  have hFresh := bootFromPlatformChecked_ok_idleSlotsFreshAt config ist hChecked
  rw [bootFromPlatformCheckedWithIdleThreads_map_ok config ist hChecked] at h
  injection h with h
  subst h
  rw [foldl_enqueueIdleThread_objects_frame_of_not_idle
    SeLe4n.Kernel.Concurrency.allCores ist oid (fun c' _ hEq => ?_)]
  · exact hPlat
  · -- If `oid` were an idle slot, freshness (`= none`) would contradict `hPlat`.
    have hAt : ist.state.objects[(idleThreadId c').toObjId]? = some o := by
      rw [hEq]; exact hPlat
    rw [hFresh c'] at hAt
    simp at hAt

/-- PR #889 review round 5: after the declared-cores boot, a core the binding
    does **not** declare has no idle object at all — the checked boot leaves
    every model idle slot fresh (`bootFromPlatformChecked_ok_idleSlotsFreshAt`,
    by the model-wide reservation) and the fold writes only the declared cores'
    slots (`foldl_enqueueIdleThread_objects_frame`).  The reservation's other
    half: an undeclared core's slot is *absent*, not available, so no
    capability can resolve to it (`syscallResolveCap_ok_not_reserved`) and no
    config object can be dispatched from it. -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_undeclared_idle_absent
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok ist)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (hc : c ∉ cores) :
    ist.state.objects[(idleThreadId c).toObjId]? = none := by
  cases hChecked : bootFromPlatformChecked config with
  | error e =>
    rw [bootFromPlatformCheckedWithIdleThreadsFor_rejects_invalid cores config e hChecked] at h
    cases h
  | ok base =>
    rw [bootFromPlatformCheckedWithIdleThreadsFor_map_ok cores config base hChecked
      (bootFromPlatformCheckedWithIdleThreadsFor_ok_affinitiesDeclared cores config ist h)] at h
    injection h with h
    subst h
    rw [foldl_enqueueIdleThread_objects_frame cores base c
      (fun c' hc' hEq => hc (hEq ▸ hc'))]
    exact bootFromPlatformChecked_ok_idleSlotsFreshAt config base hChecked c

-- ============================================================================
-- WS-BP BP3.3: every configured object is in the boot state, at its own id
-- ============================================================================

/-- **WS-BP BP3.3**: the transparent duplicate check is `List.Nodup`. -/
private theorem listAllDistinct_eq_true_iff {α : Type} [DecidableEq α] (l : List α) :
    listAllDistinct l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [listAllDistinct]
  | cons x xs ih =>
      simp only [listAllDistinct, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons, ih]
      simp

/-- **WS-BP BP3.3**: a well-formed config's object ids are pairwise distinct. -/
theorem PlatformConfig.wellFormed_objectIds_pairwise (config : PlatformConfig)
    (h : config.wellFormed = true) :
    config.initialObjects.Pairwise (fun a b => a.id ≠ b.id) := by
  have hU := config.wellFormed_objectIdsUnique h
  rw [objectIdsUnique_eq_transparent, objectIdsUniqueTransparent,
    listAllDistinct_eq_true_iff, List.Nodup, List.pairwise_map] at hU
  exact hU.imp fun hNe hEq => hNe (congrArg SeLe4n.ObjId.toNat hEq)

/-- **WS-BP BP3.3**: the object fold leaves a key no entry names alone. -/
theorem foldObjects_objects_ne (objs : List ObjectEntry) (ist : IntermediateState)
    (oid : SeLe4n.ObjId) (h : ∀ e ∈ objs, e.id ≠ oid) :
    (foldObjects objs ist).state.objects[oid]? = ist.state.objects[oid]? := by
  induction objs generalizing ist with
  | nil => rfl
  | cons e rest ih =>
      show (foldObjects rest (createBootObject ist e)).state.objects[oid]? = _
      rw [ih _ (fun e' hMem => h e' (List.mem_cons_of_mem _ hMem)), createBootObject_objects]
      have hNe : ¬((e.id == oid) = true) := fun hEq => h e List.mem_cons_self (eq_of_beq hEq)
      exact RHTable.getElem?_insert_ne _ _ _ _ hNe ist.hAllTables.1.1

/-- **WS-BP BP3.3**: over entries with pairwise-distinct ids, the object fold
    leaves every entry at its own id. -/
theorem foldObjects_objects_of_mem (objs : List ObjectEntry) (ist : IntermediateState)
    (hUniq : objs.Pairwise (fun a b => a.id ≠ b.id)) (e : ObjectEntry) (hMem : e ∈ objs) :
    (foldObjects objs ist).state.objects[e.id]? = some e.obj := by
  induction objs generalizing ist with
  | nil => cases hMem
  | cons x rest ih =>
      rw [List.pairwise_cons] at hUniq
      show (foldObjects rest (createBootObject ist x)).state.objects[e.id]? = _
      rcases List.mem_cons.mp hMem with rfl | hRest
      · rw [foldObjects_objects_ne _ _ _ (fun e' hE' => (hUniq.1 e' hE').symm),
          createBootObject_objects]
        exact RHTable.getElem?_insert_self _ _ _ ist.hAllTables.1.1
      · exact ih _ hUniq.2 hRest

/-- **WS-BP BP3.3**: a successful checked boot rejected no colliding boot root
    — the gate's fact, read off the result. -/
theorem bootFromPlatformChecked_ok_bootVSpaceRootObjIdDistinct (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    bootVSpaceRootObjIdDistinct config = true := by
  unfold bootFromPlatformChecked at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · split at h
            · split at h
              · rename_i hD; exact hD
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **WS-BP BP3.3**: **every configured object is in a successful checked
    boot's state, at its own id.**  The object ids are distinct
    (`wellFormed`), the fold installs each (`foldObjects_objects_of_mem`), the
    binding's root is installed at an id no entry names
    (`bootVSpaceRootObjIdDistinct`), and enabling interrupts touches no object.
    What a configuration names is what the boot built — the fact a deployment's
    witness threads, root task and untypeds are read off. -/
theorem bootFromPlatformChecked_ok_objects_of_mem (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist)
    (e : ObjectEntry) (hMem : e ∈ config.initialObjects) :
    ist.state.objects[e.id]? = some e.obj := by
  have hDist := bootFromPlatformChecked_ok_bootVSpaceRootObjIdDistinct config ist h
  obtain ⟨hWf, _, hShape⟩ := bootFromPlatformChecked_ok_shape config ist h
  have hBase : (bootFromPlatform config).state.objects[e.id]? = some e.obj := by
    unfold bootFromPlatform
    rw [applyMachineConfig_objects_eq]
    exact foldObjects_objects_of_mem _ _ (config.wellFormed_objectIds_pairwise hWf) e hMem
  rcases hShape with ⟨_, rfl⟩ | ⟨entry, hSome, rfl⟩
  · rw [bootEnableInterruptsOp_objects_eq]; exact hBase
  · rw [bootEnableInterruptsOp_objects_eq, installBootVSpaceRoot_objects_ne]
    · exact hBase
    · intro hEq
      unfold bootVSpaceRootObjIdDistinct at hDist
      rw [hSome] at hDist
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hDist
      exact hDist e hMem hEq.symm

/-- **WS-BP BP3.3**: ...and the idle enqueue on any core list keeps it there —
    a configured object is never at an idle slot (`idleSlotsReserved`). -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_ok_objects_of_mem
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok ist)
    (e : ObjectEntry) (hMem : e ∈ config.initialObjects) :
    ist.state.objects[e.id]? = some e.obj := by
  cases hChecked : bootFromPlatformChecked config with
  | error err =>
    rw [bootFromPlatformCheckedWithIdleThreadsFor_rejects_invalid cores config err hChecked] at h
    cases h
  | ok base =>
    rw [bootFromPlatformCheckedWithIdleThreadsFor_map_ok cores config base hChecked
      (bootFromPlatformCheckedWithIdleThreadsFor_ok_affinitiesDeclared cores config ist h)] at h
    injection h with h
    subst h
    obtain ⟨hWf, _, _⟩ := bootFromPlatformChecked_ok_shape config base hChecked
    have hRes := PlatformConfig.wellFormed_idleSlotsReserved config hWf
    have hNotIdle : SeLe4n.Kernel.isIdleObjId e.id = false := by
      unfold idleSlotsReserved at hRes
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hRes
      exact (hRes.1 e hMem).1
    rw [foldl_enqueueIdleThread_objects_frame_of_not_idle cores base e.id
      (fun c _ => SeLe4n.Kernel.idleThreadId_toObjId_ne_of_not_isIdleObjId e.id hNotIdle c)]
    exact bootFromPlatformChecked_ok_objects_of_mem config base hChecked e hMem


-- ============================================================================
-- PR #889 review: the boot state is `threadStateConsistent`
-- ============================================================================

/-- **WS-RR RR5.11** (PR #889 review): the boot state's idle TCBs carry the
    thread state the classification infers for them.

    The enqueue stores `queuedIdleThread c` (`threadState := .Ready`); on the
    boot state idle `c` is on core `c`'s run queue
    (`bootFromPlatformCheckedWithIdleThreads_idle_available`) and in no core's
    current slot (`bootFromPlatformCheckedWithIdleThreads_currentAllNone`), which
    is exactly what `inferThreadState` calls `.Ready`
    (`inferThreadState_ready_of_runQueueOnCore`).  With the dispatched form
    (`createIdleThread`, `.Running`) stored instead, this equation was false on
    every core of every successful production boot. -/
theorem bootFromPlatformCheckedWithIdleThreads_idle_threadState (config : PlatformConfig)
    (ist' : IntermediateState) (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist')
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    inferThreadState ist'.state (idleThreadId c) (queuedIdleThread c) =
      (queuedIdleThread c).threadState := by
  rw [queuedIdleThread_threadState]
  apply inferThreadState_ready_of_runQueueOnCore ist'.state c
  · exact (SeLe4n.Kernel.RunQueue.mem_toList_iff_mem _ _).mp
      (bootFromPlatformCheckedWithIdleThreads_idle_available config ist' h c).1
  · unfold threadRunningOnSomeCore runningOnSomeCore
    rw [List.any_eq_false]
    intro c' _
    rw [bootFromPlatformCheckedWithIdleThreads_currentAllNone config ist' h c']
    simp

/-- **PR #889 review**, generalised at **WS-RR RR8.16**: every TCB a successful
    checked boot installs is a config entry that passed `bootSafeObjectCheck`, so
    it carries **every** field that check's soundness bridge establishes.  The boot
    VSpace root, when present, is not a TCB, and the interrupt-enable step frames
    the store.

    Stated at the whole clause rather than at a projection of it.  The original
    shape concluded only `threadState` and `ipcState` — the two fields
    `inferThreadState` reads — so the *other eight* fields the very same
    object-reachability argument establishes were unreachable without a second copy
    of that argument, which is this project's `a recognised set is not a derived
    set` rule applied to a conclusion.  RR8.16 needed
    `schedContextBinding = .unbound`, which was in the bridge and not in the
    theorem; `bootFromPlatformChecked_ok_tcb_inactive` is now this theorem's
    two-field corollary, so the argument exists once. -/
theorem bootFromPlatformChecked_ok_tcb_bootSafeFields (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hObj : ist.state.objects[oid]? = some (KernelObject.tcb tcb)) :
    tcb.pendingMessage = none ∧ tcb.ipcState = .ready ∧
      tcb.queueNext = none ∧ tcb.queuePrev = none ∧ tcb.queuePPrev = none ∧
      tcb.timeoutBudget = none ∧
      tcb.schedContextBinding = .unbound ∧
      tcb.replyObject = none ∧
      tcb.pendingReceiveReply = none ∧
      tcb.threadState = .Inactive := by
  obtain ⟨_, hSafe, hShape⟩ := bootFromPlatformChecked_ok_shape config ist h
  have hPlain : (bootFromPlatform config).state.objects[oid]? = some (KernelObject.tcb tcb) := by
    rcases hShape with ⟨_, rfl⟩ | ⟨entry, _, rfl⟩
    · rwa [bootEnableInterruptsOp_objects_eq] at hObj
    · rw [bootEnableInterruptsOp_objects_eq] at hObj
      by_cases hEq : entry.id = oid
      · subst hEq
        rw [installBootVSpaceRoot_objects_lookup] at hObj
        exact absurd hObj (by simp)
      · rwa [installBootVSpaceRoot_objects_ne _ _ _ _ _ hEq] at hObj
  have hLook' : (foldObjects config.initialObjects
      (foldIrqs config.irqTable mkEmptyIntermediateState)).state.objects[oid]? =
        some (KernelObject.tcb tcb) := by
    unfold bootFromPlatform at hPlain
    rwa [applyMachineConfig_objects_eq] at hPlain
  rcases foldObjects_objects_reachable config.initialObjects _ _ _ hLook' with
    ⟨e, hMem, _, hEObj⟩ | hBase
  · have hCheck : bootSafeObjectCheck e.obj = true := List.all_eq_true.mp hSafe e hMem
    rw [hEObj] at hCheck
    exact (bootSafeObjectCheck_sound _ hCheck).2.2.2.1 tcb rfl
  · rw [foldIrqs_objects, mkEmpty_state_eq_default] at hBase
    have hEmpty : (default : SystemState).objects[oid]? = none := by
      simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
    rw [hEmpty] at hBase
    simp at hBase

/-- **PR #889 review**: every TCB a successful checked boot installs is `.Inactive`
    with a `.ready` IPC state — the two fields `inferThreadState` reads for a thread
    that is neither current nor queued.  The two-field projection of
    `bootFromPlatformChecked_ok_tcb_bootSafeFields`, which carries the rest. -/
theorem bootFromPlatformChecked_ok_tcb_inactive (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hObj : ist.state.objects[oid]? = some (KernelObject.tcb tcb)) :
    tcb.threadState = .Inactive ∧ tcb.ipcState = .ready :=
  let hTcb := bootFromPlatformChecked_ok_tcb_bootSafeFields config ist h oid tcb hObj
  ⟨hTcb.2.2.2.2.2.2.2.2.2, hTcb.2.1⟩

/-- **PR #889 review**: on the plain checked boot no thread is current and no
    thread is queued — the two `inferThreadState` tests, both `false`. -/
theorem bootFromPlatformChecked_ok_not_running_not_queued (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist)
    (tid : SeLe4n.ThreadId) :
    threadRunningOnSomeCore ist.state tid = false ∧
      threadQueuedOnSomeCore ist.state tid = false := by
  have hSched := bootFromPlatformChecked_ok_scheduler_eq config ist h
  constructor
  · unfold threadRunningOnSomeCore runningOnSomeCore
    rw [List.any_eq_false]
    intro c _
    rw [hSched]
    show ¬(((default : SchedulerState).currentOnCore c) == some tid) = true
    rw [(default_state_perCoreInitialized c).1]
    simp
  · unfold threadQueuedOnSomeCore runnableOnSomeCore
    rw [List.any_eq_false]
    intro c _
    rw [hSched]
    show tid ∉ (default : SchedulerState).runQueueOnCore c
    rw [(default_state_perCoreInitialized c).2.1]
    exact SeLe4n.Kernel.RunQueue.not_mem_empty tid

/-- **PR #889 review**: the plain checked boot is `threadStateConsistent` —
    every installed TCB is a boot-safe config entry (`.Inactive`, IPC-ready),
    and on the default scheduler nothing is current or queued, so the
    classification agrees with the stored field on every object. -/
theorem bootFromPlatformChecked_ok_threadStateConsistent (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    threadStateConsistent ist.state := by
  intro oid tcb hObj
  obtain ⟨hInactive, hReady⟩ := bootFromPlatformChecked_ok_tcb_inactive config ist h oid tcb hObj
  obtain ⟨hRun, hQ⟩ := bootFromPlatformChecked_ok_not_running_not_queued config ist h ⟨oid.toNat⟩
  rw [hInactive]
  unfold inferThreadState
  rw [hRun, hQ, hReady]
  rfl

-- ============================================================================
-- WS-RR RR8.16: the boot state inhabits the two information-flow gate facts
-- ============================================================================

/-- **WS-RR RR8.16**: every TCB the *production* boot installs is IPC-quiescent and
    owns no scheduling context.

    Two populations, one conclusion.  A key the idle fold did not write holds a
    config entry that passed `bootSafeObjectCheck`
    (`bootFromPlatformChecked_ok_tcb_bootSafeFields`, whose `.ipcState = .ready` and
    `.schedContextBinding = .unbound` clauses are exactly these); a key it did write
    holds `queuedIdleThread c`, which sets neither field and so carries the `TCB`
    record's own defaults, both by `rfl`.  `foldl_enqueueIdleThread_objects_cases` is
    what makes that a case analysis rather than a `Nodup` argument. -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_ok_tcb_quiescent
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok ist)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hObj : ist.state.objects[oid]? = some (KernelObject.tcb tcb)) :
    tcb.ipcState = .ready ∧ tcb.schedContextBinding = .unbound := by
  cases hChecked : bootFromPlatformChecked config with
  | error e =>
    rw [bootFromPlatformCheckedWithIdleThreadsFor_rejects_invalid cores config e hChecked] at h
    cases h
  | ok base =>
    rw [bootFromPlatformCheckedWithIdleThreadsFor_map_ok cores config base hChecked
      (bootFromPlatformCheckedWithIdleThreadsFor_ok_affinitiesDeclared cores config ist h)] at h
    injection h with h
    subst h
    rcases foldl_enqueueIdleThread_objects_cases cores base oid _ hObj with hBase | ⟨c, _, hEq⟩
    · have hFields :=
        bootFromPlatformChecked_ok_tcb_bootSafeFields config base hChecked oid tcb hBase
      exact ⟨hFields.2.1, hFields.2.2.2.2.2.2.1⟩
    · injection hEq with hEq
      subst hEq
      exact ⟨rfl, rfl⟩

/-- **WS-RR RR8.16**: the boot state satisfies `blockedSenderFlowsToEndpoint`, for
    **every** labelling context.

    The base case, and the reason it is unconditional in `ctx`: a state with no
    blocked sender constrains no label, so the predicate's antecedent is empty rather
    than its conclusion cheap.  With this, the transport family in
    `InformationFlow/Invariant/Composition.lean` carries the fact forward from a real
    state instead of from a hypothesis — which is what the PR #897 review found
    missing, and what this project's own rule demands of a stated fact: *a hypothesis
    nothing exhibits is indistinguishable from one that cannot hold.* -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_blockedSenderFlowsToEndpoint
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok ist)
    (ctx : LabelingContext) :
    blockedSenderFlowsToEndpoint ctx ist.state := by
  refine blockedSenderFlowsToEndpoint_of_none_blocked ?_
  intro tid t epId hLook
  have hReady :=
    (bootFromPlatformCheckedWithIdleThreadsFor_ok_tcb_quiescent cores config ist h
      tid.toObjId t (lookupTcb_some_objects ist.state tid t hLook)).1
  rw [hReady]
  exact ⟨by simp, by simp⟩

/-- **WS-RR RR8.16**: the boot state satisfies `donationOwnerFlowsToHolder`, for
    **every** labelling context.

    Vacuous for the same structural reason and not by coincidence: `bootSafeTcbCheck`
    refuses a bound config TCB and the idle fold installs an unbound one, so
    `replyDonationReturn?` answers `none` at every thread — a donation is something
    the kernel *mints*, and a boot state has minted none. -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_donationOwnerFlowsToHolder
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok ist)
    (ctx : LabelingContext) :
    donationOwnerFlowsToHolder ctx ist.state := by
  intro holder owner scId hRes
  have hNone : replyDonationReturn? ist.state holder = none := by
    unfold replyDonationReturn?
    cases hLook : lookupTcb ist.state holder with
    | none => rfl
    | some t =>
      have hUnbound :=
        (bootFromPlatformCheckedWithIdleThreadsFor_ok_tcb_quiescent cores config ist h
          holder.toObjId t (lookupTcb_some_objects ist.state holder t hLook)).2
      simp only [hUnbound]
  rw [hNone] at hRes
  exact absurd hRes (by simp)

/-- **WS-RR RR8.16**: the all-cores production boot — the one
    `bootAndInitialiseFromPlatform` runs — inhabits both facts.  The declared-list
    form at `allCores` (`bootFromPlatformCheckedWithIdleThreadsFor_allCores`). -/
theorem bootFromPlatformCheckedWithIdleThreads_flowGateFacts
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist)
    (ctx : LabelingContext) :
    blockedSenderFlowsToEndpoint ctx ist.state ∧
      donationOwnerFlowsToHolder ctx ist.state := by
  rw [← bootFromPlatformCheckedWithIdleThreadsFor_allCores] at h
  exact ⟨bootFromPlatformCheckedWithIdleThreadsFor_blockedSenderFlowsToEndpoint _ config ist h ctx,
    bootFromPlatformCheckedWithIdleThreadsFor_donationOwnerFlowsToHolder _ config ist h ctx⟩

/-- **PR #889 review**: two states that neither run nor queue `tid` classify it
    identically — `inferThreadState` then reads only the TCB's own IPC state. -/
theorem inferThreadState_eq_of_not_running_not_queued (st₁ st₂ : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h₁ : threadRunningOnSomeCore st₁ tid = false) (h₂ : threadQueuedOnSomeCore st₁ tid = false)
    (h₃ : threadRunningOnSomeCore st₂ tid = false) (h₄ : threadQueuedOnSomeCore st₂ tid = false) :
    inferThreadState st₁ tid tcb = inferThreadState st₂ tid tcb := by
  unfold inferThreadState
  rw [h₁, h₂, h₃, h₄]

/-- **PR #889 review** (the closure): the **production boot state** is
    `threadStateConsistent`.

    The finding was that `enqueueIdleThread` stored the dispatched idle form
    while queuing it, so every successful production boot installed a state the
    invariant rejected on every core — concealed by a harness that syncs the
    field before checking it, and installed raw by
    `bootAndInitialiseFromPlatform`.  Two things close it: the enqueue stores the
    **queued** form (`queuedIdleThread`, `.Ready`), whose classification the
    boot state matches (`bootFromPlatformCheckedWithIdleThreads_idle_threadState`);
    and every config TCB is `.Inactive` (`bootSafeObjectCheck`, PR #889 review)
    and stays so classified, because the idle enqueue queues nothing but idle
    and dispatches nothing.  So the invariant holds of the state the kernel
    boots into, with no hypothesis beyond the boot. -/
theorem bootFromPlatformCheckedWithIdleThreads_threadStateConsistent (config : PlatformConfig)
    (ist' : IntermediateState) (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist') :
    threadStateConsistent ist'.state := by
  unfold bootFromPlatformCheckedWithIdleThreads at h
  cases hChecked : bootFromPlatformChecked config with
  | error e => rw [hChecked] at h; simp [Except.map] at h
  | ok ist =>
      rw [hChecked] at h
      injection h with h
      subst h
      have hIdleBoot := bootFromPlatformCheckedWithIdleThreads_map_ok config ist hChecked
      have hPlain := bootFromPlatformChecked_ok_threadStateConsistent config ist hChecked
      intro oid tcb hObj
      by_cases hIdle : ∃ c, (idleThreadId c).toObjId = oid
      · -- An idle slot: the object is the queued idle TCB, classified `.Ready`.
        obtain ⟨c, rfl⟩ := hIdle
        have hIdleObj := (foldl_enqueueIdleThread_installs c SeLe4n.Kernel.Concurrency.allCores ist
          SeLe4n.Kernel.Concurrency.allCores_nodup (SeLe4n.Kernel.Concurrency.mem_allCores c)).2
        rw [hIdleObj] at hObj
        injection hObj with hObj
        injection hObj with hObj
        subst hObj
        exact (bootFromPlatformCheckedWithIdleThreads_idle_threadState config _ hIdleBoot c).symm
      · -- A config slot: framed by the fold, and classified as on the plain boot
        -- — nothing is current on either state, and the only queued threads on
        -- the idle boot are the idle threads, which this is not.
        have hFrame : ∀ c' ∈ SeLe4n.Kernel.Concurrency.allCores, (idleThreadId c').toObjId ≠ oid :=
          fun c' _ hEq => hIdle ⟨c', hEq⟩
        rw [foldl_enqueueIdleThread_objects_frame_of_not_idle
          SeLe4n.Kernel.Concurrency.allCores ist oid hFrame] at hObj
        have hStore := hPlain oid tcb hObj
        obtain ⟨hRun₁, hQ₁⟩ :=
          bootFromPlatformChecked_ok_not_running_not_queued config ist hChecked ⟨oid.toNat⟩
        have hRun₂ : threadRunningOnSomeCore
            (SeLe4n.Kernel.Concurrency.allCores.foldl enqueueIdleThread ist).state ⟨oid.toNat⟩
              = false := by
          unfold threadRunningOnSomeCore runningOnSomeCore
          rw [List.any_eq_false]
          intro c' _
          rw [bootFromPlatformCheckedWithIdleThreads_currentAllNone config _ hIdleBoot c']
          simp
        have hQ₂ : threadQueuedOnSomeCore
            (SeLe4n.Kernel.Concurrency.allCores.foldl enqueueIdleThread ist).state ⟨oid.toNat⟩
              = false := by
          unfold threadQueuedOnSomeCore runnableOnSomeCore
          rw [List.any_eq_false]
          intro c' _
          show (⟨oid.toNat⟩ : SeLe4n.ThreadId) ∉
            (SeLe4n.Kernel.Concurrency.allCores.foldl enqueueIdleThread
              ist).state.scheduler.runQueueOnCore c'
          rw [← SeLe4n.Kernel.RunQueue.mem_toList_iff_mem,
            bootFromPlatformCheckedWithIdleThreads_mem_runQueueOnCore_iff config _ hIdleBoot c']
          intro hEq
          apply hIdle
          exact ⟨c', by rw [← hEq]; rfl⟩
        rw [hStore]
        exact inferThreadState_eq_of_not_running_not_queued _ _ _ _ hRun₁ hQ₁ hRun₂ hQ₂

/-- PR #889 review round 2: the inactive-flag relation the live decisions read
    (`threadInactiveFlagConsistent`) holds of the production boot state — a
    corollary of the full classification, which the boot establishes and the
    dispatch does not preserve (see `threadInactiveFlagConsistent`'s docstring
    and the register). -/
theorem bootFromPlatformCheckedWithIdleThreads_threadInactiveFlagConsistent
    (config : PlatformConfig) (ist' : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist') :
    threadInactiveFlagConsistent ist'.state :=
  threadStateConsistent_implies_threadInactiveFlagConsistent _
    (bootFromPlatformCheckedWithIdleThreads_threadStateConsistent config ist' h)

-- ============================================================================
-- WS-RR RR7.27 — the DeviceTree → PlatformConfig bridge
--
-- Register §6 finding 46: `DeviceTree.fromDtbFull` is documented as production
-- DTB parsing, carries a correctness theorem, and had **zero consumers** —
-- there was no path from a bootloader's blob to anything the kernel boots
-- with.  This is that path's pure half.
--
-- What the device tree is *for* here is worth stating, because it is not what
-- a first reading suggests.  It does **not** supply the machine configuration
-- the kernel runs on: `bindPlatformConfig` binds the binding's own (PR #889
-- review round 7 — a caller must not be able to describe other hardware).  It
-- supplies the *board's own account of itself*, which the boot checks the
-- binding against: an image built for the BCM2712 that finds itself on a board
-- whose device tree does not describe the RAM and the MMIO the binding
-- declares is on the wrong hardware, and must refuse rather than program
-- peripherals that are not there.  What the account *does* decide is which
-- member of the binding's declared family is installed (PR #892 review round
-- 2, `PlatformBinding.bindMachineConfig`): the RPi5 ships in several RAM
-- sizes, and the largest variant the account covers is the one the boot runs
-- on.  The coverage vocabulary itself lives in `Boot/MemoryCoverage.lean`,
-- upstream of the bindings, so a binding can select by the same predicate the
-- bridge checks with.
-- ============================================================================

/-- **WS-RR RR7.27**: does the device tree describe a board with all the RAM
`mc` declares, at least as wide a physical address space?

Only the `.ram` regions are compared here, and that is not a narrowing — it is
what the two maps are *about*.  A device tree's `machineConfig.memoryMap` is
built by `DeviceTree.fromDtbFull` from the `/memory` nodes, which describe
DRAM; its peripherals are a separate surface (`DeviceTree.peripherals`,
discovered per node) and are checked by `deviceTreeCoversMmioRegions` below.
`.reserved` regions are the binding's statement about memory it will *not*
touch, and a board that does not carve out the same holes is not thereby
unusable.

Fail-closed by construction: anything the device tree does not mention is not
covered, so a blob that parses to an empty or partial map is refused. -/
def deviceTreeCoversMachineConfig (dt : DeviceTree) (mc : SeLe4n.MachineConfig) : Bool :=
  machineConfigCovers dt.machineConfig mc

/-- **PR #892 review round 2**: the device-tree check *is* the machine-level
coverage predicate at the device tree's own machine configuration — stated so
a binding that selects among its variants by `machineConfigCovers` and the
bridge that validates the board by `deviceTreeCoversMachineConfig` are asking
one question, and cannot drift apart. -/
theorem deviceTreeCoversMachineConfig_eq (dt : DeviceTree) (mc : SeLe4n.MachineConfig) :
    deviceTreeCoversMachineConfig dt mc = machineConfigCovers dt.machineConfig mc := rfl

/-- **WS-RR RR7.27**: is every MMIO window in `required` inside a peripheral the
device tree discovered **as that device**?

The other half of the board check, at the granularity the two sides actually
share: a binding names its MMIO windows one register block at a time
(`RPi5.mmioRegions` — the PL011, the GIC distributor, the GIC CPU interface),
and a device tree discovers peripherals the same way.  An image that would
program a GIC the board's own device tree does not have must refuse. -/
def deviceTreeCoversMmioRegions (dt : DeviceTree)
    (required : List RequiredMmioWindow) : Bool :=
  required.all fun w =>
    dt.peripherals.any fun d =>
      d.compatible.any (fun c => w.compatible.contains c)
        && d.base.toNat ≤ w.region.base.toNat
        && w.region.endAddr ≤ d.base.toNat + d.size

/-- **WS-RR RR7.27**: the bridge the finding names — a `PlatformConfig` whose
machine configuration is the device tree's and whose deployment half (the IRQ
table, the initial objects, the boot VSpace root) is the caller's.

The split is the honest one: a device tree describes the *board*, and the
objects a deployment starts with are not on it. -/
def PlatformConfig.fromDeviceTree (dt : DeviceTree)
    (irqTable : List IrqEntry) (initialObjects : List ObjectEntry)
    (bootVSpaceRoot : Option BootVSpaceRootEntry) : PlatformConfig :=
  { irqTable := irqTable
    initialObjects := initialObjects
    machineConfig := dt.machineConfig
    bootVSpaceRoot := bootVSpaceRoot }

/-- **WS-RR RR7.27**: the bridge carries the device tree's machine map through
unchanged — the property that makes the coverage check above a check *of the
board*. -/
@[simp] theorem PlatformConfig.fromDeviceTree_machineConfig (dt : DeviceTree)
    (irqTable : List IrqEntry) (initialObjects : List ObjectEntry)
    (bootVSpaceRoot : Option BootVSpaceRootEntry) :
    (PlatformConfig.fromDeviceTree dt irqTable initialObjects bootVSpaceRoot).machineConfig
      = dt.machineConfig := rfl

/-- **WS-RR RR7.27**: and the deployment half through unchanged. -/
@[simp] theorem PlatformConfig.fromDeviceTree_deployment (dt : DeviceTree)
    (irqTable : List IrqEntry) (initialObjects : List ObjectEntry)
    (bootVSpaceRoot : Option BootVSpaceRootEntry) :
    (PlatformConfig.fromDeviceTree dt irqTable initialObjects bootVSpaceRoot).irqTable
      = irqTable ∧
    (PlatformConfig.fromDeviceTree dt irqTable initialObjects bootVSpaceRoot).bootVSpaceRoot
      = bootVSpaceRoot := ⟨rfl, rfl⟩

/-- **WS-RR RR7.27**: hence a device tree whose map is the binding's own covers
it.  The witness that `deviceTreeCoversMachineConfig` is not vacuously false —
the shape a board matching its own binding produces. -/
theorem deviceTreeCoversMachineConfig_self (dt : DeviceTree) :
    deviceTreeCoversMachineConfig dt dt.machineConfig = true :=
  machineConfigCovers_self dt.machineConfig

/-- **WS-RR RR7.27**: the MMIO half is vacuous on an empty demand and
fail-closed on a non-empty one against a device tree that discovered nothing —
the direction that matters, since "no peripherals" is what a truncated or
foreign blob produces. -/
theorem deviceTreeCoversMmioRegions_no_peripherals (dt : DeviceTree)
    (required : List RequiredMmioWindow) (hEmpty : dt.peripherals = [])
    (hNonEmpty : required ≠ []) :
    deviceTreeCoversMmioRegions dt required = false := by
  unfold deviceTreeCoversMmioRegions
  cases required with
  | nil => exact absurd rfl hNonEmpty
  | cons r rest => simp [hEmpty]

-- ============================================================================
-- WS-BP BP3.5: the production boot's proof-layer invariant bundle
-- ============================================================================

/-! ### WS-BP BP3.5: the state the hardware boot installs satisfies the bundle

`bootFromPlatform_proofLayerInvariantBundle_general` is about the *unchecked*
boot of a configuration carrying no VSpace root, and the state the hardware
boot installs is neither: it carries the binding's root and the threads' roots,
and the checked boot enqueues an idle thread on every declared core on top.
This section discharges `proofLayerInvariantBundle_of_bootShape`'s hypotheses
for that state, one per fact the boot establishes:

* **every object is boot-shaped** — a boot-safe configured object, the
  binding's root (its checks), or an enqueued idle TCB;
* **the untouched fields are their defaults** — every step writes objects,
  the object index, lifecycle metadata, the ASID table or a run queue, and
  nothing else;
* **the ASID table is consistent with the roots** — each install registers
  its root's ASID at a key nothing else holds, which is what the boot's ASID
  gate (`bootVSpaceAsidsDistinct`) and its object-id gates refuse to let fail;
* **the untyped regions are disjoint** — the configuration's placement
  conjunct, since nothing the checked boot adds is an untyped;
* **the scheduler's run-queue facts hold** — the boot core's queue is empty
  or holds exactly its idle thread, at priority `0`. -/

/-- **WS-BP BP3.5**: a boot install writes objects, the object index,
    lifecycle metadata and the ASID table — none of the quiescent fields. -/
theorem createBootObject_bootQuiescentFields (ist : IntermediateState) (e : ObjectEntry)
    (h : bootQuiescentFields ist.state) : bootQuiescentFields (createBootObject ist e).state :=
  h

/-- **WS-BP BP3.5**: enabling interrupts writes the machine state only. -/
theorem bootEnableInterruptsOp_bootQuiescentFields (ist : IntermediateState)
    (h : bootQuiescentFields ist.state) :
    bootQuiescentFields (bootEnableInterruptsOp ist).state :=
  h

/-- **WS-BP BP3.5**: the idle enqueue is a store and a run-queue write, and a
    store writes objects, the object index, lifecycle metadata and the ASID
    table. -/
theorem enqueueIdleThread_bootQuiescentFields (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (h : bootQuiescentFields ist.state) :
    bootQuiescentFields (enqueueIdleThread ist c).state := by
  rw [enqueueIdleThread_state]
  unfold enqueueIdleThreadOnCore
  have hs := SystemState.storeObject_eq_withObjectStored ist.state (idleThreadId c).toObjId
    (KernelObject.tcb (queuedIdleThread c))
  generalize ist.state.withObjectStored (idleThreadId c).toObjId
    (KernelObject.tcb (queuedIdleThread c)) = st' at hs ⊢
  unfold storeObject at hs
  cases hs
  exact h

/-- **WS-BP BP3.5**: ...and so does the fold of it over any core list. -/
theorem foldl_enqueueIdleThread_bootQuiescentFields
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState)
    (h : bootQuiescentFields ist.state) :
    bootQuiescentFields (L.foldl enqueueIdleThread ist).state := by
  induction L generalizing ist with
  | nil => exact h
  | cons x xs ih => exact ih _ (enqueueIdleThread_bootQuiescentFields ist x h)

/-- **WS-BP BP3.5**: the unchecked boot leaves every quiescent field at its
    default. -/
theorem bootFromPlatform_bootQuiescentFields (config : PlatformConfig) :
    bootQuiescentFields (bootFromPlatform config).state :=
  ⟨bootFromPlatform_cdt_eq config, bootFromPlatform_cdtNodeSlot_eq config,
   bootFromPlatform_services_eq config, bootFromPlatform_serviceRegistry_eq config,
   bootFromPlatform_tlb_eq config, bootFromPlatform_tlbShootdown_eq config,
   bootFromPlatform_perCoreTlb_eq config, bootFromPlatform_perCoreICache_eq config,
   bootFromPlatform_declassificationAuditLog_eq config⟩

/-- **WS-BP BP3.5**: a successful checked boot leaves every quiescent field at
    its default — the plain boot does, and the root install and the interrupt
    enable frame them. -/
theorem bootFromPlatformChecked_ok_bootQuiescentFields (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    bootQuiescentFields ist.state := by
  obtain ⟨_, _, hShape⟩ := bootFromPlatformChecked_ok_shape config ist h
  rcases hShape with ⟨_, rfl⟩ | ⟨entry, _, rfl⟩
  · exact bootEnableInterruptsOp_bootQuiescentFields _
      (bootFromPlatform_bootQuiescentFields config)
  · exact bootEnableInterruptsOp_bootQuiescentFields _
      (createBootObject_bootQuiescentFields _ _ (bootFromPlatform_bootQuiescentFields config))

/-- **WS-BP BP3.5**: a successful checked boot passed its ASID gate and its
    boot-root safety gate — the two gate facts the bundle reads, read off the
    result. -/
theorem bootFromPlatformChecked_ok_vspaceGates (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    bootVSpaceAsidsDistinct config = true ∧ bootVSpaceRootSafe config = true := by
  unfold bootFromPlatformChecked at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · split at h
            · split at h
              · split at h
                · split at h
                  · exact ⟨by assumption, by assumption⟩
                  · cases h
                · cases h
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **WS-BP BP3.5**: every object a successful checked boot installs is
    boot-shaped — a configured object passed `bootSafeObjectCheck`, and the
    binding's root passed `bootSafeVSpaceRootCheck`. -/
theorem bootFromPlatformChecked_ok_bootObjectShape (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    ∀ (oid : SeLe4n.ObjId) (obj : KernelObject),
      ist.state.objects[oid]? = some obj → bootObjectShape obj := by
  obtain ⟨_, hSafeChk, hShape⟩ := bootFromPlatformChecked_ok_shape config ist h
  obtain ⟨_, hRootSafe⟩ := bootFromPlatformChecked_ok_vspaceGates config ist h
  have hBase : ∀ (oid : SeLe4n.ObjId) (obj : KernelObject),
      (bootFromPlatform config).state.objects[oid]? = some obj → bootObjectShape obj := by
    intro oid obj hObj
    refine bootSafeObject_bootObjectShape
      (bootFromPlatform_objects_bootSafe config ?_ oid obj hObj) ?_
    · intro e hMem
      exact bootSafeObjectCheck_sound _ (List.all_eq_true.mp hSafeChk e hMem)
    · intro vs hEq
      subst hEq
      exact (bootFromPlatform config).hPerObjectMappings oid vs hObj
  intro oid obj hObj
  rcases hShape with ⟨_, rfl⟩ | ⟨entry, hSome, rfl⟩
  · rw [bootEnableInterruptsOp_objects_eq] at hObj
    exact hBase oid obj hObj
  · rw [bootEnableInterruptsOp_objects_eq] at hObj
    by_cases hEq : entry.id = oid
    · subst hEq
      rw [installBootVSpaceRoot_objects_lookup] at hObj
      cases hObj
      unfold bootVSpaceRootSafe at hRootSafe
      rw [hSome] at hRootSafe
      exact bootSafeVSpaceRoot_bootObjectShape
        ((SeLe4n.Platform.RPi5.VSpaceBoot.bootSafeVSpaceRootCheck_iff _).mp hRootSafe)
    · rw [installBootVSpaceRoot_objects_ne _ _ _ _ _ hEq] at hObj
      exact hBase oid obj hObj

/-- **WS-BP BP3.5**: a boot install keeps the ASID table consistent with the
    roots when the key it writes holds nothing and — for a root — no root
    already holds its ASID.  Those are the two ways an install could break the
    table: overwrite a registered root, or re-point a registered ASID. -/
private theorem createBootObject_preserves_asidTableConsistent (ist : IntermediateState)
    (e : ObjectEntry) (hCons : Architecture.asidTableConsistent ist.state)
    (hFresh : ist.state.objects[e.id]? = none)
    (hAsidFresh : ∀ a, bootEntryAsid? e = some a → ist.state.asidTable[a]? = none) :
    Architecture.asidTableConsistent (createBootObject ist e).state := by
  have hObjK : ist.state.objects.invExt := ist.hAllTables.1.1
  have hAsidK : ist.state.asidTable.invExt := ist.hAllTables.2.2.1.1
  obtain ⟨hSound, hComplete⟩ := hCons
  have hObjNe : ∀ oid, e.id ≠ oid →
      (createBootObject ist e).state.objects[oid]? = ist.state.objects[oid]? := by
    intro oid hNe
    rw [createBootObject_objects]
    exact RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hNe (eq_of_beq hb)) hObjK
  have hObjSelf : (createBootObject ist e).state.objects[e.id]? = some e.obj := by
    rw [createBootObject_objects]
    exact RHTable.getElem?_insert_self _ _ _ hObjK
  have hPreSound : ∀ asid oid, ist.state.asidTable[asid]? = some oid →
      ∃ root, (createBootObject ist e).state.objects[oid]? =
        some (KernelObject.vspaceRoot root) ∧
        root.asid = asid := by
    intro asid oid hL
    obtain ⟨root, hR, hRA⟩ := hSound asid oid hL
    have hNe : e.id ≠ oid := by
      intro hEq; subst hEq; rw [hFresh] at hR; cases hR
    exact ⟨root, (hObjNe oid hNe).trans hR, hRA⟩
  cases hE : bootEntryAsid? e with
  | none =>
    have hTbl : (createBootObject ist e).state.asidTable = ist.state.asidTable := by
      rw [createBootObject_asidTable]
      unfold bootEntryAsidTable
      unfold bootEntryAsid? at hE
      split
      · rename_i vsr hObj
        rw [hObj] at hE
        cases hE
      · rfl
    refine ⟨fun asid oid hL => hPreSound asid oid (hTbl ▸ hL), ?_⟩
    intro oid root hObj
    rw [hTbl]
    by_cases hId : e.id = oid
    · subst hId
      rw [hObjSelf] at hObj
      have hEq : e.obj = .vspaceRoot root := Option.some.inj hObj
      unfold bootEntryAsid? at hE
      rw [hEq] at hE
      cases hE
    · rw [hObjNe oid hId] at hObj
      exact hComplete oid root hObj
  | some a =>
    obtain ⟨r, hr, rfl⟩ : ∃ r, e.obj = .vspaceRoot r ∧ r.asid = a := by
      unfold bootEntryAsid? at hE
      split at hE
      · rename_i vsr hObj
        cases hE
        exact ⟨vsr, hObj, rfl⟩
      · cases hE
    have hTbl : (createBootObject ist e).state.asidTable =
        ist.state.asidTable.insert r.asid e.id := by
      rw [createBootObject_asidTable]
      unfold bootEntryAsidTable
      rw [hr]
    have hNew := hAsidFresh r.asid hE
    constructor
    · intro asid oid hL
      rw [hTbl] at hL
      by_cases hA : r.asid = asid
      · subst hA
        rw [RHTable_getElem?_eq_get?, RHTable.getElem?_insert_self _ _ _ hAsidK] at hL
        cases hL
        exact ⟨r, hObjSelf.trans (by rw [hr]), rfl⟩
      · rw [RHTable_getElem?_eq_get?,
          RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hA (eq_of_beq hb)) hAsidK] at hL
        exact hPreSound asid oid hL
    · intro oid root hObj
      rw [hTbl]
      by_cases hId : e.id = oid
      · subst hId
        rw [hObjSelf, hr] at hObj
        cases hObj
        exact RHTable.getElem?_insert_self _ _ _ hAsidK
      · rw [hObjNe oid hId] at hObj
        have hPre := hComplete oid root hObj
        have hA : r.asid ≠ root.asid := by
          intro hEq; rw [← hEq, hNew] at hPre; cases hPre
        rw [RHTable_getElem?_eq_get?,
          RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hA (eq_of_beq hb)) hAsidK]
        exact hPre

/-- **WS-BP BP3.5**: folding boot installs over entries with distinct ids and
    distinct root ASIDs, none of them present yet, keeps the ASID table
    consistent.  The id and ASID distinctness are exactly what the boot's
    `wellFormed` and `bootVSpaceAsidsDistinct` gates decide. -/
private theorem foldObjects_preserves_asidTableConsistent (objs : List ObjectEntry) :
    ∀ (ist : IntermediateState), Architecture.asidTableConsistent ist.state →
    (∀ e ∈ objs, ist.state.objects[e.id]? = none) →
    objs.Pairwise (fun a b => a.id ≠ b.id) →
    (objs.filterMap bootEntryAsid?).Nodup →
    (∀ e ∈ objs, ∀ a, bootEntryAsid? e = some a → ist.state.asidTable[a]? = none) →
    Architecture.asidTableConsistent (foldObjects objs ist).state := by
  induction objs with
  | nil => intro ist h _ _ _ _; exact h
  | cons e rest ih =>
    intro ist hCons hFresh hIds hNodup hAsidFresh
    rw [List.pairwise_cons] at hIds
    have hStep := createBootObject_preserves_asidTableConsistent ist e hCons
      (hFresh e (List.mem_cons_self ..)) (hAsidFresh e (List.mem_cons_self ..))
    have hObjK : ist.state.objects.invExt := ist.hAllTables.1.1
    have hAsidK : ist.state.asidTable.invExt := ist.hAllTables.2.2.1.1
    have hRestNodup : (rest.filterMap bootEntryAsid?).Nodup := by
      rw [List.filterMap_cons] at hNodup
      split at hNodup
      · exact hNodup
      · exact (List.nodup_cons.mp hNodup).2
    show Architecture.asidTableConsistent (foldObjects rest (createBootObject ist e)).state
    apply ih _ hStep _ hIds.2 hRestNodup
    · intro e' hMem a ha
      have hPre := hAsidFresh e' (List.mem_cons_of_mem _ hMem) a ha
      rw [createBootObject_asidTable]
      unfold bootEntryAsidTable
      split
      · rename_i vsr hObj
        have hEa : bootEntryAsid? e = some vsr.asid := by
          unfold bootEntryAsid?; rw [hObj]
        have hNe : vsr.asid ≠ a := by
          intro hEq
          simp only [List.filterMap_cons, hEa] at hNodup
          apply (List.nodup_cons.mp hNodup).1
          rw [hEq]
          exact List.mem_filterMap.mpr ⟨e', hMem, ha⟩
        rw [RHTable_getElem?_eq_get?,
          RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hNe (eq_of_beq hb)) hAsidK]
        exact hPre
      · exact hPre
    · intro e' hMem
      rw [createBootObject_objects, RHTable_getElem?_eq_get?,
        RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hIds.1 e' hMem (eq_of_beq hb)) hObjK]
      exact hFresh e' (List.mem_cons_of_mem _ hMem)

/-- **WS-BP BP3.5**: the plain boot's ASID table is consistent with its roots
    when the configured ids and root ASIDs are distinct. -/
private theorem bootFromPlatform_asidTableConsistent (config : PlatformConfig)
    (hIds : config.initialObjects.Pairwise (fun a b => a.id ≠ b.id))
    (hAsids : (config.initialObjects.filterMap bootEntryAsid?).Nodup) :
    Architecture.asidTableConsistent (bootFromPlatform config).state := by
  have hEmptyObj : ∀ oid : SeLe4n.ObjId,
      (foldIrqs config.irqTable mkEmptyIntermediateState).state.objects[oid]? = none := by
    intro oid
    rw [foldIrqs_objects, mkEmpty_state_eq_default]
    exact RHTable_get?_empty 16 (by omega)
  have hEmptyAsid : ∀ a : SeLe4n.ASID,
      (foldIrqs config.irqTable mkEmptyIntermediateState).state.asidTable[a]? = none := by
    intro a
    rw [foldIrqs_asidTable, mkEmpty_state_eq_default]
    exact RHTable_get?_empty 16 (by omega)
  have hBaseCons : Architecture.asidTableConsistent
      (foldIrqs config.irqTable mkEmptyIntermediateState).state := by
    constructor
    · intro a oid hL; rw [hEmptyAsid] at hL; cases hL
    · intro oid root hObj; rw [hEmptyObj] at hObj; cases hObj
  have hFold := foldObjects_preserves_asidTableConsistent config.initialObjects
    (foldIrqs config.irqTable mkEmptyIntermediateState) hBaseCons
    (fun e _ => hEmptyObj e.id) hIds hAsids (fun _ _ a _ => hEmptyAsid a)
  unfold bootFromPlatform
  unfold Architecture.asidTableConsistent at hFold ⊢
  rw [applyMachineConfig_objects_eq, applyMachineConfig_asidTable_eq]
  exact hFold

/-- **WS-BP BP3.5**: every ASID the plain boot registers is a configured
    root's. -/
private theorem bootFromPlatform_asidTable_configured (config : PlatformConfig)
    (hCons : Architecture.asidTableConsistent (bootFromPlatform config).state)
    (a : SeLe4n.ASID) (oid : SeLe4n.ObjId)
    (hL : (bootFromPlatform config).state.asidTable[a]? = some oid) :
    a ∈ config.initialObjects.filterMap bootEntryAsid? := by
  obtain ⟨root, hR, hRA⟩ := hCons.1 a oid hL
  have hR' : (foldObjects config.initialObjects
      (foldIrqs config.irqTable mkEmptyIntermediateState)).state.objects[oid]? =
        some (.vspaceRoot root) := by
    unfold bootFromPlatform at hR
    rwa [applyMachineConfig_objects_eq] at hR
  rcases foldObjects_objects_reachable config.initialObjects _ _ _ hR' with
    ⟨e, hMem, _, hEObj⟩ | hBase
  · refine List.mem_filterMap.mpr ⟨e, hMem, ?_⟩
    unfold bootEntryAsid?
    rw [hEObj]
    exact congrArg some hRA
  · rw [foldIrqs_objects, mkEmpty_state_eq_default] at hBase
    have hEmpty : (default : SystemState).objects[oid]? = none := by
      simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
    rw [hEmpty] at hBase
    cases hBase

/-- **WS-BP BP3.5**: a successful checked boot's ASID table is consistent with
    its roots — the configured roots and the binding's.  The gates the checked
    boot runs are what make it so: `wellFormed` keeps the configured ids apart,
    `bootVSpaceRootObjIdDistinct` keeps the binding's root off them, and
    `bootVSpaceAsidsDistinct` keeps every root's ASID apart, the binding's
    included. -/
theorem bootFromPlatformChecked_ok_asidTableConsistent (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist) :
    Architecture.asidTableConsistent ist.state := by
  obtain ⟨hWf, _, hShape⟩ := bootFromPlatformChecked_ok_shape config ist h
  obtain ⟨hAsidsGate, _⟩ := bootFromPlatformChecked_ok_vspaceGates config ist h
  have hDist := bootFromPlatformChecked_ok_bootVSpaceRootObjIdDistinct config ist h
  have hIds := config.wellFormed_objectIds_pairwise hWf
  have hNodupAll : (bootVSpaceAsids config).Nodup := of_decide_eq_true hAsidsGate
  have hNodup : (config.initialObjects.filterMap bootEntryAsid?).Nodup :=
    (List.nodup_append.mp hNodupAll).1
  have hBase := bootFromPlatform_asidTableConsistent config hIds hNodup
  rcases hShape with ⟨_, rfl⟩ | ⟨entry, hSome, rfl⟩
  · unfold Architecture.asidTableConsistent at hBase ⊢
    rw [bootEnableInterruptsOp_objects_eq, bootEnableInterruptsOp_asidTable_eq]
    exact hBase
  · have hInstall : Architecture.asidTableConsistent
        (installBootVSpaceRoot (bootFromPlatform config) entry.id entry.root
          entry.hMappings).state := by
      unfold installBootVSpaceRoot
      apply createBootObject_preserves_asidTableConsistent _ _ hBase
      · -- The binding's root id names no configured entry.
        show (bootFromPlatform config).state.objects[entry.id]? = none
        cases hL : (bootFromPlatform config).state.objects[entry.id]? with
        | none => rfl
        | some o =>
          exfalso
          have hL' : (foldObjects config.initialObjects
              (foldIrqs config.irqTable mkEmptyIntermediateState)).state.objects[entry.id]? =
                some o := by
            unfold bootFromPlatform at hL
            rwa [applyMachineConfig_objects_eq] at hL
          rcases foldObjects_objects_reachable config.initialObjects _ _ _ hL' with
            ⟨e, hMem, hId, _⟩ | hB
          · unfold bootVSpaceRootObjIdDistinct at hDist
            rw [hSome] at hDist
            simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hDist
            exact hDist e hMem hId
          · rw [foldIrqs_objects, mkEmpty_state_eq_default] at hB
            have hEmpty : (default : SystemState).objects[entry.id]? = none := by
              simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
            rw [hEmpty] at hB
            cases hB
      · -- The binding's root ASID is no configured root's.
        intro a ha
        have haEq : a = entry.root.asid := by
          simp only [bootEntryAsid?] at ha
          exact (Option.some.inj ha).symm
        subst haEq
        cases hL : (bootFromPlatform config).state.asidTable[entry.root.asid]? with
        | none => rfl
        | some oid =>
          exfalso
          have hMemCfg := bootFromPlatform_asidTable_configured config hBase _ oid hL
          unfold bootVSpaceAsids at hNodupAll
          rw [hSome] at hNodupAll
          exact (List.nodup_append.mp hNodupAll).2.2 _ hMemCfg _
            (List.mem_singleton_self _) rfl
    unfold Architecture.asidTableConsistent at hInstall ⊢
    rw [bootEnableInterruptsOp_objects_eq, bootEnableInterruptsOp_asidTable_eq]
    exact hInstall

/-- **WS-BP BP3.5**: the idle enqueue keeps the ASID table consistent when the
    slot it writes holds no root — it stores a TCB, which registers nothing,
    and displaces nothing registered. -/
private theorem enqueueIdleThread_preserves_asidTableConsistent (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId)
    (hCons : Architecture.asidTableConsistent ist.state)
    (hSlot : ∀ r, ist.state.objects[(idleThreadId c).toObjId]? ≠ some (.vspaceRoot r)) :
    Architecture.asidTableConsistent (enqueueIdleThread ist c).state := by
  have hTbl : (enqueueIdleThread ist c).state.asidTable = ist.state.asidTable := by
    rw [enqueueIdleThread_state]
    show (ist.state.withObjectStored (idleThreadId c).toObjId
      (KernelObject.tcb (queuedIdleThread c))).asidTable = _
    rw [storeObject_asidTable_non_vspaceRoot ist.state _ (idleThreadId c).toObjId
      (KernelObject.tcb (queuedIdleThread c)) (fun r hr => by cases hr)
      (SystemState.storeObject_eq_withObjectStored _ _ _)]
    split
    · rename_i r hr
      exact absurd hr (hSlot r)
    · rfl
  obtain ⟨hSound, hComplete⟩ := hCons
  constructor
  · intro asid oid hL
    rw [hTbl] at hL
    obtain ⟨root, hR, hRA⟩ := hSound asid oid hL
    have hNe : (idleThreadId c).toObjId ≠ oid := by
      intro hEq; subst hEq; exact hSlot root hR
    exact ⟨root, (enqueueIdleThread_objects_ne ist c oid hNe).trans hR, hRA⟩
  · intro oid root hObj
    rw [hTbl]
    by_cases hEq : (idleThreadId c).toObjId = oid
    · subst hEq
      rw [enqueueIdleThread_objects_self] at hObj
      cases hObj
    · rw [enqueueIdleThread_objects_ne ist c oid hEq] at hObj
      exact hComplete oid root hObj

/-- **WS-BP BP3.5**: ...over the fold, given no idle slot starts out holding a
    root: a slot the fold has written holds an idle TCB, and one it has not is
    the pre-fold slot. -/
private theorem foldl_enqueueIdleThread_preserves_asidTableConsistent
    (L : List SeLe4n.Kernel.Concurrency.CoreId) :
    ∀ (ist : IntermediateState), Architecture.asidTableConsistent ist.state →
    (∀ c ∈ L, ∀ r, ist.state.objects[(idleThreadId c).toObjId]? ≠ some (.vspaceRoot r)) →
    Architecture.asidTableConsistent (L.foldl enqueueIdleThread ist).state := by
  induction L with
  | nil => intro ist h _; exact h
  | cons x xs ih =>
    intro ist hCons hSlots
    apply ih _ (enqueueIdleThread_preserves_asidTableConsistent ist x hCons
      (hSlots x (List.mem_cons_self ..)))
    intro c hc r
    by_cases hEq : (idleThreadId x).toObjId = (idleThreadId c).toObjId
    · rw [← hEq, enqueueIdleThread_objects_self]
      intro hb
      cases hb
    · rw [enqueueIdleThread_objects_ne ist x _ hEq]
      exact hSlots c (List.mem_cons_of_mem _ hc) r

/-- **WS-BP BP3.5**: untyped disjointness reads the untypeds alone, so a state
    whose untypeds are all another's inherits it. -/
theorem untypedRegionsDisjoint_of_untyped_subset {st st' : SystemState}
    (h : Kernel.untypedRegionsDisjoint st)
    (hSub : ∀ (oid : SeLe4n.ObjId) (ut : UntypedObject), st'.objects[oid]? = some (KernelObject.untyped ut) →
      st.objects[oid]? = some (KernelObject.untyped ut)) :
    Kernel.untypedRegionsDisjoint st' :=
  fun oid₁ oid₂ ut₁ ut₂ h₁ h₂ => h oid₁ oid₂ ut₁ ut₂ (hSub _ _ h₁) (hSub _ _ h₂)

/-- **WS-BP BP3.5**: an untyped a successful checked boot holds is one the
    plain boot installed — the binding's root is not an untyped. -/
private theorem bootFromPlatformChecked_ok_untyped (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformChecked config = .ok ist)
    (oid : SeLe4n.ObjId) (ut : UntypedObject)
    (hObj : ist.state.objects[oid]? = some (KernelObject.untyped ut)) :
    (bootFromPlatform config).state.objects[oid]? = some (KernelObject.untyped ut) := by
  obtain ⟨_, _, hShape⟩ := bootFromPlatformChecked_ok_shape config ist h
  rcases hShape with ⟨_, rfl⟩ | ⟨entry, _, rfl⟩
  · rwa [bootEnableInterruptsOp_objects_eq] at hObj
  · rw [bootEnableInterruptsOp_objects_eq] at hObj
    by_cases hEq : entry.id = oid
    · subst hEq
      rw [installBootVSpaceRoot_objects_lookup] at hObj
      cases hObj
    · rwa [installBootVSpaceRoot_objects_ne _ _ _ _ _ hEq] at hObj

/-- **WS-BP BP3.5**: the idle fold writes run queues and nothing else of the
    scheduler. -/
theorem foldl_enqueueIdleThread_scheduler_runQueueOnly
    (L : List SeLe4n.Kernel.Concurrency.CoreId) (ist : IntermediateState) :
    ∃ rq, (L.foldl enqueueIdleThread ist).state.scheduler =
      { ist.state.scheduler with runQueue := rq } := by
  induction L generalizing ist with
  | nil => exact ⟨ist.state.scheduler.runQueue, rfl⟩
  | cons x xs ih =>
    obtain ⟨rq, hrq⟩ := ih (enqueueIdleThread ist x)
    refine ⟨rq, ?_⟩
    rw [List.foldl_cons, hrq, enqueueIdleThread_scheduler]
    rfl

/-- **WS-BP BP3.5**: the boot core's idle queue — the empty queue with the
    boot core's idle thread inserted at its priority — holds exactly that
    thread, at priority `0`.  A closed term, so both facts are evaluation. -/
private theorem bootCoreIdleQueue_toList :
    ((SeLe4n.Kernel.RunQueue.empty.remove (idleThreadId bootCoreId)).insert
      (idleThreadId bootCoreId) (queuedIdleThread bootCoreId).priority).toList =
      [idleThreadId bootCoreId] := by
  decide

private theorem bootCoreIdleQueue_threadPriority :
    ((SeLe4n.Kernel.RunQueue.empty.remove (idleThreadId bootCoreId)).insert
      (idleThreadId bootCoreId) (queuedIdleThread bootCoreId).priority).threadPriority[
        idleThreadId bootCoreId]? = some ⟨0⟩ := by
  decide

/-- **WS-BP BP3.5**: **the state the checked, idle-enqueued boot installs
    satisfies the proof-layer invariant bundle** — for any configuration the
    checked boot accepts and any duplicate-free core list, so the hardware
    boot's state (`bootAndInitialisePlatform`, over the binding's declared
    cores) and the all-cores boot are both instances.

    This is what a transition going live owes first: the next phase's first
    row makes this boot live, and until this theorem no statement about the
    proof-layer bundle covered the state it installs — the general bridge was
    about the unchecked boot of a VSpace-free configuration, with an empty
    scheduler.  Each hypothesis of `proofLayerInvariantBundle_of_bootShape` is
    discharged from the boot itself: the objects' shape from the checked
    boot's object and root checks and the idle TCBs' defaults, the ASID table
    from the id and ASID gates, the untyped regions from `wellFormed`'s
    placement conjunct, and the scheduler facts from what the fold enqueued —
    on the boot core, nothing or its idle thread at priority `0`. -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_proofLayerInvariantBundle
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (hNodup : cores.Nodup)
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok ist) :
    Architecture.proofLayerInvariantBundle ist.state := by
  cases hChecked : bootFromPlatformChecked config with
  | error e =>
    rw [bootFromPlatformCheckedWithIdleThreadsFor_rejects_invalid cores config e hChecked] at h
    cases h
  | ok base =>
    rw [bootFromPlatformCheckedWithIdleThreadsFor_map_ok cores config base hChecked
      (bootFromPlatformCheckedWithIdleThreadsFor_ok_affinitiesDeclared cores config ist h)] at h
    injection h with h
    subst h
    obtain ⟨hWf, _, _⟩ := bootFromPlatformChecked_ok_shape config base hChecked
    have hFresh := bootFromPlatformChecked_ok_idleSlotsFreshAt config base hChecked
    have hBaseSch := bootFromPlatformChecked_ok_scheduler_eq config base hChecked
    obtain ⟨rq, hSch⟩ := foldl_enqueueIdleThread_scheduler_runQueueOnly cores base
    rw [hBaseSch] at hSch
    have hBaseQ : base.state.scheduler.runQueueOnCore bootCoreId =
        SeLe4n.Kernel.RunQueue.empty := by
      rw [hBaseSch]; exact (default_state_perCoreInitialized bootCoreId).2.1
    -- The boot core's run queue holds its idle thread at priority 0, or nothing.
    have hRunnable : ∀ tid,
        tid ∈ (cores.foldl enqueueIdleThread base).state.scheduler.runQueueOnCore bootCoreId →
        tid = idleThreadId bootCoreId ∧
        (cores.foldl enqueueIdleThread base).state.objects[(idleThreadId bootCoreId).toObjId]? =
          some (.tcb (queuedIdleThread bootCoreId)) ∧
        ((cores.foldl enqueueIdleThread base).state.scheduler.runQueueOnCore
          bootCoreId).threadPriority[tid]? = some ⟨0⟩ := by
      intro tid hMem
      by_cases hb : bootCoreId ∈ cores
      · have hQ := foldl_enqueueIdleThread_runQueueOnCore_eq bootCoreId cores base hNodup hb
        rw [hBaseQ] at hQ
        rw [hQ] at hMem ⊢
        have hIn := (SeLe4n.Kernel.RunQueue.mem_toList_iff_mem _ _).mpr hMem
        rw [bootCoreIdleQueue_toList, List.mem_singleton] at hIn
        subst hIn
        exact ⟨rfl, (foldl_enqueueIdleThread_installs bootCoreId cores base hNodup hb).2,
          bootCoreIdleQueue_threadPriority⟩
      · rw [foldl_enqueueIdleThread_runQueueOnCore_frame cores base bootCoreId
          (fun c' hc' hEq => hb (hEq ▸ hc')), hBaseQ] at hMem
        exact absurd hMem (SeLe4n.Kernel.RunQueue.not_mem_empty tid)
    have hCur : (cores.foldl enqueueIdleThread base).state.scheduler.currentOnCore
        bootCoreId = none := by
      rw [hSch]; exact (default_state_perCoreInitialized bootCoreId).1
    have hRunnableTcb : ∀ tid,
        tid ∈ (cores.foldl enqueueIdleThread base).state.scheduler.runnable →
        tid = idleThreadId bootCoreId ∧
        (cores.foldl enqueueIdleThread base).state.objects[(idleThreadId bootCoreId).toObjId]? =
          some (.tcb (queuedIdleThread bootCoreId)) ∧
        ((cores.foldl enqueueIdleThread base).state.scheduler.runQueueOnCore
          bootCoreId).threadPriority[tid]? = some ⟨0⟩ :=
      fun tid hMem => hRunnable tid ((SeLe4n.Kernel.RunQueue.mem_toList_iff_mem _ _).mp hMem)
    have hSched : schedulerInvariantBundleFull (cores.foldl enqueueIdleThread base).state := by
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [queueCurrentConsistent, hCur]
      · show ((cores.foldl enqueueIdleThread base).state.scheduler.runQueueOnCore
          bootCoreId).toList.Nodup
        by_cases hb : bootCoreId ∈ cores
        · rw [foldl_enqueueIdleThread_runQueueOnCore_eq bootCoreId cores base hNodup hb, hBaseQ]
          exact SeLe4n.Kernel.RunQueue.insert_preserves_toList_nodup _ _ _
            (SeLe4n.Kernel.RunQueue.remove_preserves_toList_nodup _ _
              (by rw [SeLe4n.Kernel.RunQueue.toList_empty]; exact List.nodup_nil))
        · rw [foldl_enqueueIdleThread_runQueueOnCore_frame cores base bootCoreId
            (fun c' hc' hEq => hb (hEq ▸ hc')), hBaseQ, SeLe4n.Kernel.RunQueue.toList_empty]
          exact List.nodup_nil
      · unfold currentThreadValid; rw [hCur]; trivial
      · intro tid hMem
        obtain ⟨rfl, hObj, _⟩ := hRunnableTcb tid hMem
        simp only [hObj]
        decide
      · unfold currentTimeSlicePositive; rw [hCur]; trivial
      · unfold edfCurrentHasEarliestDeadline; rw [hCur]; trivial
      · unfold contextMatchesCurrent; rw [hCur]; trivial
      · intro tid hMem
        obtain ⟨rfl, hObj, _⟩ := hRunnableTcb tid hMem
        exact ⟨_, hObj⟩
      · intro tid hMem
        obtain ⟨rfl, hObj, hPrio⟩ := hRunnable tid hMem
        simp only [hObj]
        rw [hPrio]
        rfl
      · unfold domainTimeRemainingPositive
        rw [hSch]
        exact (by decide : (default : SchedulerState).domainTimeRemainingOnCore bootCoreId > 0)
      · intro e hMem
        have hDS : (cores.foldl enqueueIdleThread base).state.scheduler.domainSchedule = [] := by
          rw [hSch]; rfl
        rw [hDS] at hMem
        simp at hMem
    refine proofLayerInvariantBundle_of_bootShape (cores.foldl enqueueIdleThread base)
      ?_ (foldl_enqueueIdleThread_bootQuiescentFields cores base
        (bootFromPlatformChecked_ok_bootQuiescentFields config base hChecked))
      (foldl_enqueueIdleThread_preserves_asidTableConsistent cores base
        (bootFromPlatformChecked_ok_asidTableConsistent config base hChecked)
        (fun c _ r hr => by rw [hFresh c] at hr; cases hr))
      ?_ hSched hCur ?_ ?_
    · -- Every object: the checked boot's, or an idle TCB.
      intro oid obj hObj
      rcases foldl_enqueueIdleThread_objects_cases cores base oid obj hObj with
        hB | ⟨c, _, rfl⟩
      · exact bootFromPlatformChecked_ok_bootObjectShape config base hChecked oid obj hB
      · exact queuedIdleThread_bootObjectShape c
    · -- The untypeds are the plain boot's, whose regions the placement
      -- conjunct keeps apart.
      refine untypedRegionsDisjoint_of_untyped_subset
        (bootFromPlatform_untypedRegionsDisjoint config
          (config.wellFormed_untypedRegionsDisjoint hWf)) ?_
      intro oid ut hObj
      rcases foldl_enqueueIdleThread_objects_cases cores base oid _ hObj with
        hB | ⟨c, _, hEq⟩
      · exact bootFromPlatformChecked_ok_untyped config base hChecked oid ut hB
      · cases hEq
    · -- The replenishment queues are the default's, which are empty.
      simp only [replenishQueueValid, hSch]
      exact ⟨empty_sorted, empty_sizeConsistent⟩
    · -- The boot core's queued thread is its idle thread, bucketed at its priority.
      intro tid hMem
      obtain ⟨rfl, hObj, hPrio⟩ := hRunnable tid hMem
      simp only [hObj]
      rw [hPrio]
      rfl

/-- **WS-BP BP3.5**: the all-cores form. -/
theorem bootFromPlatformCheckedWithIdleThreads_proofLayerInvariantBundle
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreads config = .ok ist) :
    Architecture.proofLayerInvariantBundle ist.state := by
  rw [← bootFromPlatformCheckedWithIdleThreadsFor_allCores] at h
  exact bootFromPlatformCheckedWithIdleThreadsFor_proofLayerInvariantBundle _
    SeLe4n.Kernel.Concurrency.allCores_nodup config ist h

/-- **WS-BP BP3.5**: the end-to-end bridge for the production boot — the
    bundle of the state the checked, idle-enqueued boot installs, and the
    frozen bundle of its freeze.  The counterpart of
    `bootToRuntime_invariantBridge_general` for the boot the hardware runs. -/
theorem bootToRuntime_invariantBridge_checked
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (hNodup : cores.Nodup)
    (config : PlatformConfig) (ist : IntermediateState)
    (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok ist) :
    Architecture.proofLayerInvariantBundle ist.state ∧
    SeLe4n.Model.apiInvariantBundle_frozen (SeLe4n.Model.freeze ist) :=
  let hBundle :=
    bootFromPlatformCheckedWithIdleThreadsFor_proofLayerInvariantBundle cores hNodup config ist h
  ⟨hBundle, SeLe4n.Model.freeze_preserves_invariants _ hBundle⟩

end SeLe4n.Platform.Boot
