/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.IntermediateState
import SeLe4n.Kernel.RadixTree.Bridge

/-!
# Q5: FrozenSystemState + Freeze

Defines the frozen execution-phase state representation and the `freeze`
function that converts a builder-phase `IntermediateState` into a
`FrozenSystemState` with dense arrays and pre-computed indices.

## Design

The two-phase boot model separates state construction (builder phase) from
runtime execution (frozen phase):

1. **Builder phase** (Q3): `IntermediateState` wraps `SystemState` with
   invariant witnesses. Builder operations (`Builder.*`) preserve proofs.

2. **Freeze phase** (Q5, this file): `freeze` converts `IntermediateState`
   to `FrozenSystemState`. Each `RHTable` becomes a `FrozenMap` (dense
   array + pre-computed index). CNode slots become `CNodeRadix` (flat
   radix array from Q4). The freeze is a one-time, pure transformation.

3. **Execution phase** (Q7, future): Kernel transitions operate on
   `FrozenSystemState` using O(1) array lookups.

## Architecture

- `FrozenMap κ ν`: dense value array + RHTable index mapping keys to
  array positions. Runtime lookup = one hash (in indexMap) + one array
  access. The index is built once at freeze time.

- `FrozenSet κ`: unit-valued `FrozenMap` for membership-only checks.

- `FrozenKernelObject`: per-object frozen representation. CNode uses
  `CNodeRadix` (zero-hash O(1) via bit extraction). VSpaceRoot uses
  `FrozenMap`. Other objects (TCB, Endpoint, etc.) are unchanged.

- `FrozenSystemState`: mirrors `SystemState` field-by-field with
  `FrozenMap` replacing `RHTable` for all map fields.

## Q5 Sub-phases

- **Q5-A**: `FrozenMap`, `FrozenSet` types and operations
- **Q5-B**: `FrozenKernelObject`, `FrozenSchedulerState`, `FrozenSystemState`
- **Q5-C**: `freezeMap`, `freezeObject`, `freeze` functions
-/

namespace SeLe4n.Model

open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.RadixTree

-- ============================================================================
-- Q5-A: FrozenMap and FrozenSet Types
-- ============================================================================

/-- Q5-A: A frozen key-value store: dense value array + pre-computed key-to-index
mapping. Built once at freeze time from an `RHTable`.

- `data`: contiguous array of values, indexed by position
- `indexMap`: maps each key to its position in `data`

Safety: `get?` performs a bounds check on the retrieved index, ensuring
memory safety without carrying proof fields in the structure. Structural
properties (all indices in-bounds, injection) are proven as separate
theorems about the `freezeMap` constructor. -/
structure FrozenMap (κ : Type) (ν : Type) [BEq κ] [Hashable κ] [LawfulBEq κ] where
  data     : Array ν
  indexMap  : RHTable κ Nat

/-- Q5-A: Runtime lookup in a frozen map: index lookup + bounds-checked array
access. One hash computation (in `indexMap.get?`) + one O(1) array access.
Returns `none` if the key is not in the map or if the index is out of
bounds (the latter cannot happen for well-constructed frozen maps). -/
@[inline] def FrozenMap.get? [BEq κ] [Hashable κ] [LawfulBEq κ] (fm : FrozenMap κ ν) (k : κ) : Option ν :=
  match fm.indexMap.get? k with
  | none => none
  | some idx =>
    if h : idx < fm.data.size then some fm.data[idx]
    else none

/-- Q5-A: Runtime mutation: in-place array update at an existing index.
Returns `none` if the key has no index (key not in frozen map).
Does NOT add new keys — frozen maps have a fixed key set. -/
def FrozenMap.set [BEq κ] [Hashable κ] [LawfulBEq κ] (fm : FrozenMap κ ν) (k : κ) (v : ν)
    : Option (FrozenMap κ ν) :=
  match fm.indexMap.get? k with
  | none => none
  | some idx =>
    if h : idx < fm.data.size then
      some { data := fm.data.set (⟨idx, h⟩ : Fin fm.data.size) v, indexMap := fm.indexMap }
    else none

/-- Q5-A: Number of entries in a frozen map. -/
@[inline] def FrozenMap.size [BEq κ] [Hashable κ] [LawfulBEq κ] (fm : FrozenMap κ ν) : Nat :=
  fm.data.size

/-- Q5-A: Check if a key exists in a frozen map. -/
@[inline] def FrozenMap.contains [BEq κ] [Hashable κ] [LawfulBEq κ] (fm : FrozenMap κ ν) (k : κ) : Bool :=
  (fm.indexMap.get? k).isSome

/-- Q5-A: Fold over all key-value pairs in a frozen map. Uses the index map
to iterate keys and resolves each to its data array slot. -/
def FrozenMap.fold [BEq κ] [Hashable κ] [LawfulBEq κ] (fm : FrozenMap κ ν) (init : γ)
    (f : γ → κ → ν → γ) : γ :=
  fm.indexMap.fold init (fun acc k idx =>
    if h : idx < fm.data.size then f acc k fm.data[idx]
    else acc)

/-- Q5-A: A frozen set: membership-only via FrozenMap's index.
Defined as a unit-valued FrozenMap. -/
def FrozenSet (κ : Type) [BEq κ] [Hashable κ] [LawfulBEq κ] := FrozenMap κ Unit

-- ============================================================================
-- Q5-A Proofs
-- ============================================================================

/-- Q5-A: `get?` returns `none` for keys not in the index map. -/
theorem FrozenMap.get?_none [BEq κ] [Hashable κ] [LawfulBEq κ]
    (fm : FrozenMap κ ν) (k : κ) (h : fm.indexMap.get? k = none) :
    fm.get? k = none := by
  unfold FrozenMap.get?
  split
  · rfl
  · rename_i idx hGet; rw [h] at hGet; cases hGet

/-- Q5-A: `set` returns `none` for keys not in the frozen map. -/
theorem FrozenMap.set_none [BEq κ] [Hashable κ] [LawfulBEq κ]
    (fm : FrozenMap κ ν) (k : κ) (v : ν) (h : fm.indexMap.get? k = none) :
    fm.set k v = none := by
  unfold FrozenMap.set; simp [h]

-- ============================================================================
-- Q5-B: FrozenKernelObject — Per-Object Frozen Representations
-- ============================================================================

/-- Q5-B: Frozen CNode — slots backed by `CNodeRadix` (flat radix array)
instead of `RHTable`. Zero-hash O(1) lookup via bit extraction. -/
structure FrozenCNode where
  depth      : Nat
  guardWidth : Nat
  guardValue : Nat
  radixWidth : Nat
  slots      : CNodeRadix
  deriving Repr

/-- Q5-B: Frozen VSpaceRoot — mappings backed by `FrozenMap` instead of
`RHTable`. One hash at freeze time; runtime uses index + array access. -/
structure FrozenVSpaceRoot where
  asid     : SeLe4n.ASID
  mappings : FrozenMap SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)

/-- Q5-B: Frozen kernel object — mirrors `KernelObject` but with frozen
representations for CNode and VSpaceRoot. TCB, Endpoint, Notification,
and UntypedObject are unchanged (they contain no embedded hash tables). -/
inductive FrozenKernelObject where
  | tcb (t : TCB)
  | endpoint (e : Endpoint)
  | notification (n : Notification)
  | cnode (c : FrozenCNode)
  | vspaceRoot (v : FrozenVSpaceRoot)
  | untyped (u : UntypedObject)

/-- Q5-B: Extract the object type from a frozen kernel object. -/
def FrozenKernelObject.objectType : FrozenKernelObject → KernelObjectType
  | .tcb _ => .tcb
  | .endpoint _ => .endpoint
  | .notification _ => .notification
  | .cnode _ => .cnode
  | .vspaceRoot _ => .vspaceRoot
  | .untyped _ => .untyped

/-- Q5-B: Frozen kernel object preserves the type tag of the source object. -/
theorem FrozenKernelObject.objectType_tcb (t : TCB) :
    (FrozenKernelObject.tcb t).objectType = .tcb := rfl
theorem FrozenKernelObject.objectType_endpoint (e : Endpoint) :
    (FrozenKernelObject.endpoint e).objectType = .endpoint := rfl
theorem FrozenKernelObject.objectType_notification (n : Notification) :
    (FrozenKernelObject.notification n).objectType = .notification := rfl
theorem FrozenKernelObject.objectType_cnode (c : FrozenCNode) :
    (FrozenKernelObject.cnode c).objectType = .cnode := rfl
theorem FrozenKernelObject.objectType_vspaceRoot (v : FrozenVSpaceRoot) :
    (FrozenKernelObject.vspaceRoot v).objectType = .vspaceRoot := rfl
theorem FrozenKernelObject.objectType_untyped (u : UntypedObject) :
    (FrozenKernelObject.untyped u).objectType = .untyped := rfl

-- ============================================================================
-- Q5-B: FrozenSchedulerState
-- ============================================================================

/-- Q5-B: Frozen scheduler state — mirrors `SchedulerState` with frozen
backing stores. `byPriority`, `threadPriority`, and `membership` are
converted from `RHTable`/`RHSet` to `FrozenMap`/`FrozenSet`. -/
structure FrozenSchedulerState where
  byPriority          : FrozenMap SeLe4n.Priority (List SeLe4n.ThreadId)
  threadPriority      : FrozenMap SeLe4n.ThreadId SeLe4n.Priority
  membership          : FrozenSet SeLe4n.ThreadId
  current             : Option SeLe4n.ThreadId
  activeDomain        : SeLe4n.DomainId
  domainTimeRemaining : Nat
  domainSchedule      : List DomainScheduleEntry
  domainScheduleIndex : Nat

-- ============================================================================
-- Q5-B: FrozenSystemState
-- ============================================================================

/-- Q5-B: Frozen system state — the execution-phase state representation.

Mirrors `SystemState` field-by-field with all `RHTable`/`RHSet` maps replaced
by `FrozenMap`/`FrozenSet`. Per-object embedded maps (CNode slots, VSpaceRoot
mappings) are individually frozen in `FrozenKernelObject`.

This is the target of the `freeze` function and the substrate for all
runtime kernel transitions (Q7). -/
structure FrozenSystemState where
  -- Core maps (FrozenMap)
  objects           : FrozenMap SeLe4n.ObjId FrozenKernelObject
  irqHandlers       : FrozenMap SeLe4n.Irq SeLe4n.ObjId
  asidTable         : FrozenMap SeLe4n.ASID SeLe4n.ObjId
  serviceRegistry   : FrozenMap ServiceId ServiceRegistration
  interfaceRegistry : FrozenMap SeLe4n.InterfaceId InterfaceSpec
  services          : FrozenMap ServiceId ServiceGraphEntry

  -- CDT (FrozenMap — dual index)
  cdtChildMap       : FrozenMap CdtNodeId (List CdtNodeId)
  cdtParentMap      : FrozenMap CdtNodeId CdtNodeId
  cdtSlotNode       : FrozenMap SlotRef CdtNodeId
  cdtNodeSlot       : FrozenMap CdtNodeId SlotRef
  cdtEdges          : List CapDerivationEdge  -- proof anchor (retained)
  cdtNextNode       : CdtNodeId

  -- Scheduler
  scheduler         : FrozenSchedulerState

  -- Lifecycle metadata (FrozenMap)
  objectTypes       : FrozenMap SeLe4n.ObjId KernelObjectType
  capabilityRefs    : FrozenMap SlotRef CapTarget

  -- Non-map fields (retained as-is)
  machine           : SeLe4n.MachineState
  objectIndex       : List SeLe4n.ObjId
  /-- WS-G2/F-P10: Frozen shadow set for O(1) objectIndex membership checks.
  Mirrors `SystemState.objectIndexSet` (RHSet → FrozenSet). -/
  objectIndexSet    : FrozenSet SeLe4n.ObjId
  /-- T2-D (M-NEW-1): Abstract TLB state, transferred from `SystemState.tlb`
  during freeze. The TLB is immutable in the frozen phase (no frozen TLB
  operations), so this is a direct field copy for completeness. -/
  tlb               : TlbState

-- ============================================================================
-- Q5-C: Freeze Functions
-- ============================================================================

/-- Q5-C: Build a `FrozenMap` from an `RHTable` by extracting entries via
`toList`, creating a dense value array, and building a key-to-index mapping.

**Construction**:
1. `RHTable.toList` extracts all `(key, value)` pairs
2. Values are collected into a dense `Array ν` (`data`)
3. Each key is mapped to its sequential position in a fresh `RHTable κ Nat`

**Safety**: `FrozenMap.get?` performs a runtime bounds check on the index
value, so the frozen map is memory-safe by construction. The structural
property `freezeMap_data_size` proves the data array size equals the
number of source entries, and `freezeMap_foldl_counter` establishes the
index counter invariant. -/
def freezeMap [BEq κ] [Hashable κ] [LawfulBEq κ] (rt : RHTable κ ν) : FrozenMap κ ν :=
  let entries := rt.toList
  let data := (entries.map (·.2)).toArray
  let indexMap := (entries.foldl (fun (acc, i) (k, _) =>
    (acc.insert k i, i + 1)) (RHTable.empty 16, 0)).1
  { data := data, indexMap := indexMap }

/-- Q5-C: Freeze a CNode's RHTable-backed slots into a `CNodeRadix` flat
radix array. Delegates to Q4-D's `freezeCNodeSlots`. -/
def freezeCNode (cn : CNode) : FrozenCNode :=
  { depth := cn.depth
    guardWidth := cn.guardWidth
    guardValue := cn.guardValue
    radixWidth := cn.radixWidth
    slots := freezeCNodeSlots cn }

/-- Q5-C: Freeze a VSpaceRoot's RHTable-backed mappings into a `FrozenMap`. -/
def freezeVSpaceRoot (vs : VSpaceRoot) : FrozenVSpaceRoot :=
  { asid := vs.asid
    mappings := freezeMap vs.mappings }

/-- Q5-C: Freeze an individual kernel object. CNode and VSpaceRoot get their
embedded maps frozen; other object types pass through unchanged. -/
def freezeObject (obj : KernelObject) : FrozenKernelObject :=
  match obj with
  | .tcb t => .tcb t
  | .endpoint e => .endpoint e
  | .notification n => .notification n
  | .cnode cn => .cnode (freezeCNode cn)
  | .vspaceRoot vs => .vspaceRoot (freezeVSpaceRoot vs)
  | .untyped u => .untyped u

/-- Q5-C: `freezeObject` preserves the object type tag. -/
theorem freezeObject_preserves_type (obj : KernelObject) :
    (freezeObject obj).objectType = obj.objectType := by
  cases obj <;> rfl

/-- Q5-C: Freeze the scheduler state. -/
def freezeScheduler (sched : SchedulerState) : FrozenSchedulerState :=
  { byPriority := freezeMap sched.runQueue.byPriority
    threadPriority := freezeMap sched.runQueue.threadPriority
    membership := freezeMap sched.runQueue.membership.table
    current := sched.current
    activeDomain := sched.activeDomain
    domainTimeRemaining := sched.domainTimeRemaining
    domainSchedule := sched.domainSchedule
    domainScheduleIndex := sched.domainScheduleIndex }

/-- Q5-C: Master freeze function — converts an `IntermediateState` (builder
phase with invariant witnesses) into a `FrozenSystemState` (execution phase
with dense arrays).

Each RHTable field in `SystemState` is converted to a `FrozenMap` via
`freezeMap`. Per-object embedded maps are frozen via `freezeObject`:
- CNode slots → `CNodeRadix` (Q4-D, zero-hash radix array)
- VSpaceRoot mappings → `FrozenMap` (dense array + index)
- TCB, Endpoint, Notification, Untyped → unchanged (no embedded maps)

**Deterministic**: `freeze` is a pure function — same input yields same
output. This is critical for reproducible kernel boot sequences. -/
def freeze (ist : IntermediateState) : FrozenSystemState :=
  let st := ist.state
  -- Freeze the object store: each KernelObject is individually frozen
  -- via freezeObject, then the whole object map is frozen.
  let frozenObjectEntries := st.objects.toList.map (fun (id, obj) =>
    (id, freezeObject obj))
  let frozenObjects : FrozenMap SeLe4n.ObjId FrozenKernelObject :=
    let data := (frozenObjectEntries.map (·.2)).toArray
    let indexMap := (frozenObjectEntries.foldl (fun (acc, i) (k, _) =>
      (acc.insert k i, i + 1)) (RHTable.empty 16, 0)).1
    { data := data, indexMap := indexMap }
  { objects := frozenObjects
    irqHandlers := freezeMap st.irqHandlers
    asidTable := freezeMap st.asidTable
    serviceRegistry := freezeMap st.serviceRegistry
    interfaceRegistry := freezeMap st.interfaceRegistry
    services := freezeMap st.services
    cdtChildMap := freezeMap st.cdt.childMap
    cdtParentMap := freezeMap st.cdt.parentMap
    cdtSlotNode := freezeMap st.cdtSlotNode
    cdtNodeSlot := freezeMap st.cdtNodeSlot
    cdtEdges := st.cdt.edges
    cdtNextNode := st.cdtNextNode
    scheduler := freezeScheduler st.scheduler
    objectTypes := freezeMap st.lifecycle.objectTypes
    capabilityRefs := freezeMap st.lifecycle.capabilityRefs
    machine := st.machine
    objectIndex := st.objectIndex
    objectIndexSet := freezeMap st.objectIndexSet.table
    tlb := st.tlb }

-- ============================================================================
-- Q5-C Proofs
-- ============================================================================

/-- Q5-C: `freeze` preserves the object index. -/
theorem freeze_preserves_objectIndex (ist : IntermediateState) :
    (freeze ist).objectIndex = ist.state.objectIndex := rfl

/-- Q5-C: `freeze` preserves the CDT edges (proof anchor). -/
theorem freeze_preserves_cdtEdges (ist : IntermediateState) :
    (freeze ist).cdtEdges = ist.state.cdt.edges := rfl

/-- Q5-C: `freeze` preserves the CDT next-node counter. -/
theorem freeze_preserves_cdtNextNode (ist : IntermediateState) :
    (freeze ist).cdtNextNode = ist.state.cdtNextNode := rfl

/-- Q5-C: `freeze` preserves the machine state. -/
theorem freeze_preserves_machine (ist : IntermediateState) :
    (freeze ist).machine = ist.state.machine := rfl

/-- T2-F (M-NEW-1): `freeze` preserves the TLB state — the frozen TLB is
    identical to the pre-freeze `SystemState.tlb`. This closes M-NEW-1:
    TLB state is no longer dropped during freeze. -/
theorem freeze_preserves_tlb (ist : IntermediateState) :
    (freeze ist).tlb = ist.state.tlb := rfl

/-- Q5-C: `freeze` preserves the scheduler current thread. -/
theorem freeze_preserves_current (ist : IntermediateState) :
    (freeze ist).scheduler.current = ist.state.scheduler.current := rfl

/-- Q5-C: `freeze` preserves the active domain. -/
theorem freeze_preserves_activeDomain (ist : IntermediateState) :
    (freeze ist).scheduler.activeDomain = ist.state.scheduler.activeDomain := rfl

/-- Q5-C: `freeze` preserves the domain schedule. -/
theorem freeze_preserves_domainSchedule (ist : IntermediateState) :
    (freeze ist).scheduler.domainSchedule = ist.state.scheduler.domainSchedule := rfl

/-- Q5-C helper: folding over an array of `none` values with the toList accumulator
returns the initial accumulator unchanged. -/
private theorem fold_none_replicate [BEq κ] [Hashable κ] [LawfulBEq κ]
    (n : Nat) (init : List (κ × ν)) :
    (List.replicate n (none : Option (RHEntry κ ν))).foldl
      (fun acc slot => match slot with | none => acc | some e => (e.key, e.value) :: acc)
      init = init := by
  induction n generalizing init with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, List.foldl_cons]; exact ih init

/-- Q5-C: `freezeMap` data size equals the number of entries in the source. -/
theorem freezeMap_data_size [BEq κ] [Hashable κ] [LawfulBEq κ] (rt : RHTable κ ν) :
    (freezeMap rt).data.size = rt.toList.length := by
  simp [freezeMap, List.size_toArray, List.length_map]

-- ============================================================================
-- Q5-C: freezeMap index validity (structural property)
-- ============================================================================

/-- Q5-C helper: the foldl counter in freezeMap equals the list length. -/
private theorem freezeMap_foldl_counter [BEq κ] [Hashable κ] [LawfulBEq κ]
    (entries : List (κ × ν)) :
    ∀ (init : RHTable κ Nat) (n : Nat),
      (entries.foldl (fun (acc, i) (k, _) => (acc.insert k i, i + 1))
        (init, n)).2 = n + entries.length := by
  intro init n
  induction entries generalizing init n with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl, List.length_cons]
    rw [ih]; omega

-- ============================================================================
-- Q5-C: Additional Structural Theorems
-- ============================================================================

/-- Q5-C helper: `toList` on an empty RHTable yields `[]`. -/
private theorem toList_empty [BEq κ] [Hashable κ] [LawfulBEq κ] (cap : Nat) (hPos : 0 < cap) :
    (RHTable.empty cap hPos : RHTable κ ν).toList = [] := by
  unfold RHTable.toList RHTable.fold
  simp only [RHTable.empty]
  rw [← Array.foldl_toList]
  exact fold_none_replicate cap []

/-- Q5-C: Freezing an empty RHTable produces a FrozenMap with empty data. -/
theorem freezeMap_empty [BEq κ] [Hashable κ] [LawfulBEq κ] (cap : Nat) (hPos : 0 < cap := by omega) :
    (freezeMap (RHTable.empty cap hPos : RHTable κ ν)).data.size = 0 := by
  rw [freezeMap_data_size, toList_empty]; simp

/-- Q5-C: `freezeObject` passes through TCB unchanged. -/
theorem freezeObject_tcb_passthrough (t : TCB) :
    freezeObject (.tcb t) = .tcb t := rfl

/-- Q5-C: `freezeObject` passes through Endpoint unchanged. -/
theorem freezeObject_endpoint_passthrough (e : Endpoint) :
    freezeObject (.endpoint e) = .endpoint e := rfl

/-- Q5-C: `freezeObject` passes through Notification unchanged. -/
theorem freezeObject_notification_passthrough (n : Notification) :
    freezeObject (.notification n) = .notification n := rfl

/-- Q5-C: `freezeObject` passes through UntypedObject unchanged. -/
theorem freezeObject_untyped_passthrough (u : UntypedObject) :
    freezeObject (.untyped u) = .untyped u := rfl

/-- Q5-C: `FrozenMap.set` preserves `data.size`. -/
theorem frozenMap_set_preserves_size [BEq κ] [Hashable κ] [LawfulBEq κ]
    (fm : FrozenMap κ ν) (k : κ) (v : ν) (fm' : FrozenMap κ ν)
    (h : fm.set k v = some fm') :
    fm'.data.size = fm.data.size := by
  unfold FrozenMap.set at h
  split at h
  · cases h
  · rename_i idx hGet
    split at h
    · rename_i hBound
      cases h
      simp [Array.size_set]
    · cases h

/-- Q5-C: `freeze` preserves the objectIndexSet (frozen version). -/
theorem freeze_preserves_objectIndexSet (ist : IntermediateState) :
    (freeze ist).objectIndexSet = freezeMap ist.state.objectIndexSet.table := rfl

end SeLe4n.Model
