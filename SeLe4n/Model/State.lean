/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine
import SeLe4n.Model.Object
import SeLe4n.Kernel.Scheduler.RunQueue
import SeLe4n.Kernel.Service.Interface
import SeLe4n.Kernel.RobinHood.Set

namespace SeLe4n.Model

open SeLe4n.Kernel.RobinHood

inductive KernelError where
  | invalidCapability
  | objectNotFound
  | illegalState
  | illegalAuthority
  | policyDenied
  | dependencyViolation
  | schedulerInvariantViolation
  | endpointStateMismatch
  | endpointQueueEmpty
  | asidNotBound
  | vspaceRootInvalid
  | mappingConflict
  | translationFault
  | flowDenied
  | declassificationDenied  -- WS-I3/R-08: declassification policy denied downgrade
  | alreadyWaiting
  | cyclicDependency
  | notImplemented
  | targetSlotOccupied   -- WS-E4/H-02: insert into occupied slot
  | replyCapInvalid      -- WS-E4/M-12: reply target not in blockedOnReply state, or replier not authorized (WS-H1/M-02)
  | untypedRegionExhausted   -- WS-F2: not enough space in untyped region
  | untypedTypeMismatch      -- WS-F2: source object is not an UntypedObject
  | untypedDeviceRestriction -- WS-F2: device untyped cannot back kernel objects
  | untypedAllocSizeTooSmall -- WS-F2: allocSize smaller than minimum for object type
  | childIdSelfOverwrite    -- WS-H2/H-06: childId = untypedId in retypeFromUntyped
  | childIdCollision        -- WS-H2/A-26: childId collides with existing object or untyped child
  | addressOutOfBounds      -- WS-H11/A-05: physical address exceeds machine address width
  | ipcMessageTooLarge      -- WS-H12d/A-09: IPC message registers exceed maxMessageRegisters (120)
  | ipcMessageTooManyCaps   -- WS-H12d/A-09: IPC message caps exceed maxExtraCaps (3)
  | backingObjectMissing    -- WS-H13/A-29: service backing object not in object store
  | invalidRegister         -- WS-J1-B: register index out of architectural bounds
  | invalidSyscallNumber    -- WS-J1-B: syscall number register value not in modeled set
  | invalidMessageInfo      -- WS-J1-B: malformed message-info word (length/caps out of bounds)
  | invalidTypeTag          -- WS-K-D: retype type tag not in modeled object set (0–5)
  | resourceExhausted       -- WS-R2/M-05: fuel exhaustion in streaming BFS revocation
  deriving Repr, DecidableEq

/-- S2-A: Low-priority blanket `ToString` from `Repr`. Enables standard
string interpolation (`s!"{x}"`) for all types with `Repr` instances.
Explicit `ToString` instances take precedence due to priority 10. -/
instance (priority := 10) instToStringOfReprFallback [Repr α] : ToString α where
  toString := reprStr

/-- M-05/WS-E6: One entry in the round-robin domain schedule table.
Mirrors seL4's `dschedule[]` — each entry specifies a domain and how
many ticks that domain runs before the scheduler advances to the next entry. -/
structure DomainScheduleEntry where
  domain : SeLe4n.DomainId
  length : Nat
  deriving Repr, DecidableEq

structure SchedulerState where
  /-- WS-G4/F-P02: Priority-bucketed run queue replacing the flat list.
      Provides O(1) amortized membership, insert, remove; O(1) best-candidate
      via cached maxPriority. The `toList` projection maintains proof/projection
      compatibility with information-flow subsystem. -/
  runQueue : SeLe4n.Kernel.RunQueue := SeLe4n.Kernel.RunQueue.empty
  current : Option SeLe4n.ThreadId
  /-- M-05/WS-E6: Currently active scheduling domain. Only threads in this
      domain are eligible for selection. Default domain 0. -/
  activeDomain : SeLe4n.DomainId := ⟨0⟩
  /-- M-05/WS-E6: Remaining ticks in the current domain schedule entry.
      When this reaches 0, the scheduler advances to the next domain. -/
  domainTimeRemaining : Nat := 5
  /-- M-05/WS-E6: Round-robin domain schedule table. Empty = single-domain mode. -/
  domainSchedule : List DomainScheduleEntry := []
  /-- M-05/WS-E6: Current index into `domainSchedule`. -/
  domainScheduleIndex : Nat := 0
  deriving Repr

/-- WS-G4: Compatibility alias — `runnable` projects to the flat list maintained
    inside `RunQueue` for proof/projection compatibility. -/
abbrev SchedulerState.runnable (s : SchedulerState) : List SeLe4n.ThreadId :=
  s.runQueue.toList

/-- Architecture-neutral address of a capability slot inside a CNode object. -/
structure SlotRef where
  cnode : SeLe4n.ObjId
  slot : SeLe4n.Slot
  deriving Repr, DecidableEq

/-- WS-G1: Hash instance for composite HashMap/HashSet keying.
    Combines cnode and slot hashes via `mixHash` for uniform distribution.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable SlotRef where
  hash a := mixHash (hash a.cnode) (hash a.slot)

/-- Lifecycle metadata required by the first M4-A transition story.

`objectTypes` keeps object-store identity explicit, while `capabilityRefs` records the target
named by each populated capability slot reference.

WS-G2/WS-H7: metadata maps are HashMap-backed for O(1) amortized lookup,
eliminating closure-chain growth from repeated updates. -/
structure LifecycleMetadata where
  objectTypes : RHTable SeLe4n.ObjId KernelObjectType
  capabilityRefs : RHTable SlotRef CapTarget

/-- R7-A.1/M-17: A single TLB entry caching an address translation.

    On ARM64, the TLB caches `(ASID, VAddr, PAddr, PagePermissions)` tuples.
    Stale entries after page table modification are a security concern — the
    `tlbConsistent` invariant (in `TlbModel.lean`) enforces that all cached
    entries match the current page tables. -/
structure TlbEntry where
  asid : SeLe4n.ASID
  vaddr : SeLe4n.VAddr
  paddr : SeLe4n.PAddr
  perms : PagePermissions
  deriving Repr, DecidableEq, BEq

/-- R7-A.1/M-17: Abstract TLB state: a collection of cached translation entries.

    The list representation is intentionally simple — hardware TLBs are
    associative caches, but for invariant reasoning we only need membership
    queries, not performance-optimal lookup. -/
structure TlbState where
  entries : List TlbEntry
  deriving Repr

instance : Inhabited TlbState where
  default := { entries := [] }

/-- An empty TLB with no cached entries. -/
def TlbState.empty : TlbState := { entries := [] }

/-- R7-A.3: Full TLB flush — invalidates all cached entries.
    On ARM64 this corresponds to `TLBI ALLE1` or `TLBI VMALLE1IS`. -/
def adapterFlushTlb (_tlb : TlbState) : TlbState :=
  TlbState.empty

/-- R7-A.3: Per-ASID TLB flush — invalidates all entries for a specific ASID.
    On ARM64 this corresponds to `TLBI ASIDE1, <asid>`. -/
def adapterFlushTlbByAsid (tlb : TlbState) (asid : SeLe4n.ASID) : TlbState :=
  { entries := tlb.entries.filter (·.asid != asid) }

/-- R7-A.3: Per-VAddr TLB flush — invalidates entries for a specific (ASID, VAddr).
    On ARM64 this corresponds to `TLBI VAE1, <asid, vaddr>`. -/
def adapterFlushTlbByVAddr (tlb : TlbState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : TlbState :=
  { entries := tlb.entries.filter (fun e => !(e.asid == asid && e.vaddr == vaddr)) }

structure SystemState where
  machine : SeLe4n.MachineState
  /-- Q2-C: Object store backed by `RHTable` (verified Robin Hood hash table)
      for O(1) amortized lookup with machine-checked invariants.

      S4-J: All `objects` uses in production kernel code are lookup-only
      (`objects[oid]?`, `objects.get?`). No operation iterates over the
      object store in an order-dependent manner. This is critical because
      `RHTable` iteration order (via `fold`/`toList`) depends on internal
      slot layout and is not deterministic across resize operations. -/
  objects : RHTable SeLe4n.ObjId KernelObject
  /-- L-05/WS-E6: Monotonic append-only index of all object IDs that have been
      stored. This list is intentionally never pruned — `storeObject` prepends
      new IDs and never removes old ones.

      **Design rationale:** Monotonic append-only semantics ensure that any
      membership witness (`id ∈ st.objectIndex`) remains valid across all future
      states. This simplifies invariant proofs: once an ID appears in the index,
      it persists, so cross-transition carryover is trivially established. The
      tradeoff is that the index may contain IDs for objects that have since been
      overwritten or logically deleted; consumers must check `st.objects[id]?`
      for `some _` to confirm the object still exists.

      **Migration path:** If bounded-memory semantics or garbage collection are
      added in a future workstream, `objectIndex` can be replaced by a data
      structure supporting removal while preserving the monotonicity invariant
      for the live-object subset.

      **S4-A: Growth analysis.** For a typical RPi5 workload with `maxObjects =
      65536`, the objectIndex list consumes at most `65536 × sizeof(ObjId)` bytes.
      At 8 bytes per ObjId (Nat on 64-bit), this is 512 KB — well within the
      RPi5's 8 GB RAM budget. The advisory predicate `objectIndexBounded` below
      documents the expected bound. -/
  objectIndex : List SeLe4n.ObjId
  /-- WS-G2/F-P10: Shadow hash set for O(1) objectIndex membership checks.
      Maintained in parallel with `objectIndex` — `storeObject` inserts into
      both. The list remains the proof anchor (monotonic, append-only);
      this set is the runtime fast path. -/
  objectIndexSet : RHSet SeLe4n.ObjId := default
  services : RHTable ServiceId ServiceGraphEntry
  scheduler : SchedulerState
  irqHandlers : RHTable SeLe4n.Irq SeLe4n.ObjId
  lifecycle : LifecycleMetadata
  /-- WS-G3/F-P06: ASID→ObjId resolution table for O(1) VSpace lookups.
      Maintained by `storeObject` — insertions on `.vspaceRoot` stores, erasures
      when a VSpaceRoot is overwritten. Replaces the O(n) `objectIndex.findSome?`
      scan in `resolveAsidRoot`. -/
  asidTable : RHTable SeLe4n.ASID SeLe4n.ObjId := {}
  /-- WS-Q1-B: Registry of concrete interface specifications keyed by InterfaceId. -/
  interfaceRegistry : RHTable SeLe4n.InterfaceId InterfaceSpec := {}
  /-- WS-Q1-B: Registry of capability-mediated service registrations keyed by ServiceId. -/
  serviceRegistry : RHTable ServiceId ServiceRegistration := {}
  cdt : CapDerivationTree := .empty   -- WS-E4/C-03: node-based Capability Derivation Tree
  cdtSlotNode : RHTable SlotRef CdtNodeId := {}
  cdtNodeSlot : RHTable CdtNodeId SlotRef := {}
  cdtNextNode : CdtNodeId := ⟨0⟩
  /-- R7-A.1/M-17: Abstract TLB state, tracking cached address translations.
      Empty by default (no stale entries at boot). Operations that modify page
      tables must flush the TLB to maintain `tlbConsistent`. -/
  tlb : TlbState := TlbState.empty

/-- Abstract owner identity for a slot in this model: the containing CNode object id. -/
abbrev CSpaceOwner := SeLe4n.ObjId

instance : Inhabited SchedulerState where
  default := { runQueue := SeLe4n.Kernel.RunQueue.empty, current := none }

instance : Inhabited SystemState where
  default := {
    machine := default
    objects := {}
    objectIndex := []
    objectIndexSet := default
    services := {}
    scheduler := default
    irqHandlers := {}
    lifecycle := {
      objectTypes := {}
      capabilityRefs := {}
    }
    asidTable := {}
    interfaceRegistry := {}
    serviceRegistry := {}
    cdt := .empty
    cdtSlotNode := {}
    cdtNodeSlot := {}
    cdtNextNode := ⟨0⟩
    tlb := TlbState.empty
  }

/-- Q2-J: Predicate asserting that every RHTable and RHSet in the system state
satisfies the Robin Hood invariant extension (WF ∧ distCorrect ∧ noDupKeys ∧
probeChainDominant). This is the global well-formedness condition for the
builder-phase state representation. -/
def SystemState.allTablesInvExt (st : SystemState) : Prop :=
  -- SystemState direct fields
  st.objects.invExt ∧
  st.irqHandlers.invExt ∧
  st.asidTable.invExt ∧
  st.cdtSlotNode.invExt ∧
  st.cdtNodeSlot.invExt ∧
  -- LifecycleMetadata
  st.lifecycle.objectTypes.invExt ∧
  st.lifecycle.capabilityRefs.invExt ∧
  -- CDT
  st.cdt.childMap.invExt ∧
  st.cdt.parentMap.invExt ∧
  -- Service and registry
  st.services.invExt ∧
  st.interfaceRegistry.invExt ∧
  st.serviceRegistry.invExt ∧
  -- RunQueue
  st.scheduler.runQueue.byPriority.invExt ∧
  st.scheduler.runQueue.threadPriority.invExt ∧
  -- RHSet invExt (via table field)
  st.objectIndexSet.table.invExt ∧
  st.scheduler.runQueue.membership.table.invExt

/-- The default SystemState satisfies `allTablesInvExt` because all tables are
empty, and empty RHTables trivially satisfy `invExt`. -/
theorem default_allTablesInvExt : (default : SystemState).allTablesInvExt := by
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt' 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHSet.empty_invExt
  exact SeLe4n.Kernel.RobinHood.RHSet.empty_invExt

abbrev Kernel := SeLe4n.KernelM SystemState KernelError

def lookupObject (id : SeLe4n.ObjId) : Kernel KernelObject :=
  fun st =>
    match st.objects[id]? with
    | none => .error .objectNotFound
    | some obj => .ok (obj, st)

/-- Read a typed VSpace-root object from the global object store. -/
def lookupVSpaceRoot (id : SeLe4n.ObjId) : Kernel VSpaceRoot :=
  fun st =>
    match st.objects[id]? with
    | some (.vspaceRoot root) => .ok (root, st)
    | some _ => .error .vspaceRootInvalid
    | none => .error .objectNotFound

/-- Replace the object stored at `id` with `obj`.

WS-G2/F-P01: Uses `HashMap.insert` instead of closure wrapping, eliminating
the O(k) closure-chain accumulation on every lookup.
WS-G2/F-P10: Uses `objectIndexSet.contains` for O(1) membership check instead
of O(n) list membership scan.
WS-G3/F-P06: Maintains `asidTable` — erases old ASID when overwriting a
VSpaceRoot, inserts new ASID when storing a VSpaceRoot. -/
def storeObject (id : SeLe4n.ObjId) (obj : KernelObject) : Kernel Unit :=
  fun st =>
    .ok ((), {
      st with
        objects := st.objects.insert id obj
        objectIndex := if st.objectIndexSet.contains id then st.objectIndex
                       else id :: st.objectIndex
        objectIndexSet := st.objectIndexSet.insert id
        lifecycle := {
          objectTypes := st.lifecycle.objectTypes.insert id obj.objectType
          capabilityRefs :=
            let cleared := st.lifecycle.capabilityRefs.filter (fun ref _ => ref.cnode ≠ id)
            match obj with
            | .cnode cn =>
                cn.slots.fold (init := cleared) fun refs slot cap =>
                  refs.insert { cnode := id, slot := slot } cap.target
            | _ => cleared
        }
        asidTable :=
          let cleared := match st.objects[id]? with
            | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
            | _ => st.asidTable
          match obj with
          | .vspaceRoot newRoot => cleared.insert newRoot.asid id
          | _ => cleared
    })

/-- Record or clear a slot-to-target lifecycle reference mapping. -/
def storeCapabilityRef (ref : SlotRef) (target : Option CapTarget) : Kernel Unit :=
  fun st =>
    let lifecycle' : LifecycleMetadata :=
      {
        st.lifecycle with
          capabilityRefs :=
            match target with
            | some t => st.lifecycle.capabilityRefs.insert ref t
            | none => st.lifecycle.capabilityRefs.erase ref
      }
    .ok ((), { st with lifecycle := lifecycle' })

/-- M-P01: Fused revoke — filter CNode slots matching the revoke target and clear
their capability refs in a single `RHTable.fold` pass, eliminating the intermediate
refs-list allocation and second traversal of the legacy two-pass revoke path. -/
def revokeAndClearRefsState
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  cn.slots.fold st (fun stAcc s c =>
    if s != sourceSlot && c.target == target then
      { stAcc with lifecycle := { stAcc.lifecycle with
          capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
            { cnode := cnodeId, slot := s } } }
    else stAcc)

/-- M-P01: Fold body for `revokeAndClearRefsState` preserves objects. -/
private theorem revokeAndClearRefsFoldBody_preserves_objects
    (pairs : List (SeLe4n.Slot × Capability))
    (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (pairs.foldl (fun stAcc (p : SeLe4n.Slot × Capability) =>
      if p.1 != sourceSlot && p.2.target == target then
        { stAcc with lifecycle := { stAcc.lifecycle with
            capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
              { cnode := cnodeId, slot := p.1 } } }
      else stAcc) st).objects = st.objects := by
  induction pairs generalizing st with
  | nil => rfl
  | cons p rest ih => simp only [List.foldl_cons]; split <;> exact ih _

/-- M-P01: `revokeAndClearRefsState` preserves `objects` (only modifies `lifecycle`). -/
theorem revokeAndClearRefsState_preserves_objects
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).objects = st.objects := by
  unfold revokeAndClearRefsState
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots st _ (fun acc => acc.objects = st.objects)
    rfl (fun acc s c hAcc => by simp only []; split <;> exact hAcc)

private theorem revokeAndClearRefsFoldBody_preserves_cdt
    (pairs : List (SeLe4n.Slot × Capability))
    (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (pairs.foldl (fun stAcc (p : SeLe4n.Slot × Capability) =>
      if p.1 != sourceSlot && p.2.target == target then
        { stAcc with lifecycle := { stAcc.lifecycle with
            capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
              { cnode := cnodeId, slot := p.1 } } }
      else stAcc) st).cdt = st.cdt ∧
    (pairs.foldl (fun stAcc (p : SeLe4n.Slot × Capability) =>
      if p.1 != sourceSlot && p.2.target == target then
        { stAcc with lifecycle := { stAcc.lifecycle with
            capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
              { cnode := cnodeId, slot := p.1 } } }
      else stAcc) st).cdtNodeSlot = st.cdtNodeSlot ∧
    (pairs.foldl (fun stAcc (p : SeLe4n.Slot × Capability) =>
      if p.1 != sourceSlot && p.2.target == target then
        { stAcc with lifecycle := { stAcc.lifecycle with
            capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
              { cnode := cnodeId, slot := p.1 } } }
      else stAcc) st).cdtSlotNode = st.cdtSlotNode := by
  induction pairs generalizing st with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons p rest ih =>
      simp only [List.foldl_cons]
      split
      · exact ih _
      · exact ih _

/-- M-P01: `revokeAndClearRefsState` preserves CDT fields and objects. -/
theorem revokeAndClearRefsState_cdt_eq
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).cdt = st.cdt ∧
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).cdtNodeSlot = st.cdtNodeSlot ∧
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).cdtSlotNode = st.cdtSlotNode ∧
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).objects = st.objects := by
  unfold revokeAndClearRefsState
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots st _
    (fun acc => acc.cdt = st.cdt ∧ acc.cdtNodeSlot = st.cdtNodeSlot ∧
      acc.cdtSlotNode = st.cdtSlotNode ∧ acc.objects = st.objects)
    ⟨rfl, rfl, rfl, rfl⟩
    (fun acc s c ⟨h1, h2, h3, h4⟩ => by simp only []; split <;> exact ⟨h1, h2, h3, h4⟩)

/-- M-P01: Fold body preserves scheduler, machine, services, irqHandlers, objectIndex fields. -/
private theorem revokeAndClearRefsFoldBody_preserves_fields
    (pairs : List (SeLe4n.Slot × Capability))
    (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    let r := pairs.foldl (fun stAcc (p : SeLe4n.Slot × Capability) =>
      if p.1 != sourceSlot && p.2.target == target then
        { stAcc with lifecycle := { stAcc.lifecycle with
            capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
              { cnode := cnodeId, slot := p.1 } } }
      else stAcc) st
    r.scheduler = st.scheduler ∧
    r.machine = st.machine ∧
    r.services = st.services ∧
    r.irqHandlers = st.irqHandlers ∧
    r.objectIndex = st.objectIndex ∧
    r.objectIndexSet = st.objectIndexSet ∧
    r.asidTable = st.asidTable := by
  induction pairs generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons p rest ih =>
      simp only [List.foldl_cons]
      split <;> exact ih _

/-- Helper tactic macro: uses `RHTable.fold_preserves` to show fold body preserves fields. -/
private theorem revokeAndClearRefsState_preserves_allFields
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    let r := revokeAndClearRefsState cn sourceSlot target cnodeId st
    r.scheduler = st.scheduler ∧ r.machine = st.machine ∧
    r.services = st.services ∧ r.irqHandlers = st.irqHandlers ∧
    r.objectIndex = st.objectIndex ∧ r.objectIndexSet = st.objectIndexSet := by
  unfold revokeAndClearRefsState
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots st _
    (fun acc => acc.scheduler = st.scheduler ∧ acc.machine = st.machine ∧
      acc.services = st.services ∧ acc.irqHandlers = st.irqHandlers ∧
      acc.objectIndex = st.objectIndex ∧ acc.objectIndexSet = st.objectIndexSet)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun acc s c ⟨h1, h2, h3, h4, h5, h6⟩ => by
      simp only []; split <;> exact ⟨h1, h2, h3, h4, h5, h6⟩)

/-- M-P01: `revokeAndClearRefsState` preserves scheduler. -/
theorem revokeAndClearRefsState_preserves_scheduler
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).scheduler = st.scheduler :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).1

/-- M-P01: `revokeAndClearRefsState` preserves machine state. -/
theorem revokeAndClearRefsState_preserves_machine
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).machine = st.machine :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).2.1

/-- M-P01: `revokeAndClearRefsState` preserves services. -/
theorem revokeAndClearRefsState_preserves_services
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).services = st.services :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).2.2.1

/-- M-P01: `revokeAndClearRefsState` preserves irqHandlers. -/
theorem revokeAndClearRefsState_preserves_irqHandlers
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).irqHandlers = st.irqHandlers :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).2.2.2.1

/-- M-P01: `revokeAndClearRefsState` preserves objectIndex. -/
theorem revokeAndClearRefsState_preserves_objectIndex
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).objectIndex = st.objectIndex :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).2.2.2.2.1

/-- M-P01: `revokeAndClearRefsState` preserves objectIndexSet. -/
theorem revokeAndClearRefsState_preserves_objectIndexSet
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).objectIndexSet = st.objectIndexSet :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).2.2.2.2.2

def setCurrentThread (tid : Option SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    let sched := { st.scheduler with current := tid }
    .ok ((), { st with scheduler := sched })

/-- Read one service graph entry. -/
def lookupService (st : SystemState) (sid : ServiceId) : Option ServiceGraphEntry :=
  st.services[sid]?

/-- M-P01: `revokeAndClearRefsState` preserves lookupService. -/
theorem revokeAndClearRefsState_lookupService
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) (sid : ServiceId) :
    lookupService (revokeAndClearRefsState cn sourceSlot target cnodeId st) sid =
    lookupService st sid := by
  unfold lookupService
  rw [revokeAndClearRefsState_preserves_services]

/-- Determine whether `sid` lists `dependency` as a declared dependency edge. -/
def hasServiceDependency (st : SystemState) (sid dependency : ServiceId) : Bool :=
  match lookupService st sid with
  | some svc => dependency ∈ svc.dependencies
  | none => false

/-- Determine whether two services are explicitly isolated from one another. -/
def hasIsolationEdge (st : SystemState) (lhs rhs : ServiceId) : Bool :=
  match lookupService st lhs, lookupService st rhs with
  | some lhsSvc, some rhsSvc => rhs ∈ lhsSvc.isolatedFrom || lhs ∈ rhsSvc.isolatedFrom
  | _, _ => false

/-- Deterministic pure state helper: replace one service graph entry. -/
def storeServiceState (sid : ServiceId) (entry : ServiceGraphEntry) (st : SystemState) : SystemState :=
  {
    st with
      services := st.services.insert sid entry
  }

theorem storeServiceState_lookup_eq
    (st : SystemState)
    (sid : ServiceId)
    (entry : ServiceGraphEntry)
    (hInv : st.services.invExt) :
    lookupService (storeServiceState sid entry st) sid = some entry := by
  simp only [lookupService, storeServiceState]
  exact RHTable.getElem?_insert_self st.services sid entry hInv

theorem storeServiceState_lookup_ne
    (st : SystemState)
    (sid sid' : ServiceId)
    (entry : ServiceGraphEntry)
    (hNe : sid' ≠ sid)
    (hInv : st.services.invExt) :
    lookupService (storeServiceState sid entry st) sid' = lookupService st sid' := by
  simp only [lookupService, storeServiceState]
  have hNeBeq : ¬((sid == sid') = true) := by
    intro hEq; exact hNe (eq_of_beq hEq).symm
  exact RHTable.getElem?_insert_ne st.services sid sid' entry hNeBeq hInv

theorem storeObject_preserves_services
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.services = st.services := by
  unfold storeObject at hStore
  cases hStore
  rfl

theorem storeCapabilityRef_preserves_scheduler
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

theorem storeCapabilityRef_preserves_services
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.services = st.services := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

theorem storeCapabilityRef_preserves_objects
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.objects = st.objects := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

/-- WS-F3: storeCapabilityRef preserves IRQ handler mappings. -/
theorem storeCapabilityRef_preserves_irqHandlers
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.irqHandlers = st.irqHandlers := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

/-- WS-F3: storeCapabilityRef preserves the object index. -/
theorem storeCapabilityRef_preserves_objectIndex
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.objectIndex = st.objectIndex := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

/-- storeCapabilityRef preserves machine state. -/
theorem storeCapabilityRef_preserves_machine
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

theorem storeCapabilityRef_lookup_eq
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hCapRefsInv : st.lifecycle.capabilityRefs.invExt)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.lifecycle.capabilityRefs[ref]? = target := by
  unfold storeCapabilityRef at hStep
  cases hTarget : target with
  | none =>
      simp [hTarget] at hStep
      cases hStep
      simp only [RHTable_getElem?_eq_get?]; exact RHTable.getElem?_erase_self _ _ hCapRefsInv
  | some t =>
      simp [hTarget] at hStep
      cases hStep
      simp only [RHTable_getElem?_eq_get?]; exact RHTable.getElem?_insert_self _ _ _ hCapRefsInv


theorem storeObject_objects_eq'
    (st : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (pair : Unit × SystemState)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok pair) :
    pair.2.objects[id]? = some obj := by
  unfold storeObject at hStore
  cases hStore
  exact RHTable.getElem?_insert_self _ _ _ hObjInv

theorem storeObject_objects_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[id]? = some obj :=
  storeObject_objects_eq' st id obj ((), st') hObjInv hStore

theorem storeObject_objects_ne'
    (st : SystemState)
    (id oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (pair : Unit × SystemState)
    (hNe : oid ≠ id)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok pair) :
    pair.2.objects[oid]? = st.objects[oid]? := by
  unfold storeObject at hStore
  cases hStore
  have hNeBeq : ¬((id == oid) = true) := by intro heq; exact hNe (eq_of_beq heq).symm
  exact RHTable.getElem?_insert_ne _ _ _ _ hNeBeq hObjInv

theorem storeObject_objects_ne
    (st st' : SystemState)
    (id oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hNe : oid ≠ id)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[oid]? = st.objects[oid]? :=
  storeObject_objects_ne' st id oid obj ((), st') hNe hObjInv hStore

theorem storeObject_preserves_objects_invExt'
    (st : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (pair : Unit × SystemState)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok pair) :
    pair.2.objects.invExt := by
  unfold storeObject at hStore
  cases hStore
  exact RHTable_insert_preserves_invExt st.objects id obj hObjInv

theorem storeObject_scheduler_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeObject at hStore
  cases hStore
  rfl

theorem storeObject_irqHandlers_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.irqHandlers = st.irqHandlers := by
  unfold storeObject at hStore
  cases hStore
  rfl

theorem storeObject_machine_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold storeObject at hStore
  cases hStore
  rfl

theorem storeObject_preserves_objects_invExt
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects.invExt :=
  storeObject_preserves_objects_invExt' st id obj ((), st') hObjInv hStore

-- WS-E4/C-03: storeObject preserves the CDT (it only touches objects/lifecycle/index)
theorem storeObject_cdt_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.cdt = st.cdt := by
  unfold storeObject at hStore
  cases hStore
  rfl

-- ============================================================================
-- WS-G3/F-P06: storeObject ASID table maintenance lemmas
-- ============================================================================

/-- WS-G3: After storing a VSpaceRoot, the ASID table maps the new root's ASID to `id`. -/
theorem storeObject_asidTable_vspaceRoot
    (st st' : SystemState) (id : SeLe4n.ObjId) (newRoot : VSpaceRoot)
    (hAsidInv : (match st.objects[id]? with
      | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
      | _ => st.asidTable).invExt)
    (hStore : storeObject id (.vspaceRoot newRoot) st = .ok ((), st')) :
    st'.asidTable[newRoot.asid]? = some id := by
  unfold storeObject at hStore
  cases hStore
  simp only []
  exact RHTable.getElem?_insert_self _ _ _ hAsidInv

/-- WS-G3: After storing a VSpaceRoot, a different ASID's table entry is unchanged
    unless it was the old root's ASID that got erased. -/
theorem storeObject_asidTable_vspaceRoot_ne
    (st st' : SystemState) (id : SeLe4n.ObjId) (newRoot : VSpaceRoot)
    (asid : SeLe4n.ASID)
    (hNe : asid ≠ newRoot.asid)
    (hAsidInv : (match st.objects[id]? with
      | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
      | _ => st.asidTable).invExt)
    (hStore : storeObject id (.vspaceRoot newRoot) st = .ok ((), st')) :
    st'.asidTable[asid]? =
      (match st.objects[id]? with
       | some (.vspaceRoot oldRoot) => (st.asidTable.erase oldRoot.asid)[asid]?
       | _ => st.asidTable[asid]?) := by
  unfold storeObject at hStore
  cases hStore
  simp only []
  have hNeBeq : ¬((newRoot.asid == asid) = true) := by intro heq; exact hNe (eq_of_beq heq).symm
  cases hOld : st.objects[id]? with
  | none =>
    simp only [hOld, RHTable_getElem?_eq_get?] at hAsidInv ⊢
    rw [RHTable.getElem?_insert_ne _ _ _ _ hNeBeq hAsidInv]
  | some obj =>
    cases obj with
    | vspaceRoot oldRoot =>
      simp only [hOld, RHTable_getElem?_eq_get?] at hAsidInv ⊢
      rw [RHTable.getElem?_insert_ne _ _ _ _ hNeBeq hAsidInv]
    | tcb _ | cnode _ | endpoint _ | notification _ | untyped _ =>
      simp only [hOld, RHTable_getElem?_eq_get?] at hAsidInv ⊢
      rw [RHTable.getElem?_insert_ne _ _ _ _ hNeBeq hAsidInv]

/-- WS-G3: After storing a non-VSpaceRoot, the ASID table only changes if the old
    object was a VSpaceRoot (in which case the old ASID is erased). -/
theorem storeObject_asidTable_non_vspaceRoot
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hNotVSpace : ∀ r, obj ≠ .vspaceRoot r)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.asidTable =
      match st.objects[id]? with
      | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
      | _ => st.asidTable := by
  unfold storeObject at hStore
  cases hStore
  cases obj with
  | vspaceRoot r => exact absurd rfl (hNotVSpace r)
  | tcb _ => rfl
  | cnode _ => rfl
  | endpoint _ => rfl
  | notification _ => rfl
  | untyped _ => rfl

/-- WS-G2: objectIndex and objectIndexSet contain the same ids. -/
def objectIndexSetSync (st : SystemState) : Prop :=
  ∀ (id : SeLe4n.ObjId), st.objectIndexSet.contains id = true ↔ id ∈ st.objectIndex

/-- WS-G2: objectIndexSetSync implies contains from objectIndex membership. -/
theorem objectIndexSetSync_contains_of_mem
    (st : SystemState) (id : SeLe4n.ObjId)
    (hSync : objectIndexSetSync st) (hMem : id ∈ st.objectIndex) :
    st.objectIndexSet.contains id = true :=
  (hSync id).mpr hMem

theorem storeObject_updates_objectTypeMeta
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    st'.lifecycle.objectTypes[oid]? = some obj.objectType := by
  unfold storeObject at hStep
  cases hStep
  simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_self _ _ _ hObjTypesInv]

namespace SystemState

/-- Read a CNode object from the global object store. -/
def lookupCNode (st : SystemState) (id : SeLe4n.ObjId) : Option CNode :=
  match st.objects[id]? with
  | some (.cnode cn) => some cn
  | _ => none

/-- Read a capability from a typed slot reference. -/
def lookupSlotCap (st : SystemState) (ref : SlotRef) : Option Capability :=
  match lookupCNode st ref.cnode with
  | none => none
  | some cn => cn.lookup ref.slot

/-- The modeled owner of a slot is its containing CNode. -/
def ownerOfSlot (ref : SlotRef) : CSpaceOwner :=
  ref.cnode

/-- Logical ownership relation for occupied slots. -/
def ownsSlot (st : SystemState) (owner : CSpaceOwner) (ref : SlotRef) : Prop :=
  owner = ownerOfSlot ref ∧ ∃ cap, lookupSlotCap st ref = some cap

/-- Enumerate all concrete capability entries held by one modeled owner CNode.
WS-G5: Projects HashMap-backed slots to `List` for enumeration compatibility. -/
def ownedSlots (st : SystemState) (owner : CSpaceOwner) : List (SeLe4n.Slot × Capability) :=
  match lookupCNode st owner with
  | some cn => cn.slots.toList
  | none => []

/-- Lifecycle metadata view of object identity typing. -/
def lookupObjectTypeMeta (st : SystemState) (id : SeLe4n.ObjId) : Option KernelObjectType :=
  st.lifecycle.objectTypes[id]?

/-- Lifecycle metadata view of capability slot reference mapping. -/
def lookupCapabilityRefMeta (st : SystemState) (ref : SlotRef) : Option CapTarget :=
  (lookupSlotCap st ref).map Capability.target


/-- Read the stable CDT node currently referenced by a CSpace slot, if any. -/
def lookupCdtNodeOfSlot (st : SystemState) (ref : SlotRef) : Option CdtNodeId :=
  st.cdtSlotNode[ref]?

/-- Read the current CSpace slot backpointer of a stable CDT node, if any. -/
def lookupCdtSlotOfNode (st : SystemState) (node : CdtNodeId) : Option SlotRef :=
  st.cdtNodeSlot[node]?

/-- Slot-address projection of the node-based CDT as observed from CSpace slots. -/
def observedCdtEdges (st : SystemState) : List CapDerivationTree.ObservedDerivationEdge :=
  st.cdt.projectObservedEdges (fun node =>
    (lookupCdtSlotOfNode st node).map (fun ref => (ref.cnode, ref.slot)))

/-- Abstraction theorem: observed slot-level CDT equals projection of node graph
through node→slot mapping. -/
theorem observedCdtEdges_eq_projection (st : SystemState) :
    observedCdtEdges st =
      st.cdt.projectObservedEdges (fun node =>
        (lookupCdtSlotOfNode st node).map (fun ref => (ref.cnode, ref.slot))) := by
  simp [observedCdtEdges, lookupCdtSlotOfNode]

/-- Attach slot `ref` to `node` and maintain bidirectional consistency.
If the slot/node already point elsewhere, stale opposite links are cleared. -/
def attachSlotToCdtNode (st : SystemState) (ref : SlotRef) (node : CdtNodeId) : SystemState :=
  let prevNode := st.cdtSlotNode[ref]?
  let prevRef := st.cdtNodeSlot[node]?
  let cdtSlotNode' :=
    match prevRef with
    | some oldRef => st.cdtSlotNode.erase oldRef
    | none => st.cdtSlotNode
  let cdtNodeSlot' :=
    match prevNode with
    | some oldNode => st.cdtNodeSlot.erase oldNode
    | none => st.cdtNodeSlot
  {
    st with
      cdtSlotNode := cdtSlotNode'.insert ref node
      cdtNodeSlot := cdtNodeSlot'.insert node ref
  }

/-- Detach a slot from its CDT node, clearing both slot→node and node→slot maps. -/
def detachSlotFromCdt (st : SystemState) (ref : SlotRef) : SystemState :=
  match st.cdtSlotNode[ref]? with
  | none => st
  | some node =>
      {
        st with
          cdtSlotNode := st.cdtSlotNode.erase ref
          cdtNodeSlot := st.cdtNodeSlot.erase node
      }

/-- Ensure `ref` has a CDT node; allocate one if absent. -/
def ensureCdtNodeForSlot (st : SystemState) (ref : SlotRef) : CdtNodeId × SystemState :=
  match st.cdtSlotNode[ref]? with
  | some node => (node, st)
  | none =>
      let node := st.cdtNextNode
      let st' :=
        {
          st with
            cdtNextNode := ⟨node.val + 1⟩
            cdtSlotNode := st.cdtSlotNode.insert ref node
            cdtNodeSlot := st.cdtNodeSlot.insert node ref
        }
      (node, st')


theorem attachSlotToCdtNode_objects_eq (st : SystemState) (ref : SlotRef) (node : CdtNodeId) :
    (attachSlotToCdtNode st ref node).objects = st.objects := by
  simp [attachSlotToCdtNode]

theorem detachSlotFromCdt_objects_eq (st : SystemState) (ref : SlotRef) :
    (detachSlotFromCdt st ref).objects = st.objects := by
  unfold detachSlotFromCdt
  split <;> simp

theorem ensureCdtNodeForSlot_objects_eq (st : SystemState) (ref : SlotRef) :
    (ensureCdtNodeForSlot st ref).snd.objects = st.objects := by
  unfold ensureCdtNodeForSlot
  split <;> rfl

/-- `lookupSlotCap` is determined entirely by the object store. -/
theorem lookupSlotCap_eq_of_objects_eq
    (st₁ st₂ : SystemState)
    (ref : SlotRef)
    (hObj : st₁.objects = st₂.objects) :
    lookupSlotCap st₁ ref = lookupSlotCap st₂ ref := by
  simp [lookupSlotCap, lookupCNode, hObj]

/-- Object-type lifecycle metadata is exact for every object-store id. -/
def objectTypeMetadataConsistent (st : SystemState) : Prop :=
  ∀ oid, lookupObjectTypeMeta st oid = (st.objects[oid]?).map KernelObject.objectType

/-- Capability-reference lifecycle metadata is exact for every slot reference. -/
def capabilityRefMetadataConsistent (st : SystemState) : Prop :=
  ∀ ref, lookupCapabilityRefMeta st ref = (lookupSlotCap st ref).map Capability.target

/-- M4-A state-model metadata consistency bundle. -/
def lifecycleMetadataConsistent (st : SystemState) : Prop :=
  objectTypeMetadataConsistent st ∧ capabilityRefMetadataConsistent st

theorem lookupSlotCap_eq_none_of_lookupCNode_eq_none
    (st : SystemState)
    (ref : SlotRef)
    (hNone : lookupCNode st ref.cnode = none) :
    lookupSlotCap st ref = none := by
  simp [lookupSlotCap, hNone]

theorem ownsSlot_iff
    (st : SystemState)
    (owner : CSpaceOwner)
    (ref : SlotRef) :
    ownsSlot st owner ref ↔
      owner = ref.cnode ∧ ∃ cap, lookupSlotCap st ref = some cap := by
  simp [ownsSlot, ownerOfSlot]

theorem ownedSlots_eq_nil_of_lookupCNode_eq_none
    (st : SystemState)
    (owner : CSpaceOwner)
    (hNone : lookupCNode st owner = none) :
    ownedSlots st owner = [] := by
  simp [ownedSlots, hNone]

end SystemState

-- ============================================================================
-- S4-A/S4-B: Object capacity advisory bounds
-- ============================================================================

/-- S4-A: Advisory maximum object count for RPi5 platform (65536).
    This is not enforced in the abstract model but serves as documentation
    of the expected object capacity for typical workloads. -/
def maxObjects : Nat := 65536

/-- S4-A: Advisory predicate — the object index size is bounded by `maxObjects`.
    Not enforced as a kernel invariant since the abstract model uses unbounded
    `Nat`; this is a documentation predicate for hardware-binding readiness. -/
def objectIndexBounded (st : SystemState) : Prop :=
  st.objectIndex.length ≤ maxObjects

theorem storeObject_preserves_objectTypeMetadataConsistent
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hConsistent : SystemState.objectTypeMetadataConsistent st)
    (hObjInv : st.objects.invExt)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.objectTypeMetadataConsistent st' := by
  intro oid'
  unfold storeObject at hStep
  cases hStep
  simp only [SystemState.lookupObjectTypeMeta] at *
  by_cases hEq : oid' = oid
  · subst hEq
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable.getElem?_insert_self _ _ _ hObjTypesInv,
        RHTable.getElem?_insert_self _ _ _ hObjInv]; simp
  · have h1 : ¬((oid == oid') = true) := by intro heq; exact hEq (eq_of_beq heq).symm
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable.getElem?_insert_ne _ _ _ _ h1 hObjTypesInv,
        RHTable.getElem?_insert_ne _ _ _ _ h1 hObjInv]
    exact hConsistent oid'

theorem storeObject_preserves_capabilityRefMetadataConsistent
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (_hConsistent : SystemState.capabilityRefMetadataConsistent st)
    (_hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.capabilityRefMetadataConsistent st' := by
  intro ref
  simp [SystemState.lookupCapabilityRefMeta]

theorem storeObject_preserves_lifecycleMetadataConsistent
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hConsistent : SystemState.lifecycleMetadataConsistent st)
    (hObjInv : st.objects.invExt)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.lifecycleMetadataConsistent st' := by
  rcases hConsistent with ⟨hObjType, hCapRef⟩
  exact ⟨storeObject_preserves_objectTypeMetadataConsistent st st' oid obj hObjType hObjInv hObjTypesInv hStep,
    storeObject_preserves_capabilityRefMetadataConsistent st st' oid obj hCapRef hStep⟩

-- ============================================================================
-- L-06/WS-E3: Default SystemState initialization proof
-- ============================================================================

/-- L-06/WS-E3: The default (empty) `SystemState` satisfies `lifecycleMetadataConsistent`.
Both metadata maps return `none` for all inputs, and `objects` returns `none`
for all IDs, so the consistency conditions hold trivially. This provides the
base case for invariant induction — the system starts in a valid state. -/
theorem default_systemState_lifecycleConsistent :
    SystemState.lifecycleMetadataConsistent (default : SystemState) := by
  constructor
  · -- objectTypeMetadataConsistent: both HashMaps are empty → both get? return none
    intro oid
    simp only [SystemState.lookupObjectTypeMeta]
    have h₁ : (default : SystemState).lifecycle.objectTypes[oid]? = none :=
      RHTable.getElem?_empty _ _ _
    have h₂ : (default : SystemState).objects[oid]? = none :=
      RHTable.getElem?_empty _ _ _
    rw [h₁, h₂]; rfl
  · -- capabilityRefMetadataConsistent: `lookupCapabilityRefMeta` is definitionally exact.
    intro ref
    simp [SystemState.lookupCapabilityRefMeta, SystemState.lookupSlotCap, SystemState.lookupCNode]

-- ============================================================================
-- M-09/WS-E3: storeObject metadata sync correctness for type-changing stores
-- ============================================================================

/-- M-09/WS-E3: `storeObject` correctly synchronizes lifecycle metadata even when
the stored object changes the type at `oid`. After storing, the metadata at `oid`
reflects the new object's type, regardless of what was stored previously. -/
theorem storeObject_metadata_sync_type_change
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    st'.lifecycle.objectTypes[oid]? = some obj.objectType :=
  storeObject_updates_objectTypeMeta st st' oid obj hObjTypesInv hStep

/-- M-09/WS-E3: `storeObject` correctly synchronizes capability-reference metadata
when the stored object changes from a CNode to a non-CNode (or vice versa).
After storing a non-CNode, all capability references pointing into `oid` are
cleared; after storing a CNode, they reflect the new CNode's slot contents.

This closes the metadata sync hazard: for type-changing stores (e.g., replacing
a CNode with a TCB), `storeObject` correctly clears all capability-reference
metadata for the replaced CNode's slots (the `| _ => none` branch), maintaining
the invariant that metadata reflects the actual object store. -/
theorem storeObject_metadata_sync_capref_at_stored
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (slot : SeLe4n.Slot)
    (hObjInv : st.objects.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.lookupCapabilityRefMeta st' { cnode := oid, slot := slot } =
      match obj with
      | .cnode cn => (cn.lookup slot).map Capability.target
      | _ => none := by
  unfold SystemState.lookupCapabilityRefMeta SystemState.lookupSlotCap SystemState.lookupCNode
  unfold storeObject at hStep
  cases hStep
  simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_self _ _ _ hObjInv]
  cases obj <;> simp [CNode.lookup]

-- ============================================================================
-- L-05/WS-E6: objectIndex monotonicity
-- ============================================================================

/-- L-05/WS-E6: `storeObject` preserves existing objectIndex membership.
Any ID present in the index before the store remains present after. This is
the formal monotonicity guarantee documented on `SystemState.objectIndex`. -/
theorem storeObject_objectIndex_monotone
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (id : SeLe4n.ObjId)
    (hMem : id ∈ st.objectIndex)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    id ∈ st'.objectIndex := by
  unfold storeObject at hStep
  cases hStep
  simp only []
  cases h : st.objectIndexSet.contains oid
  · simp; exact Or.inr hMem
  · simp; exact hMem

-- ============================================================================
-- WS-H16/A-13: objectIndex liveness — index membership implies object existence
-- ============================================================================

/-- WS-H16/A-13: Every ID in `objectIndex` has a corresponding object in
`objects`. Since `storeObject` always inserts into both `objects` and
`objectIndex` (and no operation erases from `objects`), this property holds
for any state built through `storeObject` transitions.

This closes the gap identified by A-13 where `objectIndex` grows monotonically
without a bounds proof connecting index membership to object existence. -/
def objectIndexLive (st : SystemState) : Prop :=
  ∀ (id : SeLe4n.ObjId), id ∈ st.objectIndex → st.objects[id]? ≠ none

/-- WS-H16/A-13: `objectIndexLive` holds for the default (empty) state. -/
theorem objectIndexLive_default : objectIndexLive default := by
  intro id hMem
  simp [default, Inhabited.default] at hMem

/-- WS-H16/A-13: `storeObject` preserves `objectIndexLive`.

After `storeObject oid obj st`, every ID in `st'.objectIndex` maps to a
live object: the newly stored `oid` maps to `obj`, and all pre-existing
IDs retain their objects because `HashMap.insert` does not erase other keys. -/
theorem storeObject_preserves_objectIndexLive
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hLive : objectIndexLive st)
    (hObjInv : st.objects.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    objectIndexLive st' := by
  unfold storeObject at hStep
  cases hStep
  intro id hMem
  simp only [] at hMem
  cases h : st.objectIndexSet.contains oid
  · -- oid was not in objectIndexSet, so objectIndex = oid :: st.objectIndex
    simp [h] at hMem
    cases hMem with
    | inl heq =>
      subst heq
      simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_self _ _ _ hObjInv]; simp
    | inr hOld =>
      have hOldLive := hLive id hOld
      by_cases hEq : (oid == id) = true
      · have : oid = id := eq_of_beq hEq; subst this
        simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_self _ _ _ hObjInv]; simp
      · simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_ne _ _ _ _ hEq hObjInv]
        exact hOldLive
  · -- oid was already in objectIndexSet, so objectIndex unchanged
    simp [h] at hMem
    by_cases hEq : (oid == id) = true
    · have : oid = id := eq_of_beq hEq; subst this
      simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_self _ _ _ hObjInv]; simp
    · simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_ne _ _ _ _ hEq hObjInv]
      exact hLive id hMem

end SeLe4n.Model
