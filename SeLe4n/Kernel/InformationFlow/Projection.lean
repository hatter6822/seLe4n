/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.Policy
import Std.Data.HashSet

/-!
WS-C3 proof-surface note:

Determinism of pure Lean definitions is a meta-property, so tautological equalities
such as `f x = f x` do not constitute security evidence.
Tracked replacement obligations for the information-flow projection surface live in
TPI-002 (`docs/dev_history/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Observer descriptor for IF-M1 projections. -/
structure IfObserver where
  clearance : SecurityLabel
  deriving Repr, DecidableEq

/-- Projection result used by IF-M1 low-equivalence statements.

WS-F3/CRIT-02: Extended with `activeDomain`, `irqHandlers`, and `objectIndex`
to cover all security-relevant scheduler, interrupt, and identity fields.

WS-H8/A-36/H-11: Extended with `domainTimeRemaining`, `domainSchedule`, and
`domainScheduleIndex` to prevent timing-channel attacks via domain scheduling
metadata. All three are visible under scheduling transparency (same rationale
as `activeDomain`).

WS-H10/C-05/A-38: Extended with `machineRegs` (domain-gated register file
projection). Machine timer is deliberately excluded — it is a kernel-internal
monotonic counter; projecting it unconditionally would create a covert timing
channel. Memory projection deferred to WS-H11 (VSpace domain ownership). -/
structure ObservableState where
  objects : SeLe4n.ObjId → Option KernelObject
  runnable : List SeLe4n.ThreadId
  current : Option SeLe4n.ThreadId
  services : ServiceId → Option ServiceStatus
  /-- WS-F3: Active scheduling domain — visible to all observers (scheduling
      transparency: all threads need to know which domain is active).
      WS-H8/A-36: Documented as deliberate security assumption — scheduling
      transparency requires all threads to observe the active domain for
      deterministic scheduling behavior. This matches seL4's domain scheduler
      design where domain identity is not a secret. -/
  activeDomain : SeLe4n.DomainId
  /-- WS-F3: IRQ handler mappings filtered to only those targeting observable
      notification objects. Prevents leaking high-domain IRQ routing. -/
  irqHandlers : SeLe4n.Irq → Option SeLe4n.ObjId
  /-- WS-F3: Object index filtered to observable IDs. Prevents leaking the
      existence of high-domain objects through the identity registry. -/
  objectIndex : List SeLe4n.ObjId
  /-- WS-H8/A-36/H-11: Remaining ticks in current domain schedule entry.
      Visible under scheduling transparency — allows NI proofs to cover
      domain timing state, preventing timing-channel information leaks. -/
  domainTimeRemaining : Nat
  /-- WS-H8/A-36/H-11: Domain schedule table. Visible under scheduling
      transparency — the schedule is system-wide configuration, not per-domain
      secret state. -/
  domainSchedule : List DomainScheduleEntry
  /-- WS-H8/A-36/H-11: Current index into domain schedule. Visible under
      scheduling transparency. -/
  domainScheduleIndex : Nat
  /-- WS-H10/C-05/A-38: Machine register file, filtered by current thread
      observability. The register file represents the currently-executing
      thread's architectural context. Visible only when the current thread
      is observable to the observer; `none` otherwise.
      Note: Memory projection (`Memory = PAddr → UInt8`) is deferred to
      WS-H11 (VSpace domain ownership model required for meaningful per-domain
      memory partitioning in the abstract model). -/
  machineRegs : Option RegisterFile
  /-- WS-I2/R-16: Optional memory projection, filtered by domain ownership.
      When `ctx.memoryOwnership = none`, this projection is empty (`none` at
      all addresses) for backward compatibility. -/
  memory : SeLe4n.PAddr → Option UInt8

/-- Object observability gate under a labeling context. -/
def objectObservable (ctx : LabelingContext) (observer : IfObserver) (oid : SeLe4n.ObjId) : Bool :=
  securityFlowsTo (ctx.objectLabelOf oid) observer.clearance

/-- Thread observability gate under a labeling context. -/
def threadObservable (ctx : LabelingContext) (observer : IfObserver) (tid : SeLe4n.ThreadId) : Bool :=
  securityFlowsTo (ctx.threadLabelOf tid) observer.clearance

/-- Service projection keeps only status because service identity is carried by `ServiceId`. -/
def serviceObservable (ctx : LabelingContext) (observer : IfObserver) (sid : ServiceId) : Bool :=
  securityFlowsTo (ctx.serviceLabelOf sid) observer.clearance

/-- Service projection keeps only observer-visible statuses keyed by `ServiceId`. -/
def projectServiceStatus (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    ServiceId → Option ServiceStatus :=
  fun sid =>
    if serviceObservable ctx observer sid then
      (lookupService st sid).map ServiceGraphEntry.status
    else
      none

-- ============================================================================
-- WS-F3/F-22: CNode slot filtering to prevent capability target leakage
-- ============================================================================

/-- WS-F3/F-22: Observability gate for capability targets. A capability target
is observable iff the referenced entity is within the observer's clearance.
This prevents CNode projections from leaking the identity of high-domain
objects through capability slot contents. -/
def capTargetObservable (ctx : LabelingContext) (observer : IfObserver) (target : CapTarget) : Bool :=
  match target with
  | .object oid => objectObservable ctx observer oid
  | .cnodeSlot cnode _ => objectObservable ctx observer cnode
  | .replyCap tid => threadObservable ctx observer tid

/-- WS-F3/F-22: Filter a KernelObject to redact high-domain information.
For CNode objects, removes capability slots whose targets are not observable
by the given observer. All other object types pass through unchanged.

WS-G5: Uses `HashMap.filter` for O(m) filtering on HashMap-backed CNode slots. -/
def projectKernelObject (ctx : LabelingContext) (observer : IfObserver) (obj : KernelObject) : KernelObject :=
  match obj with
  | .cnode cn =>
      .cnode { cn with slots := cn.slots.filter (fun _ cap =>
        capTargetObservable ctx observer cap.target) }
  | .tcb tcb =>
      -- WS-H12c: Strip registerContext from projected TCBs. Register context
      -- is saved/restored by schedule's inline context switch and is an
      -- implementation detail of the scheduler, not a security-relevant
      -- kernel object property. Projecting it away ensures that
      -- saveOutgoingContext/restoreIncomingContext do not affect the
      -- information-flow projection.
      .tcb { tcb with registerContext := default }
  | other => other

/-- WS-F3/F-22: `projectKernelObject` is idempotent — filtering twice yields
observationally equivalent results to filtering once.

WS-G5: With HashMap-backed CNode slots, idempotency is stated at the slot
lookup level rather than structural equality, because `Std.HashMap.filter`
in Lean 4.28.0 reverses internal `AssocList` bucket ordering, making
`(m.filter f).filter f ≠ m.filter f` structurally despite identical entries.
For all non-CNode variants, structural equality holds directly. -/
theorem projectKernelObject_idempotent
    (ctx : LabelingContext) (observer : IfObserver) (obj : KernelObject)
    (slot : SeLe4n.Slot) :
    match projectKernelObject ctx observer (projectKernelObject ctx observer obj),
          projectKernelObject ctx observer obj with
    | .cnode cn1, .cnode cn2 => cn1.lookup slot = cn2.lookup slot
    | _, _ => True := by
  cases obj with
  | cnode cn =>
    simp only [projectKernelObject, CNode.lookup]
    exact SeLe4n.HashMap_filter_filter_getElem? cn.slots _ slot
  | _ => trivial

/-- WS-F3/F-22: `projectKernelObject` preserves object type. -/
theorem projectKernelObject_objectType
    (ctx : LabelingContext) (observer : IfObserver) (obj : KernelObject) :
    (projectKernelObject ctx observer obj).objectType = obj.objectType := by
  cases obj <;> rfl

/-- Project object store to observer-visible subset.

WS-F3/F-22: Objects are now filtered through `projectKernelObject` to redact
CNode slot contents that reference high-domain targets. -/
def projectObjects (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    SeLe4n.ObjId → Option KernelObject :=
  fun oid =>
    if objectObservable ctx observer oid then
      (st.objects[oid]?).map (projectKernelObject ctx observer)
    else
      none

/-- Project runnable queue to observer-visible threads only. -/
def projectRunnable (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    List SeLe4n.ThreadId :=
  st.scheduler.runnable.filter (threadObservable ctx observer)

/-- Project current thread to observer-visible identity. -/
def projectCurrent (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    Option SeLe4n.ThreadId :=
  match st.scheduler.current with
  | some tid => if threadObservable ctx observer tid then some tid else none
  | none => none

/-- WS-F3: Project active scheduling domain (always visible — scheduling transparency). -/
def projectActiveDomain (_ctx : LabelingContext) (_observer : IfObserver) (st : SystemState) :
    SeLe4n.DomainId :=
  st.scheduler.activeDomain

/-- WS-F3: Project IRQ handler mappings, filtering to only those whose target
notification object is observable by the observer. -/
def projectIrqHandlers (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    SeLe4n.Irq → Option SeLe4n.ObjId :=
  fun irq =>
    match st.irqHandlers[irq]? with
    | some oid => if objectObservable ctx observer oid then some oid else none
    | none => none

/-- WS-F3: Project object index, filtering to only observable object IDs. -/
def projectObjectIndex (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    List SeLe4n.ObjId :=
  st.objectIndex.filter (objectObservable ctx observer)

/-- WS-H8/A-36: Project domain time remaining (scheduling transparency — always visible). -/
def projectDomainTimeRemaining (_ctx : LabelingContext) (_observer : IfObserver) (st : SystemState) :
    Nat :=
  st.scheduler.domainTimeRemaining

/-- WS-H8/A-36: Project domain schedule (scheduling transparency — always visible). -/
def projectDomainSchedule (_ctx : LabelingContext) (_observer : IfObserver) (st : SystemState) :
    List DomainScheduleEntry :=
  st.scheduler.domainSchedule

/-- WS-H8/A-36: Project domain schedule index (scheduling transparency — always visible). -/
def projectDomainScheduleIndex (_ctx : LabelingContext) (_observer : IfObserver) (st : SystemState) :
    Nat :=
  st.scheduler.domainScheduleIndex

/-- WS-H10/C-05 + WS-H12c/H-03: Project machine register file, filtered by
current thread observability. The register file is the architectural context
of the currently-executing thread. Only visible when the current thread is
observable.

Under `contextMatchesCurrent` (established by `schedule`), the machine
register file is guaranteed to equal `currentThread.registerContext` when
a thread is dispatched. The projection reads `st.machine.regs` which is
synchronized with the current TCB's `registerContext` by the inline
context switch in `schedule`. -/
def projectMachineRegs (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    Option RegisterFile :=
  match st.scheduler.current with
  | some tid => if threadObservable ctx observer tid then some st.machine.regs else none
  | none => none

/-- WS-I2/R-16: Project machine memory using optional ownership metadata.
When no ownership model is configured, memory is not observable. -/
def projectMemory (_ctx : LabelingContext) (_observer : IfObserver) (_st : SystemState) :
    SeLe4n.PAddr → Option UInt8 :=
  fun _ => none

@[simp] theorem projectMemory_state_irrelevant
    (ctx : LabelingContext) (observer : IfObserver) (s₁ s₂ : SystemState) :
    projectMemory ctx observer s₁ = projectMemory ctx observer s₂ := by
  funext _
  rfl

/-- Canonical IF-M1 state projection helper used by theorem targets.

WS-F3/CRIT-02: Extended with activeDomain, irqHandlers, and objectIndex
projections for complete security-relevant state coverage.

WS-H8/A-36/H-11: Extended with domainTimeRemaining, domainSchedule, and
domainScheduleIndex projections for timing-channel coverage.

WS-H10/C-05/A-38: Extended with machineRegs projection for MachineState
coverage. Machine timer is excluded from ObservableState because it is a
kernel-internal monotonic counter — projecting it unconditionally would
create a covert timing channel (observers could infer other domains'
execution by watching timer increments). Memory projection deferred to
WS-H11 (VSpace domain ownership model required). -/
def projectState (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) : ObservableState :=
  {
    objects := projectObjects ctx observer st
    runnable := projectRunnable ctx observer st
    current := projectCurrent ctx observer st
    services := projectServiceStatus ctx observer st
    activeDomain := projectActiveDomain ctx observer st
    irqHandlers := projectIrqHandlers ctx observer st
    objectIndex := projectObjectIndex ctx observer st
    domainTimeRemaining := projectDomainTimeRemaining ctx observer st
    domainSchedule := projectDomainSchedule ctx observer st
    domainScheduleIndex := projectDomainScheduleIndex ctx observer st
    machineRegs := projectMachineRegs ctx observer st
    memory := projectMemory ctx observer st
  }

-- ============================================================================
-- WS-G9/F-P09: Precomputed observable-object set and optimized projections
-- ============================================================================

/-- WS-G9/F-P09: Precompute the set of all observable object IDs.

Evaluates `objectObservable` exactly once per object in the index, building a
`Std.HashSet ObjId` for O(1) subsequent lookups. This eliminates redundant
`securityFlowsTo` evaluations across `projectObjects`, `projectIrqHandlers`,
`projectObjectIndex`, and `capTargetObservable` within a single `projectState`
call. -/
@[inline] def computeObservableSet (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) : Std.HashSet SeLe4n.ObjId :=
  st.objectIndex.foldl (fun acc oid =>
    if objectObservable ctx observer oid then acc.insert oid else acc) {}

/-- WS-G9: Core induction lemma for the observable set foldl. For any list `xs`,
accumulator `s`, and element `a ∈ xs`: the result of the fold contains `a`
iff `objectObservable ctx observer a = true` OR `s` already contained `a`. -/
private theorem foldl_observable_set_mem
    (ctx : LabelingContext) (observer : IfObserver)
    (xs : List SeLe4n.ObjId) (s : Std.HashSet SeLe4n.ObjId) (a : SeLe4n.ObjId)
    (hMem : a ∈ xs) :
    (xs.foldl (fun acc oid =>
        if objectObservable ctx observer oid then acc.insert oid else acc) s).contains a =
      (objectObservable ctx observer a || s.contains a) := by
  induction xs generalizing s with
  | nil => nomatch hMem
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases hEq : a = x
    · -- a = x: the head element
      subst hEq
      cases hObs : objectObservable ctx observer a with
      | true =>
        -- a is observable → inserted → stays in set through rest of fold
        show (xs.foldl _ (s.insert a)).contains a = _
        simp only [Bool.true_or]
        exact List.foldl_preserves_contains _ _ _ (Std.HashSet.contains_insert_self ..)
      | false =>
        -- a is not observable → skipped → stays at s.contains a via pred_false lemma
        show (xs.foldl _ s).contains a = _
        simp only [Bool.false_or]
        exact List.foldl_preserves_when_pred_false _ _ _ hObs
    · -- a ≠ x: a must be in xs
      have hInXs : a ∈ xs := List.mem_of_ne_of_mem hEq hMem
      cases hObs : objectObservable ctx observer x with
      | true =>
        show (xs.foldl _ (s.insert x)).contains a = _
        rw [ih (s.insert x) hInXs, Std.HashSet.contains_insert]
        have hBeq : (x == a) = false := beq_false_of_ne (Ne.symm hEq)
        simp [hBeq]
      | false =>
        show (xs.foldl _ s).contains a = _
        exact ih s hInXs

/-- WS-G9: Membership in the precomputed set is equivalent to the original
`objectObservable` gate for any ObjId that appears in the objectIndex. -/
theorem computeObservableSet_mem
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (oid : SeLe4n.ObjId)
    (hMem : oid ∈ st.objectIndex) :
    (computeObservableSet ctx observer st).contains oid =
      objectObservable ctx observer oid := by
  unfold computeObservableSet
  rw [foldl_observable_set_mem ctx observer st.objectIndex {} oid hMem]
  simp only [SeLe4n.HashSet_contains_empty, Bool.or_false]

/-- WS-G9: An element not in the objectIndex is not in the observable set. -/
theorem computeObservableSet_not_mem
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (oid : SeLe4n.ObjId)
    (hNotMem : oid ∉ st.objectIndex) :
    (computeObservableSet ctx observer st).contains oid = false := by
  unfold computeObservableSet
  rw [List.foldl_not_contains_when_absent (objectObservable ctx observer)
      st.objectIndex {} hNotMem]
  exact SeLe4n.HashSet_contains_empty

/-- WS-G9: Optimized object projection using precomputed observable set.
Replaces per-object `objectObservable` evaluation with O(1) `HashSet.contains`. -/
def projectObjectsFast (ctx : LabelingContext) (observer : IfObserver)
    (observableOids : Std.HashSet SeLe4n.ObjId) (st : SystemState) :
    SeLe4n.ObjId → Option KernelObject :=
  fun oid =>
    if observableOids.contains oid then
      (st.objects[oid]?).map (projectKernelObject ctx observer)
    else
      none

/-- WS-G9: Optimized IRQ handler projection using precomputed observable set. -/
def projectIrqHandlersFast (observableOids : Std.HashSet SeLe4n.ObjId)
    (st : SystemState) : SeLe4n.Irq → Option SeLe4n.ObjId :=
  fun irq =>
    match st.irqHandlers[irq]? with
    | some oid => if observableOids.contains oid then some oid else none
    | none => none

/-- WS-G9: Optimized object index projection using precomputed observable set. -/
def projectObjectIndexFast (observableOids : Std.HashSet SeLe4n.ObjId)
    (st : SystemState) : List SeLe4n.ObjId :=
  st.objectIndex.filter (observableOids.contains ·)

/-- WS-G9/F-P09: Optimized state projection that precomputes the observable set
once, then uses O(1) `HashSet.contains` for all observability checks in the
three sub-projections that gate on `objectObservable`: `projectObjects`,
`projectIrqHandlers`, and `projectObjectIndex`.

This is the runtime-fast equivalent of `projectState`. The equivalence theorem
`projectStateFast_eq` proves identical output under standard state synchronization
invariants, making this suitable for `@[csimp]` compiler substitution once the
preconditions are discharged at the call site.

**Design note:** `projectKernelObject` (CNode slot filtering via `capTargetObservable`)
is intentionally left unchanged. Capability targets may reference ObjIds not in
`st.objectIndex` (e.g., stale/dangling references), so substituting
`observableOids.contains` for `objectObservable` inside `capTargetObservable` would
change filtering semantics without an additional "all capability targets are indexed"
invariant. The primary F-P09 concern (redundant `objectObservable` across three
top-level sub-projections) is fully resolved. -/
def projectStateFast (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) : ObservableState :=
  let observableOids := computeObservableSet ctx observer st
  {
    objects := projectObjectsFast ctx observer observableOids st
    runnable := projectRunnable ctx observer st
    current := projectCurrent ctx observer st
    services := projectServiceStatus ctx observer st
    activeDomain := projectActiveDomain ctx observer st
    irqHandlers := projectIrqHandlersFast observableOids st
    objectIndex := projectObjectIndexFast observableOids st
    domainTimeRemaining := projectDomainTimeRemaining ctx observer st
    domainSchedule := projectDomainSchedule ctx observer st
    domainScheduleIndex := projectDomainScheduleIndex ctx observer st
    machineRegs := projectMachineRegs ctx observer st
    memory := projectMemory ctx observer st
  }

/-- WS-G9: `projectObjectsFast` with the precomputed set agrees with `projectObjects`
for states where all stored objects are in the objectIndex. -/
private theorem projectObjectsFast_eq
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (hSync : ∀ oid, st.objects[oid]? ≠ none → oid ∈ st.objectIndex) :
    projectObjectsFast ctx observer (computeObservableSet ctx observer st) st =
      projectObjects ctx observer st := by
  funext oid
  unfold projectObjectsFast projectObjects
  by_cases hIdx : oid ∈ st.objectIndex
  · rw [computeObservableSet_mem ctx observer st oid hIdx]
  · have hNone : st.objects[oid]? = none := by
      cases h : st.objects[oid]? with
      | none => rfl
      | some _ => exact absurd (hSync oid (by simp [h])) hIdx
    rw [computeObservableSet_not_mem ctx observer st oid hIdx, hNone]
    simp

/-- WS-G9: `projectIrqHandlersFast` agrees with `projectIrqHandlers` when all
IRQ handler targets are in the objectIndex. -/
private theorem projectIrqHandlersFast_eq
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (hIrqInIdx : ∀ (irq : SeLe4n.Irq) (oid : SeLe4n.ObjId), st.irqHandlers[irq]? = some oid → oid ∈ st.objectIndex) :
    projectIrqHandlersFast (computeObservableSet ctx observer st) st =
      projectIrqHandlers ctx observer st := by
  funext irq
  unfold projectIrqHandlersFast projectIrqHandlers
  cases hIrq : st.irqHandlers[irq]? with
  | none => rfl
  | some oid =>
    show (if (computeObservableSet ctx observer st).contains oid then some oid else none) =
         (if objectObservable ctx observer oid then some oid else none)
    rw [computeObservableSet_mem ctx observer st oid (hIrqInIdx irq oid hIrq)]

/-- WS-G9: `projectObjectIndexFast` agrees with `projectObjectIndex`.
Both filter `st.objectIndex` by the same effective predicate. -/
private theorem projectObjectIndexFast_eq
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    projectObjectIndexFast (computeObservableSet ctx observer st) st =
      projectObjectIndex ctx observer st := by
  unfold projectObjectIndexFast projectObjectIndex
  apply List.filter_congr
  intro oid hMem
  exact computeObservableSet_mem ctx observer st oid hMem

/-- WS-G9/F-P09: `projectStateFast` and `projectState` produce identical results
for well-formed states where all stored objects appear in the objectIndex and
all IRQ handler targets appear in the objectIndex.

These invariants hold for any state reachable from `default` via `storeObject`
(which maintains both `objectIndex` and `objectIndexSet` in sync). -/
theorem projectStateFast_eq
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (hObjSync : ∀ oid, st.objects[oid]? ≠ none → oid ∈ st.objectIndex)
    (hIrqSync : ∀ (irq : SeLe4n.Irq) (oid : SeLe4n.ObjId), st.irqHandlers[irq]? = some oid → oid ∈ st.objectIndex) :
    projectStateFast ctx observer st = projectState ctx observer st := by
  simp only [projectStateFast, projectState]
  congr 1
  · exact projectObjectsFast_eq ctx observer st hObjSync
  · exact projectIrqHandlersFast_eq ctx observer st hIrqSync
  · exact projectObjectIndexFast_eq ctx observer st

/-- Two states are low-equivalent when their observer projections are equal. -/
def lowEquivalent (ctx : LabelingContext) (observer : IfObserver) (s₁ s₂ : SystemState) : Prop :=
  projectState ctx observer s₁ = projectState ctx observer s₂

theorem lowEquivalent_refl
    (ctx : LabelingContext)
    (observer : IfObserver)
    (st : SystemState) :
    lowEquivalent ctx observer st st := by
  rfl

theorem lowEquivalent_symm
    (ctx : LabelingContext)
    (observer : IfObserver)
    (s₁ s₂ : SystemState)
    (hEq : lowEquivalent ctx observer s₁ s₂) :
    lowEquivalent ctx observer s₂ s₁ := by
  simpa [lowEquivalent] using Eq.symm hEq

theorem lowEquivalent_trans
    (ctx : LabelingContext)
    (observer : IfObserver)
    (s₁ s₂ s₃ : SystemState)
    (h₁₂ : lowEquivalent ctx observer s₁ s₂)
    (h₂₃ : lowEquivalent ctx observer s₂ s₃) :
    lowEquivalent ctx observer s₁ s₃ := by
  simpa [lowEquivalent] using Eq.trans h₁₂ h₂₃

end SeLe4n.Kernel
