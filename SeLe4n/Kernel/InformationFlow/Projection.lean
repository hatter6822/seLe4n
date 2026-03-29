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
  services : ServiceId → Bool
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
  /-- V6-E (M-IF-3): Service registry state projection. Projects the full
      `ServiceGraphEntry` (identity, dependencies, isolation edges) for each
      observable service, filtered by `serviceObservable`. This extends the
      prior `services : ServiceId → Bool` presence-only projection with
      structural visibility into the service dependency graph.

      Non-observable services return `none`, preventing information leakage
      about high-domain service topology. -/
  serviceRegistry : ServiceId → Option ServiceGraphEntry

/-- Object observability gate under a labeling context. -/
def objectObservable (ctx : LabelingContext) (observer : IfObserver) (oid : SeLe4n.ObjId) : Bool :=
  securityFlowsTo (ctx.objectLabelOf oid) observer.clearance

/-- Thread observability gate under a labeling context. -/
def threadObservable (ctx : LabelingContext) (observer : IfObserver) (tid : SeLe4n.ThreadId) : Bool :=
  securityFlowsTo (ctx.threadLabelOf tid) observer.clearance

/-- Service projection gate: a service is observable iff its label flows to the observer.

    U6-J (U-M24): **NI projection coverage gap**. The service registry is
    visible to the NI projection model only through `projectServicePresence`
    (see below), which projects a boolean presence/absence indicator per
    service ID. However, the service orchestration layer's internal state
    (dependency graphs, lifecycle transitions, restart policies) is *not*
    captured by the projection model. This means:

    1. Service-layer information flows (e.g., one service observing another's
       restart behavior) are not covered by non-interference proofs.
    2. The NI theorems in `Invariant/Composition.lean` apply only to kernel
       primitives (IPC, scheduling, capability operations), not to service
       orchestration.
    3. Service-layer information flows must be analyzed separately — either
       by extending the projection model to include service graph state, or
       by treating the service layer as a trusted component outside the NI
       boundary.

    This is a known limitation documented here for auditor awareness. -/
def serviceObservable (ctx : LabelingContext) (observer : IfObserver) (sid : ServiceId) : Bool :=
  securityFlowsTo (ctx.serviceLabelOf sid) observer.clearance

/-- WS-Q1-E2: Service projection returns whether an observable service is registered.
Replaces the old `projectServiceStatus` that projected `ServiceStatus`. -/
def projectServicePresence (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    ServiceId → Bool :=
  fun sid =>
    if serviceObservable ctx observer sid then
      (lookupService st sid).isSome
    else
      false

/-- V6-E (M-IF-3): Project service registry graph entries for observable services.

    Extends the boolean presence projection (`projectServicePresence`) with
    full `ServiceGraphEntry` visibility. For observable services, returns the
    entry (identity, dependencies, isolation edges); for non-observable services,
    returns `none`.

    **Dependency filtering**: Dependencies referencing non-observable services
    are preserved in the projection (the dependency *exists* but its target
    may be opaque). This is deliberate — the dependency graph structure of
    observable services is itself observable information. -/
def projectServiceRegistry (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    ServiceId → Option ServiceGraphEntry :=
  fun sid =>
    if serviceObservable ctx observer sid then
      lookupService st sid
    else
      none

/-- V6-E: `projectServiceRegistry` agrees with `projectServicePresence` on
    presence: if the registry projection returns `some`, then presence is `true`,
    and if it returns `none`, presence is `false` (when the service is observable). -/
theorem projectServiceRegistry_consistent_with_presence
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (sid : ServiceId) :
    (projectServiceRegistry ctx observer st sid).isSome =
      projectServicePresence ctx observer st sid := by
  simp [projectServiceRegistry, projectServicePresence]
  cases serviceObservable ctx observer sid <;> simp

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

WS-G5: With RHTable-backed CNode slots, idempotency is stated at the slot
lookup level rather than structural equality, because `RHTable.filter`
may reorder internal entries, making
`(m.filter f).filter f ≠ m.filter f` structurally despite identical entries.
For all non-CNode variants, structural equality holds directly. -/
theorem projectKernelObject_idempotent
    (ctx : LabelingContext) (observer : IfObserver) (obj : KernelObject)
    (slot : SeLe4n.Slot)
    (hUniq : ∀ cn, obj = .cnode cn → cn.slotsUnique) :
    match projectKernelObject ctx observer (projectKernelObject ctx observer obj),
          projectKernelObject ctx observer obj with
    | .cnode cn1, .cnode cn2 => cn1.lookup slot = cn2.lookup slot
    | _, _ => True := by
  cases obj with
  | cnode cn =>
    simp only [projectKernelObject, CNode.lookup]
    exact SeLe4n.Kernel.RobinHood.RHTable.filter_filter_getElem? cn.slots _ slot (hUniq cn rfl).1
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

/-- WS-I2/R-16: Address observability under optional memory-ownership metadata. -/
def memoryAddressObservable (ctx : LabelingContext) (observer : IfObserver)
    (paddr : SeLe4n.PAddr) : Bool :=
  match ctx.memoryOwnership with
  | none => false
  | some ownership =>
      match ownership.regionOwner paddr with
      | none => false
      | some dom => securityFlowsTo (ownership.domainLabelOf dom) observer.clearance

/-- R5-C.1/M-03: Project machine memory using actual content lookup.

When a memory address is observable (domain ownership model assigns it to a
domain that flows to the observer), the projection returns the actual byte
value from `st.machine.memory`. When no ownership model is configured
(`ctx.memoryOwnership = none`), `memoryAddressObservable` returns `false` for
all addresses, preserving backward compatibility.

This replaces the prior dummy-byte projection (`some 0`) that was flagged in
audit finding M-03 as failing to verify content isolation. -/
def projectMemory (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    SeLe4n.PAddr → Option UInt8 :=
  fun paddr => if memoryAddressObservable ctx observer paddr then some (st.machine.memory paddr) else none

/-- R5-C.1: When no memory ownership model is configured, projectMemory returns
none for all addresses regardless of state, preserving state-irrelevance. -/
theorem projectMemory_no_ownership
    (ctx : LabelingContext) (observer : IfObserver)
    (hNone : ctx.memoryOwnership = none) (s₁ s₂ : SystemState) :
    projectMemory ctx observer s₁ = projectMemory ctx observer s₂ := by
  funext paddr
  simp only [projectMemory, memoryAddressObservable, hNone]
  rfl

/-- R5-C.1: When memory is unmodified between two states, projectMemory agrees. -/
theorem projectMemory_eq_of_memory_eq
    (ctx : LabelingContext) (observer : IfObserver) (s₁ s₂ : SystemState)
    (hMem : s₁.machine.memory = s₂.machine.memory) :
    projectMemory ctx observer s₁ = projectMemory ctx observer s₂ := by
  funext paddr
  simp only [projectMemory, hMem]

/-- V6-E: When services are unmodified between two states, projectServiceRegistry agrees. -/
theorem projectServiceRegistry_eq_of_services_eq
    (ctx : LabelingContext) (observer : IfObserver) (s₁ s₂ : SystemState)
    (hSvc : s₁.services = s₂.services) :
    projectServiceRegistry ctx observer s₁ = projectServiceRegistry ctx observer s₂ := by
  funext sid
  simp only [projectServiceRegistry, lookupService, hSvc]

/-! ### U6-K (U-M23): Accepted Covert Channels

The following covert channels are known and accepted in the seLe4n NI model:

1. **Scheduling state (domain schedule)**: `activeDomain`, `domainSchedule`,
   `domainScheduleIndex`, and `domainTimeRemaining` are visible to all
   observers under the scheduling transparency assumption. This means any
   observer can infer the global scheduling state, including which domain is
   active and how much time remains. This is a deliberate design choice
   matching seL4's domain scheduler visibility.

2. **TCB metadata (priority, IPC state)**: Thread priority and IPC state
   are visible to any observer that can observe the thread (via
   `threadObservable`). This means an observer in one domain can infer
   another domain's thread priorities if those threads are observable to it.
   In seL4, thread priority is not considered confidential — it is visible
   through capability lookup and scheduling behavior.

3. **Machine timer (excluded)**: The machine timer (`st.machine.timer`) is
   deliberately excluded from `ObservableState` to prevent a timing covert
   channel. If projected, observers could infer other domains' execution
   duration by watching timer increments.

4. **Object store metadata**: Object IDs and types are visible through
   `objectIndex` projection. An observer can determine which objects exist
   (filtered by label), which reveals the system's object population
   indirectly.

These covert channels are consistent with seL4's information flow model
(Murray et al., CCS 2013) and are documented for auditor awareness.
Mitigation requires hardware-level isolation (e.g., partitioned caches,
separate timer domains) beyond the kernel model's scope.
-/

/-- V6-J (L-IF-1): Accepted scheduling covert channel — explicit bound theorem.

    The domain scheduling state (`activeDomain`, `domainSchedule`,
    `domainScheduleIndex`, `domainTimeRemaining`) is unconditionally visible
    to ALL observers. This creates a covert channel: a high-security domain
    can influence the scheduling state observable by a low-security domain.

    **Explicit bound**: The scheduling covert channel is bounded to at most
    4 scalar values per observation (the 4 scheduling-related fields in
    `ObservableState`). The bandwidth is limited by the domain schedule
    switching frequency (typically 1-100 Hz in seL4 configurations).

    This theorem witnesses the covert channel by showing that two observers
    with different clearances see identical scheduling projections, confirming
    that scheduling state is not filtered by security labels. -/
theorem acceptedCovertChannel_scheduling
    (ctx : LabelingContext)
    (obs₁ obs₂ : IfObserver)
    (st : SystemState) :
    projectActiveDomain ctx obs₁ st = projectActiveDomain ctx obs₂ st ∧
    projectDomainTimeRemaining ctx obs₁ st = projectDomainTimeRemaining ctx obs₂ st ∧
    projectDomainSchedule ctx obs₁ st = projectDomainSchedule ctx obs₂ st ∧
    projectDomainScheduleIndex ctx obs₁ st = projectDomainScheduleIndex ctx obs₂ st := by
  exact ⟨rfl, rfl, rfl, rfl⟩

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
    services := projectServicePresence ctx observer st
    activeDomain := projectActiveDomain ctx observer st
    irqHandlers := projectIrqHandlers ctx observer st
    objectIndex := projectObjectIndex ctx observer st
    domainTimeRemaining := projectDomainTimeRemaining ctx observer st
    domainSchedule := projectDomainSchedule ctx observer st
    domainScheduleIndex := projectDomainScheduleIndex ctx observer st
    machineRegs := projectMachineRegs ctx observer st
    memory := projectMemory ctx observer st
    serviceRegistry := projectServiceRegistry ctx observer st
  }

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
