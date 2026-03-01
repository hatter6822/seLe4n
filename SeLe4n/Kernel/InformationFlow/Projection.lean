import SeLe4n.Kernel.InformationFlow.Policy

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
to cover all security-relevant scheduler, interrupt, and identity fields. -/
structure ObservableState where
  objects : SeLe4n.ObjId → Option KernelObject
  runnable : List SeLe4n.ThreadId
  current : Option SeLe4n.ThreadId
  services : ServiceId → Option ServiceStatus
  /-- WS-F3: Active scheduling domain — visible to all observers (scheduling
      transparency: all threads need to know which domain is active). -/
  activeDomain : SeLe4n.DomainId
  /-- WS-F3: IRQ handler mappings filtered to only those targeting observable
      notification objects. Prevents leaking high-domain IRQ routing. -/
  irqHandlers : SeLe4n.Irq → Option SeLe4n.ObjId
  /-- WS-F3: Object index filtered to observable IDs. Prevents leaking the
      existence of high-domain objects through the identity registry. -/
  objectIndex : List SeLe4n.ObjId

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
by the given observer. All other object types pass through unchanged. -/
def projectKernelObject (ctx : LabelingContext) (observer : IfObserver) (obj : KernelObject) : KernelObject :=
  match obj with
  | .cnode cn =>
      .cnode { cn with slots := cn.slots.filter (fun (_, cap) =>
        capTargetObservable ctx observer cap.target) }
  | other => other

/-- WS-F3/F-22: `projectKernelObject` is idempotent — filtering twice yields the
same result as filtering once. -/
theorem projectKernelObject_idempotent
    (ctx : LabelingContext) (observer : IfObserver) (obj : KernelObject) :
    projectKernelObject ctx observer (projectKernelObject ctx observer obj) =
      projectKernelObject ctx observer obj := by
  cases obj with
  | cnode cn =>
    simp only [projectKernelObject]
    simp only [List.filter_filter, Bool.and_self]
  | _ => rfl

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
    match st.irqHandlers irq with
    | some oid => if objectObservable ctx observer oid then some oid else none
    | none => none

/-- WS-F3: Project object index, filtering to only observable object IDs. -/
def projectObjectIndex (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    List SeLe4n.ObjId :=
  st.objectIndex.filter (objectObservable ctx observer)

/-- Canonical IF-M1 state projection helper used by theorem targets.

WS-F3/CRIT-02: Extended with activeDomain, irqHandlers, and objectIndex
projections for complete security-relevant state coverage. -/
def projectState (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) : ObservableState :=
  {
    objects := projectObjects ctx observer st
    runnable := projectRunnable ctx observer st
    current := projectCurrent ctx observer st
    services := projectServiceStatus ctx observer st
    activeDomain := projectActiveDomain ctx observer st
    irqHandlers := projectIrqHandlers ctx observer st
    objectIndex := projectObjectIndex ctx observer st
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
