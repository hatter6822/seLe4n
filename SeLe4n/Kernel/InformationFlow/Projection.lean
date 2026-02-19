import SeLe4n.Kernel.InformationFlow.Policy

/-!
WS-C3 proof-surface note:

Determinism of pure Lean definitions is a meta-property, so tautological equalities
such as `f x = f x` do not constitute security evidence.
Tracked replacement obligations for the information-flow projection surface live in
TPI-002 (`docs/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Observer descriptor for IF-M1 projections. -/
structure IfObserver where
  clearance : SecurityLabel
  deriving Repr, DecidableEq

/-- Projection result used by IF-M1 low-equivalence statements. -/
structure ObservableState where
  objects : SeLe4n.ObjId → Option KernelObject
  runnable : List SeLe4n.ThreadId
  current : Option SeLe4n.ThreadId
  services : ServiceId → Option ServiceStatus

/-- Object observability gate under a labeling context. -/
def objectObservable (ctx : LabelingContext) (observer : IfObserver) (oid : SeLe4n.ObjId) : Bool :=
  securityFlowsTo (ctx.objectLabelOf oid) observer.clearance

/-- Thread observability gate under a labeling context. -/
def threadObservable (ctx : LabelingContext) (observer : IfObserver) (tid : SeLe4n.ThreadId) : Bool :=
  securityFlowsTo (ctx.threadLabelOf tid) observer.clearance

/-- Service projection keeps only status because service identity is carried by `ServiceId`. -/
def projectServiceStatus (st : SystemState) : ServiceId → Option ServiceStatus :=
  fun sid => (lookupService st sid).map ServiceGraphEntry.status

/-- Project object store to observer-visible subset. -/
def projectObjects (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    SeLe4n.ObjId → Option KernelObject :=
  fun oid =>
    if objectObservable ctx observer oid then
      st.objects oid
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

/-- Canonical IF-M1 state projection helper used by theorem targets. -/
def projectState (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) : ObservableState :=
  {
    objects := projectObjects ctx observer st
    runnable := projectRunnable ctx observer st
    current := projectCurrent ctx observer st
    services := projectServiceStatus st
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
