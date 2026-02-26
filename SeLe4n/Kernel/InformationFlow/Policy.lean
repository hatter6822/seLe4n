import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Confidentiality lattice for IF-M1. -/
inductive Confidentiality where
  | low
  | high
  deriving Repr, DecidableEq

/-- Integrity lattice for IF-M1. -/
inductive Integrity where
  | untrusted
  | trusted
  deriving Repr, DecidableEq

/-- Product security label carrying confidentiality and integrity dimensions. -/
structure SecurityLabel where
  confidentiality : Confidentiality
  integrity : Integrity
  deriving Repr, DecidableEq

namespace SecurityLabel

def publicLabel : SecurityLabel :=
  { confidentiality := .low, integrity := .untrusted }

def kernelTrusted : SecurityLabel :=
  { confidentiality := .high, integrity := .trusted }

end SecurityLabel

/-- Confidentiality order (`≤`) used by IF-M1 policy checks. -/
def confidentialityFlowsTo : Confidentiality → Confidentiality → Bool
  | .low, _ => true
  | .high, .high => true
  | .high, .low => false

/-- Integrity order (`≥`) for trusted-data flow checks. -/
def integrityFlowsTo : Integrity → Integrity → Bool
  | .trusted, .trusted => true
  | .trusted, .untrusted => true
  | .untrusted, .untrusted => true
  | .untrusted, .trusted => false

/-- Combined policy relation: confidentiality must not flow down; integrity
    must not flow up (source must be at least as trusted as destination).
    Note: this implements a "both dimensions flow upward" lattice — low
    confidentiality flows to high, and untrusted integrity flows to trusted
    destinations.  This is **not** standard BLP+BIBA (where BIBA would deny
    untrusted→trusted).  The reversed argument order on `integrityFlowsTo`
    checks `dst.integrity ≤ src.integrity`, i.e., the destination must not
    be more trusted than the source.  See audit finding M-13. -/
def securityFlowsTo (src dst : SecurityLabel) : Bool :=
  confidentialityFlowsTo src.confidentiality dst.confidentiality &&
    integrityFlowsTo dst.integrity src.integrity

/-- IF-M1 context: explicit label assignment entrypoints for each primary entity class. -/
structure LabelingContext where
  objectLabelOf : SeLe4n.ObjId → SecurityLabel
  threadLabelOf : SeLe4n.ThreadId → SecurityLabel
  endpointLabelOf : SeLe4n.ObjId → SecurityLabel
  serviceLabelOf : ServiceId → SecurityLabel

/-- Minimal default labeling: everything is publicly observable and untrusted. -/
def defaultLabelingContext : LabelingContext :=
  {
    objectLabelOf := fun _ => SecurityLabel.publicLabel
    threadLabelOf := fun _ => SecurityLabel.publicLabel
    endpointLabelOf := fun _ => SecurityLabel.publicLabel
    serviceLabelOf := fun _ => SecurityLabel.publicLabel
  }

theorem confidentialityFlowsTo_refl (c : Confidentiality) :
    confidentialityFlowsTo c c = true := by
  cases c <;> rfl

theorem integrityFlowsTo_refl (i : Integrity) :
    integrityFlowsTo i i = true := by
  cases i <;> rfl

theorem securityFlowsTo_refl (l : SecurityLabel) :
    securityFlowsTo l l = true := by
  cases l with
  | mk c i =>
      simp [securityFlowsTo, confidentialityFlowsTo_refl, integrityFlowsTo_refl]

theorem confidentialityFlowsTo_trans
    (a b c : Confidentiality)
    (h₁ : confidentialityFlowsTo a b = true)
    (h₂ : confidentialityFlowsTo b c = true) :
    confidentialityFlowsTo a c = true := by
  cases a <;> cases b <;> cases c <;> simp [confidentialityFlowsTo] at h₁ h₂ ⊢

theorem integrityFlowsTo_trans
    (a b c : Integrity)
    (h₁ : integrityFlowsTo a b = true)
    (h₂ : integrityFlowsTo b c = true) :
    integrityFlowsTo a c = true := by
  cases a <;> cases b <;> cases c <;> simp [integrityFlowsTo] at h₁ h₂ ⊢

theorem securityFlowsTo_trans
    (a b c : SecurityLabel)
    (h₁ : securityFlowsTo a b = true)
    (h₂ : securityFlowsTo b c = true) :
    securityFlowsTo a c = true := by
  cases a with
  | mk ac ai =>
      cases b with
      | mk bc bi =>
          cases c with
          | mk cc ci =>
              simp [securityFlowsTo] at h₁ h₂ ⊢
              exact And.intro
                (confidentialityFlowsTo_trans ac bc cc h₁.left h₂.left)
                (integrityFlowsTo_trans ci bi ai h₂.right h₁.right)

-- ============================================================================
-- WS-E5/H-04: Parameterized security domain lattice (3+ domains)
-- ============================================================================

/-- Three-level confidentiality lattice supporting 3+ security domains.
WS-E5/H-04: Extends the binary low/high limitation. -/
inductive ConfidentialityLevel where
  | pub
  | internal_
  | secret_
  deriving Repr, DecidableEq

/-- Three-level integrity lattice supporting 3+ security domains.
WS-E5/H-04: Extends the binary untrusted/trusted limitation. -/
inductive IntegrityLevel where
  | untrusted_
  | endorsed
  | trusted_
  deriving Repr, DecidableEq

/-- Confidentiality level ordering: pub <= internal_ <= secret_. -/
def confidentialityLevelFlowsTo : ConfidentialityLevel -> ConfidentialityLevel -> Bool
  | .pub, _ => true
  | .internal_, .pub => false
  | .internal_, _ => true
  | .secret_, .secret_ => true
  | .secret_, _ => false

/-- Integrity level ordering: untrusted_ <= endorsed <= trusted_. -/
def integrityLevelFlowsTo : IntegrityLevel -> IntegrityLevel -> Bool
  | .untrusted_, _ => true
  | .endorsed, .untrusted_ => false
  | .endorsed, _ => true
  | .trusted_, .trusted_ => true
  | .trusted_, _ => false

theorem confidentialityLevelFlowsTo_refl (c : ConfidentialityLevel) :
    confidentialityLevelFlowsTo c c = true := by
  cases c <;> rfl

theorem confidentialityLevelFlowsTo_trans
    (a b c : ConfidentialityLevel)
    (h1 : confidentialityLevelFlowsTo a b = true)
    (h2 : confidentialityLevelFlowsTo b c = true) :
    confidentialityLevelFlowsTo a c = true := by
  cases a <;> cases b <;> cases c <;> simp [confidentialityLevelFlowsTo] at *

theorem integrityLevelFlowsTo_refl (i : IntegrityLevel) :
    integrityLevelFlowsTo i i = true := by
  cases i <;> rfl

theorem integrityLevelFlowsTo_trans
    (a b c : IntegrityLevel)
    (h1 : integrityLevelFlowsTo a b = true)
    (h2 : integrityLevelFlowsTo b c = true) :
    integrityLevelFlowsTo a c = true := by
  cases a <;> cases b <;> cases c <;> simp [integrityLevelFlowsTo] at *

/-- Three-domain security label: 3 confidentiality x 3 integrity = 9 labels.
WS-E5/H-04: Satisfies the validation gate of at least 3 security domains. -/
structure ThreeDomainLabel where
  conf : ConfidentialityLevel
  integ : IntegrityLevel
  deriving Repr, DecidableEq

/-- Combined flow relation for three-domain labels. -/
def threeDomainFlowsTo (src dst : ThreeDomainLabel) : Bool :=
  confidentialityLevelFlowsTo src.conf dst.conf &&
    integrityLevelFlowsTo dst.integ src.integ

theorem threeDomainFlowsTo_refl (l : ThreeDomainLabel) :
    threeDomainFlowsTo l l = true := by
  cases l with
  | mk c i =>
    simp [threeDomainFlowsTo, confidentialityLevelFlowsTo_refl, integrityLevelFlowsTo_refl]

theorem threeDomainFlowsTo_trans
    (a b c : ThreeDomainLabel)
    (h1 : threeDomainFlowsTo a b = true)
    (h2 : threeDomainFlowsTo b c = true) :
    threeDomainFlowsTo a c = true := by
  cases a with
  | mk ac ai =>
    cases b with
    | mk bc bi =>
      cases c with
      | mk cc ci =>
        simp [threeDomainFlowsTo] at h1 h2 |-
        exact And.intro
          (confidentialityLevelFlowsTo_trans ac bc cc h1.left h2.left)
          (integrityLevelFlowsTo_trans ci bi ai h2.right h1.right)

namespace ThreeDomainLabel

def publicUntrusted : ThreeDomainLabel :=
  { conf := .pub, integ := .untrusted_ }

def internalEndorsed : ThreeDomainLabel :=
  { conf := .internal_, integ := .endorsed }

def secretTrusted : ThreeDomainLabel :=
  { conf := .secret_, integ := .trusted_ }

def internalTrusted : ThreeDomainLabel :=
  { conf := .internal_, integ := .trusted_ }

def publicTrusted : ThreeDomainLabel :=
  { conf := .pub, integ := .trusted_ }

end ThreeDomainLabel

/-- Labeling context parameterized by a generic label type.
WS-E5/H-04: Supports per-endpoint flow policies. -/
structure GenericLabelingContext (L : Type) where
  objectLabelOf : SeLe4n.ObjId -> L
  threadLabelOf : SeLe4n.ThreadId -> L
  endpointLabelOf : SeLe4n.ObjId -> L
  serviceLabelOf : ServiceId -> L
  /-- Per-endpoint flow policy. Defaults to always-allow. -/
  endpointPolicyOf : SeLe4n.ObjId -> L -> L -> Bool := fun _ _ _ => true

/-- Convert existing LabelingContext to generic form. -/
def LabelingContext.toGeneric (ctx : LabelingContext) :
    GenericLabelingContext SecurityLabel :=
  { objectLabelOf := ctx.objectLabelOf
    threadLabelOf := ctx.threadLabelOf
    endpointLabelOf := ctx.endpointLabelOf
    serviceLabelOf := ctx.serviceLabelOf
    endpointPolicyOf := fun _ src dst => securityFlowsTo src dst }

/-- WS-E5/H-04: Three-domain labeling context with 3 distinct security domains. -/
def sampleThreeDomainContext : GenericLabelingContext ThreeDomainLabel :=
  { objectLabelOf := fun oid =>
      if oid.val <= 10 then ThreeDomainLabel.publicUntrusted
      else if oid.val <= 20 then ThreeDomainLabel.internalEndorsed
      else ThreeDomainLabel.secretTrusted
    threadLabelOf := fun tid =>
      if tid.val <= 10 then ThreeDomainLabel.publicUntrusted
      else if tid.val <= 20 then ThreeDomainLabel.internalEndorsed
      else ThreeDomainLabel.secretTrusted
    endpointLabelOf := fun oid =>
      if oid.val <= 10 then ThreeDomainLabel.publicUntrusted
      else if oid.val <= 20 then ThreeDomainLabel.internalEndorsed
      else ThreeDomainLabel.secretTrusted
    serviceLabelOf := fun sid =>
      if sid.val <= 10 then ThreeDomainLabel.publicUntrusted
      else if sid.val <= 20 then ThreeDomainLabel.internalEndorsed
      else ThreeDomainLabel.secretTrusted }

end SeLe4n.Kernel
