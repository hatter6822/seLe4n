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
-- WS-E5/H-04: Generic security lattice and N-domain parameterization
-- ============================================================================

/-- WS-E5/H-04: Typeclass for a security lattice with decidable flow relation.
    Any type carrying this instance can serve as a security label domain.
    The concrete `SecurityLabel` (2×2 lattice) is one instance; `SecurityDomainN`
    provides N-level linear lattices for 3+ domain configurations. -/
class SecurityLattice (α : Type) where
  flowsTo : α → α → Bool
  flowsTo_refl : ∀ a, flowsTo a a = true
  flowsTo_trans : ∀ a b c, flowsTo a b = true → flowsTo b c = true →
    flowsTo a c = true

/-- WS-E5/H-04: The concrete 2×2 product lattice is a `SecurityLattice` instance. -/
instance : SecurityLattice SecurityLabel where
  flowsTo := securityFlowsTo
  flowsTo_refl := securityFlowsTo_refl
  flowsTo_trans := securityFlowsTo_trans

/-- WS-E5/H-04: N-level linear security domain supporting ≥3 security levels.
    Level 0 is the lowest (most public); level n-1 is the highest (most secret).
    Information flows upward: level i can flow to level j iff i ≤ j. -/
structure SecurityDomainN where
  level : Nat
  deriving DecidableEq, Repr

namespace SecurityDomainN

/-- Construct a domain at a given level. -/
@[inline] def ofLevel (n : Nat) : SecurityDomainN := ⟨n⟩

/-- The lowest (most public) domain. -/
@[inline] def bottom : SecurityDomainN := ⟨0⟩

/-- Flow relation for the N-level linear lattice: information flows upward. -/
@[inline] def flowsTo (src dst : SecurityDomainN) : Bool :=
  src.level ≤ dst.level

theorem flowsTo_refl (a : SecurityDomainN) : flowsTo a a = true := by
  simp [flowsTo, Nat.le_refl]

theorem flowsTo_trans (a b c : SecurityDomainN)
    (h₁ : flowsTo a b = true) (h₂ : flowsTo b c = true) :
    flowsTo a c = true := by
  simp [flowsTo] at h₁ h₂ ⊢
  exact Nat.le_trans h₁ h₂

theorem flowsTo_antisymm (a b : SecurityDomainN)
    (h₁ : flowsTo a b = true) (h₂ : flowsTo b a = true) :
    a = b := by
  simp [flowsTo] at h₁ h₂
  cases a; cases b; congr; exact Nat.le_antisymm h₁ h₂

end SecurityDomainN

/-- WS-E5/H-04: The N-level linear domain is a `SecurityLattice` instance. -/
instance : SecurityLattice SecurityDomainN where
  flowsTo := SecurityDomainN.flowsTo
  flowsTo_refl := SecurityDomainN.flowsTo_refl
  flowsTo_trans := SecurityDomainN.flowsTo_trans

/-- WS-E5/H-04: Product lattice over two `SecurityLattice` components.
    Generalizes the existing `SecurityLabel` = `Confidentiality × Integrity`
    pattern to arbitrary lattice pairs. -/
structure ProductLabel (α β : Type) where
  fst : α
  snd : β
  deriving DecidableEq, Repr

instance [SecurityLattice α] [SecurityLattice β] :
    SecurityLattice (ProductLabel α β) where
  flowsTo src dst :=
    SecurityLattice.flowsTo src.fst dst.fst &&
    SecurityLattice.flowsTo src.snd dst.snd
  flowsTo_refl a := by
    simp [SecurityLattice.flowsTo_refl]
  flowsTo_trans a b c h₁ h₂ := by
    simp [Bool.and_eq_true] at h₁ h₂ ⊢
    exact ⟨SecurityLattice.flowsTo_trans a.fst b.fst c.fst h₁.1 h₂.1,
           SecurityLattice.flowsTo_trans a.snd b.snd c.snd h₁.2 h₂.2⟩

-- ============================================================================
-- WS-E5/H-04: Generic labeling context parameterized by label type
-- ============================================================================

/-- WS-E5/H-04: Generic labeling context parameterized by any `SecurityLattice`
    label type. This generalizes `LabelingContext` from the concrete
    `SecurityLabel` to arbitrary label domains. -/
structure GenericLabelingContext (α : Type) where
  objectLabelOf : SeLe4n.ObjId → α
  threadLabelOf : SeLe4n.ThreadId → α
  endpointLabelOf : SeLe4n.ObjId → α
  serviceLabelOf : ServiceId → α

/-- WS-E5/H-04: Convert a concrete `LabelingContext` to the generic form. -/
def LabelingContext.toGeneric (ctx : LabelingContext) :
    GenericLabelingContext SecurityLabel :=
  { objectLabelOf := ctx.objectLabelOf
    threadLabelOf := ctx.threadLabelOf
    endpointLabelOf := ctx.endpointLabelOf
    serviceLabelOf := ctx.serviceLabelOf }

/-- WS-E5/H-04: Generic flow check using any `SecurityLattice` instance. -/
def genericFlowsTo [SecurityLattice α] (src dst : α) : Bool :=
  SecurityLattice.flowsTo src dst

/-- WS-E5/H-04: Generic flow check is reflexive for any lattice. -/
theorem genericFlowsTo_refl [SecurityLattice α] (a : α) :
    genericFlowsTo a a = true :=
  SecurityLattice.flowsTo_refl a

/-- WS-E5/H-04: Generic flow check is transitive for any lattice. -/
theorem genericFlowsTo_trans [SecurityLattice α] (a b c : α)
    (h₁ : genericFlowsTo a b = true)
    (h₂ : genericFlowsTo b c = true) :
    genericFlowsTo a c = true :=
  SecurityLattice.flowsTo_trans a b c h₁ h₂

-- ============================================================================
-- WS-E5/H-04: Per-endpoint flow policy
-- ============================================================================

/-- WS-E5/H-04: Per-endpoint flow policy that can override the default
    label-based flow decision. This enables fine-grained IPC channel
    configuration where specific endpoints may permit or deny flows
    independent of the global label ordering. -/
inductive EndpointFlowDecision where
  | useDefault   -- defer to label-based `securityFlowsTo`
  | permitAlways -- allow regardless of labels
  | denyAlways   -- deny regardless of labels
  deriving Repr, DecidableEq

/-- WS-E5/H-04: Extended labeling context with per-endpoint flow policies. -/
structure PolicyContext where
  labels : LabelingContext
  endpointPolicy : SeLe4n.ObjId → EndpointFlowDecision

/-- WS-E5/H-04: Default policy context defers all decisions to label checks. -/
def defaultPolicyContext : PolicyContext :=
  { labels := defaultLabelingContext
    endpointPolicy := fun _ => .useDefault }

/-- WS-E5/H-04: Resolve an endpoint flow decision using the policy context.
    Per-endpoint overrides take priority over label-based decisions. -/
def resolveEndpointFlow (pctx : PolicyContext)
    (senderLabel endpointLabel : SecurityLabel)
    (endpointId : SeLe4n.ObjId) : Bool :=
  match pctx.endpointPolicy endpointId with
  | .useDefault => securityFlowsTo senderLabel endpointLabel
  | .permitAlways => true
  | .denyAlways => false

/-- WS-E5/H-04: Per-endpoint policy with `useDefault` equals label-based flow. -/
theorem resolveEndpointFlow_useDefault
    (pctx : PolicyContext) (senderLabel endpointLabel : SecurityLabel)
    (endpointId : SeLe4n.ObjId)
    (hDefault : pctx.endpointPolicy endpointId = .useDefault) :
    resolveEndpointFlow pctx senderLabel endpointLabel endpointId =
      securityFlowsTo senderLabel endpointLabel := by
  simp [resolveEndpointFlow, hDefault]

/-- WS-E5/H-04: `permitAlways` always returns true regardless of labels. -/
theorem resolveEndpointFlow_permitAlways
    (pctx : PolicyContext) (senderLabel endpointLabel : SecurityLabel)
    (endpointId : SeLe4n.ObjId)
    (hPermit : pctx.endpointPolicy endpointId = .permitAlways) :
    resolveEndpointFlow pctx senderLabel endpointLabel endpointId = true := by
  simp [resolveEndpointFlow, hPermit]

/-- WS-E5/H-04: `denyAlways` always returns false regardless of labels. -/
theorem resolveEndpointFlow_denyAlways
    (pctx : PolicyContext) (senderLabel endpointLabel : SecurityLabel)
    (endpointId : SeLe4n.ObjId)
    (hDeny : pctx.endpointPolicy endpointId = .denyAlways) :
    resolveEndpointFlow pctx senderLabel endpointLabel endpointId = false := by
  simp [resolveEndpointFlow, hDeny]

-- ============================================================================
-- WS-E5/H-04: Example three-domain configuration
-- ============================================================================

/-- WS-E5/H-04: Example three-domain linear lattice demonstrating ≥3 domains.
    Domain 0 = public, Domain 1 = internal, Domain 2 = secret. -/
def threeDomainExample : GenericLabelingContext SecurityDomainN :=
  { objectLabelOf := fun oid =>
      if oid.val ≤ 10 then .ofLevel 0      -- public objects
      else if oid.val ≤ 20 then .ofLevel 1  -- internal objects
      else .ofLevel 2                        -- secret objects
    threadLabelOf := fun tid =>
      if tid.val ≤ 5 then .ofLevel 0
      else if tid.val ≤ 10 then .ofLevel 1
      else .ofLevel 2
    endpointLabelOf := fun oid =>
      if oid.val ≤ 10 then .ofLevel 0
      else if oid.val ≤ 20 then .ofLevel 1
      else .ofLevel 2
    serviceLabelOf := fun sid =>
      if sid.val ≤ 3 then .ofLevel 0
      else if sid.val ≤ 6 then .ofLevel 1
      else .ofLevel 2 }

/-- WS-E5/H-04: Three-domain lattice allows public→internal flow. -/
example : SecurityDomainN.flowsTo (.ofLevel 0) (.ofLevel 1) = true := rfl

/-- WS-E5/H-04: Three-domain lattice allows public→secret flow. -/
example : SecurityDomainN.flowsTo (.ofLevel 0) (.ofLevel 2) = true := rfl

/-- WS-E5/H-04: Three-domain lattice allows internal→secret flow. -/
example : SecurityDomainN.flowsTo (.ofLevel 1) (.ofLevel 2) = true := rfl

/-- WS-E5/H-04: Three-domain lattice denies secret→public flow. -/
example : SecurityDomainN.flowsTo (.ofLevel 2) (.ofLevel 0) = false := rfl

/-- WS-E5/H-04: Three-domain lattice denies secret→internal flow. -/
example : SecurityDomainN.flowsTo (.ofLevel 2) (.ofLevel 1) = false := rfl

/-- WS-E5/H-04: Three-domain lattice denies internal→public flow. -/
example : SecurityDomainN.flowsTo (.ofLevel 1) (.ofLevel 0) = false := rfl

end SeLe4n.Kernel
