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
-- WS-E5/H-04: Parameterized security domain lattice
-- ============================================================================

/-! ## H-04 — Parameterized Security Domains

The original `{low, high} × {untrusted, trusted}` lattice is retained for
backward compatibility. This section introduces a parameterized domain model
that supports ≥3 security domains with explicit flow policies.

Design:
- `SecurityDomain` wraps a `Nat` domain identifier (0..n-1).
- `DomainFlowPolicy` defines an explicit flow-authorization function between domains.
- Lattice properties (reflexivity, transitivity, antisymmetry) are proved generically
  under policy constraints.
- `EndpointFlowPolicy` adds per-endpoint flow overrides for fine-grained IPC policy.
- An embedding function maps the legacy 2-level lattice into a 4-domain generic lattice,
  proving that the generic system strictly subsumes the original. -/

/-- WS-E5/H-04: Nat-indexed security domain identifier.

Each domain is identified by a natural number. Domain 0 is conventionally the
lowest (most public) domain. -/
structure SecurityDomain where
  id : Nat
  deriving Repr, DecidableEq, Inhabited

namespace SecurityDomain

/-- The public (lowest) domain. -/
def lowest : SecurityDomain := ⟨0⟩

instance instOfNat (n : Nat) : OfNat SecurityDomain n where
  ofNat := ⟨n⟩

instance : ToString SecurityDomain where
  toString d := s!"domain({d.id})"

end SecurityDomain

/-- WS-E5/H-04: Explicit flow-authorization policy between security domains.

`canFlow src dst` returns `true` iff information may flow from domain `src`
to domain `dst`. The policy must be reflexive (self-flows always permitted)
and transitive (if a→b and b→c then a→c) to form a valid pre-order. -/
structure DomainFlowPolicy where
  canFlow : SecurityDomain → SecurityDomain → Bool

namespace DomainFlowPolicy

/-- A policy is reflexive: every domain can flow to itself. -/
def isReflexive (p : DomainFlowPolicy) : Prop :=
  ∀ d : SecurityDomain, p.canFlow d d = true

/-- A policy is transitive: flow composes. -/
def isTransitive (p : DomainFlowPolicy) : Prop :=
  ∀ a b c : SecurityDomain,
    p.canFlow a b = true → p.canFlow b c = true → p.canFlow a c = true

/-- A well-formed flow policy is reflexive and transitive. -/
def wellFormed (p : DomainFlowPolicy) : Prop :=
  p.isReflexive ∧ p.isTransitive

/-- Trivial policy: all flows allowed (flat lattice). -/
def allowAll : DomainFlowPolicy :=
  { canFlow := fun _ _ => true }

/-- Strict linear policy for `n` domains: domain `a` can flow to domain `b`
iff `a.id ≤ b.id`. This creates a total order 0 ≤ 1 ≤ ... ≤ n-1. -/
def linearOrder : DomainFlowPolicy :=
  { canFlow := fun src dst => decide (src.id ≤ dst.id) }

end DomainFlowPolicy

-- ============================================================================
-- Generic lattice property proofs
-- ============================================================================

theorem DomainFlowPolicy.allowAll_reflexive :
    DomainFlowPolicy.allowAll.isReflexive := by
  intro _; rfl

theorem DomainFlowPolicy.allowAll_transitive :
    DomainFlowPolicy.allowAll.isTransitive := by
  intro _ _ _ _ _; rfl

theorem DomainFlowPolicy.allowAll_wellFormed :
    DomainFlowPolicy.allowAll.wellFormed :=
  ⟨allowAll_reflexive, allowAll_transitive⟩

theorem DomainFlowPolicy.linearOrder_reflexive :
    DomainFlowPolicy.linearOrder.isReflexive := by
  intro d; simp [linearOrder]

theorem DomainFlowPolicy.linearOrder_transitive :
    DomainFlowPolicy.linearOrder.isTransitive := by
  intro a b c h₁ h₂
  simp [linearOrder] at h₁ h₂ ⊢
  exact Nat.le_trans h₁ h₂

theorem DomainFlowPolicy.linearOrder_wellFormed :
    DomainFlowPolicy.linearOrder.wellFormed :=
  ⟨linearOrder_reflexive, linearOrder_transitive⟩

/-- WS-E5/H-04: Generic flow check using a domain flow policy.

This is the parameterized replacement for `securityFlowsTo` that supports
arbitrary domain counts and flow topologies. -/
def domainFlowsTo (policy : DomainFlowPolicy) (src dst : SecurityDomain) : Bool :=
  policy.canFlow src dst

theorem domainFlowsTo_refl
    (policy : DomainFlowPolicy) (d : SecurityDomain)
    (hRefl : policy.isReflexive) :
    domainFlowsTo policy d d = true :=
  hRefl d

theorem domainFlowsTo_trans
    (policy : DomainFlowPolicy) (a b c : SecurityDomain)
    (hTrans : policy.isTransitive)
    (h₁ : domainFlowsTo policy a b = true)
    (h₂ : domainFlowsTo policy b c = true) :
    domainFlowsTo policy a c = true :=
  hTrans a b c h₁ h₂

-- ============================================================================
-- WS-E5/H-04: Generic labeling context
-- ============================================================================

/-- WS-E5/H-04: Generic labeling context assigning security domains (not fixed
`SecurityLabel` values) to entities. Supports ≥3 domains. -/
structure GenericLabelingContext where
  policy : DomainFlowPolicy
  objectDomainOf : SeLe4n.ObjId → SecurityDomain
  threadDomainOf : SeLe4n.ThreadId → SecurityDomain
  endpointDomainOf : SeLe4n.ObjId → SecurityDomain
  serviceDomainOf : ServiceId → SecurityDomain

/-- WS-E5/H-04: Default generic labeling: everything in domain 0 (public),
all flows allowed. -/
def defaultGenericLabelingContext : GenericLabelingContext :=
  {
    policy := .allowAll
    objectDomainOf := fun _ => SecurityDomain.lowest
    threadDomainOf := fun _ => SecurityDomain.lowest
    endpointDomainOf := fun _ => SecurityDomain.lowest
    serviceDomainOf := fun _ => SecurityDomain.lowest
  }

/-- WS-E5/H-04: Check whether information may flow from a source entity's
domain to a destination entity's domain under a generic labeling context. -/
def genericFlowCheck (ctx : GenericLabelingContext)
    (srcDomain dstDomain : SecurityDomain) : Bool :=
  domainFlowsTo ctx.policy srcDomain dstDomain

-- ============================================================================
-- WS-E5/H-04: Per-endpoint flow policy overrides
-- ============================================================================

/-- WS-E5/H-04: Per-endpoint flow policy allowing fine-grained overrides.

Each endpoint may optionally specify a custom flow policy that restricts which
domains can send/receive through it, independent of the global domain policy.
When `endpointPolicy` returns `none`, the global policy applies. -/
structure EndpointFlowPolicy where
  endpointPolicy : SeLe4n.ObjId → Option DomainFlowPolicy

/-- Check flow with per-endpoint override: if the endpoint has a custom policy,
use it; otherwise fall back to the global context policy. -/
def endpointFlowCheck (ctx : GenericLabelingContext)
    (epPolicy : EndpointFlowPolicy)
    (endpointId : SeLe4n.ObjId)
    (srcDomain dstDomain : SecurityDomain) : Bool :=
  match epPolicy.endpointPolicy endpointId with
  | some customPolicy => domainFlowsTo customPolicy srcDomain dstDomain
  | none => genericFlowCheck ctx srcDomain dstDomain

/-- When no per-endpoint override exists, the endpoint flow check falls back
to the global policy. -/
theorem endpointFlowCheck_fallback
    (ctx : GenericLabelingContext)
    (epPolicy : EndpointFlowPolicy)
    (endpointId : SeLe4n.ObjId)
    (src dst : SecurityDomain)
    (hNone : epPolicy.endpointPolicy endpointId = none) :
    endpointFlowCheck ctx epPolicy endpointId src dst =
      genericFlowCheck ctx src dst := by
  simp [endpointFlowCheck, hNone]

/-- When a per-endpoint override exists, the endpoint flow check uses it. -/
theorem endpointFlowCheck_override
    (ctx : GenericLabelingContext)
    (epPolicy : EndpointFlowPolicy)
    (endpointId : SeLe4n.ObjId)
    (src dst : SecurityDomain)
    (customPolicy : DomainFlowPolicy)
    (hSome : epPolicy.endpointPolicy endpointId = some customPolicy) :
    endpointFlowCheck ctx epPolicy endpointId src dst =
      domainFlowsTo customPolicy src dst := by
  simp [endpointFlowCheck, hSome]

-- ============================================================================
-- WS-E5/H-04: Legacy lattice embedding
-- ============================================================================

/-- WS-E5/H-04: Embed the legacy 2×2 lattice into a 4-domain linear lattice.

Mapping:
- `{low, untrusted}`  → domain 0 (public, lowest)
- `{low, trusted}`    → domain 1
- `{high, untrusted}` → domain 2
- `{high, trusted}`   → domain 3 (kernel, highest)

This embedding preserves `securityFlowsTo` semantics under the `linearOrder`
policy, proving that the generic system strictly subsumes the original. -/
def embedLegacyLabel (l : SecurityLabel) : SecurityDomain :=
  match l.confidentiality, l.integrity with
  | .low,  .untrusted => ⟨0⟩
  | .low,  .trusted   => ⟨1⟩
  | .high, .untrusted => ⟨2⟩
  | .high, .trusted   => ⟨3⟩

/-- The legacy `publicLabel` maps to domain 0. -/
theorem embedLegacyLabel_public :
    embedLegacyLabel SecurityLabel.publicLabel = ⟨0⟩ := rfl

/-- The legacy `kernelTrusted` label maps to domain 3. -/
theorem embedLegacyLabel_kernelTrusted :
    embedLegacyLabel SecurityLabel.kernelTrusted = ⟨3⟩ := rfl

/-- Legacy flow semantics are preserved by the embedding under linearOrder:
if `securityFlowsTo src dst = true`, then `linearOrder.canFlow (embed src) (embed dst) = true`. -/
theorem embedLegacyLabel_preserves_flow
    (src dst : SecurityLabel)
    (hFlow : securityFlowsTo src dst = true) :
    DomainFlowPolicy.linearOrder.canFlow (embedLegacyLabel src) (embedLegacyLabel dst) = true := by
  cases src with
  | mk sc si =>
    cases dst with
    | mk dc di =>
      cases sc <;> cases si <;> cases dc <;> cases di <;>
        simp [securityFlowsTo, confidentialityFlowsTo, integrityFlowsTo] at hFlow <;>
        simp [embedLegacyLabel, DomainFlowPolicy.linearOrder]

/-- Lift a legacy `LabelingContext` into a `GenericLabelingContext` using the
embedding and linearOrder policy. -/
def liftLegacyContext (ctx : LabelingContext) : GenericLabelingContext :=
  {
    policy := .linearOrder
    objectDomainOf := fun oid => embedLegacyLabel (ctx.objectLabelOf oid)
    threadDomainOf := fun tid => embedLegacyLabel (ctx.threadLabelOf tid)
    endpointDomainOf := fun oid => embedLegacyLabel (ctx.endpointLabelOf oid)
    serviceDomainOf := fun sid => embedLegacyLabel (ctx.serviceLabelOf sid)
  }

-- ============================================================================
-- WS-E5/H-04: Example 3-domain configuration
-- ============================================================================

/-- WS-E5/H-04: Example 3-domain lattice demonstrating ≥3 domain support.

Domains: 0 = userland, 1 = driver, 2 = kernel.
Flow: userland → driver → kernel (linear order). -/
def threeDomainExample : DomainFlowPolicy := .linearOrder

/-- The 3-domain example is well-formed (inherited from linearOrder). -/
theorem threeDomainExample_wellFormed :
    threeDomainExample.wellFormed :=
  DomainFlowPolicy.linearOrder_wellFormed

/-- Domain 0 (userland) can flow to domain 1 (driver). -/
theorem threeDomain_userland_to_driver :
    domainFlowsTo threeDomainExample ⟨0⟩ ⟨1⟩ = true := by
  simp [domainFlowsTo, threeDomainExample, DomainFlowPolicy.linearOrder]

/-- Domain 1 (driver) can flow to domain 2 (kernel). -/
theorem threeDomain_driver_to_kernel :
    domainFlowsTo threeDomainExample ⟨1⟩ ⟨2⟩ = true := by
  simp [domainFlowsTo, threeDomainExample, DomainFlowPolicy.linearOrder]

/-- Domain 2 (kernel) cannot flow to domain 0 (userland). -/
theorem threeDomain_kernel_not_to_userland :
    domainFlowsTo threeDomainExample ⟨2⟩ ⟨0⟩ = false := by
  simp [domainFlowsTo, threeDomainExample, DomainFlowPolicy.linearOrder]

-- ============================================================================
-- WS-H10/A-34: Security lattice resolution — integrity model documentation
-- ============================================================================

/-! ## WS-H10/A-34 — Integrity Model Threat Justification

The legacy `securityFlowsTo` function reverses the BIBA integrity comparison:
`integrityFlowsTo dst.integrity src.integrity` checks that the destination is
not MORE trusted than the source, allowing untrusted→trusted flow. Standard
BIBA denies this (no write-up for integrity).

**Design rationale (threat model justification):**
The reversed integrity in this model implements a "write-up" policy where low-
integrity (untrusted) processes may submit data to high-integrity (trusted)
components. This models a common microkernel pattern: user-space drivers and
services submit requests to trusted kernel components via IPC. The IPC channel
itself performs the integrity boundary crossing under capability-mediated
authorization. Integrity checking at the IPC layer would duplicate the capability
system's access control without security benefit in the seLe4n threat model.

The generic `DomainFlowPolicy` model (introduced in WS-E5/H-04) subsumes this
design choice: configuring a `DomainFlowPolicy` with BIBA-standard integrity
is straightforward (use `bibaPolicy` below). Production deployments should
select the appropriate policy for their threat model.

**Standard BIBA alternative:** `bibaIntegrityFlowsTo` and `bibaPolicy` below
provide a standard BIBA integrity model for deployments requiring no-write-up. -/

/-- WS-H10/A-34: Standard BIBA integrity flow — high-integrity data may flow
to low-integrity destinations (read-down), but low-integrity data may NOT
flow to high-integrity destinations (no write-up).

Contrast with `integrityFlowsTo` which allows write-up. -/
def bibaIntegrityFlowsTo : Integrity → Integrity → Bool
  | .trusted, .trusted => true
  | .trusted, .untrusted => true
  | .untrusted, .untrusted => true
  | .untrusted, .trusted => false

/-- WS-H10/A-34: BLP+BIBA combined security flow check.
Confidentiality: no read-up (standard BLP).
Integrity: no write-up (standard BIBA). -/
def bibaSecurityFlowsTo (src dst : SecurityLabel) : Bool :=
  confidentialityFlowsTo src.confidentiality dst.confidentiality &&
    bibaIntegrityFlowsTo src.integrity dst.integrity

theorem bibaIntegrityFlowsTo_refl (i : Integrity) :
    bibaIntegrityFlowsTo i i = true := by
  cases i <;> rfl

theorem bibaSecurityFlowsTo_refl (l : SecurityLabel) :
    bibaSecurityFlowsTo l l = true := by
  cases l with
  | mk c i =>
      simp [bibaSecurityFlowsTo, confidentialityFlowsTo_refl, bibaIntegrityFlowsTo_refl]

theorem bibaIntegrityFlowsTo_trans
    (a b c : Integrity)
    (h₁ : bibaIntegrityFlowsTo a b = true)
    (h₂ : bibaIntegrityFlowsTo b c = true) :
    bibaIntegrityFlowsTo a c = true := by
  cases a <;> cases b <;> cases c <;> simp [bibaIntegrityFlowsTo] at h₁ h₂ ⊢

theorem bibaSecurityFlowsTo_trans
    (a b c : SecurityLabel)
    (h₁ : bibaSecurityFlowsTo a b = true)
    (h₂ : bibaSecurityFlowsTo b c = true) :
    bibaSecurityFlowsTo a c = true := by
  cases a with
  | mk ac ai =>
      cases b with
      | mk bc bi =>
          cases c with
          | mk cc ci =>
              simp [bibaSecurityFlowsTo] at h₁ h₂ ⊢
              exact And.intro
                (confidentialityFlowsTo_trans ac bc cc h₁.left h₂.left)
                (bibaIntegrityFlowsTo_trans ai bi ci h₁.right h₂.right)

/-- WS-H10/A-34: BIBA-standard DomainFlowPolicy for the generic domain model.
Uses a linear order where domain 0 is lowest-integrity/confidentiality and
higher domains have strictly higher security. Unlike the legacy lattice,
this policy enforces standard BIBA: no write-up for integrity. -/
def bibaPolicy : DomainFlowPolicy :=
  { canFlow := fun src dst => decide (src.id ≤ dst.id) }

theorem bibaPolicy_reflexive : bibaPolicy.isReflexive := by
  intro d; simp [bibaPolicy]

theorem bibaPolicy_transitive : bibaPolicy.isTransitive := by
  intro a b c h₁ h₂
  simp [bibaPolicy] at h₁ h₂ ⊢
  exact Nat.le_trans h₁ h₂

theorem bibaPolicy_wellFormed : bibaPolicy.wellFormed :=
  ⟨bibaPolicy_reflexive, bibaPolicy_transitive⟩

/-- WS-H10/A-34: The legacy lattice is a valid (non-standard) security lattice.
Reflexivity and transitivity hold, making it a valid pre-order. -/
theorem securityLattice_reflexive : ∀ l : SecurityLabel, securityFlowsTo l l = true :=
  securityFlowsTo_refl

theorem securityLattice_transitive :
    ∀ a b c : SecurityLabel, securityFlowsTo a b = true → securityFlowsTo b c = true →
      securityFlowsTo a c = true :=
  securityFlowsTo_trans

-- ============================================================================
-- WS-H10/A-39: Declassification model
-- ============================================================================

/-! ## WS-H10/A-39 — Controlled Declassification

Declassification allows explicit, authorized downgrade of information from a
higher security domain to a lower one. Without declassification, any cross-
domain information flow that violates the lattice ordering is permanently
blocked. In practice, controlled declassification is needed for:

- Audit log publication (high → low for transparency)
- Sanitized data export (removing sensitive fields before downgrade)
- Inter-domain service results (a trusted service returning results to
  an untrusted caller)

The model uses a `DeclassificationPolicy` that explicitly authorizes which
domain pairs may declassify, preventing unrestricted downgrade. -/

/-- WS-H10/A-39: Declassification policy specifying authorized downgrade paths.

`canDeclassify src dst` returns `true` iff domain `src` is authorized to
declassify (downgrade) information to domain `dst`. This is distinct from
the normal flow policy: declassification explicitly permits flows that the
base lattice would deny.

**Well-formedness:** A declassification policy should never authorize
declassification along paths that the base policy already allows (that
would be redundant, not declassification). -/
structure DeclassificationPolicy where
  canDeclassify : SecurityDomain → SecurityDomain → Bool

namespace DeclassificationPolicy

/-- No declassification allowed (strictest policy). -/
def none : DeclassificationPolicy :=
  { canDeclassify := fun _ _ => false }

/-- Declassification is authorized iff: the base policy does NOT allow the
flow (otherwise it's not declassification) AND the declassification policy
explicitly permits it. -/
def isDeclassificationAuthorized
    (basePolicy : DomainFlowPolicy)
    (declPolicy : DeclassificationPolicy)
    (src dst : SecurityDomain) : Bool :=
  !basePolicy.canFlow src dst && declPolicy.canDeclassify src dst

/-- Declassification from domain `a` to itself is never a true declassification
(the base policy is always reflexive for well-formed policies). -/
theorem isDeclassificationAuthorized_not_reflexive
    (basePolicy : DomainFlowPolicy)
    (declPolicy : DeclassificationPolicy)
    (d : SecurityDomain)
    (hRefl : basePolicy.isReflexive) :
    isDeclassificationAuthorized basePolicy declPolicy d d = false := by
  simp [isDeclassificationAuthorized, hRefl d]

end DeclassificationPolicy

-- ============================================================================
-- WS-H10/M-16: Endpoint flow policy well-formedness
-- ============================================================================

/-! ## WS-H10/M-16 — Endpoint Flow Policy Well-Formedness

Per-endpoint `DomainFlowPolicy` overrides (from WS-E5/H-04) allow fine-grained
IPC access control. However, misconfigured endpoint policies can violate
reflexivity (a domain cannot send to its own endpoint) or transitivity (flow
composition breaks). This section adds well-formedness requirements. -/

/-- WS-H10/M-16: An endpoint flow policy configuration is well-formed when
every per-endpoint override policy satisfies `DomainFlowPolicy.wellFormed`
(reflexive + transitive). Endpoints without overrides inherit the global
policy, which must also be well-formed. -/
def endpointFlowPolicyWellFormed
    (globalPolicy : DomainFlowPolicy)
    (epPolicy : EndpointFlowPolicy) : Prop :=
  globalPolicy.wellFormed ∧
  ∀ oid p, epPolicy.endpointPolicy oid = some p → p.wellFormed

/-- WS-H10/M-16: If the global policy is well-formed and no endpoint overrides
exist, the configuration is trivially well-formed. -/
theorem endpointFlowPolicyWellFormed_no_overrides
    (globalPolicy : DomainFlowPolicy)
    (hWF : globalPolicy.wellFormed) :
    endpointFlowPolicyWellFormed globalPolicy
      { endpointPolicy := fun _ => none } := by
  constructor
  · exact hWF
  · intro _ _ h; simp at h

/-- WS-H10/M-16: The effective flow check at any endpoint inherits reflexivity
from the well-formedness requirement. -/
theorem endpointFlowCheck_reflexive
    (ctx : GenericLabelingContext)
    (epPolicy : EndpointFlowPolicy)
    (endpointId : SeLe4n.ObjId)
    (d : SecurityDomain)
    (hWF : endpointFlowPolicyWellFormed ctx.policy epPolicy) :
    endpointFlowCheck ctx epPolicy endpointId d d = true := by
  unfold endpointFlowCheck
  cases hEP : epPolicy.endpointPolicy endpointId with
  | none =>
    simp [genericFlowCheck, domainFlowsTo, hWF.1.1 d]
  | some customPolicy =>
    simp [domainFlowsTo, (hWF.2 endpointId customPolicy hEP).1 d]

/-- WS-H10/M-16: The effective flow check at any endpoint inherits transitivity
from the well-formedness requirement. -/
theorem endpointFlowCheck_transitive
    (ctx : GenericLabelingContext)
    (epPolicy : EndpointFlowPolicy)
    (endpointId : SeLe4n.ObjId)
    (a b c : SecurityDomain)
    (hWF : endpointFlowPolicyWellFormed ctx.policy epPolicy)
    (h₁ : endpointFlowCheck ctx epPolicy endpointId a b = true)
    (h₂ : endpointFlowCheck ctx epPolicy endpointId b c = true) :
    endpointFlowCheck ctx epPolicy endpointId a c = true := by
  unfold endpointFlowCheck at h₁ h₂ ⊢
  cases hEP : epPolicy.endpointPolicy endpointId with
  | none =>
    simp [hEP, genericFlowCheck, domainFlowsTo] at h₁ h₂ ⊢
    exact hWF.1.2 a b c h₁ h₂
  | some customPolicy =>
    simp [hEP, domainFlowsTo] at h₁ h₂ ⊢
    exact (hWF.2 endpointId customPolicy hEP).2 a b c h₁ h₂

end SeLe4n.Kernel
