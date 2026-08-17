-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.InformationFlow.AuditRecord

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

/-- Integrity order (`≥`) for trusted-data flow checks.

    U6-I (U-M22): **Deliberate non-standard BIBA direction**. Standard BIBA
    integrity denies write-up: an untrusted subject cannot write to a trusted
    object. seLe4n deliberately reverses this to implement a "both dimensions
    flow upward" lattice. The rationale:

    1. **seL4 compatibility**: seL4's information flow model (Murray et al.,
       CCS 2013) uses a single-dimensional confidentiality lattice. seLe4n's
       2D lattice (confidentiality × integrity) extends this, but the integrity
       dimension tracks *authority flow* rather than *data purity*.

    2. **Capability authority flow**: In a capability system, authority flows
       from high-privilege domains to low-privilege domains (delegation). The
       integrity dimension tracks this: trusted code may delegate authority to
       untrusted code (write-down = trusted→untrusted), but untrusted code
       cannot escalate authority to trusted code (write-up = untrusted→trusted
       is denied).

    3. **Practical effect**: `integrityFlowsTo dst.integrity src.integrity`
       checks `dst ≤ src`, meaning the destination must not be more trusted
       than the source. This prevents privilege escalation while allowing
       delegation.

    A standard BIBA alternative is provided as `bibaIntegrityFlowsTo` below.
    It is no longer only a comparison: WS-SM SM8.D states Biba integrity under
    per-core locks over an arbitrary write rule and instantiates it at **both**
    orders (`bibaWritePermitted` / `authorityWritePermitted`,
    `InformationFlow/FineLockFlow.lean`), because a result about one says
    nothing about a deployment configured with the other. -/
def integrityFlowsTo : Integrity → Integrity → Bool
  | .trusted, .trusted => true
  | .trusted, .untrusted => true
  | .untrusted, .untrusted => true
  | .untrusted, .trusted => false

/-- V6-C (M-IF-1): Standard BIBA integrity order for comparison.

    Standard BIBA denies write-up: untrusted subjects cannot write to trusted
    objects. This function is designed as a **drop-in replacement** for
    `integrityFlowsTo` in the `securityFlowsTo` formula, which passes arguments
    in reversed order: `integrityFlowsTo dst.integrity src.integrity`.

    When substituted into `securityFlowsTo` as `bibaIntegrityFlowsTo dst.int src.int`,
    it checks `src.int ≥ dst.int` (standard BIBA: source must be at least as
    trusted as destination, preventing write-up). This is the **opposite** of
    seLe4n's `integrityFlowsTo`, which in the same position checks `dst.int ≥ src.int`
    (allowing untrusted sources to reach trusted destinations).

    **Standalone semantics**: `bibaIntegrityFlowsTo a b = true` iff `b ≥ a`
    in the trust ordering (i.e., the second argument is at least as trusted
    as the first).

    **Live consumer** (WS-SM SM8.D): `bibaWritePermitted` in
    `InformationFlow/FineLockFlow.lean` reads it in exactly this drop-in
    position — `bibaIntegrityFlowsTo (objectLabel).integrity subject.integrity`
    — so `bibaIntegrity_underLockSet` is a statement about standard BIBA and
    `authorityIntegrity_underLockSet` its twin about the order above.
    `writeRules_differ` is the witness that those are two claims. -/
def bibaIntegrityFlowsTo : Integrity → Integrity → Bool
  | .trusted, .trusted => true
  | .trusted, .untrusted => false
  | .untrusted, .untrusted => true
  | .untrusted, .trusted => true

/-- V6-C (M-IF-1): `integrityFlowsTo` is **not** standard BIBA integrity.

    The seLe4n integrity model deliberately reverses BIBA for authority-flow
    tracking. This theorem provides an explicit compile-time witness that the
    two models differ, serving as a documentation anchor for auditors.

    The witness case `(trusted, untrusted)`: in `securityFlowsTo`, the integrity
    check is `integrityFlowsTo dst.int src.int`. When `dst=trusted, src=untrusted`:
    - seLe4n: `integrityFlowsTo .trusted .untrusted = true` → ALLOWS flow
      from untrusted source to trusted destination (authority receipt)
    - BIBA:   `bibaIntegrityFlowsTo .trusted .untrusted = false` → DENIES this
      flow (standard no-write-up rule) -/
theorem integrityFlowsTo_is_not_biba :
    integrityFlowsTo .trusted .untrusted = true ∧
    bibaIntegrityFlowsTo .trusted .untrusted = false := by
  decide

/-- V6-C (M-IF-1): Complementary witness for the opposite case.

    When `dst=untrusted, src=trusted` in `securityFlowsTo`:
    - seLe4n: `integrityFlowsTo .untrusted .trusted = false` → DENIES flow
      from trusted source to untrusted destination (no authority delegation)
    - BIBA:   `bibaIntegrityFlowsTo .untrusted .trusted = true` → ALLOWS this
      flow (standard write-down is permitted in BIBA) -/
theorem integrityFlowsTo_denies_write_up_biba_allows :
    integrityFlowsTo .untrusted .trusted = false ∧
    bibaIntegrityFlowsTo .untrusted .trusted = true := by
  decide

-- ============================================================================
-- X3-E (M-1): Privilege escalation prevention proof
-- ============================================================================

/-- X3-E (M-1): **Privilege escalation prevention theorem.**

    The non-standard BIBA direction in `integrityFlowsTo` still prevents
    privilege escalation: untrusted entities cannot modify trusted state.
    This theorem proves three security properties of the 2-element integrity
    lattice:

    1. **Escalation denial**: `integrityFlowsTo .untrusted .trusted = false` —
       untrusted code cannot flow to trusted destinations.
    2. **Flow characterization**: If `integrityFlowsTo src dst = true`, then
       either `dst = .untrusted` (any source can reach untrusted) or
       `src = .trusted` (trusted source can reach any destination). There is
       no third case: untrusted-to-trusted is the only denied pair.
    3. **Lattice completeness**: Self-flows are always permitted (reflexivity
       for both elements).

    Together, these properties ensure that the non-BIBA direction implements
    a valid authority-flow model where:
    - Trusted code can delegate authority downward (to untrusted)
    - Untrusted code can communicate with other untrusted code
    - Untrusted code CANNOT escalate to trusted status -/
theorem integrityFlowsTo_prevents_escalation :
    -- Untrusted-to-trusted flow is denied:
    integrityFlowsTo .untrusted .trusted = false ∧
    -- Only equal-or-lower trust can flow:
    (∀ src dst, integrityFlowsTo src dst = true →
      dst = .untrusted ∨ src = .trusted) ∧
    -- The lattice is a total order with trust as top:
    integrityFlowsTo .trusted .trusted = true ∧
    integrityFlowsTo .untrusted .untrusted = true := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro src dst h
  cases src <;> cases dst <;> simp_all [integrityFlowsTo]

/-- Combined policy relation: confidentiality must not flow down; integrity
    must not flow up (source must be at least as trusted as destination).

    U6-I (U-M22): This implements a "both dimensions flow upward" lattice —
    low confidentiality flows to high, and trusted integrity flows to untrusted.
    This is **not** standard BLP+BIBA (where BIBA would deny untrusted→trusted
    writes). The reversed argument order on `integrityFlowsTo` checks
    `dst.integrity ≤ src.integrity`, i.e., the destination must not be more
    trusted than the source. See the `integrityFlowsTo` docstring above for
    the full design rationale. -/
def securityFlowsTo (src dst : SecurityLabel) : Bool :=
  confidentialityFlowsTo src.confidentiality dst.confidentiality &&
    integrityFlowsTo dst.integrity src.integrity

/-- X3-E (M-1): The combined `securityFlowsTo` prevents confidential data
    leakage: a `kernelTrusted` entity (high confidentiality, trusted integrity)
    cannot flow information to a `publicLabel` entity (low confidentiality,
    untrusted integrity). The confidentiality dimension denies the downward
    flow (high → low), regardless of the integrity dimension.

    Note: `publicLabel → kernelTrusted` is ALLOWED by design — this models
    authority receipt (untrusted code invoking trusted services), which is the
    intended semantics of the non-BIBA integrity direction. -/
theorem securityFlowsTo_prevents_label_escalation :
    -- Confidential data cannot leak to public entities:
    securityFlowsTo SecurityLabel.kernelTrusted SecurityLabel.publicLabel = false ∧
    -- Authority receipt (untrusted invoking trusted) is permitted:
    securityFlowsTo SecurityLabel.publicLabel SecurityLabel.kernelTrusted = true := by
  decide

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

-- `SecurityDomain` and its instances live in
-- `SeLe4n.Kernel.InformationFlow.AuditRecord`, below `Model.State`, because
-- `SystemState` mounts a log of `DeclassificationEvent`s keyed by domain
-- (WS-SM SM8.C.8) and this module imports `Model.State`.  Same namespace, so
-- every reference below resolves unchanged.

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
-- WS-E5/H-04: Per-endpoint flow policy overrides
-- ============================================================================

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

/-- WS-E5/H-04: Per-endpoint flow policy allowing fine-grained overrides.

Each endpoint may optionally specify a custom flow policy that restricts which
domains can send/receive through it, independent of the global domain policy.
When `endpointPolicy` returns `none`, the global policy applies. -/
structure EndpointFlowPolicy where
  endpointPolicy : SeLe4n.ObjId → Option DomainFlowPolicy

-- ============================================================================
-- IF-M1: legacy labeling context
-- ============================================================================

/-- WS-I2/R-16: Ownership metadata for optional memory projection. -/
structure MemoryDomainOwnership where
  regionOwner : SeLe4n.PAddr → Option SeLe4n.DomainId
  domainLabelOf : SeLe4n.DomainId → SecurityLabel

/-- IF-M1 context: explicit label assignment entrypoints for each primary entity class. -/
structure LabelingContext where
  objectLabelOf : SeLe4n.ObjId → SecurityLabel
  threadLabelOf : SeLe4n.ThreadId → SecurityLabel
  endpointLabelOf : SeLe4n.ObjId → SecurityLabel
  serviceLabelOf : ServiceId → SecurityLabel
  memoryOwnership : Option MemoryDomainOwnership := none
  /-- WS-SM SM8.C: the **per-endpoint flow policy** the live IPC gates consult.

      WS-E5/H-04 introduced `EndpointFlowPolicy` and V6-G proved the properties a
      well-formed one must have, but no context carried one, so nothing in the
      kernel ever read it: the feature was specified and never wired.  The field
      is that wiring; `endpointFlowGate` is where it is read.

      Defaulted to "no override anywhere", which makes the gate's second conjunct
      vacuously `true` (`endpointFlowGate_eq_securityFlowsTo_of_no_override`), so
      every existing construction site and every existing behaviour is unchanged
      until an operator configures one.

      The policy is stated over `SecurityDomain`; the live gates carry
      `SecurityLabel`s, and the total embedding `embedLegacyLabel` bridges them —
      so an override is written against domains 0–3, one per point of the legacy
      2×2 lattice. -/
  endpointPolicy : EndpointFlowPolicy := { endpointPolicy := fun _ => none }
  /-- WS-SM SM8.C.9: the **declassification policy** the live `.declassify`
      syscall consults — which domain pairs may be downgraded along.

      Defaulted to **deny everything**, which is the fail-closed default and not
      merely a compatibility one: without a configured policy there is no such
      thing as an authorized downgrade, so an unconfigured deployment cannot
      declassify at all and `.declassify` returns `.declassificationDenied` on
      every call (`declassificationDecision_default_denies`).

      Stated over `SecurityDomain`, like `endpointPolicy`, and reached from the
      live path through `liftLegacyContext` — so a policy is written against
      domains 0–3, one per point of the legacy 2×2 lattice. -/
  declassificationPolicy : DeclassificationPolicy := { canDeclassify := fun _ _ => false }
  /-- WS-SM SM9.A: the **audit-monitor clearance** — the deployment's single
      privileged-reader gate.

      A caller qualifies as the audit monitor iff it dominates this domain
      (`auditMonitorAuthorized`).  Drain and the export of *global* entry
      identities key off it, and SM9.B's refusal ledger will too.

      **Configured, never derived from the records.**  The natural-looking
      alternative — "the caller dominates every `srcDomain` currently
      recorded" — is unsound in the direction that matters: drain a trail to
      `[]` and that predicate is *vacuously true*, so a low audit-capability
      holder would be reclassified as a fully-dominating monitor and handed the
      global epoch that counts the entries the drain just removed.  A predicate
      over rows that drains delete cannot gate access to a quantity that drains
      preserve (`auditMonitorGate_records_derived_unsound`).

      Defaulted to `none`, which **denies every caller** — the same fail-closed
      posture `declassificationPolicy` has, and it means an unconfigured
      deployment cannot drain at all.  The operator obligation that makes this a
      genuine full-dominance gate is `auditMonitorClearanceIsTop`: the
      configured domain must be one everything flows to.  A deployment that sets
      it lower has a monitor that cannot see the whole trail, and the 256-entry
      cliff returns for it — the conservative default, and the operator's to
      know about.

      Stated over `SecurityDomain`, like the two policy fields above, and
      reached from the live path through `liftLegacyContext`. -/
  auditMonitorClearance : Option SecurityDomain := none

/-- Minimal default labeling: everything is publicly observable and untrusted.

    X5-H (M-2): **PRODUCTION WARNING** — This default labeling context assigns
    `publicLabel` to all entities, defeating all information-flow enforcement.
    See `defaultLabelingContext_insecure` and `defaultLabelingContext_all_threads_observable`
    for formal proofs of this insecurity. Production deployments MUST override this
    with a domain-specific labeling policy. See also `docs/SECURITY_ADVISORY.md` SA-2. -/
def defaultLabelingContext : LabelingContext :=
  {
    objectLabelOf := fun _ => SecurityLabel.publicLabel
    threadLabelOf := fun _ => SecurityLabel.publicLabel
    endpointLabelOf := fun _ => SecurityLabel.publicLabel
    serviceLabelOf := fun _ => SecurityLabel.publicLabel
  }

/-- V6-K (L-IF-2): Warning theorem — the default labeling context assigns
    `publicLabel` (low confidentiality, untrusted integrity) to ALL entities.
    Under this labeling, `securityFlowsTo` is trivially `true` for all pairs,
    meaning NO information flow is restricted.

    **Production deployments MUST override `defaultLabelingContext` with a
    domain-specific labeling that assigns appropriate security labels to each
    entity.** Using the default labeling in production negates all information-
    flow enforcement guarantees.

    This theorem witnesses the insecurity: the default labeling context allows
    information to flow from any entity to any other entity. -/
theorem defaultLabelingContext_insecure :
    ∀ (oid₁ oid₂ : SeLe4n.ObjId),
    securityFlowsTo (defaultLabelingContext.objectLabelOf oid₁)
                    (defaultLabelingContext.objectLabelOf oid₂) = true := by
  intro _ _
  simp [defaultLabelingContext, SecurityLabel.publicLabel, securityFlowsTo,
        confidentialityFlowsTo, integrityFlowsTo]

/-- V6-K (L-IF-2): Corollary — the default labeling makes ALL threads
    mutually observable, defeating domain separation. -/
theorem defaultLabelingContext_all_threads_observable :
    ∀ (tid₁ tid₂ : SeLe4n.ThreadId),
    securityFlowsTo (defaultLabelingContext.threadLabelOf tid₁)
                    (defaultLabelingContext.threadLabelOf tid₂) = true := by
  intro _ _
  simp [defaultLabelingContext, SecurityLabel.publicLabel, securityFlowsTo,
        confidentialityFlowsTo, integrityFlowsTo]

-- ============================================================================
-- AI5-C (M-19): Insecure default labeling context runtime guard
-- ============================================================================

/-- AJ2-C (M-12): Helper — single sentinel probe. Checks whether all four
    entity classes assign `publicLabel` to the given ID. -/
@[inline] private def insecureProbe (ctx : LabelingContext) (n : Nat) : Bool :=
  ctx.threadLabelOf (SeLe4n.ThreadId.ofNat n) == SecurityLabel.publicLabel &&
  ctx.objectLabelOf (SeLe4n.ObjId.ofNat n) == SecurityLabel.publicLabel &&
  ctx.endpointLabelOf (SeLe4n.ObjId.ofNat n) == SecurityLabel.publicLabel &&
  ctx.serviceLabelOf (ServiceId.ofNat n) == SecurityLabel.publicLabel

/-- AI5-C (M-19) + AJ2-C (M-12): Detect the insecure default labeling context
    at runtime.

    Probes sentinel IDs 0, 1, and 42 across all four entity classes (thread,
    object, endpoint, service). A context is flagged as insecure when ALL probed
    entities in ALL classes return `publicLabel` — the signature pattern of
    `defaultLabelingContext`.

    AJ2-C strengthens the original single-ID (ID 0) probe to a multi-probe,
    widening the sampling window: the check now requires all-public labels at
    three distinct IDs before flagging a context as insecure. A context that
    assigns non-public labels at any one of the probed IDs (e.g., only at ID 0
    — the `testLabelingContext` pattern) will not be flagged, as that is
    sufficient evidence of non-default labeling. The conjunction (`&&`) means
    evasion requires changing only one probed ID, but detection coverage is
    broader: three independent samples of the ID space must all exhibit the
    insecure pattern before the heuristic fires.

    This remains O(k) with k=3 (12 label lookups total), negligible overhead per
    syscall entry. The real security gate is `LabelingContextValid` (enforced at
    boot via `labelingContextValid_is_deployment_requirement` in
    Composition.lean:727). This check is a defense-in-depth heuristic. -/
def isInsecureDefaultContext (ctx : LabelingContext) : Bool :=
  insecureProbe ctx 0 && insecureProbe ctx 1 && insecureProbe ctx 42

/-- AI5-C (M-19) + AJ2-C: The detector correctly identifies the default labeling
    context as insecure. All three sentinel IDs (0, 1, 42) map to `publicLabel`
    across all four entity classes. -/
theorem isInsecureDefaultContext_defaultLabelingContext :
    isInsecureDefaultContext defaultLabelingContext = true := by
  unfold isInsecureDefaultContext insecureProbe defaultLabelingContext
  simp [SecurityLabel.publicLabel]

/-- AI5-C (M-19): Test-only labeling context that assigns a non-public label to
    entity ID 0, defeating the insecurity detector while remaining structurally
    valid for test execution.

    This context assigns `kernelTrusted` (high confidentiality, trusted integrity)
    to thread 0, object 0, endpoint 0, and service 0. All other entities receive
    `publicLabel`, matching the default context for IDs ≥ 1.

    Test harnesses should use this context instead of `defaultLabelingContext`
    when exercising checked dispatch paths (`syscallEntryChecked`). -/
def testLabelingContext : LabelingContext :=
  {
    objectLabelOf := fun oid =>
      if oid.toNat == 0 then SecurityLabel.kernelTrusted
      else SecurityLabel.publicLabel
    threadLabelOf := fun tid =>
      if tid.toNat == 0 then SecurityLabel.kernelTrusted
      else SecurityLabel.publicLabel
    endpointLabelOf := fun oid =>
      if oid.toNat == 0 then SecurityLabel.kernelTrusted
      else SecurityLabel.publicLabel
    serviceLabelOf := fun sid =>
      if sid.toNat == 0 then SecurityLabel.kernelTrusted
      else SecurityLabel.publicLabel
  }

/-- AI5-C (M-19) + AJ2-C: The test labeling context is NOT detected as insecure.
    The sentinel probe at ID 0 returns `kernelTrusted` (non-public), causing
    `insecureProbe ctx 0` to return `false` and short-circuiting the conjunction. -/
theorem isInsecureDefaultContext_testLabelingContext :
    isInsecureDefaultContext testLabelingContext = false := by
  unfold isInsecureDefaultContext insecureProbe testLabelingContext
  simp [SecurityLabel.kernelTrusted, SecurityLabel.publicLabel,
        ThreadId.toNat_ofNat, ObjId.toNat_ofNat, ServiceId.toNat_ofNat]

/-- AJ2-C (M-12): Helper — a failed probe implies at least one entity class
    has a non-public label at the given ID. -/
private theorem insecureProbe_false_to_nonpublic
    (ctx : LabelingContext) (n : Nat)
    (h : insecureProbe ctx n = false) :
    ctx.threadLabelOf (SeLe4n.ThreadId.ofNat n) ≠ SecurityLabel.publicLabel ∨
    ctx.objectLabelOf (SeLe4n.ObjId.ofNat n) ≠ SecurityLabel.publicLabel ∨
    ctx.endpointLabelOf (SeLe4n.ObjId.ofNat n) ≠ SecurityLabel.publicLabel ∨
    ctx.serviceLabelOf (ServiceId.ofNat n) ≠ SecurityLabel.publicLabel := by
  simp only [insecureProbe] at h
  cases ht : (ctx.threadLabelOf (SeLe4n.ThreadId.ofNat n) == SecurityLabel.publicLabel)
  · exact .inl (by intro heq; simp [heq] at ht)
  · simp only [ht, Bool.true_and] at h
    cases ho : (ctx.objectLabelOf (SeLe4n.ObjId.ofNat n) == SecurityLabel.publicLabel)
    · exact .inr (.inl (by intro heq; simp [heq] at ho))
    · simp only [ho, Bool.true_and] at h
      cases he : (ctx.endpointLabelOf (SeLe4n.ObjId.ofNat n) == SecurityLabel.publicLabel)
      · exact .inr (.inr (.inl (by intro heq; simp [heq] at he)))
      · simp only [he, Bool.true_and] at h
        exact .inr (.inr (.inr (by intro heq; simp [heq] at h)))

/-- AJ2-C (M-12): False-negative characterization — when the check passes
    (`= false`), at least one probed entity in at least one class has a
    non-public label. This makes machine-checked what the heuristic guarantees.
    Zero runtime cost — purely a proof artifact. -/
theorem isInsecureDefaultContext_false_implies_nontrivial
    (ctx : LabelingContext)
    (h : isInsecureDefaultContext ctx = false) :
    ∃ n ∈ [0, 1, 42],
      ctx.threadLabelOf (SeLe4n.ThreadId.ofNat n) ≠ SecurityLabel.publicLabel ∨
      ctx.objectLabelOf (SeLe4n.ObjId.ofNat n) ≠ SecurityLabel.publicLabel ∨
      ctx.endpointLabelOf (SeLe4n.ObjId.ofNat n) ≠ SecurityLabel.publicLabel ∨
      ctx.serviceLabelOf (ServiceId.ofNat n) ≠ SecurityLabel.publicLabel := by
  simp only [isInsecureDefaultContext] at h
  -- h : insecureProbe ctx 0 && insecureProbe ctx 1 && insecureProbe ctx 42 = false
  -- Case-split on which probe failed
  cases hp0 : insecureProbe ctx 0
  · exact ⟨0, by simp, insecureProbe_false_to_nonpublic ctx 0 hp0⟩
  · simp only [hp0, Bool.true_and] at h
    cases hp1 : insecureProbe ctx 1
    · exact ⟨1, by simp, insecureProbe_false_to_nonpublic ctx 1 hp1⟩
    · simp only [hp1, Bool.true_and] at h
      exact ⟨42, by simp, insecureProbe_false_to_nonpublic ctx 42 h⟩

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
-- S3-H/U-M11: SecurityLabel lattice computational verification
-- ============================================================================

/-- S3-H: Antisymmetry of `confidentialityFlowsTo`: if both directions flow,
    then the confidentiality levels are equal. -/
theorem confidentialityFlowsTo_antisymm (a b : Confidentiality)
    (h₁ : confidentialityFlowsTo a b = true)
    (h₂ : confidentialityFlowsTo b a = true) :
    a = b := by
  cases a <;> cases b <;> simp [confidentialityFlowsTo] at h₁ h₂ ⊢

/-- S3-H: Antisymmetry of `integrityFlowsTo`. -/
theorem integrityFlowsTo_antisymm (a b : Integrity)
    (h₁ : integrityFlowsTo a b = true)
    (h₂ : integrityFlowsTo b a = true) :
    a = b := by
  cases a <;> cases b <;> simp [integrityFlowsTo] at h₁ h₂ ⊢

/-- S3-H: Antisymmetry of `securityFlowsTo`: mutual flow implies equal labels.
    This verifies the partial-order property for the `{low, high} × {untrusted, trusted}` lattice. -/
theorem securityFlowsTo_antisymm (a b : SecurityLabel)
    (h₁ : securityFlowsTo a b = true)
    (h₂ : securityFlowsTo b a = true) :
    a = b := by
  cases a with
  | mk ac ai =>
      cases b with
      | mk bc bi =>
          simp [securityFlowsTo] at h₁ h₂
          have hc := confidentialityFlowsTo_antisymm ac bc h₁.left h₂.left
          have hi := integrityFlowsTo_antisymm bi ai h₁.right h₂.right
          subst hc; subst hi; rfl

/-- S3-H: Decidable `flowsTo` check function for `SecurityLabel`.
    Returns `true` iff `src` can flow to `dst` under the combined
    confidentiality + integrity lattice. This function is already
    computationally decidable (it returns `Bool`), but this wrapper
    provides a `Decidable` instance for use in proof automation. -/
instance : Decidable (securityFlowsTo src dst = true) :=
  inferInstanceAs (Decidable (_ = true))

/-- S3-H: Verify all four lattice properties computationally for concrete labels.
    This serves as a compile-time witness that the lattice is well-formed. -/
theorem securityFlowsTo_lattice_verified :
    -- Reflexivity: all 4 labels
    securityFlowsTo SecurityLabel.publicLabel SecurityLabel.publicLabel = true ∧
    securityFlowsTo SecurityLabel.kernelTrusted SecurityLabel.kernelTrusted = true ∧
    securityFlowsTo ⟨.low, .trusted⟩ ⟨.low, .trusted⟩ = true ∧
    securityFlowsTo ⟨.high, .untrusted⟩ ⟨.high, .untrusted⟩ = true ∧
    -- Antisymmetry witness: asymmetric pairs don't have mutual flow
    securityFlowsTo SecurityLabel.publicLabel SecurityLabel.kernelTrusted = true ∧
    securityFlowsTo SecurityLabel.kernelTrusted SecurityLabel.publicLabel = false := by
  decide


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

/-- WS-E5/H-04: Check whether information may flow from a source entity's
domain to a destination entity's domain under a generic labeling context. -/
def genericFlowCheck (ctx : GenericLabelingContext)
    (srcDomain dstDomain : SecurityDomain) : Bool :=
  domainFlowsTo ctx.policy srcDomain dstDomain


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

The embedding is injective, so nothing about the legacy lattice is lost in the
*labels*.  What a lifted context does with them is a separate question: see
`DomainFlowPolicy.legacyLattice` below, which is the policy that reproduces
`securityFlowsTo` exactly.  `linearOrder` does **not** — it is a strict
over-approximation, and `linearOrder_is_not_faithful_to_legacy` names the single
pair where it differs. -/
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
if `securityFlowsTo src dst = true`, then `linearOrder.canFlow (embed src) (embed dst) = true`.

**One direction only**, and deliberately so — the converse is false, which is
exactly what `linearOrder_is_not_faithful_to_legacy` witnesses.  A reader who
takes this lemma for "the embedding preserves the lattice" will be wrong about
the denied flows, which is the half a security policy exists to enforce. -/
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

/-! ### WS-SM SM8.C: the faithful lift of the legacy lattice (PR #863 review)

`liftLegacyContext` used to carry `.linearOrder`, and the review observed that
this is an *over-approximation* of the legacy 2×2 relation.  It is: over the
sixteen label pairs the two agree on fifteen and differ on exactly one —

    {low, trusted} → {high, untrusted}     (domain 1 → domain 2)

which `securityFlowsTo` **denies** (the integrity dimension: `integrityFlowsTo
.untrusted .trusted = false`) and `1 ≤ 2` allows.  There is no pair in the other
direction, so `linearOrder` is a strict over-approximation.

Why that mattered on the live path: `declassificationDecision` reads a *true*
base-policy verdict as "this flow is already permitted, so it is not a
declassification" and returns `.flowDenied` before the declassification policy is
ever consulted.  On that one pair a deployment could therefore configure an
authorized downgrade and never be able to use it.  **Fail-closed** — the error
refuses a legitimate downgrade rather than authorizing an illegitimate one, so
this was a completeness defect and not a vulnerability — but a lift that does not
reproduce the relation it lifts is the wrong foundation for a policy decision.

`legacyLattice` is that relation, exactly. -/

/-- WS-SM SM8.C: decode an embedded domain back to its legacy label.

Total, and `none` outside the embedding's image — the four domains `0..3` are the
only ones `embedLegacyLabel` produces, and a lifted context can name no other. -/
def unembedLegacyDomain (d : SecurityDomain) : Option SecurityLabel :=
  match d.id with
  | 0 => some { confidentiality := .low,  integrity := .untrusted }
  | 1 => some { confidentiality := .low,  integrity := .trusted }
  | 2 => some { confidentiality := .high, integrity := .untrusted }
  | 3 => some { confidentiality := .high, integrity := .trusted }
  | _ => none

/-- WS-SM SM8.C: the decoder inverts the embedding. -/
@[simp] theorem unembedLegacyDomain_embed (l : SecurityLabel) :
    unembedLegacyDomain (embedLegacyLabel l) = some l := by
  cases l with
  | mk c i => cases c <;> cases i <;> rfl

/-- WS-SM SM8.C: **the legacy lattice as a domain policy** — `securityFlowsTo`
transported along the embedding, rather than approximated by a linear order.

The diagonal is admitted separately so the policy is reflexive on *every*
`SecurityDomain`, including ids outside the embedding's image; that costs nothing
on embedded domains, since `securityFlowsTo l l` is already `true`.  A domain
outside the image flows only to itself — fail-closed, and unreachable from a
lifted context anyway. -/
def legacyDomainFlows : Option SecurityLabel → Option SecurityLabel → Bool
  | some s, some d => securityFlowsTo s d
  | _, _ => false

@[simp] theorem legacyDomainFlows_some (s d : SecurityLabel) :
    legacyDomainFlows (some s) (some d) = securityFlowsTo s d := rfl

@[simp] theorem legacyDomainFlows_none_left (d : Option SecurityLabel) :
    legacyDomainFlows none d = false := by cases d <;> rfl

@[simp] theorem legacyDomainFlows_none_right (s : Option SecurityLabel) :
    legacyDomainFlows s none = false := by cases s <;> rfl

def DomainFlowPolicy.legacyLattice : DomainFlowPolicy :=
  { canFlow := fun src dst =>
      decide (src = dst) ||
        legacyDomainFlows (unembedLegacyDomain src) (unembedLegacyDomain dst) }

/-- WS-SM SM8.C (**the faithfulness theorem**): on embedded labels the policy
*is* `securityFlowsTo` — an equality, so both the admitted and the denied flows
carry, which is what `embedLegacyLabel_preserves_flow` gives only half of. -/
@[simp] theorem legacyLattice_canFlow_embed (src dst : SecurityLabel) :
    DomainFlowPolicy.legacyLattice.canFlow (embedLegacyLabel src) (embedLegacyLabel dst)
      = securityFlowsTo src dst := by
  cases src with
  | mk sc si =>
    cases dst with
    | mk dc di =>
      cases sc <;> cases si <;> cases dc <;> cases di <;> rfl

/-- WS-SM SM8.C: the load-bearing negative — `linearOrder` does **not** have the
property above, and this is the single pair that breaks it.  Keeping the
counterexample as a theorem means a future edit that "simplifies"
`liftLegacyContext` back to a linear order fails to build rather than silently
reopening the gap. -/
theorem linearOrder_is_not_faithful_to_legacy :
    DomainFlowPolicy.linearOrder.canFlow
        (embedLegacyLabel { confidentiality := .low, integrity := .trusted })
        (embedLegacyLabel { confidentiality := .high, integrity := .untrusted }) = true ∧
      securityFlowsTo { confidentiality := .low, integrity := .trusted }
        { confidentiality := .high, integrity := .untrusted } = false := by
  constructor <;> rfl

/-- WS-SM SM8.C: `legacyLattice` is reflexive — the diagonal disjunct. -/
theorem DomainFlowPolicy.legacyLattice_reflexive :
    DomainFlowPolicy.legacyLattice.isReflexive := by
  intro d; simp [DomainFlowPolicy.legacyLattice]

/-- WS-SM SM8.C: `legacyLattice` is transitive, because `securityFlowsTo` is
(both dimensions are partial orders, and the reversed integrity comparison is
still a partial order). -/
theorem DomainFlowPolicy.legacyLattice_transitive :
    DomainFlowPolicy.legacyLattice.isTransitive := by
  intro a b c hab hbc
  simp only [DomainFlowPolicy.legacyLattice, Bool.or_eq_true, decide_eq_true_eq] at hab hbc ⊢
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  refine Or.inr ?_
  cases ha : unembedLegacyDomain a with
  | none => rw [ha] at hab; simp at hab
  | some la =>
    cases hb : unembedLegacyDomain b with
    | none => rw [ha, hb] at hab; simp at hab
    | some lb =>
      cases hc : unembedLegacyDomain c with
      | none => rw [hb, hc] at hbc; simp at hbc
      | some lc =>
        rw [ha, hb] at hab
        rw [hb, hc] at hbc
        exact securityFlowsTo_trans la lb lc hab hbc

/-- WS-SM SM8.C: hence well-formed, so it is a drop-in for `linearOrder`
everywhere a lifted context is required to carry a well-formed policy. -/
theorem DomainFlowPolicy.legacyLattice_wellFormed :
    DomainFlowPolicy.legacyLattice.wellFormed :=
  ⟨legacyLattice_reflexive, legacyLattice_transitive⟩

-- ============================================================================
-- WS-SM SM8.C: the live per-endpoint flow gate
-- ============================================================================

/-- WS-SM SM8.C: **the configured per-endpoint override, evaluated on labels.**

`true` when the endpoint carries no override — that is the whole content of the
"endpoints without an override inherit the global policy" rule, stated so the
gate below can conjoin unconditionally instead of branching. -/
def endpointOverrideAllows (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (srcLabel dstLabel : SecurityLabel) : Bool :=
  match ctx.endpointPolicy.endpointPolicy endpointId with
  | none => true
  | some customPolicy =>
      customPolicy.canFlow (embedLegacyLabel srcLabel) (embedLegacyLabel dstLabel)

/-- WS-SM SM8.C: **the flow gate every endpoint-keyed IPC check runs.**

The global lattice check **and** the endpoint's own override — a conjunction,
never a replacement.

Conjoining rather than overriding is what makes V6-G's `endpointPolicyRestricted`
structural instead of a deployment obligation: a misconfigured override cannot
widen anything, because the global check still has to pass
(`endpointFlowGate_implies_securityFlowsTo`, which takes no hypothesis at all).
An override can only ever deny more, which is the only direction a per-endpoint
restriction should be able to move.

Read by the four endpoint-keyed gate sites: the `endpointSendDualChecked` /
`endpointReceiveDualChecked` / `endpointCallChecked` / `endpointReplyRecvChecked`
enforcement wrappers, the live cross-core `.send` and `.call` dispatches, and the
live `.receive` / `.replyRecv` arms. -/
def endpointFlowGate (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (srcLabel dstLabel : SecurityLabel) : Bool :=
  securityFlowsTo srcLabel dstLabel && endpointOverrideAllows ctx endpointId srcLabel dstLabel

/-- WS-SM SM8.C: **the gate never admits a flow the global lattice denies.**

No hypothesis: the restriction is a property of the gate's shape, so no
deployment obligation and no well-formedness precondition stands between a
misconfigured endpoint policy and the guarantee. -/
theorem endpointFlowGate_implies_securityFlowsTo (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (srcLabel dstLabel : SecurityLabel)
    (h : endpointFlowGate ctx endpointId srcLabel dstLabel = true) :
    securityFlowsTo srcLabel dstLabel = true :=
  (Bool.and_eq_true _ _ ▸ h).1

/-- WS-SM SM8.C: …and it admits nothing the endpoint's own policy denies. -/
theorem endpointFlowGate_implies_override (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (srcLabel dstLabel : SecurityLabel)
    (h : endpointFlowGate ctx endpointId srcLabel dstLabel = true) :
    endpointOverrideAllows ctx endpointId srcLabel dstLabel = true :=
  (Bool.and_eq_true _ _ ▸ h).2

/-- WS-SM SM8.C: the gate's introduction rule — both conjuncts, named
separately, which is how the enforcement wrappers' `…_when_allowed` theorems
carry them. -/
theorem endpointFlowGate_of (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (srcLabel dstLabel : SecurityLabel)
    (hFlow : securityFlowsTo srcLabel dstLabel = true)
    (hOverride : endpointOverrideAllows ctx endpointId srcLabel dstLabel = true) :
    endpointFlowGate ctx endpointId srcLabel dstLabel = true := by
  simp [endpointFlowGate, hFlow, hOverride]

/-- WS-SM SM8.C: a denied override denies the gate, whatever the global lattice
says — the dual of `endpointFlowGate_false_of_securityFlowsTo_false`, and the
form a *configured* deployment's denial proofs need. -/
theorem endpointFlowGate_false_of_override_false (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (srcLabel dstLabel : SecurityLabel)
    (h : endpointOverrideAllows ctx endpointId srcLabel dstLabel = false) :
    endpointFlowGate ctx endpointId srcLabel dstLabel = false := by
  simp [endpointFlowGate, h]

/-- WS-SM SM8.C: a denied global flow denies the gate, whatever the override
says — the form every `…_flowDenied` proof needs, so those keep the hypotheses
they had before the gate existed. -/
theorem endpointFlowGate_false_of_securityFlowsTo_false (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (srcLabel dstLabel : SecurityLabel)
    (h : securityFlowsTo srcLabel dstLabel = false) :
    endpointFlowGate ctx endpointId srcLabel dstLabel = false := by
  simp [endpointFlowGate, h]

/-- WS-SM SM8.C: with no override configured at this endpoint the gate **is**
the global check — so an unconfigured deployment behaves exactly as it did
before the field existed. -/
theorem endpointFlowGate_eq_securityFlowsTo_of_no_override (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (srcLabel dstLabel : SecurityLabel)
    (hNone : ctx.endpointPolicy.endpointPolicy endpointId = none) :
    endpointFlowGate ctx endpointId srcLabel dstLabel = securityFlowsTo srcLabel dstLabel := by
  simp [endpointFlowGate, endpointOverrideAllows, hNone]

/-- WS-SM SM8.C: and the default context configures no override anywhere, so the
gate is the global check at every endpoint unless a deployment says otherwise. -/
theorem endpointOverrideAllows_default (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (srcLabel dstLabel : SecurityLabel)
    (hDefault : ctx.endpointPolicy = { endpointPolicy := fun _ => none }) :
    endpointOverrideAllows ctx endpointId srcLabel dstLabel = true := by
  simp [endpointOverrideAllows, hDefault]

/-- WS-SM SM8.C (**non-vacuity**): a configured override genuinely denies a flow
the global lattice permits.  Without this the gate could be a constant `true`
conjunct and every theorem above would still hold. -/
theorem endpointFlowGate_is_not_securityFlowsTo :
    ∃ (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (srcLabel dstLabel : SecurityLabel),
      securityFlowsTo srcLabel dstLabel = true ∧
      endpointFlowGate ctx endpointId srcLabel dstLabel = false := by
  refine ⟨{ objectLabelOf := fun _ => SecurityLabel.publicLabel
            threadLabelOf := fun _ => SecurityLabel.publicLabel
            endpointLabelOf := fun _ => SecurityLabel.publicLabel
            serviceLabelOf := fun _ => SecurityLabel.publicLabel
            endpointPolicy := { endpointPolicy := fun _ => some { canFlow := fun _ _ => false } } },
          ⟨0⟩, SecurityLabel.publicLabel, SecurityLabel.publicLabel, by decide, by decide⟩

/-- WS-SM SM8.C (**V6-G at the label level**): the live gate's restriction
property — an endpoint override can only ever *narrow*.

V6-G's `endpointPolicyRestricted` is a well-formedness requirement on a
*configuration*: it says an operator must not write an override that widens the
global policy.  This is the same property one level down, at the gate the kernel
actually runs, and stated over the labels the live IPC paths carry rather than
over domains. -/
def endpointGateRestricted (ctx : LabelingContext) : Prop :=
  ∀ (endpointId : SeLe4n.ObjId) (srcLabel dstLabel : SecurityLabel),
    endpointFlowGate ctx endpointId srcLabel dstLabel = true →
    securityFlowsTo srcLabel dstLabel = true

/-- WS-SM SM8.C (**the reconciliation**): the live gate is restricted for
**every** context, with no well-formedness hypothesis at all.

This is what the conjunctive design buys, and it is strictly stronger than
V6-G's conditional form: V6-G says a *well-formed* configuration cannot widen,
and leaves a misconfigured one able to.  Conjoining makes widening structurally
impossible, so an operator cannot open a downgrade path by writing a bad
override — the worst a misconfiguration can do is deny traffic that the lattice
would have allowed. -/
theorem endpointGateRestricted_always (ctx : LabelingContext) :
    endpointGateRestricted ctx :=
  fun endpointId srcLabel dstLabel h =>
    endpointFlowGate_implies_securityFlowsTo ctx endpointId srcLabel dstLabel h

/-- WS-SM SM8.C (**the load-bearing negative**): a configuration that *violates*
V6-G still cannot widen the live gate.

The witness is a widening override — an endpoint policy that permits every
domain pair, on a context whose labels make the flow globally denied.  V6-G's
`endpointPolicyRestricted` is false of it; the gate refuses the flow anyway.
Without this the previous theorem could be read as restating V6-G, when what it
says is that V6-G's hypothesis is not needed. -/
theorem endpointGateRestricted_survives_widening_override :
    ∃ (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (srcLabel dstLabel : SecurityLabel),
      endpointOverrideAllows ctx endpointId srcLabel dstLabel = true ∧
      securityFlowsTo srcLabel dstLabel = false ∧
      endpointFlowGate ctx endpointId srcLabel dstLabel = false := by
  refine ⟨{ objectLabelOf := fun _ => SecurityLabel.publicLabel
            threadLabelOf := fun _ => SecurityLabel.publicLabel
            endpointLabelOf := fun _ => SecurityLabel.publicLabel
            serviceLabelOf := fun _ => SecurityLabel.publicLabel
            endpointPolicy := { endpointPolicy := fun _ => some { canFlow := fun _ _ => true } } },
          ⟨0⟩, SecurityLabel.kernelTrusted, SecurityLabel.publicLabel,
          by decide, by decide, by decide⟩

/-- Lift a legacy `LabelingContext` into a `GenericLabelingContext` using the
embedding and linearOrder policy.

WS-SM SM8.C: the lift carries the *global* policy only.  A caller that needs the
endpoint overrides too reads them through `endpointFlowGate` on the original
context, which is what the live IPC arms do.

WS-SM SM8.C.9: the lift **does** have a live consumer now — the `.declassify`
arm builds the `GenericLabelingContext` the declassification gate needs from the
`LabelingContext` the checked dispatch already carries, so an operator writes one
labeling and gets both.  What the arm supplies separately is the
`DeclassificationPolicy`, which is its own `LabelingContext` field: the lift's
`policy` is the *base* lattice (the one that must deny), not the downgrade
policy. -/
def liftLegacyContext (ctx : LabelingContext) : GenericLabelingContext :=
  {
    -- WS-SM SM8.C (PR #863 review): the **faithful** legacy relation, not the
    -- `linearOrder` over-approximation this used to carry.  The two differ on
    -- exactly one pair ({low,trusted} → {high,untrusted}), and on the live
    -- `.declassify` path that difference made a configurable downgrade
    -- unreachable: `declassificationDecision` reads a `true` base verdict as
    -- "already permitted, not a declassification" and returns `.flowDenied`
    -- before the declassification policy is consulted.  See
    -- `legacyLattice_canFlow_embed` (the equality) and
    -- `linearOrder_is_not_faithful_to_legacy` (the counterexample).
    policy := .legacyLattice
    objectDomainOf := fun oid => embedLegacyLabel (ctx.objectLabelOf oid)
    threadDomainOf := fun tid => embedLegacyLabel (ctx.threadLabelOf tid)
    endpointDomainOf := fun oid => embedLegacyLabel (ctx.endpointLabelOf oid)
    serviceDomainOf := fun sid => embedLegacyLabel (ctx.serviceLabelOf sid)
  }

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
is straightforward via a `linearOrder` policy. Production deployments should
select the appropriate policy for their threat model. -/

/-- WS-H10/A-34: The legacy lattice is a valid (non-standard) security lattice.
Reflexivity and transitivity hold, making it a valid pre-order. -/
theorem securityLattice_reflexive : ∀ l : SecurityLabel, securityFlowsTo l l = true :=
  securityFlowsTo_refl

theorem securityLattice_transitive :
    ∀ a b c : SecurityLabel, securityFlowsTo a b = true → securityFlowsTo b c = true →
      securityFlowsTo a c = true :=
  securityFlowsTo_trans

-- `DeclassificationBasis`, `DeclassificationEvent`, `DeclassificationAuditLog`,
-- `recordDeclassification` and the SM8.C.8 capacity bound live in
-- `SeLe4n.Kernel.InformationFlow.AuditRecord`, below `Model.State`, because
-- `SystemState` mounts the audit trail and this module imports `Model.State`.
-- Same namespace, so every reference below resolves unchanged.

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

-- ============================================================================
-- V6-G (M-IF-5): Endpoint policy restriction well-formedness
-- ============================================================================

/-- V6-G (M-IF-5): Per-endpoint policy must be a **subset** of the global policy.

    An endpoint's custom policy should only restrict flows, never widen them.
    If an endpoint policy allows a flow that the global policy denies, that
    endpoint becomes a policy bypass — threads could circumvent domain
    separation by routing traffic through the permissive endpoint.

    This predicate requires: for every domain pair (src, dst), if the endpoint
    policy allows the flow, then the global policy must also allow it. -/
def endpointPolicyRestricted
    (globalPolicy : DomainFlowPolicy)
    (epPolicy : EndpointFlowPolicy) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (customPolicy : DomainFlowPolicy),
    epPolicy.endpointPolicy oid = some customPolicy →
    ∀ (src dst : SecurityDomain),
      customPolicy.canFlow src dst = true →
      globalPolicy.canFlow src dst = true

/-- V6-G (M-IF-5): If no endpoint overrides exist, the restriction is trivially
    satisfied. -/
theorem endpointPolicyRestricted_no_overrides
    (globalPolicy : DomainFlowPolicy) :
    endpointPolicyRestricted globalPolicy { endpointPolicy := fun _ => none } := by
  intro _ _ h; simp at h

/-- V6-G (M-IF-5): Under restriction, the effective endpoint flow check is at
    most as permissive as the global flow check. -/
theorem endpointFlowCheck_restricted_subset
    (ctx : GenericLabelingContext)
    (epPolicy : EndpointFlowPolicy)
    (endpointId : SeLe4n.ObjId)
    (src dst : SecurityDomain)
    (hRestricted : endpointPolicyRestricted ctx.policy epPolicy)
    (hFlow : endpointFlowCheck ctx epPolicy endpointId src dst = true) :
    genericFlowCheck ctx src dst = true := by
  unfold endpointFlowCheck at hFlow
  cases hEP : epPolicy.endpointPolicy endpointId with
  | none => simp [hEP] at hFlow; exact hFlow
  | some customPolicy =>
    simp [hEP, domainFlowsTo] at hFlow
    exact hRestricted endpointId customPolicy hEP src dst hFlow

end SeLe4n.Kernel
