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
import SeLe4n.Kernel.Scheduler.IdleThread

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

/-- WS-RR RR5.1: the low-confidentiality, trusted-integrity corner of the 2×2
    lattice.

    Together with `highUntrusted` this is the **only** pair of lattice points
    that are mutually non-flowing (`lowTrusted_highUntrusted_mutually_isolated`),
    so a deployment that wants two genuinely isolated domains out of the legacy
    lattice has to use exactly these two.  `publicLabel` / `kernelTrusted` are
    *comparable* (`publicLabel → kernelTrusted` is permitted by design), so a
    partition into those two confines information in one direction only. -/
def lowTrusted : SecurityLabel :=
  { confidentiality := .low, integrity := .trusted }

/-- WS-RR RR5.1: the high-confidentiality, untrusted-integrity corner of the
    2×2 lattice — the isolation partner of `lowTrusted` (see there). -/
def highUntrusted : SecurityLabel :=
  { confidentiality := .high, integrity := .untrusted }

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

/-- WS-RR RR5.1: `lowTrusted` and `highUntrusted` are **mutually** non-flowing —
    neither direction is permitted.

    This is what makes them the pair a two-domain production deployment is built
    from.  `publicLabel` / `kernelTrusted` confine in one direction only
    (`securityFlowsTo_prevents_label_escalation`: the upward flow is permitted by
    design), so a partition into those two leaves every low entity able to write
    into every high one.  Here the confidentiality dimension denies
    `highUntrusted → lowTrusted` and the integrity dimension denies
    `lowTrusted → highUntrusted`, so the two domains cannot observe or influence
    each other at all.

    The four points of the lattice admit exactly one such pair: the two
    *incomparable* corners.  `confinedLabelingContext` is the deployment
    labeling built from it. -/
theorem lowTrusted_highUntrusted_mutually_isolated :
    securityFlowsTo SecurityLabel.lowTrusted SecurityLabel.highUntrusted = false ∧
    securityFlowsTo SecurityLabel.highUntrusted SecurityLabel.lowTrusted = false := by
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
  /-- WS-RR RR5.4: the deployment's **declared domain-separation witness** — two
      admissible thread ids (`separationWitnessAdmissible`: neither the reserved
      sentinel nor a per-core idle thread) this labeling puts in different
      security domains.

      `LabelingContextValid.labelNonTriviality` asks for exactly this
      existential (`∃ tid₁ tid₂, threadLabelOf tid₁ ≠ threadLabelOf tid₂`), and
      before this field the kernel had no way to *check* it: a label assignment
      is a total function over an infinite id space, so no runtime test can
      decide non-triviality by inspecting it.  The pre-RR5 guard therefore
      sampled three sentinel ids and reported "not the default" whenever any one
      of them came back non-public — which `testLabelingContext` satisfies by
      labeling id `0` alone, while every real entity stays `publicLabel`.

      Making the witness **data** turns the undecidable question into a decided
      one: the deployment names the pair, and `isInsecureDefaultContext`
      evaluates the very inequality `labelNonTriviality` asserts at it.  A false
      declaration is caught (the labels are compared, not trusted), and the two
      ids must be admissible (`separationWitnessAdmissible`): not the sentinel
      `0` — which `toObjIdChecked` refuses to turn into an object reference — and
      not a per-core idle thread, because separating either from the real
      threads separates no two things a flow decision can observe.

      Defaulted to `none`, which is **fail-closed**: a context that declares no
      separation is rejected at every checked syscall entry and at boot.  That is
      the posture the pre-boot `kernelLabelingContextRef` value now has, so no
      syscall can be served before a deployment context is installed.

      What this decides and what it does not: `isInsecureDefaultContext ctx =
      false` proves the labeling is not the one-label labeling
      (`isInsecureDefaultContext_false_implies_labelNonTriviality`).  Whether the
      partition it declares is the *right* one for the deployment's threads
      remains the integrator's obligation, stated by the other two
      `LabelingContextValid` conjuncts and discharged structurally by
      `deploymentLabelingContext`. -/
  separatedThreads : Option (SeLe4n.ThreadId × SeLe4n.ThreadId) := none

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

/-- WS-RR RR5.4: may `tid` stand as one side of a deployment's declared
    separation witness?

    Two exclusions, for the same reason: the reserved sentinel `0`
    (`ThreadId.isReserved`) never runs, and a per-core idle thread
    (`isIdleThreadId`, `Scheduler/IdleThread.lean`) is kernel-owned — it issues
    no syscall and sends no message — so a labeling that differs only on them
    separates no two threads a flow decision can tell apart.  Without the second
    exclusion a labeling that gave the four idle threads a label of their own and
    every user-visible entity `publicLabel` would name two idle threads and pass
    the guard, which is the all-public shape RR5.4 exists to refuse, one range
    higher up. -/
def separationWitnessAdmissible (tid : SeLe4n.ThreadId) : Bool :=
  !tid.isReserved && !isIdleThreadId tid

/-- WS-RR RR5.4: admissibility, as the arithmetic it decides — the form the
    constructors below discharge by `omega`. -/
theorem separationWitnessAdmissible_iff (tid : SeLe4n.ThreadId) :
    separationWitnessAdmissible tid = true ↔
      tid.toNat ≠ 0 ∧
        (tid.toNat < idleThreadIdBase ∨
          idleThreadIdBase + SeLe4n.Kernel.Concurrency.numCores ≤ tid.toNat) := by
  simp only [separationWitnessAdmissible, isIdleThreadId, SeLe4n.ThreadId.isReserved,
    SeLe4n.ThreadId.toNat, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, Nat.not_le, Nat.not_lt, ne_eq]

/-- WS-RR RR5.4: an admissible witness is not the reserved sentinel. -/
theorem separationWitnessAdmissible_not_reserved (tid : SeLe4n.ThreadId)
    (h : separationWitnessAdmissible tid = true) : tid.isReserved = false := by
  simp only [separationWitnessAdmissible, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1

/-- WS-RR RR5.4: an admissible witness is not an idle thread. -/
theorem separationWitnessAdmissible_not_idle (tid : SeLe4n.ThreadId)
    (h : separationWitnessAdmissible tid = true) : isIdleThreadId tid = false := by
  simp only [separationWitnessAdmissible, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

/-- WS-RR RR5.4 (negative fixture): no idle thread is admissible — the exclusion
    is exact on the ids `idleThreadId` produces. -/
theorem separationWitnessAdmissible_idleThreadId (c : SeLe4n.Kernel.Concurrency.CoreId) :
    separationWitnessAdmissible (idleThreadId c) = false := by
  simp only [separationWitnessAdmissible, isIdleThreadId_idleThreadId, Bool.not_true,
    Bool.and_false]

/-- WS-RR RR5.4: does `ctx` *verify* its declared domain-separation witness?

    `true` exactly when the context names a pair of admissible thread ids
    (`LabelingContext.separatedThreads`) that it really does put in different
    security domains.  Three conditions, all decided rather than sampled:

    1. a witness is declared at all (`none` is fail-closed);
    2. both ids are admissible (`separationWitnessAdmissible`): neither is the
       reserved sentinel `0` — a labeling that separates only the sentinel from
       everything else separates no two threads that can run, which is precisely
       the `testLabelingContext` shape the pre-RR5 sentinel probe accepted — and
       neither is a per-core idle thread, which runs but never originates or
       receives a flow; and
    3. the two ids genuinely carry different labels — the declaration is
       *checked*, so a context cannot pass by naming a pair it does not separate.

    O(1): one `Option` match, two range checks and one `SecurityLabel`
    comparison, against the twelve label lookups the retired three-sentinel probe
    performed at every syscall entry. -/
def verifiesDeclaredSeparation (ctx : LabelingContext) : Bool :=
  match ctx.separatedThreads with
  | none => false
  | some (tid₁, tid₂) =>
      separationWitnessAdmissible tid₁ && separationWitnessAdmissible tid₂ &&
        ctx.threadLabelOf tid₁ != ctx.threadLabelOf tid₂

/-- AI5-C (M-19) + AJ2-C (M-12) + **WS-RR RR5.4**: reject a labeling context that
    provides no domain separation.

    **What changed at RR5.4.**  This was a three-sentinel *sample*: it probed ids
    `0`, `1` and `42` across the four entity classes and reported "insecure" only
    when all twelve lookups came back `publicLabel`.  A sample cannot decide a
    property of a total function, and the gap was not hypothetical —
    `testLabelingContext` labels id `0` `kernelTrusted` and every other entity
    `publicLabel`, so probe `0` failed, the conjunction short-circuited, and the
    guard passed the very context the pre-boot labeling reference held.  Every
    flow between entities that can actually run was permitted, which makes the
    SM8/SM9 non-interference and declassification results vacuous in that
    configuration.

    It is now the **exact** check `verifiesDeclaredSeparation` describes: the
    deployment declares which two admissible threads its labeling separates and
    the kernel evaluates that inequality.  A context that declares nothing is
    rejected (fail-closed), and one that declares a pair it does not separate is
    rejected too.

    `isInsecureDefaultContext ctx = false` is therefore no longer a heuristic
    "probably not the default": it *entails*
    `LabelingContextValid.labelNonTriviality`
    (`isInsecureDefaultContext_false_implies_labelNonTriviality`), so the runtime
    guard now discharges one of the three deployment obligations rather than
    approximating it.  The other two — thread/object coherence and its
    observability corollary — remain deployment obligations, discharged
    structurally by `deploymentLabelingContext` rather than assumed. -/
def isInsecureDefaultContext (ctx : LabelingContext) : Bool :=
  !verifiesDeclaredSeparation ctx

/-- AI5-C (M-19) + WS-RR RR5.4: the default labeling context is rejected — it
    declares no separation witness, and could not declare a true one: every
    thread carries `publicLabel`. -/
theorem isInsecureDefaultContext_defaultLabelingContext :
    isInsecureDefaultContext defaultLabelingContext = true := by
  decide

/-- WS-RR RR5.4: a *stronger* statement than the rejection above — the default
    labeling context could not be repaired by declaring a witness, because no
    two threads carry different labels.  The rejection is a fact about the
    labeling, not about the missing declaration. -/
theorem defaultLabelingContext_separates_no_threads
    (tid₁ tid₂ : SeLe4n.ThreadId) :
    defaultLabelingContext.threadLabelOf tid₁ =
      defaultLabelingContext.threadLabelOf tid₂ := rfl

/-- AI5-C (M-19), retained as a **negative fixture** by WS-RR RR5.4: the
    all-public-except-the-sentinel labeling.

    It assigns `kernelTrusted` to thread `0`, object `0`, endpoint `0` and
    service `0`, and `publicLabel` to every other entity.  Id `0` is the reserved
    sentinel (`ThreadId.isReserved`; `toObjIdChecked` refuses to turn it into an
    object reference), so *no two entities that can run* are separated: every
    flow between real threads, objects, endpoints and services is permitted, and
    the non-interference results hold vacuously under it.

    Its original purpose was to defeat the sentinel-probe guard while staying
    structurally usable in tests.  RR5.4 removed that possibility: the guard now
    checks a declared witness, this context declares none, and
    `isInsecureDefaultContext_testLabelingContext` pins the rejection.  It is
    kept — rather than deleted — because a fail-closed guard needs a fixture that
    exercises the closed side, and because the pre-RR5 shape is the one a future
    contributor is most likely to reintroduce.

    **Test harnesses must not use it to reach a checked entry.**  A checked path
    exercised under a genuinely separated deployment labeling is
    `harnessLabelingContext`; a two-domain production labeling is
    `confinedLabelingContext`. -/
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

/-- WS-RR RR5.5 (the closing half): the all-public-except-the-sentinel context is
    **rejected**.  Under the retired sentinel probe this theorem read `= false` —
    the guard passed it — which is the fail-open the phase exists to close. -/
theorem isInsecureDefaultContext_testLabelingContext :
    isInsecureDefaultContext testLabelingContext = true := by
  decide

/-- WS-RR RR5.4: why the rejection above is a fact about the labeling and not
    about a missing declaration — the only pair of ids `testLabelingContext`
    separates involves the reserved sentinel.  Stated contrapositively: any two
    **non-sentinel** threads carry the same label under it, so no witness it
    could declare would be admissible. -/
theorem testLabelingContext_separates_no_real_threads
    (tid₁ tid₂ : SeLe4n.ThreadId)
    (h₁ : tid₁.isReserved = false) (h₂ : tid₂.isReserved = false) :
    testLabelingContext.threadLabelOf tid₁ = testLabelingContext.threadLabelOf tid₂ := by
  simp only [SeLe4n.ThreadId.isReserved, decide_eq_false_iff_not] at h₁ h₂
  simp only [testLabelingContext, SeLe4n.ThreadId.toNat]
  rw [if_neg (by simpa using h₁), if_neg (by simpa using h₂)]

/-- WS-RR RR5.4: the guard **decides** `LabelingContextValid.labelNonTriviality`.

    This replaces the pre-RR5 false-negative characterization, which could only
    say that one of three sampled ids carried a non-public label in one of four
    classes.  The conclusion here is the `LabelingContextValid` conjunct itself,
    so a context the runtime guard admits carries that deployment obligation
    already discharged. -/
theorem isInsecureDefaultContext_false_implies_labelNonTriviality
    (ctx : LabelingContext)
    (h : isInsecureDefaultContext ctx = false) :
    ∃ (tid₁ tid₂ : SeLe4n.ThreadId), ctx.threadLabelOf tid₁ ≠ ctx.threadLabelOf tid₂ := by
  simp only [isInsecureDefaultContext, Bool.not_eq_false', verifiesDeclaredSeparation] at h
  cases hw : ctx.separatedThreads with
  | none => rw [hw] at h; exact absurd h (by simp)
  | some p =>
      rw [hw] at h
      obtain ⟨tid₁, tid₂⟩ := p
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact ⟨tid₁, tid₂, h.2⟩

/-- WS-RR RR5.4: the admitted witness is a pair of **admissible** threads —
    neither the reserved sentinel nor an idle thread.  The companion to the
    theorem above: a labeling admitted by the guard separates two threads a flow
    decision can observe, not the reserved id `0` or the kernel's own idle
    threads from everything else. -/
theorem isInsecureDefaultContext_false_implies_real_witness
    (ctx : LabelingContext)
    (h : isInsecureDefaultContext ctx = false) :
    ∃ (tid₁ tid₂ : SeLe4n.ThreadId),
      separationWitnessAdmissible tid₁ = true ∧ separationWitnessAdmissible tid₂ = true ∧
      ctx.threadLabelOf tid₁ ≠ ctx.threadLabelOf tid₂ := by
  simp only [isInsecureDefaultContext, Bool.not_eq_false', verifiesDeclaredSeparation] at h
  cases hw : ctx.separatedThreads with
  | none => rw [hw] at h; exact absurd h (by simp)
  | some p =>
      rw [hw] at h
      obtain ⟨tid₁, tid₂⟩ := p
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact ⟨tid₁, tid₂, h.1.1, h.1.2, h.2⟩

/-- WS-RR RR5.4 (audit): the admitted witness names **no idle thread** — the
    guarantee `separationWitnessAdmissible`'s second exclusion buys, stated on the
    guard's output so a consumer need not unfold the predicate. -/
theorem isInsecureDefaultContext_false_implies_witness_not_idle
    (ctx : LabelingContext)
    (h : isInsecureDefaultContext ctx = false) :
    ∃ (tid₁ tid₂ : SeLe4n.ThreadId),
      isIdleThreadId tid₁ = false ∧ isIdleThreadId tid₂ = false ∧
      ctx.threadLabelOf tid₁ ≠ ctx.threadLabelOf tid₂ := by
  obtain ⟨tid₁, tid₂, h₁, h₂, hne⟩ := isInsecureDefaultContext_false_implies_real_witness ctx h
  exact ⟨tid₁, tid₂, separationWitnessAdmissible_not_idle tid₁ h₁,
    separationWitnessAdmissible_not_idle tid₂ h₂, hne⟩

-- ============================================================================
-- WS-RR RR5.1: production labeling contexts, valid by construction
-- ============================================================================

/-- WS-RR RR5.1: the label assignment a deployment supplies, together with the
    obligations that make the resulting `LabelingContext`
    `LabelingContextValid` — discharged at *construction* rather than assumed by
    every theorem downstream.

    Before RR5.1 there was no production labeling context anywhere in the tree:
    `defaultLabelingContext` labels everything `publicLabel`,
    `testLabelingContext` labels everything but the sentinel `publicLabel`, and
    the three `LabelingContextValid` conjuncts were carried as hypotheses that
    no artefact discharged.  A deployment therefore had to hand-write a record
    *and* hand-prove its validity, and nothing checked that it had.

    The fields:

    * `entityLabelOf` assigns a label per **entity index**, and the constructor
      uses it for both `threadLabelOf` and `objectLabelOf`.  That is what makes
      `LabelingContextValid.threadObjectCoherence` hold by reflexivity:
      `ThreadId.toObjId` is the identity on the index, so a thread and its own
      TCB object necessarily carry the same label and `securityFlowsTo l l` is
      `true`.  A deployment that wants a TCB object at a *different* label than
      its thread wants an incoherent labeling, which is the thing the conjunct
      forbids.
    * `endpointLabelOf` / `serviceLabelOf` are independent, because the model
      reads them through their own accessors and a deployment may confine an
      endpoint more tightly than the objects that hold capabilities to it.
    * `separatedLower` / `separatedUpper` and their three proofs are the
      **non-triviality witness**: two admissible threads (neither the sentinel
      nor an idle thread) the labeling really does separate.  `deploymentLabelingContext` publishes them into
      `LabelingContext.separatedThreads`, which is what lets the runtime guard
      decide `labelNonTriviality` instead of sampling for it.

    What is *not* an obligation here: which partition is right for the
    deployment's threads.  That is a policy question the kernel cannot answer;
    this structure makes the labeling's *internal* consistency machine-checked
    and its non-triviality checkable at boot. -/
structure DeploymentLabeling where
  /-- The security label of the entity at each index — used for both the thread
      and its own kernel object, which is what makes thread/object coherence
      structural. -/
  entityLabelOf : Nat → SecurityLabel
  /-- The security label of each endpoint. -/
  endpointLabelOf : SeLe4n.ObjId → SecurityLabel
  /-- The security label of each registered service. -/
  serviceLabelOf : ServiceId → SecurityLabel
  /-- One side of the declared domain-separation witness. -/
  separatedLower : SeLe4n.ThreadId
  /-- The other side of the declared domain-separation witness. -/
  separatedUpper : SeLe4n.ThreadId
  /-- `separatedLower` is admissible as a witness: neither the reserved sentinel
      nor a per-core idle thread (`separationWitnessAdmissible`). -/
  hLowerReal : separationWitnessAdmissible separatedLower = true
  /-- `separatedUpper` is admissible as a witness, likewise. -/
  hUpperReal : separationWitnessAdmissible separatedUpper = true
  /-- The witness really is separated: the two threads carry different labels. -/
  hSeparated : entityLabelOf separatedLower.toNat ≠ entityLabelOf separatedUpper.toNat

/-- WS-RR RR5.1: build the deployment's `LabelingContext` from its
    `DeploymentLabeling`.

    This is the **only** constructor production code should use.  Its output is
    `LabelingContextValid` unconditionally
    (`deploymentLabelingContext_valid`, `InformationFlow/Invariant/Composition.lean`)
    and is admitted by the boot-time and syscall-entry guard unconditionally
    (`isInsecureDefaultContext_deploymentLabelingContext`), so a deployment that
    goes through it cannot ship a labeling that defeats information-flow
    enforcement by accident.

    The three policy fields the structure does not mention — `endpointPolicy`,
    `declassificationPolicy`, `auditMonitorClearance` — keep their fail-closed
    `LabelingContext` defaults (no override anywhere, deny every downgrade, deny
    every audit reader).  A deployment configures them by updating the result. -/
def deploymentLabelingContext (d : DeploymentLabeling) : LabelingContext :=
  { objectLabelOf    := fun oid => d.entityLabelOf oid.toNat
    threadLabelOf    := fun tid => d.entityLabelOf tid.toNat
    endpointLabelOf  := d.endpointLabelOf
    serviceLabelOf   := d.serviceLabelOf
    separatedThreads := some (d.separatedLower, d.separatedUpper) }

/-- WS-RR RR5.1: a thread and its own TCB object always carry the same label
    under a constructed deployment context — the definitional fact
    `LabelingContextValid.threadObjectCoherence` is proved from. -/
theorem deploymentLabelingContext_thread_object_label_eq
    (d : DeploymentLabeling) (tid : SeLe4n.ThreadId) :
    (deploymentLabelingContext d).objectLabelOf tid.toObjId =
      (deploymentLabelingContext d).threadLabelOf tid := rfl

/-- WS-RR RR5.5 (the opening half): **every** constructed deployment context is
    admitted by the guard, with no side conditions — the structure's own three
    obligations are exactly what the guard checks. -/
theorem isInsecureDefaultContext_deploymentLabelingContext (d : DeploymentLabeling) :
    isInsecureDefaultContext (deploymentLabelingContext d) = false := by
  have hSep : verifiesDeclaredSeparation (deploymentLabelingContext d) = true := by
    show (separationWitnessAdmissible d.separatedLower &&
      separationWitnessAdmissible d.separatedUpper &&
      (d.entityLabelOf d.separatedLower.toNat != d.entityLabelOf d.separatedUpper.toNat)) = true
    rw [d.hLowerReal, d.hUpperReal]
    simp only [Bool.and_self, Bool.true_and, bne_iff_ne, ne_eq]
    exact d.hSeparated
  simp only [isInsecureDefaultContext, hSep, Bool.not_true]

/-- WS-RR RR5.1: the boundary an index partition splits at, clamped to at least
    `2`.

    The clamp keeps `indexPartitionedDeploymentLabeling` total: index `0` is the
    reserved sentinel and index `1` is the first thread that can run, so a
    boundary of `2` or more guarantees the partition has a *real* thread on each
    side and the separation witness is always available.  A caller asking for
    `0` or `1` gets `2`. -/
def separationBoundary (upperDomainBase : Nat) : Nat := max 2 upperDomainBase

theorem two_le_separationBoundary (upperDomainBase : Nat) :
    2 ≤ separationBoundary upperDomainBase := Nat.le_max_left 2 upperDomainBase

/-- WS-RR RR5.1: the index of the upper-domain witness — the boundary itself,
    lifted past the idle range when the boundary falls inside it.

    Any index at or above the boundary is in the upper domain
    (`separationBoundary_le_upperWitnessIndex`), so the witness stays separated
    from thread `1` whatever the lift; lifting is what keeps it admissible
    (`separationWitnessAdmissible_upperWitnessIndex`) for **every** boundary,
    which is what keeps `indexPartitionedDeploymentLabeling` total.  Without it a
    deployment whose boundary happened to be an idle id would build a labeling
    the guard refuses. -/
def upperWitnessIndex (upperDomainBase : Nat) : Nat :=
  max (separationBoundary upperDomainBase)
    (idleThreadIdBase + SeLe4n.Kernel.Concurrency.numCores)

theorem separationBoundary_le_upperWitnessIndex (upperDomainBase : Nat) :
    separationBoundary upperDomainBase ≤ upperWitnessIndex upperDomainBase :=
  Nat.le_max_left _ _

/-- WS-RR RR5.1: the upper witness is admissible for every boundary. -/
theorem separationWitnessAdmissible_upperWitnessIndex (upperDomainBase : Nat) :
    separationWitnessAdmissible ⟨upperWitnessIndex upperDomainBase⟩ = true := by
  rw [separationWitnessAdmissible_iff]
  simp only [SeLe4n.ThreadId.toNat, upperWitnessIndex, separationBoundary, idleThreadIdBase,
    SeLe4n.Kernel.Concurrency.numCores]
  omega

/-- WS-RR RR5.1: the two-domain index partition — entities whose index is below
    the boundary take `lowerLabel`, the rest take `upperLabel`. -/
def indexPartitionedLabel (upperDomainBase : Nat) (lowerLabel upperLabel : SecurityLabel)
    (index : Nat) : SecurityLabel :=
  if index < separationBoundary upperDomainBase then lowerLabel else upperLabel

/-- WS-RR RR5.1: the canonical `DeploymentLabeling` family — a two-domain
    partition of the entity index space at `upperDomainBase`, with the two
    domains carrying `lowerLabel` and `upperLabel`.

    The only obligation the caller discharges is that the two labels differ;
    everything else the structure requires follows from the clamped boundary
    (`separationBoundary`).  The declared witness is thread `1` (the first
    non-sentinel index, always below the boundary and below the idle range)
    against the thread at `upperWitnessIndex` — the boundary itself, or the
    first index past the idle range when the boundary falls inside it; either
    way in the upper domain and admissible.

    A deployment with more than two domains supplies its own
    `DeploymentLabeling`; this family is the one the boot path and the platform
    bindings use, and it is what makes `confinedLabelingContext` concrete. -/
def indexPartitionedDeploymentLabeling
    (upperDomainBase : Nat) (lowerLabel upperLabel : SecurityLabel)
    (hLabels : lowerLabel ≠ upperLabel) : DeploymentLabeling :=
  { entityLabelOf   := indexPartitionedLabel upperDomainBase lowerLabel upperLabel
    endpointLabelOf := fun oid =>
      indexPartitionedLabel upperDomainBase lowerLabel upperLabel oid.toNat
    serviceLabelOf  := fun sid =>
      indexPartitionedLabel upperDomainBase lowerLabel upperLabel sid.toNat
    separatedLower  := ⟨1⟩
    separatedUpper  := ⟨upperWitnessIndex upperDomainBase⟩
    hLowerReal      := by decide
    hUpperReal      := separationWitnessAdmissible_upperWitnessIndex upperDomainBase
    hSeparated      := by
      have h := two_le_separationBoundary upperDomainBase
      simp only [SeLe4n.ThreadId.toNat, indexPartitionedLabel,
        if_pos (show 1 < separationBoundary upperDomainBase by omega),
        if_neg (Nat.not_lt.mpr (separationBoundary_le_upperWitnessIndex upperDomainBase))]
      exact hLabels }

/-- WS-RR RR5.1: the `LabelingContext` of an index-partitioned deployment —
    `deploymentLabelingContext` over `indexPartitionedDeploymentLabeling`, so it
    inherits that constructor's validity and admission unconditionally.  The
    two members the tree uses are `confinedLabelingContext` (production) and
    `harnessLabelingContext` (the simulation harness and the fixtures). -/
def indexPartitionedLabelingContext (upperDomainBase : Nat)
    (lowerLabel upperLabel : SecurityLabel) (hLabels : lowerLabel ≠ upperLabel) :
    LabelingContext :=
  deploymentLabelingContext
    (indexPartitionedDeploymentLabeling upperDomainBase lowerLabel upperLabel hLabels)

/-- WS-RR RR5.5: every index-partitioned context is admitted by the guard. -/
theorem isInsecureDefaultContext_indexPartitionedLabelingContext
    (upperDomainBase : Nat) (lowerLabel upperLabel : SecurityLabel)
    (hLabels : lowerLabel ≠ upperLabel) :
    isInsecureDefaultContext
        (indexPartitionedLabelingContext upperDomainBase lowerLabel upperLabel hLabels) = false :=
  isInsecureDefaultContext_deploymentLabelingContext _

/-- WS-RR RR5.1: every index-partitioned context labels an index below the
    boundary with the lower label — the fact a fixture cites when it needs its
    entities to keep the label they had before the labeling gained a declared
    separation. -/
theorem indexPartitionedLabelingContext_threadLabel_below
    (upperDomainBase : Nat) (lowerLabel upperLabel : SecurityLabel)
    (hLabels : lowerLabel ≠ upperLabel) (tid : SeLe4n.ThreadId)
    (h : tid.toNat < separationBoundary upperDomainBase) :
    (indexPartitionedLabelingContext upperDomainBase lowerLabel upperLabel hLabels).threadLabelOf
      tid = lowerLabel := by
  simp only [indexPartitionedLabelingContext, deploymentLabelingContext,
    indexPartitionedDeploymentLabeling, indexPartitionedLabel, if_pos h]

/-- WS-RR RR5.1: the companion of the lemma above for the upper domain. -/
theorem indexPartitionedLabelingContext_threadLabel_above
    (upperDomainBase : Nat) (lowerLabel upperLabel : SecurityLabel)
    (hLabels : lowerLabel ≠ upperLabel) (tid : SeLe4n.ThreadId)
    (h : separationBoundary upperDomainBase ≤ tid.toNat) :
    (indexPartitionedLabelingContext upperDomainBase lowerLabel upperLabel hLabels).threadLabelOf
      tid = upperLabel := by
  simp only [indexPartitionedLabelingContext, deploymentLabelingContext,
    indexPartitionedDeploymentLabeling, indexPartitionedLabel,
    if_neg (Nat.not_lt.mpr h)]

/-- WS-RR RR5.1: **the production labeling context** — two mutually isolated
    domains split at `upperDomainBase`.

    The two labels are the incomparable corners of the legacy lattice
    (`lowTrusted_highUntrusted_mutually_isolated`), so neither domain can observe
    or influence the other: this is a genuine confinement, not the one-directional
    `publicLabel` / `kernelTrusted` split, under which every low entity may still
    write into every high one.

    `upperDomainBase` is the one number a deployment must choose — the entity
    index at which its untrusted domain begins.  Everything below it (the boot
    system's threads, objects, endpoints and services) is `lowTrusted`;
    everything from it upward is `highUntrusted`.

    This is what the hardware boot installs, and the claim is a definition
    rather than a sentence: the Raspberry Pi 5 binding's `deploymentLabeling`
    is `confinedLabelingContext rpi5UpperDomainBase`
    (`Platform.RPi5.rpi5_deploymentLabeling`), and
    `Platform.FFI.bootAndInitialisePlatform` boots under whatever labeling the
    binding carries.  It is a *deployment* choice in the sense that the boundary
    is configurable, and a *kernel* guarantee in the sense that whatever
    boundary is chosen, the resulting context is `LabelingContextValid` and
    admitted by the fail-closed guard — which is why `PlatformBinding` can
    demand the admission proof as a field. -/
def confinedLabelingContext (upperDomainBase : Nat) : LabelingContext :=
  indexPartitionedLabelingContext upperDomainBase
    SecurityLabel.lowTrusted SecurityLabel.highUntrusted (by decide)

/-- WS-RR RR5.5: the production context is admitted by the guard. -/
theorem isInsecureDefaultContext_confinedLabelingContext (upperDomainBase : Nat) :
    isInsecureDefaultContext (confinedLabelingContext upperDomainBase) = false :=
  isInsecureDefaultContext_indexPartitionedLabelingContext _ _ _ _

/-- WS-RR RR5.1: the production context genuinely confines — an entity below the
    boundary and one at or above it cannot reach each other in *either*
    direction.  This is the substantive difference from every labeling the tree
    had before: `testLabelingContext`'s two "domains" are comparable, so its
    separation restricts nothing. -/
theorem confinedLabelingContext_confines
    (upperDomainBase : Nat) (tidLo tidHi : SeLe4n.ThreadId)
    (hLo : tidLo.toNat < separationBoundary upperDomainBase)
    (hHi : separationBoundary upperDomainBase ≤ tidHi.toNat) :
    securityFlowsTo ((confinedLabelingContext upperDomainBase).threadLabelOf tidLo)
        ((confinedLabelingContext upperDomainBase).threadLabelOf tidHi) = false ∧
    securityFlowsTo ((confinedLabelingContext upperDomainBase).threadLabelOf tidHi)
        ((confinedLabelingContext upperDomainBase).threadLabelOf tidLo) = false := by
  rw [confinedLabelingContext,
    indexPartitionedLabelingContext_threadLabel_below _ _ _ _ tidLo hLo,
    indexPartitionedLabelingContext_threadLabel_above _ _ _ _ tidHi hHi]
  exact lowTrusted_highUntrusted_mutually_isolated

/-- WS-RR RR5.1: the index every entity of the simulation harness and the test
    fixtures lives below.

    `idleThreadIdBase` is `0x1_0000`, so per-core idle threads are the highest
    ids any fixture allocates; this boundary clears them by four bits and leaves
    room for fixtures that allocate above idle. -/
def harnessSeparationBoundary : Nat := 0x10_0000

/-- WS-RR RR5.4: the labeling the simulation harness and the test suites run
    the **checked** entries under.

    A two-domain index partition whose boundary (`harnessSeparationBoundary`)
    sits above every id the fixtures allocate, with the lower domain at
    `publicLabel`.  Every fixture entity is therefore `publicLabel` — exactly the
    label `testLabelingContext` gave them, so no fixture's flow decision changes
    — while the labeling declares, and the guard verifies, a real separation
    between thread `1` and the thread at the boundary.

    It exists so the checked entries are exercised under a labeling the
    fail-closed guard *admits*, which is the thing `testLabelingContext` used to
    do by evading the guard rather than by satisfying it.  It is deliberately not
    a demonstration of cross-domain denial: the information-flow suites build
    their own separated labelings for that, and `confinedLabelingContext` is the
    production shape. -/
def harnessLabelingContext : LabelingContext :=
  indexPartitionedLabelingContext harnessSeparationBoundary
    SecurityLabel.publicLabel SecurityLabel.kernelTrusted (by decide)

/-- WS-RR RR5.4: the harness labeling is admitted by the guard. -/
theorem isInsecureDefaultContext_harnessLabelingContext :
    isInsecureDefaultContext harnessLabelingContext = false :=
  isInsecureDefaultContext_indexPartitionedLabelingContext _ _ _ _

/-- WS-RR RR5.4: the *uniform* fixture labeling — every index a fixture uses
    carries `insideLabel`, and the declared separation lives above
    `harnessSeparationBoundary`.

    A fixture that needs one label everywhere (so every flow gate on the path
    under test is reflexively satisfied and the test isolates something else)
    used to write a constant function, which is a one-label labeling: the guard
    now refuses it, and rightly — it separates nothing.  This gives the fixture
    the uniformity it wants over the id range it uses, with a real second domain
    above it, so the labeling meets the same obligation a deployment does.

    `harnessLabelingContext` is the `publicLabel` member of this family. -/
def uniformFixtureLabelingContext (insideLabel outsideLabel : SecurityLabel)
    (hLabels : insideLabel ≠ outsideLabel) : LabelingContext :=
  indexPartitionedLabelingContext harnessSeparationBoundary insideLabel outsideLabel hLabels

/-- WS-RR RR5.4: the uniform fixture labeling is admitted by the guard. -/
theorem isInsecureDefaultContext_uniformFixtureLabelingContext
    (insideLabel outsideLabel : SecurityLabel) (hLabels : insideLabel ≠ outsideLabel) :
    isInsecureDefaultContext (uniformFixtureLabelingContext insideLabel outsideLabel hLabels)
      = false :=
  isInsecureDefaultContext_indexPartitionedLabelingContext _ _ _ _

/-- WS-RR RR5.4: every entity index the fixtures use carries `publicLabel` under
    the harness labeling — the fact that keeps every pre-RR5 fixture flow
    decision unchanged when the harness moves off `testLabelingContext`. -/
theorem harnessLabelingContext_threadLabel_public
    (tid : SeLe4n.ThreadId) (h : tid.toNat < harnessSeparationBoundary) :
    harnessLabelingContext.threadLabelOf tid = SecurityLabel.publicLabel := by
  have hb : tid.toNat < separationBoundary harnessSeparationBoundary := by
    simp only [separationBoundary, harnessSeparationBoundary] at *
    omega
  exact indexPartitionedLabelingContext_threadLabel_below _ _ _ _ tid hb

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
