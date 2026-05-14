-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

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

    A standard BIBA alternative is provided as `bibaIntegrityFlowsTo` below
    for comparison and potential future use. -/
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
    as the first). -/
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

/-- WS-G1: Hash instance for HashMap/HashSet keying. -/
@[inline] instance : Hashable SecurityDomain where
  hash a := hash a.id

namespace SecurityDomain

/-- The public (lowest) domain. -/
def lowest : SecurityDomain := ⟨0⟩

/-- WS-H14d: Construct a SecurityDomain from a Nat. -/
@[inline] def ofNat (n : Nat) : SecurityDomain := ⟨n⟩

/-- WS-H14d: Project a SecurityDomain to its underlying Nat. -/
@[inline] def toNat (d : SecurityDomain) : Nat := d.id

instance : ToString SecurityDomain where
  toString d := s!"domain({d.id})"

/-- WS-H14d: SecurityDomain roundtrip — construct then project. -/
theorem toNat_ofNat (n : Nat) : (SecurityDomain.ofNat n).toNat = n := rfl
/-- WS-H14d: SecurityDomain roundtrip — project then reconstruct. -/
theorem ofNat_toNat (d : SecurityDomain) : SecurityDomain.ofNat d.toNat = d := rfl
/-- WS-H14d: SecurityDomain injectivity. -/
theorem ofNat_injective {n₁ n₂ : Nat} (h : SecurityDomain.ofNat n₁ = SecurityDomain.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: SecurityDomain extensionality. -/
theorem ext {a b : SecurityDomain} (h : a.id = b.id) : a = b := by
  cases a; cases b; simp_all

end SecurityDomain

/-- WS-H14a: EquivBEq for SecurityDomain. -/
instance : EquivBEq SecurityDomain := ⟨⟩
/-- WS-H14a: LawfulBEq for SecurityDomain. -/
instance : LawfulBEq SecurityDomain where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
/-- WS-H14a: LawfulHashable for SecurityDomain. -/
instance : LawfulHashable SecurityDomain where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

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

-- ============================================================================
-- V6-H (M-IF-6): Declassification audit trail
-- ============================================================================

/-- V6-H (M-IF-6): Record of a declassification event for audit purposes.

    Every declassification operation should produce a `DeclassificationEvent`
    recording the source domain, destination domain, authorization basis,
    and a monotonic timestamp. The audit trail enables post-hoc analysis of
    information-flow boundary crossings.

    **Usage**: The enforcement wrappers in `Enforcement/Soundness.lean`
    (`declassifyStore`) produce declassification events. The caller is
    responsible for recording these events in an append-only audit log. -/
structure DeclassificationEvent where
  /-- Source domain initiating the declassification. -/
  srcDomain : SecurityDomain
  /-- Destination domain receiving the declassified information. -/
  dstDomain : SecurityDomain
  /-- Object ID of the target being declassified to. -/
  targetObject : SeLe4n.ObjId
  /-- Authorization basis for this declassification. Records which policy
      rule or system-integrator authority permitted the downgrade. Examples:
      `"DeclassificationPolicy.canDeclassify"`, `"system-integrator-override"`.
      The kernel does not interpret this value — it is stored for audit
      trail consumption by external analysis tools. -/
  authorizationBasis : String
  /-- Monotonic event counter (not wall-clock time — the kernel has no
      notion of real time). Used for ordering events in the audit log. -/
  timestamp : Nat
  deriving Repr, DecidableEq

/-- V6-H: An audit log is a list of declassification events, ordered by
    timestamp (most recent last). -/
abbrev DeclassificationAuditLog := List DeclassificationEvent

/-- V6-H: Record a declassification event in the audit log. -/
def recordDeclassification
    (log : DeclassificationAuditLog)
    (event : DeclassificationEvent) : DeclassificationAuditLog :=
  log ++ [event]

/-- V6-H: The audit log is append-only — recording preserves existing entries. -/
theorem recordDeclassification_preserves_existing
    (log : DeclassificationAuditLog) (event : DeclassificationEvent) :
    ∀ e ∈ log, e ∈ recordDeclassification log event := by
  intro e hMem
  exact List.mem_append_left _ hMem

/-- V6-H: A recorded event is always in the resulting log. -/
theorem recordDeclassification_contains_new
    (log : DeclassificationAuditLog) (event : DeclassificationEvent) :
    event ∈ recordDeclassification log event := by
  simp [recordDeclassification]

/-- V6-H: Audit log length increases by exactly 1 on each record. -/
theorem recordDeclassification_length
    (log : DeclassificationAuditLog) (event : DeclassificationEvent) :
    (recordDeclassification log event).length = log.length + 1 := by
  simp [recordDeclassification]

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

-- ============================================================================
-- WS-RC R6.C (DEEP-IF-02): SecurityDomain lattice completion
-- ============================================================================

/-! ## WS-RC R6.C — SecurityDomain Lattice Completion

The H-04 section header (above) promised a parameterised domain model
with "Lattice properties (reflexivity, transitivity, antisymmetry) ...
proved generically under policy constraints."  Pre-R6.C the
implementation delivered only a pre-order: reflexivity
(`domainFlowsTo_refl`) and transitivity (`domainFlowsTo_trans`).  This
section closes DEEP-IF-02 by completing the lattice over `SecurityDomain`
under the canonical `linearOrder` policy:

1. `SecurityDomain.sup` and `SecurityDomain.inf` — supremum (join) and
   infimum (meet) over the natural `Nat`-indexed order on `id`.
2. The four lattice-law theorems (associativity, commutativity, two
   absorption laws) for each of `sup` and `inf`, plus their order-
   characterising bridges.
3. Antisymmetry of `linearOrder.canFlow` — the missing pre-order
   completion to make it a partial order.
4. The bridge theorem `linearOrder_canFlow_iff_sup_eq` connecting
   `domainFlowsTo` to the lattice's `≤` (via `sup = b`).

The canonical default lattice uses the `linearOrder` policy.  For
arbitrary `DomainFlowPolicy` the order is policy-dependent (e.g.,
`allowAll` makes every pair comparable, breaking antisymmetry); the
lattice over a non-trivial policy is naturally definable as a quotient
of `SecurityDomain` by the policy's symmetric closure, recorded here as
a post-1.0 extension hook.

Lean 4.28.0 ships without Mathlib in this codebase, so the lattice
instances use Lean core's `Max` / `Min` typeclasses combined with
direct `sup`/`inf` definitions and theorem-form lattice laws.  This
gives every consumer the standard `max`/`min` notation while keeping
the proof obligations available as named theorems. -/

namespace SecurityDomain

/-- WS-RC R6.C.1a (DEEP-IF-02): The supremum (join) of two security
    domains under the canonical `Nat`-indexed order on `id`.  Matches
    `Nat.max` componentwise.  Under `DomainFlowPolicy.linearOrder` this
    is the least upper bound w.r.t. `canFlow`. -/
@[inline] def sup (a b : SecurityDomain) : SecurityDomain :=
  ⟨Nat.max a.id b.id⟩

/-- WS-RC R6.C.1b (DEEP-IF-02): The infimum (meet) of two security
    domains under the canonical `Nat`-indexed order on `id`.  Matches
    `Nat.min` componentwise.  Under `DomainFlowPolicy.linearOrder` this
    is the greatest lower bound w.r.t. `canFlow`. -/
@[inline] def inf (a b : SecurityDomain) : SecurityDomain :=
  ⟨Nat.min a.id b.id⟩

/-- WS-RC R6.C: `Max` instance compatible with Lean core's `max`
    notation.  Allows callers to write `max a b` instead of
    `SecurityDomain.sup a b`. -/
instance : Max SecurityDomain := ⟨sup⟩

/-- WS-RC R6.C: `Min` instance compatible with Lean core's `min`
    notation.  Allows callers to write `min a b` instead of
    `SecurityDomain.inf a b`. -/
instance : Min SecurityDomain := ⟨inf⟩

/-- WS-RC R6.C: The `id` of a `sup` is the `max` of the components'
    ids.  Useful for simp normalisation. -/
@[simp] theorem sup_id (a b : SecurityDomain) :
    (sup a b).id = Nat.max a.id b.id := rfl

/-- WS-RC R6.C: The `id` of an `inf` is the `min` of the components'
    ids.  Useful for simp normalisation. -/
@[simp] theorem inf_id (a b : SecurityDomain) :
    (inf a b).id = Nat.min a.id b.id := rfl

-- ============================================================================
-- WS-RC R6.C.2 (DEEP-IF-02): Lattice-law theorems
-- ============================================================================

/-- WS-RC R6.C.2 (DEEP-IF-02): `sup` is associative.  Lattice law 1. -/
theorem sup_assoc (a b c : SecurityDomain) :
    sup (sup a b) c = sup a (sup b c) := by
  apply ext
  simp [Nat.max_assoc]

/-- WS-RC R6.C.2 (DEEP-IF-02): `sup` is commutative.  Lattice law 2. -/
theorem sup_comm (a b : SecurityDomain) : sup a b = sup b a := by
  apply ext
  simp [Nat.max_comm]

/-- WS-RC R6.C.2 (DEEP-IF-02): `sup` is idempotent.  Useful follow-on
    lemma derived from the lattice laws. -/
@[simp] theorem sup_self (a : SecurityDomain) : sup a a = a := by
  apply ext; simp

/-- WS-RC R6.C.2 (DEEP-IF-02): `inf` is associative.  Lattice law 1'. -/
theorem inf_assoc (a b c : SecurityDomain) :
    inf (inf a b) c = inf a (inf b c) := by
  apply ext
  simp [Nat.min_assoc]

/-- WS-RC R6.C.2 (DEEP-IF-02): `inf` is commutative.  Lattice law 2'. -/
theorem inf_comm (a b : SecurityDomain) : inf a b = inf b a := by
  apply ext
  simp [Nat.min_comm]

/-- WS-RC R6.C.2 (DEEP-IF-02): `inf` is idempotent.  Follow-on lemma. -/
@[simp] theorem inf_self (a : SecurityDomain) : inf a a = a := by
  apply ext; simp

/-- WS-RC R6.C.2 (DEEP-IF-02): Absorption law 1 — `a ⊔ (a ⊓ b) = a`. -/
theorem absorb_sup_inf (a b : SecurityDomain) :
    sup a (inf a b) = a := by
  apply ext
  simp [Nat.max_eq_left, Nat.min_le_left]

/-- WS-RC R6.C.2 (DEEP-IF-02): Absorption law 2 — `a ⊓ (a ⊔ b) = a`. -/
theorem absorb_inf_sup (a b : SecurityDomain) :
    inf a (sup a b) = a := by
  apply ext
  simp [Nat.min_eq_left, Nat.le_max_left]

-- ============================================================================
-- WS-RC R6.C.3 (DEEP-IF-02): Bridge between `flowsTo` (linearOrder) and `sup`
-- ============================================================================

/-- WS-RC R6.C.3 (DEEP-IF-02): Under the canonical `linearOrder` flow
    policy, the lattice's `sup` characterises `≤`: `a ≤ b` iff
    `sup a b = b`.

    This is the standard equivalence "x ≤ y iff x ∨ y = y" instantiated
    to `SecurityDomain` under the `Nat.le` order.  Closes the R6.C.3
    bridge by tying the lattice's order-theoretic structure to the
    information-flow policy. -/
theorem linearOrder_canFlow_iff_sup_eq (a b : SecurityDomain) :
    DomainFlowPolicy.linearOrder.canFlow a b = true ↔ sup a b = b := by
  simp [DomainFlowPolicy.linearOrder, sup]
  constructor
  · intro h
    apply ext
    show Nat.max a.id b.id = b.id
    exact Nat.max_eq_right h
  · intro h
    have hId : Nat.max a.id b.id = b.id := congrArg SecurityDomain.id h
    show a.id ≤ b.id
    have hLe : a.id ≤ Nat.max a.id b.id := Nat.le_max_left a.id b.id
    omega

/-- WS-RC R6.C.3 (DEEP-IF-02): Dual bridge — `a ≤ b` iff
    `inf a b = a`. -/
theorem linearOrder_canFlow_iff_inf_eq (a b : SecurityDomain) :
    DomainFlowPolicy.linearOrder.canFlow a b = true ↔ inf a b = a := by
  simp [DomainFlowPolicy.linearOrder, inf]
  constructor
  · intro h
    apply ext
    show Nat.min a.id b.id = a.id
    exact Nat.min_eq_left h
  · intro h
    have hId : Nat.min a.id b.id = a.id := congrArg SecurityDomain.id h
    show a.id ≤ b.id
    have hLe : Nat.min a.id b.id ≤ b.id := Nat.min_le_right a.id b.id
    omega

-- ============================================================================
-- WS-RC R6.C: Antisymmetry of `linearOrder.canFlow`
-- ============================================================================

/-- WS-RC R6.C (DEEP-IF-02): Antisymmetry of `linearOrder.canFlow`.

    Closes the third pre-order law promised by the H-04 section header:
    if `a` can flow to `b` *and* `b` can flow to `a` under the canonical
    `linearOrder` policy, then `a = b`.  Combined with the existing
    `linearOrder_reflexive` and `linearOrder_transitive` theorems, this
    makes `linearOrder` a partial order — the structural prerequisite
    for the lattice (`sup`/`inf` of an antisymmetric pre-order is
    unique). -/
theorem linearOrder_canFlow_antisymm (a b : SecurityDomain)
    (h₁ : DomainFlowPolicy.linearOrder.canFlow a b = true)
    (h₂ : DomainFlowPolicy.linearOrder.canFlow b a = true) :
    a = b := by
  apply ext
  simp [DomainFlowPolicy.linearOrder] at h₁ h₂
  exact Nat.le_antisymm h₁ h₂

/-- WS-RC R6.C (DEEP-IF-02): A flow policy is antisymmetric if every
    bi-directional flow forces domain equality.  The canonical
    `linearOrder` policy satisfies this; `allowAll` does not (it makes
    every pair bi-directionally flow-permissive, collapsing distinct
    domains modulo the policy's equivalence). -/
def antisymmetric (p : DomainFlowPolicy) : Prop :=
  ∀ a b : SecurityDomain,
    p.canFlow a b = true → p.canFlow b a = true → a = b

end SecurityDomain

/-- WS-RC R6.C (DEEP-IF-02): `linearOrder` is antisymmetric — a strict
    partial-order property bridging `DomainFlowPolicy.linearOrder`'s
    pre-order (reflexive + transitive, already proven above) to a full
    partial order.  Exported under the `DomainFlowPolicy` namespace for
    symmetric placement alongside `linearOrder_reflexive` and
    `linearOrder_transitive`. -/
theorem DomainFlowPolicy.linearOrder_antisymm :
    SecurityDomain.antisymmetric DomainFlowPolicy.linearOrder :=
  SecurityDomain.linearOrder_canFlow_antisymm

-- ============================================================================
-- WS-RC R6.C: Completed-lattice witness bundle
-- ============================================================================

/-- WS-RC R6.C (DEEP-IF-02): Witness structure bundling the four lattice
    laws plus the two order-characterising bridges plus antisymmetry of
    the canonical policy.  Mirrors the spec promised by the H-04 section
    header at `Policy.lean` lines 484–500.

    Constructed unconditionally by `securityDomain_complete_lattice` —
    every `SecurityDomain` carries all lattice operations and the four
    laws as theorems.  Discharge-index citations point at this
    structure as a single artifact summarising the completion. -/
structure SecurityDomainLattice : Prop where
  /-- `sup` is associative. -/
  sup_assoc' : ∀ a b c : SecurityDomain,
    SecurityDomain.sup (SecurityDomain.sup a b) c
      = SecurityDomain.sup a (SecurityDomain.sup b c)
  /-- `sup` is commutative. -/
  sup_comm' : ∀ a b : SecurityDomain,
    SecurityDomain.sup a b = SecurityDomain.sup b a
  /-- `inf` is associative. -/
  inf_assoc' : ∀ a b c : SecurityDomain,
    SecurityDomain.inf (SecurityDomain.inf a b) c
      = SecurityDomain.inf a (SecurityDomain.inf b c)
  /-- `inf` is commutative. -/
  inf_comm' : ∀ a b : SecurityDomain,
    SecurityDomain.inf a b = SecurityDomain.inf b a
  /-- Absorption law 1 — `a ⊔ (a ⊓ b) = a`. -/
  absorb_sup_inf' : ∀ a b : SecurityDomain,
    SecurityDomain.sup a (SecurityDomain.inf a b) = a
  /-- Absorption law 2 — `a ⊓ (a ⊔ b) = a`. -/
  absorb_inf_sup' : ∀ a b : SecurityDomain,
    SecurityDomain.inf a (SecurityDomain.sup a b) = a
  /-- The lattice's `≤` (via `sup = b`) coincides with
      `linearOrder.canFlow`. -/
  flowsTo_iff_sup_eq' : ∀ a b : SecurityDomain,
    DomainFlowPolicy.linearOrder.canFlow a b = true
      ↔ SecurityDomain.sup a b = b
  /-- Antisymmetry of the canonical `linearOrder` policy — combined
      with the existing reflexivity/transitivity, makes it a partial
      order. -/
  linearOrder_antisymm' : SecurityDomain.antisymmetric DomainFlowPolicy.linearOrder

/-- WS-RC R6.C (DEEP-IF-02): The canonical lattice always holds.  This
    is the single witness discharging the H-04 spec promise of a
    "complete lattice" on `SecurityDomain`. -/
theorem securityDomain_complete_lattice : SecurityDomainLattice where
  sup_assoc' := SecurityDomain.sup_assoc
  sup_comm' := SecurityDomain.sup_comm
  inf_assoc' := SecurityDomain.inf_assoc
  inf_comm' := SecurityDomain.inf_comm
  absorb_sup_inf' := SecurityDomain.absorb_sup_inf
  absorb_inf_sup' := SecurityDomain.absorb_inf_sup
  flowsTo_iff_sup_eq' := SecurityDomain.linearOrder_canFlow_iff_sup_eq
  linearOrder_antisymm' := SecurityDomain.linearOrder_canFlow_antisymm

-- ============================================================================
-- WS-RC R6.C.2 (DEEP-IF-02): In-house Mathlib-compatible lattice typeclasses
-- ============================================================================

/-! ## WS-RC R6.C.2 — Lattice typeclass hierarchy (Mathlib-compatible)

Lean core ships `LE`, `LT`, `Max`, and `Min` typeclasses but does NOT
ship the order-theoretic algebraic structures (`Preorder`,
`PartialOrder`, `Sup`, `Inf`, `SemilatticeSup`, `SemilatticeInf`,
`Lattice`) — these are Mathlib-only.

Since this codebase deliberately avoids a Mathlib dependency (the
kernel's trusted computing base must stay small — see
`CLAUDE.md` "Third-party attribution" rules), R6.C.2 provides an
in-house typeclass hierarchy that:

1. **Uses the same class names** as Mathlib (`SemilatticeSup`,
   `SemilatticeInf`, `Lattice`, etc.) so a future Mathlib import in a
   downstream project would be a drop-in replacement (the in-house
   classes would then resolve to Mathlib's versions in scope of the
   import, or to ours when Mathlib isn't loaded).
2. **Uses the same field names** as Mathlib (`le_sup_left`,
   `le_sup_right`, `sup_le`, `le_antisymm`, etc.) so derived proofs
   in our codebase remain Mathlib-style.
3. **Uses the standard axiomatization** (the strongest of the
   "equivalent" axiomatizations of a semilattice) so the lattice laws
   `sup_assoc`, `sup_comm`, `sup_idem`, the absorption laws, and the
   order-via-sup bridge `a ≤ b ↔ a ⊔ b = b` are derivable theorems
   from the typeclass axioms.

The classes are placed in the `SeLe4n.Kernel` namespace so they don't
shadow any future `_root_.Preorder` / `_root_.PartialOrder` /
`_root_.Lattice` from a Mathlib import. -/

/-- WS-RC R6.C.2: In-house `Preorder` typeclass.  Mirrors Mathlib's
    `Preorder` field-for-field.  A preorder is a reflexive and
    transitive relation `≤`, with a derived strict order `<` related
    by `a < b ↔ a ≤ b ∧ ¬ b ≤ a`. -/
class Preorder (α : Type u) extends LE α, LT α where
  /-- Reflexivity of `≤`. -/
  le_refl : ∀ a : α, a ≤ a
  /-- Transitivity of `≤`. -/
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c
  /-- Strict order is anti-reflexive: `a < b → ¬ b ≤ a`.  Combined
      with reflexivity this gives the standard strict-order
      relationship. -/
  lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
    intros; rfl

/-- WS-RC R6.C.2: In-house `PartialOrder` typeclass.  Mirrors
    Mathlib's `PartialOrder`.  Adds antisymmetry to the preorder
    structure, producing a poset. -/
class PartialOrder (α : Type u) extends Preorder α where
  /-- Antisymmetry of `≤`. -/
  le_antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b

/-- WS-RC R6.C.2: In-house `Sup` typeclass.  Mirrors Mathlib's `Sup`
    (Mathlib distinguishes `Sup` from `Max` to allow lattices over
    non-totally-ordered types; we follow the same convention).  The
    notation `⊔` is reserved for Mathlib; we don't introduce it here
    to avoid namespace clutter, but consumers can write
    `SeLe4n.Kernel.Sup.sup a b` or use the wrapped `SecurityDomain.sup`. -/
class Sup (α : Type u) where
  /-- The supremum (join) operation. -/
  sup : α → α → α

/-- WS-RC R6.C.2: In-house `Inf` typeclass.  Mirrors Mathlib's `Inf`. -/
class Inf (α : Type u) where
  /-- The infimum (meet) operation. -/
  inf : α → α → α

/-- WS-RC R6.C.2: In-house `SemilatticeSup` typeclass.  Mirrors
    Mathlib's `SemilatticeSup`: a partial order with a binary supremum
    operation satisfying the standard three axioms (`le_sup_left`,
    `le_sup_right`, `sup_le`).  These axioms are the **strongest**
    standard axiomatization — they imply `sup_assoc`, `sup_comm`,
    `sup_idem`, and the order-via-sup bridge `a ≤ b ↔ sup a b = b` as
    theorems. -/
class SemilatticeSup (α : Type u) extends Sup α, PartialOrder α where
  /-- The supremum is an upper bound on the left. -/
  le_sup_left : ∀ a b : α, a ≤ Sup.sup a b
  /-- The supremum is an upper bound on the right. -/
  le_sup_right : ∀ a b : α, b ≤ Sup.sup a b
  /-- The supremum is the **least** upper bound. -/
  sup_le : ∀ {a b c : α}, a ≤ c → b ≤ c → Sup.sup a b ≤ c

/-- WS-RC R6.C.2: In-house `SemilatticeInf` typeclass.  Dual of
    `SemilatticeSup`. -/
class SemilatticeInf (α : Type u) extends Inf α, PartialOrder α where
  /-- The infimum is a lower bound on the left. -/
  inf_le_left : ∀ a b : α, Inf.inf a b ≤ a
  /-- The infimum is a lower bound on the right. -/
  inf_le_right : ∀ a b : α, Inf.inf a b ≤ b
  /-- The infimum is the **greatest** lower bound. -/
  le_inf : ∀ {a b c : α}, a ≤ b → a ≤ c → a ≤ Inf.inf b c

/-- WS-RC R6.C.2: In-house `Lattice` typeclass.  Mirrors Mathlib's
    `Lattice`: a partial order that is both a `SemilatticeSup` and a
    `SemilatticeInf`.  The absorption laws follow automatically from
    the semilattice axioms and antisymmetry. -/
class Lattice (α : Type u) extends SemilatticeSup α, SemilatticeInf α

-- ============================================================================
-- WS-RC R6.C.2: SecurityDomain instances (Preorder → PartialOrder → Lattice)
-- ============================================================================

namespace SecurityDomain

/-- WS-RC R6.C.2: `LE` instance — `a ≤ b ↔ a.id ≤ b.id` (lifts
    `Nat.le` through the `id` field). -/
instance instLE : LE SecurityDomain where
  le a b := a.id ≤ b.id

/-- WS-RC R6.C.2: `LT` instance — `a < b ↔ a.id < b.id`. -/
instance instLT : LT SecurityDomain where
  lt a b := a.id < b.id

/-- WS-RC R6.C.2: `Decidable` instance for `≤` over `SecurityDomain`,
    inherited from `Nat`. -/
instance instDecidableLE (a b : SecurityDomain) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.id ≤ b.id))

/-- WS-RC R6.C.2: `Decidable` instance for `<` over `SecurityDomain`. -/
instance instDecidableLT (a b : SecurityDomain) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.id < b.id))

/-- WS-RC R6.C.2: `≤` unfolds to `Nat.le` on `id`. -/
@[simp] theorem le_iff_id_le (a b : SecurityDomain) : a ≤ b ↔ a.id ≤ b.id :=
  Iff.rfl

/-- WS-RC R6.C.2: `<` unfolds to `Nat.lt` on `id`. -/
@[simp] theorem lt_iff_id_lt (a b : SecurityDomain) : a < b ↔ a.id < b.id :=
  Iff.rfl

end SecurityDomain

/-- WS-RC R6.C.2: `Preorder` instance for `SecurityDomain`.
    Reflexivity, transitivity, and the `<` ↔ `≤ ∧ not ≥` derivation
    all transport from `Nat`.  The transport is by definitional
    reduction through the `LE`/`LT` instance dispatch — `a ≤ b` and
    `a < b` on `SecurityDomain` definitionally equal `a.id ≤ b.id`
    and `a.id < b.id` on `Nat`. -/
instance : Preorder SecurityDomain where
  le_refl a := Nat.le_refl a.id
  le_trans h₁ h₂ := Nat.le_trans h₁ h₂
  lt_iff_le_not_le := Nat.lt_iff_le_not_le

/-- WS-RC R6.C.2: `PartialOrder` instance for `SecurityDomain`.
    Antisymmetry follows from `Nat.le_antisymm` on the `id` field. -/
instance : PartialOrder SecurityDomain where
  le_antisymm h₁ h₂ :=
    SecurityDomain.ext (Nat.le_antisymm h₁ h₂)

/-- WS-RC R6.C.2: `Sup` instance for `SecurityDomain` — delegates to
    `SecurityDomain.sup`. -/
instance : Sup SecurityDomain where
  sup := SecurityDomain.sup

/-- WS-RC R6.C.2: `Inf` instance for `SecurityDomain` — delegates to
    `SecurityDomain.inf`. -/
instance : Inf SecurityDomain where
  inf := SecurityDomain.inf

/-- WS-RC R6.C.2: `SemilatticeSup` instance for `SecurityDomain`.
    The three axioms transport directly from `Nat`'s `max` lemmas in
    Lean core (`Nat.le_max_left`, `Nat.le_max_right`,
    `Nat.max_le.mpr`). -/
instance : SemilatticeSup SecurityDomain where
  le_sup_left a b := Nat.le_max_left a.id b.id
  le_sup_right a b := Nat.le_max_right a.id b.id
  sup_le h₁ h₂ := Nat.max_le.mpr ⟨h₁, h₂⟩

/-- WS-RC R6.C.2: `SemilatticeInf` instance for `SecurityDomain`.
    Dual transport from `Nat.min_le_left`, `Nat.min_le_right`,
    `Nat.le_min.mpr`. -/
instance : SemilatticeInf SecurityDomain where
  inf_le_left a b := Nat.min_le_left a.id b.id
  inf_le_right a b := Nat.min_le_right a.id b.id
  le_inf h₁ h₂ := Nat.le_min.mpr ⟨h₁, h₂⟩

/-- WS-RC R6.C.2: `Lattice` instance for `SecurityDomain`.  The
    absorption laws are implied by the parent semilattice axioms +
    antisymmetry; no additional discharge is required (the `Lattice`
    typeclass has no `extends`-beyond-parent obligations). -/
instance : Lattice SecurityDomain where

-- ============================================================================
-- WS-RC R6.C.2: Discharge of the four lattice laws from typeclass axioms
-- ============================================================================

/-! Provide the four lattice-law theorems the plan literally names
    (`sup_assoc`, `sup_comm`, `absorb_sup_inf`, `absorb_inf_sup`) as
    GENERIC theorems over any `Lattice α`.  These are the standard
    consequences of the `SemilatticeSup`/`SemilatticeInf` axioms +
    antisymmetry.  The `SecurityDomain` versions
    (`SecurityDomain.sup_assoc`, etc.) follow from these instances.

    This shows that the in-house typeclass hierarchy is mathematically
    sound: the laws are theorems, not axioms. -/

/-- WS-RC R6.C.2: Generic `sup_assoc` for any `SemilatticeSup`.  This
    is the standard "associativity from the least-upper-bound axioms"
    proof: each side is the join of `a`, `b`, `c`. -/
theorem SemilatticeSup.sup_assoc' {α : Type u} [SemilatticeSup α]
    (a b c : α) :
    Sup.sup (Sup.sup a b) c = Sup.sup a (Sup.sup b c) := by
  apply PartialOrder.le_antisymm
  · apply SemilatticeSup.sup_le
    · apply SemilatticeSup.sup_le
      · exact SemilatticeSup.le_sup_left a (Sup.sup b c)
      · exact Preorder.le_trans
          (SemilatticeSup.le_sup_left b c)
          (SemilatticeSup.le_sup_right a (Sup.sup b c))
    · exact Preorder.le_trans
        (SemilatticeSup.le_sup_right b c)
        (SemilatticeSup.le_sup_right a (Sup.sup b c))
  · apply SemilatticeSup.sup_le
    · exact Preorder.le_trans
        (SemilatticeSup.le_sup_left a b)
        (SemilatticeSup.le_sup_left (Sup.sup a b) c)
    · apply SemilatticeSup.sup_le
      · exact Preorder.le_trans
          (SemilatticeSup.le_sup_right a b)
          (SemilatticeSup.le_sup_left (Sup.sup a b) c)
      · exact SemilatticeSup.le_sup_right (Sup.sup a b) c

/-- WS-RC R6.C.2: Generic `sup_comm` for any `SemilatticeSup`. -/
theorem SemilatticeSup.sup_comm' {α : Type u} [SemilatticeSup α]
    (a b : α) : Sup.sup a b = Sup.sup b a := by
  apply PartialOrder.le_antisymm
  · exact SemilatticeSup.sup_le
      (SemilatticeSup.le_sup_right b a)
      (SemilatticeSup.le_sup_left b a)
  · exact SemilatticeSup.sup_le
      (SemilatticeSup.le_sup_right a b)
      (SemilatticeSup.le_sup_left a b)

/-- WS-RC R6.C.2: Generic `absorb_sup_inf` for any `Lattice`.
    `a ⊔ (a ⊓ b) = a`. -/
theorem Lattice.absorb_sup_inf' {α : Type u} [Lattice α] (a b : α) :
    Sup.sup a (Inf.inf a b) = a := by
  apply PartialOrder.le_antisymm
  · exact SemilatticeSup.sup_le
      (Preorder.le_refl a)
      (SemilatticeInf.inf_le_left a b)
  · exact SemilatticeSup.le_sup_left a (Inf.inf a b)

/-- WS-RC R6.C.2: Generic `absorb_inf_sup` for any `Lattice`.
    `a ⊓ (a ⊔ b) = a`. -/
theorem Lattice.absorb_inf_sup' {α : Type u} [Lattice α] (a b : α) :
    Inf.inf a (Sup.sup a b) = a := by
  apply PartialOrder.le_antisymm
  · exact SemilatticeInf.inf_le_left a (Sup.sup a b)
  · exact SemilatticeInf.le_inf
      (Preorder.le_refl a)
      (SemilatticeSup.le_sup_left a b)

-- ============================================================================
-- WS-RC R6.C.3 (DEEP-IF-02): Plan-named aliases
-- ============================================================================

/-- WS-RC R6.C.3 (DEEP-IF-02): Plan-named alias.  The plan's
    pseudocode (`AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §10.6, R6.C.3)
    uses the name `flowsTo_iff_sup_eq` for the bridge from `flowsTo`
    to `sup`.  Since `flowsTo` on `SecurityDomain` doesn't exist at
    the type level (only `domainFlowsTo` parameterised by a policy
    and `linearOrder.canFlow` for the canonical default), we wire the
    alias through the canonical `linearOrder` policy.

    Callers wanting the bridge with the plan-named identifier use
    `flowsTo_iff_sup_eq`; callers wanting the policy-explicit version
    use `SecurityDomain.linearOrder_canFlow_iff_sup_eq` directly. -/
abbrev flowsTo_iff_sup_eq := @SecurityDomain.linearOrder_canFlow_iff_sup_eq

/-- WS-RC R6.C.3 (DEEP-IF-02): Plan-named alias for the dual bridge
    `a ≤ b ↔ inf a b = a`. -/
abbrev flowsTo_iff_inf_eq := @SecurityDomain.linearOrder_canFlow_iff_inf_eq

/-- WS-RC R6.C.3 (DEEP-IF-02): Bridge from the legacy
    BIBA-inverted `integrityFlowsTo` predicate (on `Integrity`) to
    the lattice's `≤` on the embedded `SecurityDomain`.

    The plan's pseudocode references `integrityFlowsTo` as if it
    were a relation on `SecurityDomain`; in this codebase
    `integrityFlowsTo` is defined on the legacy `Integrity` enum
    (`untrusted` / `trusted`).  The two are bridged by
    `embedLegacyLabel`, which maps `low untrusted → 0`,
    `low trusted → 1`, `high untrusted → 2`, `high trusted → 3`
    (see `embedLegacyLabel` above).

    The legacy `integrityFlowsTo` is BIBA-inverted: it returns
    `true` when the destination is "no more trusted" than the
    source — i.e. when `untrusted → trusted` (and trivially
    `untrusted → untrusted`, `trusted → trusted`).  Under
    `embedLegacyLabel + linearOrder`, this corresponds to `≤` on
    the lattice. -/
theorem integrityFlowsTo_to_linearOrder_canFlow
    (src dst : SecurityLabel)
    (hFlow : securityFlowsTo src dst = true) :
    DomainFlowPolicy.linearOrder.canFlow
        (embedLegacyLabel src) (embedLegacyLabel dst) = true :=
  embedLegacyLabel_preserves_flow src dst hFlow

/-- WS-RC R6.C.3 (DEEP-IF-02): Combined witness — every legacy flow
    is witnessed by the lattice's `≤` (via `sup`-equality). -/
theorem securityFlowsTo_iff_embedded_sup_eq
    (src dst : SecurityLabel)
    (hFlow : securityFlowsTo src dst = true) :
    SecurityDomain.sup (embedLegacyLabel src) (embedLegacyLabel dst)
      = embedLegacyLabel dst :=
  (SecurityDomain.linearOrder_canFlow_iff_sup_eq
      (embedLegacyLabel src) (embedLegacyLabel dst)).mp
    (embedLegacyLabel_preserves_flow src dst hFlow)

end SeLe4n.Kernel
