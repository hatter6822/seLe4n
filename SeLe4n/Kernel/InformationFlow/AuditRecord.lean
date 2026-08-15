/-
Copyright (c) 2025 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license.

WS-SM SM8.C: the declassification audit record, extracted below `Model/State`.

`SystemState` mounts the declassification audit trail (SM8.C.8), so the record
type has to sit *below* the state it is stored in.  `InformationFlow/Policy.lean`
imports `Model.State` — it needs `SystemState` for the labeling contexts — so the
record could not stay there without a cycle.

This is the same extraction SM7.A performed for `Architecture.TlbInvalidation`
and SM7.D for `Architecture.CacheInvalidation`: the *operand* type moves to a
pure module below the state, the policy layer that interprets it stays above.
Names and namespace are unchanged (`SeLe4n.Kernel`), so every existing reference
resolves exactly as before; `Policy.lean` imports this module and re-exports
nothing, because nothing needs re-exporting.

Imports are deliberately minimal — `Prelude` for `ObjId` and
`Concurrency.Types` for `CoreId`.  Nothing here depends on `SystemState`,
which is what makes the mount possible.
-/
import SeLe4n.Prelude
import SeLe4n.Kernel.Concurrency.Types

namespace SeLe4n.Kernel

-- ============================================================================
-- WS-E5/H-04: Security domains
-- ============================================================================

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

-- ============================================================================
-- WS-SM SM8.C.5: the authorization basis
-- ============================================================================

/-- WS-SM SM8.C.5: **why** a declassification was permitted.

    Pre-SM8.C this was a bare `String` on `DeclassificationEvent`, which admitted
    any content at all — including one naming a check that never ran, so "the
    recorded basis is the check that passed" was a convention rather than a fact.
    Typing it makes the claim checkable (`declassificationBasisKernelVerified`,
    SM8.C.5).

    Open-endedness is preserved where it was real: `integratorOverride` still
    carries an arbitrary authority string, so a system integrator can record a
    basis the kernel has never heard of.  What the type adds is that the kernel
    can tell that basis apart from one it issued itself, which is exactly the
    distinction an audit consumer needs (`kernelVerifiable`). -/
inductive DeclassificationBasis where
  /-- The `DeclassificationPolicy.canDeclassify` gate authorized the downgrade.
      This is the only basis the kernel itself produces. -/
  | policyRule
  /-- An out-of-band system-integrator authority permitted the downgrade.  The
      kernel neither issues nor verifies these; `authority` is the integrator's
      own designation, reproduced verbatim in the rendered audit record. -/
  | integratorOverride (authority : String)
  deriving Repr, DecidableEq

/-- WS-SM SM8.C.5: the audit record's external rendering, **with the trust bit
    carried as data** rather than left for a consumer to infer from the
    designation.

    `designation` is the human-readable string external analysis tools have
    always consumed; `kernelIssued` is the kernel's own verdict on whether it
    produced that basis.  The pair is what an audit consumer should read —
    see `DeclassificationBasis.render_not_injective` for why the designation
    alone is not enough. -/
structure RenderedDeclassificationBasis where
  /-- Whether the kernel itself issued this basis (`DeclassificationBasis.kernelVerifiable`). -/
  kernelIssued : Bool
  /-- The human-readable designation (`DeclassificationBasis.render`). -/
  designation : String
  deriving Repr, DecidableEq

namespace DeclassificationBasis

/-- WS-SM SM8.C.5: the audit record's human-readable designation.  External
    analysis tools consumed the pre-SM8.C `String` field directly, so the two
    bases the tree ever recorded render to the byte-identical strings they had
    before (`"DeclassificationPolicy.canDeclassify"` and the integrator's own
    designation) — typing the field changed what the *kernel* can conclude, not
    what an audit consumer reads.

    This function is **not injective** (`render_not_injective`), so it must not
    be used as a trust signal on its own.  `renderTagged` is the rendering that
    is safe to consume. -/
def render : DeclassificationBasis → String
  | .policyRule => "DeclassificationPolicy.canDeclassify"
  | .integratorOverride authority => authority

/-- WS-SM SM8.C.5: whether the kernel can **check** this basis against its own
    policy configuration.  True for the gate the kernel runs, false for an
    out-of-band authority it has no way to evaluate.

    An audit consumer reads this as: a `false` here means the event did not come
    from the kernel's declassification path — see
    `auditLogKernelIssued` in `InformationFlow/DeclassificationPerCore.lean`,
    which turns that into a decidable property of a whole log. -/
def kernelVerifiable : DeclassificationBasis → Bool
  | .policyRule => true
  | .integratorOverride _ => false

/-- WS-SM SM8.C.5: the kernel's own basis renders to the pre-SM8.C literal, so
    the audit record an external tool sees is unchanged by the typing. -/
theorem render_policyRule : render .policyRule = "DeclassificationPolicy.canDeclassify" := rfl

/-- WS-SM SM8.C.5: an integrator override renders to its authority verbatim —
    the kernel neither rewrites nor interprets it. -/
theorem render_integratorOverride (authority : String) :
    render (.integratorOverride authority) = authority := rfl

/-- WS-SM SM8.C.5: exactly one basis is kernel-verifiable.  Load-bearing rather
    than decorative: `authorizationBasis_perCore` concludes that every event the
    kernel recorded passes its own check, and that conclusion is only meaningful
    because some basis fails it. -/
theorem kernelVerifiable_iff_policyRule (b : DeclassificationBasis) :
    b.kernelVerifiable = true ↔ b = .policyRule := by
  cases b <;> simp [kernelVerifiable]

/-- WS-SM SM8.C.5: **the designation alone cannot be trusted** — an integrator
    may name its authority with the kernel's own literal, and the two render
    identically.

    Stated as a theorem rather than a caution in prose because it is the entire
    justification for `renderTagged`: a consumer that reads `render` and infers
    "the kernel authorized this" is reading a forgeable field.  Nothing in the
    kernel is wrong here — the typed `authorizationBasis` on the event always
    distinguishes the two — but the *rendering* loses the distinction, and this
    is where an external analysis tool would lose it. -/
theorem render_not_injective :
    render (.integratorOverride "DeclassificationPolicy.canDeclassify") = render .policyRule := rfl

/-- WS-SM SM8.C.5: the rendering that is safe to consume — the designation
    paired with the kernel's own verdict on who issued it. -/
def renderTagged (b : DeclassificationBasis) : RenderedDeclassificationBasis :=
  { kernelIssued := b.kernelVerifiable, designation := b.render }

/-- WS-SM SM8.C.5: the tagged rendering carries the kernel's verdict verbatim —
    a consumer reads the trust bit rather than parsing it out of a string. -/
@[simp] theorem renderTagged_kernelIssued (b : DeclassificationBasis) :
    (renderTagged b).kernelIssued = b.kernelVerifiable := rfl

/-- WS-SM SM8.C.5: the tagged rendering's designation is the untagged one, so
    nothing an external tool already displays changes. -/
@[simp] theorem renderTagged_designation (b : DeclassificationBasis) :
    (renderTagged b).designation = b.render := rfl

/-- WS-SM SM8.C.5: **the tagged rendering determines the basis** — the property
    `render` does not have (`render_not_injective`).

    The forging case is exactly the one that motivated the tag: an integrator
    override whose authority string is the kernel's own literal renders to the
    same designation, but carries `kernelIssued = false`, so the pair still
    separates them. -/
theorem renderTagged_injective {b₁ b₂ : DeclassificationBasis}
    (h : renderTagged b₁ = renderTagged b₂) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;>
    simp [renderTagged, render, kernelVerifiable,
      RenderedDeclassificationBasis.mk.injEq] at h ⊢ <;> exact h

/-- WS-SM SM8.C.5: the tagged rendering's trust bit is set exactly on the
    kernel's own basis — the consumer-facing form of
    `kernelVerifiable_iff_policyRule`. -/
theorem renderTagged_kernelIssued_iff_policyRule (b : DeclassificationBasis) :
    (renderTagged b).kernelIssued = true ↔ b = .policyRule :=
  kernelVerifiable_iff_policyRule b

end DeclassificationBasis

-- ============================================================================
-- V6-H (M-IF-6): the declassification event and the audit log
-- ============================================================================

/-- V6-H (M-IF-6): Record of a declassification event for audit purposes.

    Every declassification operation produces a `DeclassificationEvent`
    recording the source domain, destination domain, authorization basis,
    the originating core, and a monotonic timestamp. The audit trail enables
    post-hoc analysis of information-flow boundary crossings.

    **Producer**: `declassifyStoreOnCore`
    (`InformationFlow/DeclassificationPerCore.lean`) — the audited per-core form
    of the `Enforcement/Soundness.lean` gate `declassifyStore`.  It threads the
    append-only log through the operation and appends the event itself, so
    recording is not left to the caller: a successful downgrade and its audit
    entry are one step (`declassifyStoreOnCore_records_one`).

    Until WS-SM SM8.C this docstring said the enforcement wrappers produced
    events and the caller was responsible for recording them.  Neither was
    true — nothing in the tree constructed a `DeclassificationEvent`, so the
    audit trail was a type with no writer.  Per the implement-the-improvement
    rule the producer was built rather than the claim weakened. -/
structure DeclassificationEvent where
  /-- Source domain initiating the declassification. -/
  srcDomain : SecurityDomain
  /-- Destination domain receiving the declassified information. -/
  dstDomain : SecurityDomain
  /-- Object ID of the target being declassified to. -/
  targetObject : SeLe4n.ObjId
  /-- Authorization basis for this declassification: which policy rule or
      system-integrator authority permitted the downgrade.  Rendered for
      external analysis tools by `DeclassificationBasis.renderTagged`; checked
      by the kernel through `DeclassificationBasis.kernelVerifiable`. -/
  authorizationBasis : DeclassificationBasis
  /-- Monotonic event counter (not wall-clock time — the kernel has no
      notion of real time). Used for ordering events in the audit log.

      The counter is **global**, not per-core: `declassifyStoreOnCore` derives
      it from the length of the whole log, so two events recorded on different
      cores are totally ordered and a cross-core chain can be reconstructed
      (`declassificationAuditLog_timestamp_identifies_event`).  A per-core
      counter would collide across cores and lose exactly that ordering. -/
  timestamp : Nat
  /-- WS-SM SM8.C.1: the core the declassification was performed on.

      Plan `docs/planning/SMP_INFORMATION_FLOW_PLAN.md` §4.3: when a thread on
      one core declassifies state observed on another (via cross-core IPC), the
      audit trail must record where the downgrade happened, or a chain spanning
      cores cannot be attributed.  Deliberately **not** defaulted: a default
      would silently attribute every event to the boot core, which is the exact
      failure the field exists to prevent. -/
  originatingCore : Concurrency.CoreId
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

/-- WS-SM SM8.C.3: **every declassification event names a core that exists.**

    `CoreId` is `Fin numCores`, so this holds by construction rather than by a
    range check — which is the point: the SM0.E typed identifier makes an
    out-of-range attribution a type error, not a runtime one.  Stated anyway as
    the checked witness of that design: if a future cut ever widens the field to
    a raw `Nat` (to carry, say, an affinity slot from a platform that numbers
    cores sparsely), this theorem stops being provable and the widening has to
    supply a real bound. -/
theorem declassificationEvent_originatingCore_valid (e : DeclassificationEvent) :
    e.originatingCore.val < Concurrency.numCores :=
  e.originatingCore.isLt

/-- WS-SM SM8.C.3: the enumeration form — every event's core is one the
    per-core audit partition (`auditLogOnCore`) actually visits.  This is the
    half `declassificationEvent_originatingCore_valid` does not give: a bound
    says the index is in range, membership in `allCores` says the sweep that
    builds the per-core views reaches it. -/
theorem declassificationEvent_originatingCore_mem_allCores (e : DeclassificationEvent) :
    e.originatingCore ∈ Concurrency.allCores :=
  Concurrency.mem_allCores _

/-- WS-SM SM8.C.3: the whole-log form — no audit log, however assembled, can
    contain an event attributed to a core outside the enumeration.  Consumed by
    `declassificationAuditLog_partitions_by_core`, whose per-core sum would
    otherwise have to exclude the possibility of an unreachable slice. -/
theorem declassificationAuditLog_originatingCores_valid (log : DeclassificationAuditLog) :
    ∀ e ∈ log, e.originatingCore ∈ Concurrency.allCores :=
  fun e _ => declassificationEvent_originatingCore_mem_allCores e

-- ============================================================================
-- WS-SM SM8.C.8: the audit log's capacity bound
-- ============================================================================

/-! ## WS-SM SM8.C.8 — bounding the mounted trail

`SystemState.declassificationAuditLog` is durable kernel state written by the
live `.declassify` syscall, so it needs a capacity bound for the same reason
`objectIndex` does: an unbounded kernel-resident list is an allocation a
userspace caller controls.

The behaviour **at** the bound is a security decision, not a convenience one.
Two options exist and only one is sound here:

* **Drop an entry** (ring buffer, drop-oldest, or drop-newest) keeps the
  downgrade available and loses the record of it.  A downgrade the kernel
  authorized and did not record is precisely what SM8.C exists to make
  impossible.
* **Refuse the downgrade** keeps the trail complete and loses availability of
  the operation.  A refused declassification is a denial, not a leak.

So the bound is **fail-closed**: `recordDeclassificationChecked` returns `none`
at capacity and the caller must fail the whole operation, which is what
`declassifyStoreOnCore` does.  The property this buys is
`declassifyStoreOnCore_never_unaudited` — an authorized downgrade is either
recorded or does not happen.

The availability cost is real and is *not* mitigated in this cut, because the
only sound mitigation is a consumer that drains the trail, and no read
interface exists yet (registered as SM8.E debt in
`docs/planning/SMP_INFORMATION_FLOW_PLAN.md`).  A future ring buffer would have
to record its own overflow — a dropped entry that leaves no trace of the drop
is the same unaudited downgrade in a different disguise. -/

/-- WS-SM SM8.C.8: capacity of the mounted declassification audit trail.

    Sized to the same order as the kernel's other bounded per-state lists rather
    than to `maxObjects` (65536): the trail records *policy exceptions*, and a
    configuration in which a quarter of a thousand authorized downgrades occur
    before any consumer drains the log is one whose declassification policy is
    the thing to look at.  The constant is a configuration choice, not a
    correctness one — every theorem here is stated against the name. -/
def maxDeclassificationAuditEntries : Nat := 256

/-- WS-SM SM8.C.8: the capacity invariant.  Mounted as a
    `proofLayerInvariantBundle` conjunct (`Architecture/Invariant.lean`), so
    every transition that touches the trail must carry it. -/
def auditLogBounded (log : DeclassificationAuditLog) : Prop :=
  log.length ≤ maxDeclassificationAuditEntries

/-- WS-SM SM8.C.8: decidable form of the capacity invariant. -/
instance (log : DeclassificationAuditLog) : Decidable (auditLogBounded log) :=
  inferInstanceAs (Decidable (log.length ≤ _))

/-- WS-SM SM8.C.8: the empty trail is bounded — the boot witness. -/
theorem auditLogBounded_nil : auditLogBounded ([] : DeclassificationAuditLog) := by
  simp [auditLogBounded]

/-- WS-SM SM8.C.8: **fail-closed** append.  Returns `none` at capacity so the
    caller must fail the operation rather than perform an unrecorded downgrade.

    `recordDeclassification` (the V6-H primitive) stays as it was: it is the
    pure append, used wherever the bound is established separately.  This is
    the form the mounted trail is written through. -/
def recordDeclassificationChecked
    (log : DeclassificationAuditLog)
    (event : DeclassificationEvent) : Option DeclassificationAuditLog :=
  if log.length < maxDeclassificationAuditEntries then
    some (recordDeclassification log event)
  else
    none

/-- WS-SM SM8.C.8: the checked append succeeds exactly below capacity. -/
theorem recordDeclassificationChecked_isSome_iff
    (log : DeclassificationAuditLog) (event : DeclassificationEvent) :
    (recordDeclassificationChecked log event).isSome = true ↔
      log.length < maxDeclassificationAuditEntries := by
  unfold recordDeclassificationChecked
  split <;> simp_all

/-- WS-SM SM8.C.8: below capacity the checked append **is** the plain append —
    nothing about the recorded event changes, only whether it is recorded. -/
theorem recordDeclassificationChecked_eq_record
    (log : DeclassificationAuditLog) (event : DeclassificationEvent)
    (hRoom : log.length < maxDeclassificationAuditEntries) :
    recordDeclassificationChecked log event = some (recordDeclassification log event) := by
  simp [recordDeclassificationChecked, hRoom]

/-- WS-SM SM8.C.8: at capacity the checked append refuses.  The dual of
    `recordDeclassificationChecked_eq_record`, and the reason a declassification
    can fail for a reason that is neither policy nor authority. -/
theorem recordDeclassificationChecked_eq_none
    (log : DeclassificationAuditLog) (event : DeclassificationEvent)
    (hFull : maxDeclassificationAuditEntries ≤ log.length) :
    recordDeclassificationChecked log event = none := by
  simp [recordDeclassificationChecked, Nat.not_lt.mpr hFull]

/-- WS-SM SM8.C.8: the checked append preserves the capacity invariant.

    Note this is *unconditional* in the pre-state bound: success already implies
    there was room, so the post-state bound follows from the guard alone.  That
    is what makes the conjunct carriable through the live path without threading
    a precondition. -/
theorem recordDeclassificationChecked_preserves_bounded
    (log log' : DeclassificationAuditLog) (event : DeclassificationEvent)
    (hStep : recordDeclassificationChecked log event = some log') :
    auditLogBounded log' := by
  unfold recordDeclassificationChecked at hStep
  split at hStep
  · rename_i hRoom
    have : log' = recordDeclassification log event := by
      exact (Option.some.inj hStep).symm
    subst this
    simp [auditLogBounded, recordDeclassification]
    omega
  · exact absurd hStep (by simp)

/-- WS-SM SM8.C.8: a successful checked append records exactly the event asked
    for and preserves every earlier one — the no-loss property. -/
theorem recordDeclassificationChecked_records
    (log log' : DeclassificationAuditLog) (event : DeclassificationEvent)
    (hStep : recordDeclassificationChecked log event = some log') :
    event ∈ log' ∧ (∀ e ∈ log, e ∈ log') ∧ log'.length = log.length + 1 := by
  unfold recordDeclassificationChecked at hStep
  split at hStep
  · have hEq : log' = recordDeclassification log event := (Option.some.inj hStep).symm
    subst hEq
    exact ⟨recordDeclassification_contains_new log event,
           recordDeclassification_preserves_existing log event,
           recordDeclassification_length log event⟩
  · exact absurd hStep (by simp)

end SeLe4n.Kernel
