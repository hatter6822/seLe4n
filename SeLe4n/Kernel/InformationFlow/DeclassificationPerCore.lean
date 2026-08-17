-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM8.C — the per-core declassification audit
-- (docs/planning/SMP_INFORMATION_FLOW_PLAN.md §4.3 / §5 SM8.C.1 … SM8.C.7).

import SeLe4n.Kernel.InformationFlow.CovertChannelPerCore
import SeLe4n.Kernel.InformationFlow.Declassification
-- WS-SM SM9.A.4a: the reader whose observations the equivalence below describes.
-- Production, and imported here rather than the other way round: the reader must
-- not pull the SM8.A/SM8.B non-interference layer into the live syscall path.
import SeLe4n.Kernel.InformationFlow.AuditRead

/-!
# WS-SM SM8.C — the per-core declassification audit

Plan `docs/planning/SMP_INFORMATION_FLOW_PLAN.md` §4.3 and §5 sub-tasks
SM8.C.1 … SM8.C.7.  `NonInterferencePerCore` proves what an SMP kernel does not
leak and `CovertChannelPerCore` records what it does; this module covers the one
path that is *allowed* to move information down the lattice — a declassification
— and makes the resulting audit trail SMP-faithful.

Before this cut the declassification surface was a gate with no record.
`declassifyStore` (`Enforcement/Soundness.lean`) checked its two conditions and
stored the object; `DeclassificationEvent` (`Policy.lean`) described an audit
record whose docstring said the enforcement wrappers produced it and the caller
recorded it.  Neither happened: nothing in the tree constructed a
`DeclassificationEvent`, so the audit log was a type with no writer, and under
SMP it would not have been enough anyway — an event that does not say *where* it
happened cannot attribute a chain that crosses cores.

* §1 — the audit log as a **totally ordered** record.  Timestamps are the log
  position, so every kernel producer computes the ordering rather than
  remembering to maintain it, and a timestamp identifies an event across every
  core.  Well-formedness stays a *checkable predicate* because the V6-H
  primitive `recordDeclassification` accepts an arbitrary event.
* §2 (SM8.C.1) — `declassifyStoreOnCore`, the **producer**: the same gate,
  threading the log, appending exactly one event per authorized downgrade.
* §3 (SM8.C.3) — **attribution**: `declassifyStoreFromCore` derives the source
  domain from the subject the executing core is actually running, so a caller
  cannot record a domain it does not hold.
* §4 (SM8.C.4) — `DeclassificationEvent_perCore_audit`: the per-core views
  partition the log exactly, and no event is lost.
* §5 (SM8.C.2) — cross-core **chains** in the audit trail, and why a per-core
  view cannot see one.
* §6 (SM8.C.6) — the cross-core declassification **rules**, including the one
  SM8.B built `endpointFlowCheck_restricted_subset_perCore` for: a per-endpoint
  policy override can never authorize a downgrade — stated both at the model
  level and, since this cut wires the policy into the live gates (SM8.B's
  registered debt (a)), on the live `endpointFlowGate`, where it needs no
  restriction hypothesis at all.
* §7 (SM8.C.5) — `authorizationBasis_perCore`: every event the kernel records
  passes the kernel's own check, on whatever core it ran.
* §8 — the declassification's own per-core non-interference, and the statement
  that auditing opens no channel of its own.
* §10 (SM8.C.9) — the **live** declassification, per-core: the transition itself
  lives in the production module `InformationFlow/Declassification.lean` (the
  `.declassify` syscall's arm imports it); what is here is its ∀-core
  non-interference and its per-core audit properties.
* §11 — **scope, stated as witnesses**: four properties this phase does not have,
  each a theorem rather than a caveat.
* §12 — **run-level completeness**: a run of `n` authorized downgrades records
  exactly `n` attributed entries, loses none, stays well-formed and within
  capacity, and writes nothing but the trail.
* §13 — the rules as data, each carrying the theorem that makes it a fact.

**Scope boundary, stated rather than left implicit.**  A *refused*
declassification produces no audit entry: the V6-H record shape has no outcome
field, and its `authorizationBasis` names what *permitted* the downgrade, so
there is nothing for a refusal to record.  The refusal itself is fail-closed
(`declassifyStoreOnCore_denied_no_audit_entry` — no state change and no log
entry), so this is a monitoring gap, not an enforcement one: an intrusion
detector cannot count rejected attempts.  Registered as SM8.C follow-on work in
the plan's SM8.C record rather than left in a source comment.

Axiom-clean: every declaration depends only on the standard foundational axioms
(`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId allCores)

-- ============================================================================
-- §1  The audit log as a totally ordered record
-- ============================================================================
--
-- `DeclassificationEvent.timestamp` is documented as a monotonic counter.  Left
-- as a free `Nat` that is a caller convention — any producer could write any
-- number, and two producers on two cores would write the same one.  The audited
-- operation in §2 derives it from the length of the *whole* log, which makes
-- "timestamp = position" an invariant this section states, checks and preserves.

-- `auditTimestampsFrom`, `declassificationAuditLogWellFormed`, their indexed
-- characterisations, the append/drop algebra and
-- `declassificationAuditLog_timestamp_identifies_event` live in
-- `SeLe4n.Kernel.InformationFlow.AuditRecord`, below `Model.State`.
--
-- WS-SM SM9.A.1a moved them: the SM9.A drain is a *production* transition (a
-- live syscall arm) and owes `auditTimestampsFrom`-preservation, so the
-- predicate has to be visible from production code — the same extraction
-- SM8.C.8 performed for the record type itself.  Same namespace, so every
-- reference below resolves unchanged.  What stays here is the per-core theory
-- built on top of them (§4's views, §5's chains).

-- ============================================================================
-- §2  SM8.C.1 — the audited per-core declassification (the producer)
-- ============================================================================
--
-- `declassifyStore` gates and stores.  What it never did is record, which left
-- `DeclassificationEvent`'s docstring describing a producer that did not exist.
-- The audited form below writes the **mounted** trail
-- (`SystemState.declassificationAuditLog`, SM8.C.8) inside the operation, so a
-- successful downgrade and its audit entry are one step: there is no window in
-- which the store has happened and the record has not, and no caller convention
-- to forget.
--
-- Up to SM8.C.8 the trail was a value threaded through the operation.  That form
-- could only relate hops *within* one call, which was enough while nothing could
-- reach the surface; with the live `.declassify` syscall each hop is a separate
-- kernel entry, so the trail had to become state.

/-- WS-SM SM8.C.1: **the audited declassification.**  The `Enforcement/Soundness`
gate, run on core `c`, writing the mounted audit trail: on success the object is
stored *and* the event is appended; on refusal the operation fails and the trail
is the trail it started with.

**The decision is taken first, then capacity, and refusal is total.**  Both
orderings give the same successes and only one is safe: checking capacity first
would tell a caller whose downgrade the *policy* refuses that the trail is full,
and occupancy is a function of how many authorized downgrades other subjects
performed.  Capacity is still checked before the store, so there is no arm on
which the store has happened and the record has not — which is what
`declassifyStoreOnCore_never_unaudited` rests on: an authorized downgrade is
either recorded or does not happen.

The state effect is exactly `declassifyStore`'s plus the appended entry
(`declassifyStoreOnCore_ok_inv`), so every theorem the tree already proves about
the unaudited gate — `enforcementSoundness_declassifyStore`,
`declassifyStore_NI` — carries over unchanged.  Auditing adds a record, not a
transition. -/
def declassifyStoreOnCore
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) : Kernel Unit :=
  fun st =>
    match declassificationDecision ctx declPolicy srcDomain dstDomain with
    | .error err => .error err
    | .ok () =>
        match recordDeclassificationChecked st.declassificationAuditLog
            (declassificationEventOnCore c srcDomain dstDomain targetId
              st.declassificationAuditEpoch st.declassificationAuditLog) with
        | none => .error .auditLogCapacityExceeded
        | some log' =>
            match declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st with
            | .ok ((), st') => .ok ((), { st' with declassificationAuditLog := log' })
            | .error err => .error err

/-- WS-SM SM8.C.1: the forward direction — with room in the trail, a successful
gate gives a successful audited step, with the state the gate produced and the
trail it grew. -/
theorem declassifyStoreOnCore_of_ok
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hRoom : st.declassificationAuditLog.length < maxDeclassificationAuditEntries)
    (hStep : declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .ok ((), st')) :
    declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), { st' with
        declassificationAuditLog := declassifyStoreTrail c srcDomain dstDomain targetId st }) := by
  have hDec : declassificationDecision ctx declPolicy srcDomain dstDomain = .ok () := by
    obtain ⟨hDenied, hAuth⟩ := enforcementSoundness_declassifyStore ctx declPolicy srcDomain
      dstDomain targetId obj st st' hStep
    exact (declassificationDecision_ok_iff ctx declPolicy srcDomain dstDomain).mpr ⟨hDenied, hAuth⟩
  unfold declassifyStoreOnCore
  rw [hDec, recordDeclassificationChecked_eq_record _ _ hRoom]
  simp [hStep]

/-- WS-SM SM8.C.1: a refused gate refuses the audited step, **with the same
error**.  Fail-closed, and — since the decision runs first — with no capacity
information mixed in: a caller the policy refuses gets the policy's error
whatever the trail holds. -/
theorem declassifyStoreOnCore_of_error
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState) (err : KernelError)
    (hStep : declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .error err) :
    declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .error err := by
  -- the gate is the decision followed by a store that cannot fail, so a gate
  -- error IS the decision's error
  have hBind := declassifyStore_eq_decision_bind ctx declPolicy srcDomain dstDomain targetId obj st
  rw [hStep] at hBind
  unfold declassifyStoreOnCore
  obtain ⟨dec, hDec⟩ :
      ∃ d, declassificationDecision ctx declPolicy srcDomain dstDomain = d := ⟨_, rfl⟩
  rw [hDec] at hBind ⊢
  cases dec with
  | error e => simp only [Except.bind, Except.error.injEq] at hBind; rw [hBind]
  | ok u => cases u; simp [Except.bind, storeObject] at hBind

/-- WS-SM SM8.C.8 (**fail-closed at capacity**): a full trail refuses an
*authorized* downgrade outright, with the discriminant that says why.

The load-bearing half of the capacity design.  The alternative — drop an entry
and let the downgrade through — produces a state in which the kernel authorized
a cross-domain flow and no record of it exists, which is the failure the whole
phase is built to exclude.

The `hAuthorized` premise is the confinement: a caller the policy refuses never
reaches the capacity check, so trail occupancy is invisible to it
(`declassifyStoreOnCore_of_error`). -/
theorem declassifyStoreOnCore_audit_log_full
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState)
    (hAuthorized : declassificationDecision ctx declPolicy srcDomain dstDomain = .ok ())
    (hFull : maxDeclassificationAuditEntries ≤ st.declassificationAuditLog.length) :
    declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .error .auditLogCapacityExceeded := by
  unfold declassifyStoreOnCore
  rw [hAuthorized, recordDeclassificationChecked_eq_none _ _ hFull]

/-- WS-SM SM8.C.1 (**the transport lemma**): a successful audited step decomposes
into the gate's own success, room in the trail, and exactly one appended event.

This is what makes the audit non-invasive: downstream reasoning about the
audited operation rewrites to reasoning about `declassifyStore`, which is where
the enforcement and non-interference theorems already live. -/
theorem declassifyStoreOnCore_ok_inv
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    st.declassificationAuditLog.length < maxDeclassificationAuditEntries ∧
    ∃ stGate,
      declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .ok ((), stGate) ∧
      st' = { stGate with
        declassificationAuditLog := declassifyStoreTrail c srcDomain dstDomain targetId st } := by
  unfold declassifyStoreOnCore at hStep
  -- Generalise each scrutinee *before* casing on it: a bare `cases h : …` would
  -- rewrite the goal's own occurrence too, leaving a conclusion about the case
  -- value rather than about the gate.
  obtain ⟨dec, hDecEq⟩ :
      ∃ d, declassificationDecision ctx declPolicy srcDomain dstDomain = d := ⟨_, rfl⟩
  rw [hDecEq] at hStep
  cases dec with
  | error e => simp at hStep
  | ok u =>
  cases u
  obtain ⟨rec, hRec⟩ : ∃ r, recordDeclassificationChecked st.declassificationAuditLog
      (declassificationEventOnCore c srcDomain dstDomain targetId
        st.declassificationAuditEpoch st.declassificationAuditLog) = r := ⟨_, rfl⟩
  rw [hRec] at hStep
  cases rec with
  | none => simp at hStep
  | some log' =>
    have hRoom : st.declassificationAuditLog.length < maxDeclassificationAuditEntries :=
      (recordDeclassificationChecked_isSome_iff _ _).mp (by rw [hRec]; rfl)
    have hLog' : log' = recordDeclassification st.declassificationAuditLog
        (declassifyStoreEvent c srcDomain dstDomain targetId st) := by
      rw [recordDeclassificationChecked_eq_record _ _ hRoom] at hRec
      exact (Option.some.inj hRec).symm
    obtain ⟨res, hRes⟩ :
        ∃ r, declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = r := ⟨_, rfl⟩
    rw [hRes] at hStep
    cases res with
    | error err => simp at hStep
    | ok pair =>
      obtain ⟨u, stGate⟩ := pair
      cases u
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      refine ⟨hRoom, stGate, hRes, ?_⟩
      rw [← hStep.2, hLog']

/-- WS-SM SM8.C.1: **exactly one event per authorized downgrade.**  Not "at
least one" and not "the caller may add one": the trail grows by one, and by the
event the operation itself computed. -/
theorem declassifyStoreOnCore_records_one
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    st'.declassificationAuditLog =
      st.declassificationAuditLog ++ [declassifyStoreEvent c srcDomain dstDomain targetId st] ∧
      st'.declassificationAuditLog.length = st.declassificationAuditLog.length + 1 := by
  obtain ⟨_, stGate, _, hSt'⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain
    dstDomain targetId obj st st' hStep
  subst hSt'
  exact ⟨rfl, recordDeclassification_length _ _⟩

/-- WS-SM SM8.C.1 (**the headline**): *an authorized downgrade is either recorded
or does not happen.*

Every success arm appends exactly one event naming this core, and every arm that
cannot append — a full trail — is an error arm.  The property is what the mount
(SM8.C.8) and the fail-closed capacity bound exist for; with a threaded log it
could only be stated per call, and with a dropping ring buffer it would be
false. -/
theorem declassifyStoreOnCore_never_unaudited
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    ∃ e ∈ st'.declassificationAuditLog,
      e.originatingCore = c ∧ e.srcDomain = srcDomain ∧ e.dstDomain = dstDomain ∧
      e.targetObject = targetId ∧ e.authorizationBasis = .policyRule := by
  obtain ⟨hLog, _⟩ := declassifyStoreOnCore_records_one ctx declPolicy c srcDomain dstDomain
    targetId obj st st' hStep
  refine ⟨declassifyStoreEvent c srcDomain dstDomain targetId st, ?_, rfl, rfl, rfl, rfl, rfl⟩
  rw [hLog]
  exact List.mem_append_right _ (by simp)

/-- WS-SM SM8.C.8: the audited operation carries the 16th
`proofLayerInvariantBundle` conjunct.  Unconditional in the pre-state bound —
success already implies there was room, so the guard alone gives it. -/
theorem declassifyStoreOnCore_preserves_auditLogBounded
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    auditLogBounded st'.declassificationAuditLog := by
  obtain ⟨hLog, hLen⟩ := declassifyStoreOnCore_records_one ctx declPolicy c srcDomain dstDomain
    targetId obj st st' hStep
  obtain ⟨hRoom, _⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain dstDomain
    targetId obj st st' hStep
  unfold auditLogBounded
  omega

/-- WS-SM SM8.C.1: the audit trail is append-only across the operation — every
event already recorded survives.  (`recordDeclassification` is append-only on
its own; this is the statement at the transition, which is where a producer
could otherwise have rewritten history.) -/
theorem declassifyStoreOnCore_preserves_existing
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    ∀ e ∈ st.declassificationAuditLog, e ∈ st'.declassificationAuditLog := by
  obtain ⟨hLog, _⟩ := declassifyStoreOnCore_records_one ctx declPolicy c srcDomain dstDomain
    targetId obj st st' hStep
  intro e hMem
  rw [hLog]
  exact List.mem_append_left _ hMem

/-- WS-SM SM9.A.1a: the audited operation leaves the audit **epoch** alone — it
records, it does not drain.  The frame that lets its well-formedness
preservation be stated against the mounted epoch rather than against a
0-anchored predicate that a drain makes false. -/
theorem declassifyStoreOnCore_declassificationAuditEpoch_eq
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    st'.declassificationAuditEpoch = st.declassificationAuditEpoch := by
  obtain ⟨_, stGate, hGate, hSt'⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain
    dstDomain targetId obj st st' hStep
  subst hSt'
  obtain ⟨hDenied, hAuth⟩ := enforcementSoundness_declassifyStore ctx declPolicy srcDomain
    dstDomain targetId obj st stGate hGate
  rw [declassifyStore_eq_storeObject_when_authorized ctx declPolicy srcDomain dstDomain
    targetId obj st hDenied hAuth] at hGate
  exact storeObject_declassificationAuditEpoch_eq st targetId obj _ hGate

/-- WS-SM SM8.C / SM9.A.1a: the audited operation preserves the trail's
timestamp discipline **at the mounted epoch**, so the total order holds of every
trail an audited run can produce — starting, by
`default_declassificationTrailWellFormed`, from the empty one at boot, and
surviving every drain because the predicate names the epoch rather than
anchoring at `0`.

SM8.C stated this against `declassificationAuditLogWellFormed`, which was the
right statement while nothing could shorten the trail.  With SM9.A's drain that
form is not merely weaker but *false* of a drained trail, so it is restated
here rather than kept alongside. -/
theorem declassifyStoreOnCore_preserves_wellFormed
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hWF : declassificationTrailWellFormed st = true)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    declassificationTrailWellFormed st' = true := by
  obtain ⟨hLog, _⟩ := declassifyStoreOnCore_records_one ctx declPolicy c srcDomain dstDomain
    targetId obj st st' hStep
  have hEpoch := declassifyStoreOnCore_declassificationAuditEpoch_eq ctx declPolicy c srcDomain
    dstDomain targetId obj st st' hStep
  unfold declassificationTrailWellFormed at hWF ⊢
  rw [hLog, hEpoch]
  exact recordDeclassification_preserves_timestampsFrom _ st.declassificationAuditLog _ hWF rfl

/-- WS-SM SM8.C.5 (**audit soundness**): a recorded event's basis is not a
claim, it is a check that ran.  Both halves of `isDeclassificationAuthorized`
held at the moment the event was written: the base policy denied the flow (so
this genuinely was a downgrade) and the declassification policy permitted it. -/
theorem declassifyStoreOnCore_authorized
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    ctx.policy.canFlow srcDomain dstDomain = false ∧
      declPolicy.canDeclassify srcDomain dstDomain = true := by
  obtain ⟨_, stGate, hGate, _⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain
    dstDomain targetId obj st st' hStep
  exact enforcementSoundness_declassifyStore ctx declPolicy srcDomain dstDomain targetId obj
    st stGate hGate

/-- WS-SM SM8.C.1 (**fail-closed, and unaudited**): when either authorization
check fails there is no post-state and no audit entry — the operation cannot
succeed, so nothing is stored and nothing is recorded.

The second half is the scope boundary the module docstring states: a refused
attempt leaves no trace, because the V6-H record has no outcome field to carry
one. -/
theorem declassifyStoreOnCore_denied_no_audit_entry
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState)
    (hDenied : ctx.policy.canFlow srcDomain dstDomain = true ∨
      declPolicy.canDeclassify srcDomain dstDomain = false) :
    ∀ st', declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st ≠
      .ok ((), st') := by
  intro st' hStep
  obtain ⟨hNormal, hDecl⟩ := declassifyStoreOnCore_authorized ctx declPolicy c srcDomain
    dstDomain targetId obj st st' hStep
  cases hDenied with
  | inl h => rw [h] at hNormal; exact Bool.noConfusion hNormal
  | inr h => rw [h] at hDecl; exact Bool.noConfusion hDecl


-- ============================================================================
-- §3  SM8.C.3 — attribution: the recorded subject is the running subject
-- ============================================================================
--
-- `declassifyStoreOnCore` takes its source domain from the caller.  That is the
-- right shape for an internal step, and the wrong shape for an entry point: a
-- record whose subject is whatever the caller wrote is not an audit trail, it is
-- a claim.  `declassifyStoreFromCore` closes that by *reading* the subject off
-- the core the operation runs on, so the event's `srcDomain` is the domain of
-- the thread the kernel was actually executing.
--
-- The obligation "a live path enters here, never at §2" is not left to
-- convention: a Tier-3 negative anchor forbids any production or live module
-- from naming `declassifyStoreOnCore` or `authorizeDeclassificationOnCore`
-- directly, so the attributed wrappers are the only doors.

/-- WS-SM SM8.C.3: **the attributed entry point** for the model primitive.  It
resolves the source domain from core `c`'s current thread rather than accepting
one, and fails closed on a core that is running nothing.

`declassifyStoreOnCore` remains the internal step (§2) — this is the wrapper
that makes the audit record's subject a fact about the state rather than a
parameter.  The live syscall's entry point is
`declassifyObjectFromCore` (production module `InformationFlow/Declassification.lean`),
which adds the same treatment to the *destination*. -/
def declassifyStoreFromCore
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) : Kernel Unit :=
  fun st =>
    match st.scheduler.currentOnCore c with
    | none => .error .illegalState
    | some tid =>
        declassifyStoreOnCore ctx declPolicy c (ctx.threadDomainOf tid) dstDomain targetId obj st

/-- WS-SM SM8.C.3: an idle core cannot declassify — there is no subject to
attribute the downgrade to, so the operation fails closed and the state is
untouched.  (`.illegalState` is the error the syscall entry already uses for
"this core is running nothing"; see
`Platform.FFI.syscallDispatchFromAbi_illegalState_when_no_current`.) -/
theorem declassifyStoreFromCore_no_subject
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState)
    (hIdle : st.scheduler.currentOnCore c = none) :
    declassifyStoreFromCore ctx declPolicy c dstDomain targetId obj st =
      .error .illegalState := by
  simp [declassifyStoreFromCore, hIdle]

/-- WS-SM SM8.C.3: with a subject present the wrapper *is* the internal step at
the subject's own domain — the bridge every §2 theorem travels along. -/
theorem declassifyStoreFromCore_eq_onCore
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid) :
    declassifyStoreFromCore ctx declPolicy c dstDomain targetId obj st =
      declassifyStoreOnCore ctx declPolicy c (ctx.threadDomainOf tid) dstDomain targetId obj
        st := by
  simp [declassifyStoreFromCore, hCur]

/-- WS-SM SM8.C: a successful declassification leaves the scheduler alone — it
is an object-store write.  Needed twice: to carry attribution from the pre-state
to the post-state (below), and for the §8 non-interference confinement. -/
theorem declassifyStore_scheduler_eq
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  obtain ⟨hDenied, hAuth⟩ := enforcementSoundness_declassifyStore ctx declPolicy srcDomain
    dstDomain targetId obj st st' hStep
  rw [declassifyStore_eq_storeObject_when_authorized ctx declPolicy srcDomain dstDomain
    targetId obj st hDenied hAuth] at hStep
  exact storeObject_scheduler_eq st st' targetId obj hStep

/-- WS-SM SM8.C: and the machine alone — the register banks included, which is
what the SM8.A per-core read set needs. -/
theorem declassifyStore_machine_eq
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .ok ((), st')) :
    st'.machine = st.machine := by
  obtain ⟨hDenied, hAuth⟩ := enforcementSoundness_declassifyStore ctx declPolicy srcDomain
    dstDomain targetId obj st st' hStep
  rw [declassifyStore_eq_storeObject_when_authorized ctx declPolicy srcDomain dstDomain
    targetId obj st hDenied hAuth] at hStep
  exact storeObject_machine_eq st st' targetId obj hStep

/-- WS-SM SM8.C.8: the audited step frames the scheduler too — the trail write
is a `SystemState` field update that touches nothing else. -/
theorem declassifyStoreOnCore_scheduler_eq
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  obtain ⟨_, stGate, hGate, hSt'⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain
    dstDomain targetId obj st st' hStep
  subst hSt'
  exact declassifyStore_scheduler_eq ctx declPolicy srcDomain dstDomain targetId obj st stGate
    hGate

/-- WS-SM SM8.C.8: and the machine — the SM8.A per-core read set's other half. -/
theorem declassifyStoreOnCore_machine_eq
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    st'.machine = st.machine := by
  obtain ⟨_, stGate, hGate, hSt'⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain
    dstDomain targetId obj st st' hStep
  subst hSt'
  exact declassifyStore_machine_eq ctx declPolicy srcDomain dstDomain targetId obj st stGate
    hGate

/-- WS-SM SM8.C.3 (**the headline**): every event `declassifyStoreFromCore`
records is attributable — **in the post-state**, which is the state an auditor
inspects.

Unconditional: no hypothesis relates the caller's arguments to the state,
because the wrapper does not accept a source domain to relate.  The post-state
form (rather than the pre-state one, which is definitional) is what carries: a
declassification writes the object store and the trail, so the scheduler slot
the attribution reads is the same slot afterwards. -/
theorem declassifyStoreFromCore_event_attributable
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hStep : declassifyStoreFromCore ctx declPolicy c dstDomain targetId obj st =
      .ok ((), st')) :
    declassificationEventAttributable ctx st'
      (declassifyStoreEvent c (ctx.threadDomainOf tid) dstDomain targetId st) := by
  rw [declassifyStoreFromCore_eq_onCore ctx declPolicy c dstDomain targetId obj st tid hCur]
    at hStep
  have hSched := declassifyStoreOnCore_scheduler_eq ctx declPolicy c (ctx.threadDomainOf tid)
    dstDomain targetId obj st st' hStep
  simp [declassificationEventAttributable, declassificationSubjectDomainOnCore,
    declassificationEventOnCore, hSched, hCur]

/-- WS-SM SM8.C.3 (**scope, stated as a witness**): attributability is a property
of the state **at the moment of recording**, not a durable property of the log.

The subject a core runs changes.  An event recorded while core `c` ran a
domain-2 thread is not attributable against a later state in which `c` runs
something else — or nothing.  So an audit consumer checks an event against the
state at its own timestamp, and a whole-log check against the *current* state is
the wrong reading; it is also the natural one, which is why this is a theorem
rather than a caveat in a docstring.

What survives arbitrarily far is the pair `declassifyStoreFromCore` establishes
at the time of the write: the recorded subject *was* the running subject.  A
deployment that wants that fact checkable later has to snapshot the scheduler
alongside the trail, which is a different feature. -/
theorem declassificationEventAttributable_not_state_stable :
    ∃ (ctx : GenericLabelingContext) (st st' : SystemState) (e : DeclassificationEvent),
      declassificationEventAttributable ctx st e ∧
        ¬ declassificationEventAttributable ctx st' e := by
  refine ⟨{ policy := { canFlow := fun _ _ => false }
            objectDomainOf := fun _ => ⟨0⟩, threadDomainOf := fun _ => ⟨1⟩
            endpointDomainOf := fun _ => ⟨0⟩, serviceDomainOf := fun _ => ⟨0⟩ },
          { (default : SystemState) with scheduler :=
              (default : SystemState).scheduler.setCurrentOnCore bootCoreId (some ⟨1⟩) },
          (default : SystemState),
          { srcDomain := ⟨1⟩, dstDomain := ⟨0⟩, targetObject := ⟨0⟩,
            authorizationBasis := .policyRule, timestamp := 0,
            originatingCore := bootCoreId }, ?_, ?_⟩
  · simp [declassificationEventAttributable, declassificationSubjectDomainOnCore,
      SchedulerState.setCurrentOnCore_currentOnCore_self]
  · have hIdle : (default : SystemState).scheduler.currentOnCore bootCoreId = none :=
      (default_state_perCoreInitialized bootCoreId).1
    simp [declassificationEventAttributable, declassificationSubjectDomainOnCore, hIdle]

/-- WS-SM SM8.C.3 (**the load-bearing negative**): the *unattributed* entry
point genuinely admits an event no state supports.

`declassifyStoreOnCore` consults no scheduler slot, so on a core running nothing
it still records a source domain — the event is well-formed, correctly
authorized, and attributable to no one.  This is why §3 exists and why a live
declassification path must enter through the attributed wrappers; without it,
`declassifyStoreFromCore_event_attributable` would be a theorem about a wrapper
that adds nothing.  The Tier-3 anchor that forbids production modules from
calling §2 directly is the enforcement of what this negative motivates. -/
theorem declassifyStoreOnCore_admits_unattributable :
    ∃ (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy) (c : CoreId)
      (srcDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId) (obj : KernelObject)
      (st st' : SystemState),
      declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
        .ok ((), st') ∧
      ¬ declassificationEventAttributable ctx st'
          (declassifyStoreEvent c srcDomain dstDomain targetId st) := by
  refine ⟨{ policy := { canFlow := fun _ _ => false }
            objectDomainOf := fun _ => ⟨0⟩, threadDomainOf := fun _ => ⟨0⟩
            endpointDomainOf := fun _ => ⟨0⟩, serviceDomainOf := fun _ => ⟨0⟩ },
          { canDeclassify := fun _ _ => true }, bootCoreId, ⟨1⟩, ⟨0⟩, ⟨7⟩,
          .notification { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
                          pendingBadge := none, boundTCB := none },
          (default : SystemState), _, rfl, ?_⟩
  intro hAttr
  -- The post-state's scheduler slot reduces definitionally to the pre-state's
  -- (a declassification writes the object store and the trail), and the boot
  -- state runs nothing on any core — so the attribution reads `none`.
  have hIdle : (default : SystemState).scheduler.currentOnCore bootCoreId = none :=
    (default_state_perCoreInitialized bootCoreId).1
  simp [declassificationEventAttributable, declassificationSubjectDomainOnCore,
    declassificationEventOnCore, hIdle] at hAttr


-- ============================================================================
-- §4  SM8.C.4 — the per-core audit view, and that it partitions the log
-- ============================================================================
--
-- With `originatingCore` on the record, "what did core `c` declassify" is a
-- view of the one global log rather than a separate log per core.  The choice
-- matters: §5 shows a chain that crosses cores lives in no single view, so per-
-- core logs would have lost it.  What this section owes is that the views are
-- nonetheless a faithful *partition* — each event in exactly one, none dropped.

/-- WS-SM SM8.C.4: **core `c`'s audit view** — the events core `c` declassified,
in the order the global log recorded them. -/
def auditLogOnCore (log : DeclassificationAuditLog) (c : CoreId) : DeclassificationAuditLog :=
  log.filter (fun e => e.originatingCore == c)

@[simp] theorem auditLogOnCore_nil (c : CoreId) : auditLogOnCore [] c = [] := rfl

/-- WS-SM SM8.C.4: membership in a view is membership in the log plus the
attribution — the exact characterisation, so a view can neither invent an event
nor keep one that names another core. -/
theorem mem_auditLogOnCore_iff (log : DeclassificationAuditLog) (c : CoreId)
    (e : DeclassificationEvent) :
    e ∈ auditLogOnCore log c ↔ e ∈ log ∧ e.originatingCore = c := by
  simp [auditLogOnCore, List.mem_filter]

/-- WS-SM SM8.C.4: every event appears in the view of the core it names. -/
theorem mem_auditLogOnCore_originatingCore (log : DeclassificationAuditLog)
    {e : DeclassificationEvent} (hMem : e ∈ log) :
    e ∈ auditLogOnCore log e.originatingCore :=
  (mem_auditLogOnCore_iff log e.originatingCore e).mpr ⟨hMem, rfl⟩

/-- WS-SM SM8.C.4: a view is a **sublist**, not merely a subset — the global
order survives the restriction, so an auditor reading one core's events reads
them in the order they happened. -/
theorem auditLogOnCore_sublist (log : DeclassificationAuditLog) (c : CoreId) :
    (auditLogOnCore log c).Sublist log :=
  List.filter_sublist

theorem auditLogOnCore_cons_self (e : DeclassificationEvent)
    (rest : DeclassificationAuditLog) :
    auditLogOnCore (e :: rest) e.originatingCore =
      e :: auditLogOnCore rest e.originatingCore := by
  simp [auditLogOnCore]

theorem auditLogOnCore_cons_ne (e : DeclassificationEvent) (rest : DeclassificationAuditLog)
    (c : CoreId) (hne : e.originatingCore ≠ c) :
    auditLogOnCore (e :: rest) c = auditLogOnCore rest c := by
  simp [auditLogOnCore, hne]

/-- WS-SM SM8.C.4: an empty log contributes zero to every core's view. -/
private theorem sum_auditLogOnCore_lengths_nil (cs : List CoreId) :
    (cs.map (fun c => (auditLogOnCore [] c).length)).sum = 0 := by
  induction cs with
  | nil => rfl
  | cons _ _ ih => simpa [auditLogOnCore] using ih

/-- WS-SM SM8.C.4: an event whose core is outside `cs` contributes nothing to
the views over `cs`.  The disjointness half of the partition count. -/
private theorem sum_auditLogOnCore_lengths_of_not_mem (cs : List CoreId)
    (e : DeclassificationEvent) (rest : DeclassificationAuditLog)
    (hNot : e.originatingCore ∉ cs) :
    (cs.map (fun c => (auditLogOnCore (e :: rest) c).length)).sum =
      (cs.map (fun c => (auditLogOnCore rest c).length)).sum := by
  induction cs with
  | nil => rfl
  | cons c₀ cs ih =>
    simp only [List.mem_cons, not_or] at hNot
    simp only [List.map_cons, List.sum_cons,
      auditLogOnCore_cons_ne e rest c₀ hNot.1, ih hNot.2]

/-- WS-SM SM8.C.4: an event whose core is in a duplicate-free `cs` contributes
exactly one entry to the views over `cs`. -/
private theorem sum_auditLogOnCore_lengths_cons (cs : List CoreId) (hNodup : cs.Nodup)
    (e : DeclassificationEvent) (rest : DeclassificationAuditLog)
    (hMem : e.originatingCore ∈ cs) :
    (cs.map (fun c => (auditLogOnCore (e :: rest) c).length)).sum =
      (cs.map (fun c => (auditLogOnCore rest c).length)).sum + 1 := by
  induction cs with
  | nil => exact absurd hMem List.not_mem_nil
  | cons c₀ cs ih =>
    rw [List.nodup_cons] at hNodup
    by_cases hc : e.originatingCore = c₀
    · subst hc
      have hNot : e.originatingCore ∉ cs := fun h => hNodup.1 h
      simp only [List.map_cons, List.sum_cons, auditLogOnCore_cons_self,
        List.length_cons, sum_auditLogOnCore_lengths_of_not_mem cs e rest hNot]
      omega
    · have hMem' : e.originatingCore ∈ cs := by
        rcases List.mem_cons.mp hMem with h | h
        · exact absurd h hc
        · exact h
      simp only [List.map_cons, List.sum_cons,
        auditLogOnCore_cons_ne e rest c₀ (fun h => hc h), ih hNodup.2 hMem']
      omega

/-- WS-SM SM8.C.4 (`DeclassificationEvent_perCore_audit`, the counting half):
**the per-core views partition the log** — the lengths sum to the log's length,
so no event is dropped and none is double-counted.

`allCores_nodup` is what makes it a partition rather than a cover: without it a
core listed twice would count its own events twice and the sum would exceed the
log.  `declassificationEvent_originatingCore_mem_allCores` (SM8.C.3) is what
makes it a cover rather than a partition of a subset: without it an event could
name a core the sweep never visits and be lost. -/
theorem declassificationAuditLog_partitions_by_core (log : DeclassificationAuditLog) :
    (allCores.map (fun c => (auditLogOnCore log c).length)).sum = log.length := by
  induction log with
  | nil => exact sum_auditLogOnCore_lengths_nil allCores
  | cons e rest ih =>
    rw [sum_auditLogOnCore_lengths_cons allCores SeLe4n.Kernel.Concurrency.allCores_nodup e rest
      (declassificationEvent_originatingCore_mem_allCores e), ih]
    simp [List.length_cons]

/-- WS-SM SM8.C.4 (`DeclassificationEvent_perCore_audit`, the membership half):
**every event is in exactly one view.**  Uniqueness is the content — an event
attributed to two cores would make the per-core audit ambiguous, and the
`Fin`-typed core field is what rules it out. -/
theorem DeclassificationEvent_perCore_audit (log : DeclassificationAuditLog)
    {e : DeclassificationEvent} (hMem : e ∈ log) :
    e ∈ auditLogOnCore log e.originatingCore ∧
      ∀ c : CoreId, e ∈ auditLogOnCore log c → c = e.originatingCore := by
  refine ⟨mem_auditLogOnCore_originatingCore log hMem, ?_⟩
  intro c hIn
  exact ((mem_auditLogOnCore_iff log c e).mp hIn).2.symm

/-- WS-SM SM8.C.4: **within one core's view a timestamp still identifies an
event** — the global result restricted along the sublist.

Stated as identification rather than as an ordering: what an auditor reading a
single core's history needs is that two of its entries with the same timestamp
are the same entry, which is what lets the view be ordered by timestamp without
consulting the global log. -/
theorem auditLogOnCore_timestamp_identifies_event (start : Nat)
    (log : DeclassificationAuditLog)
    (c : CoreId) (hWF : auditTimestampsFrom start log = true)
    {e₁ e₂ : DeclassificationEvent}
    (h₁ : e₁ ∈ auditLogOnCore log c) (h₂ : e₂ ∈ auditLogOnCore log c)
    (hTs : e₁.timestamp = e₂.timestamp) : e₁ = e₂ :=
  declassificationAuditLog_timestamp_identifies_event start log hWF
    ((mem_auditLogOnCore_iff log c e₁).mp h₁).1
    ((mem_auditLogOnCore_iff log c e₂).mp h₂).1 hTs

/-- WS-SM SM8.C.4: the audited operation files its event under the core it ran
on — the per-core view is a view of what that core actually did. -/
theorem declassifyStoreOnCore_recorded_in_own_view
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    declassifyStoreEvent c srcDomain dstDomain targetId st ∈
      auditLogOnCore st'.declassificationAuditLog c := by
  obtain ⟨hLog, _⟩ := declassifyStoreOnCore_records_one ctx declPolicy c srcDomain dstDomain
    targetId obj st st' hStep
  refine (mem_auditLogOnCore_iff _ c _).mpr ⟨?_, rfl⟩
  rw [hLog]
  exact List.mem_append_right _ (by simp)

/-- WS-SM SM8.C.4: and under **no other** core's view.  The dual of the theorem
above, and the one that makes a per-core audit report trustworthy: a core cannot
have another core's downgrade attributed to it.

Stated of an arbitrary event rather than of the audited operation's, because it
holds of any log however assembled — the attribution is carried by the event,
not established by the producer. -/
theorem declassificationEvent_not_in_other_view (log : DeclassificationAuditLog)
    (c' : CoreId) {e : DeclassificationEvent} (hne : c' ≠ e.originatingCore) :
    e ∉ auditLogOnCore log c' := by
  intro hIn
  exact hne ((mem_auditLogOnCore_iff log c' e).mp hIn).2.symm

-- ============================================================================
-- §5  SM8.C.2 — cross-core declassification chains in the audit trail
-- ============================================================================
--
-- Plan §4.3's motivating case: a thread on one core declassifies state that was
-- itself declassified on another.  Each hop is a legitimate, individually
-- authorized downgrade; the *composition* is a path from the first hop's source
-- domain to the last hop's destination that no single hop names.  Two facts
-- follow, and they pull in opposite directions — which is why both are stated:
-- the chain is fully present in the global log (so an auditor can reconstruct
-- it), and it is present in no single core's view (so a per-core audit cannot).

/-- WS-SM SM8.C.2: **a declassification chain** — consecutive hops compose
(one hop's destination domain is the next hop's source) and run in recorded
order (timestamps strictly increase).

The timestamp clause is what makes this a *chain* rather than a set of
compatible events: information can only flow along hops that happened in order,
and §1's global counter is what lets hops on different cores be compared. -/
def declassificationChainLinked : List DeclassificationEvent → Bool
  | [] => true
  | [_] => true
  | e₁ :: e₂ :: rest =>
      (e₁.dstDomain == e₂.srcDomain) && decide (e₁.timestamp < e₂.timestamp) &&
        declassificationChainLinked (e₂ :: rest)

/-- WS-SM SM8.C.2: the domain the chain starts from. -/
def chainSourceDomain : List DeclassificationEvent → Option SecurityDomain
  | [] => none
  | e :: _ => some e.srcDomain

/-- WS-SM SM8.C.2: the domain the chain ends at. -/
def chainTargetDomain (chain : List DeclassificationEvent) : Option SecurityDomain :=
  chain.getLast?.map (fun e => e.dstDomain)

/-- WS-SM SM8.C.2: the cores a chain touches, without repeats.

Built by filtering `allCores` rather than by de-duplicating the chain's own core
list: the result inherits `allCores`'s duplicate-freedom (`chainCores_nodup`)
and its order, so two audits of the same chain report the same list. -/
def chainCores (chain : List DeclassificationEvent) : List CoreId :=
  allCores.filter (fun c => chain.any (fun e => e.originatingCore == c))

/-- WS-SM SM8.C.2: **the chain crosses cores** — two of its hops ran on
different cores.

Stated directly as "two hops disagree" rather than as a count over `chainCores`,
because that is the form every consumer needs: the two witnesses are what shows
no single per-core view holds the chain. -/
def chainIsCrossCore (chain : List DeclassificationEvent) : Bool :=
  chain.any (fun e₁ => chain.any (fun e₂ => e₁.originatingCore != e₂.originatingCore))

/-- WS-SM SM8.C.2: the chain's hops are all in the log — decidable, so an audit
tool can check a candidate chain against a recorded trail. -/
def chainRecordedIn (log : DeclassificationAuditLog) (chain : List DeclassificationEvent) : Bool :=
  chain.all (fun e => decide (e ∈ log))

theorem chainRecordedIn_iff (log : DeclassificationAuditLog)
    (chain : List DeclassificationEvent) :
    chainRecordedIn log chain = true ↔ ∀ e ∈ chain, e ∈ log := by
  simp [chainRecordedIn]

theorem chainIsCrossCore_iff (chain : List DeclassificationEvent) :
    chainIsCrossCore chain = true ↔
      ∃ e₁ ∈ chain, ∃ e₂ ∈ chain, e₁.originatingCore ≠ e₂.originatingCore := by
  simp [chainIsCrossCore]

theorem mem_chainCores_iff (chain : List DeclassificationEvent) (c : CoreId) :
    c ∈ chainCores chain ↔ ∃ e ∈ chain, e.originatingCore = c := by
  simp [chainCores, List.mem_filter, SeLe4n.Kernel.Concurrency.mem_allCores]

theorem chainCores_nodup (chain : List DeclassificationEvent) : (chainCores chain).Nodup :=
  List.Nodup.sublist List.filter_sublist SeLe4n.Kernel.Concurrency.allCores_nodup

/-- A list holding two distinct elements has length at least two.  Stated
generically because it is a fact about lists, not about audit logs. -/
private theorem two_le_length_of_distinct_mem {α : Type} {l : List α} {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) : 2 ≤ l.length := by
  induction l with
  | nil => exact absurd ha List.not_mem_nil
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · have hpos : 0 < xs.length := List.length_pos_of_mem hb'
        simp only [List.length_cons]; omega
    · rcases List.mem_cons.mp hb with rfl | hb'
      · have hpos : 0 < xs.length := List.length_pos_of_mem ha'
        simp only [List.length_cons]; omega
      · have := ih ha' hb'
        simp only [List.length_cons]; omega

/-- WS-SM SM8.C.2: a cross-core chain touches at least two cores — the count
form of `chainIsCrossCore`, for a report that wants a number. -/
theorem chainCores_length_ge_two_of_crossCore (chain : List DeclassificationEvent)
    (hCross : chainIsCrossCore chain = true) : 2 ≤ (chainCores chain).length := by
  obtain ⟨e₁, h₁, e₂, h₂, hne⟩ := (chainIsCrossCore_iff chain).mp hCross
  exact two_le_length_of_distinct_mem
    ((mem_chainCores_iff chain e₁.originatingCore).mpr ⟨e₁, h₁, rfl⟩)
    ((mem_chainCores_iff chain e₂.originatingCore).mpr ⟨e₂, h₂, rfl⟩) hne

/-- WS-SM SM8.C.2 (**the headline, negative half**): a chain that crosses cores
is contained in **no** single core's audit view.

This is the theorem that decides the design.  Keeping one log per core — the
natural SMP implementation, one counter and one buffer per CPU — would put each
hop in a different buffer with no relation between them; the composed downgrade
would be invisible to every reader.  Recording `originatingCore` on the event of
one global log keeps the chain in one place and the attribution with it. -/
theorem crossCoreChain_not_within_one_view (log : DeclassificationAuditLog)
    (chain : List DeclassificationEvent) (hCross : chainIsCrossCore chain = true) (c : CoreId) :
    ¬ (∀ e ∈ chain, e ∈ auditLogOnCore log c) := by
  intro hAll
  obtain ⟨e₁, h₁, e₂, h₂, hne⟩ := (chainIsCrossCore_iff chain).mp hCross
  have hc₁ := ((mem_auditLogOnCore_iff log c e₁).mp (hAll e₁ h₁)).2
  have hc₂ := ((mem_auditLogOnCore_iff log c e₂).mp (hAll e₂ h₂)).2
  exact hne (hc₁.trans hc₂.symm)

/-- WS-SM SM8.C.2 (**the headline, positive half**): two audited
declassifications on two different cores, the second downgrading what the first
produced, leave a linked cross-core chain **in the audit trail** — both hops
recorded, composing, in order, each attributed to the core that performed it.

Together with `crossCoreChain_not_within_one_view` this is SM8.C.2: the chain is
recoverable, and recoverable only from the global log. -/
theorem declassificationChain_recorded_across_cores
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c₁ c₂ : CoreId) (a b d : SecurityDomain)
    (target₁ target₂ : SeLe4n.ObjId) (obj₁ obj₂ : KernelObject)
    (st st₁ st₂ : SystemState)
    (hne : c₁ ≠ c₂)
    (hStep₁ : declassifyStoreOnCore ctx declPolicy c₁ a b target₁ obj₁ st = .ok ((), st₁))
    (hStep₂ : declassifyStoreOnCore ctx declPolicy c₂ b d target₂ obj₂ st₁ = .ok ((), st₂)) :
    ∃ e₁ e₂ : DeclassificationEvent,
      st₂.declassificationAuditLog = st.declassificationAuditLog ++ [e₁, e₂] ∧
      declassificationChainLinked [e₁, e₂] = true ∧
      chainRecordedIn st₂.declassificationAuditLog [e₁, e₂] = true ∧
      chainIsCrossCore [e₁, e₂] = true ∧
      e₁.originatingCore = c₁ ∧ e₂.originatingCore = c₂ ∧
      chainSourceDomain [e₁, e₂] = some a ∧ chainTargetDomain [e₁, e₂] = some d := by
  obtain ⟨hLog₁, hLen₁⟩ := declassifyStoreOnCore_records_one ctx declPolicy c₁ a b target₁ obj₁
    st st₁ hStep₁
  obtain ⟨hLog₂, _⟩ := declassifyStoreOnCore_records_one ctx declPolicy c₂ b d target₂ obj₂
    st₁ st₂ hStep₂
  -- WS-SM SM9.A.1a: recording does not drain, so the second hop is stamped from
  -- the same epoch as the first — which is what keeps the chain's timestamps
  -- strictly increasing now that a timestamp is `epoch + index` rather than an
  -- index.
  have hEpoch₁ := declassifyStoreOnCore_declassificationAuditEpoch_eq ctx declPolicy c₁ a b
    target₁ obj₁ st st₁ hStep₁
  refine ⟨declassifyStoreEvent c₁ a b target₁ st,
          declassifyStoreEvent c₂ b d target₂ st₁, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · rw [hLog₂, hLog₁]; simp [List.append_assoc]
  · -- the hops compose (`b` is both), and the second timestamp is the first plus one
    simp [declassificationChainLinked, declassificationEventOnCore, hLen₁, hEpoch₁]
  · refine (chainRecordedIn_iff _ _).mpr ?_
    intro e hMem
    rw [hLog₂, hLog₁]
    rcases List.mem_cons.mp hMem with rfl | hMem'
    · simp
    · rcases List.mem_cons.mp hMem' with rfl | hEmpty
      · simp
      · exact absurd hEmpty List.not_mem_nil
  · refine (chainIsCrossCore_iff _).mpr ?_
    exact ⟨declassifyStoreEvent c₁ a b target₁ st, by simp,
           declassifyStoreEvent c₂ b d target₂ st₁, by simp, hne⟩

/-- WS-SM SM8.C.2 / SM8.C.3 (**the attributed form**): the same cross-core chain,
recorded by the entry point a live path may actually call.

The theorem above is stated over `declassifyStoreOnCore`, whose source domain is
a parameter — so on its own it says a chain composes when the caller *claims* it
does.  Here both hops enter through `declassifyStoreFromCore`, so each hop's
source domain is read off the core that ran it, and the composition `a → b → d`
is a fact about which subjects were running rather than about what two callers
wrote.  The middle domain `b` is where it bites: hop 1's *destination* is hop 2's
*subject*, so the chain links only if the thread core `c₂` runs really is in the
domain hop 1 downgraded into. -/
theorem declassificationChain_recorded_across_cores_attributed
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c₁ c₂ : CoreId) (b d : SecurityDomain)
    (target₁ target₂ : SeLe4n.ObjId) (obj₁ obj₂ : KernelObject)
    (st st₁ st₂ : SystemState) (tid₁ tid₂ : SeLe4n.ThreadId)
    (hne : c₁ ≠ c₂)
    (hCur₁ : st.scheduler.currentOnCore c₁ = some tid₁)
    (hCur₂ : st₁.scheduler.currentOnCore c₂ = some tid₂)
    (hMid : ctx.threadDomainOf tid₂ = b)
    (hStep₁ : declassifyStoreFromCore ctx declPolicy c₁ b target₁ obj₁ st = .ok ((), st₁))
    (hStep₂ : declassifyStoreFromCore ctx declPolicy c₂ d target₂ obj₂ st₁ = .ok ((), st₂)) :
    ∃ e₁ e₂ : DeclassificationEvent,
      st₂.declassificationAuditLog = st.declassificationAuditLog ++ [e₁, e₂] ∧
      declassificationChainLinked [e₁, e₂] = true ∧
      chainRecordedIn st₂.declassificationAuditLog [e₁, e₂] = true ∧
      chainIsCrossCore [e₁, e₂] = true ∧
      e₁.originatingCore = c₁ ∧ e₂.originatingCore = c₂ ∧
      declassificationEventAttributable ctx st₁ e₁ ∧
      chainSourceDomain [e₁, e₂] = some (ctx.threadDomainOf tid₁) ∧
      chainTargetDomain [e₁, e₂] = some d := by
  rw [declassifyStoreFromCore_eq_onCore ctx declPolicy c₁ b target₁ obj₁ st tid₁ hCur₁] at hStep₁
  rw [declassifyStoreFromCore_eq_onCore ctx declPolicy c₂ d target₂ obj₂ st₁ tid₂ hCur₂] at hStep₂
  subst hMid
  obtain ⟨e₁, e₂, hLog, hLinked, hRec, hCross, hC₁, hC₂, hSrc, hDst⟩ :=
    declassificationChain_recorded_across_cores ctx declPolicy c₁ c₂ (ctx.threadDomainOf tid₁)
      (ctx.threadDomainOf tid₂) d target₁ target₂ obj₁ obj₂ st st₁ st₂ hne hStep₁ hStep₂
  refine ⟨e₁, e₂, hLog, hLinked, hRec, hCross, hC₁, hC₂, ?_, hSrc, hDst⟩
  -- hop 1's event is attributable in the state hop 1 produced (§3's headline)
  have hAttr := declassifyStoreFromCore_event_attributable ctx declPolicy c₁
    (ctx.threadDomainOf tid₂) target₁ obj₁ st st₁ tid₁ hCur₁
    (by rw [declassifyStoreFromCore_eq_onCore ctx declPolicy c₁ (ctx.threadDomainOf tid₂)
              target₁ obj₁ st tid₁ hCur₁]; exact hStep₁)
  -- and the event the chain names *is* that event
  have hE₁ : e₁ = declassifyStoreEvent c₁ (ctx.threadDomainOf tid₁) (ctx.threadDomainOf tid₂)
      target₁ st := by
    obtain ⟨hLog₁, _⟩ := declassifyStoreOnCore_records_one ctx declPolicy c₁
      (ctx.threadDomainOf tid₁) (ctx.threadDomainOf tid₂) target₁ obj₁ st st₁ hStep₁
    obtain ⟨hLog₂, _⟩ := declassifyStoreOnCore_records_one ctx declPolicy c₂
      (ctx.threadDomainOf tid₂) d target₂ obj₂ st₁ st₂ hStep₂
    rw [hLog₂, hLog₁] at hLog
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.append_cancel_left_eq, List.cons.injEq] at hLog
    exact hLog.1.symm
  rw [hE₁]
  exact hAttr

-- ============================================================================
-- §6  SM8.C.6 — the cross-core declassification rules
-- ============================================================================
--
-- What an SMP deployment may conclude from a declassification audit trail, and
-- what it may not.  Four rules, each a theorem rather than a paragraph.

/-- WS-SM SM8.C.6: every hop of a chain was individually authorized. -/
def chainHopsAuthorized (basePolicy : DomainFlowPolicy) (declPolicy : DeclassificationPolicy)
    (chain : List DeclassificationEvent) : Bool :=
  chain.all (fun e =>
    DeclassificationPolicy.isDeclassificationAuthorized basePolicy declPolicy
      e.srcDomain e.dstDomain)

/-- WS-SM SM8.C.6: the chain's **end-to-end** downgrade is itself authorized —
the operator explicitly permitted the path from the first hop's source to the
last hop's destination, not merely each step of it. -/
def chainCompositionAuthorized (basePolicy : DomainFlowPolicy)
    (declPolicy : DeclassificationPolicy) (chain : List DeclassificationEvent) : Bool :=
  match chainSourceDomain chain, chainTargetDomain chain with
  | some src, some dst =>
      DeclassificationPolicy.isDeclassificationAuthorized basePolicy declPolicy src dst
  | _, _ => false

/-- WS-SM SM8.C.6: **the laundering detector.**  A multi-hop chain, every hop
authorized and recorded in order, whose composed downgrade the operator never
authorized.

Decidable, and computed from the audit log alone — which is the point of
recording chains at all: per-hop authorization is checked by the kernel at the
time of each hop, and this is the property only a *reader of the trail* can
check afterwards. -/
def chainLaunders (basePolicy : DomainFlowPolicy) (declPolicy : DeclassificationPolicy)
    (chain : List DeclassificationEvent) : Bool :=
  declassificationChainLinked chain &&
    chainHopsAuthorized basePolicy declPolicy chain &&
    decide (2 ≤ chain.length) &&
    !chainCompositionAuthorized basePolicy declPolicy chain

/-- WS-SM SM8.C.6 (Rule 1 — **composition soundness**): when the composite check
passes, the end-to-end downgrade really was authorized: the base policy denied
the flow (so it is a downgrade) and the declassification policy named it. -/
theorem chainCompositionAuthorized_sound (basePolicy : DomainFlowPolicy)
    (declPolicy : DeclassificationPolicy) (chain : List DeclassificationEvent)
    (src dst : SecurityDomain)
    (hSrc : chainSourceDomain chain = some src)
    (hDst : chainTargetDomain chain = some dst)
    (hAuth : chainCompositionAuthorized basePolicy declPolicy chain = true) :
    basePolicy.canFlow src dst = false ∧ declPolicy.canDeclassify src dst = true := by
  rw [chainCompositionAuthorized, hSrc, hDst] at hAuth
  simp only [DeclassificationPolicy.isDeclassificationAuthorized, Bool.and_eq_true,
    Bool.not_eq_true'] at hAuth
  exact hAuth

/-- WS-SM SM8.C.6 (Rule 2 — **per-hop authorization does not compose**): there
are well-formed policy configurations in which every hop of a chain is
authorized and the composed downgrade is not.

This is declassification laundering, and it is why the audit trail has to record
chains rather than just hops: nothing the kernel checks *at* a hop can see the
composition, because the composition does not exist until the second hop runs —
possibly on another core, possibly much later.

The base policy here is reflexive and transitive (`wellFormed`), so the witness
cannot be dismissed as a degenerate configuration: with `canFlow` the identity
relation, `2 → 1` and `1 → 0` are both authorized downgrades and `2 → 0` is
not. -/
theorem declassificationChain_hop_authorization_does_not_compose :
    ∃ (basePolicy : DomainFlowPolicy) (declPolicy : DeclassificationPolicy)
      (a b d : SecurityDomain),
      basePolicy.wellFormed ∧
      DeclassificationPolicy.isDeclassificationAuthorized basePolicy declPolicy a b = true ∧
      DeclassificationPolicy.isDeclassificationAuthorized basePolicy declPolicy b d = true ∧
      DeclassificationPolicy.isDeclassificationAuthorized basePolicy declPolicy a d = false := by
  refine ⟨{ canFlow := fun src dst => decide (src.id = dst.id) },
          { canDeclassify := fun src dst =>
              (decide (src.id = 2) && decide (dst.id = 1)) ||
              (decide (src.id = 1) && decide (dst.id = 0)) },
          ⟨2⟩, ⟨1⟩, ⟨0⟩, ⟨?_, ?_⟩, by decide, by decide, by decide⟩
  · intro d; simp
  · intro a b c h₁ h₂
    simp only [decide_eq_true_eq] at h₁ h₂ ⊢
    omega

/-- WS-SM SM8.C.6 (Rule 2, on a chain): the detector fires on a real cross-core
chain — two hops on two cores, each authorized, composing to a downgrade the
policy never named.

Concrete rather than existential in the policies alone: the events are the
events an audited run produces (basis `.policyRule`, timestamps 0 and 1, cores 0
and 2), so the property is checked on the shape the trail actually holds. -/
theorem crossCoreChain_launders_witness :
    ∃ (basePolicy : DomainFlowPolicy) (declPolicy : DeclassificationPolicy)
      (chain : List DeclassificationEvent),
      declassificationChainLinked chain = true ∧
      chainIsCrossCore chain = true ∧
      chainHopsAuthorized basePolicy declPolicy chain = true ∧
      chainCompositionAuthorized basePolicy declPolicy chain = false ∧
      chainLaunders basePolicy declPolicy chain = true := by
  refine ⟨{ canFlow := fun src dst => decide (src.id = dst.id) },
          { canDeclassify := fun src dst =>
              (decide (src.id = 2) && decide (dst.id = 1)) ||
              (decide (src.id = 1) && decide (dst.id = 0)) },
          [ { srcDomain := ⟨2⟩, dstDomain := ⟨1⟩, targetObject := ⟨901⟩,
              authorizationBasis := .policyRule, timestamp := 0,
              originatingCore := bootCoreId }
          , { srcDomain := ⟨1⟩, dstDomain := ⟨0⟩, targetObject := ⟨902⟩,
              authorizationBasis := .policyRule, timestamp := 1,
              originatingCore := ⟨2, by decide⟩ } ],
          by decide, by decide, by decide, by decide, by decide⟩

/-- WS-SM SM8.C.6: a gate that admits has a subject.  `endpointFlowCheckAtCore`
returns `false` on a core running nothing, so naming the subject below is
naming, not assuming. -/
theorem endpointFlowCheckAtCore_subject_exists (ctx : GenericLabelingContext)
    (epPolicy : EndpointFlowPolicy) (endpointId : SeLe4n.ObjId) (st : SystemState) (c : CoreId)
    (hAdmitted : endpointFlowCheckAtCore ctx epPolicy endpointId st c = true) :
    ∃ tid : SeLe4n.ThreadId, st.scheduler.currentOnCore c = some tid := by
  cases hCur : st.scheduler.currentOnCore c with
  | none => simp [endpointFlowCheckAtCore, hCur] at hAdmitted
  | some tid => exact ⟨tid, rfl⟩

/-- WS-SM SM8.C.6 (Rule 3 — **an endpoint override is never a declassification
basis**): under the V6-G restriction, a flow the endpoint gate admits **as the
kernel resolves it** — at state `st`, on core `c`, for the thread running there
— is a flow the global policy already admits, and a flow the global policy
admits is by definition not a downgrade.

This is the consumer SM8.B built `endpointFlowCheck_restricted_subset_perCore`
for.  Its content is that IPC cannot be a second, unaudited declassification
path: the only way down the lattice is the explicit `DeclassificationPolicy`,
which produces an audit event every time it is taken (§2).

Stated against `endpointFlowCheckAtCore` rather than the core-free
`endpointFlowCheck` on purpose.  The latter takes neither a state nor a core, so
a per-core statement about it would carry a decorative `c`; the resolved gate is
the one whose subject depends on which core is asking, and that dependence is
exactly what an SMP declassification audit has to reason about. -/
theorem endpointOverride_is_not_a_declassification_basis
    (ctx : GenericLabelingContext) (epPolicy : EndpointFlowPolicy)
    (declPolicy : DeclassificationPolicy) (endpointId : SeLe4n.ObjId)
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hRestricted : endpointPolicyRestricted_perCore ctx.policy epPolicy)
    (hAdmitted : endpointFlowCheckAtCore ctx epPolicy endpointId st c = true) :
    DeclassificationPolicy.isDeclassificationAuthorized ctx.policy declPolicy
      (ctx.threadDomainOf tid) (ctx.endpointDomainOf endpointId) = false := by
  rw [endpointFlowCheckAtCore, hCur] at hAdmitted
  have hGlobal := endpointFlowCheck_restricted_subset_perCore ctx epPolicy endpointId
    (ctx.threadDomainOf tid) (ctx.endpointDomainOf endpointId) c hRestricted hAdmitted
  simp only [genericFlowCheck, domainFlowsTo] at hGlobal
  simp [DeclassificationPolicy.isDeclassificationAuthorized, hGlobal]

/-- WS-SM SM8.C.6 (Rule 3, **the load-bearing negative**): drop the restriction
and the endpoint override becomes a downgrade path that leaves no trace.

The flow is admitted at the endpoint, the global policy denies it, and — because
IPC produces no `DeclassificationEvent` — nothing is recorded.  So
`endpointPolicyRestricted_perCore` is not a tidiness property: it is what keeps
the audit trail complete, and a deployment that configures a widening endpoint
override has an unaudited declassification channel.

This theorem is about `endpointFlowCheck`, the WS-E5/H-04 form in which an
override **replaces** the global policy.  SM8.B registered the fact that nothing
consulted a configured policy at all as debt (a); this cut closes it, and closes
it with the *other* semantics: the live gate `endpointFlowGate` **conjoins**, so
the configuration below cannot arise on a live path
(`liveEndpointOverride_is_not_a_declassification_basis`, which needs no
restriction hypothesis at all).  The witness stays because it is the reason the
live gate is a conjunction rather than a replacement. -/
theorem unrestricted_endpointOverride_is_an_unaudited_downgrade :
    ∃ (ctx : GenericLabelingContext) (epPolicy : EndpointFlowPolicy)
      (endpointId : SeLe4n.ObjId) (src dst : SecurityDomain),
      endpointFlowCheck ctx epPolicy endpointId src dst = true ∧
      ctx.policy.canFlow src dst = false ∧
      ¬ endpointPolicyRestricted_perCore ctx.policy epPolicy := by
  refine ⟨{ policy := { canFlow := fun _ _ => false }
            objectDomainOf := fun _ => ⟨0⟩, threadDomainOf := fun _ => ⟨0⟩
            endpointDomainOf := fun _ => ⟨0⟩, serviceDomainOf := fun _ => ⟨0⟩ },
          { endpointPolicy := fun _ => some { canFlow := fun _ _ => true } },
          ⟨0⟩, ⟨2⟩, ⟨0⟩, rfl, rfl, ?_⟩
  intro hRestricted
  have := hRestricted bootCoreId ⟨0⟩ { canFlow := fun _ _ => true } rfl ⟨2⟩ ⟨0⟩ rfl
  exact Bool.noConfusion this

/-- WS-SM SM8.C.6 (Rule 3, **on the live gate**): the per-endpoint override the
kernel actually consults can never authorize a downgrade — and, unlike the
model-level form above, this needs **no restriction hypothesis**.

`endpointFlowGate` (`Policy.lean`, the predicate the four endpoint-keyed IPC
gates branch on since SM8.C) is `securityFlowsTo … && endpointOverrideAllows …`.
The conjunction is what makes V6-G's `endpointPolicyRestricted` structural: a
misconfigured override cannot widen anything, so an admitted flow is one the
global lattice already admitted, and a flow the lattice admits is by definition
not a downgrade.

Stated over the `liftLegacyContext` embedding, which is how the legacy 2×2
lattice the live gates carry sits inside the domain model the declassification
policy is written against. -/
theorem liveEndpointOverride_is_not_a_declassification_basis
    (ctx : LabelingContext) (declPolicy : DeclassificationPolicy)
    (endpointId : SeLe4n.ObjId) (srcLabel dstLabel : SecurityLabel)
    (hAdmitted : endpointFlowGate ctx endpointId srcLabel dstLabel = true) :
    DeclassificationPolicy.isDeclassificationAuthorized (liftLegacyContext ctx).policy declPolicy
      (embedLegacyLabel srcLabel) (embedLegacyLabel dstLabel) = false := by
  have hFlow := endpointFlowGate_implies_securityFlowsTo ctx endpointId srcLabel dstLabel hAdmitted
  -- PR #863 review: `liftLegacyContext` now carries the faithful
  -- `legacyLattice`, so this rides the *equality* `legacyLattice_canFlow_embed`
  -- rather than the one-directional `embedLegacyLabel_preserves_flow`.
  simp [DeclassificationPolicy.isDeclassificationAuthorized, liftLegacyContext,
    legacyLattice_canFlow_embed, hFlow]

/-- WS-SM SM8.C.6 (Rule 3, live, **the fail-closed direction**): whatever an
override admits, the live gate still demands the global check — so a deployment
cannot open a downgrade path by configuring one.  The contrapositive an operator
reads: a denied global flow stays denied at every endpoint. -/
theorem liveEndpointGate_denied_when_global_denied
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (srcLabel dstLabel : SecurityLabel)
    (hDenied : securityFlowsTo srcLabel dstLabel = false) :
    endpointFlowGate ctx endpointId srcLabel dstLabel = false :=
  endpointFlowGate_false_of_securityFlowsTo_false ctx endpointId srcLabel dstLabel hDenied

/-- WS-SM SM8.C.6 (Rule 4 — **the core dimension is audit, not authority**):
the state a declassification commits does not depend on which core ran it; the
two runs differ in exactly one field of exactly one audit event.

Stated because the opposite would be easy to assume once every other SMP surface
is per-core: there is no per-core declassification policy, so an operator cannot
authorize a downgrade on one core and deny it on another.  If a future cut adds
one, this theorem is where it breaks. -/
theorem declassifyStoreOnCore_state_core_independent
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c₁ c₂ : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st₁ st₂ : SystemState)
    (h₁ : declassifyStoreOnCore ctx declPolicy c₁ srcDomain dstDomain targetId obj st =
      .ok ((), st₁))
    (h₂ : declassifyStoreOnCore ctx declPolicy c₂ srcDomain dstDomain targetId obj st =
      .ok ((), st₂)) :
    { st₁ with declassificationAuditLog := [] } =
      { st₂ with declassificationAuditLog := [] } ∧
      ∃ e₁ e₂ : DeclassificationEvent,
        st₁.declassificationAuditLog = st.declassificationAuditLog ++ [e₁] ∧
        st₂.declassificationAuditLog = st.declassificationAuditLog ++ [e₂] ∧
        e₁.originatingCore = c₁ ∧ e₂.originatingCore = c₂ ∧
        { e₁ with originatingCore := c₂ } = e₂ := by
  obtain ⟨_, stGate₁, hGate₁, hSt₁⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c₁ srcDomain
    dstDomain targetId obj st st₁ h₁
  obtain ⟨_, stGate₂, hGate₂, hSt₂⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c₂ srcDomain
    dstDomain targetId obj st st₂ h₂
  obtain ⟨hLog₁, _⟩ := declassifyStoreOnCore_records_one ctx declPolicy c₁ srcDomain dstDomain
    targetId obj st st₁ h₁
  obtain ⟨hLog₂, _⟩ := declassifyStoreOnCore_records_one ctx declPolicy c₂ srcDomain dstDomain
    targetId obj st st₂ h₂
  rw [hGate₁] at hGate₂
  have hGateEq : stGate₁ = stGate₂ := congrArg Prod.snd (Except.ok.inj hGate₂)
  refine ⟨?_, _, _, hLog₁, hLog₂, rfl, rfl, rfl⟩
  -- the two runs differ only in the appended event's `originatingCore`, so with
  -- the trail erased the committed states are literally equal
  subst hSt₁; subst hSt₂; rw [hGateEq]

-- ============================================================================
-- §7  SM8.C.5 — `authorizationBasis_perCore` (V6-H extended)
-- ============================================================================
--
-- V6-H gave the record an `authorizationBasis` and said the kernel does not
-- interpret it.  Typing the field (`DeclassificationBasis`, `Policy.lean`) makes
-- interpretation possible; this section is what the kernel then concludes.

/-- WS-SM SM8.C.5: **the kernel's own check on a recorded event.**  For the
basis the kernel issues, re-run the gate the event claims authorized it; for an
out-of-band integrator authority, report that the kernel cannot vouch for it.

`false` on `integratorOverride` is a statement about the *kernel's* reach, not a
verdict that the event is illegitimate — the integrator's authority is real, it
is simply not something a kernel policy can evaluate.  What the audit consumer
gets is the ability to tell the two apart. -/
def declassificationBasisKernelVerified (basePolicy : DomainFlowPolicy)
    (declPolicy : DeclassificationPolicy) (e : DeclassificationEvent) : Bool :=
  match e.authorizationBasis with
  | .policyRule =>
      DeclassificationPolicy.isDeclassificationAuthorized basePolicy declPolicy
        e.srcDomain e.dstDomain
  | .integratorOverride _ => false

/-- WS-SM SM8.C.5: every event in the log carries a basis the kernel issued. -/
def auditLogKernelIssued (log : DeclassificationAuditLog) : Bool :=
  log.all (fun e => e.authorizationBasis.kernelVerifiable)

/-- WS-SM SM8.C.5: every event in the log passes the kernel's check. -/
def auditLogBasesVerified (basePolicy : DomainFlowPolicy) (declPolicy : DeclassificationPolicy)
    (log : DeclassificationAuditLog) : Bool :=
  log.all (fun e => declassificationBasisKernelVerified basePolicy declPolicy e)

/-- WS-SM SM8.C.5: **re-attributing an event to another core cannot change the
verdict.**

An `rfl`, and a load-bearing one: it says an attacker who could rewrite
`originatingCore` still could not turn a failing basis into a passing one, and
that an auditor on any core reaches the same conclusion about any event.  It is
also the tripwire for Rule 4 (§6): a future per-core declassification policy
makes this false, which is the right place for that change to announce
itself. -/
theorem declassificationBasisKernelVerified_core_independent (basePolicy : DomainFlowPolicy)
    (declPolicy : DeclassificationPolicy) (e : DeclassificationEvent) (c : CoreId) :
    declassificationBasisKernelVerified basePolicy declPolicy { e with originatingCore := c } =
      declassificationBasisKernelVerified basePolicy declPolicy e := rfl

/-- WS-SM SM8.C.5: the event a successful audited declassification records
passes the kernel's check — the gate that authorized it is the gate the basis
names, and it held. -/
theorem declassifyStoreOnCore_event_basis_verified
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    declassificationBasisKernelVerified ctx.policy declPolicy
      (declassifyStoreEvent c srcDomain dstDomain targetId st) = true := by
  obtain ⟨hNormal, hDecl⟩ := declassifyStoreOnCore_authorized ctx declPolicy c srcDomain
    dstDomain targetId obj st st' hStep
  simp [declassificationBasisKernelVerified, declassificationEventOnCore,
    DeclassificationPolicy.isDeclassificationAuthorized, hNormal, hDecl]

/-- WS-SM SM8.C.5 (**`authorizationBasis_perCore`, the headline**): basis
verification is an **invariant** of the audited declassification, on whichever
core it runs.

Read it as the audit-integrity property: if every event recorded so far passes
the kernel's own check, then after any declassification on any core, every event
still does — the kernel never appends a record it cannot justify, and never
disturbs one it already justified.  With `auditLogBasesVerified … [] = true` as
the boot witness, every log an audited run can produce is verified end to end.

The "per-core" of the name is the quantifier: `c` is arbitrary.  Nothing in the
statement or the proof is boot-core-pinned, and by
`declassificationBasisKernelVerified_core_independent` nothing could be. -/
theorem authorizationBasis_perCore
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (st st' : SystemState)
    (hVerified : auditLogBasesVerified ctx.policy declPolicy st.declassificationAuditLog = true)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    auditLogBasesVerified ctx.policy declPolicy st'.declassificationAuditLog = true := by
  obtain ⟨hLog, _⟩ := declassifyStoreOnCore_records_one ctx declPolicy c srcDomain dstDomain
    targetId obj st st' hStep
  have hNew := declassifyStoreOnCore_event_basis_verified ctx declPolicy c srcDomain dstDomain
    targetId obj st st' hStep
  rw [hLog]
  simp only [auditLogBasesVerified, List.all_append, Bool.and_eq_true,
    List.all_cons, List.all_nil]
  exact ⟨hVerified, by simp [hNew]⟩

/-- WS-SM SM8.C.5: the boot witness — an empty audit trail is verified. -/
theorem auditLogBasesVerified_nil (basePolicy : DomainFlowPolicy)
    (declPolicy : DeclassificationPolicy) :
    auditLogBasesVerified basePolicy declPolicy [] = true := rfl

/-- WS-SM SM8.C.5: the same invariant on the weaker, policy-free property —
every event the kernel appends carries a kernel-issued basis. -/
theorem declassifyStoreOnCore_preserves_kernelIssued
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (st st' : SystemState)
    (hIssued : auditLogKernelIssued st.declassificationAuditLog = true)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    auditLogKernelIssued st'.declassificationAuditLog = true := by
  obtain ⟨hLog, _⟩ := declassifyStoreOnCore_records_one ctx declPolicy c srcDomain dstDomain
    targetId obj st st' hStep
  rw [hLog]
  simp only [auditLogKernelIssued, List.all_append, Bool.and_eq_true,
    List.all_cons, List.all_nil]
  exact ⟨hIssued, rfl, trivial⟩

/-- WS-SM SM8.C.5 (**the detection result**): a log containing an integrator
override is not kernel-issued.

Contrapositive of the invariant above, and the reason `kernelVerifiable` is a
field of the type rather than a comment: an audit consumer that finds
`auditLogKernelIssued = false` knows some entry did not come from the kernel's
declassification path, and can go and find it.  Before SM8.C the basis was a
free `String`, so no such conclusion was available at all. -/
theorem auditLog_integratorOverride_not_kernelIssued (log : DeclassificationAuditLog)
    {e : DeclassificationEvent} (hMem : e ∈ log) (authority : String)
    (hBasis : e.authorizationBasis = .integratorOverride authority) :
    auditLogKernelIssued log = false := by
  cases hCheck : auditLogKernelIssued log with
  | false => rfl
  | true =>
    exfalso
    simp only [auditLogKernelIssued, List.all_eq_true] at hCheck
    have hE := hCheck e hMem
    rw [hBasis] at hE
    simp [DeclassificationBasis.kernelVerifiable] at hE

-- ============================================================================
-- §8  The declassification's own non-interference, per core
-- ============================================================================
--
-- Two things are owed here.  A declassification is *supposed* to be visible —
-- to the domain it was authorized for, and to no one else; that is the
-- single-core `declassifyStore_NI`, and SMP needs it on every core.  And the
-- audit itself must not become a channel: a record the kernel keeps is state,
-- and state an observer can see is a flow.

/-- WS-SM SM8.C: a declassification writes **no core's** scheduler slots or
register bank — it is an object-store write.  So the SM8.B cross-core machinery
applies with an empty write set: the operation is invisible on *every* core
(the observer's included) unless it moves the shared, label-filtered half. -/
theorem declassifyStore_confinedToCores_nil
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st st' : SystemState)
    (hStep : declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  have hSched := declassifyStore_scheduler_eq ctx declPolicy srcDomain dstDomain targetId obj
    st st' hStep
  have hMach := declassifyStore_machine_eq ctx declPolicy srcDomain dstDomain targetId obj
    st st' hStep
  exact ⟨fun _ _ => by rw [hSched], fun _ _ => by rw [hSched], fun _ _ => by rw [hSched],
    fun _ _ => by rw [hSched], fun _ _ => by rw [hSched], fun _ _ => by rw [hMach]⟩

/-- WS-SM SM8.C.8: the per-core projection does not read the mounted trail —
the `projectStateOnCore` companion of
`declassificationAuditLog_write_preserves_projection`, needed by the NI proofs
below now that the audited step writes a `SystemState` field. -/
theorem declassificationAuditLog_write_preserves_projectionOnCore
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (log : DeclassificationAuditLog) (c : CoreId) :
    projectStateOnCore ctx observer { st with declassificationAuditLog := log } c =
      projectStateOnCore ctx observer st c := rfl

/-- WS-SM SM8.C: a declassification to a target the observer cannot see is
invisible to that observer on **every** core — the per-core lift of the shared
half of `declassifyStore_NI`.

The confinement half is free (nothing per-core moves); the content is that the
object write lands at a non-observable id, so the shared fragment does not move
either. -/
theorem declassifyStoreOnCore_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (gctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (st st' : SystemState) (c' : CoreId)
    (hTargetHigh : objectObservable ctx observer targetId = false)
    (hObjInv : st.objects.invExt)
    (hStep : declassifyStoreOnCore gctx declPolicy c srcDomain dstDomain targetId obj st =
      .ok ((), st')) :
    projectStateOnCore ctx observer st' c' = projectStateOnCore ctx observer st c' := by
  obtain ⟨_, stGate, hGate, hSt'⟩ := declassifyStoreOnCore_ok_inv gctx declPolicy c srcDomain
    dstDomain targetId obj st st' hStep
  obtain ⟨hDenied, hAuth⟩ := enforcementSoundness_declassifyStore gctx declPolicy srcDomain
    dstDomain targetId obj st stGate hGate
  rw [declassifyStore_eq_storeObject_when_authorized gctx declPolicy srcDomain dstDomain
    targetId obj st hDenied hAuth] at hGate
  -- the trail write is invisible (SM8.C.8's projection decision), so the whole
  -- step's projection is the store's
  rw [hSt', declassificationAuditLog_write_preserves_projectionOnCore ctx observer stGate _ c']
  exact storeObject_preserves_projectionOnCore ctx observer st stGate targetId obj c'
    hTargetHigh hObjInv hGate

/-- WS-SM SM8.C (the ∀-core non-interference): two audited declassifications at
a non-observable target, from low-equivalent states, land in low-equivalent
states — on every core.

The SMP-faithful form of `declassifyStore_NI`, which covers the boot core only.
Note what it does *not* say: a declassification to a target the observer *can*
see is visible, and is meant to be — that is the whole point of the operation,
and the audit trail is what makes the downgrade accountable. -/
theorem declassifyStoreOnCore_perCore_NI (ctx : LabelingContext) (observer : IfObserver)
    (gctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c₁ c₂ : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj₁ obj₂ : KernelObject)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent_smp ctx observer s₁ s₂)
    (hTargetHigh : objectObservable ctx observer targetId = false)
    (hObjInv₁ : s₁.objects.invExt) (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : declassifyStoreOnCore gctx declPolicy c₁ srcDomain dstDomain targetId obj₁ s₁ =
      .ok ((), s₁'))
    (hStep₂ : declassifyStoreOnCore gctx declPolicy c₂ srcDomain dstDomain targetId obj₂ s₂ =
      .ok ((), s₂')) :
    lowEquivalent_smp ctx observer s₁' s₂' := by
  intro c
  show projectStateOnCore ctx observer s₁' c = projectStateOnCore ctx observer s₂' c
  rw [declassifyStoreOnCore_preserves_projectionOnCore ctx observer gctx declPolicy c₁ srcDomain
        dstDomain targetId obj₁ s₁ s₁' c hTargetHigh hObjInv₁ hStep₁,
      declassifyStoreOnCore_preserves_projectionOnCore ctx observer gctx declPolicy c₂ srcDomain
        dstDomain targetId obj₂ s₂ s₂' c hTargetHigh hObjInv₂ hStep₂]
  exact hLow c

/-- WS-SM SM8.C.8 (**auditing opens no channel**): the state a declassification
commits — *modulo the trail itself* — does not depend on the trail it started
from, and no observer can see the trail at all.

Two halves, and SM8.C.8 changed which one carries the weight.  Before the mount
the trail was threaded through the operation, so it was outside every observer's
view by construction and this theorem was a plain `stA = stB`; the docstring said
that a cut mounting the trail in `SystemState` is where it would stop holding.
That cut is SM8.C.8, so the statement is now the honest one: erase the trail from
both post-states and they are equal, which says the *rest* of the state carries
no residue of the audit history.

The other half is no longer free and is discharged explicitly:
`declassificationAuditLog_write_preserves_projection` (and its per-core
companion) is the decision that the mounted trail is outside `ObservableState`,
so an observer still cannot read it — see the field's own docstring for why
projecting it would open a channel out of exactly the boundary it polices. -/
theorem declassifyStoreOnCore_state_trail_independent
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (logA logB : DeclassificationAuditLog) (st stA stB : SystemState)
    (hStepA : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj
      { st with declassificationAuditLog := logA } = .ok ((), stA))
    (hStepB : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj
      { st with declassificationAuditLog := logB } = .ok ((), stB)) :
    { stA with declassificationAuditLog := [] } =
      { stB with declassificationAuditLog := [] } := by
  obtain ⟨_, stGateA, hGateA, hStA⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain
    dstDomain targetId obj _ stA hStepA
  obtain ⟨_, stGateB, hGateB, hStB⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain
    dstDomain targetId obj _ stB hStepB
  -- the gate is `storeObject` under two checks that read no state, so the two
  -- runs' gate outputs differ only in the trail they carried in
  obtain ⟨hDenied, hAuth⟩ := enforcementSoundness_declassifyStore ctx declPolicy srcDomain
    dstDomain targetId obj _ stGateA hGateA
  rw [declassifyStore_eq_storeObject_when_authorized ctx declPolicy srcDomain dstDomain
    targetId obj _ hDenied hAuth] at hGateA
  rw [declassifyStore_eq_storeObject_when_authorized ctx declPolicy srcDomain dstDomain
    targetId obj _ hDenied hAuth] at hGateB
  unfold storeObject at hGateA hGateB
  subst hStA; subst hStB
  cases hGateA; cases hGateB
  rfl

-- ============================================================================
-- §10  SM8.C.9 — the live declassification, per-core
-- ============================================================================
--
-- The transition itself and its invariant obligations live in the production
-- module `InformationFlow/Declassification.lean`, which the live `.declassify`
-- arm imports.  What belongs here is the part that needs the SM8.A/SM8.B
-- per-core observer: non-interference on every core, and the per-core audit
-- properties the model primitive has in §2–§7.

/-- WS-SM SM8.C.9: the live declassification is invisible to every per-core
observer.

Immediate from the frame — the only field it writes is the audit trail, which
is outside `ObservableState` by the SM8.C.8 projection decision — but stated
because "writes one field" and "that field is unobservable" are two facts, and
only the pair gives non-interference. -/
theorem authorizeDeclassificationOnCore_preserves_projectionOnCore
    (ctx : LabelingContext) (observer : IfObserver) (gctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st st' : SystemState) (c' : CoreId)
    (hStep : authorizeDeclassificationOnCore gctx declPolicy c srcDomain dstDomain targetId st =
      .ok ((), st')) :
    projectStateOnCore ctx observer st' c' = projectStateOnCore ctx observer st c' := by
  obtain ⟨hSt', _, _⟩ := authorizeDeclassificationOnCore_frame gctx declPolicy c srcDomain
    dstDomain targetId st st' hStep
  rw [hSt']
  exact declassificationAuditLog_write_preserves_projectionOnCore ctx observer st _ c'

/-- WS-SM SM8.C.9 (the ∀-core non-interference): two live declassifications from
low-equivalent states land in low-equivalent states, on every core.

**Unconditional** — unlike `declassifyStoreOnCore_perCore_NI`, which needs the
target to be non-observable because the model primitive *stores* into it.  The
live syscall stores nothing, so there is no observable write to exclude.  That
difference is the security content of the SM8.C.9 design, not an accident of
what was easy to prove. -/
theorem authorizeDeclassificationOnCore_perCore_NI
    (ctx : LabelingContext) (observer : IfObserver) (gctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (c₁ c₂ : CoreId)
    (src₁ dst₁ src₂ dst₂ : SecurityDomain) (target₁ target₂ : SeLe4n.ObjId)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent_smp ctx observer s₁ s₂)
    (hStep₁ : authorizeDeclassificationOnCore gctx declPolicy c₁ src₁ dst₁ target₁ s₁ =
      .ok ((), s₁'))
    (hStep₂ : authorizeDeclassificationOnCore gctx declPolicy c₂ src₂ dst₂ target₂ s₂ =
      .ok ((), s₂')) :
    lowEquivalent_smp ctx observer s₁' s₂' := by
  intro c
  show projectStateOnCore ctx observer s₁' c = projectStateOnCore ctx observer s₂' c
  rw [authorizeDeclassificationOnCore_preserves_projectionOnCore ctx observer gctx declPolicy
        c₁ src₁ dst₁ target₁ s₁ s₁' c hStep₁,
      authorizeDeclassificationOnCore_preserves_projectionOnCore ctx observer gctx declPolicy
        c₂ src₂ dst₂ target₂ s₂ s₂' c hStep₂]
  exact hLow c

/-- WS-SM SM8.C.9: the live declassification files its event under the core it
ran on — the §4 per-core view property, at the live entry point. -/
theorem declassifyObjectFromCore_recorded_in_own_view
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    declassifyStoreEvent c (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId) targetId st ∈
      auditLogOnCore st'.declassificationAuditLog c := by
  have hSt' := declassifyObjectFromCore_frame ctx declPolicy c targetId st st' tid hCur hStep
  subst hSt'
  refine (mem_auditLogOnCore_iff _ c _).mpr ⟨?_, rfl⟩
  show _ ∈ declassifyStoreTrail c (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId)
    targetId st
  exact recordDeclassification_contains_new _ _

/-- WS-SM SM8.C.9 / SM9.A.1a: the live declassification preserves the trail's
timestamp discipline **at the mounted epoch**, so the total order holds of every
trail a running system can produce — starting, by
`default_declassificationTrailWellFormed`, from the empty one at boot, and
surviving the drain SM9.A.3 adds.

The staged surface for the production theorem
`declassifyObjectFromCore_preserves_trailWellFormed`: the per-core theory's
consumers (`declassifyRun_preserves_wellFormed` below) fold it, so it is named
here as well as proved there. -/
theorem declassifyObjectFromCore_preserves_wellFormed
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hWF : declassificationTrailWellFormed st = true)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    declassificationTrailWellFormed st' = true :=
  declassifyObjectFromCore_preserves_trailWellFormed ctx declPolicy c targetId st st' hWF hStep

/-- WS-SM SM8.C.5: **`authorizationBasis_perCore` at the live entry point.**  If
every event recorded so far passes the kernel's own check, then after any live
declassification on any core, every event still does. -/
theorem declassifyObjectFromCore_authorizationBasis_perCore
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ty : SeLe4n.Model.KernelObjectType)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hPresent : st.getObjectType? targetId = some ty)
    (hVerified : auditLogBasesVerified ctx.policy declPolicy st.declassificationAuditLog = true)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    auditLogBasesVerified ctx.policy declPolicy st'.declassificationAuditLog = true := by
  obtain ⟨hNormal, hDecl⟩ := declassifyObjectFromCore_authorized ctx declPolicy c targetId st st'
    tid ty hCur hPresent hStep
  have hSt' := declassifyObjectFromCore_frame ctx declPolicy c targetId st st' tid hCur hStep
  subst hSt'
  simp only [auditLogBasesVerified, declassifyStoreTrail, recordDeclassification,
    List.all_append, Bool.and_eq_true, List.all_cons, List.all_nil]
  refine ⟨hVerified, ?_, trivial⟩
  simp [declassificationBasisKernelVerified, declassificationEventOnCore,
    DeclassificationPolicy.isDeclassificationAuthorized, hNormal, hDecl]

-- ============================================================================
-- §11  Scope, stated as witnesses
-- ============================================================================
--
-- Four properties this phase does *not* have.  Each is a theorem rather than a
-- caveat in prose, because a caveat is exactly what a later reader skips.

/-- WS-SM SM8.C (**§1's scope**): `recordDeclassification` — the V6-H primitive —
admits a log the well-formedness predicate rejects.

Which is why §1 is a *checkable predicate* rather than a claim that the ordering
holds by construction.  Nothing in the kernel produces such a log (every kernel
producer computes the timestamp from the position), but the primitive is
exported, so "the trail is totally ordered" is a property to be *established*
for a given log, not read off the type. -/
theorem recordDeclassification_admits_ill_formed :
    ∃ (log : DeclassificationAuditLog) (e : DeclassificationEvent),
      declassificationAuditLogWellFormed log = true ∧
        declassificationAuditLogWellFormed (recordDeclassification log e) = false := by
  refine ⟨[], { srcDomain := ⟨1⟩, dstDomain := ⟨0⟩, targetObject := ⟨0⟩,
                authorizationBasis := .policyRule, timestamp := 7,
                originatingCore := bootCoreId }, rfl, rfl⟩

/-- WS-SM SM8.C.2 (**the laundering detector's scope**): `declassificationChainLinked`
is **syntactic**, and fires on events that are causally unrelated.

Two downgrades `a → b` and `b → d` are "linked" here when the middle domains
match and the timestamps increase.  Nothing establishes that the second
downgrade released information the first produced — the model has no
data-dependency relation between events, so it cannot.

The over-approximation is in the safe direction for a *detector*: `chainLaunders`
reports a composition the policy does not authorize wherever the syntactic shape
is present, so it cannot miss a real laundering chain, and an operator
investigating a report has to establish causality themselves.  It would be the
unsafe direction for an *enforcement* gate, which is why nothing enforces on it.

Closing this needs a provenance relation on the object store (which object's
content flowed into which), scoped to SM8.E. -/
theorem declassificationChainLinked_is_syntactic :
    ∃ e₁ e₂ : DeclassificationEvent,
      declassificationChainLinked [e₁, e₂] = true ∧
        e₁.targetObject ≠ e₂.targetObject ∧
        e₁.originatingCore = e₂.originatingCore := by
  refine ⟨{ srcDomain := ⟨2⟩, dstDomain := ⟨1⟩, targetObject := ⟨100⟩,
            authorizationBasis := .policyRule, timestamp := 0,
            originatingCore := bootCoreId },
          { srcDomain := ⟨1⟩, dstDomain := ⟨0⟩, targetObject := ⟨200⟩,
            authorizationBasis := .policyRule, timestamp := 1,
            originatingCore := bootCoreId }, by decide, by decide, rfl⟩

/-- WS-SM SM8.C.5 (**`authorizationBasis_perCore`'s scope**): the *verdict* is
core-uniform, so the theorem's `∀ c` is a quantifier over a dimension the
verdict does not read (`declassificationBasisKernelVerified_core_independent`).

What the core genuinely selects is the recorded **subject**: the same live
declassification on two cores running threads in different domains records
different source domains, so the *events* differ even though every one of them
passes the same check.  Stated because "per-core" in the name would otherwise
promise a per-core policy that deliberately does not exist (§6 Rule 4). -/
theorem declassificationSubjectDomain_is_core_selected :
    ∃ (ctx : GenericLabelingContext) (st : SystemState) (c₁ c₂ : CoreId),
      declassificationSubjectDomainOnCore ctx st c₁ ≠
        declassificationSubjectDomainOnCore ctx st c₂ := by
  refine ⟨{ policy := { canFlow := fun _ _ => false }
            objectDomainOf := fun _ => ⟨0⟩
            threadDomainOf := fun tid => ⟨tid.toNat⟩
            endpointDomainOf := fun _ => ⟨0⟩, serviceDomainOf := fun _ => ⟨0⟩ },
          { (default : SystemState) with scheduler :=
              (((default : SystemState).scheduler.setCurrentOnCore bootCoreId
                 (some ⟨1⟩)).setCurrentOnCore ⟨1, by decide⟩ (some ⟨2⟩)) },
          bootCoreId, ⟨1, by decide⟩, ?_⟩
  -- core 0 runs thread 1 (domain 1), core 1 runs thread 2 (domain 2)
  simp [declassificationSubjectDomainOnCore, bootCoreId,
    SeLe4n.ThreadId.toNat, SecurityDomain.mk.injEq]

/-- WS-SM SM8.C (**the outcome gap**): a *refused* declassification leaves no
trace, and **cannot** leave one without changing the transition's shape.

The V6-H record has no outcome field, so the trail records authorized downgrades
and nothing else.  A monitoring system therefore cannot distinguish "no attempts"
from "many attempts, all denied" — a detection gap, not an enforcement one, since
every refusal is already fail-closed
(`declassifyStoreOnCore_denied_no_audit_entry`).

**The closure recipe this docstring used to give was wrong**, and the second
conjunct is where that shows.  It read
`st.declassificationAuditLog = st.declassificationAuditLog` — a `rfl` that holds
of any two syntactically equal terms and therefore says nothing at all — beside
a sentence promising the gap could be closed with "an outcome field on the
record and a producer on the error arms".  It cannot: `Kernel α` is
`SystemState → Except KernelError (α × SystemState)`, so the error arm carries
**no post-state**, and there is no state for a producer on it to write into.
The conjunct now says that: the refusal has no success arm, over an arbitrary
post-state, which is the fact a would-be producer runs into.

Closing the gap therefore needs one of two things, both larger than a field:
a total transformer (`SystemState → SystemState × Except KernelError α`) for
this transition, with the dispatch entry committing its state on the error path
as well; or a separate structure the entry writes by re-deriving the refusal
from the decoded syscall and the returned discriminant, the way
`computeCrossCoreSgis` re-derives pokes from the diff.  Either way it is the
kernel's error discipline that moves, not the audit record — and neither may
write refusals into *this* trail, whose capacity is fail-closed: an unprivileged
caller able to append on refusal could exhaust the 256 entries and deny every
subsequent authorized downgrade.  Re-registered against SM9 with that analysis
rather than the recipe that does not typecheck. -/
theorem declassification_refusal_is_unrecorded
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (targetObj : KernelObject) (st : SystemState)
    (hDenied : declPolicy.canDeclassify srcDomain dstDomain = false)
    (hNotFlow : ctx.policy.canFlow srcDomain dstDomain = false) :
    declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId targetObj st =
      .error .declassificationDenied ∧
    ¬ ∃ st', declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId targetObj st =
      .ok ((), st') := by
  have hDec : declassificationDecision ctx declPolicy srcDomain dstDomain =
      .error .declassificationDenied := by
    unfold declassificationDecision; simp [hNotFlow, hDenied]
  have hErr : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId targetObj st =
      .error .declassificationDenied := by
    unfold declassifyStoreOnCore
    rw [hDec]
  refine ⟨hErr, ?_⟩
  rintro ⟨st', hOk⟩
  rw [hErr] at hOk
  simp at hOk

-- ============================================================================
-- §12  SM8.C — run-level completeness
-- ============================================================================
--
-- §2 and §13 state what *one* declassification records.  A deployment's audit
-- question is about a run: after n downgrades, does the trail hold n attributed
-- entries, in order, with nothing lost?  With the trail mounted (SM8.C.8) a run
-- is a fold over the state, so the question has an answer that is not just the
-- single-step theorem repeated by hand.

/-- WS-SM SM8.C: one request in a declassification run — the two operands the
live syscall takes. -/
structure DeclassificationRequest where
  /-- The core the declassification is performed on. -/
  core : CoreId
  /-- The object being declassified into. -/
  targetId : SeLe4n.ObjId
  deriving Repr, DecidableEq

/-- WS-SM SM8.C: a **run** — the live declassification, folded over a list of
requests, stopping at the first refusal.

Deliberately the *live* entry point rather than the model primitive: a run is
what a deployment does, and the live path is the only one a deployment has. -/
def declassifyRun (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy) :
    List DeclassificationRequest → Kernel Unit
  | [] => fun st => .ok ((), st)
  | r :: rest => fun st =>
      match declassifyObjectFromCore ctx declPolicy r.core r.targetId st with
      | .ok ((), st') => declassifyRun ctx declPolicy rest st'
      | .error e => .error e

@[simp] theorem declassifyRun_nil (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (st : SystemState) :
    declassifyRun ctx declPolicy [] st = .ok ((), st) := rfl

/-- WS-SM SM8.C: **a run of `n` authorized downgrades records exactly `n`
entries.**

The completeness property: not "at least one per request" and not "the caller
may drop some" — the trail grows by exactly the number of requests that ran. -/
theorem declassifyRun_records_each (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) :
    ∀ (reqs : List DeclassificationRequest) (st st' : SystemState),
      declassifyRun ctx declPolicy reqs st = .ok ((), st') →
      st'.declassificationAuditLog.length = st.declassificationAuditLog.length + reqs.length := by
  intro reqs
  induction reqs with
  | nil => intro st st' h; cases h; simp
  | cons r rest ih =>
    intro st st' h
    unfold declassifyRun at h
    obtain ⟨res, hRes⟩ :
        ∃ x, declassifyObjectFromCore ctx declPolicy r.core r.targetId st = x := ⟨_, rfl⟩
    rw [hRes] at h
    cases res with
    | error e => simp at h
    | ok pair =>
      obtain ⟨u, stMid⟩ := pair
      cases u
      obtain ⟨⟨tid, hCur⟩, -⟩ := declassifyObjectFromCore_ok_resolved ctx declPolicy r.core
        r.targetId st stMid hRes
      have hStep := declassifyObjectFromCore_never_unaudited ctx declPolicy r.core r.targetId
        st stMid tid hCur hRes
      have hMid : stMid.declassificationAuditLog.length =
          st.declassificationAuditLog.length + 1 := by
        rw [declassifyObjectFromCore_frame ctx declPolicy r.core r.targetId st stMid tid hCur
          hRes]
        exact recordDeclassification_length _ _
      have := ih stMid st' h
      simp only [List.length_cons]
      omega

/-- WS-SM SM8.C: **a run loses nothing** — every event the trail held before the
run is still in it afterwards. -/
theorem declassifyRun_preserves_existing (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) :
    ∀ (reqs : List DeclassificationRequest) (st st' : SystemState),
      declassifyRun ctx declPolicy reqs st = .ok ((), st') →
      ∀ e ∈ st.declassificationAuditLog, e ∈ st'.declassificationAuditLog := by
  intro reqs
  induction reqs with
  | nil => intro st st' h; cases h; exact fun _ hMem => hMem
  | cons r rest ih =>
    intro st st' h
    unfold declassifyRun at h
    obtain ⟨res, hRes⟩ :
        ∃ x, declassifyObjectFromCore ctx declPolicy r.core r.targetId st = x := ⟨_, rfl⟩
    rw [hRes] at h
    cases res with
    | error e => simp at h
    | ok pair =>
      obtain ⟨u, stMid⟩ := pair
      cases u
      obtain ⟨tid, hCur, hSt⟩ := declassifyObjectFromCore_frame_of_ok ctx declPolicy r.core
        r.targetId st stMid hRes
      intro e hMem
      refine ih stMid st' h e ?_
      rw [hSt]
      exact List.mem_append_left _ hMem

/-- WS-SM SM8.C / SM9.A.1a: **a run's trail stays well-formed at its epoch**, so
the total order — and with it
`declassificationAuditLog_timestamp_identifies_event` — holds of every trail a
running system can reach from boot, drains included. -/
theorem declassifyRun_preserves_wellFormed (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) :
    ∀ (reqs : List DeclassificationRequest) (st st' : SystemState),
      declassificationTrailWellFormed st = true →
      declassifyRun ctx declPolicy reqs st = .ok ((), st') →
      declassificationTrailWellFormed st' = true := by
  intro reqs
  induction reqs with
  | nil => intro st st' hWF h; cases h; exact hWF
  | cons r rest ih =>
    intro st st' hWF h
    unfold declassifyRun at h
    obtain ⟨res, hRes⟩ :
        ∃ x, declassifyObjectFromCore ctx declPolicy r.core r.targetId st = x := ⟨_, rfl⟩
    rw [hRes] at h
    cases res with
    | error e => simp at h
    | ok pair =>
      obtain ⟨u, stMid⟩ := pair
      cases u
      exact ih stMid st' (declassifyObjectFromCore_preserves_wellFormed ctx declPolicy r.core
        r.targetId st stMid hWF hRes) h

/-- WS-SM SM8.C.8: **a run stays within capacity.**  Unconditional: every step
is fail-closed at the bound, so a run that got this far never crossed it. -/
theorem declassifyRun_preserves_auditLogBounded (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) :
    ∀ (reqs : List DeclassificationRequest) (st st' : SystemState),
      auditLogBounded st.declassificationAuditLog →
      declassifyRun ctx declPolicy reqs st = .ok ((), st') →
      auditLogBounded st'.declassificationAuditLog := by
  intro reqs
  induction reqs with
  | nil => intro st st' hB h; cases h; exact hB
  | cons r rest ih =>
    intro st st' hB h
    unfold declassifyRun at h
    obtain ⟨res, hRes⟩ :
        ∃ x, declassifyObjectFromCore ctx declPolicy r.core r.targetId st = x := ⟨_, rfl⟩
    rw [hRes] at h
    cases res with
    | error e => simp at h
    | ok pair =>
      obtain ⟨u, stMid⟩ := pair
      cases u
      obtain ⟨⟨tid, hCur⟩, ⟨ty, hTy⟩⟩ := declassifyObjectFromCore_ok_resolved ctx declPolicy
        r.core r.targetId st stMid hRes
      rw [declassifyObjectFromCore_eq_onCore ctx declPolicy r.core r.targetId st tid ty hCur
        hTy] at hRes
      exact ih stMid st' (authorizeDeclassificationOnCore_preserves_auditLogBounded ctx
        declPolicy r.core (ctx.threadDomainOf tid) (ctx.objectDomainOf r.targetId) r.targetId
        st stMid hRes) h

/-- WS-SM SM8.C: **a run writes only the trail** — the object store, the
scheduler and the machine are exactly as they were, however long the run.

The run-level form of the frame, and the reason a deployment can audit
declassification without reasoning about what else the syscall might have
touched: nothing else. -/
theorem declassifyRun_frame (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) :
    ∀ (reqs : List DeclassificationRequest) (st st' : SystemState),
      declassifyRun ctx declPolicy reqs st = .ok ((), st') →
      st'.objects = st.objects ∧ st'.scheduler = st.scheduler ∧ st'.machine = st.machine := by
  intro reqs
  induction reqs with
  | nil => intro st st' h; cases h; exact ⟨rfl, rfl, rfl⟩
  | cons r rest ih =>
    intro st st' h
    unfold declassifyRun at h
    obtain ⟨res, hRes⟩ :
        ∃ x, declassifyObjectFromCore ctx declPolicy r.core r.targetId st = x := ⟨_, rfl⟩
    rw [hRes] at h
    cases res with
    | error e => simp at h
    | ok pair =>
      obtain ⟨u, stMid⟩ := pair
      cases u
      obtain ⟨tid, hCur, hSt⟩ := declassifyObjectFromCore_frame_of_ok ctx declPolicy r.core
        r.targetId st stMid hRes
      obtain ⟨ho, hs, hm⟩ := ih stMid st' h
      exact ⟨by rw [ho, hSt], by rw [hs, hSt], by rw [hm, hSt]⟩

/-- WS-SM SM8.C: **a run is invisible on every core.**  The ∀-core
non-interference at run scale, from the per-step form. -/
theorem declassifyRun_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (gctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) :
    ∀ (reqs : List DeclassificationRequest) (st st' : SystemState) (c : CoreId),
      declassifyRun gctx declPolicy reqs st = .ok ((), st') →
      projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  intro reqs
  induction reqs with
  | nil => intro st st' c h; cases h; rfl
  | cons r rest ih =>
    intro st st' c h
    unfold declassifyRun at h
    obtain ⟨res, hRes⟩ :
        ∃ x, declassifyObjectFromCore gctx declPolicy r.core r.targetId st = x := ⟨_, rfl⟩
    rw [hRes] at h
    cases res with
    | error e => simp at h
    | ok pair =>
      obtain ⟨u, stMid⟩ := pair
      cases u
      obtain ⟨tid, hCur, hSt⟩ := declassifyObjectFromCore_frame_of_ok gctx declPolicy r.core
        r.targetId st stMid hRes
      rw [ih stMid st' c h, hSt]
      exact declassificationAuditLog_write_preserves_projectionOnCore ctx observer st _ c

-- ============================================================================
-- §13  SM8.C.6 — the rules as data, each carrying its own proof
-- ============================================================================
--
-- The same device `CovertChannelPerCore` uses for the accepted-channel
-- inventory, and for the same reason: a rule that lives only in prose ages out
-- with the code around it.  Here each rule names a theorem *and* supplies it, so
-- adding a rule without deciding what proves it is a missing-arm error and
-- attributing the wrong theorem to a rule is a type error.

/-- WS-SM SM8.C.6: the cross-core declassification rules. -/
inductive DeclassificationRuleId where
  /-- An authorized composite really is an authorized downgrade. -/
  | compositionSoundness
  /-- Authorizing each hop does not authorize the composition (laundering). -/
  | hopAuthorizationDoesNotCompose
  /-- A per-endpoint policy override can never authorize a downgrade. -/
  | endpointOverrideIsNotABasis
  /-- The core an event names is audit information, never authority. -/
  | coreDimensionIsAuditOnly
  /-- The per-core views partition the log; no event is lost or duplicated. -/
  | perCorePartition
  /-- A cross-core chain lives in no single core's view. -/
  | crossCoreChainNeedsGlobalLog
  /-- The recorded source domain is the running subject's, not the caller's. -/
  | attributionFromRunningSubject
  /-- The audit trail is not observable state. -/
  | auditIsNotObservable
  /-- WS-SM SM8.C (§11): the trail's total order is a **checkable predicate**,
  not a type invariant — the V6-H primitive admits an ill-formed log. -/
  | timestampOrderIsCheckable
  /-- WS-SM SM8.C.2 (§11): chain linkage is **syntactic** — matching domains and
  increasing timestamps, with no data-dependency relation behind them. -/
  | chainLinkageIsSyntactic
  /-- WS-SM SM8.C (§11): a **refused** declassification leaves no trace, so the
  trail cannot distinguish "no attempts" from "all denied" — and the refusal has
  no success arm, so no producer *on* the error arm could leave one. -/
  | refusalIsUnrecorded
  /-- WS-SM SM8.C.9: the live declassification writes **only** the audit trail —
  it authorizes and records, and moves no data. -/
  | liveDeclassificationWritesOnlyTheTrail
  deriving Repr, DecidableEq

/-- WS-SM SM8.C.6: the enumeration.  `mem_all` and `all_nodup` make it complete
and repeat-free, so the count theorems mean what they say. -/
def DeclassificationRuleId.all : List DeclassificationRuleId :=
  [ .compositionSoundness, .hopAuthorizationDoesNotCompose, .endpointOverrideIsNotABasis
  , .coreDimensionIsAuditOnly, .perCorePartition, .crossCoreChainNeedsGlobalLog
  , .attributionFromRunningSubject, .auditIsNotObservable
  , .timestampOrderIsCheckable, .chainLinkageIsSyntactic, .refusalIsUnrecorded
  , .liveDeclassificationWritesOnlyTheTrail ]

theorem DeclassificationRuleId.mem_all (id : DeclassificationRuleId) :
    id ∈ DeclassificationRuleId.all := by cases id <;> decide

theorem DeclassificationRuleId.all_nodup : DeclassificationRuleId.all.Nodup := by decide

/-- WS-SM SM8.C.6: **what each rule claims**, as a proposition rather than a
sentence — so the evidence below can be checked against it. -/
def DeclassificationRuleId.evidenceProp : DeclassificationRuleId → Prop
  | .compositionSoundness =>
      ∀ (basePolicy : DomainFlowPolicy) (declPolicy : DeclassificationPolicy)
        (chain : List DeclassificationEvent) (src dst : SecurityDomain),
        chainSourceDomain chain = some src → chainTargetDomain chain = some dst →
        chainCompositionAuthorized basePolicy declPolicy chain = true →
        basePolicy.canFlow src dst = false ∧ declPolicy.canDeclassify src dst = true
  | .hopAuthorizationDoesNotCompose =>
      ∃ (basePolicy : DomainFlowPolicy) (declPolicy : DeclassificationPolicy)
        (a b d : SecurityDomain),
        basePolicy.wellFormed ∧
        DeclassificationPolicy.isDeclassificationAuthorized basePolicy declPolicy a b = true ∧
        DeclassificationPolicy.isDeclassificationAuthorized basePolicy declPolicy b d = true ∧
        DeclassificationPolicy.isDeclassificationAuthorized basePolicy declPolicy a d = false
  | .endpointOverrideIsNotABasis =>
      ∀ (ctx : GenericLabelingContext) (epPolicy : EndpointFlowPolicy)
        (declPolicy : DeclassificationPolicy) (endpointId : SeLe4n.ObjId)
        (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId),
        st.scheduler.currentOnCore c = some tid →
        endpointPolicyRestricted_perCore ctx.policy epPolicy →
        endpointFlowCheckAtCore ctx epPolicy endpointId st c = true →
        DeclassificationPolicy.isDeclassificationAuthorized ctx.policy declPolicy
          (ctx.threadDomainOf tid) (ctx.endpointDomainOf endpointId) = false
  | .coreDimensionIsAuditOnly =>
      ∀ (basePolicy : DomainFlowPolicy) (declPolicy : DeclassificationPolicy)
        (e : DeclassificationEvent) (c : CoreId),
        declassificationBasisKernelVerified basePolicy declPolicy { e with originatingCore := c } =
          declassificationBasisKernelVerified basePolicy declPolicy e
  | .perCorePartition =>
      ∀ log : DeclassificationAuditLog,
        (allCores.map (fun c => (auditLogOnCore log c).length)).sum = log.length
  | .crossCoreChainNeedsGlobalLog =>
      ∀ (log : DeclassificationAuditLog) (chain : List DeclassificationEvent),
        chainIsCrossCore chain = true →
        ∀ c : CoreId, ¬ (∀ e ∈ chain, e ∈ auditLogOnCore log c)
  | .attributionFromRunningSubject =>
      ∀ (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy) (c : CoreId)
        (dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId) (obj : KernelObject)
        (st st' : SystemState) (tid : SeLe4n.ThreadId),
        st.scheduler.currentOnCore c = some tid →
        declassifyStoreFromCore ctx declPolicy c dstDomain targetId obj st = .ok ((), st') →
        declassificationEventAttributable ctx st'
          (declassifyStoreEvent c (ctx.threadDomainOf tid) dstDomain targetId st)
  | .auditIsNotObservable =>
      ∀ (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy) (c : CoreId)
        (srcDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId) (obj : KernelObject)
        (logA logB : DeclassificationAuditLog) (st stA stB : SystemState),
        declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj
          { st with declassificationAuditLog := logA } = .ok ((), stA) →
        declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj
          { st with declassificationAuditLog := logB } = .ok ((), stB) →
        { stA with declassificationAuditLog := [] } =
          { stB with declassificationAuditLog := [] }
  | .timestampOrderIsCheckable =>
      ∃ (log : DeclassificationAuditLog) (e : DeclassificationEvent),
        declassificationAuditLogWellFormed log = true ∧
          declassificationAuditLogWellFormed (recordDeclassification log e) = false
  | .chainLinkageIsSyntactic =>
      ∃ e₁ e₂ : DeclassificationEvent,
        declassificationChainLinked [e₁, e₂] = true ∧
          e₁.targetObject ≠ e₂.targetObject ∧
          e₁.originatingCore = e₂.originatingCore
  | .refusalIsUnrecorded =>
      ∀ (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy) (c : CoreId)
        (srcDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId)
        (targetObj : KernelObject) (st : SystemState),
        declPolicy.canDeclassify srcDomain dstDomain = false →
        ctx.policy.canFlow srcDomain dstDomain = false →
        declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId targetObj st =
          .error .declassificationDenied ∧
        ¬ ∃ st', declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId targetObj st =
          .ok ((), st')
  | .liveDeclassificationWritesOnlyTheTrail =>
      ∀ (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy) (c : CoreId)
        (srcDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId)
        (st st' : SystemState),
        authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
          .ok ((), st') →
        st' = { st with
          declassificationAuditLog := declassifyStoreTrail c srcDomain dstDomain targetId st } ∧
        st.declassificationAuditLog.length < maxDeclassificationAuditEntries ∧
        declassificationDecision ctx declPolicy srcDomain dstDomain = .ok ()

/-- WS-SM SM8.C.6: **the evidence** — a total, dependently-typed function giving
each rule a proof of *its own* claim.  This is the obligation; the name table
below is the readable shadow of it. -/
def declassificationRuleEvidence : (id : DeclassificationRuleId) → id.evidenceProp
  | .compositionSoundness => fun basePolicy declPolicy chain src dst hSrc hDst hAuth =>
      chainCompositionAuthorized_sound basePolicy declPolicy chain src dst hSrc hDst hAuth
  | .hopAuthorizationDoesNotCompose =>
      declassificationChain_hop_authorization_does_not_compose
  | .endpointOverrideIsNotABasis =>
      fun ctx epPolicy declPolicy endpointId st c tid hCur hRestricted hAdmitted =>
        endpointOverride_is_not_a_declassification_basis ctx epPolicy declPolicy endpointId
          st c tid hCur hRestricted hAdmitted
  | .coreDimensionIsAuditOnly => fun basePolicy declPolicy e c =>
      declassificationBasisKernelVerified_core_independent basePolicy declPolicy e c
  | .perCorePartition => fun log => declassificationAuditLog_partitions_by_core log
  | .crossCoreChainNeedsGlobalLog => fun log chain hCross c =>
      crossCoreChain_not_within_one_view log chain hCross c
  | .attributionFromRunningSubject =>
      fun ctx declPolicy c dstDomain targetId obj st st' tid hCur hStep =>
        declassifyStoreFromCore_event_attributable ctx declPolicy c dstDomain targetId obj
          st st' tid hCur hStep
  | .auditIsNotObservable =>
      fun ctx declPolicy c srcDomain dstDomain targetId obj logA logB st stA stB
        hStepA hStepB =>
        declassifyStoreOnCore_state_trail_independent ctx declPolicy c srcDomain dstDomain targetId
          obj logA logB st stA stB hStepA hStepB
  | .timestampOrderIsCheckable => recordDeclassification_admits_ill_formed
  | .chainLinkageIsSyntactic => declassificationChainLinked_is_syntactic
  | .refusalIsUnrecorded =>
      fun ctx declPolicy c srcDomain dstDomain targetId targetObj st hDenied hNotFlow =>
        declassification_refusal_is_unrecorded ctx declPolicy c srcDomain dstDomain targetId
          targetObj st hDenied hNotFlow
  | .liveDeclassificationWritesOnlyTheTrail =>
      fun ctx declPolicy c srcDomain dstDomain targetId st st' hStep =>
        authorizeDeclassificationOnCore_frame ctx declPolicy c srcDomain dstDomain targetId
          st st' hStep

/-- WS-SM SM8.C.6: the theorem each rule rests on, compile-time-validated
through `niName!` — a renamed or deleted theorem breaks this table, not just a
comment somewhere. -/
def declassificationRuleEvidenceName : DeclassificationRuleId → String
  | .compositionSoundness => niName! chainCompositionAuthorized_sound
  | .hopAuthorizationDoesNotCompose =>
      niName! declassificationChain_hop_authorization_does_not_compose
  | .endpointOverrideIsNotABasis => niName! endpointOverride_is_not_a_declassification_basis
  | .coreDimensionIsAuditOnly => niName! declassificationBasisKernelVerified_core_independent
  | .perCorePartition => niName! declassificationAuditLog_partitions_by_core
  | .crossCoreChainNeedsGlobalLog => niName! crossCoreChain_not_within_one_view
  | .attributionFromRunningSubject => niName! declassifyStoreFromCore_event_attributable
  | .auditIsNotObservable => niName! declassifyStoreOnCore_state_trail_independent
  | .timestampOrderIsCheckable => niName! recordDeclassification_admits_ill_formed
  | .chainLinkageIsSyntactic => niName! declassificationChainLinked_is_syntactic
  | .refusalIsUnrecorded => niName! declassification_refusal_is_unrecorded
  | .liveDeclassificationWritesOnlyTheTrail =>
      niName! authorizeDeclassificationOnCore_frame

/-- WS-SM SM8.C.6: a one-line statement of each rule, for an audit report that
wants prose rather than a proof term. -/
def declassificationRuleStatement : DeclassificationRuleId → String
  | .compositionSoundness =>
      "a chain whose composition check passes really was authorized end to end"
  | .hopAuthorizationDoesNotCompose =>
      "authorizing every hop does not authorize the composition (laundering)"
  | .endpointOverrideIsNotABasis =>
      "a restricted per-endpoint override can never authorize a downgrade"
  | .coreDimensionIsAuditOnly =>
      "the originating core is audit information, never authority"
  | .perCorePartition =>
      "the per-core audit views partition the log exactly"
  | .crossCoreChainNeedsGlobalLog =>
      "a cross-core chain is contained in no single core's view"
  | .attributionFromRunningSubject =>
      "the recorded source domain is the executing core's running subject's"
  | .auditIsNotObservable =>
      "the committed state, modulo the trail, does not depend on the audit trail"
  | .timestampOrderIsCheckable =>
      "the trail's total order is a checkable predicate, not a type invariant"
  | .chainLinkageIsSyntactic =>
      "chain linkage is syntactic: matching domains and increasing timestamps"
  | .refusalIsUnrecorded =>
      "a refused declassification leaves no trace, and has no post-state to leave one in"
  | .liveDeclassificationWritesOnlyTheTrail =>
      "the live declassification writes only the audit trail; it moves no data"

theorem declassificationRules_count : DeclassificationRuleId.all.length = 12 := by rfl

/-- WS-SM SM8.C.6: every rule names a theorem — no rule is discharged with an
empty citation. -/
theorem declassificationRuleEvidence_nonempty :
    ∀ id : DeclassificationRuleId, (declassificationRuleEvidenceName id).length > 0 := by
  intro id; cases id <;> decide

/-- WS-SM SM8.C.6: no two rules share a witness — each is carried by its own
theorem, so no rule is a restatement of another. -/
theorem declassificationRuleEvidence_distinct :
    (DeclassificationRuleId.all.map declassificationRuleEvidenceName).length = 12 ∧
      ∀ id₁ id₂ : DeclassificationRuleId,
        declassificationRuleEvidenceName id₁ = declassificationRuleEvidenceName id₂ →
        id₁ = id₂ := by
  refine ⟨rfl, ?_⟩
  intro id₁ id₂ h
  cases id₁ <;> cases id₂ <;> first | rfl | (exfalso; exact absurd h (by decide))

/-- WS-SM SM8.C.6: every rule has a statement — the prose half is total too. -/
theorem declassificationRuleStatement_nonempty :
    ∀ id : DeclassificationRuleId, (declassificationRuleStatement id).length > 0 := by
  intro id; cases id <;> decide

-- ============================================================================
-- §14  SM9.A.4a — the observation relation an audit reader is described by
-- ============================================================================

/-! ## Adding a reader changes what is observable

SM8.C could keep the audit trail out of `ObservableState` for a reason it stated
plainly: nothing could read it, so
`declassificationAuditLog_write_preserves_projection` is `rfl`.  **SM9.A makes it
readable, and that changes the observation relation.**

The consequence is concrete and easy to miss.  The naive lemma —
*"two states low-equivalent at `L` give identical visible views"* — is **false**:
`lowEquivalent` compares `ObservableState`, which does not contain the trail, so
two low-equivalent states can differ by an audit entry whose `srcDomain` flows to
`L`, and their `auditLogVisibleTo` results then differ
(`lowEquivalent_does_not_determine_visible_view`).

Two ways to make the relation match the reader:

* **Extend `ObservableState`** with the clearance-filtered trail as a fourteenth
  component.  Honest — it *is* now observable — but the SM8.A field partition is
  a bijection with `ObservableState.ofFragments_eta`, deliberately built so a
  fourteenth field is a compile error, and every SM8.B non-interference theorem
  moves with it.
* **A separate relation** conjoining `lowEquivalent` with agreement on what the
  reader can see.  Contained; every SM8 theorem stands unchanged; and the flow
  argument is stated in the relation that actually describes an audit reader's
  observations rather than in one that describes a subject with no reader.

**Decision: the second.**  `ObservableState` stays a thirteen-component
partition and its tripwire keeps working.  The first becomes the right move only
if a later phase adds a *second* readable-but-unprojected structure — at that
point one relation per reader stops scaling and the partition should absorb them.
Recorded here so that decision is made on evidence rather than rediscovered. -/

/-- WS-SM SM9.A.4a (plan §3.7): **the clause set, as a total function.**

Not a list with a `mem_all` completeness theorem, and the difference is the
whole mechanism.  `mem_all` proves every constructor of a hand-maintained type
appears in `all`, and nothing forces a newly mounted readable field to add a
constructor at all (`readableStructure_list_gate_insufficient`).  A **missing
case in a total function is a compile error**, and `AuditReadOp` is fused with
`ReadableStructure` so a read operation cannot exist without naming a structure
— which is what makes the constructor unavoidable in the first place.

The trail's clause has two halves because the reader exports two things: the
entries its clearance admits, and — only under the configured monitor gate — the
epoch.  The epoch is conditional rather than always present because it *counts*
entries, including entries a partial reader may not see. -/
def readableStructureAgrees (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (s₁ s₂ : SystemState) : ReadableStructure → Prop
  | .declassificationAuditTrail =>
      auditLogVisibleTo ctx reader s₁.declassificationAuditLog
        = auditLogVisibleTo ctx reader s₂.declassificationAuditLog ∧
      (auditMonitorAuthorized ctx monitorClearance reader = true →
        s₁.declassificationAuditEpoch = s₂.declassificationAuditEpoch)

/-- WS-SM SM9.A.4a: the totality anchor.  The *mechanism* is the definition —
an exhaustive match with no wildcard, so a new `ReadableStructure` constructor
does not elaborate until it has a clause; this theorem is the named surface for
that fact. -/
theorem auditObservationalEquivalence_clause_total (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (s₁ s₂ : SystemState) (str : ReadableStructure) :
    ∃ p : Prop, readableStructureAgrees ctx monitorClearance reader s₁ s₂ str = p :=
  ⟨_, rfl⟩

/-- WS-SM SM9.A.4a: **the relation an audit reader is described by** —
`lowEquivalent` conjoined with agreement on every readable structure.

Stated over a `LabelingContext` and lifted internally, because that is the shape
the live arm runs in (`liftLegacyContext ctx`): a relation stated over a
different context than the dispatch uses would describe a reader the kernel does
not have. -/
def auditObservationalEquivalence (ctx : LabelingContext) (observer : IfObserver)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (s₁ s₂ : SystemState) : Prop :=
  lowEquivalent ctx observer s₁ s₂ ∧
  ∀ str : ReadableStructure,
    readableStructureAgrees (liftLegacyContext ctx) monitorClearance reader s₁ s₂ str

/-- WS-SM SM9.A.4a: reflexivity. -/
theorem auditObservationalEquivalence_refl (ctx : LabelingContext) (observer : IfObserver)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain) (s : SystemState) :
    auditObservationalEquivalence ctx observer monitorClearance reader s s :=
  ⟨rfl, fun str => by cases str; exact ⟨rfl, fun _ => rfl⟩⟩

/-- WS-SM SM9.A.4a: symmetry. -/
theorem auditObservationalEquivalence_symm (ctx : LabelingContext) (observer : IfObserver)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    {s₁ s₂ : SystemState}
    (h : auditObservationalEquivalence ctx observer monitorClearance reader s₁ s₂) :
    auditObservationalEquivalence ctx observer monitorClearance reader s₂ s₁ := by
  refine ⟨h.1.symm, fun str => ?_⟩
  cases str
  obtain ⟨hView, hEpoch⟩ := h.2 .declassificationAuditTrail
  exact ⟨hView.symm, fun hMon => (hEpoch hMon).symm⟩

/-- WS-SM SM9.A.4a: transitivity. -/
theorem auditObservationalEquivalence_trans (ctx : LabelingContext) (observer : IfObserver)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    {s₁ s₂ s₃ : SystemState}
    (h₁ : auditObservationalEquivalence ctx observer monitorClearance reader s₁ s₂)
    (h₂ : auditObservationalEquivalence ctx observer monitorClearance reader s₂ s₃) :
    auditObservationalEquivalence ctx observer monitorClearance reader s₁ s₃ := by
  refine ⟨h₁.1.trans h₂.1, fun str => ?_⟩
  cases str
  obtain ⟨hView₁, hEpoch₁⟩ := h₁.2 .declassificationAuditTrail
  obtain ⟨hView₂, hEpoch₂⟩ := h₂.2 .declassificationAuditTrail
  exact ⟨hView₁.trans hView₂, fun hMon => (hEpoch₁ hMon).trans (hEpoch₂ hMon)⟩

/-- WS-SM SM9.A.4a (**the general congruence**): a transition that frames the
trail and the epoch on both sides, and preserves the projection, preserves the
relation.

This is the congruence that covers *most* of the kernel: every transition that
is not an audit writer frames both fields, so the relation rides them for free.
The two that do write are handled below. -/
theorem auditObservationalEquivalence_of_trailFramed (ctx : LabelingContext)
    (observer : IfObserver) (monitorClearance : Option SecurityDomain)
    (reader : SecurityDomain) {s₁ s₂ s₁' s₂' : SystemState}
    (h : auditObservationalEquivalence ctx observer monitorClearance reader s₁ s₂)
    (hProj : lowEquivalent ctx observer s₁' s₂')
    (hTrail₁ : s₁'.declassificationAuditLog = s₁.declassificationAuditLog)
    (hTrail₂ : s₂'.declassificationAuditLog = s₂.declassificationAuditLog)
    (hEpoch₁ : s₁'.declassificationAuditEpoch = s₁.declassificationAuditEpoch)
    (hEpoch₂ : s₂'.declassificationAuditEpoch = s₂.declassificationAuditEpoch) :
    auditObservationalEquivalence ctx observer monitorClearance reader s₁' s₂' := by
  refine ⟨hProj, fun str => ?_⟩
  cases str
  obtain ⟨hView, hEp⟩ := h.2 .declassificationAuditTrail
  refine ⟨?_, fun hMon => ?_⟩
  · rw [hTrail₁, hTrail₂]; exact hView
  · rw [hEpoch₁, hEpoch₂]; exact hEp hMon

/-- WS-SM SM9.A.4a: **the declassification's congruence.**

Two equivalent states that record the *same* event stay equivalent.  The
premise is not a formality: the recorded timestamp is `epoch + length`, which is
a **global** quantity, so two states with different hidden histories append
events that differ in that field even when everything the reader can export
agrees.  That is the relation being finer than the reader's discrimination
rather than a leak — `auditRead_hides_global_position` is the statement that a
partial reader cannot tell — and stating the premise is the honest way to say
so.  For a monitor the premise is discharged, since its view is the whole trail
and its epoch agrees. -/
theorem authorizeDeclassificationOnCore_preserves_auditObservationalEquivalence
    (ctx : LabelingContext) (observer : IfObserver)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (gctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy) (c : CoreId)
    (srcDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId)
    {s₁ s₂ s₁' s₂' : SystemState}
    (h : auditObservationalEquivalence ctx observer monitorClearance reader s₁ s₂)
    (hProj : lowEquivalent ctx observer s₁' s₂')
    (hSameEvent : declassifyStoreEvent c srcDomain dstDomain targetId s₁ =
      declassifyStoreEvent c srcDomain dstDomain targetId s₂)
    (hStep₁ : authorizeDeclassificationOnCore gctx declPolicy c srcDomain dstDomain targetId s₁
      = .ok ((), s₁'))
    (hStep₂ : authorizeDeclassificationOnCore gctx declPolicy c srcDomain dstDomain targetId s₂
      = .ok ((), s₂')) :
    auditObservationalEquivalence ctx observer monitorClearance reader s₁' s₂' := by
  obtain ⟨hSt₁, -, -⟩ := authorizeDeclassificationOnCore_frame gctx declPolicy c srcDomain
    dstDomain targetId s₁ s₁' hStep₁
  obtain ⟨hSt₂, -, -⟩ := authorizeDeclassificationOnCore_frame gctx declPolicy c srcDomain
    dstDomain targetId s₂ s₂' hStep₂
  subst hSt₁; subst hSt₂
  refine ⟨hProj, fun str => ?_⟩
  cases str
  obtain ⟨hView, hEp⟩ := h.2 .declassificationAuditTrail
  refine ⟨?_, fun hMon => hEp hMon⟩
  show auditLogVisibleTo (liftLegacyContext ctx) reader
      (declassifyStoreTrail c srcDomain dstDomain targetId s₁) =
    auditLogVisibleTo (liftLegacyContext ctx) reader
      (declassifyStoreTrail c srcDomain dstDomain targetId s₂)
  simp only [declassifyStoreTrail, recordDeclassification, auditLogVisibleTo_append, hView,
    hSameEvent]

/-- WS-SM SM9.A.4a: **the drain's congruence**, for the caller that can perform
one.

A monitor's view is the whole trail and its epoch agrees, so two equivalent
states drained by the same count stay equivalent — and this is the congruence
that matters, because the drain is the reader's *own* write. -/
theorem auditDrain_preserves_auditObservationalEquivalence
    (ctx : LabelingContext) (observer : IfObserver)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (c : CoreId) (count : Nat) {s₁ s₂ : SystemState} {n₁ n₂ : Nat} {s₁' s₂' : SystemState}
    (h : auditObservationalEquivalence ctx observer monitorClearance reader s₁ s₂)
    (hProj : lowEquivalent ctx observer s₁' s₂')
    (hMonitor : auditMonitorAuthorized (liftLegacyContext ctx) monitorClearance reader = true)
    (hFull₁ : auditLogVisibleTo (liftLegacyContext ctx) reader s₁.declassificationAuditLog
      = s₁.declassificationAuditLog)
    (hFull₂ : auditLogVisibleTo (liftLegacyContext ctx) reader s₂.declassificationAuditLog
      = s₂.declassificationAuditLog)
    (hStep₁ : auditDrainVisiblePrefix (liftLegacyContext ctx) monitorClearance c count s₁
      = .ok (n₁, s₁'))
    (hStep₂ : auditDrainVisiblePrefix (liftLegacyContext ctx) monitorClearance c count s₂
      = .ok (n₂, s₂')) :
    auditObservationalEquivalence ctx observer monitorClearance reader s₁' s₂' := by
  obtain ⟨hView, hEp⟩ := h.2 .declassificationAuditTrail
  have hTrail : s₁.declassificationAuditLog = s₂.declassificationAuditLog := by
    rw [← hFull₁, ← hFull₂]; exact hView
  have hEpoch := hEp hMonitor
  obtain ⟨hSt₁, -, -⟩ := auditDrain_frame (liftLegacyContext ctx) monitorClearance c count
    s₁ n₁ s₁' hStep₁
  obtain ⟨hSt₂, -, -⟩ := auditDrain_frame (liftLegacyContext ctx) monitorClearance c count
    s₂ n₂ s₂' hStep₂
  subst hSt₁; subst hSt₂
  refine ⟨hProj, fun str => ?_⟩
  cases str
  refine ⟨?_, fun _ => ?_⟩
  · show auditLogVisibleTo (liftLegacyContext ctx) reader
        (s₁.declassificationAuditLog.drop (min count s₁.declassificationAuditLog.length)) =
      auditLogVisibleTo (liftLegacyContext ctx) reader
        (s₂.declassificationAuditLog.drop (min count s₂.declassificationAuditLog.length))
    rw [hTrail]
  · show s₁.declassificationAuditEpoch + min count s₁.declassificationAuditLog.length =
      s₂.declassificationAuditEpoch + min count s₂.declassificationAuditLog.length
    rw [hTrail, hEpoch]

/-- WS-SM SM9.A.4a (**the load-bearing negative**): plain `lowEquivalent` does
**not** imply equal visible views.

The lemma an earlier draft of this sub-task specified — "two states
low-equivalent at `L` give identical visible views" — is not merely
unproven, it is **false**, and shipping it would have surfaced
mid-implementation.  `lowEquivalent` compares `ObservableState`, which by design
does not contain the trail; the witness is the smallest instance of that gap, a
state that differs from the boot state by exactly one audit entry the reader is
cleared to see. -/
theorem lowEquivalent_does_not_determine_visible_view :
    ∃ (ctx : LabelingContext) (observer : IfObserver) (gctx : GenericLabelingContext)
      (reader : SecurityDomain) (s₁ s₂ : SystemState),
      lowEquivalent ctx observer s₁ s₂ ∧
      auditLogVisibleTo gctx reader s₁.declassificationAuditLog ≠
        auditLogVisibleTo gctx reader s₂.declassificationAuditLog := by
  refine ⟨defaultLabelingContext, IfObserver.ofLabel SecurityLabel.publicLabel,
    { policy := DomainFlowPolicy.allowAll
      objectDomainOf := fun _ => SecurityDomain.lowest
      threadDomainOf := fun _ => SecurityDomain.lowest
      endpointDomainOf := fun _ => SecurityDomain.lowest
      serviceDomainOf := fun _ => SecurityDomain.lowest },
    SecurityDomain.lowest, default,
    { (default : SystemState) with
      declassificationAuditLog := [auditTimestampWitness 0] }, ?_, ?_⟩
  · exact (declassificationAuditLog_write_preserves_projection _ _ default _).symm
  · simp [auditLogVisibleTo, DomainFlowPolicy.allowAll]

-- ============================================================================
-- §15  SM9.A.4b — the reader opens no channel
-- ============================================================================

/-- WS-SM SM9.A.4b (**the flow argument**): the reader is a function of the
observation relation — two states an audit reader cannot distinguish return the
same word for **every** sub-operation.

Substantive rather than definitional: the relation compares the *visible view*
and (conditionally) the epoch, and this theorem is what establishes that no arm
reads anything else — not the hidden entries, not the trail's length, not the
epoch when the caller is not entitled to it. -/
theorem auditRead_no_channel (ctx : LabelingContext) (observer : IfObserver)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (s₁ s₂ : SystemState) (op : AuditReadOp)
    (h : auditObservationalEquivalence ctx observer monitorClearance reader s₁ s₂) :
    auditReadWord (liftLegacyContext ctx) monitorClearance reader s₁ op =
      auditReadWord (liftLegacyContext ctx) monitorClearance reader s₂ op := by
  obtain ⟨hView, hEpoch⟩ := h.2 .declassificationAuditTrail
  exact auditRead_determined_by_view (liftLegacyContext ctx) monitorClearance reader s₁ s₂ op
    hView hEpoch

/-- WS-SM SM9.A.4b: the same for the live entry point.

The equal reader resolution (`hReader₁`/`hReader₂`) is a **hypothesis**, not a
consequence of the equivalence: `auditObservationalEquivalence` carries
`lowEquivalent`, which compares *projections*, and a projection does not
determine the domain of a current thread the observer cannot see — so two
equivalent states can genuinely resolve different readers on a core running a
subject above the observer's clearance.  The theorem says what is true: at
whatever clearance the state resolves, the returned word is a function of that
clearance's visible view alone. -/
theorem auditReadFromCore_no_channel (ctx : LabelingContext) (observer : IfObserver)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (c : CoreId) (s₁ s₂ : SystemState) (op : AuditReadOp)
    (w₁ w₂ : Nat) (r₁ r₂ : SystemState)
    (h : auditObservationalEquivalence ctx observer monitorClearance reader s₁ s₂)
    (hReader₁ : auditReaderDomain (liftLegacyContext ctx) s₁ c = some reader)
    (hReader₂ : auditReaderDomain (liftLegacyContext ctx) s₂ c = some reader)
    (hStep₁ : auditReadFromCore (liftLegacyContext ctx) monitorClearance c op s₁
      = .ok (w₁, r₁))
    (hStep₂ : auditReadFromCore (liftLegacyContext ctx) monitorClearance c op s₂
      = .ok (w₂, r₂)) :
    w₁ = w₂ := by
  have hv₁ := auditReadFromCore_value (liftLegacyContext ctx) monitorClearance c op s₁ reader
    w₁ r₁ hReader₁ hStep₁
  have hv₂ := auditReadFromCore_value (liftLegacyContext ctx) monitorClearance c op s₂ reader
    w₂ r₂ hReader₂ hStep₂
  rw [auditRead_no_channel ctx observer monitorClearance reader s₁ s₂ op h] at hv₁
  exact Except.ok.inj (hv₁.symm.trans hv₂)

/-- WS-SM SM9.A.4b (**why this is not an eighth covert channel**): the reader is
capability-gated, right-gated and clearance-filtered — an *authorized, audited*
read rather than an unauthorized information path.

Registering a CC-8 would cost a `CovertChannelId` constructor, four total-match
tables, a witness theorem, five numeric theorems, Tier-3 anchors and a
golden-fixture line, and it is **not owed**: a covert channel is a path that
carries information *without* authorization.  What the reader *is* owed is an
observation relation describing what it can see, which §14 supplies and
`auditRead_no_channel` is stated over.

The three gates, as one checkable statement: a capability that does not target
the audit trail is rejected outright; an unconfigured deployment has no monitor,
so no caller may drain; and a caller that is not the monitor sees no epoch. -/
theorem auditRead_gates_are_three (ctx : LabelingContext) (oid : SeLe4n.ObjId)
    (reader : SecurityDomain) (c : CoreId) (count : Nat) (st : SystemState)
    (epoch : Nat) :
    extractAuditAuthority
        { target := .object oid, rights := AccessRightSet.ofList AccessRight.all,
          badge := none } = .error .invalidCapability ∧
    auditDrainVisiblePrefix (liftLegacyContext ctx) none c count st = .error .illegalAuthority ∧
    auditReadWord (liftLegacyContext ctx) none reader
        { st with declassificationAuditEpoch := epoch } .status =
      auditReadWord (liftLegacyContext ctx) none reader st .status :=
  ⟨extractAuditAuthority_rejects_non_audit_capability oid,
   auditDrain_unconfigured_denied (liftLegacyContext ctx) c count st,
   auditReadStatus_partial_hides_generation (liftLegacyContext ctx) none reader st epoch rfl⟩

/-- WS-SM SM9.A.4b: the drain's own per-core non-interference — it writes the
trail and the epoch, and no observer on any core reads either. -/
theorem auditDrain_preserves_projectionOnCore (ctx : LabelingContext) (observer : IfObserver)
    (gctx : GenericLabelingContext) (monitorClearance : Option SecurityDomain)
    (c : CoreId) (count : Nat) (st : SystemState) (n : Nat) (st' : SystemState)
    (viewCore : CoreId)
    (hStep : auditDrainVisiblePrefix gctx monitorClearance c count st = .ok (n, st')) :
    projectStateOnCore ctx observer st' viewCore = projectStateOnCore ctx observer st viewCore := by
  obtain ⟨hSt', -, -⟩ := auditDrain_frame gctx monitorClearance c count st n st' hStep
  subst hSt'
  rfl

/-- WS-SM SM9.A.4b: and the ∀-core aggregate — a drain is invisible to every
per-core observer. -/
theorem auditDrain_perCore_NI (ctx : LabelingContext) (observer : IfObserver)
    (gctx : GenericLabelingContext) (monitorClearance : Option SecurityDomain)
    (c : CoreId) (count : Nat) (st : SystemState) (n : Nat) (st' : SystemState)
    (hStep : auditDrainVisiblePrefix gctx monitorClearance c count st = .ok (n, st')) :
    lowEquivalent_smp ctx observer st st' :=
  fun viewCore =>
    (auditDrain_preserves_projectionOnCore ctx observer gctx monitorClearance c count st n st'
      viewCore hStep).symm

/-- WS-SM SM9.A.4b: the read writes nothing, so it is invisible on every core
for the strongest possible reason — there is no post-state to compare. -/
theorem auditReadFromCore_perCore_NI (ctx : LabelingContext) (observer : IfObserver)
    (gctx : GenericLabelingContext) (monitorClearance : Option SecurityDomain)
    (c : CoreId) (op : AuditReadOp) (st : SystemState) (w : Nat) (st' : SystemState)
    (hStep : auditReadFromCore gctx monitorClearance c op st = .ok (w, st')) :
    lowEquivalent_smp ctx observer st st' := by
  have hEq := auditReadFromCore_frame gctx monitorClearance c op st w st' hStep
  subst hEq
  exact fun _ => rfl


end SeLe4n.Kernel
