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
  position, so ordering is structural rather than a caller convention, and a
  timestamp identifies an event across every core.
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
* §9 — the rules as data, each carrying the theorem that makes it a fact.

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

/-- WS-SM SM8.C: the audit log's timestamps run consecutively from `start`.

Written as a `Bool` recursion rather than an indexed `Prop` so an audit consumer
can *decide* it on a concrete log; `auditTimestampsFrom_iff` is the indexed
characterisation the proofs use. -/
def auditTimestampsFrom (start : Nat) : DeclassificationAuditLog → Bool
  | [] => true
  | e :: rest => (e.timestamp == start) && auditTimestampsFrom (start + 1) rest

/-- WS-SM SM8.C: **the audit log is well-formed** — every event's timestamp is
its own position in the log.

This is the structural form of V6-H's "monotonic event counter": monotonicity is
not a property a producer must remember to maintain, it is what the position
*is*. -/
def declassificationAuditLogWellFormed (log : DeclassificationAuditLog) : Bool :=
  auditTimestampsFrom 0 log

/-- WS-SM SM8.C: the indexed characterisation — the `Bool` check holds exactly
when every entry's timestamp is `start` plus its index. -/
theorem auditTimestampsFrom_iff (start : Nat) (log : DeclassificationAuditLog) :
    auditTimestampsFrom start log = true ↔
      ∀ (i : Nat) (h : i < log.length), (log[i]'h).timestamp = start + i := by
  induction log generalizing start with
  | nil => simp [auditTimestampsFrom]
  | cons e rest ih =>
    simp only [auditTimestampsFrom, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨hHead, hTail⟩ i hi
      cases i with
      | zero => simpa using hHead
      | succ n =>
        have hn : n < rest.length := by
          simp only [List.length_cons] at hi; omega
        have hRest := hTail n hn
        rw [List.getElem_cons_succ]
        omega
    · intro h
      refine ⟨?_, ?_⟩
      · have h0 := h 0 (by simp)
        simpa using h0
      · intro i hi
        have hi' : i + 1 < (e :: rest).length := by
          simp only [List.length_cons]; omega
        have hs := h (i + 1) hi'
        rw [List.getElem_cons_succ] at hs
        omega

/-- WS-SM SM8.C: the well-formed log's timestamps are exactly its indices. -/
theorem declassificationAuditLogWellFormed_iff (log : DeclassificationAuditLog) :
    declassificationAuditLogWellFormed log = true ↔
      ∀ (i : Nat) (h : i < log.length), (log[i]'h).timestamp = i := by
  simp [declassificationAuditLogWellFormed, auditTimestampsFrom_iff]

/-- WS-SM SM8.C: the empty log is well-formed — the boot witness every audited
run starts from. -/
theorem declassificationAuditLogWellFormed_nil :
    declassificationAuditLogWellFormed [] = true := rfl

/-- WS-SM SM8.C: appending distributes — the check on `log ++ [e]` is the check
on `log` conjoined with `e`'s timestamp landing at `log`'s end. -/
theorem auditTimestampsFrom_append (start : Nat) (log : DeclassificationAuditLog)
    (e : DeclassificationEvent) :
    auditTimestampsFrom start (log ++ [e]) =
      (auditTimestampsFrom start log && (e.timestamp == start + log.length)) := by
  induction log generalizing start with
  | nil => simp [auditTimestampsFrom]
  | cons a rest ih =>
    have hArith : start + 1 + rest.length = start + (rest.length + 1) := by omega
    simp only [List.cons_append, auditTimestampsFrom, ih, Bool.and_assoc,
      List.length_cons, hArith]

/-- WS-SM SM8.C: **recording preserves well-formedness** exactly when the
recorded event's timestamp is the pre-log's length.  §2's producer computes it
that way, so the invariant rides every audited declassification. -/
theorem recordDeclassification_preserves_wellFormed (log : DeclassificationAuditLog)
    (e : DeclassificationEvent)
    (hWF : declassificationAuditLogWellFormed log = true)
    (hTs : e.timestamp = log.length) :
    declassificationAuditLogWellFormed (recordDeclassification log e) = true := by
  simp only [declassificationAuditLogWellFormed, recordDeclassification,
    auditTimestampsFrom_append, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hWF, by omega⟩

/-- WS-SM SM8.C.2 (the ordering result the cross-core chain reconstruction
rests on): **in a well-formed log a timestamp identifies an event**, whichever
cores the events came from.

This is why `declassifyStoreOnCore` derives the timestamp from the length of the
whole log rather than from a per-core counter.  A per-core counter would make
two events on two cores share a timestamp, and the interleaving of a chain that
crosses cores would be unrecoverable from the record. -/
theorem declassificationAuditLog_timestamp_identifies_event
    (log : DeclassificationAuditLog)
    (hWF : declassificationAuditLogWellFormed log = true)
    {e₁ e₂ : DeclassificationEvent} (h₁ : e₁ ∈ log) (h₂ : e₂ ∈ log)
    (hTs : e₁.timestamp = e₂.timestamp) : e₁ = e₂ := by
  rw [declassificationAuditLogWellFormed_iff] at hWF
  obtain ⟨i₁, hi₁, hEq₁⟩ := List.getElem_of_mem h₁
  obtain ⟨i₂, hi₂, hEq₂⟩ := List.getElem_of_mem h₂
  have hT₁ : e₁.timestamp = i₁ := by rw [← hEq₁]; exact hWF i₁ hi₁
  have hT₂ : e₂.timestamp = i₂ := by rw [← hEq₂]; exact hWF i₂ hi₂
  have hIdx : i₁ = i₂ := by omega
  subst hIdx
  rw [← hEq₁, ← hEq₂]

-- ============================================================================
-- §2  SM8.C.1 — the audited per-core declassification (the producer)
-- ============================================================================
--
-- `declassifyStore` gates and stores.  What it never did is record, which left
-- `DeclassificationEvent`'s docstring describing a producer that did not exist.
-- The audited form below threads the append-only log *through* the operation,
-- so a successful downgrade and its audit entry are one step: there is no
-- window in which the store has happened and the record has not, and no caller
-- convention to forget.

/-- WS-SM SM8.C.1: the event an authorized downgrade on core `c` records.

Three of the six fields are not free choices: the basis is `.policyRule`
(the only gate the kernel runs), the timestamp is the log position
(§1), and the core is the core the operation ran on.  Only the two domains and
the target come from the caller — and §3 removes the source domain from that
list too. -/
def declassificationEventOnCore (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (log : DeclassificationAuditLog) : DeclassificationEvent :=
  { srcDomain := srcDomain
    dstDomain := dstDomain
    targetObject := targetId
    authorizationBasis := .policyRule
    timestamp := log.length
    originatingCore := c }

/-- WS-SM SM8.C.1: **the audited declassification.**  The `Enforcement/Soundness`
gate, run on core `c`, threading the audit log: on success the object is stored
*and* the event is appended; on refusal the operation fails and the log the
caller holds is the log it started with.

The state effect is exactly `declassifyStore`'s
(`declassifyStoreOnCore_ok_inv`), so every theorem the tree already proves about
the unaudited gate — `enforcementSoundness_declassifyStore`,
`declassifyStore_NI` — carries over unchanged.  Auditing adds a record, not a
transition. -/
def declassifyStoreOnCore
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log : DeclassificationAuditLog) : Kernel DeclassificationAuditLog :=
  fun st =>
    match declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st with
    | .ok ((), st') =>
        .ok (recordDeclassification log
              (declassificationEventOnCore c srcDomain dstDomain targetId log), st')
    | .error err => .error err

/-- WS-SM SM8.C.1: the forward direction — a successful gate gives a successful
audited step, with the state the gate produced and the log it grew. -/
theorem declassifyStoreOnCore_of_ok
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log : DeclassificationAuditLog) (st st' : SystemState)
    (hStep : declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .ok ((), st')) :
    declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
      .ok (recordDeclassification log
            (declassificationEventOnCore c srcDomain dstDomain targetId log), st') := by
  simp [declassifyStoreOnCore, hStep]

/-- WS-SM SM8.C.1: a refused gate refuses the audited step, with the same error.
Fail-closed: there is no arm on which the audit succeeds and the gate does
not. -/
theorem declassifyStoreOnCore_of_error
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log : DeclassificationAuditLog) (st : SystemState) (err : KernelError)
    (hStep : declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .error err) :
    declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
      .error err := by
  simp [declassifyStoreOnCore, hStep]

/-- WS-SM SM8.C.1 (**the transport lemma**): a successful audited step decomposes
into the gate's own success and exactly one appended event.

This is what makes the audit non-invasive: downstream reasoning about the
audited operation rewrites to reasoning about `declassifyStore`, which is where
the enforcement and non-interference theorems already live. -/
theorem declassifyStoreOnCore_ok_inv
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log log' : DeclassificationAuditLog) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
      .ok (log', st')) :
    declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .ok ((), st') ∧
      log' = recordDeclassification log
        (declassificationEventOnCore c srcDomain dstDomain targetId log) := by
  unfold declassifyStoreOnCore at hStep
  -- Generalise the gate's result *before* casing on it: a bare `cases h : …`
  -- would rewrite the goal's own occurrence of `declassifyStore …` too, leaving
  -- a conclusion about the case value rather than about the gate.
  obtain ⟨res, hRes⟩ :
      ∃ r, declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = r := ⟨_, rfl⟩
  rw [hRes] at hStep
  cases res with
  | error err => simp at hStep
  | ok pair =>
    obtain ⟨u, stMid⟩ := pair
    cases u
    simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
    obtain ⟨hLogEq, hStEq⟩ := hStep
    subst hStEq
    exact ⟨hRes, hLogEq.symm⟩

/-- WS-SM SM8.C.1: **exactly one event per authorized downgrade.**  Not "at
least one" and not "the caller may add one": the log grows by one, and by the
event the operation itself computed. -/
theorem declassifyStoreOnCore_records_one
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log log' : DeclassificationAuditLog) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
      .ok (log', st')) :
    log' = log ++ [declassificationEventOnCore c srcDomain dstDomain targetId log] ∧
      log'.length = log.length + 1 := by
  obtain ⟨_, hLog⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain dstDomain
    targetId obj log log' st st' hStep
  exact ⟨hLog, by rw [hLog]; exact recordDeclassification_length log _⟩

/-- WS-SM SM8.C.1: the audit trail is append-only across the operation — every
event already recorded survives.  (`recordDeclassification` is append-only on
its own; this is the statement at the transition, which is where a producer
could otherwise have rewritten history.) -/
theorem declassifyStoreOnCore_preserves_existing
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log log' : DeclassificationAuditLog) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
      .ok (log', st')) :
    ∀ e ∈ log, e ∈ log' := by
  obtain ⟨_, hLog⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain dstDomain
    targetId obj log log' st st' hStep
  intro e hMem
  rw [hLog]
  exact recordDeclassification_preserves_existing log _ e hMem

/-- WS-SM SM8.C.1 (**the field the phase exists for**): the recorded core is the
core the operation ran on.

Load-bearing rather than definitional bookkeeping: the pre-SM8.C record had no
core at all, and the tempting way to add one — default it to `bootCoreId` — would
make this theorem false for every secondary core while still compiling
everywhere. -/
theorem declassifyStoreOnCore_originatingCore
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (log : DeclassificationAuditLog) :
    (declassificationEventOnCore c srcDomain dstDomain targetId log).originatingCore = c := rfl

/-- WS-SM SM8.C.5: the kernel records its own basis, never an integrator
override — so `kernelVerifiable` is `true` on everything the kernel writes. -/
theorem declassifyStoreOnCore_basis_is_policyRule
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (log : DeclassificationAuditLog) :
    (declassificationEventOnCore c srcDomain dstDomain targetId log).authorizationBasis =
      .policyRule := rfl

/-- WS-SM SM8.C: the recorded timestamp is the position the event lands at — the
premise `recordDeclassification_preserves_wellFormed` needs. -/
theorem declassifyStoreOnCore_timestamp
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (log : DeclassificationAuditLog) :
    (declassificationEventOnCore c srcDomain dstDomain targetId log).timestamp =
      log.length := rfl

/-- WS-SM SM8.C: the audited operation preserves log well-formedness, so §1's
total order holds of every log an audited run can produce (starting, by
`declassificationAuditLogWellFormed_nil`, from the empty one). -/
theorem declassifyStoreOnCore_preserves_wellFormed
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log log' : DeclassificationAuditLog) (st st' : SystemState)
    (hWF : declassificationAuditLogWellFormed log = true)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
      .ok (log', st')) :
    declassificationAuditLogWellFormed log' = true := by
  obtain ⟨_, hLog⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain dstDomain
    targetId obj log log' st st' hStep
  rw [hLog]
  exact recordDeclassification_preserves_wellFormed log _ hWF rfl

/-- WS-SM SM8.C.5 (**audit soundness**): a recorded event's basis is not a
claim, it is a check that ran.  Both halves of `isDeclassificationAuthorized`
held at the moment the event was written: the base policy denied the flow (so
this genuinely was a downgrade) and the declassification policy permitted it. -/
theorem declassifyStoreOnCore_authorized
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log log' : DeclassificationAuditLog) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
      .ok (log', st')) :
    ctx.policy.canFlow srcDomain dstDomain = false ∧
      declPolicy.canDeclassify srcDomain dstDomain = true := by
  obtain ⟨hGate, _⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain dstDomain
    targetId obj log log' st st' hStep
  exact enforcementSoundness_declassifyStore ctx declPolicy srcDomain dstDomain targetId obj
    st st' hGate

/-- WS-SM SM8.C.1 (**fail-closed, and unaudited**): when either authorization
check fails there is no post-state and no audit entry — the operation cannot
succeed, so nothing is stored and nothing is recorded.

The second half is the scope boundary the module docstring states: a refused
attempt leaves no trace, because the V6-H record has no outcome field to carry
one. -/
theorem declassifyStoreOnCore_denied_no_audit_entry
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log : DeclassificationAuditLog) (st : SystemState)
    (hDenied : ctx.policy.canFlow srcDomain dstDomain = true ∨
      declPolicy.canDeclassify srcDomain dstDomain = false) :
    ∀ log' st', declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st ≠
      .ok (log', st') := by
  intro log' st' hStep
  obtain ⟨hNormal, hDecl⟩ := declassifyStoreOnCore_authorized ctx declPolicy c srcDomain
    dstDomain targetId obj log log' st st' hStep
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

/-- WS-SM SM8.C.3: the domain of the subject core `c` is running, if any.

The per-core read `currentOnCore c` is deliberate: under SMP "the current
thread" is not a single value, and a boot-pinned read would attribute every
secondary core's downgrade to whatever the boot core happened to be running.
The same read `endpointFlowCheckAtCore` (SM8.B.11) uses for the same reason. -/
def declassificationSubjectDomainOnCore (ctx : GenericLabelingContext) (st : SystemState)
    (c : CoreId) : Option SecurityDomain :=
  (st.scheduler.currentOnCore c).map ctx.threadDomainOf

/-- WS-SM SM8.C.3: **the event is attributable** — the core it names was running
a subject, and that subject's domain is the source domain the event records.

An unattributable event is not a forged one (the kernel does not forge); it is
an event whose `srcDomain` cannot be checked against anything, which is what an
auditor needs to be able to rule out. -/
def declassificationEventAttributable (ctx : GenericLabelingContext) (st : SystemState)
    (e : DeclassificationEvent) : Prop :=
  declassificationSubjectDomainOnCore ctx st e.originatingCore = some e.srcDomain

/-- WS-SM SM8.C.3: **the attributed entry point.**  The declassification a live
path must call: it resolves the source domain from core `c`'s current thread
rather than accepting one, and fails closed on a core that is running nothing.

`declassifyStoreOnCore` remains the internal step (§2) — this is the wrapper
that makes the audit record's subject a fact about the state rather than a
parameter. -/
def declassifyStoreFromCore
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log : DeclassificationAuditLog) : Kernel DeclassificationAuditLog :=
  fun st =>
    match st.scheduler.currentOnCore c with
    | none => .error .illegalState
    | some tid =>
        declassifyStoreOnCore ctx declPolicy c (ctx.threadDomainOf tid) dstDomain targetId obj
          log st

/-- WS-SM SM8.C.3: an idle core cannot declassify — there is no subject to
attribute the downgrade to, so the operation fails closed and the state is
untouched.  (`.illegalState` is the error the syscall entry already uses for
"this core is running nothing"; see
`Platform.FFI.syscallDispatchFromAbi_illegalState_when_no_current`.) -/
theorem declassifyStoreFromCore_no_subject
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log : DeclassificationAuditLog) (st : SystemState)
    (hIdle : st.scheduler.currentOnCore c = none) :
    declassifyStoreFromCore ctx declPolicy c dstDomain targetId obj log st =
      .error .illegalState := by
  simp [declassifyStoreFromCore, hIdle]

/-- WS-SM SM8.C.3: with a subject present the wrapper *is* the internal step at
the subject's own domain — the bridge every §2 theorem travels along. -/
theorem declassifyStoreFromCore_eq_onCore
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log : DeclassificationAuditLog) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid) :
    declassifyStoreFromCore ctx declPolicy c dstDomain targetId obj log st =
      declassifyStoreOnCore ctx declPolicy c (ctx.threadDomainOf tid) dstDomain targetId obj
        log st := by
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

/-- WS-SM SM8.C.3 (**the headline**): every event `declassifyStoreFromCore`
records is attributable — **in the post-state**, which is the state an auditor
inspects.

Unconditional: no hypothesis relates the caller's arguments to the state,
because the wrapper does not accept a source domain to relate.  The post-state
form (rather than the pre-state one, which is definitional) is what carries: a
declassification writes the object store, so the scheduler slot the attribution
reads is the same slot afterwards. -/
theorem declassifyStoreFromCore_event_attributable
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log log' : DeclassificationAuditLog) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hStep : declassifyStoreFromCore ctx declPolicy c dstDomain targetId obj log st =
      .ok (log', st')) :
    declassificationEventAttributable ctx st'
      (declassificationEventOnCore c (ctx.threadDomainOf tid) dstDomain targetId log) := by
  rw [declassifyStoreFromCore_eq_onCore ctx declPolicy c dstDomain targetId obj log st tid hCur]
    at hStep
  obtain ⟨hGate, _⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c (ctx.threadDomainOf tid)
    dstDomain targetId obj log log' st st' hStep
  have hSched := declassifyStore_scheduler_eq ctx declPolicy (ctx.threadDomainOf tid) dstDomain
    targetId obj st st' hGate
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
declassification path must enter through `declassifyStoreFromCore`; without it,
`declassifyStoreFromCore_event_attributable` would be a theorem about a wrapper
that adds nothing. -/
theorem declassifyStoreOnCore_admits_unattributable :
    ∃ (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy) (c : CoreId)
      (srcDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId) (obj : KernelObject)
      (log log' : DeclassificationAuditLog) (st st' : SystemState),
      declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
        .ok (log', st') ∧
      ¬ declassificationEventAttributable ctx st'
          (declassificationEventOnCore c srcDomain dstDomain targetId log) := by
  refine ⟨{ policy := { canFlow := fun _ _ => false }
            objectDomainOf := fun _ => ⟨0⟩, threadDomainOf := fun _ => ⟨0⟩
            endpointDomainOf := fun _ => ⟨0⟩, serviceDomainOf := fun _ => ⟨0⟩ },
          { canDeclassify := fun _ _ => true }, bootCoreId, ⟨1⟩, ⟨0⟩, ⟨7⟩,
          .notification { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
                          pendingBadge := none, boundTCB := none },
          [], _, (default : SystemState), _, rfl, ?_⟩
  intro hAttr
  -- The post-state's scheduler slot reduces definitionally to the pre-state's
  -- (a declassification is an object-store write), and the boot state runs
  -- nothing on any core — so the attribution reads `none`.
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
theorem auditLogOnCore_timestamp_identifies_event (log : DeclassificationAuditLog)
    (c : CoreId) (hWF : declassificationAuditLogWellFormed log = true)
    {e₁ e₂ : DeclassificationEvent}
    (h₁ : e₁ ∈ auditLogOnCore log c) (h₂ : e₂ ∈ auditLogOnCore log c)
    (hTs : e₁.timestamp = e₂.timestamp) : e₁ = e₂ :=
  declassificationAuditLog_timestamp_identifies_event log hWF
    ((mem_auditLogOnCore_iff log c e₁).mp h₁).1
    ((mem_auditLogOnCore_iff log c e₂).mp h₂).1 hTs

/-- WS-SM SM8.C.4: the audited operation files its event under the core it ran
on — the per-core view is a view of what that core actually did. -/
theorem declassifyStoreOnCore_recorded_in_own_view
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log log' : DeclassificationAuditLog) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
      .ok (log', st')) :
    declassificationEventOnCore c srcDomain dstDomain targetId log ∈ auditLogOnCore log' c := by
  obtain ⟨_, hLog⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain dstDomain
    targetId obj log log' st st' hStep
  refine (mem_auditLogOnCore_iff log' c _).mpr ⟨?_, rfl⟩
  rw [hLog]
  exact recordDeclassification_contains_new log _

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
    (log log₁ log₂ : DeclassificationAuditLog) (st st₁ st₂ : SystemState)
    (hne : c₁ ≠ c₂)
    (hStep₁ : declassifyStoreOnCore ctx declPolicy c₁ a b target₁ obj₁ log st = .ok (log₁, st₁))
    (hStep₂ : declassifyStoreOnCore ctx declPolicy c₂ b d target₂ obj₂ log₁ st₁ =
      .ok (log₂, st₂)) :
    ∃ e₁ e₂ : DeclassificationEvent,
      log₂ = log ++ [e₁, e₂] ∧
      declassificationChainLinked [e₁, e₂] = true ∧
      chainRecordedIn log₂ [e₁, e₂] = true ∧
      chainIsCrossCore [e₁, e₂] = true ∧
      e₁.originatingCore = c₁ ∧ e₂.originatingCore = c₂ ∧
      chainSourceDomain [e₁, e₂] = some a ∧ chainTargetDomain [e₁, e₂] = some d := by
  obtain ⟨_, hLog₁⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c₁ a b target₁ obj₁
    log log₁ st st₁ hStep₁
  obtain ⟨_, hLog₂⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c₂ b d target₂ obj₂
    log₁ log₂ st₁ st₂ hStep₂
  refine ⟨declassificationEventOnCore c₁ a b target₁ log,
          declassificationEventOnCore c₂ b d target₂ log₁, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · rw [hLog₂, hLog₁]; simp [recordDeclassification]
  · -- the hops compose (`b` is both), and the second timestamp is the first plus one
    have hLen : log₁.length = log.length + 1 := by
      rw [hLog₁]; exact recordDeclassification_length log _
    simp [declassificationChainLinked, declassificationEventOnCore, hLen]
  · refine (chainRecordedIn_iff log₂ _).mpr ?_
    intro e hMem
    rw [hLog₂, hLog₁]
    rcases List.mem_cons.mp hMem with rfl | hMem'
    · exact List.mem_append_left _ (recordDeclassification_contains_new log _)
    · rcases List.mem_cons.mp hMem' with rfl | hEmpty
      · rw [← hLog₁]; exact recordDeclassification_contains_new log₁ _
      · exact absurd hEmpty List.not_mem_nil
  · refine (chainIsCrossCore_iff _).mpr ?_
    exact ⟨declassificationEventOnCore c₁ a b target₁ log, by simp,
           declassificationEventOnCore c₂ b d target₂ log₁, by simp, hne⟩

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
  have hDomain := embedLegacyLabel_preserves_flow srcLabel dstLabel hFlow
  simp [DeclassificationPolicy.isDeclassificationAuthorized, liftLegacyContext, hDomain]

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
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (log log₁ log₂ : DeclassificationAuditLog) (st st₁ st₂ : SystemState)
    (h₁ : declassifyStoreOnCore ctx declPolicy c₁ srcDomain dstDomain targetId obj log st =
      .ok (log₁, st₁))
    (h₂ : declassifyStoreOnCore ctx declPolicy c₂ srcDomain dstDomain targetId obj log st =
      .ok (log₂, st₂)) :
    st₁ = st₂ ∧
      ∃ e₁ e₂ : DeclassificationEvent,
        log₁ = log ++ [e₁] ∧ log₂ = log ++ [e₂] ∧
        e₁.originatingCore = c₁ ∧ e₂.originatingCore = c₂ ∧
        { e₁ with originatingCore := c₂ } = e₂ := by
  obtain ⟨hGate₁, hLog₁⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c₁ srcDomain dstDomain
    targetId obj log log₁ st st₁ h₁
  obtain ⟨hGate₂, hLog₂⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c₂ srcDomain dstDomain
    targetId obj log log₂ st st₂ h₂
  rw [hGate₁] at hGate₂
  exact ⟨congrArg Prod.snd (Except.ok.inj hGate₂), _, _, hLog₁, hLog₂, rfl, rfl, rfl⟩

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
    (log log' : DeclassificationAuditLog) (st st' : SystemState)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
      .ok (log', st')) :
    declassificationBasisKernelVerified ctx.policy declPolicy
      (declassificationEventOnCore c srcDomain dstDomain targetId log) = true := by
  obtain ⟨hNormal, hDecl⟩ := declassifyStoreOnCore_authorized ctx declPolicy c srcDomain
    dstDomain targetId obj log log' st st' hStep
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
    (log log' : DeclassificationAuditLog) (st st' : SystemState)
    (hVerified : auditLogBasesVerified ctx.policy declPolicy log = true)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
      .ok (log', st')) :
    auditLogBasesVerified ctx.policy declPolicy log' = true := by
  obtain ⟨_, hLog⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain dstDomain
    targetId obj log log' st st' hStep
  have hNew := declassifyStoreOnCore_event_basis_verified ctx declPolicy c srcDomain dstDomain
    targetId obj log log' st st' hStep
  rw [hLog]
  simp only [auditLogBasesVerified, recordDeclassification, List.all_append, Bool.and_eq_true,
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
    (log log' : DeclassificationAuditLog) (st st' : SystemState)
    (hIssued : auditLogKernelIssued log = true)
    (hStep : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj log st =
      .ok (log', st')) :
    auditLogKernelIssued log' = true := by
  obtain ⟨_, hLog⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain dstDomain
    targetId obj log log' st st' hStep
  rw [hLog]
  simp only [auditLogKernelIssued, recordDeclassification, List.all_append, Bool.and_eq_true,
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
    (log log' : DeclassificationAuditLog) (st st' : SystemState) (c' : CoreId)
    (hTargetHigh : objectObservable ctx observer targetId = false)
    (hObjInv : st.objects.invExt)
    (hStep : declassifyStoreOnCore gctx declPolicy c srcDomain dstDomain targetId obj log st =
      .ok (log', st')) :
    projectStateOnCore ctx observer st' c' = projectStateOnCore ctx observer st c' := by
  obtain ⟨hGate, _⟩ := declassifyStoreOnCore_ok_inv gctx declPolicy c srcDomain dstDomain
    targetId obj log log' st st' hStep
  obtain ⟨hDenied, hAuth⟩ := enforcementSoundness_declassifyStore gctx declPolicy srcDomain
    dstDomain targetId obj st st' hGate
  rw [declassifyStore_eq_storeObject_when_authorized gctx declPolicy srcDomain dstDomain
    targetId obj st hDenied hAuth] at hGate
  exact storeObject_preserves_projectionOnCore ctx observer st st' targetId obj c'
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
    (log₁ log₂ log₁' log₂' : DeclassificationAuditLog)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent_smp ctx observer s₁ s₂)
    (hTargetHigh : objectObservable ctx observer targetId = false)
    (hObjInv₁ : s₁.objects.invExt) (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : declassifyStoreOnCore gctx declPolicy c₁ srcDomain dstDomain targetId obj₁ log₁ s₁ =
      .ok (log₁', s₁'))
    (hStep₂ : declassifyStoreOnCore gctx declPolicy c₂ srcDomain dstDomain targetId obj₂ log₂ s₂ =
      .ok (log₂', s₂')) :
    lowEquivalent_smp ctx observer s₁' s₂' := by
  intro c
  show projectStateOnCore ctx observer s₁' c = projectStateOnCore ctx observer s₂' c
  rw [declassifyStoreOnCore_preserves_projectionOnCore ctx observer gctx declPolicy c₁ srcDomain
        dstDomain targetId obj₁ log₁ log₁' s₁ s₁' c hTargetHigh hObjInv₁ hStep₁,
      declassifyStoreOnCore_preserves_projectionOnCore ctx observer gctx declPolicy c₂ srcDomain
        dstDomain targetId obj₂ log₂ log₂' s₂ s₂' c hTargetHigh hObjInv₂ hStep₂]
  exact hLow c

/-- WS-SM SM8.C (**auditing opens no channel**): the state a declassification
commits does not depend on the audit log it was handed.

The audit trail is threaded through the operation rather than mounted in
`SystemState`, so it is outside every observer's view by construction — there is
no `ObservableState` component for it and no projection to reason about.  What
follows is the checked form of that: two runs differing only in their audit
history commit the same state, so nothing an observer sees can depend on what
was audited before.  If a future cut mounts the log in `SystemState` (to survive
a reboot, say), this is the theorem that stops holding, and the projection will
owe a decision about who may read the trail. -/
theorem declassifyStoreOnCore_state_log_independent
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (logA logB logA' logB' : DeclassificationAuditLog) (st stA stB : SystemState)
    (hStepA : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj logA st =
      .ok (logA', stA))
    (hStepB : declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj logB st =
      .ok (logB', stB)) :
    stA = stB := by
  obtain ⟨hGateA, _⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain dstDomain
    targetId obj logA logA' st stA hStepA
  obtain ⟨hGateB, _⟩ := declassifyStoreOnCore_ok_inv ctx declPolicy c srcDomain dstDomain
    targetId obj logB logB' st stB hStepB
  rw [hGateA] at hGateB
  exact congrArg Prod.snd (Except.ok.inj hGateB)

-- ============================================================================
-- §9  SM8.C.6 — the rules as data, each carrying its own proof
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
  deriving Repr, DecidableEq

/-- WS-SM SM8.C.6: the enumeration.  `mem_all` and `all_nodup` make it complete
and repeat-free, so the count theorems mean what they say. -/
def DeclassificationRuleId.all : List DeclassificationRuleId :=
  [ .compositionSoundness, .hopAuthorizationDoesNotCompose, .endpointOverrideIsNotABasis
  , .coreDimensionIsAuditOnly, .perCorePartition, .crossCoreChainNeedsGlobalLog
  , .attributionFromRunningSubject, .auditIsNotObservable ]

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
        (log log' : DeclassificationAuditLog) (st st' : SystemState) (tid : SeLe4n.ThreadId),
        st.scheduler.currentOnCore c = some tid →
        declassifyStoreFromCore ctx declPolicy c dstDomain targetId obj log st = .ok (log', st') →
        declassificationEventAttributable ctx st'
          (declassificationEventOnCore c (ctx.threadDomainOf tid) dstDomain targetId log)
  | .auditIsNotObservable =>
      ∀ (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy) (c : CoreId)
        (srcDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId) (obj : KernelObject)
        (logA logB logA' logB' : DeclassificationAuditLog) (st stA stB : SystemState),
        declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj logA st =
          .ok (logA', stA) →
        declassifyStoreOnCore ctx declPolicy c srcDomain dstDomain targetId obj logB st =
          .ok (logB', stB) →
        stA = stB

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
      fun ctx declPolicy c dstDomain targetId obj log log' st st' tid hCur hStep =>
        declassifyStoreFromCore_event_attributable ctx declPolicy c dstDomain targetId obj
          log log' st st' tid hCur hStep
  | .auditIsNotObservable =>
      fun ctx declPolicy c srcDomain dstDomain targetId obj logA logB logA' logB' st stA stB
        hStepA hStepB =>
        declassifyStoreOnCore_state_log_independent ctx declPolicy c srcDomain dstDomain targetId
          obj logA logB logA' logB' st stA stB hStepA hStepB

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
  | .auditIsNotObservable => niName! declassifyStoreOnCore_state_log_independent

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
      "the committed state does not depend on the audit trail"

theorem declassificationRules_count : DeclassificationRuleId.all.length = 8 := by rfl

/-- WS-SM SM8.C.6: every rule names a theorem — no rule is discharged with an
empty citation. -/
theorem declassificationRuleEvidence_nonempty :
    ∀ id : DeclassificationRuleId, (declassificationRuleEvidenceName id).length > 0 := by
  intro id; cases id <;> decide

/-- WS-SM SM8.C.6: no two rules share a witness — each is carried by its own
theorem, so no rule is a restatement of another. -/
theorem declassificationRuleEvidence_distinct :
    (DeclassificationRuleId.all.map declassificationRuleEvidenceName).length = 8 ∧
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

end SeLe4n.Kernel
