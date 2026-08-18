/-
Copyright (c) 2025 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license.

WS-SM SM8.C.9: the live declassification transition.

The `.declassify` syscall's kernel-side operation, and the smallest module that
can hold it.  It is deliberately **not** in `InformationFlow/DeclassificationPerCore.lean`:
that module is staged and sits on top of the SM8.A/SM8.B non-interference layer,
which the live syscall path must not pull into its import closure.  What lives
here is the transition and the properties a dispatch arm owes; the per-core audit
theory (views, chains, laundering, the rules as data) stays staged above it.

## What the syscall does, and what it does not

`declassifyStore` (`Enforcement/Soundness.lean`) models a declassification as a
gated **store**: it verifies the downgrade is authorized and then writes an
object at the target.  Its own docstring calls that store a *simulation* of the
information transfer, and simulating a transfer is not something a syscall may
do — the object would have to come from the caller, so a `.declassify` built
that way would let userspace install a chosen `KernelObject` at a chosen id and
break every object-store invariant at once.

So the live transition runs the **decision** the gate runs
(`declassificationDecision`, shared with `declassifyStore` rather than restated
— `declassifyStore_eq_decision_bind`) and records the result.  Its state effect
is exactly one appended audit entry: fifteen of the sixteen
`proofLayerInvariantBundle` conjuncts are carried by the frame, and the
sixteenth by the capacity guard.

Read positively, that is the primitive an MLS trusted downgrader wants: the
kernel is the arbiter of which downgrades its policy permits, and the durable
attributed trail is the evidence.  Read negatively, it means `.declassify`
moves no bytes — a data-carrying declassification (a badge into a notification,
say) would ride the SM6.B signal path and its whole invariant surface, and is
scoped to SM8.D/SM8.E rather than folded in here.
-/
import SeLe4n.Kernel.InformationFlow.Enforcement.Soundness
import SeLe4n.Kernel.Architecture.Invariant

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  The recorded event
-- ============================================================================

/-- WS-SM SM8.C.1: the event an authorized downgrade on core `c` records.

Three of the six fields are not free choices: the basis is `.policyRule`
(the only gate the kernel runs), the timestamp is the event's **global**
position, and the core is the core the operation ran on.  Only the two domains
and the target come from the caller — and the attributed entry points below
remove both domains from that list too.

**WS-SM SM9.A.1a — the timestamp is `epoch + log.length`, not `log.length`.**
Up to SM9.A the trail only ever grew, so a position in it *was* a global
identity.  Drain removes a prefix, and with the pre-epoch producer the very
next append reuses a timestamp that is still in the trail: drain one entry from
a three-entry trail and the new entry lands at `2` alongside the survivor that
already carries `2` (`preEpochTimestamp_reused_after_drain`).  That falsifies
`declassificationAuditLog_timestamp_identifies_event` in substance — not merely
in its hypothesis — and breaks `declassificationChainLinked`'s
strictly-increasing conjunct with it.  Offsetting by the epoch, which counts
exactly the entries drained so far, makes a timestamp name an event for the
lifetime of the system: it is never reused and never decreases. -/
def declassificationEventOnCore (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (epoch : Nat)
    (log : DeclassificationAuditLog) : DeclassificationEvent :=
  { srcDomain := srcDomain
    dstDomain := dstDomain
    targetObject := targetId
    authorizationBasis := .policyRule
    timestamp := epoch + log.length
    originatingCore := c }

/-- WS-SM SM8.C.1: the event a given pre-state records, named once so the
theorems below do not each recompute it. -/
abbrev declassifyStoreEvent (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st : SystemState) : DeclassificationEvent :=
  declassificationEventOnCore c srcDomain dstDomain targetId
    st.declassificationAuditEpoch st.declassificationAuditLog

/-- WS-SM SM8.C.1: the trail a successful audited step leaves — the pre-state's
trail with this step's event appended. -/
abbrev declassifyStoreTrail (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st : SystemState) : DeclassificationAuditLog :=
  recordDeclassification st.declassificationAuditLog
    (declassifyStoreEvent c srcDomain dstDomain targetId st)

/-- WS-SM SM8.C.1 (**the field the phase exists for**): the recorded core is the
core the operation ran on.

Load-bearing rather than definitional bookkeeping: the pre-SM8.C record had no
core at all, and the tempting way to add one — default it to `bootCoreId` — would
make this theorem false for every secondary core while still compiling
everywhere. -/
theorem declassificationEventOnCore_originatingCore
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (epoch : Nat) (log : DeclassificationAuditLog) :
    (declassificationEventOnCore c srcDomain dstDomain targetId epoch
      log).originatingCore = c := rfl

/-- WS-SM SM8.C.5: the kernel records its own basis, never an integrator
override — so `kernelVerifiable` is `true` on everything the kernel writes. -/
theorem declassificationEventOnCore_basis_is_policyRule
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (epoch : Nat) (log : DeclassificationAuditLog) :
    (declassificationEventOnCore c srcDomain dstDomain targetId epoch
      log).authorizationBasis = .policyRule := rfl

/-- WS-SM SM8.C / SM9.A.1a: the recorded timestamp is the event's **global**
position — the number of entries drained so far plus its index in the current
trail. -/
theorem declassificationEventOnCore_timestamp
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (epoch : Nat) (log : DeclassificationAuditLog) :
    (declassificationEventOnCore c srcDomain dstDomain targetId epoch log).timestamp =
      epoch + log.length := rfl

-- ============================================================================
-- §2  Attribution: the subject the executing core is running
-- ============================================================================

/-- WS-SM SM8.C.3: the domain of the subject core `c` is running, if any.

The per-core read `currentOnCore c` is deliberate: under SMP "the current
thread" is not a single value, and a boot-pinned read would attribute every
secondary core's downgrade to whatever the boot core happened to be running. -/
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

-- ============================================================================
-- §3  The live transition
-- ============================================================================

/-- WS-SM SM8.C.9: **the live declassification.**  The authorization decision
`declassifyStore` runs, on core `c`, recorded in the mounted audit trail.

**The decision is taken first, then capacity, and refusal is total.**

Both orderings give the same successes, and only one of them is safe.  Checking
capacity first would tell a caller whose downgrade the *policy* refuses that the
trail is full — and trail occupancy is a function of how many authorized
downgrades other subjects have performed, so that is a channel from every
declassifying subject to every subject that can call `.declassify` at all.
Deciding first confines the observation to a caller whose downgrade *is*
authorized, which learns nothing it could not learn by the downgrade succeeding.

Capacity is still checked **before the commit**, so there is no arm on which the
downgrade is authorized and the record is not written — which is what
`authorizeDeclassificationOnCore_never_unaudited` rests on.

The only state this writes is the trail
(`authorizeDeclassificationOnCore_frame`), which is what makes the invariant
obligations a one-conjunct affair. -/
def authorizeDeclassificationOnCore
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) : Kernel Unit :=
  fun st =>
    match declassificationDecision ctx declPolicy srcDomain dstDomain with
    | .error err => .error err
    | .ok () =>
        match recordDeclassificationChecked st.declassificationAuditLog
            (declassifyStoreEvent c srcDomain dstDomain targetId st) with
        | none => .error .auditLogCapacityExceeded
        | some log' => .ok ((), { st with declassificationAuditLog := log' })

/-- WS-SM SM8.C.9 (**the frame**): the only field a successful live
declassification writes is the audit trail.

Everything the module's invariant obligations rest on: the object store, the
scheduler, the machine, every SM7 memory-model field and every lock are
untouched, so `.declassify` is not a write primitive by any route. -/
theorem authorizeDeclassificationOnCore_frame
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hStep : authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
      .ok ((), st')) :
    st' = { st with
      declassificationAuditLog := declassifyStoreTrail c srcDomain dstDomain targetId st } ∧
    st.declassificationAuditLog.length < maxDeclassificationAuditEntries ∧
    declassificationDecision ctx declPolicy srcDomain dstDomain = .ok () := by
  unfold authorizeDeclassificationOnCore at hStep
  obtain ⟨dec, hDec⟩ :
      ∃ d, declassificationDecision ctx declPolicy srcDomain dstDomain = d := ⟨_, rfl⟩
  rw [hDec] at hStep
  cases dec with
  | error err => simp at hStep
  | ok u =>
    cases u
    obtain ⟨rec, hRec⟩ : ∃ r, recordDeclassificationChecked st.declassificationAuditLog
        (declassifyStoreEvent c srcDomain dstDomain targetId st) = r := ⟨_, rfl⟩
    rw [hRec] at hStep
    cases rec with
    | none => simp at hStep
    | some log' =>
      have hRoom : st.declassificationAuditLog.length < maxDeclassificationAuditEntries :=
        (recordDeclassificationChecked_isSome_iff _ _).mp (by rw [hRec]; rfl)
      have hLog' : log' = declassifyStoreTrail c srcDomain dstDomain targetId st := by
        rw [recordDeclassificationChecked_eq_record _ _ hRoom] at hRec
        exact (Option.some.inj hRec).symm
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      exact ⟨by rw [← hStep.2, hLog'], hRoom, hDec⟩

/-- WS-SM SM8.C.9: the live declassification succeeds exactly when there is room
in the trail and the downgrade is authorized. -/
theorem authorizeDeclassificationOnCore_ok_iff
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st : SystemState) :
    (∃ st', authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
      .ok ((), st')) ↔
      (st.declassificationAuditLog.length < maxDeclassificationAuditEntries ∧
        declassificationDecision ctx declPolicy srcDomain dstDomain = .ok ()) := by
  constructor
  · rintro ⟨st', hStep⟩
    obtain ⟨_, hRoom, hDec⟩ := authorizeDeclassificationOnCore_frame ctx declPolicy c srcDomain
      dstDomain targetId st st' hStep
    exact ⟨hRoom, hDec⟩
  · rintro ⟨hRoom, hDec⟩
    refine ⟨{ st with
      declassificationAuditLog := declassifyStoreTrail c srcDomain dstDomain targetId st }, ?_⟩
    unfold authorizeDeclassificationOnCore
    rw [hDec, recordDeclassificationChecked_eq_record _ _ hRoom]

/-- WS-SM SM8.C.8 (**fail-closed at capacity**): a full trail refuses an
*authorized* downgrade outright, with the discriminant that says why.

The load-bearing half of the capacity design.  The alternative — drop an entry
and let the downgrade through — produces a state in which the kernel authorized
a cross-domain flow and no record of it exists, which is the failure the whole
phase is built to exclude.

The `hAuthorized` premise is the confinement: a caller whose downgrade the
policy refuses gets `.declassificationDenied` and learns nothing about the
trail's occupancy (`authorizeDeclassificationOnCore_denied_before_capacity`). -/
theorem authorizeDeclassificationOnCore_audit_log_full
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st : SystemState)
    (hAuthorized : declassificationDecision ctx declPolicy srcDomain dstDomain = .ok ())
    (hFull : maxDeclassificationAuditEntries ≤ st.declassificationAuditLog.length) :
    authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
      .error .auditLogCapacityExceeded := by
  unfold authorizeDeclassificationOnCore
  rw [hAuthorized, recordDeclassificationChecked_eq_none _ _ hFull]

/-- WS-SM SM8.C.8 / SM8.C.9 (**the ordering, as a theorem**): a caller whose
downgrade the policy refuses learns **nothing about the trail's occupancy** —
the error it gets is the policy's, on a full trail exactly as on an empty one.

The reason the decision is taken before the capacity check.  Trail occupancy is
a function of how many authorized downgrades *other* subjects performed, so
surfacing it to every caller — including one the policy refuses — would be a
channel from every declassifying subject to every subject that can call
`.declassify` at all.  Stated over an arbitrary state, so the two states in the
statement may differ in trail length by any amount. -/
theorem authorizeDeclassificationOnCore_denied_before_capacity
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st st' : SystemState) (err : KernelError)
    (hDenied : declassificationDecision ctx declPolicy srcDomain dstDomain = .error err) :
    authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
      authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st' ∧
    authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
      .error err := by
  constructor <;> · unfold authorizeDeclassificationOnCore; rw [hDenied]

/-- WS-SM SM8.C.5 (**audit soundness**): a recorded event's basis is not a
claim, it is a check that ran.  Both halves of `isDeclassificationAuthorized`
held at the moment the event was written: the base policy denied the flow (so
this genuinely was a downgrade) and the declassification policy permitted it. -/
theorem authorizeDeclassificationOnCore_authorized
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hStep : authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
      .ok ((), st')) :
    ctx.policy.canFlow srcDomain dstDomain = false ∧
      declPolicy.canDeclassify srcDomain dstDomain = true := by
  obtain ⟨_, _, hDec⟩ := authorizeDeclassificationOnCore_frame ctx declPolicy c srcDomain
    dstDomain targetId st st' hStep
  exact (declassificationDecision_ok_iff ctx declPolicy srcDomain dstDomain).mp hDec

/-- WS-SM SM8.C.9: **exactly one event per authorized downgrade**, appended to
the trail the pre-state carried. -/
theorem authorizeDeclassificationOnCore_records_one
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hStep : authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
      .ok ((), st')) :
    st'.declassificationAuditLog =
      st.declassificationAuditLog ++ [declassifyStoreEvent c srcDomain dstDomain targetId st] ∧
      st'.declassificationAuditLog.length = st.declassificationAuditLog.length + 1 := by
  obtain ⟨hSt', _, _⟩ := authorizeDeclassificationOnCore_frame ctx declPolicy c srcDomain
    dstDomain targetId st st' hStep
  subst hSt'
  exact ⟨rfl, recordDeclassification_length _ _⟩

/-- WS-SM SM8.C.9 (**the headline**): *an authorized downgrade is either recorded
or does not happen.*

Every success arm appends exactly one event naming this core, this subject
domain, this destination and this target; every arm that cannot append — a full
trail — is an error arm.  The property the mount (SM8.C.8) and the fail-closed
capacity bound exist for. -/
theorem authorizeDeclassificationOnCore_never_unaudited
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hStep : authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
      .ok ((), st')) :
    ∃ e ∈ st'.declassificationAuditLog,
      e.originatingCore = c ∧ e.srcDomain = srcDomain ∧ e.dstDomain = dstDomain ∧
      e.targetObject = targetId ∧ e.authorizationBasis = .policyRule := by
  obtain ⟨hLog, _⟩ := authorizeDeclassificationOnCore_records_one ctx declPolicy c srcDomain
    dstDomain targetId st st' hStep
  refine ⟨declassifyStoreEvent c srcDomain dstDomain targetId st, ?_, rfl, rfl, rfl, rfl, rfl⟩
  rw [hLog]
  exact List.mem_append_right _ (by simp)

/-- WS-SM SM8.C.8: the live declassification carries the 16th
`proofLayerInvariantBundle` conjunct. -/
theorem authorizeDeclassificationOnCore_preserves_auditLogBounded
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hStep : authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
      .ok ((), st')) :
    auditLogBounded st'.declassificationAuditLog := by
  obtain ⟨_, hLen⟩ := authorizeDeclassificationOnCore_records_one ctx declPolicy c srcDomain
    dstDomain targetId st st' hStep
  obtain ⟨_, hRoom, _⟩ := authorizeDeclassificationOnCore_frame ctx declPolicy c srcDomain
    dstDomain targetId st st' hStep
  unfold auditLogBounded
  omega

/-- WS-SM SM8.C.9: **the whole invariant bundle**, carried across the live
declassification.

Fifteen conjuncts ride `proofLayerInvariantBundle_setDeclassificationAuditLog`
(the transition writes one field, and none of the fifteen reads it); the
sixteenth is the capacity bound above.  This is the obligation a dispatch arm
owes, discharged once. -/
theorem authorizeDeclassificationOnCore_preserves_proofLayerInvariantBundle
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hInv : Architecture.proofLayerInvariantBundle st)
    (hStep : authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
      .ok ((), st')) :
    Architecture.proofLayerInvariantBundle st' := by
  obtain ⟨hSt', _, _⟩ := authorizeDeclassificationOnCore_frame ctx declPolicy c srcDomain
    dstDomain targetId st st' hStep
  have hBounded := authorizeDeclassificationOnCore_preserves_auditLogBounded ctx declPolicy c
    srcDomain dstDomain targetId st st' hStep
  rw [hSt'] at hBounded ⊢
  exact Architecture.proofLayerInvariantBundle_setDeclassificationAuditLog st _ hInv hBounded

-- ============================================================================
-- §4  The attributed live entry point
-- ============================================================================

/-- WS-SM SM8.C.9: **the entry point the `.declassify` syscall calls.**

Neither domain comes from the caller.  The *source* is the domain of the thread
core `c` is running (§2); the *destination* is the domain the labeling context
assigns the target object.  A caller that could name either would be able to
record a downgrade between two domains it has nothing to do with — an audit
trail that says whatever the caller wants is not an audit trail.  Resolving both
kernel-side also collapses the ABI to a single operand: the capability naming
the target.

Fails closed three ways: an idle core has no subject (`.illegalState`), an
absent target has no domain to resolve (`.objectNotFound`), and a full trail
refuses the downgrade (`.auditLogCapacityExceeded`, from §3). -/
def declassifyObjectFromCore
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) : Kernel Unit :=
  fun st =>
    match st.scheduler.currentOnCore c with
    | none => .error .illegalState
    | some tid =>
        match st.getObjectType? targetId with
        | none => .error .objectNotFound
        | some _ =>
            authorizeDeclassificationOnCore ctx declPolicy c
              (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId) targetId st

/-- WS-SM SM8.C.3: an idle core cannot declassify — there is no subject to
attribute the downgrade to, so the operation fails closed and the state is
untouched.  (`.illegalState` is the error the syscall entry already uses for
"this core is running nothing"; see
`Platform.FFI.syscallDispatchFromAbi_illegalState_when_no_current`.) -/
theorem declassifyObjectFromCore_no_subject
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st : SystemState)
    (hIdle : st.scheduler.currentOnCore c = none) :
    declassifyObjectFromCore ctx declPolicy c targetId st = .error .illegalState := by
  simp [declassifyObjectFromCore, hIdle]

/-- WS-SM SM8.C.9: an absent target cannot be declassified — there is no object
whose domain the destination could be resolved from.

Fail-closed rather than "resolve the context's function at the id anyway": the
labeling context is total, so it *would* answer, and the trail would record a
downgrade into a domain no object is in. -/
theorem declassifyObjectFromCore_absent_target
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hAbsent : st.getObjectType? targetId = none) :
    declassifyObjectFromCore ctx declPolicy c targetId st = .error .objectNotFound := by
  simp [declassifyObjectFromCore, hCur, hAbsent]

/-- WS-SM SM8.C.9: with a subject and a target present the entry point *is* the
transition at the two kernel-resolved domains — the bridge every §3 theorem
travels along. -/
theorem declassifyObjectFromCore_eq_onCore
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (ty : SeLe4n.Model.KernelObjectType)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hPresent : st.getObjectType? targetId = some ty) :
    declassifyObjectFromCore ctx declPolicy c targetId st =
      authorizeDeclassificationOnCore ctx declPolicy c
        (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId) targetId st := by
  simp [declassifyObjectFromCore, hCur, hPresent]

/-- WS-SM SM8.C.9: the entry point's frame — like the transition it wraps, the
only field it writes is the audit trail. -/
theorem declassifyObjectFromCore_frame
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    st' =
      { st with
        declassificationAuditLog :=
          declassifyStoreTrail c (ctx.threadDomainOf tid)
            (ctx.objectDomainOf targetId) targetId st } := by
  unfold declassifyObjectFromCore at hStep
  rw [hCur] at hStep
  obtain ⟨ty, hTy⟩ : ∃ t, st.getObjectType? targetId = t := ⟨_, rfl⟩
  rw [hTy] at hStep
  cases ty with
  | none => simp at hStep
  | some _ =>
    exact (authorizeDeclassificationOnCore_frame ctx declPolicy c (ctx.threadDomainOf tid)
      (ctx.objectDomainOf targetId) targetId st st' hStep).1

/-- WS-SM SM8.C.9: a successful live declassification implies the executing core
was running a subject, and the target was present.

The inverse of the two fail-closed arms, and what lets every downstream theorem
drop the `hCur` / `hPresent` hypotheses: success already carries them. -/
theorem declassifyObjectFromCore_ok_resolved
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    (∃ tid, st.scheduler.currentOnCore c = some tid) ∧
      (∃ ty, st.getObjectType? targetId = some ty) := by
  unfold declassifyObjectFromCore at hStep
  obtain ⟨cur, hCur⟩ : ∃ x, st.scheduler.currentOnCore c = x := ⟨_, rfl⟩
  rw [hCur] at hStep
  cases cur with
  | none => simp at hStep
  | some tid =>
    obtain ⟨ty, hTy⟩ : ∃ t, st.getObjectType? targetId = t := ⟨_, rfl⟩
    rw [hTy] at hStep
    cases ty with
    | none => simp at hStep
    | some t => exact ⟨⟨tid, hCur⟩, ⟨t, hTy⟩⟩

/-- WS-SM SM8.C.9: the frame, with no resolution hypothesis — success supplies
it.  The form the run-level theorems fold over. -/
theorem declassifyObjectFromCore_frame_of_ok
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    ∃ tid, st.scheduler.currentOnCore c = some tid ∧
      st' = { st with
        declassificationAuditLog :=
          declassifyStoreTrail c (ctx.threadDomainOf tid)
            (ctx.objectDomainOf targetId) targetId st } := by
  obtain ⟨⟨tid, hCur⟩, -⟩ := declassifyObjectFromCore_ok_resolved ctx declPolicy c targetId
    st st' hStep
  exact ⟨tid, hCur,
    declassifyObjectFromCore_frame ctx declPolicy c targetId st st' tid hCur hStep⟩

/-- WS-SM SM8.C.3 (**the headline**): every event the live entry point records is
attributable — **in the post-state**, which is the state an auditor inspects.

Unconditional in the caller's arguments, because the entry point does not accept
a source domain to relate.  The post-state form carries because the transition
writes only the trail, so the scheduler slot the attribution reads is the same
slot afterwards. -/
theorem declassifyObjectFromCore_event_attributable
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    declassificationEventAttributable ctx st'
      (declassifyStoreEvent c (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId)
        targetId st) := by
  have hSt' := declassifyObjectFromCore_frame ctx declPolicy c targetId st st' tid hCur hStep
  subst hSt'
  simp [declassificationEventAttributable, declassificationSubjectDomainOnCore,
    declassificationEventOnCore, hCur]

/-- WS-SM SM8.C.9 (**the caller cannot name the destination**): the recorded
destination domain is the one the labeling context assigns the *target object*.

The anti-forgery property that pays for resolving the destination kernel-side.
Together with `declassifyObjectFromCore_event_attributable` — which pins the
source to the running subject — it says both endpoints of every recorded
downgrade are facts about the state, not arguments. -/
theorem declassifyObjectFromCore_destination_is_target_domain
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    ∃ e ∈ st'.declassificationAuditLog,
      e.dstDomain = ctx.objectDomainOf e.targetObject ∧
      e.srcDomain = ctx.threadDomainOf tid ∧
      e.originatingCore = c := by
  have hSt' := declassifyObjectFromCore_frame ctx declPolicy c targetId st st' tid hCur hStep
  subst hSt'
  refine ⟨declassifyStoreEvent c (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId)
    targetId st, ?_, rfl, rfl, rfl⟩
  show _ ∈ declassifyStoreTrail c (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId)
    targetId st
  exact recordDeclassification_contains_new _ _

/-- WS-SM SM8.C.9: the live entry point carries the whole invariant bundle —
the obligation `API.dispatchCapabilityOnly`'s `.declassify` arm owes. -/
theorem declassifyObjectFromCore_preserves_proofLayerInvariantBundle
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hInv : Architecture.proofLayerInvariantBundle st)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    Architecture.proofLayerInvariantBundle st' := by
  unfold declassifyObjectFromCore at hStep
  obtain ⟨cur, hCur⟩ : ∃ x, st.scheduler.currentOnCore c = x := ⟨_, rfl⟩
  rw [hCur] at hStep
  cases cur with
  | none => simp at hStep
  | some tid =>
    obtain ⟨ty, hTy⟩ : ∃ t, st.getObjectType? targetId = t := ⟨_, rfl⟩
    rw [hTy] at hStep
    cases ty with
    | none => simp at hStep
    | some _ =>
      exact authorizeDeclassificationOnCore_preserves_proofLayerInvariantBundle ctx declPolicy c
        (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId) targetId st st' hInv hStep

/-- WS-SM SM8.C.9: **the headline, at the live entry point** — an authorized
downgrade performed by the syscall is either recorded or does not happen. -/
theorem declassifyObjectFromCore_never_unaudited
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    ∃ e ∈ st'.declassificationAuditLog,
      e.originatingCore = c ∧ e.srcDomain = ctx.threadDomainOf tid ∧
      e.dstDomain = ctx.objectDomainOf targetId ∧ e.targetObject = targetId ∧
      e.authorizationBasis = .policyRule := by
  have hSt' := declassifyObjectFromCore_frame ctx declPolicy c targetId st st' tid hCur hStep
  subst hSt'
  refine ⟨declassifyStoreEvent c (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId)
    targetId st, ?_, rfl, rfl, rfl, rfl, rfl⟩
  show _ ∈ declassifyStoreTrail c (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId)
    targetId st
  exact recordDeclassification_contains_new _ _

/-- WS-SM SM8.C.5: the live entry point's authorization soundness — both halves
of the gate held at the moment the event was written, at the two kernel-resolved
domains. -/
theorem declassifyObjectFromCore_authorized
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ty : SeLe4n.Model.KernelObjectType)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hPresent : st.getObjectType? targetId = some ty)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    ctx.policy.canFlow (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId) = false ∧
      declPolicy.canDeclassify (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId) = true := by
  rw [declassifyObjectFromCore_eq_onCore ctx declPolicy c targetId st tid ty hCur hPresent]
    at hStep
  exact authorizeDeclassificationOnCore_authorized ctx declPolicy c (ctx.threadDomainOf tid)
    (ctx.objectDomainOf targetId) targetId st st' hStep

/-- WS-SM SM8.C.8: the live entry point refuses at capacity, with the
discriminant that says why. -/
theorem declassifyObjectFromCore_audit_log_full
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (ty : SeLe4n.Model.KernelObjectType)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hPresent : st.getObjectType? targetId = some ty)
    (hAuthorized : declassificationDecision ctx declPolicy (ctx.threadDomainOf tid)
      (ctx.objectDomainOf targetId) = .ok ())
    (hFull : maxDeclassificationAuditEntries ≤ st.declassificationAuditLog.length) :
    declassifyObjectFromCore ctx declPolicy c targetId st =
      .error .auditLogCapacityExceeded := by
  rw [declassifyObjectFromCore_eq_onCore ctx declPolicy c targetId st tid ty hCur hPresent]
  exact authorizeDeclassificationOnCore_audit_log_full ctx declPolicy c (ctx.threadDomainOf tid)
    (ctx.objectDomainOf targetId) targetId st hAuthorized hFull

-- ============================================================================
-- §5  WS-SM SM9.A.1a — the trail's timestamp discipline, at the mounted epoch
-- ============================================================================

/-- WS-SM SM9.A.1a: **the mounted trail is well-formed at its epoch** — entry
`i` carries timestamp `epoch + i`.

The epoch-relative correction of SM8.C's `declassificationAuditLogWellFormed`,
which anchored at `0` and is therefore *false* of any trail a drain has
shortened.  Everything that predicate bought — a timestamp identifies an event,
a chain's timestamps strictly increase — is bought by this one for the lifetime
of the system rather than only until the first drain.

Boot is the 0-anchored instance (`default_declassificationTrailWellFormed`), and
the two writers preserve it: recording stamps `epoch + length` and leaves the
epoch alone; draining removes `d` entries and advances the epoch by exactly `d`
(`auditTimestampsFrom_append` / `auditTimestampsFrom_drop` are the two halves). -/
def declassificationTrailWellFormed (st : SystemState) : Bool :=
  auditTimestampsFrom st.declassificationAuditEpoch st.declassificationAuditLog

/-- WS-SM SM9.A.1a: decidable, like the predicate it generalises — an audit
consumer can check a concrete snapshot. -/
instance (st : SystemState) : Decidable (declassificationTrailWellFormed st = true) :=
  inferInstanceAs (Decidable (_ = true))

/-- WS-SM SM9.A.1a: at boot the epoch is `0` and the trail is empty, so the
epoch-relative predicate reduces to SM8.C's 0-anchored one. -/
@[simp] theorem default_declassificationTrailWellFormed :
    declassificationTrailWellFormed (default : SystemState) = true := rfl

/-- WS-SM SM9.A.1a: a never-drained trail's epoch-relative well-formedness *is*
SM8.C's 0-anchored predicate — so nothing proved before drain existed has to be
re-derived, it is this theorem's `epoch = 0` instance. -/
theorem declassificationTrailWellFormed_of_epoch_zero (st : SystemState)
    (hEpoch : st.declassificationAuditEpoch = 0) :
    declassificationTrailWellFormed st =
      declassificationAuditLogWellFormed st.declassificationAuditLog := by
  simp [declassificationTrailWellFormed, declassificationAuditLogWellFormed, hEpoch]

/-- WS-SM SM9.A.1a: **the live declassification preserves the trail's timestamp
discipline at the epoch.**

The producer's half.  It stamps `epoch + length` and writes no other field, so
`auditTimestampsFrom_append` discharges it directly — which is the point of
computing the timestamp from the state rather than accepting it as an argument. -/
theorem authorizeDeclassificationOnCore_preserves_trailWellFormed
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hWF : declassificationTrailWellFormed st = true)
    (hStep : authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
      .ok ((), st')) :
    declassificationTrailWellFormed st' = true := by
  obtain ⟨hSt', _, _⟩ := authorizeDeclassificationOnCore_frame ctx declPolicy c srcDomain
    dstDomain targetId st st' hStep
  subst hSt'
  exact recordDeclassification_preserves_timestampsFrom _ _ _ hWF rfl

/-- WS-SM SM9.A.1a: the live entry point's half — the obligation the
`.declassify` dispatch arm owes about the trail's ordering. -/
theorem declassifyObjectFromCore_preserves_trailWellFormed
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hWF : declassificationTrailWellFormed st = true)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    declassificationTrailWellFormed st' = true := by
  obtain ⟨tid, _, hSt'⟩ :=
    declassifyObjectFromCore_frame_of_ok ctx declPolicy c targetId st st' hStep
  subst hSt'
  exact recordDeclassification_preserves_timestampsFrom _ _ _ hWF rfl

/-- WS-SM SM9.A.1a: **a recorded event's timestamp is unique in the trail it
lands in**, at the mounted epoch.

The consumer-facing form: an auditor holding a well-formed snapshot may use a
timestamp as an event's name.  Restating SM8.C's identification result against
`declassificationTrailWellFormed` is what keeps that true after a drain. -/
theorem declassificationTrail_timestamp_identifies_event (st : SystemState)
    (hWF : declassificationTrailWellFormed st = true)
    {e₁ e₂ : DeclassificationEvent}
    (h₁ : e₁ ∈ st.declassificationAuditLog) (h₂ : e₂ ∈ st.declassificationAuditLog)
    (hTs : e₁.timestamp = e₂.timestamp) : e₁ = e₂ :=
  declassificationAuditLog_timestamp_identifies_event _ _ hWF h₁ h₂ hTs

-- ============================================================================
-- WS-SM SM8.C: the declassification's members of the enforcement families
-- ============================================================================

/-! `enforcementBoundary` classifies `declassifyObjectFromCore` as policy-gated,
and the two families every other policy-gated entry belongs to state that a
denied operation changes nothing and that a gate has no behaviour beyond
delegate-or-deny.  The declassification is the one entry for which
"delegate-or-deny" is a *trichotomy* rather than a dichotomy — a fail-closed
capacity refusal is a third outcome — so the sufficiency theorem below is
stated with three arms, and the point of stating it is that there is no fourth. -/

/-- WS-SM SM8.C: a refused declassification changes no state.

Stronger than it looks, because the refusal is the *only* thing that can happen
when the gate says no: `authorizeDeclassificationOnCore` consults the decision
before it reads the trail's occupancy, so a refused caller neither writes an
entry nor consumes capacity. -/
theorem authorizeDeclassificationOnCore_denied_preserves_state
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st : SystemState) (err : KernelError)
    (hDeny : declassificationDecision ctx declPolicy srcDomain dstDomain = .error err) :
    ¬∃ st', authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st
      = .ok ((), st') := by
  rintro ⟨st', h⟩
  obtain ⟨_, hDec⟩ :=
    (authorizeDeclassificationOnCore_ok_iff ctx declPolicy c srcDomain dstDomain
      targetId st).mp ⟨st', h⟩
  rw [hDeny] at hDec
  simp at hDec

/-- WS-SM SM8.C: **enforcement sufficiency for the declassification** — the live
transition does exactly one of three things, and nothing else.

1. The policy authorizes it and the trail has room: it records exactly one event
   and writes no other field.
2. The policy authorizes it and the trail is full: it refuses with
   `.auditLogCapacityExceeded`, leaving the state untouched — the fail-closed
   arm, which is why a downgrade the kernel authorized is never unrecorded.
3. The policy refuses: the decision's own error is returned verbatim, so the
   caller sees `.flowDenied` (the flow was allowed outright, so no
   declassification was needed) or `.declassificationDenied` (no rule permits
   it) rather than a code that conflates the two.

Arm 3 is stated as "the decision's error, verbatim" rather than enumerating the
two discriminants, so that a future decision arm cannot be silently remapped
onto an existing code. -/
theorem enforcement_sufficiency_declassify
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (st : SystemState) :
    (declassificationDecision ctx declPolicy srcDomain dstDomain = .ok () ∧
       st.declassificationAuditLog.length < maxDeclassificationAuditEntries ∧
       authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
         .ok ((), { st with declassificationAuditLog :=
           declassifyStoreTrail c srcDomain dstDomain targetId st })) ∨
    (declassificationDecision ctx declPolicy srcDomain dstDomain = .ok () ∧
       maxDeclassificationAuditEntries ≤ st.declassificationAuditLog.length ∧
       authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
         .error .auditLogCapacityExceeded) ∨
    (∃ err, declassificationDecision ctx declPolicy srcDomain dstDomain = .error err ∧
       authorizeDeclassificationOnCore ctx declPolicy c srcDomain dstDomain targetId st =
         .error err) := by
  cases hDec : declassificationDecision ctx declPolicy srcDomain dstDomain with
  | error err =>
    refine Or.inr (Or.inr ⟨err, rfl, ?_⟩)
    unfold authorizeDeclassificationOnCore
    rw [hDec]
  | ok u =>
    cases u
    by_cases hRoom : st.declassificationAuditLog.length < maxDeclassificationAuditEntries
    · refine Or.inl ⟨rfl, hRoom, ?_⟩
      unfold authorizeDeclassificationOnCore
      rw [hDec, recordDeclassificationChecked_eq_record _ _ hRoom]
    · have hFull : maxDeclassificationAuditEntries ≤ st.declassificationAuditLog.length :=
        Nat.not_lt.mp hRoom
      refine Or.inr (Or.inl ⟨rfl, hFull, ?_⟩)
      unfold authorizeDeclassificationOnCore
      rw [hDec, recordDeclassificationChecked_eq_none _ _ hFull]

/-- WS-SM SM8.C: the family's member for the **boundary's named entry**.

`enforcementBoundary` classifies `declassifyObjectFromCore`, not the inner gate,
so the family owes a theorem about that name.  It is the entry point's own
denial-preservation, and it covers all three ways the entry point refuses: an
idle core, an absent target, and a decision the policy declines — none of which
writes a field.

The hypothesis is stated against the *resolved* subject, which is the only form
available: the entry point reads the source domain off whichever thread the core
is running, so a caller cannot name a pair for which to assume denial. -/
theorem declassifyObjectFromCore_denied_preserves_state
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st : SystemState)
    (hDeny : ∀ tid, st.scheduler.currentOnCore c = some tid →
      ∃ err, declassificationDecision ctx declPolicy (ctx.threadDomainOf tid)
        (ctx.objectDomainOf targetId) = .error err) :
    ¬∃ st', declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st') := by
  rintro ⟨st', hStep⟩
  obtain ⟨⟨tid, hCur⟩, ⟨ty, hTy⟩⟩ :=
    declassifyObjectFromCore_ok_resolved ctx declPolicy c targetId st st' hStep
  obtain ⟨err, hErr⟩ := hDeny tid hCur
  rw [declassifyObjectFromCore_eq_onCore ctx declPolicy c targetId st tid ty hCur hTy] at hStep
  exact authorizeDeclassificationOnCore_denied_preserves_state ctx declPolicy c
    (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId) targetId st err hErr ⟨st', hStep⟩

end SeLe4n.Kernel
