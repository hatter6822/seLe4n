/-
Copyright (c) 2025 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license.

WS-SM SM9.C: the data-carrying declassification.

`.declassify` (SM8.C.9) authorizes a downgrade and records it; **no bytes
cross**.  This module is the transition that moves the data: a notification
signal whose badge is permitted to cross a label boundary the base policy
denies, on the SM6.B cross-core signal path, with one audit entry per authorized
hop.

## Two hops, two authorizations, two records

The live `notificationSignalBoundCrossCoreDispatchChecked` gates **two** flows —
`signaler → notification` and, when the signal resolves a receiver,
`notification → receiver`.  The second was added at v0.31.73 for a reason that
matters more here than there: without it a signal authorized to the notification
delivers the badge onward into a low bound TCB.  A declassifying variant gated
only on the notification would re-open that leak with *stronger* authority
behind it, so this transition gates the **resolved destination** as well
(`declassifiedSignal_gates_resolved_receiver`).

Gating both hops immediately raises what one audit event can honestly say.  On a
`high → mid` notification followed by a `mid → low` delivery, a single record
must either drop the first downgrade or collapse two domain pairs — and
potentially two authorization decisions — into a direct `high → low` edge no
policy authorized.  So the transition emits **one event per authorized
downgrade**, in hop order, sharing one actor
(`declassifiedSignal_audits_each_hop`, `declassifiedSignal_no_invented_edge`).

An ordinary hop — one the base policy already permits — is *not* a
declassification and records nothing.  That is why a signal both of whose hops
are ordinary is exactly the ordinary checked signal
(`declassifiedSignal_ordinary_eq_signal`): the syscall adds authority where the
policy withholds it and adds nothing where the policy does not.

## What a footprint does not do

Naming the receiver's TCB in the effect footprint says *where the writes land*.
It says nothing about whether that sink is permitted, and conflating the two is
exactly how the v0.31.73 leak would come back.  `footprint_does_not_authorize`
keeps the distinction on the record: there are states whose footprint names a
receiver the transition then refuses to deliver to.
-/
import SeLe4n.Kernel.IPC.CrossCore.NotificationBindDispatch
import SeLe4n.Kernel.IPC.CrossCore.NotificationInvariant
import SeLe4n.Kernel.InformationFlow.AuditRead

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind bootCoreId)

-- ============================================================================
-- §0  WS-SM SM9.C.1 — the audit trail is not IPC state
-- ============================================================================

/-! An IPC transition must leave the declassification audit trail alone: it is
the audit layer's own state, and a signal that could grow or renumber it would
make the trail a function of IPC traffic rather than of authorized downgrades.

Nothing in the tree said so, because until SM9.C no IPC transition sat next to
the trail.  The frames below say it once per building block and then once for
the signal, which is what lets §8's headline theorems talk about entries
appended to **the pre-state's** trail. -/

/-- WS-SM SM9.C.1: a queue-link store leaves the audit trail alone — it is one
`storeObject`. -/
theorem storeTcbQueueLinks_declassificationAuditLog_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (h : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    st'.declassificationAuditLog = st.declassificationAuditLog := by
  unfold storeTcbQueueLinks at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i pair hStore
      simp only [Except.ok.injEq] at h
      subst h
      exact storeObject_declassificationAuditLog_eq st _ _ ((), pair) hStore

/-- WS-SM SM9.C.1: …and the epoch. -/
theorem storeTcbQueueLinks_declassificationAuditEpoch_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (h : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    st'.declassificationAuditEpoch = st.declassificationAuditEpoch := by
  unfold storeTcbQueueLinks at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i pair hStore
      simp only [Except.ok.injEq] at h
      subst h
      exact storeObject_declassificationAuditEpoch_eq st _ _ ((), pair) hStore

/-- WS-SM SM9.C.1: an IPC-state-and-message store leaves the trail alone. -/
theorem storeTcbIpcStateAndMessage_declassificationAuditLog_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (h : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st') :
    st'.declassificationAuditLog = st.declassificationAuditLog := by
  unfold storeTcbIpcStateAndMessage at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i pair hStore
      simp only [Except.ok.injEq] at h
      subst h
      exact storeObject_declassificationAuditLog_eq st _ _ ((), pair) hStore

/-- WS-SM SM9.C.1: a receive-complete store leaves the trail alone. -/
theorem storeTcbReceiveComplete_declassificationAuditLog_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (h : storeTcbReceiveComplete st tid msg = .ok st') :
    st'.declassificationAuditLog = st.declassificationAuditLog := by
  unfold storeTcbReceiveComplete at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i pair hStore
      simp only [Except.ok.injEq] at h
      subst h
      exact storeObject_declassificationAuditLog_eq st _ _ ((), pair) hStore

/-- WS-SM SM9.C.1: the per-core enqueue leaves the trail alone — it writes the
object store and the scheduler, and neither is the trail. -/
@[simp] theorem enqueueRunnableOnCore_declassificationAuditLog_eq (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) :
    (enqueueRunnableOnCore st c tid).declassificationAuditLog =
      st.declassificationAuditLog := by
  unfold enqueueRunnableOnCore
  split
  · split <;> rfl
  · rfl

/-- WS-SM SM9.C.1: the cross-core wake leaves the trail alone. -/
@[simp] theorem wakeThread_declassificationAuditLog_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) :
    (wakeThread st tid executingCore).1.declassificationAuditLog =
      st.declassificationAuditLog := by
  unfold wakeThread
  exact enqueueRunnableOnCore_declassificationAuditLog_eq st _ tid

/-- WS-SM SM9.C.1: the queue-dequeue leaves the trail alone — the
`endpointQueueRemoveDual_frame` instance at the trail. -/
theorem endpointQueueRemoveDual_declassificationAuditLog_eq (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    st'.declassificationAuditLog = st.declassificationAuditLog :=
  endpointQueueRemoveDual_frame (fun s => s.declassificationAuditLog)
    (fun s s' oid obj h => storeObject_declassificationAuditLog_eq s oid obj ((), s') h)
    (fun s s' t qp qpp qn h => storeTcbQueueLinks_declassificationAuditLog_eq s s' t qp qpp qn h)
    st st' endpointId isReceiveQ tid hStep

/-- WS-SM SM9.C.1: **the cross-core signal leaves the audit trail alone.**

The property SM9.C's headline theorems are stated against: entries the
declassifying signal appends are appended to the trail the *pre-state* carried,
because the delivery itself contributed none. -/
theorem notificationSignalOnCore_declassificationAuditLog_eq (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState) :
    ((notificationSignalOnCore notificationId badge executingCore st).1).declassificationAuditLog =
      st.declassificationAuditLog := by
  unfold notificationSignalOnCore
  cases hN : st.getNotification? notificationId with
  | none => simp only []; split <;> rfl
  | some ntfn =>
    simp only []
    cases hT : ntfn.waitingThreads.tail? with
    | none =>
      simp only []
      cases hStore : storeObject notificationId _ st with
      | error e => rfl
      | ok pair =>
        exact storeObject_declassificationAuditLog_eq st _ _ pair hStore
    | some pair =>
      simp only []
      cases hStore : storeObject notificationId _ st with
      | error e => rfl
      | ok p1 =>
        simp only []
        cases hMsg : storeTcbIpcStateAndMessage p1.2 pair.1 .ready
            (some { IpcMessage.empty with badge := some badge }) with
        | error e => rfl
        | ok st2 =>
          simp only []
          rw [wakeThread_declassificationAuditLog_eq st2 pair.1 executingCore,
            storeTcbIpcStateAndMessage_declassificationAuditLog_eq p1.2 st2 pair.1 .ready _ hMsg,
            storeObject_declassificationAuditLog_eq st _ _ p1 hStore]

/-- WS-SM SM9.C.1: the bound-aware signal too — the delivery path composes a
dequeue, a store and a wake, none of which is an audit write. -/
theorem notificationSignalBoundOnCore_declassificationAuditLog_eq
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) :
    ((notificationSignalBoundOnCore notificationId badge executingCore st).1).declassificationAuditLog
      = st.declassificationAuditLog := by
  unfold notificationSignalBoundOnCore
  cases hTarget : boundDeliveryTarget? st notificationId with
  | none =>
    simp only []
    exact notificationSignalOnCore_declassificationAuditLog_eq notificationId badge
      executingCore st
  | some pair =>
    obtain ⟨t, epId⟩ := pair
    simp only []
    cases hRemove : endpointQueueRemoveDual epId true t st with
    | error e => rfl
    | ok u =>
      obtain ⟨_, st1⟩ := u
      simp only []
      cases hStore : storeTcbReceiveComplete st1 t
          (some { IpcMessage.empty with badge := some badge }) with
      | error e => rfl
      | ok st2 =>
        simp only []
        rw [wakeThread_declassificationAuditLog_eq st2 t executingCore,
          storeTcbReceiveComplete_declassificationAuditLog_eq st1 st2 t _ hStore,
          endpointQueueRemoveDual_declassificationAuditLog_eq st st1 epId true t hRemove]


/-- WS-SM SM9.C.1: a failed cross-core signal returns the **pre-state** — every
error arm is written that way, so a `withLockSet` bracket releases cleanly and a
composed transition can return the caller's own state. -/
theorem notificationSignalOnCore_error_state (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState) (e : KernelError)
    (h : (notificationSignalOnCore notificationId badge executingCore st).2 = .error e) :
    (notificationSignalOnCore notificationId badge executingCore st).1 = st := by
  unfold notificationSignalOnCore at h ⊢
  cases hN : st.getNotification? notificationId with
  | none => simp only []; split <;> rfl
  | some ntfn =>
    simp only [hN] at h ⊢
    cases hT : ntfn.waitingThreads.tail? with
    | none =>
      simp only [hT] at h ⊢
      cases hStore : storeObject notificationId _ st with
      | error e' => rfl
      | ok pair => simp only [hStore] at h; exact absurd h (by simp)
    | some pair =>
      simp only [hT] at h ⊢
      cases hStore : storeObject notificationId _ st with
      | error e' => rfl
      | ok p1 =>
        simp only [hStore] at h ⊢
        cases hMsg : storeTcbIpcStateAndMessage p1.2 pair.1 .ready
            (some { IpcMessage.empty with badge := some badge }) with
        | error e' => rfl
        | ok st2 => simp only [hMsg] at h; exact absurd h (by simp)

/-- WS-SM SM9.C.1: the bound-aware signal too. -/
theorem notificationSignalBoundOnCore_error_state (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState) (e : KernelError)
    (h : (notificationSignalBoundOnCore notificationId badge executingCore st).2 = .error e) :
    (notificationSignalBoundOnCore notificationId badge executingCore st).1 = st := by
  unfold notificationSignalBoundOnCore at h ⊢
  cases hTarget : boundDeliveryTarget? st notificationId with
  | none =>
    simp only [hTarget] at h ⊢
    exact notificationSignalOnCore_error_state notificationId badge executingCore st e h
  | some pair =>
    obtain ⟨t, epId⟩ := pair
    simp only [hTarget] at h ⊢
    cases hRemove : endpointQueueRemoveDual epId true t st with
    | error e' => rfl
    | ok u =>
      simp only [hRemove] at h ⊢
      cases hStore : storeTcbReceiveComplete u.2 t
          (some { IpcMessage.empty with badge := some badge }) with
      | error e' => rfl
      | ok st2 => simp only [hStore] at h; exact absurd h (by simp)

/-- WS-SM SM9.C.1: **a signal does not change which thread a core is running.**

It enqueues the woken thread on its home core's run queue; the `current` slot is
the scheduler's business.  The fact SM9.C's attribution rests on: the subject an
audit entry names is still the subject the core is running in the post-state an
auditor inspects. -/
theorem notificationSignalOnCore_currentOnCore_eq (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState) (c : CoreId) :
    ((notificationSignalOnCore notificationId badge executingCore st).1).scheduler.currentOnCore c
      = st.scheduler.currentOnCore c := by
  unfold notificationSignalOnCore
  cases hN : st.getNotification? notificationId with
  | none => simp only []; split <;> rfl
  | some ntfn =>
    simp only []
    cases hT : ntfn.waitingThreads.tail? with
    | none =>
      simp only []
      cases hStore : storeObject notificationId _ st with
      | error e => rfl
      | ok pair =>
        obtain ⟨u, stp⟩ := pair
        cases u
        rw [storeObject_scheduler_eq st stp _ _ hStore]
    | some pair =>
      simp only []
      cases hStore : storeObject notificationId _ st with
      | error e => rfl
      | ok p1 =>
        simp only []
        cases hMsg : storeTcbIpcStateAndMessage p1.2 pair.1 .ready
            (some { IpcMessage.empty with badge := some badge }) with
        | error e => rfl
        | ok st2 =>
          simp only []
          show ((wakeThread st2 pair.1 executingCore).1).scheduler.currentOnCore c = _
          unfold wakeThread
          rw [enqueueRunnableOnCore_currentOnCore st2 _ pair.1 c,
            storeTcbIpcStateAndMessage_scheduler_eq p1.2 st2 pair.1 .ready _ hMsg,
            storeObject_scheduler_eq st p1.2 _ _ (by cases p1 with | mk u v => cases u; exact hStore)]

/-- WS-SM SM9.C.1: the bound-aware signal too — bound delivery dequeues, stores
and wakes, and none of the three touches a `current` slot. -/
theorem notificationSignalBoundOnCore_currentOnCore_eq (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState) (c : CoreId) :
    (((notificationSignalBoundOnCore notificationId badge executingCore st).1).scheduler).currentOnCore c
      = st.scheduler.currentOnCore c := by
  unfold notificationSignalBoundOnCore
  cases hTarget : boundDeliveryTarget? st notificationId with
  | none =>
    simp only []
    exact notificationSignalOnCore_currentOnCore_eq notificationId badge executingCore st c
  | some pair =>
    obtain ⟨t, epId⟩ := pair
    simp only []
    cases hRemove : endpointQueueRemoveDual epId true t st with
    | error e => rfl
    | ok u =>
      obtain ⟨_, st1⟩ := u
      simp only []
      cases hStore : storeTcbReceiveComplete st1 t
          (some { IpcMessage.empty with badge := some badge }) with
      | error e => rfl
      | ok st2 =>
        simp only []
        show ((wakeThread st2 t executingCore).1).scheduler.currentOnCore c = _
        unfold wakeThread
        rw [enqueueRunnableOnCore_currentOnCore st2 _ t c,
          storeTcbReceiveComplete_scheduler_eq st1 st2 t _ hStore,
          endpointQueueRemoveDual_scheduler_eq st st1 epId true t hRemove]

-- ============================================================================
-- §1  WS-SM SM9.C.1 — the resolved destination
-- ============================================================================

/-- WS-SM SM9.C.1: **the receiver a signal on `notificationId` would deliver
to**, resolved from the pre-state.

Exactly the destination `notificationSignalBoundOnCore` picks: the bound TCB
when the bound-delivery path applies, otherwise the head waiter, and nothing
when the badge merely accumulates in the notification's `pendingBadge`.  The two
cases are mutually exclusive by construction — `boundDeliveryTarget?` requires an
empty waiter list — so this is a resolution rather than a preference.

Read from the **pre**-state, which is the only state that still has it: after
the signal the waiter is dequeued and woken. -/
def declassifiedSignalReceiver? (st : SystemState) (notificationId : SeLe4n.ObjId) :
    Option SeLe4n.ThreadId :=
  match boundDeliveryTarget? st notificationId with
  | some (t, _) => some t
  | none => notificationSignalWaiter? st notificationId

/-- WS-SM SM9.C.1: on the bound-delivery path the resolved receiver is the bound
TCB. -/
@[simp] theorem declassifiedSignalReceiver?_bound (st : SystemState)
    (notificationId : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (ep : SeLe4n.ObjId)
    (hTarget : boundDeliveryTarget? st notificationId = some (t, ep)) :
    declassifiedSignalReceiver? st notificationId = some t := by
  simp [declassifiedSignalReceiver?, hTarget]

/-- WS-SM SM9.C.1: off the bound-delivery path the resolved receiver is the head
waiter — the thread `notificationSignalWaiter?` pre-resolves, which is the same
thread the SM6.B lock set takes a write lock on. -/
@[simp] theorem declassifiedSignalReceiver?_fallthrough (st : SystemState)
    (notificationId : SeLe4n.ObjId)
    (hNone : boundDeliveryTarget? st notificationId = none) :
    declassifiedSignalReceiver? st notificationId =
      notificationSignalWaiter? st notificationId := by
  simp [declassifiedSignalReceiver?, hNone]

/-- WS-SM SM9.C.1 (PR #872 review): a resolved receiver implies a **live
notification** — both resolution routes open on `getNotification?`, so the
target gate below never refuses a state in which a receiver exists. -/
theorem declassifiedSignalReceiver?_some_notification (st : SystemState)
    (notificationId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (h : declassifiedSignalReceiver? st notificationId = some receiver) :
    ∃ ntfn, st.getNotification? notificationId = some ntfn := by
  cases hN : st.getNotification? notificationId with
  | some ntfn => exact ⟨ntfn, rfl⟩
  | none =>
    exfalso
    unfold declassifiedSignalReceiver? boundDeliveryTarget?
      notificationSignalWaiter? at h
    rw [hN] at h
    simp at h

/-- WS-SM SM9.C.1 (PR #872 review): the typed kind-agnostic accessor answers
`isSome` exactly when the raw store does — the bridge that makes the target
gate's error distinction *definitionally* the ordinary signal's. -/
theorem getObjectType?_isSome_eq_raw (st : SystemState) (id : SeLe4n.ObjId) :
    (st.getObjectType? id).isSome = (st.objects[id]?).isSome := by
  unfold SystemState.getObjectType?
  cases st.objects[id]? <;> rfl

-- ============================================================================
-- §2  WS-SM SM9.C.1 — per-hop authorization
-- ============================================================================

/-- WS-SM SM9.C.1: **which of the two authorizations a refusal is about.**

The distinction has to reach the refusal ledger: a monitor reading "denied" with
no idea which gate refused cannot tell an unauthorized caller from an authorized
caller aimed at an unauthorized sink, and those call for opposite responses.  It
rides the `KernelError` discriminant, which the ledger already stores. -/
inductive DeclassifiedSignalHop where
  /-- The signaller releasing into the notification. -/
  | callerToNotification
  /-- The notification releasing onward into the resolved receiver. -/
  | notificationToReceiver
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM9.C.1: the error a refused hop returns.  Total with no wildcard, so
a third hop cannot be added without deciding what it reports. -/
def DeclassifiedSignalHop.refusal : DeclassifiedSignalHop → KernelError
  | .callerToNotification => .declassificationDenied
  | .notificationToReceiver => .declassificationDeniedAtReceiver

/-- WS-SM SM9.C.1: the two hops report **different** discriminants — the
property the refusal ledger's usefulness rests on. -/
theorem DeclassifiedSignalHop.refusal_injective :
    ∀ h₁ h₂ : DeclassifiedSignalHop, h₁.refusal = h₂.refusal → h₁ = h₂ := by
  intro h₁ h₂ h; cases h₁ <;> cases h₂ <;> first | rfl | (exact absurd h (by decide))

/-- WS-SM SM9.C.1: **how a hop was permitted** — by the base policy, or by the
declassification policy.

The distinction is what decides whether the hop owes an audit entry: an ordinary
flow is not a downgrade and there is nothing to record, while a downgrade is
exactly what the trail exists to record. -/
inductive DeclassifiedHopAuthorization where
  /-- The base policy already permits this flow; no downgrade, no record. -/
  | ordinary
  /-- The base policy denies it and the declassification policy authorizes it. -/
  | declassified
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM9.C.1: **one hop's gate.**

Reuses `declassificationDecision` rather than restating its two checks, so the
data-carrying path and `.declassify` cannot drift apart on what counts as an
authorized downgrade.  The `.error .flowDenied` arm that decision returns for an
*allowed* base flow is the "not a declassification" answer, which here is a
success with nothing to record rather than a refusal. -/
def declassifiedSignalHopAuthorization (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (hop : DeclassifiedSignalHop)
    (srcDomain dstDomain : SecurityDomain) :
    Except KernelError DeclassifiedHopAuthorization :=
  if ctx.policy.canFlow srcDomain dstDomain then
    .ok .ordinary
  else
    match declassificationDecision ctx declPolicy srcDomain dstDomain with
    | .ok () => .ok .declassified
    | .error _ => .error hop.refusal

/-- WS-SM SM9.C.1: a hop the base policy permits is ordinary. -/
theorem declassifiedSignalHopAuthorization_ordinary (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (hop : DeclassifiedSignalHop)
    (srcDomain dstDomain : SecurityDomain)
    (hFlow : ctx.policy.canFlow srcDomain dstDomain = true) :
    declassifiedSignalHopAuthorization ctx declPolicy hop srcDomain dstDomain = .ok .ordinary := by
  simp [declassifiedSignalHopAuthorization, hFlow]

/-- WS-SM SM9.C.1: a hop the base policy denies and the declassification policy
authorizes is a **downgrade**. -/
theorem declassifiedSignalHopAuthorization_declassified (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (hop : DeclassifiedSignalHop)
    (srcDomain dstDomain : SecurityDomain)
    (hDeny : ctx.policy.canFlow srcDomain dstDomain = false)
    (hDecl : declPolicy.canDeclassify srcDomain dstDomain = true) :
    declassifiedSignalHopAuthorization ctx declPolicy hop srcDomain dstDomain =
      .ok .declassified := by
  simp [declassifiedSignalHopAuthorization, hDeny, declassificationDecision, hDecl]

/-- WS-SM SM9.C.1: a hop neither policy permits is refused, **with this hop's
own discriminant**. -/
theorem declassifiedSignalHopAuthorization_refused (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (hop : DeclassifiedSignalHop)
    (srcDomain dstDomain : SecurityDomain)
    (hDeny : ctx.policy.canFlow srcDomain dstDomain = false)
    (hNoDecl : declPolicy.canDeclassify srcDomain dstDomain = false) :
    declassifiedSignalHopAuthorization ctx declPolicy hop srcDomain dstDomain =
      .error hop.refusal := by
  simp [declassifiedSignalHopAuthorization, hDeny, declassificationDecision, hNoDecl]

/-- WS-SM SM9.C.1 (**the soundness of a `.declassified` verdict**): the gate says
"downgrade" exactly when `declassificationDecision` authorized it — the same two
checks `.declassify` runs, on the same function. -/
theorem declassifiedSignalHopAuthorization_declassified_authorized
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (hop : DeclassifiedSignalHop) (srcDomain dstDomain : SecurityDomain)
    (h : declassifiedSignalHopAuthorization ctx declPolicy hop srcDomain dstDomain =
      .ok .declassified) :
    declassificationDecision ctx declPolicy srcDomain dstDomain = .ok () := by
  unfold declassifiedSignalHopAuthorization at h
  split at h
  · exact absurd h (by simp)
  · next hDeny =>
    obtain ⟨dec, hDec⟩ : ∃ d, declassificationDecision ctx declPolicy srcDomain dstDomain = d :=
      ⟨_, rfl⟩
    rw [hDec] at h
    cases dec with
    | error e => exact absurd h (by simp)
    | ok u => cases u; exact hDec

/-- WS-SM SM9.C.1: an `.ordinary` verdict really is an ordinary flow — the base
policy permits it, so no downgrade occurred and no record is owed. -/
theorem declassifiedSignalHopAuthorization_ordinary_flows
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (hop : DeclassifiedSignalHop) (srcDomain dstDomain : SecurityDomain)
    (h : declassifiedSignalHopAuthorization ctx declPolicy hop srcDomain dstDomain =
      .ok .ordinary) :
    ctx.policy.canFlow srcDomain dstDomain = true := by
  unfold declassifiedSignalHopAuthorization at h
  split at h
  · assumption
  · next hDeny =>
    obtain ⟨dec, hDec⟩ : ∃ d, declassificationDecision ctx declPolicy srcDomain dstDomain = d :=
      ⟨_, rfl⟩
    rw [hDec] at h
    cases dec with
    | error e => exact absurd h (by simp)
    | ok u => cases u; exact absurd h (by simp)

-- ============================================================================
-- §3  WS-SM SM9.C.1 — the per-hop record obligations
-- ============================================================================

/-- WS-SM SM9.C.1: **one authorized downgrade the transition owes a record
for** — the flow's two endpoints and the object the badge lands in.

A list of these is what the commit below folds into the trail.  Deliberately not
a list of whole `DeclassificationEvent`s: the timestamp is the trail's own
shape, so an event can only be built against the state it is appended to, and
building it early would stamp the second hop with the first hop's position. -/
structure DeclassifiedHopRecord where
  /-- The domain the badge is released *from* on this hop. -/
  srcDomain : SecurityDomain
  /-- The domain it is released *into*. -/
  dstDomain : SecurityDomain
  /-- The object that receives it — the notification on hop 1, the receiver's
      TCB on hop 2.  This is the SM9.C.1 "actual destination". -/
  target : SeLe4n.ObjId
  deriving Repr, DecidableEq

/-- WS-SM SM9.C.1: the record a hop owes — `[]` for an ordinary flow, one entry
for a downgrade.  A list rather than an `Option` so the two hops concatenate. -/
def declassifiedHopRecords (auth : DeclassifiedHopAuthorization)
    (srcDomain dstDomain : SecurityDomain) (target : SeLe4n.ObjId) :
    List DeclassifiedHopRecord :=
  match auth with
  | .ordinary => []
  | .declassified => [{ srcDomain := srcDomain, dstDomain := dstDomain, target := target }]

/-- WS-SM SM9.C.1: an ordinary hop owes nothing. -/
@[simp] theorem declassifiedHopRecords_ordinary (srcDomain dstDomain : SecurityDomain)
    (target : SeLe4n.ObjId) :
    declassifiedHopRecords .ordinary srcDomain dstDomain target = [] := rfl

/-- WS-SM SM9.C.1: a downgrade owes exactly one. -/
@[simp] theorem declassifiedHopRecords_declassified (srcDomain dstDomain : SecurityDomain)
    (target : SeLe4n.ObjId) :
    declassifiedHopRecords .declassified srcDomain dstDomain target =
      [{ srcDomain := srcDomain, dstDomain := dstDomain, target := target }] := rfl

/-- WS-SM SM9.C.1: **append the owed records to the trail**, each stamped
against the state it lands in.

Fail-closed as a whole: `recordDeclassificationChecked` refuses at capacity, and
`foldlM` over `Option` propagates that refusal, so a two-hop delivery with room
for only one entry records *neither* and the operation fails.  Recording one hop
of an authorized two-hop delivery would leave a downgrade the kernel performed
and did not record, which is the failure the fail-closed bound exists to
exclude. -/
def recordDeclassifiedHopsFrom (c : CoreId) (actor : DeclassificationActor)
    (tags : DeclassificationTaint) :
    List DeclassifiedHopRecord → SystemState → Option SystemState
  | [], st => some st
  | r :: rest, st =>
      match recordDeclassificationChecked st.declassificationAuditLog
          (declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st) with
      | none => none
      | some log' =>
          recordDeclassifiedHopsFrom c actor
            (tags.insert (st.declassificationAuditEpoch + st.declassificationAuditLog.length))
            rest { st with declassificationAuditLog := log' }

/-- WS-SM SM9.C.1 / SM9.D.13a: **append the owed records to the trail**, each
stamped against the state it lands in and each carrying the acting subject's
provenance.

The accumulator is what makes a two-hop delivery a *causal* chain rather than
merely a syntactically linked one.  The first hop's snapshot is the subject's
taint at the pre-state; the second hop's is that snapshot **extended with the
first hop's freshly allocated timestamp**, so `declassificationChainCausal`
accepts the pair the transition writes.  Taking the pre-transition snapshot for
both would reject it — the timestamp does not exist until the first hop is
recorded — which is the failure mode §3.5 of the plan names.

Fail-closed as a whole: `recordDeclassificationChecked` refuses at capacity and
the recursion propagates that refusal, so a two-hop delivery with room for only
one entry records *neither* and the operation fails.  Recording one hop of an
authorized two-hop delivery would leave a downgrade the kernel performed and did
not record, which is the failure the fail-closed bound exists to exclude. -/
def recordDeclassifiedHops (c : CoreId) (actor : DeclassificationActor)
    (records : List DeclassifiedHopRecord) (st : SystemState) : Option SystemState :=
  recordDeclassifiedHopsFrom c actor (declassificationActorTaint actor st) records st

/-- WS-SM SM9.C.1: no records, no change. -/
@[simp] theorem recordDeclassifiedHopsFrom_nil (c : CoreId) (actor : DeclassificationActor)
    (tags : DeclassificationTaint) (st : SystemState) :
    recordDeclassifiedHopsFrom c actor tags [] st = some st := rfl

/-- WS-SM SM9.C.1: no records, no change. -/
@[simp] theorem recordDeclassifiedHops_nil (c : CoreId) (actor : DeclassificationActor)
    (st : SystemState) : recordDeclassifiedHops c actor [] st = some st := rfl

/-- WS-SM SM9.C.1 / SM9.D.13a: **the step form** — recording one record and then
the rest, with the accumulator advanced by the entry just written.

Stated over `recordDeclassifiedHopsFrom` because the continuation's snapshot is
*not* the one `recordDeclassifiedHops` would recompute at the mid-state: the
taint side table is untouched by the audit write, so re-reading it would lose
exactly the freshly allocated timestamp the extension exists to carry. -/
theorem recordDeclassifiedHopsFrom_cons (c : CoreId) (actor : DeclassificationActor)
    (tags : DeclassificationTaint)
    (r : DeclassifiedHopRecord) (rest : List DeclassifiedHopRecord) (st st' : SystemState)
    (h : recordDeclassifiedHopsFrom c actor tags (r :: rest) st = some st') :
    st.declassificationAuditLog.length < maxDeclassificationAuditEntries ∧
    recordDeclassifiedHopsFrom c actor
      (tags.insert (st.declassificationAuditEpoch + st.declassificationAuditLog.length)) rest
      { st with declassificationAuditLog :=
          st.declassificationAuditLog ++
            [declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st] }
      = some st' := by
  unfold recordDeclassifiedHopsFrom at h
  obtain ⟨rec, hRec⟩ : ∃ x, recordDeclassificationChecked st.declassificationAuditLog
      (declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st) = x :=
    ⟨_, rfl⟩
  rw [hRec] at h
  cases rec with
  | none => exact absurd h (by simp)
  | some log' =>
    have hRoom : st.declassificationAuditLog.length < maxDeclassificationAuditEntries :=
      (recordDeclassificationChecked_isSome_iff _ _).mp (by rw [hRec]; rfl)
    have hLog' : log' = st.declassificationAuditLog ++
        [declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st] := by
      rw [recordDeclassificationChecked_eq_record _ _ hRoom] at hRec
      exact (Option.some.inj hRec).symm
    subst hLog'
    exact ⟨hRoom, h⟩

/-- WS-SM SM9.C.1: recording writes **only** the trail.

Every field but `declassificationAuditLog` is carried through untouched, which
is what lets the whole invariant surface of the underlying signal transfer
across the audit write. -/
theorem recordDeclassifiedHopsFrom_frame (c : CoreId) (actor : DeclassificationActor)
    (records : List DeclassifiedHopRecord) :
    ∀ (tags : DeclassificationTaint) (st st' : SystemState),
      recordDeclassifiedHopsFrom c actor tags records st = some st' →
      st' = { st with declassificationAuditLog := st'.declassificationAuditLog } := by
  induction records with
  | nil => intro tags st st' h; cases h; rfl
  | cons r rest ih =>
    intro tags st st' h
    obtain ⟨-, hRest⟩ := recordDeclassifiedHopsFrom_cons c actor tags r rest st st' h
    have := ih _ _ st' hRest
    rw [this]

/-- WS-SM SM9.C.1: recording writes **only** the trail — the entry-point form. -/
theorem recordDeclassifiedHops_frame (c : CoreId) (actor : DeclassificationActor)
    (records : List DeclassifiedHopRecord) (st st' : SystemState)
    (h : recordDeclassifiedHops c actor records st = some st') :
    st' = { st with declassificationAuditLog := st'.declassificationAuditLog } :=
  recordDeclassifiedHopsFrom_frame c actor records _ st st' h

/-- WS-SM SM9.C.1: recording **grows** the trail by exactly one entry per record,
appending in hop order. -/
theorem recordDeclassifiedHopsFrom_log (c : CoreId) (actor : DeclassificationActor)
    (records : List DeclassifiedHopRecord) :
    ∀ (tags : DeclassificationTaint) (st st' : SystemState),
      recordDeclassifiedHopsFrom c actor tags records st = some st' →
      ∃ appended : DeclassificationAuditLog,
        st'.declassificationAuditLog = st.declassificationAuditLog ++ appended ∧
        appended.length = records.length := by
  induction records with
  | nil => intro tags st st' h; cases h; exact ⟨[], by simp, rfl⟩
  | cons r rest ih =>
    intro tags st st' h
    obtain ⟨-, hRest⟩ := recordDeclassifiedHopsFrom_cons c actor tags r rest st st' h
    obtain ⟨appended, hApp, hLen⟩ := ih _ _ st' hRest
    refine ⟨declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st
              :: appended, ?_, ?_⟩
    · simp only [hApp, List.append_assoc, List.cons_append, List.nil_append]
    · simp [hLen]

/-- WS-SM SM9.C.1: recording **grows** the trail by exactly one entry per record,
appending in hop order — the entry-point form. -/
theorem recordDeclassifiedHops_log (c : CoreId) (actor : DeclassificationActor)
    (records : List DeclassifiedHopRecord) (st st' : SystemState)
    (h : recordDeclassifiedHops c actor records st = some st') :
    ∃ appended : DeclassificationAuditLog,
      st'.declassificationAuditLog = st.declassificationAuditLog ++ appended ∧
      appended.length = records.length :=
  recordDeclassifiedHopsFrom_log c actor records _ st st' h

/-- WS-SM SM9.C.1: recording preserves the capacity bound at any accumulator —
every append is the checked one. -/
theorem recordDeclassifiedHopsFrom_preserves_auditLogBounded (c : CoreId)
    (actor : DeclassificationActor) (records : List DeclassifiedHopRecord) :
    ∀ (tags : DeclassificationTaint) (st st' : SystemState),
      auditLogBounded st.declassificationAuditLog →
      recordDeclassifiedHopsFrom c actor tags records st = some st' →
      auditLogBounded st'.declassificationAuditLog := by
  induction records with
  | nil => intro tags st st' hBounded h; cases h; exact hBounded
  | cons r rest ih =>
    intro tags st st' hBounded h
    obtain ⟨hRoom, hRest⟩ := recordDeclassifiedHopsFrom_cons c actor tags r rest st st' h
    refine ih _ _ st' ?_ hRest
    show auditLogBounded (st.declassificationAuditLog ++ [_])
    simp only [auditLogBounded, List.length_append, List.length_cons, List.length_nil]
    omega

/-- WS-SM SM9.C.1 / SM9.A.1a: recording preserves the trail's timestamp
discipline at any accumulator — each append stamps `epoch + length` against the
state it lands in, which is what `declassifyStoreEventWithTags` computes. -/
theorem recordDeclassifiedHopsFrom_preserves_trailWellFormed (c : CoreId)
    (actor : DeclassificationActor) (records : List DeclassifiedHopRecord) :
    ∀ (tags : DeclassificationTaint) (st st' : SystemState),
      declassificationTrailWellFormed st = true →
      recordDeclassifiedHopsFrom c actor tags records st = some st' →
      declassificationTrailWellFormed st' = true := by
  induction records with
  | nil => intro tags st st' hWF h; cases h; exact hWF
  | cons r rest ih =>
    intro tags st st' hWF h
    obtain ⟨-, hRest⟩ := recordDeclassifiedHopsFrom_cons c actor tags r rest st st' h
    refine ih _ _ st' ?_ hRest
    show declassificationTrailWellFormed
      { st with declassificationAuditLog := st.declassificationAuditLog ++ [_] } = true
    show auditTimestampsFrom st.declassificationAuditEpoch
      (recordDeclassification st.declassificationAuditLog _) = true
    exact recordDeclassification_preserves_timestampsFrom _ _ _ hWF rfl

/-- WS-SM SM9.C.1: recording preserves the capacity bound — every append is the
checked one. -/
theorem recordDeclassifiedHops_preserves_auditLogBounded (c : CoreId)
    (actor : DeclassificationActor) (records : List DeclassifiedHopRecord)
    (st st' : SystemState)
    (hBounded : auditLogBounded st.declassificationAuditLog)
    (h : recordDeclassifiedHops c actor records st = some st') :
    auditLogBounded st'.declassificationAuditLog :=
  recordDeclassifiedHopsFrom_preserves_auditLogBounded c actor records _ st st' hBounded h

/-- WS-SM SM9.C.1 / SM9.A.1a: recording preserves the trail's timestamp
discipline at its epoch — each append stamps `epoch + length` against the state
it lands in, which is what `declassifyStoreEvent` computes. -/
theorem recordDeclassifiedHops_preserves_trailWellFormed (c : CoreId)
    (actor : DeclassificationActor) (records : List DeclassifiedHopRecord)
    (st st' : SystemState)
    (hWF : declassificationTrailWellFormed st = true)
    (h : recordDeclassifiedHops c actor records st = some st') :
    declassificationTrailWellFormed st' = true :=
  recordDeclassifiedHopsFrom_preserves_trailWellFormed c actor records _ st st' hWF h

-- ============================================================================
-- §4  WS-SM SM9.C.1 / SM9.C.2 — the transition
-- ============================================================================

/-- WS-SM SM9.C.1: the records a signal on `notificationId` owes, and whether it
is authorized at all — resolved entirely from the **pre**-state.

Factored out of the transition so the gate and the audit are one computation
read twice (the §3.5 "defined once" discipline): the commit below folds exactly
this list, and `declassifiedSignal_audits_each_hop` reads it too, so a record
the gate authorized and the commit did not write is not expressible.

**The second hop gates the plain waiter too — deliberately, where the ordinary
checked signal does not** (PR #872 review).  The ordinary
`notificationSignalBoundCrossCoreDispatchChecked` gates `notification →
receiver` only on the *bound-delivery* path and trusts the waiter queue,
because the checked *wait* gate admits a plain waiter only when that flow
already holds — so for a waiter admitted under the checked discipline this
hop's base verdict is `true`, the hop is `.ordinary`, and the gate is provably
a no-op (`declassifiedSignalPlan_admitted_receiver_error_is_first_hop`).  The
gate bites exactly on states the checked discipline does not produce — a
waiter admitted through the *unchecked* `.notificationWait` arm, or relabeled
after admission — and there the symmetric alternative would deliver a
freshly-downgraded badge to a receiver no policy authorized: the v0.31.73
badge-leak class with declassification authority behind it.  The honest cost
is a one-bit disclosure: a caller authorized at hop 1 can distinguish
"denied-domain plain waiter present" (refusal) from "no waiter" (success),
which the same class of refusal already disclosed for *bound* receivers on the
ordinary checked path since v0.31.73.  Exhibited rather than hidden:
`declassifiedSignalPlan_outcome_depends_on_receiver`. -/
def declassifiedSignalPlan (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) (st : SystemState) :
    Except KernelError (List DeclassifiedHopRecord) :=
  match declassifiedSignalHopAuthorization ctx declPolicy .callerToNotification
          actorDomain (ctx.objectDomainOf notificationId) with
  | .error e => .error e
  | .ok hop1 =>
      match declassifiedSignalReceiver? st notificationId with
      | none =>
          .ok (declassifiedHopRecords hop1 actorDomain (ctx.objectDomainOf notificationId)
            notificationId)
      | some receiver =>
          match declassifiedSignalHopAuthorization ctx declPolicy .notificationToReceiver
                  (ctx.objectDomainOf notificationId) (ctx.threadDomainOf receiver) with
          | .error e => .error e
          | .ok hop2 =>
              .ok (declassifiedHopRecords hop1 actorDomain (ctx.objectDomainOf notificationId)
                    notificationId ++
                declassifiedHopRecords hop2 (ctx.objectDomainOf notificationId)
                  (ctx.threadDomainOf receiver) receiver.toObjId)

/-- WS-SM SM9.C.1 / SM9.C.2 (**the transition**): a notification signal whose
badge may cross a boundary the base policy denies, on core `c`.

The shape, in the order the steps run and for the reasons SM8.C.9 established:

1. **Resolve the actor** from the state (`currentOnCore c`), never from an
   argument — an audit trail whose subject a caller can name is not an audit
   trail.  An idle core has no subject, so it fails closed.
2. **Validate the target** (PR #872 review): the operand must be a live
   notification *before* any policy is consulted, exactly as the sibling
   `.declassify` validates its target (`declassifyObjectFromCore` reads
   `getObjectType?` before `authorizeDeclassificationOnCore`).  A wrong-kind
   or absent target answers the ordinary signal's own errors —
   `.invalidCapability` / `.objectNotFound`, the AK7 recovery distinction —
   **independently of every policy and labeling**
   (`notificationSignalDeclassifiedOnCore_invalid_target_policy_blind`), so an
   invalid capability is never a policy oracle: before this step ran first, a
   caller holding a writable capability to a non-notification object read its
   own hop-1 verdict off the error discriminant.
3. **Decide both hops**, before any capacity check.  Deciding first confines the
   observation of trail occupancy to a caller whose downgrade *is* authorized
   (`declassifiedSignal_denied_before_capacity`), which is the SM8.C.9 ordering
   and the reason CC-8 is bounded to declassifying subjects.
4. **Run the signal** — the same `notificationSignalBoundOnCore` the ordinary
   `.notificationSignal` arm runs, so the delivery semantics, the cross-core
   wake and the SGI are not a second implementation of anything.
5. **Record**, fail-closed on capacity, returning the **pre-state** on any
   refusal so a partially-audited delivery is not expressible.

Returns the post-state paired with the optional cross-core `.reschedule` SGI,
matching `notificationSignalBoundOnCore`'s own shape so the runtime's diff-based
SGI seam is unchanged. -/
def notificationSignalDeclassifiedOnCore (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  match st.scheduler.currentOnCore c with
  | none => (st, .error .illegalState)
  | some signaler =>
      match st.getNotification? notificationId with
      | none =>
          -- PR #872 review: the target gate, ahead of every policy read.  The
          -- error distinction is the ordinary signal's own (AK7 recovery:
          -- present-but-wrong-kind vs genuinely absent), decided through the
          -- typed kind-agnostic accessor.
          if (st.getObjectType? notificationId).isSome then (st, .error .invalidCapability)
          else (st, .error .objectNotFound)
      | some _ =>
          let actor := declassificationActorOf ctx signaler
          match declassifiedSignalPlan ctx declPolicy notificationId actor.domain st with
          | .error e => (st, .error e)
          | .ok records =>
              match notificationSignalBoundOnCore notificationId badge c st with
              | (_, .error e) => (st, .error e)
              | (st1, .ok sgi) =>
                  match recordDeclassifiedHops c actor records st1 with
                  | none => (st, .error .auditLogCapacityExceeded)
                  | some st2 => (st2, .ok sgi)

/-- WS-SM SM9.C.2: the cross-core dispatch the live arm calls — the transition
with the executing core read from the state, exactly as SM6.B's
`notificationSignalBoundCrossCoreDispatch` does.

Deliberately **not** a boot-pinned sibling: the actor and the wake target are
both per-core facts, and a `bootCoreId` form would be the defect the per-core
routing gate exists to catch. -/
def notificationSignalDeclassifiedCrossCoreDispatch (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge
    (determineExecutingCore st signaler) st

-- ============================================================================
-- §5  WS-SM SM9.C.1 — path reductions and the fail-closed arms
-- ============================================================================

/-- WS-SM SM9.C.1: an idle core cannot declassify — there is no subject to
attribute the downgrade to, so the operation fails closed with the state
untouched.  The same discriminant, and the same reason, as
`declassifyObjectFromCore_no_subject`. -/
theorem notificationSignalDeclassifiedOnCore_no_subject (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState)
    (hIdle : st.scheduler.currentOnCore c = none) :
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st, .error .illegalState) := by
  simp [notificationSignalDeclassifiedOnCore, hIdle]

/-- WS-SM SM9.C.1: with a subject, the transition is the plan-then-commit
composition — the reduction every theorem below travels along. -/
theorem notificationSignalDeclassifiedOnCore_eq_of_subject (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) (signaler : SeLe4n.ThreadId)
    (ntfn : Notification)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hNtfn : st.getNotification? notificationId = some ntfn) :
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (match declassifiedSignalPlan ctx declPolicy notificationId
              (declassificationActorOf ctx signaler).domain st with
       | .error e => (st, .error e)
       | .ok records =>
           match notificationSignalBoundOnCore notificationId badge c st with
           | (_, .error e) => (st, .error e)
           | (st1, .ok sgi) =>
               match recordDeclassifiedHops c (declassificationActorOf ctx signaler)
                   records st1 with
               | none => (st, .error .auditLogCapacityExceeded)
               | some st2 => (st2, .ok sgi)) := by
  simp [notificationSignalDeclassifiedOnCore, hCur, hNtfn]

/-- WS-SM SM9.C.1: a refused plan refuses the transition, with the state
untouched and the plan's own error. -/
theorem notificationSignalDeclassifiedOnCore_plan_refused (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) (signaler : SeLe4n.ThreadId)
    (ntfn : Notification) (e : KernelError)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hNtfn : st.getNotification? notificationId = some ntfn)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId
      (declassificationActorOf ctx signaler).domain st = .error e) :
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st, .error e) := by
  rw [notificationSignalDeclassifiedOnCore_eq_of_subject ctx declPolicy notificationId badge c
    st signaler ntfn hCur hNtfn, hPlan]

/-- WS-SM SM9.C.1 (**success decomposes**): a successful declassifying signal
ran the ordinary bound signal and then appended exactly the planned records.

The transport every downstream theorem uses, and the reason the invariant
surface of the underlying signal carries: the committed state is the *signal's*
post-state with the trail extended, and nothing else. -/
theorem notificationSignalDeclassifiedOnCore_ok_inv (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind))
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ∃ signaler records,
      st.scheduler.currentOnCore c = some signaler ∧
      declassifiedSignalPlan ctx declPolicy notificationId
        (declassificationActorOf ctx signaler).domain st = .ok records ∧
      notificationSignalBoundOnCore notificationId badge c st =
        ((notificationSignalBoundOnCore notificationId badge c st).1, .ok sgi) ∧
      recordDeclassifiedHops c (declassificationActorOf ctx signaler) records
        (notificationSignalBoundOnCore notificationId badge c st).1 = some st' := by
  unfold notificationSignalDeclassifiedOnCore at hStep
  obtain ⟨cur, hCur⟩ : ∃ x, st.scheduler.currentOnCore c = x := ⟨_, rfl⟩
  rw [hCur] at hStep
  cases cur with
  | none => exact absurd hStep (by simp)
  | some signaler =>
    simp only at hStep
    obtain ⟨ntfn?, hNtfn⟩ : ∃ x, st.getNotification? notificationId = x := ⟨_, rfl⟩
    rw [hNtfn] at hStep
    cases ntfn? with
    | none =>
      -- PR #872 review: the target gate refuses before any policy read, so an
      -- `.ok` outcome is impossible on this arm.
      simp only at hStep
      split at hStep <;> exact absurd (congrArg Prod.snd hStep) (by simp)
    | some ntfn =>
      simp only at hStep
      obtain ⟨plan, hPlan⟩ : ∃ p, declassifiedSignalPlan ctx declPolicy notificationId
          (declassificationActorOf ctx signaler).domain st = p := ⟨_, rfl⟩
      rw [hPlan] at hStep
      cases plan with
      | error e => exact absurd hStep (by simp)
      | ok records =>
        simp only at hStep
        obtain ⟨pair, hPair⟩ : ∃ p, notificationSignalBoundOnCore notificationId badge c st = p :=
          ⟨_, rfl⟩
        rw [hPair] at hStep
        obtain ⟨st1, res⟩ := pair
        cases res with
        | error e => exact absurd hStep (by simp)
        | ok sgi' =>
          simp only at hStep
          obtain ⟨rec, hRec⟩ : ∃ r, recordDeclassifiedHops c
              (declassificationActorOf ctx signaler) records st1 = r := ⟨_, rfl⟩
          rw [hRec] at hStep
          cases rec with
          | none => exact absurd hStep (by simp)
          | some st2 =>
            simp only [Prod.mk.injEq, Except.ok.injEq] at hStep
            obtain ⟨hSt2, hSgi⟩ := hStep
            subst hSt2; subst hSgi
            refine ⟨signaler, records, hCur, hPlan, ?_, ?_⟩
            · rw [hPair]
            · rw [hPair]; exact hRec

-- ============================================================================
-- §6  WS-SM SM9.C.1 — what the records become
-- ============================================================================

/-- WS-SM SM9.C.1: **what the appended entries are** — one per record, in record
order, each carrying this transition's actor, this core and the kernel's own
basis.

The correspondence `declassifiedSignal_no_invented_edge` and
`declassifiedSignal_audits_actual_destination` both read: an appended entry's
flow endpoints and target are some planned record's, and nothing else was
appended. -/
theorem recordDeclassifiedHopsFrom_appended (c : CoreId) (actor : DeclassificationActor)
    (records : List DeclassifiedHopRecord) :
    ∀ (tags : DeclassificationTaint) (st st' : SystemState),
      recordDeclassifiedHopsFrom c actor tags records st = some st' →
      ∃ appended : DeclassificationAuditLog,
        st'.declassificationAuditLog = st.declassificationAuditLog ++ appended ∧
        appended.length = records.length ∧
        (∀ e ∈ appended, ∃ r ∈ records,
          e.srcDomain = r.srcDomain ∧ e.dstDomain = r.dstDomain ∧ e.targetObject = r.target) ∧
        (∀ e ∈ appended, e.actor = actor ∧ e.originatingCore = c ∧
          e.authorizationBasis = .policyRule) := by
  induction records with
  | nil => intro tags st st' h; cases h; exact ⟨[], by simp, rfl, by simp, by simp⟩
  | cons r rest ih =>
    intro tags st st' h
    obtain ⟨-, hRest⟩ := recordDeclassifiedHopsFrom_cons c actor tags r rest st st' h
    obtain ⟨appended, hApp, hLen, hCorr, hFields⟩ := ih _ _ st' hRest
    refine ⟨declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st
              :: appended, ?_, by simp [hLen], ?_, ?_⟩
    · simp only [hApp, List.append_assoc, List.cons_append, List.nil_append]
    · intro e hMem
      rcases List.mem_cons.mp hMem with rfl | hMem'
      · exact ⟨r, List.mem_cons_self, rfl, rfl, rfl⟩
      · obtain ⟨r', hr', hEq⟩ := hCorr e hMem'
        exact ⟨r', List.mem_cons_of_mem _ hr', hEq⟩
    · intro e hMem
      rcases List.mem_cons.mp hMem with rfl | hMem'
      · exact ⟨rfl, rfl, rfl⟩
      · exact hFields e hMem'

/-- WS-SM SM9.C.1: **what the appended entries are** — the entry-point form. -/
theorem recordDeclassifiedHops_appended (c : CoreId) (actor : DeclassificationActor)
    (records : List DeclassifiedHopRecord) (st st' : SystemState)
    (h : recordDeclassifiedHops c actor records st = some st') :
    ∃ appended : DeclassificationAuditLog,
      st'.declassificationAuditLog = st.declassificationAuditLog ++ appended ∧
      appended.length = records.length ∧
      (∀ e ∈ appended, ∃ r ∈ records,
        e.srcDomain = r.srcDomain ∧ e.dstDomain = r.dstDomain ∧ e.targetObject = r.target) ∧
      (∀ e ∈ appended, e.actor = actor ∧ e.originatingCore = c ∧
        e.authorizationBasis = .policyRule) :=
  recordDeclassifiedHopsFrom_appended c actor records _ st st' h

/-- WS-SM SM9.C.1: **the exact two-hop shape.**  Two records append two events in
hop order, and the second is stamped one past the first — the fact
`secondHopEvent_names_firstHop` rests on. -/
theorem recordDeclassifiedHops_two (c : CoreId) (actor : DeclassificationActor)
    (r₁ r₂ : DeclassifiedHopRecord) (st st' : SystemState)
    (h : recordDeclassifiedHops c actor [r₁, r₂] st = some st') :
    ∃ e₁ e₂ : DeclassificationEvent,
      st'.declassificationAuditLog = st.declassificationAuditLog ++ [e₁, e₂] ∧
      e₁ = declassifyStoreEvent c actor r₁.srcDomain r₁.dstDomain r₁.target st ∧
      e₂.srcDomain = r₂.srcDomain ∧ e₂.dstDomain = r₂.dstDomain ∧
      e₂.targetObject = r₂.target ∧ e₂.actor = actor ∧ e₂.originatingCore = c ∧
      e₂.authorizationBasis = .policyRule ∧
      e₂.timestamp = e₁.timestamp + 1 ∧
      declassificationEventNames e₂ e₁ = true := by
  obtain ⟨-, hRest⟩ := recordDeclassifiedHopsFrom_cons c actor
    (declassificationActorTaint actor st) r₁ [r₂] st st' h
  obtain ⟨-, hRest'⟩ := recordDeclassifiedHopsFrom_cons c actor
    ((declassificationActorTaint actor st).insert
      (st.declassificationAuditEpoch + st.declassificationAuditLog.length)) r₂ []
    { st with declassificationAuditLog := st.declassificationAuditLog ++
        [declassifyStoreEvent c actor r₁.srcDomain r₁.dstDomain r₁.target st] } st' hRest
  refine ⟨declassifyStoreEvent c actor r₁.srcDomain r₁.dstDomain r₁.target st,
          declassifyStoreEventWithTags c actor r₂.srcDomain r₂.dstDomain r₂.target
            ((declassificationActorTaint actor st).insert
              (st.declassificationAuditEpoch + st.declassificationAuditLog.length))
            { st with declassificationAuditLog := st.declassificationAuditLog ++
                [declassifyStoreEvent c actor r₁.srcDomain r₁.dstDomain r₁.target st] },
          ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hFinal : st' = { st with declassificationAuditLog :=
        (st.declassificationAuditLog ++
          [declassifyStoreEvent c actor r₁.srcDomain r₁.dstDomain r₁.target st]) ++
          [declassifyStoreEventWithTags c actor r₂.srcDomain r₂.dstDomain r₂.target
            ((declassificationActorTaint actor st).insert
              (st.declassificationAuditEpoch + st.declassificationAuditLog.length))
            { st with declassificationAuditLog := st.declassificationAuditLog ++
                [declassifyStoreEvent c actor r₁.srcDomain r₁.dstDomain r₁.target st] }] } := by
      simpa using hRest'.symm
    rw [hFinal]; simp
  · show st.declassificationAuditEpoch +
        (st.declassificationAuditLog ++
          [declassifyStoreEvent c actor r₁.srcDomain r₁.dstDomain r₁.target st]).length =
      (st.declassificationAuditEpoch + st.declassificationAuditLog.length) + 1
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · show ((declassificationActorTaint actor st).insert
        (st.declassificationAuditEpoch + st.declassificationAuditLog.length)).contains
        (st.declassificationAuditEpoch + st.declassificationAuditLog.length) = true
    exact DeclassificationTaint.contains_insert_self _ _

-- ============================================================================
-- §7  WS-SM SM9.C.1 — what the plan authorizes
-- ============================================================================

/-- WS-SM SM9.C.1 (**no invented edge, at the plan**): every record the plan
produces names a domain pair `declassificationDecision` returned `.ok` for.

The half `declassifiedSignal_no_invented_edge` lifts to the trail.  Stated over
the *decision* rather than over the two policies separately, because the
decision is the single function `.declassify` and this transition share: an
edge in the trail is an edge some run of that function authorized. -/
theorem declassifiedSignalPlan_records_authorized (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) (st : SystemState) (records : List DeclassifiedHopRecord)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId actorDomain st = .ok records) :
    ∀ r ∈ records, declassificationDecision ctx declPolicy r.srcDomain r.dstDomain = .ok () := by
  unfold declassifiedSignalPlan at hPlan
  obtain ⟨a1, hA1⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy .callerToNotification
      actorDomain (ctx.objectDomainOf notificationId) = a := ⟨_, rfl⟩
  rw [hA1] at hPlan
  cases a1 with
  | error e => exact absurd hPlan (by simp)
  | ok hop1 =>
    have hHop1 : ∀ r ∈ declassifiedHopRecords hop1 actorDomain
        (ctx.objectDomainOf notificationId) notificationId,
        declassificationDecision ctx declPolicy r.srcDomain r.dstDomain = .ok () := by
      cases hop1 with
      | ordinary => intro r hMem; simp at hMem
      | declassified =>
        intro r hMem
        rcases List.mem_singleton.mp hMem with rfl
        exact declassifiedSignalHopAuthorization_declassified_authorized ctx declPolicy
          .callerToNotification _ _ hA1
    obtain ⟨recv, hRecv⟩ : ∃ x, declassifiedSignalReceiver? st notificationId = x := ⟨_, rfl⟩
    rw [hRecv] at hPlan
    cases recv with
    | none =>
      simp only [Except.ok.injEq] at hPlan
      subst hPlan; exact hHop1
    | some receiver =>
      simp only at hPlan
      obtain ⟨a2, hA2⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy
          .notificationToReceiver (ctx.objectDomainOf notificationId)
          (ctx.threadDomainOf receiver) = a := ⟨_, rfl⟩
      rw [hA2] at hPlan
      cases a2 with
      | error e => exact absurd hPlan (by simp)
      | ok hop2 =>
        simp only [Except.ok.injEq] at hPlan
        subst hPlan
        intro r hMem
        rcases List.mem_append.mp hMem with h1 | h2
        · exact hHop1 r h1
        · cases hop2 with
          | ordinary => simp at h2
          | declassified =>
            rcases List.mem_singleton.mp h2 with rfl
            exact declassifiedSignalHopAuthorization_declassified_authorized ctx declPolicy
              .notificationToReceiver _ _ hA2

/-- WS-SM SM9.C.1: **each planned record is one of the two hop shapes** — the
caller releasing into the notification, or the notification releasing into the
resolved receiver.  There is no third. -/
theorem declassifiedSignalPlan_record_shape (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) (st : SystemState) (records : List DeclassifiedHopRecord)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId actorDomain st = .ok records) :
    ∀ r ∈ records,
      (r.srcDomain = actorDomain ∧ r.dstDomain = ctx.objectDomainOf notificationId ∧
        r.target = notificationId) ∨
      (∃ receiver, declassifiedSignalReceiver? st notificationId = some receiver ∧
        r.srcDomain = ctx.objectDomainOf notificationId ∧
        r.dstDomain = ctx.threadDomainOf receiver ∧ r.target = receiver.toObjId) := by
  unfold declassifiedSignalPlan at hPlan
  obtain ⟨a1, hA1⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy .callerToNotification
      actorDomain (ctx.objectDomainOf notificationId) = a := ⟨_, rfl⟩
  rw [hA1] at hPlan
  cases a1 with
  | error e => exact absurd hPlan (by simp)
  | ok hop1 =>
    have hHop1 : ∀ r ∈ declassifiedHopRecords hop1 actorDomain
        (ctx.objectDomainOf notificationId) notificationId,
        r.srcDomain = actorDomain ∧ r.dstDomain = ctx.objectDomainOf notificationId ∧
          r.target = notificationId := by
      cases hop1 with
      | ordinary => intro r hMem; simp at hMem
      | declassified =>
        intro r hMem
        rcases List.mem_singleton.mp hMem with rfl
        exact ⟨rfl, rfl, rfl⟩
    obtain ⟨recv, hRecv⟩ : ∃ x, declassifiedSignalReceiver? st notificationId = x := ⟨_, rfl⟩
    rw [hRecv] at hPlan
    cases recv with
    | none =>
      simp only [Except.ok.injEq] at hPlan
      subst hPlan
      exact fun r hr => Or.inl (hHop1 r hr)
    | some receiver =>
      simp only at hPlan
      obtain ⟨a2, hA2⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy
          .notificationToReceiver (ctx.objectDomainOf notificationId)
          (ctx.threadDomainOf receiver) = a := ⟨_, rfl⟩
      rw [hA2] at hPlan
      cases a2 with
      | error e => exact absurd hPlan (by simp)
      | ok hop2 =>
        simp only [Except.ok.injEq] at hPlan
        subst hPlan
        intro r hMem
        rcases List.mem_append.mp hMem with h1 | h2
        · exact Or.inl (hHop1 r h1)
        · cases hop2 with
          | ordinary => simp at h2
          | declassified =>
            rcases List.mem_singleton.mp h2 with rfl
            exact Or.inr ⟨receiver, hRecv, rfl, rfl, rfl⟩

/-- WS-SM SM9.C.1: every planned record's **source** is a domain the labeling
assigns — the acting subject's on hop 1, the notification's on hop 2. -/
theorem declassifiedSignalPlan_record_sources (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (signaler : SeLe4n.ThreadId) (st : SystemState) (records : List DeclassifiedHopRecord)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId
      (ctx.threadDomainOf signaler) st = .ok records) :
    ∀ r ∈ records, labelingAssignedDomain ctx r.srcDomain := by
  intro r hr
  rcases declassifiedSignalPlan_record_shape ctx declPolicy notificationId
    (ctx.threadDomainOf signaler) st records hPlan r hr with h1 | ⟨receiver, -, h2, -, -⟩
  · rw [h1.1]
    exact labelingAssignedDomain_thread ctx signaler
  · rw [h2]
    exact labelingAssignedDomain_object ctx notificationId

/-- WS-SM SM9.C.1: every planned record's **destination** likewise — the
notification's domain on hop 1, the receiver's on hop 2. -/
theorem declassifiedSignalPlan_record_destinations (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (signaler : SeLe4n.ThreadId) (st : SystemState) (records : List DeclassifiedHopRecord)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId
      (ctx.threadDomainOf signaler) st = .ok records) :
    ∀ r ∈ records, labelingAssignedDomain ctx r.dstDomain := by
  intro r hr
  rcases declassifiedSignalPlan_record_shape ctx declPolicy notificationId
    (ctx.threadDomainOf signaler) st records hPlan r hr with h1 | ⟨receiver, -, -, h2, -⟩
  · rw [h1.2.1]
    exact labelingAssignedDomain_object ctx notificationId
  · rw [h2]
    exact labelingAssignedDomain_thread ctx receiver

/-- WS-SM SM9.C.1 (**the resolved-destination gate, at the plan**): when the
signal resolves a receiver and neither policy permits the onward flow, the plan
refuses with the *receiver's own* discriminant. -/
theorem declassifiedSignalPlan_receiver_refused (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hFirst : ctx.policy.canFlow actorDomain (ctx.objectDomainOf notificationId) = true)
    (hRecv : declassifiedSignalReceiver? st notificationId = some receiver)
    (hDeny : ctx.policy.canFlow (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false)
    (hNoDecl : declPolicy.canDeclassify (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false) :
    declassifiedSignalPlan ctx declPolicy notificationId actorDomain st =
      .error .declassificationDeniedAtReceiver := by
  unfold declassifiedSignalPlan
  rw [declassifiedSignalHopAuthorization_ordinary ctx declPolicy .callerToNotification
    actorDomain (ctx.objectDomainOf notificationId) hFirst]
  simp only
  rw [hRecv]
  simp only
  rw [declassifiedSignalHopAuthorization_refused ctx declPolicy .notificationToReceiver
    (ctx.objectDomainOf notificationId) (ctx.threadDomainOf receiver) hDeny hNoDecl]
  rfl

/-- WS-SM SM9.C.1: **both hops ordinary ⇒ nothing to record.**  The plan of a
signal the base policy already permits end to end is empty, which is what makes
the transition degenerate to the ordinary checked signal. -/
theorem declassifiedSignalPlan_ordinary (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) (st : SystemState)
    (hFirst : ctx.policy.canFlow actorDomain (ctx.objectDomainOf notificationId) = true)
    (hSecond : ∀ receiver, declassifiedSignalReceiver? st notificationId = some receiver →
      ctx.policy.canFlow (ctx.objectDomainOf notificationId)
        (ctx.threadDomainOf receiver) = true) :
    declassifiedSignalPlan ctx declPolicy notificationId actorDomain st = .ok [] := by
  unfold declassifiedSignalPlan
  rw [declassifiedSignalHopAuthorization_ordinary ctx declPolicy .callerToNotification
    actorDomain (ctx.objectDomainOf notificationId) hFirst]
  simp only
  obtain ⟨recv, hRecv⟩ : ∃ x, declassifiedSignalReceiver? st notificationId = x := ⟨_, rfl⟩
  rw [hRecv]
  cases recv with
  | none => rfl
  | some receiver =>
    simp only
    rw [declassifiedSignalHopAuthorization_ordinary ctx declPolicy .notificationToReceiver
      (ctx.objectDomainOf notificationId) (ctx.threadDomainOf receiver) (hSecond receiver hRecv)]
    rfl

/-- WS-SM SM9.C.1: **both hops downgrades ⇒ two records**, in hop order, the
first naming the notification and the second the *receiver's own TCB*. -/
theorem declassifiedSignalPlan_two_hops (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hRecv : declassifiedSignalReceiver? st notificationId = some receiver)
    (hDeny₁ : ctx.policy.canFlow actorDomain (ctx.objectDomainOf notificationId) = false)
    (hDecl₁ : declPolicy.canDeclassify actorDomain (ctx.objectDomainOf notificationId) = true)
    (hDeny₂ : ctx.policy.canFlow (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false)
    (hDecl₂ : declPolicy.canDeclassify (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = true) :
    declassifiedSignalPlan ctx declPolicy notificationId actorDomain st =
      .ok [ { srcDomain := actorDomain, dstDomain := ctx.objectDomainOf notificationId,
              target := notificationId }
          , { srcDomain := ctx.objectDomainOf notificationId,
              dstDomain := ctx.threadDomainOf receiver, target := receiver.toObjId } ] := by
  unfold declassifiedSignalPlan
  rw [declassifiedSignalHopAuthorization_declassified ctx declPolicy .callerToNotification
    actorDomain (ctx.objectDomainOf notificationId) hDeny₁ hDecl₁]
  simp only
  rw [hRecv]
  simp only
  rw [declassifiedSignalHopAuthorization_declassified ctx declPolicy .notificationToReceiver
    (ctx.objectDomainOf notificationId) (ctx.threadDomainOf receiver) hDeny₂ hDecl₂]
  rfl

-- ============================================================================
-- §8  WS-SM SM9.C.1 — the headline properties
-- ============================================================================

/-- WS-SM SM9.C.1 (**the frame**): a successful declassifying signal commits the
ordinary bound signal's post-state with the trail extended, and **nothing
else**.

Everything downstream rests on this: the delivery semantics, the wake, the SGI
and the whole IPC invariant surface are the ones SM6.B already proved, because
the state is literally SM6.B's with one field replaced. -/
theorem notificationSignalDeclassifiedOnCore_frame (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind))
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    st' = { (notificationSignalBoundOnCore notificationId badge c st).1 with
      declassificationAuditLog := st'.declassificationAuditLog } := by
  obtain ⟨signaler, records, -, -, -, hRec⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  exact recordDeclassifiedHops_frame c (declassificationActorOf ctx signaler) records _ st' hRec

/-- WS-SM SM9.C.1 (**the badge crosses**): a successful declassifying signal's
object store is the ordinary bound signal's.

This is the whole point of the sub-phase, stated as an equation: the syscall
does not *simulate* a transfer the way `declassifyStore` does — it runs the real
delivery, so the badge lands where the ordinary signal would have put it and
every SM6.B delivery theorem applies verbatim. -/
theorem declassifiedSignal_delivers_badge (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind))
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    st'.objects = (notificationSignalBoundOnCore notificationId badge c st).1.objects ∧
    st'.scheduler = (notificationSignalBoundOnCore notificationId badge c st).1.scheduler ∧
    st'.machine = (notificationSignalBoundOnCore notificationId badge c st).1.machine ∧
    sgi = ((notificationSignalBoundOnCore notificationId badge c st).2).toOption.getD none := by
  obtain ⟨-, -, -, -, hSignal, -⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  have hFrame := notificationSignalDeclassifiedOnCore_frame ctx declPolicy notificationId badge
    c st st' sgi hStep
  refine ⟨by rw [hFrame], by rw [hFrame], by rw [hFrame], ?_⟩
  rw [show (notificationSignalBoundOnCore notificationId badge c st).2 = .ok sgi from
    congrArg Prod.snd hSignal]
  rfl

/-- WS-SM SM9.C.1 (**`declassifiedSignal_gates_resolved_receiver`**): a signal
whose *resolved destination* is authorized by neither policy is refused, with
the state untouched and the receiver hop's own discriminant.

The v0.31.73 leak, closed under declassification authority.  Without this the
caller's authorization to release into the notification would carry the badge
onward into a receiver no policy admits — and with a *stronger* warrant behind
it than the ordinary signal has, which is what makes the omission worse here
than there. -/
theorem declassifiedSignal_gates_resolved_receiver (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) (signaler receiver : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hFirst : ctx.policy.canFlow (ctx.threadDomainOf signaler)
      (ctx.objectDomainOf notificationId) = true)
    (hRecv : declassifiedSignalReceiver? st notificationId = some receiver)
    (hDeny : ctx.policy.canFlow (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false)
    (hNoDecl : declPolicy.canDeclassify (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false) :
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st, .error .declassificationDeniedAtReceiver) := by
  obtain ⟨ntfn, hNtfn⟩ :=
    declassifiedSignalReceiver?_some_notification st notificationId receiver hRecv
  exact notificationSignalDeclassifiedOnCore_plan_refused ctx declPolicy notificationId badge c
    st signaler ntfn _ hCur hNtfn
    (declassifiedSignalPlan_receiver_refused ctx declPolicy notificationId
      (declassificationActorOf ctx signaler).domain st receiver hFirst hRecv hDeny hNoDecl)

/-- WS-SM SM9.C.1 (**`declassifiedSignal_no_invented_edge`**): every event the
transition appends names a domain pair some `declassificationDecision` returned
`.ok` for — the trail reports no edge no policy authorized.

The property a *single* record for a two-hop delivery could not have: collapsing
`high → mid` and `mid → low` into one entry would put a direct `high → low` edge
in the trail, and no run of the decision ever returned `.ok` for that pair. -/
theorem declassifiedSignal_no_invented_edge (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind))
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ∃ appended : DeclassificationAuditLog,
      st'.declassificationAuditLog = st.declassificationAuditLog ++ appended ∧
      ∀ e ∈ appended,
        declassificationDecision ctx declPolicy e.srcDomain e.dstDomain = .ok () ∧
        e.originatingCore = c ∧ e.authorizationBasis = .policyRule := by
  obtain ⟨signaler, records, -, hPlan, hSignal, hRec⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  obtain ⟨appended, hApp, -, hCorr, hFields⟩ :=
    recordDeclassifiedHops_appended c (declassificationActorOf ctx signaler) records _ st' hRec
  have hTrailEq := notificationSignalBoundOnCore_declassificationAuditLog_eq notificationId
    badge c st
  refine ⟨appended, by rw [hApp, hTrailEq], fun e hMem => ?_⟩
  obtain ⟨r, hr, hSrc, hDst, -⟩ := hCorr e hMem
  obtain ⟨-, hCore, hBasis⟩ := hFields e hMem
  refine ⟨?_, hCore, hBasis⟩
  rw [hSrc, hDst]
  exact declassifiedSignalPlan_records_authorized ctx declPolicy notificationId
    (declassificationActorOf ctx signaler).domain st records hPlan r hr


-- ============================================================================
-- §9  WS-SM SM9.C.1 — two authorizations, two records
-- ============================================================================

/-- WS-SM SM9.C.1 (**`declassifiedSignal_audits_each_hop`**): a delivery whose
*both* hops are downgrades records **two** events, in hop order, sharing one
actor and one core — the first naming the notification, the second naming the
receiver's own TCB, and stamped one past the first.

The property a single collapsed record could not have.  On `high → mid` then
`mid → low` one entry must either drop a downgrade or invent the direct
`high → low` edge; two entries report exactly the two decisions that ran. -/
theorem declassifiedSignal_audits_each_hop (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind)) (signaler receiver : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hRecv : declassifiedSignalReceiver? st notificationId = some receiver)
    (hDeny₁ : ctx.policy.canFlow (ctx.threadDomainOf signaler)
      (ctx.objectDomainOf notificationId) = false)
    (hDecl₁ : declPolicy.canDeclassify (ctx.threadDomainOf signaler)
      (ctx.objectDomainOf notificationId) = true)
    (hDeny₂ : ctx.policy.canFlow (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false)
    (hDecl₂ : declPolicy.canDeclassify (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = true)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ∃ e₁ e₂ : DeclassificationEvent,
      st'.declassificationAuditLog = st.declassificationAuditLog ++ [e₁, e₂] ∧
      e₁.srcDomain = ctx.threadDomainOf signaler ∧
      e₁.dstDomain = ctx.objectDomainOf notificationId ∧
      e₁.targetObject = notificationId ∧
      e₂.srcDomain = ctx.objectDomainOf notificationId ∧
      e₂.dstDomain = ctx.threadDomainOf receiver ∧
      e₂.targetObject = receiver.toObjId ∧
      e₁.actor = declassificationActorOf ctx signaler ∧
      e₂.actor = declassificationActorOf ctx signaler ∧
      e₁.originatingCore = c ∧ e₂.originatingCore = c ∧
      e₂.timestamp = e₁.timestamp + 1 ∧
      declassificationEventNames e₂ e₁ = true := by
  obtain ⟨signaler', records, hCur', hPlan, -, hRec⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  rw [hCur] at hCur'
  have hEq : signaler' = signaler := (Option.some.inj hCur').symm
  rw [hEq] at hPlan hRec
  rw [declassifiedSignalPlan_two_hops ctx declPolicy notificationId
    (declassificationActorOf ctx signaler).domain st receiver hRecv hDeny₁ hDecl₁ hDeny₂ hDecl₂]
    at hPlan
  obtain rfl : records = _ := (Except.ok.inj hPlan).symm
  obtain ⟨e₁, e₂, hLog, hE₁, hSrc₂, hDst₂, hTgt₂, hAct₂, hCore₂, -, hTs, hNames⟩ :=
    recordDeclassifiedHops_two c (declassificationActorOf ctx signaler) _ _ _ st' hRec
  refine ⟨e₁, e₂, ?_, ?_, ?_, ?_, hSrc₂, hDst₂, hTgt₂, ?_, hAct₂, ?_, hCore₂, hTs, hNames⟩
  · rw [hLog, notificationSignalBoundOnCore_declassificationAuditLog_eq]
  · rw [hE₁]; rfl
  · rw [hE₁]; rfl
  · rw [hE₁]; rfl
  · rw [hE₁]; rfl
  · rw [hE₁]; rfl

/-- WS-SM SM9.C.1 (**`declassifiedSignal_audits_actual_destination`**): the
second hop's entry names the **resolved receiver**, not the notification the
capability pointed at.

Without it a monitor reading the trail knows a badge left a `mid` notification
and not which `low` subject received it — while the whole reason the second gate
exists is that the receiver is a sink in its own right. -/
theorem declassifiedSignal_audits_actual_destination (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind)) (signaler receiver : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hRecv : declassifiedSignalReceiver? st notificationId = some receiver)
    (hDeny₁ : ctx.policy.canFlow (ctx.threadDomainOf signaler)
      (ctx.objectDomainOf notificationId) = false)
    (hDecl₁ : declPolicy.canDeclassify (ctx.threadDomainOf signaler)
      (ctx.objectDomainOf notificationId) = true)
    (hDeny₂ : ctx.policy.canFlow (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false)
    (hDecl₂ : declPolicy.canDeclassify (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = true)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ∃ e ∈ st'.declassificationAuditLog,
      e.targetObject = receiver.toObjId ∧ e.dstDomain = ctx.threadDomainOf receiver ∧
      e.srcDomain = ctx.objectDomainOf notificationId ∧ e.originatingCore = c := by
  obtain ⟨e₁, e₂, hLog, -, -, -, hSrc₂, hDst₂, hTgt₂, -, -, -, hCore₂, -⟩ :=
    declassifiedSignal_audits_each_hop ctx declPolicy notificationId badge c st st' sgi
      signaler receiver hCur hRecv hDeny₁ hDecl₁ hDeny₂ hDecl₂ hStep
  refine ⟨e₂, ?_, hTgt₂, hDst₂, hSrc₂, hCore₂⟩
  rw [hLog]
  exact List.mem_append_right _ (by simp)

/-- WS-SM SM9.C.1 (**`secondHopEvent_names_firstHop`**, at the linkage the tree
has): the two entries a two-hop delivery records are a **linked chain** — the
first's destination is the second's source and the timestamps strictly increase,
so the detector the trail already carries does not reject the very scenario this
design exists to record.

The *causal* form — the second event naming the first through a snapshot of the
actor's taint — needs `predecessorTags`, which is SM9.D.13a's field and
deliberately not invented here: a field no producer could set is the
unwired-structure shape CLAUDE.md forbids.  What SM9.C owes and delivers is that
the chain the transition writes is one `declassificationChainLinked` accepts. -/
theorem secondHopEvent_names_firstHop (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind)) (signaler receiver : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hRecv : declassifiedSignalReceiver? st notificationId = some receiver)
    (hDeny₁ : ctx.policy.canFlow (ctx.threadDomainOf signaler)
      (ctx.objectDomainOf notificationId) = false)
    (hDecl₁ : declPolicy.canDeclassify (ctx.threadDomainOf signaler)
      (ctx.objectDomainOf notificationId) = true)
    (hDeny₂ : ctx.policy.canFlow (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false)
    (hDecl₂ : declPolicy.canDeclassify (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = true)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ∃ e₁ e₂ : DeclassificationEvent,
      st'.declassificationAuditLog = st.declassificationAuditLog ++ [e₁, e₂] ∧
      e₁.dstDomain = e₂.srcDomain ∧ e₁.timestamp < e₂.timestamp := by
  obtain ⟨e₁, e₂, hLog, -, hDst₁, -, hSrc₂, -, -, -, -, -, -, hTs⟩ :=
    declassifiedSignal_audits_each_hop ctx declPolicy notificationId badge c st st' sgi
      signaler receiver hCur hRecv hDeny₁ hDecl₁ hDeny₂ hDecl₂ hStep
  exact ⟨e₁, e₂, hLog, by rw [hDst₁, hSrc₂], by omega⟩

/-- WS-SM SM9.C.1 (**`secondHop_actor_differs_from_flowSource`**): the two
identities genuinely separate.

A two-hop delivery's second entry has the *notification's* domain as its source
and the *signalling subject's* as its actor, and there are states where those
differ — which is why SM8.C's `attributionFromRunningSubject` had to be restated
over the actor.  Read the other way: recording the second event's source as the
actor's domain would assert a `high → low` edge no decision returned. -/
theorem secondHop_actor_differs_from_flowSource (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind)) (signaler receiver : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hRecv : declassifiedSignalReceiver? st notificationId = some receiver)
    (hDeny₁ : ctx.policy.canFlow (ctx.threadDomainOf signaler)
      (ctx.objectDomainOf notificationId) = false)
    (hDecl₁ : declPolicy.canDeclassify (ctx.threadDomainOf signaler)
      (ctx.objectDomainOf notificationId) = true)
    (hDeny₂ : ctx.policy.canFlow (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false)
    (hDecl₂ : declPolicy.canDeclassify (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = true)
    (hDiffer : ctx.threadDomainOf signaler ≠ ctx.objectDomainOf notificationId)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ∃ e ∈ st'.declassificationAuditLog,
      e.actor.domain = ctx.threadDomainOf signaler ∧
      e.srcDomain = ctx.objectDomainOf notificationId ∧
      e.actor.domain ≠ e.srcDomain := by
  obtain ⟨e₁, e₂, hLog, -, -, -, hSrc₂, -, -, -, hAct₂, -, -, -⟩ :=
    declassifiedSignal_audits_each_hop ctx declPolicy notificationId badge c st st' sgi
      signaler receiver hCur hRecv hDeny₁ hDecl₁ hDeny₂ hDecl₂ hStep
  refine ⟨e₂, ?_, by rw [hAct₂], hSrc₂, ?_⟩
  · rw [hLog]; exact List.mem_append_right _ (by simp)
  · rw [hAct₂, hSrc₂]; exact hDiffer

-- ============================================================================
-- §10  WS-SM SM9.C.1 — the ordinary path, attribution, and the ordering
-- ============================================================================

/-- WS-SM SM9.C.1 (**the degenerate case, as an equation**): when the base policy
already permits both hops, the declassifying signal **is** the ordinary
cross-core bound signal, and records nothing.

Worth an equation rather than a remark: it says the syscall adds authority
exactly where the policy withholds it and adds *no* behaviour where the policy
does not, so a deployment cannot use it as a second, less-audited signal path. -/
theorem declassifiedSignal_ordinary_eq_signal (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) (signaler : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hFirst : ctx.policy.canFlow (ctx.threadDomainOf signaler)
      (ctx.objectDomainOf notificationId) = true)
    (hSecond : ∀ receiver, declassifiedSignalReceiver? st notificationId = some receiver →
      ctx.policy.canFlow (ctx.objectDomainOf notificationId)
        (ctx.threadDomainOf receiver) = true) :
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      notificationSignalBoundOnCore notificationId badge c st := by
  cases hN : st.getNotification? notificationId with
  | none =>
    -- PR #872 review: on a wrong-kind or absent target BOTH sides answer the
    -- ordinary signal's own recovery — the target gate is the ordinary
    -- signal's none-arm, decided through the typed accessor.
    have hL : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
        (if (st.objects[notificationId]?).isSome then (st, .error .invalidCapability)
         else (st, .error .objectNotFound)) := by
      rw [← getObjectType?_isSome_eq_raw]
      simp [notificationSignalDeclassifiedOnCore, hCur, hN]
    have hR : notificationSignalBoundOnCore notificationId badge c st =
        (if (st.objects[notificationId]?).isSome then (st, .error .invalidCapability)
         else (st, .error .objectNotFound)) := by
      unfold notificationSignalBoundOnCore boundDeliveryTarget? notificationSignalOnCore
      rw [hN]
    rw [hL, hR]
  | some ntfn =>
  rw [notificationSignalDeclassifiedOnCore_eq_of_subject ctx declPolicy notificationId badge c
    st signaler ntfn hCur hN,
    declassifiedSignalPlan_ordinary ctx declPolicy notificationId
      (declassificationActorOf ctx signaler).domain st hFirst hSecond]
  simp only
  obtain ⟨pair, hPair⟩ : ∃ p, notificationSignalBoundOnCore notificationId badge c st = p :=
    ⟨_, rfl⟩
  rw [hPair]
  obtain ⟨st1, res⟩ := pair
  cases res with
  | error e =>
    simp only
    have hFst : (notificationSignalBoundOnCore notificationId badge c st).1 = st1 :=
      congrArg Prod.fst hPair
    have hSnd : (notificationSignalBoundOnCore notificationId badge c st).2 = .error e :=
      congrArg Prod.snd hPair
    rw [← hFst,
      notificationSignalBoundOnCore_error_state notificationId badge c st e hSnd]
  | ok sgi => rfl

/-- WS-SM SM9.C.1: under a **deny-all** declassification policy every hop the
plan admits is `.ordinary` — a `.declassified` verdict is unreachable.

The step every unconfigured-deployment statement below travels along.  The
argument is the gate's own soundness (`…_declassified_authorized`): a
`.declassified` verdict means `declassificationDecision` succeeded, which
`declassificationDecision_ok_iff` says requires `canDeclassify = true`. -/
theorem declassifiedSignalHopAuthorization_default_ordinary (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (hop : DeclassifiedSignalHop)
    (srcDomain dstDomain : SecurityDomain) (auth : DeclassifiedHopAuthorization)
    (hDefault : declPolicy.canDeclassify = fun _ _ => false)
    (h : declassifiedSignalHopAuthorization ctx declPolicy hop srcDomain dstDomain = .ok auth) :
    auth = .ordinary := by
  cases auth with
  | ordinary => rfl
  | declassified =>
    have hDec := declassifiedSignalHopAuthorization_declassified_authorized ctx declPolicy hop
      srcDomain dstDomain h
    have := ((declassificationDecision_ok_iff ctx declPolicy srcDomain dstDomain).mp hDec).2
    rw [hDefault] at this
    exact absurd this (by simp)

/-- WS-SM SM9.C.1 (**the unconfigured deployment, at the plan**): with a deny-all
declassification policy an admitted plan is **empty**.

Not "the transition fails" — that would be false, and stating it would be the
kind of over-claim this workstream keeps correcting.  A signal whose hops the
base lattice already permits is an ordinary signal, and the honest property is
that an unconfigured deployment can perform *no downgrade*: the plan it admits
records nothing, so by `declassifiedSignal_never_unaudited`'s dual the trail
never grows and by `declassifiedSignal_ordinary_eq_signal` the transition is
literally `notificationSignalBoundOnCore`. -/
theorem declassifiedSignalPlan_default_empty (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) (st : SystemState)
    (records : List DeclassifiedHopRecord)
    (hDefault : declPolicy.canDeclassify = fun _ _ => false)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId actorDomain st = .ok records) :
    records = [] := by
  unfold declassifiedSignalPlan at hPlan
  obtain ⟨a₁, hA₁⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy
      .callerToNotification actorDomain (ctx.objectDomainOf notificationId) = a := ⟨_, rfl⟩
  rw [hA₁] at hPlan
  cases a₁ with
  | error e => exact absurd hPlan (by simp)
  | ok auth₁ =>
    have hOrd₁ := declassifiedSignalHopAuthorization_default_ordinary ctx declPolicy
      .callerToNotification actorDomain (ctx.objectDomainOf notificationId) auth₁ hDefault hA₁
    subst hOrd₁
    simp only at hPlan
    obtain ⟨recv, hRecv⟩ : ∃ x, declassifiedSignalReceiver? st notificationId = x := ⟨_, rfl⟩
    rw [hRecv] at hPlan
    cases recv with
    | none =>
      simp only [declassifiedHopRecords_ordinary] at hPlan
      exact (Except.ok.inj hPlan).symm
    | some receiver =>
      simp only at hPlan
      obtain ⟨a₂, hA₂⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy
          .notificationToReceiver (ctx.objectDomainOf notificationId)
          (ctx.threadDomainOf receiver) = a := ⟨_, rfl⟩
      rw [hA₂] at hPlan
      cases a₂ with
      | error e => exact absurd hPlan (by simp)
      | ok auth₂ =>
        have hOrd₂ := declassifiedSignalHopAuthorization_default_ordinary ctx declPolicy
          .notificationToReceiver (ctx.objectDomainOf notificationId)
          (ctx.threadDomainOf receiver) auth₂ hDefault hA₂
        subst hOrd₂
        simp only [declassifiedHopRecords_ordinary, List.append_nil] at hPlan
        exact (Except.ok.inj hPlan).symm

/-- WS-SM SM9.C.1 (**`declassifiedSignal_never_unaudited`**): every downgrade the
transition performs is recorded.

The two halves the fail-closed capacity bound buys: a hop the plan marked a
downgrade contributes an entry, and a delivery that could not record **all** of
its downgrades performs none of them — the state is the pre-state and the badge
does not move. -/
theorem declassifiedSignal_never_unaudited (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind)) (signaler : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ∃ records : List DeclassifiedHopRecord,
      declassifiedSignalPlan ctx declPolicy notificationId
        (declassificationActorOf ctx signaler).domain st = .ok records ∧
      ∃ appended : DeclassificationAuditLog,
        st'.declassificationAuditLog = st.declassificationAuditLog ++ appended ∧
        appended.length = records.length ∧
        ∀ e ∈ appended, e.actor = declassificationActorOf ctx signaler ∧
          e.originatingCore = c ∧ e.authorizationBasis = .policyRule := by
  obtain ⟨signaler', records, hCur', hPlan, -, hRec⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  rw [hCur] at hCur'
  have hEq : signaler' = signaler := (Option.some.inj hCur').symm
  rw [hEq] at hPlan hRec
  obtain ⟨appended, hApp, hLen, -, hFields⟩ :=
    recordDeclassifiedHops_appended c (declassificationActorOf ctx signaler) records _ st' hRec
  exact ⟨records, hPlan, appended,
    by rw [hApp, notificationSignalBoundOnCore_declassificationAuditLog_eq], hLen, hFields⟩

/-- WS-SM SM9.C.1 / SM9.C.8 (**an unconfigured deployment never downgrades**):
with `LabelingContext.declassificationPolicy` at its deny-all default, a
successful declassifying signal leaves the audit trail **unchanged**.

This is the fail-closed default in its exact form, and it is deliberately not
"the syscall fails".  The syscall is a *signal*: refusing it outright under the
default would mean an operator who never configured a declassification policy
cannot use the syscall at all, which is a usability claim rather than a security
one — and the security claim it would be mistaken for is this theorem.

Its contrapositive is what an auditor wants: a trail that grew is a trail whose
deployment configured a policy that authorized the growth.  Composed with
`declassifiedSignal_never_unaudited` it gives the full statement — every
downgrade is recorded, and under the default there are none. -/
theorem declassifiedSignal_default_policy_never_downgrades (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind))
    (hDefault : declPolicy.canDeclassify = fun _ _ => false)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    st'.declassificationAuditLog = st.declassificationAuditLog := by
  obtain ⟨signaler, records, hCur, hPlan, -, hRec⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  have hNil := declassifiedSignalPlan_default_empty ctx declPolicy notificationId
    (declassificationActorOf ctx signaler).domain st records hDefault hPlan
  subst hNil
  rw [recordDeclassifiedHops_nil] at hRec
  rw [← Option.some.inj hRec, notificationSignalBoundOnCore_declassificationAuditLog_eq]

/-- WS-SM SM9.C.8: the same fact one level up — an unconfigured deployment's
declassifying signal **is** the ordinary bound signal, state for state.

Stronger than the trail statement above and derived from a different route (the
plan is empty, so the record step is the identity), which is why both are worth
having: this one says the syscall is behaviourally indistinguishable from
`.notificationSignal`, so a deployment that has not configured a policy is not
running a second, differently-audited signal path. -/
theorem declassifiedSignal_default_policy_eq_signal (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind))
    (hDefault : declPolicy.canDeclassify = fun _ _ => false)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    notificationSignalBoundOnCore notificationId badge c st = (st', .ok sgi) := by
  obtain ⟨signaler, records, hCur, hPlan, hSignal, hRec⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  have hNil := declassifiedSignalPlan_default_empty ctx declPolicy notificationId
    (declassificationActorOf ctx signaler).domain st records hDefault hPlan
  subst hNil
  rw [recordDeclassifiedHops_nil] at hRec
  rw [hSignal, Option.some.inj hRec]

/-- WS-SM SM9.C.1 (**`attributionFromRunningSubject_over_actor`**): every entry
the transition records is **attributable** — its actor is the subject the
originating core was running, at the domain the labeling gives that subject.

SM8.C's rule, restated over the field that makes it true of a *two-hop* event.
Read on the second entry it says: the `mid → low` release was performed by the
`high` subject on core `c`, which is exactly what an auditor needs and exactly
what recording the actor's domain as the source would have destroyed. -/
theorem attributionFromRunningSubject_over_actor (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × SgiKind)) (signaler : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ∀ e ∈ st'.declassificationAuditLog, e ∉ st.declassificationAuditLog →
      declassificationEventAttributable ctx st' e := by
  obtain ⟨records, -, appended, hApp, -, hFields⟩ :=
    declassifiedSignal_never_unaudited ctx declPolicy notificationId badge c st st' sgi
      signaler hCur hStep
  have hCurEq : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
    rw [notificationSignalDeclassifiedOnCore_frame ctx declPolicy notificationId badge c st st'
      sgi hStep]
    exact notificationSignalBoundOnCore_currentOnCore_eq notificationId badge c st c
  intro e hMem hNew
  rw [hApp] at hMem
  rcases List.mem_append.mp hMem with hOld | hNewMem
  · exact absurd hOld hNew
  · obtain ⟨hActor, hCore, -⟩ := hFields e hNewMem
    refine ⟨?_, ?_⟩
    · rw [hCore, hActor]
      show declassificationSubjectOnCore st' c = some signaler
      unfold declassificationSubjectOnCore
      rw [hCurEq]; exact hCur
    · rw [hActor]

-- ============================================================================
-- §11  WS-SM SM9.C.3 / SM9.C.4 — the invariant surface
-- ============================================================================

/-! ## What the audit write costs the invariants, and what it does not

The declassifying signal is `notificationSignalBoundOnCore` followed by an audit
append, and the append writes exactly one `SystemState` field
(`recordDeclassifiedHops_frame`).  So every invariant that does **not read the
trail** transfers across the append definitionally, and the only new obligation
is the trail's own capacity bound.

That gives the section its shape: each result comes in two forms — an
**unconditional** one where the underlying signal's own theorem exists, and a
**transfer** one where it does not.  The one place the second form is needed is
`ipcInvariantFull` on the *bound-delivery* path: SM6.D closed the whole bundle
for `notificationSignalOnCore` and left the bound path's
`endpointQueueRemoveDual` per-conjunct suite as registered debt.  SM9.C does not
inherit that gap silently — it states the transfer, and instantiates it
unconditionally on the fall-through path where SM6.D's theorem applies. -/

/-- WS-SM SM9.C.4: the whole `proofLayerInvariantBundle` across the audit fold
at any accumulator — each append is a bounded trail write, and the SM8.C.8
carriage lemma does the rest. -/
theorem recordDeclassifiedHopsFrom_preserves_proofLayerInvariantBundle (c : CoreId)
    (actor : DeclassificationActor) (records : List DeclassifiedHopRecord) :
    ∀ (tags : DeclassificationTaint) (st st' : SystemState),
      Architecture.proofLayerInvariantBundle st →
      recordDeclassifiedHopsFrom c actor tags records st = some st' →
      Architecture.proofLayerInvariantBundle st' := by
  induction records with
  | nil => intro tags st st' hInv h; cases h; exact hInv
  | cons r rest ih =>
    intro tags st st' hInv h
    obtain ⟨hRoom, hRest⟩ := recordDeclassifiedHopsFrom_cons c actor tags r rest st st' h
    refine ih _ _ st' ?_ hRest
    refine Architecture.proofLayerInvariantBundle_setDeclassificationAuditLog st _ hInv ?_
    unfold auditLogBounded
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- WS-SM SM9.C.4: the audit fold carries the whole invariant bundle.

Unconditional in every conjunct but the sixteenth, which the checked append
establishes at each step — the shape SM8.C.9's live declassification already
uses, folded. -/
theorem recordDeclassifiedHops_preserves_proofLayerInvariantBundle (c : CoreId)
    (actor : DeclassificationActor) (records : List DeclassifiedHopRecord)
    (st st' : SystemState)
    (hInv : Architecture.proofLayerInvariantBundle st)
    (h : recordDeclassifiedHops c actor records st = some st') :
    Architecture.proofLayerInvariantBundle st' :=
  recordDeclassifiedHopsFrom_preserves_proofLayerInvariantBundle c actor records _ st st' hInv h

/-- WS-SM SM9.C.4: **the whole bundle across the declassifying signal**, given
that the delivery it wraps carries it.

The transfer half is the SM9.C content: the audit append preserves every
conjunct, the sixteenth by the capacity guard the fold applies at each entry.
The premise is SM6.B/SM6.D's obligation, not this transition's, and is stated
rather than assumed away. -/
theorem notificationSignalDeclassifiedOnCore_preserves_proofLayerInvariantBundle
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hSignalInv : Architecture.proofLayerInvariantBundle
      (notificationSignalBoundOnCore notificationId badge c st).1)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    Architecture.proofLayerInvariantBundle st' := by
  obtain ⟨signaler, records, -, -, -, hRec⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  exact recordDeclassifiedHops_preserves_proofLayerInvariantBundle c
    (declassificationActorOf ctx signaler) records _ st' hSignalInv hRec

/-- WS-SM SM9.C.4: the 16th conjunct on its own, **unconditionally** — the trail
the transition leaves is bounded whatever the delivery did, because every append
it makes is the checked one. -/
theorem notificationSignalDeclassifiedOnCore_preserves_auditLogBounded
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hBounded : auditLogBounded st.declassificationAuditLog)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    auditLogBounded st'.declassificationAuditLog := by
  obtain ⟨signaler, records, -, -, -, hRec⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  refine recordDeclassifiedHops_preserves_auditLogBounded c (declassificationActorOf ctx signaler)
    records _ st' ?_ hRec
  rw [notificationSignalBoundOnCore_declassificationAuditLog_eq]
  exact hBounded

/-- WS-SM SM9.C.4 / SM9.A.1a: the trail's timestamp discipline survives —
**both** entries of a two-hop delivery are stamped from the state they land in,
so the second is the first plus one and no timestamp is reused. -/
theorem notificationSignalDeclassifiedOnCore_preserves_trailWellFormed
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hWF : declassificationTrailWellFormed st = true)
    (hEpoch : ((notificationSignalBoundOnCore notificationId badge c st).1).declassificationAuditEpoch
      = st.declassificationAuditEpoch)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    declassificationTrailWellFormed st' = true := by
  obtain ⟨signaler, records, -, -, -, hRec⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  refine recordDeclassifiedHops_preserves_trailWellFormed c (declassificationActorOf ctx signaler)
    records _ st' ?_ hRec
  unfold declassificationTrailWellFormed at hWF ⊢
  rw [hEpoch, notificationSignalBoundOnCore_declassificationAuditLog_eq]
  exact hWF

/-- WS-SM SM9.C.3: the object-store integrity invariant, **unconditionally** —
the audit append writes no object, so this is SM6.B's theorem transported. -/
theorem notificationSignalDeclassifiedOnCore_preserves_objects_invExt
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    st'.objects.invExt := by
  obtain ⟨hObjects, -, -, -⟩ := declassifiedSignal_delivers_badge ctx declPolicy notificationId
    badge c st st' sgi hStep
  rw [hObjects]
  exact notificationSignalBoundOnCore_preserves_objects_invExt notificationId badge c st hObjInv

/-- WS-SM SM9.C.3: the IPC invariant, **unconditionally** — SM6.B proved it for
the bound-aware signal, and the audit append is object-store-transparent. -/
theorem notificationSignalDeclassifiedOnCore_preserves_ipcInvariant
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ipcInvariant st' := by
  obtain ⟨hObjects, -, -, -⟩ := declassifiedSignal_delivers_badge ctx declPolicy notificationId
    badge c st st' sgi hStep
  exact ipcInvariant_of_objects_eq hObjects
    (notificationSignalBoundOnCore_preserves_ipcInvariant notificationId badge c st hInv hObjInv)

/-- WS-SM SM9.C.3: **the whole twenty-conjunct IPC bundle, transferred.**

The audit append changes no object lookup and no scheduler slot, so a bundle
that holds of the delivery's post-state holds of the committed one.  The premise
is the delivery's own obligation — SM6.D's, discharged unconditionally on the
fall-through path below and registered debt on the bound-delivery path. -/
theorem notificationSignalDeclassifiedOnCore_ipcInvariantFull_transfer
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hSignalInv : ipcInvariantFull (notificationSignalBoundOnCore notificationId badge c st).1)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ipcInvariantFull st' := by
  obtain ⟨hObjects, hSched, -, -⟩ := declassifiedSignal_delivers_badge ctx declPolicy
    notificationId badge c st st' sgi hStep
  refine ipcInvariantFull_of_getElem_eq (fun oid => by rw [hObjects]) ?_ hSignalInv
  have hPsi := hSignalInv.passiveServerIdle
  unfold passiveServerIdle at hPsi ⊢
  intro tid tcb hTcb hUnbound hNotQ hNotCur
  exact hPsi tid tcb (by rw [← hObjects]; exact hTcb) hUnbound
    (by rw [← hSched]; exact hNotQ) (by rw [← hSched]; exact hNotCur)

/-- WS-SM SM9.C.3 (**the fall-through instance, unconditional**): off the
bound-delivery path the delivery *is* `notificationSignalOnCore`, whose whole
bundle SM6.D closed — so the declassifying signal carries it with no premise
about the delivery at all.

The waiter and badge-accumulation paths are the ones a deployment reaches
without a bound notification, which is every deployment that has not called
`.tcbBindNotification`. -/
theorem notificationSignalDeclassifiedOnCore_preserves_ipcInvariantFull_fallthrough
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hNoBound : boundDeliveryTarget? st notificationId = none)
    (hInv : ipcInvariantFull st) (hObjInv : st.objects.invExt)
    (hWtpmn' : blockedThreadsPendingMessageConsistent
      (notificationSignalOnCore notificationId badge c st).1)
    (hRCLRecip' : replyCallerLinkageReciprocal
      (notificationSignalOnCore notificationId badge c st).1)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ipcInvariantFull st' := by
  refine notificationSignalDeclassifiedOnCore_ipcInvariantFull_transfer ctx declPolicy
    notificationId badge c st st' sgi ?_ hStep
  rw [notificationSignalBoundOnCore_fallthrough_eq notificationId badge c st hNoBound]
  exact notificationSignalOnCore_preserves_ipcInvariantFull notificationId badge c st hInv
    hObjInv hWtpmn' hRCLRecip' hNWC hAllBudgetsNone

/-- WS-SM SM9.C.3: **the per-core bundle**, from the whole-bundle form and core
`c`'s passive slice — which the audit append leaves alone for the same reason
everything else does. -/
theorem notificationSignalDeclassifiedOnCore_ipcInvariantFull_perCore_transfer
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind)) (view : CoreId)
    (hSignalInv : ipcInvariantFull (notificationSignalBoundOnCore notificationId badge c st).1)
    (hSignalPsi : passiveServerIdle_perCore
      (notificationSignalBoundOnCore notificationId badge c st).1 view)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ipcInvariantFull_perCore st' view := by
  obtain ⟨hObjects, hSched, -, -⟩ := declassifiedSignal_delivers_badge ctx declPolicy
    notificationId badge c st st' sgi hStep
  refine ipcInvariantFull_perCore_of_full
    (notificationSignalDeclassifiedOnCore_ipcInvariantFull_transfer ctx declPolicy notificationId
      badge c st st' sgi hSignalInv hStep) ?_
  unfold passiveServerIdle_perCore at hSignalPsi ⊢
  intro tid tcb hTcb hUnbound hNotQ hNotCur
  refine hSignalPsi tid tcb ?_ hUnbound (by rw [← hSched]; exact hNotQ)
    (by rw [← hSched]; exact hNotCur)
  rw [SystemState.getTcb?] at hTcb ⊢
  rw [← hObjects]; exact hTcb

-- ============================================================================
-- §12  WS-SM SM9.C.1 — the ordering, the trail invariants, the dispatch
-- ============================================================================

/-- WS-SM SM9.C.1 (**the SM8.C.9 ordering, kept**): a caller whose downgrade the
*policy* refuses learns **nothing about the trail's occupancy** — the error it
gets is the policy's, on a full trail exactly as on an empty one.

The plan is computed before the trail is touched, so the two states in the
statement may differ in trail length by any amount.  Without this ordering,
occupancy — a function of how many authorized downgrades *other* subjects
performed — would be readable by every caller of a syscall the policy refuses,
which is CC-8 widened from declassifying subjects to all of them. -/
theorem declassifiedSignal_denied_before_capacity (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st₁ st₂ : SystemState) (signaler : SeLe4n.ThreadId)
    (ntfn₁ ntfn₂ : Notification) (e : KernelError)
    (hCur₁ : st₁.scheduler.currentOnCore c = some signaler)
    (hCur₂ : st₂.scheduler.currentOnCore c = some signaler)
    (hNtfn₁ : st₁.getNotification? notificationId = some ntfn₁)
    (hNtfn₂ : st₂.getNotification? notificationId = some ntfn₂)
    (hSameRecv : declassifiedSignalReceiver? st₁ notificationId =
      declassifiedSignalReceiver? st₂ notificationId)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId
      (declassificationActorOf ctx signaler).domain st₁ = .error e) :
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st₁ =
      (st₁, .error e) ∧
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st₂ =
      (st₂, .error e) := by
  have hPlan₂ : declassifiedSignalPlan ctx declPolicy notificationId
      (declassificationActorOf ctx signaler).domain st₂ = .error e := by
    unfold declassifiedSignalPlan at hPlan ⊢
    rw [← hSameRecv]
    exact hPlan
  exact ⟨notificationSignalDeclassifiedOnCore_plan_refused ctx declPolicy notificationId badge c
      st₁ signaler ntfn₁ e hCur₁ hNtfn₁ hPlan,
    notificationSignalDeclassifiedOnCore_plan_refused ctx declPolicy notificationId badge c
      st₂ signaler ntfn₂ e hCur₂ hNtfn₂ hPlan₂⟩

/-- WS-SM SM9.C.1: the transition establishes the trail's **actor** invariant —
both hops share one actor, read off the state, so every entry it writes carries
that subject's own domain. -/
theorem notificationSignalDeclassifiedOnCore_preserves_trailActors
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind)) (signaler : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hActors : auditTrailActorsFromLabeling ctx st.declassificationAuditLog)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    auditTrailActorsFromLabeling ctx st'.declassificationAuditLog := by
  obtain ⟨-, -, appended, hApp, -, hFields⟩ :=
    declassifiedSignal_never_unaudited ctx declPolicy notificationId badge c st st' sgi
      signaler hCur hStep
  intro e hMem
  rw [hApp] at hMem
  rcases List.mem_append.mp hMem with hOld | hNew
  · exact hActors e hOld
  · obtain ⟨hActor, -, -⟩ := hFields e hNew
    rw [hActor]

/-- WS-SM SM9.C.1: and the **source** invariant — hop 1's source is the acting
subject's domain and hop 2's is the notification's, so both are domains the
labeling assigns.

Hop 2 is exactly why `auditTrailSourcesFromLabeling` had to generalise from
"some *subject's* domain" to "some *entity's*": an intermediate object's domain
need be no thread's. -/
theorem notificationSignalDeclassifiedOnCore_preserves_trailSources
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind)) (signaler : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hSources : auditTrailSourcesFromLabeling ctx st.declassificationAuditLog)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    auditTrailSourcesFromLabeling ctx st'.declassificationAuditLog := by
  obtain ⟨signaler', records, hCur', hPlan, -, hRec⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  rw [hCur] at hCur'
  have hEq : signaler' = signaler := (Option.some.inj hCur').symm
  rw [hEq] at hPlan hRec
  obtain ⟨appended, hApp, -, hCorr, -⟩ :=
    recordDeclassifiedHops_appended c (declassificationActorOf ctx signaler) records _ st' hRec
  rw [notificationSignalBoundOnCore_declassificationAuditLog_eq] at hApp
  intro e hMem
  rw [hApp] at hMem
  rcases List.mem_append.mp hMem with hOld | hNew
  · exact hSources e hOld
  · obtain ⟨r, hr, hSrc, -, -⟩ := hCorr e hNew
    rw [hSrc]
    exact declassifiedSignalPlan_record_sources ctx declPolicy notificationId signaler st
      records hPlan r hr

/-- WS-SM SM9.C.1: and the **destination** invariant — hop 1's destination is the
notification's domain and hop 2's is the receiver's, both labeling-assigned. -/
theorem notificationSignalDeclassifiedOnCore_preserves_trailDestinations
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind)) (signaler : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hDests : auditTrailDestinationsFromLabeling ctx st.declassificationAuditLog)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    auditTrailDestinationsFromLabeling ctx st'.declassificationAuditLog := by
  obtain ⟨signaler', records, hCur', hPlan, -, hRec⟩ :=
    notificationSignalDeclassifiedOnCore_ok_inv ctx declPolicy notificationId badge c st st'
      sgi hStep
  rw [hCur] at hCur'
  have hEq : signaler' = signaler := (Option.some.inj hCur').symm
  rw [hEq] at hPlan hRec
  obtain ⟨appended, hApp, -, hCorr, -⟩ :=
    recordDeclassifiedHops_appended c (declassificationActorOf ctx signaler) records _ st' hRec
  rw [notificationSignalBoundOnCore_declassificationAuditLog_eq] at hApp
  intro e hMem
  rw [hApp] at hMem
  rcases List.mem_append.mp hMem with hOld | hNew
  · exact hDests e hOld
  · obtain ⟨r, hr, -, hDst, -⟩ := hCorr e hNew
    rw [hDst]
    exact declassifiedSignalPlan_record_destinations ctx declPolicy notificationId signaler st
      records hPlan r hr

/-- WS-SM SM9.C.2: the live dispatch **is** the transition at the caller's own
core — definitional, so every §5–§12 theorem is a statement about the live arm
with `c := determineExecutingCore st signaler`. -/
@[simp] theorem notificationSignalDeclassifiedCrossCoreDispatch_eq
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (st : SystemState) :
    notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy notificationId signaler
      badge st =
      notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge
        (determineExecutingCore st signaler) st := rfl


-- ============================================================================
-- §13  WS-SM SM9.C.1 / SM9.C.8 — the failed hop, and the enforcement families
-- ============================================================================

/-- WS-SM SM9.C.1: a hop authorization's error is always **that hop's own**
discriminant — the gate discards the decision's error and reports the hop, so
the two hops stay distinguishable at the refusal ledger whatever the decision
returned. -/
theorem declassifiedSignalHopAuthorization_error_refusal (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (hop : DeclassifiedSignalHop)
    (srcDomain dstDomain : SecurityDomain) (e : KernelError)
    (h : declassifiedSignalHopAuthorization ctx declPolicy hop srcDomain dstDomain =
      .error e) :
    e = hop.refusal := by
  unfold declassifiedSignalHopAuthorization at h
  split at h
  · exact absurd h (by simp)
  · obtain ⟨dec, hDec⟩ : ∃ d, declassificationDecision ctx declPolicy srcDomain dstDomain = d :=
      ⟨_, rfl⟩
    rw [hDec] at h
    cases dec with
    | error e' => exact (Except.error.inj h).symm
    | ok u => cases u; exact absurd h (by simp)

/-- WS-SM SM9.C.1 (**`refusalRecord_names_failed_hop`, the transition half**): a
plan refused with the *receiver's* discriminant had **resolved a receiver** —
the second-hop gate is the only producer of `.declassificationDeniedAtReceiver`,
and it runs only under `declassifiedSignalReceiver? st notificationId = some r`.

This is what makes the seam's re-resolution meaningful: the receiver a hop-2
refusal is about exists in the pre-state, by the same function the seam
re-runs. -/
theorem declassifiedSignalPlan_deniedAtReceiver_resolves (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) (st : SystemState)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId actorDomain st =
      .error .declassificationDeniedAtReceiver) :
    ∃ receiver, declassifiedSignalReceiver? st notificationId = some receiver := by
  unfold declassifiedSignalPlan at hPlan
  obtain ⟨a1, hA1⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy .callerToNotification
      actorDomain (ctx.objectDomainOf notificationId) = a := ⟨_, rfl⟩
  rw [hA1] at hPlan
  cases a1 with
  | error e =>
    have hE : e = DeclassifiedSignalHop.callerToNotification.refusal :=
      declassifiedSignalHopAuthorization_error_refusal ctx declPolicy .callerToNotification
        actorDomain (ctx.objectDomainOf notificationId) e hA1
    subst hE
    exact absurd (Except.error.inj hPlan) (by decide)
  | ok hop1 =>
    simp only at hPlan
    obtain ⟨recv, hRecv⟩ : ∃ x, declassifiedSignalReceiver? st notificationId = x := ⟨_, rfl⟩
    rw [hRecv] at hPlan
    cases recv with
    | none => exact absurd hPlan (by simp)
    | some receiver => exact ⟨receiver, hRecv⟩

/-- WS-SM SM9.C.8 (**the `_denied_preserves_state` family member**): every
refusal of the declassifying signal returns the **pre-state exactly** — the
idle-core arm, both hop gates, the delivery's own failure, and the fail-closed
capacity refusal alike.

One statement rather than one per refusal mode, and stronger than the family's
`Kernel`-monad members can be: the transition is total, so "changes nothing" is
an equation on the returned state rather than the absence of a committed one. -/
theorem notificationSignalDeclassifiedOnCore_denied_preserves_state
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (e : KernelError)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .error e)) :
    st' = st := by
  unfold notificationSignalDeclassifiedOnCore at hStep
  obtain ⟨cur, hCur⟩ : ∃ x, st.scheduler.currentOnCore c = x := ⟨_, rfl⟩
  rw [hCur] at hStep
  cases cur with
  | none => exact (congrArg Prod.fst hStep).symm
  | some signaler =>
    simp only at hStep
    obtain ⟨ntfn?, hNtfn⟩ : ∃ x, st.getNotification? notificationId = x := ⟨_, rfl⟩
    rw [hNtfn] at hStep
    cases ntfn? with
    | none =>
      -- PR #872 review: the target gate's two refusals return the pre-state
      -- like every other arm.
      simp only at hStep
      split at hStep <;> exact (congrArg Prod.fst hStep).symm
    | some ntfn =>
      simp only at hStep
      obtain ⟨plan, hPlan⟩ : ∃ p, declassifiedSignalPlan ctx declPolicy notificationId
          (declassificationActorOf ctx signaler).domain st = p := ⟨_, rfl⟩
      rw [hPlan] at hStep
      cases plan with
      | error e' => exact (congrArg Prod.fst hStep).symm
      | ok records =>
        simp only at hStep
        obtain ⟨pair, hPair⟩ : ∃ p, notificationSignalBoundOnCore notificationId badge c st = p :=
          ⟨_, rfl⟩
        rw [hPair] at hStep
        obtain ⟨st1, res⟩ := pair
        cases res with
        | error e' => exact (congrArg Prod.fst hStep).symm
        | ok sgi =>
          simp only at hStep
          obtain ⟨rec, hRec⟩ : ∃ r, recordDeclassifiedHops c
              (declassificationActorOf ctx signaler) records st1 = r := ⟨_, rfl⟩
          rw [hRec] at hStep
          cases rec with
          | none => exact (congrArg Prod.fst hStep).symm
          | some st2 => exact absurd (congrArg Prod.snd hStep) (by simp)

/-- WS-SM SM9.C.8 (**the `enforcement_sufficiency_*` family member**): the
declassifying signal does exactly one of **six** things, and nothing else.

`enforcement_sufficiency_declassify` is a trichotomy because `.declassify`'s
transfer is simulated; here the delivery is *real*, which adds its own failure
mode, the actor is state-resolved, which adds the idle-core refusal, and — PR
#872 review — the target is validated before any policy read, which adds the
wrong-kind/absent refusal:

1. an idle core cannot attribute a downgrade, so it refuses (`.illegalState`);
2. a target that is not a live notification refuses with the ordinary
   signal's own recovery — `.invalidCapability` present-but-wrong-kind,
   `.objectNotFound` absent — before any policy is consulted, so an invalid
   capability is never a policy oracle
   (`notificationSignalDeclassifiedOnCore_invalid_target_policy_blind`);
3. a plan either hop's gate refuses is returned verbatim, with that hop's own
   discriminant, the state untouched;
4. a delivery failure of the underlying bound signal is returned verbatim —
   this transition invents no discriminant for it and performs no partial
   commit;
5. an authorized plan whose records do not all fit refuses fail-closed with
   `.auditLogCapacityExceeded`, delivering nothing — recording one hop of a
   two-hop delivery is not among the outcomes;
6. otherwise the delivery commits with exactly the planned records appended.

Arms 3 and 4 are stated as "the error, verbatim" so a future refusal cannot be
silently remapped onto an existing discriminant. -/
theorem enforcement_sufficiency_declassifySignal
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) :
    (st.scheduler.currentOnCore c = none ∧
       notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
         (st, .error .illegalState)) ∨
    (∃ signaler, st.scheduler.currentOnCore c = some signaler ∧
       st.getNotification? notificationId = none ∧
       (((st.getObjectType? notificationId).isSome ∧
           notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
             (st, .error .invalidCapability)) ∨
        (st.getObjectType? notificationId = none ∧
           notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
             (st, .error .objectNotFound)))) ∨
    (∃ signaler e, st.scheduler.currentOnCore c = some signaler ∧
       declassifiedSignalPlan ctx declPolicy notificationId
         (declassificationActorOf ctx signaler).domain st = .error e ∧
       notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
         (st, .error e)) ∨
    (∃ signaler records e, st.scheduler.currentOnCore c = some signaler ∧
       declassifiedSignalPlan ctx declPolicy notificationId
         (declassificationActorOf ctx signaler).domain st = .ok records ∧
       (notificationSignalBoundOnCore notificationId badge c st).2 = .error e ∧
       notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
         (st, .error e)) ∨
    (∃ signaler records sgi, st.scheduler.currentOnCore c = some signaler ∧
       declassifiedSignalPlan ctx declPolicy notificationId
         (declassificationActorOf ctx signaler).domain st = .ok records ∧
       (notificationSignalBoundOnCore notificationId badge c st).2 = .ok sgi ∧
       recordDeclassifiedHops c (declassificationActorOf ctx signaler) records
         (notificationSignalBoundOnCore notificationId badge c st).1 = none ∧
       notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
         (st, .error .auditLogCapacityExceeded)) ∨
    (∃ signaler records sgi st2, st.scheduler.currentOnCore c = some signaler ∧
       declassifiedSignalPlan ctx declPolicy notificationId
         (declassificationActorOf ctx signaler).domain st = .ok records ∧
       (notificationSignalBoundOnCore notificationId badge c st).2 = .ok sgi ∧
       recordDeclassifiedHops c (declassificationActorOf ctx signaler) records
         (notificationSignalBoundOnCore notificationId badge c st).1 = some st2 ∧
       notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
         (st2, .ok sgi)) := by
  obtain ⟨cur, hCur⟩ : ∃ x, st.scheduler.currentOnCore c = x := ⟨_, rfl⟩
  cases cur with
  | none =>
    exact Or.inl ⟨hCur, notificationSignalDeclassifiedOnCore_no_subject ctx declPolicy
      notificationId badge c st hCur⟩
  | some signaler =>
    obtain ⟨ntfn?, hN⟩ : ∃ x, st.getNotification? notificationId = x := ⟨_, rfl⟩
    cases ntfn? with
    | none =>
      refine Or.inr (Or.inl ⟨signaler, hCur, hN, ?_⟩)
      by_cases hTy : (st.getObjectType? notificationId).isSome
      · refine Or.inl ⟨hTy, ?_⟩
        simp [notificationSignalDeclassifiedOnCore, hCur, hN, hTy]
      · refine Or.inr ⟨Option.not_isSome_iff_eq_none.mp hTy, ?_⟩
        simp [notificationSignalDeclassifiedOnCore, hCur, hN, hTy]
    | some ntfn =>
      have hEq := notificationSignalDeclassifiedOnCore_eq_of_subject ctx declPolicy
        notificationId badge c st signaler ntfn hCur hN
      obtain ⟨plan, hPlan⟩ : ∃ p, declassifiedSignalPlan ctx declPolicy notificationId
          (declassificationActorOf ctx signaler).domain st = p := ⟨_, rfl⟩
      rw [hPlan] at hEq
      cases plan with
      | error e => exact Or.inr (Or.inr (Or.inl ⟨signaler, e, hCur, hPlan, hEq⟩))
      | ok records =>
        simp only at hEq
        obtain ⟨pair, hPair⟩ : ∃ p, notificationSignalBoundOnCore notificationId badge c st = p :=
          ⟨_, rfl⟩
        rw [hPair] at hEq
        obtain ⟨st1, res⟩ := pair
        have hFst : (notificationSignalBoundOnCore notificationId badge c st).1 = st1 :=
          congrArg Prod.fst hPair
        have hSnd : (notificationSignalBoundOnCore notificationId badge c st).2 = res :=
          congrArg Prod.snd hPair
        cases res with
        | error e =>
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨signaler, records, e, hCur, hPlan, hSnd, hEq⟩)))
        | ok sgi =>
          simp only at hEq
          obtain ⟨rec, hRec⟩ : ∃ r, recordDeclassifiedHops c
              (declassificationActorOf ctx signaler) records st1 = r := ⟨_, rfl⟩
          rw [hRec] at hEq
          cases rec with
          | none =>
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨signaler, records, sgi, hCur, hPlan, hSnd, ?_, hEq⟩))))
            rw [hFst]; exact hRec
          | some st2 =>
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨signaler, records, sgi, st2, hCur, hPlan, hSnd, ?_, hEq⟩))))
            rw [hFst]; exact hRec


-- ============================================================================
-- §14  WS-SM SM9.C.1 — the plain-waiter gate: no-op when admitted, honest
--       about what its refusal discloses (PR #872 review)
-- ============================================================================

/-- WS-SM SM9.C.1 (PR #872 review): **for a receiver the base policy admits,
the receiver refusal is unreachable** — an error out of the plan is the
*caller's* hop, never the receiver's.

This is the checked-deployment case: the checked wait gate admits a plain
waiter only when `notification → waiter` already flows, so on every state that
discipline produces the second hop is `.ordinary` and this transition's
receiver gate is a no-op.  The refusal — and the one-bit disclosure it carries
— is confined to states built outside the checked discipline (an
unchecked-wait admission, or a post-admission relabeling), where the
alternative to refusing is delivering a freshly-downgraded badge to a receiver
no policy authorized. -/
theorem declassifiedSignalPlan_admitted_receiver_error_is_first_hop
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (actorDomain : SecurityDomain) (st : SystemState)
    (receiver : SeLe4n.ThreadId) (e : KernelError)
    (hRecv : declassifiedSignalReceiver? st notificationId = some receiver)
    (hFlow : ctx.policy.canFlow (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = true)
    (hErr : declassifiedSignalPlan ctx declPolicy notificationId actorDomain st = .error e) :
    e = KernelError.declassificationDenied := by
  unfold declassifiedSignalPlan at hErr
  obtain ⟨a1, hA1⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy .callerToNotification
      actorDomain (ctx.objectDomainOf notificationId) = a := ⟨_, rfl⟩
  rw [hA1] at hErr
  cases a1 with
  | error e' =>
    have hE : e' = DeclassifiedSignalHop.callerToNotification.refusal :=
      declassifiedSignalHopAuthorization_error_refusal ctx declPolicy .callerToNotification
        actorDomain (ctx.objectDomainOf notificationId) e' hA1
    have : e = e' := (Except.error.inj hErr).symm
    rw [this, hE]; rfl
  | ok hop1 =>
    simp only at hErr
    rw [hRecv] at hErr
    simp only at hErr
    rw [declassifiedSignalHopAuthorization_ordinary ctx declPolicy .notificationToReceiver
      (ctx.objectDomainOf notificationId) (ctx.threadDomainOf receiver) hFlow] at hErr
    exact absurd hErr (by simp)

/-- WS-SM SM9.C.1 (PR #872 review, **the disclosure, exhibited**): with the
caller's own hop authorized, the plan's verdict depends on the resolved
receiver — success with one record when nobody is waiting, the receiver's
refusal when a denied-domain plain waiter is.

A caller holding a write capability on the notification therefore reads one
bit of queue state off the ABI outcome.  Kept, and stated rather than hidden,
because every alternative is worse: delivering ungated re-opens the v0.31.73
badge leak with downgrade authority behind it; parking the badge past a queued
waiter invents notification states the ordinary machinery never produces and
breaks the frame equality the whole invariant transfer rests on; and refusing
both ways kills the delivery the phase exists to perform.  The same class of
refusal has disclosed *bound*-receiver state on the ordinary checked path
since v0.31.73 — this widens it to plain waiters exactly where the data it
protects is a freshly-downgraded badge, and only on states the checked wait
discipline does not produce
(`declassifiedSignalPlan_admitted_receiver_error_is_first_hop`). -/
theorem declassifiedSignalPlan_outcome_depends_on_receiver
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (actorDomain : SecurityDomain)
    (s₁ s₂ : SystemState) (receiver : SeLe4n.ThreadId)
    (hRecv₁ : declassifiedSignalReceiver? s₁ notificationId = none)
    (hRecv₂ : declassifiedSignalReceiver? s₂ notificationId = some receiver)
    (hDeny₁ : ctx.policy.canFlow actorDomain (ctx.objectDomainOf notificationId) = false)
    (hDecl₁ : declPolicy.canDeclassify actorDomain (ctx.objectDomainOf notificationId) = true)
    (hDeny₂ : ctx.policy.canFlow (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false)
    (hNoDecl₂ : declPolicy.canDeclassify (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false) :
    declassifiedSignalPlan ctx declPolicy notificationId actorDomain s₁ =
      .ok [{ srcDomain := actorDomain, dstDomain := ctx.objectDomainOf notificationId,
             target := notificationId }] ∧
    declassifiedSignalPlan ctx declPolicy notificationId actorDomain s₂ =
      .error .declassificationDeniedAtReceiver := by
  constructor
  · unfold declassifiedSignalPlan
    rw [declassifiedSignalHopAuthorization_declassified ctx declPolicy .callerToNotification
      actorDomain (ctx.objectDomainOf notificationId) hDeny₁ hDecl₁]
    simp only
    rw [hRecv₁]
    rfl
  · unfold declassifiedSignalPlan
    rw [declassifiedSignalHopAuthorization_declassified ctx declPolicy .callerToNotification
      actorDomain (ctx.objectDomainOf notificationId) hDeny₁ hDecl₁]
    simp only
    rw [hRecv₂]
    simp only
    rw [declassifiedSignalHopAuthorization_refused ctx declPolicy .notificationToReceiver
      (ctx.objectDomainOf notificationId) (ctx.threadDomainOf receiver) hDeny₂ hNoDecl₂]
    rfl


-- ============================================================================
-- §15  WS-SM SM9.C.1 — the target gate (PR #872 review, round 2)
-- ============================================================================

/-- WS-SM SM9.C.1 (PR #872 review): a present-but-wrong-kind target answers the
ordinary signal's own `.invalidCapability` — before any policy is consulted. -/
theorem notificationSignalDeclassifiedOnCore_wrong_kind (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) (signaler : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hNone : st.getNotification? notificationId = none)
    (hSome : (st.getObjectType? notificationId).isSome = true) :
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st, .error .invalidCapability) := by
  simp [notificationSignalDeclassifiedOnCore, hCur, hNone, hSome]

/-- WS-SM SM9.C.1 (PR #872 review): an absent target answers the ordinary
signal's own `.objectNotFound` — before any policy is consulted. -/
theorem notificationSignalDeclassifiedOnCore_absent_target (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) (signaler : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hNoType : st.getObjectType? notificationId = none) :
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st, .error .objectNotFound) := by
  have hNone : st.getNotification? notificationId = none := by
    unfold SystemState.getObjectType? at hNoType
    unfold SystemState.getNotification?
    cases hRaw : st.objects[notificationId]? with
    | none => rfl
    | some obj => rw [hRaw] at hNoType; exact absurd hNoType (by simp)
  simp [notificationSignalDeclassifiedOnCore, hCur, hNone, hNoType]

/-- WS-SM SM9.C.1 (PR #872 review, **the finding's own theorem — an invalid
target is never a policy oracle**): on a target that is not a live
notification, the transition's outcome is a function of the object store
alone — identical under **every** pair of labeling contexts and declassification
policies.

Before the target gate ran first, a caller holding a writable capability to a
non-notification object read its own hop-1 verdict off the error discriminant
(`.declassificationDenied` when the plan refused, `.invalidCapability` when it
admitted the flow far enough to reach the delivery's typed lookup) — the
result for an invalid capability depended on otherwise unrelated label-policy
state.  Now nothing policy-dependent is evaluated on this path at all: the
sibling `.declassify` has always validated its target first
(`declassifyObjectFromCore` reads `getObjectType?` before
`authorizeDeclassificationOnCore`), and the two entry points now share the
discipline. -/
theorem notificationSignalDeclassifiedOnCore_invalid_target_policy_blind
    (ctx₁ ctx₂ : GenericLabelingContext) (declPolicy₁ declPolicy₂ : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState)
    (hNone : st.getNotification? notificationId = none) :
    notificationSignalDeclassifiedOnCore ctx₁ declPolicy₁ notificationId badge c st =
      notificationSignalDeclassifiedOnCore ctx₂ declPolicy₂ notificationId badge c st := by
  unfold notificationSignalDeclassifiedOnCore
  cases hCur : st.scheduler.currentOnCore c with
  | none => rfl
  | some signaler => rw [hNone]

end SeLe4n.Kernel
