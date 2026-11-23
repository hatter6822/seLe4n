/-
Copyright (c) 2025 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license.

WS-SM SM9.C: the data-carrying declassification.

`.declassify` (SM8.C.9) authorizes a downgrade and records it; **no bytes
cross**.  This module is the transition that moves the data: a notification
signal whose badge is permitted to cross a label boundary the base policy
denies, on the SM6.B cross-core signal path, with one audit entry when the
downgrade is authorized.

## One authorization: the caller's

The transition gates the one flow a policy decides — `signaler → notification`.
The onward delivery `notification → receiver` needs no gate of its own, because
every receiver a signal can resolve is at the notification's label: a thread
reaches a notification's queue or its binding only through the two-way
`notificationFlowGate` (the checked wait and bind), which admits exactly equal
labels, and the boot refuses a configuration that queues or binds a thread of
another label (`notificationLabelsCoherent`).  On such a state the onward flow
is the identity flow, which the base lattice permits and which is no
downgrade (`declassifiedSignalReceiver_flow_ordinary_of_coherent`).  The
second-hop gate this transition used to run, and the refusal it reported, were
deleted for that reason: on the states the kernel produces they could never
fire.

An ordinary hop — one the base policy already permits — is *not* a
declassification and records nothing.  That is why a signal whose hop is
ordinary is exactly the ordinary checked signal
(`declassifiedSignal_ordinary_eq_signal`): the syscall adds authority where the
policy withholds it and adds nothing where the policy does not.

## What a footprint does not do

Naming the receiver's TCB in the effect footprint says *where the writes land*.
It carries no authorization: the receiver is admissible because the wait and
bind gates put only threads of the notification's own label there, not because
the footprint names it (`footprint_receiver_at_notification_label`).
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
  unfold storeTcbQueueLinks modifyTcb at h
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
  unfold storeTcbQueueLinks modifyTcb at h
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
  unfold storeTcbIpcStateAndMessage modifyTcb at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i pair hStore
      simp only [Except.ok.injEq] at h
      subst h
      exact storeObject_declassificationAuditLog_eq st _ _ ((), pair) hStore

/-- `storeTcbIpcStateAndMessage_declassificationAuditLog_eq` for the store of a thread a signal wakes (`storeTcbSignalWoken`). -/
theorem storeTcbSignalWoken_declassificationAuditLog_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (h : storeTcbSignalWoken st tid badge = .ok st') :
    st'.declassificationAuditLog = st.declassificationAuditLog := by
  unfold storeTcbSignalWoken modifyTcb at h
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
  unfold storeTcbReceiveComplete modifyTcb at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i pair hStore
      simp only [Except.ok.injEq] at h
      subst h
      exact storeObject_declassificationAuditLog_eq st _ _ ((), pair) hStore

/-- `storeTcbReceiveComplete_declassificationAuditLog_eq` for the store of a thread a signal wakes (`storeTcbSignalBoundWoken`). -/
theorem storeTcbSignalBoundWoken_declassificationAuditLog_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (h : storeTcbSignalBoundWoken st tid badge = .ok st') :
    st'.declassificationAuditLog = st.declassificationAuditLog := by
  unfold storeTcbSignalBoundWoken modifyTcb at h
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
  have h := enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c tid
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

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
    cases hT : ntfn.waitHead with
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
        cases hMsg : storeTcbSignalWoken p1.2 pair badge with
        | error e => rfl
        | ok st2 =>
          simp only []
          rw [wakeThread_declassificationAuditLog_eq _ pair executingCore,
            detachNtfnHead_declassificationAuditLog,
            storeTcbSignalWoken_declassificationAuditLog_eq p1.2 st2 pair _ hMsg,
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
      cases hStore : storeTcbSignalBoundWoken st1 t badge with
      | error e => rfl
      | ok st2 =>
        simp only []
        rw [wakeThread_declassificationAuditLog_eq st2 t executingCore,
          storeTcbSignalBoundWoken_declassificationAuditLog_eq st1 st2 t _ hStore,
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
    cases hT : ntfn.waitHead with
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
        cases hMsg : storeTcbSignalWoken p1.2 pair badge with
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
      cases hStore : storeTcbSignalBoundWoken u.2 t badge with
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
    cases hT : ntfn.waitHead with
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
        cases hMsg : storeTcbSignalWoken p1.2 pair badge with
        | error e => rfl
        | ok st2 =>
          simp only []
          show ((wakeThread _ pair executingCore).1).scheduler.currentOnCore c = _
          unfold wakeThread
          rw [enqueueRunnableOnCore_currentOnCore _ _ pair c, detachNtfnHead_scheduler,
            storeTcbSignalWoken_scheduler_eq p1.2 st2 pair _ hMsg,
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
      cases hStore : storeTcbSignalBoundWoken st1 t badge with
      | error e => rfl
      | ok st2 =>
        simp only []
        show ((wakeThread st2 t executingCore).1).scheduler.currentOnCore c = _
        unfold wakeThread
        rw [enqueueRunnableOnCore_currentOnCore st2 _ t c,
          storeTcbSignalBoundWoken_scheduler_eq st1 st2 t _ hStore,
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
the signal the waiter is dequeued and woken.  Inlined (WS-ZA), so a caller
matches the receiver where it resolves it and no `some` is built. -/
@[inline] def declassifiedSignalReceiver? (st : SystemState) (notificationId : SeLe4n.ObjId) :
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
-- §2  WS-SM SM9.C.1 — the hop's authorization
-- ============================================================================

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
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain) :
    Except KernelError DeclassifiedHopAuthorization :=
  if ctx.policy.canFlow srcDomain dstDomain then
    .ok .ordinary
  else
    match declassificationDecision ctx declPolicy srcDomain dstDomain with
    | .ok () => .ok .declassified
    | .error _ => .error .declassificationDenied

/-- WS-SM SM9.C.1: a hop the base policy permits is ordinary. -/
theorem declassifiedSignalHopAuthorization_ordinary (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (hFlow : ctx.policy.canFlow srcDomain dstDomain = true) :
    declassifiedSignalHopAuthorization ctx declPolicy srcDomain dstDomain = .ok .ordinary := by
  simp [declassifiedSignalHopAuthorization, hFlow]

/-- WS-SM SM9.C.1: a hop the base policy denies and the declassification policy
authorizes is a **downgrade**. -/
theorem declassifiedSignalHopAuthorization_declassified (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (hDeny : ctx.policy.canFlow srcDomain dstDomain = false)
    (hDecl : declPolicy.canDeclassify srcDomain dstDomain = true) :
    declassifiedSignalHopAuthorization ctx declPolicy srcDomain dstDomain =
      .ok .declassified := by
  simp [declassifiedSignalHopAuthorization, hDeny, declassificationDecision, hDecl]

/-- WS-SM SM9.C.1: a hop neither policy permits is refused with
`.declassificationDenied`. -/
theorem declassifiedSignalHopAuthorization_refused (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (hDeny : ctx.policy.canFlow srcDomain dstDomain = false)
    (hNoDecl : declPolicy.canDeclassify srcDomain dstDomain = false) :
    declassifiedSignalHopAuthorization ctx declPolicy srcDomain dstDomain =
      .error .declassificationDenied := by
  simp [declassifiedSignalHopAuthorization, hDeny, declassificationDecision, hNoDecl]

/-- WS-SM SM9.C.1 (**the soundness of a `.declassified` verdict**): the gate says
"downgrade" exactly when `declassificationDecision` authorized it — the same two
checks `.declassify` runs, on the same function. -/
theorem declassifiedSignalHopAuthorization_declassified_authorized
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (h : declassifiedSignalHopAuthorization ctx declPolicy srcDomain dstDomain =
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
    (srcDomain dstDomain : SecurityDomain)
    (h : declassifiedSignalHopAuthorization ctx declPolicy srcDomain dstDomain =
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
-- §3  WS-SM SM9.C.1 — the record obligation
-- ============================================================================

/-- WS-SM SM9.C.1: **one authorized downgrade the transition owes a record
for** — the flow's two endpoints and the object the badge lands in.

A list of these is what the commit below folds into the trail.  Deliberately not
a list of whole `DeclassificationEvent`s: the timestamp is the trail's own
shape, so an event can only be built against the state it is appended to. -/
structure DeclassifiedHopRecord where
  /-- The domain the badge is released *from* on this hop. -/
  srcDomain : SecurityDomain
  /-- The domain it is released *into*. -/
  dstDomain : SecurityDomain
  /-- The object that receives it: the notification the capability names. -/
  target : SeLe4n.ObjId
  deriving Repr, DecidableEq

/-- WS-SM SM9.C.1: the record a hop owes — `[]` for an ordinary flow, one entry
for a downgrade. -/
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
the recursion propagates that refusal, so a list with more records than the
trail has room for records *none* of them and the operation fails.  Recording a
prefix would leave a downgrade the kernel performed and did not record, which is
the failure the fail-closed bound exists to exclude. -/
def recordDeclassifiedHopsFrom (c : CoreId) (actor : DeclassificationActor)
    (tags : TaintWords) :
    List DeclassifiedHopRecord → SystemState → Option SystemState
  | [], st => some st
  | r :: rest, st =>
      match recordDeclassificationChecked st.declassificationAudit
          (declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st) with
      | none => none
      | some log' =>
          recordDeclassifiedHopsFrom c actor
            (TaintWords.join tags
              (TaintWords.singletonWords
                (st.declassificationAuditEpoch + st.declassificationAudit.length)))
            rest { st with declassificationAudit := log' }

/-- WS-SM SM9.C.1 / SM9.D.13a: **append the owed records to the trail**, each
stamped against the state it lands in and each carrying the acting subject's
provenance.

The first record's snapshot is the subject's taint at the pre-state; each later
record's is that snapshot **extended with the timestamps the earlier records
were allocated**, so the entries of one list form a *causal* chain
(`declassificationChainCausal`) rather than merely a syntactically linked one.
The declassifying signal's plan holds at most one record, so on that path the
snapshot is the pre-state's.

Fail-closed as a whole: `recordDeclassificationChecked` refuses at capacity and
the recursion propagates that refusal, so a list with more records than the
trail has room for records *none* of them and the operation fails. -/
def recordDeclassifiedHops (c : CoreId) (actor : DeclassificationActor)
    (records : List DeclassifiedHopRecord) (st : SystemState) : Option SystemState :=
  recordDeclassifiedHopsFrom c actor (declassificationActorWords actor st) records st

/-- WS-SM SM9.C.1: no records, no change. -/
@[simp] theorem recordDeclassifiedHopsFrom_nil (c : CoreId) (actor : DeclassificationActor)
    (tags : TaintWords) (st : SystemState) :
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
    (tags : TaintWords)
    (r : DeclassifiedHopRecord) (rest : List DeclassifiedHopRecord) (st st' : SystemState)
    (h : recordDeclassifiedHopsFrom c actor tags (r :: rest) st = some st') :
    st.declassificationAuditLog.length < maxDeclassificationAuditEntries ∧
    recordDeclassifiedHopsFrom c actor
      (TaintWords.join tags
        (TaintWords.singletonWords
          (st.declassificationAuditEpoch + st.declassificationAudit.length))) rest
      { st with declassificationAudit :=
          (st.declassificationAudit.append
            (declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st)) }
      = some st' := by
  unfold recordDeclassifiedHopsFrom at h
  obtain ⟨rec, hRec⟩ : ∃ x, recordDeclassificationChecked st.declassificationAudit
      (declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st) = x :=
    ⟨_, rfl⟩
  rw [hRec] at h
  cases rec with
  | none => exact absurd h (by simp)
  | some log' =>
    have hRoom : st.declassificationAuditLog.length < maxDeclassificationAuditEntries :=
      (recordDeclassificationChecked_isSome_iff _ _).mp (by rw [hRec]; rfl)
    have hLog' : log' = st.declassificationAudit.append
        (declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st) := by
      rw [recordDeclassificationChecked_eq_record _ _ hRoom] at hRec
      exact (Option.some.inj hRec).symm
    subst hLog'
    exact ⟨hRoom, h⟩

/-- WS-SM SM9.C.1: recording writes **only** the trail.

Every field but the audit ring `declassificationAudit` is carried through untouched, which
is what lets the whole invariant surface of the underlying signal transfer
across the audit write. -/
theorem recordDeclassifiedHopsFrom_frame (c : CoreId) (actor : DeclassificationActor)
    (records : List DeclassifiedHopRecord) :
    ∀ (tags : TaintWords) (st st' : SystemState),
      recordDeclassifiedHopsFrom c actor tags records st = some st' →
      st' = { st with declassificationAudit := st'.declassificationAudit } := by
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
    st' = { st with declassificationAudit := st'.declassificationAudit } :=
  recordDeclassifiedHopsFrom_frame c actor records _ st st' h

/-- WS-SM SM9.C.1: recording **grows** the trail by exactly one entry per record,
appending in hop order. -/
theorem recordDeclassifiedHopsFrom_log (c : CoreId) (actor : DeclassificationActor)
    (records : List DeclassifiedHopRecord) :
    ∀ (tags : TaintWords) (st st' : SystemState),
      recordDeclassifiedHopsFrom c actor tags records st = some st' →
      ∃ appended : DeclassificationAuditLog,
        st'.declassificationAuditLog = st.declassificationAuditLog ++ appended ∧
        appended.length = records.length := by
  induction records with
  | nil => intro tags st st' h; cases h; exact ⟨[], by simp, rfl⟩
  | cons r rest ih =>
    intro tags st st' h
    obtain ⟨hRoom, hRest⟩ := recordDeclassifiedHopsFrom_cons c actor tags r rest st st' h
    obtain ⟨appended, hApp, hLen⟩ := ih _ _ st' hRest
    have hMid : ({ st with declassificationAudit := (st.declassificationAudit.append
        (declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st)) } :
          SystemState).declassificationAuditLog =
        st.declassificationAuditLog ++
          [declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st] :=
      AuditRing.toList_append _ _ hRoom
    refine ⟨declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st
              :: appended, ?_, ?_⟩
    · rw [hApp, hMid]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
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

/-- WS-SM SM9.C.1 / SM9.A.1a: recording preserves the trail's timestamp
discipline at any accumulator — each append stamps `epoch + length` against the
state it lands in, which is what `declassifyStoreEventWithTags` computes. -/
theorem recordDeclassifiedHopsFrom_preserves_trailWellFormed (c : CoreId)
    (actor : DeclassificationActor) (records : List DeclassifiedHopRecord) :
    ∀ (tags : TaintWords) (st st' : SystemState),
      declassificationTrailWellFormed st = true →
      recordDeclassifiedHopsFrom c actor tags records st = some st' →
      declassificationTrailWellFormed st' = true := by
  induction records with
  | nil => intro tags st st' hWF h; cases h; exact hWF
  | cons r rest ih =>
    intro tags st st' hWF h
    obtain ⟨hRoom, hRest⟩ := recordDeclassifiedHopsFrom_cons c actor tags r rest st st' h
    refine ih _ _ st' ?_ hRest
    unfold declassificationTrailWellFormed at hWF ⊢
    show auditTimestampsFrom (st.declassificationAudit.append _).epoch
      (st.declassificationAudit.append _).toList = true
    rw [AuditRing.toList_append _ _ hRoom, AuditRing.epoch_append]
    exact recordDeclassification_preserves_timestampsFrom _ _ _ hWF (by simp; rfl)

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
is authorized at all — decided from the acting subject's domain and the
notification's, before any write.

Factored out of the transition so the gate and the audit are one computation
read twice (the §3.5 "defined once" discipline): the commit below folds exactly
this list, and `declassifiedSignal_no_invented_edge` reads it too, so a record
the gate authorized and the commit did not write is not expressible.

**One hop.**  The onward delivery into the resolved receiver is not gated here:
every receiver a signal resolves is at the notification's label (the two-way
wait and bind gates, and the boot's `notificationLabelsCoherent`), so that flow
is the identity flow and owes neither an authorization nor a record
(`declassifiedSignalReceiver_flow_ordinary_of_coherent`).  The plan therefore
reads no state. -/
def declassifiedSignalPlan (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) :
    Except KernelError (List DeclassifiedHopRecord) :=
  match declassifiedSignalHopAuthorization ctx declPolicy actorDomain
          (ctx.objectDomainOf notificationId) with
  | .error e => .error e
  | .ok hop =>
      .ok (declassifiedHopRecords hop actorDomain (ctx.objectDomainOf notificationId)
        notificationId)

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
3. **Decide the hop**, before any capacity check.  Deciding first confines the
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
          if (st.getObjectType? notificationId).isSome then (st, .error (.invalidCapability 0))
          else (st, .error .objectNotFound)
      | some _ =>
          let actor := declassificationActorOf ctx signaler
          match declassifiedSignalPlan ctx declPolicy notificationId actor.domain with
          | .error e => (st, .error e)
          | .ok records =>
              match notificationSignalBoundOnCore notificationId badge c st with
              | (_, .error e) => (st, .error e)
              | (st1, .ok sgi) =>
                  match recordDeclassifiedHops c actor records st1 with
                  | none => (st, .error .auditLogCapacityExceeded)
                  | some st2 => (st2, .ok sgi)

/-- WS-SM SM9.C.2: the cross-core dispatch the live arm calls — the transition
at the core the syscall trapped on (threaded from the entry point), exactly as
SM6.B's `notificationSignalBoundCrossCoreDispatch` does.

WS-SX SX8.2: seL4-MCS `sendSignal` then donates the notification's context to
the thread the signal woke, under the checked kernel's context-label check read
through this context (`donateToSignalledFlowingGeneric`, the donation the
checked `sendSignalOnCoreFlowing` makes): the declassification downgrades the
signal's own hop, never the lending of another thread's reply stack.  It runs once the audit record is committed, so a
refused record donates nothing and the downgrade stays fail-closed; the record
writes the audit trail alone, which the donation neither reads nor writes, so
the state a program sees is the checked signal's followed by the record.

Deliberately **not** a boot-pinned sibling: the actor and the wake target are
both per-core facts, and a `bootCoreId` form would be the defect the per-core
routing gate exists to catch. -/
def notificationSignalDeclassifiedCrossCoreDispatch (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  match notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge
      executingCore st with
  | (st', .ok sgi) => (donateToSignalledFlowingGeneric ctx st st' notificationId, .ok sgi)
  | (st', .error e) => (st', .error e)

/-- The declassifying dispatch's answer is the declassifying signal's: the
donation writes state alone. -/
theorem notificationSignalDeclassifiedCrossCoreDispatch_snd (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) :
    (notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy notificationId badge c st).2 =
      (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st).2 := by
  unfold notificationSignalDeclassifiedCrossCoreDispatch
  rcases notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st with
    ⟨st', _ | _⟩ <;> rfl

/-- **A property the declassifying signal carries and every donation after it
carries, the declassifying dispatch carries.** -/
theorem notificationSignalDeclassifiedCrossCoreDispatch_induct (P : SystemState → Prop)
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState)
    (hSig : P (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st).1)
    (hDonate : ∀ t sgi, signalWokenThread? st notificationId = some t →
      (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st).2 = .ok sgi →
      P (maybeDonateSchedContext
        (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st).1
        notificationId t)) :
    P (notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy notificationId badge c
      st).1 := by
  unfold notificationSignalDeclassifiedCrossCoreDispatch
  revert hSig hDonate
  rcases notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st with
    ⟨st', _ | sgi⟩
  · intro hSig _; exact hSig
  · intro hSig hDonate
    dsimp only
    unfold donateToSignalledFlowingGeneric
    cases hW : signalWokenThread? st notificationId with
    | none => exact hSig
    | some t =>
      exact maybeDonateSchedContextFlowingGeneric_induct P ctx _ notificationId t hSig
        (hDonate t sgi hW rfl)

/-- A refused declassifying dispatch donates nothing. -/
theorem notificationSignalDeclassifiedCrossCoreDispatch_fst_of_error
    {ctx : GenericLabelingContext} {declPolicy : DeclassificationPolicy}
    {notificationId : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId} {st : SystemState}
    {e : KernelError}
    (h : (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st).2 = .error e) :
    (notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy notificationId badge c st).1 =
      (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st).1 := by
  unfold notificationSignalDeclassifiedCrossCoreDispatch
  revert h
  rcases notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st with
    ⟨st', _ | _⟩
  · intro _; rfl
  · intro h; cases h

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
              (declassificationActorOf ctx signaler).domain with
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
      (declassificationActorOf ctx signaler).domain = .error e) :
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
        (declassificationActorOf ctx signaler).domain = .ok records ∧
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
          (declassificationActorOf ctx signaler).domain = p := ⟨_, rfl⟩
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

The correspondence `declassifiedSignal_no_invented_edge` reads: an appended entry's
flow endpoints and target are some planned record's, and nothing else was
appended. -/
theorem recordDeclassifiedHopsFrom_appended (c : CoreId) (actor : DeclassificationActor)
    (records : List DeclassifiedHopRecord) :
    ∀ (tags : TaintWords) (st st' : SystemState),
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
    obtain ⟨hRoom, hRest⟩ := recordDeclassifiedHopsFrom_cons c actor tags r rest st st' h
    obtain ⟨appended, hApp, hLen, hCorr, hFields⟩ := ih _ _ st' hRest
    have hMid : ({ st with declassificationAudit := (st.declassificationAudit.append
        (declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st)) } :
          SystemState).declassificationAuditLog =
        st.declassificationAuditLog ++
          [declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st] :=
      AuditRing.toList_append _ _ hRoom
    refine ⟨declassifyStoreEventWithTags c actor r.srcDomain r.dstDomain r.target tags st
              :: appended, ?_, by simp [hLen], ?_, ?_⟩
    · rw [hApp, hMid]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
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
    (actorDomain : SecurityDomain) (records : List DeclassifiedHopRecord)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId actorDomain = .ok records) :
    ∀ r ∈ records, declassificationDecision ctx declPolicy r.srcDomain r.dstDomain = .ok () := by
  unfold declassifiedSignalPlan at hPlan
  obtain ⟨a1, hA1⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy
      actorDomain (ctx.objectDomainOf notificationId) = a := ⟨_, rfl⟩
  rw [hA1] at hPlan
  cases a1 with
  | error e => exact absurd hPlan (by simp)
  | ok hop =>
    simp only [Except.ok.injEq] at hPlan
    subst hPlan
    cases hop with
    | ordinary => intro r hMem; simp at hMem
    | declassified =>
      intro r hMem
      rcases List.mem_singleton.mp hMem with rfl
      exact declassifiedSignalHopAuthorization_declassified_authorized ctx declPolicy _ _ hA1

/-- WS-SM SM9.C.1: **each planned record is the caller's release into the
notification** — its source the acting subject's domain, its destination the
notification's, its target the notification itself.  There is no other. -/
theorem declassifiedSignalPlan_record_shape (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) (records : List DeclassifiedHopRecord)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId actorDomain = .ok records) :
    ∀ r ∈ records,
      r.srcDomain = actorDomain ∧ r.dstDomain = ctx.objectDomainOf notificationId ∧
        r.target = notificationId := by
  unfold declassifiedSignalPlan at hPlan
  obtain ⟨a1, hA1⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy
      actorDomain (ctx.objectDomainOf notificationId) = a := ⟨_, rfl⟩
  rw [hA1] at hPlan
  cases a1 with
  | error e => exact absurd hPlan (by simp)
  | ok hop =>
    simp only [Except.ok.injEq] at hPlan
    subst hPlan
    cases hop with
    | ordinary => intro r hMem; simp at hMem
    | declassified =>
      intro r hMem
      rcases List.mem_singleton.mp hMem with rfl
      exact ⟨rfl, rfl, rfl⟩

/-- WS-SM SM9.C.1: every planned record's **source** is a domain the labeling
assigns — the acting subject's. -/
theorem declassifiedSignalPlan_record_sources (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (signaler : SeLe4n.ThreadId) (records : List DeclassifiedHopRecord)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId
      (ctx.threadDomainOf signaler) = .ok records) :
    ∀ r ∈ records, labelingAssignedDomain ctx r.srcDomain := by
  intro r hr
  rw [(declassifiedSignalPlan_record_shape ctx declPolicy notificationId
    (ctx.threadDomainOf signaler) records hPlan r hr).1]
  exact labelingAssignedDomain_thread ctx signaler

/-- WS-SM SM9.C.1: every planned record's **destination** likewise — the
notification's domain. -/
theorem declassifiedSignalPlan_record_destinations (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (signaler : SeLe4n.ThreadId) (records : List DeclassifiedHopRecord)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId
      (ctx.threadDomainOf signaler) = .ok records) :
    ∀ r ∈ records, labelingAssignedDomain ctx r.dstDomain := by
  intro r hr
  rw [(declassifiedSignalPlan_record_shape ctx declPolicy notificationId
    (ctx.threadDomainOf signaler) records hPlan r hr).2.1]
  exact labelingAssignedDomain_object ctx notificationId

/-- WS-SM SM9.C.1: **an ordinary hop ⇒ nothing to record.**  The plan of a
signal the base policy already permits is empty, which is what makes the
transition degenerate to the ordinary checked signal. -/
theorem declassifiedSignalPlan_ordinary (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain)
    (hFirst : ctx.policy.canFlow actorDomain (ctx.objectDomainOf notificationId) = true) :
    declassifiedSignalPlan ctx declPolicy notificationId actorDomain = .ok [] := by
  unfold declassifiedSignalPlan
  rw [declassifiedSignalHopAuthorization_ordinary ctx declPolicy
    actorDomain (ctx.objectDomainOf notificationId) hFirst]
  rfl

/-- WS-SM SM9.C.1: **a downgrade ⇒ one record**, naming the notification. -/
theorem declassifiedSignalPlan_declassified (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain)
    (hDeny : ctx.policy.canFlow actorDomain (ctx.objectDomainOf notificationId) = false)
    (hDecl : declPolicy.canDeclassify actorDomain (ctx.objectDomainOf notificationId) = true) :
    declassifiedSignalPlan ctx declPolicy notificationId actorDomain =
      .ok [ { srcDomain := actorDomain, dstDomain := ctx.objectDomainOf notificationId,
              target := notificationId } ] := by
  unfold declassifiedSignalPlan
  rw [declassifiedSignalHopAuthorization_declassified ctx declPolicy
    actorDomain (ctx.objectDomainOf notificationId) hDeny hDecl]
  rfl

/-- WS-SM SM9.C.1: **a refused hop ⇒ `.declassificationDenied`**, the one
refusal the plan reports. -/
theorem declassifiedSignalPlan_refused (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain)
    (hDeny : ctx.policy.canFlow actorDomain (ctx.objectDomainOf notificationId) = false)
    (hNoDecl : declPolicy.canDeclassify actorDomain (ctx.objectDomainOf notificationId) = false) :
    declassifiedSignalPlan ctx declPolicy notificationId actorDomain =
      .error .declassificationDenied := by
  unfold declassifiedSignalPlan
  rw [declassifiedSignalHopAuthorization_refused ctx declPolicy
    actorDomain (ctx.objectDomainOf notificationId) hDeny hNoDecl]

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
      declassificationAudit := st'.declassificationAudit } := by
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

/-- WS-SM SM9.C.1 (**`declassifiedSignal_no_invented_edge`**): every event the
transition appends names a domain pair some `declassificationDecision` returned
`.ok` for — the trail reports no edge no policy authorized. -/
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
    (declassificationActorOf ctx signaler).domain records hPlan r hr


-- ============================================================================
-- §9  WS-SM SM9.C.1 — the onward delivery is the identity flow
-- ============================================================================

/-- WS-SM SM9.C.1 (**the second hop is the identity flow**): on a
notification-label coherent state, the receiver a declassifying signal
resolves carries the notification's own domain, so the onward flow
`notification → receiver` is one the base lattice permits and no downgrade —
its authorization is `.ordinary` under every declassification policy.

This is why the transition gates and records one hop only.  The coherence is a
hypothesis rather than a consequence of reachability: the boot establishes it
(`notificationLabelsCoherent`, refused otherwise) and the checked wait and bind
admit a thread to a notification only at its label (`notificationFlowGate`), but
the preservation theorem over every transition is registered debt, so the fact
is stated on the states it is proved for. -/
theorem declassifiedSignalReceiver_flow_ordinary_of_coherent (ctx : LabelingContext)
    (declPolicy : DeclassificationPolicy) (st : SystemState)
    (notificationId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hCoherent : notificationLabelsCoherent st ctx = true)
    (hRecv : declassifiedSignalReceiver? st notificationId = some receiver) :
    (liftLegacyContext ctx).objectDomainOf notificationId =
        (liftLegacyContext ctx).threadDomainOf receiver ∧
      declassifiedSignalHopAuthorization (liftLegacyContext ctx) declPolicy
        ((liftLegacyContext ctx).objectDomainOf notificationId)
        ((liftLegacyContext ctx).threadDomainOf receiver) = .ok .ordinary := by
  have hLabel := notificationLabelsCoherent_signalReceiver_label hCoherent
    (by unfold declassifiedSignalReceiver? at hRecv; exact hRecv)
  have hDom : (liftLegacyContext ctx).objectDomainOf notificationId =
      (liftLegacyContext ctx).threadDomainOf receiver := by
    show embedLegacyLabel (ctx.objectLabelOf notificationId) =
      embedLegacyLabel (ctx.threadLabelOf receiver)
    rw [hLabel]
  refine ⟨hDom, declassifiedSignalHopAuthorization_ordinary _ _ _ _ ?_⟩
  rw [hDom]
  exact DomainFlowPolicy.legacyLattice_reflexive _

-- ============================================================================
-- §10  WS-SM SM9.C.1 — the ordinary path, attribution, and the ordering
-- ============================================================================

/-- WS-SM SM9.C.1 (**the degenerate case, as an equation**): when the base policy
already permits the caller's hop, the declassifying signal **is** the ordinary
cross-core bound signal, and records nothing.

Worth an equation rather than a remark: it says the syscall adds authority
exactly where the policy withholds it and adds *no* behaviour where the policy
does not, so a deployment cannot use it as a second, less-audited signal path. -/
theorem declassifiedSignal_ordinary_eq_signal (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) (signaler : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some signaler)
    (hFirst : ctx.policy.canFlow (ctx.threadDomainOf signaler)
      (ctx.objectDomainOf notificationId) = true) :
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      notificationSignalBoundOnCore notificationId badge c st := by
  cases hN : st.getNotification? notificationId with
  | none =>
    -- PR #872 review: on a wrong-kind or absent target BOTH sides answer the
    -- ordinary signal's own recovery — the target gate is the ordinary
    -- signal's none-arm, decided through the typed accessor.
    have hL : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
        (if (st.getObject? notificationId).isSome then (st, .error (.invalidCapability 0))
         else (st, .error .objectNotFound)) := by
      rw [SystemState.getObject?_eq_getElem, ← getObjectType?_isSome_eq_raw]
      simp [notificationSignalDeclassifiedOnCore, hCur, hN]
    have hR : notificationSignalBoundOnCore notificationId badge c st =
        (if (st.getObject? notificationId).isSome then (st, .error (.invalidCapability 0))
         else (st, .error .objectNotFound)) := by
      unfold notificationSignalBoundOnCore boundDeliveryTarget? notificationSignalOnCore
      rw [hN]
    rw [hL, hR]
  | some ntfn =>
  rw [notificationSignalDeclassifiedOnCore_eq_of_subject ctx declPolicy notificationId badge c
    st signaler ntfn hCur hN,
    declassifiedSignalPlan_ordinary ctx declPolicy notificationId
      (declassificationActorOf ctx signaler).domain hFirst]
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
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain) (auth : DeclassifiedHopAuthorization)
    (hDefault : declPolicy.canDeclassify = fun _ _ => false)
    (h : declassifiedSignalHopAuthorization ctx declPolicy srcDomain dstDomain = .ok auth) :
    auth = .ordinary := by
  cases auth with
  | ordinary => rfl
  | declassified =>
    have hDec := declassifiedSignalHopAuthorization_declassified_authorized ctx declPolicy
      srcDomain dstDomain h
    have := ((declassificationDecision_ok_iff ctx declPolicy srcDomain dstDomain).mp hDec).2
    rw [hDefault] at this
    exact absurd this (by simp)

/-- WS-SM SM9.C.1 (**the unconfigured deployment, at the plan**): with a deny-all
declassification policy an admitted plan is **empty**.

Not "the transition fails" — that would be false, and stating it would be the
kind of over-claim this workstream keeps correcting.  A signal whose hop the
base lattice already permits is an ordinary signal, and the honest property is
that an unconfigured deployment can perform *no downgrade*: the plan it admits
records nothing, so by `declassifiedSignal_never_unaudited`'s dual the trail
never grows and by `declassifiedSignal_ordinary_eq_signal` the transition is
literally `notificationSignalBoundOnCore`. -/
theorem declassifiedSignalPlan_default_empty (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain)
    (records : List DeclassifiedHopRecord)
    (hDefault : declPolicy.canDeclassify = fun _ _ => false)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId actorDomain = .ok records) :
    records = [] := by
  unfold declassifiedSignalPlan at hPlan
  obtain ⟨a₁, hA₁⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy
      actorDomain (ctx.objectDomainOf notificationId) = a := ⟨_, rfl⟩
  rw [hA₁] at hPlan
  cases a₁ with
  | error e => exact absurd hPlan (by simp)
  | ok auth₁ =>
    have hOrd₁ := declassifiedSignalHopAuthorization_default_ordinary ctx declPolicy
      actorDomain (ctx.objectDomainOf notificationId) auth₁ hDefault hA₁
    subst hOrd₁
    simp only [declassifiedHopRecords_ordinary] at hPlan
    exact (Except.ok.inj hPlan).symm

/-- WS-SM SM9.C.1 (**`declassifiedSignal_never_unaudited`**): every downgrade the
transition performs is recorded.

The two halves the fail-closed capacity bound buys: a hop the plan marked a
downgrade contributes an entry, and a delivery that could not record its
downgrade performs none of it — the state is the pre-state and the badge
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
        (declassificationActorOf ctx signaler).domain = .ok records ∧
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
    (declassificationActorOf ctx signaler).domain records hDefault hPlan
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
    (declassificationActorOf ctx signaler).domain records hDefault hPlan
  subst hNil
  rw [recordDeclassifiedHops_nil] at hRec
  rw [hSignal, Option.some.inj hRec]

/-- WS-SM SM9.C.1 (**`attributionFromRunningSubject_over_actor`**): every entry
the transition records is **attributable** — its actor is the subject the
originating core was running, at the domain the labeling gives that subject.

SM8.C's rule, restated over the actor field the record carries. -/
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
`ipcInvariantFull`: the audit append is object-store-transparent, so the
bundle transfers from the delivery's post-state
(`notificationSignalDeclassifiedOnCore_ipcInvariantFull_transfer`), and the
delivery's own bundle is the bound-aware signal's
(`notificationSignalBoundOnCore_preserves_ipcInvariantFull`), whose one
non-bundle premise is the bound receiver's splice predecessor
(`splicePredecessorBlocked`). -/

/-- WS-SM SM9.C.4: the whole `proofLayerInvariantBundle` across the audit fold
at any accumulator — each append is a trail write, and the SM8.C.8 carriage
lemma does the rest. -/
theorem recordDeclassifiedHopsFrom_preserves_proofLayerInvariantBundle (c : CoreId)
    (actor : DeclassificationActor) (records : List DeclassifiedHopRecord) :
    ∀ (tags : TaintWords) (st st' : SystemState),
      Architecture.proofLayerInvariantBundle st →
      recordDeclassifiedHopsFrom c actor tags records st = some st' →
      Architecture.proofLayerInvariantBundle st' := by
  induction records with
  | nil => intro tags st st' hInv h; cases h; exact hInv
  | cons r rest ih =>
    intro tags st st' hInv h
    obtain ⟨-, hRest⟩ := recordDeclassifiedHopsFrom_cons c actor tags r rest st st' h
    exact ih _ _ st' (Architecture.proofLayerInvariantBundle_setDeclassificationAuditLog st _ hInv) hRest

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

/-- WS-SM SM9.C.4 / SM9.A.1a: the trail's timestamp discipline survives —
every entry the delivery records is stamped from the state it lands in, so no
timestamp is reused. -/
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

/-- WS-SM SM9.C.3: **the whole nineteen-conjunct IPC bundle, transferred.**

The audit append changes no object lookup, so a bundle
that holds of the delivery's post-state holds of the committed one.  The premise
is the delivery's own obligation, discharged below from the bound-aware
signal's bundle. -/
theorem notificationSignalDeclassifiedOnCore_ipcInvariantFull_transfer
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hSignalInv : ipcInvariantFull (notificationSignalBoundOnCore notificationId badge c st).1)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ipcInvariantFull st' := by
  obtain ⟨hObjects, -, -, -⟩ := declassifiedSignal_delivers_badge ctx declPolicy
    notificationId badge c st st' sgi hStep
  exact ipcInvariantFull_of_getElem_eq (fun oid => by rw [hObjects]) hSignalInv

/-- WS-SM SM9.C.3: **the whole bundle across the declassifying signal**, on
both delivery paths.  The delivery is the bound-aware signal
(`notificationSignalBoundOnCore`): off the bound path it is
`notificationSignalOnCore`, and on it the bound receiver is spliced off its
endpoint's receive queue, which keeps the bundle when that receiver's queue
predecessor is blocked on the same side (`splicePredecessorBlocked`). -/
theorem notificationSignalDeclassifiedOnCore_preserves_ipcInvariantFull
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hInv : ipcInvariantFull st) (hObjInv : st.objects.invExt)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hPred : ∀ (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId),
      boundDeliveryTarget? st notificationId = some (t, epId) →
      splicePredecessorBlocked true epId st t)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ipcInvariantFull st' :=
  notificationSignalDeclassifiedOnCore_ipcInvariantFull_transfer ctx declPolicy
    notificationId badge c st st' sgi
    (notificationSignalBoundOnCore_preserves_ipcInvariantFull notificationId badge c st hInv
      hObjInv hNWC hAllBudgetsNone hPred) hStep

/-- WS-SM SM9.C.3: **the per-core bundle**, from the whole-bundle form. -/
theorem notificationSignalDeclassifiedOnCore_ipcInvariantFull_perCore_transfer
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind)) (view : CoreId)
    (hSignalInv : ipcInvariantFull (notificationSignalBoundOnCore notificationId badge c st).1)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
      (st', .ok sgi)) :
    ipcInvariantFull_perCore st' view :=
  ipcInvariantFull_perCore_of_full
    (notificationSignalDeclassifiedOnCore_ipcInvariantFull_transfer ctx declPolicy notificationId
      badge c st st' sgi hSignalInv hStep)

-- ============================================================================
-- §12  WS-SM SM9.C.1 — the ordering, the trail invariants, the dispatch
-- ============================================================================

/-- WS-SM SM9.C.1 (**the SM8.C.9 ordering, kept**): a caller whose downgrade the
*policy* refuses learns **nothing about the trail's occupancy** — the error it
gets is the policy's, on a full trail exactly as on an empty one.

The plan is computed before the trail is touched and reads no state, so the two
states in the statement may differ in anything but the acting subject and the
notification's presence — the trail's length among it.  Without this ordering,
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
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId
      (declassificationActorOf ctx signaler).domain = .error e) :
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st₁ =
      (st₁, .error e) ∧
    notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st₂ =
      (st₂, .error e) := by
  exact ⟨notificationSignalDeclassifiedOnCore_plan_refused ctx declPolicy notificationId badge c
      st₁ signaler ntfn₁ e hCur₁ hNtfn₁ hPlan,
    notificationSignalDeclassifiedOnCore_plan_refused ctx declPolicy notificationId badge c
      st₂ signaler ntfn₂ e hCur₂ hNtfn₂ hPlan⟩

/-- WS-SM SM9.C.1: the transition establishes the trail's **actor** invariant —
the actor is read off the state, so every entry it writes carries that
subject's own domain. -/
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

/-- WS-SM SM9.C.1: and the **source** invariant — a record's source is the
acting subject's domain, which the labeling assigns. -/
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
    exact declassifiedSignalPlan_record_sources ctx declPolicy notificationId signaler
      records hPlan r hr

/-- WS-SM SM9.C.1: and the **destination** invariant — a record's destination is
the notification's domain, which the labeling assigns. -/
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
    exact declassifiedSignalPlan_record_destinations ctx declPolicy notificationId signaler
      records hPlan r hr



-- ============================================================================
-- §13  WS-SM SM9.C.1 / SM9.C.8 — the failed hop, and the enforcement families
-- ============================================================================

/-- WS-SM SM9.C.1: a hop authorization's error is always
`.declassificationDenied` — the gate discards the decision's error, so the
refusal the ledger records names the declassification whatever the decision
returned. -/
theorem declassifiedSignalHopAuthorization_error_refusal (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain) (e : KernelError)
    (h : declassifiedSignalHopAuthorization ctx declPolicy srcDomain dstDomain =
      .error e) :
    e = .declassificationDenied := by
  unfold declassifiedSignalHopAuthorization at h
  split at h
  · exact absurd h (by simp)
  · obtain ⟨dec, hDec⟩ : ∃ d, declassificationDecision ctx declPolicy srcDomain dstDomain = d :=
      ⟨_, rfl⟩
    rw [hDec] at h
    cases dec with
    | error e' => exact (Except.error.inj h).symm
    | ok u => cases u; exact absurd h (by simp)

/-- WS-SM SM9.C.1: **the plan's only refusal is `.declassificationDenied`.** -/
theorem declassifiedSignalPlan_error_refusal (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) (e : KernelError)
    (hPlan : declassifiedSignalPlan ctx declPolicy notificationId actorDomain = .error e) :
    e = .declassificationDenied := by
  unfold declassifiedSignalPlan at hPlan
  obtain ⟨a1, hA1⟩ : ∃ a, declassifiedSignalHopAuthorization ctx declPolicy
      actorDomain (ctx.objectDomainOf notificationId) = a := ⟨_, rfl⟩
  rw [hA1] at hPlan
  cases a1 with
  | error e' =>
    have hE := declassifiedSignalHopAuthorization_error_refusal ctx declPolicy
      actorDomain (ctx.objectDomainOf notificationId) e' hA1
    rw [← hE]; exact (Except.error.inj hPlan).symm
  | ok hop => exact absurd hPlan (by simp)

/-- WS-SM SM9.C.8 (**the `_denied_preserves_state` family member**): every
refusal of the declassifying signal returns the **pre-state exactly** — the
idle-core arm, the target gate, the hop gate, the delivery's own failure, and the fail-closed
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
          (declassificationActorOf ctx signaler).domain = p := ⟨_, rfl⟩
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
3. a plan the hop gate refuses is returned verbatim
   (`.declassificationDenied`), the state untouched;
4. a delivery failure of the underlying bound signal is returned verbatim —
   this transition invents no discriminant for it and performs no partial
   commit;
5. an authorized plan whose records do not all fit refuses fail-closed with
   `.auditLogCapacityExceeded`, delivering nothing;
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
             (st, .error (.invalidCapability 0))) ∨
        (st.getObjectType? notificationId = none ∧
           notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
             (st, .error .objectNotFound)))) ∨
    (∃ signaler e, st.scheduler.currentOnCore c = some signaler ∧
       declassifiedSignalPlan ctx declPolicy notificationId
         (declassificationActorOf ctx signaler).domain = .error e ∧
       notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
         (st, .error e)) ∨
    (∃ signaler records e, st.scheduler.currentOnCore c = some signaler ∧
       declassifiedSignalPlan ctx declPolicy notificationId
         (declassificationActorOf ctx signaler).domain = .ok records ∧
       (notificationSignalBoundOnCore notificationId badge c st).2 = .error e ∧
       notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
         (st, .error e)) ∨
    (∃ signaler records sgi, st.scheduler.currentOnCore c = some signaler ∧
       declassifiedSignalPlan ctx declPolicy notificationId
         (declassificationActorOf ctx signaler).domain = .ok records ∧
       (notificationSignalBoundOnCore notificationId badge c st).2 = .ok sgi ∧
       recordDeclassifiedHops c (declassificationActorOf ctx signaler) records
         (notificationSignalBoundOnCore notificationId badge c st).1 = none ∧
       notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st =
         (st, .error .auditLogCapacityExceeded)) ∨
    (∃ signaler records sgi st2, st.scheduler.currentOnCore c = some signaler ∧
       declassifiedSignalPlan ctx declPolicy notificationId
         (declassificationActorOf ctx signaler).domain = .ok records ∧
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
          (declassificationActorOf ctx signaler).domain = p := ⟨_, rfl⟩
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
-- §14  WS-SM SM9.C.1 — the target gate (PR #872 review, round 2)
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
      (st, .error (.invalidCapability 0)) := by
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
