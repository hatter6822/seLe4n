-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.NotificationBind
import SeLe4n.Kernel.IPC.CrossCore.SignalDonation
import SeLe4n.Kernel.IPC.CrossCore.NotificationInvariant
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch

/-!
# WS-SM SM6.B — Below-API cross-core bound-signal dispatch

The pure dispatch ops the live `API` `.notificationSignal` arm routes through (the
notification analogue of SM6.A's `endpointCallCrossCoreDispatch{,Checked}`):

* `notificationSignalBoundCrossCoreDispatch` — `notificationSignalBoundOnCore`
  at `executingCore`, the core the syscall trapped on, threaded from the
  entry point (`syscallEntryChecked`) through the dispatcher — never re-derived
  from the state.
* `notificationSignalBoundCrossCoreDispatchChecked` — the info-flow-checked form,
  gating on `securityFlowsTo signaler→notification` (rejecting `.flowDenied`).

Both surface the optional cross-core `.reschedule` SGI; the live runtime entry
re-derives and fires it from the committed state diff (`computeCrossCoreSgis`),
so no new Rust extern is needed (the SM6.A SGI seam is operation-agnostic).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

/-- WS-SM SM6.B: the unchecked cross-core bound-signal dispatch — seL4's
`sendSignal` (`sendSignalOnCore`: the bound-aware cross-core wake, then the
donation of the notification's context to the thread it woke) at the core the
syscall trapped on. -/
def notificationSignalBoundCrossCoreDispatch (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  sendSignalOnCore notificationId badge executingCore st

/-- WS-SM SM6.B: the info-flow-checked cross-core bound-signal dispatch.  Gates on
`securityFlowsTo signaler→notification` AND — when the signal would take the
bound-delivery path (`boundDeliveryTarget?` resolves a bound `BlockedOnReceive`
TCB) — on the two-way `notificationFlowGate` between the notification and the
receiver, because bound delivery writes the badge **directly into the bound
TCB**, a second sink beyond the notification, and whether it happens depends on
the receiver's state, which a lower notification's observer must not learn.
Without the receiver gate a policy permitting a high signaler → high notification
but denying flow to a *low* bound TCB would be bypassed (codex review #3): the badge
would leak to the low receiver.  Fail-closed with `.flowDenied` on either denial.
A passed signal is seL4's `sendSignal` (`sendSignalOnCore`): the wake, then
the donation of the notification's context to the thread it woke. -/
@[inline] def notificationSignalBoundCrossCoreDispatchChecked (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (executingCore : CoreId)
    (st : SystemState) : SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  if securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) then
    match boundDeliveryTarget? st notificationId with
    | some (receiver, _) =>
        if notificationFlowGate ctx notificationId receiver then
          sendSignalOnCore notificationId badge executingCore st
        else
          (st, .error .flowDenied)
    | none =>
        sendSignalOnCore notificationId badge executingCore st
  else
    (st, .error .flowDenied)

/-- **WS-LS LS2.3**: a checked signal that succeeds committed the unchecked
transition's state — every refusing branch returns the pre-state with an error,
so the state a successful answer carries is the signal's
(`sendSignalOnCore`). -/
theorem notificationSignalBoundCrossCoreDispatchChecked_fst_of_ok (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (executingCore : CoreId) (st st' : SystemState) (r : Option (CoreId × SgiKind))
    (h : notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge
      executingCore st = (st', .ok r)) :
    (sendSignalOnCore notificationId badge executingCore st).1 = st' := by
  unfold notificationSignalBoundCrossCoreDispatchChecked at h
  split at h
  · split at h
    · split at h
      · exact congrArg Prod.fst h
      · exact absurd (congrArg Prod.snd h) (by simp)
    · exact congrArg Prod.fst h
  · exact absurd (congrArg Prod.snd h) (by simp)

/-- **A property the entry state carries and the signal carries, the checked
signal carries**: every gate refuses in the state it was handed, and a passed gate
runs the signal (`sendSignalOnCore`).  Each family lemma of the
checked signal is this, with the signal's (the wake's composed with the donation's,
`sendSignalOnCore_induct`). -/
theorem notificationSignalBoundCrossCoreDispatchChecked_induct (P : SystemState → Prop)
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState)
    (hRefl : P st)
    (hSig : P (sendSignalOnCore notificationId badge executingCore st).1) :
    P (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge
      executingCore st).1 := by
  unfold notificationSignalBoundCrossCoreDispatchChecked
  repeat' split
  all_goals first | exact hSig | exact hRefl

/-- WS-SM SM6.B: a disallowed signaler→notification flow is rejected before any
state change. -/
theorem notificationSignalBoundCrossCoreDispatchChecked_flow_denied
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = false) :
    notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge executingCore st
      = (st, .error .flowDenied) := by
  simp [notificationSignalBoundCrossCoreDispatchChecked, hDeny]

/-- WS-SM SM6.B: even with signaler→notification permitted, a bound delivery whose
receiver the notification may **not** flow to is rejected before any state change —
the badge never reaches a lower bound TCB (codex review #3). -/
theorem notificationSignalBoundCrossCoreDispatchChecked_flow_denied_to_receiver
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState) (receiver : SeLe4n.ThreadId) (ep : SeLe4n.ObjId)
    (hAllow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = true)
    (hTarget : boundDeliveryTarget? st notificationId = some (receiver, ep))
    (hDenyR : notificationFlowGate ctx notificationId receiver = false) :
    notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge executingCore st
      = (st, .error .flowDenied) := by
  simp [notificationSignalBoundCrossCoreDispatchChecked, hAllow, hTarget, hDenyR]

/-- WS-SM SM6.B: with signaler→notification permitted and no bound-delivery target
(the ordinary signal path), the checked dispatch is the signal
(`sendSignalOnCore`). -/
theorem notificationSignalBoundCrossCoreDispatchChecked_flow_allowed_no_delivery
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState)
    (hAllow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = true)
    (hNone : boundDeliveryTarget? st notificationId = none) :
    notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge executingCore st
      = sendSignalOnCore notificationId badge executingCore st := by
  simp [notificationSignalBoundCrossCoreDispatchChecked, hAllow, hNone]

/-- WS-SM SM6.B: when both the signaler→notification and notification→receiver flows
are permitted, the checked bound delivery is the signal
(`sendSignalOnCore`). -/
theorem notificationSignalBoundCrossCoreDispatchChecked_flow_allowed_to_receiver
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState) (receiver : SeLe4n.ThreadId) (ep : SeLe4n.ObjId)
    (hAllow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = true)
    (hTarget : boundDeliveryTarget? st notificationId = some (receiver, ep))
    (hAllowR : notificationFlowGate ctx notificationId receiver = true) :
    notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge executingCore st
      = sendSignalOnCore notificationId badge executingCore st := by
  simp [notificationSignalBoundCrossCoreDispatchChecked, hAllow, hTarget, hAllowR]

-- ============================================================================
-- §5  Cross-core notification WAIT dispatch (per-core deschedule)
-- ============================================================================

/-- WS-SM SM6.B: the unchecked cross-core notification-wait dispatch — runs
`notificationWaitOnCore` at `executingCore`, the core the syscall trapped on,
so a `.notificationWait` issued on a *non-boot* core deschedules the blocked caller
on **its own** core rather than the boot core.  The wait analogue of
`notificationSignalBoundCrossCoreDispatch`; a wait surfaces no cross-core SGI (it
pokes no other core), so the result carries only the consumed badge. -/
def notificationWaitCrossCoreDispatch (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) :
    SystemState × Except KernelError (Option SeLe4n.Badge) :=
  notificationWaitOnCore notificationId waiter executingCore st

/-- WS-SM SM6.B: the info-flow-checked cross-core notification-wait dispatch — gates
on the two-way `notificationFlowGate` (the badge flows from the notification to
the waiter, and a blocking wait writes the waiter into the notification's queue;
matching `notificationWaitChecked`), fail-closed with `.flowDenied`. -/
def notificationWaitCrossCoreDispatchChecked (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) :
    SystemState × Except KernelError (Option SeLe4n.Badge) :=
  if notificationFlowGate ctx notificationId waiter then
    -- seL4's `handleRecv`: a notification bound to another thread is the
    -- wait's capability fault (`missingCapability 0`), refused before any
    -- write; checked after the flow, so a denied wait learns nothing of it.
    if notificationBoundElsewhere st notificationId waiter then
      (st, .error (.invalidCapability 0))
    else
    notificationWaitOnCore notificationId waiter executingCore st
  else
    (st, .error .flowDenied)

/-- **WS-LS LS2.3**: a checked wait that succeeds committed the unchecked
transition's state. -/
theorem notificationWaitCrossCoreDispatchChecked_fst_of_ok (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st st' : SystemState) (r : Option SeLe4n.Badge)
    (h : notificationWaitCrossCoreDispatchChecked ctx notificationId waiter executingCore st
      = (st', .ok r)) :
    (notificationWaitOnCore notificationId waiter executingCore st).1 = st' := by
  unfold notificationWaitCrossCoreDispatchChecked at h
  split at h
  · split at h
    · exact absurd (congrArg Prod.snd h) (by simp)
    · exact congrArg Prod.fst h
  · exact absurd (congrArg Prod.snd h) (by simp)

/-- **A checked wait that succeeds passed its two-way gate**, so the waiter
carries the notification's label: the label equation of the lend a receive's
completed signal makes to it (WS-SX SX22). -/
theorem notificationWaitCrossCoreDispatchChecked_label_of_ok {ctx : LabelingContext}
    {notificationId : SeLe4n.ObjId} {waiter : SeLe4n.ThreadId} {executingCore : CoreId}
    {st st' : SystemState} {r : Option SeLe4n.Badge}
    (h : notificationWaitCrossCoreDispatchChecked ctx notificationId waiter executingCore st
      = (st', .ok r)) :
    ctx.threadLabelOf waiter = ctx.objectLabelOf notificationId := by
  unfold notificationWaitCrossCoreDispatchChecked at h
  split at h
  · rename_i hG; exact ((twoWayLabelGate_iff_eq _ _).mp hG).symm
  · exact absurd (congrArg Prod.snd h) (by simp)

/-- WS-SM SM6.B: a disallowed wait flow is rejected before any state change. -/
theorem notificationWaitCrossCoreDispatchChecked_flow_denied
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (executingCore : CoreId) (st : SystemState)
    (hDeny : notificationFlowGate ctx notificationId waiter = false) :
    notificationWaitCrossCoreDispatchChecked ctx notificationId waiter executingCore st
      = (st, .error .flowDenied) := by
  simp [notificationWaitCrossCoreDispatchChecked, hDeny]

/-- WS-SM SM6.B: when the flow is permitted, the checked wait dispatch is exactly the
unchecked one on a notification bound to no other thread — the guards are pure
preconditions. -/
theorem notificationWaitCrossCoreDispatchChecked_flow_allowed
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (executingCore : CoreId) (st : SystemState)
    (hAllow : notificationFlowGate ctx notificationId waiter = true)
    (hUnbound : notificationBoundElsewhere st notificationId waiter = false) :
    notificationWaitCrossCoreDispatchChecked ctx notificationId waiter executingCore st
      = notificationWaitCrossCoreDispatch notificationId waiter executingCore st := by
  simp [notificationWaitCrossCoreDispatchChecked, notificationWaitCrossCoreDispatch, hAllow,
    hUnbound]

/-- WS-SM SM6.B: the cross-core wait dispatch preserves `objects.invExt`. -/
theorem notificationWaitCrossCoreDispatch_preserves_objects_invExt
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    (notificationWaitCrossCoreDispatch notificationId waiter executingCore st).1.objects.invExt :=
  notificationWaitOnCore_preserves_objects_invExt notificationId waiter
    executingCore st hObjInv

/-- WS-SM SM6.B: the cross-core wait dispatch preserves `ipcInvariant`. -/
theorem notificationWaitCrossCoreDispatch_preserves_ipcInvariant
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId) (st : SystemState)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) :
    ipcInvariant (notificationWaitCrossCoreDispatch notificationId waiter executingCore st).1 :=
  notificationWaitOnCore_preserves_ipcInvariant notificationId waiter
    executingCore st hInv hObjInv

/-- WS-RR RR2 (closure audit): the live `.notificationWait` dispatch wrapper
preserves the **whole** IPC invariant bundle — the wrapper is
`notificationWaitOnCore` at the executing core and nothing else, so
this is that bundle instantiated.  (The bound-signal wrapper has no such
corollary yet: `notificationSignalBoundOnCore`'s own bundle is the SM6.D
bound-delivery debt, registered in WS-SM SM6.D
tracked-debt list.) -/
theorem notificationWaitCrossCoreDispatch_preserves_ipcInvariantFull
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId) (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWaiterNotRecv : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hWaiterNotReply : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hWaiterReady : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        tcb.ipcState = .ready) :
    ipcInvariantFull (notificationWaitCrossCoreDispatch notificationId waiter executingCore st).1 :=
  notificationWaitOnCore_preserves_ipcInvariantFull notificationId waiter
    executingCore st hInv hObjInv hWaiterNotRecv
    hWaiterNotReply hAllBudgetsNone hWaiterReady


-- ============================================================================
-- Notification label coherence: what the two-way gates establish
-- ============================================================================

/-- **One object's share of notification label coherence.**  A notification's
bound thread, queue head and queue tail each meet the notification under the
two-way `notificationFlowGate`; a thread blocked on a notification meets it, and
so do its queue neighbours; a thread blocked on no notification carries no
queue links.

The neighbour clause is what reaches a queue's interior: the gate admits exactly
equal labels (`twoWayLabelGate_iff_eq`), so a chain of admitted neighbours from
an admitted head has the notification's label throughout, and a link out of a
thread blocked on no notification is refused rather than left unexamined. -/
@[inline] def notificationEntryLabelsCoherent (ctx : LabelingContext) (oid : SeLe4n.ObjId) :
    KernelObject → Bool
  | .notification n =>
      (n.boundTCB.all fun t => notificationFlowGate ctx oid t) &&
        (n.waitHead.all fun t => notificationFlowGate ctx oid t) &&
        (n.waitTail.all fun t => notificationFlowGate ctx oid t)
  | .tcb t =>
      match t.ipcState with
      | .blockedOnNotification nid =>
          notificationFlowGate ctx nid (SeLe4n.ThreadId.ofObjId oid) &&
            (t.ntfnPrev.all fun u => notificationFlowGate ctx nid u) &&
            (t.ntfnNext.all fun u => notificationFlowGate ctx nid u)
      | _ => t.ntfnPrevCode == 0 && t.ntfnNextCode == 0
  | _ => true

/-- **Every notification's waiters and bound thread meet it under the two-way
gate** (`notificationEntryLabelsCoherent` of every stored object).

The live Wait (`notificationWaitCrossCoreDispatchChecked`) and bind
(`bindNotificationChecked`) admit a thread only through `notificationFlowGate`,
and every other writer of a notification's queue or bound field removes a
thread, so no syscall introduces an incoherent waiter or binding.  A boot
configuration installs its objects as given, so the boot checks this before it
installs anything (`Platform.Boot` and the boot wrapper in `Platform.FFI`): the
base case of the coherence the gates keep. -/
def notificationLabelsCoherent (st : SystemState) (ctx : LabelingContext) : Bool :=
  st.objects.fold true fun acc oid obj => acc && notificationEntryLabelsCoherent ctx oid obj

/-- What coherence says of one stored object. -/
theorem notificationLabelsCoherent_entry {st : SystemState} {ctx : LabelingContext}
    (h : notificationLabelsCoherent st ctx = true) {oid : SeLe4n.ObjId} {obj : KernelObject}
    (hObj : st.objects[oid]? = some obj) :
    notificationEntryLabelsCoherent ctx oid obj = true :=
  SeLe4n.Kernel.RobinHood.RHTable.fold_and_true_of_get? st.objects
    (notificationEntryLabelsCoherent ctx) h hObj

/-- What coherence says of a stored notification. -/
theorem notificationLabelsCoherent_notification {st : SystemState} {ctx : LabelingContext}
    (h : notificationLabelsCoherent st ctx = true) {nid : SeLe4n.ObjId} {ntfn : Notification}
    (hN : st.getNotification? nid = some ntfn) :
    (∀ t, ntfn.boundTCB = some t → notificationFlowGate ctx nid t = true) ∧
      (∀ t, ntfn.waitHead = some t → notificationFlowGate ctx nid t = true) ∧
      (∀ t, ntfn.waitTail = some t → notificationFlowGate ctx nid t = true) := by
  have hObj : st.objects[nid]? = some (.notification ntfn) := by
    unfold SystemState.getNotification? at hN
    split at hN
    · next hEq => cases hN; exact hEq
    · cases hN
  have hE := notificationLabelsCoherent_entry h hObj
  simp only [notificationEntryLabelsCoherent, Bool.and_eq_true, Option.all_eq_true] at hE
  obtain ⟨⟨hB, hH⟩, hT⟩ := hE
  exact ⟨fun t ht => hB t ht, fun t ht => hH t ht, fun t ht => hT t ht⟩

/-- What coherence says of a thread blocked on a notification: it meets the
notification, and so does each of its queue neighbours. -/
theorem notificationLabelsCoherent_blocked {st : SystemState} {ctx : LabelingContext}
    (h : notificationLabelsCoherent st ctx = true) {tid : SeLe4n.ThreadId} {tcb : TCB}
    {nid : SeLe4n.ObjId} (hT : st.getTcb? tid = some tcb)
    (hIpc : tcb.ipcState = .blockedOnNotification nid) :
    notificationFlowGate ctx nid tid = true ∧
      (∀ u, tcb.ntfnPrev = some u → notificationFlowGate ctx nid u = true) ∧
      (∀ u, tcb.ntfnNext = some u → notificationFlowGate ctx nid u = true) := by
  have hObj : st.objects[tid.toObjId]? = some (.tcb tcb) := by
    unfold SystemState.getTcb? at hT
    split at hT
    · next hEq => cases hT; exact hEq
    · cases hT
  have hE := notificationLabelsCoherent_entry h hObj
  simp only [notificationEntryLabelsCoherent, hIpc, Bool.and_eq_true,
    Option.all_eq_true] at hE
  obtain ⟨⟨hSelf, hP⟩, hN⟩ := hE
  exact ⟨hSelf, fun u hu => hP u hu, fun u hu => hN u hu⟩

-- ============================================================================
-- Notification label agreement: the label part of coherence, carried per entry
-- ============================================================================

/-- **One object's share of notification label agreement**: the label clauses
of `notificationEntryLabelsCoherent`.  A notification's bound thread and queue
ends meet it under the two-way gate; a thread blocked on a notification meets
it; a thread's queue neighbours carry its own label.  The queue's shape (a
thread blocked on no notification holds no links) is not a label fact and is
left to the IPC invariants. -/
def notificationEntryLabelsAgree (ctx : LabelingContext) (oid : SeLe4n.ObjId) :
    KernelObject → Prop
  | .notification n =>
      (∀ t, n.boundTCB = some t → notificationFlowGate ctx oid t = true) ∧
        (∀ t, n.waitHead = some t → notificationFlowGate ctx oid t = true) ∧
        (∀ t, n.waitTail = some t → notificationFlowGate ctx oid t = true)
  | .tcb t =>
      (∀ nid, t.ipcState = .blockedOnNotification nid →
          notificationFlowGate ctx nid (SeLe4n.ThreadId.ofObjId oid) = true) ∧
        (∀ u, t.ntfnPrev = some u →
          ctx.threadLabelOf u = ctx.threadLabelOf (SeLe4n.ThreadId.ofObjId oid)) ∧
        (∀ u, t.ntfnNext = some u →
          ctx.threadLabelOf u = ctx.threadLabelOf (SeLe4n.ThreadId.ofObjId oid))
  | _ => True

/-- **Every notification's bound thread and queue ends carry its label, every
thread blocked on a notification carries the notification's, and every queue
link joins threads of one label** (`notificationEntryLabelsAgree` of every
stored object).  The label part of `notificationLabelsCoherent`, which the boot
checks (`notificationLabelsCoherent_agree`), carried across every kernel
entry. -/
def notificationLabelsAgree (ctx : LabelingContext) (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (obj : KernelObject), st.objects[oid]? = some obj →
    notificationEntryLabelsAgree ctx oid obj

/-- **Coherence implies agreement**, object by object. -/
theorem notificationEntryLabelsCoherent_agree {ctx : LabelingContext} {oid : SeLe4n.ObjId}
    {obj : KernelObject} (h : notificationEntryLabelsCoherent ctx oid obj = true) :
    notificationEntryLabelsAgree ctx oid obj := by
  cases obj with
  | notification n =>
    simp only [notificationEntryLabelsCoherent, Bool.and_eq_true, Option.all_eq_true] at h
    obtain ⟨⟨hB, hH⟩, hT⟩ := h
    exact ⟨fun t ht => hB t ht, fun t ht => hH t ht, fun t ht => hT t ht⟩
  | tcb t =>
    simp only [notificationEntryLabelsCoherent] at h
    split at h
    · rename_i nid hI
      simp only [Bool.and_eq_true, Option.all_eq_true] at h
      obtain ⟨⟨hS, hP⟩, hN⟩ := h
      have eS := (twoWayLabelGate_iff_eq _ _).mp hS
      refine ⟨fun n hn => by rw [hI] at hn; cases hn; exact hS, fun u hu => ?_, fun u hu => ?_⟩
      · exact ((twoWayLabelGate_iff_eq _ _).mp (hP u hu)).symm.trans eS
      · exact ((twoWayLabelGate_iff_eq _ _).mp (hN u hu)).symm.trans eS
    · rename_i hNot
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      refine ⟨fun n hn => absurd hn (hNot n), fun u hu => ?_, fun u hu => ?_⟩
      · simp [TCB.ntfnPrev, h.1, SeLe4n.ThreadId.ofOptCode] at hu
      · simp [TCB.ntfnNext, h.2, SeLe4n.ThreadId.ofOptCode] at hu
  | _ => trivial

/-- **The boot's check gives the carried form.** -/
theorem notificationLabelsCoherent_agree {st : SystemState} {ctx : LabelingContext}
    (h : notificationLabelsCoherent st ctx = true) : notificationLabelsAgree ctx st :=
  fun _ _ hO => notificationEntryLabelsCoherent_agree (notificationLabelsCoherent_entry h hO)

/-- What agreement says of a stored notification. -/
theorem notificationLabelsAgree_notification {st : SystemState} {ctx : LabelingContext}
    (h : notificationLabelsAgree ctx st) {nid : SeLe4n.ObjId} {ntfn : Notification}
    (hN : st.getNotification? nid = some ntfn) :
    (∀ t, ntfn.boundTCB = some t → notificationFlowGate ctx nid t = true) ∧
      (∀ t, ntfn.waitHead = some t → notificationFlowGate ctx nid t = true) ∧
      (∀ t, ntfn.waitTail = some t → notificationFlowGate ctx nid t = true) :=
  h nid _ ((SystemState.getNotification?_eq_some_iff _ _ _).mp hN)

/-- **A coherent state's signal receiver meets the notification**: the thread a
signal on `notificationId` delivers to — the bound thread on the bound-delivery
path (`boundDeliveryTarget?`), otherwise the queue head
(`notificationSignalWaiter?`) — passes the two-way gate against it, so the
notification-to-receiver flow is between equal labels. -/
theorem notificationLabelsAgree_signalReceiver {st : SystemState} {ctx : LabelingContext}
    (h : notificationLabelsAgree ctx st) {nid : SeLe4n.ObjId}
    {receiver : SeLe4n.ThreadId}
    (hR : (match boundDeliveryTarget? st nid with
      | some (t, _) => some t
      | none => notificationSignalWaiter? st nid) = some receiver) :
    notificationFlowGate ctx nid receiver = true := by
  cases hN : st.getNotification? nid with
  | none =>
    exfalso
    unfold boundDeliveryTarget? notificationSignalWaiter? at hR
    rw [hN] at hR
    simp at hR
  | some ntfn =>
    obtain ⟨hB, hH, _⟩ := notificationLabelsAgree_notification h hN
    cases hT : boundDeliveryTarget? st nid with
    | some p =>
      rw [hT] at hR
      obtain ⟨t, ep⟩ := p
      simp only [Option.some.injEq] at hR
      subst hR
      unfold boundDeliveryTarget? at hT
      rw [hN] at hT
      simp only at hT
      split at hT
      · split at hT
        · next t' hBt =>
          split at hT
          · split at hT
            · cases hT; exact hB _ hBt
            · cases hT
          · cases hT
        · cases hT
      · cases hT
    | none =>
      rw [hT] at hR
      unfold notificationSignalWaiter? at hR
      rw [hN] at hR
      exact hH _ hR

/-- The receiver half of `notificationLabelsAgree_signalReceiver` as label
equality. -/
theorem notificationLabelsAgree_signalReceiver_label {st : SystemState}
    {ctx : LabelingContext} (h : notificationLabelsAgree ctx st)
    {nid : SeLe4n.ObjId} {receiver : SeLe4n.ThreadId}
    (hR : (match boundDeliveryTarget? st nid with
      | some (t, _) => some t
      | none => notificationSignalWaiter? st nid) = some receiver) :
    ctx.objectLabelOf nid = ctx.threadLabelOf receiver :=
  (twoWayLabelGate_iff_eq _ _).mp (notificationLabelsAgree_signalReceiver h hR)


/-- **The thread a signal wakes carries the notification's label**
(`signalWokenThread?`: the bound receiver, else the queue head), so the lend
of the notification's context to it is between equal labels (WS-SX SX22, D30
retired: the check it replaced always passed). -/
theorem notificationLabelsAgree_signalWokenThread {st : SystemState}
    {ctx : LabelingContext} (h : notificationLabelsAgree ctx st)
    {nid : SeLe4n.ObjId} {t : SeLe4n.ThreadId} (hW : signalWokenThread? st nid = some t) :
    ctx.threadLabelOf t = ctx.objectLabelOf nid := by
  refine (notificationLabelsAgree_signalReceiver_label h ?_).symm
  unfold signalWokenThread? at hW
  cases hB : boundDeliveryTarget? st nid with
  | some p => rw [hB] at hW; exact hW
  | none =>
    rw [hB] at hW
    unfold notificationSignalWaiter?
    cases hN : st.getNotification? nid with
    | none => rw [hN] at hW; cases hW
    | some m => rw [hN] at hW; exact hW

end SeLe4n.Kernel
