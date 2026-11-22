-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.Defs
import SeLe4n.Kernel.Scheduler.SchedulerLinkFrame

/-!
# IPC read-view agreement

Two states agree on the **IPC read view** when every object the IPC invariant
bundle reads is the same on both sides once each thread's scheduler state (its
run-queue and reply-waiter links, its `threadState`, and the per-send capability
record), its taint words and its bound-notification code are cleared; the
binding is compared on its own (`sameNotificationBindings`).  This file holds the relation and its transport of every
conjunct of `ipcInvariantFull`.  It needs only the invariant definitions and the
scheduler-link frames, so the single-core preservation proofs below the
cross-core operations can use it too: a `threadState` store
(`ipcReadViewAgreement.of_updateTcb_threadState`), such as the `Inactive` store
of a receive that takes a `Call` linking no reply, is inside the frame.

`LookupCongruence` imports this file and builds the cross-core transports on it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §5  Read-view agreement: transports for transitions that rewrite only
--     objects the bundle never reads
-- ============================================================================

/-- Object kinds none of `ipcInvariantFull`'s queue, message, donation or reply
conjuncts read.  CNode *content* is read by exactly one clause —
`capabilityBadgesWellFormed` — which the master transport below therefore takes
as an explicit obligation for the target state; no conjunct reads a VSpaceRoot
or a piece of untyped memory at all — nor a **frame** (WS-BP BP7.1), which is a
page of memory a thread maps, not a structure any conjunct walks.  `none` is
deliberately **not** inert: a transition that deletes or creates an object of a
read kind must not slip through this frame, so only a rewrite that keeps the oid
on a non-read kind on *both* sides qualifies — and the one creation that is
sound, an absent key becoming a non-read kind, has its own lemma
(`of_fresh_inert_write`) rather than a widening of this predicate. -/
def ipcReadInert : Option KernelObject → Prop
  | some (.cnode _) => True
  | some (.vspaceRoot _) => True
  | some (.untyped _) => True
  | some (.frame _) => True
  | some (.pageTable _) => True
  | _ => False

/-- A scheduler-link clearing keeps a slot's binding view. -/
theorem notificationBindingCodes_map_withoutSchedulerLinks (o : Option KernelObject) :
    notificationBindingCodes (o.map KernelObject.withoutSchedulerLinks) =
      notificationBindingCodes o := by
  cases o with
  | none => rfl
  | some o => cases o <;> rfl

/-- A derivation-link clearing keeps a slot's binding view. -/
theorem notificationBindingCodes_map_withoutLinks (o : Option KernelObject) :
    notificationBindingCodes (o.map KernelObject.withoutLinks) =
      notificationBindingCodes o := by
  cases o with
  | none => rfl
  | some o => cases o <;> rfl

/-- An absent slot or one of a kind outside the read view holds no binding. -/
theorem notificationBindingCodes_of_absentOrInert {o : Option KernelObject}
    (h : o = none ∨ ipcReadInert o) : notificationBindingCodes o = (0, 0) := by
  rcases h with rfl | h
  · rfl
  · obtain _ | o := o
    · rfl
    · cases o <;> first | rfl | exact absurd h (by simp [ipcReadInert])

/-- A thread as every IPC bundle conjunct but the reciprocity reads it: the record
with its run-queue fields, its space-slot links, its bound-notification code,
(WS-ZA ZA5.11) its taint words and its scheduler `threadState` cleared.  The
code is read by `notificationBindingReciprocal` alone, which the whole-bundle
transports take as its own hypothesis; `threadState` is read by no IPC
conjunct (they classify a thread by its `ipcState`), so a thread made
`Inactive` -- a call that links no reply, a fault suspension -- stays inside the
frame. -/
def _root_.SeLe4n.Model.TCB.ipcReadView (t : TCB) : TCB :=
  TCB.withoutLinks { TCB.withoutRunLinks t with
    threadState := .Inactive, boundNotificationCode := 0, taintTag0 := 0, taintTag1 := 0, taintTag2 := 0, taintTag3 := 0, taintTag4 := 0,
    taintTag5 := 0, taintTag6 := 0, taintTag7 := 0, taintCount := 0, taintSaturated := false }

/-- A thread's taint words are outside its IPC read view. -/
@[simp] theorem _root_.SeLe4n.Model.TCB.ipcReadView_withTaintWords (t : TCB)
    (w : SeLe4n.Kernel.TaintWords) : (t.withTaintWords w).ipcReadView = t.ipcReadView := rfl

/-- Two TCBs with the same IPC read view: the first is the second with its
run-queue fields, space-slot links and bound-notification code rewritten. -/
theorem _root_.SeLe4n.Model.TCB.eq_withIpcReadView_of_eq {t t' : TCB}
    (e : t'.ipcReadView = t.ipcReadView) :
    t' = { t with runCoreCode := t'.runCoreCode, runPrio := t'.runPrio,
                  runPrevCode := t'.runPrevCode, runNextCode := t'.runNextCode,
                  runBucketPrevCode := t'.runBucketPrevCode,
                  runBucketNextCode := t'.runBucketNextCode,
                  replyWaiterPrevCode := t'.replyWaiterPrevCode,
                  replyWaiterNextCode := t'.replyWaiterNextCode,
                  replyWaitersHeadCode := t'.replyWaitersHeadCode,
                  replyWaitersCount := t'.replyWaitersCount,
                  ipcBadge := t'.ipcBadge, ipcBadged := t'.ipcBadged,
                  ipcCanGrant := t'.ipcCanGrant, ipcCanGrantReply := t'.ipcCanGrantReply, ipcFaultSend := t'.ipcFaultSend,
                  spaceLinks := t'.spaceLinks, threadState := t'.threadState,
                  boundNotificationCode := t'.boundNotificationCode,
                  taintTag0 := t'.taintTag0, taintTag1 := t'.taintTag1,
                  taintTag2 := t'.taintTag2, taintTag3 := t'.taintTag3,
                  taintTag4 := t'.taintTag4, taintTag5 := t'.taintTag5,
                  taintTag6 := t'.taintTag6, taintTag7 := t'.taintTag7,
                  taintCount := t'.taintCount, taintSaturated := t'.taintSaturated } := by
  cases t; cases t'
  simp only [TCB.ipcReadView, TCB.withoutRunLinks, TCB.withoutLinks, TCB.mk.injEq] at e ⊢
  simp only [e, and_self]

/-- Pointwise agreement on every object kind the IPC bundle's conjuncts read
through the store: TCBs, endpoints, notifications, replies and SchedContexts.
CNodes are deliberately absent — `capabilityBadgesWellFormed` is the one clause
that reads them, and the transitions this frame serves (capability writes,
page-table writes, untyped scrubs) exist precisely to rewrite them. -/
structure ipcReadViewAgreement (s1 s2 : SystemState) : Prop where
  /-- The TCB clauses are agreement **off the run-queue links** (WS-ZA ZA4.5)
  **and the space-slot links**: no conjunct reads the six run-queue fields,
  which are the scheduler's, nor a thread's derivation-link words, which are
  the tree's, so a run-queue or link write on either side stays inside the
  frame.  Nor does any of them read the bound-notification code: that is
  `notificationBindingReciprocal`'s, which the whole-bundle transports take
  separately, so a bind or unbind stays inside the frame too
  (`TCB.ipcReadView`). -/
  tcb : ∀ (oid : SeLe4n.ObjId) (t : TCB), s2.objects[oid]? = some (.tcb t) →
    ∃ t₀ : TCB, s1.objects[oid]? = some (.tcb t₀) ∧ t.ipcReadView = t₀.ipcReadView
  tcbFwd : ∀ (oid : SeLe4n.ObjId) (t₀ : TCB), s1.objects[oid]? = some (.tcb t₀) →
    ∃ t : TCB, s2.objects[oid]? = some (.tcb t) ∧ t.ipcReadView = t₀.ipcReadView
  /-- The endpoint clauses are agreement **off the service record**: no conjunct
  reads `Endpoint.service` (the registration flag and words), the service registry's back-link
  (`SystemState.tableBackLinksClear`), so a registration or a revocation,
  which writes it on its endpoint, stays inside the frame. -/
  endpoint : ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
    s2.objects[oid]? = some (.endpoint ep) →
    ∃ sv : EndpointService, s1.objects[oid]? = some (.endpoint (ep.withService sv))
  endpointFwd : ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
    s1.objects[oid]? = some (.endpoint ep) →
    ∃ sv : EndpointService, s2.objects[oid]? = some (.endpoint (ep.withService sv))
  /-- The notification clause is *content* agreement, not value agreement:
  every notification-reading conjunct but the reciprocity reads `state`,
  `waitHead` and `pendingBadge` only, so a rewrite that moves `boundTCB` or the
  lock word — the `.tcbBindNotification` arms — stays inside the frame. -/
  notification : ∀ (oid : SeLe4n.ObjId) (ntfn : Notification),
    s2.objects[oid]? = some (.notification ntfn) →
    ∃ ntfn₀ : Notification, s1.objects[oid]? = some (.notification ntfn₀) ∧
      ntfn₀.state = ntfn.state ∧ ntfn₀.waitHead = ntfn.waitHead ∧
      ntfn₀.pendingBadge = ntfn.pendingBadge
  reply : ∀ (oid : SeLe4n.ObjId) (r : SeLe4n.Kernel.Reply),
    s2.objects[oid]? = some (.reply r) ↔ s1.objects[oid]? = some (.reply r)
  /-- The SchedContext clause is likewise *content* agreement, stated in the
  `s1 → s2` direction the transports consume: the bundle reads only an SC's
  existence and its `boundThread`, so budget, period, priority, deadline and
  domain rewrites — the `.schedContextConfigure` and priority arms — stay
  inside the frame. -/
  schedContext : ∀ (oid : SeLe4n.ObjId) (sc : SeLe4n.Kernel.SchedContext),
    s1.objects[oid]? = some (.schedContext sc) →
    ∃ sc' : SeLe4n.Kernel.SchedContext, s2.objects[oid]? = some (.schedContext sc') ∧
      sc'.boundThread = sc.boundThread

namespace sameNotificationBindings

/-- WS-ZA ZA5.11: stores that agree off the taint words hold the same binding
codes — a word write moves no binding. -/
theorem of_objectsAgreeOffTaint {s1 s2 : SystemState}
    (h : s1.objectsAgreeOffTaint s2) : sameNotificationBindings s1 s2 := fun x => by
  have e := congrArg (Option.map KernelObject.bindingCodes) (h x)
  simp only [Option.map_map, Function.comp_def, KernelObject.eraseTaint,
    KernelObject.bindingCodes_withTaintWords] at e
  cases h2 : s2.objects[x]? <;> cases h1 : s1.objects[x]? <;> rw [h1, h2] at e <;>
    first | rfl | cases e | exact Option.some.inj e

/-- Stores that agree off the scheduler links hold the same binding codes. -/
theorem of_objectsAgreeOffSchedulerLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffSchedulerLinks s1) : sameNotificationBindings s1 s2 := fun x => by
  rw [← notificationBindingCodes_map_withoutSchedulerLinks, h x,
    notificationBindingCodes_map_withoutSchedulerLinks]

/-- Stores that agree off the run-queue links hold the same binding codes. -/
theorem of_objectsAgreeOffRunLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffRunLinks s1) : sameNotificationBindings s1 s2 :=
  of_objectsAgreeOffSchedulerLinks (.of_runLinks h)

/-- Stores that agree off the derivation links hold the same binding codes. -/
theorem of_objectsAgreeOffDerivationLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffDerivationLinks s1) : sameNotificationBindings s1 s2 := fun x => by
  rw [← notificationBindingCodes_map_withoutLinks, (h x).map_withoutLinks,
    notificationBindingCodes_map_withoutLinks]

/-- Rewrites that keep every rewritten key absent or outside the read view, on
each side, move no binding code. -/
theorem of_inertOrAbsentWrites {s1 s2 : SystemState}
    (h : ∀ oid : SeLe4n.ObjId,
      s2.objects[oid]? = s1.objects[oid]? ∨
      ((s1.objects[oid]? = none ∨ ipcReadInert s1.objects[oid]?) ∧
       (s2.objects[oid]? = none ∨ ipcReadInert s2.objects[oid]?))) :
    sameNotificationBindings s1 s2 := fun oid => by
  rcases h oid with hEq | ⟨h1, h2⟩
  · rw [hEq]
  · rw [notificationBindingCodes_of_absentOrInert h1,
      notificationBindingCodes_of_absentOrInert h2]

/-- Rewrites inert on both sides move no binding code. -/
theorem of_inertWrites {s1 s2 : SystemState}
    (h : ∀ oid : SeLe4n.ObjId,
      s2.objects[oid]? = s1.objects[oid]? ∨
      (ipcReadInert s1.objects[oid]? ∧ ipcReadInert s2.objects[oid]?)) :
    sameNotificationBindings s1 s2 :=
  of_inertOrAbsentWrites fun oid => (h oid).imp id fun ⟨h1, h2⟩ => ⟨.inr h1, .inr h2⟩

/-- One rewritten slot, inert on both sides. -/
theorem of_single_inert_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (h1 : ipcReadInert s1.objects[key]?) (h2 : ipcReadInert s2.objects[key]?) :
    sameNotificationBindings s1 s2 :=
  of_inertWrites fun oid => by
    by_cases hEq : oid = key
    · subst hEq; exact Or.inr ⟨h1, h2⟩
    · exact Or.inl (hNe oid hEq)

/-- An absent key made a non-read kind. -/
theorem of_fresh_inert_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (h1 : s1.objects[key]? = none) (h2 : ipcReadInert s2.objects[key]?) :
    sameNotificationBindings s1 s2 :=
  of_inertOrAbsentWrites fun oid => by
    by_cases hEq : oid = key
    · subst hEq; exact Or.inr ⟨.inl h1, .inr h2⟩
    · exact Or.inl (hNe oid hEq)

/-- One slot rewritten to an object with the slot's codes. -/
theorem of_single_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (hKey : notificationBindingCodes s2.objects[key]? = notificationBindingCodes s1.objects[key]?) :
    sameNotificationBindings s1 s2 := fun oid => by
  by_cases hEq : oid = key
  · subst hEq; exact hKey
  · rw [hNe oid hEq]

/-- One SchedContext rewritten: a SchedContext holds no binding code. -/
theorem of_schedContext_content_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    {sc sc' : SeLe4n.Kernel.SchedContext}
    (hPre : s1.objects[key]? = some (.schedContext sc))
    (hAt : s2.objects[key]? = some (.schedContext sc'))
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (_hBound : sc'.boundThread = sc.boundThread) :
    sameNotificationBindings s1 s2 :=
  of_single_write hNe (by rw [hAt, hPre]; rfl)

end sameNotificationBindings

/-- Lookup agreement on endpoints gives the read view's endpoint clause. -/
theorem endpointBack_of_iff {s1 s2 : SystemState}
    (h : ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
      s2.objects[oid]? = some (.endpoint ep) ↔ s1.objects[oid]? = some (.endpoint ep)) :
    ∀ (oid : SeLe4n.ObjId) (ep : Endpoint), s2.objects[oid]? = some (.endpoint ep) →
      ∃ sv : EndpointService, s1.objects[oid]? = some (.endpoint (ep.withService sv)) :=
  fun oid ep hx => ⟨ep.service, (h oid ep).mp hx⟩

/-- ...and its forward clause. -/
theorem endpointFwd_of_iff {s1 s2 : SystemState}
    (h : ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
      s2.objects[oid]? = some (.endpoint ep) ↔ s1.objects[oid]? = some (.endpoint ep)) :
    ∀ (oid : SeLe4n.ObjId) (ep : Endpoint), s1.objects[oid]? = some (.endpoint ep) →
      ∃ sv : EndpointService, s2.objects[oid]? = some (.endpoint (ep.withService sv)) :=
  fun oid ep hx => ⟨ep.service, (h oid ep).mpr hx⟩

namespace ipcReadViewAgreement

/-- **WS-ZA ZA4.5 / ZA6.3**: object stores that agree off the scheduler links are
read-view agreement — the relation a run-queue or release-queue write induces: a
context's release fields are outside its bound thread. -/
theorem of_objectsAgreeOffSchedulerLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffSchedulerLinks s1) : ipcReadViewAgreement s1 s2 :=
  ⟨fun _ _ hx => (h.get_tcb' hx).elim fun t ht =>
     ⟨t, ht.1, congrArg (fun u : TCB => TCB.withoutLinks { u with
       threadState := .Inactive, boundNotificationCode := 0, taintTag0 := 0, taintTag1 := 0, taintTag2 := 0, taintTag3 := 0, taintTag4 := 0, taintTag5 := 0, taintTag6 := 0, taintTag7 := 0, taintCount := 0, taintSaturated := false }) ht.2⟩,
   fun _ _ hx => (h.get_tcb hx).elim fun t ht =>
     ⟨t, ht.1, congrArg (fun u : TCB => TCB.withoutLinks { u with
       threadState := .Inactive, boundNotificationCode := 0, taintTag0 := 0, taintTag1 := 0, taintTag2 := 0, taintTag3 := 0, taintTag4 := 0, taintTag5 := 0, taintTag6 := 0, taintTag7 := 0, taintCount := 0, taintSaturated := false }) ht.2⟩,
   endpointBack_of_iff fun _ _ => h.get_endpoint_iff,
   endpointFwd_of_iff fun _ _ => h.get_endpoint_iff,
   fun _ ntfn hObj => ⟨ntfn, h.get_notification_iff.mp hObj, rfl, rfl, rfl⟩,
   fun _ _ => h.get_reply_iff,
   fun _ _ hSc => (h.get_sc hSc).elim fun sc' hs =>
     ⟨sc', hs.1, SeLe4n.Kernel.SchedContext.proj_eq_of_withoutRelease_eq (·.boundThread) hs.2⟩⟩

/-- **WS-ZA ZA4.5**: object stores that agree off the run-queue links are
read-view agreement — the relation a run-queue write induces. -/
theorem of_objectsAgreeOffRunLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffRunLinks s1) : ipcReadViewAgreement s1 s2 :=
  of_objectsAgreeOffSchedulerLinks (.of_runLinks h)

/-- Object stores that agree off the derivation links are read-view agreement:
a CNode is outside the view, and a thread differs only in its space-slot links. -/
theorem of_objectsAgreeOffDerivationLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffDerivationLinks s1) : ipcReadViewAgreement s1 s2 :=
  ⟨fun _ _ hx => (h.tcb_back hx).elim fun t ht =>
     ⟨t, ht.1, congrArg (fun u : TCB => { TCB.withoutRunLinks u with
       threadState := .Inactive, boundNotificationCode := 0, taintTag0 := 0, taintTag1 := 0, taintTag2 := 0, taintTag3 := 0, taintTag4 := 0, taintTag5 := 0, taintTag6 := 0, taintTag7 := 0, taintCount := 0, taintSaturated := false }) ht.2⟩,
   fun _ _ hx => (h.tcb_fwd hx).elim fun t ht =>
     ⟨t, ht.1, congrArg (fun u : TCB => { TCB.withoutRunLinks u with
       threadState := .Inactive, boundNotificationCode := 0, taintTag0 := 0, taintTag1 := 0, taintTag2 := 0, taintTag3 := 0, taintTag4 := 0, taintTag5 := 0, taintTag6 := 0, taintTag7 := 0, taintCount := 0, taintSaturated := false }) ht.2⟩,
   endpointBack_of_iff fun _ _ => h.obj_iff (fun _ e => KernelObject.noConfusion e),
   endpointFwd_of_iff fun _ _ => h.obj_iff (fun _ e => KernelObject.noConfusion e),
   fun _ ntfn hObj =>
     ⟨ntfn, h.obj_back hObj (fun _ e => KernelObject.noConfusion e), rfl, rfl, rfl⟩,
   fun _ _ => h.obj_iff (fun _ e => KernelObject.noConfusion e),
   fun _ sc hSc => ⟨sc, h.obj_fwd hSc (fun _ e => KernelObject.noConfusion e), rfl⟩⟩

/-- WS-ZA ZA5.11: **object stores that agree off the taint words are read-view
agreement** — the relation the taint step induces: a thread's taint words are
outside its read view (`TCB.ipcReadView_withTaintWords`), a notification's are
outside the content the clause reads, and every other kind holds none. -/
theorem of_objectsAgreeOffTaint {s1 s2 : SystemState}
    (h : s1.objectsAgreeOffTaint s2) : ipcReadViewAgreement s1 s2 :=
  ⟨fun _ _ hx => (h.tcb_back hx).elim fun t ⟨ht, e⟩ => ⟨t, ht,
     (TCB.ipcReadView_withTaintWords _ {}).symm.trans
       ((congrArg TCB.ipcReadView e).trans (TCB.ipcReadView_withTaintWords _ {}))⟩,
   fun _ _ hx => (h.tcb_fwd hx).elim fun t ⟨ht, e⟩ => ⟨t, ht,
     (TCB.ipcReadView_withTaintWords _ {}).symm.trans
       ((congrArg TCB.ipcReadView e).trans (TCB.ipcReadView_withTaintWords _ {}))⟩,
   endpointBack_of_iff fun oid _ => h.inert_iff oid rfl,
   endpointFwd_of_iff fun oid _ => h.inert_iff oid rfl,
   fun _ _ hx => (h.notification_back hx).elim fun n ⟨hn, e⟩ =>
     ⟨n, hn, (congrArg Notification.state e).symm, (congrArg Notification.waitHead e).symm,
       (congrArg Notification.pendingBadge e).symm⟩,
   fun oid _ => h.inert_iff oid rfl,
   fun oid sc hSc => ⟨sc, (h.inert_iff oid rfl).mpr hSc, rfl⟩⟩

/-- Full pointwise lookup agreement is read-view agreement. -/
theorem of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?) :
    ipcReadViewAgreement s1 s2 :=
  of_objectsAgreeOffRunLinks (.of_getElem_eq hEq)

/-- The frame the capability, VSpace and untyped-scrub transitions induce:
lookups agree except at rewritten oids, and every rewritten oid holds a kind
outside the read view in **both** states. -/
theorem of_inertWrites {s1 s2 : SystemState}
    (h : ∀ oid : SeLe4n.ObjId,
      s2.objects[oid]? = s1.objects[oid]? ∨
      (ipcReadInert s1.objects[oid]? ∧ ipcReadInert s2.objects[oid]?)) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), ¬ ipcReadInert (some o) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNotInert
    rcases h oid with hEq | ⟨h1, h2⟩
    · rw [hEq]
    · constructor
      · intro hx; rw [hx] at h2; exact absurd h2 hNotInert
      · intro hx; rw [hx] at h1; exact absurd h1 hNotInert
  exact ⟨fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mp h, rfl⟩,
         fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mpr h, rfl⟩,
         endpointBack_of_iff (fun oid ep => step oid (.endpoint ep) (by simp [ipcReadInert])),
         endpointFwd_of_iff (fun oid ep => step oid (.endpoint ep) (by simp [ipcReadInert])),
         fun oid ntfn hObj =>
           ⟨ntfn, (step oid (.notification ntfn) (by simp [ipcReadInert])).mp hObj,
             rfl, rfl, rfl⟩,
         fun oid r => step oid (.reply r) (by simp [ipcReadInert]),
         fun oid sc hSc =>
           ⟨sc, (step oid (.schedContext sc) (by simp [ipcReadInert])).mpr hSc, rfl⟩⟩

/-- The single-oid instance: one rewritten slot, inert on both sides — the
shape of every CNode-slot write and every page-table update. -/
theorem of_single_inert_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (h1 : ipcReadInert s1.objects[key]?) (h2 : ipcReadInert s2.objects[key]?) :
    ipcReadViewAgreement s1 s2 :=
  of_inertWrites fun oid => by
    by_cases hEq : oid = key
    · subst hEq; exact Or.inr ⟨h1, h2⟩
    · exact Or.inl (hNe oid hEq)

/-- **WS-BP BP7.1**: the creation instance — a key that held **no** object and
now holds one of a non-read kind.  Sound for the reason `ipcReadInert` excludes
`none` on both sides: a read-kind lookup is `some` of that kind, which neither an
absent key nor a non-read object is, so every read-kind lookup agrees.  The shape
of the frame an untyped carve creates. -/
theorem of_fresh_inert_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (h1 : s1.objects[key]? = none) (h2 : ipcReadInert s2.objects[key]?) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), ¬ ipcReadInert (some o) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNotInert
    by_cases hK : oid = key
    · subst hK
      rw [h1]
      constructor
      · intro hx; rw [hx] at h2; exact absurd h2 hNotInert
      · intro hx; cases hx
    · rw [hNe oid hK]
  exact ⟨fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mp h, rfl⟩,
         fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mpr h, rfl⟩,
         endpointBack_of_iff (fun oid ep => step oid (.endpoint ep) (by simp [ipcReadInert])),
         endpointFwd_of_iff (fun oid ep => step oid (.endpoint ep) (by simp [ipcReadInert])),
         fun oid ntfn hObj =>
           ⟨ntfn, (step oid (.notification ntfn) (by simp [ipcReadInert])).mp hObj,
             rfl, rfl, rfl⟩,
         fun oid r => step oid (.reply r) (by simp [ipcReadInert]),
         fun oid sc hSc =>
           ⟨sc, (step oid (.schedContext sc) (by simp [ipcReadInert])).mpr hSc, rfl⟩⟩

/-- **WS-BP BP7.1 slice 3**: the general form of the two instances above — every
rewritten key holds, on **each** side independently, either nothing or a kind
outside the read view.  Covers creation (absent → inert), rewriting (inert →
inert) and **erasure** (inert → absent) at once, which is the shape a memory
object's final delete induces: VSpace roots rewritten, frames erased, the
untyped rewritten. -/
theorem of_inertOrAbsentWrites {s1 s2 : SystemState}
    (h : ∀ oid : SeLe4n.ObjId,
      s2.objects[oid]? = s1.objects[oid]? ∨
      ((s1.objects[oid]? = none ∨ ipcReadInert s1.objects[oid]?) ∧
       (s2.objects[oid]? = none ∨ ipcReadInert s2.objects[oid]?))) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), ¬ ipcReadInert (some o) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNotInert
    rcases h oid with hEq | ⟨h1, h2⟩
    · rw [hEq]
    · constructor
      · intro hx; rw [hx] at h2
        rcases h2 with h2 | h2
        · cases h2
        · exact absurd h2 hNotInert
      · intro hx; rw [hx] at h1
        rcases h1 with h1 | h1
        · cases h1
        · exact absurd h1 hNotInert
  exact ⟨fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mp h, rfl⟩,
         fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mpr h, rfl⟩,
         endpointBack_of_iff (fun oid ep => step oid (.endpoint ep) (by simp [ipcReadInert])),
         endpointFwd_of_iff (fun oid ep => step oid (.endpoint ep) (by simp [ipcReadInert])),
         fun oid ntfn hObj =>
           ⟨ntfn, (step oid (.notification ntfn) (by simp [ipcReadInert])).mp hObj,
             rfl, rfl, rfl⟩,
         fun oid r => step oid (.reply r) (by simp [ipcReadInert]),
         fun oid sc hSc =>
           ⟨sc, (step oid (.schedContext sc) (by simp [ipcReadInert])).mpr hSc, rfl⟩⟩

/-- A single notification rewrite preserving queue content — `state`,
`waitHead`, `pendingBadge`; `boundTCB`, the tail and the lock word are free —
is read-view agreement.  The `.tcbBindNotification` /
`.tcbUnbindNotification` arms' notification store is exactly this shape. -/
theorem of_notification_content_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    {ntfn ntfn' : Notification}
    (hPre : s1.objects[key]? = some (.notification ntfn))
    (hAt : s2.objects[key]? = some (.notification ntfn'))
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (hState : ntfn'.state = ntfn.state)
    (hWaiters : ntfn'.waitHead = ntfn.waitHead)
    (hBadge : ntfn'.pendingBadge = ntfn.pendingBadge) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject),
      (∀ n : Notification, o ≠ .notification n) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNo
    by_cases hK : oid = key
    · subst hK
      rw [hPre, hAt]
      constructor
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo ntfn')
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo ntfn)
    · rw [hNe oid hK]
  refine ⟨fun oid t h => ⟨t, (step oid (.tcb t) (fun n h => KernelObject.noConfusion h)).mp h, rfl⟩,
          fun oid t h => ⟨t, (step oid (.tcb t) (fun n h => KernelObject.noConfusion h)).mpr h, rfl⟩,
          endpointBack_of_iff (fun oid ep => step oid (.endpoint ep) (fun n h => KernelObject.noConfusion h)),
          endpointFwd_of_iff (fun oid ep => step oid (.endpoint ep) (fun n h => KernelObject.noConfusion h)),
          fun oid n hObj => ?_,
          fun oid r => step oid (.reply r) (fun n h => KernelObject.noConfusion h),
          fun oid sc hSc =>
            ⟨sc, (step oid (.schedContext sc)
              (fun n h => KernelObject.noConfusion h)).mpr hSc, rfl⟩⟩
  by_cases hK : oid = key
  · subst hK
    rw [hAt] at hObj
    obtain rfl : ntfn' = n := by
      simpa only [Option.some.injEq, KernelObject.notification.injEq] using hObj
    exact ⟨ntfn, hPre, hState.symm, hWaiters.symm, hBadge.symm⟩
  · rw [hNe oid hK] at hObj
    exact ⟨n, hObj, rfl, rfl, rfl⟩

/-- A single TCB rewrite that keeps the thread's IPC read view — run links,
space-slot links and the bound-notification code are free — is read-view
agreement.  The bind and unbind arms' thread store is exactly this shape. -/
theorem of_tcb_ipcReadView_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    {t t' : TCB}
    (hPre : s1.objects[key]? = some (.tcb t))
    (hAt : s2.objects[key]? = some (.tcb t'))
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (hView : t'.ipcReadView = t.ipcReadView) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), (∀ x : TCB, o ≠ .tcb x) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNo
    by_cases hK : oid = key
    · subst hK
      rw [hPre, hAt]
      constructor
      · intro hx; exact absurd (Option.some.inj hx).symm (hNo t')
      · intro hx; exact absurd (Option.some.inj hx).symm (hNo t)
    · rw [hNe oid hK]
  refine ⟨fun oid x h => ?_, fun oid x h => ?_,
          endpointBack_of_iff (fun oid ep => step oid (.endpoint ep) (fun _ h => KernelObject.noConfusion h)),
          endpointFwd_of_iff (fun oid ep => step oid (.endpoint ep) (fun _ h => KernelObject.noConfusion h)),
          fun oid n hObj =>
            ⟨n, (step oid (.notification n) (fun _ h => KernelObject.noConfusion h)).mp hObj,
              rfl, rfl, rfl⟩,
          fun oid r => step oid (.reply r) (fun _ h => KernelObject.noConfusion h),
          fun oid sc hSc =>
            ⟨sc, (step oid (.schedContext sc) (fun _ h => KernelObject.noConfusion h)).mpr hSc,
              rfl⟩⟩
  · by_cases hK : oid = key
    · subst hK
      rw [hAt] at h; cases h
      exact ⟨t, hPre, hView⟩
    · rw [hNe oid hK] at h; exact ⟨x, h, rfl⟩
  · by_cases hK : oid = key
    · subst hK
      rw [hPre] at h; cases h
      exact ⟨t', hAt, hView⟩
    · exact ⟨x, by rw [hNe oid hK]; exact h, rfl⟩

/-- **A `threadState` store is read-view agreement**: the scheduler state is
outside the IPC read view, so making a thread `Inactive` (a call that links no
reply, a fault suspension) is inside the frame. -/
theorem of_updateTcb_threadState (s : SystemState) (tid : SeLe4n.ThreadId)
    (ts : ThreadState) (hInv : s.objects.invExt) :
    ipcReadViewAgreement s (s.updateTcb tid fun t => { t with threadState := ts }) := by
  cases hT : s.getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact .of_getElem_eq (fun _ => rfl)
  | some t =>
    exact of_tcb_ipcReadView_write (key := tid.toObjId) (t := t) (t' := { t with threadState := ts })
      ((SystemState.getTcb?_eq_some_iff s tid t).mp hT)
      ((SystemState.getTcb?_eq_some_iff _ tid _).mp
        (by rw [SystemState.updateTcb_getTcb?_self s tid _ hInv, hT]; rfl))
      (fun oid hNe => SystemState.updateTcb_objects_ne s tid _ oid (Ne.symm hNe) hInv) rfl

/-- A single SchedContext rewrite preserving `boundThread` — budget, period,
priority, deadline, domain and the lock word are free — is read-view
agreement.  The `.schedContextConfigure` arm's store and the priority arms'
SC-priority update are exactly this shape. -/
theorem of_schedContext_content_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    {sc sc' : SeLe4n.Kernel.SchedContext}
    (hPre : s1.objects[key]? = some (.schedContext sc))
    (hAt : s2.objects[key]? = some (.schedContext sc'))
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (hBound : sc'.boundThread = sc.boundThread) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject),
      (∀ x : SeLe4n.Kernel.SchedContext, o ≠ .schedContext x) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNo
    by_cases hK : oid = key
    · subst hK
      rw [hPre, hAt]
      constructor
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo sc')
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo sc)
    · rw [hNe oid hK]
  refine ⟨fun oid t h => ⟨t, (step oid (.tcb t) (fun x h => KernelObject.noConfusion h)).mp h, rfl⟩,
          fun oid t h => ⟨t, (step oid (.tcb t) (fun x h => KernelObject.noConfusion h)).mpr h, rfl⟩,
          endpointBack_of_iff (fun oid ep => step oid (.endpoint ep) (fun x h => KernelObject.noConfusion h)),
          endpointFwd_of_iff (fun oid ep => step oid (.endpoint ep) (fun x h => KernelObject.noConfusion h)),
          fun oid n hObj =>
            ⟨n, (step oid (.notification n)
              (fun x h => KernelObject.noConfusion h)).mp hObj, rfl, rfl, rfl⟩,
          fun oid r => step oid (.reply r) (fun x h => KernelObject.noConfusion h),
          fun oid x hSc => ?_⟩
  by_cases hK : oid = key
  · subst hK
    rw [hPre] at hSc
    obtain rfl : sc = x := by
      simpa only [Option.some.injEq, KernelObject.schedContext.injEq] using hSc
    exact ⟨sc', hAt, hBound⟩
  · rw [← hNe oid hK] at hSc
    exact ⟨x, hSc, rfl⟩

/-- Read-view agreement composes. -/
theorem trans {s1 s2 s3 : SystemState}
    (hFore : ipcReadViewAgreement s1 s2) (hAft : ipcReadViewAgreement s2 s3) :
    ipcReadViewAgreement s1 s3 :=
  ⟨fun oid t h3 => by
     obtain ⟨t2, h2, e2⟩ := hAft.tcb oid t h3
     obtain ⟨t1, h1, e1⟩ := hFore.tcb oid t2 h2
     exact ⟨t1, h1, e2.trans e1⟩,
   fun oid t h1 => by
     obtain ⟨t2, h2, e2⟩ := hFore.tcbFwd oid t h1
     obtain ⟨t3, h3, e3⟩ := hAft.tcbFwd oid t2 h2
     exact ⟨t3, h3, e3.trans e2⟩,
   fun oid ep h3 => by
     obtain ⟨_, h2⟩ := hAft.endpoint oid ep h3
     obtain ⟨c1, h1⟩ := hFore.endpoint oid _ h2
     exact ⟨c1, h1⟩,
   fun oid ep h1 => by
     obtain ⟨_, h2⟩ := hFore.endpointFwd oid ep h1
     obtain ⟨c3, h3⟩ := hAft.endpointFwd oid _ h2
     exact ⟨c3, h3⟩,
   fun oid n h3 => by
     obtain ⟨n2, h2, hS2, hW2, hB2⟩ := hAft.notification oid n h3
     obtain ⟨n1, h1, hS1, hW1, hB1⟩ := hFore.notification oid n2 h2
     exact ⟨n1, h1, hS1.trans hS2, hW1.trans hW2, hB1.trans hB2⟩,
   fun oid r => (hAft.reply oid r).trans (hFore.reply oid r),
   fun oid sc h1 => by
     obtain ⟨sc2, h2, hB2⟩ := hFore.schedContext oid sc h1
     obtain ⟨sc3, h3, hB3⟩ := hAft.schedContext oid sc2 h2
     exact ⟨sc3, h3, hB3.trans hB2⟩⟩

/-- A TCB of `s2` is a TCB of `s1` with its run-queue fields rewritten — the
form `run_links_back` substitutes. -/
theorem get_tcb_back {s1 s2 : SystemState} (hView : ipcReadViewAgreement s1 s2)
    {x : SeLe4n.ObjId} {t' : TCB} (hx : s2.objects[x]? = some (.tcb t')) :
    ∃ t : TCB, ∃ (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx rwp rwn rwh rwc : Nat) (ib : UInt64) (ibd icg icgr ifs : Bool)
      (sl : Vector Nat (slotLinkWords * 4)) (ts : ThreadState) (bnc : Nat) (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64)
      (wc : Nat) (ws : Bool),
      s1.objects[x]? = some (.tcb t) ∧
      t' = { t with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                    runBucketPrevCode := rbpv, runBucketNextCode := rbnx,
                    replyWaiterPrevCode := rwp, replyWaiterNextCode := rwn,
                    replyWaitersHeadCode := rwh, replyWaitersCount := rwc,
                    ipcBadge := ib, ipcBadged := ibd, ipcCanGrant := icg, ipcCanGrantReply := icgr, ipcFaultSend := ifs,
                    spaceLinks := sl, threadState := ts, boundNotificationCode := bnc,
                    taintTag0 := w0, taintTag1 := w1, taintTag2 := w2, taintTag3 := w3,
                    taintTag4 := w4, taintTag5 := w5, taintTag6 := w6, taintTag7 := w7,
                    taintCount := wc, taintSaturated := ws } := by
  obtain ⟨t, ht, e⟩ := hView.tcb x t' hx
  exact ⟨t, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, TCB.eq_withIpcReadView_of_eq e⟩

/-- The same, from `s1` to `s2` — the form `run_links_fwd` substitutes. -/
theorem get_tcb_fwd {s1 s2 : SystemState} (hView : ipcReadViewAgreement s1 s2)
    {x : SeLe4n.ObjId} {t : TCB} (hx : s1.objects[x]? = some (.tcb t)) :
    ∃ t' : TCB, ∃ (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx rwp rwn rwh rwc : Nat) (ib : UInt64) (ibd icg icgr ifs : Bool)
      (sl : Vector Nat (slotLinkWords * 4)) (ts : ThreadState) (bnc : Nat) (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64)
      (wc : Nat) (ws : Bool),
      s2.objects[x]? = some (.tcb t') ∧
      t = { t' with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                    runBucketPrevCode := rbpv, runBucketNextCode := rbnx,
                    replyWaiterPrevCode := rwp, replyWaiterNextCode := rwn,
                    replyWaitersHeadCode := rwh, replyWaitersCount := rwc,
                    ipcBadge := ib, ipcBadged := ibd, ipcCanGrant := icg, ipcCanGrantReply := icgr, ipcFaultSend := ifs,
                    spaceLinks := sl, threadState := ts, boundNotificationCode := bnc,
                    taintTag0 := w0, taintTag1 := w1, taintTag2 := w2, taintTag3 := w3,
                    taintTag4 := w4, taintTag5 := w5, taintTag6 := w6, taintTag7 := w7,
                    taintCount := wc, taintSaturated := ws } := by
  obtain ⟨t', ht, e⟩ := hView.tcbFwd x t hx
  exact ⟨t', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, TCB.eq_withIpcReadView_of_eq e.symm⟩

/-- The typed-getter form of the reply clause. -/
theorem getReply?_iff {s1 s2 : SystemState} (hView : ipcReadViewAgreement s1 s2)
    (rid : SeLe4n.ReplyId) (r : SeLe4n.Kernel.Reply) :
    s2.getReply? rid = some r ↔ s1.getReply? rid = some r :=
  (SystemState.getReply?_eq_some_iff s2 rid r).trans
    ((hView.reply rid.toObjId r).trans (SystemState.getReply?_eq_some_iff s1 rid r).symm)

end ipcReadViewAgreement

/-- Read-view transport of a `queueNext` reachability path. -/
theorem QueueNextPath_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) {a b : SeLe4n.ThreadId}
    (hp : QueueNextPath s2 a b) : QueueNextPath s1 a b := by
  induction hp with
  | single x y tcbA hObj hNext =>
    run_links_back hView at tcbA hObj
    exact .single x y tcbA hObj hNext
  | cons x y z tcbA hObj hNext _ ih =>
    run_links_back hView at tcbA hObj
    exact .cons x y z tcbA hObj hNext ih

/-- **WS-RR RR8.3**: read-view transport of the pairing.  The view's `tcb`
clause is full-record agreement, so the pair travels with the record. -/
theorem queuePPrevAgreesWithPrev_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) (h : queuePPrevAgreesWithPrev s1) :
    queuePPrevAgreesWithPrev s2 :=
  fun tid tcb hTcb => by
    run_links_back hView at tcb hTcb
    exact h tid tcb hTcb

/-- Read-view transport of TCB-queue chain acyclicity. -/
theorem tcbQueueChainAcyclic_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : tcbQueueChainAcyclic s1) : tcbQueueChainAcyclic s2 :=
  fun tid hp => h tid (QueueNextPath_of_readViewAgreement hView hp)

/-- Read-view transport of doubly-linked TCB-queue link integrity. -/
theorem tcbQueueLinkIntegrity_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : tcbQueueLinkIntegrity s1) : tcbQueueLinkIntegrity s2 := by
  obtain ⟨hFwd, hRev⟩ := h
  refine ⟨fun a tcbA hA b hNext => ?_, fun b tcbB hB a hPrev => ?_⟩
  · run_links_back hView at tcbA hA
    obtain ⟨tcbB, hB, hPrev⟩ := hFwd a tcbA hA b hNext
    run_links_fwd hView at tcbB hB
    exact ⟨_, hB, hPrev⟩
  · run_links_back hView at tcbB hB
    obtain ⟨tcbA, hA, hNext⟩ := hRev b tcbB hB a hPrev
    run_links_fwd hView at tcbA hA
    exact ⟨_, hA, hNext⟩

/-- Read-view transport of single-queue well-formedness. -/
theorem intrusiveQueueWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) {q : IntrusiveQueue}
    (h : intrusiveQueueWellFormed q s1) : intrusiveQueueWellFormed q s2 := by
  obtain ⟨hP1, hP2, hP3⟩ := h
  refine ⟨hP1, fun hd hHead => ?_, fun tl hTail => ?_⟩
  · obtain ⟨tcb, hObj, hPrev⟩ := hP2 hd hHead
    run_links_fwd hView at tcb hObj
    exact ⟨_, hObj, hPrev⟩
  · obtain ⟨tcb, hObj, hNext⟩ := hP3 tl hTail
    run_links_fwd hView at tcb hObj
    exact ⟨_, hObj, hNext⟩

/-- Read-view transport of an endpoint's dual-queue well-formedness. -/
theorem dualQueueEndpointWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) {epId : SeLe4n.ObjId}
    (h : dualQueueEndpointWellFormed epId s1) : dualQueueEndpointWellFormed epId s2 := by
  unfold dualQueueEndpointWellFormed at h ⊢
  cases hObj : s2.objects[epId]? with
  | none => trivial
  | some obj =>
    cases obj with
    | endpoint ep =>
      obtain ⟨_, hObj'⟩ := hView.endpoint _ _ hObj
      rw [hObj'] at h
      exact ⟨intrusiveQueueWellFormed_of_readViewAgreement hView h.1,
             intrusiveQueueWellFormed_of_readViewAgreement hView h.2⟩
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ =>
      trivial

/-- Read-view transport of the dual-queue system invariant. -/
theorem dualQueueSystemInvariant_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : dualQueueSystemInvariant s1) : dualQueueSystemInvariant s2 := by
  obtain ⟨hEp, hLink, hAcyc, hPP, hHD⟩ := h
  refine ⟨fun epId ep hObj => ?_,
          tcbQueueLinkIntegrity_of_readViewAgreement hView hLink,
          tcbQueueChainAcyclic_of_readViewAgreement hView hAcyc,
          queuePPrevAgreesWithPrev_of_readViewAgreement hView hPP,
          -- **PR #897 review**: the read view agrees on endpoints, which is all the
          -- fifth conjunct reads.
          fun epA epB eA eB hd recvA recvB hA hB =>
            let ⟨cA, hA'⟩ := hView.endpoint _ _ hA
            let ⟨cB, hB'⟩ := hView.endpoint _ _ hB
            hHD epA epB (eA.withService cA) (eB.withService cB) hd recvA recvB
              hA' hB'⟩
  obtain ⟨_, hObj⟩ := hView.endpoint _ _ hObj
  exact dualQueueEndpointWellFormed_of_readViewAgreement hView (hEp epId _ hObj)

/-- Read-view transport of pending-message boundedness. -/
theorem allPendingMessagesBounded_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : allPendingMessagesBounded s1) : allPendingMessagesBounded s2 := by
  intro tid tcb msg hObj hPend
  run_links_back hView at tcb hObj
  exact h tid tcb msg hObj hPend

/-- Read-view transport of the generic in-flight-message family. -/
theorem pendingMessagesSatisfy_of_readViewAgreement {P : IpcMessage → Prop} {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : pendingMessagesSatisfy P s1) : pendingMessagesSatisfy P s2 := by
  intro tid tcb msg hObj hPend
  run_links_back hView at tcb hObj
  exact h tid tcb msg hObj hPend

/-- Read-view transport of the notification half of `badgeWellFormed`. -/
theorem notificationBadgesWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : notificationBadgesWellFormed s1) : notificationBadgesWellFormed s2 := by
  intro oid ntfn badge hObj hBadge
  obtain ⟨ntfn₀, hL, _, _, hB⟩ := hView.notification oid ntfn hObj
  exact h oid ntfn₀ badge hL (hB.trans hBadge)

/-- Read-view transport of notification well-formedness. -/
theorem ipcInvariant_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : ipcInvariant s1) : ipcInvariant s2 := by
  intro oid ntfn hObj
  obtain ⟨ntfn₀, hL, hS, hW, hB⟩ := hView.notification oid ntfn hObj
  have h₀ := h oid ntfn₀ hL
  unfold notificationInvariant notificationQueueWellFormed at h₀ ⊢
  rw [← hS, ← hW, ← hB]
  exact h₀

/-- Read-view transport of `blockedThreadsPendingMessageConsistent`. -/
theorem blockedThreadsPendingMessageConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : blockedThreadsPendingMessageConsistent s1) :
    blockedThreadsPendingMessageConsistent s2 := by
  intro tid tcb hObj
  run_links_back hView at tcb hObj
  exact h tid tcb hObj

/-- Read-view transport of `endpointQueueNoDup`. -/
theorem endpointQueueNoDup_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : endpointQueueNoDup s1) : endpointQueueNoDup s2 := by
  intro oid ep hEp
  obtain ⟨_, hEp⟩ := hView.endpoint _ _ hEp
  obtain ⟨hSelf, hDisj⟩ := h oid _ hEp
  refine ⟨fun tid tcb hTcb => ?_, hDisj⟩
  run_links_back hView at tcb hTcb
  exact hSelf tid tcb hTcb

/-- Read-view transport of `ipcStateQueueMembershipConsistent`. -/
theorem ipcStateQueueMembershipConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : ipcStateQueueMembershipConsistent s1) : ipcStateQueueMembershipConsistent s2 := by
  intro tid tcb hTcb
  run_links_back hView at tcb hTcb
  have hG := h tid tcb hTcb
  cases hIpc : tcb.ipcState with
  | blockedOnSend epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      obtain ⟨_, hEp⟩ := hView.endpointFwd _ _ hEp
      refine ⟨_, hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · run_links_fwd hView at prevTcb hPrev
        exact Or.inr ⟨prev, _, hPrev, hNext⟩
  | blockedOnReceive epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      obtain ⟨_, hEp⟩ := hView.endpointFwd _ _ hEp
      refine ⟨_, hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · run_links_fwd hView at prevTcb hPrev
        exact Or.inr ⟨prev, _, hPrev, hNext⟩
  | blockedOnCall epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      obtain ⟨_, hEp⟩ := hView.endpointFwd _ _ hEp
      refine ⟨_, hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · run_links_fwd hView at prevTcb hPrev
        exact Or.inr ⟨prev, _, hPrev, hNext⟩
  | ready => trivial
  | blockedOnNotification nid => trivial
  | blockedOnReply ep rt => trivial

/-- Read-view transport of `queueNextBlockingConsistent`. -/
theorem queueNextBlockingConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : queueNextBlockingConsistent s1) : queueNextBlockingConsistent s2 := by
  intro a b tcbA tcbB hA hB hNext
  run_links_back hView at tcbA hA; run_links_back hView at tcbB hB
  exact h a b tcbA tcbB hA hB hNext

/-- Read-view transport of `queueHeadBlockedConsistent`. -/
theorem queueHeadBlockedConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : queueHeadBlockedConsistent s1) : queueHeadBlockedConsistent s2 := by
  intro epId ep hd tcb hEp hTcb
  obtain ⟨c, hEp⟩ := hView.endpoint _ _ hEp
  run_links_back hView at tcb hTcb
  exact h epId (ep.withService c) hd tcb hEp hTcb

/-- Read-view transport of `ipcStateQueueConsistent`: a thread's `ipcState` is
in the view, and an endpoint a blocked thread names is still there. -/
theorem ipcStateQueueConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : ipcStateQueueConsistent s1) : ipcStateQueueConsistent s2 := by
  intro tid tcb hTcb
  obtain ⟨t0, h0, e⟩ := hView.tcb _ tcb hTcb
  have hI := congrArg TCB.ipcState e
  change tcb.ipcState = t0.ipcState at hI
  have h1 := h tid t0 h0
  have fwd : ∀ epId, (∃ ep, s1.objects[epId]? = some (KernelObject.endpoint ep)) →
      ∃ ep, s2.objects[epId]? = some (KernelObject.endpoint ep) := fun epId ⟨ep, hEp⟩ =>
    let ⟨sv, h2⟩ := hView.endpointFwd epId ep hEp
    ⟨_, h2⟩
  rw [hI]
  revert h1
  cases t0.ipcState <;> simp only [] <;> first | exact fwd _ | exact fun _ => trivial

/-- Read-view transport of `blockedThreadTimeoutConsistent`. -/
theorem blockedThreadTimeoutConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : blockedThreadTimeoutConsistent s1) : blockedThreadTimeoutConsistent s2 := by
  intro tid tcb scId hTcb hBudget
  run_links_back hView at tcb hTcb
  obtain ⟨⟨sc, hSc⟩, hBlk⟩ := h tid tcb scId hTcb hBudget
  obtain ⟨sc', hSc', _⟩ := hView.schedContext _ sc hSc
  exact ⟨⟨sc', hSc'⟩, hBlk⟩

/-- Read-view transport of `allTimeoutBudgetsNone`. -/
theorem allTimeoutBudgetsNone_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : allTimeoutBudgetsNone s1) : allTimeoutBudgetsNone s2 := by
  intro tid tcb hTcb
  run_links_back hView at tcb hTcb
  exact h tid tcb hTcb

/-- Read-view transport of `donationChainAcyclic`. -/
theorem donationChainAcyclic_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationChainAcyclic s1) : donationChainAcyclic s2 := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
  run_links_back hView at tcb1 h1; run_links_back hView at tcb2 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2

/-- Read-view transport of `donationOwnerValid`. -/
theorem donationOwnerValid_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationOwnerValid s1) : donationOwnerValid s2 := by
  intro tid tcb scId owner hTcb hBind
  run_links_back hView at tcb hTcb
  obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOwner, hUnbound, hReply⟩⟩ :=
    h tid tcb scId owner hTcb hBind
  obtain ⟨sc', hSc', hBT⟩ := hView.schedContext _ sc hSc
  run_links_fwd hView at ownerTcb hOwner
  exact ⟨⟨sc', hSc', hBT.trans hBound⟩, ⟨_, hOwner, hUnbound, hReply⟩⟩

/-- Read-view transport of `donationBudgetTransfer`. -/
theorem donationBudgetTransfer_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationBudgetTransfer s1) : donationBudgetTransfer s2 := by
  intro tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2
  run_links_back hView at tcb1 h1; run_links_back hView at tcb2 h2
  exact h tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2

/-- Read-view transport of `replyCallerLinkageReciprocal`. -/
theorem replyCallerLinkageReciprocal_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : replyCallerLinkageReciprocal s1) : replyCallerLinkageReciprocal s2 := by
  refine ⟨fun tid tcb rid hTcb hRep => ?_, fun rid r tid hRep hCaller => ?_⟩
  · run_links_back hView at tcb hTcb
    obtain ⟨r, hR, hBack⟩ := h.1 tid tcb rid hTcb hRep
    exact ⟨r, (hView.reply _ _).mpr hR, hBack⟩
  · rw [hView.reply] at hRep
    obtain ⟨tcb, hTcb, hFwd, hBlk⟩ := h.2 rid r tid hRep hCaller
    run_links_fwd hView at tcb hTcb
    exact ⟨_, hTcb, hFwd, hBlk⟩

/-- Read-view transport of `blockedOnReplyHasReplyObject`. -/
theorem blockedOnReplyHasReplyObject_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : blockedOnReplyHasReplyObject s1) : blockedOnReplyHasReplyObject s2 := by
  intro tid tcb ep rt hTcb hIpc
  run_links_back hView at tcb hTcb
  exact h tid tcb ep rt hTcb hIpc

/-- Read-view transport of `replyCallerLinkage`. -/
theorem replyCallerLinkage_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : replyCallerLinkage s1) : replyCallerLinkage s2 :=
  ⟨replyCallerLinkageReciprocal_of_readViewAgreement hView h.1,
   blockedOnReplyHasReplyObject_of_readViewAgreement hView h.2⟩

/-- Read-view transport of `pendingReceiveReplyWellFormed`. -/
theorem pendingReceiveReplyWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : pendingReceiveReplyWellFormed s1) : pendingReceiveReplyWellFormed s2 := by
  refine ⟨fun tid tcb rid hTcb hStash => ?_,
          fun tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hS1 hS2 => ?_,
          fun tid tcb rid hTcb hStash => ?_⟩
  · rw [SystemState.getTcb?_eq_some_iff] at hTcb
    run_links_back hView at tcb hTcb
    rw [← SystemState.getTcb?_eq_some_iff] at hTcb
    obtain ⟨hRecv, ⟨r, hR, hFree⟩⟩ := h.1 tid tcb rid hTcb hStash
    exact ⟨hRecv, ⟨r, (hView.getReply?_iff _ _).mpr hR, hFree⟩⟩
  · rw [SystemState.getTcb?_eq_some_iff] at h1 h2
    run_links_back hView at tcb₁ h1; run_links_back hView at tcb₂ h2
    rw [← SystemState.getTcb?_eq_some_iff] at h1 h2
    exact h.2.1 tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hS1 hS2
  · rw [SystemState.getTcb?_eq_some_iff] at hTcb
    run_links_back hView at tcb hTcb
    rw [← SystemState.getTcb?_eq_some_iff] at hTcb
    obtain ⟨r, hR, hS⟩ := h.2.2 tid tcb rid hTcb hStash
    exact ⟨r, (hView.getReply?_iff _ _).mpr hR, hS⟩

/-- Read-view transport of `donationOwnerUnique`. -/
theorem donationOwnerUnique_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationOwnerUnique s1) : donationOwnerUnique s2 := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
  run_links_back hView at tcb1 h1; run_links_back hView at tcb2 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2

/-- Read-view transport of `endpointQueueTailBlockedConsistent`. -/
theorem endpointQueueTailBlockedConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : endpointQueueTailBlockedConsistent s1) : endpointQueueTailBlockedConsistent s2 := by
  intro epId ep tl tcb hEp hTcb
  obtain ⟨c, hEp⟩ := hView.endpoint _ _ hEp
  run_links_back hView at tcb hTcb
  exact h epId (ep.withService c) tl tcb hEp hTcb

/-- Read-view transport of `queueNextTargetBlocked`. -/
theorem queueNextTargetBlocked_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : queueNextTargetBlocked s1) : queueNextTargetBlocked s2 := by
  intro a b tcbA tcbB hA hB hNext
  run_links_back hView at tcbA hA; run_links_back hView at tcbB hB
  exact h a b tcbA tcbB hA hB hNext

/-- Read-view transport of `endpointQueueLinksOnlyBlocked`. -/
theorem endpointQueueLinksOnlyBlocked_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : endpointQueueLinksOnlyBlocked s1) : endpointQueueLinksOnlyBlocked s2 := by
  intro a tcbA hA hNext
  run_links_back hView at tcbA hA
  exact h a tcbA hA hNext

/-- **The read-view master transport**: two states agreeing on every object
kind the bundle reads satisfy the eighteen conjuncts that read neither a CNode
nor a binding code interchangeably; the CNode-reading clause
(`capabilityBadgesWellFormed`) and the binding reciprocity are supplied for the
target state.  This is the lever that carries the whole bundle across the
capability, VSpace and untyped-scrub dispatch arms, whose writes the bundle
never reads, and across the bind and unbind arms, whose writes only the
reciprocity reads. -/
theorem ipcInvariantFull_of_readViewAgreement_of_reciprocal {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (hCapBadges : capabilityBadgesWellFormed s2)
    (hNBR : notificationBindingReciprocal s2)
    (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ⟨ipcInvariant_of_readViewAgreement hView h.ipcInvariant,
   dualQueueSystemInvariant_of_readViewAgreement hView h.dualQueueSystemInvariant,
   allPendingMessagesBounded_of_readViewAgreement hView h.allPendingMessagesBounded,
   ⟨notificationBadgesWellFormed_of_readViewAgreement hView h.badgeWellFormed.1, hCapBadges⟩,
   blockedThreadsPendingMessageConsistent_of_readViewAgreement hView
     h.blockedThreadsPendingMessageConsistent,
   endpointQueueNoDup_of_readViewAgreement hView h.endpointQueueNoDup,
   ipcStateQueueMembershipConsistent_of_readViewAgreement hView
     h.ipcStateQueueMembershipConsistent,
   queueNextBlockingConsistent_of_readViewAgreement hView h.queueNextBlockingConsistent,
   queueHeadBlockedConsistent_of_readViewAgreement hView h.queueHeadBlockedConsistent,
   blockedThreadTimeoutConsistent_of_readViewAgreement hView h.blockedThreadTimeoutConsistent,
   donationChainAcyclic_of_readViewAgreement hView h.donationChainAcyclic,
   donationOwnerValid_of_readViewAgreement hView h.donationOwnerValid,
   donationBudgetTransfer_of_readViewAgreement hView h.donationBudgetTransfer,
   replyCallerLinkage_of_readViewAgreement hView h.replyCallerLinkage,
   pendingReceiveReplyWellFormed_of_readViewAgreement hView h.pendingReceiveReplyWellFormed,
   donationOwnerUnique_of_readViewAgreement hView h.donationOwnerUnique,
   endpointQueueTailBlockedConsistent_of_readViewAgreement hView
     h.endpointQueueTailBlockedConsistent,
   queueNextTargetBlocked_of_readViewAgreement hView h.queueNextTargetBlocked,
   hNBR,
   endpointQueueLinksOnlyBlocked_of_readViewAgreement hView h.endpointQueueLinksOnlyBlocked⟩

/-- The master transport for a write that moves no binding code: the
reciprocity carries with the codes. -/
theorem ipcInvariantFull_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (hCodes : sameNotificationBindings s1 s2)
    (hCapBadges : capabilityBadgesWellFormed s2)
    (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ipcInvariantFull_of_readViewAgreement_of_reciprocal hView hCapBadges
    (.of_codes hCodes h.notificationBindingReciprocal) h


/-- Read-view agreement keeps every donation owner: a context's `boundThread` and a thread's binding
and IPC state are inside the view. -/
theorem donationOwnerFrame.of_readViewAgreement {s1 s2 : SystemState}
    (h : ipcReadViewAgreement s1 s2) : donationOwnerFrame s1 s2 := by
  refine ⟨fun scId sc hSc => h.schedContext _ sc hSc, fun owner ownerTcb hT hU hR => ?_⟩
  obtain ⟨t', ht, e⟩ := h.tcbFwd owner.toObjId ownerTcb hT
  have eB : t'.ipcReadView.schedContextBinding = ownerTcb.ipcReadView.schedContextBinding :=
    congrArg TCB.schedContextBinding e
  have eI : t'.ipcReadView.ipcState = ownerTcb.ipcReadView.ipcState := congrArg TCB.ipcState e
  obtain ⟨ep, rt, hb⟩ := hR
  exact ⟨t', ht, by rw [show t'.schedContextBinding = _ from eB]; exact hU, ep, rt, eI.trans hb⟩

/-- The IPC read view frames the timeout budget: it is inside the view. -/
theorem timeoutBudgetFrame.of_readViewAgreement {s1 s2 : SystemState}
    (h : ipcReadViewAgreement s1 s2) : timeoutBudgetFrame s1 s2 := fun tid tcb' hT => by
  obtain ⟨t, ht, e⟩ := h.tcb tid.toObjId tcb' hT
  exact ⟨t, ht, (congrArg TCB.timeoutBudget e).symm⟩

/-- The IPC read view frames the reply links: a reply's caller and a thread's `replyObject` and IPC
state are inside the view. -/
theorem replyLinkageFrame.of_readViewAgreement {s1 s2 : SystemState}
    (h : ipcReadViewAgreement s1 s2) : replyLinkageFrame s1 s2 := by
  refine ⟨fun rid _ => ?_, fun tid tcb' hT => ?_, fun tid tcb _ hT _ => ?_⟩
  · exact ⟨fun ⟨r, hr, hc⟩ => ⟨r, (h.reply _ r).mp hr, hc⟩,
      fun ⟨r, hr, hc⟩ => ⟨r, (h.reply _ r).mpr hr, hc⟩⟩
  · obtain ⟨t, ht, e⟩ := h.tcb tid.toObjId tcb' hT
    have eR : tcb'.ipcReadView.replyObject = t.ipcReadView.replyObject := congrArg TCB.replyObject e
    exact ⟨t, ht, eR⟩
  · obtain ⟨t', ht, e⟩ := h.tcbFwd tid.toObjId tcb hT
    have eI : t'.ipcReadView.ipcState = tcb.ipcReadView.ipcState := congrArg TCB.ipcState e
    have eR : t'.ipcReadView.replyObject = tcb.ipcReadView.replyObject :=
      congrArg TCB.replyObject e
    exact ⟨t', ht, eR, fun ep rt hb => ⟨ep, rt, eI.trans hb⟩⟩

/-- Read-view transport of the scheduler bundle, across a step that leaves the
scheduler alone: the bundle reads the scheduler and whether the current thread's
TCB exists, and a read-view write keeps every TCB a TCB. -/
theorem schedulerInvariantBundle_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) (hS : s2.scheduler = s1.scheduler)
    (h : schedulerInvariantBundle s1) : schedulerInvariantBundle s2 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hS ▸ h1, hS ▸ h2, ?_⟩
  unfold currentThreadValid at h3 ⊢
  rw [hS]
  cases hC : s1.scheduler.currentOnCore bootCoreId with
  | none => trivial
  | some x =>
    rw [hC] at h3
    obtain ⟨t₀, ht₀⟩ := h3
    obtain ⟨t, ht, -⟩ := hView.tcbFwd x.toObjId t₀ ht₀
    exact ⟨t, ht⟩

/-- Read-view transport of the IPC/scheduler contract, across a step that
leaves the scheduler alone: each clause reads a thread's `ipcState`, which is
inside the read view, and the run queue (a thread made `Inactive` by a call
that links no reply stays inside the frame). -/
theorem ipcSchedulerContractPredicates_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) (hS : s2.scheduler = s1.scheduler)
    (h : ipcSchedulerContractPredicates s1) : ipcSchedulerContractPredicates s2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tid tcb hT; run_links_back hView at tcb hT; rw [hS]; exact h1 tid tcb hT
  · intro tid tcb e hT; run_links_back hView at tcb hT; rw [hS]; exact h2 tid tcb e hT
  · intro tid tcb e hT; run_links_back hView at tcb hT; rw [hS]; exact h3 tid tcb e hT
  · intro tid tcb e hT; run_links_back hView at tcb hT; rw [hS]; exact h4 tid tcb e hT
  · intro tid tcb e r hT; run_links_back hView at tcb hT; rw [hS]; exact h5 tid tcb e r hT
  · intro tid tcb e hT; run_links_back hView at tcb hT; rw [hS]; exact h6 tid tcb e hT

end SeLe4n.Kernel
