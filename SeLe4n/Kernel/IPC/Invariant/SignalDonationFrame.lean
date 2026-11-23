-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.IPC.Invariant.SignalWakeLinkFrame

/-!
# The state a notification donation runs on

seL4-MCS's `completeSignal` takes the notification's word, writes it to the
badge register and then runs `maybeDonateSchedContext`
(`completeSignalArm`).  The donation's family lemmas — step coverage, the IPC
bundle — ask two facts of the state the donation runs on: the binding pair
(`schedContextBindingBidirectional`, so no thread holds the context the guard
finds bound to none) and that the receiver lends no context
(no thread holds a context `.donated` from it).

Neither the consumption nor the badge register writes a scheduling link: the
consumption stores the notification over itself and readies the receiver, and
the register write is one TCB's register file (`SchedLinkFrame`).  So both facts
are the dispatch's pre-state facts, carried across.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The binding pair carries over a step that keeps every binding link**. -/
theorem schedContextBindingBidirectional.of_bindingLinksAgree {st st' : SystemState}
    (hB : bindingLinksAgree st st') (h : schedContextBindingBidirectional st) :
    schedContextBindingBidirectional st' := by
  intro t tcb s hT hs
  obtain ⟨u, hu, e⟩ := hB.tcb_back hT
  obtain ⟨sc, h0, hbt⟩ := h t u s hu (by rw [e]; exact hs)
  obtain ⟨sc', hs', e'⟩ := hB.symm.sc_back h0
  exact ⟨sc', hs', e'.trans hbt⟩

/-- **The badge register's write keeps every scheduling link.** -/
theorem SchedLinkFrame.writeReturnFrameToTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    SchedLinkFrame st (Architecture.writeReturnFrameToTcb st tid frame) :=
  SchedLinkFrame.updateTcb st tid _ hInv

/-- **A TCB's IPC state written keeps every scheduling link.** -/
theorem SchedLinkFrame.storeTcbIpcState {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {ipc : ThreadIpcState} (hInv : st.objects.invExt)
    (h : storeTcbIpcState st tid ipc = .ok st') : SchedLinkFrame st st' := by
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  have hPre := lookupTcb_some_objects st tid tcb hL
  exact SchedLinkFrame.storeObject hInv hS (by rw [hPre]; rfl) (by rw [hPre]; rfl)
    (by rw [hPre]; rfl)

/-- **A wait that consumed its notification's word keeps every scheduling
link**: the notification stored over itself, the waiter readied. -/
theorem notificationWaitOnCore_consumed_schedLinkFrame {notifId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {c : Concurrency.CoreId} {st st1 : SystemState}
    {badge : SeLe4n.Badge} (hInv : st.objects.invExt)
    (h : notificationWaitOnCore notifId tid c st = (st1, .ok (some badge))) :
    SchedLinkFrame st st1 := by
  unfold notificationWaitOnCore at h
  cases hN : st.getNotification? notifId with
  | none =>
    rw [hN] at h
    by_cases hO : (st.getObject? notifId).isSome = true
    · simp only [hO, ↓reduceIte] at h; cases h
    · simp only [hO, Bool.false_eq_true, ↓reduceIte] at h; cases h
  | some ntfn =>
    rw [hN] at h
    have hPre := (SystemState.getNotification?_eq_some_iff _ _ _).mp hN
    cases hB : ntfn.pendingBadge with
    | some b =>
      simp only [hB] at h
      generalize hS : storeObject notifId _ st = rS at h
      cases rS with
      | error e => cases h
      | ok v =>
        obtain ⟨⟨⟩, stA⟩ := v
        dsimp only at h
        have F1 := SchedLinkFrame.storeObject hInv hS (by rw [hPre]; rfl) (by rw [hPre]; rfl)
          (by rw [hPre]; rfl)
        have hInvA := storeObject_preserves_objects_invExt st stA notifId _ hInv hS
        cases hT : storeTcbIpcState stA tid .ready with
        | error e => rw [hT] at h; cases h
        | ok stB =>
          rw [hT] at h
          cases h
          exact F1.trans (SchedLinkFrame.storeTcbIpcState hInvA hT)
    | none =>
      simp only [hB] at h
      repeat' split at h
      all_goals simp_all

/-- ...and so does the checked wait. -/
theorem notificationWaitCrossCoreDispatchChecked_consumed_schedLinkFrame
    {ctx : LabelingContext} {notifId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {c : Concurrency.CoreId} {st st1 : SystemState} {badge : SeLe4n.Badge}
    (hInv : st.objects.invExt)
    (h : notificationWaitCrossCoreDispatchChecked ctx notifId tid c st =
      (st1, .ok (some badge))) :
    SchedLinkFrame st st1 :=
  notificationWaitOnCore_consumed_schedLinkFrame hInv
    (notificationWaitCrossCoreDispatchChecked_ok_inner h)

/-- **The state `completeSignalArm` donates on keeps every scheduling link of
the state it was handed**: the consumption, then the badge register. -/
theorem completeSignalArm_donationPre_schedLinkFrame {notifId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {c : Concurrency.CoreId} {st st1 : SystemState}
    {badge : SeLe4n.Badge} (hInv : st.objects.invExt)
    (h : notificationWaitOnCore notifId tid c st = (st1, .ok (some badge))) :
    SchedLinkFrame st (Architecture.writeReturnFrameToTcb st1 tid
      (Architecture.badgeReturnFrame st1 tid badge)) :=
  (notificationWaitOnCore_consumed_schedLinkFrame hInv h).trans
    (SchedLinkFrame.writeReturnFrameToTcb _ _ _
      (by
        have := notificationWaitCrossCoreDispatch_preserves_objects_invExt notifId tid c st hInv
        unfold notificationWaitCrossCoreDispatch at this
        rw [h] at this
        exact this))

/-- **The donation keeps the IPC bundle** on a state where the binding pair
holds and the receiver lends no context: the identity, or the bind's writes
under seL4's guard (`schedContextBindPerform_preserves_ipcInvariantFull`). -/
theorem maybeDonateSchedContext_preserves_ipcInvariantFull (st : SystemState)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st) (hBidir : schedContextBindingBidirectional st) :
    ipcInvariantFull (maybeDonateSchedContext st n tid) :=
  maybeDonateSchedContext_induct (fun _ s' => ipcInvariantFull s') st n tid hInv
    (fun vS vT _ hA => schedContextBindPerform_preserves_ipcInvariantFull st vS vT hObjInv hInv
      hBidir hA)

/-- **seL4's return on a running receiver keeps the IPC bundle**: the binding
pair cleared in the unbind direction (`schedContextUnbindTail_preserves_ipcInvariantFull`,
the context written with its thread link alone cleared), then reschedule flags. -/
theorem schedContextReturnLinks_preserves_ipcInvariantFull (st : SystemState)
    (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId) (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st) (hA : schedContextReturnAdmitted st vS vT = true) :
    ipcInvariantFull (schedContextReturnLinks st vS vT.val) := by
  unfold schedContextReturnLinks
  split
  · exact hInv
  rename_i sc hSc _
  split
  · exact hInv
  rename_i tcb hT
  have hScRaw := (SystemState.getSchedContext?_eq_some_iff st _ sc).mp hSc
  have hTRaw := (SystemState.getTcb?_eq_some_iff st _ tcb).mp hT
  have hBound : sc.boundThread = some vT.val := by
    unfold schedContextReturnAdmitted at hA
    rw [hSc, hT] at hA
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hA
    exact hA.1
  dsimp only
  refine markKeyChangeFor_preserves_ipcInvariantFull _ _ _
    (markCandidacyGainFor_preserves_ipcInvariantFull _ _ _ ?_)
  have hTail := schedContextUnbindTail_preserves_ipcInvariantFull st vS.val vT.val sc
    { sc with boundThreadCode := 0 } tcb
    (SystemState.rewriteAdmissible_schedContext hSc _) rfl hObjInv hInv hScRaw hTRaw hBound
  split
  · exact markReschedulePendingOnCore_preserves_ipcInvariantFull _ _ hTail
  · exact hTail

/-- **The return keeps the IPC bundle**: seL4's three writes, then the purge,
which moves release links alone. -/
theorem schedContextReturnPerform_preserves_ipcInvariantFull (st : SystemState)
    (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId) (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st) (hA : schedContextReturnAdmitted st vS vT = true) :
    ipcInvariantFull (schedContextReturnPerform st vS vT.val) :=
  purgeReplenishment_preserves_ipcInvariantFull _ _
    (schedContextReturnLinks_preserves_ipcInvariantFull st vS vT hObjInv hInv hA)

/-- **seL4-MCS `maybeReturnSchedContext` keeps the IPC invariant**: the
identity, or seL4's writes and the purge
(`schedContextReturnPerform_preserves_ipcInvariantFull`). -/
theorem maybeReturnSchedContext_preserves_ipcInvariantFull (st : SystemState)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st) : ipcInvariantFull (maybeReturnSchedContext st n tid) :=
  maybeReturnSchedContext_induct (fun _ s' => ipcInvariantFull s') st n tid hInv
    (fun vS vT hT hA => by
      subst hT
      exact schedContextReturnPerform_preserves_ipcInvariantFull st vS vT hObjInv hInv hA)

/-- **The receive's return keeps every endpoint queue head's blocking**: it
writes no endpoint, and the TCBs it writes keep their IPC state. -/
theorem receiveReturnSchedContext_queueHeadBlockedConsistent (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hI : st.objects.invExt) (hQ : queueHeadBlockedConsistent st) :
    queueHeadBlockedConsistent (receiveReturnSchedContext blocks st tid) := by
  intro epId ep hd tcb hEp hT
  have hEp0 : st.objects[epId]? = some (.endpoint ep) := by
    rcases receiveReturnSchedContext_objects blocks st tid hI epId with e | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ <;>
      rw [e] at hEp
    · exact hEp
    · cases hEp
    · cases hEp
  obtain ⟨y, hy, hxy⟩ := receiveReturnSchedContext_tcb blocks st tid hI _ tcb hT
  have h := hQ epId ep hd y hEp0 hy
  rcases hxy with h' | h' <;> subst h' <;> exact h

/-- **seL4 `receiveIPC`'s return keeps the IPC bundle and the store's integrity.** -/
theorem receiveReturnSchedContext_preserves_ipcInvariantFull (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (receiveReturnSchedContext blocks st tid) ∧
      (receiveReturnSchedContext blocks st tid).objects.invExt :=
  receiveReturnSchedContext_induct
    (fun _ s' => ipcInvariantFull s' ∧ s'.objects.invExt) blocks st tid ⟨hInv, hObjInv⟩
    (fun vS vT hT hA => by
      subst hT
      exact ⟨schedContextReturnPerform_preserves_ipcInvariantFull st vS vT hObjInv hInv hA,
        schedContextReturnPerform_preserves_objects_invExt st vS vT.val hObjInv⟩)

/-- The state the consumption and the badge register leave keeps the object
store's integrity. -/
theorem completeSignalArm_donationPre_objects_invExt {notifId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {c : Concurrency.CoreId} {st st1 : SystemState}
    {badge : SeLe4n.Badge} (hInv : st.objects.invExt)
    (h : notificationWaitOnCore notifId tid c st = (st1, .ok (some badge))) :
    (Architecture.writeReturnFrameToTcb st1 tid
      (Architecture.badgeReturnFrame st1 tid badge)).objects.invExt := by
  have := notificationWaitCrossCoreDispatch_preserves_objects_invExt notifId tid c st hInv
  unfold notificationWaitCrossCoreDispatch at this
  rw [h] at this
  exact writeReturnFrameToTcb_preserves_objects_invExt _ _ _ this

/-- **The completion's donation keeps the IPC bundle**, on the dispatch's
pre-state facts: the bundle holds on the state the consumption and the badge
register leave, and the binding pair holds on the state handed to the
completion. -/
theorem completeSignalArm_donation_preserves_ipcInvariantFull {ctx : LabelingContext}
    {notifId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {c : Concurrency.CoreId} {st st1 : SystemState}
    {badge : SeLe4n.Badge} (n : SeLe4n.ObjId) (hObjInv : st.objects.invExt)
    (h : notificationWaitOnCore notifId tid c st = (st1, .ok (some badge)))
    (hInv2 : ipcInvariantFull (Architecture.writeReturnFrameToTcb st1 tid
      (Architecture.badgeReturnFrame st1 tid badge)))
    (hBi : schedContextBindingBidirectional st) :
    ipcInvariantFull (maybeDonateSchedContextFlowing ctx (Architecture.writeReturnFrameToTcb st1 tid
      (Architecture.badgeReturnFrame st1 tid badge)) n tid) := by
  have F := completeSignalArm_donationPre_schedLinkFrame hObjInv h
  refine maybeDonateSchedContextFlowing_induct (fun s => ipcInvariantFull s) ctx _ n tid hInv2 ?_
  exact maybeDonateSchedContext_preserves_ipcInvariantFull _ n tid
    (completeSignalArm_donationPre_objects_invExt hObjInv h) hInv2
    (schedContextBindingBidirectional.of_bindingLinksAgree F.binding hBi)

/-! ### The context each thread runs on and each context's thread

The binding pair reads, of a thread, only the context its binding names
(`SchedContextBinding.scId?`), whether its own or on loan, and of a context only
the thread it names.  A receive's busy-reply cancel moves a loan to its holder
(the head cut makes the holder's binding its own), which changes the binding but
not the context it names; so the pair is carried by agreement on those two
projections. -/

/-- **Every thread runs on the context it ran on, and every context names the
thread it named.** -/
def scIdLinksAgree (st st' : SystemState) : Prop :=
  (∀ t : SeLe4n.ThreadId, (st'.getTcb? t).map (·.schedContextBinding.scId?) =
    (st.getTcb? t).map (·.schedContextBinding.scId?)) ∧
  (∀ s : SeLe4n.SchedContextId, (st'.getSchedContext? s).map (·.boundThread) =
    (st.getSchedContext? s).map (·.boundThread))

namespace scIdLinksAgree

theorem refl (st : SystemState) : scIdLinksAgree st st := ⟨fun _ => rfl, fun _ => rfl⟩

theorem trans {a b c : SystemState} (h₁ : scIdLinksAgree a b) (h₂ : scIdLinksAgree b c) :
    scIdLinksAgree a c :=
  ⟨fun t => (h₂.1 t).trans (h₁.1 t), fun s => (h₂.2 s).trans (h₁.2 s)⟩

/-- The context a binding names is read off its context word alone. -/
theorem scId?_of_scCode {t t' : TCB} (h : t'.scBindingScCode = t.scBindingScCode) :
    t'.schedContextBinding.scId? = t.schedContextBinding.scId? := by
  unfold TCB.schedContextBinding SchedContextBinding.ofCodes
  rw [h]
  cases t.scBindingScCode with
  | zero => rfl
  | succ k => cases t'.scBindingOwnerCode <;> cases t.scBindingOwnerCode <;> rfl

/-- A step keeping every binding link keeps both projections. -/
theorem of_bindingLinksAgree {st st' : SystemState} (h : bindingLinksAgree st st') :
    scIdLinksAgree st st' := by
  refine ⟨fun t => ?_, fun s => ?_⟩
  · cases h1 : st'.getTcb? t with
    | none =>
      cases h0 : st.getTcb? t with
      | none => rfl
      | some u =>
        obtain ⟨u', hu', -⟩ := h.getTcb?_fwd h0
        rw [h1] at hu'; cases hu'
    | some t' =>
      obtain ⟨u, hu, e, -⟩ := h.getTcb?_back h1
      rw [hu]
      exact congrArg some (scId?_of_scCode e)
  · cases h1 : st'.getSchedContext? s with
    | none =>
      cases h0 : st.getSchedContext? s with
      | none => rfl
      | some u =>
        obtain ⟨u', hu', -⟩ := h.getSchedContext?_fwd h0
        rw [h1] at hu'; cases hu'
    | some sc' =>
      obtain ⟨u, hu, e⟩ := h.getSchedContext?_back h1
      rw [hu]
      exact congrArg some e.symm

theorem of_schedLinkFrame {st st' : SystemState} (h : SchedLinkFrame st st') :
    scIdLinksAgree st st' := of_bindingLinksAgree h.binding

/-- A thread rewritten keeping its context word. -/
theorem updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).scBindingScCode = x.scBindingScCode) :
    scIdLinksAgree st (st.updateTcb tid f) := by
  refine ⟨fun y => ?_, fun s => by rw [SystemState.updateTcb_getSchedContext? _ _ _ hInv]⟩
  by_cases hy : tid.toObjId = y.toObjId
  · have hy' : tid = y := SeLe4n.ThreadId.toObjId_injective _ _ hy
    subst hy'
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv, Option.map_map]
    cases st.getTcb? tid with
    | none => rfl
    | some t => exact congrArg some (scId?_of_scCode (hf t))
  · rw [SystemState.updateTcb_getTcb?_ne _ _ _ hInv _ hy]

end scIdLinksAgree

/-- **The binding pair carries over a step keeping both projections.** -/
theorem schedContextBindingBidirectional.of_scIdLinksAgree {st st' : SystemState}
    (hA : scIdLinksAgree st st') (h : schedContextBindingBidirectional st) :
    schedContextBindingBidirectional st' := by
  intro t tcb s hT hs
  have hb := hA.1 t
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hT] at hb
  cases hp : st.getTcb? t with
  | none => rw [hp] at hb; cases hb
  | some tcb0 =>
    rw [hp] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    obtain ⟨sc0, h0, hbt⟩ := h t tcb0 s ((SystemState.getTcb?_eq_some_iff _ _ _).mp hp)
      (by rw [← hb]; exact hs)
    have hs' := hA.2 s
    rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mpr h0] at hs'
    cases hq : st'.getSchedContext? s with
    | none => rw [hq] at hs'; cases hs'
    | some sc =>
      rw [hq] at hs'
      simp only [Option.map_some, Option.some.injEq] at hs'
      exact ⟨sc, (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hq, hs'.trans hbt⟩

/-- **The head cut keeps both projections**: a reply stored over itself, the
context's head and origin cleared, and a holder's loan made its own — the
context its binding names unchanged. -/
theorem cutCancelledCallerHead_scIdLinksAgree (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) :
    scIdLinksAgree st (Lifecycle.Suspend.cutCancelledCallerHead st tcb) ∧
      (Lifecycle.Suspend.cutCancelledCallerHead st tcb).objects.invExt := by
  refine (Lifecycle.Suspend.cutCancelledCallerHead_closed
    (fun s => scIdLinksAgree st s ∧ s.objects.invExt)
    (fun s s1 rid r scId ⟨hA, hI⟩ _ hR hS => ?_)
    (fun s scId holder ht o ⟨hA, hI⟩ _ _ _ => ?_) st tcb ⟨.refl st, hInv⟩).imp id id
  · have F1 := SchedLinkFrame.storeReplyOver hI ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hS
    have hI1 := storeObject_preserves_objects_invExt s s1 _ _ hI hS
    have F2 := SchedLinkFrame.updateSchedContext s1 scId
      (fun sc => { sc with scReply := none, donationOrigin := none }) hI1 (fun _ => rfl)
    exact ⟨hA.trans (scIdLinksAgree.of_schedLinkFrame (F1.trans F2)),
      SystemState.updateSchedContext_preserves_objects_invExt _ scId _ hI1⟩
  · refine ⟨hA.trans ((scIdLinksAgree.updateTcb s holder
      (fun t => { t with scBindingOwnerCode := 0 }) hI (fun _ => rfl)).trans
      (scIdLinksAgree.of_schedLinkFrame (SchedLinkFrame.markKeyChangeFrom _ _ holder))), ?_⟩
    rw [markKeyChangeFrom_objects]
    exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hI

/-- **The suspend's IPC cancel keeps both projections**: on a reply-blocked
thread the head cut then a tail that writes no scheduling link (seL4's
`reply_remove_tcb`: no loan is left to return); on any other, a queue's exit and
the restore. -/
theorem cancelIpcKeepingContexts_scIdLinksAgree (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) :
    scIdLinksAgree st (Lifecycle.Suspend.cancelIpcKeepingContexts st tid tcb) := by
  cases hI : tcb.ipcState with
  | blockedOnReply ep rt =>
    rw [Lifecycle.Suspend.cancelIpcKeepingContexts_reply_arm st tid tcb ep rt hI hInv]
    have hC : Lifecycle.Suspend.cutCancelledCallerHead st tcb =
        Lifecycle.Suspend.cutThreadHeadFrameKeepingContext st tcb := by
      unfold Lifecycle.Suspend.cutCancelledCallerHead; rw [hI]
    obtain ⟨hA, hI1⟩ := cutCancelledCallerHead_scIdLinksAgree st tcb hInv
    rw [hC] at hA hI1
    exact hA.trans (scIdLinksAgree.of_schedLinkFrame (SchedLinkFrame.replyCancelTail _ tid tcb hI1))
  | blockedOnNotification n =>
    rw [Lifecycle.Suspend.cancelIpcKeepingContexts_of_not_reply st tid tcb
      (by intro ep rt h; rw [hI] at h; cases h)]
    exact scIdLinksAgree.of_schedLinkFrame (SchedLinkFrame.notificationCancel st tid tcb n hInv hI)
  | ready =>
    rw [Lifecycle.Suspend.cancelIpcKeepingContexts_of_not_reply st tid tcb
      (by intro ep rt h; rw [hI] at h; cases h)]
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hI]
    exact .refl st
  | blockedOnSend ep | blockedOnReceive ep | blockedOnCall ep =>
    rw [Lifecycle.Suspend.cancelIpcKeepingContexts_of_not_reply st tid tcb
      (by intro ep rt h; rw [hI] at h; cases h)]
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hI]
    dsimp only
    have hR : scIdLinksAgree st (removeFromBlockingEndpoint st tid ep) :=
      ⟨fun y => by
        have e := removeFromBlockingEndpoint_binding_frame st tid ep hInv y
        have := congrArg (Option.map SchedContextBinding.scId?) e
        simpa only [Option.map_map] using this,
       fun s => by rw [removeFromBlockingEndpoint_getSchedContext?_eq st tid ep hInv]⟩
    have hRI := removeFromBlockingEndpoint_preserves_objects_invExt st tid ep hInv
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact hR.trans (scIdLinksAgree.of_schedLinkFrame (SchedLinkFrame.updateTcb _ _ _ hRI))

/-- **A receive's busy-reply cancel keeps both projections**: the holder's IPC
cancel, the boost it lent reverted, and its `Inactive` write. -/
theorem cancelReplyHolder_scIdLinksAgree (st : SystemState) (holder : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (hInv : st.objects.invExt) :
    scIdLinksAgree st (cancelReplyHolder st holder ec) := by
  rcases cancelReplyHolder_cases st holder ec with h | ⟨tcb, -, -, h⟩
  · rw [h]; exact .refl st
  rw [h]
  have hK := cancelIpcKeepingContexts_scIdLinksAgree st holder tcb hInv
  have hKI := Lifecycle.Suspend.cancelIpcKeepingContexts_preserves_objects_invExt st holder tcb hInv
  have hR : scIdLinksAgree st (Lifecycle.Suspend.suspendCancelRevert st holder tcb ec) ∧
      (Lifecycle.Suspend.suspendCancelRevert st holder tcb ec).objects.invExt := by
    unfold Lifecycle.Suspend.suspendCancelRevert; dsimp only; split
    · exact ⟨hK.trans (scIdLinksAgree.of_schedLinkFrame (SchedLinkFrame.propagatePip _ _ ec _ hKI)),
        PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt _ _ _ _ hKI⟩
    · exact ⟨hK, hKI⟩
  exact hR.1.trans (scIdLinksAgree.of_schedLinkFrame (SchedLinkFrame.updateTcb _ _ _ hR.2))

/-- ...and so does the receive's cancel, whichever holder it names. -/
theorem cancelRecvBusyReply_scIdLinksAgree (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) (ec : Concurrency.CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    scIdLinksAgree st (cancelRecvBusyReply ctx tid gate decoded ec st) := by
  unfold cancelRecvBusyReply
  split
  · exact .refl st
  · exact cancelReplyHolder_scIdLinksAgree st _ ec hInv

/-- **The binding pair holds on the state a receive's cancel leaves.** -/
theorem cancelRecvBusyReply_bidirectional {ctx : LabelingContext} {tid : SeLe4n.ThreadId}
    {gate : SyscallGate} {decoded : SyscallDecodeResult} {ec : Concurrency.CoreId}
    {st : SystemState} (hInv : st.objects.invExt) (h : schedContextBindingBidirectional st) :
    schedContextBindingBidirectional (cancelRecvBusyReply ctx tid gate decoded ec st) :=
  schedContextBindingBidirectional.of_scIdLinksAgree
    (cancelRecvBusyReply_scIdLinksAgree ctx tid gate decoded ec st hInv) h

/-! ### The guard the donation reads, read on the completion's pre-state

seL4's guard reads the notification's context, the context's thread and the
receiver's context; the receiver's home core reads its affinity.  The
consumption and the badge register write none of them, so a footprint built
from the state the completion is handed names exactly the cores the donation
writes. -/

/-- **What the guard reads of an object**: a notification's context word. -/
def ntfnContextOf : Option KernelObject → Option Nat
  | some (.notification n) => some n.schedContextCode
  | _ => none

/-- Two states hold the same context word in every notification. -/
def ntfnContextsAgree (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, ntfnContextOf st'.objects[oid]? = ntfnContextOf st.objects[oid]?

namespace ntfnContextsAgree

theorem refl (st : SystemState) : ntfnContextsAgree st st := fun _ => rfl

theorem trans {a b c : SystemState} (h₁ : ntfnContextsAgree a b) (h₂ : ntfnContextsAgree b c) :
    ntfnContextsAgree a c := fun o => (h₂ o).trans (h₁ o)

theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hS : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (hk : ntfnContextOf (some o) = ntfnContextOf st.objects[k]?) : ntfnContextsAgree st st' := by
  intro oid
  by_cases h : oid = k
  · subst h; rw [storeObject_objects_eq st st' oid o hInv hS]; exact hk
  · rw [storeObject_objects_ne st st' k oid o h hInv hS]

theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) : ntfnContextsAgree st (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact refl st
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hG]
    have hPre := (SystemState.getTcb?_eq_some_iff st t x).mp hG
    exact proj_insert_eq ntfnContextOf hInv (by rw [hPre]; rfl)

/-- A notification's context is its context word, decoded. -/
theorem getNotification?_map_schedContext (st : SystemState) (n : SeLe4n.ObjId) :
    (st.getNotification? n).map (·.schedContext) =
      (ntfnContextOf st.objects[n]?).map SeLe4n.SchedContextId.ofOptCode := by
  unfold SystemState.getNotification?
  cases st.objects[n]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- The notification's context, read through the word. -/
theorem getNotification?_schedContext {st st' : SystemState} (h : ntfnContextsAgree st st')
    (n : SeLe4n.ObjId) :
    (st'.getNotification? n).map (·.schedContext) = (st.getNotification? n).map (·.schedContext) := by
  rw [getNotification?_map_schedContext, getNotification?_map_schedContext, h n]

end ntfnContextsAgree

/-- **A consumed wait and its badge register keep every notification's context
word.** -/
theorem completeSignalArm_donationPre_ntfnContexts {notifId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {c : Concurrency.CoreId} {st st1 : SystemState}
    {badge : SeLe4n.Badge} (hInv : st.objects.invExt)
    (h : notificationWaitOnCore notifId tid c st = (st1, .ok (some badge))) :
    ntfnContextsAgree st (Architecture.writeReturnFrameToTcb st1 tid
      (Architecture.badgeReturnFrame st1 tid badge)) := by
  have hInv1 : st1.objects.invExt := by
    have := notificationWaitCrossCoreDispatch_preserves_objects_invExt notifId tid c st hInv
    unfold notificationWaitCrossCoreDispatch at this
    rw [h] at this; exact this
  refine ntfnContextsAgree.trans ?_ (ntfnContextsAgree.updateTcb _ _ _ hInv1)
  unfold notificationWaitOnCore at h
  cases hN : st.getNotification? notifId with
  | none =>
    rw [hN] at h
    by_cases hO : (st.getObject? notifId).isSome = true
    · simp only [hO, ↓reduceIte] at h; cases h
    · simp only [hO, Bool.false_eq_true, ↓reduceIte] at h; cases h
  | some ntfn =>
    rw [hN] at h
    have hPre := (SystemState.getNotification?_eq_some_iff _ _ _).mp hN
    cases hB : ntfn.pendingBadge with
    | some b =>
      simp only [hB] at h
      generalize hS : storeObject notifId _ st = rS at h
      cases rS with
      | error e => cases h
      | ok v =>
        obtain ⟨⟨⟩, stA⟩ := v
        dsimp only at h
        have F1 := ntfnContextsAgree.storeObject hInv hS (by rw [hPre]; rfl)
        have hInvA := storeObject_preserves_objects_invExt st stA notifId _ hInv hS
        cases hT : storeTcbIpcState stA tid .ready with
        | error e => rw [hT] at h; cases h
        | ok stB =>
          rw [hT] at h
          cases h
          obtain ⟨tcb, hL, hS2⟩ := modifyTcb_ok_decompose hT
          exact F1.trans (ntfnContextsAgree.storeObject hInvA hS2
            (by rw [lookupTcb_some_objects stA tid tcb hL]; rfl))
    | none =>
      simp only [hB] at h
      repeat' split at h
      all_goals simp_all

/-- **The donation's cores, read on the completion's pre-state**: the guard and
the receiver's home core are the same on the state the consumption and the
badge register leave. -/
theorem completeSignalArm_signalDonationCores_eq {notifId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {c : Concurrency.CoreId} {st st1 : SystemState}
    {badge : SeLe4n.Badge} (n : SeLe4n.ObjId) (hInv : st.objects.invExt)
    (h : notificationWaitOnCore notifId tid c st = (st1, .ok (some badge))) :
    signalDonationCores (Architecture.writeReturnFrameToTcb st1 tid
      (Architecture.badgeReturnFrame st1 tid badge)) n tid = signalDonationCores st n tid := by
  have F := completeSignalArm_donationPre_schedLinkFrame hInv h
  have A := scIdLinksAgree.of_schedLinkFrame F
  have hG := signalDonationGuard_congr (n := n) (tid := tid)
    ((completeSignalArm_donationPre_ntfnContexts hInv h).getNotification?_schedContext n)
    A.2 (A.1 tid)
  unfold signalDonationCores
  rw [hG, (show schedAuxAgree st _ from F.aux).determineTargetCore_eq]

/-! ### seL4's `sendSignal`: the wake, then the donation

The wake writes no scheduling link (`notificationSignalBoundOnCore_schedLinkFrame`),
so the donation after it finds the binding pair the signal was handed. -/

/-- **seL4's `sendSignal` keeps the IPC bundle**: the wake's lemma, then the
donation's on the state the wake leaves. -/
theorem sendSignalOnCore_preserves_ipcInvariantFull (n : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : Concurrency.CoreId) (st : SystemState) (hObjInv : st.objects.invExt)
    (hWake : ipcInvariantFull (notificationSignalBoundOnCore n badge c st).1)
    (hBi : schedContextBindingBidirectional st) :
    ipcInvariantFull (sendSignalOnCore n badge c st).1 := by
  have F := notificationSignalBoundOnCore_schedLinkFrame n badge c st hObjInv
  refine sendSignalOnCore_induct (fun s => ipcInvariantFull s) n badge c st hWake
    (fun t _ _ _ => ?_)
  exact maybeDonateSchedContext_preserves_ipcInvariantFull _ n t
    (notificationSignalBoundOnCore_preserves_objects_invExt n badge c st hObjInv) hWake
    (schedContextBindingBidirectional.of_bindingLinksAgree F.binding hBi)

/-- **The checked `sendSignal` keeps the IPC bundle**: its donation is the
donation or nothing. -/
theorem sendSignalOnCoreFlowing_preserves_ipcInvariantFull (ctx : LabelingContext)
    (n : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : Concurrency.CoreId) (st : SystemState) (hObjInv : st.objects.invExt)
    (hWake : ipcInvariantFull (notificationSignalBoundOnCore n badge c st).1)
    (hBi : schedContextBindingBidirectional st) :
    ipcInvariantFull (sendSignalOnCoreFlowing ctx n badge c st).1 := by
  have F := notificationSignalBoundOnCore_schedLinkFrame n badge c st hObjInv
  refine sendSignalOnCoreFlowing_induct (fun s => ipcInvariantFull s) ctx n badge c st hWake
    (fun t _ _ _ => ?_)
  exact maybeDonateSchedContext_preserves_ipcInvariantFull _ n t
    (notificationSignalBoundOnCore_preserves_objects_invExt n badge c st hObjInv) hWake
    (schedContextBindingBidirectional.of_bindingLinksAgree F.binding hBi)

/-- **WS-RR RR7.22 (residual)**: the unchecked bound-signal dispatch preserves
the whole bundle.  The dispatch is seL4's `sendSignal` (`sendSignalOnCore`) at
the executing core: the wake's bundle lemma, then the donation's. -/
theorem notificationSignalBoundCrossCoreDispatch_preserves_ipcInvariantFull
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hPred : ∀ (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId),
      boundDeliveryTarget? st notificationId = some (t, epId) →
      splicePredecessorBlocked true epId st t)
    (hBi : schedContextBindingBidirectional st) :
    ipcInvariantFull
      (notificationSignalBoundCrossCoreDispatch notificationId badge executingCore st).1 :=
  sendSignalOnCore_preserves_ipcInvariantFull notificationId badge executingCore st hObjInv
    (notificationSignalBoundOnCore_preserves_ipcInvariantFull notificationId badge
      executingCore st hInv hObjInv hNWC hAllBudgetsNone hPred) hBi

/-- **WS-RR RR7.22 (residual)**: the *flow-checked* bound-signal dispatch, the
form the live arm runs, preserves the bundle: a refused gate returns the
pre-state, and a passed one runs the checked signal (`sendSignalOnCoreFlowing`). -/
theorem notificationSignalBoundCrossCoreDispatchChecked_preserves_ipcInvariantFull
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (executingCore : Concurrency.CoreId) (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hPred : ∀ (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId),
      boundDeliveryTarget? st notificationId = some (t, epId) →
      splicePredecessorBlocked true epId st t)
    (hBi : schedContextBindingBidirectional st) :
    ipcInvariantFull
      (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge
        executingCore st).1 :=
  notificationSignalBoundCrossCoreDispatchChecked_induct (fun s => ipcInvariantFull s) ctx
    notificationId signaler badge executingCore st hInv
    (sendSignalOnCoreFlowing_preserves_ipcInvariantFull ctx notificationId badge executingCore st
      hObjInv (notificationSignalBoundOnCore_preserves_ipcInvariantFull notificationId badge
        executingCore st hInv hObjInv hNWC hAllBudgetsNone hPred) hBi)

/-- **A successful declassifying signal's state agrees with the wake's on every
object**: the record writes the audit trail alone
(`notificationSignalDeclassifiedOnCore_frame`). -/
theorem notificationSignalDeclassifiedOnCore_objects_eq (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (n : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : Concurrency.CoreId) (st s0 : SystemState) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (h : notificationSignalDeclassifiedOnCore ctx declPolicy n badge c st = (s0, .ok sgi)) :
    s0.objects = (notificationSignalBoundOnCore n badge c st).1.objects := by
  rw [notificationSignalDeclassifiedOnCore_frame ctx declPolicy n badge c st s0 sgi h]

/-- A successful declassifying signal moves no binding link: the wake's
frame, the record writing the audit trail alone. -/
theorem notificationSignalDeclassifiedOnCore_bindingLinksAgree {ctx : GenericLabelingContext}
    {declPolicy : DeclassificationPolicy} {n : SeLe4n.ObjId} {badge : SeLe4n.Badge}
    {c : Concurrency.CoreId} {st : SystemState} {sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : (notificationSignalDeclassifiedOnCore ctx declPolicy n badge c st).2 = .ok sgi)
    (hObjInv : st.objects.invExt) :
    bindingLinksAgree st (notificationSignalDeclassifiedOnCore ctx declPolicy n badge c st).1 := by
  have hObj := notificationSignalDeclassifiedOnCore_objects_eq ctx declPolicy n badge c st _ sgi
    (Prod.ext rfl h)
  exact fun oid => by
    rw [hObj]; exact (notificationSignalBoundOnCore_schedLinkFrame n badge c st hObjInv).binding oid

/-- **The declassifying dispatch keeps the IPC bundle** on both delivery
paths: the declassifying signal's lemma (the bound receiver's splice
predecessor blocked, `splicePredecessorBlocked`), then the donation's on its
state, which agrees with the wake's on every object, so finds the binding pair
the signal was handed. -/
theorem notificationSignalDeclassifiedCrossCoreDispatch_preserves_ipcInvariantFull
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (n : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : Concurrency.CoreId)
    (st st' : SystemState) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (hInv : ipcInvariantFull st) (hObjInv : st.objects.invExt)
    (hNWC : notificationWaiterConsistent st) (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hPred : ∀ (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId),
      boundDeliveryTarget? st n = some (t, epId) →
      splicePredecessorBlocked true epId st t)
    (hBi : schedContextBindingBidirectional st)
    (hStep : notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy n badge c st =
      (st', .ok sgi)) :
    ipcInvariantFull st' := by
  unfold notificationSignalDeclassifiedCrossCoreDispatch at hStep
  cases hOn : notificationSignalDeclassifiedOnCore ctx declPolicy n badge c st with
  | mk s0 r =>
    rw [hOn] at hStep
    cases r with
    | error e => cases hStep
    | ok sgi0 =>
      simp only [Prod.mk.injEq, Except.ok.injEq] at hStep
      obtain ⟨rfl, -⟩ := hStep
      have hS0 := notificationSignalDeclassifiedOnCore_preserves_ipcInvariantFull ctx
        declPolicy n badge c st s0 sgi0 hInv hObjInv hNWC hAllBudgetsNone hPred hOn
      have hObj := notificationSignalDeclassifiedOnCore_objects_eq ctx declPolicy n badge c st s0
        sgi0 hOn
      have F := notificationSignalBoundOnCore_schedLinkFrame n badge c st hObjInv
      have hB : bindingLinksAgree st s0 := fun oid => by rw [hObj]; exact F.binding oid
      unfold donateToSignalledFlowingGeneric
      cases signalWokenThread? st n with
      | none => exact hS0
      | some t =>
        refine maybeDonateSchedContextFlowingGeneric_induct (fun s => ipcInvariantFull s) ctx _ n t
          hS0 ?_
        exact maybeDonateSchedContext_preserves_ipcInvariantFull _ n t
          (hObj ▸ notificationSignalBoundOnCore_preserves_objects_invExt n badge c st hObjInv) hS0
          (schedContextBindingBidirectional.of_bindingLinksAgree hB hBi)

end SeLe4n.Kernel
