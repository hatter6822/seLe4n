-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ReschedulePendingArms.Scheduling
import SeLe4n.Kernel.ReschedulePendingArms.Ipc
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsAffinity
import SeLe4n.Kernel.Scheduler.Invariant.PerCoreInvariantSuite

/-!
# The timer tick covers

WS-ZA ZA6.2.  The tick reports the cross-core decisions it stales through the
reschedule flags alone, so the tick's completeness is the coverage relation
itself: after `timerTickOnCore st c`, every core other than `c` whose decision
the tick staled has its flag up (`reschedulePendingCovers`), and no remote
flag went down.  The relation reads everything the chooser reads, the budget
eligibility included (`chooseBestRunnableEffective_eq_of_views`), so this is
the statement that a refill making a queued, ineligible thread eligible flags
the core whose queue holds it.

The drain's steps are each a refill and its wake under the refill's key hook
(`markRefillKeyChange`); the hook is discharged by `markKeyChangeFrom_covers`
once the refill is shown to move no other thread's view, which is where the
binding pair (`schedContextBindingBidirectional`) is consumed: the context the
refill writes is read by its bound thread alone.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-- A covering step keeps every remote queue's members and current slot, or
raised the core's flag. -/
theorem slots_of_reschedulePendingCovers {e : CoreId} {pre post : SystemState}
    (h : reschedulePendingCovers e pre post) :
    ∀ c, c ≠ e → post.scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, post.queuedOn c t = true → pre.queuedOn c t = true) ∧
        post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c) :=
  fun c hc => (h c hc).imp id fun hU => ⟨fun t ht => (hU.1 t ht).1, hU.2.1⟩

/-- A run-queue placement moves no thread's key or budget eligibility: the woken
TCB's rewrite marks it `.ready`, and its run-queue links are no key input. -/
theorem enqueueRunnableOnCore_views (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    schedKeyView (enqueueRunnableOnCore st c tid) t = schedKeyView st t ∧
      budgetEligibleView (enqueueRunnableOnCore st c tid) t = budgetEligibleView st t := by
  cases hTcb : st.getTcb? tid with
  | none => rw [enqueueRunnableOnCore_no_tcb_noop st c tid hTcb]; exact ⟨rfl, rfl⟩
  | some tcb =>
    cases hFresh : wakeDeclines st c tid with
    | true => rw [enqueueRunnableOnCore_eq_self_of_declines st c tid hFresh]; exact ⟨rfl, rfl⟩
    | false =>
      exact ⟨(schedKeyView_of_objectsAgreeOffRunLinks
          (enqueueRunnableOnCore_objectsAgree_marked st c tid tcb hTcb hFresh) t).trans
          (schedKeyView_rewriteObject_tcb hTcb (SystemState.rewriteAdmissible_tcb hTcb _) hInv
            (schedKeyFieldsEq_ipcState tcb _) t),
        (budgetEligibleView_of_objectsAgreeOffRunLinks
          (enqueueRunnableOnCore_objectsAgree_marked st c tid tcb hTcb hFresh) t).trans
          (budgetEligibleView_rewriteObject_tcb (t' := tcb.setIpcState .ready) hTcb
            (SystemState.rewriteAdmissible_tcb hTcb _) hInv rfl t)⟩

/-- A run-queue placement moves no binding. -/
theorem enqueueRunnableOnCore_bindingsAgree (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    bindingsAgree (enqueueRunnableOnCore st c tid) st := by
  cases hTcb : st.getTcb? tid with
  | none => rw [enqueueRunnableOnCore_no_tcb_noop st c tid hTcb]; exact bindingsAgree.refl _
  | some tcb =>
    cases hFresh : wakeDeclines st c tid with
    | true =>
      rw [enqueueRunnableOnCore_eq_self_of_declines st c tid hFresh]; exact bindingsAgree.refl _
    | false =>
      refine (bindingsAgree.of_objectsAgreeOffRunLinks
        (enqueueRunnableOnCore_objectsAgree_marked st c tid tcb hTcb hFresh)).trans ?_
      intro y
      show (((st.rewriteObject tid.toObjId (.tcb (tcb.setIpcState .ready))
        (SystemState.rewriteAdmissible_tcb hTcb _))).getTcb? y).map _ = _
      by_cases hy : tid = y
      · subst hy
        rw [SystemState.rewriteObject_tcb_getTcb?_self st tid _ _ hInv, hTcb]; rfl
      · rw [SystemState.rewriteObject_getTcb?_ne st _ _ _ hInv y
          (fun h => hy (SeLe4n.ThreadId.toObjId_injective _ _ h))]

/-- A conditional flag raise covers: it writes one flag up and nothing else. -/
theorem markReschedulePendingOnCoreIf_stepCovers (e : CoreId) (W : SystemState) (d : CoreId)
    (b : Bool) :
    stepCovers e W { W with scheduler := W.scheduler.markReschedulePendingOnCoreIf d b } := by
  refine stepCovers_of_frame (fun _ => rfl) (fun _ => rfl) (fun _ _ _ ht => ht)
    (fun c _ => SchedulerState.markReschedulePendingOnCoreIf_currentOnCore _ _ _ _)
    (fun c _ hF => ?_)
  by_cases hd : d = c
  · subst hd
    show (W.scheduler.markReschedulePendingOnCoreIf d b).reschedulePendingOnCore d = true
    rw [SchedulerState.markReschedulePendingOnCoreIf_reschedulePendingOnCore_self, hF]; rfl
  · show (W.scheduler.markReschedulePendingOnCoreIf d b).reschedulePendingOnCore c = true
    rw [SchedulerState.markReschedulePendingOnCoreIf_reschedulePendingOnCore_ne _ _ _ _ hd]
    exact hF

/-- The refill keeps every thread's queue placement. -/
theorem refillSchedContext_queuedOn (st : SystemState) (scId : SeLe4n.SchedContextId)
    (now : Nat) (hInv : st.objects.invExt) (c : CoreId) (t : SeLe4n.ThreadId) :
    (refillSchedContext st scId now).queuedOn c t = st.queuedOn c t :=
  (show SystemState.RunCoresAgree (refillSchedContext st scId now) st from fun y => by
    rw [refillSchedContext_getTcb?_eq st scId now hInv y]).queuedOn c t

/-- The refill writes its context's slot alone, a context on both sides, so it
keeps the key and the budget eligibility of every thread not bound to it. -/
theorem refillSchedContext_views_of_unbound (st : SystemState) (scId : SeLe4n.SchedContextId)
    (now : Nat) (hInv : st.objects.invExt) {t : SeLe4n.ThreadId}
    (hNo : ∀ tcb, st.getTcb? t = some tcb → tcb.schedContextBinding.scId? ≠ some scId) :
    schedKeyView (refillSchedContext st scId now) t = schedKeyView st t ∧
      budgetEligibleView (refillSchedContext st scId now) t = budgetEligibleView st t := by
  cases hS : st.getSchedContext? scId with
  | none =>
    rw [refillSchedContext, SystemState.updateSchedContext_eq_self_of_none hS]; exact ⟨rfl, rfl⟩
  | some sc =>
    have hPre := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS
    have hPost : (refillSchedContext st scId now).objects[scId.toObjId]? =
        some (.schedContext (cbsUpdateDeadline (sc.releaseReadyHead now) now true)) := by
      apply (SystemState.getSchedContext?_eq_some_iff _ _ _).mp
      unfold refillSchedContext
      rw [SystemState.updateSchedContext_getSchedContext?_self _ _ _ hInv, hS]; rfl
    have hFrame : ∀ oid, oid ≠ scId.toObjId →
        keyInputsOf (refillSchedContext st scId now).objects[oid]? = keyInputsOf st.objects[oid]? :=
      fun oid h => by
        unfold refillSchedContext
        rw [SystemState.updateSchedContext_objects_ne _ _ _ _ (Ne.symm h) hInv]
    exact ⟨schedKeyView_eq_of_scSlotWrite hFrame hPre hPost hNo,
      budgetEligibleView_eq_of_scSlotWrite hFrame hPre hPost hNo⟩

/-- What the refill and its wake leave of the refilled state: every view, every
binding and bound thread, the store invariant, and coverage — the wake flags
the core it places on, and the target-core mark only raises a flag. -/
theorem refillWakeOnCore_facts (st : SystemState) (e : CoreId) (scId : SeLe4n.SchedContextId)
    (now : Nat) (hInv : st.objects.invExt) :
    let R := refillSchedContext st scId now
    let M := refillWakeOnCore st e scId now
    (∀ t, schedKeyView M t = schedKeyView R t ∧ budgetEligibleView M t = budgetEligibleView R t) ∧
      stepCovers e R M ∧ bindingsAgree M R ∧
      (∀ s, (M.getSchedContext? s).map (·.boundThread) = (R.getSchedContext? s).map (·.boundThread)) := by
  intro R M
  have hR : R.objects.invExt := refillSchedContext_preserves_objects_invExt st scId now hInv
  show (∀ t, schedKeyView (refillWakeOnCore st e scId now) t = schedKeyView R t ∧
      budgetEligibleView (refillWakeOnCore st e scId now) t = budgetEligibleView R t) ∧
    stepCovers e R (refillWakeOnCore st e scId now) ∧ bindingsAgree (refillWakeOnCore st e scId now) R ∧
    (∀ s, ((refillWakeOnCore st e scId now).getSchedContext? s).map (·.boundThread) =
      (R.getSchedContext? s).map (·.boundThread))
  unfold refillWakeOnCore
  dsimp only
  split
  · split
    · exact ⟨fun _ => ⟨rfl, rfl⟩, stepCovers_refl e R, bindingsAgree.refl R, fun _ => rfl⟩
    · rename_i tid _ _
      refine ⟨fun t => ?_, stepCovers_trans (wakeThread_stepCovers e R tid e hR).1
        (markReschedulePendingOnCoreIf_stepCovers e _ _ _), ?_, fun s => ?_⟩
      · exact enqueueRunnableOnCore_views R _ tid hR t
      · exact enqueueRunnableOnCore_bindingsAgree R _ tid hR
      · exact enqueueRunnableOnCore_boundThread R _ tid hR s
  · exact ⟨fun _ => ⟨rfl, rfl⟩, stepCovers_refl e R, bindingsAgree.refl R, fun _ => rfl⟩

/-- Under the binding pair, a thread that the context does not name as bound
binds no reading of it. -/
theorem notBound_of_bidirectional {st : SystemState} (hBi : schedContextBindingBidirectional st)
    {scId : SeLe4n.SchedContextId} {t : SeLe4n.ThreadId}
    (h : ∀ sc, st.getSchedContext? scId = some sc → sc.boundThread ≠ some t) :
    ∀ tcb, st.getTcb? t = some tcb → tcb.schedContextBinding.scId? ≠ some scId := by
  intro tcb hT hb
  obtain ⟨sc, hS, hbt⟩ := hBi t tcb scId ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hb
  exact h sc ((SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hS) hbt

/-- **One due replenishment covers**: the refill moves only its bound thread's
view (the binding pair), the wake flags the core it places on, and the key hook
flags every core whose decision the bound thread's moved key or regained
candidacy staled. -/
theorem processOneReplenishmentOnCore_stepCovers (st : SystemState) (e : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt)
    (hBi : schedContextBindingBidirectional st) :
    stepCovers e st (processOneReplenishmentOnCore st e scId now) := by
  obtain ⟨hV, hC, -, -⟩ := refillWakeOnCore_facts st e scId now hInv
  have hRq := refillSchedContext_queuedOn st scId now hInv
  have hSlots : ∀ c, c ≠ e →
      (refillWakeOnCore st e scId now).scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, (refillWakeOnCore st e scId now).queuedOn c t = true → st.queuedOn c t = true) ∧
        (refillWakeOnCore st e scId now).scheduler.currentOnCore c = st.scheduler.currentOnCore c) :=
    fun c hc => (slots_of_reschedulePendingCovers hC.1 c hc).imp id fun ⟨h1, h2⟩ =>
      ⟨fun t ht => (hRq c t) ▸ h1 t ht, by rw [h2, refillSchedContext_scheduler_eq]⟩
  have hFrame : ∀ t, (∀ tcb, st.getTcb? t = some tcb → tcb.schedContextBinding.scId? ≠ some scId) →
      schedKeyView (refillWakeOnCore st e scId now) t = schedKeyView st t ∧
      budgetEligibleView (refillWakeOnCore st e scId now) t = budgetEligibleView st t :=
    fun t hNo =>
      have hR := refillSchedContext_views_of_unbound st scId now hInv hNo
      ⟨(hV t).1.trans hR.1, (hV t).2.trans hR.2⟩
  refine ⟨?_, fun c _ hF => processOneReplenishmentOnCore_reschedulePendingOnCore_mono st e scId now c hF,
    fun c hc t ht => ?_, residentKeptOffCore_of_eq
      (congrArg MachineState.residentCode (processOneReplenishmentOnCore_machine_eq st e scId now))⟩
  rotate_left
  · rw [processOneReplenishmentOnCore, markRefillKeyChange_extract_frame
      (fun s => s.scheduler.currentOnCore c) st _ scId (fun _ _ => by
        simp [SystemState.markReschedulePendingOnCore])] at ht
    have := hC.3 c hc t ht
    rwa [refillSchedContext_scheduler_eq] at this
  rw [processOneReplenishmentOnCore]
  unfold markRefillKeyChange
  cases hS : st.getSchedContext? scId with
  | none =>
    have hNo := fun t => notBound_of_bidirectional hBi (scId := scId) (t := t)
      (fun sc h => by rw [hS] at h; cases h)
    exact reschedulePendingCovers_of_frame (fun t => (hFrame t (hNo t)).1)
      (fun t => (hFrame t (hNo t)).2) hSlots
  | some sc =>
    dsimp only
    cases hB : sc.boundThread with
    | none =>
      have hNo := fun t => notBound_of_bidirectional hBi (scId := scId) (t := t)
        (fun sc' h => by rw [hS] at h; cases h; rw [hB]; exact fun h => by cases h)
      exact reschedulePendingCovers_of_frame (fun t => (hFrame t (hNo t)).1)
        (fun t => (hFrame t (hNo t)).2) hSlots
    | some t0 =>
      refine markKeyChangeFrom_covers (fun t ht => hFrame t ?_) hSlots
      exact notBound_of_bidirectional hBi (fun sc' h => by
        rw [hS] at h; cases h; rw [hB]; exact fun h => ht (Option.some.inj h).symm)

/-- One due replenishment keeps the binding pair: no binding moves and no
context's bound thread. -/
theorem processOneReplenishmentOnCore_preserves_bidirectional (st : SystemState) (e : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt)
    (hBi : schedContextBindingBidirectional st) :
    schedContextBindingBidirectional (processOneReplenishmentOnCore st e scId now) := by
  obtain ⟨-, -, hBa, hBt⟩ := refillWakeOnCore_facts st e scId now hInv
  refine hBi.of_bindings ((bindingsAgree.of_objects_eq (markRefillKeyChange_objects _ _ _)).trans
    (hBa.trans (by unfold refillSchedContext; exact bindingsAgree.updateSchedContext hInv)))
    (fun s => ?_)
  rw [processOneReplenishmentOnCore, markRefillKeyChange_getSchedContext?, hBt s,
    refillSchedContext_boundThread st scId now hInv s]

/-- **The drain covers**: the replenish-queue write-back moves no view, queue,
current slot or flag, and each due replenishment covers under the store
invariant and the binding pair, which each one keeps. -/
theorem processReplenishmentsDueOnCore_stepCovers (st : SystemState) (c : CoreId) (now : Nat)
    (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st) :
    stepCovers c st (processReplenishmentsDueOnCore st c now) := by
  simp only [processReplenishmentsDueOnCore]
  refine (drainDueOnCore_induction
    (fun s => s.objects.invExt ∧ schedContextBindingBidirectional s ∧ stepCovers c st s) c now
    (fun s scId h => ⟨processOneReplenishmentOnCore_preserves_objects_invExt s c scId now h.1,
      processOneReplenishmentOnCore_preserves_bidirectional s c scId now h.1 h.2.1,
      stepCovers_trans h.2.2 (processOneReplenishmentOnCore_stepCovers s c scId now h.1 h.2.1)⟩)
    (fun s scId h => ⟨SystemState.releasePlace_objects_invExt s c scId h.1,
      schedContextBindingBidirectional_of_agreeOffReleaseLinks
        (SystemState.releasePlace_agree s c scId) h.2.1,
      stepCovers_trans h.2.2 (releasePlace_stepCovers c s c scId)⟩)
    _ st ⟨hInv, hBi, stepCovers_refl c st⟩).2.2

/-! ### The charge's timeout pass -/

/-- The abort of a timed-out thread's IPC moves no key input and no scheduler
slot: it unlinks the thread from the endpoint queue and rewrites its TCB's IPC
state, message, timeout budget and return registers. -/
theorem abortPendingIpcOnEndpoint_stepCovers (e : CoreId) {epId : SeLe4n.ObjId} {isRecvQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : abortPendingIpcOnEndpoint epId isRecvQ tid st = .ok st') : stepCovers e st st' := by
  refine stepCovers_of_keys_sched ?_ (abortPendingIpcOnEndpoint_scheduler_eq _ _ _ _ _ h)
    (hRes := congrArg MachineState.residentCode (abortPendingIpcOnEndpoint_machine _ _ _ _ _ h))
  unfold abortPendingIpcOnEndpoint at h
  split at h
  · cases h
  · rename_i st1 hEQR
    have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hEQR
    split at h
    · cases h
    · rename_i tcb hLook
      dsimp only at h
      split at h
      · cases h
      · rename_i hS
        cases h
        exact keyInputsEq_trans (endpointQueueRemove_keyInputsEq hInv hEQR)
          (keyInputsEq_storeObject hInv1 hS (by rw [lookupTcb_some_objects _ _ _ hLook]; rfl))

/-- The priority-inheritance revert covers: each step is a boost update, which
flags the cores its key change stales. -/
theorem revertPriorityInheritance_stepCovers (e : CoreId) (fuel : Nat) :
    ∀ (st : SystemState) (tid : SeLe4n.ThreadId), st.objects.invExt →
      stepCovers e st (PriorityInheritance.revertPriorityInheritance st tid fuel) := by
  induction fuel with
  | zero => intro st _ _; exact stepCovers_refl e st
  | succ fuel ih =>
    intro st tid hInv
    have h1 := updatePipBoostOnCore_stepCovers e Concurrency.bootCoreId st tid hInv
    have hI1 := PriorityInheritance.updatePipBoost_preserves_objects_invExt st tid hInv
    simp only [PriorityInheritance.revertPriorityInheritance]
    split
    · exact stepCovers_trans h1 (ih _ _ hI1)
    · exact h1

/-- **A thread's timeout covers**: the abort is object-only, the wake flags the
core it places on, and the revert's boosts flag what their key changes stale. -/
theorem timeoutThread_stepCovers (e : CoreId) {epId : SeLe4n.ObjId} {isRecvQ : Bool}
    {tid : SeLe4n.ThreadId} {ec : CoreId} {st : SystemState}
    {r : SystemState × Option (CoreId × SgiKind)} (hInv : st.objects.invExt)
    (h : timeoutThread epId isRecvQ tid ec st = .ok r) : stepCovers e st r.1 := by
  unfold timeoutThread at h
  split at h
  · cases h
  · rename_i st2 hAbort
    have hA := abortPendingIpcOnEndpoint_stepCovers e hInv hAbort
    have hI2 := abortPendingIpcOnEndpoint_preserves_objects_invExt _ _ _ _ _ hInv hAbort
    have hW := (wakeThread_stepCovers e st2 tid ec hI2).1
    have hIW := wakeThread_preserves_objects_invExt st2 tid ec hI2
    dsimp only at h
    split at h
    · rename_i serverId _
      cases h
      exact stepCovers_trans hA (stepCovers_trans hW (stepCovers_trans
        (unlinkReplyWaiter_stepCovers e _ tid serverId)
        (revertPriorityInheritance_stepCovers e _ _ serverId
          (SystemState.unlinkReplyWaiter_objects_invExt _ _ _ hIW))))
    · cases h
      exact stepCovers_trans hA hW

/-- **The timeout pass covers**: a fold of thread timeouts, each covering under
the store invariant, which each keeps. -/
theorem timeoutBlockedThreads_stepCovers (e : CoreId) (st : SystemState)
    (scId : SeLe4n.SchedContextId) (ec : CoreId) (hInv : st.objects.invExt) :
    stepCovers e st (timeoutBlockedThreads st scId ec).1 := by
  rw [timeoutBlockedThreads_eq_fold]
  generalize (schedContextTimeoutThreads st scId) = tids
  suffices H : ∀ (acc : SystemState × List (SeLe4n.ThreadId × KernelError) × List (CoreId × SgiKind)),
      stepCovers e st acc.1 → acc.1.objects.invExt →
      stepCovers e st (tids.foldl (timeoutBlockedThreadStep ec) acc).1 from
    H _ (stepCovers_refl e st) hInv
  induction tids with
  | nil => intro acc h _; exact h
  | cons hd tl ih =>
    intro acc hC hA
    rw [List.foldl_cons]
    obtain ⟨s, errs, sgis⟩ := acc
    apply ih
    · simp only [timeoutBlockedThreadStep]
      split
      · split
        · split
          · rename_i r hT
            exact stepCovers_trans hC (timeoutThread_stepCovers e hA hT)
          · exact hC
        · exact hC
      · exact hC
    · simp only [timeoutBlockedThreadStep]
      split
      · split
        · split
          · rename_i r hT
            exact timeoutThread_preserves_objects_invExt _ _ _ _ _ _ hA hT
          · exact hA
        · exact hA
      · exact hA

/-! ### The tick -/

/-- A step that keeps the store, every remote `current` slot and every remote
flag that was up covers: the views and queue membership read the store alone. -/
theorem stepCovers_of_objects_eq {e : CoreId} {pre post : SystemState}
    (hObj : post.objects = pre.objects)
    (hCur : ∀ c, c ≠ e → post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c)
    (hMono : reschedulePendingMonotone e pre post)
    (hRes : post.machine.residentCode = pre.machine.residentCode := by resident_frame) :
    stepCovers e pre post :=
  have hKeys := keyInputsEq_of_objects_eq hObj
  stepCovers_of_frame (schedKeyView_eq_of_keyInputsEq hKeys)
    (budgetEligibleView_eq_of_keyInputsEq hKeys)
    (fun c _ t ht => (hKeys.runCoresAgree.queuedOn c t) ▸ ht) hCur hMono hRes

/-- Writing a core's timeout-error diagnostic covers. -/
theorem setLastTimeoutErrorsOnCore_stepCovers (e : CoreId) (st : SystemState) (c : CoreId)
    (v : List (SeLe4n.ThreadId × KernelError)) :
    stepCovers e st { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c v } :=
  stepCovers_of_objects_eq rfl (fun _ _ => by simp) (fun _ _ h => by simpa using h)

/-- The drain keeps the binding pair. -/
theorem processReplenishmentsDueOnCore_preserves_bidirectional (st : SystemState) (c : CoreId)
    (now : Nat) (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st) :
    schedContextBindingBidirectional (processReplenishmentsDueOnCore st c now) := by
  simp only [processReplenishmentsDueOnCore]
  exact (drainDueOnCore_induction
    (fun s => s.objects.invExt ∧ schedContextBindingBidirectional s) c now
    (fun s scId h => ⟨processOneReplenishmentOnCore_preserves_objects_invExt s c scId now h.1,
      processOneReplenishmentOnCore_preserves_bidirectional s c scId now h.1 h.2⟩)
    (fun s scId h => ⟨SystemState.releasePlace_objects_invExt s c scId h.1,
      schedContextBindingBidirectional_of_agreeOffReleaseLinks
        (SystemState.releasePlace_agree s c scId) h.2⟩)
    _ st ⟨hInv, hBi⟩).2

/-- **The prepared state covers**: the diagnostic clear frames every view, slot
and flag, and the drain covers; the binding pair survives both. -/
theorem timerTickOnCorePrepared_stepCovers (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st) :
    stepCovers c st (timerTickOnCorePrepared st c) ∧
      schedContextBindingBidirectional (timerTickOnCorePrepared st c) := by
  unfold timerTickOnCorePrepared
  exact ⟨stepCovers_trans (setLastTimeoutErrorsOnCore_stepCovers c st c [])
      (processReplenishmentsDueOnCore_stepCovers _ c _ hInv hBi),
    processReplenishmentsDueOnCore_preserves_bidirectional _ c _ hInv hBi⟩

/-- **The prepared tick state carries `currentBoundHomedOnCore`** (WS-ZA ZA6.3):
the diagnostic clear and the drain keep core `c`'s current thread, every thread's
home and the binding pair, so the thread current on `c` before the tick, homed on
`c` by the placement invariant (`currentHome`), is homed on `c` after it, and the
context its binding names names it.  The budget phase's affinity precondition,
discharged from the two invariants the per-core bundle carries. -/
theorem timerTickOnCorePrepared_currentBoundHomedOnCore (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hD : st.currentDequeuedUnique)
    (hBi : schedContextBindingBidirectional st) :
    currentBoundHomedOnCore (timerTickOnCorePrepared st c) c := by
  intro tid tcb hCur hTcb
  have hInv0 : ({ st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } :
      SystemState).objects.invExt := hInv
  have hCur0 : st.scheduler.currentOnCore c = some tid := by
    unfold timerTickOnCorePrepared at hCur
    rw [processReplenishmentsDueOnCore_currentOnCore_eq] at hCur
    simpa using hCur
  obtain ⟨x, hx, -⟩ := hD.currentActive c tid hCur0
  refine ⟨?_, fun scId sc hb hSc => ?_⟩
  · unfold timerTickOnCorePrepared
    rw [processReplenishmentsDueOnCore_determineTargetCore _ c _ hInv0]
    exact determineTargetCore_eq_of_homedOn hx (hD.currentHome c tid hCur0)
  · obtain ⟨sc0, hS0, hB0⟩ := (timerTickOnCorePrepared_stepCovers st c hInv hBi).2 tid tcb scId
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb) hb
    rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hS0] at hSc
    cases hSc
    exact hB0

/-- **Every committed state carries `currentBoundHomedOnCore` at every core**
(WS-ZA ZA6.3): the placement invariant homes each current thread on its core
(`currentHome`), and the binding pair has its context name it — the state a
syscall on core `c` (the bound yield's charge among them) starts from. -/
theorem currentBoundHomedOnCore_of_placement (st : SystemState) (c : CoreId)
    (hD : st.currentDequeuedUnique) (hBi : schedContextBindingBidirectional st) :
    currentBoundHomedOnCore st c := by
  intro tid tcb hCur hTcb
  obtain ⟨x, hx, -⟩ := hD.currentActive c tid hCur
  refine ⟨determineTargetCore_eq_of_homedOn hx (hD.currentHome c tid hCur),
    fun scId sc hb hSc => ?_⟩
  obtain ⟨sc0, hS0, hB0⟩ := hBi tid tcb scId ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb) hb
  rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hS0] at hSc
  cases hSc
  exact hB0

/-- **The bound yield's requeue is on the context's own core** (WS-ZA ZA6.3):
the yielding thread is current on `c`, so its context, charged its budget,
is free on `c`, and the requeue's branch that leaves both
queues as they are is unreachable (`spendBudget_requeue_releaseFreeFor`). -/
theorem yieldCharge_requeue_releaseFreeFor {st : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {scId : SchedContextId} {sc : SchedContext}
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore st d)
    (hD : st.currentDequeuedUnique) (hBi : schedContextBindingBidirectional st)
    (hc : st.scheduler.currentOnCore c = some tid)
    (hT : st.getTcb? tid = some tcb) (hb : tcb.schedContextBinding.scId? = some scId)
    (hSc : st.getSchedContext? scId = some sc) :
    (st.rewriteObject scId.toObjId (.schedContext (cbsUpdateDeadline
        (sc.chargeBudget st.machine.timer sc.budget.val st.machine.timer) st.machine.timer true))
      (SystemState.rewriteAdmissible_schedContext hSc _)).releaseFreeFor c scId = true :=
  spendBudget_requeue_releaseFreeFor _ _ hInv hRef hAff
    (currentBoundHomedOnCore_of_placement st c hD hBi) hc hT hb hSc

/-- **The exhausting charge covers**: the spend and its key hook cover, the
timeout pass covers, and the diagnostic write and the timeout wakes' flags
frame every view and slot and only raise flags. -/
theorem budgetExhaustOnCore_stepCovers (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (scId : SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (ticks : Nat) (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st)
    (hBindId : tcb.schedContextBinding.scId? = some scId)
    (hAway : ∀ c', c' ≠ c → st.scheduler.reschedulePendingOnCore c' = false →
      st.queuedOn c' tid = false) :
    stepCovers c st (budgetExhaustOnCore st c tid (effectiveSchedParams st tcb) scId sc hSc ticks) := by
  obtain ⟨hS, hI⟩ := spendBudgetKeyHook_stepCovers st c tid tcb hTcb scId sc hSc _ ticks hInv hBi
    hBindId hAway
  refine stepCovers_trans (stepCovers_trans hS (timeoutBlockedThreads_stepCovers c _ scId c hI)) ?_
  unfold budgetExhaustOnCore
  exact stepCovers_of_objects_eq rfl (fun _ _ => by simp)
    (fun _ _ h => markRescheduleTargets_reschedulePendingOnCore_mono _ _ _ (by simpa using h))

/-- **The charge covers.**  The unbound decrement writes `timeSlice`, no key
input; the slice expiry covers; the bound charge that leaves budget keeps the
context's deadline and its budget positive; the exhausting charge covers, the
charged thread on no unflagged remote queue (`hAway`); a context the store does
not hold is charged nothing. -/
theorem timerTickBudgetOnCore_stepCovers (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st)
    (hAway : ∀ c', c' ≠ c → st.scheduler.reschedulePendingOnCore c' = false →
      st.queuedOn c' tid = false) :
    stepCovers c st (timerTickBudgetOnCore st c tid tcb hTcb).1 := by
  have hO := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  unfold timerTickBudgetOnCore
  split
  · split
    · exact sliceExpireOnCore_stepCovers c st tid tcb hTcb hInv
    · exact stepCovers_of_scheduler_eq
        (keyInputsEq_rewriteObject (SystemState.rewriteAdmissible_tcb hTcb _) hInv
          (by rw [hO]; rfl))
        rfl
  all_goals
    rename_i hBind
    split
    · rename_i sc hSc _
      dsimp only
      split
      · exact budgetExhaustOnCore_stepCovers st c tid tcb hTcb _ sc hSc 1 hInv hBi
          (by rw [hBind]; rfl) hAway
      · rename_i hBudget
        have hScRaw := (SystemState.getSchedContext?_eq_some_iff st _ sc).mp hSc
        have hEx : sc.tickExhausts (st.machine.timer - 1) = false := by simpa using hBudget
        have hD := (SchedContext.fields_of_refillsErased
          (sc.chargeBudget_refillsErased (st.machine.timer - 1) 1 st.machine.timer)).2.2.2.2.1
        have hP1 := sc.chargeBudget_tick_pos _ st.machine.timer hEx
        have hP0 := sc.tickExhausts_false_pos _ hEx
        exact stepCovers_of_scheduler_eq
          (keyInputsEq_rewriteObject (SystemState.rewriteAdmissible_schedContext hSc _) hInv (by
            rw [hScRaw]
            simp only [keyInputsOf, Budget.isPositive, hD]
            congr 3
            simp only [decide_eq_decide]
            omega))
          rfl
    · exact stepCovers_refl c st

/-- The re-enqueue of the outgoing thread covers: the context save covers, and
the enqueue writes core `e`'s queue alone. -/
theorem requeueOutgoingOnCore_stepCovers (e : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) : stepCovers e st (requeueOutgoingOnCore st e) := by
  refine stepCovers_trans (saveOutgoingContextOnCore_stepCovers e st hInv)
    (stepCovers_of_local_slots
      (schedKeyView_of_objectsAgreeOffRunLinks (requeueOutgoingOnCore_objectsAgreeOffRunLinks st e))
      (budgetEligibleView_of_objectsAgreeOffRunLinks
        (requeueOutgoingOnCore_objectsAgreeOffRunLinks st e)) ?_ ?_)
  · intro c hc t ht
    unfold requeueOutgoingOnCore at ht; dsimp only at ht
    split at ht
    · exact ht
    · split at ht
      · split at ht
        · rw [SystemState.runEnqueueAdmitted_queuedOn] at ht
          split at ht
          · simp [hc] at ht
          · exact ht
        · exact ht
      · exact ht
  · intro c hc
    obtain ⟨E, hE⟩ := requeueOutgoingOnCore_scheduler st e
    have hne : e ≠ c := Ne.symm hc
    rw [hE, saveOutgoingContextOnCore_scheduler]
    simp [SchedulerState.setRunQueueOnCore, SchedulerState.setRunQueueEndsOnCore,
      SchedulerState.currentOnCore, SchedulerState.reschedulePendingOnCore]

/-- **The domain step covers**: the in-domain decrement writes core `e`'s
quantum alone; the boundary re-enqueues core `e`'s outgoing thread, rewrites
core `e`'s domain slots and runs core `e`'s scheduling point. -/
theorem scheduleDomainOnCoreState_stepCovers (e : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) : stepCovers e st (scheduleDomainOnCoreState st e) := by
  unfold scheduleDomainOnCoreState
  split
  · exact stepCovers_refl e st
  · split
    · have hSw : stepCovers e st (switchDomainOnCoreState st e) ∧
          (switchDomainOnCoreState st e).objects.invExt := by
        unfold switchDomainOnCoreState
        split
        · exact ⟨stepCovers_refl e st, hInv⟩
        · dsimp only
          split
          · exact ⟨stepCovers_refl e st, hInv⟩
          · refine ⟨stepCovers_trans (requeueOutgoingOnCore_stepCovers e st hInv)
              (stepCovers_of_objects_eq rfl (fun c hc => ?_) (fun c hc hp => ?_)),
              requeueOutgoingOnCore_objects_invExt st e hInv⟩
            · have hne : e ≠ c := Ne.symm hc
              simp [hne]
            · have hne : e ≠ c := Ne.symm hc
              simpa [hne] using hp
      exact stepCovers_trans hSw.1 (scheduleEffectiveOnCore_stepCovers e _ _ hSw.2
        (scheduleEffectiveOnCore_eq_state _ e))
    · unfold decrementDomainTimeOnCore
      exact stepCovers_of_objects_eq rfl (fun _ _ => by simp) (fun _ _ h => by simpa using h)

/-- **The tick covers** (WS-ZA ZA6.2, the tick's completeness over the flags).
After `timerTickOnCore st c`, every core other than `c` whose scheduling
decision the tick staled — a due refill's wake or regained candidacy or moved
deadline, a timeout wake, the exhausting charge's moved deadline, including a
thread already queued but ineligible before its refill (PR #880 round 7) —
has its reschedule flag up, and no remote flag came down.  Consumes the store
invariant and the binding pair, which every phase keeps; no runtime check. -/
theorem timerTickOnCore_stepCovers (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st)
    (hD : st.currentDequeuedUnique) :
    stepCovers c st (timerTickOnCore st c) := by
  obtain ⟨hP, hPBi⟩ := timerTickOnCorePrepared_stepCovers st c hInv hBi
  have hPInv := timerTickOnCorePrepared_preserves_objects_invExt st c hInv
  -- The charged thread, current on `c`, was on no queue before the tick
  -- (`currentDequeuedUnique`), so on no unflagged remote queue after the drain.
  have hAway : ∀ tid, (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid →
      ∀ c', c' ≠ c → (timerTickOnCorePrepared st c).scheduler.reschedulePendingOnCore c' = false →
        (timerTickOnCorePrepared st c).queuedOn c' tid = false := by
    intro tid hCur c' hc' hFl
    have hCur0 : st.scheduler.currentOnCore c = some tid := by
      unfold timerTickOnCorePrepared at hCur
      rw [processReplenishmentsDueOnCore_currentOnCore_eq] at hCur
      simpa using hCur
    cases hq : (timerTickOnCorePrepared st c).queuedOn c' tid
    · rfl
    · rcases hP.1 c' hc' with hUp | hUn
      · rw [hFl] at hUp; cases hUp
      · have := (hUn.1 tid hq).1
        rw [hD.not_queued hCur0 c'] at this; cases this
  refine (timerTickOnCore_of_current (P := fun s => stepCovers c st s ∧ s.objects.invExt) st c
    ⟨hP, hPInv⟩ (fun s hs => ⟨stepCovers_trans hs.1
        (handleRescheduleSgiOnCore_stepCovers c s _ hs.2 (handleRescheduleSgiOnCore_eq_state s c)),
      handleRescheduleSgiOnCore_preserves_objects_invExt s c _ hs.2
        (handleRescheduleSgiOnCore_eq_state s c)⟩)
    (fun s hs => ⟨stepCovers_trans hs.1
        (scheduleEffectiveOnCore_stepCovers c s _ hs.2 (scheduleEffectiveOnCore_eq_state s c)),
      scheduleEffectiveOnCore_preserves_objects_invExt s c _ hs.2
        (scheduleEffectiveOnCore_eq_state s c)⟩)
    (fun tid tcb hTcb st3 b hCur hb => ⟨stepCovers_trans hP (by
        have h := timerTickBudgetOnCore_stepCovers _ c tid tcb hTcb hPInv hPBi (hAway tid hCur)
        rw [hb] at h; exact h),
      timerTickBudgetOnCore_preserves_objects_invExt _ c tid tcb st3 b hPInv hb⟩)).1

/-- The local decision leaves the deciding core's flag down. -/
theorem handleRescheduleOnCoreState_reschedulePendingOnCore_self (st : SystemState) (c : CoreId) :
    (handleRescheduleOnCoreState st c).scheduler.reschedulePendingOnCore c = false := by
  unfold handleRescheduleOnCoreState rescheduleNoCandidateOnCore
  split
  · split <;> simp [SystemState.clearReschedulePendingOnCore]
  · dsimp only
    split
    · split
      · split
        · simp
        · split <;> simp [SystemState.clearReschedulePendingOnCore]
      · split <;> simp [SystemState.clearReschedulePendingOnCore]
    · simp [SystemState.clearReschedulePendingOnCore]

/-- The dispatch leaves the dispatching core's flag down. -/
theorem scheduleEffectiveOnCoreState_reschedulePendingOnCore_self (st : SystemState) (c : CoreId) :
    (scheduleEffectiveOnCoreState st c).scheduler.reschedulePendingOnCore c = false := by
  unfold scheduleEffectiveOnCoreState
  split
  · simp [SystemState.clearReschedulePendingOnCore]
  · simp

/-- **The tick decides on its own flag**: core `c`'s flag is down after its tick.
A wake the drain or a timeout landed on core `c` itself raised it, so the
tick's own scheduling decision ran on it (PR #880 round 7); a ticking core is
never in its own SGI set. -/
theorem timerTickOnCore_reschedulePendingOnCore_self (st : SystemState) (c : CoreId) :
    (timerTickOnCore st c).scheduler.reschedulePendingOnCore c = false := by
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ |
      ⟨_, _, _, _, _, _, h⟩ <;> rw [h]
  rotate_left 2
  · exact scheduleEffectiveOnCoreState_reschedulePendingOnCore_self _ c
  all_goals
    unfold rescheduleIfPendingOnCore
    split
    · exact handleRescheduleOnCoreState_reschedulePendingOnCore_self _ c
    · rename_i hF; simpa using hF

/-- The clock advance writes the timer alone: no core's residency moves. -/
theorem tickClockedState_residentCode (st : SystemState) (c : CoreId) :
    (tickClockedState st c).machine.residentCode = st.machine.residentCode := by
  unfold tickClockedState; split <;> rfl

/-- **The run-loop step covers**: the clock advance frames every view, slot and
flag; the tick covers; the domain step covers. -/
theorem perCoreTimerTickStep_stepCovers (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < Concurrency.numCores) (hInv : st.objects.invExt)
    (hBi : schedContextBindingBidirectional st)
    (hD : st.currentDequeuedUnique) :
    stepCovers ⟨coreId.toNat, h⟩ st (perCoreTimerTickStep st coreId).1 := by
  rw [perCoreTimerTickStep_valid_core st coreId h]
  have hC : stepCovers ⟨coreId.toNat, h⟩ st (tickClockedState st ⟨coreId.toNat, h⟩) :=
    stepCovers_of_objects_eq (tickClockedState_objects _ _) (fun _ _ => by simp)
      (fun _ _ hp => by simpa using hp) (tickClockedState_residentCode _ _)
  have hCInv : (tickClockedState st ⟨coreId.toNat, h⟩).objects.invExt := by
    rw [tickClockedState_objects]; exact hInv
  have hCBi : schedContextBindingBidirectional (tickClockedState st ⟨coreId.toNat, h⟩) := by
    unfold tickClockedState; split <;> exact hBi
  have hCD : (tickClockedState st ⟨coreId.toNat, h⟩).currentDequeuedUnique :=
    SystemState.currentDequeuedUniqueExcept_of_eq (st := st)
      (by rw [tickClockedState_scheduler])
      (fun c t => by unfold SystemState.runLinkOn SystemState.getTcb?; rw [tickClockedState_objects])
      (SystemState.StateMono.of_objects (tickClockedState_objects _ _)) hD
  exact stepCovers_trans (stepCovers_trans hC (timerTickOnCore_stepCovers _ _ hCInv hCBi hCD))
    (scheduleDomainOnCoreState_stepCovers _ _ (timerTickOnCore_preserves_objects_invExt _ _ hCInv))

/-- **The run-loop step's SGIs are complete** (WS-ZA ZA6.2).  Every core other
than the ticking one whose scheduling decision the step staled is poked by the
step's SGI set, unless its flag was already up before the step — its SGI is
then outstanding from the entry that raised it, and one reschedule answers
both (the duplicate collapse). -/
theorem perCoreTimerTickStep_sgis_complete (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < Concurrency.numCores) (hInv : st.objects.invExt)
    (hBi : schedContextBindingBidirectional st)
    (hD : st.currentDequeuedUnique) (d : CoreId) (hd : d ≠ ⟨coreId.toNat, h⟩)
    (hStaled : ¬ coreDecisionUnstaled st (perCoreTimerTickStep st coreId).1 d) :
    (perCoreTimerTickStep st coreId).2.get d = true ∨
      st.scheduler.reschedulePendingOnCore d = true := by
  have hF := ((perCoreTimerTickStep_stepCovers st coreId h hInv hBi hD).1 d hd).resolve_right hStaled
  rw [perCoreTimerTickStep_raised_get]
  cases hPre : st.scheduler.reschedulePendingOnCore d
  · left
    have hG : st.scheduler.reschedulePending.get d = false := hPre
    have hF' : (perCoreTimerTickStep st coreId).1.scheduler.reschedulePending.get d = true := hF
    rw [hG, hF']; rfl
  · exact Or.inr rfl

/-- **The run-loop step fires every SGI the diff names**, unless it was already
outstanding: the whole-index diff between the pre-state and the committed state
— what the tick returned as its SGI list before the flags carried it — names
no core the step's SGI set misses, but for a core whose flag was already up
(the duplicate collapse).  `hId` is the committed store's self-identity. -/
theorem perCoreTimerTickStep_sgis_cover_diff (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < Concurrency.numCores) (hInv : st.objects.invExt)
    (hBi : schedContextBindingBidirectional st)
    (hD : st.currentDequeuedUnique)
    (hId : ∀ oid (tcb : TCB), (perCoreTimerTickStep st coreId).1.getObject? oid = some (.tcb tcb) →
      tcb.tid.toObjId = oid)
    {d : CoreId} {k : SgiKind}
    (hMem : (d, k) ∈ PriorityInheritance.computeCrossCoreSgis st (perCoreTimerTickStep st coreId).1
      ⟨coreId.toNat, h⟩) :
    (perCoreTimerTickStep st coreId).2.get d = true ∨
      st.scheduler.reschedulePendingOnCore d = true := by
  have hF := computeCrossCoreSgis_core_flagged_of_covers hId
    (perCoreTimerTickStep_stepCovers st coreId h hInv hBi hD).1 hMem
  rw [perCoreTimerTickStep_raised_get]
  cases hPre : st.scheduler.reschedulePendingOnCore d
  · left
    have hG : st.scheduler.reschedulePending.get d = false := hPre
    have hF' : (perCoreTimerTickStep st coreId).1.scheduler.reschedulePending.get d = true := hF
    rw [hG, hF']; rfl
  · exact Or.inr rfl

/-- The domain step leaves the ticking core's flag where the tick left it, or
down when it dispatches. -/
theorem scheduleDomainOnCoreState_reschedulePendingOnCore_self (st : SystemState) (c : CoreId)
    (hF : st.scheduler.reschedulePendingOnCore c = false) :
    (scheduleDomainOnCoreState st c).scheduler.reschedulePendingOnCore c = false := by
  unfold scheduleDomainOnCoreState
  split
  · exact hF
  · split
    · exact scheduleEffectiveOnCoreState_reschedulePendingOnCore_self _ c
    · unfold decrementDomainTimeOnCore; simpa using hF

/-- **The step never pokes the ticking core**: its own flag is down after the
step, so the step's SGI set never names it. -/
theorem perCoreTimerTickStep_raised_self (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < Concurrency.numCores) :
    (perCoreTimerTickStep st coreId).2.get ⟨coreId.toNat, h⟩ = false := by
  rw [perCoreTimerTickStep_raised_get, perCoreTimerTickStep_valid_core st coreId h]
  have := scheduleDomainOnCoreState_reschedulePendingOnCore_self _ ⟨coreId.toNat, h⟩
    (timerTickOnCore_reschedulePendingOnCore_self (tickClockedState st ⟨coreId.toNat, h⟩)
      ⟨coreId.toNat, h⟩)
  have h' : (perCoreTimerTickPost st ⟨coreId.toNat, h⟩).scheduler.reschedulePending.get
      ⟨coreId.toNat, h⟩ = false := this
  rw [h']; simp

end SeLe4n.Kernel
