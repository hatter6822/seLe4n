-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Scheduling
import SeLe4n.Kernel.IPC.Invariant.SchedLinkFrame
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationQueueShape
import SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation

/-!
# A suspend keeps every context named by its holder

The restart of an IPC-blocked thread runs the suspend's cancel and then the
resume (`restartThreadOnCore`), and the resume's context settle reads, on the
state the suspend leaves, that every context a thread holds is the one its
binding names (`holdersNameTheirContexts`).  This module carries that fact
across every step of `suspendThreadOnCore`: most steps write no binding code
and no context's holder (`bindingLinksAgree`); the head cut clears a holder's
owner code and keeps the context it names; the donation return of a
reply-blocked caller moves one context from its holder to the caller, which
held none.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- A binding read off its codes names the context its context code names. -/
theorem schedContextBinding_scId?_of_codes {x y : TCB}
    (h : x.scBindingScCode = y.scBindingScCode) :
    x.schedContextBinding.scId? = y.schedContextBinding.scId? := by
  simp only [TCB.schedContextBinding, h]
  cases y.scBindingScCode <;> cases x.scBindingOwnerCode <;> cases y.scBindingOwnerCode <;> rfl

/-- **A step whose contexts are contexts before it, held by the same thread, and
whose threads are threads before it, naming the same context, keeps every
context named by its holder.** -/
theorem holdersNameTheirContexts.of_back {st st' : SystemState}
    (hS : ∀ s sc', st'.getSchedContext? s = some sc' →
      ∃ sc, st.getSchedContext? s = some sc ∧ sc.boundThread = sc'.boundThread)
    (hT : ∀ t x', st'.getTcb? t = some x' →
      ∃ x, st.getTcb? t = some x ∧ x.schedContextBinding.scId? = x'.schedContextBinding.scId?)
    (h : holdersNameTheirContexts st) : holdersNameTheirContexts st' := by
  intro s sc' t hs hb x' hx
  obtain ⟨sc, hsc, e⟩ := hS s sc' hs
  obtain ⟨x, hx0, ex⟩ := hT t x' hx
  rw [← ex]
  exact h s sc t hsc (by rw [e]; exact hb) x hx0

/-- A step agreeing on every binding code keeps every context named by its holder. -/
theorem holdersNameTheirContexts.of_binding {st st' : SystemState}
    (hA : bindingLinksAgree st st') (h : holdersNameTheirContexts st) :
    holdersNameTheirContexts st' :=
  holdersNameTheirContexts.of_back (fun _ _ hs => hA.getSchedContext?_back hs)
    (fun _ _ hx => by
      obtain ⟨x, hx0, e1, -⟩ := hA.getTcb?_back hx
      exact ⟨x, hx0, schedContextBinding_scId?_of_codes e1.symm⟩) h

/-- A step that writes no scheduling context and keeps every thread's binding. -/
theorem holdersNameTheirContexts.of_maps {st st' : SystemState}
    (hS : ∀ s, st'.getSchedContext? s = st.getSchedContext? s)
    (hT : ∀ t, (st'.getTcb? t).map (·.schedContextBinding) =
      (st.getTcb? t).map (·.schedContextBinding))
    (h : holdersNameTheirContexts st) : holdersNameTheirContexts st' :=
  holdersNameTheirContexts.of_back (fun s sc' hs => ⟨sc', by rw [← hS s]; exact hs, rfl⟩)
    (fun t x' hx => by
      have e := hT t
      rw [hx] at e
      obtain ⟨x, hx0, ex⟩ := Option.map_eq_some_iff.mp e.symm
      exact ⟨x, hx0, by rw [ex]⟩) h

/-- **The donation return keeps every context named by its holder**: the
returned context goes to the recipient, whose binding the return writes to name
it; the holder's binding is cleared, and it held no other context, since its
binding named the returned one; the recipient held none, since the return
accepts only an unbound recipient; every other thread and context is as it was. -/
theorem returnDonatedSchedContext_holdersNameTheirContexts {st st' : SystemState}
    {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {originalOwner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt) (hH : holdersNameTheirContexts st)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    holdersNameTheirContexts st' := by
  obtain ⟨scPre, hScPre, hScPreBound⟩ :=
    returnDonatedSchedContext_ok_implies_sc_bound st st' serverTid scId originalOwner
      newOwner? h
  obtain ⟨scPost, hScPost, hScPostBound⟩ :=
    returnDonatedSchedContext_post_boundThread st st' serverTid scId originalOwner hObjInv
      newOwner? h
  have hNotResOwn : ¬ originalOwner.isReserved :=
    returnDonatedSchedContext_ok_recipient_not_reserved st st' serverTid scId originalOwner
      newOwner? h
  -- A thread the step leaves was a thread before it.
  have back : ∀ y x', st'.getTcb? y = some x' → ∃ t0, st.getTcb? y = some t0 := by
    intro y x' hx'
    obtain ⟨t0, ht0, -⟩ := returnDonatedSchedContext_tcb_rewrite_backward st st' serverTid scId
      originalOwner newOwner? hObjInv h y.toObjId x'
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx')
    exact ⟨t0, (SystemState.getTcb?_eq_some_iff _ _ _).mpr ht0⟩
  -- The holder's binding names the returned context.
  have hSrv : ∀ t0, st.getTcb? serverTid = some t0 → t0.schedContextBinding.scId? = some scId :=
    hH scId scPre serverTid hScPre hScPreBound
  -- The recipient held no binding.
  have hOwn : ∀ t0, st.getTcb? originalOwner = some t0 → t0.schedContextBinding.scId? = none :=
    fun t0 ht0 => by
      rw [returnDonatedSchedContext_ok_recipient_unbound st st' serverTid scId originalOwner
        newOwner? h t0 (by unfold lookupTcb; rw [if_neg hNotResOwn]; exact ht0)]
      rfl
  intro s sc' y hs hb x' hx'
  have hC := returnDonatedSchedContext_tcb_binding_cases st st' serverTid scId originalOwner
    newOwner? hObjInv h y.toObjId x' ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx')
  obtain ⟨t0, ht0⟩ := back y x' hx'
  by_cases hSS : s = scId
  · subst hSS
    rw [hScPost] at hs
    cases hs
    rw [hScPostBound] at hb
    cases hb
    by_cases hKS : originalOwner.toObjId = serverTid.toObjId
    · have e := SeLe4n.ThreadId.toObjId_injective _ _ hKS
      have := hSrv t0 (by rw [← e]; exact ht0)
      rw [hOwn t0 ht0] at this
      cases this
    · rw [hC.2.1 hKS rfl]
      cases newOwner? <;> rfl
  · rw [returnDonatedSchedContext_getSchedContext?_ne st st' serverTid scId s originalOwner hSS
      hObjInv newOwner? h] at hs
    have hy := hH s sc' y hs hb
    by_cases hKS : y.toObjId = serverTid.toObjId
    · have e := SeLe4n.ThreadId.toObjId_injective _ _ hKS
      subst e
      have h1 := hy t0 ht0
      rw [hSrv t0 ht0] at h1
      exact absurd (Option.some.inj h1).symm hSS
    · by_cases hKO : y.toObjId = originalOwner.toObjId
      · have e := SeLe4n.ThreadId.toObjId_injective _ _ hKO
        subst e
        have h1 := hy t0 ht0
        rw [hOwn t0 ht0] at h1
        cases h1
      · obtain ⟨u, hu, hub⟩ := hC.2.2 hKS hKO
        rw [← hub]
        exact hy u ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hu)

/-- ...and so does a cancelled caller's donation return, or its refusal. -/
theorem returnDonationToCancelledCaller_holdersNameTheirContexts (st : SystemState)
    (c : SeLe4n.ThreadId) (t : TCB) (hInv : st.objects.invExt) (hH : holdersNameTheirContexts st) :
    holdersNameTheirContexts (Lifecycle.Suspend.returnDonationToCancelledCaller st c t) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · split
    · rename_i hOk
      obtain ⟨n, -, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
      exact returnDonatedSchedContext_holdersNameTheirContexts hInv hH hPop
    · exact hH
  · exact hH

-- ============================================================================
-- The scheduling point: a register save, run-queue links and the scheduler
-- ============================================================================

theorem bindingLinksAgree.of_agreeOffRunLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffRunLinks st) : bindingLinksAgree st st' :=
  fun o => proj_eq_of_map_eq _ _ schedBindingLinksOf_withoutRunLinks (h o)

theorem preemptCurrentOnCore_bindingLinksAgree (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    bindingLinksAgree st (preemptCurrentOnCore st c incoming) := by
  unfold preemptCurrentOnCore
  split
  · exact fun _ => rfl
  · split
    · exact fun _ => rfl
    · split
      · rename_i prevTcb h _
        have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp h
        refine bindingLinksAgree.trans (fun o => ?_)
          (bindingLinksAgree.of_agreeOffRunLinks
            (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ c _ _))
        rw [SystemState.rewriteObject_objects]
        exact proj_insert_eq _ hInv (by rw [hO]; rfl) o
      · exact fun _ => rfl

theorem switchToThreadOnCore_bindingLinksAgree {st st' : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId} (hInv : st.objects.invExt) (h : switchToThreadOnCore st c tid = .ok st') :
    bindingLinksAgree st st' := fun o => by
  rw [switchToThreadOnCore_ok_objects st st' c tid h]
  exact ((preemptCurrentOnCore_bindingLinksAgree st c tid hInv).trans
    (bindingLinksAgree.of_agreeOffRunLinks
      (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ c tid))) o

theorem handleRescheduleSgiOnCore_bindingLinksAgree {st st' : SystemState} {c : CoreId}
    (hInv : st.objects.invExt) (h : handleRescheduleSgiOnCore st c = .ok st') :
    bindingLinksAgree st st' := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · cases h
  · split at h
    · cases h; exact preemptCurrentOnCore_bindingLinksAgree st c _ hInv
    · cases h; exact fun _ => rfl
  · split at h
    · split at h
      · cases h
        rename_i st₁ hSw
        exact fun o => switchToThreadOnCore_bindingLinksAgree hInv hSw o
      · split at h
        · cases h; exact preemptCurrentOnCore_bindingLinksAgree st c _ hInv
        · cases h; exact fun _ => rfl
    · cases h; exact fun _ => rfl

theorem suspendRescheduleOnCore_bindingLinksAgree {st st' : SystemState}
    {runningCore executingCore : CoreId} {wasCurrent localDeboosted : Bool}
    {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.suspendRescheduleOnCore st runningCore executingCore wasCurrent
      localDeboosted = .ok (st', sgi?)) : bindingLinksAgree st st' := by
  unfold Lifecycle.Suspend.suspendRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (rename_i hH; rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1];
        exact handleRescheduleSgiOnCore_bindingLinksAgree hInv hH)
    | (rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact fun _ => rfl)

-- ============================================================================
-- The IPC cancel
-- ============================================================================

/-- **The head cut keeps every context named by its holder**: the reply stored
over itself and the context's head and origin cleared write no binding, and a
holder's owner code cleared keeps the context its binding names. -/
theorem cutCancelledCallerHead_holdersNameTheirContexts (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) (hH : holdersNameTheirContexts st) :
    holdersNameTheirContexts (Lifecycle.Suspend.cutCancelledCallerHead st tcb) :=
  (Lifecycle.Suspend.cutCancelledCallerHead_closed
    (fun s => s.objects.invExt ∧ holdersNameTheirContexts s)
    (fun s0 s1 _ r scId h0 _ hR hS => by
      have hRo := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
      have F1 := SchedLinkFrame.storeObject h0.1 hS (by rw [hRo]; rfl) (by rw [hRo]; rfl)
        (by rw [hRo]; rfl)
      have hI1 := storeObject_preserves_objects_invExt s0 s1 _ _ h0.1 hS
      have F2 := SchedLinkFrame.updateSchedContext s1 scId
        (fun sc => { sc with scReply := none, donationOrigin := none }) hI1 (fun _ => rfl)
      exact ⟨SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hI1,
        holdersNameTheirContexts.of_binding (F1.trans F2).binding h0.2⟩)
    (fun s0 _ holder ht _ h0 _ hT _ => by
      have hI1 := SystemState.updateTcb_preserves_objects_invExt s0 holder
        (fun t => { t with scBindingOwnerCode := 0 }) h0.1
      refine ⟨by rw [markKeyChangeFrom_objects]; exact hI1, ?_⟩
      refine holdersNameTheirContexts.of_back (fun k sc' hk => ⟨sc', ?_, rfl⟩)
        (fun t x' hx => ?_) h0.2
      · rw [markKeyChangeFrom_getSchedContext?,
          SystemState.updateTcb_getSchedContext? _ _ _ h0.1 k] at hk
        exact hk
      · rw [markKeyChangeFrom_getTcb?] at hx
        by_cases hE : holder.toObjId = t.toObjId
        · have e := SeLe4n.ThreadId.toObjId_injective _ _ hE
          subst e
          rw [SystemState.updateTcb_getTcb?_self _ _ _ h0.1] at hx
          obtain ⟨x, hx0, rfl⟩ := Option.map_eq_some_iff.mp hx
          exact ⟨x, hx0, schedContextBinding_scId?_of_codes rfl⟩
        · rw [SystemState.updateTcb_getTcb?_ne _ _ _ h0.1 _ hE] at hx
          exact ⟨x', hx, rfl⟩)
    st tcb ⟨hInv, hH⟩).2

/-- **The IPC cancel keeps every context named by its holder**: an endpoint or
notification waiter's dequeue and restore write no binding, and a reply-blocked
caller's donation return moves one context to the caller that held none. -/
theorem cancelIpcBlocking_holdersNameTheirContexts (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) (hH : holdersNameTheirContexts st) :
    holdersNameTheirContexts (Lifecycle.Suspend.cancelIpcBlocking st tid tcb) := by
  have endpointArm : ∀ ep, holdersNameTheirContexts (Lifecycle.Suspend.restoreToReadyCancelled
      (removeFromBlockingEndpoint st tid ep) tid) := fun ep => by
    have h1 := holdersNameTheirContexts.of_maps
      (removeFromBlockingEndpoint_getSchedContext?_eq st tid ep hInv)
      (removeFromBlockingEndpoint_binding_frame st tid ep hInv) hH
    have hI1 := removeFromBlockingEndpoint_preserves_objects_invExt st tid ep hInv
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact holdersNameTheirContexts.of_binding (SchedLinkFrame.updateTcb _ tid _ hI1).binding h1
  cases hIp : tcb.ipcState with
  | ready =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st tid tcb = st by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    exact hH
  | blockedOnSend ep =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st tid tcb = _ by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    exact endpointArm ep
  | blockedOnReceive ep =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st tid tcb = _ by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    exact endpointArm ep
  | blockedOnCall ep =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st tid tcb = _ by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    exact endpointArm ep
  | blockedOnNotification n =>
    exact holdersNameTheirContexts.of_binding
      (SchedLinkFrame.notificationCancel st tid tcb n hInv hIp).binding hH
  | blockedOnReply ep rt =>
    rw [cancelIpcBlocking_replyArm_unfold st tid tcb hIp]
    have h1 := returnDonationToCancelledCaller_holdersNameTheirContexts st tid tcb hInv hH
    have hI1 := (FinaliseFrameAny.returnDonationToCancelledCaller st tid tcb hInv).invExt
    exact holdersNameTheirContexts.of_binding (SchedLinkFrame.replyCancelTail _ tid tcb hI1).binding h1

-- ============================================================================
-- The suspend
-- ============================================================================

/-- A thread rewritten in its slot keeping its binding codes. -/
theorem bindingLinksAgree.updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).scBindingScCode = x.scBindingScCode ∧
      (f x).scBindingOwnerCode = x.scBindingOwnerCode) :
    bindingLinksAgree st (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact fun _ => rfl
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hG]
    have hPre := (SystemState.getTcb?_eq_some_iff st t x).mp hG
    obtain ⟨h1, h2⟩ := hf x
    exact proj_insert_eq _ hInv (by rw [hPre]; simp [schedBindingLinksOf, h1, h2])

/-- The suspend's tail after its two writes to the victim: the release removal,
the yield-link cancel and the scheduling point write no binding. -/
private theorem suspendTail_holdersNameTheirContexts {a b : SystemState} {t : SeLe4n.ThreadId}
    {f : TCB → TCB} {r e : CoreId} {w l : Bool} {g : Option (CoreId × Concurrency.SgiKind)}
    (h : Lifecycle.Suspend.suspendRescheduleOnCore
      (cancelYieldTo (Lifecycle.Suspend.releaseRemoveThread (a.updateTcb t f) t) t) r e w l
        = .ok (b, g))
    (P : a.objects.invExt ∧ holdersNameTheirContexts a)
    (hf : ∀ x, (f x).scBindingScCode = x.scBindingScCode ∧
      (f x).scBindingOwnerCode = x.scBindingOwnerCode) :
    holdersNameTheirContexts b := by
  have I5 := SystemState.updateTcb_preserves_objects_invExt a t f P.1
  have H5 := holdersNameTheirContexts.of_binding
    (bindingLinksAgree.updateTcb a t f P.1 hf) P.2
  have I6 := Lifecycle.Suspend.releaseRemoveThread_objects_invExt _ t I5
  have H6 := holdersNameTheirContexts.of_binding (fun o => proj_eq_of_map_eq _ _
    (fun x => by cases x <;> rfl) (Lifecycle.Suspend.releaseRemoveThread_agree _ t o)) H5
  have I7 := SystemState.cancelYieldTo_preserves_objects_invExt _ t I6
  have H7 := holdersNameTheirContexts.of_binding (SchedLinkFrame.of_objectsAgreeOffYield
    (SystemState.cancelYieldTo_objectsAgreeOffYield _ t I6)
    (SystemState.cancelYieldTo_scheduler _ t)).binding H6
  exact holdersNameTheirContexts.of_binding (suspendRescheduleOnCore_bindingLinksAgree I7 h) H7

/-- **A suspend keeps every context named by its holder**: the head cut and the
IPC cancel keep it (`cutCancelledCallerHead_holdersNameTheirContexts`,
`cancelIpcBlocking_holdersNameTheirContexts`), and every later step writes no
binding code and no context's holder. -/
theorem suspendThreadOnCore_holdersNameTheirContexts {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {c : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt) (hH : holdersNameTheirContexts st)
    (hStep : Lifecycle.Suspend.suspendThreadOnCore st vtid c = .ok (st', sgi?)) :
    holdersNameTheirContexts st' := by
  simp only [Lifecycle.Suspend.suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb hT =>
    split at hStep
    case isTrue => exact absurd hStep (by simp)
    case isFalse hA =>
      have hI0 := Lifecycle.Suspend.cutCancelledCallerHead_preserves_objects_invExt st tcb hInv
      have S1 : (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb).objects.invExt ∧
          holdersNameTheirContexts (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) :=
        ⟨Lifecycle.Suspend.cancelIpcKeepingContexts_preserves_objects_invExt st vtid.val tcb hInv,
          cancelIpcBlocking_holdersNameTheirContexts _ vtid.val tcb hI0
            (cutCancelledCallerHead_holdersNameTheirContexts st tcb hInv hH)⟩
      have S2 : (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) serverId c).1
           | none => Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb).objects.invExt ∧
          holdersNameTheirContexts (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) serverId c).1
           | none => Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact S1
        | some serverId =>
          exact ⟨PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt _ _ _ _ S1.1,
            holdersNameTheirContexts.of_binding (SchedLinkFrame.propagatePip _ _ _ _ S1.1).binding
              S1.2⟩
      have S3 : (descheduleAt (match PriorityInheritance.blockingServer st vtid.val with
               | some serverId => (PriorityInheritance.propagatePipChainCrossCore
                   (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) serverId c).1
               | none => Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) vtid.val (placedCoreOf? st vtid.val)).objects.invExt ∧
          holdersNameTheirContexts (descheduleAt (match PriorityInheritance.blockingServer st vtid.val with
               | some serverId => (PriorityInheritance.propagatePipChainCrossCore
                   (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) serverId c).1
               | none => Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) vtid.val (placedCoreOf? st vtid.val)) :=
        ⟨by
          unfold descheduleAt
          cases placedCoreOf? st vtid.val with
          | none => exact S2.1
          | some k => exact removeRunnableOnCore_objects_invExt _ _ k S2.1,
        holdersNameTheirContexts.of_binding (SchedLinkFrame.descheduleAt _ _ _).binding S2.2⟩
      have S4 : (Lifecycle.Suspend.clearPendingStateValid
            (descheduleAt (match PriorityInheritance.blockingServer st vtid.val with
               | some serverId => (PriorityInheritance.propagatePipChainCrossCore
                   (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) serverId c).1
               | none => Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) vtid.val (placedCoreOf? st vtid.val)) vtid).objects.invExt ∧
          holdersNameTheirContexts (Lifecycle.Suspend.clearPendingStateValid
            (descheduleAt (match PriorityInheritance.blockingServer st vtid.val with
               | some serverId => (PriorityInheritance.propagatePipChainCrossCore
                   (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) serverId c).1
               | none => Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) vtid.val (placedCoreOf? st vtid.val)) vtid) := by
        unfold Lifecycle.Suspend.clearPendingStateValid Lifecycle.Suspend.clearPendingState
        refine ⟨SystemState.updateTcb_preserves_objects_invExt _ _ _ S3.1,
          holdersNameTheirContexts.of_binding (bindingLinksAgree.updateTcb _ _ _ S3.1 ?_) S3.2⟩
        intro x; exact ⟨rfl, rfl⟩
      exact suspendTail_holdersNameTheirContexts hStep S4 fun _ => ⟨rfl, rfl⟩

end SeLe4n.Kernel
