-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.SyscallDispatch

/-! # The capability-only arms' writes keep the lenders' flow

WS-SX SX8.  The primitives the capability-only table (`dispatchCapabilityOnly`)
runs that write no reply object and no context's stack head: the reply-cap
mint, the service revoke, the handler issue, the notification binding and the
thread setters.  Each is a `LendersFrame` built from its `chainObjectsKept`
twin (ruling (af)) and the records' own frame for the store's invariant.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace chainObjectsKept

theorem mintReplyCapWithCdt {src dst : CSpaceAddr} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.mintReplyCapWithCdt src dst st = .ok ((), st')) :
    chainObjectsKept st st' := by
  unfold _root_.SeLe4n.Kernel.mintReplyCapWithCdt at hStep
  split at hStep
  · contradiction
  · rename_i stM hMint
    cases hStep
    have K : chainObjectsKept st stM ∧ stM.objects.invExt := by
      unfold mintReplyCap at hMint
      split at hMint
      · contradiction
      · rename_i parent stMid hLk
        have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
        subst hMid
        split at hMint
        · dsimp only [] at hMint
          split at hMint
          · exact ⟨cspaceInsertSlot hInv hMint, (RecordsFrame.cspaceInsertSlot hInv hMint).invExt⟩
          · contradiction
        · contradiction
    exact K.1.trans (cdtAddChild stM src dst .mint K.2)

theorem revokeService {sid : ServiceId} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.revokeService sid st = .ok ((), st')) :
    chainObjectsKept st st' := by
  obtain ⟨ep, -, -, rfl⟩ := revokeService_ok h
  exact insert_other hInv (fun _ e => by cases e) (fun _ e => by cases e)

theorem bindNotification {st st' : SystemState} {nid : SeLe4n.ObjId} {tcbId : SeLe4n.ThreadId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.bindNotification nid tcbId st = .ok ((), st')) :
    chainObjectsKept st st' := by
  unfold _root_.SeLe4n.Kernel.bindNotification at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i st1 hStore1
          split at h
          · cases h
          · rename_i st2 hStore2
            cases h
            exact (storeObject_other hInv hStore1 (fun _ e => by cases e) (fun _ e => by cases e)).trans
              (storeObject_other (storeObject_preserves_objects_invExt _ _ _ _ hInv hStore1) hStore2
                (fun _ e => by cases e) (fun _ e => by cases e))
  · split at h <;> cases h

theorem unbindNotification {st st' : SystemState} {tcbId : SeLe4n.ThreadId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.unbindNotification tcbId st = .ok ((), st')) :
    chainObjectsKept st st' := by
  unfold _root_.SeLe4n.Kernel.unbindNotification at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i st1 hStore1
        have K1 := storeObject_other hInv hStore1 (fun _ e => by cases e) (fun _ e => by cases e)
        have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hStore1
        split at h
        · split at h
          · cases h
          · rename_i st2 hStore2
            cases h
            exact K1.trans (storeObject_other hI1 hStore2 (fun _ e => by cases e)
              (fun _ e => by cases e))
        · cases h; exact K1

end chainObjectsKept

namespace LendersFrame

theorem runRequeueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    LendersFrame st (st.runRequeueOnCore c t p) :=
  of_kept (chainObjectsKept.of_objectsAgreeOffRunLinks
      (SystemState.runRequeueOnCore_objectsAgreeOffRunLinks st c t p))
    (RecordsFrame.runRequeueOnCore st c t p hInv)

theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) : LendersFrame st (st.updateTcb t f) :=
  ⟨(chainObjectsKept.updateTcb st t f hInv).linksShrink,
   SystemState.updateTcb_preserves_objects_invExt st t f hInv⟩

theorem repropagateFromWaiter (st : SystemState) (t : SeLe4n.ThreadId) (ec : CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    LendersFrame st (PriorityInheritance.repropagateFromWaiter st t ec fuel) :=
  PriorityInheritance.repropagateFromWaiter_preserves (LendersFrame st) st t ec fuel
    (fun s _ => propagatePipChainCrossCore st s ec fuel hInv) (refl hInv)

theorem priorityRescheduleOnCore {st st' : SystemState} {running? : Option CoreId} {ec : CoreId}
    {sp : Bool} {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCore st running? ec sp =
      .ok (st', sgi?)) : LendersFrame st st' := by
  rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases _ _ _ _ _ _ h
    with hEq | hH
  · subst hEq; exact refl hInv
  · exact handleRescheduleSgiOnCore hInv hH

/-- The priority ops' shared effect: the source write, the re-bucket, the key
hook, the chain re-walk and the preemption seam. -/
theorem applyPriorityChangeOnCore {st st' : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    {p : SeLe4n.Priority} {ec : CoreId} {b : Bool} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.applyPriorityChangeOnCore st t tcb p ec b =
      .ok (st', sgi?)) : LendersFrame st st' := by
  unfold SchedContext.PriorityManagement.applyPriorityChangeOnCore at h
  have F1 : LendersFrame st (SchedContext.PriorityManagement.updatePrioritySource st t tcb p) := by
    unfold SchedContext.PriorityManagement.updatePrioritySource
    exact updateTcb _ t _ hInv
  have F2 := F1.andThen fun h => (show LendersFrame _
      (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore _ t p (determineTargetCore st t)) by
    unfold SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
    split
    · exact runRequeueOnCore _ _ _ _ h
    · exact refl h)
  have F3 := F2.andThen fun h => markKeyChangeFor _ t (effectiveSchedParams st tcb) h
  have F4 := F3.andThen fun h => repropagateFromWaiter _ t ec st.objects.size h
  exact F4.andThen fun h' => priorityRescheduleOnCore h' h

theorem setPriorityOnCore {st st' : SystemState} {vCaller vTarget : SeLe4n.ValidThreadId}
    {p : SeLe4n.Priority} {ec : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.setPriorityOnCore st vCaller vTarget p ec =
      .ok (st', sgi?)) : LendersFrame st st' := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact applyPriorityChangeOnCore hInv h
      · cases h
  · cases h

theorem setMCPriorityOnCore {st st' : SystemState} {vCaller vTarget : SeLe4n.ValidThreadId}
    {p : SeLe4n.Priority} {ec : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.setMCPriorityOnCore st vCaller vTarget p ec =
      .ok (st', sgi?)) : LendersFrame st st' := by
  unfold SchedContext.PriorityManagement.setMCPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · rename_i targetTcb hTarget _
        dsimp only at h
        have hS := rewriteObject_tcb hTarget { targetTcb with maxControlledPriority := p } rfl
          (SystemState.rewriteAdmissible_tcb hTarget _) hInv
        split at h
        · exact hS.andThen fun h' => applyPriorityChangeOnCore h' h
        · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hS
      · cases h
  · cases h

end LendersFrame

namespace LendersFrame

theorem markReschedulePendingOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    LendersFrame st (st.markReschedulePendingOnCore c) := withScheduler _ _ hInv

theorem markCandidacyGainFor (st : SystemState) (t : SeLe4n.ThreadId) (b : Bool)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.markCandidacyGainFor st t b) :=
  of_kept (chainObjectsKept.of_objects_eq (markCandidacyGainFor_objects st t b))
    (RecordsFrame.markCandidacyGainFor st t b hInv)

theorem runDescheduleOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : LendersFrame st (st.runDescheduleOnCore c t) :=
  of_kept (chainObjectsKept.of_objectsAgreeOffRunLinks
      (SystemState.runDescheduleOnCore_objectsAgreeOffRunLinks st c t))
    (RecordsFrame.runDescheduleOnCore st c t hInv)

theorem runEnqueueHeadOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    LendersFrame st (st.runEnqueueHeadOnCore c t p) :=
  of_kept (chainObjectsKept.of_objectsAgreeOffRunLinks
      (SystemState.runEnqueueHeadOnCore_objectsAgreeOffRunLinks st c t p))
    (RecordsFrame.runEnqueueHeadOnCore st c t p hInv)

theorem purgeReplenishment (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : LendersFrame st (SchedContextOps.purgeReplenishment st s) :=
  of_views (contextStackViewsAgree_of_objectsAgreeOffReleaseLinks
      (SchedContextOps.purgeReplenishment_agree st s))
    (RecordsFrame.purgeReplenishment st s hInv).invExt

theorem setConsumed (st : SystemState) (s : SeLe4n.SchedContextId) (t : SeLe4n.ThreadId)
    {callOnly : Bool} (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.setConsumed st s t callOnly) := by
  unfold _root_.SeLe4n.Kernel.setConsumed
  split
  · refine (updateSchedContext st s _ ?_ hInv).andThen fun h => updateTcb _ t _ h
    intro x; rfl
  · exact refl hInv

theorem schedContextConsumedOnCore {s : SeLe4n.SchedContextId} {c : CoreId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.schedContextConsumedOnCore s c st = .ok st') : LendersFrame st st' := by
  obtain ⟨caller, -, rfl⟩ := schedContextConsumedOnCore_ok h
  exact setConsumed st s caller hInv

theorem setYieldLink (st : SystemState) (s : SeLe4n.SchedContextId) (caller : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : LendersFrame st (_root_.SeLe4n.Kernel.setYieldLink st s caller) :=
  by refine (updateSchedContext st s _ ?_ hInv).andThen fun h => updateTcb _ caller _ h
     intro x; rfl

theorem yieldToRequeue (st : SystemState) (home : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    LendersFrame st (SchedContextOps.yieldToRequeue st home t p) := by
  unfold SchedContextOps.yieldToRequeue
  split
  · exact refl hInv
  · exact ((runRemoveOnCore st home t hInv).andThen fun h => runEnqueueHeadOnCore _ home t p h).andThen
      fun h => markReschedulePendingOnCore _ home h

theorem yieldToLink (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (caller t : SeLe4n.ThreadId) (pC pT : SeLe4n.Priority) (hInv : st.objects.invExt) :
    LendersFrame st (SchedContextOps.yieldToLink st c s caller t pC pT) := by
  unfold SchedContextOps.yieldToLink SchedContextOps.yieldToLinkPrefix
  refine ((((((setYieldLink st s caller hInv).andThen fun h => runRemoveOnCore _ c t h).andThen
    fun h => runDescheduleOnCore _ c caller h).andThen fun h => runEnqueueHeadOnCore _ c caller pC h).andThen
    fun h => runEnqueueHeadOnCore _ c t pT h).andThen fun h => ?_)
  exact handleRescheduleSgiOnCore h (handleRescheduleSgiOnCore_eq_state _ c)

theorem cancelYieldFrom (st : SystemState) (s : SeLe4n.SchedContextId) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.cancelYieldFrom st s) := by
  unfold _root_.SeLe4n.Kernel.cancelYieldFrom
  split
  · split
    · exact refl hInv
    · refine (updateSchedContext st s _ ?_ hInv).andThen fun h => updateTcb _ _ _ h
      intro x; rfl
  · exact refl hInv

theorem completeYieldFrom (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : LendersFrame st (_root_.SeLe4n.Kernel.completeYieldFrom st s) := by
  unfold _root_.SeLe4n.Kernel.completeYieldFrom
  split
  · split
    · exact refl hInv
    · exact (setConsumed st s _ hInv).andThen fun h => cancelYieldFrom _ s h
  · exact refl hInv

theorem schedContextYieldToOnCore {s : SeLe4n.SchedContextId} {c : CoreId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextYieldToOnCore s c st = .ok st') : LendersFrame st st' := by
  obtain ⟨caller, -, t, -, -, -, -, -, -, -, -, -, -, rfl⟩ :=
    SchedContextOps.schedContextYieldToOnCore_ok h
  unfold SchedContextOps.yieldToBound
  dsimp only
  have F := (completeYieldFrom st s hInv).andThen fun h =>
    releasePlace _ (determineTargetCore (_root_.SeLe4n.Kernel.completeYieldFrom st s) t) s h
  refine F.andThen fun hI => ?_
  generalize (_root_.SeLe4n.Kernel.completeYieldFrom st s).releasePlace
    (determineTargetCore (_root_.SeLe4n.Kernel.completeYieldFrom st s) t) s = st2 at hI ⊢
  split
  · exact setConsumed _ _ _ hI
  · split
    · exact setConsumed _ _ _ hI
    · split
      · exact setConsumed _ _ _ hI
      · split
        · split
          · exact (yieldToRequeue _ _ _ _ hI).andThen fun h => setConsumed _ _ _ h
          · exact yieldToLink _ _ _ _ _ _ _ hI
        · exact setConsumed _ _ _ hI

theorem schedContextBind {vScId : SeLe4n.ValidObjId} {vTid : SeLe4n.ValidThreadId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextBind vScId vTid st = .ok ((), st')) : LendersFrame st st' := by
  rw [(SchedContextOps.schedContextBind_ok_donate h).2]
  exact schedContextBindPerform st vScId vTid hInv

theorem configureResumeBound (st : SystemState) (t : SeLe4n.ThreadId) (sc : SchedContext)
    (hInv : st.objects.invExt) : LendersFrame st (SchedContextOps.configureResumeBound st t sc) := by
  unfold SchedContextOps.configureResumeBound
  dsimp only
  split
  · split
    · exact refl hInv
    · exact runRemoveOnCore _ _ _ hInv
  · split
    · split
      · exact (runEnqueueOnCore _ _ _ _ hInv).andThen fun h => markReschedulePendingOnCore _ _ h
      · split
        · exact markReschedulePendingOnCore _ _ hInv
        · exact refl hInv
    · exact refl hInv

end LendersFrame

namespace LendersFrame

/-- Two frames that need only the store's invariant, chained. -/
theorem chain {a b c : SystemState} (F : a.objects.invExt → LendersFrame a b)
    (G : b.objects.invExt → LendersFrame b c) : a.objects.invExt → LendersFrame a c :=
  fun h => (F h).andThen G

/-- A context rewritten in place keeping its stack head. -/
theorem rewriteObject_sc {st : SystemState} {k : SeLe4n.ObjId} {sc sc' : SchedContext}
    (hOld : st.objects[k]? = some (.schedContext sc)) (hR : sc'.scReply = sc.scReply)
    (hA : st.rewriteAdmissible k (.schedContext sc')) (hInv : st.objects.invExt) :
    LendersFrame st (st.rewriteObject k (.schedContext sc') hA) :=
  of_views (contextStackViewsAgree_insert hInv (by rw [hOld]; exact hR) (by rw [hOld]; rfl)
      (by rw [hOld]; rfl))
    (SystemState.rewriteObject_preserves_objects_invExt st k _ hA hInv)

theorem schedContextUnbindQueueStage (st : SystemState) (home : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (w : Bool) (hInv : st.objects.invExt) :
    LendersFrame st (SchedContextOps.schedContextUnbindQueueStage st home t p w) := by
  unfold SchedContextOps.schedContextUnbindQueueStage
  split
  · exact runRequeueOnCore _ _ _ _ hInv
  · split
    · exact (runEnqueueOnCore _ _ _ _ hInv).andThen fun h => markReschedulePendingOnCore _ _ h
    · exact refl hInv

/-- The unbind clears the context's bound thread and the thread's binding in
place, re-buckets the thread, purges the replenishment and runs the key hooks;
the context keeps its stack head. -/
theorem schedContextUnbind {vScId : SeLe4n.ValidObjId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) : LendersFrame st st' := by
  unfold SchedContextOps.schedContextUnbind at hStep
  split at hStep
  · rename_i sc hSc _
    have hRaw := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
    split at hStep
    · contradiction
    · split at hStep
      · dsimp only [] at hStep
        cases hStep
        refine chain ?_ (fun h => markKeyChangeFor _ _ _ h) hInv
        refine chain ?_ (fun h => markCandidacyGainFor _ _ _ h)
        refine chain ?_ (fun h => purgeReplenishment _ _ h)
        refine chain ?_ (fun h => schedContextUnbindQueueStage _ _ _ _ _ h)
        refine chain (chain (fun h => withScheduler _ _ h) fun h => rewriteObject_sc
          (by exact hRaw) (by rfl) _ h) fun h => updateTcb _ _ _ h
      · cases hStep
        exact chain (fun h => rewriteObject_sc (by exact hRaw) (by rfl) _ h) (fun h => purgeReplenishment _ _ h) hInv
  · cases hStep

theorem schedContextUnbindOnCore {vScId : SeLe4n.ValidObjId} {ec : CoreId}
    {st st' : SystemState} {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextUnbindOnCore vScId ec st = .ok (st', sgi?)) :
    LendersFrame st st' :=
  schedContextUnbind hInv (SchedContextOps.schedContextUnbindOnCore_ok h).2.1

end LendersFrame

namespace LendersFrame

/-- A notification rewritten in place: no stack view moves. -/
theorem insert_notification {st : SystemState} {k : SeLe4n.ObjId} {n n' : Notification}
    (hOld : st.objects[k]? = some (.notification n)) (hInv : st.objects.invExt) :
    LendersFrame st { st with objects := st.objects.insert k (.notification n') } :=
  of_views (contextStackViewsAgree_insert hInv (by rw [hOld]; rfl) (by rw [hOld]; rfl)
      (by rw [hOld]; rfl))
    (RHTable_insert_preserves_invExt _ _ _ hInv)

/-- **A context's head cleared or kept**: the links shrink, since a head after
the write is the head the context had. -/
theorem updateSchedContext_clearHead (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext)
    (hf : ∀ x, (f x).scReply = none ∨ (f x).scReply = x.scReply) (hInv : st.objects.invExt) :
    LendersFrame st (st.updateSchedContext scId f) := by
  unfold SystemState.updateSchedContext
  split
  · rename_i sc h _
    have hRaw := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp h
    have hIns : (st.objects.insert scId.toObjId (.schedContext (f sc)))[scId.toObjId]? =
        some (.schedContext (f sc)) := by
      simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
    refine ⟨contextStackLinksShrink_of_slot scId.toObjId (fun x hx => ?_) (fun s r hk hr => ?_)
      (fun x hx => ?_) (fun l hl => ?_),
      SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hInv⟩
    · show (st.objects.insert scId.toObjId _)[x]? = _
      simp only [RHTable_getElem?_eq_get?]
      exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb).symm) hInv
    · change objStackHead (st.objects.insert scId.toObjId _)[scId.toObjId]? = some r at hr
      rw [hIns] at hr
      have hs : s = scId := SeLe4n.SchedContextId.toObjId_injective _ _ hk
      subst hs
      refine .head ?_
      rw [contextStackHead_eq_obj, hRaw]
      rcases hf sc with e | e <;> simp only [objStackHead, e] at hr ⊢
      · cases hr
      · exact hr
    · change objStackPrev (st.objects.insert scId.toObjId _)[scId.toObjId]? = some x at hx
      rw [hIns] at hx; cases hx
    · change objStackCaller (st.objects.insert scId.toObjId _)[scId.toObjId]? = some l at hl
      rw [hIns] at hl; cases hl
  · exact refl hInv

/-- **A context's reply-stack unlink** (seL4-MCS `schedContext_unbindReply`):
the head frame's upward link cleared, then the context's head. -/
theorem schedContextUnbindReply (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.schedContextUnbindReply st x) :=
  of_shrink (schedContextUnbindReply_linksShrink st x hInv)
    (RecordsFrame.schedContextUnbindReply st x hInv).invExt

theorem unbindSchedContextNotification (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.unbindSchedContextNotification st s) := by
  rcases unbindSchedContextNotification_shape st s hInv with h | ⟨sc, hS, h | ⟨n, ntfn, h1, h⟩⟩
  · rw [h]; exact refl hInv
  · rw [h]; exact updateSchedContext st s _ (fun _ => rfl) hInv
  · rw [h]
    exact (updateSchedContext st s (fun c => { c with notificationCode := 0 }) (fun _ => rfl)
      hInv).andThen fun h' => insert_notification h1 h'

theorem schedContextBindNotification {vScId : SeLe4n.ValidObjId}
    {n : SeLe4n.ObjId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.schedContextBindNotification vScId n st = .ok ((), st')) :
    LendersFrame st st' := by
  obtain ⟨hA, rfl⟩ := schedContextBindNotification_ok_admitted h
  obtain ⟨_, _, hS, -, hN, -⟩ := schedContextBindNotificationAdmitted_facts hA
  obtain ⟨h1, hEq⟩ := bindNotificationSchedLink_eq hS hN hInv
  rw [hEq]
  exact (updateSchedContext st (SeLe4n.SchedContextId.ofObjId vScId.val)
    (fun sc => { sc with notificationCode := n.val + 1 }) (fun _ => rfl) hInv).andThen
    fun h' => insert_notification h1 h'

/-- **`SchedContext_Unbind`**: the thread unbind, the notification unbind and
the reply-stack unlink. -/
theorem schedContextUnbindAllOnCore {vScId : SeLe4n.ValidObjId}
    {ec : CoreId} {st st' : SystemState}
    {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextUnbindAllOnCore vScId ec st = .ok (st', sgi?)) :
    LendersFrame st st' := by
  obtain ⟨stU, hU | ⟨-, hU, -⟩, rfl⟩ := SchedContextOps.schedContextUnbindAllOnCore_ok h
  · obtain ⟨rfl, -⟩ := hU
    exact (unbindSchedContextNotification _ (SeLe4n.SchedContextId.ofObjId vScId.val) hInv).andThen
      fun h' => schedContextUnbindReply _ _ h'
  · exact ((schedContextUnbindOnCore hInv hU).andThen fun h' =>
      unbindSchedContextNotification _ (SeLe4n.SchedContextId.ofObjId vScId.val) h').andThen
      fun h' => schedContextUnbindReply _ _ h'

theorem schedContextUnbindThreadObjectOnCore {vScId : SeLe4n.ValidObjId}
    {tid : SeLe4n.ThreadId} {ec : CoreId} {st st' : SystemState}
    {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextUnbindThreadObjectOnCore vScId tid ec st = .ok (st', sgi?)) :
    LendersFrame st st' :=
  schedContextUnbindOnCore hInv (SchedContextOps.schedContextUnbindThreadObjectOnCore_ok h)

theorem schedContextUnbindNotificationObject {vScId : SeLe4n.ValidObjId}
    {n : SeLe4n.ObjId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextUnbindNotificationObject vScId n st = .ok ((), st')) :
    LendersFrame st st' := by
  obtain ⟨-, rfl⟩ := SchedContextOps.schedContextUnbindNotificationObject_ok h
  exact unbindSchedContextNotification _ _ hInv

end LendersFrame

theorem configuredSchedContext_scReply (budget period : Nat) (extraRefills badge flags : UInt64)
    (timer : Nat) (keep : Bool) (sc : SchedContext) :
    (SchedContextOps.configuredSchedContext budget period extraRefills badge flags timer keep sc).scReply =
      sc.scReply := by
  unfold SchedContextOps.configuredSchedContext
  cases keep
  · exact (SchedContext.fields_of_refillsErased (SchedContext.refillNew_refillsErased _ _ _)).2.2.2.2.2.2.2.1
  · exact (SchedContext.fields_of_refillsErased
      (SchedContext.refillUpdate_refillsErased _ _ _ _)).2.2.2.2.2.2.2.1

namespace LendersFrame

/-- A context stored with the head its slot already had. -/
theorem storeSchedContext_keepHead {st st' : SystemState} {s : SeLe4n.SchedContextId}
    {sc' : SchedContext} (hInv : st.objects.invExt)
    (h : storeObject s.toObjId (.schedContext sc') st = .ok ((), st'))
    (hH : contextStackHead st s = sc'.scReply) : LendersFrame st st' :=
  ⟨contextStackLinksShrink_storeSchedContext hInv h (fun _ hr => .head (hH.trans hr)),
   storeObject_preserves_objects_invExt _ _ _ _ hInv h⟩

/-- The configure purges the context's replenishment, stores the reconfigured
context (its head kept) over the old one, and runs the placement, the candidacy
hook and the resume tail. -/
theorem schedContextConfigure {vScId : SeLe4n.ValidObjId}
    {budget period : Nat} {extraRefills badge flags : UInt64} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextConfigure vScId budget period extraRefills badge flags st =
      .ok ((), st')) : LendersFrame st st' := by
  cases hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none =>
    unfold SchedContextOps.schedContextConfigure at h
    split at h
    · exact absurd h (by simp)
    · rw [hSc] at h; exact absurd h (by simp)
  | some sc =>
    have hScRaw := (SystemState.getSchedContext?_eq_some_iff st
      (SchedContextId.ofObjId vScId.val) sc).mp hSc
    unfold SchedContextOps.schedContextConfigure at h
    split at h
    · exact absurd h (by simp)
    · rw [hSc] at h
      dsimp only at h
      split at h
      · split at h
        · exact absurd h (by simp)
        · rename_i stStored hStore
          have V := contextStackViewsAgree_of_objectsAgreeOffReleaseLinks
            (SchedContextOps.purgeReplenishment_agree st ⟨vScId.val.toNat⟩)
          have Fp := purgeReplenishment st ⟨vScId.val.toNat⟩ hInv
          have F1 : LendersFrame st stStored := Fp.andThen fun hI =>
            storeSchedContext_keepHead (s := SeLe4n.SchedContextId.ofObjId vScId.val) hI hStore (by
              rw [configuredSchedContext_scReply]
              refine (V.head _).trans ?_
              rw [contextStackHead_eq_obj]
              exact congrArg objStackHead hScRaw)
          split at h
          · rw [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2]; exact F1
          · split at h
            · rw [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]
              exact ((F1.andThen fun h => releasePlace _ _ _ h).andThen fun h =>
                markCandidacyGainFor _ _ _ h).andThen fun h => configureResumeBound _ _ _ h
            · rw [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]; exact F1.andThen fun h => releasePlace _ _ _ h
      · exact absurd h (by simp)

end LendersFrame

namespace LendersFrame

theorem migrateSchedContextReplenishment (st : SystemState) (scId : SeLe4n.SchedContextId)
    (fromCore toCore : CoreId) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.migrateSchedContextReplenishment st scId fromCore toCore) :=
  of_views (contextStackViewsAgree_of_objectsAgreeOffReleaseLinks
      (migrateSchedContextReplenishment_agree st scId fromCore toCore))
    (RecordsFrame.migrateSchedContextReplenishment st scId fromCore toCore hInv).invExt

theorem vacateForAffinityChange (st : SystemState) (t : SeLe4n.ThreadId) (o n : CoreId)
    (hInv : st.objects.invExt) : LendersFrame st (_root_.SeLe4n.Kernel.vacateForAffinityChange st t o n) := by
  unfold _root_.SeLe4n.Kernel.vacateForAffinityChange
  split
  · exact withScheduler _ _ hInv
  · exact refl hInv

theorem migrateRunQueueOnAffinityChange (st : SystemState) (t : SeLe4n.ThreadId) (o n : CoreId)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.migrateRunQueueOnAffinityChange st t o n) := by
  unfold _root_.SeLe4n.Kernel.migrateRunQueueOnAffinityChange
  split
  · exact refl hInv
  · split
    · exact refl hInv
    · split
      · exact ((runRemoveOnCore st o t hInv).andThen fun h => runEnqueueAdmitted _ n t _ h).andThen
          fun h => withScheduler _ _ h
      · exact refl hInv

theorem requeueVacatedOnNewHome (st : SystemState) (t : SeLe4n.ThreadId) (n : CoreId) (v : Bool)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.requeueVacatedOnNewHome st t n v) := by
  unfold _root_.SeLe4n.Kernel.requeueVacatedOnNewHome
  split
  · split
    · exact (runEnqueueOnCore st n t _ hInv).andThen fun h => withScheduler _ _ h
    · exact refl hInv
  · exact refl hInv

theorem setThreadCpuAffinityWithMigration {st st' : SystemState} {t : SeLe4n.ThreadId}
    {affinity : Option CoreId} {ec : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.setThreadCpuAffinityWithMigration st t affinity ec = .ok (st', sgi?)) :
    LendersFrame st st' := by
  obtain ⟨tcb, stSet, -, -, -, -, hSet, rfl, -⟩ := setThreadCpuAffinityWithMigration_ok_shape h
  have F0 := vacateForAffinityChange st t (determineTargetCore st t)
    (affinity.getD Concurrency.bootCoreId) hInv
  have F1 : LendersFrame st stSet := by
    unfold setThreadCpuAffinity at hSet
    split at hSet
    · rename_i x hT _
      rw [Except.ok.injEq] at hSet; subst hSet
      refine F0.andThen fun h => rewriteObject_tcb hT _ ?_ _ h
      rfl
    · cases hSet
  refine chain (chain (fun _ => ?_) (fun h => migrateRunQueueOnAffinityChange _ _ _ _ h))
    (fun h => requeueVacatedOnNewHome _ _ _ _ h) hInv
  split
  · exact F1.andThen fun h => migrateSchedContextReplenishment _ _ _ _ h
  · exact F1

theorem setThreadCpuAffinityOnCore {st st' : SystemState} {vTarget : SeLe4n.ValidThreadId}
    {affinity : Option CoreId} {ec : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.setThreadCpuAffinityOnCore st vTarget affinity ec = .ok (st', sgi?)) :
    LendersFrame st st' :=
  setThreadCpuAffinityWithMigration hInv h

theorem schedControlConfigure {core : CoreId} {vScId : SeLe4n.ValidObjId}
    {budget period : Nat} {extraRefills badge flags : UInt64} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : SchedContextOps.schedControlConfigure core vScId budget period extraRefills badge flags
      st = .ok ((), st')) : LendersFrame st st' := by
  rcases SchedContextOps.schedControlConfigure_ok_cases h with h | ⟨_, _, _, _, -, -, -, hM, h⟩
  · exact schedContextConfigure hInv h
  · exact (setThreadCpuAffinityWithMigration hInv hM).andThen fun h' => schedContextConfigure h' h

end LendersFrame

namespace chainObjectsKept

/-- **A write of VSpace roots alone** rewrites no reply object and no context. -/
theorem of_vspaceRootOnlyWrite {st st' : SystemState} (h : vspaceRootOnlyWrite st st') :
    chainObjectsKept st st' := by
  refine ⟨fun x r hx => ?_, fun x sc hx => ?_⟩ <;> rcases h x with e | ⟨-, r', hr'⟩
  all_goals first
    | (rw [← e]; exact hx)
    | (rw [hr'] at hx; cases hx)

end chainObjectsKept

namespace LendersFrame

/-- A store of an object of neither chain kind. -/
theorem storeObject_other {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (h : storeObject k o st = .ok ((), st'))
    (hRp : ∀ r, o ≠ .reply r) (hSc : ∀ sc, o ≠ .schedContext sc) : LendersFrame st st' :=
  ⟨(chainObjectsKept.storeObject_other hInv h hRp hSc).linksShrink,
   storeObject_preserves_objects_invExt _ _ _ _ hInv h⟩

theorem of_vspaceRootOnlyWrite {st st' : SystemState} (h : vspaceRootOnlyWrite st st')
    (hI : st'.objects.invExt) : LendersFrame st st' :=
  ⟨(chainObjectsKept.of_vspaceRootOnlyWrite h).linksShrink, hI⟩

theorem vspaceUnifyInstructionPage {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : Architecture.vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    LendersFrame st st' :=
  of_kept (chainObjectsKept.of_objects_eq (Architecture.vspaceUnifyInstructionPage_frame h).1)
    (RecordsFrame.vspaceUnifyInstructionPage hInv h)

theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast {ec : CoreId}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) : LendersFrame st st' :=
  have hF := vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame ec asid vaddr st st' hInv h
  of_vspaceRootOnlyWrite hF.2.1 hF.1

theorem vspaceMapFromFrameCap {tid : SeLe4n.ThreadId} {ec : CoreId}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.vspaceMapFromFrameCap tid ec args st = .ok ((), st')) :
    LendersFrame st st' := by
  obtain ⟨_, _, _, st1, _, _, _, _, _, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid ec args st st' h
  obtain ⟨cn, _, -, -, hS⟩ := cspaceRecordFrameMapping_ok_decompose _ _ st2 st' hRec
  have hF := vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame ec _ _ _ _ st st1 hInv hMap
  have F1 := of_vspaceRootOnlyWrite hF.2.1 hF.1
  obtain ⟨f, rootId, root, stR, -, -, -, h1, h2⟩ := tagFrameMapping_ok _ _ _ st1 st2 epoch hT
  have F2 := F1.andThen fun hI => storeObject_other hI h1 (fun _ e => by cases e) (fun _ e => by cases e)
  have F3 := F2.andThen fun hI => storeObject_other hI h2 (fun _ e => by cases e) (fun _ e => by cases e)
  exact F3.andThen fun hI => storeObject_other hI hS (fun _ e => by cases e) (fun _ e => by cases e)

theorem vspaceMapOrRemapFromFrameCap {tid : SeLe4n.ThreadId} {ec : CoreId}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.vspaceMapOrRemapFromFrameCap tid ec args st = .ok ((), st')) :
    LendersFrame st st' :=
  vspaceMapOrRemapFromFrameCap_closed (fun a b => a.objects.invExt → LendersFrame a b)
    (fun _ _ h hI => vspaceMapFromFrameCap hI h)
    (fun _ _ h hI => vspaceUnmapPageWithShootdownAndIcacheBroadcast hI h)
    (fun _ _ _ h₁ h₂ hI => (h₁ hI).andThen h₂) h hInv

theorem vspaceUnmapFrameCap {ec : CoreId} {addr : CSpaceAddr} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.vspaceUnmapFrameCap ec addr st = .ok ((), st')) :
    LendersFrame st st' := by
  obtain ⟨st1, hU, hC⟩ := vspaceUnmapFrameCap_cases h
  obtain ⟨cn, _, -, -, hS⟩ := cspaceClearFrameMapping_ok_decompose _ st1 st' hC
  obtain ⟨hI1, hV, -⟩ := unmapLivePages_ok_frame ec _ st st1 hInv hU
  exact (of_vspaceRootOnlyWrite hV hI1).andThen fun hI =>
    storeObject_other hI hS (fun _ e => by cases e) (fun _ e => by cases e)

theorem pageTableMap {tableId rootId : SeLe4n.ObjId} {vaddr : SeLe4n.VAddr} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) : LendersFrame st st' := by
  obtain ⟨table, root, level, st1, -, -, -, -, -, -, hS1, hS2⟩ :=
    Architecture.pageTableMap_ok tableId rootId vaddr st st' h
  have F1 := storeObject_other hInv hS1 (fun _ e => by cases e) (fun _ e => by cases e)
  have F2 : ∀ ws, LendersFrame st1 (Architecture.recordPhysicalWrites st1 ws) := fun _ =>
    ⟨(chainObjectsKept.of_objects_eq (st := st1) (st' := Architecture.recordPhysicalWrites st1 _) rfl).linksShrink, F1.invExt⟩
  exact (F1.andThen fun _ => F2 _).andThen fun hI =>
    storeObject_other hI hS2 (fun _ e => by cases e) (fun _ e => by cases e)

end LendersFrame

namespace LendersFrame

theorem pageTableUnmap {tableId : SeLe4n.ObjId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : Architecture.pageTableUnmap tableId st = .ok ((), st')) : LendersFrame st st' := by
  unfold Architecture.pageTableUnmap at h
  cases hT : st.getPageTable? tableId with
  | none => rw [hT] at h; cases h
  | some table =>
    have Ft : ∀ {s : SystemState}, storeObject tableId (.pageTable table.uninstalled) st =
        .ok ((), s) → LendersFrame st s :=
      fun hS => storeObject_other hInv hS (fun _ e => by cases e) (fun _ e => by cases e)
    rw [hT] at h
    simp only at h
    split at h
    · cases h; exact refl hInv
    · split at h
      · exact Ft h
      · split at h
        · split at h
          · cases h
          · cases hS1 : storeObject tableId (.pageTable table.uninstalled) st with
            | error e => rw [hS1] at h; cases h
            | ok p =>
              obtain ⟨⟨⟩, st1⟩ := p
              rw [hS1] at h
              simp only at h
              have F1 := Ft hS1
              have F2 : ∀ ws, LendersFrame st1 (Architecture.recordPhysicalWrites st1 ws) := fun _ =>
                ⟨(chainObjectsKept.of_objects_eq (st := st1)
                  (st' := Architecture.recordPhysicalWrites st1 _) rfl).linksShrink, F1.invExt⟩
              exact (F1.andThen fun _ => F2 _).andThen fun hI =>
                storeObject_other hI h (fun _ e => by cases e) (fun _ e => by cases e)
        · exact Ft h

theorem irqControlGet {control dst : CSpaceAddr} {line : Nat} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.irqControlGet control dst line st = .ok ((), st')) :
    LendersFrame st st' := by
  refine ⟨?_, (RecordsFrame.irqControlGet hInv h).invExt⟩
  unfold _root_.SeLe4n.Kernel.irqControlGet at h
  cases hR : irqControlLineRefusal st line with
  | some e => rw [hR] at h; cases h
  | none =>
    rw [hR] at h
    simp only at h
    cases hI : _root_.SeLe4n.Kernel.cspaceInsertSlot dst (Capability.irqHandlerOf line)
        (Architecture.setIrqLineSignal st line true) with
    | error e => rw [hI] at h; cases h
    | ok pr =>
      obtain ⟨⟨⟩, st1⟩ := pr
      rw [hI] at h
      injection h with h
      injection h with hu h
      subst h
      have F0 := RecordsFrame.of_objects_eq hInv (Architecture.setIrqLineSignal_objects st line true)
        (Architecture.setIrqLineSignal_asidTable st line true)
      have K0 : chainObjectsKept st (Architecture.setIrqLineSignal st line true) :=
        chainObjectsKept.of_objects_eq (Architecture.setIrqLineSignal_objects st line true)
      have F1 := RecordsFrame.cspaceInsertSlot F0.invExt hI
      exact ((K0.trans (chainObjectsKept.cspaceInsertSlot F0.invExt hI)).trans
        (chainObjectsKept.cdtAddChild st1 control dst .mint F1.invExt)).linksShrink

theorem irqControlGetFromCap {tid : SeLe4n.ThreadId} {srcAddr : SeLe4n.CPtr}
    {root? : Option SeLe4n.CPtr}
    {args? : Except KernelError Architecture.SyscallArgDecode.IrqControlGetArgs} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.irqControlGetFromCap tid srcAddr root? args? st = .ok ((), st')) :
    LendersFrame st st' := by
  obtain ⟨_, _, _, _, _, _, hG⟩ := irqControlGetFromCap_ok tid srcAddr root? args? st st' h
  exact irqControlGet hInv hG

end LendersFrame

namespace LendersFrame

theorem descheduleAt (st : SystemState) (t : SeLe4n.ThreadId) (p : Option CoreId)
    (hInv : st.objects.invExt) : LendersFrame st (_root_.SeLe4n.Kernel.descheduleAt st t p) := by
  refine of_kept ?_ (RecordsFrame.descheduleAt st t p hInv)
  unfold _root_.SeLe4n.Kernel.descheduleAt
  split
  · exact chainObjectsKept.removeRunnableOnCore _ _ _
  · exact chainObjectsKept.refl _

theorem releaseRemoveThread (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    LendersFrame st (Lifecycle.Suspend.releaseRemoveThread st t) :=
  of_views (contextStackViewsAgree_of_objectsAgreeOffReleaseLinks
      (Lifecycle.Suspend.releaseRemoveThread_agree st t))
    (RecordsFrame.releaseRemoveThread st t hInv).invExt

theorem cancelYieldTo (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.cancelYieldTo st t) := by
  unfold _root_.SeLe4n.Kernel.cancelYieldTo
  split
  · split
    · exact refl hInv
    · rename_i k _
      exact (updateSchedContext st ⟨k⟩ SchedContext.yieldCleared (fun _ => rfl) hInv).andThen
        fun h => updateTcb _ t _ h
  · exact refl hInv

theorem suspendRescheduleOnCore {st st' : SystemState} {runningCore executingCore : CoreId}
    {wasCurrent localDeboosted : Bool} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.suspendRescheduleOnCore st runningCore executingCore wasCurrent
      localDeboosted = .ok (st', sgi?)) : LendersFrame st st' := by
  unfold Lifecycle.Suspend.suspendRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (rename_i hH; rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1];
        exact handleRescheduleSgiOnCore hInv hH)
    | (rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact refl hInv)

/-- **The thread suspend** (seL4 `suspend`): seL4-MCS's `cancelIPC` (a links
shrink), the priority revert, the deschedule, the state writes, the release
removal, the yield cancel and the scheduling point. -/
theorem suspendThreadOnCore {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (hStep : Lifecycle.Suspend.suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    LendersFrame st st' := by
  simp only [Lifecycle.Suspend.suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb hT =>
    split at hStep
    case isTrue => cases hStep; exact refl hInv
    case isFalse hA =>
      have S1 := cancelIpcKeepingContexts st vtid.val tcb hInv
      have S2 : LendersFrame st
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) serverId executingCore).1
           | none => Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact S1
        | some serverId => exact S1.andThen fun h => propagatePipChainCrossCore _ _ _ _ h
      have S3 := S2.andThen fun h => descheduleAt _ vtid.val (placedCoreOf? st vtid.val) h
      have S4 := S3.andThen fun h =>
        (show LendersFrame _ (Lifecycle.Suspend.clearPendingStateValid _ vtid) by
          unfold Lifecycle.Suspend.clearPendingStateValid Lifecycle.Suspend.clearPendingState
          exact updateTcb _ _ _ h)
      have S5 := S4.andThen fun h => updateTcb _ vtid.val (fun t => { t with threadState := .Inactive }) h
      have S6 := S5.andThen fun h => releaseRemoveThread _ vtid.val h
      have S7 := S6.andThen fun h => cancelYieldTo _ vtid.val h
      exact S7.andThen fun h => suspendRescheduleOnCore h hStep

end LendersFrame

namespace LendersFrame

theorem markKeyChangeFrom (pre st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.markKeyChangeFrom pre st t) :=
  of_kept (chainObjectsKept.of_objects_eq (markKeyChangeFrom_objects pre st t))
    (RecordsFrame.markKeyChangeFrom pre st t hInv)

theorem enqueueRunnableOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : LendersFrame st (_root_.SeLe4n.Kernel.enqueueRunnableOnCore st c t) :=
  ⟨(chainObjectsKept.enqueueRunnableOnCore st c t hInv).linksShrink,
   enqueueRunnableOnCore_preserves_objects_invExt st c t hInv⟩

theorem resumeContext (st : SystemState) (t : SeLe4n.ThreadId) (home : CoreId)
    (hInv : st.objects.invExt) : LendersFrame st (Lifecycle.Suspend.resumeContext st t home) := by
  rcases Lifecycle.Suspend.resumeContext_cases st t home with e | ⟨s, e⟩ <;> rw [e]
  · exact refl hInv
  · exact (updateSchedContext st s (fun sc => sc.refillUnblockCheck st.machine.timer)
      (fun sc => (SchedContext.fields_of_refillsErased
        (SchedContext.refillUnblockCheck_refillsErased sc _)).2.2.2.2.2.2.2.1) hInv).andThen
      fun h => settleReturnedContext _ home s h

theorem resumeReadyMidState (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    LendersFrame st (Lifecycle.Suspend.resumeReadyMidState st t) := by
  have S : LendersFrame st (Lifecycle.Suspend.restoreToReadyStaging st t false) := by
    unfold Lifecycle.Suspend.restoreToReadyStaging; exact updateTcb _ _ _ hInv
  unfold Lifecycle.Suspend.resumeReadyMidState
  dsimp only
  exact S.andThen fun h => updateTcb _ t _ h

theorem retirePendingFaultForResume (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.retirePendingFaultForResume st t) := by
  unfold _root_.SeLe4n.Kernel.retirePendingFaultForResume
  split
  · split
    · split
      · unfold discardPendingFault; exact updateTcb _ _ _ hInv
      · unfold applyFaultRestart; exact updateTcb _ _ _ hInv
    · exact refl hInv
  · exact refl hInv

/-- **The thread resume** (seL4 `restart`'s resume half): the ready mark, the
key hook, the context's return, the wake and the scheduling point. -/
theorem resumeThreadOnCore {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    LendersFrame st st' := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · have S0 := ((resumeReadyMidState st vtid.val hInv).andThen fun h =>
        markKeyChangeFrom st _ vtid.val h).andThen fun h =>
          resumeContext _ vtid.val (determineTargetCore st vtid.val) h
      have S := S0.andThen fun h => enqueueRunnableOnCore _ (determineTargetCore st vtid.val) vtid.val h
      split at h
      · split at h
        · split at h
          · rename_i hH
            rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]
            exact S.andThen fun h' => handleRescheduleSgiOnCore h' hH
          · cases h
        · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact S
      · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact S0
  · cases h

/-- **The thread restart** (seL4 `restart`): a resume, or a suspend then a
resume, each after the fault retire; or nothing. -/
theorem restartThreadOnCore {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.restartThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    LendersFrame st st' := by
  rcases Lifecycle.Suspend.restartThreadOnCore_cases h with hRes | ⟨st1, _, hSus, hRes⟩ | ⟨rfl, _⟩
  · exact (retirePendingFaultForResume st vtid.val hInv).andThen fun h' => resumeThreadOnCore h' hRes
  · exact ((suspendThreadOnCore hInv hSus).andThen fun h' =>
      retirePendingFaultForResume st1 vtid.val h').andThen fun h' => resumeThreadOnCore h' hRes
  · exact refl hInv

end LendersFrame

/-- **A carve shrinks the links**: the watermark, the fresh child (a new reply
object or context is born with no link and no caller, seL4's zeroed object),
the free index, the scrub, the capability insert and the derivation edge. -/
theorem untypedRetypeObject_linksShrink {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.untypedRetypeObject src childId dst req st = .ok ((), st')) :
    contextStackLinksShrink st st' := by
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hInv h
  obtain ⟨ut₀, ut', cap, stUt, _, stCh, cn, hUt, _, _, _, _, _, _, hLk, _, _, hStUt, hStCh, hOCh,
    hStIdx⟩ := retypeFromUntyped_ok_stores st st1 src untypedId childId _ _ hInv hRt
  have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hStUt
  have hI2 := storeObject_preserves_objects_invExt _ _ _ _ hI1 hStCh
  have hI3 := storeObject_preserves_objects_invExt _ _ _ _ hI2 hStIdx
  have L1 := (chainObjectsKept.storeObject_other hInv hStUt (fun _ e => by cases e)
    (fun _ e => by cases e)).linksShrink
  have L2 : contextStackLinksShrink stUt stCh := by
    refine contextStackLinksShrink_storeObject hI1 hStCh (fun _ r _ hr => ?_) (fun x hx => ?_)
      (fun l hl => ?_)
    · cases req <;> simp [CarveRequest.object, objStackHead,
        SeLe4n.Kernel.SchedContext.empty] at hr
    · cases req <;> simp [CarveRequest.object, objStackPrev, SeLe4n.Kernel.Reply.empty] at hx
    · cases req <;> simp [CarveRequest.object, objStackCaller, SeLe4n.Kernel.Reply.empty] at hl
  have L3 := (chainObjectsKept.storeObject_other hI2 hStIdx (fun _ e => by cases e)
    (fun _ e => by cases e)).linksShrink
  have hIZ : (req.scrub st1 ut (req.carveIndex ut (retypeFreeIndex st src utCap))).objects.invExt := by
    rw [CarveRequest.scrub_objects]; exact hI3
  have L4 : contextStackLinksShrink st1
      (req.scrub st1 ut (req.carveIndex ut (retypeFreeIndex st src utCap))) :=
    (chainObjectsKept.of_objects_eq (CarveRequest.scrub_objects st1 ut _ req)).linksShrink
  have L5 := (chainObjectsKept.cspaceInsertSlot hIZ hIns).linksShrink
  have L6 := (chainObjectsKept.cdtAddChild st2 src dst .retype
    (cspaceInsertSlot_preserves_objects_invExt _ _ _ _ hIZ hIns)).linksShrink
  exact ((((L1.trans L2).trans L3).trans L4).trans L5).trans L6

namespace LendersFrame

/-- The live `.untypedRetype` arm: the carve chain. -/
theorem untypedRetypeFromCap {tid : SeLe4n.ThreadId} {ec : CoreId}
    {srcAddr : SeLe4n.CPtr} {root? : Option SeLe4n.CPtr}
    {args? : Except KernelError SeLe4n.Kernel.Architecture.SyscallArgDecode.UntypedRetypeArgs}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.untypedRetypeFromCap tid ec srcAddr root? args? st = .ok ((), st')) :
    LendersFrame st st' :=
  (untypedRetypeFromCap_chain h).rel (P := fun s => s.objects.invExt)
    (R := fun a b => a.objects.invExt → LendersFrame a b) (fun _ => refl)
    (fun h1 h2 hI => (h1 hI).andThen h2)
    (fun hP hC => untypedRetypeObject_preserves_objects_invExt hP hC)
    (fun hP hC _ => ⟨untypedRetypeObject_linksShrink hP hC,
      untypedRetypeObject_preserves_objects_invExt hP hC⟩) hInv hInv

end LendersFrame

/-- **A finalisation write** (threads, endpoints, notifications and contexts
alone, each context keeping its head) moves none of the three stack views. -/
theorem contextStackViewsAgree_of_finaliseWrite {st st' : SystemState}
    (h : finaliseWrite st st') : contextStackViewsAgree st st' := by
  have key : ∀ x : SeLe4n.ObjId, objStackHead st'.objects[x]? = objStackHead st.objects[x]? ∧
      objStackPrev st'.objects[x]? = objStackPrev st.objects[x]? ∧
      objStackCaller st'.objects[x]? = objStackCaller st.objects[x]? := fun x => by
    rcases h x with e | ⟨pre, post, hp, hq, ht, -, hh, hw⟩
    · rw [e]; exact ⟨rfl, rfl, rfl⟩
    · rw [hp, hq]
      rcases hw with hw | hw | hw | hw <;>
        cases pre <;> simp only [KernelObject.objectType, reduceCtorEq] at hw <;>
        cases post <;> simp only [KernelObject.objectType, reduceCtorEq] at ht <;>
        simp_all [objStackHead, objStackPrev, objStackCaller, schedContextStackHead?]
  refine ⟨fun s => ?_, fun r => ?_, fun r => ?_⟩
  · rw [contextStackHead_eq_obj, contextStackHead_eq_obj]; exact (key _).1
  · rw [replyStackPrev_eq_obj, replyStackPrev_eq_obj]; exact (key _).2.1
  · rw [replyStackCaller_eq_obj, replyStackCaller_eq_obj]; exact (key _).2.2

namespace LendersFrame

theorem of_finaliseFrame {st st' : SystemState} (F : FinaliseFrame st st') : LendersFrame st st' :=
  of_views (contextStackViewsAgree_of_finaliseWrite F.write) F.invExt

/-- A reply-blocked caller's cancel, its lent context handed back and its
holder descheduled, then its server's boost reverted. -/
theorem finaliseReplyCancel (s : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : s.objects.invExt) :
    LendersFrame s (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?) := by
  have S1 : LendersFrame s (cancelIpcBlockingMigrated c t s) := by
    unfold cancelIpcBlockingMigrated
    have S := cancelIpcBlocking s c t hInv
    split
    · exact S.andThen fun h => settleReturnedContext _ _ _ h
    · exact S
  have S2 : LendersFrame s (cancelIpcBlockingReclaimed c t s) := by
    unfold cancelIpcBlockingReclaimed descheduleUnboundHolder
    split
    · exact S1
    · exact S1.andThen fun h => of_finaliseFrame (FinaliseFrame.descheduleAt _ _ _ h)
  exact S2.andThen fun h => of_finaliseFrame (FinaliseFrame.finaliseReplyRevert _ _ h)

theorem finaliseReplyUnheldPop (st : SystemState) (r : Reply) (c : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.finaliseReplyUnheldPop st r c) := by
  rcases finaliseReplyUnheldPop_cases st r c with e | ⟨_, _, _, _, _, hP, e⟩ |
      ⟨_, _, _, _, _, _, hP, e⟩
  · rw [e]; exact refl hInv
  · rw [e]
    have F := RecordsFrame.returnUnheldSchedContext hInv hP
    exact (of_shrink (returnUnheldSchedContext_linksShrink hInv hP) F.invExt).andThen
      fun h => settleReturnedContext _ _ _ h
  · rw [e]
    exact of_shrink (severUnheldSchedContext_linksShrink hInv hP)
      (RecordsFrame.severUnheldSchedContext hInv hP).invExt

/-- **The finalisation** (seL4 `finaliseCap` on the object's last capability)
shrinks the links: every step writes threads, endpoints, notifications and
contexts keeping their heads, or is one of the removals (the cancel of a
reply's caller, the cut, the unstack, the unheld pop). -/
theorem finaliseFinalObject (target : Nat) (st : SystemState) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.finaliseFinalObject target st) :=
  finaliseFinalObject_closed (LendersFrame st)
    (fun _ _ _ _ _ _ h _ _ _ _ => h.andThen fun hI =>
      of_finaliseFrame (FinaliseFrame.storeEndpointWaiterCancelled _ _ _ _ _ _ hI))
    (fun _ s _ t tcb h _ _ _ _ => (h.andThen fun hI => cancelIpcBlocking s t tcb hI).andThen
      fun hI => of_finaliseFrame (FinaliseFrame.wakeCancelledWaiter _ _ hI))
    (fun _ s _ t h _ _ _ _ => h.andThen fun hI =>
      of_finaliseFrame (FinaliseFrame.storeUnbindNotification s t _ hI))
    (fun s t _ h _ _ _ _ => h.andThen fun hI => of_finaliseFrame (FinaliseFrame.descheduleAt s t _ hI))
    (fun s s' t tcb sc x h hT hS hSc hB hOk => h.andThen fun hI =>
      of_finaliseFrame (FinaliseFrame.releaseStep s s s' t tcb sc x (.refl hI) hT hS hSc hB hOk))
    (fun s _ t tcb _ h _ _ _ _ => h.andThen fun hI => cancelIpcBlocking s t tcb hI)
    (fun s e q t ep tcb h _ _ _ => h.andThen fun hI =>
      of_finaliseFrame (FinaliseFrame.storeEndpointBlockedCancelled s e q t ep tcb hI))
    (fun s t _ h _ _ _ _ _ => h.andThen fun hI => of_finaliseFrame (FinaliseFrame.suspend s t hI))
    (fun s t h => h.andThen fun hI => of_finaliseFrame (FinaliseFrame.releaseCores s t hI))
    (fun s s1 _ _ _ r h _ _ hR _ hS _ _ _ _ => h.andThen fun hI =>
      (show LendersFrame s s1 from
        of_shrink (contextStackLinksShrink_storeReply hI hR hS (Or.inr rfl) (Or.inr rfl))
          (storeObject_preserves_objects_invExt _ _ _ _ hI hS)).andThen fun h' =>
        updateSchedContext_clearHead _ _ _ (fun _ => Or.inl rfl) h')
    (fun s _ _ c t h _ _ _ _ => h.andThen fun hI => finaliseReplyCancel s c t hI)
    (fun s s1 _ tid _ h _ _ hEq => by
      subst hEq; exact h.andThen fun hI => of_finaliseFrame (FinaliseFrame.updateTcb s tid _ hI))
    ⟨fun s t h => h.andThen fun hI => cancelYieldTo s t hI,
     fun s c h => h.andThen fun hI => completeYieldFrom s c hI⟩
    (fun s w x _ h _ _ _ => h.andThen fun hI => of_finaliseFrame (FinaliseFrame.orphanReplyWaiter s w x hI))
    (fun s _ r c _ h _ _ _ _ => h.andThen fun hI => finaliseReplyUnheldPop s r c hI)
    (fun s _ _ _ t h _ _ _ _ => h.andThen fun hI => cutCancelledCallerHead s t hI)
    (fun s c h => h.andThen fun hI => unbindSchedContextNotification s c hI)
    target st (refl hInv)

end LendersFrame

end SeLe4n.Kernel
