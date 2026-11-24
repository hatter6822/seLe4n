-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Entry
import SeLe4n.Kernel.KernelRecords.Entry

/-! # The timer entry keeps the lenders' flow

WS-SX SX8.  The tick writes thread records, contexts, the scheduler and the
machine.  It writes no reply object, and every context it writes keeps its
stack head (`SchedContext.scReply`): the charge, the refill and the release
placement edit a context's budget, refills and release links alone
(`SchedContext.fields_of_refillsErased`).  So each step is a
`LendersFrame`: its writes only shrink the stack views (here they keep them),
and it keeps the store's invariant, which the next step reads.  The tick's
timeouts abort IPC blocks, wake, unlink reply waiters and revert priority
inheritance, all on threads and endpoints.  The entry therefore needs no
premise but the store's invariant at the state it runs from.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **One slot rewritten keeping its three stack views**: the generic frame of a
write to a context that keeps its head, or to an object of another kind. -/
theorem contextStackViewsAgree_insert {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt)
    (hH : objStackHead (some o) = objStackHead st.objects[k]?)
    (hP : objStackPrev (some o) = objStackPrev st.objects[k]?)
    (hC : objStackCaller (some o) = objStackCaller st.objects[k]?)
    (hB : objBindingWords (some o) = objBindingWords st.objects[k]?) :
    contextStackViewsAgree st { st with objects := st.objects.insert k o } := by
  have hIns : (st.objects.insert k o)[k]? = some o := by
    simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
  have hNe : ∀ x, ¬ k = x → (st.objects.insert k o)[x]? = st.objects[x]? := fun x hx => by
    simp only [RHTable_getElem?_eq_get?]
    exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb)) hInv
  refine ⟨fun s => ?_, fun r => ?_, fun r => ?_, fun x => ?_⟩
  · rw [contextStackHead_eq_obj, contextStackHead_eq_obj]
    show objStackHead (st.objects.insert k o)[s.toObjId]? = _
    by_cases hx : k = s.toObjId
    · rw [← hx, hIns]; exact hH
    · rw [hNe _ hx]
  · rw [replyStackPrev_eq_obj, replyStackPrev_eq_obj]
    show objStackPrev (st.objects.insert k o)[r.toObjId]? = _
    by_cases hx : k = r.toObjId
    · rw [← hx, hIns]; exact hP
    · rw [hNe _ hx]
  · rw [replyStackCaller_eq_obj, replyStackCaller_eq_obj]
    show objStackCaller (st.objects.insert k o)[r.toObjId]? = _
    by_cases hx : k = r.toObjId
    · rw [← hx, hIns]; exact hC
    · rw [hNe _ hx]
  · show objBindingWords (st.objects.insert k o)[x]? = _
    by_cases hx : k = x
    · rw [← hx, hIns]; exact hB
    · rw [hNe _ hx]

/-- **A step that only shrinks the stack views and keeps the store's invariant**:
the unit the timer path chains (a `LendersStage` with the invariant the next
step reads). -/
structure LendersFrame (st st' : SystemState) : Prop where
  links : contextStackLinksShrink st st'
  invExt : st'.objects.invExt

namespace LendersFrame

theorem refl {st : SystemState} (h : st.objects.invExt) : LendersFrame st st :=
  ⟨.refl _, h⟩

theorem andThen {a b c : SystemState} (F : LendersFrame a b)
    (G : b.objects.invExt → LendersFrame b c) : LendersFrame a c :=
  ⟨F.links.trans (G F.invExt).links, (G F.invExt).invExt⟩

theorem of_kept {st st' : SystemState} (K : chainObjectsKept st st') (R : RecordsFrame st st') :
    LendersFrame st st' := ⟨K.linksShrink, R.invExt⟩

theorem of_views {st st' : SystemState} (V : contextStackViewsAgree st st')
    (h : st'.objects.invExt) : LendersFrame st st' :=
  ⟨contextStackLinksShrink_of_viewsAgree V, h⟩

theorem stage {ctx : LabelingContext} {st st' : SystemState} (F : LendersFrame st st') :
    LendersStage ctx st st' := LendersStage.of_linksShrink F.links

/-- The charge and the refill keep a context's thread word. -/
theorem chargeBudget_boundThreadCode (sc : SchedContext) (start usage now : Nat) :
    (sc.chargeBudget start usage now).boundThreadCode = sc.boundThreadCode :=
  (SchedContext.fields_of_refillsErased (sc.chargeBudget_refillsErased start usage now)).2.2.2.2.2.2.1

theorem releaseReadyHead_boundThreadCode (sc : SchedContext) (now : Nat) :
    (sc.releaseReadyHead now).boundThreadCode = sc.boundThreadCode :=
  (SchedContext.fields_of_refillsErased (sc.releaseReadyHead_refillsErased now)).2.2.2.2.2.2.1

/-- A context rewritten keeping its stack head. -/
theorem rewriteObject_schedContext {st : SystemState} {scId : SeLe4n.SchedContextId}
    {sc : SchedContext} (h : st.getSchedContext? scId = some sc) (sc' : SchedContext)
    (hR : sc'.scReply = sc.scReply)
    (hA : st.rewriteAdmissible scId.toObjId (.schedContext sc')) (hInv : st.objects.invExt)
    (hB : sc'.boundThreadCode = sc.boundThreadCode := by
      first
        | rfl
        | exact chargeBudget_boundThreadCode _ _ _ _
        | exact releaseReadyHead_boundThreadCode _ _) :
    LendersFrame st (st.rewriteObject scId.toObjId (.schedContext sc') hA) := by
  have hRaw := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp h
  exact of_views (contextStackViewsAgree_insert hInv (by rw [hRaw]; exact hR)
      (by rw [hRaw]; rfl) (by rw [hRaw]; rfl) (by rw [hRaw]; simp only [objBindingWords, hB]))
    (RecordsFrame.rewriteObject_schedContext h sc' hA hInv).invExt

/-- A context's read-modify-write keeping its stack head. -/
theorem updateSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hf : ∀ x, (f x).scReply = x.scReply)
    (hInv : st.objects.invExt)
    (hfB : ∀ x, (f x).boundThreadCode = x.boundThreadCode := by
      intro x
      first
        | rfl
        | exact chargeBudget_boundThreadCode _ _ _ _
        | exact releaseReadyHead_boundThreadCode _ _) :
    LendersFrame st (st.updateSchedContext scId f) := by
  unfold SystemState.updateSchedContext
  split
  · rename_i sc h _
    exact rewriteObject_schedContext h _ (hf sc) _ hInv (hfB sc)
  · exact refl hInv

/-- The charge and the refill keep a context's stack head. -/
theorem chargeBudget_scReply (sc : SchedContext) (start usage now : Nat) :
    (sc.chargeBudget start usage now).scReply = sc.scReply :=
  (SchedContext.fields_of_refillsErased (sc.chargeBudget_refillsErased start usage now)).2.2.2.2.2.2.2.1

theorem releaseReadyHead_scReply (sc : SchedContext) (now : Nat) :
    (sc.releaseReadyHead now).scReply = sc.scReply :=
  (SchedContext.fields_of_refillsErased (sc.releaseReadyHead_refillsErased now)).2.2.2.2.2.2.2.1

/-! ### The scheduler's writes -/

theorem withScheduler (st : SystemState) (s : SchedulerState) (hInv : st.objects.invExt) :
    LendersFrame st { st with scheduler := s } :=
  of_kept (chainObjectsKept.withScheduler st s) (RecordsFrame.withScheduler st s hInv)

theorem runEnqueueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) : LendersFrame st (st.runEnqueueOnCore c t p) :=
  of_kept (chainObjectsKept.runEnqueueOnCore st c t p) (RecordsFrame.runEnqueueOnCore st c t p hInv)

theorem runRemoveOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : LendersFrame st (st.runRemoveOnCore c t) :=
  of_kept (chainObjectsKept.runRemoveOnCore st c t) (RecordsFrame.runRemoveOnCore st c t hInv)

theorem runEnqueueAdmitted (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    LendersFrame st (st.runEnqueueAdmitted c t p) :=
  of_kept (chainObjectsKept.of_objectsAgreeOffRunLinks
      (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks st c t p))
    (RecordsFrame.runEnqueueAdmitted st c t p hInv)

theorem restoreIncomingContextOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : LendersFrame st (restoreIncomingContextOnCore st c tid) :=
  of_kept (chainObjectsKept.restoreIncomingContextOnCore st c tid)
    (RecordsFrame.restoreIncomingContextOnCore st c tid hInv)

theorem saveOutgoingContextOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    LendersFrame st (saveOutgoingContextOnCore st c) := by
  refine of_kept ?_ (RecordsFrame.saveOutgoingContextOnCore st c hInv)
  unfold _root_.SeLe4n.Kernel.saveOutgoingContextOnCore
  split
  · exact chainObjectsKept.refl _
  · exact chainObjectsKept.updateTcb st _ _ hInv

theorem rewriteObject_tcb {st : SystemState} {t : SeLe4n.ThreadId} {x : TCB}
    (h : st.getTcb? t = some x) (x' : TCB) (hV : x'.recordView = x.recordView)
    (hA : st.rewriteAdmissible t.toObjId (.tcb x')) (hInv : st.objects.invExt)
    (hB : x'.scBindingScCode = x.scBindingScCode ∧ x'.scBindingOwnerCode = x.scBindingOwnerCode :=
      by exact ⟨rfl, rfl⟩) :
    LendersFrame st (st.rewriteObject t.toObjId (.tcb x') hA) :=
  of_kept (chainObjectsKept.rewriteObject_tcb hA hInv
      (objBindingShrink.ofTcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp h) (.inr hB)))
    (RecordsFrame.rewriteObject_tcb h x' hV hA hInv)

theorem releasePlace (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : LendersFrame st (st.releasePlace c s) :=
  of_views (contextStackViewsAgree_of_objectsAgreeOffReleaseLinks (SystemState.releasePlace_agree st c s))
    (RecordsFrame.releasePlace st c s hInv).invExt

theorem markKeyChangeFor (st : SystemState) (t : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.markKeyChangeFor st t k) :=
  of_kept (chainObjectsKept.of_objects_eq (markKeyChangeFor_objects st t k))
    (RecordsFrame.markKeyChangeFor st t k hInv)

theorem wakeThread (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) (hR : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready) :
    LendersFrame st (_root_.SeLe4n.Kernel.wakeThread st tid c).1 :=
  of_kept (chainObjectsKept.wakeThread st tid c hInv) (RecordsFrame.wakeThread st tid c hInv hR)

theorem sliceExpireOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.sliceExpireOnCore st c tid tcb hTcb) := by
  unfold _root_.SeLe4n.Kernel.sliceExpireOnCore
  refine (rewriteObject_tcb hTcb _ ?_ _ hInv).andThen fun h => runEnqueueOnCore _ _ _ _ h
  rfl

theorem spendBudgetOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (start ticks : Nat) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.spendBudgetOnCore st c tid scId sc hSc start ticks) := by
  unfold _root_.SeLe4n.Kernel.spendBudgetOnCore replenishOnCore
  exact ((rewriteObject_schedContext hSc _ (chargeBudget_scReply sc _ _ _) _ hInv).andThen
    fun h => releasePlace _ c scId h).andThen fun h => runEnqueueOnCore _ _ _ _ h

theorem idleFallbackOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.idleFallbackOnCore st c) := by
  unfold _root_.SeLe4n.Kernel.idleFallbackOnCore dispatchIdleOnCore
  split
  · exact ((runRemoveOnCore st c _ hInv).andThen fun h => restoreIncomingContextOnCore _ c _ h).andThen
      fun h => withScheduler _ _ h
  · exact withScheduler _ _ hInv

theorem scheduleEffectiveOnCore {st st' : SystemState} {c : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.scheduleEffectiveOnCore st c = .ok st') : LendersFrame st st' := by
  unfold _root_.SeLe4n.Kernel.scheduleEffectiveOnCore at h
  split at h
  · cases h
  · rw [Except.ok.injEq] at h; subst h
    exact ((saveOutgoingContextOnCore st c hInv).andThen fun h => idleFallbackOnCore _ c h).andThen
      fun h => withScheduler _ _ h
  · split at h
    · split at h
      · rw [Except.ok.injEq] at h; subst h
        rename_i tid _ _ _ _ _
        exact (((saveOutgoingContextOnCore st c hInv).andThen fun h => runRemoveOnCore _ c tid h).andThen
          fun h => restoreIncomingContextOnCore _ c tid h).andThen fun h => withScheduler _ _ h
      · cases h
    · cases h

theorem handleRescheduleSgiOnCore {st st' : SystemState} {c : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.handleRescheduleSgiOnCore st c = .ok st') : LendersFrame st st' :=
  of_kept (chainObjectsKept.handleRescheduleSgiOnCore hInv h) (RecordsFrame.handleRescheduleSgiOnCore hInv h)

end LendersFrame

/-- **A labelled step** (WS-SX SX16.2): the lenders' stage carried from `st` to
`st'`, and the store's invariant at `st'`.  The unit a chain composes once it
holds a pop, which grows the binding views and so is no links shrink: each pop
discharges its owner obligation inside its step, at its own pre-state. -/
structure LendersStep (ctx : LabelingContext) (st st' : SystemState) : Prop where
  stage : LendersStage ctx st st'
  invExt : st'.objects.invExt

namespace LendersStep

variable {ctx : LabelingContext}

theorem refl {st : SystemState} (h : st.objects.invExt) : LendersStep ctx st st :=
  ⟨LendersStage.refl _, h⟩

theorem andThen {a b c : SystemState} (F : LendersStep ctx a b)
    (G : b.objects.invExt → LendersStep ctx b c) : LendersStep ctx a c :=
  ⟨F.stage.trans (G F.invExt).stage, (G F.invExt).invExt⟩

/-- A frame read as a labelled step. -/
theorem of_frame {st st' : SystemState} (F : LendersFrame st st') : LendersStep ctx st st' :=
  ⟨F.stage, F.invExt⟩

end LendersStep

namespace LendersFrame

/-- A frame followed by a labelled step. -/
theorem andThenStep {ctx : LabelingContext} {a b c : SystemState} (F : LendersFrame a b)
    (G : b.objects.invExt → LendersStep ctx b c) : LendersStep ctx a c :=
  (LendersStep.of_frame F).andThen G

end LendersFrame

namespace LendersStep

variable {ctx : LabelingContext}

/-- **One slot written keeping its three stack views**, its binding words grown
with equal labels: a creating write read as a labelled step. -/
theorem of_insert {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hObj : st'.objects = st.objects.insert k o)
    (hH : objStackHead (some o) = objStackHead st.objects[k]?)
    (hP : objStackPrev (some o) = objStackPrev st.objects[k]?)
    (hC : objStackCaller (some o) = objStackCaller st.objects[k]?)
    (hG : bindingViewsGrow ctx st st') (hI : st'.objects.invExt) : LendersStep ctx st st' := by
  have hIns : st'.objects[k]? = some o := by
    rw [hObj]; simp only [RHTable_getElem?_eq_get?]
    exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
  have hNe : ∀ x, x ≠ k → st'.objects[x]? = st.objects[x]? := fun x hx => by
    rw [hObj]; simp only [RHTable_getElem?_eq_get?]
    exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb).symm) hInv
  refine ⟨fun hL => lendingLabelsEqual_of_grow hL (contextStacksShrink_of_slot k hNe ?_ ?_ ?_) hG, hI⟩
  · intro s r hs hr
    rw [hIns, hH] at hr
    exact .head (by rw [contextStackHead_eq_obj, hs]; exact hr)
  · intro x hx; rw [hIns, hP] at hx; exact hx
  · intro l hl; rw [hIns, hC] at hl; exact hl

/-- **A thread record rewritten**, its binding words naming contexts labelled
as the thread and owners labelled as those contexts. -/
theorem updateTcb_grow (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt)
    (hT : ∀ (x : TCB) (s : SeLe4n.SchedContextId), st.getTcb? t = some x →
      (f x).scBindingScCode = s.val + 1 → ctx.threadLabelOf t = ctx.objectLabelOf s.toObjId)
    (hO : ∀ (x : TCB) (s : SeLe4n.SchedContextId) (o : SeLe4n.ThreadId), st.getTcb? t = some x →
      (f x).scBindingScCode = s.val + 1 → (f x).scBindingOwnerCode = o.val + 1 →
      ctx.threadLabelOf o = ctx.objectLabelOf s.toObjId) :
    LendersStep ctx st (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact refl hInv
  | some x =>
    have hI := SystemState.updateTcb_preserves_objects_invExt st t f hInv
    rw [SystemState.updateTcb_eq_of_some hG] at hI ⊢
    have hO0 := (SystemState.getTcb?_eq_some_iff st t x).mp hG
    have hObj : ({ st with objects := st.objects.insert t.toObjId (.tcb (f x)) } : SystemState).objects
        = st.objects.insert t.toObjId (.tcb (f x)) := rfl
    have hIns : ({ st with objects := st.objects.insert t.toObjId (.tcb (f x)) } : SystemState).objects[t.toObjId]?
        = some (.tcb (f x)) := by
      simp only [RHTable_getElem?_eq_get?]
      exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
    refine of_insert hInv hObj (by rw [hO0]; rfl) (by rw [hO0]; rfl) (by rw [hO0]; rfl)
      (bindingViewsGrow_of_tcbSlot (fun y hy => ?_) hIns (fun s hs => hT x s hG hs)
        (fun s o hs ho => hO x s o hG hs ho)) hI
    show objBindingWords (st.objects.insert t.toObjId _)[y]? = _
    simp only [RHTable_getElem?_eq_get?]
    rw [RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hy (eq_of_beq hb).symm) hInv]

/-- **A context rewritten keeping its stack head**, its thread word naming a
thread labelled as the context. -/
theorem rewriteObject_schedContext_grow {st : SystemState} {scId : SeLe4n.SchedContextId}
    {sc : SchedContext} (h : st.getSchedContext? scId = some sc) (sc' : SchedContext)
    (hR : sc'.scReply = sc.scReply)
    (hA : st.rewriteAdmissible scId.toObjId (.schedContext sc')) (hInv : st.objects.invExt)
    (hC : ∀ t : SeLe4n.ThreadId, sc'.boundThreadCode = t.val + 1 →
      ctx.threadLabelOf t = ctx.objectLabelOf scId.toObjId) :
    LendersStep ctx st (st.rewriteObject scId.toObjId (.schedContext sc') hA) := by
  have hRaw := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp h
  have hObj := SystemState.rewriteObject_objects st scId.toObjId (.schedContext sc') hA
  have hIns : (st.rewriteObject scId.toObjId (.schedContext sc') hA).objects[scId.toObjId]?
      = some (.schedContext sc') := by
    rw [hObj]; simp only [RHTable_getElem?_eq_get?]
    exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
  refine of_insert hInv hObj (by rw [hRaw]; exact hR) (by rw [hRaw]; rfl) (by rw [hRaw]; rfl)
    (bindingViewsGrow_of_schedContextSlot (fun y hy => ?_) hIns hC)
    (RecordsFrame.rewriteObject_schedContext h sc' hA hInv).invExt
  rw [hObj]; simp only [RHTable_getElem?_eq_get?]
  rw [RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hy (eq_of_beq hb).symm) hInv]

end LendersStep

namespace LendersFrame

/-! ### The replenishments -/

theorem processOneReplenishmentOnCore (st : SystemState) (c : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.processOneReplenishmentOnCore st c scId now) := by
  have hRefill : LendersFrame st (refillSchedContext st scId now) := by
    unfold refillSchedContext
    exact updateSchedContext _ _ _ (fun x => releaseReadyHead_scReply x now) hInv
  unfold _root_.SeLe4n.Kernel.processOneReplenishmentOnCore
  refine LendersFrame.andThen (b := refillWakeOnCore st c scId now) ?_ fun h =>
    of_kept (chainObjectsKept.of_objects_eq (markRefillKeyChange_objects _ _ _))
      (RecordsFrame.of_objects_eq h (markRefillKeyChange_objects _ _ _)
        (markRefillKeyChange_extract_frame SystemState.asidTable _ _ _ fun _ _ => rfl)
        (markRefillKeyChange_extract_frame (fun x : SystemState => x.machine.physicalAddressWidth)
          _ _ _ fun _ _ => rfl))
  unfold refillWakeOnCore
  dsimp only
  split
  · rename_i tid hW
    split
    · exact hRefill
    · refine (hRefill.andThen fun h => wakeThread _ tid c h ?_).andThen fun h => withScheduler _ _ h
      intro x hx
      have hA : ((refillSchedContext st scId now).getTcb? tid).any TCB.isRunnable = true := by
        unfold replenishWakeTarget at hW
        dsimp only at hW
        repeat' split at hW
        all_goals first | cases hW | exact (Option.filter_eq_some_iff.mp hW).2
      rw [hx] at hA
      simp only [Option.any_some, TCB.isRunnable, Bool.and_eq_true, decide_eq_true_eq] at hA
      exact hA.1
  · exact hRefill

theorem processReplenishmentsDueOnCore (st : SystemState) (c : CoreId) (now : Nat)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.processReplenishmentsDueOnCore st c now) := by
  unfold _root_.SeLe4n.Kernel.processReplenishmentsDueOnCore
  exact drainDueOnCore_induction (LendersFrame st) c now
    (fun s scId h => h.andThen fun h' => processOneReplenishmentOnCore s c scId now h')
    (fun s scId h => h.andThen fun h' => releasePlace s c scId h') _ st (refl hInv)

/-! ### The timeouts -/

theorem abortPendingIpcOnEndpoint {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    chainObjectsKept st st' :=
  ⟨fun x r hx => abortPendingIpcOnEndpoint_unwritten_kind_backward (fun o => ∃ r, o = .reply r)
      (fun _ ⟨_, e⟩ => by cases e) (fun _ ⟨_, e⟩ => by cases e) epId isReceiveQ tid st st' hInv h x _
      ⟨r, rfl⟩ hx,
   fun x sc hx => abortPendingIpcOnEndpoint_unwritten_kind_backward
      (fun o => ∃ sc, o = .schedContext sc)
      (fun _ ⟨_, e⟩ => by cases e) (fun _ ⟨_, e⟩ => by cases e) epId isReceiveQ tid st st' hInv h x _
      ⟨sc, rfl⟩ hx,
   bindingViewsShrink_of_objects fun x => by
    cases hx : st'.objects[x]? with
    | none => exact .of_free rfl
    | some o =>
      cases o with
      | tcb t' =>
        obtain ⟨t, ht, hb⟩ := abortPendingIpcOnEndpoint_binding_backward epId isReceiveQ tid st st'
          hInv h x t' hx
        exact .ofTcbBinding ht hb.symm
      | notification n =>
        exact .of_eq (by
          rw [abortPendingIpcOnEndpoint_notification_backward epId isReceiveQ tid st st' hInv h x n hx])
      | schedContext sc =>
        exact .of_eq (by
          rw [abortPendingIpcOnEndpoint_schedContext_backward epId isReceiveQ tid st st' hInv h x sc hx])
      | _ => exact .of_free rfl⟩

theorem unlinkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    LendersFrame st (st.unlinkReplyWaiter w s) :=
  ⟨(chainObjectsKept.of_objectsAgreeOffRunLinks
    (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks st w s)).linksShrink,
   SystemState.unlinkReplyWaiter_objects_invExt st w s hInv⟩

theorem updatePipBoostOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : LendersFrame st (PriorityInheritance.updatePipBoostOnCore st c t) :=
  of_kept ⟨fun x r hx =>
      ((PriorityInheritance.updatePipBoostOnCore_reply_schedContext_iff st c t hInv x).1 r).mp hx,
    fun x sc hx =>
      ((PriorityInheritance.updatePipBoostOnCore_reply_schedContext_iff st c t hInv x).2 sc).mp hx,
    bindingViewsShrink_of_objects fun x => by
      rcases PriorityInheritance.updatePipBoostOnCore_keepsScBindingAt st c t hInv x with
        e | ⟨pre, post, h1, h2, hS, hO⟩
      · exact .of_eq (by rw [e])
      · rw [h2]; exact .ofTcb h1 (.inr ⟨hS, hO⟩)⟩
    (RecordsFrame.updatePipBoostOnCore st c t hInv)

theorem revertPriorityInheritance (st : SystemState) (t : SeLe4n.ThreadId) (fuel : Nat)
    (hInv : st.objects.invExt) :
    LendersFrame st (PriorityInheritance.revertPriorityInheritance st t fuel) := by
  induction fuel generalizing st t with
  | zero => exact refl hInv
  | succ n ih =>
    unfold PriorityInheritance.revertPriorityInheritance
    have F := updatePipBoostOnCore st Concurrency.bootCoreId t hInv
    split
    · exact F.andThen fun h => ih _ _ h
    · exact F

theorem timeoutThread {epId : SeLe4n.ObjId} {isReceiveQ : Bool} {tid : SeLe4n.ThreadId}
    {ec : CoreId} {st : SystemState} {r : SystemState × Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.timeoutThread epId isReceiveQ tid ec st = .ok r) :
    LendersFrame st r.1 := by
  unfold _root_.SeLe4n.Kernel.timeoutThread at h
  split at h
  · cases h
  · rename_i st2 hA
    obtain ⟨S, hRdy⟩ := RecordsStep.abortPendingIpcOnEndpoint hInv hA
    have L0 : LendersFrame st st2 := ⟨(abortPendingIpcOnEndpoint hInv hA).linksShrink, S.invExt⟩
    have L1 := L0.andThen fun h => wakeThread st2 tid ec h hRdy
    dsimp only at h
    split at h
    · rename_i server _
      rw [Except.ok.injEq] at h; subst h
      exact (L1.andThen fun h => unlinkReplyWaiter _ tid server h).andThen
        fun h => revertPriorityInheritance _ _ _ h
    · rw [Except.ok.injEq] at h; subst h; exact L1

end LendersFrame

namespace LendersFrame

/-- The bound-context timeout pass: a fold of timeouts. -/
theorem timeoutBlockedThreads (st : SystemState) (scId : SeLe4n.SchedContextId) (ec : CoreId)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.timeoutBlockedThreads st scId ec).1 := by
  rw [timeoutBlockedThreads_eq_fold]; delta timeoutBlockedThreadStep
  suffices H : ∀ (l : List SeLe4n.ThreadId)
      (acc : SystemState × List (SeLe4n.ThreadId × KernelError) × List (CoreId × Concurrency.SgiKind)),
      LendersFrame st acc.1 →
      LendersFrame st (l.foldl (fun acc tid =>
        let (st', errs, sgis) := acc
        match st'.getTcb? tid with
        | some tcb =>
          match tcbBlockingInfo tcb with
          | some (epId, isReceiveQ) =>
            match _root_.SeLe4n.Kernel.timeoutThread epId isReceiveQ tid ec st' with
            | .ok r => (r.1, errs, sgis ++ r.2.toList)
            | .error e => (st', errs ++ [(tid, e)], sgis)
          | none => (st', errs, sgis)
        | none => (st', errs, sgis)) acc).1 from
    H _ _ (refl hInv)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨s, e, g⟩ := acc
    dsimp only
    split
    · split
      · split
        · rename_i r hT
          exact h.andThen fun h' => timeoutThread h' hT
        · exact h
      · exact h
    · exact h

theorem budgetExhaustOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (ticks : Nat) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.budgetExhaustOnCore st c tid k scId sc hSc ticks) :=
  (((spendBudgetOnCore st c tid scId sc hSc _ ticks hInv).andThen
    fun h => markKeyChangeFor _ tid k h).andThen fun h => timeoutBlockedThreads _ scId c h).andThen
    fun h => withScheduler _ _ h

/-- The tick's charge of a thread: a slice or budget step. -/
theorem timerTickBudgetOnCore {st : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId} {tcb : TCB}
    {hTcb : st.getTcb? tid = some tcb} {r : SystemState × Bool} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.timerTickBudgetOnCore st c tid tcb hTcb = r) : LendersFrame st r.1 := by
  subst h
  unfold _root_.SeLe4n.Kernel.timerTickBudgetOnCore
  split
  · split
    · exact sliceExpireOnCore st c tid tcb hTcb hInv
    · exact rewriteObject_tcb hTcb _ (by rfl) (SystemState.rewriteAdmissible_tcb hTcb _) hInv
  all_goals
    split
    · rename_i sc hSc _
      dsimp only
      split
      · exact budgetExhaustOnCore st c tid _ _ sc hSc 1 hInv
      · exact rewriteObject_schedContext hSc _ (chargeBudget_scReply sc _ _ _)
          (SystemState.rewriteAdmissible_schedContext hSc _) hInv
    · exact refl hInv

/-- **The timer tick keeps the stack views**: the diagnostic clear, the
replenishment drain, the charge (whose exhaustion times out the context's
blocked threads), and the reschedule or the scheduling point. -/
theorem timerTickOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.timerTickOnCore st c) := by
  have hP : LendersFrame st (timerTickOnCorePrepared st c) :=
    (withScheduler st (st.scheduler.setLastTimeoutErrorsOnCore c []) hInv).andThen
      fun h => processReplenishmentsDueOnCore _ c st.machine.timer h
  refine timerTickOnCore_of (P := LendersFrame st) st c hP ?_ ?_ ?_
  · intro s hs
    exact hs.andThen fun h => handleRescheduleSgiOnCore h (handleRescheduleSgiOnCore_eq_state s c)
  · intro s hs
    exact hs.andThen fun h => scheduleEffectiveOnCore h (scheduleEffectiveOnCore_eq_state s c)
  · intro tid tcb hTcb st3 b hb
    exact hP.andThen fun h => timerTickBudgetOnCore h hb

end LendersFrame

namespace LendersFrame

/-- The outgoing thread's re-enqueue at a domain boundary. -/
theorem requeueOutgoingOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.requeueOutgoingOnCore st c) := by
  have F := saveOutgoingContextOnCore st c hInv
  unfold _root_.SeLe4n.Kernel.requeueOutgoingOnCore; dsimp only
  split
  · exact F
  · split
    · split
      · exact F.andThen fun h => runEnqueueAdmitted _ _ _ _ h
      · exact F
    · exact F

theorem switchDomainOnCore {st st' : SystemState} {c : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.switchDomainOnCore st c = .ok st') : LendersFrame st st' := by
  unfold _root_.SeLe4n.Kernel.switchDomainOnCore at h
  split at h
  · cases h; exact refl hInv
  · dsimp only at h
    split at h
    · cases h
    · cases h
      exact (requeueOutgoingOnCore st c hInv).andThen fun h =>
        of_kept (chainObjectsKept.of_objects_eq rfl) (RecordsFrame.of_objects_eq h rfl rfl)

theorem scheduleDomainOnCore {st st' : SystemState} {c : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.scheduleDomainOnCore st c = .ok st') : LendersFrame st st' := by
  unfold _root_.SeLe4n.Kernel.scheduleDomainOnCore at h
  split at h
  · cases h; exact refl hInv
  · split at h
    · split at h
      · cases h
      · rename_i stD hD
        exact (switchDomainOnCore hInv hD).andThen fun h' => scheduleEffectiveOnCore h' h
    · cases h
      exact of_kept (chainObjectsKept.of_objects_eq rfl) (RecordsFrame.of_objects_eq hInv rfl rfl)

/-- The per-core timer step: the clock, the tick, the domain accounting. -/
theorem perCoreTimerTickStep (st : SystemState) (coreId : UInt64) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.perCoreTimerTickStep st coreId).1 := by
  by_cases hc : coreId.toNat < Concurrency.numCores
  · rw [perCoreTimerTickStep_valid_core st coreId hc]
    have hClk : LendersFrame st (tickClockedState st ⟨coreId.toNat, hc⟩) :=
      of_kept (chainObjectsKept.of_objects_eq (tickClockedState_objects _ _))
        (RecordsFrame.of_objects_eq hInv (tickClockedState_objects _ _)
          (by unfold tickClockedState; split <;> rfl) (by unfold tickClockedState; split <;> rfl))
    exact (hClk.andThen fun h => timerTickOnCore _ _ h).andThen fun h =>
      scheduleDomainOnCore h (scheduleDomainOnCore_eq_state _ _)
  · rw [perCoreTimerTickStep_invalid_core st coreId hc]
    exact refl hInv

end LendersFrame

/-- **The timer entry's committed state keeps the lenders' flow**: the trap-frame
save, the tick, the residency settlement, the activation and the ledger drains.
The only premise is the store's invariant at the state the entry runs from. -/
theorem perCoreTimerTickEntryState_lendersStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (hInv : st.objects.invExt) :
    LendersStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) := by
  have F1 := RecordsFrame.saveCapturedTrapFrameAt st coreId frame hInv
  have L := LendersFrame.perCoreTimerTickStep _ coreId F1.invExt
  exact ((LendersStage.of_kept (chainObjectsKept.saveCapturedTrapFrameAt st coreId frame hInv)).trans
    L.stage).trans (LendersStage.entryTail _ coreId L.invExt)

end SeLe4n.Kernel
