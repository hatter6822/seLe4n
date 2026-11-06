/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.CancelAllReachability

/-!
# A finalised server's waiters are all orphaned

WS-ZA ZA5.4 part 25, restated for seL4-MCS's server finalise (WS-ZA ZA6.34): a
thread's final delete leaves every caller waiting on it for a reply blocked on
that reply with no recorded server (`orphanReplyWaiters`), as seL4-MCS leaves a
caller `BlockedOnReply` with `reply->replyTCB` intact once its server's TCB is
gone.  The walk follows the server's live head and re-reads each waiter's guard.
This module proves that the walk never refuses midway: from a state carrying the
finalisation's invariant (`finaliseStepInvariant`) in which the server waits on
no reply of its own, the walk, given at least the server's count as fuel, leaves
no thread waiting on the server (`orphanReplyWaiters_endsAll`).

The argument: one waiter's orphaning writes that waiter's state word (its server
forgotten, `TCB.serverForgotten`) and then the reply-waiter links of it, its
neighbours and the server (`objectsAgreeOffReplyLinks`).  Every other thread
keeps what the walk's guard reads (`TCB.waiterKeyEq`), the orphaned waiter
waits on no server, so the queue loses exactly it (`replyWaitersConsistent`),
and no binding is written (`bindingLinksAgree`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **What a waiter's guard reads of its TCB**, compared: the two IPC
codes (its blocking state and server), its reply link, its endpoint-queue links
and its timeout budget; and, for the server whose waiters are ended, the rest of
what its quiescence reads that no waiter's end writes: its endpoint-queue back
link, its bound-notification code and its own id. -/
def TCB.waiterKeyEq (a b : TCB) : Prop :=
  a.ipcObjectCode = b.ipcObjectCode ∧ a.ipcStateCode = b.ipcStateCode ∧
    a.replyObjectCode = b.replyObjectCode ∧ a.queueNextCode = b.queueNextCode ∧
    a.queuePrevCode = b.queuePrevCode ∧ a.timeoutBudget = b.timeoutBudget ∧
    a.queuePPrevCode = b.queuePPrevCode ∧ a.boundNotificationCode = b.boundNotificationCode ∧
    a.tid = b.tid

namespace TCB.waiterKeyEq

theorem refl (a : TCB) : TCB.waiterKeyEq a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem symm {a b : TCB} (h : TCB.waiterKeyEq a b) : TCB.waiterKeyEq b a := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm⟩

theorem trans {a b c : TCB} (h₁ : TCB.waiterKeyEq a b) (h₂ : TCB.waiterKeyEq b c) :
    TCB.waiterKeyEq a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h₂
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7, a8.trans b8, a9.trans b9⟩

theorem ipcState {a b : TCB} (h : TCB.waiterKeyEq a b) : a.ipcState = b.ipcState := by
  show ThreadIpcState.ofCodes a.ipcObjectCode a.ipcStateCode =
    ThreadIpcState.ofCodes b.ipcObjectCode b.ipcStateCode
  rw [h.1, h.2.1]

theorem blockingServer {a b : TCB} (h : TCB.waiterKeyEq a b) :
    a.blockingServer? = b.blockingServer? := by
  unfold TCB.blockingServer?; rw [h.ipcState]

/-- Two threads agreeing off their run-queue fields agree on the key. -/
theorem of_withoutRunLinks {a b : TCB} (h : a.withoutRunLinks = b.withoutRunLinks) :
    TCB.waiterKeyEq a b :=
  ⟨by have e := congrArg TCB.ipcObjectCode h; exact e,
    by have e := congrArg TCB.ipcStateCode h; exact e,
    by have e := congrArg TCB.replyObjectCode h; exact e,
    by have e := congrArg TCB.queueNextCode h; exact e,
    by have e := congrArg TCB.queuePrevCode h; exact e,
    by have e := congrArg TCB.timeoutBudget h; exact e,
    by have e := congrArg TCB.queuePPrevCode h; exact e,
    by have e := congrArg TCB.boundNotificationCode h; exact e,
    by have e := congrArg TCB.tid h; exact e⟩

/-- ...and so do two agreeing off their reply-waiter links. -/
theorem of_withoutReplyLinks {a b : TCB} (h : a.withoutReplyLinks = b.withoutReplyLinks) :
    TCB.waiterKeyEq a b :=
  ⟨by have e := congrArg TCB.ipcObjectCode h; exact e,
    by have e := congrArg TCB.ipcStateCode h; exact e,
    by have e := congrArg TCB.replyObjectCode h; exact e,
    by have e := congrArg TCB.queueNextCode h; exact e,
    by have e := congrArg TCB.queuePrevCode h; exact e,
    by have e := congrArg TCB.timeoutBudget h; exact e,
    by have e := congrArg TCB.queuePPrevCode h; exact e,
    by have e := congrArg TCB.boundNotificationCode h; exact e,
    by have e := congrArg TCB.tid h; exact e⟩

end TCB.waiterKeyEq

-- ============================================================================
-- The frame one waiter's end keeps
-- ============================================================================

/-- **A step that keeps every thread off `E` up to what a waiter's guard
reads**: its key (both ways) and a zero run-core code; and every reply heading
no stack whose caller is off `E`, exactly. -/
structure WaiterFrame (st st' : SystemState) (E : SeLe4n.ThreadId → Prop) : Prop where
  fwd : ∀ (v : SeLe4n.ThreadId) (t : TCB), ¬ E v → st.getTcb? v = some t →
    ∃ t', st'.getTcb? v = some t' ∧ TCB.waiterKeyEq t' t ∧ (t.runCoreCode = 0 → t'.runCoreCode = 0)
  bwd : ∀ (v : SeLe4n.ThreadId) (t' : TCB), ¬ E v → st'.getTcb? v = some t' →
    ∃ t, st.getTcb? v = some t ∧ TCB.waiterKeyEq t' t
  reply : ∀ (k : SeLe4n.ObjId) (r : Reply), st.getObject? k = some (.reply r) → r.next = none →
    (∀ e, E e → r.callerCode ≠ e.val + 1) → st'.getObject? k = some (.reply r)

namespace WaiterFrame

theorem refl (st : SystemState) (E : SeLe4n.ThreadId → Prop) : WaiterFrame st st E :=
  ⟨fun _ t _ h => ⟨t, h, .refl t, id⟩, fun _ t _ h => ⟨t, h, .refl t⟩, fun _ _ h _ _ => h⟩

theorem trans {a b c : SystemState} {E : SeLe4n.ThreadId → Prop} (h₁ : WaiterFrame a b E)
    (h₂ : WaiterFrame b c E) : WaiterFrame a c E := by
  refine ⟨fun v t hv ht => ?_, fun v t hv ht => ?_, fun k r hk hn hc => ?_⟩
  · obtain ⟨m, hm, km, zm⟩ := h₁.fwd v t hv ht
    obtain ⟨n, hn, kn, zn⟩ := h₂.fwd v m hv hm
    exact ⟨n, hn, kn.trans km, fun z => zn (zm z)⟩
  · obtain ⟨m, hm, km⟩ := h₂.bwd v t hv ht
    obtain ⟨n, hn, kn⟩ := h₁.bwd v m hv hm
    exact ⟨n, hn, km.trans kn⟩
  · exact h₂.reply k r (h₁.reply k r hk hn hc) hn hc

/-- A frame for a smaller exclusion is one for a larger. -/
theorem mono {a b : SystemState} {E E' : SeLe4n.ThreadId → Prop} (h : WaiterFrame a b E)
    (hE : ∀ v, E v → E' v) : WaiterFrame a b E' :=
  ⟨fun v t hv ht => h.fwd v t (fun e => hv (hE v e)) ht,
    fun v t hv ht => h.bwd v t (fun e => hv (hE v e)) ht,
    fun k r hk hn hc => h.reply k r hk hn (fun e he => hc e (hE e he))⟩

theorem of_objects_eq {a b : SystemState} (E : SeLe4n.ThreadId → Prop)
    (h : b.objects = a.objects) : WaiterFrame a b E := by
  have hT : ∀ v, b.getTcb? v = a.getTcb? v := fun v => by unfold SystemState.getTcb?; rw [h]
  have hO : ∀ k, b.getObject? k = a.getObject? k := fun k => by
    unfold SystemState.getObject?; rw [h]
  refine ⟨fun v t _ ht => ⟨t, (hT v).trans ht, .refl t, id⟩,
    fun v t _ ht => ⟨t, (hT v).symm.trans ht, .refl t⟩, fun k r hk _ _ => (hO k).trans hk⟩

/-- **A step writing contexts' release fields alone keeps every thread and every
reply** (the replenishment migration). -/
theorem of_agreeOffReleaseLinks {a b : SystemState} (E : SeLe4n.ThreadId → Prop)
    (h : SystemState.objectsAgreeOffReleaseLinks b a) : WaiterFrame a b E :=
  ⟨fun v t _ ht => ⟨t, (h.getTcb? v).trans ht, .refl t, id⟩,
    fun v t _ ht => ⟨t, (h.getTcb? v).symm.trans ht, .refl t⟩,
    fun _ _ hk _ _ => h.get_of_not_sc (fun _ e => KernelObject.noConfusion e) hk⟩

/-- **A step agreeing off the reply-waiter links keeps every thread** (a
reply-waiter unlink). -/
theorem of_agreeOffReplyLinks {a b : SystemState} (E : SeLe4n.ThreadId → Prop)
    (h : SystemState.objectsAgreeOffReplyLinks b a) : WaiterFrame a b E := by
  refine ⟨fun v t _ ht => ?_, fun v t _ ht => ?_, fun k r hk _ _ => ?_⟩
  · obtain ⟨t', h', e⟩ := h.get_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht)
    exact ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h', .of_withoutReplyLinks e,
      fun z => by have e' := congrArg TCB.runCoreCode e; exact e'.trans z⟩
  · obtain ⟨t0, h0, e⟩ := h.get_tcb' ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht)
    exact ⟨t0, (SystemState.getTcb?_eq_some_iff _ _ _).mpr h0, .of_withoutReplyLinks e⟩
  · exact h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e) hk

end WaiterFrame

theorem threadId_toObjId_ne {v w : SeLe4n.ThreadId} (h : v ≠ w) : w.toObjId ≠ v.toObjId := by
  intro e
  apply h
  cases v; cases w
  simp only [SeLe4n.ThreadId.toObjId, SeLe4n.ThreadId.toNat, SeLe4n.ObjId.ofNat,
    SeLe4n.ObjId.mk.injEq] at e
  rw [e]

namespace WaiterFrame

/-- **A TCB update of `w` keeps every other thread and every reply.** -/
theorem updateTcb (st : SystemState) (w : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) : WaiterFrame st (st.updateTcb w f) (· = w) := by
  refine ⟨fun v t hv ht => ?_, fun v t hv ht => ?_, fun k r hk _ _ => ?_⟩
  · refine ⟨t, ?_, .refl t, id⟩
    rw [SystemState.updateTcb_getTcb?_ne st w f hInv v (threadId_toObjId_ne hv)]; exact ht
  · refine ⟨t, ?_, .refl t⟩
    rw [← SystemState.updateTcb_getTcb?_ne st w f hInv v (threadId_toObjId_ne hv)]; exact ht
  · by_cases hkw : w.toObjId = k
    · subst hkw
      have hN : st.getTcb? w = none := by
        unfold SystemState.getTcb?
        unfold SystemState.getObject? at hk
        rw [hk]
      rw [SystemState.updateTcb_eq_self_of_none hN]; exact hk
    · unfold SystemState.getObject? at hk ⊢
      rw [SystemState.updateTcb_objects_ne st w f k hkw hInv]; exact hk

end WaiterFrame

-- ============================================================================
-- The priority-inheritance walk keeps every thread off the run queues off them
-- ============================================================================

open SeLe4n.Kernel.Concurrency (CoreId) in
/-- **A boost keeps a thread off every run queue off them**: its object write
rewrites the holder's `pipBoost` alone, and its bucket re-key moves only a
holder already queued on the core, whose run-core code is not zero. -/
theorem updatePipBoostOnCore_runCoreCode_zero (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (y : SeLe4n.ThreadId) (t : TCB)
    (hT : st.getTcb? y = some t) (h0 : t.runCoreCode = 0) :
    ∃ t', (PriorityInheritance.updatePipBoostOnCore st c tid).getTcb? y = some t' ∧
      t'.runCoreCode = 0 := by
  have hMark : ∀ (S : SystemState) k, (markKeyChangeFor S tid k).getTcb? y = S.getTcb? y :=
    fun S k => by unfold SystemState.getTcb?; rw [markKeyChangeFor_objects]
  cases hTid : st.getTcb? tid with
  | none =>
    unfold PriorityInheritance.updatePipBoostOnCore
    rw [SystemState.getTcbWitnessed?_eq_none hTid]
    exact ⟨t, hT, h0⟩
  | some tcb =>
    have hRw : ∀ (new : TCB) (hA : st.rewriteAdmissible tid.toObjId (.tcb new)),
        new.runCoreCode = tcb.runCoreCode →
        ∃ t', (st.rewriteObject tid.toObjId (.tcb new) hA).getTcb? y = some t' ∧
          t'.runCoreCode = 0 := by
      intro new hA hNew
      by_cases hy : tid.toObjId = y.toObjId
      · have hyt : y = tid :=
          Classical.byContradiction fun hne => threadId_toObjId_ne hne hy
        subst hyt
        rw [hTid] at hT; cases hT
        refine ⟨new, ?_, hNew.trans h0⟩
        rw [SystemState.getTcb?_eq_some_iff]
        exact SystemState.rewriteObject_objects_self _ _ _ hA hInv
      · exact ⟨t, by rw [SystemState.rewriteObject_getTcb?_ne _ _ _ hA hInv y hy]; exact hT, h0⟩
    unfold PriorityInheritance.updatePipBoostOnCore
    simp only [SystemState.getTcbWitnessed?_eq_some hTid]
    split
    · exact ⟨t, hT, h0⟩
    · split
      · rename_i hQ
        split
        · have hyt : y ≠ tid := by
            intro e; subst e
            rw [hTid] at hT; cases hT
            unfold SystemState.queuedOn at hQ; rw [hTid] at hQ
            simp only [beq_iff_eq] at hQ; omega
          have hReq : ∀ (S : SystemState) (p : SeLe4n.Priority),
              (∃ t1, S.getTcb? y = some t1 ∧ t1.runCoreCode = 0) →
              ∃ t2, (S.runRequeueOnCore c tid p).getTcb? y = some t2 ∧ t2.runCoreCode = 0 := by
            intro S p ⟨t1, h1, zeroA⟩
            have hM := SystemState.runRequeueOnCore_runCoreCode_ne S c tid y p hyt
            rw [h1] at hM
            cases h2 : (S.runRequeueOnCore c tid p).getTcb? y with
            | none => rw [h2] at hM; cases hM
            | some t2 =>
              rw [h2] at hM
              simp only [Option.map_some, Option.some.injEq] at hM
              exact ⟨t2, rfl, hM.trans zeroA⟩
          rw [hMark]; exact hReq _ _ (hRw _ _ rfl)
        · rw [hMark]; exact hRw _ _ rfl
      · rw [hMark]; exact hRw _ _ rfl

open SeLe4n.Kernel.Concurrency (CoreId) in
/-- ...and so does the whole chain walk, by induction on the fuel. -/
theorem propagatePipChainCrossCore_runCoreCode_zero (ec : CoreId) :
    ∀ (fuel : Nat) (st : SystemState) (tid : SeLe4n.ThreadId), st.objects.invExt →
      ∀ (y : SeLe4n.ThreadId) (t : TCB), st.getTcb? y = some t → t.runCoreCode = 0 →
      ∃ t', (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1.getTcb? y = some t' ∧
        t'.runCoreCode = 0
  | 0, st, _, _, _, t, hT, h0 => ⟨t, hT, h0⟩
  | n + 1, st, tid, hInv, y, t, hT, h0 => by
    rw [PriorityInheritance.propagatePipChainCrossCore_step]
    have hB := PriorityInheritance.pipBoostWithWake_preserves_objects_invExt st tid ec hInv
    obtain ⟨t1, h1, zeroA⟩ := updatePipBoostOnCore_runCoreCode_zero st
      (determineTargetCore st tid) tid hInv y t hT h0
    simp only
    split
    · exact propagatePipChainCrossCore_runCoreCode_zero ec n _ _ hB y t1 h1 zeroA
    · exact ⟨t1, h1, zeroA⟩

namespace WaiterFrame

open SeLe4n.Kernel.Concurrency (CoreId) in
/-- **The priority-inheritance walk keeps every thread and every reply**: it
rewrites `pipBoost` and run links alone (`propagatePipChainCrossCore_tcb_backward`),
keeps a thread off the run queues off them, and writes no reply. -/
theorem propagate (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (fuel : Nat)
    (hInv : st.objects.invExt) (E : SeLe4n.ThreadId → Prop) :
    WaiterFrame st (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1 E := by
  have hBack : ∀ (v : SeLe4n.ThreadId) (t' : TCB),
      (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1.getTcb? v = some t' →
      ∃ t, st.getTcb? v = some t ∧ TCB.waiterKeyEq t' t := by
    intro v t' ht'
    obtain ⟨t, p, hPre, hEq⟩ := PriorityInheritance.propagatePipChainCrossCore_tcb_backward st tid
      ec fuel hInv v t' ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht')
    have k := TCB.waiterKeyEq.of_withoutRunLinks hEq
    exact ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hPre, k⟩
  refine ⟨fun v t _ ht => ?_, fun v t' _ ht' => hBack v t' ht', fun k r hk _ _ => ?_⟩
  · have hS := PriorityInheritance.propagatePipChainCrossCore_getTcb?_isSome fuel st tid ec hInv v
      (by rw [ht]; rfl)
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp hS
    obtain ⟨t0, h0, k0⟩ := hBack v t' ht'
    rw [ht] at h0; cases h0
    refine ⟨t', ht', k0, fun z => ?_⟩
    obtain ⟨t2, h2, zeroB⟩ := propagatePipChainCrossCore_runCoreCode_zero ec fuel st tid hInv v t ht z
    rw [ht'] at h2; cases h2; exact zeroB
  · unfold SystemState.getObject? at hk ⊢
    rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st tid ec hInv k with
      e | ⟨pre, -, hp, -, -, -, -⟩
    · rw [e]; exact hk
    · rw [hk] at hp; cases hp

end WaiterFrame

namespace WaiterFrame

/-- **A deschedule keeps every other thread and every reply**: it writes run
links alone, and moves no other thread on or off a run queue. -/
theorem descheduleAtPlacement (st : SystemState) (w : SeLe4n.ThreadId) (E : SeLe4n.ThreadId → Prop) :
    WaiterFrame st (SeLe4n.Kernel.descheduleAtPlacement st w) E := by
  have hA := descheduleAtPlacement_objectsAgreeOffRunLinks st w
  have hRun : ∀ y t, st.getTcb? y = some t → t.runCoreCode = 0 →
      ((SeLe4n.Kernel.descheduleAtPlacement st w).getTcb? y).map TCB.runCoreCode =
        (st.getTcb? y).map TCB.runCoreCode := by
    intro y t ht z
    unfold SeLe4n.Kernel.descheduleAtPlacement descheduleAt
    split
    · rename_i c _
      by_cases hy : y = w
      · subst hy
        have hq : (st.runLinkOn c y).queued = false := by
          rw [← SystemState.queuedOn_eq_runLinkOn]
          unfold SystemState.queuedOn; rw [ht]
          simp [z]
        show ((st.runDescheduleOnCore c y).getTcb? y).map TCB.runCoreCode = _
        have h := SystemState.runRemoveOnCore_objects st c y
        rw [if_neg (by rw [hq]; exact Bool.false_ne_true)] at h
        rw [show (st.runDescheduleOnCore c y).getTcb? y = (st.runRemoveOnCore c y).getTcb? y from rfl,
          SystemState.getTcb?_frame h]
      · exact SystemState.runRemoveOnCore_runCoreCode_ne st c w y hy
    · rfl
  refine ⟨fun v t _ ht => ?_, fun v t' _ ht' => ?_, fun k r hk _ _ => ?_⟩
  · obtain ⟨t', h', e⟩ := hA.getTcb?_some ht
    refine ⟨t', h', .of_withoutRunLinks e, fun z => ?_⟩
    have hM := hRun v t ht z
    rw [h', ht] at hM
    simp only [Option.map_some, Option.some.injEq] at hM
    exact hM.trans z
  · obtain ⟨t, h0, e⟩ := hA.get_tcb' ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht')
    exact ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mpr h0, .of_withoutRunLinks e⟩
  · unfold SystemState.getObject? at hk ⊢
    exact hA.get_of_not_tcb (fun _ e => KernelObject.noConfusion e) hk

end WaiterFrame

namespace WaiterFrame

/-- **A consume of `w`'s reply link keeps every other thread and every other
reply**: it writes `w`'s reply and `w`. -/
theorem consumeReplyLink (st : SystemState) (w : SeLe4n.ThreadId) (t tw : TCB)
    (hInv : st.objects.invExt) (rid : SeLe4n.ReplyId) (r : Reply)
    (hRO : t.replyObject = some rid) (hR : st.objects[rid.toObjId]? = some (.reply r))
    (hC : r.callerCode = w.val + 1) (hW : st.getTcb? w = some tw) :
    WaiterFrame st (Lifecycle.Suspend.consumeReplyLink st w t) (· = w) := by
  rw [Lifecycle.Suspend.consumeReplyLink_some st w t rid hRO]
  have hStep := SystemState.consumeCallerReply_eq_link st w rid
  have hWo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hW
  refine ⟨fun v t0 hv ht => ?_, fun v t' hv ht' => ?_, fun k r' hk _ hc => ?_⟩
  · have ht0 := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht
    have hvR : v.toObjId ≠ rid.toObjId := fun e => by rw [e, hR] at ht0; cases ht0
    refine ⟨t0, (SystemState.getTcb?_eq_some_iff _ _ _).mpr ?_, .refl t0, id⟩
    exact SystemState.consumeCallerReply_tcb_other st _ w rid hInv hStep v.toObjId t0
      (threadId_toObjId_ne hv).symm ht0
  · have ht0 := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht'
    have hvR : v.toObjId ≠ rid.toObjId := by
      intro e
      obtain ⟨r'', hr''⟩ := SystemState.consumeCallerReply_getReply?_isSome st _ w rid hInv hStep rid r
        (by unfold SystemState.getReply?; rw [hR])
      unfold SystemState.getReply? at hr''
      rw [← e, ht0] at hr''; cases hr''
    refine ⟨t', ?_, .refl t'⟩
    rw [SystemState.getTcb?_eq_some_iff, ← consumeCallerReply_objects_frame st _ w rid hInv hStep
      v.toObjId hvR (threadId_toObjId_ne hv).symm]
    exact ht0
  · unfold SystemState.getObject? at hk ⊢
    have hkR : k ≠ rid.toObjId := fun e => by
      rw [e, hR] at hk; cases hk; exact hc w rfl hC
    have hkW : k ≠ w.toObjId := fun e => by rw [e, hWo] at hk; cases hk
    rw [consumeCallerReply_objects_frame st _ w rid hInv hStep k hkR hkW]; exact hk

end WaiterFrame

/-- **The removal of a reply heading no stack**: on a state where its caller is
finalisable, the caller is blocked on the reply, hands nothing back, and the
removal is the splice, restore, consume and unlink on the state itself, then the
revert. -/
theorem finaliseReplyRevertCancel_noHead (st : SystemState) {x : SeLe4n.ObjId}
    {c : SeLe4n.ThreadId} {t : TCB} {r : Reply}
    (hR : st.getObject? x = some (.reply r))
    (hNH : replyStackLinkIsHead r.next = false)
    (hF : replyCallerFinalisable st x r c t = true) :
    (∃ ep rt, t.ipcState = .blockedOnReply ep rt) ∧
      t.replyObject = some ⟨x.val⟩ ∧
      Lifecycle.Suspend.cancelledCallerDonation? st c t = none ∧
      finaliseReplyRevert (finaliseReplyCancel st r c t) t.blockingServer? = finaliseReplyRevert
        (SystemState.unlinkReplyWaiterOpt
          (Lifecycle.Suspend.consumeReplyLink
            (Lifecycle.Suspend.restoreToReadyCancelled (cutThreadReplyFrameOut st t) c) c t)
          c t.blockingServer?) t.blockingServer? := by
  obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, hRO, -, -, -⟩ := replyCallerFinalisable_parts hF
  have hD : Lifecycle.Suspend.cancelledCallerDonation? st c t = none := by
    rcases replyCallerFinalisable_cases hR hF with ⟨-, hD⟩ | ⟨s, -, -, -, hN, -⟩
    · exact hD
    · rw [hN] at hNH; cases hNH
  refine ⟨⟨ep, rt, hB⟩, hRO, hD, ?_⟩
  unfold finaliseReplyCancel
  rw [hNH]
  simp only [Bool.false_eq_true, if_false]
  rw [cancelIpcBlocking_replyArm_of_noDonation st c t hB hD]

/-- **The removal of a reply heading no stack writes no binding.** -/
theorem finaliseReplyRevertCancel_noHead_schedLinkFrame (st : SystemState)
    (hInv : st.objects.invExt) {x : SeLe4n.ObjId} {c : SeLe4n.ThreadId} {t : TCB} {r : Reply}
    (hR : st.getObject? x = some (.reply r))
    (hNH : replyStackLinkIsHead r.next = false)
    (hF : replyCallerFinalisable st x r c t = true) :
    SchedLinkFrame st (finaliseReplyRevert (finaliseReplyCancel st r c t) t.blockingServer?) ∧
      (finaliseReplyRevert (finaliseReplyCancel st r c t) t.blockingServer?).objects.invExt := by
  obtain ⟨⟨ep, rt, hB⟩, -, hD, hEq⟩ := finaliseReplyRevertCancel_noHead st hR hNH hF
  rw [hEq]
  have F := SchedLinkFrame.replyCancelTail st c t hInv
  have hI : (SystemState.unlinkReplyWaiterOpt
      (Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled (cutThreadReplyFrameOut st t) c) c t)
      c t.blockingServer?).objects.invExt := by
    rw [← cancelIpcBlocking_replyArm_of_noDonation st c t hB hD]
    exact Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st c t hInv
  exact ⟨F.trans (SchedLinkFrame.finaliseReplyRevert _ _ hI),
    (FinaliseFrame.finaliseReplyRevert _ _ hI).invExt⟩

-- ============================================================================
-- The walk ends every waiter
-- ============================================================================

/-- A thread waits on `x` in the views exactly when its TCB names `x` as its
server. -/
theorem waiterOf_iff {st : SystemState} {v x : SeLe4n.ThreadId} :
    ReplyViews.waiterOf st.replyViews v x ↔ ∃ t, st.getTcb? v = some t ∧ t.blockingServer? = some x := by
  constructor
  · rintro ⟨vv, hv, hs⟩
    obtain ⟨t, ht, e⟩ := SystemState.tcb_of_replyViews hv
    refine ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mpr ht, ?_⟩
    rw [← e] at hs; exact hs
  · rintro ⟨t, ht, hs⟩
    exact ⟨t.replyView, SystemState.replyViews_of_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht), hs⟩

/-- A list of distinct members of `m` is no longer than `m`. -/
theorem length_le_of_nodup_sub : ∀ {l' m : List SeLe4n.ThreadId}, l'.Nodup →
    (∀ a ∈ l', a ∈ m) → l'.length ≤ m.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l', m, hN, hs => by
    have hN' := List.nodup_cons.mp hN
    have ha : a ∈ m := hs a (List.mem_cons_self ..)
    have ih := length_le_of_nodup_sub (m := m.erase a) hN'.2 (fun b hb =>
      (List.mem_erase_of_ne (fun (e : b = a) => hN'.1 (e ▸ hb))).mpr (hs b (List.mem_cons_of_mem _ hb)))
    rw [List.length_erase_of_mem ha] at ih
    have h2 : 0 < m.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- A list of distinct members of `l`, none of them `w ∈ l`, is shorter than `l`. -/
theorem length_lt_of_nodup_sub {l l' : List SeLe4n.ThreadId} {w : SeLe4n.ThreadId}
    (hN : l'.Nodup) (hw : w ∈ l) (hs : ∀ a ∈ l', a ∈ l ∧ a ≠ w) : l'.length + 1 ≤ l.length := by
  have h1 := length_le_of_nodup_sub (m := l.erase w) hN
    (fun a ha => (List.mem_erase_of_ne (hs a ha).2).mpr (hs a ha).1)
  rw [List.length_erase_of_mem hw] at h1
  have h2 : 0 < l.length := List.length_pos_of_mem hw
  omega

/-- **A step keeps the server `x`**: what its quiescence reads that no waiter's
end writes (`TCB.waiterKeyEq`), and a zero run-core code. -/
def serverKept (s s' : SystemState) (x : SeLe4n.ThreadId) : Prop :=
  ∀ tx, s.getTcb? x = some tx →
    ∃ tx', s'.getTcb? x = some tx' ∧ TCB.waiterKeyEq tx' tx ∧ (tx.runCoreCode = 0 → tx'.runCoreCode = 0)

theorem serverKept.refl (s : SystemState) (x : SeLe4n.ThreadId) : serverKept s s x :=
  fun tx h => ⟨tx, h, .refl tx, id⟩

theorem serverKept.trans {a b c : SystemState} {x : SeLe4n.ThreadId} (h₁ : serverKept a b x)
    (h₂ : serverKept b c x) : serverKept a c x := by
  intro tx h
  obtain ⟨m, hm, km, zm⟩ := h₁ tx h
  obtain ⟨n, hn, kn, zn⟩ := h₂ m hm
  exact ⟨n, hn, kn.trans km, fun z => zn (zm z)⟩

/-- A frame excluding a thread other than `x` keeps `x`. -/
theorem WaiterFrame.serverKept {a b : SystemState} {E : SeLe4n.ThreadId → Prop}
    (h : WaiterFrame a b E) {x : SeLe4n.ThreadId} (hx : ¬ E x) : serverKept a b x :=
  fun tx hX => h.fwd x tx hx hX

/-- The boost revert keeps every thread and every reply, and the store's
invariant. -/
theorem finaliseReplyRevert_frame (s : SystemState) (hInv : s.objects.invExt)
    (o : Option SeLe4n.ThreadId) (E : SeLe4n.ThreadId → Prop) :
    WaiterFrame s (finaliseReplyRevert s o) E ∧ (finaliseReplyRevert s o).objects.invExt := by
  cases o with
  | none => exact ⟨.refl _ _, hInv⟩
  | some y =>
    exact ⟨WaiterFrame.propagate s y Concurrency.bootCoreId s.objectIndex.length hInv E,
      PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt s y
        Concurrency.bootCoreId s.objectIndex.length hInv⟩

-- ============================================================================
-- The orphan walk ends every waiter
-- ============================================================================

namespace WaiterFrame

/-- **An in-place write of `w` keeps every other thread and every reply.** -/
theorem mapTcbInPlace (st : SystemState) (w : SeLe4n.ThreadId) (g : TCB → TCB) :
    WaiterFrame st (st.mapTcbInPlace w g) (· = w) := by
  refine ⟨fun v t hv ht => ⟨t, ?_, .refl t, id⟩, fun v t hv ht => ⟨t, ?_, .refl t⟩,
    fun k r hk _ _ => ?_⟩
  · rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ (threadId_toObjId_ne hv)]; exact ht
  · rw [← SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ (threadId_toObjId_ne hv)]; exact ht
  · unfold SystemState.getObject? at hk ⊢
    rw [SystemState.objects_mapTcbInPlace]
    split
    · rw [hk]; rfl
    · exact hk

/-- **One waiter's orphaning keeps every other thread and every reply**: the
server-forget write of `w`, then the unlink, off the reply-waiter links. -/
theorem orphanReplyWaiter (st : SystemState) (w x : SeLe4n.ThreadId) :
    WaiterFrame st (SeLe4n.Kernel.orphanReplyWaiter st w x) (· = w) :=
  (WaiterFrame.mapTcbInPlace st w TCB.serverForgotten).trans
    (WaiterFrame.of_agreeOffReplyLinks _
      (SystemState.unlinkReplyWaiter_objectsAgreeOffReplyLinks _ w x))

end WaiterFrame

/-- **An orphaned waiter waits on no server**: its state word names none, and the
unlink writes reply-waiter links alone. -/
theorem orphanReplyWaiter_forgets (st : SystemState) (w x : SeLe4n.ThreadId) {t : TCB}
    (hT : st.getTcb? w = some t) :
    ∀ t', (orphanReplyWaiter st w x).getTcb? w = some t' → t'.blockingServer? = none := by
  intro t' ht'
  obtain ⟨t0, h0, k⟩ := (WaiterFrame.of_agreeOffReplyLinks (fun _ => False)
    (SystemState.unlinkReplyWaiter_objectsAgreeOffReplyLinks
      (st.mapTcbInPlace w TCB.serverForgotten) w x)).bwd w t' (fun h => h) ht'
  rw [SystemState.mapTcbInPlace_getTcb?_self, hT] at h0
  cases h0
  rw [k.blockingServer]; rfl

/-- The walk at a server whose head code is zero stops. -/
theorem orphanReplyWaiters_headZero {x : SeLe4n.ThreadId} {n : Nat} {s : SystemState} {tx : TCB}
    (hX : s.getTcb? x = some tx) (hH : tx.replyWaitersHeadCode = 0) :
    orphanReplyWaiters x (n + 1) s = s := by
  show (match s.getTcb? x with
    | some tx => match tx.replyWaitersHeadCode with
      | 0 => s
      | k + 1 => match s.getTcb? ⟨k⟩ with
        | some t => if k != x.val && replyCallerServerCode t == x.val + 1 then
            orphanReplyWaiters x n (orphanReplyWaiter s ⟨k⟩ x) else s
        | none => s
    | none => s) = s
  rw [hX]; simp only [hH]

/-- The walk at a server headed by another thread waiting on it orphans that
thread and goes on. -/
theorem orphanReplyWaiters_headStep {x : SeLe4n.ThreadId} {n k : Nat} {s : SystemState}
    {tx t : TCB} (hX : s.getTcb? x = some tx) (hH : tx.replyWaitersHeadCode = k + 1)
    (hT : s.getTcb? ⟨k⟩ = some t) (hk : k ≠ x.val) (hS : replyCallerServerCode t = x.val + 1) :
    orphanReplyWaiters x (n + 1) s = orphanReplyWaiters x n (orphanReplyWaiter s ⟨k⟩ x) := by
  have hG : (k != x.val && replyCallerServerCode t == x.val + 1) = true := by
    simp [hS, hk]
  show (match s.getTcb? x with
    | some tx => match tx.replyWaitersHeadCode with
      | 0 => s
      | k + 1 => match s.getTcb? ⟨k⟩ with
        | some t => if k != x.val && replyCallerServerCode t == x.val + 1 then
            orphanReplyWaiters x n (orphanReplyWaiter s ⟨k⟩ x) else s
        | none => s
    | none => s) = _
  rw [hX]; simp only [hH, hT, hG, if_true]

/-- **The orphan walk never refuses midway** (WS-ZA ZA5.4 part 25, restated for
seL4-MCS's server finalise): from a state carrying the finalisation's invariant
in which `x` waits on no reply of its own, the walk, with at least `x`'s count
as fuel, orphans every thread waiting on `x` — none waits on `x` after it.  Each
step orphans the queue's head (a waiter of `x` other than `x`, so its guard
admits it), keeps every other thread (`WaiterFrame.orphanReplyWaiter`), and
shortens the queue (`replyWaitersConsistent`, `length_lt_of_nodup_sub`).  It
keeps `x` itself (`serverKept`), and writes no binding (`bindingLinksAgree`):
an orphaned caller keeps whatever context it held. -/
theorem orphanReplyWaiters_endsAll (x : SeLe4n.ThreadId) :
    ∀ (n : Nat) (s : SystemState), finaliseStepInvariant s →
      (∀ tx, s.getTcb? x = some tx → tx.blockingServer? ≠ some x) →
      (∃ tx, s.getTcb? x = some tx ∧ tx.replyWaitersCount ≤ n) →
      (∀ v, ¬ ReplyViews.waiterOf (orphanReplyWaiters x n s).replyViews v x) ∧
        serverKept s (orphanReplyWaiters x n s) x ∧
        bindingLinksAgree s (orphanReplyWaiters x n s) := by
  intro n
  induction n with
  | zero =>
    intro s h _ ⟨tx, hX, hC⟩
    refine ⟨fun v hv => ?_, serverKept.refl s x, fun _ => rfl⟩
    obtain ⟨l, -, hLen, -, hMem⟩ := h.2.2.2.1.1 x tx.replyView
      (SystemState.replyViews_of_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hX))
    have hl : l = [] := List.eq_nil_of_length_eq_zero (by
      rw [hLen]; show tx.replyWaitersCount = 0; omega)
    subst hl
    exact List.not_mem_nil ((hMem v).mpr hv)
  | succ n ih =>
    intro s h hNx ⟨tx, hX, hC⟩
    obtain ⟨l, hCh, hLen, hNd, hMem⟩ := h.2.2.2.1.1 x tx.replyView
      (SystemState.replyViews_of_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hX))
    cases l with
    | nil =>
      have hH : tx.replyWaitersHeadCode = 0 :=
        (SeLe4n.ThreadId.ofOptCode_eq_none_iff _).mp hCh
      rw [orphanReplyWaiters_headZero hX hH]
      exact ⟨fun v hv => List.not_mem_nil ((hMem v).mpr hv), serverKept.refl s x, fun _ => rfl⟩
    | cons w l' =>
      have hH : tx.replyWaitersHeadCode = w.val + 1 := by
        have hc := hCh.1
        revert hc
        show SeLe4n.ThreadId.ofOptCode tx.replyWaitersHeadCode = some w → _
        cases tx.replyWaitersHeadCode with
        | zero => intro e; cases e
        | succ k => intro e; cases e; rfl
      obtain ⟨t, hT, hsw⟩ := waiterOf_iff.mp ((hMem w).mp (List.mem_cons_self ..))
      have hxw : ¬ x = w := by
        intro e; subst e; rw [hX] at hT; cases hT; exact hNx _ hX hsw
      have hwx : w.val ≠ x.val := fun e => hxw (by cases w; cases x; simp only at e; rw [e])
      have hS : replyCallerServerCode t = x.val + 1 := by
        unfold replyCallerServerCode; rw [hsw]
      rw [orphanReplyWaiters_headStep hX hH hT hwx hS]
      have h' := (h.orphan hT hS).1
      have F := WaiterFrame.orphanReplyWaiter s w x
      have hEnd := orphanReplyWaiter_forgets s w x hT
      have hBack : ∀ u, ReplyViews.waiterOf (orphanReplyWaiter s w x).replyViews u x →
          u ≠ w ∧ ReplyViews.waiterOf s.replyViews u x := by
        intro u hu
        obtain ⟨tu, htu, hsu⟩ := waiterOf_iff.mp hu
        have huw : u ≠ w := by
          intro e; subst e
          rw [hEnd tu htu] at hsu; cases hsu
        obtain ⟨t0, h0, k0⟩ := F.bwd u tu huw htu
        exact ⟨huw, waiterOf_iff.mpr ⟨t0, h0, k0.blockingServer.symm.trans hsu⟩⟩
      obtain ⟨tx', hX', kx, -⟩ := F.fwd x tx hxw hX
      have hIh := ih _ h' (fun t2 h2 => by
        rw [hX'] at h2; cases h2; rw [kx.blockingServer]; exact hNx tx hX) ⟨tx', hX', ?_⟩
      · exact ⟨hIh.1, (F.serverKept hxw).trans hIh.2.1,
          bindingLinksAgree.trans (SchedLinkFrame.orphanReplyWaiter s w x).binding hIh.2.2⟩
      · obtain ⟨l2, -, hLen2, hNd2, hMem2⟩ := h'.2.2.2.1.1 x tx'.replyView
          (SystemState.replyViews_of_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hX'))
        have hlt := length_lt_of_nodup_sub hNd2 (List.mem_cons_self (a := w) (l := l'))
          (fun a ha => by
            obtain ⟨haw, ha0⟩ := hBack a ((hMem2 a).mp ha)
            exact ⟨(hMem a).mpr ha0, haw⟩)
        have e1 : l2.length = tx'.replyWaitersCount := hLen2
        have e2 : (w :: l').length = tx.replyWaitersCount := hLen
        omega

/-- **The finalisation's walk orphans every caller waiting on `x`**, given the
server's own count as fuel (`finaliseThreadOrphanWaiters`), on a state carrying
the finalisation's invariant in which `x` waits on no reply of its own. -/
theorem finaliseThreadOrphanWaiters_endsAll (s : SystemState) (x : SeLe4n.ThreadId) (tx : TCB)
    (h : finaliseStepInvariant s) (hX : s.getTcb? x = some tx)
    (hNx : tx.blockingServer? ≠ some x) :
    (∀ v, ¬ ReplyViews.waiterOf (finaliseThreadOrphanWaiters s x).replyViews v x) ∧
      serverKept s (finaliseThreadOrphanWaiters s x) x ∧
      bindingLinksAgree s (finaliseThreadOrphanWaiters s x) := by
  have e : finaliseThreadOrphanWaiters s x = orphanReplyWaiters x tx.replyWaitersCount s := by
    unfold finaliseThreadOrphanWaiters; rw [hX]
  rw [e]
  exact orphanReplyWaiters_endsAll x _ s h (fun t ht => by rw [hX] at ht; cases ht; exact hNx)
    ⟨tx, hX, Nat.le_refl _⟩

end SeLe4n.Kernel
