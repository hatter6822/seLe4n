/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.CancelAllReachability

/-!
# A finalised server's waiters are all ended

WS-ZA ZA5.4 part 25: a thread's final delete ends every caller waiting on it
for a reply (`finaliseReplyWaiters`), each as seL4's `reply_remove` ends it.
The walk follows the server's live head and re-reads each waiter's guard.  This
module proves that the walk never refuses midway: from a state carrying the
finalisation's invariant (`finaliseStepInvariant`) in which every waiter is a
plain one (`plainWaiterReady`: its reply heads no stack and its end is
admitted), the walk, given at least the server's count as fuel, leaves no
thread waiting on the server (`finaliseReplyWaiters_endsAll`).

The argument: one waiter's end writes that waiter, its reply, the server's
queue links and its neighbours' (`objectsAgreeOffReplyLinks`), the
priority-inheritance walk from the server (`pipBoost` and run links only), and
the suspend's deschedule of that waiter (run links only).  None of these writes
reaches what another plain waiter's guard reads (`TCB.waiterKeyEq`, a zero
run-core code, and its own reply), so every other waiter stays ready, and the
queue loses exactly the ended one (`replyWaitersConsistent`).

The lender goes first (`finaliseThreadReturnLoan`): its reply heads the lent
context's stack (`lentContextHeadsLenderFrame`), so its pop writes the
context, the holder's and the lender's binding codes, the stack's head and the
frame below it (`returnDonated_replyUnframed`), and its end keeps every plain
waiter (`finaliseReplyWaiter_unframed`).  So, on a state the admission
`replyWaitersAdmitted` admits, the loan return and the walk together leave no
thread waiting on the server
(`finaliseThreadEndWaiters_returnLoan_endsAll_of_admitted`): the admission's
queue walk reads every waiter but the lender as plain
(`replyWaitersEndableFrom_plain`).

Scope: the theorem is stated on the state the loan return runs on.  The
finalisation reads the admission one step earlier, before the thread's own
notification unbind and IPC cancel (`finaliseThread`), and that carriage is
not proved here: like every other finalise step, the loan return and the walk
re-read their guards, and a state outside the guard is left as it is.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **What a plain waiter's guard reads of its TCB**, compared: the two IPC
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

/-- **What makes `v` a plain waiter of the server `x`**, read off its TCB `t`
and the reply `r` it waits on: the guard `replyWaiterEndable` admits it and the
reply heads no stack, as fields. -/
def plainWaiterOk (x v : SeLe4n.ThreadId) (t : TCB) (r : Reply) : Prop :=
  v.val ≠ x.val ∧ t.blockingServer? = some x ∧ r.callerCode = v.val + 1 ∧ r.next = none ∧
    v.isReserved = false ∧ isIdleThreadId v = false ∧ t.runCoreCode = 0 ∧
    4 ≤ t.ipcStateCode ∧ t.replyObjectCode ≠ 0 ∧ t.queueNextCode = 0 ∧
    t.queuePrevCode = 0 ∧ t.timeoutBudget = none

/-- **`v` is a plain waiter of `x` in `st`**: stored, with its reply stored
where its reply link names, and `plainWaiterOk`. -/
def plainWaiterReady (st : SystemState) (x v : SeLe4n.ThreadId) : Prop :=
  ∃ t r, st.getTcb? v = some t ∧ st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r) ∧
    plainWaiterOk x v t r

/-- **A plain waiter's guard passes**: `replyWaiterEndable` reads exactly
`plainWaiterOk`'s fields (a reply heading no stack pops nothing and needs no
holder). -/
theorem replyWaiterEndable_of_ok {st : SystemState} {x v : SeLe4n.ThreadId} {t : TCB}
    {r : Reply} (hR : st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r))
    (h : plainWaiterOk x v t r) : replyWaiterEndable st x v t = true := by
  obtain ⟨hvx, hS, hC, hN, hRes, hId, hRun, hIpc, hRO, hQN, hQP, hTB⟩ := h
  have hSC : replyCallerServerCode t = x.val + 1 := by
    unfold replyCallerServerCode; rw [hS]
  unfold replyWaiterEndable replyCallerCancelAdmitted replyCallerFinalisable replyHeadPopCommits
    replyHeadHeldByServer
  rw [hR]
  simp only [hN, hSC, hC, hRes, hId, hRun, hQN, hQP, hTB, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, Bool.not_false, Option.isNone_none, decide_eq_true_eq, and_true, true_and]
  exact ⟨hvx, hIpc, by omega⟩

/-- ...and its reply reads as heading no stack. -/
theorem replyCallerReplyUnstacked_of_ok {st : SystemState} {x v : SeLe4n.ThreadId} {t : TCB}
    {r : Reply} (hR : st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r))
    (h : plainWaiterOk x v t r) : replyCallerReplyUnstacked st t = true := by
  unfold replyCallerReplyUnstacked; rw [hR]; simp only [h.2.2.2.1, Option.isNone_none]

/-- **The admission's per-waiter reads are a plain waiter's**: a thread the guard
admits whose reply reads as heading no stack is `plainWaiterOk`. -/
theorem plainWaiterOk_of_guard {st : SystemState} {x v : SeLe4n.ThreadId} {t : TCB}
    (hE : replyWaiterEndable st x v t = true) (hU : replyCallerReplyUnstacked st t = true) :
    ∃ r, st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r) ∧ plainWaiterOk x v t r := by
  unfold replyCallerReplyUnstacked at hU
  obtain ⟨r, hR⟩ : ∃ r, st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r) := by
    revert hU
    cases st.getObject? ⟨t.replyObjectCode - 1⟩ with
    | none => intro h; cases h
    | some o => cases o <;> intro h <;> first | cases h | exact ⟨_, rfl⟩
  rw [hR] at hU
  have hN : r.next = none := by
    simpa only [Option.isNone_iff_eq_none] using hU
  unfold replyWaiterEndable replyCallerCancelAdmitted at hE
  rw [hR] at hE
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hE
  obtain ⟨⟨hvx, hSC⟩, ⟨hC, hF⟩, -⟩ := hE
  obtain ⟨-, hRes, hId, hRun, ⟨ep, rt, hB⟩, hRO, hQN, hQP, hTB⟩ := replyCallerFinalisable_parts hF
  refine ⟨r, hR, hvx, ?_, hC, hN, by simpa using hRes, hId, hRun, ?_, ?_, ?_, ?_, hTB⟩
  · unfold replyCallerServerCode at hSC
    cases hS : t.blockingServer? with
    | none => rw [hS] at hSC; cases hSC
    | some s =>
      rw [hS] at hSC
      simp only [Nat.add_right_cancel_iff] at hSC
      cases s; cases x; simp only at hSC; subst hSC; rfl
  · simp only [replyCallerFinalisable, Bool.and_eq_true, decide_eq_true_eq] at hF
    exact hF.1.1.1.1.2
  · intro h0
    simp only [TCB.replyObject, h0] at hRO
    cases hRO
  · exact (SeLe4n.ThreadId.ofOptCode_eq_none_iff _).mp hQN
  · exact (SeLe4n.ThreadId.ofOptCode_eq_none_iff _).mp hQP

-- ============================================================================
-- The frame one waiter's end keeps
-- ============================================================================

/-- **A step that keeps every thread off `E` up to what a plain waiter's guard
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

/-- **A plain waiter off `E` stays ready across a frame.** -/
theorem ready {a b : SystemState} {E : SeLe4n.ThreadId → Prop} (h : WaiterFrame a b E)
    {x v : SeLe4n.ThreadId} (hv : ¬ E v) (hR : plainWaiterReady a x v) : plainWaiterReady b x v := by
  obtain ⟨t, r, ht, hr, hok⟩ := hR
  obtain ⟨t', ht', k, z⟩ := h.fwd v t hv ht
  have hr' : b.getObject? ⟨t'.replyObjectCode - 1⟩ = some (.reply r) := by
    rw [k.2.2.1]
    refine h.reply _ r hr hok.2.2.2.1 (fun e he hc => hv ?_)
    have : v = e := by
      cases v; cases e; simp only [hok.2.2.1, Nat.add_right_cancel_iff] at hc; subst hc; rfl
    exact this ▸ he
  obtain ⟨hvx, hS, hC, hN, hRes, hId, hRun, hIpc, hRO, hQN, hQP, hTB⟩ := hok
  exact ⟨t', r, ht', hr', hvx, k.blockingServer.trans hS, hC, hN, hRes, hId, z hRun,
    k.2.1 ▸ hIpc, k.2.2.1 ▸ hRO, k.2.2.2.1 ▸ hQN, k.2.2.2.2.1 ▸ hQP, k.2.2.2.2.2.1 ▸ hTB⟩

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

/-- A plain waiter's reply link names the reply its code stands for. -/
theorem plainWaiterOk.replyObject {x v : SeLe4n.ThreadId} {t : TCB} {r : Reply}
    (h : plainWaiterOk x v t r) : t.replyObject = some ⟨t.replyObjectCode - 1⟩ := by
  have h0 := h.2.2.2.2.2.2.2.2.1
  unfold TCB.replyObject
  cases hc : t.replyObjectCode with
  | zero => exact absurd hc h0
  | succ k => rfl

/-- A plain waiter is reply-blocked on its server. -/
theorem plainWaiterOk.blocked {x v : SeLe4n.ThreadId} {t : TCB} {r : Reply}
    (h : plainWaiterOk x v t r) : ∃ ep, t.ipcState = .blockedOnReply ep (some x) := by
  have hS := h.2.1
  unfold TCB.blockingServer? at hS
  split at hS
  · rename_i ep s heq; cases hS; exact ⟨ep, heq⟩
  · cases hS

namespace WaiterFrame

/-- **The splice of a waiter's reply linked to no frame above keeps every other
thread and every other reply heading no stack**: it is the identity, or — on a
contextless stack top — the cut from the frame below, which writes the waiter's
own reply and a frame below that links up to it, so heads no stack's top.  The
waiter's reply keeps its caller and its `next`. -/
theorem spliceUnframed (st : SystemState) (hInv : st.objects.invExt) {w : SeLe4n.ThreadId}
    {t : TCB} {rid : SeLe4n.ReplyId} {r : Reply} (hRO : t.replyObject = some rid)
    (hRo : st.objects[rid.toObjId]? = some (.reply r)) (hC : r.callerCode = w.val + 1)
    (hN : ∀ a, r.next ≠ some (.frame a)) :
    WaiterFrame st (spliceThreadReplyFrameOut st t) (· = w) ∧
      ∃ r', (spliceThreadReplyFrameOut st t).objects[rid.toObjId]? = some (.reply r') ∧
        r'.callerCode = r.callerCode ∧ r'.next = r.next := by
  have hGR : st.getReply? rid = some r := (SystemState.getReply?_eq_some_iff _ _ _).mpr hRo
  have hTcb := spliceThreadReplyFrameOut_getTcb?_eq st t hInv
  rcases spliceThreadReplyFrameOut_cases st t with h | ⟨rid0, hr0, h⟩
  · rw [h]; exact ⟨.refl _ _, r, hRo, rfl, rfl⟩
  rw [hRO] at hr0; cases hr0
  rcases spliceReplyFrameOut_cases h with h' | ⟨r1, above, _, hR1, hN1, _, _, _⟩ |
      ⟨r1, below, b, hR1, hN1, _, hB, hBn, hS⟩
  · rw [h']; exact ⟨.refl _ _, r, hRo, rfl, rfl⟩
  · rw [hGR] at hR1; cases hR1; exact absurd hN1 (hN above)
  rw [hGR] at hR1; cases hR1
  obtain ⟨-, hRv, hFrame⟩ := severReplyFrameBelowStores_values hInv hGR hN1 hB hBn hS
  have hBObj := (SystemState.getReply?_eq_some_iff _ _ _).mp hB
  refine ⟨⟨fun v tv _ hv => ⟨tv, by rw [hTcb]; exact hv, .refl tv, id⟩,
    fun v tv _ hv => ⟨tv, by rw [← hTcb]; exact hv, .refl tv⟩, fun k rk hk hkn hkc => ?_⟩,
    { r with prev := none }, (SystemState.getReply?_eq_some_iff _ _ _).mp hRv, rfl, rfl⟩
  unfold SystemState.getObject? at hk ⊢
  have hkB : k ≠ below.toObjId := by
    intro e; rw [e, hBObj] at hk; cases hk; rw [hBn] at hkn; cases hkn
  have hkR : k ≠ rid.toObjId := by
    intro e; rw [e, hRo] at hk; cases hk; exact hkc w rfl hC
  rw [hFrame k hkB hkR]; exact hk

/-- **A plain waiter's cancel keeps every other thread and every other reply**
(`cancelIpcBlocking`'s reply arm with nothing to give back): the splice is the
identity on a reply heading no stack, the restore and the consume write `w` and
its reply, and the unlink writes reply-waiter links alone. -/
theorem cancelPlain (st : SystemState) (hInv : st.objects.invExt) {x w : SeLe4n.ThreadId}
    {t : TCB} {r : Reply} (hT : st.getTcb? w = some t)
    (hR : st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r)) (hok : plainWaiterOk x w t r) :
    WaiterFrame st (Lifecycle.Suspend.cancelIpcBlocking st w t) (· = w) := by
  obtain ⟨ep, hB⟩ := hok.blocked
  have hRO := hok.replyObject
  let rid : SeLe4n.ReplyId := ⟨t.replyObjectCode - 1⟩
  have hRo : st.objects[rid.toObjId]? = some (.reply r) := hR
  have hGR : st.getReply? rid = some r := by unfold SystemState.getReply?; rw [hRo]
  have hD : Lifecycle.Suspend.cancelledCallerDonation? st w t = none := by
    unfold Lifecycle.Suspend.cancelledCallerDonation?
    rw [hB, hRO]
    apply replyFrameHeadHolder?_of_no_head
    unfold replyFrameHeadContext?
    rw [hGR]
    have hn := hok.2.2.2.1
    dsimp only
    rw [hn]
  rw [cancelIpcBlocking_replyArm_of_noDonation st w t hB hD]
  obtain ⟨f0, r0, hr0, hc0, -⟩ := WaiterFrame.spliceUnframed st hInv hRO hRo hok.2.2.1
    (fun a e => by rw [hok.2.2.2.1] at e; cases e)
  have I0 := spliceThreadReplyFrameOut_preserves_objects_invExt st t hInv
  have hT0 : (spliceThreadReplyFrameOut st t).getTcb? w = some t := by
    rw [spliceThreadReplyFrameOut_getTcb?_eq st t hInv]; exact hT
  generalize spliceThreadReplyFrameOut st t = s0 at f0 hr0 I0 hT0
  have f1 : WaiterFrame s0 (Lifecycle.Suspend.restoreToReadyCancelled s0 w) (· = w) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact WaiterFrame.updateTcb s0 w _ I0
  have hI1 : (Lifecycle.Suspend.restoreToReadyCancelled s0 w).objects.invExt :=
    Lifecycle.Suspend.restoreToReadyStaging_invExt s0 w _ I0
  have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT0
  have hwR : w.toObjId ≠ rid.toObjId := fun e => by rw [e, hr0] at hTo; cases hTo
  have hR1 : (Lifecycle.Suspend.restoreToReadyCancelled s0 w).objects[rid.toObjId]? =
      some (.reply r0) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    rw [SystemState.updateTcb_objects_ne s0 w _ _ hwR I0]; exact hr0
  have hW1 : ∃ tw, (Lifecycle.Suspend.restoreToReadyCancelled s0 w).getTcb? w = some tw := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    rw [SystemState.updateTcb_getTcb?_self s0 w _ I0, hT0]; exact ⟨_, rfl⟩
  obtain ⟨tw, hW1⟩ := hW1
  have f2 := WaiterFrame.consumeReplyLink _ w t tw hI1 rid r0 hRO hR1 (hc0.trans hok.2.2.1) hW1
  have f3 := WaiterFrame.of_agreeOffReplyLinks (· = w)
    (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks
      (Lifecycle.Suspend.consumeReplyLink (Lifecycle.Suspend.restoreToReadyCancelled s0 w) w t) w
      t.blockingServer?)
  exact f0.trans ((f1.trans f2).trans f3)

end WaiterFrame

-- ============================================================================
-- One plain waiter's end
-- ============================================================================

/-- **A finalised thread's suspend keeps every other thread and every reply**,
and leaves `w`'s key as it found it. -/
theorem finaliseThreadSuspend_waiterFrame (st : SystemState) (hInv : st.objects.invExt)
    (w : SeLe4n.ThreadId) :
    WaiterFrame st (finaliseThreadSuspend st w) (· = w) ∧
      ∀ t', (finaliseThreadSuspend st w).getTcb? w = some t' →
        ∃ t, st.getTcb? w = some t ∧ TCB.waiterKeyEq t' t := by
  unfold finaliseThreadSuspend
  split
  · rename_i t0 hT0
    split
    · have hD := descheduleAtPlacement_preserves_objects_invExt st w hInv
      refine ⟨(WaiterFrame.descheduleAtPlacement st w _).trans (WaiterFrame.updateTcb _ w _ hD),
        fun t' ht' => ?_⟩
      rw [SystemState.updateTcb_getTcb?_self _ w _ hD] at ht'
      cases hM : (descheduleAtPlacement st w).getTcb? w with
      | none => rw [hM] at ht'; cases ht'
      | some tm =>
        rw [hM] at ht'
        simp only [Option.map_some, Option.some.injEq] at ht'
        subst ht'
        obtain ⟨tp, hp, e⟩ := (descheduleAtPlacement_objectsAgreeOffRunLinks st w).get_tcb'
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hM)
        have k : TCB.waiterKeyEq tm tp := TCB.waiterKeyEq.of_withoutRunLinks e
        exact ⟨tp, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hp, k⟩
    · exact ⟨.refl _ _, fun t' ht' => ⟨t', ht', .refl t'⟩⟩
  · exact ⟨.refl _ _, fun t' ht' => ⟨t', ht', .refl t'⟩⟩

/-- **One plain waiter's end** (`finaliseReplyWaiter`): it keeps every other
thread and every other reply (`WaiterFrame`), and leaves the waiter `.ready`
on no server. -/
theorem finaliseReplyWaiter_plain (st : SystemState) (hInv : st.objects.invExt)
    {x w : SeLe4n.ThreadId} {t : TCB} {r : Reply} (hT : st.getTcb? w = some t)
    (hR : st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r)) (hok : plainWaiterOk x w t r) :
    WaiterFrame st (finaliseReplyWaiter st w t) (· = w) ∧
      ∀ t', (finaliseReplyWaiter st w t).getTcb? w = some t' → t'.ipcState = .ready := by
  have hE := replyWaiterEndable_of_ok hR hok
  unfold replyWaiterEndable replyCallerCancelAdmitted at hE
  rw [hR] at hE
  simp only [Bool.and_eq_true] at hE
  obtain ⟨-, hG⟩ := hE
  have hCancel : finaliseReplyCallerCancel st w t =
      finaliseReplyRevert (Lifecycle.Suspend.cancelIpcBlocking st w t) t.blockingServer? := by
    unfold finaliseReplyCallerCancel finaliseReplyCancel
    rw [hR]
    simp only [Bool.and_eq_true, hG, and_self, if_true, hok.2.2.2.1, replyStackLinkIsHead,
      Bool.false_eq_true, if_false]
  have hS : t.blockingServer? = some x := hok.2.1
  have hI1 := Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st w t hInv
  have f1 := WaiterFrame.cancelPlain st hInv hT hR hok
  have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  have hReady := cancelIpcBlocking_victim_ready st w t hInv
    (lookupTcb_of_objects_of_not_reserved st w t hTo (by rw [hok.2.2.2.2.1]; exact Bool.false_ne_true))
  generalize hS1 : Lifecycle.Suspend.cancelIpcBlocking st w t = s1 at f1 hI1 hReady
  have hRev : finaliseReplyRevert s1 t.blockingServer? =
      (PriorityInheritance.propagatePipChainCrossCore s1 x Concurrency.bootCoreId).1 := by
    unfold finaliseReplyRevert; rw [hS]
  unfold finaliseReplyWaiter
  rw [hCancel, hS1, hRev]
  have f2 := WaiterFrame.propagate s1 x Concurrency.bootCoreId s1.objectIndex.length hI1 (· = w)
  have f2' := WaiterFrame.propagate s1 x Concurrency.bootCoreId s1.objectIndex.length hI1
    (fun _ => False)
  have hI2 := PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt s1 x
    Concurrency.bootCoreId s1.objectIndex.length hI1
  generalize (PriorityInheritance.propagatePipChainCrossCore s1 x Concurrency.bootCoreId).1 = s2
    at f2 f2' hI2
  obtain ⟨f3, hW3⟩ := finaliseThreadSuspend_waiterFrame s2 hI2 w
  refine ⟨(f1.trans f2).trans f3, fun t' ht' => ?_⟩
  obtain ⟨t2, h2, k2⟩ := hW3 t' ht'
  obtain ⟨t1, h1, k1⟩ := f2'.bwd w t2 (fun h => h) h2
  rw [k2.ipcState, k1.ipcState]
  exact hReady t1 ((SystemState.getTcb?_eq_some_iff _ _ _).mp h1)

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

/-- The walk's step keeps the finalisation's invariant. -/
theorem finaliseStepInvariant_replyWaiter {s : SystemState} {w : SeLe4n.ThreadId} {t : TCB}
    (h : finaliseStepInvariant s) (hT : s.getTcb? w = some t) :
    finaliseStepInvariant (finaliseReplyWaiter s w t) :=
  finaliseReplyWaiter_closed finaliseStepInvariant
    (fun _ _ _ _ _ h hX hC hT hF => (h.reply hX hC hT hF).1)
    (fun _ _ _ h hT hS hO hI hId => (h.suspend hT hS hO hI hId).1) s w t h hT

/-- The walk at a server whose head code is zero stops. -/
theorem finaliseReplyWaiters_headZero {x : SeLe4n.ThreadId} {n : Nat} {s : SystemState} {tx : TCB}
    (hX : s.getTcb? x = some tx) (hH : tx.replyWaitersHeadCode = 0) :
    finaliseReplyWaiters x (n + 1) s = s := by
  show (match s.getTcb? x with
    | some tx => match tx.replyWaitersHeadCode with
      | 0 => s
      | k + 1 => match s.getTcb? ⟨k⟩ with
        | some t => if replyWaiterEndable s x ⟨k⟩ t then finaliseReplyWaiters x n (finaliseReplyWaiter s ⟨k⟩ t) else s
        | none => s
    | none => s) = s
  rw [hX]; simp only [hH]

/-- The walk at a server headed by an admitted waiter ends it and goes on. -/
theorem finaliseReplyWaiters_headStep {x : SeLe4n.ThreadId} {n k : Nat} {s : SystemState}
    {tx t : TCB} (hX : s.getTcb? x = some tx) (hH : tx.replyWaitersHeadCode = k + 1)
    (hT : s.getTcb? ⟨k⟩ = some t) (hG : replyWaiterEndable s x ⟨k⟩ t = true) :
    finaliseReplyWaiters x (n + 1) s = finaliseReplyWaiters x n (finaliseReplyWaiter s ⟨k⟩ t) := by
  show (match s.getTcb? x with
    | some tx => match tx.replyWaitersHeadCode with
      | 0 => s
      | k + 1 => match s.getTcb? ⟨k⟩ with
        | some t => if replyWaiterEndable s x ⟨k⟩ t then finaliseReplyWaiters x n (finaliseReplyWaiter s ⟨k⟩ t) else s
        | none => s
    | none => s) = _
  rw [hX]; simp only [hH, hT, hG, if_true]

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

/-- **The walk never refuses midway** (WS-ZA ZA5.4 part 25): from a state
carrying the finalisation's invariant in which every thread waiting on `x` is a
plain waiter, the walk, with at least `x`'s count as fuel, ends every one of
them — none waits on `x` after it.  Each step ends the queue's head (the guard
admits a plain waiter, `replyWaiterEndable_of_ok`), keeps every other waiter
plain (`finaliseReplyWaiter_plain`, `WaiterFrame.ready`), and shortens the queue
(`replyWaitersConsistent`, `length_lt_of_nodup_sub`).  It keeps `x` itself
(`serverKept`, WS-ZA ZA5.4 part 26): each step's frame excludes only the waiter
it ends. -/
theorem finaliseReplyWaiters_endsAll (x : SeLe4n.ThreadId) :
    ∀ (n : Nat) (s : SystemState), finaliseStepInvariant s →
      (∀ v, ReplyViews.waiterOf s.replyViews v x → plainWaiterReady s x v) →
      (∃ tx, s.getTcb? x = some tx ∧ tx.replyWaitersCount ≤ n) →
      (∀ v, ¬ ReplyViews.waiterOf (finaliseReplyWaiters x n s).replyViews v x) ∧
        serverKept s (finaliseReplyWaiters x n s) x := by
  intro n
  induction n with
  | zero =>
    intro s h _ ⟨tx, hX, hC⟩
    refine ⟨fun v hv => ?_, serverKept.refl s x⟩
    obtain ⟨l, -, hLen, -, hMem⟩ := h.2.2.2.1.1 x tx.replyView
      (SystemState.replyViews_of_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hX))
    have hl : l = [] := List.eq_nil_of_length_eq_zero (by
      rw [hLen]; show tx.replyWaitersCount = 0; omega)
    subst hl
    exact List.not_mem_nil ((hMem v).mpr hv)
  | succ n ih =>
    intro s h hAll ⟨tx, hX, hC⟩
    obtain ⟨l, hCh, hLen, hNd, hMem⟩ := h.2.2.2.1.1 x tx.replyView
      (SystemState.replyViews_of_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hX))
    cases l with
    | nil =>
      have hH : tx.replyWaitersHeadCode = 0 :=
        (SeLe4n.ThreadId.ofOptCode_eq_none_iff _).mp hCh
      rw [finaliseReplyWaiters_headZero hX hH]
      exact ⟨fun v hv => List.not_mem_nil ((hMem v).mpr hv), serverKept.refl s x⟩
    | cons w l' =>
      have hH : tx.replyWaitersHeadCode = w.val + 1 := by
        have hc := hCh.1
        revert hc
        show SeLe4n.ThreadId.ofOptCode tx.replyWaitersHeadCode = some w → _
        cases tx.replyWaitersHeadCode with
        | zero => intro e; cases e
        | succ k => intro e; cases e; rfl
      obtain ⟨t, r, hT, hR, hok⟩ := hAll w ((hMem w).mp (List.mem_cons_self ..))
      rw [finaliseReplyWaiters_headStep hX hH hT (replyWaiterEndable_of_ok hR hok)]
      have h' := finaliseStepInvariant_replyWaiter h hT
      obtain ⟨F, hEnd⟩ := finaliseReplyWaiter_plain s h.2.1 hT hR hok
      have hBack : ∀ u, ReplyViews.waiterOf (finaliseReplyWaiter s w t).replyViews u x →
          u ≠ w ∧ ReplyViews.waiterOf s.replyViews u x := by
        intro u hu
        obtain ⟨tu, htu, hsu⟩ := waiterOf_iff.mp hu
        have huw : u ≠ w := by
          intro e; subst e
          have hr := hEnd tu htu
          unfold TCB.blockingServer? at hsu; rw [hr] at hsu; cases hsu
        obtain ⟨t0, h0, k0⟩ := F.bwd u tu huw htu
        exact ⟨huw, waiterOf_iff.mpr ⟨t0, h0, k0.blockingServer.symm.trans hsu⟩⟩
      have hxw : ¬ x = w := fun e => hok.1 (by rw [e])
      obtain ⟨tx', hX', -, -⟩ := F.fwd x tx hxw hX
      have hIh := ih _ h' (fun u hu => ?_) ⟨tx', hX', ?_⟩
      · exact ⟨hIh.1, (F.serverKept hxw).trans hIh.2⟩
      · obtain ⟨huw, hu0⟩ := hBack u hu
        exact F.ready huw (hAll u hu0)
      · obtain ⟨l2, -, hLen2, hNd2, hMem2⟩ := h'.2.2.2.1.1 x tx'.replyView
          (SystemState.replyViews_of_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hX'))
        have hlt := length_lt_of_nodup_sub hNd2 (List.mem_cons_self (a := w) (l := l'))
          (fun a ha => by
            obtain ⟨haw, ha0⟩ := hBack a ((hMem2 a).mp ha)
            exact ⟨(hMem a).mpr ha0, haw⟩)
        have e1 : l2.length = tx'.replyWaitersCount := hLen2
        have e2 : (w :: l').length = tx.replyWaitersCount := hLen
        omega

-- ============================================================================
-- The lender's pop keeps every plain waiter
-- ============================================================================

/-- **The reply below a stack's head is a frame**, when the outer-caller
resolution answers: it is what the resolution checks. -/
theorem replyStackOuterCaller?_below {st : SystemState} {s : SeLe4n.SchedContextId}
    {n : Option SeLe4n.ThreadId} {sc : SchedContext} {x : SeLe4n.ReplyId} {rx : Reply}
    {y : SeLe4n.ReplyId} (hRes : replyStackOuterCaller? st s = .ok n)
    (hSc : st.objects[s.toObjId]? = some (.schedContext sc))
    (hHead : donationHeadOf? st s sc = .ok (some (x, rx))) (hPrev : rx.prev = some y) :
    ∃ b, st.objects[y.toObjId]? = some (.reply b) ∧ b.next = some (.frame x) := by
  unfold replyStackOuterCaller? at hRes
  have hG : st.getSchedContext? s = some sc := by
    unfold SystemState.getSchedContext?; rw [hSc]
  rw [hG] at hRes
  simp only [hHead, hPrev] at hRes
  revert hRes
  cases hB : st.getReply? y with
  | none => intro h; cases h
  | some b =>
    intro hRes
    refine ⟨b, ?_, ?_⟩
    · unfold SystemState.getReply? at hB
      split at hB
      · rename_i r hr; cases hB; exact hr
      · cases hB
    · by_cases hn : b.next = some (.frame x)
      · exact hn
      · simp only [hn, bne_iff_ne, ne_eq, not_false_eq_true, if_true] at hRes
        cases hRes

/-- The head a context's stack resolution reads heads the stack. -/
theorem donationHeadOf?_head {st : SystemState} {s : SeLe4n.SchedContextId} {sc : SchedContext}
    {x : SeLe4n.ReplyId} {rx : Reply} (h : donationHeadOf? st s sc = .ok (some (x, rx))) :
    st.objects[x.toObjId]? = some (.reply rx) ∧ rx.next = some (.head s) := by
  unfold donationHeadOf? at h
  split at h
  · cases h
  · rename_i rid _
    revert h
    cases hR : st.getReply? rid with
    | none => intro h; cases h
    | some r =>
      intro h
      by_cases hn : r.next = some (.head s)
      · simp only [hn, bne_self_eq_false, Bool.false_eq_true, if_false, Except.ok.injEq,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, hn⟩
        unfold SystemState.getReply? at hR
        split at hR
        · rename_i r' hr'; cases hR; exact hr'
        · cases hR
      · simp only [hn, bne_iff_ne, ne_eq, not_false_eq_true, if_true] at h
        cases h

namespace WaiterFrame

/-- **The donation return keeps every thread and every reply heading no stack**:
it rewrites two threads' binding codes, which no guard of a plain waiter reads,
moves no thread on or off a run queue, and writes the stack's head and the
frame below it, neither of which heads no stack. -/
theorem returnDonated {st st' : SystemState} {h : SeLe4n.ThreadId} {s : SeLe4n.SchedContextId}
    {c : SeLe4n.ThreadId} {n : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hRes : replyStackOuterCaller? st s = .ok n)
    (hPop : returnDonatedSchedContext st h s c n = .ok st') (E : SeLe4n.ThreadId → Prop) :
    WaiterFrame st st' E := by
  have hRC := returnDonatedSchedContext_runCoresAgree st st' h s c hInv n hPop
  refine ⟨fun v t _ ht => ?_, fun v t' _ ht' => ?_, fun k r hk hn _ => ?_⟩
  · obtain ⟨t', h', c0, o0, e⟩ := returnDonatedSchedContext_tcb_rewrite st st' h s c hInv n hPop
      v.toObjId t ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht)
    have ht' := (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'
    refine ⟨t', ht', by subst e; exact .refl _, fun z => ?_⟩
    have hM := hRC v
    rw [ht', ht] at hM
    simp only [Option.map_some, Option.some.injEq] at hM
    exact hM.trans z
  · obtain ⟨t0, h0, c0, o0, e⟩ := returnDonatedSchedContext_tcb_rewrite_backward st st' h s c n
      hInv hPop v.toObjId t' ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht')
    exact ⟨t0, (SystemState.getTcb?_eq_some_iff _ _ _).mpr h0,
      by subst e; exact .refl _⟩
  · unfold SystemState.getObject? at hk ⊢
    obtain ⟨sc, head?, hSc, hHd, hKeep, -, -⟩ := returnDonatedSchedContext_reply_cases hInv hPop
    refine hKeep k r hk (fun x rx e => ?_) (fun x rx y e hy => ?_)
    · subst e
      obtain ⟨hx, hxn⟩ := donationHeadOf?_head hHd
      intro hkx; rw [hkx, hx] at hk; cases hk; rw [hn] at hxn; cases hxn
    · subst e
      obtain ⟨b, hb, hbn⟩ := replyStackOuterCaller?_below hRes hSc hHd hy
      intro hky; rw [hky, hb] at hk; cases hk; rw [hn] at hbn; cases hbn

end WaiterFrame

-- ============================================================================
-- The lender's end keeps every plain waiter
-- ============================================================================

/-- **The donation return leaves a reply linked to no frame above still linked to
none, with its caller**: the pop writes the stack's head (its links cleared) and
the frame below it (made the head); a reply that was neither keeps its links. -/
theorem returnDonated_replyUnframed {st st' : SystemState} {h : SeLe4n.ThreadId}
    {s : SeLe4n.SchedContextId} {c : SeLe4n.ThreadId} {n : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hPop : returnDonatedSchedContext st h s c n = .ok st') {rid : SeLe4n.ReplyId} {r : Reply}
    (hRo : st.objects[rid.toObjId]? = some (.reply r)) (hN : ∀ a, r.next ≠ some (.frame a)) :
    ∃ r', st'.objects[rid.toObjId]? = some (.reply r') ∧ r'.callerCode = r.callerCode ∧
      ∀ a, r'.next ≠ some (.frame a) := by
  obtain ⟨sc, head?, -, hHd, hKeep, hBelow, hHeadW⟩ := returnDonatedSchedContext_reply_cases hInv hPop
  cases head? with
  | none =>
    exact ⟨r, hKeep _ _ hRo (fun _ _ e => by cases e) (fun _ _ _ e => by cases e), rfl, hN⟩
  | some p =>
    obtain ⟨x0, rx0⟩ := p
    obtain ⟨hx, hxn⟩ := donationHeadOf?_head hHd
    by_cases e1 : rid.toObjId = x0.toObjId
    · rw [e1, hx] at hRo
      cases hRo
      refine ⟨{ r with prev := none, next := none }, ?_, rfl, fun a e => by cases e⟩
      rw [e1]
      refine hHeadW _ _ rfl hx (fun y hy hyx => ?_)
      obtain ⟨b, hb, hbn⟩ := hChain.prevLinkReciprocal x0 r y hx hy
      rw [hyx, hx] at hb
      cases hb
      rw [hxn] at hbn
      cases hbn
    · by_cases e2 : ∃ y, rx0.prev = some y ∧ rid.toObjId = y.toObjId
      · obtain ⟨y, hy, e2⟩ := e2
        refine ⟨{ r with next := some (.head s) }, ?_, rfl, fun a e => by cases e⟩
        rw [e2]
        exact hBelow x0 rx0 y r rfl hy (e2 ▸ hRo) (fun h => e1 (e2.trans h))
      · refine ⟨r, hKeep _ _ hRo (fun x' rx' e => ?_) (fun x' rx' y e hy => ?_), rfl, hN⟩
        · cases e; exact e1
        · cases e; exact fun h => e2 ⟨y, hy, h⟩

/-- **The cancelled caller's donation return keeps every thread and every reply
heading no stack**, keeps the store's invariant, and leaves the caller's reply,
linked to no frame above, linked to none with its caller. -/
theorem returnDonationToCancelledCaller_frame (st : SystemState) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (w : SeLe4n.ThreadId) (t : TCB)
    {rid : SeLe4n.ReplyId} {r : Reply} (hRo : st.objects[rid.toObjId]? = some (.reply r))
    (hN : ∀ a, r.next ≠ some (.frame a)) :
    WaiterFrame st (Lifecycle.Suspend.returnDonationToCancelledCaller st w t) (fun _ => False) ∧
      (Lifecycle.Suspend.returnDonationToCancelledCaller st w t).objects.invExt ∧
      ∃ r', (Lifecycle.Suspend.returnDonationToCancelledCaller st w t).objects[rid.toObjId]? =
          some (.reply r') ∧ r'.callerCode = r.callerCode ∧ ∀ a, r'.next ≠ some (.frame a) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · rename_i scId holder _ _ _
    split
    · rename_i st' hOk
      obtain ⟨n, hRes, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
      exact ⟨WaiterFrame.returnDonated hInv hRes hPop _,
        returnDonatedSchedContext_preserves_objects_invExt _ _ _ _ _ hInv _ hPop,
        returnDonated_replyUnframed hInv hChain hPop hRo hN⟩
    · exact ⟨.refl _ _, hInv, r, hRo, rfl, hN⟩
  · exact ⟨.refl _ _, hInv, r, hRo, rfl, hN⟩

namespace WaiterFrame

/-- **A reply-blocked caller's cancel, its reply linked to no frame above, keeps
every other thread and every other reply heading no stack**: the donation
return (`returnDonationToCancelledCaller_frame`), the splice (the identity on a
reply linked to no frame above), the restore and the consume (`w` and its reply)
and the unlink (reply-waiter links alone). -/
theorem cancelUnframed (st : SystemState) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) {w : SeLe4n.ThreadId} {t : TCB}
    {rid : SeLe4n.ReplyId} {r : Reply} (hB : ∃ ep rt, t.ipcState = .blockedOnReply ep rt)
    (hRO : t.replyObject = some rid) (hRo : st.objects[rid.toObjId]? = some (.reply r))
    (hC : r.callerCode = w.val + 1) (hN : ∀ a, r.next ≠ some (.frame a))
    (hT : st.getTcb? w = some t) :
    WaiterFrame st (Lifecycle.Suspend.cancelIpcBlocking st w t) (· = w) := by
  obtain ⟨ep, rt, hB⟩ := hB
  obtain ⟨F0, I0, r0, hr0, hc0, hn0⟩ := returnDonationToCancelledCaller_frame st hInv hChain w t hRo hN
  unfold Lifecycle.Suspend.cancelIpcBlocking
  rw [hB]
  dsimp only
  have hT0 := F0.fwd w t (fun h => h) hT
  generalize Lifecycle.Suspend.returnDonationToCancelledCaller st w t = s0 at F0 I0 hr0 hT0
  obtain ⟨tw0, hT0, -⟩ := hT0
  obtain ⟨fS, r1, hr1, hc1, -⟩ := WaiterFrame.spliceUnframed s0 I0 hRO hr0 (hc0.trans hC) hn0
  have I1 := spliceThreadReplyFrameOut_preserves_objects_invExt s0 t I0
  have hT1 : (spliceThreadReplyFrameOut s0 t).getTcb? w = some tw0 := by
    rw [spliceThreadReplyFrameOut_getTcb?_eq s0 t I0]; exact hT0
  have F1 := (F0.mono (fun _ h => h.elim)).trans fS
  generalize spliceThreadReplyFrameOut s0 t = s1 at fS F1 hr1 I1 hT1
  have f1 : WaiterFrame s1 (Lifecycle.Suspend.restoreToReadyCancelled s1 w) (· = w) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact WaiterFrame.updateTcb s1 w _ I1
  have hI1 : (Lifecycle.Suspend.restoreToReadyCancelled s1 w).objects.invExt :=
    Lifecycle.Suspend.restoreToReadyStaging_invExt s1 w _ I1
  have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT1
  have hwR : w.toObjId ≠ rid.toObjId := fun e => by rw [e, hr1] at hTo; cases hTo
  have hR1 : (Lifecycle.Suspend.restoreToReadyCancelled s1 w).objects[rid.toObjId]? =
      some (.reply r1) := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    rw [SystemState.updateTcb_objects_ne s1 w _ _ hwR I1]; exact hr1
  have hW1 : ∃ tw, (Lifecycle.Suspend.restoreToReadyCancelled s1 w).getTcb? w = some tw := by
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    rw [SystemState.updateTcb_getTcb?_self s1 w _ I1, hT1]; exact ⟨_, rfl⟩
  obtain ⟨tw, hW1⟩ := hW1
  have f2 := WaiterFrame.consumeReplyLink _ w t tw hI1 rid r1 hRO hR1
    (hc1.trans (hc0.trans hC)) hW1
  have f3 := WaiterFrame.of_agreeOffReplyLinks (· = w)
    (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks
      (Lifecycle.Suspend.consumeReplyLink (Lifecycle.Suspend.restoreToReadyCancelled s1 w) w t) w
      t.blockingServer?)
  exact ((F1.trans f1).trans f2).trans f3

end WaiterFrame

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

/-- **The end of a caller whose reply is linked to no frame above** — the head of
a stack, the lender's case, or a reply on none — when its guard admits it: it
keeps every other thread and every other reply heading no stack
(`WaiterFrame`), and leaves the caller `.ready` on no server. -/
theorem finaliseReplyWaiter_unframed (st : SystemState) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) {x w : SeLe4n.ThreadId} {t : TCB} {r : Reply}
    (hT : st.getTcb? w = some t)
    (hR : st.getObject? ⟨t.replyObjectCode - 1⟩ = some (.reply r))
    (hN : ∀ a, r.next ≠ some (.frame a)) (hE : replyWaiterEndable st x w t = true) :
    WaiterFrame st (finaliseReplyWaiter st w t) (· = w) ∧
      ∀ t', (finaliseReplyWaiter st w t).getTcb? w = some t' → t'.ipcState = .ready := by
  unfold replyWaiterEndable replyCallerCancelAdmitted at hE
  rw [hR] at hE
  dsimp only at hE
  have hG := ((Bool.and_eq_true _ _).mp hE).2
  have hCF := ((Bool.and_eq_true _ _).mp hG).1
  have hC : r.callerCode = w.val + 1 := beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hCF).1
  obtain ⟨-, hRes, -, -, hB, hRO, -, -, -⟩ :=
    replyCallerFinalisable_parts ((Bool.and_eq_true _ _).mp hCF).2
  have hRo : st.objects[(⟨t.replyObjectCode - 1⟩ : SeLe4n.ReplyId).toObjId]? = some (.reply r) := by
    unfold SystemState.getObject? at hR; exact hR
  have hCancel : finaliseReplyCallerCancel st w t =
      finaliseReplyRevert (finaliseReplyCancel st r w t) t.blockingServer? := by
    unfold finaliseReplyCallerCancel
    rw [hR]
    dsimp only
    rw [if_pos hG]
  have FU := WaiterFrame.cancelUnframed st hInv hChain hB hRO hRo hC hN hT
  have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  have hI0 := Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st w t hInv
  have hRd0 := cancelIpcBlocking_victim_ready st w t hInv
    (lookupTcb_of_objects_of_not_reserved st w t hTo (by simpa using hRes))
  have hC1 : WaiterFrame st (finaliseReplyCancel st r w t) (· = w) ∧
      (finaliseReplyCancel st r w t).objects.invExt ∧
      ∀ t', (finaliseReplyCancel st r w t).getTcb? w = some t' → t'.ipcState = .ready := by
    unfold finaliseReplyCancel
    split
    · refine ⟨?_, cancelIpcBlockingReclaimed_objects_invExt w t st hI0, fun t' ht' => ?_⟩
      · unfold cancelIpcBlockingReclaimed descheduleUnboundHolder
        split
        · exact FU.trans (.of_objects_eq _ (cancelIpcBlockingMigrated_objects _ _ _))
        · exact (FU.trans (.of_objects_eq _ (cancelIpcBlockingMigrated_objects _ _ _))).trans
            (WaiterFrame.descheduleAtPlacement _ _ _)
      · have hM := cancelIpcBlockingReclaimed_getTcb? w t st w
        rw [ht'] at hM
        cases hc : (Lifecycle.Suspend.cancelIpcBlocking st w t).getTcb? w with
        | none => rw [hc] at hM; cases hM
        | some tc =>
          rw [hc] at hM
          simp only [Option.map_some, Option.some.injEq] at hM
          rw [(TCB.waiterKeyEq.of_withoutRunLinks hM).ipcState]
          exact hRd0 tc ((SystemState.getTcb?_eq_some_iff _ _ _).mp hc)
    · exact ⟨FU, hI0, fun t' ht' => hRd0 t' ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht')⟩
  obtain ⟨f1, hI1, hRd1⟩ := hC1
  unfold finaliseReplyWaiter
  rw [hCancel]
  obtain ⟨f2, hI2⟩ := finaliseReplyRevert_frame _ hI1 t.blockingServer? (· = w)
  obtain ⟨f2', -⟩ := finaliseReplyRevert_frame _ hI1 t.blockingServer? (fun _ => False)
  generalize finaliseReplyRevert (finaliseReplyCancel st r w t) t.blockingServer? = s2
    at f2 f2' hI2
  obtain ⟨f3, hW3⟩ := finaliseThreadSuspend_waiterFrame s2 hI2 w
  refine ⟨(f1.trans f2).trans f3, fun t' ht' => ?_⟩
  obtain ⟨t2, h2, k2⟩ := hW3 t' ht'
  obtain ⟨t1, h1, k1⟩ := f2'.bwd w t2 (fun h => h) h2
  rw [k2.ipcState, k1.ipcState]
  exact hRd1 t1 h1

-- ============================================================================
-- The loan return and the walk end every waiter
-- ============================================================================

/-- **The lender of a context `x` holds on loan is endable as `x`'s waiter**
(`tx`, `x`'s TCB): when `x`'s binding names an owner `L`, `L` is stored, its
reply is linked to no frame above (it heads the context's stack), and the guard
admits it. -/
def lenderEndable (st : SystemState) (x : SeLe4n.ThreadId) (tx : TCB) : Prop :=
  ∀ o, tx.scBindingOwnerCode = o + 1 → ∃ tl r, st.getTcb? ⟨o⟩ = some tl ∧
    st.getObject? ⟨tl.replyObjectCode - 1⟩ = some (.reply r) ∧
    (∀ a, r.next ≠ some (.frame a)) ∧ replyWaiterEndable st x ⟨o⟩ tl = true

/-- **The loan return and the walk end every caller waiting on `x`**
(WS-ZA ZA5.4 part 25): from a state carrying the finalisation's invariant in
which `x`'s lender, if any, is endable (`lenderEndable`) and every other thread
waiting on `x` is a plain waiter, the lender's pop (`finaliseThreadReturnLoan`)
and the walk (`finaliseThreadEndWaiters`) leave no thread waiting on `x`.  The
pop keeps every other waiter plain (`finaliseReplyWaiter_unframed`) and ends the
lender, so the walk starts from a queue of plain waiters
(`finaliseReplyWaiters_endsAll`).  Both keep `x` itself (`serverKept`). -/
theorem finaliseThreadEndWaiters_returnLoan_endsAll (s : SystemState) (x : SeLe4n.ThreadId)
    (tx : TCB) (h : finaliseStepInvariant s) (hX : s.getTcb? x = some tx)
    (hL : lenderEndable s x tx)
    (hAll : ∀ v, ReplyViews.waiterOf s.replyViews v x →
      (∀ o, tx.scBindingOwnerCode = o + 1 → v ≠ ⟨o⟩) → plainWaiterReady s x v) :
    (∀ v, ¬ ReplyViews.waiterOf
      (finaliseThreadEndWaiters (finaliseThreadReturnLoan s x) x).replyViews v x) ∧
    serverKept s (finaliseThreadEndWaiters (finaliseThreadReturnLoan s x) x) x := by
  have walk : ∀ s1 : SystemState, finaliseStepInvariant s1 →
      (∀ v, ReplyViews.waiterOf s1.replyViews v x → plainWaiterReady s1 x v) →
      (∃ tx1, s1.getTcb? x = some tx1) →
      (∀ v, ¬ ReplyViews.waiterOf (finaliseThreadEndWaiters s1 x).replyViews v x) ∧
        serverKept s1 (finaliseThreadEndWaiters s1 x) x := by
    intro s1 h1 hA1 ⟨tx1, hX1⟩
    unfold finaliseThreadEndWaiters
    rw [hX1]
    exact finaliseReplyWaiters_endsAll x _ s1 h1 hA1 ⟨tx1, hX1, Nat.le_refl _⟩
  cases hO : tx.scBindingOwnerCode with
  | zero =>
    have hR : finaliseThreadReturnLoan s x = s := by
      unfold finaliseThreadReturnLoan; rw [hX]; simp only [hO]
    rw [hR]
    exact walk s h (fun v hv => hAll v hv (fun o e => by rw [hO] at e; cases e)) ⟨tx, hX⟩
  | succ o =>
    obtain ⟨tl, r, hT, hRl, hN, hE⟩ := hL o hO
    have hR : finaliseThreadReturnLoan s x = finaliseReplyWaiter s ⟨o⟩ tl := by
      unfold finaliseThreadReturnLoan; rw [hX]; simp only [hO, hT, hE, if_true]
    rw [hR]
    obtain ⟨F, hEnd⟩ := finaliseReplyWaiter_unframed s h.2.1 h.2.2.2.2.1 hT hRl hN hE
    have hxL : ¬ x = ⟨o⟩ := by
      intro e
      unfold replyWaiterEndable at hE
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hE
      exact hE.1.1 (by rw [e])
    obtain ⟨tx', hX', -, -⟩ := F.fwd x tx hxL hX
    have hWk := walk _ (finaliseStepInvariant_replyWaiter h hT) (fun u hu => ?_) ⟨tx', hX'⟩
    · exact ⟨hWk.1, (F.serverKept hxL).trans hWk.2⟩
    obtain ⟨tu, htu, hsu⟩ := waiterOf_iff.mp hu
    have huL : ¬ u = ⟨o⟩ := by
      intro e; subst e
      have hr := hEnd tu htu
      unfold TCB.blockingServer? at hsu; rw [hr] at hsu; cases hsu
    obtain ⟨t0, h0, k0⟩ := F.bwd u tu huL htu
    have hu0 : ReplyViews.waiterOf s.replyViews u x :=
      waiterOf_iff.mpr ⟨t0, h0, k0.blockingServer.symm.trans hsu⟩
    exact F.ready huL (hAll u hu0 (fun o' e => by rw [hO] at e; cases e; exact huL))

/-- **The admission's queue walk reads every queued waiter but the lender as a
plain waiter**: along a queue `l` of `x`'s waiters, linked from `code`, the walk
`replyWaitersEndableFrom` with fuel at least `l`'s length admits each one but
the lender as endable with its reply on no stack (`plainWaiterOk_of_guard`). -/
theorem replyWaitersEndableFrom_plain {st : SystemState} {x : SeLe4n.ThreadId} {lc : Nat} :
    ∀ (l : List SeLe4n.ThreadId) (fuel code : Nat) (prev : Option SeLe4n.ThreadId),
      ReplyViews.chain st.replyViews prev (SeLe4n.ThreadId.ofOptCode code) l →
      l.length ≤ fuel → replyWaitersEndableFrom st x lc fuel code = true →
      ∀ v ∈ l, v.val + 1 ≠ lc → plainWaiterReady st x v
  | [], _, _, _, _, _, _, v, hv, _ => absurd hv (List.not_mem_nil)
  | w :: l', fuel, code, prev, hCh, hLen, hA, v, hv, hlc => by
    obtain ⟨hc, vw, hVw, -, hRest⟩ := hCh
    have hcode : code = w.val + 1 := (SeLe4n.ThreadId.ofOptCode_eq_some_iff _ _).mp hc
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hLen; omega⟩
    subst hcode
    have hW : (⟨w.val⟩ : SeLe4n.ThreadId) = w := rfl
    unfold replyWaitersEndableFrom at hA
    rw [hW] at hA
    cases hT : st.getTcb? w with
    | none => rw [hT] at hA; cases hA
    | some t =>
      rw [hT] at hA
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hA
      obtain ⟨hHd, hTl⟩ := hA
      have hVt : vw = t.replyView := by
        have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
        have e : st.replyViews w.toObjId = some t.replyView := by
          unfold SystemState.replyViews SystemState.getObject?; rw [hTo]; rfl
        rw [e] at hVw; cases hVw; rfl
      subst hVt
      rcases List.mem_cons.mp hv with e | hv'
      · subst e
        rcases hHd with h1 | ⟨hE, hU⟩
        · exact absurd h1 hlc
        · obtain ⟨r, hR, hok⟩ := plainWaiterOk_of_guard hE hU
          exact ⟨t, r, hT, hR, hok⟩
      · exact replyWaitersEndableFrom_plain l' f t.replyWaiterNextCode (some w) hRest
          (by simp at hLen; omega) hTl v hv' hlc

/-- **The admission's lender clause, with the finalisation's invariant, makes the
lender endable**: the lent context heads the lender's reply
(`lentContextHeadsLenderFrame`), so that reply is linked to no frame above, and
the admission reads the lender's guard.  The admission reads the loan's context
code too, so `x`'s binding is a loan (`.donated`). -/
theorem lenderEndable_of_admitted {s : SystemState} {x : SeLe4n.ThreadId} {tx : TCB}
    (h : finaliseStepInvariant s) (hX : s.getTcb? x = some tx)
    (hA : replyWaitersAdmitted s x tx = true) : lenderEndable s x tx := by
  intro o hO
  unfold replyWaitersAdmitted at hA
  rw [hO] at hA
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hA
  obtain ⟨⟨⟨hSc, -⟩, hM⟩, -⟩ := hA
  cases hT : s.getTcb? ⟨o⟩ with
  | none => rw [hT] at hM; cases hM
  | some tl =>
    rw [hT] at hM
    cases hS : tx.scBindingScCode with
    | zero => exact absurd hS hSc
    | succ c =>
      have hBind : tx.schedContextBinding = .donated ⟨c⟩ ⟨o⟩ := by
        show SchedContextBinding.ofCodes tx.scBindingScCode tx.scBindingOwnerCode = _
        rw [hS, hO]; rfl
      obtain ⟨rid, r, hRO, hRo, hN⟩ := h.2.2.2.2.2 x tx ⟨c⟩ ⟨o⟩ tl
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hX) hBind
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)
      have hcode : tl.replyObjectCode = rid.val + 1 :=
        (SeLe4n.ReplyId.ofOptCode_eq_some_iff _ _).mp hRO
      refine ⟨tl, r, rfl, ?_, (fun a e => by rw [hN] at e; cases e), hM⟩
      unfold SystemState.getObject?
      rw [hcode, Nat.add_sub_cancel]
      exact hRo

/-- **A finalised thread's loan return and walk end every caller waiting on it,
on a state its admission reads** (WS-ZA ZA5.4 part 25): on a state carrying the
finalisation's invariant on which `replyWaitersAdmitted` admits `x`, no thread
waits on `x` after the lender's pop and the walk — neither refuses midway.  The
admission's queue walk reads every waiter but the lender as plain
(`replyWaitersEndableFrom_plain`) and its lender clause makes the lender endable
(`lenderEndable_of_admitted`).  Both keep `x` itself (`serverKept`). -/
theorem finaliseThreadEndWaiters_returnLoan_endsAll_of_admitted (s : SystemState)
    (x : SeLe4n.ThreadId) (tx : TCB) (h : finaliseStepInvariant s)
    (hX : s.getTcb? x = some tx)
    (hA : replyWaitersAdmitted s x tx = true) :
    (∀ v, ¬ ReplyViews.waiterOf
      (finaliseThreadEndWaiters (finaliseThreadReturnLoan s x) x).replyViews v x) ∧
    serverKept s (finaliseThreadEndWaiters (finaliseThreadReturnLoan s x) x) x := by
  have hL := lenderEndable_of_admitted h hX hA
  unfold replyWaitersAdmitted at hA
  have hW := ((Bool.and_eq_true _ _).mp hA).2
  obtain ⟨l, hCh, hLen, -, hMem⟩ := h.2.2.2.1.1 x tx.replyView
    (SystemState.replyViews_of_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hX))
  refine finaliseThreadEndWaiters_returnLoan_endsAll s x tx h hX hL (fun v hv hne => ?_)
  refine replyWaitersEndableFrom_plain l tx.replyWaitersCount tx.replyWaitersHeadCode none hCh
    (by rw [hLen]; exact Nat.le_refl _) hW v ((hMem v).mpr hv) (fun e => ?_)
  exact hne v.val (by rw [← e]) rfl

end SeLe4n.Kernel
