/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvDonatedInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyUnheldInPlace

/-!
# A reply-receive answering a caller recording no server, each object written in its slot

WS-ZA ZA6.34: seL4-MCS's `seL4_ReplyRecv` through a reply capability whose
caller's server was finalised (`finaliseCap` leaves the caller blocked with no
server recorded, and `doReplyTransfer` lets any holder of the capability answer
it).  The reply leg wakes the caller and consumes its reply object
(`storeReplyLegReady`), `reply_pop` hands the context the reply object heads,
which no thread holds, to the caller (`returnUnheldSchedContextInPlace`, settled
on the caller's home core), and the receive leg blocks the replier on its
endpoint.  The receive's checks are read on the pre-state and carried across the
reply leg and the pop: the pop and the settle write only the caller's binding,
the reply stack's links and the context (`popFrame`), so every other reading the
receive makes is the one the pre-state gives (`popUnheldSettled_receiveGuard`).
The result is proven equal to the specification's
(`replyRecvOnCore_unheld_delivered`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section UnheldPopWrites

/-- **The unheld pop writes only what a pop writes**, each in its slot. -/
theorem returnUnheldSchedContextInPlace_popFrame (st : SystemState)
    (owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) :
    popFrame (returnUnheldSchedContextInPlace st owner scId) st := by
  unfold returnUnheldSchedContextInPlace
  split
  · exact popFrame.refl st
  · split
    · exact popFrame.refl st
    · split
      · exact popFrame.refl st
      · split
        · exact popFrame.refl st
        · dsimp only
          refine (markKeyChangeParts_popFrame _ _ _ _ _).trans
            ((markCandidacyGainFor_popFrame _ _ _).trans ?_)
          split
          · refine (popFrame_updateTcb _ _ _ ?_ ?_).trans
              ((popFrame_modifyObject _ _ _ ?_ ?_).trans
              (popFrame_updateSchedContext _ _ _ hNo))
            all_goals (repeat (first | exact hNo | apply updateTcb_noResizeDue |
              apply modifyObject_noResizeDue | apply updateSchedContext_noResizeDue |
              (intro o; cases o <;> rfl) | (intro _; rfl)))
          · refine (popFrame_updateTcb _ _ _ ?_ ?_).trans
              ((popFrame_modifyObject _ _ _ ?_ ?_).trans
              ((popFrame_modifyObject _ _ _ ?_ ?_).trans
              (popFrame_updateSchedContext _ _ _ hNo)))
            all_goals (repeat (first | exact hNo | apply updateTcb_noResizeDue |
              apply modifyObject_noResizeDue | apply updateSchedContext_noResizeDue |
              (intro o; cases o <;> rfl) | (intro _; rfl)))

/-- A context's update leaves a thread's slot as it was. -/
theorem updateSchedContext_tcbAt (s : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hNo : s.objects.noResizeDue) {x : SeLe4n.ObjId} {t : TCB}
    (hX : s.objects[x]? = some (.tcb t)) :
    (s.updateSchedContext scId f).objects[x]? = some (.tcb t) := by
  rw [SystemState.updateSchedContext_eq_impl]
  unfold SystemState.updateSchedContextImpl
  split
  · by_cases e : x = scId.toObjId
    · subst e; rw [objects_modifyObject_self _ _ _ hNo, hX]; rfl
    · rw [objects_modifyObject_ne _ _ _ hNo _ e, hX]
  · exact hX

/-- A reply's update leaves a thread's slot as it was. -/
theorem modifyReply_tcbAt (s : SystemState) (k : SeLe4n.ObjId) (f : Reply → Reply)
    (hNo : s.objects.noResizeDue) {x : SeLe4n.ObjId} {t : TCB}
    (hX : s.objects[x]? = some (.tcb t)) :
    (s.modifyObject k (SystemState.mapReplyObject f)).objects[x]? = some (.tcb t) := by
  by_cases e : x = k
  · subst e; rw [objects_modifyObject_self _ _ _ hNo, hX]; rfl
  · rw [objects_modifyObject_ne _ _ _ hNo _ e, hX]

/-- **The unheld pop leaves every thread but its recipient as it was.** -/
theorem returnUnheldSchedContextInPlace_tcbAt (st : SystemState)
    (owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) {x : SeLe4n.ObjId} {t : TCB} (hx : x ≠ owner.toObjId)
    (hX : st.objects[x]? = some (.tcb t)) :
    (returnUnheldSchedContextInPlace st owner scId).objects[x]? = some (.tcb t) := by
  unfold returnUnheldSchedContextInPlace
  split
  · exact hX
  · split
    · exact hX
    · split
      · exact hX
      · split
        · exact hX
        · dsimp only
          rw [markKeyChangeParts_objects, markCandidacyGainFor_objects]
          split
          · rw [objects_updateTcb_ne _ _ _ (modifyObject_noResizeDue _ _ _
              (updateSchedContext_noResizeDue _ _ _ hNo)) _ hx]
            exact modifyReply_tcbAt _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
              (updateSchedContext_tcbAt _ _ _ hNo hX)
          · rw [objects_updateTcb_ne _ _ _ (modifyObject_noResizeDue _ _ _ (modifyObject_noResizeDue _ _ _
              (updateSchedContext_noResizeDue _ _ _ hNo))) _ hx]
            exact modifyReply_tcbAt _ _ _ (modifyObject_noResizeDue _ _ _
              (updateSchedContext_noResizeDue _ _ _ hNo))
              (modifyReply_tcbAt _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
                (updateSchedContext_tcbAt _ _ _ hNo hX))

/-- **The unheld pop takes its head off the stack**: the reply object the
context heads ends with no links. -/
theorem returnUnheldSchedContextInPlace_reply (st : SystemState)
    (owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hr : SeLe4n.ReplyId) (r : Reply) (ot : TCB) (hNo : st.objects.noResizeDue)
    (hSc : st.getSchedContext? scId = some sc) (hH : sc.scReply = some hr)
    (hR : st.getReply? hr = some r) (hO : st.getTcb? owner = some ot)
    (hb : ∀ b, r.prev = some b → b ≠ hr) :
    (returnUnheldSchedContextInPlace st owner scId).objects[hr.toObjId]? =
      some (.reply { r with prev := none, next := none }) := by
  have hRo := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hOo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hO
  have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hOR : hr.toObjId ≠ owner.toObjId := fun e => by rw [e, hOo] at hRo; cases hRo
  have hSR : hr.toObjId ≠ scId.toObjId := fun e => by rw [e, hScO] at hRo; cases hRo
  have hU : ∀ f : SchedContext → SchedContext,
      (st.updateSchedContext scId f).objects[hr.toObjId]? = some (.reply r) := fun f => by
    rw [SystemState.updateSchedContext_eq_impl]
    unfold SystemState.updateSchedContextImpl
    rw [hSc]
    rw [objects_modifyObject_ne _ _ _ hNo _ hSR, hRo]
  unfold returnUnheldSchedContextInPlace
  simp only [hSc, hH, hR, hO]
  rw [markKeyChangeParts_objects, markCandidacyGainFor_objects]
  cases hP : r.prev with
  | none =>
    dsimp only
    rw [objects_updateTcb_ne _ _ _ (modifyObject_noResizeDue _ _ _
        (updateSchedContext_noResizeDue _ _ _ hNo)) _ hOR,
      objects_modifyObject_self _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo), hU]
    rfl
  | some b =>
    dsimp only
    have hbr : b.toObjId ≠ hr.toObjId := fun e =>
      hb b hP (SeLe4n.ReplyId.toObjId_injective _ _ e)
    rw [objects_updateTcb_ne _ _ _ (modifyObject_noResizeDue _ _ _ (modifyObject_noResizeDue _ _ _
        (updateSchedContext_noResizeDue _ _ _ hNo))) _ hOR,
      objects_modifyObject_ne _ _ _ (modifyObject_noResizeDue _ _ _
        (updateSchedContext_noResizeDue _ _ _ hNo)) _ (Ne.symm hbr),
      objects_modifyObject_self _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo), hU]
    rfl

end UnheldPopWrites

section UnheldReplyRecvGuard

/-- **The stack the unheld gate reads**: under `replyUnheldPopsInPlace` the
reply object heads the stack of a context naming it back, and the frame below
it, if any, is another reply object. -/
theorem replyUnheldPopsInPlace_stack (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hG : replyUnheldPopsInPlace st c rid = true) :
    ∃ rp scId sc, st.objects[rid.toObjId]? = some (.reply rp) ∧ rp.next = some (.head scId) ∧
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧ sc.scReply = some rid ∧
      (∀ b, rp.prev = some b → b ≠ rid) := by
  unfold replyUnheldPopsInPlace at hG
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨_, hM⟩ := hG
  cases hRg : st.getReply? rid with
  | none => rw [hRg] at hM; cases hM
  | some rp =>
  rw [hRg] at hM
  dsimp only at hM
  cases hN : rp.next with
  | none => rw [hN] at hM; cases hM
  | some l =>
  cases l with
  | frame _ => rw [hN] at hM; cases hM
  | head scId =>
  rw [hN] at hM
  dsimp only at hM
  simp only [Bool.and_eq_true] at hM
  obtain ⟨hSm, hU⟩ := hM
  cases hScg : st.getSchedContext? scId with
  | none => rw [hScg] at hSm; cases hSm
  | some sc =>
  rw [hScg] at hSm
  dsimp only at hSm
  have hHead : sc.scReply = some rid := by
    revert hSm
    cases sc.scReply with
    | none => intro h; cases h
    | some h =>
      intro e
      have : h = rid := by cases h; cases rid; simp only [beq_iff_eq] at e; subst e; rfl
      rw [this]
  refine ⟨rp, scId, sc, (SystemState.getReply?_eq_some_iff _ _ _).mp hRg, hN,
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hScg, hHead, ?_⟩
  intro b hb
  unfold unheldPopsInPlace at hU
  rw [hScg] at hU
  simp only [Bool.and_eq_true] at hU
  obtain ⟨_, _, hU⟩ := hU
  rw [hHead] at hU
  dsimp only at hU
  simp only [Bool.and_eq_true] at hU
  obtain ⟨_, hU⟩ := hU
  rw [hRg] at hU
  dsimp only at hU
  simp only [Bool.and_eq_true] at hU
  obtain ⟨_, hP⟩ := hU
  rw [hb] at hP
  dsimp only at hP
  simp only [Bool.and_eq_true] at hP
  obtain ⟨⟨⟨hbne, _⟩, _⟩, _⟩ := hP
  exact fun e => by subst e; simp at hbne

/-- **The unheld pop carries the receive's guard**: on the state the reply leg
to a caller recording no server and its unheld pop leave, the endpoint is as it
was, the replier may block on it and its block writes in place, each read on
the pre-state. -/
theorem popUnheldSettled_receiveGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (rt : TCB) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (home : CoreId)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) (hNext : rp.next = some (.head scId))
    (hScO : st.objects[scId.toObjId]? = some (.schedContext sc)) (hHead : sc.scReply = some rid)
    (hBelow : ∀ b, rp.prev = some b → b ≠ rid)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLeg st c rid msg) c scId) home scId).objects[epId]? = some (.endpoint ep) ∧
      (∃ rt1, (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
          (storeReplyLeg st c rid msg) c scId) home scId).objects[tid.toObjId]? = some (.tcb rt1) ∧
        receiveBlockAdmits rt1 = true) ∧
      receiveBlocksInPlace (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLeg st c rid msg) c scId) home scId) epId tid ep.receiveQ.tail (some rid) =
        true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hR; cases hR
  have hSc' : scId.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hScO; cases hScO
  have hSr : scId.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hScO; cases hScO
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo]
  generalize hS1 : storeReplyLegReady st c rid = S1
  have hAg := fun x hx hy => hS1 ▸ storeReplyLegReady_agree st c rid ct hNo hTc hFC x hx hy
  have hNo1 : S1.objects.noResizeDue := hS1 ▸ storeReplyLegReady_noResizeDue st c rid hNo
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyLegReady_keepsFinds st c rid hNo hFC
  obtain ⟨tc1, htc1, hcv⟩ := hS1 ▸ storeReplyLegReady_callerView st c rid ct hNo hTc hFC hRc
  have hc1 : tc1.ipcStateCode = (receiverReady ct).ipcStateCode := by
    have h := congrArg TCB.ipcStateCode hcv; exact h
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyLegReady_reply st c rid ct rp hNo hTc hFC hRp hRc
  generalize hTdef : S1.mapTcbInPlace c (holdMessage msg) = T
  have hNoT : T.objects.noResizeDue := by rw [← hTdef]; exact hNo1
  have hHold : ∀ x, x ≠ c.toObjId → T.objects[x]? = S1.objects[x]? := fun x hx => by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  have hTC : T.objects[c.toObjId]? = some (.tcb (holdMessage msg tc1)) := by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
  have hView : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (T.objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks := fun x hx hy => by
    rw [hHold _ hx]; exact hAg x hx hy
  have hTR : T.objects[rid.toObjId]? = some (.reply rp.consumed) := by rw [hHold _ hRc]; exact hR1
  have hKT : T.objectsKeepFinds st := by
    rw [← hTdef]; exact (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
  -- the pop's reads on `T`
  have hScT : T.getSchedContext? scId = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hSc' hSr) (fun _ e => by cases e) hScO)
  obtain ⟨rtT, hRtT, eT⟩ := agreeAt_tcb (hView _ hTc' hTr) hR
  have hHeadC : rp.consumed = { rp with callerCode := 0 } := Reply.consumed_of_head rp scId hNext
  have hPr := returnUnheldSchedContextInPlace_reply T c scId sc rid rp.consumed (holdMessage msg tc1)
    hNoT hScT hHead ((SystemState.getReply?_eq_some_iff _ _ _).mpr hTR)
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC)
    (fun b hb => hBelow b (by rw [hHeadC] at hb; exact hb))
  have hPt := returnUnheldSchedContextInPlace_tcbAt T c scId hNoT hTc' hRtT
  have hFr := returnUnheldSchedContextInPlace_popFrame T c scId hNoT
  generalize returnUnheldSchedContextInPlace T c scId = Rr at hPt hPr hFr
  have hAgS := SchedContextOps.settleReturnedContext_agree Rr home scId
  have hF := (settleReturnedContext_popFrame Rr home scId).trans hFr
  generalize SchedContextOps.settleReturnedContext Rr home scId = P at hAgS hF
  have hPt' : P.objects[tid.toObjId]? = some (.tcb rtT) :=
    releaseAgreeAt_of_not_sc hAgS hPt (fun _ e => by cases e)
  have hPr' : P.objects[rid.toObjId]? =
      some (.reply { rp.consumed with prev := none, next := none }) :=
    releaseAgreeAt_of_not_sc hAgS hPr (fun _ e => by cases e)
  have hComb : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (P.objects[x]?).map popFieldsView = (st.objects[x]?).map popFieldsView :=
    fun x hx hy => (hF.2.2.2 x).trans (popAgreeAt_of_runLinks (hView x hx hy))
  obtain ⟨tcP, hPC, ecP⟩ := popAgreeAt_tcb (hF.2.2.2 c.toObjId) hTC
  refine ⟨popAgreeAt_endpoint (hComb _ hEc hEr) hE, ⟨rtT, hPt', ?_⟩, ?_⟩
  · have : receiveBlockAdmits rtT = receiveBlockAdmits rtT.withoutRunLinks := rfl
    rw [this, eT]; exact hA
  · unfold receiveBlocksInPlace
    have hKP : P.objectsKeepFinds st := hF.2.2.1.trans hKT
    have hV : ∀ x, P.getObjectType? x = st.getObjectType? x := by
      intro x
      by_cases hxc : x = c.toObjId
      · subst hxc; unfold SystemState.getObjectType?; rw [hPC, hT]; rfl
      · by_cases hxr : x = rid.toObjId
        · subst hxr; unfold SystemState.getObjectType?; rw [hPr', hRp]; rfl
        · exact getObjectType?_of_popAgree (hComb x hxc hxr)
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨enqueuesInPlace_of_frame _ _ _ hKP hV ?_ hEnq, ?_⟩, ?_⟩
    · intro p hp
      by_cases hpc : p.toObjId = c.toObjId
      · exact Option.isSome_iff_exists.mpr
          ⟨tcP, (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hpc ▸ hPC)⟩
      · by_cases hpr : p.toObjId = rid.toObjId
        · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
          have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hx
          rw [hpr, hRp] at this; cases this
        · exact getTcb?_isSome_of_popAgree (hComb _ hpc hpr) hp
    · have hFree : ({ rp.consumed with prev := none, next := none } : Reply).isFree = true := by
        have h := Reply.consumed_caller rp
        simp only [Reply.caller] at h
        simp only [Reply.isFree, Reply.caller, h, Option.isNone_none, Bool.and_self]
      have hSt : P.replyStashedAt rid { rp.consumed with prev := none, next := none } = false := by
        rw [replyStashedAt_eq_stasherTestAt]
        rw [replyStashedAt_eq_stasherTestAt] at hStash
        show (match rp.consumed.stasherCode with
          | 0 => false
          | k + 1 => stasherTestAt P (⟨k⟩ : SeLe4n.ThreadId) (rid.val + 1)) = false
        rw [Reply.consumed_stasherCode]
        revert hStash
        cases rp.stasherCode with
        | zero => intro _; rfl
        | succ k =>
          intro hStash
          dsimp only at hStash ⊢
          by_cases hkc : (⟨k⟩ : SeLe4n.ThreadId).toObjId = c.toObjId
          · unfold stasherTestAt SystemState.getTcb?
            rw [hkc, hPC]
            have e := congrArg TCB.ipcStateCode ecP
            simp only [TCB.withoutRunLinks] at e
            simp only [e]
            show ((holdMessage msg tc1).ipcStateCode == 1 && _) = false
            have e2 : (holdMessage msg tc1).ipcStateCode = tc1.ipcStateCode := rfl
            simp only [e2, hc1, receiverReady, TCB.setIpcState_ipcStateCode]
            rfl
          · by_cases hkr : (⟨k⟩ : SeLe4n.ThreadId).toObjId = rid.toObjId
            · unfold stasherTestAt SystemState.getTcb?; rw [hkr, hPr']
            · rw [stasherTestAt_of_popAgree (hComb _ hkc hkr)]; exact hStash
      simp only [SystemState.replyStashValid]
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hPr']
      simp only [hSt, hFree]
      rfl
    · show replyRecordsInPlace _ (rid.val + 1) = true
      simp only [replyRecordsInPlace, Bool.and_eq_true] at hRec ⊢
      exact ⟨(hKP _).trans hRec.1, storeLeavesIndexAndTypes_of_frame hV hRec.2⟩

end UnheldReplyRecvGuard

section UnheldReplyRecv

/-- **The reply-receive answering a caller recording no server, in place**:
under `replyUnheldPopsInPlace`, with no sender waiting and the replier's block
admissible (read on the pre-state and carried across the reply leg and the
pop, `popUnheldSettled_receiveGuard`), the specification's reply-receive is
the reply leg's writes, the unheld pop and its settle on the caller's home
core, the replier's block, its priority walk and the caller's staged message.
No holder loses a context, so none is taken off its core. -/
theorem replyRecvAnsweringOnCore_unheld_inPlace
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : answer = none →
      replyTransferInert st tid ct grant = true) :
    endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
      .ok ({ results := #[] }, replyRecvAnswerCaller answer
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock
            (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
              (storeReplyLeg st c rid msg) c ⟨replyHeadContextCode st rid - 1⟩)
              (determineTargetCore st c) ⟨replyHeadContextCode st rid - 1⟩) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c 0) ∧
      ∃ x, (removeRunnableOnCore (storeReceiveBlock
            (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
              (storeReplyLeg st c rid msg) c ⟨replyHeadContextCode st rid - 1⟩)
              (determineTargetCore st c) ⟨replyHeadContextCode st rid - 1⟩) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core).getTcb? tid = some x ∧
        x.ipcState = .blockedOnReceive epId := by
  obtain ⟨rp', scId, hRp', hN, hCode, hCRes, hNo, hLC, hFC, hLR, hFR, hPopR, hAppl⟩ :=
    replyUnheldPopsInPlace_pop st c rid msg ct hT hG
  rw [hRp] at hRp'
  cases hRp'
  obtain ⟨rp2, scId2, sc, hRp2, hN2, hScO, hHead, hBelow⟩ := replyUnheldPopsInPlace_stack st c rid hG
  rw [hRp] at hRp2
  cases hRp2
  rw [hN] at hN2
  injection hN2 with hN2
  injection hN2 with hN2
  subst hN2
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hEq, _⟩ := replyOnCore_eq_storeLeg st tid c none ct ep0 rid rp msg core hSz hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := popUnheldSettled_receiveGuard st c tid rid msg ct rp
    epId ep rt scId sc (determineTargetCore st c) hNo hT hFC hRp hN hScO hHead hBelow hNe hE hR
    hA hEnq hStash hRec
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hXf := replyRecvReplyTransfer_of_inert answer st tid c grant ct hTc hInert
  have hRecS : recordedReplyServer? st c = none := by
    simp only [recordedReplyServer?, hTc, hIpc]
  rw [← storeReplyLeg_eq_hold _ _ _ _ hNo] at hPopR
  simp only [SystemState.unlinkReplyWaiterOpt] at hEq
  generalize hS1 : storeReplyLeg st c rid msg = S1 at hEq hPopR hE1 hR1 hG1
  generalize hP : SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace S1 c scId)
    (determineTargetCore st c) scId = P at hPopR hE1 hR1 hG1
  have hEp1 : P.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE1
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core P =
      (removeRunnableOnCore (storeReceiveBlock P epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq P epId ep tid rt1 (some rid) core hE1 hS hR1 hA1 hG1]
    have hSnd : (receiveRendezvousSender? P epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [hSnd, ↓reduceIte]
  obtain ⟨tb, hTb, hBk⟩ := receiveBlock_receiver_blocked P epId ep tid rt1 (some rid) core hE1 hR1
    hA1 hG1
  refine ⟨?_, tb, hTb, hBk⟩
  have hRes : tid.isReserved = false := by
    have h := hG1
    simp only [receiveBlocksInPlace, enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1.1.1.1.1
  unfold endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_none, hEq, hPopR, hXf, hRecv, hEp1, Option.bind_some, hS,
    replyRecvPostReceiveDonation_none_self _ _ _ _ hRes]
  simp [applyReceiveLegPipHandoff, Architecture.stageWokenSendCompletion_none]

theorem replyRecvOnCore_unheld_inPlace (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : replyTransferInert st tid ct grant = true) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock
            (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
              (storeReplyLeg st c rid msg) c ⟨replyHeadContextCode st rid - 1⟩)
              (determineTargetCore st c) ⟨replyHeadContextCode st rid - 1⟩) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c 0) ∧
      ∃ x, (removeRunnableOnCore (storeReceiveBlock
            (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
              (storeReplyLeg st c rid msg) c ⟨replyHeadContextCode st rid - 1⟩)
              (determineTargetCore st c) ⟨replyHeadContextCode st rid - 1⟩) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core).getTcb? tid = some x ∧
        x.ipcState = .blockedOnReceive epId :=
  replyRecvAnsweringOnCore_unheld_inPlace none st epId tid c rid msg grant core ct ep0 rt ep rp hSz hT hIpc hRO hG hNe hE hS hR hA hEnq
    hRp hStash hRec (fun _ => hInert)

end UnheldReplyRecv

section UnheldReplyRecvDelivered

/-- The reply-receive answering a caller recording no server, its caller woken
holding no message: the reply leg's writes, the unheld pop and its settle, the
replier's block on the endpoint, then its priority walk. -/
@[noinline] def storeReplyRecvUnheldReady (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (core : CoreId) : SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore
    (removeRunnableOnCore (storeReceiveBlock
      (SchedContextOps.settleReturnedContext
        (returnUnheldSchedContextInPlace (storeReplyLegReady st c rid) c scId) home scId) epId tid
      tailCode (rid.val + 1)) tid core) tid core).1

/-- **The reply-receive answering a caller recording no server, delivered**:
under the guard of `replyRecvOnCore_unheld_inPlace` and a reply of at most four
words, the checked arm's result is the caller's frame written into its saved
registers on top of `storeReplyRecvUnheldReady`; the replier, blocked on the
endpoint, stages nothing. -/
theorem replyRecvOnCore_unheld_delivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters) (hSz4 : msg.registers.size ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : replyTransferInert st tid ct grant = true) :
    (match endpointReplyRecvOnCore epId tid rid c msg grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), writeDeliveredFrameIfReady
        (storeReplyRecvUnheldReady st c tid rid ⟨replyHeadContextCode st rid - 1⟩
          (determineTargetCore st c) epId ep.recvTailCode core) c
        (Architecture.returnFrameOfMessage msg 0 0)
        (fun _ => (storeReplyRecvUnheldReady st c tid rid ⟨replyHeadContextCode st rid - 1⟩
          (determineTargetCore st c) epId ep.recvTailCode core).mapTcbInPlace c
          (holdMessage msg))) := by
  obtain ⟨_, _, _, _, _, _, hNo, _⟩ := replyUnheldPopsInPlace_pop st c rid msg ct hT hG
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvOnCore_unheld_inPlace st epId tid c rid msg grant core
    ct ep0 rt ep rp hSz hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hStash hRec hInert
  rw [hEq]
  simp only [CapTransferSummary.capInfo_empty]
  revert hX
  generalize (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId
  intro hX
  have h1 := storeReplyLegReady_noResizeDue st c rid hNo
  have h2 := settleReturnedContext_noResizeDue _ (determineTargetCore st c) scId
    (returnUnheldSchedContextInPlace_noResizeDue _ c scId h1)
  have h3 := storeReceiveBlock_noResizeDue _ epId tid ep.recvTailCode
    (SeLe4n.ReplyId.optCode (some rid)) h2
  have h4 := removeRunnableOnCore_noResizeDue _ tid core h3
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo, returnUnheldSchedContextInPlace_msg c id _ id _ c scId h1,
    settleReturnedContext_msg, storeReceiveBlock_msg _ _ _ _ _ _ _ h2 hNe,
    removeRunnableOnCore_msg] at hX ⊢
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hX
  rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ h4,
    stageDeliveredMessage_holdMessage _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ h4) hSz4]
  obtain ⟨x2, hX2, e2⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h4 tid x hX
  rw [stageDeliveredMessage_writeDeliveredFrameIfReady_blocked _ c tid _ _ 0 hCT x2 hX2
    (by rw [e2, hB]; exact fun h => by cases h)]
  rfl

end UnheldReplyRecvDelivered

/-- **The reply-receive answering a caller recording no server, delivered from
the registers**: `storeReplyRecvUnheldReady`'s writes, then the reply's frame
written into the caller's saved registers.  The message is built only where the
caller is, unexpectedly, not ready. -/
@[noinline] def performReplyRecvUnheldDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId) : SystemState :=
  let X := storeReplyRecvUnheldReady st c tid rid scId home epId tailCode core
  writeDeliveredFrameIfReady X c (Architecture.regReplyRecvFrame layout rf len badge)
    (fun _ => holdReplyRecvBody X c layout rf len badge)

end SeLe4n.Kernel
