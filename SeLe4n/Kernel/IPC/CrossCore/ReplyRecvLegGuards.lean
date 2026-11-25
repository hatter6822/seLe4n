/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyHeldInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvUnlinkedTakeInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvDonatedCallTakeInPlace

/-!
# The reply leg's guards, one family over every pop arm

WS-SX SX25.1.  The reply-receive's reply leg ends in one of five arms: no pop
(the caller recorded the server and lent it nothing), the donated pop, the held
pop, the unheld pop, or no pop on a reply linked to nothing.  Each receive leg
the composed path runs after it (block, take, donating take) reads a guard on
the state the reply leg leaves, and checks it on the pre-state.  The guards are
carried by one shape per receive leg: the reply's writes, then the pop's, which
leave every thread but the pop's own (the caller and the context's holder) as it
was (`returnDonatedSchedContextInPlace_tcbAt`,
`keepDonatedSchedContextInPlace_tcbAt`, `returnUnheldSchedContextInPlace_tcbAt`)
and write nothing else a guard reads (`popFrame`).

The family, per pop arm and receive leg: the take's guard across the donated
and held pops (`popDonationSettled_takeGuard`, `keepHeldPop_takeGuard`; the
unheld pop's is `popUnheldSettled_takeGuard`), and the Call take's across the
unheld pop, which donates the queued caller's context to a server holding none
(`popUnheldSettled_callDonationGuard`), and across the held pop, which leaves
the server bound to the context it keeps, so the take donates nothing
(`keepHeldPop_callTakeGuard`, read through `receiveCallTakesPastPop`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section ReplyLegGuards

/-- **The donated pop leaves every thread but its two as it was**: the context's
holder and its recipient. -/
theorem returnDonatedSchedContextInPlace_tcbAt (st : SystemState)
    (holder owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) {x : SeLe4n.ObjId} {t : TCB}
    (hxo : x ≠ owner.toObjId) (hxh : x ≠ holder.toObjId)
    (hX : st.objects[x]? = some (.tcb t)) :
    (returnDonatedSchedContextInPlace st holder owner scId).objects[x]? = some (.tcb t) := by
  unfold returnDonatedSchedContextInPlace
  split
  · exact hX
  · split
    · exact hX
    · split
      · exact hX
      · split
        · exact hX
        · split
          · exact hX
          · dsimp only
            rw [markKeyChangeParts_objects, markCandidacyGainFor_objects, markKeyChangeParts_objects,
              markCandidacyGainFor_objects]
            rw [objects_updateTcb_ne _ _ _ (by
                split <;> repeat (first
                  | assumption
                  | apply updateTcb_noResizeDue
                  | apply modifyObject_noResizeDue
                  | apply updateSchedContext_noResizeDue)) _ hxh,
              objects_updateTcb_ne _ _ _ (by
                  split <;> repeat (first
                    | assumption
                    | apply updateTcb_noResizeDue
                    | apply modifyObject_noResizeDue
                    | apply updateSchedContext_noResizeDue)) _ hxo]
            split <;> repeat (first
                | assumption
                | apply modifyReply_tcbAt
                | apply updateSchedContext_tcbAt
                | apply modifyObject_noResizeDue
                | apply updateSchedContext_noResizeDue)

/-- **The held pop leaves every thread but the holder as it was.** -/
theorem keepDonatedSchedContextInPlace_tcbAt (st : SystemState)
    (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) {x : SeLe4n.ObjId} {t : TCB} (hxh : x ≠ holder.toObjId)
    (hX : st.objects[x]? = some (.tcb t)) :
    (keepDonatedSchedContextInPlace st holder scId).objects[x]? = some (.tcb t) := by
  unfold keepDonatedSchedContextInPlace
  split
  · exact hX
  · split
    · exact hX
    · split
      · exact hX
      · split
        · exact hX
        · dsimp only
          rw [objects_updateTcb_ne _ _ _ (by
              split <;> repeat (first
                | assumption
                | apply updateTcb_noResizeDue
                | apply modifyObject_noResizeDue
                | apply updateSchedContext_noResizeDue)) _ hxh]
          split <;> repeat (first
              | assumption
              | apply modifyReply_tcbAt
              | apply updateSchedContext_tcbAt
              | apply modifyObject_noResizeDue
              | apply updateSchedContext_noResizeDue)

/-- **The take's guard across the reply leg and the donated pop with its
settle**: on the state they leave, the endpoint is as it was, the sender a
thread keeping every word the take reads, and the take's in-place guard, read
on the pre-state, still holds.  The pop writes the caller's and the holder's
bindings, the stack's links and the context, never the sender's slot. -/
theorem popDonationSettled_takeGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (scId : SeLe4n.SchedContextId) (home : CoreId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c) (hST : s ≠ tid)
    (hG : receiveTakesInPlace st epId tid s sTcb = true) :
    (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId
        home).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId
          home).objects[s.toObjId]? = some (.tcb sTcb1) ∧
        SenderWordsKept sTcb1 sTcb ∧
        receiveTakesInPlace (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid
          scId home) epId tid s sTcb1 = true := by
  have hSc' : s.toObjId ≠ c.toObjId := fun e => hSC (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hSt' : s.toObjId ≠ tid.toObjId := fun e => hST (SeLe4n.ThreadId.toObjId_injective _ _ e)
  obtain ⟨hE1, sTcb1, hS1, hK, hG1⟩ := storeReplyRendezvous_takeGuard st c tid rid msg ct rp epId
    ep s sTcb hNo hT hFC hRp hE hS hSC hG
  have hNoT := storeReplyRendezvous_noResizeDue st c tid rid msg hNo
  unfold popDonationSettledInPlace
  generalize storeReplyRendezvous st c tid rid msg = T at hE1 hS1 hG1 hNoT
  have hPt := returnDonatedSchedContextInPlace_tcbAt T tid c scId hNoT hSc' hSt' hS1
  have hFr := returnDonatedSchedContextInPlace_popFrame T tid c scId hNoT
  generalize returnDonatedSchedContextInPlace T tid c scId = Rr at hPt hFr
  have hPt' := releaseAgreeAt_of_not_sc (SchedContextOps.settleReturnedContext_agree Rr home scId)
    hPt (fun _ e => by cases e)
  have hF := (settleReturnedContext_popFrame Rr home scId).trans hFr
  obtain ⟨hEP, hGP⟩ := takeGuard_of_popFrame hF hE1 hG1
  exact ⟨hEP, sTcb1, hPt', hK, hGP⟩

/-- **The take's guard across the reply leg and the held pop**: the held pop
writes the holder's binding, the stack's links and the context, never the
sender's slot. -/
theorem keepHeldPop_takeGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (scId : SeLe4n.SchedContextId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c) (hST : s ≠ tid)
    (hG : receiveTakesInPlace st epId tid s sTcb = true) :
    (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
        scId).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
          scId).objects[s.toObjId]? = some (.tcb sTcb1) ∧
        SenderWordsKept sTcb1 sTcb ∧
        receiveTakesInPlace (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg)
          tid scId) epId tid s sTcb1 = true := by
  have hSt' : s.toObjId ≠ tid.toObjId := fun e => hST (SeLe4n.ThreadId.toObjId_injective _ _ e)
  obtain ⟨hE1, sTcb1, hS1, hK, hG1⟩ := storeReplyRendezvous_takeGuard st c tid rid msg ct rp epId
    ep s sTcb hNo hT hFC hRp hE hS hSC hG
  have hNoT := storeReplyRendezvous_noResizeDue st c tid rid msg hNo
  generalize storeReplyRendezvous st c tid rid msg = T at hE1 hS1 hG1 hNoT
  have hPt := keepDonatedSchedContextInPlace_tcbAt T tid scId hNoT hSt' hS1
  obtain ⟨hEP, hGP⟩ := takeGuard_of_popFrame (keepDonatedSchedContextInPlace_popFrame T tid scId hNoT)
    hE1 hG1
  exact ⟨hEP, sTcb1, hPt, hK, hGP⟩

/-- **The unheld pop keeps every other thread and context**: it writes the
context it returns, reply objects and its recipient's binding, so a thread
other than the recipient and a context other than the returned one stand as
they were. -/
theorem returnUnheldSchedContextInPlace_keepsAt (S : SystemState)
    (owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : S.objects.noResizeDue) {x : SeLe4n.ObjId} {o : KernelObject}
    (hx : S.objects[x]? = some o)
    (hT : ∀ u, o = .tcb u → x ≠ owner.toObjId)
    (hS : ∀ sc, o = .schedContext sc → x ≠ scId.toObjId)
    (hR : ∀ r, o ≠ .reply r) :
    (returnUnheldSchedContextInPlace S owner scId).objects[x]? = some o := by
  have hRp : ∀ (g : Reply → Reply) (k : SeLe4n.ObjId), x = k →
      SystemState.mapReplyObject g o = o := fun g _ _ => by
    cases o with
    | reply r => exact absurd rfl (hR r)
    | _ => rfl
  unfold returnUnheldSchedContextInPlace
  split
  · exact hx
  split
  · exact hx
  split
  · exact hx
  split
  · exact hx
  dsimp only
  rw [markKeyChangeParts_objects, markCandidacyGainFor_objects]
  have hN : ∀ {s : SystemState}, s.objects.noResizeDue → ∀ k F,
      (s.modifyObject k F).objects.noResizeDue := fun h k F => modifyObject_noResizeDue _ k F h
  apply updateTcb_keepsAt _ _ _ ?_ ?_ hT
  · split
    · exact hN (updateSchedContext_noResizeDue _ _ _ hNo) _ _
    · exact hN (hN (updateSchedContext_noResizeDue _ _ _ hNo) _ _) _ _
  split
  · exact modifyObject_keepsAt _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
      (updateSchedContext_keepsAt _ _ _ hNo hx hS) (hRp _ _)
  · exact modifyObject_keepsAt _ _ _ (hN (updateSchedContext_noResizeDue _ _ _ hNo) _ _)
      (modifyObject_keepsAt _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
        (updateSchedContext_keepsAt _ _ _ hNo hx hS) (hRp _ _)) (hRp _ _)

/-- **The donating take's guard across the reply leg, the unheld pop and its
settle**: `popDonationSettled_callDonationGuard` for the unheld pop.  The pop
returns the context to the caller and never writes the server, so the server
holds no context after it only if it held none before (`hRt0`); the pop frees
the reply object, and writes nothing else the guard reads. -/
theorem popUnheldSettled_callDonationGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (home : CoreId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb rt : TCB) (P : SystemState)
    (hP : SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
      (storeReplyLeg st c rid msg) c scId) home scId = P)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) (hNext : rp.next = some (.head scId))
    (hScO : st.objects[scId.toObjId]? = some (.schedContext sc)) (hHead : sc.scReply = some rid)
    (hBelow : ∀ b, rp.prev = some b → b ≠ rid)
    (hNe : tid ≠ c)
    (hLR : storeLeavesIndexAndTypes st rid.toObjId .reply = true)
    (hFR : st.objects.findsInPlace rid.toObjId = true)
    (hRtT : st.getTcb? tid = some rt) (hRt0 : rt.scBindingScCode = 0)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hG : receiveCallDonatesPastPop st epId tid s sTcb rid (scId.val + 1) = true) :
    P.objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcbP, P.objects[s.toObjId]? = some (.tcb sTcbP) ∧ SenderWordsKept sTcbP sTcb ∧
        sTcbP.scBindingScCode = sTcb.scBindingScCode ∧
        determineTargetCore P s = determineTargetCore st s ∧
        determineTargetCore P tid = determineTargetCore st tid ∧
        receiveCallDonatesInPlace P epId tid s sTcbP rid = true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hR : st.objects[tid.toObjId]? = some (.tcb rt) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hRtT
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hR; cases hR
  have hSc' : scId.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hScO; cases hScO
  have hSr : scId.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hScO; cases hScO
  have hsc : s.toObjId ≠ c.toObjId := fun e => hSC (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hsr : s.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hS; cases hS
  -- the guard, read on the pre-state
  have hG' := hG
  simp only [receiveCallDonatesPastPop, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hSW, hRRes⟩, hRS⟩, hRN⟩, hLRt⟩, hFRt⟩, hRO⟩, hCall⟩, hPopNe⟩, hCtx⟩ := hG'
  obtain ⟨k, hk⟩ : ∃ k, sTcb.scBindingScCode = k + 1 := by
    cases h : sTcb.scBindingScCode with
    | zero => simp only [callerContextReady, h, Bool.false_eq_true] at hCtx
    | succ k => exact ⟨k, rfl⟩
  have hCtx' := hCtx
  unfold callerContextReady at hCtx'
  rw [hk] at hCtx'
  simp only [Bool.and_eq_true] at hCtx'
  obtain ⟨⟨hLsc, hFsc⟩, hScM⟩ := hCtx'
  obtain ⟨scs, hScs⟩ : ∃ scs, st.getSchedContext? ⟨k⟩ = some scs := by
    cases h : st.getSchedContext? ⟨k⟩ with
    | none => rw [h] at hScM; cases hScM
    | some scs => exact ⟨scs, rfl⟩
  rw [hScs] at hScM
  simp only [Bool.and_eq_true] at hScM
  have hScsO : st.objects[(SeLe4n.SchedContextId.toObjId ⟨k⟩)]? = some (.schedContext scs) :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hScs
  have hkc : (SeLe4n.SchedContextId.toObjId ⟨k⟩) ≠ c.toObjId := fun e => by
    rw [e, hT] at hScsO; cases hScsO
  have hkr : (SeLe4n.SchedContextId.toObjId ⟨k⟩) ≠ rid.toObjId := fun e => by
    rw [e, hRp] at hScsO; cases hScsO
  have hkS : (SeLe4n.SchedContextId.toObjId ⟨k⟩) ≠ scId.toObjId := fun e => by
    have := SeLe4n.SchedContextId.toObjId_injective _ _ e
    subst this
    rw [hk] at hPopNe
    exact hPopNe rfl
  -- the reply leg
  have hKS := storeReplyLegReady_keepsSendCaps st c rid hNo
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo] at hP
  generalize hS1 : storeReplyLegReady st c rid = S1 at hKS hP
  have hAg := fun x hx hy => hS1 ▸ storeReplyLegReady_agree st c rid ct hNo hTc hFC x hx hy
  have hNo1 : S1.objects.noResizeDue := hS1 ▸ storeReplyLegReady_noResizeDue st c rid hNo
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyLegReady_keepsFinds st c rid hNo hFC
  obtain ⟨tc1, htc1, -⟩ := hS1 ▸ storeReplyLegReady_callerView st c rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyLegReady_reply st c rid ct rp hNo hTc hFC hRp hRc
  generalize hTdef : S1.mapTcbInPlace c (holdMessage msg) = T at hP
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
  -- the pop
  have hScT : T.getSchedContext? scId = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hSc' hSr) (fun _ e => by cases e) hScO)
  obtain ⟨rtT, hRtT', eRt⟩ := agreeAt_tcb (hView _ hTc' hTr) hR
  have hB0 : rtT.scBindingScCode = 0 := by
    have := congrArg TCB.scBindingScCode eRt
    exact this.trans hRt0
  have hHeadC : rp.consumed = { rp with callerCode := 0 } := Reply.consumed_of_head rp scId hNext
  have hPr := returnUnheldSchedContextInPlace_reply T c scId sc rid rp.consumed
    (holdMessage msg tc1) hNoT hScT hHead ((SystemState.getReply?_eq_some_iff _ _ _).mpr hTR)
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC)
    (fun b hb => hBelow b (by rw [hHeadC] at hb; exact hb))
  have hPt := returnUnheldSchedContextInPlace_tcbAt T c scId hNoT hTc' hRtT'
  have hFr := returnUnheldSchedContextInPlace_popFrame T c scId hNoT
  obtain ⟨sTcb1, hS1o, e1⟩ := agreeAt_tcb (hAg _ hsc hsr) hS
  have hsT : T.objects[s.toObjId]? = some (.tcb sTcb1) := by rw [hHold _ hsc]; exact hS1o
  have hsR := returnUnheldSchedContextInPlace_tcbAt T c scId hNoT hsc hsT
  have hkT : T.objects[(SeLe4n.SchedContextId.toObjId ⟨k⟩)]? = some (.schedContext scs) := by
    rw [hHold _ hkc]; exact agreeAt_of_not_tcb (hAg _ hkc hkr) (fun _ e => by cases e) hScsO
  have hkR := returnUnheldSchedContextInPlace_keepsAt T c scId hNoT hkT
    (fun _ e => by cases e) (fun _ _ => hkS) (fun _ e => by cases e)
  generalize returnUnheldSchedContextInPlace T c scId = Rr at hPt hPr hFr hsR hkR hP
  have hAgS := SchedContextOps.settleReturnedContext_agree Rr home scId
  have hF := (settleReturnedContext_popFrame Rr home scId).trans hFr
  rw [hP] at hAgS hF
  have hPt' : P.objects[tid.toObjId]? = some (.tcb rtT) :=
    releaseAgreeAt_of_not_sc hAgS hPt (fun _ e => by cases e)
  have hPr' : P.objects[rid.toObjId]? =
      some (.reply { rp.consumed with prev := none, next := none }) :=
    releaseAgreeAt_of_not_sc hAgS hPr (fun _ e => by cases e)
  have hsP : P.objects[s.toObjId]? = some (.tcb sTcb1) :=
    releaseAgreeAt_of_not_sc hAgS hsR (fun _ e => by cases e)
  have hComb : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (P.objects[x]?).map popFieldsView = (st.objects[x]?).map popFieldsView :=
    fun x hx hy => (hF.2.2.2 x).trans (popAgreeAt_of_runLinks (hView x hx hy))
  obtain ⟨tcP, hPC, _⟩ := popAgreeAt_tcb (hF.2.2.2 c.toObjId) hTC
  obtain ⟨scP, hkP, ekP⟩ : ∃ scP, P.objects[(SeLe4n.SchedContextId.toObjId ⟨k⟩)]? =
      some (.schedContext scP) ∧ scP.withoutRelease = scs.withoutRelease := by
    have e := hAgS (SeLe4n.SchedContextId.toObjId ⟨k⟩)
    rw [hkR] at e
    cases e' : P.objects[(SeLe4n.SchedContextId.toObjId ⟨k⟩)]? with
    | none => rw [e'] at e; cases e
    | some o =>
      rw [e'] at e
      cases o <;> simp only [Option.map_some, Option.some.injEq, KernelObject.withoutRelease,
        reduceCtorEq, KernelObject.schedContext.injEq] at e
      exact ⟨_, rfl, e⟩
  -- the frame of the whole reply leg
  have hKP : P.objectsKeepFinds st := hF.2.2.1.trans hKT
  have hV : ∀ x, P.getObjectType? x = st.getObjectType? x := by
    intro x
    by_cases hxc : x = c.toObjId
    · subst hxc; unfold SystemState.getObjectType?
      rw [hPC, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc]; rfl
    · by_cases hxr : x = rid.toObjId
      · subst hxr; unfold SystemState.getObjectType?; rw [hPr', hRp]; rfl
      · exact getObjectType?_of_popAgree (hComb x hxc hxr)
  have hTcbP : ∀ p : SeLe4n.ThreadId, (st.getTcb? p).isSome = true →
      (P.getTcb? p).isSome = true := by
    intro p hp
    by_cases hpc : p.toObjId = c.toObjId
    · exact Option.isSome_iff_exists.mpr
        ⟨tcP, (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hpc ▸ hPC)⟩
    · by_cases hpr : p.toObjId = rid.toObjId
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
        have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hx
        rw [hpr, hRp] at this; cases this
      · exact getTcb?_isSome_of_popAgree (hComb _ hpc hpr) hp
  have hSL : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes P id ty = true :=
    fun h => storeLeavesIndexAndTypes_of_frame hV h
  -- the queued caller, as it was
  have hw : sTcb1.sendCapWords = sTcb.sendCapWords := by
    have k := hKS s.toObjId
    rw [hS1o, hS] at k
    simpa [KernelObject.sendCapWords] using k
  have hKept := SenderWordsKept.of_withoutRunLinks e1 hw
  have wl : ∀ {α : Type} (g : TCB → α), (∀ u : TCB, g u.withoutRunLinks = g u) →
      g sTcb1 = g sTcb := fun g hg => by rw [← hg sTcb1, ← hg sTcb, e1]
  have hBind : sTcb1.scBindingScCode = sTcb.scBindingScCode := wl TCB.scBindingScCode (fun _ => rfl)
  have hAff : sTcb1.cpuAffinity = sTcb.cpuAffinity := wl TCB.cpuAffinity (fun _ => rfl)
  have hROc : sTcb1.replyObjectCode = sTcb.replyObjectCode := wl TCB.replyObjectCode (fun _ => rfl)
  have hQ : sTcb1.queueNext = sTcb.queueNext := by simp only [TCB.queueNext, hKept.queueNext]
  have hDs : determineTargetCore P s = determineTargetCore st s := by
    unfold determineTargetCore
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hsP, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hS]
    dsimp only
    rw [hAff]
  have hDt : determineTargetCore P tid = determineTargetCore st tid := by
    have ha : rtT.cpuAffinity = rt.cpuAffinity := by
      have := congrArg TCB.cpuAffinity eRt
      exact this
    unfold determineTargetCore
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hPt', hRtT]
    dsimp only
    rw [ha]
  refine ⟨popAgreeAt_endpoint (hComb _ hEc hEr) hE, sTcb1, hsP, hKept, hBind, hDs, hDt, ?_⟩
  have hFree : ({ rp.consumed with prev := none, next := none } : Reply).isFree = true := by
    have h := Reply.consumed_caller rp
    simp only [Reply.caller] at h
    simp only [Reply.isFree, Reply.caller, h, Option.isNone_none, Bool.and_self]
  have hPtG : P.getTcb? tid = some rtT := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hPt'
  have hPrG : P.getReply? rid = some { rp.consumed with prev := none, next := none } :=
    (SystemState.getReply?_eq_some_iff _ _ _).mpr hPr'
  have hkPG : P.getSchedContext? ⟨k⟩ = some scP :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hkP
  have hBT : scP.boundThreadCode = scs.boundThreadCode := by
    have := congrArg SchedContext.boundThreadCode ekP
    exact this
  have hSRp : scP.scReply = scs.scReply := by
    have := congrArg SchedContext.scReply ekP
    exact this
  have hRO' : sTcb1.replyObject = sTcb.replyObject := by simp only [TCB.replyObject, hROc]
  have hSWP := sendWakesInPlace_of_frame epId s sTcb.queueNext hKP hV hTcbP hSW
  have hLRtP := hSL hLRt
  have hFRtP := (hKP _).trans hFRt
  have hLRP := hSL hLR
  have hFRP := (hKP _).trans hFR
  have hLscP := hSL hLsc
  have hFscP := (hKP _).trans hFsc
  unfold receiveCallDonatesInPlace receiveCallTakesReplyInPlace
  rw [hPtG, hPrG, hQ, hRO', hKept.ipcState]
  simp only [callDonationReady_eq_callerContextReady, callerContextReady, hBind, hk, hkPG, hBT,
    hSRp, hB0, hFree, hKept.canGrant, hKept.canGrantReply, Bool.and_eq_true, Bool.not_eq_true',
    bne_iff_ne, ne_eq, beq_self_eq_true, Option.isSome_some, Bool.true_and]
  and_intros
  all_goals (first | assumption | trivial | skip)
  · exact hScM.1
  · have hM := hScM.2
    revert hM
    cases scs.scReply with
    | none => intro _; rfl
    | some old =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isSome_iff_exists]
      rintro ⟨⟨⟨hOR, hOL⟩, hOF⟩, oR, hoR⟩
      have hoRo := (SystemState.getReply?_eq_some_iff _ _ _).mp hoR
      have hoc : old.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hoRo; cases hoRo
      have hor : old.toObjId ≠ rid.toObjId := fun e =>
        hOR (SeLe4n.ReplyId.toObjId_injective _ _ e)
      obtain ⟨oR', hoR', _⟩ := popAgreeAt_reply (hComb _ hoc hor) hoRo
      exact ⟨⟨⟨hOR, hSL hOL⟩, (hKP _).trans hOF⟩, oR',
        (SystemState.getReply?_eq_some_iff _ _ _).mpr hoR'⟩

/-- **The receive leg's take of a caller after a held pop, checked before the
reply leg**: every check of `receiveCallTakesInPlace` that the reply leg and the
held pop leave standing, read on the pre-state.  The two the pop settles are not
asked here: it frees the reply object and leaves the server holding the context
it keeps, so the take donates nothing (`keepHeldPop_callTakeGuard`). -/
@[inline] def receiveCallTakesPastPop (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) : Bool :=
  sendWakesInPlace st endpointId s sTcb.queueNext &&
  !receiver.isReserved && receiver != s &&
  (match sTcb.queueNext with
   | none => true
   | some n => receiver != n) &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  sTcb.replyObject.isNone &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => sTcb.ipcCanGrant || sTcb.ipcCanGrantReply
   | _ => false)

/-- `receiveCallTakesPastPop` as it is compiled: the caller's successor asked
of its link code. -/
@[inline] def receiveCallTakesPastPopImpl (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) : Bool :=
  sendWakesInPlaceCode st endpointId s sTcb.queueNextCode &&
  !receiver.isReserved && receiver != s &&
  queueSuccessorDiffers receiver sTcb.queueNextCode &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  sTcb.replyObject.isNone &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => sTcb.ipcCanGrant || sTcb.ipcCanGrantReply
   | _ => false)

@[csimp] theorem receiveCallTakesPastPop_eq_impl :
    @receiveCallTakesPastPop = @receiveCallTakesPastPopImpl := by
  funext st endpointId receiver s sTcb
  unfold receiveCallTakesPastPop receiveCallTakesPastPopImpl
  rw [sendWakesInPlaceCode_eq, queueSuccessorDiffers_eq, TCB.ofOptCode_queueNextCode]
  rfl

/-- **The Call take's guard across the reply leg and the held pop**: on the
state they leave, the endpoint is as it was, the queued caller `s` a thread
keeping every word the take reads, its binding and its home, the server keeps
its home, and the take's in-place guard (`receiveCallTakesInPlace`) holds, each
read on the pre-state (`receiveCallTakesPastPop`): the held pop frees the reply
object and leaves the server bound to the context it keeps, so the take
donates nothing, and it writes nothing else the guard reads. -/
theorem keepHeldPop_callTakeGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb rt : TCB) (P : SystemState)
    (hP : keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid scId = P)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) (hNext : rp.next = some (.head scId))
    (hScO : st.objects[scId.toObjId]? = some (.schedContext sc)) (hHead : sc.scReply = some rid)
    (hBelow : ∀ b, rp.prev = some b → b ≠ rid)
    (hNe : tid ≠ c)
    (hLR : storeLeavesIndexAndTypes st rid.toObjId .reply = true)
    (hFR : st.objects.findsInPlace rid.toObjId = true)
    (hRtT : st.getTcb? tid = some rt)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hG : receiveCallTakesPastPop st epId tid s sTcb = true) :
    P.objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcbP, P.objects[s.toObjId]? = some (.tcb sTcbP) ∧ SenderWordsKept sTcbP sTcb ∧
        sTcbP.scBindingScCode = sTcb.scBindingScCode ∧
        determineTargetCore P s = determineTargetCore st s ∧
        determineTargetCore P tid = determineTargetCore st tid ∧
        receiveCallTakesInPlace P epId tid s sTcbP rid = true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hR : st.objects[tid.toObjId]? = some (.tcb rt) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hRtT
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hR; cases hR
  have hSc' : scId.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hScO; cases hScO
  have hSr : scId.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hScO; cases hScO
  have hsc : s.toObjId ≠ c.toObjId := fun e => hSC (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hsr : s.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hS; cases hS
  -- the guard, read on the pre-state
  have hG' := hG
  simp only [receiveCallTakesPastPop, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSW, hRRes⟩, hRS⟩, hRN⟩, hLRt⟩, hFRt⟩, hRO⟩, hCall⟩ := hG'
  have hst : s.toObjId ≠ tid.toObjId := fun e =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  -- the reply leg
  have hKS := storeReplyRendezvousReady_keepsSendCaps st c tid rid hNo
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hP
  generalize hS1 : storeReplyRendezvousReady st c tid rid = S1 at hKS hP
  have hAg := fun x hx hy => hS1 ▸ storeReplyRendezvousReady_agree st c tid rid ct hNo hTc hFC x hx hy
  have hNo1 : S1.objects.noResizeDue := hS1 ▸ storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyRendezvousReady_keepsFinds st c tid rid hNo hFC
  obtain ⟨tc1, htc1, -⟩ := hS1 ▸ storeReplyRendezvousReady_caller st c tid rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyRendezvousReady_reply st c tid rid ct rp hNo hTc hFC hRp hRc
  generalize hTdef : S1.mapTcbInPlace c (holdMessage msg) = T at hP
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
  -- the held pop
  have hScT : T.getSchedContext? scId = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hSc' hSr) (fun _ e => by cases e) hScO)
  obtain ⟨rtT, hRtT', _⟩ := agreeAt_tcb (hView _ hTc' hTr) hR
  have hHeadC : rp.consumed = { rp with callerCode := 0 } := Reply.consumed_of_head rp scId hNext
  obtain ⟨⟨t, hPt, hB, -, -⟩, hPr⟩ := keepDonatedSchedContextInPlace_exact T tid scId sc rid
    rp.consumed rtT hNoT hScT hHead ((SystemState.getReply?_eq_some_iff _ _ _).mpr hTR)
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRtT')
    (fun b hb => hBelow b (by rw [hHeadC] at hb; exact hb))
  have hF := keepDonatedSchedContextInPlace_popFrame T tid scId hNoT
  obtain ⟨sTcb1, hS1o, e1⟩ := agreeAt_tcb (hAg _ hsc hsr) hS
  have hsT : T.objects[s.toObjId]? = some (.tcb sTcb1) := by rw [hHold _ hsc]; exact hS1o
  have hsP := keepDonatedSchedContextInPlace_tcbAt T tid scId hNoT hst hsT
  rw [hP] at hPt hPr hF hsP
  have hComb : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (P.objects[x]?).map popFieldsView = (st.objects[x]?).map popFieldsView :=
    fun x hx hy => (hF.2.2.2 x).trans (popAgreeAt_of_runLinks (hView x hx hy))
  obtain ⟨tcP, hPC, _⟩ := popAgreeAt_tcb (hF.2.2.2 c.toObjId) hTC
  -- the frame of the whole reply leg
  have hKP : P.objectsKeepFinds st := hF.2.2.1.trans hKT
  have hV : ∀ x, P.getObjectType? x = st.getObjectType? x := by
    intro x
    by_cases hxc : x = c.toObjId
    · subst hxc; unfold SystemState.getObjectType?
      rw [hPC, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc]; rfl
    · by_cases hxr : x = rid.toObjId
      · subst hxr; unfold SystemState.getObjectType?; rw [hPr, hRp]; rfl
      · exact getObjectType?_of_popAgree (hComb x hxc hxr)
  have hTcbP : ∀ p : SeLe4n.ThreadId, (st.getTcb? p).isSome = true →
      (P.getTcb? p).isSome = true := by
    intro p hp
    by_cases hpc : p.toObjId = c.toObjId
    · exact Option.isSome_iff_exists.mpr
        ⟨tcP, (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hpc ▸ hPC)⟩
    · by_cases hpr : p.toObjId = rid.toObjId
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
        have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hx
        rw [hpr, hRp] at this; cases this
      · exact getTcb?_isSome_of_popAgree (hComb _ hpc hpr) hp
  have hSL : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes P id ty = true :=
    fun h => storeLeavesIndexAndTypes_of_frame hV h
  -- the queued caller, as it was
  have hw : sTcb1.sendCapWords = sTcb.sendCapWords := by
    have k := hKS s.toObjId
    rw [hS1o, hS] at k
    simpa [KernelObject.sendCapWords] using k
  have hKept := SenderWordsKept.of_withoutRunLinks e1 hw
  have wl : ∀ {α : Type} (g : TCB → α), (∀ u : TCB, g u.withoutRunLinks = g u) →
      g sTcb1 = g sTcb := fun g hg => by rw [← hg sTcb1, ← hg sTcb, e1]
  have hBind : sTcb1.scBindingScCode = sTcb.scBindingScCode := wl TCB.scBindingScCode (fun _ => rfl)
  have hAff : sTcb1.cpuAffinity = sTcb.cpuAffinity := wl TCB.cpuAffinity (fun _ => rfl)
  have hROc : sTcb1.replyObjectCode = sTcb.replyObjectCode := wl TCB.replyObjectCode (fun _ => rfl)
  have hQ : sTcb1.queueNext = sTcb.queueNext := by simp only [TCB.queueNext, hKept.queueNext]
  have hDs : determineTargetCore P s = determineTargetCore st s := by
    unfold determineTargetCore
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hsP, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hS]
    dsimp only
    rw [hAff]
  have hDt : determineTargetCore P tid = determineTargetCore st tid := by
    obtain ⟨t', h', e'⟩ := popAgreeAt_tcb (hComb _ hTc' hTr) hR
    have ha : t'.cpuAffinity = rt.cpuAffinity := by
      have := congrArg TCB.cpuAffinity e'
      exact this
    unfold determineTargetCore
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h', hRtT]
    dsimp only
    rw [ha]
  refine ⟨popAgreeAt_endpoint (hComb _ hEc hEr) hE, sTcb1, hsP, hKept, hBind, hDs, hDt, ?_⟩
  have hFree : ({ rp.consumed with prev := none, next := none } : Reply).isFree = true := by
    have h := Reply.consumed_caller rp
    simp only [Reply.caller] at h
    simp only [Reply.isFree, Reply.caller, h, Option.isNone_none, Bool.and_self]
  have hPtG : P.getTcb? tid = some t := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hPt
  have hPrG : P.getReply? rid = some { rp.consumed with prev := none, next := none } :=
    (SystemState.getReply?_eq_some_iff _ _ _).mpr hPr
  have hNothing : callDonatesNothing sTcb1 t = true := by
    unfold callDonatesNothing TCB.schedContextBinding
    rw [hB]
    cases t.scBindingOwnerCode <;> rfl
  have hRO' : sTcb1.replyObject = sTcb.replyObject := by simp only [TCB.replyObject, hROc]
  have hSWP := sendWakesInPlace_of_frame epId s sTcb.queueNext hKP hV hTcbP hSW
  have hLRtP := hSL hLRt
  have hFRtP := (hKP _).trans hFRt
  have hLRP := hSL hLR
  have hFRP := (hKP _).trans hFR
  unfold receiveCallTakesInPlace
  rw [hPtG, hPrG, hQ, hRO', hKept.ipcState]
  simp only [hNothing, hFree, hKept.canGrant, hKept.canGrantReply, Bool.and_eq_true,
    Bool.not_eq_true', bne_iff_ne, ne_eq]
  and_intros
  all_goals (first | assumption | trivial | skip)

end ReplyLegGuards

end SeLe4n.Kernel
