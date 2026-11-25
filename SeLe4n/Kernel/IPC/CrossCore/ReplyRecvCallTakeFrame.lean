-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.ReplyPopFrame
import SeLe4n.Kernel.IPC.CrossCore.ReceiveCallDonatingInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeFrame

/-!
# The Call take's frame: what the composed Call take reads

The guards, carries and writes the reply-receive's Call take reads, over every
reply arm (`ReplyRecvCallTakeComposed`), and the reply leg guards
(`ReplyRecvLegGuards`): the pop's keeps, the take-and-donation guards read on
the pre-state past the reply leg (`receiveCallDonatesPastReply`) and past the
pop (`receiveCallDonatesPastPop`), each arm's carry of them across its leg and
pop (`storeReplyRendezvous_callDonationGuard`,
`popDonationSettled_callDonationGuard`, `storeReplyLeg_callDonationGuard`) and
across the receive's context return
(`receiveReturnSchedContext_callDonationGuard`), the in-place lend of the
caller's context (`lendSchedContextInPlace`) and the server's frame
(`writeReceiverMessageFrame`).  The per-arm Call-take performers that first read
them are retired (WS-SX SX27); the composed take is the one Call take.
-/
namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency
open Architecture.RegisterDecode

section PopKeeps

/-- A thread write keeps any object other than a thread at its key, and any
object at another key. -/
theorem updateTcb_keepsAt (s : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (hNo : s.objects.noResizeDue) {x : SeLe4n.ObjId} {o : KernelObject}
    (hx : s.objects[x]? = some o) (hT : ∀ u, o = .tcb u → x ≠ t.toObjId) :
    (s.updateTcb t g).objects[x]? = some o := by
  by_cases e : x = t.toObjId
  · rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.objects_mapTcbInPlace,
      if_pos (beq_iff_eq.mpr e.symm), hx]
    cases o with
    | tcb u => exact absurd e (hT u rfl)
    | _ => rfl
  · rw [objects_updateTcb_ne _ _ _ hNo _ e]; exact hx

/-- An object write keeps the object at its key when it leaves that object as
it is, and every object at another key. -/
theorem modifyObject_keepsAt (s : SystemState) (k : SeLe4n.ObjId) (F : KernelObject → KernelObject)
    (hNo : s.objects.noResizeDue) {x : SeLe4n.ObjId} {o : KernelObject}
    (hx : s.objects[x]? = some o) (hF : x = k → F o = o) :
    (s.modifyObject k F).objects[x]? = some o := by
  by_cases e : x = k
  · subst e; rw [objects_modifyObject_self _ _ _ hNo, hx, Option.map_some, hF rfl]
  · rw [objects_modifyObject_ne _ _ _ hNo _ e]; exact hx

theorem updateSchedContext_keepsAt (s : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hNo : s.objects.noResizeDue) {x : SeLe4n.ObjId}
    {o : KernelObject} (hx : s.objects[x]? = some o)
    (hS : ∀ sc, o = .schedContext sc → x ≠ scId.toObjId) :
    (s.updateSchedContext scId f).objects[x]? = some o := by
  rw [SystemState.updateSchedContext_eq_impl]
  unfold SystemState.updateSchedContextImpl
  split
  · refine modifyObject_keepsAt _ _ _ hNo hx (fun e => ?_)
    cases o with
    | schedContext sc => exact absurd e (hS sc rfl)
    | _ => rfl
  · exact hx

/-- **The pop keeps every other thread and context**: it writes the context it
returns, reply objects, and the two threads' bindings, so a thread other than
those two and a context other than the returned one stand as they were. -/
theorem returnDonatedSchedContextInPlace_keepsAt (S : SystemState)
    (holder owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : S.objects.noResizeDue) {x : SeLe4n.ObjId} {o : KernelObject}
    (hx : S.objects[x]? = some o)
    (hT : ∀ u, o = .tcb u → x ≠ owner.toObjId ∧ x ≠ holder.toObjId)
    (hS : ∀ sc, o = .schedContext sc → x ≠ scId.toObjId)
    (hR : ∀ r, o ≠ .reply r) :
    (returnDonatedSchedContextInPlace S holder owner scId).objects[x]? = some o := by
  have hRp : ∀ (g : Reply → Reply) (k : SeLe4n.ObjId), x = k →
      SystemState.mapReplyObject g o = o := fun g _ _ => by
    cases o with
    | reply r => exact absurd rfl (hR r)
    | _ => rfl
  unfold returnDonatedSchedContextInPlace
  split
  · exact hx
  split
  · exact hx
  split
  · exact hx
  split
  · exact hx
  split
  · exact hx
  dsimp only
  rw [markKeyChangeParts_objects, markCandidacyGainFor_objects, markKeyChangeParts_objects,
    markCandidacyGainFor_objects]
  have hN : ∀ {s : SystemState}, s.objects.noResizeDue → ∀ k F,
      (s.modifyObject k F).objects.noResizeDue := fun h k F => modifyObject_noResizeDue _ k F h
  apply updateTcb_keepsAt _ _ _ ?_ ?_ (fun u e => (hT u e).2)
  · apply updateTcb_noResizeDue
    split
    · exact hN (updateSchedContext_noResizeDue _ _ _ hNo) _ _
    · exact hN (hN (updateSchedContext_noResizeDue _ _ _ hNo) _ _) _ _
  apply updateTcb_keepsAt _ _ _ ?_ ?_ (fun u e => (hT u e).1)
  · split
    · exact hN (updateSchedContext_noResizeDue _ _ _ hNo) _ _
    · exact hN (hN (updateSchedContext_noResizeDue _ _ _ hNo) _ _) _ _
  split
  · exact modifyObject_keepsAt _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
      (updateSchedContext_keepsAt _ _ _ hNo hx hS) (hRp _ _)
  · exact modifyObject_keepsAt _ _ _ (hN (updateSchedContext_noResizeDue _ _ _ hNo) _ _)
      (modifyObject_keepsAt _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
        (updateSchedContext_keepsAt _ _ _ hNo hx hS) (hRp _ _)) (hRp _ _)

end PopKeeps

section PastPopGuard

/-- **The caller's context, ready to be donated**: `callDonationReady` without
its question of the receiver, which a reply-receive's pop answers (it leaves
the server unbound).  Read off the codes, so the test builds nothing. -/
@[inline] def callerContextReady (st : SystemState) (caller : SeLe4n.ThreadId) (ct : TCB)
    (rid : SeLe4n.ReplyId) : Bool :=
  match ct.scBindingScCode with
  | 0 => false
  | k + 1 =>
    storeLeavesIndexAndTypes st (SeLe4n.SchedContextId.toObjId ⟨k⟩) .schedContext &&
    st.objects.findsInPlace (SeLe4n.SchedContextId.toObjId ⟨k⟩) &&
    (match st.getSchedContext? ⟨k⟩ with
     | some sc => sc.boundThreadCode == caller.val + 1 &&
         (match sc.scReply with
          | none => true
          | some old => old != rid &&
              storeLeavesIndexAndTypes st old.toObjId .reply &&
              st.objects.findsInPlace old.toObjId &&
              (st.getReply? old).isSome)
     | none => false)

theorem callDonationReady_eq_callerContextReady (st : SystemState) (caller r : SeLe4n.ThreadId)
    (ct rt : TCB) (rid : SeLe4n.ReplyId) :
    callDonationReady st caller r ct rt rid =
      (rt.scBindingScCode == 0 && callerContextReady st caller ct rid) := rfl

/-- **The receive leg's take of a donating caller, checked before the reply
leg**: every check of `receiveCallDonatesInPlace` that the reply leg and the
pop leave standing, read on the pre-state, with the caller's context another
than the one the pop returns (`popCode`, the code `replyHeadContextCode`
reads).  The two the pop itself settles, the reply object free and the receiver
unbound, are not asked here: on the pre-state neither holds
(`popDonationSettled_callDonationGuard` carries the rest and proves those two). -/
@[inline] def receiveCallDonatesPastPop (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) (popCode : Nat) : Bool :=
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
   | _ => false) &&
  sTcb.scBindingScCode != popCode &&
  callerContextReady st s sTcb rid

/-- `receiveCallDonatesPastPop` as it is compiled: the caller's successor asked
of its link code. -/
@[inline] def receiveCallDonatesPastPopImpl (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) (popCode : Nat) : Bool :=
  sendWakesInPlaceCode st endpointId s sTcb.queueNextCode &&
  !receiver.isReserved && receiver != s &&
  queueSuccessorDiffers receiver sTcb.queueNextCode &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  sTcb.replyObject.isNone &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => sTcb.ipcCanGrant || sTcb.ipcCanGrantReply
   | _ => false) &&
  sTcb.scBindingScCode != popCode &&
  callerContextReady st s sTcb rid

@[csimp] theorem receiveCallDonatesPastPop_eq_impl :
    @receiveCallDonatesPastPop = @receiveCallDonatesPastPopImpl := by
  funext st endpointId receiver s sTcb rid popCode
  unfold receiveCallDonatesPastPop receiveCallDonatesPastPopImpl
  rw [sendWakesInPlaceCode_eq, queueSuccessorDiffers_eq, TCB.ofOptCode_queueNextCode]
  rfl

/-- The send rendezvous's in-place guard carries over to a state with every key
found where it was, every key holding an object of the same kind and every
thread still a thread. -/
theorem sendWakesInPlace_of_frame {s s' : SystemState} (epId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (hK : s'.objectsKeepFinds s)
    (hV : ∀ x, s'.getObjectType? x = s.getObjectType? x)
    (hTcb : ∀ p : SeLe4n.ThreadId, (s.getTcb? p).isSome = true → (s'.getTcb? p).isSome = true)
    (h : sendWakesInPlace s epId head next = true) :
    sendWakesInPlace s' epId head next = true := by
  have hS : ∀ {id ty}, storeLeavesIndexAndTypes s id ty = true →
      storeLeavesIndexAndTypes s' id ty = true :=
    fun h => storeLeavesIndexAndTypes_of_frame hV h
  unfold sendWakesInPlace at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
  refine ⟨⟨⟨⟨⟨a1, hS a2⟩, (hK _).trans a3⟩, hS a4⟩, (hK _).trans a5⟩, ?_⟩
  revert a6
  cases next with
  | none => exact id
  | some n =>
    simp only [Bool.and_eq_true]
    rintro ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩
    exact ⟨⟨⟨⟨c1, c2⟩, hS c3⟩, (hK _).trans c4⟩, hTcb _ c5⟩

end PastPopGuard

section PastPopTransport

/-- **The pop carries the receive leg's donating take**: on the state a
donated reply leg and its pop leave (`P`), the endpoint is as it was, the
queued caller `s` is a thread keeping every word the take reads, its binding
and its home, the server keeps its home, and the take's and the donation's
in-place guard (`receiveCallDonatesInPlace`) holds, each read on the pre-state
(`receiveCallDonatesPastPop`): the pop frees the reply object and unbinds the
server, and writes nothing else the guard reads. -/
theorem popDonationSettled_callDonationGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (home : CoreId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB) (P : SystemState)
    (hP : popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId home = P)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) (hNext : rp.next = some (.head scId))
    (hScO : st.objects[scId.toObjId]? = some (.schedContext sc)) (hHead : sc.scReply = some rid)
    (hBelow : ∀ b, rp.prev = some b → b ≠ rid)
    (hNe : tid ≠ c)
    (hLR : storeLeavesIndexAndTypes st rid.toObjId .reply = true)
    (hFR : st.objects.findsInPlace rid.toObjId = true)
    (hRt : (st.getTcb? tid).isSome = true)
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
  obtain ⟨rt, hRtT⟩ := Option.isSome_iff_exists.mp hRt
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
  have hst : s.toObjId ≠ tid.toObjId := fun e =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
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
  have hKS := storeReplyRendezvousReady_keepsSendCaps st c tid rid hNo
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hP
  generalize hS1 : storeReplyRendezvousReady st c tid rid = S1 at hKS hP
  have hAg := fun x hx hy => hS1 ▸ storeReplyRendezvousReady_agree st c tid rid ct hNo hTc hFC x hx hy
  have hNo1 : S1.objects.noResizeDue := hS1 ▸ storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyRendezvousReady_keepsFinds st c tid rid hNo hFC
  obtain ⟨tc1, htc1, hc1⟩ := hS1 ▸ storeReplyRendezvousReady_caller st c tid rid ct hNo hTc hFC hRc
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
  -- the pop
  have hScT : T.getSchedContext? scId = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hSc' hSr) (fun _ e => by cases e) hScO)
  obtain ⟨rtT, hRtT', _⟩ := agreeAt_tcb (hView _ hTc' hTr) hR
  have hHeadC : rp.consumed = { rp with callerCode := 0 } := Reply.consumed_of_head rp scId hNext
  obtain ⟨⟨t, hPt, hB0⟩, hPr⟩ := returnDonatedSchedContextInPlace_exact T tid c scId sc rid rp.consumed
    (holdMessage msg tc1) rtT hNoT hScT hHead ((SystemState.getReply?_eq_some_iff _ _ _).mpr hTR)
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC) ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRtT')
    (fun b hb => hBelow b (by rw [hHeadC] at hb; exact hb))
  have hFr := returnDonatedSchedContextInPlace_popFrame T tid c scId hNoT
  obtain ⟨sTcb1, hS1o, e1⟩ := agreeAt_tcb (hAg _ hsc hsr) hS
  have hsT : T.objects[s.toObjId]? = some (.tcb sTcb1) := by rw [hHold _ hsc]; exact hS1o
  have hsR := returnDonatedSchedContextInPlace_keepsAt T tid c scId hNoT hsT
    (fun _ _ => ⟨hsc, hst⟩) (fun _ e => by cases e) (fun _ e => by cases e)
  have hkT : T.objects[(SeLe4n.SchedContextId.toObjId ⟨k⟩)]? = some (.schedContext scs) := by
    rw [hHold _ hkc]; exact agreeAt_of_not_tcb (hAg _ hkc hkr) (fun _ e => by cases e) hScsO
  have hkR := returnDonatedSchedContextInPlace_keepsAt T tid c scId hNoT hkT
    (fun _ e => by cases e) (fun _ _ => hkS) (fun _ e => by cases e)
  unfold popDonationSettledInPlace at hP
  generalize returnDonatedSchedContextInPlace T tid c scId = Rr at hPt hPr hFr hsR hkR hP
  have hAgS := SchedContextOps.settleReturnedContext_agree Rr home scId
  have hF := (settleReturnedContext_popFrame Rr home scId).trans hFr
  rw [hP] at hAgS hF
  have hPt' : P.objects[tid.toObjId]? = some (.tcb t) :=
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
  have hPtG : P.getTcb? tid = some t := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hPt'
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
    hSRp, hB0, hFree, hKept.canGrant, hKept.canGrantReply, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_self_eq_true,
    Option.isSome_some, Bool.true_and]
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

end PastPopTransport

section Commute

/-- **The receive's take commutes with a delivery** to a thread other than the
caller it takes and the receiver. -/
theorem storeReceiveCallReady_msg (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (st : SystemState) (endpointId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hNo : st.objects.noResizeDue) (hS : r ≠ s) (hR : r ≠ receiver) :
    storeReceiveCallReady (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) endpointId s nextCode
        receiver rid =
      (storeReceiveCallReady st endpointId s nextCode receiver rid).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  unfold storeReceiveCallReady
  dsimp only
  have h1 := storePopHead_noResizeDue st endpointId false s (ThreadId.ofOptCode nextCode) hNo
  have h2 := updateTcb_noResizeDue _ s (callCallerTcb endpointId receiver) h1
  have h3 := modifyObject_noResizeDue _ rid.toObjId (replyWithCaller s) h2
  have h4 := updateTcb_noResizeDue _ s
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) h3
  rw [storePopHead_msg r ρ μ π st endpointId false s _ hNo,
    updateTcb_msg r ρ μ π _ s _ h1 (fun h => absurd h.symm hS),
    modifyObject_msg r ρ μ _ rid.toObjId _ h2 (fun o => by cases o <;> rfl),
    updateTcb_msg r ρ μ π _ s _ h3 (fun h => absurd h.symm hS),
    updateTcb_msg r ρ μ π _ receiver _ h4 (fun h => absurd h.symm hR),
    linkReplyWaiter_msg]

end Commute

section LendInPlace

/-- **A taken caller's context lent in place**: the donation of `scS` from
`donor` to `donee` and its replenishment migrated from `donorHome` to
`doneeHome` (the specification's `applyRendezvousCallDonation`,
`applyRendezvousCallDonation_lendInPlace`). -/
@[inline] def lendSchedContextInPlace (X : SystemState)
    (donor donee : SeLe4n.ThreadId) (scS : SeLe4n.SchedContextId) (donorHome doneeHome : CoreId) :
    SystemState :=
  migrateSchedContextReplenishment (donateSchedContextInPlace X donor donee scS) scS donorHome
    doneeHome

/-- **The rendezvous donation, in place**: where the lend is the in-place
donation and migration, it is `lendSchedContextInPlace`. -/
theorem applyRendezvousCallDonation_lendInPlace {X : SystemState}
    {receiver donor : SeLe4n.ThreadId} {scS : SeLe4n.SchedContextId} {donorHome doneeHome : CoreId}
    (h : applyRendezvousCallDonation X receiver donor =
      .ok (migrateSchedContextReplenishment (donateSchedContextInPlace X donor receiver scS) scS
        donorHome doneeHome)) :
    applyRendezvousCallDonation X receiver donor =
      .ok (lendSchedContextInPlace X donor receiver scS donorHome doneeHome) := h

theorem lendSchedContextInPlace_msg (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (X : SystemState) (donor donee : SeLe4n.ThreadId)
    (scS : SeLe4n.SchedContextId) (donorHome doneeHome : CoreId) (hNo : X.objects.noResizeDue)
    (hC : r ≠ donor) :
    lendSchedContextInPlace (X.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) donor donee
        scS donorHome doneeHome =
      (lendSchedContextInPlace X donor donee scS donorHome doneeHome).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  simp only [lendSchedContextInPlace]
  rw [donateSchedContextInPlace_msg r ρ μ π X donor donee scS hNo hC,
    migrateSchedContextReplenishment_mapTcbInPlace]

theorem lendSchedContextInPlace_noResizeDue (X : SystemState)
    (donor donee : SeLe4n.ThreadId) (scS : SeLe4n.SchedContextId) (donorHome doneeHome : CoreId)
    (hNo : X.objects.noResizeDue) :
    (lendSchedContextInPlace X donor donee scS donorHome doneeHome).objects.noResizeDue :=
  migrateSchedContextReplenishment_noResizeDue _ scS donorHome doneeHome
    (donateSchedContextInPlace_noResizeDue X donor donee scS hNo)

theorem lendSchedContextInPlace_ipcStateCarried (X : SystemState)
    (donor donee : SeLe4n.ThreadId) (scS : SeLe4n.SchedContextId) (donorHome doneeHome : CoreId)
    (hNo : X.objects.noResizeDue) :
    ipcStateCarried X (lendSchedContextInPlace X donor donee scS donorHome doneeHome) := by
  intro t x hx
  obtain ⟨x1, hx1, e1⟩ := donateSchedContextInPlace_ipcStateCarried X donor donee scS hNo t x hx
  exact ⟨x1, (migrateSchedContextReplenishment_getTcb? _ scS donorHome doneeHome t).trans hx1, e1⟩

end LendInPlace

section ReceiverFrame

/-- The receiver's frame: the taken caller's inline words, read from its saved
registers `sRf`, written into the receiver's; its message held where the
receiver is, unexpectedly, not ready. -/
@[noinline] def writeReceiverMessageFrame (X : SystemState) (receiver : SeLe4n.ThreadId)
    (sRf : SeLe4n.RegisterFile) (sLen : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool) :
    SystemState :=
  writeDeliveredFrameIfReady X receiver
    (Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout sRf sLen badgeWord badged)
    (fun _ => X.mapTcbInPlace receiver (holdMessage
      { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout sRf sLen,
        badge := SeLe4n.Badge.opt badgeWord badged }))

end ReceiverFrame

section PopServer

theorem replyPopsInPlace_serverTcb {st : SystemState} {c : SeLe4n.ThreadId} {b : Nat}
    {server : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyPopsInPlace st c b server rid = true) : (st.getTcb? server).isSome = true := by
  unfold replyPopsInPlace at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

end PopServer

section CallTakeGuard

/-- **The receive leg's take of a donating caller, checked before the reply
leg**: every check of `receiveCallDonatesInPlace` but the reply object's being
free, read on the pre-state, with the receiver read as the receive's context
return leaves it: holding no context, or holding the one the return takes back
(`receiveReturnFires`).  On the pre-state the reply object still links the
answered caller; the reply leg frees it (`storeReplyRendezvous_callDonationGuard`
carries the rest and proves that one), and the return clears the receiver's
binding (`receiveReturnSchedContext_callDonationGuard`). -/
@[inline] def receiveCallDonatesPastReply (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) : Bool :=
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
   | _ => false) &&
  (match st.getTcb? receiver with
   | some rt => (rt.scBindingScCode == 0 || receiveReturnFires true st receiver) &&
       callerContextReady st s sTcb rid
   | none => false)

/-- `receiveCallDonatesPastReply` as it is compiled: the caller's successor
asked of its link code. -/
@[inline] def receiveCallDonatesPastReplyImpl (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) : Bool :=
  sendWakesInPlaceCode st endpointId s sTcb.queueNextCode &&
  !receiver.isReserved && receiver != s &&
  queueSuccessorDiffers receiver sTcb.queueNextCode &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  sTcb.replyObject.isNone &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => sTcb.ipcCanGrant || sTcb.ipcCanGrantReply
   | _ => false) &&
  (match st.getTcb? receiver with
   | some rt => (rt.scBindingScCode == 0 || receiveReturnFires true st receiver) &&
       callerContextReady st s sTcb rid
   | none => false)

@[csimp] theorem receiveCallDonatesPastReply_eq_impl :
    @receiveCallDonatesPastReply = @receiveCallDonatesPastReplyImpl := by
  funext st endpointId receiver s sTcb rid
  unfold receiveCallDonatesPastReply receiveCallDonatesPastReplyImpl
  rw [sendWakesInPlaceCode_eq, queueSuccessorDiffers_eq, TCB.ofOptCode_queueNextCode]
  rfl

/-- **The reply leg carries the receive leg's donating take**: on the state the
reply leg leaves (the caller `c` woken holding `msg`, its reply object
consumed), the endpoint is as it was, the queued caller `s` is a thread keeping
every word the take reads, its binding and its home, the server keeps its home,
the take's in-place guard and the caller's context hold, and the server holds no
context or the one the receive's return takes back, each check read on the
pre-state (`receiveCallDonatesPastReply`): the reply object, linking no stack,
comes out free, and the reply leg writes nothing else the guard reads, nor
anything the return's guard reads (the server's binding, its notification's
context, that context's thread). -/
theorem storeReplyRendezvous_callDonationGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hNx : rp.next = none)
    (hLR : storeLeavesIndexAndTypes st rid.toObjId .reply = true)
    (hFR : st.objects.findsInPlace rid.toObjId = true)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c) (hNe : tid ≠ c)
    (hG : receiveCallDonatesPastReply st epId tid s sTcb rid = true) :
    (storeReplyRendezvous st c tid rid msg).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (storeReplyRendezvous st c tid rid msg).objects[s.toObjId]? = some (.tcb sTcb1) ∧
        SenderWordsKept sTcb1 sTcb ∧
        sTcb1.scBindingScCode = sTcb.scBindingScCode ∧
        determineTargetCore (storeReplyRendezvous st c tid rid msg) s =
          determineTargetCore st s ∧
        determineTargetCore (storeReplyRendezvous st c tid rid msg) tid =
          determineTargetCore st tid ∧
        receiveCallTakesReplyInPlace (storeReplyRendezvous st c tid rid msg) epId tid s sTcb1 rid =
          true ∧
        callerContextReady (storeReplyRendezvous st c tid rid msg) s sTcb1 rid = true ∧
        ∃ rt1, (storeReplyRendezvous st c tid rid msg).getTcb? tid = some rt1 ∧
          (rt1.scBindingScCode = 0 ∨
            receiveReturnFires true (storeReplyRendezvous st c tid rid msg) tid = true) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hSc' : s.toObjId ≠ c.toObjId := fun e => hSC (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hSr : s.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hS; cases hS
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hG' := hG
  simp only [receiveCallDonatesPastReply, Bool.and_eq_true] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hSW, hRRes⟩, hRS⟩, hRN⟩, hLRt⟩, hFRt⟩, hRO⟩, hCall⟩, hRT⟩ := hG'
  obtain ⟨rt, hRtT⟩ : ∃ rt, st.getTcb? tid = some rt := by
    cases h : st.getTcb? tid with
    | none => rw [h] at hRT; cases hRT
    | some rt => exact ⟨rt, rfl⟩
  rw [hRtT] at hRT
  simp only [Bool.and_eq_true] at hRT
  obtain ⟨hRt0, hCtx⟩ := hRT
  have hRtO : st.objects[tid.toObjId]? = some (.tcb rt) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hRtT
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hRtO; cases hRtO
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
  -- the reply leg
  have hKS := storeReplyRendezvousReady_keepsSendCaps st c tid rid hNo
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]
  generalize hS1 : storeReplyRendezvousReady st c tid rid = S1 at hKS
  have hAg := fun x hx hy => hS1 ▸ storeReplyRendezvousReady_agree st c tid rid ct hNo hTc hFC x hx hy
  have hHold : ∀ x, x ≠ c.toObjId →
      (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = S1.objects[x]? := fun x hx => by
    rw [SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyRendezvousReady_keepsFinds st c tid rid hNo hFC
  obtain ⟨tc1, htc1, -⟩ := hS1 ▸ storeReplyRendezvousReady_caller st c tid rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyRendezvousReady_reply st c tid rid ct rp hNo hTc hFC hRp hRc
  generalize hTdef : S1.mapTcbInPlace c (holdMessage msg) = T at hHold ⊢
  have hView : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (T.objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks := fun x hx hy => by
    rw [hHold _ hx]; exact hAg x hx hy
  have hTC : ∃ t, T.objects[c.toObjId]? = some (.tcb t) := ⟨holdMessage msg tc1, by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl⟩
  have hTR : T.objects[rid.toObjId]? = some (.reply rp.consumed) := by rw [hHold _ hRc]; exact hR1
  have hV : ∀ x, T.getObjectType? x = st.getObjectType? x := by
    intro x
    by_cases hxc : x = c.toObjId
    · subst hxc; obtain ⟨t, h⟩ := hTC
      unfold SystemState.getObjectType?; rw [h, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc]; rfl
    · by_cases hxr : x = rid.toObjId
      · subst hxr; unfold SystemState.getObjectType?; rw [hTR, hRp]; rfl
      · exact getObjectType?_of_view (hView x hxc hxr)
  have hKF : T.objectsKeepFinds st := by
    rw [← hTdef]; exact (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
  have hTcb : ∀ p : SeLe4n.ThreadId, (st.getTcb? p).isSome = true → (T.getTcb? p).isSome = true := by
    intro p hp
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
    have h1 := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht
    by_cases hpc : p.toObjId = c.toObjId
    · obtain ⟨t', h⟩ := hTC
      exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hpc ▸ h)⟩
    · by_cases hpr : p.toObjId = rid.toObjId
      · rw [hpr, hRp] at h1; cases h1
      · obtain ⟨t', h', _⟩ := agreeAt_tcb (hView _ hpc hpr) h1
        exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'⟩
  have hSL : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes T id ty = true :=
    fun h => storeLeavesIndexAndTypes_of_frame hV h
  -- the queued caller and the server, as they were
  obtain ⟨sTcb1, hS1o, e1⟩ := agreeAt_tcb (hAg _ hSc' hSr) hS
  have hsT : T.objects[s.toObjId]? = some (.tcb sTcb1) := by rw [hHold _ hSc']; exact hS1o
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
  obtain ⟨rt1, hRt1, e2⟩ := agreeAt_tcb (hView _ hTc' hTr) hRtO
  have hB2 : rt1.scBindingScCode = rt.scBindingScCode := by
    have := congrArg TCB.scBindingScCode e2; exact this
  have hA2 : rt1.cpuAffinity = rt.cpuAffinity := by
    have := congrArg TCB.cpuAffinity e2; exact this
  have hDs : determineTargetCore T s = determineTargetCore st s := by
    unfold determineTargetCore
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hsT, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hS]
    dsimp only
    rw [hAff]
  have hDt : determineTargetCore T tid = determineTargetCore st tid := by
    unfold determineTargetCore
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hRt1, hRtT]
    dsimp only
    rw [hA2]
  have hFree : rp.consumed.isFree = true := by
    rw [Reply.isFree_iff]
    refine ⟨Reply.consumed_caller _, ?_, ?_⟩ <;> simp [Reply.consumed, hNx]
  have hRtG : T.getTcb? tid = some rt1 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hRt1
  have hRpG : T.getReply? rid = some rp.consumed := (SystemState.getReply?_eq_some_iff _ _ _).mpr hTR
  have hkT : T.getSchedContext? ⟨k⟩ = some scs := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hkc hkr) (fun _ e => by cases e) hScsO)
  have hRO' : sTcb1.replyObject = sTcb.replyObject := by simp only [TCB.replyObject, hROc]
  have hSWT := sendWakesInPlace_of_frame epId s sTcb.queueNext hKF hV hTcb hSW
  have hLRtT := hSL hLRt
  have hFRtT := (hKF _).trans hFRt
  have hLRT := hSL hLR
  have hFRT := (hKF _).trans hFR
  have hLscT := hSL hLsc
  have hFscT := (hKF _).trans hFsc
  -- the receive's return reads the receiver's binding, its notification's
  -- context and that context's thread, none of which the reply leg writes
  have hObjBind : ∀ {α : Type} (g : KernelObject → Option α),
      (∀ o, g o.withoutRunLinks = g o) → (∀ t, g (.tcb t) = none) → (∀ r, g (.reply r) = none) →
      ∀ x : SeLe4n.ObjId, (T.objects[x]?).bind g = (st.objects[x]?).bind g := by
    intro α g hg ht hr x
    by_cases hxc : x = c.toObjId
    · subst hxc
      obtain ⟨t', h⟩ := hTC
      rw [h, hT]; simp [ht]
    by_cases hxr : x = rid.toObjId
    · subst hxr
      rw [hTR, hRp]; simp [hr]
    have e := congrArg (fun o => Option.bind o g) (hView x hxc hxr)
    simpa [Option.bind_map, Function.comp_def, hg] using e
  have hNt : ∀ n, T.getNotification? n = st.getNotification? n := by
    intro n
    have gN : ∀ (S : SystemState), S.getNotification? n = (S.objects[n]?).bind
        (fun o => match o with | .notification m => some m | _ => none) := by
      intro S; unfold SystemState.getNotification?
      cases S.objects[n]? with
      | none => rfl
      | some o => cases o <;> rfl
    rw [gN, gN]
    exact hObjBind _ (fun o => by cases o <;> rfl) (fun _ => rfl) (fun _ => rfl) n
  have hSct : ∀ q, T.getSchedContext? q = st.getSchedContext? q := by
    intro q
    have gS : ∀ (S : SystemState), S.getSchedContext? q = (S.objects[q.toObjId]?).bind
        (fun o => match o with | .schedContext m => some m | _ => none) := by
      intro S; unfold SystemState.getSchedContext?
      cases S.objects[q.toObjId]? with
      | none => rfl
      | some o => cases o <;> rfl
    rw [gS, gS]
    exact hObjBind _ (fun o => by cases o <;> rfl) (fun _ => rfl) (fun _ => rfl) _
  have hFires : receiveReturnFires true T tid = receiveReturnFires true st tid := by
    have hBN : rt1.boundNotificationCode = rt.boundNotificationCode := by
      have := congrArg TCB.boundNotificationCode e2; exact this
    have hO2 : rt1.scBindingOwnerCode = rt.scBindingOwnerCode := by
      have := congrArg TCB.scBindingOwnerCode e2; exact this
    unfold receiveReturnFires
    rw [hRtG, hRtT]
    dsimp only
    rw [hBN, signalReturnGuard_congr (st := st) (st' := T)
      (by rw [hNt]) (fun q => by rw [hSct]) (by rw [hRtG, hRtT]; simp only [Option.map_some,
        TCB.schedContextBinding, hB2, hO2])]
  refine ⟨agreeAt_of_not_tcb (hView _ hEc hEr) (fun _ e => by cases e) hE, sTcb1, hsT, hKept,
    hBind, hDs, hDt, ?_, ?_, rt1, hRtG, ?_⟩
  · simp only [Bool.not_eq_true', bne_iff_ne, ne_eq] at hRS hRN hRRes
    unfold receiveCallTakesReplyInPlace
    rw [hRpG, hQ, hRO', hKept.ipcState]
    simp only [hRtG, hFree, hKept.canGrant, hKept.canGrantReply, Bool.and_eq_true,
      Bool.not_eq_true', bne_iff_ne, ne_eq, Option.isSome_some]
    and_intros
    all_goals (first | assumption | trivial)
  · simp only [callerContextReady, hBind, hk, hkT, Bool.and_eq_true]
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
        exact ⟨⟨⟨hOR, hSL hOL⟩, (hKF _).trans hOF⟩, oR, (SystemState.getReply?_eq_some_iff _ _ _).mpr
          (agreeAt_of_not_tcb (hView _ hoc hor) (fun _ e => by cases e) hoRo)⟩
  · simp only [Bool.or_eq_true, beq_iff_eq] at hRt0
    rcases hRt0 with h0 | hf
    · exact Or.inl (hB2.trans h0)
    · exact Or.inr (hFires.trans hf)

/-- **The receive's return carries the receive leg's donating take** (seL4-MCS
`receiveIPC`: `maybeReturnSchedContext`, then `reply_push`'s donation).  On a
state where the take's checks and the caller's context hold, and the receiver
either holds no context or holds the one its bound notification names (the
return fires), the state the return leaves has the endpoint and the queued
caller as they were, both threads homed where they were, and the take's and
the donation's in-place guard holds there: the return clears only the
receiver's binding, so the receiver comes out holding no context, and it
rewrites only the returned context, which is bound to the receiver while the
caller's is bound to the caller. -/
theorem receiveReturnSchedContext_callDonationGuard (T : SystemState) (epId : SeLe4n.ObjId)
    (ep : Endpoint) (tid s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) (rt : TCB)
    (hNo : T.objects.noResizeDue)
    (hE : T.objects[epId]? = some (.endpoint ep))
    (hS : T.objects[s.toObjId]? = some (.tcb sTcb))
    (hTk : receiveCallTakesReplyInPlace T epId tid s sTcb rid = true)
    (hCx : callerContextReady T s sTcb rid = true)
    (hRt : T.getTcb? tid = some rt)
    (hOr : rt.scBindingScCode = 0 ∨ receiveReturnFires true T tid = true) :
    (receiveReturnSchedContext true T tid).objects[epId]? = some (.endpoint ep) ∧
      (receiveReturnSchedContext true T tid).objects[s.toObjId]? = some (.tcb sTcb) ∧
      determineTargetCore (receiveReturnSchedContext true T tid) s = determineTargetCore T s ∧
      determineTargetCore (receiveReturnSchedContext true T tid) tid =
        determineTargetCore T tid ∧
      receiveCallDonatesInPlace (receiveReturnSchedContext true T tid) epId tid s sTcb rid =
        true := by
  have hRtO : T.objects[tid.toObjId]? = some (.tcb rt) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hRt
  rcases hOr with h0 | hF
  · rw [receiveReturnSchedContext_of_scUnbound hRtO h0]
    refine ⟨hE, hS, rfl, rfl, ?_⟩
    unfold receiveCallDonatesInPlace
    rw [hTk, hRt]
    simp only [callDonationReady_eq_callerContextReady, h0, hCx]
    rfl
  have hst : s ≠ tid := by
    have h := hTk
    simp only [receiveCallTakesReplyInPlace, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact fun e => h.1.1.1.1.1.1.1.1.1.2 e.symm
  have hsT : s.toObjId ≠ tid.toObjId := fun e => hst (SeLe4n.ThreadId.toObjId_injective _ _ e)
  obtain ⟨rt', hRt', hRtR⟩ := receiveReturnSchedContext_getTcb?_self_of_fires hNo hF
  rw [hRt] at hRt'
  cases hRt'
  -- the caller's context, bound to the caller
  obtain ⟨k, hk⟩ : ∃ k, sTcb.scBindingScCode = k + 1 := by
    cases h : sTcb.scBindingScCode with
    | zero => simp only [callerContextReady, h, Bool.false_eq_true] at hCx
    | succ k => exact ⟨k, rfl⟩
  obtain ⟨sc, hScT, hBTs⟩ : ∃ sc, T.getSchedContext? ⟨k⟩ = some sc ∧
      sc.boundThreadCode = s.val + 1 := by
    have h := hCx
    unfold callerContextReady at h
    rw [hk] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨-, hM⟩ := h
    cases e : T.getSchedContext? ⟨k⟩ with
    | none => rw [e] at hM; cases hM
    | some sc =>
      rw [e] at hM
      simp only [Bool.and_eq_true, beq_iff_eq] at hM
      exact ⟨sc, rfl, hM.1⟩
  have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hScT
  have hkT : (SeLe4n.SchedContextId.toObjId ⟨k⟩) ≠ tid.toObjId := fun e => by
    rw [e, hRtO] at hScO; cases hScO
  have hAgK := receiveReturnSchedContext_agreeOff true T tid hNo _ hkT (fun sc0 h => by
    rw [hScO] at h; cases h
    simp only [SchedContext.boundThread, hBTs, SeLe4n.ThreadId.ofOptCode, ne_eq,
      Option.some.injEq]
    exact fun e => hst e)
  obtain ⟨sc', hScO', hW⟩ := withoutRelease_map_eq_sc hAgK hScO
  have hScR : (receiveReturnSchedContext true T tid).getSchedContext? ⟨k⟩ = some sc' :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hScO'
  have hBT : sc'.boundThreadCode = sc.boundThreadCode := by
    have := congrArg SchedContext.boundThreadCode hW; exact this
  have hRP : sc'.scReply = sc.scReply := by
    have := congrArg SchedContext.scReply hW; exact this
  -- the queued caller and the endpoint, as they were
  have hsR : (receiveReturnSchedContext true T tid).objects[s.toObjId]? = some (.tcb sTcb) :=
    withoutRelease_map_eq_of_not_sc
      (receiveReturnSchedContext_agreeOff true T tid hNo _ hsT
        (fun _ h => by rw [hS] at h; cases h)) hS (fun _ e => by cases e)
  have hAg := receiveReturnSchedContext_returnAgree true T tid hNo
  have hER : (receiveReturnSchedContext true T tid).objects[epId]? = some (.endpoint ep) := by
    rcases hAg epId with e | ⟨o0, o', h0, h1, r⟩
    · rw [e, hE]
    · rw [hE] at h0; cases h0
      rcases r with rfl | ⟨_, e1, _⟩ | ⟨_, _, e1, _⟩
      · exact h1
      · cases e1
      · cases e1
  -- every reply as it was
  have hRpR : ∀ r, (receiveReturnSchedContext true T tid).getReply? r = T.getReply? r := by
    intro r
    unfold SystemState.getReply?
    rcases hAg r.toObjId with e | ⟨o, o', h0, h1, rr⟩
    · rw [e]
    · rw [h0, h1]
      rcases rr with rfl | ⟨t, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ <;> rfl
  have hKF := receiveReturnSchedContext_keepsFinds true T tid hNo
  generalize receiveReturnSchedContext true T tid = R at hAg hKF hRtR hScR hsR hER hRpR ⊢
  have hV : ∀ x, R.getObjectType? x = T.getObjectType? x := by
    intro x
    unfold SystemState.getObjectType?
    rcases hAg x with e | ⟨o, o', h0, h1, r⟩
    · rw [e]
    · rw [h0, h1]
      rcases r with rfl | ⟨t, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ <;> rfl
  have hTcb : ∀ p : SeLe4n.ThreadId, (R.getTcb? p).isSome = (T.getTcb? p).isSome := by
    intro p
    unfold SystemState.getTcb?
    rcases hAg p.toObjId with e | ⟨o, o', h0, h1, r⟩
    · rw [e]
    · rw [h0, h1]
      rcases r with rfl | ⟨t, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ <;> rfl
  have hSL : ∀ id ty, storeLeavesIndexAndTypes R id ty = storeLeavesIndexAndTypes T id ty :=
    fun _ _ => Bool.eq_iff_iff.mpr ⟨fun h => storeLeavesIndexAndTypes_of_frame (fun x => (hV x).symm) h,
      fun h => storeLeavesIndexAndTypes_of_frame hV h⟩
  have hSW : ∀ n, sendWakesInPlace R epId s n = sendWakesInPlace T epId s n :=
    fun n => Bool.eq_iff_iff.mpr
      ⟨fun h => sendWakesInPlace_of_frame epId s n (fun k => (hKF k).symm) (fun x => (hV x).symm)
          (fun p hp => (hTcb p).symm.trans hp) h,
        fun h => sendWakesInPlace_of_frame epId s n hKF hV (fun p hp => (hTcb p).trans hp) h⟩
  have hKF' : ∀ k, R.objects.findsInPlace k = T.objects.findsInPlace k := hKF
  refine ⟨hER, hsR, ?_, ?_, ?_⟩
  · unfold determineTargetCore
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hsR, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hS]
  · unfold determineTargetCore
    rw [hRtR, hRt]
  · unfold receiveCallDonatesInPlace
    rw [hRtR]
    have hTk' : receiveCallTakesReplyInPlace R epId tid s sTcb rid = true := by
      rw [← hTk]
      unfold receiveCallTakesReplyInPlace
      simp only [hSW, hSL, hKF', hTcb, hRpR]
    have hCx' : callerContextReady R s sTcb rid = true := by
      rw [← hCx]
      unfold callerContextReady
      rw [hk]
      simp only [hSL, hKF', hScR, hScT, hBT, hRP, hRpR]
    simp only [hTk', callDonationReady_eq_callerContextReady, hCx']
    rfl

end CallTakeGuard

/-- **The call-take's guard across the reply leg alone**:
`storeReplyRendezvous_callDonationGuard` for `storeReplyLeg` (no server's reply
waiters to leave). -/
theorem storeReplyLeg_callDonationGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hNx : rp.next = none)
    (hLR : storeLeavesIndexAndTypes st rid.toObjId .reply = true)
    (hFR : st.objects.findsInPlace rid.toObjId = true)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c) (hNe : tid ≠ c)
    (hG : receiveCallDonatesPastReply st epId tid s sTcb rid = true) :
    (storeReplyLeg st c rid msg).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (storeReplyLeg st c rid msg).objects[s.toObjId]? = some (.tcb sTcb1) ∧
        SenderWordsKept sTcb1 sTcb ∧
        sTcb1.scBindingScCode = sTcb.scBindingScCode ∧
        determineTargetCore (storeReplyLeg st c rid msg) s =
          determineTargetCore st s ∧
        determineTargetCore (storeReplyLeg st c rid msg) tid =
          determineTargetCore st tid ∧
        receiveCallTakesReplyInPlace (storeReplyLeg st c rid msg) epId tid s sTcb1 rid =
          true ∧
        callerContextReady (storeReplyLeg st c rid msg) s sTcb1 rid = true ∧
        ∃ rt1, (storeReplyLeg st c rid msg).getTcb? tid = some rt1 ∧
          (rt1.scBindingScCode = 0 ∨
            receiveReturnFires true (storeReplyLeg st c rid msg) tid = true) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hSc' : s.toObjId ≠ c.toObjId := fun e => hSC (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hSr : s.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hS; cases hS
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hG' := hG
  simp only [receiveCallDonatesPastReply, Bool.and_eq_true] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hSW, hRRes⟩, hRS⟩, hRN⟩, hLRt⟩, hFRt⟩, hRO⟩, hCall⟩, hRT⟩ := hG'
  obtain ⟨rt, hRtT⟩ : ∃ rt, st.getTcb? tid = some rt := by
    cases h : st.getTcb? tid with
    | none => rw [h] at hRT; cases hRT
    | some rt => exact ⟨rt, rfl⟩
  rw [hRtT] at hRT
  simp only [Bool.and_eq_true] at hRT
  obtain ⟨hRt0, hCtx⟩ := hRT
  have hRtO : st.objects[tid.toObjId]? = some (.tcb rt) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hRtT
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hRtO; cases hRtO
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
  -- the reply leg
  have hKS := storeReplyLegReady_keepsSendCaps st c rid hNo
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo]
  generalize hS1 : storeReplyLegReady st c rid = S1 at hKS
  have hAg := fun x hx hy => hS1 ▸ storeReplyLegReady_agree st c rid ct hNo hTc hFC x hx hy
  have hHold : ∀ x, x ≠ c.toObjId →
      (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = S1.objects[x]? := fun x hx => by
    rw [SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyLegReady_keepsFinds st c rid hNo hFC
  obtain ⟨tc1, htc1, -⟩ := hS1 ▸ storeReplyLegReady_callerView st c rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyLegReady_reply st c rid ct rp hNo hTc hFC hRp hRc
  generalize hTdef : S1.mapTcbInPlace c (holdMessage msg) = T at hHold ⊢
  have hView : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (T.objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks := fun x hx hy => by
    rw [hHold _ hx]; exact hAg x hx hy
  have hTC : ∃ t, T.objects[c.toObjId]? = some (.tcb t) := ⟨holdMessage msg tc1, by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl⟩
  have hTR : T.objects[rid.toObjId]? = some (.reply rp.consumed) := by rw [hHold _ hRc]; exact hR1
  have hV : ∀ x, T.getObjectType? x = st.getObjectType? x := by
    intro x
    by_cases hxc : x = c.toObjId
    · subst hxc; obtain ⟨t, h⟩ := hTC
      unfold SystemState.getObjectType?; rw [h, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc]; rfl
    · by_cases hxr : x = rid.toObjId
      · subst hxr; unfold SystemState.getObjectType?; rw [hTR, hRp]; rfl
      · exact getObjectType?_of_view (hView x hxc hxr)
  have hKF : T.objectsKeepFinds st := by
    rw [← hTdef]; exact (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
  have hTcb : ∀ p : SeLe4n.ThreadId, (st.getTcb? p).isSome = true → (T.getTcb? p).isSome = true := by
    intro p hp
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
    have h1 := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht
    by_cases hpc : p.toObjId = c.toObjId
    · obtain ⟨t', h⟩ := hTC
      exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hpc ▸ h)⟩
    · by_cases hpr : p.toObjId = rid.toObjId
      · rw [hpr, hRp] at h1; cases h1
      · obtain ⟨t', h', _⟩ := agreeAt_tcb (hView _ hpc hpr) h1
        exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'⟩
  have hSL : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes T id ty = true :=
    fun h => storeLeavesIndexAndTypes_of_frame hV h
  -- the queued caller and the server, as they were
  obtain ⟨sTcb1, hS1o, e1⟩ := agreeAt_tcb (hAg _ hSc' hSr) hS
  have hsT : T.objects[s.toObjId]? = some (.tcb sTcb1) := by rw [hHold _ hSc']; exact hS1o
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
  obtain ⟨rt1, hRt1, e2⟩ := agreeAt_tcb (hView _ hTc' hTr) hRtO
  have hB2 : rt1.scBindingScCode = rt.scBindingScCode := by
    have := congrArg TCB.scBindingScCode e2; exact this
  have hA2 : rt1.cpuAffinity = rt.cpuAffinity := by
    have := congrArg TCB.cpuAffinity e2; exact this
  have hDs : determineTargetCore T s = determineTargetCore st s := by
    unfold determineTargetCore
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hsT, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hS]
    dsimp only
    rw [hAff]
  have hDt : determineTargetCore T tid = determineTargetCore st tid := by
    unfold determineTargetCore
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hRt1, hRtT]
    dsimp only
    rw [hA2]
  have hFree : rp.consumed.isFree = true := by
    rw [Reply.isFree_iff]
    refine ⟨Reply.consumed_caller _, ?_, ?_⟩ <;> simp [Reply.consumed, hNx]
  have hRtG : T.getTcb? tid = some rt1 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hRt1
  have hRpG : T.getReply? rid = some rp.consumed := (SystemState.getReply?_eq_some_iff _ _ _).mpr hTR
  have hkT : T.getSchedContext? ⟨k⟩ = some scs := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hkc hkr) (fun _ e => by cases e) hScsO)
  have hRO' : sTcb1.replyObject = sTcb.replyObject := by simp only [TCB.replyObject, hROc]
  have hSWT := sendWakesInPlace_of_frame epId s sTcb.queueNext hKF hV hTcb hSW
  have hLRtT := hSL hLRt
  have hFRtT := (hKF _).trans hFRt
  have hLRT := hSL hLR
  have hFRT := (hKF _).trans hFR
  have hLscT := hSL hLsc
  have hFscT := (hKF _).trans hFsc
  -- the receive's return reads the receiver's binding, its notification's
  -- context and that context's thread, none of which the reply leg writes
  have hObjBind : ∀ {α : Type} (g : KernelObject → Option α),
      (∀ o, g o.withoutRunLinks = g o) → (∀ t, g (.tcb t) = none) → (∀ r, g (.reply r) = none) →
      ∀ x : SeLe4n.ObjId, (T.objects[x]?).bind g = (st.objects[x]?).bind g := by
    intro α g hg ht hr x
    by_cases hxc : x = c.toObjId
    · subst hxc
      obtain ⟨t', h⟩ := hTC
      rw [h, hT]; simp [ht]
    by_cases hxr : x = rid.toObjId
    · subst hxr
      rw [hTR, hRp]; simp [hr]
    have e := congrArg (fun o => Option.bind o g) (hView x hxc hxr)
    simpa [Option.bind_map, Function.comp_def, hg] using e
  have hNt : ∀ n, T.getNotification? n = st.getNotification? n := by
    intro n
    have gN : ∀ (S : SystemState), S.getNotification? n = (S.objects[n]?).bind
        (fun o => match o with | .notification m => some m | _ => none) := by
      intro S; unfold SystemState.getNotification?
      cases S.objects[n]? with
      | none => rfl
      | some o => cases o <;> rfl
    rw [gN, gN]
    exact hObjBind _ (fun o => by cases o <;> rfl) (fun _ => rfl) (fun _ => rfl) n
  have hSct : ∀ q, T.getSchedContext? q = st.getSchedContext? q := by
    intro q
    have gS : ∀ (S : SystemState), S.getSchedContext? q = (S.objects[q.toObjId]?).bind
        (fun o => match o with | .schedContext m => some m | _ => none) := by
      intro S; unfold SystemState.getSchedContext?
      cases S.objects[q.toObjId]? with
      | none => rfl
      | some o => cases o <;> rfl
    rw [gS, gS]
    exact hObjBind _ (fun o => by cases o <;> rfl) (fun _ => rfl) (fun _ => rfl) _
  have hFires : receiveReturnFires true T tid = receiveReturnFires true st tid := by
    have hBN : rt1.boundNotificationCode = rt.boundNotificationCode := by
      have := congrArg TCB.boundNotificationCode e2; exact this
    have hO2 : rt1.scBindingOwnerCode = rt.scBindingOwnerCode := by
      have := congrArg TCB.scBindingOwnerCode e2; exact this
    unfold receiveReturnFires
    rw [hRtG, hRtT]
    dsimp only
    rw [hBN, signalReturnGuard_congr (st := st) (st' := T)
      (by rw [hNt]) (fun q => by rw [hSct]) (by rw [hRtG, hRtT]; simp only [Option.map_some,
        TCB.schedContextBinding, hB2, hO2])]
  refine ⟨agreeAt_of_not_tcb (hView _ hEc hEr) (fun _ e => by cases e) hE, sTcb1, hsT, hKept,
    hBind, hDs, hDt, ?_, ?_, rt1, hRtG, ?_⟩
  · simp only [Bool.not_eq_true', bne_iff_ne, ne_eq] at hRS hRN hRRes
    unfold receiveCallTakesReplyInPlace
    rw [hRpG, hQ, hRO', hKept.ipcState]
    simp only [hRtG, hFree, hKept.canGrant, hKept.canGrantReply, Bool.and_eq_true,
      Bool.not_eq_true', bne_iff_ne, ne_eq, Option.isSome_some]
    and_intros
    all_goals (first | assumption | trivial)
  · simp only [callerContextReady, hBind, hk, hkT, Bool.and_eq_true]
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
        exact ⟨⟨⟨hOR, hSL hOL⟩, (hKF _).trans hOF⟩, oR, (SystemState.getReply?_eq_some_iff _ _ _).mpr
          (agreeAt_of_not_tcb (hView _ hoc hor) (fun _ e => by cases e) hoRo)⟩
  · simp only [Bool.or_eq_true, beq_iff_eq] at hRt0
    rcases hRt0 with h0 | hf
    · exact Or.inl (hB2.trans h0)
    · exact Or.inr (hFires.trans hf)

end SeLe4n.Kernel
