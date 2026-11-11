-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvDonatedInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReceiveCallDonatingInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeInPlace

/-!
# The donated reply-receive whose receive leg takes a donating caller, in place

The passive-server loop of seL4-MCS under load: a server running on the
context its caller `c` donated answers `c` with `seL4_ReplyRecv`.  The reply
leg wakes `c`, `reply_pop` hands the context back to `c` and leaves the server
unbound, and the receive leg finds a third thread `s` queued by a `Call` on the
endpoint: `receiveIPC` pops it, blocks it on the reply through the same reply
object, and `schedContext_donate` hands `s`'s context to the now passive
server.  The specification runs the same order (`endpointReplyRecvAnsweringOnCore`).

Every check the receive leg's in-place take and donation make
(`receiveCallDonatesInPlace`) is read on the pre-state
(`receiveCallDonatesPastPop`) and carried across the reply leg and the pop
(`popDonationSettled_callDonationGuard`): the pop writes only the context it
returns, the reply object it pops, the frame below, the caller's and the
server's bindings, and the release links, so the queued caller, its context
and that context's head reply read as they did, while the reply object comes
out free and the server unbound, which is what the receive leg asks of them.
The composite is then the reply's writes, the pop, the take, the donation, the
replenishment's migration, the server's priority walk, the caller's frame and
the server's frame (`replyRecvOnCore_donatedCallTake_delivered`), with nothing
built.
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
   | .blockedOnCall _ => true
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
   | .blockedOnCall _ => true
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
    hSRp, hB0, hFree, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_self_eq_true,
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

/-- A frame write at one thread reads every other thread where it was. -/
theorem writeDeliveredFrameIfReady_getTcb?_ne (X : SystemState) (c t : SeLe4n.ThreadId)
    (f : Architecture.SyscallReturnFrame) (h : TCB → TCB) (hNe : c.toObjId ≠ t.toObjId) :
    (writeDeliveredFrameIfReady X c f (fun _ => X.mapTcbInPlace c h)).getTcb? t = X.getTcb? t := by
  unfold writeDeliveredFrameIfReady
  split
  · split <;> exact SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe
  · rfl

theorem writeDeliveredFrameIfReady_noResizeDue (X : SystemState) (c : SeLe4n.ThreadId)
    (f : Architecture.SyscallReturnFrame) (h : TCB → TCB) (hNo : X.objects.noResizeDue) :
    (writeDeliveredFrameIfReady X c f (fun _ => X.mapTcbInPlace c h)).objects.noResizeDue := by
  unfold writeDeliveredFrameIfReady
  split
  · split <;> exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo
  · exact hNo

end Commute

section DonatedCallTake

/-- **A donated reply-receive whose receive leg takes a donating caller**, every
write in its slot, read on the pre-state: the caller `c` blocked on a reply from
the receiver through reply object `rid` and the pop's checks
(`replyPopsInPlace`), the receiver an unreserved thread, and at the head of the
endpoint's send queue a thread other than `c`, delivering no fault, whose take
and donation the reply leg and the pop leave in place
(`receiveCallDonatesPastPop`).  Every read is a code. -/
@[inline] def replyRecvDonatedCallTakes (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ (some server) => server.val == tid.val
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1 &&
       replyPopsInPlace st c ct.scBindingScCode tid rid
   | none => false) &&
  !tid.isReserved &&
  (match st.getEndpoint? epId with
   | some ep =>
       (match ep.sendQ.head with
        | some s =>
            s.val != c.val &&
            (match st.getTcb? s with
             | some sTcb => !sTcb.ipcFaultSend &&
                 receiveCallDonatesPastPop st epId tid s sTcb rid (replyHeadContextCode st rid)
             | none => false)
        | none => false)
   | none => false)

theorem replyRecvDonatedCallTakes_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvDonatedCallTakes st epId tid c rid = true) :
    ∃ (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB),
      st.objects[c.toObjId]? = some (.tcb ct) ∧
      ct.ipcState = .blockedOnReply ep0 (some tid) ∧ ct.replyObject = some rid ∧
      replyPopsInPlace st c ct.scBindingScCode tid rid = true ∧ tid.isReserved = false ∧
      st.getEndpoint? epId = some ep ∧ ep.sendQ.head = some s ∧
      st.getTcb? s = some sTcb ∧ s ≠ c ∧ sTcb.ipcFaultSend = false ∧
      receiveCallDonatesPastPop st epId tid s sTcb rid (replyHeadContextCode st rid) = true := by
  unfold replyRecvDonatedCallTakes at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hC, hSRes⟩, hE⟩ := h
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at hC; cases hC
  | some ct =>
  rw [hTc] at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hIpc, hRO⟩, hW⟩ := hC
  obtain ⟨ep0, hIpc'⟩ : ∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid) := by
    revert hIpc
    split
    · next ep0 server hS =>
      intro e
      have : server = tid := by
        cases server; cases tid; simp only [beq_iff_eq] at e; subst e; rfl
      subst this
      exact ⟨ep0, hS⟩
    · intro e; cases e
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at hE; cases hE
  | some ep =>
  rw [hEp] at hE
  dsimp only at hE
  cases hH : ep.sendQ.head with
  | none => rw [hH] at hE; cases hE
  | some s =>
  rw [hH] at hE
  simp only [Bool.and_eq_true] at hE
  obtain ⟨hSC, hT⟩ := hE
  have hSC' : s ≠ c := fun e => by subst e; simp at hSC
  cases hTs : st.getTcb? s with
  | none => rw [hTs] at hT; cases hT
  | some sTcb =>
  rw [hTs] at hT
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hT
  obtain ⟨hF, hG⟩ := hT
  refine ⟨ct, ep0, ep, s, sTcb, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hW,
    hSRes, rfl, hH, hTs, hSC', hF, hG⟩
  simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]

/-- The reply leg's writes, the pop and its settle, the receive leg's take of
the queued caller `s`, the donation of `s`'s context to the server, its
replenishment migrated from `donorHome` to `doneeHome`, the server's priority
walk, then the answered caller's frame, read from the server's saved registers
`rf`.  Out of line from the server's own frame (`writeReceiverMessageFrame`):
`rf` is the server's register file, released once these legs return, so that
frame's write finds it unshared. -/
@[noinline] def replyRecvDonatedCallTakeLegs (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (scS : SeLe4n.SchedContextId)
    (donorHome doneeHome core : CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) : SystemState :=
  let Y := (PriorityInheritance.propagatePipChainCrossCore
      (migrateSchedContextReplenishment
        (donateSchedContextInPlace (storeReceiveCallReady
          (popDonationSettledInPlace (storeReplyRendezvousReady st c tid rid) c tid scId home)
          epId s nextCode tid rid) s tid scS) scS donorHome doneeHome) tid core).1
  writeDeliveredFrameIfReady Y c (Architecture.regReplyRecvFrame layout rf len badge)
    (fun _ => holdReplyRecvBody Y c layout rf len badge)

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

/-- **The donated reply-receive taking a donating caller, delivered**: the legs
(`replyRecvDonatedCallTakeLegs`), then the server's frame
(`writeReceiverMessageFrame`). -/
@[inline] def performReplyRecvDonatedCallTakeDelivered (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId)
    (home : CoreId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (donorHome doneeHome core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (sRf : SeLe4n.RegisterFile) (sLen : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) : SystemState :=
  writeReceiverMessageFrame
    (replyRecvDonatedCallTakeLegs st c tid rid scId home epId s nextCode scS donorHome doneeHome
      core layout rf len badge) tid sRf sLen badgeWord badged

end DonatedCallTake

section DonatedCallTakeDelivered

theorem replyPopsInPlace_serverTcb {st : SystemState} {c : SeLe4n.ThreadId} {b : Nat}
    {server : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyPopsInPlace st c b server rid = true) : (st.getTcb? server).isSome = true := by
  unfold replyPopsInPlace at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-- **The donated reply-receive taking a donating caller is the
specification's**: under the pop's guard with the receiver the server the
caller recorded, a reply of at most four words transferring no capability, and
at the head of the send queue a caller `s` other than `c`, blocked by a routed
capability-free call, delivering no fault, whose take and donation the reply
leg and the pop leave in place (each read on the pre-state and carried by
`popDonationSettled_callDonationGuard`), the checked arm's result is
`performReplyRecvDonatedCallTakeDelivered`, every context, core and word it
takes read on the pre-state. -/
theorem replyRecvOnCore_donatedCallTake_delivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId)
    (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hSz4 : Architecture.regMessageLength layout len - 1 ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hInert : replyTransferInert st tid ct grant = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hF : sTcb.ipcFaultSend = false)
    (hGt : receiveCallDonatesPastPop st epId tid s sTcb rid (replyHeadContextCode st rid) = true)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .call capAddr mi) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvDonatedCallTakeDelivered st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId s sTcb.queueNextCode
        ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s) (determineTargetCore st tid) core
        layout rf len badge sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
        sTcb.ipcBadged) := by
  generalize hM : ({ registers := Architecture.regReplyRecvBody layout rf len, badge := badge } :
    IpcMessage) = msg
  have hSzM : msg.registers.size ≤ 4 := by
    rw [← hM, Architecture.regReplyRecvBody_size]; exact hSz4
  have hSz : ¬ msg.registers.size > maxMessageRegisters := by unfold maxMessageRegisters; omega
  obtain ⟨rp, scId, sc, hRp, hN, hScO, hHead, hBelow, hCode, hCRes, hNe', hNo, hLC, hFC, hLR, hFR,
    _, hPop⟩ := replyPopsInPlace_donation st c tid rid msg ct hT hSRes hG
  have hNe : tid ≠ c := fun e => hNe' e.symm
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  rw [hCode] at hGt
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st tid c tid ct ep0 rid rp msg core hSz hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  obtain ⟨hEP, sTcbP, hSP, hKept, hBind, hDs, hDt, hGP⟩ := popDonationSettled_callDonationGuard
    st c tid rid msg ct rp scId sc (determineTargetCore st c) epId ep s sTcb _ rfl hNo hT hFC hRp
    hN hScO hHead hBelow hNe hLR hFR (replyPopsInPlace_serverTcb hG) hE hS hSC hGt
  have hR' : registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcbP.registerContext 32 =
      .call capAddr mi := by rw [hKept.regs]; exact hR
  have hF' : sTcbP.ipcFaultSend = false := by rw [hKept.faultSend]; exact hF
  obtain ⟨hRecv, -, -, hCallT, hDonE⟩ := receiveCallDonatingTake_delivered _ epId ep tid rid core s
    sTcbP capAddr mi hEP hH hSP hGP hF' hR'
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hXf := replyRecvReplyTransfer_of_inert none st tid c grant ct hTc (fun _ => hInert)
  have hRecS : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  rw [← storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hPop
  have hEp1 := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hEP
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_some, hEq, hPop, hXf, hRecv, hEp1, Option.bind_some, hH]
  simp only [replyRecvPostReceiveDonation, hCallT, ↓reduceIte, replyRecvHolderDeschedule, hDonE,
    applyReceiveLegPipHandoff, beq_self_eq_true, replyRecvAnswerCaller,
    CapTransferSummary.capInfo_empty]
  unfold performReplyRecvDonatedCallTakeDelivered writeReceiverMessageFrame
    replyRecvDonatedCallTakeLegs holdReplyRecvBody
  dsimp only
  -- the queued caller, blocked on the reply after the take
  have hTRP : receiveCallTakesReplyInPlace (popDonationSettledInPlace
      (storeReplyRendezvous st c tid rid msg) c tid scId (determineTargetCore st c)) epId tid s
      sTcbP rid = true := by
    simp only [receiveCallDonatesInPlace, Bool.and_eq_true] at hGP; exact hGP.1
  obtain ⟨-, hIpcS, -⟩ := receiveCallTake_inPlace_facts _ epId ep tid rid core s sTcbP hEP hH hSP
    hTRP
  obtain ⟨x, hx, hxI⟩ := Option.map_eq_some_iff.mp hIpcS
  have hcs : c ≠ s := fun e => hSC e.symm
  have hct : c ≠ tid := hNe'
  have hst : s ≠ tid := fun e => by
    simp only [receiveCallTakesReplyInPlace, Bool.and_eq_true, bne_iff_ne, ne_eq] at hTRP
    exact hTRP.1.1.1.1.1.1.1.1.1.2 e.symm
  have h1 := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hNoP : (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId
      (determineTargetCore st c)).objects.noResizeDue := by
    rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]
    exact popDonationSettledInPlace_noResizeDue _ c tid scId _
      ((RHTable.noResizeDue_mapValueAt _ _ _).mpr h1)
  have hNoPr := popDonationSettledInPlace_noResizeDue _ c tid scId (determineTargetCore st c) h1
  rw [hDs, hDt, hBind]
  rw [receiveCallTakeState_eq_hold _ _ _ _ _ _ hNoP, hKept.queueNext] at hx ⊢
  rw [(blockedSender_of_routedCall _ s sTcbP capAddr mi hR' hF').2]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    popDonationSettledInPlace_msg c id _ id _ c tid scId _ h1 hct,
    storeReceiveCallReady_msg c id _ id _ epId s _ tid rid hNoPr hcs hct] at hx ⊢
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _
      (fun e => hst (SeLe4n.ThreadId.toObjId_injective _ _ e).symm),
    SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _
      (fun e => hcs (SeLe4n.ThreadId.toObjId_injective _ _ e))] at hx
  generalize hScS : (⟨sTcb.scBindingScCode - 1⟩ : SeLe4n.SchedContextId) = scS
  have hNoR := storeReceiveCallReady_noResizeDue _ epId s sTcb.queueNextCode tid rid hNoPr
  generalize hRdef : storeReceiveCallReady (popDonationSettledInPlace
    (storeReplyRendezvousReady st c tid rid) c tid scId (determineTargetCore st c)) epId s
    sTcb.queueNextCode tid rid = R at hx hNoR ⊢
  have hNoRc : (R.mapTcbInPlace c (holdMessage msg)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoR
  rw [donateSchedContextInPlace_msg tid id _ id _ s tid scS hNoRc hst.symm,
    donateSchedContextInPlace_msg c id _ id R s tid scS hNoR hcs,
    migrateSchedContextReplenishment_mapTcbInPlace, migrateSchedContextReplenishment_mapTcbInPlace]
  have hNoD := donateSchedContextInPlace_noResizeDue R s tid scS hNoR
  have hNoM := migrateSchedContextReplenishment_noResizeDue _ scS (determineTargetCore st s)
    (determineTargetCore st tid) hNoD
  rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ ?_, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoM]
  rotate_left
  · exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoM
  -- the caller's state carried to the walk's
  obtain ⟨x1, hx1, e1⟩ := donateSchedContextInPlace_ipcStateCarried R s tid scS hNoR s x hx
  have hx2 := (migrateSchedContextReplenishment_getTcb? _ scS (determineTargetCore st s)
    (determineTargetCore st tid) s).trans hx1
  obtain ⟨x', hx', e'⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core hNoM s x1 hx2
  have hNoY := propagatePipChainCrossCore_noResizeDue _ tid core hNoM
  generalize (PriorityInheritance.propagatePipChainCrossCore (migrateSchedContextReplenishment
    (donateSchedContextInPlace R s tid scS) scS (determineTargetCore st s)
    (determineTargetCore st tid)) tid core).1 = Y0 at hx' hNoY ⊢
  rw [show ∀ m : IpcMessage, TCB.withMessageSlots id (fun _ => some m) id = holdMessage m from
    fun _ => rfl]
  rw [SystemState.mapTcbInPlace_swap Y0 _ _ (fun h => absurd h hNe)]
  subst hM
  have hcsO : c.toObjId ≠ s.toObjId := fun e => hcs (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hNoYt : (Y0.mapTcbInPlace tid (holdMessage
      { registers := Architecture.regMessageBody arm64DefaultLayout sTcbP.registerContext mi.length,
        badge := sTcbP.ipcBadgeView })).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoY
  rw [stageDeliveredMessage_holdMessage _ c _ hNoYt hSzM,
    writeDeliveredFrameIfReady_mapTcbInPlace Y0 c tid _ _ _ hct,
    Architecture.returnFrameOfMessage_regReplyRecvBody]
  have hNoW := writeDeliveredFrameIfReady_noResizeDue Y0 c
    (Architecture.regReplyRecvFrame layout rf len badge)
    (holdMessage { registers := Architecture.regReplyRecvBody layout rf len, badge := badge }) hNoY
  rw [stageWokenSendCompletion_msg _ tid s id _ id hst hNoW,
    Architecture.stageWokenSendCompletion_id_when_not_ready _ s x'
      ((writeDeliveredFrameIfReady_getTcb?_ne Y0 c s _ _ hcsO).trans hx')
      (by rw [e', e1, hxI]; exact fun h => by cases h)]
  have hSzS : (Architecture.regMessageBody arm64DefaultLayout sTcbP.registerContext
      mi.length).size ≤ 4 := by
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [show ∀ m : IpcMessage, TCB.withMessageSlots id (fun _ => some m) id = holdMessage m from
    fun _ => rfl]
  rw [stageDeliveredMessage_holdMessage _ tid _ hNoW hSzS,
    Architecture.returnFrameOfMessage_regMessageBody, Architecture.regMessageFrameW_eq,
    TCB.ipcBadgeView_eq_opt, hKept.regs, hKept.badge, hKept.badged]

end DonatedCallTakeDelivered

end SeLe4n.Kernel
