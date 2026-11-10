-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvDonatedCallTakeInPlace

/-!
# The reply-receive whose receive leg takes a donating caller, in place

The server loop of seL4-MCS on a passive server answering a caller that did not
donate: the server answers its caller `c` with `seL4_ReplyRecv`, the reply leg
wakes `c` and frees the reply object (`doReplyTransfer`, `reply_remove`), and
the receive leg finds a third thread `s` queued by a `Call` on the endpoint:
`receiveIPC` pops it, blocks it on the reply through the same reply object, and
-- the server holding no context -- `reply_push (canDonate)` donates `s`'s
context to the server (`schedContext_donate`).  The specification runs the
same order (`endpointReplyRecvAnsweringOnCore`, the pop returning nothing, then
`replyRecvPostReceiveDonation`'s donation of a dequeued call).

Every check the receive leg's in-place take and donation make
(`receiveCallDonatesInPlace`) is read on the pre-state
(`receiveCallDonatesPastReply`) and carried across the reply leg
(`storeReplyRendezvous_callDonationGuard`): the reply leg writes the caller,
its reply object and the server's reply-waiter links, so the queued caller, its
context, the context's reply stack and the server read as they did, while the
reply object comes out free, which is what the take asks of it.  The composite
is then the reply's writes, the take, the donation and its replenishment's
migration, the server's priority walk, the caller's frame and the server's
frame (`replyRecvOnCore_callTake_delivered`), with nothing built.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency
open Architecture.RegisterDecode

section CallTakeGuard

/-- **The receive leg's take of a donating caller, checked before the reply
leg**: every check of `receiveCallDonatesInPlace` but the reply object's being
free, read on the pre-state.  On the pre-state the reply object still links the
answered caller; the reply leg frees it (`storeReplyRendezvous_callDonationGuard`
carries the rest and proves that one). -/
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
   | .blockedOnCall _ => true
   | _ => false) &&
  (match st.getTcb? receiver with
   | some rt => callDonationReady st s receiver sTcb rt rid
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
   | .blockedOnCall _ => true
   | _ => false) &&
  (match st.getTcb? receiver with
   | some rt => callDonationReady st s receiver sTcb rt rid
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
and the take's and the donation's in-place guard (`receiveCallDonatesInPlace`)
holds, each check read on the pre-state (`receiveCallDonatesPastReply`): the
reply object, linking no stack, comes out free, and the reply leg writes nothing
else the guard reads. -/
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
        receiveCallDonatesInPlace (storeReplyRendezvous st c tid rid msg) epId tid s sTcb1 rid =
          true := by
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
  simp only [callDonationReady_eq_callerContextReady, Bool.and_eq_true] at hRT
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
  obtain ⟨hI, hL⟩ := storeReplyRendezvousReady_fields st c tid rid hNo
  rw [hS1] at hI hL
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
  have hV : ∀ x, notVSpaceRootAt st x = true → notVSpaceRootAt T x = true := by
    intro x hx
    by_cases hxc : x = c.toObjId
    · subst hxc; obtain ⟨t, h⟩ := hTC
      unfold notVSpaceRootAt; rw [SystemState.getObject?_eq_getElem, h]
    · by_cases hxr : x = rid.toObjId
      · subst hxr; unfold notVSpaceRootAt; rw [SystemState.getObject?_eq_getElem, hTR]
      · rw [notVSpaceRootAt_of_view (hView x hxc hxr)]; exact hx
  have hKF : T.objectsKeepFinds st := by
    rw [← hTdef]; exact (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
  have hIT : T.objectIndexSet = st.objectIndexSet := by rw [← hTdef]; exact hI
  have hLT : T.lifecycle = st.lifecycle := by rw [← hTdef]; exact hL
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
    fun h => storeLeavesIndexAndTypes_of_frame hIT hLT hV h
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
  refine ⟨agreeAt_of_not_tcb (hView _ hEc hEr) (fun _ e => by cases e) hE, sTcb1, hsT, hKept,
    hBind, hDs, hDt, ?_⟩
  have hFree : rp.consumed.isFree = true := by
    rw [Reply.isFree_iff]
    refine ⟨Reply.consumed_caller _, ?_, ?_⟩ <;> simp [Reply.consumed, hNx]
  have hRtG : T.getTcb? tid = some rt1 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hRt1
  have hRpG : T.getReply? rid = some rp.consumed := (SystemState.getReply?_eq_some_iff _ _ _).mpr hTR
  have hkT : T.getSchedContext? ⟨k⟩ = some scs := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hkc hkr) (fun _ e => by cases e) hScsO)
  have hRO' : sTcb1.replyObject = sTcb.replyObject := by simp only [TCB.replyObject, hROc]
  have hSWT := sendWakesInPlace_of_frame epId s sTcb.queueNext hIT hLT hKF hV hTcb hSW
  have hLRtT := hSL hLRt
  have hFRtT := (hKF _).trans hFRt
  have hLRT := hSL hLR
  have hFRT := (hKF _).trans hFR
  have hLscT := hSL hLsc
  have hFscT := (hKF _).trans hFsc
  simp only [Bool.not_eq_true', bne_iff_ne, ne_eq] at hRS hRN hRRes
  unfold receiveCallDonatesInPlace receiveCallTakesReplyInPlace
  rw [hRtG, hRpG, hQ, hRO', hKept.ipcState]
  simp only [callDonationReady_eq_callerContextReady, callerContextReady, hBind, hk, hkT, hB2,
    hFree, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, Option.isSome_some]
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

end CallTakeGuard

section CallTake

/-- **A reply-receive whose receive leg takes a donating caller**, every write
in its slot, read on the pre-state: the receiver other than the caller `c`, `c`
blocked on a reply from the receiver through reply object `rid` and the reply's
checks (`replyWakesInPlace`), and at the head of the endpoint's send queue a
thread other than `c`, delivering no fault, whose take and donation the reply
leg leaves in place (`receiveCallDonatesPastReply`).  Every read is a code. -/
@[inline] def replyRecvCallTakes (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  tid.val != c.val &&
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ (some server) => server.val == tid.val
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1 &&
       replyWakesInPlace st c ct rid
   | none => false) &&
  (match st.getEndpoint? epId with
   | some ep =>
       (match ep.sendQ.head with
        | some s =>
            s.val != c.val &&
            (match st.getTcb? s with
             | some sTcb => !sTcb.ipcFaultSend && receiveCallDonatesPastReply st epId tid s sTcb rid
             | none => false)
        | none => false)
   | none => false) &&
  (match st.getReply? rid with
   | some _ => true
   | none => false)

theorem replyRecvCallTakes_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvCallTakes st epId tid c rid = true) :
    ∃ (ct : TCB) (ep0 : SeLe4n.ObjId) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId)
      (sTcb : TCB),
      st.objects[c.toObjId]? = some (.tcb ct) ∧
      ct.ipcState = .blockedOnReply ep0 (some tid) ∧ ct.replyObject = some rid ∧
      replyWakesInPlace st c ct rid = true ∧ tid ≠ c ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧
      st.getEndpoint? epId = some ep ∧ ep.sendQ.head = some s ∧
      st.getTcb? s = some sTcb ∧ s ≠ c ∧ sTcb.ipcFaultSend = false ∧
      receiveCallDonatesPastReply st epId tid s sTcb rid = true := by
  unfold replyRecvCallTakes at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hNe, hC⟩, hE⟩, hRp⟩ := h
  have hNe' : tid ≠ c := fun e => by subst e; simp at hNe
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
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRp; cases hRp
  | some rp =>
  refine ⟨ct, ep0, rp, ep, s, sTcb, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hW,
    hNe', (SystemState.getReply?_eq_some_iff _ _ _).mp hR, rfl, hH, hTs, hSC', hF, hG⟩
  simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]

/-- The reply leg's writes, the receive leg's take of the queued caller `s`,
the donation of `s`'s context `scS` to the server, its replenishment migrated
from `donorHome` to `doneeHome`, the server's priority walk, then the answered
caller's frame, read from the server's saved registers `rf`.  Out of line from
the server's own frame (`writeReceiverMessageFrame`): `rf` is the server's
register file, released once these legs return, so that frame's write finds it
unshared. -/
@[noinline] def replyRecvCallTakeLegs (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (donorHome doneeHome core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) : SystemState :=
  let Y := (PriorityInheritance.propagatePipChainCrossCore
      (migrateSchedContextReplenishment
        (donateSchedContextInPlace (storeReceiveCallReady
          (storeReplyRendezvousReady st c tid rid) epId s nextCode tid rid) s tid scS)
        scS donorHome doneeHome) tid core).1
  writeDeliveredFrameIfReady Y c (Architecture.regReplyRecvFrame layout rf len badge)
    (fun _ => holdReplyRecvBody Y c layout rf len badge)

/-- **The reply-receive taking a donating caller, delivered**: the legs
(`replyRecvCallTakeLegs`), then the server's frame
(`writeReceiverMessageFrame`). -/
@[inline] def performReplyRecvCallTakeDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (donorHome doneeHome core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (sRf : SeLe4n.RegisterFile) (sLen : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) : SystemState :=
  writeReceiverMessageFrame
    (replyRecvCallTakeLegs st c tid rid epId s nextCode scS donorHome doneeHome core layout rf
      len badge) tid sRf sLen badgeWord badged

end CallTake

section CallTakeDelivered

/-- **The reply-receive taking a donating caller is the specification's**: under
the reply's guard with the receiver the server the caller recorded, a reply of
at most four words transferring no capability, and at the head of the send
queue a caller `s` other than `c`, blocked by a routed capability-free call,
delivering no fault, whose take and donation the reply leg leaves in place
(each check read on the pre-state and carried by
`storeReplyRendezvous_callDonationGuard`), the checked arm's result is
`performReplyRecvCallTakeDelivered`: the pop returns nothing, so the dequeued
call donates its context to the server exactly as `.receive` does
(`replyRecvPostReceiveDonation`), every context, core and word it takes read on
the pre-state. -/
theorem replyRecvOnCore_callTake_delivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (rp : Reply) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hSz4 : Architecture.regMessageLength layout len - 1 ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true) (hNe : tid ≠ c)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hInert : replyTransferInert st tid ct grant = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hF : sTcb.ipcFaultSend = false)
    (hGt : receiveCallDonatesPastReply st epId tid s sTcb rid = true)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .call capAddr mi) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvCallTakeDelivered st c tid rid epId s sTcb.queueNextCode
        ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s) (determineTargetCore st tid) core
        layout rf len badge sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
        sTcb.ipcBadged) := by
  generalize hM : ({ registers := Architecture.regReplyRecvBody layout rf len, badge := badge } :
    IpcMessage) = msg
  have hSzM : msg.registers.size ≤ 4 := by
    rw [← hM, Architecture.regReplyRecvBody_size]; exact hSz4
  have hSz : ¬ msg.registers.size > maxMessageRegisters := by unfold maxMessageRegisters; omega
  have hNo := replyWakesInPlace_noResizeDue hG
  have hG0 := hG
  simp only [replyWakesInPlace, Bool.and_eq_true] at hG0
  obtain ⟨⟨⟨⟨⟨_, _⟩, hFC⟩, hLR⟩, hFR⟩, hRpG⟩ := hG0
  rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRp] at hRpG
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hRpG
  obtain ⟨hNx, -⟩ := hRpG
  obtain ⟨hE1, sTcbP, hSP, hKept, hBind, hDs, hDt, hGP⟩ := storeReplyRendezvous_callDonationGuard
    st c tid rid msg ct rp epId ep s sTcb hNo hT hFC hRp hNx hLR hFR hE hS hSC hNe hGt
  have hR' : registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcbP.registerContext 32 =
      .call capAddr mi := by rw [hKept.regs]; exact hR
  have hF' : sTcbP.ipcFaultSend = false := by rw [hKept.faultSend]; exact hF
  obtain ⟨hRecv, -, -, hCallT, hDonE⟩ := receiveCallDonatingTake_delivered _ epId ep tid rid core s
    sTcbP capAddr mi hE1 hH hSP hGP hF' hR'
  obtain ⟨hEq, hHead⟩ := replyOnCore_inPlace st tid c tid ct ep0 rid msg core hSz hT hIpc hRO hG
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hXf := replyRecvReplyTransfer_of_inert none st tid c grant ct hTc (fun _ => hInert)
  have hRecS : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hPop : replyRecvPopDonation rid c (storeReplyRendezvous st c tid rid msg) =
      .ok (none, storeReplyRendezvous st c tid rid msg) := by
    unfold replyRecvPopDonation
    rw [replyFrameHeadHolder?_of_no_head _ _ hHead]
    simp only [popUnheldReplyHead_of_no_head _ _ _ _ hHead]
  have hEp1 := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE1
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_some, hEq, hPop, hXf, hRecv, hEp1, Option.bind_some, hH]
  simp only [replyRecvPostReceiveDonation, hCallT, ↓reduceIte, hDonE,
    applyReceiveLegPipHandoff, beq_self_eq_true, replyRecvAnswerCaller,
    CapTransferSummary.capInfo_empty]
  unfold performReplyRecvCallTakeDelivered writeReceiverMessageFrame replyRecvCallTakeLegs
    holdReplyRecvBody
  dsimp only
  -- the queued caller, blocked on the reply after the take
  have hTRP : receiveCallTakesReplyInPlace (storeReplyRendezvous st c tid rid msg) epId tid s
      sTcbP rid = true := by
    simp only [receiveCallDonatesInPlace, Bool.and_eq_true] at hGP; exact hGP.1
  obtain ⟨-, hIpcS, -⟩ := receiveCallTake_inPlace_facts _ epId ep tid rid core s sTcbP hE1 hH hSP
    hTRP
  obtain ⟨x, hx, hxI⟩ := Option.map_eq_some_iff.mp hIpcS
  have hcs : c ≠ s := fun e => hSC e.symm
  have hct : c ≠ tid := fun e => hNe e.symm
  have hst : s ≠ tid := fun e => by
    simp only [receiveCallTakesReplyInPlace, Bool.and_eq_true, bne_iff_ne, ne_eq] at hTRP
    exact hTRP.1.1.1.1.1.1.1.1.1.2 e.symm
  have h1 := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hNoP : (storeReplyRendezvous st c tid rid msg).objects.noResizeDue := by
    rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]
    exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr h1
  rw [hDs, hDt, hBind]
  rw [receiveCallTakeState_eq_hold _ _ _ _ _ _ hNoP, hKept.queueNext] at hx ⊢
  rw [(blockedSender_of_routedCall _ s sTcbP capAddr mi hR' hF').2]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    storeReceiveCallReady_msg c id _ id _ epId s _ tid rid h1 hcs hct] at hx ⊢
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _
      (fun e => hst (SeLe4n.ThreadId.toObjId_injective _ _ e).symm),
    SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _
      (fun e => hcs (SeLe4n.ThreadId.toObjId_injective _ _ e))] at hx
  generalize hScS : (⟨sTcb.scBindingScCode - 1⟩ : SeLe4n.SchedContextId) = scS
  have hNoR := storeReceiveCallReady_noResizeDue _ epId s sTcb.queueNextCode tid rid h1
  generalize hRdef : storeReceiveCallReady (storeReplyRendezvousReady st c tid rid) epId s
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

end CallTakeDelivered

end SeLe4n.Kernel
