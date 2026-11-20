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
reply object comes out free, which is what the take asks of it.

Before the take, `receiveIPC` returns the server's bound notification's context
(`maybeReturnSchedContext`).  A passive server bound to the context its
notification lent it holds that context here, so on the pre-state the guard
reads the server as the return leaves it: holding no context, or holding the
one the return takes back (`receiveReturnFires`, which the reply leg leaves as
it was).  The return then clears the server's binding and touches no context
but its own, which is not the queued caller's (that one is bound to the
caller), so the take's guard holds after it
(`receiveReturnSchedContext_callDonationGuard`) and the caller's context is
donated to the server, as seL4's `reply_push (canDonate)` does once the server
has no context.  The composite is then the reply's writes, the return in place
(`receiveReturnSchedContextFast`), the take, the donation and its
replenishment's migration, the server's priority walk, the caller's frame and
the server's frame (`replyRecvOnCore_callTake_delivered`), with nothing built.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency
open Architecture.RegisterDecode

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

/-- The reply leg's writes, the receive's context return in place, the
receive leg's take of the queued caller `s`,
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
          (receiveReturnSchedContextFast true (storeReplyRendezvousReady st c tid rid) tid.val)
          epId s nextCode tid rid) s tid scS)
        scS donorHome doneeHome) tid core).1
  writeDeliveredFrameIfReady Y c (Architecture.regMessageFrame layout rf len badge)
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
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
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
    (hR : registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .call capAddr mi) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvCallTakeDelivered st c tid rid epId s sTcb.queueNextCode
        ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s) (determineTargetCore st tid) core
        layout rf len badge sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
        sTcb.ipcBadged) := by
  generalize hM : ({ registers := Architecture.regMessageBody layout rf len, badge := badge } :
    IpcMessage) = msg
  have hSzM : msg.registers.size ≤ 4 := by
    rw [← hM, Architecture.regMessageBody_size]; exact hSz4
  have hSz : ¬ msg.registers.size > maxMessageRegisters := by unfold maxMessageRegisters; omega
  have hNo := replyWakesInPlace_noResizeDue hG
  have hG0 := hG
  simp only [replyWakesInPlace, Bool.and_eq_true] at hG0
  obtain ⟨⟨⟨⟨⟨_, _⟩, hFC⟩, hLR⟩, hFR⟩, hRpG⟩ := hG0
  rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRp] at hRpG
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hRpG
  obtain ⟨hNx, -⟩ := hRpG
  obtain ⟨hE1, sTcbP, hSP, hKept, hBind, hDs, hDt, hTkP, hCxP, rtP, hRtP, hOrP⟩ :=
    storeReplyRendezvous_callDonationGuard
      st c tid rid msg ct rp epId ep s sTcb hNo hT hFC hRp hNx hLR hFR hE hS hSC hNe hGt
  have hNoP := storeReplyRendezvous_noResizeDue st c tid rid msg hNo
  obtain ⟨hE2, hSP2, hDsR, hDtR, hGP⟩ := receiveReturnSchedContext_callDonationGuard _ epId ep tid s
    sTcbP rid rtP hNoP hE1 hSP hTkP hCxP hRtP hOrP
  have hR' : registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcbP.registerContext) SeLe4n.arm64DefaultLayout sTcbP.registerContext 32 =
      .call capAddr mi := by rw [hKept.regs]; exact hR
  have hF' : sTcbP.ipcFaultSend = false := by rw [hKept.faultSend]; exact hF
  obtain ⟨hRecv, -, -, hCallT, hDonE⟩ := receiveCallDonatingTake_delivered _ epId ep tid rid core s
    sTcbP capAddr mi hE2 hH hSP2 hGP hF' hR'
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
  have hEp1 := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE2
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_some, hEq, hPop, hXf, hRecv, hEp1, Option.bind_some, hH]
  simp only [replyRecvPostReceiveDonation, hCallT, ↓reduceIte, hDonE,
    applyReceiveLegPipHandoff, beq_self_eq_true, replyRecvAnswerCaller,
    CapTransferSummary.capInfo_empty]
  unfold performReplyRecvCallTakeDelivered writeReceiverMessageFrame replyRecvCallTakeLegs
    holdReplyRecvBody
  dsimp only
  rw [receiveReturnSchedContextFast_eq]
  -- the queued caller, blocked on the reply after the take
  have hTRP : receiveCallTakesReplyInPlace
      (receiveReturnSchedContext true (storeReplyRendezvous st c tid rid msg) tid) epId tid s
      sTcbP rid = true := by
    simp only [receiveCallDonatesInPlace, Bool.and_eq_true] at hGP; exact hGP.1
  obtain ⟨-, hIpcS, -⟩ := receiveCallTake_inPlace_facts _ epId ep tid rid core s sTcbP hE2 hH hSP2
    hTRP
  obtain ⟨x, hx, hxI⟩ := Option.map_eq_some_iff.mp hIpcS
  have hcs : c ≠ s := fun e => hSC e.symm
  have hct : c ≠ tid := fun e => hNe e.symm
  have hst : s ≠ tid := fun e => by
    simp only [receiveCallTakesReplyInPlace, Bool.and_eq_true, bne_iff_ne, ne_eq] at hTRP
    exact hTRP.1.1.1.1.1.1.1.1.1.2 e.symm
  have h0 := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have h1 := receiveReturnSchedContext_noResizeDue true _ tid h0
  have hNoR0 := receiveReturnSchedContext_noResizeDue true _ tid hNoP
  rw [hDsR, hDtR, hDs, hDt, hBind]
  rw [receiveCallTakeState_eq_hold _ _ _ _ _ _ hNoR0, hKept.queueNext] at hx ⊢
  rw [(blockedSender_of_routedCall _ s sTcbP capAddr mi hR' hF').2]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    receiveReturnSchedContext_msg c id _ id true _ tid h0 hct,
    storeReceiveCallReady_msg c id _ id _ epId s _ tid rid h1 hcs hct] at hx ⊢
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _
      (fun e => hst (SeLe4n.ThreadId.toObjId_injective _ _ e).symm),
    SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _
      (fun e => hcs (SeLe4n.ThreadId.toObjId_injective _ _ e))] at hx
  generalize hScS : (⟨sTcb.scBindingScCode - 1⟩ : SeLe4n.SchedContextId) = scS
  have hNoR := storeReceiveCallReady_noResizeDue _ epId s sTcb.queueNextCode tid rid h1
  generalize hRdef : storeReceiveCallReady
    (receiveReturnSchedContext true (storeReplyRendezvousReady st c tid rid) tid) epId s
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
    Architecture.returnFrameOfMessage_regMessageBody]
  have hNoW := writeDeliveredFrameIfReady_noResizeDue Y0 c
    (Architecture.regMessageFrame layout rf len badge)
    (holdMessage { registers := Architecture.regMessageBody layout rf len, badge := badge }) hNoY
  have hSzS : (Architecture.regMessageBody arm64DefaultLayout sTcbP.registerContext
      mi.length).size ≤ 4 := by
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [stageDeliveredMessage_holdMessage _ tid _ hNoW hSzS,
    Architecture.returnFrameOfMessage_regMessageBody, Architecture.regMessageFrameW_eq,
    TCB.ipcBadgeView_eq_opt, hKept.regs, hKept.badge, hKept.badged]

end CallTakeDelivered

end SeLe4n.Kernel
