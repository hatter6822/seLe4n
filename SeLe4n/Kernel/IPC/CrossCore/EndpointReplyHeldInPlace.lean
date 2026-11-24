/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvDonatedInPlace
import SeLe4n.Kernel.IPC.Operations.HeldContextPopInPlace

/-!
# A reply to a caller holding a context of its own, each object written in its slot

seL4-MCS's `doReplyTransfer` on a reply whose frame heads the stack of the
context the server holds, the answered caller holding a context of its own: the
reply leg, then `reply_pop`'s held arm (the head popped off the context, which
stays with the server, `keepDonatedSchedContextInPlace`), the server's priority
walk, and on a reply-receive the receive leg blocking the server on its
endpoint.  When every check of the reply leg and of the pop passes on the
pre-state (`replyHeldPopsInPlace`), each write lands in its slot and the result
is proven equal to the specification's (`replyTransferChecked_held_inPlace`,
`replyRecvOnCore_held_delivered`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section HeldPopFrame

/-- The held pop leaves the table's size and capacity alone. -/
theorem keepDonatedSchedContextInPlace_noResizeDue (st : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hNo : st.objects.noResizeDue) :
    (keepDonatedSchedContextInPlace st holder scId).objects.noResizeDue := by
  unfold keepDonatedSchedContextInPlace
  split
  · exact hNo
  · split
    · exact hNo
    · split
      · exact hNo
      · split
        · exact hNo
        · dsimp only
          refine updateTcb_noResizeDue _ _ _ ?_
          split <;> (repeat (first | exact hNo | apply modifyObject_noResizeDue |
            apply updateSchedContext_noResizeDue))

/-- **The held pop commutes with a delivery** to a thread other than the
holder: it reads no message slot, and writes only the holder's binding, the
context and the two replies' links. -/
theorem keepDonatedSchedContextInPlace_msg (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (st : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hNo : st.objects.noResizeDue) (hH : r ≠ holder) :
    keepDonatedSchedContextInPlace (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) holder scId =
      (keepDonatedSchedContextInPlace st holder scId).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  have hPop : ∀ x : Reply, popOuterCode (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) x =
      popOuterCode st x := by
    intro x; unfold popOuterCode; simp only [SystemState.getReply?_mapTcbInPlace]
  have hTH : (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).getTcb? holder = st.getTcb? holder := by
    rw [SystemState.getTcb?_mapTcbInPlace, if_neg hH]
  unfold keepDonatedSchedContextInPlace
  simp only [SystemState.getSchedContext?_mapTcbInPlace, SystemState.getReply?_mapTcbInPlace,
    hPop, hTH]
  cases st.getSchedContext? scId with
  | none => rfl
  | some sc =>
    try dsimp only
    cases sc.scReply with
    | none => rfl
    | some hr =>
      try dsimp only
      cases st.getReply? hr with
      | none => rfl
      | some rr =>
        try dsimp only
        cases st.getTcb? holder with
        | none => rfl
        | some ht =>
          try dsimp only
          cases rr.prev with
          | none =>
            try dsimp only
            rw [updateSchedContext_msg r ρ μ π _ _ _ hNo,
              modifyObject_msg r ρ μ _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
                (fun o => by cases o <;> rfl),
              updateTcb_msg r ρ μ π _ holder _ ?_ (fun h => absurd h hH.symm)]
            all_goals (repeat (first | exact hNo | with_reducible apply modifyObject_noResizeDue |
              with_reducible apply updateSchedContext_noResizeDue))
          | some b =>
            try dsimp only
            rw [updateSchedContext_msg r ρ μ π _ _ _ hNo,
              modifyObject_msg r ρ μ _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
                (fun o => by cases o <;> rfl),
              modifyObject_msg r ρ μ _ _ _ ?_ (fun o => by cases o <;> rfl),
              updateTcb_msg r ρ μ π _ holder _ ?_ (fun h => absurd h hH.symm)]
            all_goals (repeat (first | exact hNo | with_reducible apply modifyObject_noResizeDue |
              with_reducible apply updateSchedContext_noResizeDue))

/-- **The held pop writes only what a pop writes**, each in its slot. -/
theorem keepDonatedSchedContextInPlace_popFrame (st : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hNo : st.objects.noResizeDue) :
    popFrame (keepDonatedSchedContextInPlace st holder scId) st := by
  unfold keepDonatedSchedContextInPlace
  split
  · exact popFrame.refl st
  · split
    · exact popFrame.refl st
    · split
      · exact popFrame.refl st
      · split
        · exact popFrame.refl st
        · dsimp only
          split
          · refine (popFrame_updateTcb _ _ _ ?_ ?_).trans
              ((popFrame_modifyObject _ _ _ ?_ ?_).trans
              (popFrame_updateSchedContext _ _ _ hNo))
            all_goals (repeat (first | exact hNo | apply modifyObject_noResizeDue |
              apply updateSchedContext_noResizeDue |
              (intro o; cases o <;> rfl) | (intro _; rfl)))
          · refine (popFrame_updateTcb _ _ _ ?_ ?_).trans
              ((popFrame_modifyObject _ _ _ ?_ ?_).trans
              ((popFrame_modifyObject _ _ _ ?_ ?_).trans
              (popFrame_updateSchedContext _ _ _ hNo)))
            all_goals (repeat (first | exact hNo | apply modifyObject_noResizeDue |
              apply updateSchedContext_noResizeDue |
              (intro o; cases o <;> rfl) | (intro _; rfl)))

/-- The held pop's last write, on any state its earlier writes leave: the
holder's binding codes rewritten, the popped head untouched. -/
theorem heldPopTail_exact (S s3 : SystemState) (holder : SeLe4n.ThreadId) (hr : SeLe4n.ReplyId)
    (r : Reply) (ht : TCB) (sc own : Nat) (h3 : s3.objects.noResizeDue) (hF3 : popFrame s3 S)
    (hS3R : s3.objects[hr.toObjId]? = some (.reply { r with prev := none, next := none }))
    (hHR : holder.toObjId ≠ hr.toObjId)
    (hHo : S.objects[holder.toObjId]? = some (.tcb ht)) :
    (∃ t, (s3.updateTcb holder fun t =>
          { t with scBindingScCode := sc, scBindingOwnerCode := own }).objects[holder.toObjId]? =
        some (.tcb t) ∧ t.scBindingScCode = sc ∧ t.scBindingOwnerCode = own ∧
        ({ t.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 } : TCB) =
          { ht.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 }) ∧
      (s3.updateTcb holder fun t =>
          { t with scBindingScCode := sc, scBindingOwnerCode := own }).objects[hr.toObjId]? =
        some (.reply { r with prev := none, next := none }) := by
  obtain ⟨x, hx, ex⟩ := popAgreeAt_tcb (hF3.2.2.2 holder.toObjId) hHo
  refine ⟨⟨{ x with scBindingScCode := sc, scBindingOwnerCode := own }, ?_, rfl, rfl, ?_⟩, ?_⟩
  · rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ h3, SystemState.objects_mapTcbInPlace,
      if_pos (beq_self_eq_true _), hx]
    rfl
  · exact ex
  · rw [objects_updateTcb_ne _ _ _ h3 _ (fun e => hHR e.symm)]
    exact hS3R

/-- **The held pop's two exact writes the receive reads**: the holder's binding
the one `heldPopOwnerCode` reads, every other field as it was, and the popped
head off its links. -/
theorem keepDonatedSchedContextInPlace_exact (S : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (hr : SeLe4n.ReplyId) (r : Reply)
    (ht : TCB) (hNo : S.objects.noResizeDue)
    (hSc : S.getSchedContext? scId = some sc) (hH : sc.scReply = some hr)
    (hR : S.getReply? hr = some r) (hHt : S.getTcb? holder = some ht)
    (hb : ∀ b, r.prev = some b → b ≠ hr) :
    (∃ t, (keepDonatedSchedContextInPlace S holder scId).objects[holder.toObjId]? = some (.tcb t) ∧
        t.scBindingScCode = scId.val + 1 ∧
        t.scBindingOwnerCode = heldPopOwnerCode ht.scBindingOwnerCode (popOuterCode S r) ∧
        ({ t.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 } : TCB) =
          { ht.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 }) ∧
      (keepDonatedSchedContextInPlace S holder scId).objects[hr.toObjId]? =
        some (.reply { r with prev := none, next := none }) := by
  have hRo := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hHo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hHt
  have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hHR : holder.toObjId ≠ hr.toObjId := fun e => by rw [e, hRo] at hHo; cases hHo
  have hSR : hr.toObjId ≠ scId.toObjId := fun e => by rw [e, hScO] at hRo; cases hRo
  have hRp : ∀ (g : Reply → Reply), (∀ r, ({ g r with prev := none, next := none } : Reply) =
      { r with prev := none, next := none }) →
      ∀ o, popFieldsView (SystemState.mapReplyObject g o) = popFieldsView o := by
    intro g hg o; cases o <;> simp only [SystemState.mapReplyObject, popFieldsView, hg]
  unfold keepDonatedSchedContextInPlace
  simp only [hSc, hH, hR, hHt]
  generalize popOuterCode S r = k
  generalize (fun s : SchedContext => ({ s with scReply := r.prev } : SchedContext)) = f
  have h1 := updateSchedContext_noResizeDue S scId f hNo
  have hF1 := popFrame_updateSchedContext S scId f hNo
  have hS1R : (S.updateSchedContext scId f).objects[hr.toObjId]? = S.objects[hr.toObjId]? := by
    rw [SystemState.updateSchedContext_eq_impl]
    unfold SystemState.updateSchedContextImpl
    split
    · exact objects_modifyObject_ne _ _ _ hNo _ hSR
    · rfl
  generalize S.updateSchedContext scId f = s1 at h1 hF1 hS1R
  have h2 := modifyObject_noResizeDue s1 hr.toObjId
    (SystemState.mapReplyObject fun x => { x with prev := none, next := none }) h1
  have hF2 := (popFrame_modifyObject s1 hr.toObjId _ h1
    (hRp (fun x => { x with prev := none, next := none }) (fun _ => rfl))).trans hF1
  have hS2R : (s1.modifyObject hr.toObjId
      (SystemState.mapReplyObject fun x => { x with prev := none, next := none })).objects[hr.toObjId]? =
      some (.reply { r with prev := none, next := none }) := by
    rw [objects_modifyObject_self _ _ _ h1, hS1R, hRo]; rfl
  generalize s1.modifyObject hr.toObjId
    (SystemState.mapReplyObject fun x => { x with prev := none, next := none }) = s2 at h2 hF2 hS2R
  cases hp : r.prev with
  | none => exact heldPopTail_exact S s2 holder hr r ht _ _ h2 hF2 hS2R hHR hHo
  | some b =>
    refine heldPopTail_exact S _ holder hr r ht _ _ (modifyObject_noResizeDue _ _ _ h2)
      ((popFrame_modifyObject _ _ _ h2
        (hRp (fun x => { x with next := r.next }) (fun _ => rfl))).trans hF2) ?_ hHR hHo
    rw [objects_modifyObject_ne _ _ _ h2 _
      (fun e => hb b hp (SeLe4n.ReplyId.toObjId_injective _ _ e).symm), hS2R]

end HeldPopFrame

section HeldPopSpec

/-- **The reply's held pop, in place**: on a state where the answered reply
heads the stack of a context `holder` holds, the frame below (if any) links up
to it with a caller, that caller holds a context of its own, and
every check of the held pop passes, the reply's donation step returns
`keepDonatedSchedContextInPlace`'s state: the holder keeps the context and
stays where it runs. -/
theorem applyReplyDonationOnCore_eq_held (S : SystemState) (rid : SeLe4n.ReplyId)
    (cv : SeLe4n.ValidThreadId) (c holder : SeLe4n.ThreadId) (hcv : cv.val = c)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (r : Reply) (ht : TCB)
    (hR : S.getReply? rid = some r) (hNext : r.next = some (.head scId))
    (hSc : S.getSchedContext? scId = some sc) (hHead : sc.scReply = some rid)
    (hB : sc.boundThread = some holder)
    (hBelow : ∀ b, r.prev = some b → b ≠ rid ∧ (∃ bR, S.getReply? b = some bR ∧
      bR.next = some (.frame rid) ∧ bR.callerCode ≠ 0) ∧
      storeLeavesIndexAndTypes S b.toObjId .reply = true ∧
      S.objects.findsInPlace b.toObjId = true)
    (hOuter : outerCallerAcceptable S holder holder
      (heldPopOuter? S holder (SeLe4n.ThreadId.ofOptCode (popOuterCode S r))) = true)
    (hRecip : donationRecipientAcceptable S c = false)
    (hHRes : holder.isReserved = false) (hHT : S.getTcb? holder = some ht)
    (hHB : ht.scBindingScCode = scId.val + 1)
    (hLsc : storeLeavesIndexAndTypes S scId.toObjId .schedContext = true)
    (hFsc : S.objects.findsInPlace scId.toObjId = true)
    (hLr : storeLeavesIndexAndTypes S rid.toObjId .reply = true)
    (hFr : S.objects.findsInPlace rid.toObjId = true)
    (hLh : storeLeavesIndexAndTypes S holder.toObjId .tcb = true) (home : CoreId) :
    applyReplyDonationOnCore S rid cv home = .ok (keepDonatedSchedContextInPlace S holder scId) := by
  have hHolder : replyFrameHeadHolder? S rid = some (scId, holder) := by
    apply replyFrameHeadHolder?_of_head
    · unfold replyFrameHeadContext?
      rw [hR]
      simp only [hNext, hSc, hHead, beq_self_eq_true, ↓reduceIte]
    · rw [hSc]; exact hB
  obtain ⟨hv, hhv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff holder).mpr hHRes)
  have hhv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hhv
  unfold applyReplyDonationOnCore
  rw [hHolder]
  simp only [hhv, hcv, hRecip, Bool.false_eq_true, ↓reduceIte]
  rw [hhv', keepDonatedSchedContextResolved_eq_inPlace S holder scId sc rid r ht hSc hB hHead
    hR hNext hBelow hOuter hHRes hHT hHB hLsc hFsc hLr hFr hLh]

/-- **The reply-receive's held pop, in place**: on the states of
`applyReplyDonationOnCore_eq_held`, the reply-receive's pop hands back no
context and returns `keepDonatedSchedContextInPlace`'s state. -/
theorem replyRecvPopDonation_eq_held (S : SystemState) (rid : SeLe4n.ReplyId)
    (c holder : SeLe4n.ThreadId) (hCRes : c.isReserved = false)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (r : Reply) (ht : TCB)
    (hR : S.getReply? rid = some r) (hNext : r.next = some (.head scId))
    (hSc : S.getSchedContext? scId = some sc) (hHead : sc.scReply = some rid)
    (hB : sc.boundThread = some holder)
    (hBelow : ∀ b, r.prev = some b → b ≠ rid ∧ (∃ bR, S.getReply? b = some bR ∧
      bR.next = some (.frame rid) ∧ bR.callerCode ≠ 0) ∧
      storeLeavesIndexAndTypes S b.toObjId .reply = true ∧
      S.objects.findsInPlace b.toObjId = true)
    (hOuter : outerCallerAcceptable S holder holder
      (heldPopOuter? S holder (SeLe4n.ThreadId.ofOptCode (popOuterCode S r))) = true)
    (hRecip : donationRecipientAcceptable S c = false)
    (hHRes : holder.isReserved = false) (hHT : S.getTcb? holder = some ht)
    (hHB : ht.scBindingScCode = scId.val + 1)
    (hLsc : storeLeavesIndexAndTypes S scId.toObjId .schedContext = true)
    (hFsc : S.objects.findsInPlace scId.toObjId = true)
    (hLr : storeLeavesIndexAndTypes S rid.toObjId .reply = true)
    (hFr : S.objects.findsInPlace rid.toObjId = true)
    (hLh : storeLeavesIndexAndTypes S holder.toObjId .tcb = true) :
    replyRecvPopDonation rid c S = .ok (none, keepDonatedSchedContextInPlace S holder scId) := by
  have hHolder : replyFrameHeadHolder? S rid = some (scId, holder) := by
    apply replyFrameHeadHolder?_of_head
    · unfold replyFrameHeadContext?
      rw [hR]
      simp only [hNext, hSc, hHead, beq_self_eq_true, ↓reduceIte]
    · rw [hSc]; exact hB
  obtain ⟨hv, hhv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff holder).mpr hHRes)
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  unfold replyRecvPopDonation
  rw [hHolder]
  simp only [hhv, hcv, hRecip, Bool.false_eq_true, ↓reduceIte]
  rw [keepDonatedSchedContextResolved_eq_inPlace S holder scId sc rid r ht hSc hB hHead
    hR hNext hBelow hOuter hHRes hHT hHB hLsc hFsc hLr hFr hLh]

end HeldPopSpec

section HeldReplyGate

/-- **A reply whose held pop may write in place**, read on the pre-state: the
answered caller `c` (an unreserved thread holding a context of its own, code
`cBinding`) and the server distinct, the caller's and its reply object's slots
local, the reply object heading the stack of a context whose held pop by the
server passes its checks (`keptPopsInPlace`), the context naming the reply
back, and the frame below
(if any) names a caller other than `c`, whose state the reply leg rewrites.
Every read is a code, so the test builds nothing. -/
@[inline] def replyHeldPopsInPlace (st : SystemState) (c : SeLe4n.ThreadId) (cBinding : Nat)
    (server : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  !c.isReserved && c.val != server.val && cBinding != 0 &&
  storeLeavesIndexAndTypes st c.toObjId .tcb &&
  st.objects.findsInPlace c.toObjId &&
  storeLeavesIndexAndTypes st rid.toObjId .reply &&
  st.objects.findsInPlace rid.toObjId &&
  (match st.getReply? rid with
   | some rp =>
     match rp.next with
     | some (.head scId) =>
       (match st.getSchedContext? scId with
        | some sc =>
          (match sc.scReply with
           | some h => h.val == rid.val
           | none => false)
        | none => false) &&
       popOuterCode st rp != c.val + 1 &&
       keptPopsInPlace st server scId
     | _ => false
   | none => false)

/-- **The gate carries the held pop across the reply leg**: under
`replyHeldPopsInPlace` the reply object heads the stack of context `scId` (the
code the arm reads), held by `server`, and on the state the reply leg leaves (its
writes, the caller holding message `msg`) the reply's donation step and the
reply-receive's pop are the held pop in place. -/
theorem replyHeldPopsInPlace_pop (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hG : replyHeldPopsInPlace st c ct.scBindingScCode server rid = true) :
    ∃ rp scId sc st0, st.objects[rid.toObjId]? = some (.reply rp) ∧ rp.next = some (.head scId) ∧
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧ sc.scReply = some rid ∧
      (∀ b, rp.prev = some b → b ≠ rid) ∧
      replyHeadContextCode st rid = scId.val + 1 ∧
      c.isReserved = false ∧ server.isReserved = false ∧ c ≠ server ∧ st.objects.noResizeDue ∧
      st.objects[server.toObjId]? = some (.tcb st0) ∧ st0.scBindingScCode = scId.val + 1 ∧
      storeLeavesIndexAndTypes st c.toObjId .tcb = true ∧
      st.objects.findsInPlace c.toObjId = true ∧
      storeLeavesIndexAndTypes st rid.toObjId .reply = true ∧
      st.objects.findsInPlace rid.toObjId = true ∧
      (∀ (cv : SeLe4n.ValidThreadId) (home : CoreId), cv.val = c →
        applyReplyDonationOnCore
            ((storeReplyRendezvousReady st c server rid).mapTcbInPlace c (holdMessage msg)) rid cv
            home =
          .ok (keepDonatedSchedContextInPlace
            ((storeReplyRendezvousReady st c server rid).mapTcbInPlace c (holdMessage msg))
            server scId)) ∧
      replyRecvPopDonation rid c
          ((storeReplyRendezvousReady st c server rid).mapTcbInPlace c (holdMessage msg)) =
        .ok (none, keepDonatedSchedContextInPlace
          ((storeReplyRendezvousReady st c server rid).mapTcbInPlace c (holdMessage msg))
          server scId) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  unfold replyHeldPopsInPlace at hG
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨⟨⟨hCRes, hNeV⟩, hCB⟩, hLC⟩, hFC⟩, hLR⟩, hFR⟩, hM⟩ := hG
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFC
  have hNe : c ≠ server := fun e => by subst e; simp at hNeV
  cases hRg : st.getReply? rid with
  | none => rw [hRg] at hM; cases hM
  | some rp =>
  rw [hRg] at hM
  dsimp only at hM
  have hRp : st.objects[rid.toObjId]? = some (.reply rp) :=
    (SystemState.getReply?_eq_some_iff _ _ _).mp hRg
  cases hN : rp.next with
  | none => rw [hN] at hM; cases hM
  | some l =>
  cases l with
  | frame _ => rw [hN] at hM; cases hM
  | head scId =>
  rw [hN] at hM
  dsimp only at hM
  simp only [Bool.and_eq_true] at hM
  obtain ⟨⟨hScM, hOutNe⟩, hKept⟩ := hM
  obtain ⟨sc, rid', rp', ht, hScg, hB, hHd', hR', hN', hBelow', hOuterC, hSRes, hHT0, hHB, hLsc, hFsc,
    _, _, hLS⟩ := keptPopsInPlace_spec st server scId hKept
  rw [hScg] at hScM
  dsimp only at hScM
  have hHd := hScM
  have hHead : sc.scReply = some rid := by
    revert hHd
    cases sc.scReply with
    | none => intro h; cases h
    | some h =>
      intro e
      have : h = rid := by cases h; cases rid; simp only [beq_iff_eq] at e; subst e; rfl
      rw [this]
  rw [hHead] at hHd'
  cases hHd'
  rw [hRg] at hR'
  cases hR'
  have hScO : st.objects[scId.toObjId]? = some (.schedContext sc) :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hScg
  have hSrvO : st.objects[server.toObjId]? = some (.tcb ht) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hHT0
  refine ⟨rp, scId, sc, ht, hRp, hN, hScO, hHead, fun b hb => (hBelow' b hb).1,
    by simp only [replyHeadContextCode, hRg, hN], hCRes, hSRes, hNe, hNo, hSrvO, hHB, hLC, hFC,
    hLR, hFR, ?_⟩
  -- The state after the reply leg, against the pre-state.
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  generalize hS1 : storeReplyRendezvousReady st c server rid = S1
  have hAg := fun x hx hy => hS1 ▸ storeReplyRendezvousReady_agree st c server rid ct hNo hTc hFC x hx hy
  have hHold : ∀ x, x ≠ c.toObjId →
      (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = S1.objects[x]? := fun x hx => by
    rw [SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyRendezvousReady_keepsFinds st c server rid hNo hFC
  obtain ⟨tc1, htc1, hc1⟩ := hS1 ▸ storeReplyRendezvousReady_callerView st c server rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyRendezvousReady_reply st c server rid ct rp hNo hTc hFC hRp hRc
  generalize hTdef : S1.mapTcbInPlace c (holdMessage msg) = T
  have hTC : T.objects[c.toObjId]? = some (.tcb (holdMessage msg tc1)) := by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
  have hView : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (T.objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks := fun x hx hy => by
    rw [← hTdef, hHold _ hx]; exact hAg x hx hy
  have hTR : T.objects[rid.toObjId]? = some (.reply rp.consumed) := by
    rw [← hTdef, hHold _ hRc]; exact hR1
  have hV : ∀ x, T.getObjectType? x = st.getObjectType? x := by
    intro x
    by_cases hxc : x = c.toObjId
    · subst hxc; unfold SystemState.getObjectType?; rw [hTC, hT]; rfl
    · by_cases hxr : x = rid.toObjId
      · subst hxr; unfold SystemState.getObjectType?; rw [hTR, hRp]; rfl
      · exact getObjectType?_of_view (hView x hxc hxr)
  have hLT : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes T id ty = true := fun h => storeLeavesIndexAndTypes_of_frame hV h
  have hFT : ∀ k, T.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
    rw [← hTdef]; exact ((SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK) k
  have hRT : T.getReply? rid = some rp.consumed := (SystemState.getReply?_eq_some_iff _ _ _).mpr hTR
  have hNextC : rp.consumed.next = some (.head scId) := by simp only [Reply.consumed, hN]
  have hPrevC : rp.consumed.prev = rp.prev := by simp only [Reply.consumed, hN]
  have hScC : scId.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hScO; cases hScO
  have hScR : scId.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hScO; cases hScO
  have hScT : T.getSchedContext? scId = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hScC hScR) (fun _ e => by cases e) hScO)
  have hSC : server.toObjId ≠ c.toObjId :=
    fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have hSR : server.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hSrvO; cases hSrvO
  obtain ⟨htT, hHTo, ehT⟩ := agreeAt_tcb (hView _ hSC hSR) hSrvO
  have hHT : T.getTcb? server = some htT := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hHTo
  have hHBT : htT.scBindingScCode = scId.val + 1 := by
    have h := congrArg TCB.scBindingScCode ehT; exact h.trans hHB
  have hOT : T.getTcb? c = some (holdMessage msg tc1) := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC
  -- The frame below, as the pre-state had it.
  have hBelowRead : ∀ b, rp.prev = some b → T.getReply? b = st.getReply? b := by
    intro b hb
    obtain ⟨hbr, ⟨bR, hBg, _, _⟩, _, _⟩ := hBelow' b hb
    have hBO : st.objects[b.toObjId]? = some (.reply bR) :=
      (SystemState.getReply?_eq_some_iff _ _ _).mp hBg
    have hbc : b.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hBO; cases hBO
    have hbr' : b.toObjId ≠ rid.toObjId := fun e => hbr (SeLe4n.ReplyId.toObjId_injective _ _ e)
    rw [hBg]
    exact (SystemState.getReply?_eq_some_iff _ _ _).mpr
      (agreeAt_of_not_tcb (hView _ hbc hbr') (fun _ e => by cases e) hBO)
  have hBelowT : ∀ b, rp.consumed.prev = some b → b ≠ rid ∧ (∃ bR, T.getReply? b = some bR ∧
      bR.next = some (.frame rid) ∧ bR.callerCode ≠ 0) ∧
      storeLeavesIndexAndTypes T b.toObjId .reply = true ∧
      T.objects.findsInPlace b.toObjId = true := by
    intro b hb
    rw [hPrevC] at hb
    obtain ⟨hbr, ⟨bR, hBg, hBN, hBC⟩, hLb, hFb⟩ := hBelow' b hb
    exact ⟨hbr, ⟨bR, (hBelowRead b hb).trans hBg, hBN, hBC⟩, hLT hLb, (hFT _).trans hFb⟩
  have hPopT : popOuterCode T rp.consumed = popOuterCode st rp := by
    unfold popOuterCode
    rw [hPrevC]
    cases hP : rp.prev with
    | none => rfl
    | some b => dsimp only; rw [hBelowRead b hP]
  have hOwnT : htT.scBindingOwnerCode = ht.scBindingOwnerCode := by
    have h := congrArg TCB.scBindingOwnerCode ehT; exact h
  have hOuter : outerCallerAcceptable T server server
      (heldPopOuter? T server (SeLe4n.ThreadId.ofOptCode (popOuterCode T rp.consumed))) = true := by
    have hBindT : htT.schedContextBinding =
        SchedContextBinding.ofCodes (scId.val + 1) htT.scBindingOwnerCode := by
      unfold TCB.schedContextBinding; rw [hHBT]
    rw [heldPopOuter?_of_getTcb hHT, hBindT, heldPopOwner?_ofCodes, ← outerCallerAcceptableCode_eq,
      hPopT, hOwnT]
    -- The pop records the stack's answer only on a holder on loan; a holder that
    -- owns the context checks the bottom answer, which passes.
    have hOutNe' : (heldPopOwnerCode ht.scBindingOwnerCode (popOuterCode st rp) != c.val + 1)
        = true := by
      unfold heldPopOwnerCode; split
      · simp
      · exact hOutNe
    generalize heldPopOwnerCode ht.scBindingOwnerCode (popOuterCode st rp) = k at hOuterC hOutNe' ⊢
    have hk := hOuterC
    have hkc := hOutNe'
    cases k with
    | zero => rfl
    | succ o =>
      simp only [outerCallerAcceptableCode, Bool.and_eq_true] at hk ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hk
      refine ⟨⟨h1, h2⟩, ?_⟩
      have hoc : (⟨o⟩ : SeLe4n.ThreadId).toObjId ≠ c.toObjId := fun e => by
        have := SeLe4n.ThreadId.toObjId_injective _ _ e
        rw [← this] at hkc; simp at hkc
      have hor : (⟨o⟩ : SeLe4n.ThreadId).toObjId ≠ rid.toObjId := fun e => by
        unfold outerTestAt at h3
        rw [(show st.getTcb? ⟨o⟩ = none from by
          unfold SystemState.getTcb?; rw [e, hRp])] at h3
        cases h3
      rw [outerTestAt_of_view (hView _ hoc hor)]; exact h3
  have hRecip : donationRecipientAcceptable T c = false := by
    have e : tc1.scBindingScCode = ct.scBindingScCode := by
      have h := congrArg TCB.scBindingScCode hc1; exact h
    have hLk : lookupTcb T c = some (holdMessage msg tc1) := by
      unfold lookupTcb; rw [hCRes]; exact hOT
    rw [donationRecipientAcceptable_eq_of_some T c _ hLk, TCB.schedContextBinding_beq_unbound]
    show (tc1.scBindingScCode == 0) = false
    rw [e]; simpa only [bne_iff_ne, ne_eq, beq_eq_false_iff_ne] using hCB
  exact ⟨fun cv home hcv => applyReplyDonationOnCore_eq_held T rid cv c server hcv scId sc rp.consumed
    htT hRT hNextC hScT hHead hB hBelowT hOuter hRecip hSRes hHT hHBT
    (hLT hLsc) ((hFT _).trans hFsc) (hLT hLR) ((hFT _).trans hFR) (hLT hLS) home,
    replyRecvPopDonation_eq_held T rid c server hCRes scId sc rp.consumed htT hRT hNextC hScT hHead hB
    hBelowT hOuter hRecip hSRes hHT hHBT
    (hLT hLsc) ((hFT _).trans hFsc) (hLT hLR) ((hFT _).trans hFR) (hLT hLS)⟩

end HeldReplyGate

section HeldReplyDelivered

/-- **The held reply, delivered**: the caller woken without the message, the
head popped off the context the server keeps (`keepDonatedSchedContextInPlace`),
the server's priority walk, then the reply's frame written into the caller's
saved registers.  The server stays where it runs. -/
@[noinline] def performReplyHeldDelivered (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : CoreId) : SystemState :=
  let X := (PriorityInheritance.propagatePipChainCrossCore
    (keepDonatedSchedContextInPlace (storeReplyRendezvousReady st c server rid) server scId)
    server core).1
  writeDeliveredFrameIfReady X c (Architecture.regMessageFrameW layout rf len badgeWord badged)
    (fun _ => holdDeliveredBody X c layout rf len (SeLe4n.Badge.opt badgeWord badged))

/-- **The checked held reply, in place**: under the flow gate and
`replyHeldPopsInPlace`, a reply of at most four words to an unfaulted caller
blocked on it, holding a context of its own, whose reply object heads the stack
of the context the server holds, commits `performReplyHeldDelivered`'s state,
its context the one the reply object heads (`replyHeadContextCode`), read on
the pre-state. -/
theorem replyTransferChecked_held_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : CoreId) (msg : IpcMessage)
    (grant : Bool)
    (hMsg : msg =
      { registers := Architecture.regMessageBody layout rf len, badge := SeLe4n.Badge.opt badgeWord badged })
    (hSz : ¬ Architecture.regMessageLength layout len > maxMessageRegisters)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hG : replyHeldPopsInPlace st c ct.scBindingScCode server rid = true)
    (hNoF : ct.faultWords.isFault = false)
    (hX : replyTransferInert st replier ct grant = true)
    (hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf c) = true) :
    replyTransferOnCoreChecked ctx replier c mi regs msg grant core st =
      .ok ((), performReplyHeldDelivered st c server rid ⟨replyHeadContextCode st rid - 1⟩
        layout rf len badgeWord badged core) := by
  replace hMsg := hMsg.symm
  obtain ⟨rp, scId, _, _, hRp, hN, _, _, _, hCode, hCRes, hSRes, hNe, hNo, _, _, hLC, hFC, hLR, hFR,
    hDon, _⟩ := replyHeldPopsInPlace_pop st c server rid msg ct hT hG
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  have hSz' : ¬ msg.registers.size > maxMessageRegisters := by
    rw [← hMsg, Architecture.regMessageBody_size]; exact hSz
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st replier c server ct ep rid rp msg core hSz' hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hPF : ct.pendingFault = none := TCB.pendingFault_eq_none_of_not_isFault hNoF
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNF : threadHasPendingFault st c = false := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_none]
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff server).mpr hSRes)
  have hRec : recordedReplyServer? st c = some server := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hAns : answeredReplyObject? st c = some rid := by
    simp only [answeredReplyObject?, hTc, Option.bind_some, hRO]
  have hNoS := storeReplyRendezvousReady_noResizeDue st c server rid hNo
  have hNoP := keepDonatedSchedContextInPlace_noResizeDue _ server scId hNoS
  unfold replyTransferOnCoreChecked
  rw [hNF, endpointReplyCrossCoreDispatchChecked_flow_allowed _ _ _ _ _ _ hFlow]
  simp only [Bool.false_eq_true, ↓reduceIte,
    replyTransferCaps_of_inert st replier c grant ct hTc hX, CapTransferSummary.capInfo_empty]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hsv, hAns, hcv]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    hDon cv _ (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  unfold performReplyHeldDelivered
  subst hMsg
  rw [keepDonatedSchedContextInPlace_msg c id _ id _ server scId hNoS hNe,
    Architecture.regMessageFrameW_eq, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoP,
    stageDeliveredMessage_holdMessage _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ hNoP)
      (by rw [Architecture.regMessageBody_size]; exact hSz4),
    Architecture.returnFrameOfMessage_regMessageBody]
  rfl

end HeldReplyDelivered

section HeldReplyRecvGuard

/-- **A held reply-receive that may block in place**, read on the pre-state:
the caller blocked on a reply from the receiver through reply object `rid`, the
held pop's checks (`replyHeldPopsInPlace`), no sender waiting on the endpoint,
the receiver an unreserved thread that owns the context it holds (so the held
pop leaves it `.bound` and it may block) and whose block writes in place, and
its reply object not stashed and in its slot for the stasher record.  Every
read is a code. -/
@[inline] def replyRecvHeldBlocks (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ (some server) => server.val == tid.val
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1 &&
       replyHeldPopsInPlace st c ct.scBindingScCode tid rid
   | none => false) &&
  !tid.isReserved &&
  (match st.getEndpoint? epId with
   | some ep =>
       ep.sendQ.head.isNone &&
       (match st.getTcb? tid with
        | some rt => rt.scBindingOwnerCode == 0 && enqueueAdmits rt &&
            enqueuesInPlaceCode st epId tid ep.recvTailCode
        | none => false)
   | none => false) &&
  (match st.getReply? rid with
   | some rp => !st.replyStashedAt rid rp && replyRecordsInPlace st (rid.val + 1)
   | none => false)

theorem replyRecvHeldBlocks_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvHeldBlocks st epId tid c rid = true) :
    ∃ (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply),
      st.objects[c.toObjId]? = some (.tcb ct) ∧
      ct.ipcState = .blockedOnReply ep0 (some tid) ∧ ct.replyObject = some rid ∧
      replyHeldPopsInPlace st c ct.scBindingScCode tid rid = true ∧ tid.isReserved = false ∧
      st.objects[epId]? = some (.endpoint ep) ∧ ep.sendQ.head = none ∧
      st.objects[tid.toObjId]? = some (.tcb rt) ∧ rt.scBindingOwnerCode = 0 ∧
      enqueueAdmits rt = true ∧
      enqueuesInPlace st epId tid ep.receiveQ.tail = true ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧
      st.replyStashedAt rid rp = false ∧ replyRecordsInPlace st (rid.val + 1) = true := by
  unfold replyRecvHeldBlocks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hC, hSRes⟩, hE⟩, hRp⟩ := h
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
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hE
  obtain ⟨hS, hT⟩ := hE
  cases hTt : st.getTcb? tid with
  | none => rw [hTt] at hT; cases hT
  | some rt =>
  rw [hTt] at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨⟨hOwn, hA⟩, hEnq⟩ := hT
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRp; cases hRp
  | some rp =>
  rw [hR] at hRp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hRp
  obtain ⟨hStash, hRecR⟩ := hRp
  refine ⟨ct, ep0, rt, ep, rp, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hW,
    hSRes, (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp, hS,
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hTt, beq_iff_eq.mp hOwn, hA, ?_,
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR, hStash, hRecR⟩
  · simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
  · rw [enqueuesInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode] at hEnq; exact hEnq

/-- **The held pop carries the receive's guard**: on the state a held reply
leg and its pop leave, the endpoint is as it was, the server (still `.bound` to
the context it owns) may block on it and its block writes in place, each read
on the pre-state. -/
theorem keepHeldPop_receiveGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (rt : TCB) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) (hNext : rp.next = some (.head scId))
    (hScO : st.objects[scId.toObjId]? = some (.schedContext sc)) (hHead : sc.scReply = some rid)
    (hBelow : ∀ b, rp.prev = some b → b ≠ rid)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hOwn : rt.scBindingOwnerCode = 0)
    (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid scId).objects[epId]? =
        some (.endpoint ep) ∧
      (∃ rt1, (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid scId).objects[tid.toObjId]? = some (.tcb rt1) ∧ receiveBlockAdmits rt1 = true ∧
          rt1.boundNotificationCode = rt.boundNotificationCode) ∧
      receiveBlocksInPlace (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg)
        tid scId) epId tid ep.receiveQ.tail (some rid) = true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hR; cases hR
  have hSc' : scId.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hScO; cases hScO
  have hSr : scId.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hScO; cases hScO
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]
  generalize hS1 : storeReplyRendezvousReady st c tid rid = S1
  have hAg := fun x hx hy => hS1 ▸ storeReplyRendezvousReady_agree st c tid rid ct hNo hTc hFC x hx hy
  have hNo1 : S1.objects.noResizeDue := hS1 ▸ storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyRendezvousReady_keepsFinds st c tid rid hNo hFC
  obtain ⟨tc1, htc1, hc1⟩ := hS1 ▸ storeReplyRendezvousReady_caller st c tid rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyRendezvousReady_reply st c tid rid ct rp hNo hTc hFC hRp hRc
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
  obtain ⟨rtT, hRtT, eRtT⟩ := agreeAt_tcb (hView _ hTc' hTr) hR
  have hHeadC : rp.consumed = { rp with callerCode := 0 } := Reply.consumed_of_head rp scId hNext
  obtain ⟨⟨t, hPt', hB0, hB1, _⟩, hPr'⟩ := keepDonatedSchedContextInPlace_exact T tid scId sc rid
    rp.consumed rtT hNoT hScT hHead ((SystemState.getReply?_eq_some_iff _ _ _).mpr hTR)
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRtT)
    (fun b hb => hBelow b (by rw [hHeadC] at hb; exact hb))
  have hF := keepDonatedSchedContextInPlace_popFrame T tid scId hNoT
  have hOwnT : rtT.scBindingOwnerCode = 0 := by
    have h := congrArg TCB.scBindingOwnerCode eRtT; exact h.trans hOwn
  rw [hOwnT] at hB1
  generalize keepDonatedSchedContextInPlace T tid scId = P at hPt' hPr' hF
  have hComb : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (P.objects[x]?).map popFieldsView = (st.objects[x]?).map popFieldsView :=
    fun x hx hy => (hF.2.2.2 x).trans (popAgreeAt_of_runLinks (hView x hx hy))
  obtain ⟨tcP, hPC, ecP⟩ := popAgreeAt_tcb (hF.2.2.2 c.toObjId) hTC
  refine ⟨popAgreeAt_endpoint (hComb _ hEc hEr) hE, ⟨t, hPt', ?_, ?_⟩, ?_⟩
  · obtain ⟨t', h', e'⟩ := popAgreeAt_tcb (hComb _ hTc' hTr) hR
    rw [hPt'] at h'
    cases h'
    unfold receiveBlockAdmits
    rw [← enqueueAdmits_popView t, e', enqueueAdmits_popView, hA]
    have hU : t.schedContextBinding = .bound scId := by
      unfold TCB.schedContextBinding SchedContextBinding.ofCodes
      rw [hB0, hB1]; rfl
    rw [hU]
    rfl
  · obtain ⟨t', h', e'⟩ := popAgreeAt_tcb (hComb _ hTc' hTr) hR
    rw [hPt'] at h'
    cases h'
    have := congrArg TCB.boundNotificationCode e'
    exact this
  · unfold receiveBlocksInPlace
    have hKP : P.objectsKeepFinds st := hF.2.2.1.trans hKT
    have hV : ∀ x, P.getObjectType? x = st.getObjectType? x := by
      intro x
      by_cases hxc : x = c.toObjId
      · subst hxc; unfold SystemState.getObjectType?
        rw [hPC, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc]; rfl
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


end HeldReplyRecvGuard

section HeldReplyRecv

theorem replyRecvAnsweringOnCore_held_inPlace
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyHeldPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hOwn : rt.scBindingOwnerCode = 0)
    (hA : enqueueAdmits rt = true)
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
            (receiveReturnSchedContext true
              (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
                ⟨replyHeadContextCode st rid - 1⟩) tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c 0) ∧
      ∃ x, (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true
              (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
                ⟨replyHeadContextCode st rid - 1⟩) tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core).getTcb? tid = some x ∧
        x.ipcState = .blockedOnReceive epId := by
  obtain ⟨rp', scId, sc, _, hRp', hN, hScO, hHead, hBelow, hCode, hCRes, _, hNe, hNo, _, _, hLC, hFC,
    hLR, hFR, _, hPop⟩ := replyHeldPopsInPlace_pop st c tid rid msg ct hT hG
  rw [hRp] at hRp'
  cases hRp'
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st tid c tid ct ep0 rid rp msg core hSz hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  obtain ⟨hE1, ⟨rt1, hR1, hA1, hB1⟩, hG1⟩ := keepHeldPop_receiveGuard st c tid rid msg ct rp
    epId ep rt scId sc hNo hT hFC hRp hN hScO hHead hBelow
    (fun e => hNe e.symm) hE hR hOwn hA hEnq hStash hRec
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hXf := replyRecvReplyTransfer_of_inert answer st tid c grant ct hTc hInert
  have hRecS : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hNoP := keepDonatedSchedContextInPlace_noResizeDue _ tid scId
    (storeReplyRendezvous_noResizeDue st c tid rid msg hNo)
  rw [← storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hPop
  generalize hS1 : storeReplyRendezvous st c tid rid msg = S1 at hEq hPop hE1 hR1 hG1 hNoP
  generalize hP : keepDonatedSchedContextInPlace S1 tid scId = P
    at hPop hE1 hR1 hG1 hNoP
  obtain ⟨hE2, ⟨rt2, hR2, hA2⟩, hG2⟩ := receiveReturnSchedContext_receiveGuard true P tid hNoP
    hE1 hR1 hA1 hG1
  generalize hQ : receiveReturnSchedContext true P tid = Q at hE2 hR2 hG2
  have hEp1 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE2
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
      (removeRunnableOnCore (storeReceiveBlock Q epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq Q epId ep tid rt2 (some rid) core hE2 hS hR2 hA2 hG2]
    have hSnd : (receiveRendezvousSender? Q epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [hSnd, ↓reduceIte]
  obtain ⟨tb, hTb, hBk⟩ := receiveBlock_receiver_blocked Q epId ep tid rt2 (some rid) core hE2 hR2
    hA2 hG2
  have hDq : rendezvousDequeuedCall (removeRunnableOnCore (storeReceiveBlock Q epId tid
      ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid = false := by
    unfold rendezvousDequeuedCall lookupTcb
    simp only [hSRes, Bool.false_eq_true, ↓reduceIte, hTb, hBk]
  refine ⟨?_, tb, hTb, hBk⟩
  unfold endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_some, hEq, hPop, hXf, hQ, hRecv, hEp1, Option.bind_some, hS]
  simp [replyRecvPostReceiveDonation, hDq, applyReceiveLegPipHandoff]

theorem replyRecvOnCore_held_inPlace (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyHeldPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hOwn : rt.scBindingOwnerCode = 0)
    (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : replyTransferInert st tid ct grant = true) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true
              (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
                ⟨replyHeadContextCode st rid - 1⟩) tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c 0) ∧
      ∃ x, (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true
              (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
                ⟨replyHeadContextCode st rid - 1⟩) tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core).getTcb? tid = some x ∧
        x.ipcState = .blockedOnReceive epId :=
  replyRecvAnsweringOnCore_held_inPlace none st epId tid c rid msg grant core ct ep0 rt ep rp hSz hT hIpc hRO hSRes hG hE hS hR hOwn hA hEnq
    hRp hStash hRec (fun _ => hInert)

end HeldReplyRecv

section HeldReplyRecvDelivered

/-- The held reply-receive that blocks, its caller woken holding no message:
the reply's writes, the held pop (the server keeps the context), the server's
context return on its bound notification (`receiveReturnSchedContextFast`), the
server's block on the endpoint, the server taken off its core, then its
priority walk. -/
@[noinline] def storeReplyRecvHeldReady (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (core : CoreId) : SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore
    (removeRunnableOnCore (storeReceiveBlock
      (receiveReturnSchedContextFast true
        (keepDonatedSchedContextInPlace (storeReplyRendezvousReady st c tid rid) tid scId) tid.val)
      epId tid tailCode (rid.val + 1)) tid core) tid core).1

/-- **The held reply-receive, delivered**: under the guard of
`replyRecvOnCore_held_inPlace` and a reply of at most four words, the checked
arm's result is the caller's frame written into its saved registers on top of
`storeReplyRecvHeldReady`; the server, blocked on the endpoint, stages
nothing. -/
theorem replyRecvOnCore_held_delivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters) (hSz4 : msg.registers.size ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyHeldPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hOwn : rt.scBindingOwnerCode = 0)
    (hA : enqueueAdmits rt = true)
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
        (storeReplyRecvHeldReady st c tid rid ⟨replyHeadContextCode st rid - 1⟩
          epId ep.recvTailCode core) c
        (Architecture.returnFrameOfMessage msg 0 0)
        (fun _ => (storeReplyRecvHeldReady st c tid rid ⟨replyHeadContextCode st rid - 1⟩
          epId ep.recvTailCode core).mapTcbInPlace c
          (holdMessage msg))) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hNe', hNo, _⟩ := replyHeldPopsInPlace_pop st c tid rid msg
    ct hT hG
  have hNe : tid ≠ c := fun e => hNe' e.symm
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvOnCore_held_inPlace st epId tid c rid msg grant core
    ct ep0 rt ep rp hSz hT hIpc hRO hSRes hG hE hS hR hOwn hA hEnq hRp hStash hRec hInert
  rw [hEq]
  simp only [CapTransferSummary.capInfo_empty]
  revert hX
  generalize (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId
  intro hX
  have h1 := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have h2' := keepDonatedSchedContextInPlace_noResizeDue _ tid scId h1
  have h2 := receiveReturnSchedContext_noResizeDue true _ tid h2'
  have h3 := storeReceiveBlock_noResizeDue _ epId tid ep.recvTailCode
    (SeLe4n.ReplyId.optCode (some rid)) h2
  have h4 := removeRunnableOnCore_noResizeDue _ tid core h3
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    keepDonatedSchedContextInPlace_msg c id _ id _ tid scId h1 (fun e => hNe e.symm),
    receiveReturnSchedContext_msg c id _ id true _ tid h2' hNe.symm,
    storeReceiveBlock_msg _ _ _ _ _ _ _ h2 hNe, removeRunnableOnCore_msg] at hX ⊢
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hX
  rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ h4,
    stageDeliveredMessage_holdMessage _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ h4) hSz4]
  obtain ⟨x2, hX2, e2⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h4 tid x hX
  rw [stageDeliveredMessage_writeDeliveredFrameIfReady_blocked _ c tid _ _ 0 hCT x2 hX2
    (by rw [e2, hB]; exact fun h => by cases h)]
  unfold storeReplyRecvHeldReady
  rw [receiveReturnSchedContextFast_eq]
  rfl

end HeldReplyRecvDelivered

/-- **The held reply-receive that blocks, delivered from the registers**:
`storeReplyRecvHeldReady`'s writes, then the reply's frame written into the
caller's saved registers.  The message is built only where the caller is,
unexpectedly, not ready. -/
@[noinline] def performReplyRecvHeldDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId) : SystemState :=
  let X := storeReplyRecvHeldReady st c tid rid scId epId tailCode core
  writeDeliveredFrameIfReady X c (Architecture.regMessageFrame layout rf len badge)
    (fun _ => holdReplyRecvBody X c layout rf len badge)

end SeLe4n.Kernel
