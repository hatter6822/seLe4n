/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.ReplyPopFrame
import SeLe4n.Kernel.IPC.Operations.HeldContextPopInPlace

/-!
# A reply to a caller holding a context of its own, each object written in its slot

seL4-MCS's `doReplyTransfer` on a reply whose frame heads the stack of the
context the server holds, the answered caller holding a context of its own: the
reply leg, then `reply_pop`'s held arm (the head popped off the context, which
stays with the server, `keepDonatedSchedContextInPlace`) and the server's
priority walk.  When every check of the reply leg and of the pop passes on the
pre-state (`replyHeldPopsInPlace`), each write lands in its slot and the result
is proven equal to the specification's (`replyTransferChecked_held_inPlace`).
The reply-receive's held arm is `ReplyRecvBlockComposed`'s.
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
    (hLh : storeLeavesIndexAndTypes S holder.toObjId .tcb = true) (home : CoreId)
    (keep : Bool := false) (core : CoreId := bootCoreId) :
    applyReplyDonationOnCore S rid cv home keep core =
      .ok (keepDonatedSchedContextInPlace S holder scId) := by
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
      (∀ (keep : Bool) (core : CoreId) (cv : SeLe4n.ValidThreadId) (home : CoreId), cv.val = c →
        applyReplyDonationOnCore
            ((storeReplyRendezvousReady st c server rid).mapTcbInPlace c (holdMessage msg)) rid cv
            home keep core =
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
  exact ⟨fun keep core cv home hcv => applyReplyDonationOnCore_eq_held T rid cv c server hcv scId sc
    rp.consumed htT hRT hNextC hScT hHead hB hBelowT hOuter hRecip hSRes hHT hHBT
    (hLT hLsc) ((hFT _).trans hFsc) (hLT hLR) ((hFT _).trans hFR) (hLT hLS) home keep core,
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
    (hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf c) = true)
    (keep : Bool := false) :
    replyTransferOnCoreChecked ctx replier c mi regs msg grant core st keep =
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
  rw [hNF, endpointReplyCrossCoreDispatchChecked_flow_allowed _ _ _ _ _ _ hFlow keep]
  simp only [Bool.false_eq_true, ↓reduceIte,
    replyTransferCaps_of_inert st replier c grant ct hTc hX, CapTransferSummary.capInfo_empty]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hsv, hAns, hcv]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    hDon keep core cv _ (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
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




end SeLe4n.Kernel
