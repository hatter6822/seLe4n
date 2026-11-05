/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDonatingInPlace
import SeLe4n.Kernel.IPC.Operations.DonationPopInPlace

/-!
# A donated reply, each object written in its slot

seL4-MCS's `doReplyTransfer` on a reply whose frame heads the stack of the
context the server holds on loan: the reply leg, then `reply_pop` (the context
handed back down the stack: to the caller one frame below, still owed it, as a
loan, or to its owner at the bottom), the context settled on its new holder's
home (`settleReturnedContext`, the tail of `schedContext_donate`) and the
server taken off its core.  When every check of the reply leg and of the pop
passes on the pre-state, each write lands in its slot
(`returnDonatedSchedContextInPlace`) and the result is proven equal to the
specification's (`replyTransferChecked_donated_inPlace`); a reply-receive's pop
runs the same writes between its reply leg and its receive leg.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section DonationPop

/-- **The in-place pop keeps the reply stacks well formed** wherever the
specification's pop does: on the states of
`returnDonatedSchedContextResolved_eq_inPlace` it is that pop's state. -/
theorem returnDonatedSchedContextInPlace_preserves_donationChainWellFormed (st : SystemState)
    (holder owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hr : SeLe4n.ReplyId) (r : Reply) (ot ht : TCB)
    (hSc : st.getSchedContext? scId = some sc) (hB : sc.boundThread = some holder)
    (hHead : sc.scReply = some hr) (hR : st.getReply? hr = some r)
    (hNext : r.next = some (.head scId))
    (hBelow : ∀ b, r.prev = some b → b ≠ hr ∧ (∃ bR, st.getReply? b = some bR ∧
      bR.next = some (.frame hr) ∧ bR.callerCode ≠ 0) ∧
      storeLeavesIndexAndTypes st b.toObjId .reply = true ∧
      st.objects.findsInPlace b.toObjId = true)
    (hOuter : outerCallerAcceptable st holder owner
      (SeLe4n.ThreadId.ofOptCode (popOuterCode st r)) = true)
    (hRecip : donationRecipientAcceptable st owner = true)
    (hORes : owner.isReserved = false) (hHRes : holder.isReserved = false)
    (hOT : st.getTcb? owner = some ot) (hHT : st.getTcb? holder = some ht)
    (hNeOH : owner ≠ holder)
    (hLsc : storeLeavesIndexAndTypes st scId.toObjId .schedContext = true)
    (hFsc : st.objects.findsInPlace scId.toObjId = true)
    (hLr : storeLeavesIndexAndTypes st hr.toObjId .reply = true)
    (hFr : st.objects.findsInPlace hr.toObjId = true)
    (hLo : storeLeavesIndexAndTypes st owner.toObjId .tcb = true)
    (hFo : st.objects.findsInPlace owner.toObjId = true)
    (hLh : storeLeavesIndexAndTypes st holder.toObjId .tcb = true)
    (hObjInv : st.objects.invExt)
    (hChainNone : ∀ sc, st.getSchedContext? scId = some sc →
      donationHeadOf? st scId sc = .ok none → donationChainWellFormed st)
    (hChainHead : ∀ sc rid r, st.getSchedContext? scId = some sc →
      donationHeadOf? st scId sc = .ok (some (rid, r)) → donationChainWellFormedExcept st rid) :
    donationChainWellFormed (returnDonatedSchedContextInPlace st holder owner scId) := by
  obtain ⟨newOwner?, _, h⟩ := returnDonatedSchedContextResolved_ok_decompose
    (returnDonatedSchedContextResolved_eq_inPlace st holder owner scId sc hr r ot ht hSc hB hHead
      hR hNext hBelow hOuter hRecip hORes hHRes hOT hHT hNeOH hLsc hFsc hLr hFr hLo hFo hLh)
  exact returnDonatedSchedContext_preserves_donationChainWellFormed_of_except st _ holder scId owner
    newOwner? hObjInv hChainNone hChainHead h

/-- The recipient of a pop is the answered caller wherever the context records
no origin other than it. -/
theorem replyDonationRecipient_eq_self (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (c : SeLe4n.ThreadId) (hSc : st.getSchedContext? scId = some sc)
    (hO : ∀ o, sc.donationOrigin = some o → o = c) :
    replyDonationRecipient st scId c = c := by
  cases h : donationOriginRecipient? st scId with
  | none => exact replyDonationRecipient_eq_of_no_origin st scId c h
  | some o =>
    rw [replyDonationRecipient_eq_origin st h]
    obtain ⟨sc', hSc', hO'⟩ := donationOriginRecipient?_eq_donationOrigin st h
    rw [hSc] at hSc'; cases hSc'
    exact hO o hO'

/-- And wherever a frame below names an outer caller, whatever origin the context
records: a pop above the bottom of the stack hands the context to the answered
caller (`replyDonationRecipient_eq_of_outer_some`). -/
theorem replyDonationRecipient_eq_self_of_head (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (c : SeLe4n.ThreadId) (hr : SeLe4n.ReplyId) (r : Reply)
    (hSc : st.getSchedContext? scId = some sc) (hHead : sc.scReply = some hr)
    (hR : st.getReply? hr = some r) (hNext : r.next = some (.head scId))
    (hBelow : ∀ b, r.prev = some b → ∃ bR, st.getReply? b = some bR ∧
      bR.next = some (.frame hr) ∧ bR.callerCode ≠ 0)
    (hO : r.prev = none → ∀ o, sc.donationOrigin = some o → o = c) :
    replyDonationRecipient st scId c = c := by
  cases hP : r.prev with
  | none => exact replyDonationRecipient_eq_self st scId sc c hSc (hO hP)
  | some b =>
    obtain ⟨_, hRes⟩ := replyStackOuterCaller?_of_head st scId sc hr r hSc hHead hR hNext hBelow
    obtain ⟨bR, hB, _, hBC⟩ := hBelow b hP
    have hPo : popOuterCode st r = bR.callerCode := by
      unfold popOuterCode; rw [hP]; simp only [hB]
    rw [hPo] at hRes
    cases hc : bR.callerCode with
    | zero => exact absurd hc hBC
    | succ k =>
      rw [hc] at hRes
      exact replyDonationRecipient_eq_of_outer_some st scId c ⟨k⟩ hRes

/-- **The reply's donation, in place**: on a state where the answered reply heads
the stack of a context its holder holds, the frame below (if any) links up to it
with a caller, the context at the bottom of the stack records no origin other
than the answered caller, and every check of the pop passes, the reply's donation step returns
`replyDonationPopInPlace`'s state. -/
theorem applyReplyDonationOnCore_eq_inPlace (S : SystemState) (rid : SeLe4n.ReplyId)
    (cv : SeLe4n.ValidThreadId) (c holder : SeLe4n.ThreadId) (hcv : cv.val = c)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (r : Reply) (ot ht : TCB)
    (hR : S.getReply? rid = some r) (hNext : r.next = some (.head scId))
    (hSc : S.getSchedContext? scId = some sc) (hHead : sc.scReply = some rid)
    (hB : sc.boundThread = some holder)
    (hOrig : r.prev = none → ∀ o, sc.donationOrigin = some o → o = c)
    (hBelow : ∀ b, r.prev = some b → b ≠ rid ∧ (∃ bR, S.getReply? b = some bR ∧
      bR.next = some (.frame rid) ∧ bR.callerCode ≠ 0) ∧
      storeLeavesIndexAndTypes S b.toObjId .reply = true ∧
      S.objects.findsInPlace b.toObjId = true)
    (hOuter : outerCallerAcceptable S holder c
      (SeLe4n.ThreadId.ofOptCode (popOuterCode S r)) = true)
    (hRecip : donationRecipientAcceptable S c = true)
    (hORes : c.isReserved = false) (hHRes : holder.isReserved = false)
    (hOT : S.getTcb? c = some ot) (hHT : S.getTcb? holder = some ht)
    (hNeOH : c ≠ holder)
    (hLsc : storeLeavesIndexAndTypes S scId.toObjId .schedContext = true)
    (hFsc : S.objects.findsInPlace scId.toObjId = true)
    (hLr : storeLeavesIndexAndTypes S rid.toObjId .reply = true)
    (hFr : S.objects.findsInPlace rid.toObjId = true)
    (hLo : storeLeavesIndexAndTypes S c.toObjId .tcb = true)
    (hFo : S.objects.findsInPlace c.toObjId = true)
    (hLh : storeLeavesIndexAndTypes S holder.toObjId .tcb = true) :
    applyReplyDonationOnCore S rid cv (replyDonationRecipientHome S rid c) =
      .ok (replyDonationPopInPlace S c holder scId (determineTargetCore S c)) := by
  have hHolder : replyFrameHeadHolder? S rid = some (scId, holder) := by
    apply replyFrameHeadHolder?_of_head
    · unfold replyFrameHeadContext?
      rw [hR]
      simp only [hNext, hSc, hHead, beq_self_eq_true, ↓reduceIte]
    · rw [hSc]; exact hB
  have hRecipEq := replyDonationRecipient_eq_self_of_head S scId sc c rid r hSc hHead hR hNext
    (fun b hb => (hBelow b hb).2.1) hOrig
  obtain ⟨hv, hhv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff holder).mpr hHRes)
  have hhv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hhv
  unfold applyReplyDonationOnCore
  rw [replyDonationRecipientHome_of_head S rid c scId holder hHolder, hHolder]
  simp only [hhv, hcv, hRecipEq]
  rw [hhv', returnDonatedSchedContextResolved_eq_inPlace S holder c scId sc rid r ot ht hSc hB hHead
    hR hNext hBelow hOuter hRecip hORes hHRes hOT hHT hNeOH hLsc hFsc hLr hFr hLo hFo hLh]
  rfl

/-- **The reply-receive's donation pop, in place**: on the states of
`applyReplyDonationOnCore_eq_inPlace`, the reply-receive's pop hands back the
context and its holder and returns `popDonationSettledInPlace`'s state. -/
theorem replyRecvPopDonation_eq_inPlace (S : SystemState) (rid : SeLe4n.ReplyId)
    (c holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (r : Reply) (ot ht : TCB)
    (hR : S.getReply? rid = some r) (hNext : r.next = some (.head scId))
    (hSc : S.getSchedContext? scId = some sc) (hHead : sc.scReply = some rid)
    (hB : sc.boundThread = some holder)
    (hOrig : r.prev = none → ∀ o, sc.donationOrigin = some o → o = c)
    (hBelow : ∀ b, r.prev = some b → b ≠ rid ∧ (∃ bR, S.getReply? b = some bR ∧
      bR.next = some (.frame rid) ∧ bR.callerCode ≠ 0) ∧
      storeLeavesIndexAndTypes S b.toObjId .reply = true ∧
      S.objects.findsInPlace b.toObjId = true)
    (hOuter : outerCallerAcceptable S holder c
      (SeLe4n.ThreadId.ofOptCode (popOuterCode S r)) = true)
    (hRecip : donationRecipientAcceptable S c = true)
    (hORes : c.isReserved = false) (hHRes : holder.isReserved = false)
    (hOT : S.getTcb? c = some ot) (hHT : S.getTcb? holder = some ht)
    (hNeOH : c ≠ holder)
    (hLsc : storeLeavesIndexAndTypes S scId.toObjId .schedContext = true)
    (hFsc : S.objects.findsInPlace scId.toObjId = true)
    (hLr : storeLeavesIndexAndTypes S rid.toObjId .reply = true)
    (hFr : S.objects.findsInPlace rid.toObjId = true)
    (hLo : storeLeavesIndexAndTypes S c.toObjId .tcb = true)
    (hFo : S.objects.findsInPlace c.toObjId = true)
    (hLh : storeLeavesIndexAndTypes S holder.toObjId .tcb = true) :
    replyRecvPopDonation rid c S =
      .ok (some (scId, holder), popDonationSettledInPlace S c holder scId (determineTargetCore S c)) := by
  have hHolder : replyFrameHeadHolder? S rid = some (scId, holder) := by
    apply replyFrameHeadHolder?_of_head
    · unfold replyFrameHeadContext?
      rw [hR]
      simp only [hNext, hSc, hHead, beq_self_eq_true, ↓reduceIte]
    · rw [hSc]; exact hB
  have hRecipEq := replyDonationRecipient_eq_self_of_head S scId sc c rid r hSc hHead hR hNext
    (fun b hb => (hBelow b hb).2.1) hOrig
  obtain ⟨hv, hhv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff holder).mpr hHRes)
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hORes)
  unfold replyRecvPopDonation
  rw [hHolder]
  simp only [hhv, hcv, hRecipEq]
  rw [returnDonatedSchedContextResolved_eq_inPlace S holder c scId sc rid r ot ht hSc hB hHead
    hR hNext hBelow hOuter hRecip hORes hHRes hOT hHT hNeOH hLsc hFsc hLr hFr hLo hFo hLh]
  rfl

/-- The pop leaves the table's size and capacity alone. -/
theorem returnDonatedSchedContextInPlace_noResizeDue (st : SystemState)
    (holder owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) :
    (returnDonatedSchedContextInPlace st holder owner scId).objects.noResizeDue := by
  unfold returnDonatedSchedContextInPlace
  split
  · exact hNo
  · split
    · exact hNo
    · split
      · exact hNo
      · split
        · exact hNo
        · split
          · exact hNo
          · dsimp only
            rw [markKeyChangeParts_objects, markCandidacyGainFor_objects, markKeyChangeParts_objects,
              markCandidacyGainFor_objects]
            refine updateTcb_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _ ?_)
            split <;> (repeat (first | exact hNo | apply modifyObject_noResizeDue |
              apply updateSchedContext_noResizeDue))

/-- **The pop commutes with a delivery** to a thread other than the holder. -/
theorem returnDonatedSchedContextInPlace_msg (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (st : SystemState) (holder owner : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hNo : st.objects.noResizeDue) (hH : r ≠ holder) :
    returnDonatedSchedContextInPlace (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) holder owner
        scId =
      (returnDonatedSchedContextInPlace st holder owner scId).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  have hPop : ∀ x : Reply, popOuterCode (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) x =
      popOuterCode st x := by
    intro x; unfold popOuterCode; simp only [SystemState.getReply?_mapTcbInPlace]
  unfold returnDonatedSchedContextInPlace
  simp only [SystemState.getSchedContext?_mapTcbInPlace, SystemState.getReply?_mapTcbInPlace,
    effectiveDeadline_msg, hasSufficientBudget_msg, hPop]
  have hTH : (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).getTcb? holder = st.getTcb? holder := by
    rw [SystemState.getTcb?_mapTcbInPlace, if_neg hH]
  rw [hTH]
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
        rcases getTcb?_msg_cases r ρ μ π st owner with h | ⟨_, h⟩ <;> rw [h] <;>
          cases st.getTcb? owner <;> (try simp only [Option.map_none]) <;>
          try (with_reducible rfl)
        all_goals
          cases st.getTcb? holder with
          | none => rfl
          | some ht =>
            try simp only [Option.map_some, TCB.withMessageSlots_boostedPriority,
              TCB.withMessageSlots_domain, effectiveDeadline_withMessageSlots,
              hasSufficientBudget_withMessageSlots]
            try dsimp only
            cases rr.prev with
            | none =>
              try dsimp only
              rw [updateSchedContext_msg r ρ μ π _ _ _ hNo,
                modifyObject_msg r ρ μ _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
                  (fun o => by cases o <;> rfl),
                updateTcb_msg r ρ μ π _ owner _ ?_ ?_,
                updateTcb_msg r ρ μ π _ holder _ ?_ (fun h => absurd h hH.symm),
                markCandidacyGainFor_msg, markKeyChangeParts_msg, markCandidacyGainFor_msg,
                markKeyChangeParts_msg]
              all_goals (repeat (first | exact hNo | with_reducible apply updateTcb_noResizeDue |
                with_reducible apply modifyObject_noResizeDue |
                with_reducible apply updateSchedContext_noResizeDue | (intro _ _; rfl)))
            | some b =>
              try dsimp only
              rw [updateSchedContext_msg r ρ μ π _ _ _ hNo,
                modifyObject_msg r ρ μ _ _ _ (updateSchedContext_noResizeDue _ _ _ hNo)
                  (fun o => by cases o <;> rfl),
                modifyObject_msg r ρ μ _ _ _ ?_ (fun o => by cases o <;> rfl),
                updateTcb_msg r ρ μ π _ owner _ ?_ ?_,
                updateTcb_msg r ρ μ π _ holder _ ?_ (fun h => absurd h hH.symm),
                markCandidacyGainFor_msg, markKeyChangeParts_msg, markCandidacyGainFor_msg,
                markKeyChangeParts_msg]
              all_goals (repeat (first | exact hNo | with_reducible apply updateTcb_noResizeDue |
                with_reducible apply modifyObject_noResizeDue |
                with_reducible apply updateSchedContext_noResizeDue | (intro _ _; rfl)))

section SettleMoves
variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat)

theorem releaseCoreOf_mapTcbInPlace (st : SystemState) (g : TCB → TCB) (s : SeLe4n.SchedContextId) :
    (st.mapTcbInPlace r g).releaseCoreOf s = st.releaseCoreOf s := by
  unfold SystemState.releaseCoreOf; rw [SystemState.getSchedContext?_mapTcbInPlace]

theorem releaseRemoveAnywhere_mapTcbInPlace (st : SystemState) (g : TCB → TCB)
    (s : SeLe4n.SchedContextId) :
    (st.mapTcbInPlace r g).releaseRemoveAnywhere s =
      (st.releaseRemoveAnywhere s).mapTcbInPlace r g := by
  unfold SystemState.releaseRemoveAnywhere
  rw [releaseCoreOf_mapTcbInPlace]
  split
  · exact releaseRemoveOn_mapTcbInPlace r g st _ s
  · rfl

theorem releasePlace_mapTcbInPlace (st : SystemState) (g : TCB → TCB) (c : CoreId)
    (s : SeLe4n.SchedContextId) :
    (st.mapTcbInPlace r g).releasePlace c s = (st.releasePlace c s).mapTcbInPlace r g := by
  have hF : (st.mapTcbInPlace r g).releaseFreeFor c s = st.releaseFreeFor c s := by
    unfold SystemState.releaseFreeFor; rw [releaseCoreOf_mapTcbInPlace]
  have hK : (st.mapTcbInPlace r g).releaseKeyOf s = st.releaseKeyOf s := by
    unfold SystemState.releaseKeyOf; rw [SystemState.getSchedContext?_mapTcbInPlace]
  unfold SystemState.releasePlace
  rw [hF, hK]
  split
  · split
    · rw [releaseRemoveOn_mapTcbInPlace, releaseInsertOn_mapTcbInPlace]
    · exact releaseRemoveOn_mapTcbInPlace r g st c s
  · rfl

theorem contextHolderActive_msg (st : SystemState) (s : SeLe4n.SchedContextId) :
    SchedContextOps.contextHolderActive (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) s =
      SchedContextOps.contextHolderActive st s := by
  unfold SchedContextOps.contextHolderActive SystemState.holderActive
  rw [SystemState.getSchedContext?_mapTcbInPlace]
  cases st.getSchedContext? s with
  | none => rfl
  | some sc =>
    simp only [Option.any_some]
    split
    · next t _ =>
      rcases getTcb?_msg_cases r ρ μ π st t with h | ⟨_, h⟩ <;> rw [h]
      cases st.getTcb? t <;> rfl
    · rfl

/-- **The settle commutes with a delivery**: it writes release links and reads a
holder's state, which a delivery leaves alone. -/
theorem settleReturnedContext_msg (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    SchedContextOps.settleReturnedContext (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c s =
      (SchedContextOps.settleReturnedContext st c s).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  unfold SchedContextOps.settleReturnedContext SchedContextOps.purgeReplenishment
  dsimp only
  rw [releaseRemoveAnywhere_mapTcbInPlace, contextHolderActive_msg]
  split
  · exact releasePlace_mapTcbInPlace r _ _ c s
  · rfl

theorem placedCoreOf?_msg (st : SystemState) (t : SeLe4n.ThreadId) :
    placedCoreOf? (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) t = placedCoreOf? st t := by
  unfold placedCoreOf?
  simp only [queuedOn_msg, SystemState.mapTcbInPlace_scheduler]

theorem descheduleAtPlacement_msg (st : SystemState) (t : SeLe4n.ThreadId) :
    descheduleAtPlacement (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) t =
      (descheduleAtPlacement st t).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold descheduleAtPlacement descheduleAt
  rw [placedCoreOf?_msg]
  split
  · exact removeRunnableOnCore_msg r ρ μ π st t _
  · rfl

end SettleMoves

/-- **The reply's donation pop commutes with a delivery** to a thread other than
the holder. -/
theorem popDonationSettledInPlace_msg (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (st : SystemState) (c holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (hNo : st.objects.noResizeDue)
    (hH : r ≠ holder) :
    popDonationSettledInPlace (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c holder scId home =
      (popDonationSettledInPlace st c holder scId home).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  unfold popDonationSettledInPlace
  rw [returnDonatedSchedContextInPlace_msg r ρ μ π st holder c scId hNo hH,
    settleReturnedContext_msg]

theorem replyDonationPopInPlace_msg (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (st : SystemState) (c holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (hNo : st.objects.noResizeDue)
    (hH : r ≠ holder) :
    replyDonationPopInPlace (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c holder scId home =
      (replyDonationPopInPlace st c holder scId home).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  unfold replyDonationPopInPlace
  rw [popDonationSettledInPlace_msg r ρ μ π st c holder scId home hNo hH, descheduleAtPlacement_msg]

theorem releaseRemoveOn_noResizeDue (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) : (st.releaseRemoveOn c s).objects.noResizeDue :=
  releaseUnlinkOn_noResizeDue _ _ _ hNo

theorem releaseInsertOn_noResizeDue (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) (hNo : st.objects.noResizeDue) : (st.releaseInsertOn c s t).objects.noResizeDue := by
  unfold SystemState.releaseInsertOn
  split
  · exact hNo
  · exact releaseLinkIn_noResizeDue _ _ _ _ hNo

/-- The settle leaves the table's size and capacity alone. -/
theorem settleReturnedContext_noResizeDue (st : SystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) (hNo : st.objects.noResizeDue) :
    (SchedContextOps.settleReturnedContext st c s).objects.noResizeDue := by
  have hP : (SchedContextOps.purgeReplenishment st s).objects.noResizeDue := by
    unfold SchedContextOps.purgeReplenishment SystemState.releaseRemoveAnywhere
    split
    · exact releaseRemoveOn_noResizeDue _ _ _ hNo
    · exact hNo
  unfold SchedContextOps.settleReturnedContext
  dsimp only
  split
  · unfold SystemState.releasePlace
    split
    · split
      · exact releaseInsertOn_noResizeDue _ _ _ _ (releaseRemoveOn_noResizeDue _ _ _ hP)
      · exact releaseRemoveOn_noResizeDue _ _ _ hP
    · exact hP
  · exact hP

/-- The pop and its settle leave the table's size and capacity alone. -/
theorem popDonationSettledInPlace_noResizeDue (st : SystemState) (c holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (hNo : st.objects.noResizeDue) :
    (popDonationSettledInPlace st c holder scId home).objects.noResizeDue :=
  settleReturnedContext_noResizeDue _ home scId
    (returnDonatedSchedContextInPlace_noResizeDue st holder c scId hNo)

/-- The reply's donation pop leaves the table's size and capacity alone. -/
theorem replyDonationPopInPlace_noResizeDue (st : SystemState) (c holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (hNo : st.objects.noResizeDue) :
    (replyDonationPopInPlace st c holder scId home).objects.noResizeDue := by
  have h := popDonationSettledInPlace_noResizeDue st c holder scId home hNo
  unfold replyDonationPopInPlace descheduleAtPlacement descheduleAt
  split
  · exact removeRunnableOnCore_noResizeDue _ _ _ h
  · exact h

end DonationPop

section DonatedReplyGate

/-- Objects that agree off their run-queue links agree on the outer caller's
test: it reads a binding and a state code, which no run-queue link holds. -/
theorem outerTestAt_of_view {s s' : SystemState} {x : SeLe4n.ThreadId}
    (h : (s'.objects[x.toObjId]?).map KernelObject.withoutRunLinks =
      (s.objects[x.toObjId]?).map KernelObject.withoutRunLinks) :
    outerTestAt s' x = outerTestAt s x := by
  unfold outerTestAt SystemState.getTcb?
  cases e : s.objects[x.toObjId]? with
  | none =>
    rw [e] at h
    cases e' : s'.objects[x.toObjId]? with
    | none => rfl
    | some _ => rw [e'] at h; cases h
  | some o =>
    cases o with
    | tcb t =>
      obtain ⟨t', h', e1⟩ := agreeAt_tcb h e
      rw [h']
      have a := congrArg TCB.ipcStateCode e1
      have b := congrArg TCB.scBindingScCode e1
      simp only [TCB.withoutRunLinks] at a b
      simp only [a, b]
    | _ =>
      rw [agreeAt_of_not_tcb h (fun _ e => by cases e) e]

/-- The answered caller after the reply's writes, off its run-queue links: woken
ready with its reply object released, every other field as it was. -/
theorem storeReplyRendezvousReady_callerView (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (ct : TCB) (hNo : st.objects.noResizeDue)
    (hT : st.getTcb? c = some ct) (hFC : st.objects.findsInPlace c.toObjId = true)
    (hNe : rid.toObjId ≠ c.toObjId) :
    ∃ t, (storeReplyRendezvousReady st c server rid).objects[c.toObjId]? = some (.tcb t) ∧
      t.withoutRunLinks = ({ receiverReady ct with replyObjectCode := 0 } : TCB).withoutRunLinks := by
  unfold storeReplyRendezvousReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  have hT1 : (st.updateTcb c receiverReady).getTcb? c = some (receiverReady ct) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.mapTcbInPlace_getTcb?_self, hT]
    rfl
  have hF1 : (st.updateTcb c receiverReady).objects.findsInPlace c.toObjId = true := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
    exact (SystemState.mapTcbInPlace_keepsFinds _ _ _ _).trans hFC
  have hA2 := enqueueRunnableOnCore_agree_of_findsInPlace _
    (determineTargetCore (st.updateTcb c receiverReady) c) c (receiverReady ct) hT1
      (by simp [receiverReady]) hF1
  obtain ⟨t2, h2, e2⟩ := hA2.get_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT1)
  have h3 : ((enqueueRunnableOnCore (st.updateTcb c receiverReady)
      (determineTargetCore (st.updateTcb c receiverReady) c) c).modifyObject rid.toObjId
        replyConsumedObject).getTcb? c = some t2 :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      (by rw [objects_modifyObject_ne _ _ _ hNo2 _ (fun e => hNe e.symm)]; exact h2)
  have h4 := SystemState.updateTcb_eq_mapTcbInPlace _ c (fun t => { t with replyObjectCode := 0 }) hNo3
  have h4' : (((enqueueRunnableOnCore (st.updateTcb c receiverReady)
      (determineTargetCore (st.updateTcb c receiverReady) c) c).modifyObject rid.toObjId
        replyConsumedObject).updateTcb c (fun t => { t with replyObjectCode := 0 })).objects[c.toObjId]?
        = some (.tcb { t2 with replyObjectCode := 0 }) := by
    rw [h4]
    exact (SystemState.getTcb?_eq_some_iff _ _ _).mp
      (by rw [SystemState.mapTcbInPlace_getTcb?_self, h3]; rfl)
  obtain ⟨t5, h5, e5⟩ := (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks _ c server).get_tcb h4'
  refine ⟨t5, h5, ?_⟩
  rw [e5]
  have hR : ∀ t : TCB, ({ t with replyObjectCode := 0 } : TCB).withoutRunLinks =
      { t.withoutRunLinks with replyObjectCode := 0 } := fun _ => rfl
  rw [hR, hR, e2]

/-- **The gate carries the pop across the reply leg**: under `replyPopsInPlace`
the reply object heads the stack of context `scId` (the code the arm reads), and
on the state the reply leg leaves (its writes, the caller holding message `msg`)
the reply's donation step is the in-place pop, settled on the caller's home core
read on the pre-state. -/
theorem replyPopsInPlace_donation (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB)
    (hT : st.objects[c.toObjId]? = some (.tcb ct)) (hSRes : server.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode server rid = true) :
    ∃ rp scId sc, st.objects[rid.toObjId]? = some (.reply rp) ∧ rp.next = some (.head scId) ∧
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧ sc.scReply = some rid ∧
      (∀ b, rp.prev = some b → b ≠ rid) ∧
      replyHeadContextCode st rid = scId.val + 1 ∧
      c.isReserved = false ∧ c ≠ server ∧ st.objects.noResizeDue ∧
      storeLeavesIndexAndTypes st c.toObjId .tcb = true ∧
      st.objects.findsInPlace c.toObjId = true ∧
      storeLeavesIndexAndTypes st rid.toObjId .reply = true ∧
      st.objects.findsInPlace rid.toObjId = true ∧
      (∀ cv : SeLe4n.ValidThreadId, cv.val = c →
        applyReplyDonationOnCore
            ((storeReplyRendezvousReady st c server rid).mapTcbInPlace c (holdMessage msg)) rid cv
            (replyDonationRecipientHome
              ((storeReplyRendezvousReady st c server rid).mapTcbInPlace c (holdMessage msg)) rid c) =
          .ok (replyDonationPopInPlace
            ((storeReplyRendezvousReady st c server rid).mapTcbInPlace c (holdMessage msg))
            c server scId (determineTargetCore st c))) ∧
      replyRecvPopDonation rid c
          ((storeReplyRendezvousReady st c server rid).mapTcbInPlace c (holdMessage msg)) =
        .ok (some (scId, server), popDonationSettledInPlace
          ((storeReplyRendezvousReady st c server rid).mapTcbInPlace c (holdMessage msg))
          c server scId (determineTargetCore st c)) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  unfold replyPopsInPlace at hG
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hCRes, hNeV⟩, hCB⟩, hLC⟩, hFC⟩, hLR⟩, hFR⟩, hLS⟩, hSome⟩, hM⟩ := hG
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFC
  have hNe : c ≠ server := fun e => by subst e; simp at hNeV
  obtain ⟨srv, hSrv⟩ := Option.isSome_iff_exists.mp hSome
  have hSrvO : st.objects[server.toObjId]? = some (.tcb srv) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hSrv
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
  obtain ⟨⟨hLsc, hFsc⟩, hM⟩ := hM
  cases hScg : st.getSchedContext? scId with
  | none => rw [hScg] at hM; cases hM
  | some sc =>
  rw [hScg] at hM
  dsimp only at hM
  simp only [Bool.and_eq_true] at hM
  obtain ⟨⟨⟨hHd, hBT⟩, hOr⟩, hBl⟩ := hM
  have hScO : st.objects[scId.toObjId]? = some (.schedContext sc) :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hScg
  have hHead : sc.scReply = some rid := by
    revert hHd
    cases sc.scReply with
    | none => intro h; cases h
    | some h =>
      intro e
      have : h = rid := by cases h; cases rid; simp only [beq_iff_eq] at e; subst e; rfl
      rw [this]
  have hB : sc.boundThread = some server := by
    unfold SchedContext.boundThread; rw [beq_iff_eq.mp hBT]; rfl
  have hOrig : rp.prev = none → ∀ o, sc.donationOrigin = some o → o = c := by
    intro hP o ho
    rw [hP, ho] at hOr
    cases o; cases c
    simp only [Option.isSome_none, Bool.false_or, beq_iff_eq] at hOr; subst hOr; rfl
  refine ⟨rp, scId, sc, hRp, hN, hScO, hHead, ?_, by simp only [replyHeadContextCode, hRg, hN],
    hCRes, hNe, hNo, hLC, hFC, hLR, hFR, ?_⟩
  · intro b hb
    rw [hb] at hBl
    dsimp only at hBl
    simp only [Bool.and_eq_true] at hBl
    obtain ⟨⟨⟨hbne, _⟩, _⟩, _⟩ := hBl
    exact fun e => by subst e; simp at hbne
  -- The state after the reply leg, against the pre-state.
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  generalize hS1 : storeReplyRendezvousReady st c server rid = S1
  have hAg := fun x hx hy => hS1 ▸ storeReplyRendezvousReady_agree st c server rid ct hNo hTc hFC x hx hy
  have hHold : ∀ x, x ≠ c.toObjId →
      (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = S1.objects[x]? := fun x hx => by
    rw [SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  obtain ⟨hI, hL⟩ := storeReplyRendezvousReady_fields st c server rid hNo
  rw [hS1] at hI hL
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
  have hV : ∀ x, notVSpaceRootAt st x = true → notVSpaceRootAt T x = true := by
    intro x hx
    by_cases hxc : x = c.toObjId
    · subst hxc; unfold notVSpaceRootAt; rw [SystemState.getObject?_eq_getElem, hTC]
    · by_cases hxr : x = rid.toObjId
      · subst hxr; unfold notVSpaceRootAt; rw [SystemState.getObject?_eq_getElem, hTR]
      · rw [notVSpaceRootAt_of_view (hView x hxc hxr)]; exact hx
  have hLT : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes T id ty = true := fun h => by
    rw [← hTdef]
    exact storeLeavesIndexAndTypes_of_frame (s' := S1.mapTcbInPlace c (holdMessage msg)) hI hL
      (hTdef ▸ hV) h
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
  obtain ⟨ht, hHTo, _⟩ := agreeAt_tcb (hView _ hSC hSR) hSrvO
  have hOT : T.getTcb? c = some (holdMessage msg tc1) := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC
  have hHT : T.getTcb? server = some ht := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hHTo
  -- The frame below, and the caller it names, as the pre-state had them.
  have hOuterT : ∀ k, outerCallerAcceptableCode st server c k = true →
      outerCallerAcceptableCode T server c k = true := by
    intro k hk
    cases k with
    | zero => rfl
    | succ o =>
      simp only [outerCallerAcceptableCode, Bool.and_eq_true] at hk ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hk
      refine ⟨⟨h1, h2⟩, ?_⟩
      have hoc : (⟨o⟩ : SeLe4n.ThreadId).toObjId ≠ c.toObjId := fun e => by
        have := SeLe4n.ThreadId.toObjId_injective _ _ e
        rw [← this] at h1; simp at h1
      have hor : (⟨o⟩ : SeLe4n.ThreadId).toObjId ≠ rid.toObjId := fun e => by
        unfold outerTestAt at h3
        rw [(show st.getTcb? ⟨o⟩ = none from by
          unfold SystemState.getTcb?; rw [e, hRp])] at h3
        cases h3
      rw [outerTestAt_of_view (hView _ hoc hor)]; exact h3
  have hBelowT : ∀ b, rp.consumed.prev = some b → b ≠ rid ∧ (∃ bR, T.getReply? b = some bR ∧
      bR.next = some (.frame rid) ∧ bR.callerCode ≠ 0) ∧
      storeLeavesIndexAndTypes T b.toObjId .reply = true ∧
      T.objects.findsInPlace b.toObjId = true := by
    intro b hb
    rw [hPrevC] at hb
    rw [hb] at hBl
    dsimp only at hBl
    simp only [Bool.and_eq_true] at hBl
    obtain ⟨⟨⟨hbne, hLb⟩, hFb⟩, hBm⟩ := hBl
    have hbr : b ≠ rid := fun e => by subst e; simp at hbne
    cases hBg : st.getReply? b with
    | none => rw [hBg] at hBm; cases hBm
    | some bR =>
    rw [hBg] at hBm
    dsimp only at hBm
    simp only [Bool.and_eq_true] at hBm
    obtain ⟨⟨hBN, hBC⟩, _⟩ := hBm
    have hBO : st.objects[b.toObjId]? = some (.reply bR) :=
      (SystemState.getReply?_eq_some_iff _ _ _).mp hBg
    have hbc : b.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hBO; cases hBO
    have hbr' : b.toObjId ≠ rid.toObjId := fun e => hbr (SeLe4n.ReplyId.toObjId_injective _ _ e)
    refine ⟨hbr, ⟨bR, (SystemState.getReply?_eq_some_iff _ _ _).mpr
      (agreeAt_of_not_tcb (hView _ hbc hbr') (fun _ e => by cases e) hBO), ?_, ?_⟩,
      hLT hLb, (hFT _).trans hFb⟩
    · revert hBN
      cases bR.next with
      | none => intro h; cases h
      | some l =>
        cases l with
        | head _ => intro h; cases h
        | frame f =>
          intro e
          have : f = rid := by cases f; cases rid; simp only [beq_iff_eq] at e; subst e; rfl
          rw [this]
    · simpa only [bne_iff_ne, ne_eq] using hBC
  have hOuter : outerCallerAcceptable T server c
      (SeLe4n.ThreadId.ofOptCode (popOuterCode T rp.consumed)) = true := by
    rw [← outerCallerAcceptableCode_eq]
    unfold popOuterCode
    rw [hPrevC]
    cases hP : rp.prev with
    | none => rfl
    | some b =>
      rw [hP] at hBl
      dsimp only at hBl
      simp only [Bool.and_eq_true] at hBl
      obtain ⟨⟨⟨hbne, _⟩, _⟩, hBm⟩ := hBl
      have hbr : b ≠ rid := fun e => by subst e; simp at hbne
      cases hBg : st.getReply? b with
      | none => rw [hBg] at hBm; cases hBm
      | some bR =>
      rw [hBg] at hBm
      dsimp only at hBm
      simp only [Bool.and_eq_true] at hBm
      have hBO : st.objects[b.toObjId]? = some (.reply bR) :=
        (SystemState.getReply?_eq_some_iff _ _ _).mp hBg
      have hbc : b.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hBO; cases hBO
      have hbr' : b.toObjId ≠ rid.toObjId := fun e => hbr (SeLe4n.ReplyId.toObjId_injective _ _ e)
      dsimp only
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr
        (agreeAt_of_not_tcb (hView _ hbc hbr') (fun _ e => by cases e) hBO)]
      exact hOuterT _ hBm.2
  have hRecip : donationRecipientAcceptable T c = true := by
    have e : tc1.scBindingScCode = ct.scBindingScCode := by
      have h := congrArg TCB.scBindingScCode hc1; exact h
    have hLk : lookupTcb T c = some (holdMessage msg tc1) := by
      unfold lookupTcb; rw [hCRes]; exact hOT
    rw [donationRecipientAcceptable_eq_of_some T c _ hLk, TCB.schedContextBinding_beq_unbound]
    show (tc1.scBindingScCode == 0) = true
    rw [e]; exact hCB
  have hDT : determineTargetCore T c = determineTargetCore st c := by
    have e : tc1.cpuAffinity = ct.cpuAffinity := by
      have h := congrArg TCB.cpuAffinity hc1; exact h
    unfold determineTargetCore
    rw [hOT, hTc]
    show (match tc1.cpuAffinity with | some c' => c' | none => bootCoreId) = _
    rw [e]
    rfl
  rw [← hDT]
  exact ⟨fun cv hcv => applyReplyDonationOnCore_eq_inPlace T rid cv c server hcv scId sc rp.consumed
    (holdMessage msg tc1) ht hRT hNextC hScT hHead hB (fun h => hOrig (hPrevC ▸ h)) hBelowT hOuter hRecip hCRes hSRes hOT hHT
    hNe (hLT hLsc) ((hFT _).trans hFsc) (hLT hLR) ((hFT _).trans hFR) (hLT hLC) ((hFT _).trans hFC)
    (hLT hLS),
    replyRecvPopDonation_eq_inPlace T rid c server scId sc rp.consumed
    (holdMessage msg tc1) ht hRT hNextC hScT hHead hB (fun h => hOrig (hPrevC ▸ h)) hBelowT hOuter hRecip hCRes hSRes hOT hHT
    hNe (hLT hLsc) ((hFT _).trans hFsc) (hLT hLR) ((hFT _).trans hFR) (hLT hLC) ((hFT _).trans hFC)
    (hLT hLS)⟩

end DonatedReplyGate

section DonatedReplyDelivered

/-- **The donated reply, delivered**: the caller woken without the message, the
loaned context handed back down the stack in place
(`replyDonationPopInPlace`, settled on the caller's home `home`), the server's
priority walk, then the reply's frame written into the caller's saved
registers. -/
@[noinline] def performReplyDonatedDelivered (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : CoreId) : SystemState :=
  let X := (PriorityInheritance.propagatePipChainCrossCore
    (replyDonationPopInPlace (storeReplyRendezvousReady st c server rid) c server scId home)
    server core).1
  writeDeliveredFrameIfReady X c (Architecture.regMessageFrameW layout rf len badgeWord badged)
    (fun _ => holdDeliveredBody X c layout rf len (SeLe4n.Badge.opt badgeWord badged))

/-- **The checked donated reply, in place**: under the flow gate and
`replyPopsInPlace`, a reply of at most four words to an unfaulted caller blocked
on it, whose reply object heads the stack of the context the server holds on
loan, commits `performReplyDonatedDelivered`'s state, its context the one the
reply object heads (`replyHeadContextCode`) and its home the caller's, both
read on the pre-state. -/
theorem replyTransferChecked_donated_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : CoreId) (msg : IpcMessage)
    (hMsg : msg =
      { registers := Architecture.regMessageBody layout rf len, badge := SeLe4n.Badge.opt badgeWord badged })
    (hSz : ¬ Architecture.regMessageLength layout len > maxMessageRegisters)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode server rid = true)
    (hNoF : ct.faultWords.isFault = false)
    (hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf c) = true) :
    replyTransferOnCoreChecked ctx replier c mi regs msg core st =
      .ok ((), performReplyDonatedDelivered st c server rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) layout rf len badgeWord badged core) := by
  replace hMsg := hMsg.symm
  obtain ⟨rp, scId, _, hRp, hN, _, _, _, hCode, hCRes, hNe, hNo, hLC, hFC, hLR, hFR, hDon, _⟩ :=
    replyPopsInPlace_donation st c server rid msg ct hT hSRes hG
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
  have hNoP := replyDonationPopInPlace_noResizeDue _ c server scId (determineTargetCore st c) hNoS
  unfold replyTransferOnCoreChecked
  rw [hNF, endpointReplyCrossCoreDispatchChecked_flow_allowed _ _ _ _ _ _ hFlow]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hsv, hAns, hcv]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    hDon cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  unfold performReplyDonatedDelivered
  subst hMsg
  rw [replyDonationPopInPlace_msg c id _ id _ c server scId _ hNoS hNe,
    Architecture.regMessageFrameW_eq, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoP,
    stageDeliveredMessage_holdMessage _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ hNoP)
      (by rw [Architecture.regMessageBody_size]; exact hSz4),
    Architecture.returnFrameOfMessage_regMessageBody]
  rfl

end DonatedReplyDelivered

end SeLe4n.Kernel
