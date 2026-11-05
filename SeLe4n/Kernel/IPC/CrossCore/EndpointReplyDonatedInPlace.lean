/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDonatingInPlace

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

/-- The code of the caller one frame below the head `r` (`0` at the bottom of
the stack): the thread a pop hands the context to as a loan, read as a code so
the read builds nothing. -/
@[inline] def popOuterCode (st : SystemState) (r : Reply) : Nat :=
  match r.prev with
  | none => 0
  | some b =>
    match st.getReply? b with
    | some bR => bR.callerCode
    | none => 0

/-- **The donation pop, in place** (seL4-MCS's `reply_pop`): the context
rebound to `owner` with the frame below as its head, the popped head's links
cleared, the frame below re-headed, `owner`'s binding the loan it is still owed
(or its own context at the bottom of the stack) and the holder's cleared.  Every
key the reschedule hook compares is read before the first write, and the links
it stores are the cells the head already holds, so the pop builds nothing.  The
identity where a read the specification refuses on finds nothing
(`returnDonatedSchedContextResolved_eq_inPlace` states the states on which it is
the specification's). -/
@[noinline] def returnDonatedSchedContextInPlace (st : SystemState)
    (holder owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) : SystemState :=
  match st.getSchedContext? scId with
  | none => st
  | some sc =>
    match sc.scReply with
    | none => st
    | some hr =>
      match st.getReply? hr with
      | none => st
      | some r =>
        match st.getTcb? owner with
        | none => st
        | some ot =>
          match st.getTcb? holder with
          | none => st
          | some ht =>
            let rprev := r.prev
            let rnext := r.next
            let outer := popOuterCode st r
            let op := ot.boostedPriority
            let od := effectiveDeadline st ot
            let odom := ot.domain
            let oe := hasSufficientBudget st ot
            let hp := ht.boostedPriority
            let hd := effectiveDeadline st ht
            let hdom := ht.domain
            let he := hasSufficientBudget st ht
            let s1 := st.updateSchedContext scId fun s =>
              { s with boundThreadCode := SeLe4n.ThreadId.optCode (some owner), scReply := rprev,
                       donationOrigin := if outer == 0 then none else s.donationOrigin }
            let s2 := s1.modifyObject hr.toObjId
              (SystemState.mapReplyObject fun x => { x with prev := none, next := none })
            let s3 := match rprev with
              | none => s2
              | some b => s2.modifyObject b.toObjId
                  (SystemState.mapReplyObject fun x => { x with next := rnext })
            let s4 := s3.updateTcb owner fun t =>
              { t with scBindingScCode := scId.val + 1, scBindingOwnerCode := outer }
            let s5 := s4.updateTcb holder fun t =>
              { t with scBindingScCode := 0, scBindingOwnerCode := 0 }
            markKeyChangeParts (markCandidacyGainFor (markKeyChangeParts
              (markCandidacyGainFor s5 owner oe) owner op od odom) holder he) holder hp hd hdom

/-- The binding the pop gives `owner`, as codes: its context, owed to the caller
`k` frames up (`0` at the bottom). -/
theorem donationReturnBinding_ofOptCode_codes (scId : SeLe4n.SchedContextId) (k : Nat) :
    SchedContextBinding.scCode (donationReturnBinding scId (SeLe4n.ThreadId.ofOptCode k)) =
        scId.val + 1 ∧
      SchedContextBinding.ownerCode (donationReturnBinding scId (SeLe4n.ThreadId.ofOptCode k)) = k := by
  cases k <;> exact ⟨rfl, rfl⟩

/-- The resolver of the outer caller answers the caller one frame below the
head, whose code `popOuterCode` reads. -/
theorem replyStackOuterCaller?_of_head (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (hr : SeLe4n.ReplyId) (r : Reply)
    (hSc : st.getSchedContext? scId = some sc) (hHead : sc.scReply = some hr)
    (hR : st.getReply? hr = some r) (hNext : r.next = some (.head scId))
    (hBelow : ∀ b, r.prev = some b → ∃ bR, st.getReply? b = some bR ∧
      bR.next = some (.frame hr) ∧ bR.callerCode ≠ 0) :
    donationHeadOf? st scId sc = .ok (some (hr, r)) ∧
      replyStackOuterCaller? st scId = .ok (SeLe4n.ThreadId.ofOptCode (popOuterCode st r)) := by
  have hD : donationHeadOf? st scId sc = .ok (some (hr, r)) := by
    unfold donationHeadOf?
    rw [hHead]
    simp only [hR, hNext, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine ⟨hD, ?_⟩
  unfold replyStackOuterCaller? popOuterCode
  rw [hSc]
  simp only [hD]
  cases hP : r.prev with
  | none => rfl
  | some b =>
    obtain ⟨bR, hB, hBN, hBC⟩ := hBelow b hP
    simp only [hB, hBN, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Reply.caller]
    cases hc : bR.callerCode with
    | zero => exact absurd hc hBC
    | succ k => rfl

/-- **The donation pop, in place**: on a state whose checks all pass — the
context held by `holder` and heading a stack at `hr`, the frame below (if any)
linked up to it with a caller, the outer caller and the recipient acceptable,
both threads present and distinct — and whose writes each leave the object
index and the types alone at keys found in place, the resolved return
succeeds with `returnDonatedSchedContextInPlace`'s state. -/
theorem returnDonatedSchedContextResolved_eq_inPlace (st : SystemState)
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
    (hLh : storeLeavesIndexAndTypes st holder.toObjId .tcb = true) :
    returnDonatedSchedContextResolved st holder scId owner =
      .ok (returnDonatedSchedContextInPlace st holder owner scId) := by
  obtain ⟨hD, hRes⟩ := replyStackOuterCaller?_of_head st scId sc hr r hSc hHead hR hNext
    (fun b hb => (hBelow b hb).2.1)
  have hScO : st.objects[scId.toObjId]? = some (.schedContext sc) :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hRO : st.objects[hr.toObjId]? = some (.reply r) :=
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hOO : st.objects[owner.toObjId]? = some (.tcb ot) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hOT
  have hHO : st.objects[holder.toObjId]? = some (.tcb ht) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hHT
  have hScR : scId.toObjId ≠ hr.toObjId := fun h => by rw [h, hRO] at hScO; cases hScO
  have hScOw : scId.toObjId ≠ owner.toObjId := fun h => by rw [h, hOO] at hScO; cases hScO
  have hScH : scId.toObjId ≠ holder.toObjId := fun h => by rw [h, hHO] at hScO; cases hScO
  have hROw : hr.toObjId ≠ owner.toObjId := fun h => by rw [h, hOO] at hRO; cases hRO
  have hRH : hr.toObjId ≠ holder.toObjId := fun h => by rw [h, hHO] at hRO; cases hRO
  have hOH : owner.toObjId ≠ holder.toObjId :=
    fun h => hNeOH (SeLe4n.ThreadId.toObjId_injective _ _ h)
  have hBNe : (sc.boundThread != some holder) = false := by rw [hB]; exact bne_self_eq_false _
  have hIso : ∀ k : Nat, (SeLe4n.ThreadId.ofOptCode k).isNone = (k == 0) := by
    intro k; cases k <;> rfl
  have hLkO : ∀ s : SystemState, s.getTcb? owner = some ot → lookupTcb s owner = some ot :=
    fun s h => by unfold lookupTcb; rw [hORes]; exact h
  have hLkH : ∀ s : SystemState, s.getTcb? holder = some ht → lookupTcb s holder = some ht :=
    fun s h => by unfold lookupTcb; rw [hHRes]; exact h
  unfold returnDonatedSchedContextResolved
  rw [hRes]
  simp only []
  unfold returnDonatedSchedContext returnDonatedSchedContextInPlace
  rw [hSc]
  simp only [hBNe, hOuter, hRecip, hD, hHead, hR, hOT, hHT, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Option.bind_some]
  generalize hk : popOuterCode st r = k at *
  obtain ⟨hC1, hC2⟩ := donationReturnBinding_ofOptCode_codes scId k
  unfold donationReturnSchedContext
  rw [hIso k, storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLsc),
    SystemState.updateSchedContext_eq_of_some hSc]
  simp only []
  generalize hS1 : ({ st with objects := st.objects.insert scId.toObjId (.schedContext
    { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some owner), scReply := r.prev,
              donationOrigin := if (k == 0) = true then none else sc.donationOrigin }) } :
      SystemState) = S1
  have hO1 : ∀ x, scId.toObjId ≠ x → S1.objects[x]? = st.objects[x]? := fun x hx => by
    rw [← hS1]; exact RobinHood.RHTable.get?_insert_ne_of_findsInPlace x _ hFsc hx
  have hK1 : ∀ x, S1.objects.findsInPlace x = st.objects.findsInPlace x := fun x => by
    rw [← hS1]; exact RobinHood.RHTable.findsInPlace_insert_of_findsInPlace x _ hFsc
  have hL1 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes S1 id ty = true := fun h => by
    rw [← hS1]; exact storeLeavesIndexAndTypes_insert_inPlace hFsc (fun _ e => by cases e) h
  -- The popped head's links cleared.
  have hR1 : S1.objects[hr.toObjId]? = some (.reply r) := (hO1 _ hScR).trans hRO
  rw [storeDonationHeadPop_some, storeDonationHeadClear_some,
    (SystemState.getReply?_eq_some_iff _ _ _).mpr hR1]
  simp only []
  rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL1 hLr)]
  simp only []
  have hM2 : S1.modifyObject hr.toObjId (SystemState.mapReplyObject fun x =>
        { x with prev := none, next := none }) =
      { S1 with objects := S1.objects.insert hr.toObjId (.reply { r with prev := none, next := none }) } := by
    unfold SystemState.modifyObject
    rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? (by exact hR1)]
    rfl
  rw [hM2]
  have hFr1 := (hK1 _).trans hFr
  generalize hS2 : ({ S1 with objects := S1.objects.insert hr.toObjId (.reply
    { r with prev := none, next := none }) } : SystemState) = S2
  have hO2 : ∀ x, hr.toObjId ≠ x → S2.objects[x]? = S1.objects[x]? := fun x hx => by
    rw [← hS2]; exact RobinHood.RHTable.get?_insert_ne_of_findsInPlace x _ hFr1 hx
  have hK2 : ∀ x, S2.objects.findsInPlace x = st.objects.findsInPlace x := fun x => by
    rw [← hS2]; exact (RobinHood.RHTable.findsInPlace_insert_of_findsInPlace x _ hFr1).trans (hK1 x)
  have hL2 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes S2 id ty = true := fun h => by
    rw [← hS2]; exact storeLeavesIndexAndTypes_insert_inPlace hFr1 (fun _ e => by cases e) (hL1 h)
  -- The frame below re-headed.
  have hTO2 : S2.objects[owner.toObjId]? = some (.tcb ot) :=
    ((hO2 _ hROw).trans (hO1 _ hScOw)).trans hOO
  have hTH2 : S2.objects[holder.toObjId]? = some (.tcb ht) :=
    ((hO2 _ hRH).trans (hO1 _ hScH)).trans hHO
  obtain ⟨T, hReHead, hEq3, hTO, hTH, hFTo, hLTo, hLTh⟩ : ∃ T,
      storeReplyReHead scId r.prev S2 = .ok T ∧
      (match r.prev with
        | none => S2
        | some b => S2.modifyObject b.toObjId
            (SystemState.mapReplyObject fun x => { x with next := r.next })) = T ∧
      T.objects[owner.toObjId]? = some (.tcb ot) ∧
      T.objects[holder.toObjId]? = some (.tcb ht) ∧
      T.objects.findsInPlace owner.toObjId = true ∧
      storeLeavesIndexAndTypes T owner.toObjId .tcb = true ∧
      storeLeavesIndexAndTypes T holder.toObjId .tcb = true := by
    cases hP : r.prev with
    | none =>
      exact ⟨S2, storeReplyReHead_none _ _, rfl, hTO2, hTH2, (hK2 _).trans hFo, hL2 hLo, hL2 hLh⟩
    | some b =>
      obtain ⟨hbNe, ⟨bR, hBR, _, _⟩, hLb, hFb⟩ := hBelow b hP
      have hBO : st.objects[b.toObjId]? = some (.reply bR) :=
        (SystemState.getReply?_eq_some_iff _ _ _).mp hBR
      have hRB : hr.toObjId ≠ b.toObjId :=
        fun h => hbNe (SeLe4n.ReplyId.toObjId_injective _ _ h).symm
      have hScB : scId.toObjId ≠ b.toObjId := fun h => by rw [h, hBO] at hScO; cases hScO
      have hBOw : b.toObjId ≠ owner.toObjId := fun h => by rw [h, hOO] at hBO; cases hBO
      have hBH : b.toObjId ≠ holder.toObjId := fun h => by rw [h, hHO] at hBO; cases hBO
      have hB2 : S2.objects[b.toObjId]? = some (.reply bR) :=
        ((hO2 _ hRB).trans (hO1 _ hScB)).trans hBO
      have hFb2 := (hK2 _).trans hFb
      refine ⟨{ S2 with objects := S2.objects.insert b.toObjId (.reply { bR with next := some (.head scId) }) }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [storeReplyReHead_some, (SystemState.getReply?_eq_some_iff _ _ _).mpr hB2]
        simp only []
        rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL2 hLb)]
      · show S2.modifyObject b.toObjId (SystemState.mapReplyObject fun x =>
            { x with next := r.next }) = _
        unfold SystemState.modifyObject
        rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? (by exact hB2), hNext]
        rfl
      · exact (RobinHood.RHTable.get?_insert_ne_of_findsInPlace _ _ hFb2 hBOw).trans hTO2
      · exact (RobinHood.RHTable.get?_insert_ne_of_findsInPlace _ _ hFb2 hBH).trans hTH2
      · exact (RobinHood.RHTable.findsInPlace_insert_of_findsInPlace _ _ hFb2).trans
          ((hK2 _).trans hFo)
      · exact storeLeavesIndexAndTypes_insert_inPlace hFb2 (fun _ e => by cases e) (hL2 hLo)
      · exact storeLeavesIndexAndTypes_insert_inPlace hFb2 (fun _ e => by cases e) (hL2 hLh)
  rw [hReHead, hEq3]
  simp only []
  have hTOt : T.getTcb? owner = some ot := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hTO
  rw [hLkO T hTOt]
  simp only []
  rw [hC1, hC2, storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLTo),
    SystemState.updateTcb_eq_of_some hTOt]
  simp only []
  generalize hT3 : ({ T with objects := T.objects.insert owner.toObjId (.tcb
    { ot with scBindingScCode := scId.val + 1, scBindingOwnerCode := k }) } : SystemState) = T3
  have hX : T3.objects[holder.toObjId]? = some (.tcb ht) := by
    rw [← hT3]; exact (RobinHood.RHTable.get?_insert_ne_of_findsInPlace _ _ hFTo hOH).trans hTH
  have hXT : T3.getTcb? holder = some ht := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hX
  have hLT3 : storeLeavesIndexAndTypes T3 holder.toObjId .tcb = true := by
    rw [← hT3]; exact storeLeavesIndexAndTypes_insert_inPlace hFTo (fun _ e => by cases e) hLTh
  rw [hLkH T3 hXT]
  simp only []
  rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLT3),
    SystemState.updateTcb_eq_of_some hXT]
  simp only []
  rw [markKeyChangeFrom_of_getTcb st _ owner ot hOT,
    markKeyChangeFrom_of_getTcb st _ holder ht hHT]

/-- The pop of the reply's donation, in place: the context handed back to the
answered caller `c` (`returnDonatedSchedContextInPlace`), settled on `home`
(`settleReturnedContext`, the tail of seL4's `schedContext_donate`), and the
holder taken off its core.  `home` is the caller's home core, read by the caller
before the first write. -/
@[noinline] def replyDonationPopInPlace (st : SystemState) (c holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (home : CoreId) : SystemState :=
  descheduleAtPlacement
    (SchedContextOps.settleReturnedContext (returnDonatedSchedContextInPlace st holder c scId)
      home scId) holder

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

/-- **The reply's donation, in place**: on a state where the answered reply heads
the stack of a context its holder holds, the frame below (if any) links up to it
with a caller, the context records no origin other than the answered caller, and
every check of the pop passes, the reply's donation step returns
`replyDonationPopInPlace`'s state. -/
theorem applyReplyDonationOnCore_eq_inPlace (S : SystemState) (rid : SeLe4n.ReplyId)
    (cv : SeLe4n.ValidThreadId) (c holder : SeLe4n.ThreadId) (hcv : cv.val = c)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (r : Reply) (ot ht : TCB)
    (hR : S.getReply? rid = some r) (hNext : r.next = some (.head scId))
    (hSc : S.getSchedContext? scId = some sc) (hHead : sc.scReply = some rid)
    (hB : sc.boundThread = some holder)
    (hOrig : ∀ o, sc.donationOrigin = some o → o = c)
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
  have hRecipEq := replyDonationRecipient_eq_self S scId sc c hSc hOrig
  obtain ⟨hv, hhv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff holder).mpr hHRes)
  have hhv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hhv
  unfold applyReplyDonationOnCore
  rw [replyDonationRecipientHome_of_head S rid c scId holder hHolder, hHolder]
  simp only [hhv, hcv, hRecipEq]
  rw [hhv', returnDonatedSchedContextResolved_eq_inPlace S holder c scId sc rid r ot ht hSc hB hHead
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
theorem replyDonationPopInPlace_msg (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (st : SystemState) (c holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (hNo : st.objects.noResizeDue)
    (hH : r ≠ holder) :
    replyDonationPopInPlace (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c holder scId home =
      (replyDonationPopInPlace st c holder scId home).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  unfold replyDonationPopInPlace
  rw [returnDonatedSchedContextInPlace_msg r ρ μ π st holder c scId hNo hH,
    settleReturnedContext_msg, descheduleAtPlacement_msg]

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

/-- The reply's donation pop leaves the table's size and capacity alone. -/
theorem replyDonationPopInPlace_noResizeDue (st : SystemState) (c holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (hNo : st.objects.noResizeDue) :
    (replyDonationPopInPlace st c holder scId home).objects.noResizeDue := by
  unfold replyDonationPopInPlace descheduleAtPlacement descheduleAt
  have h := settleReturnedContext_noResizeDue _ home scId
    (returnDonatedSchedContextInPlace_noResizeDue st holder c scId hNo)
  split
  · exact removeRunnableOnCore_noResizeDue _ _ _ h
  · exact h

end DonationPop

end SeLe4n.Kernel
