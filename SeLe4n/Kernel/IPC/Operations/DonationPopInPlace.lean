/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.DonationInPlace
import SeLe4n.Kernel.Lifecycle.Suspend

/-!
# seL4-MCS's `reply_pop`, each object written in its slot

The donation pop (`returnDonatedSchedContextInPlace`: the context handed back
down its reply stack, the popped head's links cleared, the frame below
re-headed, the two threads' bindings rewritten), proven equal to the
specification's pop on every state whose checks pass
(`returnDonatedSchedContextResolved_eq_inPlace`), and the gate that reads those
checks on the pre-state as codes (`replyPopsInPlace`).  A donated reply and a
reply-receive pop through it after their reply leg
(`IPC/CrossCore/EndpointReplyDonatedInPlace.lean`); a final delete pops through
it directly, a reply heading a context's stack removed as seL4-MCS's
`reply_remove` removes it, and the caller ended (`cancelIpcBlockingReclaimedImpl`,
which the reply and thread finalisations run, `IPC/Operations/CancelAll.lean`).
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

/-- The pop of a reply's donation and its settle, in place: the context handed
back to the answered caller `c` (`returnDonatedSchedContextInPlace`) and settled
on `home` (`settleReturnedContext`, the tail of seL4's `schedContext_donate`).
A reply-receive's pop runs this between its reply leg and its receive leg; a
reply's then takes the holder off its core (`replyDonationPopInPlace`). -/
@[noinline] def popDonationSettledInPlace (st : SystemState) (c holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (home : CoreId) : SystemState :=
  SchedContextOps.settleReturnedContext (returnDonatedSchedContextInPlace st holder c scId) home scId

/-- The pop of the reply's donation, in place: the pop and its settle
(`popDonationSettledInPlace`), then the holder taken off its core.  `home` is
the caller's home core, read by the caller before the first write. -/
@[noinline] def replyDonationPopInPlace (st : SystemState) (c holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (home : CoreId) : SystemState :=
  descheduleAtPlacement (popDonationSettledInPlace st c holder scId home) holder


end DonationPop

section DonationPopGate

/-- Whether a thread's binding is `.unbound`, read off its code. -/
theorem TCB.schedContextBinding_beq_unbound (t : TCB) :
    (t.schedContextBinding == .unbound) = (t.scBindingScCode == 0) := by
  unfold TCB.schedContextBinding SchedContextBinding.ofCodes
  cases t.scBindingScCode with
  | zero => rfl
  | succ s => cases t.scBindingOwnerCode <;> rfl

/-- Whether a thread is blocked on a reply, read off its state code. -/
theorem TCB.blockedOnReply_test_eq (t : TCB) :
    (match t.ipcState with
     | .blockedOnReply _ _ => true
     | _ => false) = decide (4 ≤ t.ipcStateCode) := by
  unfold TCB.ipcState ThreadIpcState.ofCodes
  cases t.ipcStateCode with
  | zero => cases t.ipcObjectCode <;> rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => cases n with
      | zero => rfl
      | succ n => cases n with
        | zero => rfl
        | succ n => exact (decide_eq_true (by omega)).symm

/-- The outer caller's own state, as the pop reads it: unbound and blocked on a
reply, off its codes. -/
@[inline] def outerTestAt (st : SystemState) (x : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? x with
  | some t => t.scBindingScCode == 0 && decide (4 ≤ t.ipcStateCode)
  | none => false

/-- The checks the pop makes of the outer caller (code `k`, `0` at the bottom of
the stack), read off codes so the test builds nothing. -/
@[inline] def outerCallerAcceptableCode (st : SystemState) (server c : SeLe4n.ThreadId) :
    Nat → Bool
  | 0 => true
  | o + 1 => o != c.val && o != server.val && outerTestAt st ⟨o⟩

theorem outerCallerAcceptableCode_eq (st : SystemState) (server c : SeLe4n.ThreadId) (k : Nat) :
    outerCallerAcceptableCode st server c k =
      outerCallerAcceptable st server c (SeLe4n.ThreadId.ofOptCode k) := by
  cases k with
  | zero => rfl
  | succ o =>
    have h1 : ((⟨o⟩ : SeLe4n.ThreadId) != c) = (o != c.val) := by
      apply Bool.eq_iff_iff.mpr
      cases c; simp only [bne_iff_ne, ne_eq, SeLe4n.ThreadId.mk.injEq]
    have h2 : ((⟨o⟩ : SeLe4n.ThreadId) != server) = (o != server.val) := by
      apply Bool.eq_iff_iff.mpr
      cases server; simp only [bne_iff_ne, ne_eq, SeLe4n.ThreadId.mk.injEq]
    simp only [outerCallerAcceptableCode, outerCallerAcceptable, SeLe4n.ThreadId.ofOptCode, h1, h2,
      outerTestAt]
    cases st.getTcb? ⟨o⟩ with
    | none => rfl
    | some t =>
      dsimp only
      rw [TCB.schedContextBinding_beq_unbound]
      exact congrArg (fun x => (o != c.val && o != server.val && (t.scBindingScCode == 0 && x)))
        (TCB.blockedOnReply_test_eq t).symm

/-- The context code a reply heads (`0` where it heads none). -/
@[inline] def replyHeadContextCode (st : SystemState) (rid : SeLe4n.ReplyId) : Nat :=
  match st.getReply? rid with
  | some rp =>
    match rp.next with
    | some (.head s) => s.val + 1
    | _ => 0
  | none => 0

/-- **A reply whose pop may write in place**, read on the pre-state: the
answered caller `c` (an unreserved thread, unbound) and the server distinct, the
caller's, its reply object's and the server's slots local, the reply object
heading the stack of a context the server is bound to, and the frame below (if
any) another local reply linked up to it whose caller passes the pop's checks;
at the bottom of the stack (no frame below) the context records no origin other
than the caller, since only there is the recorded origin the recipient
(`donationOriginRecipient?`).  Every read is a code, so the
test builds nothing. -/
@[inline] def replyPopsInPlace (st : SystemState) (c : SeLe4n.ThreadId) (cBinding : Nat)
    (server : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  !c.isReserved && c.val != server.val && cBinding == 0 &&
  storeLeavesIndexAndTypes st c.toObjId .tcb &&
  st.objects.findsInPlace c.toObjId &&
  storeLeavesIndexAndTypes st rid.toObjId .reply &&
  st.objects.findsInPlace rid.toObjId &&
  storeLeavesIndexAndTypes st server.toObjId .tcb &&
  (st.getTcb? server).isSome &&
  (match st.getReply? rid with
   | some rp =>
     match rp.next with
     | some (.head scId) =>
       storeLeavesIndexAndTypes st scId.toObjId .schedContext &&
       st.objects.findsInPlace scId.toObjId &&
       (match st.getSchedContext? scId with
        | some sc =>
          (match sc.scReply with
           | some h => h.val == rid.val
           | none => false) &&
          sc.boundThreadCode == server.val + 1 &&
          (rp.prev.isSome ||
            match sc.donationOrigin with
            | some o => o.val == c.val
            | none => true) &&
          (match rp.prev with
           | none => true
           | some b =>
             b.val != rid.val && storeLeavesIndexAndTypes st b.toObjId .reply &&
             st.objects.findsInPlace b.toObjId &&
             (match st.getReply? b with
              | some bR =>
                (match bR.next with
                 | some (.frame f) => f.val == rid.val
                 | _ => false) &&
                bR.callerCode != 0 && outerCallerAcceptableCode st server c bR.callerCode
              | none => false))
        | none => false)
     | _ => false
   | none => false)

end DonationPopGate

section HeadReplyCancel

/-- A thread's binding is `.unbound` exactly when its context code is `0`. -/
theorem TCB.schedContextBinding_eq_unbound_iff (t : TCB) :
    t.schedContextBinding = .unbound ↔ t.scBindingScCode = 0 := by
  unfold TCB.schedContextBinding SchedContextBinding.ofCodes
  cases t.scBindingScCode with
  | zero => simp
  | succ s => cases t.scBindingOwnerCode <;> simp

/-- **The gate's pop, on the state it reads**: under `replyPopsInPlace`, read with
the caller's own binding code, the reply heads the stack of a context (the code
`replyHeadContextCode` reads) held by `server`, the frame-keyed resolver names
that context and holder, and the specification's pop of it from `server` to the
caller commits with `returnDonatedSchedContextInPlace`'s state. -/
theorem replyPopsInPlace_pop (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (ct : TCB)
    (hT : st.getTcb? c = some ct) (hSRes : server.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode server rid = true) :
    ∃ scId : SeLe4n.SchedContextId,
      replyHeadContextCode st rid = scId.val + 1 ∧
      replyFrameHeadHolder? st rid = some (scId, server) ∧
      donatedReturnCommits st server scId c = true ∧
      returnDonatedSchedContextResolved st server scId c =
        .ok (returnDonatedSchedContextInPlace st server c scId) := by
  unfold replyPopsInPlace at hG
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hCRes, hNeV⟩, hCB⟩, hLC⟩, hFC⟩, hLR⟩, hFR⟩, hLS⟩, hSome⟩, hM⟩ := hG
  have hNe : c ≠ server := fun e => by subst e; simp at hNeV
  obtain ⟨srv, hSrv⟩ := Option.isSome_iff_exists.mp hSome
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
  obtain ⟨⟨hLsc, hFsc⟩, hM⟩ := hM
  cases hScg : st.getSchedContext? scId with
  | none => rw [hScg] at hM; cases hM
  | some sc =>
  rw [hScg] at hM
  dsimp only at hM
  simp only [Bool.and_eq_true] at hM
  obtain ⟨⟨⟨hHd, hBT⟩, _⟩, hBl⟩ := hM
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
  have hBelow : ∀ b, rp.prev = some b → b ≠ rid ∧ (∃ bR, st.getReply? b = some bR ∧
      bR.next = some (.frame rid) ∧ bR.callerCode ≠ 0) ∧
      storeLeavesIndexAndTypes st b.toObjId .reply = true ∧
      st.objects.findsInPlace b.toObjId = true := by
    intro b hb
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
    refine ⟨hbr, ⟨bR, rfl, ?_, ?_⟩, hLb, hFb⟩
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
  have hOuter : outerCallerAcceptable st server c
      (SeLe4n.ThreadId.ofOptCode (popOuterCode st rp)) = true := by
    rw [← outerCallerAcceptableCode_eq]
    unfold popOuterCode
    cases hP : rp.prev with
    | none => rfl
    | some b =>
      rw [hP] at hBl
      dsimp only at hBl
      simp only [Bool.and_eq_true] at hBl
      obtain ⟨_, hBm⟩ := hBl
      cases hBg : st.getReply? b with
      | none => rw [hBg] at hBm; cases hBm
      | some bR =>
      rw [hBg] at hBm
      dsimp only at hBm
      simp only [Bool.and_eq_true] at hBm
      simp only [hBg]
      exact hBm.2
  have hLk : lookupTcb st c = some ct := by unfold lookupTcb; rw [hCRes]; exact hT
  have hRecip : donationRecipientAcceptable st c = true := by
    rw [donationRecipientAcceptable_eq_of_some st c _ hLk, TCB.schedContextBinding_beq_unbound]
    exact hCB
  have hCommit : donatedReturnCommits st server scId c = true := by
    obtain ⟨_, hRes⟩ := replyStackOuterCaller?_of_head st scId sc rid rp hScg hHead hRg hN
      (fun b hb => (hBelow b hb).2.1)
    have hLs : lookupTcb st server = some srv := by unfold lookupTcb; rw [hSRes]; exact hSrv
    unfold donatedReturnCommits
    rw [hRes, hScg]
    simp only [hB, beq_self_eq_true, hOuter, hRecip, hLk, hLs, Option.isSome_some, Bool.and_self]
  refine ⟨scId, by simp only [replyHeadContextCode, hRg, hN], ?_, hCommit, ?_⟩
  · apply replyFrameHeadHolder?_of_head
    · unfold replyFrameHeadContext?
      rw [hRg]
      simp only [hN, hScg, hHead, beq_self_eq_true, ↓reduceIte]
    · rw [hScg]; exact hB
  · exact returnDonatedSchedContextResolved_eq_inPlace st server c scId sc rid rp ct srv hScg hB
      hHead hRg hN hBelow hOuter hRecip hCRes hSRes hT hSrv hNe hLsc hFsc hLR hFR hLC hFC hLS

/-- **Whether a donation return passes the in-place pop's checks**, read as
codes: the server is no reserved thread and the reply heading context `scId`'s
stack passes `replyPopsInPlace` for the pop of `scId` from `server` back to
`c`, read with `c`'s own binding code off the store. -/
@[inline] def donatedReturnPopsInPlace (st : SystemState) (server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (c : SeLe4n.ThreadId) : Bool :=
  !server.isReserved &&
    match st.getSchedContext? scId with
    | some sc =>
      match sc.scReply with
      | some rid =>
        replyHeadContextCode st rid == scId.val + 1 &&
          match st.getTcb? c with
          | some ct => replyPopsInPlace st c ct.scBindingScCode server rid
          | none => false
      | none => false
    | none => false

/-- **`donatedReturnCommits` as compiled**: `true` at once where the in-place
pop's code checks pass (`donatedReturnPopsInPlace`), which imply every check of
the specification's (`replyPopsInPlace_pop`); the specification's reads
otherwise. -/
def donatedReturnCommitsImpl (st : SystemState) (server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (c : SeLe4n.ThreadId) : Bool :=
  donatedReturnPopsInPlace st server scId c || donatedReturnCommits st server scId c

@[csimp] theorem donatedReturnCommits_eq_impl :
    @donatedReturnCommits = @donatedReturnCommitsImpl := by
  funext st server scId c
  unfold donatedReturnCommitsImpl
  cases h : donatedReturnPopsInPlace st server scId c with
  | false => rfl
  | true =>
    simp only [Bool.true_or]
    unfold donatedReturnPopsInPlace at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hSRes, hM⟩ := h
    cases hSc : st.getSchedContext? scId with
    | none => rw [hSc] at hM; cases hM
    | some sc =>
    rw [hSc] at hM
    dsimp only at hM
    cases hR : sc.scReply with
    | none => rw [hR] at hM; cases hM
    | some rid =>
    rw [hR] at hM
    dsimp only at hM
    simp only [Bool.and_eq_true] at hM
    obtain ⟨hCode, hM⟩ := hM
    cases hT : st.getTcb? c with
    | none => rw [hT] at hM; cases hM
    | some ct =>
    rw [hT] at hM
    dsimp only at hM
    obtain ⟨scId', hC', _, hCommit, _⟩ := replyPopsInPlace_pop st c server rid ct hT hSRes hM
    have hEq : scId' = scId := by
      rw [hC'] at hCode
      cases scId'; cases scId
      simp only [beq_iff_eq, Nat.add_right_cancel_iff] at hCode
      rw [hCode]
    rw [← hEq]; exact hCommit

/-- **Whether the cancel of a caller `c` (its TCB `t`) blocked on a reply that
heads a context's stack may write in place**, read on the pre-state as codes:
`c` is blocked on a reply its reply code names, its recorded server is no
reserved thread, and the pop of that reply's context from the server back to
`c` passes every check of `replyPopsInPlace`, read with `c`'s own binding code
off the store. -/
@[inline] def headReplyCancelInPlace (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB) :
    Bool :=
  decide (4 ≤ t.ipcStateCode) && t.replyObjectCode != 0 &&
    match replyCallerServerCode t with
    | 0 => false
    | s + 1 =>
      !(⟨s⟩ : SeLe4n.ThreadId).isReserved &&
        match st.getTcb? c with
        | some ct => replyPopsInPlace st c ct.scBindingScCode ⟨s⟩ ⟨t.replyObjectCode - 1⟩
        | none => false

/-- **A head reply's caller cancelled, each object written in its slot**
(seL4-MCS's `reply_remove` head branch): the context handed back to the caller
`c` by the pop (`returnDonatedSchedContextInPlace`, `reply_pop`), the caller
restored with the cancellation frame, its reply link consumed and it taken off
its server's reply-waiter queue (`cancelReplyArmInPlace`, from the caller's
reply code `code` and its server's `serverCode`), the context settled on the
home of the thread it is now bound to (`settleReturnedContext`, the tail of
`schedContext_donate`), and the server, unbound by the pop, taken off the
scheduler (`schedContext_donate`'s `tcbSchedDequeue` of the thread it leaves).
`fromCore` is the server's home, read before the first write. -/
@[noinline] def cancelHeadReplyCallerInPlace (st : SystemState) (c server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (code serverCode : Nat) (fromCore : CoreId) : SystemState :=
  let torn := Lifecycle.Suspend.cancelReplyArmInPlace
    (returnDonatedSchedContextInPlace st server c scId) c code serverCode
  let post := SchedContextOps.settleReturnedContext torn
    (replenishHomeOfSchedContext torn scId fromCore) scId
  match post.getTcb? server, post.getTcb? c with
  | some h, some v =>
    if h.scBindingScCode == 0 && v.scBindingScCode != 0 then descheduleAtPlacement post server
    else post
  | _, _ => post

/-- **The reclaim-complete cancel of a head reply's caller is its in-place
writes** on every state `headReplyCancelInPlace` admits. -/
theorem cancelIpcBlockingReclaimed_eq_inPlace (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (h : headReplyCancelInPlace st c t = true) :
    cancelIpcBlockingReclaimed c t st =
      cancelHeadReplyCallerInPlace st c ⟨replyCallerServerCode t - 1⟩
        ⟨replyHeadContextCode st ⟨t.replyObjectCode - 1⟩ - 1⟩ t.replyObjectCode
        (replyCallerServerCode t) (determineTargetCore st ⟨replyCallerServerCode t - 1⟩) := by
  unfold headReplyCancelInPlace at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h4, hRc⟩, hM⟩ := h
  cases hS : replyCallerServerCode t with
  | zero => rw [hS] at hM; cases hM
  | succ s =>
  rw [hS] at hM
  dsimp only at hM
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hM
  obtain ⟨hSRes, hM⟩ := hM
  cases hTg : st.getTcb? c with
  | none => rw [hTg] at hM; cases hM
  | some ct =>
  rw [hTg] at hM
  dsimp only at hM
  obtain ⟨scId, hCode, hHolder, _, hPop⟩ := replyPopsInPlace_pop st c ⟨s⟩ _ ct hTg hSRes hM
  have hSc : (⟨replyHeadContextCode st ⟨t.replyObjectCode - 1⟩ - 1⟩ : SeLe4n.SchedContextId) =
      scId := by rw [hCode]; rfl
  rw [hSc]
  have hBl := TCB.blockedOnReply_test_eq t
  have hIpc : ∃ ep rt, t.ipcState = .blockedOnReply ep rt := by
    revert hBl
    cases t.ipcState with
    | blockedOnReply ep rt => intro _; exact ⟨ep, rt, rfl⟩
    | _ => intro e; rw [h4] at e; cases e
  obtain ⟨ep, rt, hIpc⟩ := hIpc
  have hRO : t.replyObject = some ⟨t.replyObjectCode - 1⟩ := by
    unfold TCB.replyObject
    cases e : t.replyObjectCode with
    | zero => exact absurd e hRc
    | succ k => rfl
  have hDon : Lifecycle.Suspend.cancelledCallerDonation? st c t = some (scId, ⟨s⟩) := by
    unfold Lifecycle.Suspend.cancelledCallerDonation?
    rw [hIpc]
    simp only [hRO, hHolder]
  have hRet : Lifecycle.Suspend.returnDonationToCancelledCaller st c t =
      returnDonatedSchedContextInPlace st ⟨s⟩ c scId := by
    unfold Lifecycle.Suspend.returnDonationToCancelledCaller
    rw [hDon, hTg]
    simp only [hPop]
  have hTorn : Lifecycle.Suspend.cancelIpcBlocking st c t =
      Lifecycle.Suspend.cancelReplyArmInPlace (returnDonatedSchedContextInPlace st ⟨s⟩ c scId) c
        t.replyObjectCode (s + 1) := by
    rw [Lifecycle.Suspend.cancelIpcBlocking_eq_impl]
    unfold Lifecycle.Suspend.cancelIpcBlockingImpl
    rw [hIpc]
    simp only [hRet, hS]
  unfold cancelIpcBlockingReclaimed descheduleUnboundHolder cancelIpcBlockingMigrated
    cancelUnboundHolder? cancelHeadReplyCallerInPlace
  rw [hDon]
  simp only [hTorn, Nat.add_sub_cancel]
  generalize SchedContextOps.settleReturnedContext _ _ scId = post
  cases post.getTcb? ⟨s⟩ with
  | none => rfl
  | some hT =>
    cases post.getTcb? c with
    | none => rfl
    | some vT =>
      simp only [TCB.schedContextBinding_eq_unbound_iff, ne_eq]
      by_cases e1 : hT.scBindingScCode = 0 <;> by_cases e2 : vT.scBindingScCode = 0 <;>
        simp [e1, e2]

/-- **The reclaim-complete cancel of a caller blocked on a head reply, as
compiled**: its in-place writes where `headReplyCancelInPlace` admits them,
every code read before the first write; the specification's cancel otherwise. -/
@[inline] def cancelHeadReplyCaller (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB) :
    SystemState :=
  if headReplyCancelInPlace st c t then
    let code := t.replyObjectCode
    let serverCode := replyCallerServerCode t
    let server : SeLe4n.ThreadId := ⟨serverCode - 1⟩
    cancelHeadReplyCallerInPlace st c server ⟨replyHeadContextCode st ⟨code - 1⟩ - 1⟩ code
      serverCode (determineTargetCore st server)
  else cancelIpcBlockingReclaimed c t st

theorem cancelHeadReplyCaller_eq (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB) :
    cancelHeadReplyCaller st c t = cancelIpcBlockingReclaimed c t st := by
  unfold cancelHeadReplyCaller
  split
  · next h => exact (cancelIpcBlockingReclaimed_eq_inPlace st c t h).symm
  · rfl

end HeadReplyCancel

end SeLe4n.Kernel
