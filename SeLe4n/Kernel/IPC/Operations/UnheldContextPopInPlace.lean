/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.DonationPopInPlace
import SeLe4n.Kernel.IPC.Operations.UnheldContextPop

/-!
# seL4-MCS's `reply_pop` on a context no thread holds, each object written in its slot

The unheld pop (`returnUnheldSchedContextInPlace`: the context handed to the
popped reply's caller, the popped head's links cleared, the frame below
re-headed, the caller's binding rewritten), proven equal to the
specification's pop on every state whose checks pass
(`returnUnheldSchedContextResolved_eq_inPlace`), and the gate that reads those
checks on the pre-state as codes (`unheldPopsInPlace`).  A final delete of an
orphaned caller's head reply pops through it (`finaliseReplyUnheldPop`'s
compiled form, `IPC/Operations/CancelAll.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- **The unheld pop, in place** (seL4-MCS's `reply_pop` after
`schedContext_unbindTCB`): the context, bound to no thread, rebound to `owner`
with the frame below as its head, the popped head's links cleared, the frame
below re-headed, and `owner`'s binding the loan it is still owed (or its own
context at the bottom of the stack).  Every key the reschedule hook compares is
read before the first write, and the links it stores are the cells the head
already holds, so the pop builds nothing.  The identity where a read the
specification refuses on finds nothing (`returnUnheldSchedContextResolved_eq_inPlace`
states the states on which it is the specification's). -/
@[noinline] def returnUnheldSchedContextInPlace (st : SystemState)
    (owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) : SystemState :=
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
          let rprev := r.prev
          let rnext := r.next
          let outer := popOuterCode st r
          let op := ot.boostedPriority
          let od := effectiveDeadline st ot
          let odom := ot.domain
          let oe := hasSufficientBudget st ot
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
          markKeyChangeParts (markCandidacyGainFor s4 owner oe) owner op od odom

/-- **The unheld pop, in place**: on a state whose checks all pass — the context
bound to no thread and heading a stack at `hr`, the frame below (if any) linked
up to it with a caller, the outer caller and the recipient acceptable, the
recipient present — and whose writes each leave the object index and the types
alone at keys found in place, the resolved pop succeeds with
`returnUnheldSchedContextInPlace`'s state. -/
theorem returnUnheldSchedContextResolved_eq_inPlace (st : SystemState)
    (owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hr : SeLe4n.ReplyId) (r : Reply) (ot : TCB)
    (hSc : st.getSchedContext? scId = some sc) (hBT : sc.boundThreadCode = 0)
    (hHead : sc.scReply = some hr) (hR : st.getReply? hr = some r)
    (hNext : r.next = some (.head scId))
    (hBelow : ∀ b, r.prev = some b → b ≠ hr ∧ (∃ bR, st.getReply? b = some bR ∧
      bR.next = some (.frame hr) ∧ bR.callerCode ≠ 0) ∧
      storeLeavesIndexAndTypes st b.toObjId .reply = true ∧
      st.objects.findsInPlace b.toObjId = true)
    (hOuter : outerCallerAcceptable st owner owner
      (SeLe4n.ThreadId.ofOptCode (popOuterCode st r)) = true)
    (hRecip : donationRecipientAcceptable st owner = true)
    (hORes : owner.isReserved = false) (hOT : st.getTcb? owner = some ot)
    (hLsc : storeLeavesIndexAndTypes st scId.toObjId .schedContext = true)
    (hFsc : st.objects.findsInPlace scId.toObjId = true)
    (hLr : storeLeavesIndexAndTypes st hr.toObjId .reply = true)
    (hFr : st.objects.findsInPlace hr.toObjId = true)
    (hLo : storeLeavesIndexAndTypes st owner.toObjId .tcb = true) :
    returnUnheldSchedContextResolved st scId owner =
      .ok (returnUnheldSchedContextInPlace st owner scId) := by
  obtain ⟨hD, hRes⟩ := replyStackOuterCaller?_of_head st scId sc hr r hSc hHead hR hNext
    (fun b hb => (hBelow b hb).2.1)
  have hScO : st.objects[scId.toObjId]? = some (.schedContext sc) :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hRO : st.objects[hr.toObjId]? = some (.reply r) :=
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hOO : st.objects[owner.toObjId]? = some (.tcb ot) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hOT
  have hScR : scId.toObjId ≠ hr.toObjId := fun h => by rw [h, hRO] at hScO; cases hScO
  have hScOw : scId.toObjId ≠ owner.toObjId := fun h => by rw [h, hOO] at hScO; cases hScO
  have hROw : hr.toObjId ≠ owner.toObjId := fun h => by rw [h, hOO] at hRO; cases hRO
  have hBNe : (sc.boundThreadCode != 0) = false := by rw [hBT]; rfl
  have hIso : ∀ k : Nat, (SeLe4n.ThreadId.ofOptCode k).isNone = (k == 0) := by
    intro k; cases k <;> rfl
  have hLkO : ∀ s : SystemState, s.getTcb? owner = some ot → lookupTcb s owner = some ot :=
    fun s h => by unfold lookupTcb; rw [hORes]; exact h
  unfold returnUnheldSchedContextResolved
  rw [hRes]
  simp only []
  unfold returnUnheldSchedContext returnUnheldSchedContextInPlace
  rw [hSc]
  simp only [hBNe, hOuter, hRecip, hD, hHead, hR, hOT, Bool.not_true, Bool.false_eq_true,
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
  obtain ⟨T, hReHead, hEq3, hTO, hLTo⟩ : ∃ T,
      storeReplyReHead scId r.prev S2 = .ok T ∧
      (match r.prev with
        | none => S2
        | some b => S2.modifyObject b.toObjId
            (SystemState.mapReplyObject fun x => { x with next := r.next })) = T ∧
      T.objects[owner.toObjId]? = some (.tcb ot) ∧
      storeLeavesIndexAndTypes T owner.toObjId .tcb = true := by
    cases hP : r.prev with
    | none => exact ⟨S2, storeReplyReHead_none _ _, rfl, hTO2, hL2 hLo⟩
    | some b =>
      obtain ⟨hbNe, ⟨bR, hBR, _, _⟩, hLb, hFb⟩ := hBelow b hP
      have hBO : st.objects[b.toObjId]? = some (.reply bR) :=
        (SystemState.getReply?_eq_some_iff _ _ _).mp hBR
      have hRB : hr.toObjId ≠ b.toObjId :=
        fun h => hbNe (SeLe4n.ReplyId.toObjId_injective _ _ h).symm
      have hScB : scId.toObjId ≠ b.toObjId := fun h => by rw [h, hBO] at hScO; cases hScO
      have hBOw : b.toObjId ≠ owner.toObjId := fun h => by rw [h, hOO] at hBO; cases hBO
      have hB2 : S2.objects[b.toObjId]? = some (.reply bR) :=
        ((hO2 _ hRB).trans (hO1 _ hScB)).trans hBO
      have hFb2 := (hK2 _).trans hFb
      refine ⟨{ S2 with objects := S2.objects.insert b.toObjId (.reply { bR with next := some (.head scId) }) }, ?_, ?_, ?_, ?_⟩
      · rw [storeReplyReHead_some, (SystemState.getReply?_eq_some_iff _ _ _).mpr hB2]
        simp only []
        rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL2 hLb)]
      · show S2.modifyObject b.toObjId (SystemState.mapReplyObject fun x =>
            { x with next := r.next }) = _
        unfold SystemState.modifyObject
        rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? (by exact hB2), hNext]
        rfl
      · exact (RobinHood.RHTable.get?_insert_ne_of_findsInPlace _ _ hFb2 hBOw).trans hTO2
      · exact storeLeavesIndexAndTypes_insert_inPlace hFb2 (fun _ e => by cases e) (hL2 hLo)
  rw [hReHead, hEq3]
  simp only []
  have hTOt : T.getTcb? owner = some ot := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hTO
  rw [hLkO T hTOt]
  simp only []
  rw [hC1, hC2, storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLTo),
    SystemState.updateTcb_eq_of_some hTOt]
  simp only []
  rw [markKeyChangeFrom_of_getTcb st _ owner ot hOT]

/-- **A context no thread holds whose pop back to `c` may write in place**, read
on the pre-state: `c` an unreserved, unbound thread whose slot is local; the
context's slot local, the context bound to no thread and heading the stack of a
local reply that names it back; and the frame below that reply (if any) another
local reply linked up to it whose caller passes the pop's checks.  Every read is
a code, so the test builds nothing. -/
@[inline] def unheldPopsInPlace (st : SystemState) (scId : SeLe4n.SchedContextId)
    (c : SeLe4n.ThreadId) : Bool :=
  !c.isReserved && storeLeavesIndexAndTypes st c.toObjId .tcb &&
  storeLeavesIndexAndTypes st scId.toObjId .schedContext &&
  st.objects.findsInPlace scId.toObjId &&
  (match st.getTcb? c with
   | some ct => ct.scBindingScCode == 0
   | none => false) &&
  (match st.getSchedContext? scId with
   | some sc =>
     sc.boundThreadCode == 0 &&
     (match sc.scReply with
      | some rid =>
        storeLeavesIndexAndTypes st rid.toObjId .reply &&
        st.objects.findsInPlace rid.toObjId &&
        (match st.getReply? rid with
         | some rp =>
           (match rp.next with
            | some (.head s) => s.val == scId.val
            | _ => false) &&
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
                 bR.callerCode != 0 && outerCallerAcceptableCode st c c bR.callerCode
               | none => false))
         | none => false)
      | none => false)
   | none => false)

/-- **The gate's pop, on the state it reads**: under `unheldPopsInPlace` the
specification's commit test passes and its resolved pop commits with
`returnUnheldSchedContextInPlace`'s state. -/
theorem unheldPopsInPlace_pop (st : SystemState) (scId : SeLe4n.SchedContextId)
    (c : SeLe4n.ThreadId) (hG : unheldPopsInPlace st scId c = true) :
    unheldReturnCommits st scId c = true ∧
      returnUnheldSchedContextResolved st scId c =
        .ok (returnUnheldSchedContextInPlace st c scId) := by
  unfold unheldPopsInPlace at hG
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨hCRes, hLC⟩, hLsc⟩, hFsc⟩, hCm⟩, hM⟩ := hG
  cases hTg : st.getTcb? c with
  | none => rw [hTg] at hCm; cases hCm
  | some ct =>
  rw [hTg] at hCm
  have hCB : (ct.scBindingScCode == 0) = true := hCm
  cases hScg : st.getSchedContext? scId with
  | none => rw [hScg] at hM; cases hM
  | some sc =>
  rw [hScg] at hM
  dsimp only at hM
  simp only [Bool.and_eq_true] at hM
  obtain ⟨hBT, hM⟩ := hM
  cases hHd : sc.scReply with
  | none => rw [hHd] at hM; cases hM
  | some rid =>
  rw [hHd] at hM
  dsimp only at hM
  simp only [Bool.and_eq_true] at hM
  obtain ⟨⟨hLR, hFR⟩, hM⟩ := hM
  cases hRg : st.getReply? rid with
  | none => rw [hRg] at hM; cases hM
  | some rp =>
  rw [hRg] at hM
  dsimp only at hM
  simp only [Bool.and_eq_true] at hM
  obtain ⟨hNm, hBl⟩ := hM
  have hN : rp.next = some (.head scId) := by
    revert hNm
    cases rp.next with
    | none => intro h; cases h
    | some l =>
      cases l with
      | frame _ => intro h; cases h
      | head s =>
        intro e
        have : s = scId := by cases s; cases scId; simp only [beq_iff_eq] at e; subst e; rfl
        rw [this]
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
  have hOuter : outerCallerAcceptable st c c
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
  have hLk : lookupTcb st c = some ct := by unfold lookupTcb; rw [hCRes]; exact hTg
  have hRecip : donationRecipientAcceptable st c = true := by
    rw [donationRecipientAcceptable_eq_of_some st c _ hLk, TCB.schedContextBinding_beq_unbound]
    exact hCB
  have hBT0 : sc.boundThreadCode = 0 := by simpa using hBT
  obtain ⟨_, hRes⟩ := replyStackOuterCaller?_of_head st scId sc rid rp hScg hHd hRg hN
    (fun b hb => (hBelow b hb).2.1)
  refine ⟨?_, returnUnheldSchedContextResolved_eq_inPlace st c scId sc rid rp ct hScg hBT0 hHd hRg
    hN hBelow hOuter hRecip hCRes hTg hLsc hFsc hLR hFR hLC⟩
  unfold unheldReturnCommits
  rw [hRes, hScg]
  simp only [hBT0, beq_self_eq_true, hOuter, hRecip, hLk, Option.isSome_some, Bool.and_self]

/-- **`unheldReturnCommits` as compiled**: `true` at once where the in-place
pop's code checks pass (`unheldPopsInPlace`, which imply the specification's,
`unheldPopsInPlace_pop`); the specification's reads otherwise. -/
def unheldReturnCommitsImpl (st : SystemState) (scId : SeLe4n.SchedContextId)
    (owner : SeLe4n.ThreadId) : Bool :=
  unheldPopsInPlace st scId owner || unheldReturnCommits st scId owner

@[csimp] theorem unheldReturnCommits_eq_impl :
    @unheldReturnCommits = @unheldReturnCommitsImpl := by
  funext st scId owner
  unfold unheldReturnCommitsImpl
  cases hG : unheldPopsInPlace st scId owner with
  | false => rfl
  | true => rw [(unheldPopsInPlace_pop st scId owner hG).1]; rfl

end SeLe4n.Kernel
