/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.DonationPopInPlace

/-!
# seL4-MCS's `reply_pop` at a held head whose recipient holds a context, each object written in its slot

The held pop (`keepDonatedSchedContextInPlace`: the head popped off the
context, the popped head's links cleared, the frame below re-headed, the
holder's binding rewritten to what it already holds or, on a loan, to the loan
owed one frame further up), proven equal to the specification's pop on every
state whose checks pass (`keepDonatedSchedContextResolved_eq_inPlace`), and the
gate that reads those checks on the pre-state as codes (`keptPopsInPlace`).
The held-head pop (`popHeldReplyHead`) and its commit test (`heldPopCommits`)
take it through `@[csimp]`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- The owner code the held pop leaves on a holder whose owner code is `own`,
the caller one frame below the popped head being `k`: a holder that owns the
context (`own = 0`) keeps owning it, as seL4 writes nothing to it; a holder
that has it on loan owes it to the caller below. -/
@[inline] def heldPopOwnerCode (own k : Nat) : Nat :=
  if own == 0 then 0 else k

/-- **The held pop, in place** (seL4-MCS's `reply_pop` where the recipient
holds a context of its own): the context's head moved to the frame below, the
popped head's links cleared, the frame below re-headed, and the holder's
binding the one `heldPopOwnerCode` reads.  The holder's scheduling key is the
one it had (it keeps the context its budget reads), so the pop marks nothing.
The links it stores are the cells the head already holds, so the pop builds
nothing.  The identity where a read the specification refuses on finds
nothing (`keepDonatedSchedContextResolved_eq_inPlace` states the states on
which it is the specification's). -/
@[noinline] def keepDonatedSchedContextInPlace (st : SystemState)
    (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) : SystemState :=
  match st.getSchedContext? scId with
  | none => st
  | some sc =>
    match sc.scReply with
    | none => st
    | some hr =>
      match st.getReply? hr with
      | none => st
      | some r =>
        match st.getTcb? holder with
        | none => st
        | some ht =>
          let rprev := r.prev
          let rnext := r.next
          let outer := popOuterCode st r
          let kept := heldPopOwnerCode ht.scBindingOwnerCode outer
          let s1 := st.updateSchedContext scId fun s =>
            { s with scReply := rprev,
                     donationOrigin := if outer == 0 then none else s.donationOrigin }
          let s2 := s1.modifyObject hr.toObjId
            (SystemState.mapReplyObject fun x => { x with prev := none, next := none })
          let s3 := match rprev with
            | none => s2
            | some b => s2.modifyObject b.toObjId
                (SystemState.mapReplyObject fun x => { x with next := rnext })
          s3.updateTcb holder fun t =>
            { t with scBindingScCode := scId.val + 1, scBindingOwnerCode := kept }

/-- The binding the held pop writes, as codes: on a holder whose context code
names `scId`, `heldPopOwner?` at the caller `k` is the caller `heldPopOwnerCode`
reads. -/
theorem heldPopOwner?_ofCodes (scId : SeLe4n.SchedContextId) (own k : Nat) :
    heldPopOwner? (SchedContextBinding.ofCodes (scId.val + 1) own) (SeLe4n.ThreadId.ofOptCode k) =
      SeLe4n.ThreadId.ofOptCode (heldPopOwnerCode own k) := by
  cases own <;> rfl

/-- **The held pop, in place**: on a state whose checks all pass — the context
held by `holder` and heading a stack at `hr`, the frame below (if any) linked up
to it with a caller, the outer caller acceptable, the holder present with a
binding that names the context — and whose writes each leave the object index
and the types alone at keys found in place, the resolved held pop succeeds with
`keepDonatedSchedContextInPlace`'s state. -/
theorem keepDonatedSchedContextResolved_eq_inPlace (st : SystemState)
    (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hr : SeLe4n.ReplyId) (r : Reply) (ht : TCB)
    (hSc : st.getSchedContext? scId = some sc) (hBT : sc.boundThread = some holder)
    (hHead : sc.scReply = some hr) (hR : st.getReply? hr = some r)
    (hNext : r.next = some (.head scId))
    (hBelow : ∀ b, r.prev = some b → b ≠ hr ∧ (∃ bR, st.getReply? b = some bR ∧
      bR.next = some (.frame hr) ∧ bR.callerCode ≠ 0) ∧
      storeLeavesIndexAndTypes st b.toObjId .reply = true ∧
      st.objects.findsInPlace b.toObjId = true)
    (hOuter : outerCallerAcceptable st holder holder
      (heldPopOuter? st holder (SeLe4n.ThreadId.ofOptCode (popOuterCode st r))) = true)
    (hHRes : holder.isReserved = false) (hHT : st.getTcb? holder = some ht)
    (hHB : ht.scBindingScCode = scId.val + 1)
    (hLsc : storeLeavesIndexAndTypes st scId.toObjId .schedContext = true)
    (hFsc : st.objects.findsInPlace scId.toObjId = true)
    (hLr : storeLeavesIndexAndTypes st hr.toObjId .reply = true)
    (hFr : st.objects.findsInPlace hr.toObjId = true)
    (hLh : storeLeavesIndexAndTypes st holder.toObjId .tcb = true) :
    keepDonatedSchedContextResolved st holder scId =
      .ok (keepDonatedSchedContextInPlace st holder scId) := by
  obtain ⟨hD, hRes⟩ := replyStackOuterCaller?_of_head st scId sc hr r hSc hHead hR hNext
    (fun b hb => (hBelow b hb).2.1)
  have hScO : st.objects[scId.toObjId]? = some (.schedContext sc) :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hRO : st.objects[hr.toObjId]? = some (.reply r) :=
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hHO : st.objects[holder.toObjId]? = some (.tcb ht) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hHT
  have hScR : scId.toObjId ≠ hr.toObjId := fun h => by rw [h, hRO] at hScO; cases hScO
  have hScH : scId.toObjId ≠ holder.toObjId := fun h => by rw [h, hHO] at hScO; cases hScO
  have hRH : hr.toObjId ≠ holder.toObjId := fun h => by rw [h, hHO] at hRO; cases hRO
  have hBNe : (sc.boundThread != some holder) = false := by rw [hBT]; simp
  have hIso : ∀ k : Nat, (SeLe4n.ThreadId.ofOptCode k).isNone = (k == 0) := by
    intro k; cases k <;> rfl
  have hLkH : ∀ s : SystemState, s.getTcb? holder = some ht → lookupTcb s holder = some ht :=
    fun s h => by unfold lookupTcb; rw [hHRes]; exact h
  have hBind : ht.schedContextBinding = SchedContextBinding.ofCodes (scId.val + 1)
      ht.scBindingOwnerCode := by
    unfold TCB.schedContextBinding; rw [hHB]
  have hScQ : (ht.schedContextBinding.scId? != some scId) = false := by
    rw [hBind]; unfold SchedContextBinding.ofCodes
    cases ht.scBindingOwnerCode <;> simp [SchedContextBinding.scId?]
  unfold keepDonatedSchedContextResolved
  rw [hRes]
  simp only []
  unfold keepDonatedSchedContext keepDonatedSchedContextInPlace
  rw [hSc]
  simp only [hBNe, hOuter, hD, hHead, hR, hHT, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Option.bind_some]
  generalize hk : popOuterCode st r = k at *
  obtain ⟨hC1, hC2⟩ := donationReturnBinding_ofOptCode_codes scId
    (heldPopOwnerCode ht.scBindingOwnerCode k)
  unfold donationSeverSchedContext
  rw [hIso k, storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLsc),
    SystemState.updateSchedContext_eq_of_some hSc]
  simp only []
  generalize hS1 : ({ st with objects := st.objects.insert scId.toObjId (.schedContext
    { sc with scReply := r.prev,
              donationOrigin := if (k == 0) = true then none else sc.donationOrigin }) } :
      SystemState) = S1
  have hO1 : ∀ x, scId.toObjId ≠ x → S1.objects[x]? = st.objects[x]? := fun x hx => by
    rw [← hS1]; exact RobinHood.RHTable.get?_insert_ne_of_findsInPlace x _ hFsc hx
  have hK1 : ∀ x, S1.objects.findsInPlace x = st.objects.findsInPlace x := fun x => by
    rw [← hS1]; exact RobinHood.RHTable.findsInPlace_insert_of_findsInPlace x _ hFsc
  have hL1 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes S1 id ty = true := fun h => by
    rw [← hS1]; exact storeLeavesIndexAndTypes_insert_inPlace_of_leaves hFsc (by simpa only [KernelObject.objectType] using hLsc) h
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
    rw [← hS2]; exact storeLeavesIndexAndTypes_insert_inPlace_of_leaves hFr1 (by simpa only [KernelObject.objectType] using hL1 hLr) (hL1 h)
  -- The frame below re-headed.
  have hTO2 : S2.objects[holder.toObjId]? = some (.tcb ht) :=
    ((hO2 _ hRH).trans (hO1 _ hScH)).trans hHO
  obtain ⟨T, hReHead, hEq3, hTO, hLTo⟩ : ∃ T,
      storeReplyReHead scId r.prev S2 = .ok T ∧
      (match r.prev with
        | none => S2
        | some b => S2.modifyObject b.toObjId
            (SystemState.mapReplyObject fun x => { x with next := r.next })) = T ∧
      T.objects[holder.toObjId]? = some (.tcb ht) ∧
      storeLeavesIndexAndTypes T holder.toObjId .tcb = true := by
    cases hP : r.prev with
    | none => exact ⟨S2, storeReplyReHead_none _ _, rfl, hTO2, hL2 hLh⟩
    | some b =>
      obtain ⟨hbNe, ⟨bR, hBR, _, _⟩, hLb, hFb⟩ := hBelow b hP
      have hBO : st.objects[b.toObjId]? = some (.reply bR) :=
        (SystemState.getReply?_eq_some_iff _ _ _).mp hBR
      have hRB : hr.toObjId ≠ b.toObjId :=
        fun h => hbNe (SeLe4n.ReplyId.toObjId_injective _ _ h).symm
      have hScB : scId.toObjId ≠ b.toObjId := fun h => by rw [h, hBO] at hScO; cases hScO
      have hBH : b.toObjId ≠ holder.toObjId := fun h => by rw [h, hHO] at hBO; cases hBO
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
      · exact (RobinHood.RHTable.get?_insert_ne_of_findsInPlace _ _ hFb2 hBH).trans hTO2
      · exact storeLeavesIndexAndTypes_insert_inPlace_of_leaves hFb2 (by simpa only [KernelObject.objectType] using hL2 hLb) (hL2 hLh)
  rw [hReHead, hEq3]
  simp only []
  have hTOt : T.getTcb? holder = some ht := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hTO
  rw [hLkH T hTOt]
  simp only [hScQ, Bool.false_eq_true, ↓reduceIte]
  rw [hBind, heldPopOwner?_ofCodes, hC1, hC2,
    storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLTo),
    SystemState.updateTcb_eq_of_some hTOt]

/-- The owner code `holder` holds (`0` where it is not stored): the code
`heldPopOwnerCode` reads, so the gate asks the pop's outer check of the caller
the pop records, as the specification does (`heldPopOuter?`). -/
@[inline] def heldHolderOwnerCode (st : SystemState) (holder : SeLe4n.ThreadId) : Nat :=
  match st.getTcb? holder with
  | some ht => ht.scBindingOwnerCode
  | none => 0

/-- **A held pop that may write in place**, read on the pre-state: `holder` an
unreserved thread whose slot is local and whose binding names the context; the
context's slot local, the context bound to `holder` and heading the stack of a
local reply that names it back; and the frame below that reply (if any) another
local reply linked up to it whose caller passes the pop's checks.  Every read is
a code, so the test builds nothing. -/
@[inline] def keptPopsInPlace (st : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) : Bool :=
  !holder.isReserved && storeLeavesIndexAndTypes st holder.toObjId .tcb &&
  storeLeavesIndexAndTypes st scId.toObjId .schedContext &&
  st.objects.findsInPlace scId.toObjId &&
  (match st.getTcb? holder with
   | some ht => ht.scBindingScCode == scId.val + 1
   | none => false) &&
  (match st.getSchedContext? scId with
   | some sc =>
     sc.boundThreadCode == holder.val + 1 &&
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
                 bR.callerCode != 0 && outerCallerAcceptableCode st holder holder
                   (heldPopOwnerCode (heldHolderOwnerCode st holder) bR.callerCode)
               | none => false))
         | none => false)
      | none => false)
   | none => false)

/-- **What the gate reads**: under `keptPopsInPlace` the context is bound to
`holder` and heads the stack of a reply that names it back, the frame below (if
any) links up to it with a caller the pop's outer check accepts (as a code), and
`holder`'s binding names the context, every write's slot local. -/
theorem keptPopsInPlace_spec (st : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hG : keptPopsInPlace st holder scId = true) :
    ∃ sc rid rp ht, st.getSchedContext? scId = some sc ∧ sc.boundThread = some holder ∧
      sc.scReply = some rid ∧ st.getReply? rid = some rp ∧ rp.next = some (.head scId) ∧
      (∀ b, rp.prev = some b → b ≠ rid ∧ (∃ bR, st.getReply? b = some bR ∧
        bR.next = some (.frame rid) ∧ bR.callerCode ≠ 0) ∧
        storeLeavesIndexAndTypes st b.toObjId .reply = true ∧
        st.objects.findsInPlace b.toObjId = true) ∧
      outerCallerAcceptableCode st holder holder
        (heldPopOwnerCode ht.scBindingOwnerCode (popOuterCode st rp)) = true ∧
      holder.isReserved = false ∧ st.getTcb? holder = some ht ∧
      ht.scBindingScCode = scId.val + 1 ∧
      storeLeavesIndexAndTypes st scId.toObjId .schedContext = true ∧
      st.objects.findsInPlace scId.toObjId = true ∧
      storeLeavesIndexAndTypes st rid.toObjId .reply = true ∧
      st.objects.findsInPlace rid.toObjId = true ∧
      storeLeavesIndexAndTypes st holder.toObjId .tcb = true := by
  unfold keptPopsInPlace at hG
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨hHRes, hLH⟩, hLsc⟩, hFsc⟩, hHm⟩, hM⟩ := hG
  cases hTg : st.getTcb? holder with
  | none => rw [hTg] at hHm; cases hHm
  | some ht =>
  rw [hTg] at hHm
  have hHB : ht.scBindingScCode = scId.val + 1 := beq_iff_eq.mp hHm
  cases hScg : st.getSchedContext? scId with
  | none => rw [hScg] at hM; cases hM
  | some sc =>
  rw [hScg] at hM
  dsimp only at hM
  simp only [Bool.and_eq_true] at hM
  obtain ⟨hBT, hM⟩ := hM
  have hB : sc.boundThread = some holder := by
    unfold SchedContext.boundThread; rw [beq_iff_eq.mp hBT]; rfl
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
  have hOuter : outerCallerAcceptableCode st holder holder
      (heldPopOwnerCode ht.scBindingOwnerCode (popOuterCode st rp)) = true := by
    unfold popOuterCode
    cases hP : rp.prev with
    | none => unfold heldPopOwnerCode; split <;> rfl
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
      simpa only [heldHolderOwnerCode, hTg] using hBm.2
  exact ⟨sc, rid, rp, ht, rfl, hB, hHd, hRg, hN, hBelow, hOuter, hHRes, rfl, hHB, hLsc, hFsc,
    hLR, hFR, hLH⟩

/-- **The gate's pop, on the state it reads**: under `keptPopsInPlace` the
specification's commit test passes and its resolved held pop commits with
`keepDonatedSchedContextInPlace`'s state. -/
theorem keptPopsInPlace_pop (st : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hG : keptPopsInPlace st holder scId = true) :
    keptPopCommits st holder scId = true ∧
      keepDonatedSchedContextResolved st holder scId =
        .ok (keepDonatedSchedContextInPlace st holder scId) := by
  obtain ⟨sc, rid, rp, ht, hScg, hB, hHd, hRg, hN, hBelow, hOuterC, hHRes, hTg, hHB, hLsc, hFsc,
    hLR, hFR, hLH⟩ := keptPopsInPlace_spec st holder scId hG
  have hOuter : outerCallerAcceptable st holder holder
      (heldPopOuter? st holder (SeLe4n.ThreadId.ofOptCode (popOuterCode st rp))) = true := by
    have hBind : ht.schedContextBinding = SchedContextBinding.ofCodes (scId.val + 1)
        ht.scBindingOwnerCode := by
      unfold TCB.schedContextBinding; rw [hHB]
    rw [heldPopOuter?_of_getTcb hTg, hBind, heldPopOwner?_ofCodes, ← outerCallerAcceptableCode_eq]
    exact hOuterC
  have hLk : lookupTcb st holder = some ht := by unfold lookupTcb; rw [hHRes]; exact hTg
  have hScQ : ht.schedContextBinding.scId? = some scId := by
    unfold TCB.schedContextBinding; rw [hHB]; unfold SchedContextBinding.ofCodes
    cases ht.scBindingOwnerCode <;> rfl
  obtain ⟨_, hRes⟩ := replyStackOuterCaller?_of_head st scId sc rid rp hScg hHd hRg hN
    (fun b hb => (hBelow b hb).2.1)
  refine ⟨?_, keepDonatedSchedContextResolved_eq_inPlace st holder scId sc rid rp ht hScg hB hHd
    hRg hN hBelow hOuter hHRes hTg hHB hLsc hFsc hLR hFR hLH⟩
  unfold keptPopCommits
  rw [hRes, hScg]
  simp only [hB, beq_self_eq_true, hOuter, hLk, Option.bind_some, hScQ, Bool.and_self]

/-- **`keptPopCommits` as compiled**: `true` at once where the in-place pop's
code checks pass (`keptPopsInPlace`, which imply the specification's,
`keptPopsInPlace_pop`); the specification's reads otherwise. -/
def keptPopCommitsImpl (st : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) : Bool :=
  keptPopsInPlace st holder scId || keptPopCommits st holder scId

@[csimp] theorem keptPopCommits_eq_impl : @keptPopCommits = @keptPopCommitsImpl := by
  funext st holder scId
  unfold keptPopCommitsImpl
  cases hG : keptPopsInPlace st holder scId with
  | false => rfl
  | true => rw [(keptPopsInPlace_pop st holder scId hG).1]; rfl

/-- **The resolved held pop, as compiled**: in place where `keptPopsInPlace`
admits it, every check read as a code before the first write; the
specification's held pop otherwise.  Not `@[inline]`: it names the constant it
replaces, so it is compiled once, before the `@[csimp]` below, and that call
stays the specification's. -/
def keepDonatedSchedContextResolvedImpl (st : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) : Except KernelError SystemState :=
  if keptPopsInPlace st holder scId then .ok (keepDonatedSchedContextInPlace st holder scId)
  else keepDonatedSchedContextResolved st holder scId

@[csimp] theorem keepDonatedSchedContextResolved_eq_impl :
    @keepDonatedSchedContextResolved = @keepDonatedSchedContextResolvedImpl := by
  funext st holder scId
  unfold keepDonatedSchedContextResolvedImpl
  cases hG : keptPopsInPlace st holder scId with
  | false => rfl
  | true => simp only [(keptPopsInPlace_pop st holder scId hG).2, ↓reduceIte]

/-- **The held-head pop, as compiled**: the router as specified, compiled after
`keepDonatedSchedContextResolved_eq_impl`, so its held arm is the held pop in
place where `keptPopsInPlace` admits it. -/
def popHeldReplyHeadImpl (st : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (recipient : SeLe4n.ThreadId) :
    Except KernelError SystemState :=
  if donationRecipientAcceptable st recipient then
    returnDonatedSchedContextResolved st holder scId recipient
  else keepDonatedSchedContextResolved st holder scId

@[csimp] theorem popHeldReplyHead_eq_impl : @popHeldReplyHead = @popHeldReplyHeadImpl := by
  funext st holder scId recipient
  rfl

/-- **The held-head pop's commit test, as compiled**: the router's own test
picks the arm, compiled after `keptPopCommits_eq_impl` and
`donatedReturnCommits_eq_impl`, so each arm asks its in-place gate first. -/
def heldPopCommitsImpl (st : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (recipient : SeLe4n.ThreadId) : Bool :=
  if donationRecipientAcceptable st recipient then donatedReturnCommits st holder scId recipient
  else keptPopCommits st holder scId

@[csimp] theorem heldPopCommits_eq_impl : @heldPopCommits = @heldPopCommitsImpl := by
  funext st holder scId recipient
  rfl

end SeLe4n.Kernel
