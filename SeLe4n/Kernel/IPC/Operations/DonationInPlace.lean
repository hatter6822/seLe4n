/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.Endpoint

/-!
# A Call's donation, each object written in its slot

The writes `donateSchedContext` makes (seL4-MCS's `schedContext_donate` and
`reply_push`), each object rewritten where it stands, on a state whose checks
all pass (`donateSchedContext_eq_inPlace`): the lent context rebound to the
server with the donor's reply as its head, that reply linked onto the stack,
the frame below linked up to it, the donor's binding cleared and the server's
set.  Every key the reschedule hook compares is read before the first write,
so nothing holds the state the writes rewrite, and the links the push stores
are the cells the objects were built with (`SeLe4n.reuseSome`), so the push
builds none.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Whether a donor lends a context it owns (`donationFirstPush`), read from its
binding's codes, so the test builds no binding and no `some`. -/
@[inline] def donationFirstPushCode (donor : TCB) (scId : SeLe4n.SchedContextId) : Bool :=
  donor.scBindingScCode == scId.val + 1 && donor.scBindingOwnerCode == 0

theorem donationFirstPushCode_eq (donor : TCB) (scId : SeLe4n.SchedContextId) :
    donationFirstPushCode donor scId = donationFirstPush donor scId := by
  unfold donationFirstPushCode donationFirstPush
  show _ = ((SchedContextBinding.ofCodes donor.scBindingScCode
    donor.scBindingOwnerCode).ownScId? == some scId)
  cases h1 : donor.scBindingScCode with
  | zero => simp [SchedContextBinding.ofCodes, SchedContextBinding.ownScId?]
  | succ s =>
    cases h2 : donor.scBindingOwnerCode with
    | zero =>
      obtain ⟨v⟩ := scId
      simp only [SchedContextBinding.ofCodes, SchedContextBinding.ownScId?, beq_self_eq_true,
        Bool.and_true]
      by_cases h : s = v
      · subst h; simp
      · have hne : ({ val := s } : SeLe4n.SchedContextId) ≠ { val := v } :=
          fun e => h (by cases e; rfl)
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
        exact ⟨fun e => absurd (Nat.succ.inj e) h,
          fun e => absurd (Option.some.inj e) hne⟩
    | succ o => simp [SchedContextBinding.ofCodes, SchedContextBinding.ownScId?]

/-- **The donation push, in place.**  `donateSchedContext`'s writes on a state
whose checks pass: the identity where a read the specification refuses on finds
nothing (`donateSchedContext_eq_inPlace` states the states on which it is the
specification's). -/
@[noinline] def donateSchedContextInPlace (st : SystemState) (client server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) : SystemState :=
  match st.getSchedContext? scId with
  | none => st
  | some sc =>
    match lookupTcb st client with
    | none => st
    | some donor =>
      match donor.replyObjectCode with
      | 0 => st
      | k + 1 =>
        match st.getReply? ⟨k⟩ with
        | none => st
        | some pr =>
          match st.getTcb? server with
          | none => st
          | some srv =>
            let rid : SeLe4n.ReplyId := ⟨k⟩
            let below := sc.scReply
            let headC := ReplyStackLink.reuseHead sc.headLinkCell scId
            let ridC := SeLe4n.reuseSome pr.idCell rid
            let frameC := ReplyStackLink.reuseFrame pr.frameLinkCell rid
            let first := donationFirstPushCode donor scId
            let originC := SeLe4n.reuseSome donor.idCell client
            let cp := donor.boostedPriority
            let cd := effectiveDeadline st donor
            let cdom := donor.domain
            let ce := hasSufficientBudget st donor
            let sp := srv.boostedPriority
            let sd := effectiveDeadline st srv
            let sdom := srv.domain
            let se := hasSufficientBudget st srv
            let s1 := st.updateSchedContext scId fun s =>
              { s with boundThreadCode := SeLe4n.ThreadId.optCode (some server), scReply := ridC,
                       donationOrigin := if first then originC else s.donationOrigin }
            let s2 := s1.modifyObject rid.toObjId
              (SystemState.mapReplyObject fun r => { r with prev := below, next := headC })
            let s3 := match below with
              | none => s2
              | some old => s2.modifyObject old.toObjId
                  (SystemState.mapReplyObject fun r => { r with next := frameC })
            let s4 := s3.updateTcb client fun t =>
              { t with scBindingScCode := 0, scBindingOwnerCode := 0,
                       originScCode := if first then scId.val + 1 else t.originScCode }
            let s5 := s4.updateTcb server fun t =>
              { t with
                scBindingScCode := SchedContextBinding.scCode (.donated scId client),
                scBindingOwnerCode := SchedContextBinding.ownerCode (.donated scId client) }
            markKeyChangeParts (markCandidacyGainFor (markKeyChangeParts
              (markCandidacyGainFor s5 client ce) client cp cd cdom) server se) server sp sd sdom

/-- The push frame a donor's own free reply resolves to. -/
theorem donationPushFrame?_of (st : SystemState) (donor : TCB) (rid : SeLe4n.ReplyId) (pr : Reply)
    (hRO : donor.replyObject = some rid) (hR : st.getReply? rid = some pr)
    (hPrev : pr.prev = none) (hNext : pr.next = none) (hCaller : pr.caller ≠ none) :
    donationPushFrame? st donor = .ok (rid, pr) := by
  unfold donationPushFrame?
  rw [hRO]
  simp only [hR, hPrev, hNext, Option.isSome_none, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  cases hc : pr.caller with
  | none => exact absurd hc hCaller
  | some c => rfl

/-- The key hook of a thread found in the pre-state, its key read before the
writes (`markKeyChangeFor_eq_parts`). -/
theorem markKeyChangeFrom_of_getTcb (pre post : SystemState) (tid : SeLe4n.ThreadId) (t : TCB)
    (h : pre.getTcb? tid = some t) :
    markKeyChangeFrom pre post tid =
      markKeyChangeParts (markCandidacyGainFor post tid (hasSufficientBudget pre t)) tid
        t.boostedPriority (effectiveDeadline pre t) t.domain := by
  unfold markKeyChangeFrom
  rw [h]
  dsimp only
  rw [markKeyChangeFor_eq_parts, effectiveSchedParams_eq_parts]

/-- **The donation, in place**: on a state whose checks all pass — the context
held by the donor, the donor's own reply free and not already the context's
head, a frame below that resolves, both threads present — and whose writes each
leave the object index and the types alone at keys found in place,
`donateSchedContext` succeeds with `donateSchedContextInPlace`'s state. -/
theorem donateSchedContext_eq_inPlace (st : SystemState) (client server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (donor srv : TCB)
    (rid : SeLe4n.ReplyId) (pr : Reply)
    (hSc : st.getSchedContext? scId = some sc) (hB : sc.boundThread = some client)
    (hC : lookupTcb st client = some donor) (hRO : donor.replyObject = some rid)
    (hR : st.getReply? rid = some pr) (hPrev : pr.prev = none) (hNext : pr.next = none)
    (hCaller : pr.caller ≠ none) (hNe : sc.scReply ≠ some rid)
    (hOld : ∀ old, sc.scReply = some old →
      (∃ oR, st.getReply? old = some oR) ∧
      storeLeavesIndexAndTypes st old.toObjId .reply = true ∧
      st.objects.findsInPlace old.toObjId = true)
    (hS : st.getTcb? server = some srv) (hSRes : server.isReserved = false)
    (hLsc : storeLeavesIndexAndTypes st scId.toObjId .schedContext = true)
    (hFsc : st.objects.findsInPlace scId.toObjId = true)
    (hLr : storeLeavesIndexAndTypes st rid.toObjId .reply = true)
    (hFr : st.objects.findsInPlace rid.toObjId = true)
    (hLc : storeLeavesIndexAndTypes st client.toObjId .tcb = true)
    (hFc : st.objects.findsInPlace client.toObjId = true)
    (hLs : storeLeavesIndexAndTypes st server.toObjId .tcb = true) :
    donateSchedContext st client server scId =
      .ok (donateSchedContextInPlace st client server scId) := by
  have hScO : st.objects[scId.toObjId]? = some (.schedContext sc) :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hRO' : st.objects[rid.toObjId]? = some (.reply pr) :=
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hCRes : client.isReserved = false := by
    unfold lookupTcb at hC
    cases h : client.isReserved
    · rfl
    · rw [h] at hC; cases hC
  have hCT : st.getTcb? client = some donor := by
    unfold lookupTcb at hC; rw [hCRes] at hC; exact hC
  have hCO : st.objects[client.toObjId]? = some (.tcb donor) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hCT
  have hSO : st.objects[server.toObjId]? = some (.tcb srv) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hS
  have hScR : scId.toObjId ≠ rid.toObjId := fun h => by rw [h, hRO'] at hScO; cases hScO
  have hScC : scId.toObjId ≠ client.toObjId := fun h => by rw [h, hCO] at hScO; cases hScO
  have hRC : rid.toObjId ≠ client.toObjId := fun h => by rw [h, hCO] at hRO'; cases hRO'
  have hk : donor.replyObjectCode = rid.val + 1 :=
    (SeLe4n.ReplyId.ofOptCode_eq_some_iff _ _).mp hRO
  have hBNe : (sc.boundThread != some client) = false := by rw [hB]; exact bne_self_eq_false _
  have hHNe : (sc.scReply == some rid) = false := by
    cases h : sc.scReply with
    | none => rfl
    | some o =>
      rw [h] at hNe
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact hNe
  have hFirst : ∀ p, donorOriginCode donor scId p =
      if donationFirstPush donor scId then scId.val + 1 else p := fun _ => rfl
  -- The two sides, read off.
  unfold donateSchedContextInPlace donateSchedContext
  rw [hSc]
  dsimp only
  rw [hBNe, hC]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [donationPushFrame?_of st donor rid pr hRO hR hPrev hNext hCaller, hk]
  dsimp only
  rw [show (⟨rid.val⟩ : SeLe4n.ReplyId) = rid from rfl, hR, hS]
  dsimp only
  simp only [SeLe4n.reuseSome_eq, ReplyStackLink.reuseHead_eq, ReplyStackLink.reuseFrame_eq,
    donationFirstPushCode_eq]
  -- The context's store.
  rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLsc),
    SystemState.updateSchedContext_eq_of_some hSc]
  dsimp only
  unfold storeDonationFramePush
  rw [hHNe]
  simp only [Bool.false_eq_true, ↓reduceIte]
  generalize hS1 : ({ st with objects := st.objects.insert scId.toObjId (.schedContext
    { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some server), scReply := some rid,
              donationOrigin := if donationFirstPush donor scId then some client
                else sc.donationOrigin }) } : SystemState) = S1
  have hO1 : ∀ k, scId.toObjId ≠ k → S1.objects[k]? = st.objects[k]? := fun k hk' => by
    rw [← hS1]; exact RobinHood.RHTable.get?_insert_ne_of_findsInPlace k _ hFsc hk'
  have hK1 : ∀ k, S1.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
    rw [← hS1]; exact RobinHood.RHTable.findsInPlace_insert_of_findsInPlace k _ hFsc
  have hL1 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes S1 id ty = true := fun h => by
    rw [← hS1]; exact storeLeavesIndexAndTypes_insert_inPlace_of_leaves hFsc (by simpa only [KernelObject.objectType] using hLsc) h
  -- The pushed frame's store.
  have hR1 : S1.objects[rid.toObjId]? = some (.reply pr) := (hO1 _ hScR).trans hRO'
  rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL1 hLr)]
  dsimp only
  have hM2 : S1.modifyObject rid.toObjId (SystemState.mapReplyObject fun r =>
        { r with prev := sc.scReply, next := some (.head scId) }) =
      { S1 with objects := S1.objects.insert rid.toObjId (.reply { pr with prev := sc.scReply, next := some (.head scId) }) } := by
    unfold SystemState.modifyObject
    rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? (by exact hR1)]
    rfl
  rw [hM2]
  have hFr1 := (hK1 _).trans hFr
  generalize hS2 : ({ S1 with objects := S1.objects.insert rid.toObjId (.reply { pr with prev := sc.scReply, next := some (.head scId) }) } : SystemState) = S2
  have hO2 : ∀ k, rid.toObjId ≠ k → S2.objects[k]? = S1.objects[k]? := fun k hk' => by
    rw [← hS2]; exact RobinHood.RHTable.get?_insert_ne_of_findsInPlace k _ hFr1 hk'
  have hK2 : ∀ k, S2.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
    rw [← hS2]; exact (RobinHood.RHTable.findsInPlace_insert_of_findsInPlace k _ hFr1).trans (hK1 k)
  have hL2 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes S2 id ty = true := fun h => by
    rw [← hS2]; exact storeLeavesIndexAndTypes_insert_inPlace_of_leaves hFr1 (by simpa only [KernelObject.objectType] using hL1 hLr) (hL1 h)
  have hScS : scId.toObjId ≠ server.toObjId := fun h => by rw [h, hSO] at hScO; cases hScO
  have hRS : rid.toObjId ≠ server.toObjId := fun h => by rw [h, hSO] at hRO'; cases hRO'
  cases hBelow : sc.scReply with
  | none =>
    dsimp only
    have hTC : S2.objects[client.toObjId]? = some (.tcb donor) :=
      ((hO2 _ hRC).trans (hO1 _ hScC)).trans hCO
    have hTS : S2.objects[server.toObjId]? = some (.tcb srv) :=
      ((hO2 _ hRS).trans (hO1 _ hScS)).trans hSO
    have hFTc := (hK2 _).trans hFc
    have hLTc := hL2 hLc
    have hLTs := hL2 hLs
    generalize S2 = T at hTC hTS hFTc hLTc hLTs ⊢
    have hLk : lookupTcb T client = some donor := by
      unfold lookupTcb; rw [hCRes]; exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC
    rw [hLk]
    dsimp only
    simp only [hFirst]
    rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLTc),
      SystemState.updateTcb_eq_of_some ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC)]
    dsimp only
    generalize hT3 : ({ T with objects := T.objects.insert client.toObjId (.tcb
      { donor with scBindingScCode := 0, scBindingOwnerCode := 0,
                   originScCode := if donationFirstPush donor scId then scId.val + 1
                     else donor.originScCode }) } : SystemState) = T3
    obtain ⟨x, hX⟩ : ∃ x, T3.objects[server.toObjId]? = some (.tcb x) := by
      by_cases hEq : client.toObjId = server.toObjId
      · rw [← hEq, ← hT3]
        exact ⟨_, RobinHood.RHTable.get?_insert_self_of_findsInPlace _ hFTc⟩
      · rw [← hT3]
        exact ⟨srv, (RobinHood.RHTable.get?_insert_ne_of_findsInPlace _ _ hFTc hEq).trans hTS⟩
    have hXT : T3.getTcb? server = some x := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hX
    have hLk3 : lookupTcb T3 server = some x := by
      unfold lookupTcb; rw [hSRes]; exact hXT
    have hLT3 : storeLeavesIndexAndTypes T3 server.toObjId .tcb = true := by
      rw [← hT3]; exact storeLeavesIndexAndTypes_insert_inPlace_of_leaves hFTc (by simpa only [KernelObject.objectType] using hLTc) hLTs
    rw [hLk3]
    dsimp only
    rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLT3),
      SystemState.updateTcb_eq_of_some hXT]
    dsimp only
    rw [markKeyChangeFrom_of_getTcb st _ client donor hCT,
      markKeyChangeFrom_of_getTcb st _ server srv hS]
  | some old =>
    dsimp only
    obtain ⟨⟨oR, hOR⟩, hLo, hFo⟩ := hOld old hBelow
    have hORO : st.objects[old.toObjId]? = some (.reply oR) :=
      (SystemState.getReply?_eq_some_iff _ _ _).mp hOR
    have hOldNe : old ≠ rid := fun h => hNe (by rw [hBelow, h])
    have hRQ : rid.toObjId ≠ old.toObjId := fun h => hOldNe (SeLe4n.ReplyId.toObjId_injective _ _ h).symm
    have hScQ : scId.toObjId ≠ old.toObjId := fun h => by rw [h, hORO] at hScO; cases hScO
    have hQC : old.toObjId ≠ client.toObjId := fun h => by rw [h, hCO] at hORO; cases hORO
    have hQS : old.toObjId ≠ server.toObjId := fun h => by rw [h, hSO] at hORO; cases hORO
    have hO2q : S2.objects[old.toObjId]? = some (.reply oR) :=
      ((hO2 _ hRQ).trans (hO1 _ hScQ)).trans hORO
    have hR2q : S2.getReply? old = some oR := (SystemState.getReply?_eq_some_iff _ _ _).mpr hO2q
    rw [hR2q]
    dsimp only
    rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL2 hLo)]
    dsimp only
    have hM3 : S2.modifyObject old.toObjId (SystemState.mapReplyObject fun r =>
          { r with next := some (.frame rid) }) =
        { S2 with objects := S2.objects.insert old.toObjId (.reply { oR with next := some (.frame rid) }) } := by
      unfold SystemState.modifyObject
      rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? (by exact hO2q)]
      rfl
    rw [hM3]
    have hFo2 := (hK2 _).trans hFo
    have hTC : ({ S2 with objects := S2.objects.insert old.toObjId (.reply { oR with next := some (.frame rid) }) } : SystemState).objects[client.toObjId]? =
          some (.tcb donor) :=
      (RobinHood.RHTable.get?_insert_ne_of_findsInPlace _ _ hFo2 hQC).trans
        (((hO2 _ hRC).trans (hO1 _ hScC)).trans hCO)
    have hTS : ({ S2 with objects := S2.objects.insert old.toObjId (.reply { oR with next := some (.frame rid) }) } : SystemState).objects[server.toObjId]? =
          some (.tcb srv) :=
      (RobinHood.RHTable.get?_insert_ne_of_findsInPlace _ _ hFo2 hQS).trans
        (((hO2 _ hRS).trans (hO1 _ hScS)).trans hSO)
    have hFTc : ({ S2 with objects := S2.objects.insert old.toObjId (.reply { oR with next := some (.frame rid) }) } : SystemState).objects.findsInPlace
          client.toObjId = true :=
      (RobinHood.RHTable.findsInPlace_insert_of_findsInPlace _ _ hFo2).trans ((hK2 _).trans hFc)
    have hLTc : storeLeavesIndexAndTypes ({ S2 with objects := S2.objects.insert old.toObjId (.reply { oR with next := some (.frame rid) }) } : SystemState) client.toObjId .tcb = true :=
      storeLeavesIndexAndTypes_insert_inPlace_of_leaves hFo2 (by simpa only [KernelObject.objectType] using hL2 hLo) (hL2 hLc)
    have hLTs : storeLeavesIndexAndTypes ({ S2 with objects := S2.objects.insert old.toObjId (.reply { oR with next := some (.frame rid) }) } : SystemState) server.toObjId .tcb = true :=
      storeLeavesIndexAndTypes_insert_inPlace_of_leaves hFo2 (by simpa only [KernelObject.objectType] using hL2 hLo) (hL2 hLs)
    generalize ({ S2 with objects := S2.objects.insert old.toObjId (.reply { oR with next := some (.frame rid) }) } : SystemState) = T
      at hTC hTS hFTc hLTc hLTs ⊢
    have hLk : lookupTcb T client = some donor := by
      unfold lookupTcb; rw [hCRes]; exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC
    rw [hLk]
    dsimp only
    simp only [hFirst]
    rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLTc),
      SystemState.updateTcb_eq_of_some ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC)]
    dsimp only
    generalize hT3 : ({ T with objects := T.objects.insert client.toObjId (.tcb
      { donor with scBindingScCode := 0, scBindingOwnerCode := 0,
                   originScCode := if donationFirstPush donor scId then scId.val + 1
                     else donor.originScCode }) } : SystemState) = T3
    obtain ⟨x, hX⟩ : ∃ x, T3.objects[server.toObjId]? = some (.tcb x) := by
      by_cases hEq : client.toObjId = server.toObjId
      · rw [← hEq, ← hT3]
        exact ⟨_, RobinHood.RHTable.get?_insert_self_of_findsInPlace _ hFTc⟩
      · rw [← hT3]
        exact ⟨srv, (RobinHood.RHTable.get?_insert_ne_of_findsInPlace _ _ hFTc hEq).trans hTS⟩
    have hXT : T3.getTcb? server = some x := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hX
    have hLk3 : lookupTcb T3 server = some x := by
      unfold lookupTcb; rw [hSRes]; exact hXT
    have hLT3 : storeLeavesIndexAndTypes T3 server.toObjId .tcb = true := by
      rw [← hT3]; exact storeLeavesIndexAndTypes_insert_inPlace_of_leaves hFTc (by simpa only [KernelObject.objectType] using hLTc) hLTs
    rw [hLk3]
    dsimp only
    rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLT3),
      SystemState.updateTcb_eq_of_some hXT]
    dsimp only
    rw [markKeyChangeFrom_of_getTcb st _ client donor hCT,
      markKeyChangeFrom_of_getTcb st _ server srv hS]
