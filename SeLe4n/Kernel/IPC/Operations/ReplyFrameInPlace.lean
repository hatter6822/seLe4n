/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations

/-!
# A reply frame cut off its stack, and a caller's reply link consumed, in place

The writes `cutReplyFrameOutOrSelf` and `consumeCallerReplyLink` make, each
object rewritten where it stands (`SystemState.storeReplyWith`,
`SystemState.storeTcbWith`), proven equal to the specification's stores
(`cutReplyFrameOutOrSelfInPlace_eq`, `consumeCallerReplyInPlace_eq`).  They sit
below the thread cancel (`Lifecycle.Suspend.cancelIpcBlocking`), whose reply
arm the suspend and the thread's and the reply's finalisation all run, so each
of them compiles through these writes.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The server a caller blocked on a reply waits for, as a code**: `0` for none,
`s + 1` for the server `s` (`TCB.blockingServer?`). -/
@[inline] def replyCallerServerCode (t : TCB) : Nat :=
  match t.blockingServer? with
  | some s => s.val + 1
  | none => 0

theorem ofOptCode_replyCallerServerCode (t : TCB) :
    SeLe4n.ThreadId.ofOptCode (replyCallerServerCode t) = t.blockingServer? := by
  unfold replyCallerServerCode
  cases t.blockingServer? <;> rfl


/-- A store whose key is found in place leaves every other key's object. -/
theorem storeObject_objects_ne_of_findsInPlace {st st' : SystemState} {id oid : SeLe4n.ObjId}
    {obj : KernelObject} (hF : st.objects.findsInPlace id = true) (hNe : id ≠ oid)
    (h : storeObject id obj st = .ok ((), st')) : st'.objects[oid]? = st.objects[oid]? := by
  unfold storeObject at h; cases h
  exact SeLe4n.Kernel.RobinHood.RHTable.get?_insert_ne_of_findsInPlace oid obj hF hNe

/-- ...and every in-place question. -/
theorem storeObject_findsInPlace_of_findsInPlace {st st' : SystemState} {id : SeLe4n.ObjId}
    {obj : KernelObject} (hF : st.objects.findsInPlace id = true)
    (h : storeObject id obj st = .ok ((), st')) (k : SeLe4n.ObjId) :
    st'.objects.findsInPlace k = st.objects.findsInPlace k := by
  unfold storeObject at h; cases h
  exact SeLe4n.Kernel.RobinHood.RHTable.findsInPlace_insert_of_findsInPlace k obj hF

/-- ...and reads back what it wrote at its own key. -/
theorem storeObject_objects_self_of_findsInPlace {st st' : SystemState} {id : SeLe4n.ObjId}
    {obj : KernelObject} (hF : st.objects.findsInPlace id = true)
    (h : storeObject id obj st = .ok ((), st')) : st'.objects[id]? = some obj := by
  unfold storeObject at h; cases h
  exact SeLe4n.Kernel.RobinHood.RHTable.get?_insert_self_of_findsInPlace obj hF

/-- **The cut from the frame below, as compiled**: the frame below's `next` and
the cut frame's `prev`, each written in its slot (`storeReplyWith`), with no
record rebuilt and no pre-state held.  The second write reads the cut frame
where the first left it, which is its pre-state record when the first key is
found in place; otherwise the specification's stores run. -/
@[inline] def severReplyFrameBelowStoresInPlace (st : SystemState) (rid below : SeLe4n.ReplyId)
    (r b : Reply) : SystemState :=
  if st.objects.findsInPlace below.toObjId then
    (st.storeReplyWith below.toObjId fun b => { b with next := none }).storeReplyWith
      rid.toObjId fun r => { r with prev := none }
  else
    match severReplyFrameBelowStores st rid below r b with
    | .ok st' => st'
    | .error _ => st

theorem severReplyFrameBelowStoresInPlace_eq {st : SystemState} {rid below : SeLe4n.ReplyId}
    {r b : Reply} (hR : st.objects[rid.toObjId]? = some (.reply r))
    (hB : st.objects[below.toObjId]? = some (.reply b)) (hNe : below.toObjId ≠ rid.toObjId) :
    severReplyFrameBelowStores st rid below r b = .ok (severReplyFrameBelowStoresInPlace st rid below r b) := by
  unfold severReplyFrameBelowStoresInPlace
  split
  · next hF =>
    have h1 := SystemState.storeObject_reply_eq_storeReplyWith hB (fun b => { b with next := none })
    have hR1 : (st.storeReplyWith below.toObjId fun b => { b with next := none }).objects[rid.toObjId]? =
        some (.reply r) := by
      rw [storeObject_objects_ne_of_findsInPlace hF hNe h1]; exact hR
    have h2 := SystemState.storeObject_reply_eq_storeReplyWith hR1 (fun r => { r with prev := none })
    unfold severReplyFrameBelowStores
    rw [h1]; dsimp only; rw [h2]
  · obtain ⟨s, hs⟩ := severReplyFrameBelowStores_isOk st rid below r b
    rw [hs]

/-- **The frame-above splice, as compiled**: the frame above's `prev`, the frame
below's `next` (when there is one) and the cut frame's two links, each written in
its slot (`storeReplyWith`).  Each later write reads its key where the earlier ones left
it, which is its pre-state record when the earlier keys are found in place;
otherwise the specification's stores run. -/
@[inline] def cutReplyFrameStoresInPlace (st : SystemState) (rid above : SeLe4n.ReplyId)
    (r a : Reply) : SystemState :=
  match cutFrameBelow? st rid r above with
  | none =>
    if st.objects.findsInPlace above.toObjId then
      (st.storeReplyWith above.toObjId fun a => a.unlinkedFrom rid).storeReplyWith
        rid.toObjId fun r => { r with prev := none, next := none }
    else
      match cutReplyFrameStores st rid above r a with
      | .ok st' => st'
      | .error _ => st
  | some (below, _) =>
    if st.objects.findsInPlace above.toObjId && st.objects.findsInPlace below.toObjId then
      ((st.storeReplyWith above.toObjId fun a => a.unlinkedFrom rid).storeReplyWith
        below.toObjId fun b => { b with next := none }).storeReplyWith
        rid.toObjId fun r => { r with prev := none, next := none }
    else
      match cutReplyFrameStores st rid above r a with
      | .ok st' => st'
      | .error _ => st

theorem cutReplyFrameStoresInPlace_eq {st : SystemState} {rid above : SeLe4n.ReplyId}
    {r a : Reply} (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (hA : st.getReply? above = some a) (hP : a.prev = some rid) :
    cutReplyFrameStores st rid above r a = .ok (cutReplyFrameStoresInPlace st rid above r a) := by
  have hAo := (SystemState.getReply?_eq_some_iff _ _ _).mp hA
  have hRo := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  unfold cutReplyFrameStoresInPlace
  cases hBelow : cutFrameBelow? st rid r above with
  | none =>
    dsimp only
    split
    · next hFA =>
      have h1 := SystemState.storeObject_reply_eq_storeReplyWith hAo (fun a => a.unlinkedFrom rid)
      generalize hS1 : st.storeReplyWith above.toObjId (fun a => a.unlinkedFrom rid) = s1 at h1
      have hR1 : s1.objects[rid.toObjId]? = some (.reply (r.unlinkedFrom rid)) ∨
          s1.objects[rid.toObjId]? = some (.reply r) := by
        by_cases hAR : above.toObjId = rid.toObjId
        · have hEq : above = rid := SeLe4n.ReplyId.toObjId_injective _ _ hAR
          subst hEq
          rw [hRo] at hAo
          have hra : r = a := KernelObject.reply.inj (Option.some.inj hAo)
          subst hra
          exact Or.inl (by rw [← hAR]; exact storeObject_objects_self_of_findsInPlace hFA h1)
        · exact Or.inr (by rw [storeObject_objects_ne_of_findsInPlace hFA hAR h1]; exact hRo)
      unfold cutReplyFrameStores
      rw [hBelow]; dsimp only
      rw [h1]; dsimp only
      rcases hR1 with hR1 | hR1
      · rw [← Reply.unlinkedFrom_clear r rid, SystemState.storeObject_reply_eq_storeReplyWith hR1
          (fun r => { r with prev := none, next := none })]
      · rw [SystemState.storeObject_reply_eq_storeReplyWith hR1
          (fun r => { r with prev := none, next := none })]
    · obtain ⟨s, hs⟩ := cutReplyFrameStores_isOk st rid above r a
      rw [hs]
  | some p =>
    obtain ⟨below, b⟩ := p
    dsimp only
    split
    · next hF =>
      rw [Bool.and_eq_true] at hF
      obtain ⟨hFA, hFB⟩ := hF
      obtain ⟨_, hNeBA, hB, _⟩ := cutFrameBelow?_eq_some hBelow
      have hBo := (SystemState.getReply?_eq_some_iff _ _ _).mp hB
      have hNeBR := cutFrameBelow?_ne_cut hR hN hBelow
      have hNeAR := cutFrameBelow?_above_ne_cut hR hA hP hBelow
      have hk : ∀ {x y : SeLe4n.ReplyId}, x ≠ y → x.toObjId ≠ y.toObjId :=
        fun h e => h (SeLe4n.ReplyId.toObjId_injective _ _ e)
      have h1 := SystemState.storeObject_reply_eq_storeReplyWith hAo
        (fun a => a.unlinkedFrom rid)
      generalize hS1 : st.storeReplyWith above.toObjId (fun a => a.unlinkedFrom rid) = s1
        at h1
      have hB1 : s1.objects[below.toObjId]? = some (.reply b) := by
        rw [storeObject_objects_ne_of_findsInPlace hFA (hk (Ne.symm hNeBA)) h1]; exact hBo
      have hR1 : s1.objects[rid.toObjId]? = some (.reply r) := by
        rw [storeObject_objects_ne_of_findsInPlace hFA (hk hNeAR) h1]; exact hRo
      have hFB1 : s1.objects.findsInPlace below.toObjId = true := by
        rw [storeObject_findsInPlace_of_findsInPlace hFA h1]; exact hFB
      have h2 := SystemState.storeObject_reply_eq_storeReplyWith hB1
        (fun b => { b with next := none })
      generalize hS2 : s1.storeReplyWith below.toObjId
        (fun b => { b with next := none }) = s2 at h2
      have hR2 : s2.objects[rid.toObjId]? = some (.reply r) := by
        rw [storeObject_objects_ne_of_findsInPlace hFB1 (hk hNeBR) h2]; exact hR1
      have h3 := SystemState.storeObject_reply_eq_storeReplyWith hR2
        (fun r => { r with prev := none, next := none })
      unfold cutReplyFrameStores
      rw [hBelow]; dsimp only
      rw [h1]; dsimp only; rw [h2]; dsimp only; rw [h3]
    · obtain ⟨s, hs⟩ := cutReplyFrameStores_isOk st rid above r a
      rw [hs]

/-- **The splice of a reply heading no stack, as compiled**: the same reads and
the same stores as `cutReplyFrameOutOrSelf`, with no `Except` cell on the
arms that write nothing (a reply linked to no frame either way, the busy reply's
case), and the frame-above splice and the cut from the frame below each writing
their links in their slots (`cutReplyFrameStoresInPlace`,
`severReplyFrameBelowStoresInPlace`). -/
@[inline] def cutReplyFrameOutOrSelfInPlace (st : SystemState) (rid : SeLe4n.ReplyId) :
    SystemState :=
  match st.getReply? rid with
  | none => st
  | some r =>
    match r.next with
    | some (.frame above) =>
      match st.getReply? above with
      | none => st
      | some a =>
        if a.prev != some rid then st
        else cutReplyFrameStoresInPlace st rid above r a
    | some (.head _) => st
    | none =>
      match r.prev with
      | none => st
      | some below =>
        match st.getReply? below with
        | none => st
        | some b =>
          if b.next != some (.frame rid) then st
          else severReplyFrameBelowStoresInPlace st rid below r b

theorem cutReplyFrameOutOrSelfInPlace_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    cutReplyFrameOutOrSelfInPlace st rid = cutReplyFrameOutOrSelf st rid := by
  unfold cutReplyFrameOutOrSelfInPlace cutReplyFrameOutOrSelf cutReplyFrameOut
  cases hR : st.getReply? rid with
  | none => rfl
  | some r =>
    dsimp only
    cases hN : r.next with
    | none =>
      dsimp only
      cases hPv : r.prev with
      | none => rfl
      | some below =>
        dsimp only
        cases hB : st.getReply? below with
        | none => rfl
        | some b =>
          dsimp only
          by_cases hBn : (b.next != some (.frame rid)) = true
          · simp only [hBn, ↓reduceIte]
          · simp only [hBn, Bool.false_eq_true, ↓reduceIte]
            have hBn' : b.next = some (.frame rid) := by simpa using hBn
            rw [severReplyFrameBelowStoresInPlace_eq ((SystemState.getReply?_eq_some_iff _ _ _).mp hR)
              ((SystemState.getReply?_eq_some_iff _ _ _).mp hB)
              (severReplyFrameBelow_ne hR hN hB hBn')]
    | some l =>
      cases l with
      | head _ => rfl
      | frame above =>
        dsimp only
        cases hA : st.getReply? above with
        | none => rfl
        | some a =>
          dsimp only
          by_cases hP : (a.prev != some rid) = true
          · simp only [hP, ↓reduceIte]
          · simp only [hP, Bool.false_eq_true, ↓reduceIte]
            have hP' : a.prev = some rid := by simpa using hP
            rw [cutReplyFrameStoresInPlace_eq hR hN hA hP']

/-- A reply's `prev` names `rid`, read off the link itself, so no `some` cell is
built to compare it with (`Reply.prevNames_eq`). -/
@[inline] def Reply.prevNames (a : Reply) (rid : SeLe4n.ReplyId) : Bool :=
  match a.prev with
  | some x => x == rid
  | none => false

theorem Reply.prevNames_eq (a : Reply) (rid : SeLe4n.ReplyId) :
    a.prevNames rid = !(a.prev != some rid) := by
  unfold Reply.prevNames
  cases a.prev with
  | none => rfl
  | some x => simp [bne]

/-- A reply's `next` is the frame link to `rid`, read off the link itself, so no
`some (.frame rid)` cells are built to compare it with
(`Reply.nextNamesFrame_eq`). -/
@[inline] def Reply.nextNamesFrame (b : Reply) (rid : SeLe4n.ReplyId) : Bool :=
  match b.next with
  | some (.frame x) => x == rid
  | _ => false

theorem Reply.nextNamesFrame_eq (b : Reply) (rid : SeLe4n.ReplyId) :
    b.nextNamesFrame rid = !(b.next != some (.frame rid)) := by
  unfold Reply.nextNamesFrame
  rcases b.next with _ | ⟨x⟩ | ⟨_⟩
  · rfl
  · by_cases h : x = rid
    · subst h; simp
    · have h1 : (x == rid) = false := by simpa using h
      have h2 : (some (ReplyStackLink.frame x) == some (.frame rid)) = false := by simpa using h
      simp [bne, h1, h2]
  · simp

/-- `cutFrameBelow?`'s question, answered as a test: the cut frame's `prev`
names a frame other than the one above that resolves and links up to the cut
frame.  Read off the links, so no cell is built for the answer
(`cutReplyFrameStoresInPlace_eq_impl`). -/
@[inline] def cutFrameBelowLinks (st : SystemState) (rid below above : SeLe4n.ReplyId) : Bool :=
  below != above &&
  (match st.getReply? below with
   | some b => b.nextNamesFrame rid
   | none => false)

/-- `cutReplyFrameStoresInPlace` as it is compiled: the frame below found from
the cut frame's own `prev` (`cutFrameBelowLinks`), so neither the comparison
with the frame link nor the resolved pair builds a cell. -/
@[inline] def cutReplyFrameStoresInPlaceImpl (st : SystemState) (rid above : SeLe4n.ReplyId)
    (r a : Reply) : SystemState :=
  match r.prev with
  | some below =>
    if cutFrameBelowLinks st rid below above then
      if st.objects.findsInPlace above.toObjId && st.objects.findsInPlace below.toObjId then
        ((st.storeReplyWith above.toObjId fun a => a.unlinkedFrom rid).storeReplyWith
          below.toObjId fun b => { b with next := none }).storeReplyWith
          rid.toObjId fun r => { r with prev := none, next := none }
      else
        match cutReplyFrameStores st rid above r a with
        | .ok st' => st'
        | .error _ => st
    else
      if st.objects.findsInPlace above.toObjId then
        (st.storeReplyWith above.toObjId fun a => a.unlinkedFrom rid).storeReplyWith
          rid.toObjId fun r => { r with prev := none, next := none }
      else
        match cutReplyFrameStores st rid above r a with
        | .ok st' => st'
        | .error _ => st
  | none =>
    if st.objects.findsInPlace above.toObjId then
      (st.storeReplyWith above.toObjId fun a => a.unlinkedFrom rid).storeReplyWith
        rid.toObjId fun r => { r with prev := none, next := none }
    else
      match cutReplyFrameStores st rid above r a with
      | .ok st' => st'
      | .error _ => st

@[csimp] theorem cutReplyFrameStoresInPlace_eq_impl :
    @cutReplyFrameStoresInPlace = @cutReplyFrameStoresInPlaceImpl := by
  funext st rid above r a
  unfold cutReplyFrameStoresInPlace cutReplyFrameStoresInPlaceImpl cutFrameBelow?
    cutFrameBelowLinks
  cases r.prev with
  | none => rfl
  | some below =>
    dsimp only
    cases hE : (below == above)
    · cases hB : st.getReply? below with
      | none => simp [bne, hE]
      | some b =>
        by_cases hN : b.next = some (.frame rid)
        · simp [bne, hE, hN, Reply.nextNamesFrame]
        · have hN' : b.nextNamesFrame rid = false := by
            rw [Reply.nextNamesFrame_eq]; simpa using hN
          simp [bne, hE, hN, hN']
    · simp [bne, hE]

/-- `cutReplyFrameOutOrSelfInPlace` as it is compiled: the reciprocity tests
read off the links (`Reply.prevNames`, `Reply.nextNamesFrame`), so no cell is
built to compare a link with. -/
@[inline] def cutReplyFrameOutOrSelfInPlaceImpl (st : SystemState) (rid : SeLe4n.ReplyId) :
    SystemState :=
  match st.getReply? rid with
  | none => st
  | some r =>
    match r.next with
    | some (.frame above) =>
      match st.getReply? above with
      | none => st
      | some a =>
        if a.prevNames rid then cutReplyFrameStoresInPlace st rid above r a
        else st
    | some (.head _) => st
    | none =>
      match r.prev with
      | none => st
      | some below =>
        match st.getReply? below with
        | none => st
        | some b =>
          if b.nextNamesFrame rid then severReplyFrameBelowStoresInPlace st rid below r b
          else st

@[csimp] theorem cutReplyFrameOutOrSelfInPlace_eq_impl :
    @cutReplyFrameOutOrSelfInPlace = @cutReplyFrameOutOrSelfInPlaceImpl := by
  funext st rid
  unfold cutReplyFrameOutOrSelfInPlace cutReplyFrameOutOrSelfInPlaceImpl
  simp only [Reply.prevNames_eq, Reply.nextNamesFrame_eq]
  rcases st.getReply? rid with _ | r
  · rfl
  · dsimp only
    rcases r.next with _ | ⟨above⟩ | ⟨_⟩
    · rcases r.prev with _ | below
      · rfl
      · dsimp only
        rcases st.getReply? below with _ | b
        · rfl
        · dsimp only
          cases (b.next != some (.frame rid)) <;> rfl
    · dsimp only
      rcases st.getReply? above with _ | a
      · rfl
      · dsimp only
        cases (a.prev != some rid) <;> rfl
    · rfl

/-- **A caller's reply link consumed, as compiled**: the reply's consumed record
and the caller's cleared link, each written in its slot (`storeReplyWith`,
`storeTcbWith`) — the stores `consumeCallerReplyLink` makes.  `storeTcbWith`
writes nothing to a slot holding no thread, as the link form's `getTcb?` arm
does. -/
@[inline] def consumeCallerReplyInPlace (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : SystemState :=
  (st.storeReplyWith rid.toObjId Reply.consumed).storeTcbWith c.toObjId
    fun tcb => { tcb with replyObjectCode := 0 }

theorem consumeCallerReplyInPlace_eq (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) :
    consumeCallerReplyInPlace st c rid = st.consumeCallerReplyLink c rid := by
  have hL := SystemState.consumeCallerReply_eq_link st c rid
  suffices hS : SystemState.consumeCallerReply c rid st = .ok ((), consumeCallerReplyInPlace st c rid) by
    rw [hS] at hL
    exact (Prod.mk.inj (Except.ok.inj hL)).2
  have hR : SystemState.consumeReply rid st = .ok ((), st.storeReplyWith rid.toObjId Reply.consumed) := by
    unfold SystemState.consumeReply
    cases hg : st.getReply? rid with
    | some r => exact SystemState.storeObject_reply_eq_storeReplyWith ((SystemState.getReply?_eq_some_iff _ _ _).mp hg) _
    | none =>
      show Except.ok ((), st) = _
      unfold SystemState.storeReplyWith
      cases ho : st.objects[rid.toObjId]? with
      | none => rfl
      | some o =>
        cases o with
        | reply r =>
          rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr ho] at hg; cases hg
        | _ => rfl
  unfold SystemState.consumeCallerReply consumeCallerReplyInPlace
  rw [hR]
  dsimp only
  generalize st.storeReplyWith rid.toObjId Reply.consumed = st1
  cases ht : st1.objects[c.toObjId]? with
  | none =>
    have : st1.getTcb? c = none := by unfold SystemState.getTcb?; rw [ht]
    rw [this]
    unfold SystemState.storeTcbWith; rw [ht]
  | some o =>
    cases o with
    | tcb t =>
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr ht]
      exact SystemState.storeObject_tcb_eq_storeTcbWith ht (fun tcb => { tcb with replyObjectCode := 0 })
    | _ =>
      have : st1.getTcb? c = none := by unfold SystemState.getTcb?; rw [ht]
      rw [this]
      unfold SystemState.storeTcbWith; rw [ht]

end SeLe4n.Kernel
