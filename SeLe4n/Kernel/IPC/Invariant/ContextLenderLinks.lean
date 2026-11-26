-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.ContextLenderSites
import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.CrossCore.FaultReceiveInPlace

/-!
# The lenders across the writers that link a caller

WS-SX SX8 (D27): every writer that links a caller into a reply object owes a
lender result, whatever it does to the donation chain (`ReplyStackWriteCensus`
derives the set from what each writer writes).  A caller is linked only on a
reply object that is free (`Reply.isFree`: no caller, no link up or down), and
under `donationChainWellFormed` a free reply object is on no context's stack
(`not_onContextStack_of_next_none`), so the link adds no lender.

The writers around the link store thread records, endpoints and the scheduler,
none of which holds a stack view.  `chainObjectsKept` is that fact read off the
object store — every reply object and every context after the step was there
before it, field for field — and it is what lets a freeness the link checks at
its own state be read back at the writer's pre-state, where the chain holds.
`contextStackLinksShrinkOff` is the links shrink with one reply object's caller
left free: the link itself.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-! ### The two relations -/

/-- **Every reply object and every context after the step was there before
it**: the step wrote neither kind. -/
structure chainObjectsKept (st st' : SystemState) : Prop where
  reply : ∀ (x : SeLe4n.ObjId) (r : Reply),
    st'.objects[x]? = some (.reply r) → st.objects[x]? = some (.reply r)
  schedContext : ∀ (x : SeLe4n.ObjId) (sc : SchedContext),
    st'.objects[x]? = some (.schedContext sc) → st.objects[x]? = some (.schedContext sc)
  /-- Every thread's and notification's binding word after the step was there
  before it (a context's is kept with the context). -/
  binding : bindingViewsShrink st st'

namespace chainObjectsKept

theorem refl (st : SystemState) : chainObjectsKept st st :=
  ⟨fun _ _ h => h, fun _ _ h => h, .refl st⟩

theorem trans {st st' st'' : SystemState} (h1 : chainObjectsKept st st')
    (h2 : chainObjectsKept st' st'') : chainObjectsKept st st'' :=
  ⟨fun x r h => h1.reply x r (h2.reply x r h), fun x sc h => h1.schedContext x sc (h2.schedContext x sc h),
   h1.binding.trans h2.binding⟩

theorem of_eq {st st' : SystemState} (h : st' = st) : chainObjectsKept st st' := h ▸ refl st

/-- The relation reads the object store alone. -/
theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    chainObjectsKept st st' :=
  ⟨fun x r hx => by rw [h] at hx; exact hx, fun x sc hx => by rw [h] at hx; exact hx,
   .of_objects_eq h⟩

/-- **Read off the kept reply objects and contexts and the unchanged binding
words**: the form a step summarised slot by slot takes. -/
theorem of_words {st st' : SystemState}
    (hR : ∀ (x : SeLe4n.ObjId) (r : Reply),
      st'.objects[x]? = some (.reply r) → st.objects[x]? = some (.reply r))
    (hS : ∀ (x : SeLe4n.ObjId) (sc : SchedContext),
      st'.objects[x]? = some (.schedContext sc) → st.objects[x]? = some (.schedContext sc))
    (hB : ∀ x : SeLe4n.ObjId, objBindingWords st'.objects[x]? = objBindingWords st.objects[x]?) :
    chainObjectsKept st st' :=
  ⟨hR, hS, bindingViewsShrink_of_objects fun x => .of_eq (hB x)⟩

/-- **It is a links shrink.** -/
theorem linksShrink {st st' : SystemState} (h : chainObjectsKept st st') :
    contextStackLinksShrink st st' :=
  contextStackLinksShrink_of_agree h.reply h.schedContext h.binding

/-- A reply object read after the step was the same before it. -/
theorem getReply? {st st' : SystemState} (h : chainObjectsKept st st') {rid : SeLe4n.ReplyId}
    {rep : Reply} (hR : st'.getReply? rid = some rep) : st.getReply? rid = some rep :=
  (SystemState.getReply?_eq_some_iff _ _ _).mpr
    (h.reply _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hR))

/-- A step agreeing with its pre-state off the run-queue links. -/
theorem of_objectsAgreeOffRunLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffRunLinks st) : chainObjectsKept st st' :=
  ⟨fun _ _ hx => h.get_reply_iff.mp hx, fun _ _ hx => h.get_schedContext_iff.mp hx,
   bindingViewsShrink_of_objects fun x => .of_eq (objBindingWords_of_withoutRunLinks (h x))⟩

/-- **One slot written with an object of neither kind.** -/
theorem of_slot {st st' : SystemState} (k : SeLe4n.ObjId)
    (hNe : ∀ x, x ≠ k → st'.objects[x]? = st.objects[x]?)
    (hK : ∀ o, st'.objects[k]? = some o → (∀ r, o ≠ .reply r) ∧ (∀ sc, o ≠ .schedContext sc))
    (hB : objBindingShrink st.objects[k]? st'.objects[k]?) :
    chainObjectsKept st st' := by
  refine ⟨fun x r hx => ?_, fun x sc hx => ?_, bindingViewsShrink_of_slot k hNe hB⟩
  · by_cases hk : x = k
    · subst hk; exact absurd rfl ((hK _ hx).1 r)
    · rw [hNe x hk] at hx; exact hx
  · by_cases hk : x = k
    · subst hk; exact absurd rfl ((hK _ hx).2 sc)
    · rw [hNe x hk] at hx; exact hx

/-- **A store of an object of neither kind.** -/
theorem storeObject_other {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (h : storeObject k o st = .ok ((), st'))
    (hRp : ∀ r, o ≠ .reply r) (hSc : ∀ sc, o ≠ .schedContext sc)
    (hB : objBindingShrink st.objects[k]? (some o) := by
      first
        | exact objBindingShrink.of_free rfl
        | exact objBindingShrink.of_eq rfl
        | (apply objBindingShrink.ofTcb (by assumption); exact .inr ⟨rfl, rfl⟩)
        | (apply objBindingShrink.ofTcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp
            (by assumption)); exact .inr ⟨rfl, rfl⟩)
        | (apply objBindingShrink.ofTcb (lookupTcb_some_objects _ _ _ (by assumption));
            exact .inr ⟨rfl, rfl⟩)
        | (apply objBindingShrink.ofNotification (by assumption); exact .inr rfl)
        | (apply objBindingShrink.ofSchedContext (by assumption); exact .inr rfl)) :
    chainObjectsKept st st' :=
  of_slot k (fun x hx => storeObject_objects_ne st st' k x o hx hInv h)
    (fun o' ho => by
      rw [storeObject_objects_eq st st' k o hInv h] at ho; cases ho; exact ⟨hRp, hSc⟩)
    (by rw [storeObject_objects_eq st st' k o hInv h]; exact hB)

/-- **An in-place write of an object of neither kind.** -/
theorem insert_other {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hRp : ∀ r, o ≠ .reply r) (hSc : ∀ sc, o ≠ .schedContext sc)
    (hB : objBindingShrink st.objects[k]? (some o) := by
      first
        | exact objBindingShrink.of_free rfl
        | exact objBindingShrink.of_eq rfl
        | (apply objBindingShrink.ofTcb (by assumption); exact .inr ⟨rfl, rfl⟩)
        | (apply objBindingShrink.ofTcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp
            (by assumption)); exact .inr ⟨rfl, rfl⟩)
        | (apply objBindingShrink.ofTcb (lookupTcb_some_objects _ _ _ (by assumption));
            exact .inr ⟨rfl, rfl⟩)
        | (apply objBindingShrink.ofNotification (by assumption); exact .inr rfl)
        | (apply objBindingShrink.ofSchedContext (by assumption); exact .inr rfl)) :
    chainObjectsKept st { st with objects := st.objects.insert k o } := by
  refine of_slot (st' := { st with objects := st.objects.insert k o }) k (fun x hx => ?_)
    (fun o' ho => ?_) ?_
  · show (st.objects.insert k o)[x]? = _
    simp only [RHTable_getElem?_eq_get?]
    exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb).symm) hInv
  · have hEq : (st.objects.insert k o)[k]? = some o := by
      simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
    have : o' = o := Option.some.inj (ho.symm.trans hEq)
    subst this; exact ⟨hRp, hSc⟩
  · show objBindingShrink _ (st.objects.insert k o)[k]?
    rw [show (st.objects.insert k o)[k]? = some o by
      simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv]
    exact hB

end chainObjectsKept

/-- **The links shrink with one reply object's caller left free**: every head
and every `prev` link after the step was there before it, and every caller but
the one at `rid`. -/
structure contextStackLinksShrinkOff (st st' : SystemState) (rid : SeLe4n.ReplyId) : Prop where
  head : ∀ s r, contextStackHead st' s = some r → OnContextStackView st s r
  prev : ∀ r x, replyStackPrev st' r = some x → replyStackPrev st r = some x
  caller : ∀ r l, r ≠ rid → replyStackCaller st' r = some l → replyStackCaller st r = some l
  binding : bindingViewsShrink st st'

namespace contextStackLinksShrinkOff

theorem of_linksShrink {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : contextStackLinksShrink st st') : contextStackLinksShrinkOff st st' rid :=
  ⟨h.head, h.prev, fun r l _ hC => h.caller r l hC, h.binding⟩

theorem onStack {st st' : SystemState} {rid : SeLe4n.ReplyId} {s : SeLe4n.SchedContextId}
    {r : SeLe4n.ReplyId} (h : contextStackLinksShrinkOff st st' rid)
    (hOn : OnContextStackView st' s r) : OnContextStackView st s r := by
  induction hOn with
  | head hH => exact h.head _ _ hH
  | lower _ hP ih => exact .lower ih (h.prev _ _ hP)

theorem shrink_trans {st st' st'' : SystemState} {rid : SeLe4n.ReplyId}
    (h1 : contextStackLinksShrink st st') (h2 : contextStackLinksShrinkOff st' st'' rid) :
    contextStackLinksShrinkOff st st'' rid :=
  ⟨fun s r hH => (h2.head s r hH).of_linksShrink h1, fun r x hP => h1.prev r x (h2.prev r x hP),
   fun r l hne hC => h1.caller r l (h2.caller r l hne hC), h1.binding.trans h2.binding⟩

theorem trans_shrink {st st' st'' : SystemState} {rid : SeLe4n.ReplyId}
    (h1 : contextStackLinksShrinkOff st st' rid) (h2 : contextStackLinksShrink st' st'') :
    contextStackLinksShrinkOff st st'' rid :=
  ⟨fun s r hH => h1.onStack (h2.head s r hH), fun r x hP => h1.prev r x (h2.prev r x hP),
   fun r l hne hC => h1.caller r l hne (h2.caller r l hC), h1.binding.trans h2.binding⟩

end contextStackLinksShrinkOff

/-- **A caller linked on a free reply object adds no lender**: the step's
links shrink everywhere but the caller at `rid`, and `rid` is free at the
pre-state, where the chain holds, so it is on no context's stack. -/
theorem lendingLabelsEqual_of_linksShrinkOff {ctx : LabelingContext} {st st' : SystemState}
    {rid : SeLe4n.ReplyId} {rep : Reply} (hChain : donationChainWellFormed st)
    (hFlow : lendingLabelsEqual ctx st) (hR : st.getReply? rid = some rep) (hN : rep.next = none)
    (h : contextStackLinksShrinkOff st st' rid) : lendingLabelsEqual ctx st' := by
  refine ⟨?_, bindingLabelsEqual_of_shrink hFlow.2 h.binding⟩
  have hFlow := hFlow.1
  rw [contextLendersLabelsEqual_iff_views] at hFlow ⊢
  intro s r l hOn hC
  have hOn0 := h.onStack hOn
  by_cases hr : r = rid
  · subst hr; exact absurd hOn0 (not_onContextStack_of_next_none hChain hR hN s)
  · exact hFlow s r l hOn0 (h.caller r l hr hC)

/-! ### The writers of neither kind -/

namespace chainObjectsKept

/-- A thread record rewritten through `modifyTcb`. -/
theorem modifyTcb {st st' : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : SeLe4n.Kernel.modifyTcb st tid f = .ok st')
    (hf : ∀ t : TCB, (f t).scBindingScCode = t.scBindingScCode ∧
      (f t).scBindingOwnerCode = t.scBindingOwnerCode := by intro _; exact ⟨rfl, rfl⟩) :
    chainObjectsKept st st' := by
  unfold SeLe4n.Kernel.modifyTcb at h
  cases hL : lookupTcb st tid with
  | none => rw [hL] at h; cases h
  | some t =>
    rw [hL] at h; simp only [] at h
    cases hS : storeObject tid.toObjId (.tcb (f t)) st with
    | error e => rw [hS] at h; cases h
    | ok p =>
      obtain ⟨⟨⟩, s⟩ := p
      rw [hS] at h; cases h
      exact storeObject_other hInv hS (fun _ e => by cases e) (fun _ e => by cases e)
        (.ofTcb (lookupTcb_some_objects st tid t hL) (.inr (hf t)))

theorem storeTcbQueueLinks {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {prev : Option SeLe4n.ThreadId} {pprev : Option QueuePPrev} {next : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : SeLe4n.Kernel.storeTcbQueueLinks st tid prev pprev next = .ok st') :
    chainObjectsKept st st' := modifyTcb hInv h

theorem storeTcbIpcStateAndMessage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {s : ThreadIpcState} {msg : Option IpcMessage} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.storeTcbIpcStateAndMessage st tid s msg = .ok st') :
    chainObjectsKept st st' := modifyTcb hInv h

theorem storeTcbReceiveComplete {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {msg : Option IpcMessage} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.storeTcbReceiveComplete st tid msg = .ok st') :
    chainObjectsKept st st' := modifyTcb hInv h

/-- A thread record rewritten in its slot, keeping both its binding words or
clearing its context word. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt)
    (hf : ∀ x : TCB, (f x).scBindingScCode = 0 ∨ ((f x).scBindingScCode = x.scBindingScCode ∧
      (f x).scBindingOwnerCode = x.scBindingOwnerCode) := by
      intro _; first | exact .inr ⟨rfl, rfl⟩ | exact .inl rfl) :
    chainObjectsKept st (st.updateTcb t f) := by
  cases hT : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact refl _
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hT]
    exact insert_other hInv (fun _ e => by cases e) (fun _ e => by cases e)
      (.ofTcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) (hf x))

/-- **A wake** writes thread records and the scheduler alone. -/
theorem enqueueRunnableOnCore (st : SystemState) (c : Concurrency.CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : chainObjectsKept st (SeLe4n.Kernel.enqueueRunnableOnCore st c t) := by
  cases hTcb : st.getTcb? t with
  | none =>
    unfold SeLe4n.Kernel.enqueueRunnableOnCore; rw [SystemState.getTcbWitnessed?_eq_none hTcb]
    exact refl _
  | some tcb =>
    cases hR : wakeDeclines st c t with
    | true => rw [enqueueRunnableOnCore_eq_self_of_declines st c t hR]; exact refl _
    | false =>
      have hAg := enqueueRunnableOnCore_objectsAgree_marked st c t tcb hTcb hR
      exact (insert_other (k := t.toObjId) (o := .tcb (tcb.setIpcState .ready)) hInv
        (fun _ e => by cases e) (fun _ e => by cases e)).trans (of_objectsAgreeOffRunLinks hAg)

theorem wakeThread (st : SystemState) (t : SeLe4n.ThreadId) (c : Concurrency.CoreId)
    (hInv : st.objects.invExt) : chainObjectsKept st (SeLe4n.Kernel.wakeThread st t c).1 := by
  rw [wakeThread_state_eq_enqueue]; exact enqueueRunnableOnCore st _ t hInv

theorem removeRunnableOnCore (st : SystemState) (t : SeLe4n.ThreadId) (c : Concurrency.CoreId) :
    chainObjectsKept st (SeLe4n.Kernel.removeRunnableOnCore st t c) :=
  of_objectsAgreeOffRunLinks (removeRunnableOnCore_objectsAgreeOffRunLinks st t c)

theorem linkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId) :
    chainObjectsKept st (st.linkReplyWaiter w s) :=
  of_objectsAgreeOffRunLinks (SystemState.linkReplyWaiter_objectsAgreeOffRunLinks st w s)

theorem recordSendCap (st : SystemState) (t : SeLe4n.ThreadId) (b : Option SeLe4n.Badge)
    (g gr : Bool) : chainObjectsKept st (SeLe4n.Kernel.recordSendCap st t b g gr) :=
  of_objectsAgreeOffRunLinks (recordSendCap_objectsAgreeOffRunLinks st t b g gr)

/-- **An object rewritten in its slot** by an update that leaves a reply object
and a context as they are and makes neither kind out of another. -/
theorem modifyObject {st : SystemState} {k : SeLe4n.ObjId} {f : KernelObject → KernelObject}
    (hInv : st.objects.invExt)
    (hf : ∀ o, st.objects[k]? = some o → (∀ r, f o = .reply r → o = .reply r) ∧
      (∀ sc, f o = .schedContext sc → o = .schedContext sc) ∧
      objBindingWords (some (f o)) = objBindingWords (some o)) :
    chainObjectsKept st (st.modifyObject k f) := by
  unfold SystemState.modifyObject RobinHood.RHTable.modify
  cases hG : st.objects.get? k with
  | none => exact refl _
  | some v =>
    have hPre : st.objects[k]? = some v := by rw [RHTable_getElem?_eq_get?]; exact hG
    simp only []
    have hEq : (st.objects.insert k (f v))[k]? = some (f v) := by
      simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
    have hNe : ∀ x, x ≠ k → (st.objects.insert k (f v))[x]? = st.objects[x]? := fun x hx => by
      simp only [RHTable_getElem?_eq_get?]
      exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb).symm) hInv
    refine ⟨fun x r hx => ?_, fun x sc hx => ?_, bindingViewsShrink_of_slot k hNe
      (.of_eq (by rw [hEq, hPre]; exact (hf v hPre).2.2))⟩
    · by_cases hk : x = k
      · subst hk
        have : f v = .reply r := Option.some.inj (hEq.symm.trans hx)
        rw [hPre, (hf v hPre).1 r this]
      · exact (hNe x hk) ▸ hx
    · by_cases hk : x = k
      · subst hk
        have : f v = .schedContext sc := Option.some.inj (hEq.symm.trans hx)
        rw [hPre, (hf v hPre).2.1 sc this]
      · exact (hNe x hk) ▸ hx

/-- **The in-place pop** writes the endpoint and two thread records. -/
theorem storePopHead (st : SystemState) (e : SeLe4n.ObjId) (isRecv : Bool) (h : SeLe4n.ThreadId)
    (n : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    chainObjectsKept st (SeLe4n.Kernel.storePopHead st e isRecv h n) := by
  unfold SeLe4n.Kernel.storePopHead; dsimp only
  have h1 : chainObjectsKept st (st.modifyObject e (popEndpoint isRecv (SeLe4n.ThreadId.optCode n))) :=
    modifyObject hInv (fun o _ => by
      cases o <;> simp only [popEndpoint] <;> (try split) <;> simp [objBindingWords])
  have hI1 := modifyObject_preserves_objects_invExt (k := e)
    (f := popEndpoint isRecv (SeLe4n.ThreadId.optCode n)) hInv
  cases n with
  | none => exact h1.trans (updateTcb _ _ _ hI1)
  | some m =>
    exact h1.trans ((updateTcb _ m _ hI1).trans
      (updateTcb _ _ _ (SystemState.updateTcb_preserves_objects_invExt _ _ _ hI1)))

end chainObjectsKept

namespace chainObjectsKept

/-- **The queue pop** writes the endpoint and queue-link thread records. -/
theorem endpointQueuePopHead {st st' : SystemState} {eid : SeLe4n.ObjId} {isRecv : Bool}
    {t : SeLe4n.ThreadId} {tcb : TCB} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.endpointQueuePopHead eid isRecv st = .ok (t, tcb, st')) :
    chainObjectsKept st st' := by
  unfold SeLe4n.Kernel.endpointQueuePopHead SystemState.getObject? at h
  split at h <;> try cases h
  rename_i ep _
  dsimp only at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  rename_i st1 hS
  have hI1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hS
  have hK1 := storeObject_other hInv hS (fun _ e => by cases e) (fun _ e => by cases e)
  split at h <;> try cases h
  rename_i st2 hR2
  have hK2 : chainObjectsKept st1 st2 ∧ st2.objects.invExt := by
    split at hR2
    · cases hR2; exact ⟨refl _, hI1⟩
    · split at hR2
      · cases hR2
      · exact ⟨storeTcbQueueLinks hI1 hR2,
          storeTcbQueueLinks_preserves_objects_invExt _ _ _ _ _ _ hI1 hR2⟩
  split at h <;> try cases h
  rename_i st3 hS3
  exact hK1.trans (hK2.1.trans (storeTcbQueueLinks hK2.2 hS3))

/-- **The queue append** writes the endpoint and queue-link thread records. -/
theorem endpointQueueEnqueue {st st' : SystemState} {eid : SeLe4n.ObjId} {isRecv : Bool}
    {t : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.endpointQueueEnqueue eid isRecv t st = .ok st') :
    chainObjectsKept st st' := by
  unfold SeLe4n.Kernel.endpointQueueEnqueue SystemState.getObject? at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  dsimp only at h
  split at h
  · split at h <;> try cases h
    rename_i st1 hS
    exact (storeObject_other hInv hS (fun _ e => by cases e) (fun _ e => by cases e)).trans
      (storeTcbQueueLinks (storeObject_preserves_objects_invExt st st1 _ _ hInv hS) h)
  · split at h <;> try cases h
    split at h <;> try cases h
    rename_i st1 hS
    have hI1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hS
    split at h <;> try cases h
    rename_i st2 hS2
    exact (storeObject_other hInv hS (fun _ e => by cases e) (fun _ e => by cases e)).trans
      ((storeTcbQueueLinks hI1 hS2).trans (storeTcbQueueLinks
        (storeTcbQueueLinks_preserves_objects_invExt _ _ _ _ _ _ hI1 hS2) h))

end chainObjectsKept

/-! ### The link -/

/-- **One reply object rewritten with its caller only**: its `prev` link kept,
and no context written. -/
theorem contextStackLinksShrinkOff_of_replyCaller {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {r r' : Reply} (hR : st.objects[rid.toObjId]? = some (.reply r))
    (hEq : st'.objects[rid.toObjId]? = some (.reply r'))
    (hNe : ∀ x, x ≠ rid.toObjId → st'.objects[x]? = st.objects[x]?) (hP : r'.prev = r.prev) :
    contextStackLinksShrinkOff st st' rid := by
  refine ⟨fun s x hH => .head ?_, fun x y hP' => ?_, fun x l hx hC => ?_,
    bindingViewsShrink_of_slot _ hNe (.of_eq (by rw [hEq, hR]; rfl))⟩
  · rw [contextStackHead_eq_obj] at hH ⊢
    by_cases hk : s.toObjId = rid.toObjId
    · rw [hk, hEq] at hH; cases hH
    · rw [hNe _ hk] at hH; exact hH
  · rw [replyStackPrev_eq_obj] at hP' ⊢
    by_cases hk : x.toObjId = rid.toObjId
    · rw [hk, hEq] at hP'; rw [hk, hR]; simpa [objStackPrev, hP] using hP'
    · rw [hNe _ hk] at hP'; exact hP'
  · rw [replyStackCaller_eq_obj] at hC ⊢
    have hk : x.toObjId ≠ rid.toObjId := fun e => hx (SeLe4n.ReplyId.toObjId_injective _ _ e)
    rw [hNe _ hk] at hC; exact hC

/-- **`linkReply`** writes the caller of a reply object free at its pre-state. -/
theorem linkReply_linksShrinkOff {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {caller : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : SystemState.linkReply rid caller st = .ok ((), st')) :
    (∃ rep, st.getReply? rid = some rep ∧ rep.next = none) ∧
      contextStackLinksShrinkOff st st' rid ∧ st'.objects.invExt := by
  unfold SystemState.linkReply at h
  cases hR : st.getReply? rid with
  | none => rw [hR] at h; cases h
  | some r =>
    rw [hR] at h; simp only [] at h
    split at h
    · rename_i hFree
      have hF := (Reply.isFree_iff r).mp hFree
      refine ⟨⟨r, rfl, hF.2.2⟩, contextStackLinksShrinkOff_of_replyCaller
        ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) (storeObject_objects_eq st st' _ _ hInv h)
        (fun x hx => storeObject_objects_ne st st' _ x _ hx hInv h) rfl,
        storeObject_preserves_objects_invExt st st' _ _ hInv h⟩
    · cases h

/-- **`linkCallerReply`**: the link, then the caller's own record. -/
theorem linkCallerReply_linksShrinkOff {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {caller : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    (∃ rep, st.getReply? rid = some rep ∧ rep.next = none) ∧
      contextStackLinksShrinkOff st st' rid ∧ st'.objects.invExt := by
  unfold SystemState.linkCallerReply at h
  cases h1 : SystemState.linkReply rid caller st with
  | error e => rw [h1] at h; cases h
  | ok p =>
    obtain ⟨⟨⟩, s1⟩ := p
    rw [h1] at h; simp only [] at h
    obtain ⟨hFree, hOff, hI1⟩ := linkReply_linksShrinkOff hInv h1
    split at h
    · cases h
    · split at h
      · exact ⟨hFree, hOff.trans_shrink (contextStackLinksShrink_storeObject_other hI1 h
          (fun _ e => by cases e) (fun _ e => by cases e)),
          storeObject_preserves_objects_invExt s1 st' _ _ hI1 h⟩
      · cases h

/-- **`linkServerStashedReply`**: `linkCallerReply` on the stashed reply object,
then the server's record. -/
theorem linkServerStashedReply_linksShrinkOff {st st' : SystemState}
    {caller server : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    ∃ rid, (∃ rep, st.getReply? rid = some rep ∧ rep.next = none) ∧
      contextStackLinksShrinkOff st st' rid ∧ st'.objects.invExt := by
  unfold SystemState.linkServerStashedReply at h
  split at h
  · cases h
  · rename_i rid _
    split at h
    · cases h
    · rename_i s1 h1
      obtain ⟨hFree, hOff, hI1⟩ := linkCallerReply_linksShrinkOff hInv h1
      refine ⟨rid, hFree, ?_⟩
      split at h
      · cases h; exact ⟨hOff, hI1⟩
      · exact ⟨hOff.trans_shrink (contextStackLinksShrink_storeObject_other hI1 h
          (fun _ e => by cases e) (fun _ e => by cases e)),
          storeObject_preserves_objects_invExt s1 st' _ _ hI1 h⟩

/-- **The lenders across `linkServerStashedReply`.** -/
theorem linkServerStashedReply_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st st' : SystemState} {caller server : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hFlow : lendingLabelsEqual ctx st)
    (h : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    lendingLabelsEqual ctx st' := by
  obtain ⟨_, ⟨rep, hR, hN⟩, hOff, _⟩ := linkServerStashedReply_linksShrinkOff hInv h
  exact lendingLabelsEqual_of_linksShrinkOff hChain hFlow hR hN hOff

/-- **A reply object's caller written in its slot** (`replyWithCaller`, the
in-place link); an object of another kind is left as it is. -/
theorem modifyObject_replyWithCaller_linksShrinkOff (st : SystemState) (rid : SeLe4n.ReplyId)
    (caller : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    contextStackLinksShrinkOff st (st.modifyObject rid.toObjId (replyWithCaller caller)) rid := by
  cases hO : st.objects[rid.toObjId]? with
  | some o =>
    cases o with
    | reply rep =>
      unfold SystemState.modifyObject RobinHood.RHTable.modify
      have hG : st.objects.get? rid.toObjId = some (.reply rep) := by
        rw [← RHTable_getElem?_eq_get?]; exact hO
      rw [hG]; simp only []
      refine contextStackLinksShrinkOff_of_replyCaller (r' := { rep with
        callerCode := SeLe4n.ThreadId.optCode (some caller) }) hO ?_ (fun x hx => ?_) rfl
      · show (st.objects.insert _ _)[_]? = _
        simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
      · show (st.objects.insert _ _)[x]? = _
        simp only [RHTable_getElem?_eq_get?]
        exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb).symm) hInv
    | _ =>
      exact .of_linksShrink (chainObjectsKept.modifyObject hInv (fun o ho => by
        rw [hO] at ho; cases ho; simp [replyWithCaller, objBindingWords])).linksShrink
  | none =>
    exact .of_linksShrink (chainObjectsKept.modifyObject hInv (fun o ho => by
      rw [hO] at ho; cases ho)).linksShrink

theorem storePopHead_preserves_objects_invExt' (st : SystemState) (e : SeLe4n.ObjId)
    (isRecv : Bool) (h : SeLe4n.ThreadId) (n : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (storePopHead st e isRecv h n).objects.invExt := by
  unfold storePopHead; dsimp only
  have hI1 := modifyObject_preserves_objects_invExt (k := e)
    (f := popEndpoint isRecv (SeLe4n.ThreadId.optCode n)) hInv
  cases n with
  | none => exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hI1
  | some m =>
    exact SystemState.updateTcb_preserves_objects_invExt _ _ _
      (SystemState.updateTcb_preserves_objects_invExt _ _ _ hI1)

/-- **The lenders across the in-place call rendezvous** (`storeCallRendezvous`):
the caller is linked on a reply object free at the pre-state, which is what
`callWakesInPlace` / `callTakesReplyInPlace` check. -/
theorem storeCallRendezvous_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st : SystemState} {endpointId : SeLe4n.ObjId} {caller r : SeLe4n.ThreadId}
    {next : Option SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {msg : IpcMessage}
    {core : Concurrency.CoreId} {rep : Reply} (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hFlow : lendingLabelsEqual ctx st)
    (hR : st.getReply? rid = some rep) (hFree : rep.isFree = true) :
    lendingLabelsEqual ctx (storeCallRendezvous st endpointId caller r next rid msg core) := by
  unfold storeCallRendezvous; dsimp only
  have hI0 := storePopHead_preserves_objects_invExt' st endpointId true r next hInv
  have hK0 := chainObjectsKept.storePopHead st endpointId true r next hInv
  generalize storePopHead st endpointId true r next = s0 at hI0 hK0
  have hK1 := hK0.trans (chainObjectsKept.updateTcb s0 r (callReceiverTcb msg) hI0)
  have hI1 := SystemState.updateTcb_preserves_objects_invExt s0 r (callReceiverTcb msg) hI0
  generalize s0.updateTcb r (callReceiverTcb msg) = s1 at hI1 hK1
  have hK2 := hK1.trans (chainObjectsKept.enqueueRunnableOnCore s1 (determineTargetCore s1 r) r hI1)
  have hI2 := enqueueRunnableOnCore_preserves_objects_invExt s1 (determineTargetCore s1 r) r hI1
  generalize enqueueRunnableOnCore s1 (determineTargetCore s1 r) r = s2 at hI2 hK2
  have hK3 := hK2.trans (chainObjectsKept.updateTcb s2 caller (callCallerTcb endpointId r) hI2)
  have hI3 := SystemState.updateTcb_preserves_objects_invExt s2 caller (callCallerTcb endpointId r) hI2
  generalize s2.updateTcb caller (callCallerTcb endpointId r) = s3 at hI3 hK3
  have hOff := contextStackLinksShrinkOff.shrink_trans hK3.linksShrink
    (modifyObject_replyWithCaller_linksShrinkOff s3 rid caller hI3)
  have hI4 := modifyObject_preserves_objects_invExt (k := rid.toObjId) (f := replyWithCaller caller) hI3
  generalize s3.modifyObject rid.toObjId (replyWithCaller caller) = s4 at hI4 hOff
  have hK5 := chainObjectsKept.updateTcb s4 caller
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hI4
  have hI5 := SystemState.updateTcb_preserves_objects_invExt s4 caller
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hI4
  generalize s4.updateTcb caller (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) = s5 at hI5 hK5
  have hK6 := hK5.trans (chainObjectsKept.updateTcb s5 r (fun t => { t with pendingReceiveReplyCode := 0 }) hI5)
  generalize s5.updateTcb r (fun t => { t with pendingReceiveReplyCode := 0 }) = s6 at hK6
  have hK7 := hK6.trans ((chainObjectsKept.removeRunnableOnCore s6 caller core).trans
    (chainObjectsKept.linkReplyWaiter _ caller r))
  exact lendingLabelsEqual_of_linksShrinkOff hChain hFlow hR ((Reply.isFree_iff rep).mp hFree).2.2
    (hOff.trans_shrink hK7.linksShrink)

/-- **The in-place link between writers of neither kind**: the lenders across a
step that writes no reply object and no context, links a caller in place on a
reply object free at the pre-state, and again writes neither kind. -/
theorem lendingLabelsEqual_of_inPlaceLink {ctx : LabelingContext} {st s st' : SystemState}
    {rid : SeLe4n.ReplyId} {caller : SeLe4n.ThreadId} {rep : Reply}
    (hChain : donationChainWellFormed st) (hFlow : lendingLabelsEqual ctx st)
    (hR : st.getReply? rid = some rep) (hFree : rep.isFree = true)
    (hK1 : chainObjectsKept st s) (hI : s.objects.invExt)
    (hK2 : chainObjectsKept (s.modifyObject rid.toObjId (replyWithCaller caller)) st') :
    lendingLabelsEqual ctx st' :=
  lendingLabelsEqual_of_linksShrinkOff hChain hFlow hR ((Reply.isFree_iff rep).mp hFree).2.2
    ((contextStackLinksShrinkOff.shrink_trans hK1.linksShrink
      (modifyObject_replyWithCaller_linksShrinkOff s rid caller hI)).trans_shrink hK2.linksShrink)

/-- **The lenders across `storeCallRendezvousReady`**: `storeCallRendezvous`
with the receiver holding no message. -/
theorem storeCallRendezvousReady_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st : SystemState} {endpointId : SeLe4n.ObjId} {caller r : SeLe4n.ThreadId}
    {nextCode : Nat} {rid : SeLe4n.ReplyId} {core : Concurrency.CoreId} {rep : Reply}
    (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hFlow : lendingLabelsEqual ctx st) (hR : st.getReply? rid = some rep)
    (hFree : rep.isFree = true) :
    lendingLabelsEqual ctx (storeCallRendezvousReady st endpointId caller r nextCode rid core) := by
  unfold storeCallRendezvousReady; dsimp only
  have hI0 := storePopHead_preserves_objects_invExt' st endpointId true r
    (ThreadId.ofOptCode nextCode) hInv
  have hK0 := chainObjectsKept.storePopHead st endpointId true r (ThreadId.ofOptCode nextCode) hInv
  generalize storePopHead st endpointId true r (ThreadId.ofOptCode nextCode) = s0 at hI0 hK0
  have hK1 := hK0.trans (chainObjectsKept.updateTcb s0 r receiverReady hI0)
  have hI1 := SystemState.updateTcb_preserves_objects_invExt s0 r receiverReady hI0
  generalize s0.updateTcb r receiverReady = s1 at hI1 hK1
  have hK2 := hK1.trans (chainObjectsKept.enqueueRunnableOnCore s1 (determineTargetCore s1 r) r hI1)
  have hI2 := enqueueRunnableOnCore_preserves_objects_invExt s1 (determineTargetCore s1 r) r hI1
  generalize enqueueRunnableOnCore s1 (determineTargetCore s1 r) r = s2 at hI2 hK2
  have hK3 := hK2.trans (chainObjectsKept.updateTcb s2 caller (callCallerTcb endpointId r) hI2)
  have hI3 := SystemState.updateTcb_preserves_objects_invExt s2 caller (callCallerTcb endpointId r) hI2
  generalize s2.updateTcb caller (callCallerTcb endpointId r) = s3 at hI3 hK3
  refine lendingLabelsEqual_of_inPlaceLink (caller := caller) hChain hFlow hR hFree hK3 hI3 ?_
  have hI4 := modifyObject_preserves_objects_invExt (k := rid.toObjId) (f := replyWithCaller caller) hI3
  generalize s3.modifyObject rid.toObjId (replyWithCaller caller) = s4 at hI4
  have hK5 := chainObjectsKept.updateTcb s4 caller
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hI4
  have hI5 := SystemState.updateTcb_preserves_objects_invExt s4 caller
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hI4
  generalize s4.updateTcb caller (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) = s5 at hI5 hK5
  exact (hK5.trans (chainObjectsKept.updateTcb s5 r (fun t => { t with pendingReceiveReplyCode := 0 }) hI5)).trans
    ((chainObjectsKept.removeRunnableOnCore _ caller core).trans (chainObjectsKept.linkReplyWaiter _ caller r))

/-- **The lenders across the receive's in-place take of a queued caller**
(`storeReceiveCallReady`). -/
theorem storeReceiveCallReady_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st : SystemState} {endpointId : SeLe4n.ObjId} {s : SeLe4n.ThreadId} {nextCode : Nat}
    {receiver : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {rep : Reply}
    (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hFlow : lendingLabelsEqual ctx st) (hR : st.getReply? rid = some rep)
    (hFree : rep.isFree = true) :
    lendingLabelsEqual ctx (storeReceiveCallReady st endpointId s nextCode receiver rid) := by
  unfold storeReceiveCallReady; dsimp only
  have hI0 := storePopHead_preserves_objects_invExt' st endpointId false s
    (ThreadId.ofOptCode nextCode) hInv
  have hK0 := chainObjectsKept.storePopHead st endpointId false s (ThreadId.ofOptCode nextCode) hInv
  generalize storePopHead st endpointId false s (ThreadId.ofOptCode nextCode) = s0 at hI0 hK0
  have hK1 := hK0.trans (chainObjectsKept.updateTcb s0 s (callCallerTcb endpointId receiver) hI0)
  have hI1 := SystemState.updateTcb_preserves_objects_invExt s0 s (callCallerTcb endpointId receiver) hI0
  generalize s0.updateTcb s (callCallerTcb endpointId receiver) = s1 at hI1 hK1
  refine lendingLabelsEqual_of_inPlaceLink (caller := s) hChain hFlow hR hFree hK1 hI1 ?_
  have hI2 := modifyObject_preserves_objects_invExt (k := rid.toObjId) (f := replyWithCaller s) hI1
  generalize s1.modifyObject rid.toObjId (replyWithCaller s) = s2 at hI2
  have hK3 := chainObjectsKept.updateTcb s2 s
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hI2
  have hI3 := SystemState.updateTcb_preserves_objects_invExt s2 s
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hI2
  generalize s2.updateTcb s (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) = s3 at hI3 hK3
  exact (hK3.trans (chainObjectsKept.updateTcb s3 receiver receiverReady hI3)).trans
    (chainObjectsKept.linkReplyWaiter _ s receiver)

/-- **The lenders across the specification's take of a queued caller**
(`receiveCallTakeState`). -/
theorem receiveCallTakeState_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st : SystemState} {endpointId : SeLe4n.ObjId} {s : SeLe4n.ThreadId} {sTcb : TCB}
    {receiver : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {rep : Reply}
    (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hFlow : lendingLabelsEqual ctx st) (hR : st.getReply? rid = some rep)
    (hFree : rep.isFree = true) :
    lendingLabelsEqual ctx (receiveCallTakeState st endpointId s sTcb receiver rid) := by
  unfold receiveCallTakeState
  have hI0 := storePopHead_preserves_objects_invExt' st endpointId false s sTcb.queueNext hInv
  have hK0 := chainObjectsKept.storePopHead st endpointId false s sTcb.queueNext hInv
  generalize storePopHead st endpointId false s sTcb.queueNext = s0 at hI0 hK0
  have hK1 := hK0.trans (chainObjectsKept.updateTcb s0 s (callCallerTcb endpointId receiver) hI0)
  have hI1 := SystemState.updateTcb_preserves_objects_invExt s0 s (callCallerTcb endpointId receiver) hI0
  generalize s0.updateTcb s (callCallerTcb endpointId receiver) = s1 at hI1 hK1
  refine lendingLabelsEqual_of_inPlaceLink (caller := s) hChain hFlow hR hFree hK1 hI1 ?_
  have hI2 := modifyObject_preserves_objects_invExt (k := rid.toObjId) (f := replyWithCaller s) hI1
  generalize s1.modifyObject rid.toObjId (replyWithCaller s) = s2 at hI2
  have hK3 := chainObjectsKept.updateTcb s2 s
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hI2
  have hI3 := SystemState.updateTcb_preserves_objects_invExt s2 s
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hI2
  generalize s2.updateTcb s (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) = s3 at hI3 hK3
  exact (hK3.trans (chainObjectsKept.updateTcb s3 receiver _ hI3)).trans
    (chainObjectsKept.linkReplyWaiter _ s receiver)

/-- **The link between writers of neither kind**, the monadic form: the
freeness the link checks at its own state is read back at the pre-state, where
the chain holds. -/
theorem lendingLabelsEqual_of_keptLink {ctx : LabelingContext} {st s s' st' : SystemState}
    {rid : SeLe4n.ReplyId} {rep : Reply} (hChain : donationChainWellFormed st)
    (hFlow : lendingLabelsEqual ctx st) (hK1 : chainObjectsKept st s)
    (hR : s.getReply? rid = some rep) (hN : rep.next = none)
    (hOff : contextStackLinksShrinkOff s s' rid) (hK2 : chainObjectsKept s' st') :
    lendingLabelsEqual ctx st' :=
  lendingLabelsEqual_of_linksShrinkOff hChain hFlow (hK1.getReply? hR) hN
    ((contextStackLinksShrinkOff.shrink_trans hK1.linksShrink hOff).trans_shrink hK2.linksShrink)

/-- **The lenders across the per-core call** (`endpointCallOnCore`): the
rendezvous links the caller on the reply object its server stashed, which is
free; every other write is a thread record, an endpoint or the scheduler. -/
theorem endpointCallOnCore_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st : SystemState} {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId}
    {payload : SendPayload} {core : Concurrency.CoreId} (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hFlow : lendingLabelsEqual ctx st) :
    lendingLabelsEqual ctx (endpointCallOnCore endpointId caller payload core st).1 := by
  unfold endpointCallOnCore
  split
  · split
    · split
      · split
        · exact hFlow
        · rename_i receiver _ st1 hPop
          have hK1 := chainObjectsKept.endpointQueuePopHead hInv hPop
          have hI1 := endpointQueuePopHead_preserves_objects_invExt _ _ _ _ _ _ hInv hPop
          split
          · exact hFlow
          · rename_i st2 hS2
            have hK2 := hK1.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2)
            have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hS2
            have hK3 := hK2.trans (chainObjectsKept.wakeThread st2 receiver core hI2)
            have hI3 := wakeThread_preserves_objects_invExt st2 receiver core hI2
            split
            · exact hFlow
            · rename_i st4 hS4
              have hK4 := hK3.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI3 hS4)
              have hI4 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI3 hS4
              split
              · exact hFlow
              · rename_i st5 hL
                obtain ⟨rid, ⟨rep, hR, hN⟩, hOff, _⟩ := linkServerStashedReply_linksShrinkOff hI4 hL
                exact lendingLabelsEqual_of_keptLink hChain hFlow hK4 hR hN hOff
                  ((chainObjectsKept.removeRunnableOnCore st5 caller core).trans
                    (chainObjectsKept.linkReplyWaiter _ caller receiver))
      · split
        · exact hFlow
        · rename_i receiver _ st1 hPop
          have hK1 := chainObjectsKept.endpointQueuePopHead hInv hPop
          have hI1 := endpointQueuePopHead_preserves_objects_invExt _ _ _ _ _ _ hInv hPop
          split
          · exact hFlow
          · rename_i st2 hS2
            have hK2 := hK1.trans (chainObjectsKept.storeTcbReceiveComplete hI1 hS2)
            have hI2 := storeTcbReceiveComplete_preserves_objects_invExt _ _ _ _ hI1 hS2
            split
            · exact hFlow
            · dsimp only
              have hK3 := hK2.trans (chainObjectsKept.wakeThread st2 receiver core hI2)
              have hI3 := wakeThread_preserves_objects_invExt st2 receiver core hI2
              exact lendingLabelsEqual_of_linksShrink hFlow
                ((hK3.trans ((chainObjectsKept.removeRunnableOnCore _ caller core).trans
                  (chainObjectsKept.updateTcb _ caller _
                    (removeRunnableOnCore_objects_invExt _ caller core hI3)))).linksShrink)
    · split
      · exact hFlow
      · rename_i st1 hE
        have hK1 := chainObjectsKept.endpointQueueEnqueue hInv hE
        have hI1 := endpointQueueEnqueue_preserves_objects_invExt _ _ _ _ _ hInv hE
        split
        · exact hFlow
        · rename_i st2 hS2
          exact lendingLabelsEqual_of_linksShrink hFlow
            ((hK1.trans ((chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2).trans
              ((chainObjectsKept.removeRunnableOnCore _ caller core).trans
                (chainObjectsKept.recordSendCap _ caller _ _ _)))).linksShrink)
  · split <;> exact hFlow

/-- **The lenders across the single-core call** (`endpointCall`). -/
theorem endpointCall_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st st' : SystemState} {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId}
    {payload : SendPayload} (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hFlow : lendingLabelsEqual ctx st)
    (h : endpointCall endpointId caller payload st = .ok ((), st')) :
    lendingLabelsEqual ctx st' := by
  unfold endpointCall at h
  split at h <;> try cases h
  split at h
  · split at h
    · split at h <;> try cases h
      rename_i receiver _ st1 hPop
      have hK1 := chainObjectsKept.endpointQueuePopHead hInv hPop
      have hI1 := endpointQueuePopHead_preserves_objects_invExt _ _ _ _ _ _ hInv hPop
      split at h <;> try cases h
      rename_i st2 hS2
      have hK2 := hK1.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2)
      have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hS2
      dsimp only at h
      have hK3 := hK2.trans (chainObjectsKept.of_objectsAgreeOffRunLinks
        (ensureRunnable_objectsAgreeOffRunLinks st2 receiver))
      have hI3 := ensureRunnable_objects_invExt st2 receiver hI2
      split at h <;> try cases h
      rename_i st4 hS4
      have hK4 := hK3.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI3 hS4)
      have hI4 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI3 hS4
      split at h <;> try cases h
      rename_i st5 hL
      obtain ⟨rid, ⟨rep, hR, hN⟩, hOff, _⟩ := linkServerStashedReply_linksShrinkOff hI4 hL
      exact lendingLabelsEqual_of_keptLink hChain hFlow hK4 hR hN hOff
        ((chainObjectsKept.of_objectsAgreeOffRunLinks (removeRunnable_objectsAgreeOffRunLinks st5 caller)).trans
          (chainObjectsKept.linkReplyWaiter _ caller receiver))
    · split at h <;> try cases h
      rename_i receiver _ st1 hPop
      have hK1 := chainObjectsKept.endpointQueuePopHead hInv hPop
      have hI1 := endpointQueuePopHead_preserves_objects_invExt _ _ _ _ _ _ hInv hPop
      split at h <;> try cases h
      rename_i st2 hS2
      have hK2 := hK1.trans (chainObjectsKept.storeTcbReceiveComplete hI1 hS2)
      have hI2 := storeTcbReceiveComplete_preserves_objects_invExt _ _ _ _ hI1 hS2
      split at h <;> try cases h
      have hI3 := removeRunnable_objects_invExt _ caller (ensureRunnable_objects_invExt st2 receiver hI2)
      exact lendingLabelsEqual_of_linksShrink hFlow
        ((hK2.trans ((chainObjectsKept.of_objectsAgreeOffRunLinks
          (ensureRunnable_objectsAgreeOffRunLinks st2 receiver)).trans
          ((chainObjectsKept.of_objectsAgreeOffRunLinks
            (removeRunnable_objectsAgreeOffRunLinks _ caller)).trans
            (chainObjectsKept.updateTcb _ caller _ hI3)))).linksShrink)
  · split at h <;> try cases h
    rename_i st1 hE
    have hK1 := chainObjectsKept.endpointQueueEnqueue hInv hE
    have hI1 := endpointQueueEnqueue_preserves_objects_invExt _ _ _ _ _ hInv hE
    split at h <;> try cases h
    rename_i st2 hS2
    exact lendingLabelsEqual_of_linksShrink hFlow
      ((hK1.trans ((chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2).trans
        ((chainObjectsKept.of_objectsAgreeOffRunLinks (removeRunnable_objectsAgreeOffRunLinks _ caller)).trans
          (chainObjectsKept.recordSendCap _ caller _ _ _)))).linksShrink)

/-! ### The receive's other writes -/

theorem objStackViews_map_withoutRelease (o? : Option KernelObject) :
    objStackHead (o?.map KernelObject.withoutRelease) = objStackHead o? ∧
    objStackPrev (o?.map KernelObject.withoutRelease) = objStackPrev o? ∧
    objStackCaller (o?.map KernelObject.withoutRelease) = objStackCaller o? := by
  cases o? with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some o => cases o <;> exact ⟨rfl, rfl, rfl⟩

/-- **A write of release links alone** (the replenishment migration) is a
frame of the three views. -/
theorem contextStackViewsAgree_of_objectsAgreeOffReleaseLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffReleaseLinks st) : contextStackViewsAgree st st' := by
  have key : ∀ x : SeLe4n.ObjId, objStackHead st'.objects[x]? = objStackHead st.objects[x]? ∧
      objStackPrev st'.objects[x]? = objStackPrev st.objects[x]? ∧
      objStackCaller st'.objects[x]? = objStackCaller st.objects[x]? := fun x => by
    have a := objStackViews_map_withoutRelease st'.objects[x]?
    have b := objStackViews_map_withoutRelease st.objects[x]?
    rw [h x] at a
    exact ⟨a.1.symm.trans b.1, a.2.1.symm.trans b.2.1, a.2.2.symm.trans b.2.2⟩
  have keyB : ∀ o : Option KernelObject,
      objBindingWords (o.map KernelObject.withoutRelease) = objBindingWords o := by
    intro o; cases o with
    | none => rfl
    | some o => cases o <;> rfl
  refine ⟨fun s => ?_, fun r => ?_, fun r => ?_, fun x => ?_⟩
  · rw [contextStackHead_eq_obj, contextStackHead_eq_obj]; exact (key _).1
  · rw [replyStackPrev_eq_obj, replyStackPrev_eq_obj]; exact (key _).2.1
  · rw [replyStackCaller_eq_obj, replyStackCaller_eq_obj]; exact (key _).2.2
  · rw [← keyB st'.objects[x]?, ← keyB st.objects[x]?, h x]

/-- **The receive's pre-block return of a lent context** carries equal lending
labels: a held-head pop (the donation return or the held pop) to the owner its
binding records, labelled as the context by the owner clause. -/
theorem cleanupPreReceiveDonationChecked_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st st' : SystemState} {receiver : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hFlow : lendingLabelsEqual ctx st)
    (h : cleanupPreReceiveDonationChecked st receiver = .ok st') : lendingLabelsEqual ctx st' := by
  unfold cleanupPreReceiveDonationChecked at h
  cases hLk : lookupTcb st receiver with
  | none => rw [hLk] at h; cases h; exact hFlow
  | some recvTcb =>
    rw [hLk] at h; simp only [] at h
    cases hB : recvTcb.schedContextBinding with
    | donated scId owner =>
      rw [hB] at h; simp only [] at h
      have hOwner := (hFlow.2.donated (lookupTcb_some_objects st receiver recvTcb hLk) hB).2
      exact popHeldReplyHead_lift h
        (fun _ _ hR => returnDonatedSchedContextResolved_preserves_lendingLabelsEqual hInv hFlow
          hOwner hR)
        (fun _ _ hK => keepDonatedSchedContextResolved_preserves_lendingLabelsEqual hInv hFlow hK)
    | _ => rw [hB] at h; cases h; exact hFlow

theorem cleanupPreReceiveDonationChecked_objects_invExt {st st' : SystemState}
    {receiver : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : cleanupPreReceiveDonationChecked st receiver = .ok st') : st'.objects.invExt := by
  have := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hInv
  rwa [cleanupPreReceiveDonationChecked_ok_eq_cleanup st st' receiver h] at this

/-- ...and its per-core form, the pop then the replenishment migration. -/
theorem cleanupPreReceiveDonationMigrated_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st st' : SystemState} {receiver : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hFlow : lendingLabelsEqual ctx st)
    (h : cleanupPreReceiveDonationMigrated st receiver = .ok st') : lendingLabelsEqual ctx st' := by
  obtain ⟨stClean, hC, rfl⟩ := cleanupPreReceiveDonationMigrated_ok_decompose h
  have hS := cleanupPreReceiveDonationChecked_preserves_lendingLabelsEqual hInv hFlow hC
  unfold preReceiveReturnMigration
  split
  · exact lendingLabelsEqual_of_viewsAgree hS
      (contextStackViewsAgree_of_objectsAgreeOffReleaseLinks
        (migrateSchedContextReplenishment_agree _ _ _ _))
  · exact hS

/-- **The stasher record** writes one reply object's `stasherCode` alone. -/
theorem recordReplyStasher_linksShrink (st : SystemState) (code : Nat)
    (receiver : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    contextStackLinksShrink st (st.recordReplyStasher code receiver) := by
  unfold SystemState.recordReplyStasher
  split
  · exact .refl _
  · split
    · rename_i r hR
      split
      · rename_i s1 hS
        exact contextStackLinksShrink_storeReply hInv hR hS (.inr rfl) (.inr rfl)
      · exact .refl _
    · exact .refl _

/-- **The lenders across the per-core receive** (`endpointReceiveDualOnCore`):
a dequeued caller is linked on the reply object the receive supplies, which
`linkCallerReply` refuses unless free; the block returns a lent context
(a pop) and records the stash. -/
theorem endpointReceiveDualOnCore_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st : SystemState} {endpointId : SeLe4n.ObjId} {receiver : SeLe4n.ThreadId}
    {replyId : Option SeLe4n.ReplyId} {core : Concurrency.CoreId} (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hFlow : lendingLabelsEqual ctx st) :
    lendingLabelsEqual ctx (endpointReceiveDualOnCore endpointId receiver replyId core st).1 := by
  unfold endpointReceiveDualOnCore
  split
  · split
    · split
      · exact hFlow
      · rename_i sender senderTcb st1 hPop
        have hK1 := chainObjectsKept.endpointQueuePopHead hInv hPop
        have hI1 := endpointQueuePopHead_preserves_objects_invExt _ _ _ _ _ _ hInv hPop
        dsimp only
        split
        · simp only [↓reduceIte]
          split
          · split
            · exact hFlow
            · rename_i st2 hS2
              have hK2 := hK1.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2)
              have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hS2
              split
              · exact hFlow
              · rename_i rid
                split
                · exact hFlow
                · rename_i st3 hL
                  obtain ⟨⟨rep, hR, hN⟩, hOff, hI3⟩ := linkCallerReply_linksShrinkOff hI2 hL
                  split
                  · rename_i st4 hS4
                    exact lendingLabelsEqual_of_keptLink hChain hFlow hK2 hR hN
                      (hOff.trans_shrink (contextStackLinksShrink_of_agree
                        (chainObjectsKept.storeTcbIpcStateAndMessage hI3 hS4).reply
                        (chainObjectsKept.storeTcbIpcStateAndMessage hI3 hS4).schedContext
                        (chainObjectsKept.storeTcbIpcStateAndMessage hI3 hS4).binding))
                      (chainObjectsKept.linkReplyWaiter _ sender receiver)
                  · exact hFlow
          · split
            · exact hFlow
            · rename_i st2 hS2
              have hK2 := hK1.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2)
              have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hS2
              have hK3 := hK2.trans (chainObjectsKept.updateTcb st2 sender
                (fun t => { t with threadState := .Inactive }) hI2)
              have hI3 := SystemState.updateTcb_preserves_objects_invExt st2 sender
                (fun t => { t with threadState := .Inactive }) hI2
              split
              · rename_i st4 hS4
                exact lendingLabelsEqual_of_linksShrink hFlow
                  (hK3.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI3 hS4)).linksShrink
              · exact hFlow
        · simp only [Bool.false_eq_true, ↓reduceIte]
          split
          · exact hFlow
          · rename_i st2 hS2
            have hK2 := hK1.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2)
            have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hS2
            have hK3 := hK2.trans (chainObjectsKept.wakeThread st2 sender core hI2)
            have hI3 := wakeThread_preserves_objects_invExt st2 sender core hI2
            split
            · rename_i st4 hS4
              exact lendingLabelsEqual_of_linksShrink hFlow
                (hK3.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI3 hS4)).linksShrink
            · exact hFlow
    · split
      · exact hFlow
      · rename_i stC hC
        have hF0 := cleanupPreReceiveDonationMigrated_preserves_lendingLabelsEqual hInv hFlow hC
        have hI0 := cleanupPreReceiveDonationMigrated_preserves_objects_invExt _ _ _ hInv hC
        split
        · exact hFlow
        · rename_i st1 hE
          have hK1 := chainObjectsKept.endpointQueueEnqueue hI0 hE
          have hI1 := endpointQueueEnqueue_preserves_objects_invExt _ _ _ _ _ hI0 hE
          split
          · exact hFlow
          · rename_i st2 hS2
            have hK2 := hK1.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2)
            have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hS2
            have hS2' := hK2.linksShrink
            split
            · exact lendingLabelsEqual_of_linksShrink hF0
                (hS2'.trans (chainObjectsKept.removeRunnableOnCore _ receiver core).linksShrink)
            · split
              · split
                · exact hFlow
                · rename_i hT3 _ _ st3 hS3
                  have hI3 := SystemState.recordReplyStasher_objects_invExt st2
                    (SeLe4n.ReplyId.optCode replyId) receiver hI2
                  exact lendingLabelsEqual_of_linksShrink hF0 (hS2'.trans
                    ((recordReplyStasher_linksShrink st2 _ receiver hI2).trans
                    ((contextStackLinksShrink_storeObject_other hI3 hS3 (fun _ e => by cases e)
                      (fun _ e => by cases e) (.ofTcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp
                        ((SystemState.recordReplyStasher_getTcb? st2 _ receiver hI2 receiver).trans
                          hT3)) (.inr ⟨rfl, rfl⟩))).trans
                      (chainObjectsKept.removeRunnableOnCore _ receiver core).linksShrink)))
              · exact hFlow
  · split <;> exact hFlow

/-- **The lenders across the receive body's checks-first form**: it is the
specification (`endpointReceiveDualOnCore_eq_checked`), so the lenders it
keeps are the specification's. -/
theorem endpointReceiveDualOnCoreChecked_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st : SystemState} {endpointId : SeLe4n.ObjId} {receiver : SeLe4n.ThreadId}
    {replyId : Option SeLe4n.ReplyId} {core : Concurrency.CoreId} (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hFlow : lendingLabelsEqual ctx st) :
    lendingLabelsEqual ctx
      (endpointReceiveDualOnCoreChecked endpointId receiver replyId core st).1 := by
  rw [← endpointReceiveDualOnCore_eq_checked]
  exact endpointReceiveDualOnCore_preserves_lendingLabelsEqual hInv hChain hFlow

/-- **The lenders across the single-core receive** (`endpointReceiveDual`). -/
theorem endpointReceiveDual_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st st' : SystemState} {endpointId : SeLe4n.ObjId} {receiver t : SeLe4n.ThreadId}
    {replyId : Option SeLe4n.ReplyId} (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hFlow : lendingLabelsEqual ctx st)
    (h : endpointReceiveDual endpointId receiver replyId st = .ok (t, st')) :
    lendingLabelsEqual ctx st' := by
  unfold endpointReceiveDual at h
  split at h <;> try cases h
  split at h
  · split at h <;> try cases h
    rename_i sender senderTcb st1 hPop
    have hK1 := chainObjectsKept.endpointQueuePopHead hInv hPop
    have hI1 := endpointQueuePopHead_preserves_objects_invExt _ _ _ _ _ _ hInv hPop
    dsimp only at h
    split at h
    · simp only [↓reduceIte] at h
      split at h
      · split at h <;> try cases h
        rename_i st2 hS2
        have hK2 := hK1.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2)
        have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hS2
        split at h <;> try cases h
        split at h <;> try cases h
        rename_i st3 hL
        obtain ⟨⟨rep, hR, hN⟩, hOff, hI3⟩ := linkCallerReply_linksShrinkOff hI2 hL
        split at h <;> try cases h
        rename_i st4 hS4
        exact lendingLabelsEqual_of_keptLink hChain hFlow hK2 hR hN
          (hOff.trans_shrink (chainObjectsKept.storeTcbIpcStateAndMessage hI3 hS4).linksShrink)
          (chainObjectsKept.linkReplyWaiter _ _ receiver)
      · split at h <;> try cases h
        rename_i st2 hS2
        have hK2 := hK1.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2)
        have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hS2
        have hK3 := hK2.trans (chainObjectsKept.updateTcb st2 sender
          (fun t => { t with threadState := .Inactive }) hI2)
        have hI3 := SystemState.updateTcb_preserves_objects_invExt st2 sender
          (fun t => { t with threadState := .Inactive }) hI2
        split at h <;> try cases h
        rename_i st4 hS4
        exact lendingLabelsEqual_of_linksShrink hFlow
          (hK3.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI3 hS4)).linksShrink
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      split at h <;> try cases h
      rename_i st2 hS2
      have hK2 := hK1.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2)
      have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hS2
      have hK3 := hK2.trans (chainObjectsKept.of_objectsAgreeOffRunLinks
        (ensureRunnable_objectsAgreeOffRunLinks st2 sender))
      have hI3 := ensureRunnable_objects_invExt st2 sender hI2
      split at h <;> try cases h
      rename_i st4 hS4
      exact lendingLabelsEqual_of_linksShrink hFlow
        (hK3.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI3 hS4)).linksShrink
  · split at h <;> try cases h
    rename_i stC hC
    have hF0 := cleanupPreReceiveDonationChecked_preserves_lendingLabelsEqual hInv hFlow hC
    have hI0 := cleanupPreReceiveDonationChecked_objects_invExt hInv hC
    split at h <;> try cases h
    rename_i st1 hE
    have hK1 := chainObjectsKept.endpointQueueEnqueue hI0 hE
    have hI1 := endpointQueueEnqueue_preserves_objects_invExt _ _ _ _ _ hI0 hE
    split at h <;> try cases h
    rename_i st2 hS2
    have hK2 := hK1.trans (chainObjectsKept.storeTcbIpcStateAndMessage hI1 hS2)
    have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hS2
    have hS2' := hK2.linksShrink
    split at h
    · cases h
      exact lendingLabelsEqual_of_linksShrink hF0 (hS2'.trans
        (chainObjectsKept.of_objectsAgreeOffRunLinks
          (removeRunnable_objectsAgreeOffRunLinks _ receiver)).linksShrink)
    · split at h
      · split at h <;> try cases h
        rename_i hT3 _ _ st3 hS3
        have hI3 := SystemState.recordReplyStasher_objects_invExt st2
          (SeLe4n.ReplyId.optCode replyId) receiver hI2
        exact lendingLabelsEqual_of_linksShrink hF0 (hS2'.trans
          ((recordReplyStasher_linksShrink st2 _ receiver hI2).trans
          ((contextStackLinksShrink_storeObject_other hI3 hS3 (fun _ e => by cases e)
            (fun _ e => by cases e) (.ofTcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp
              ((SystemState.recordReplyStasher_getTcb? st2 _ receiver hI2 receiver).trans
                hT3)) (.inr ⟨rfl, rfl⟩))).trans
            (chainObjectsKept.of_objectsAgreeOffRunLinks
              (removeRunnable_objectsAgreeOffRunLinks _ receiver)).linksShrink)))
      · cases h

end SeLe4n.Kernel
