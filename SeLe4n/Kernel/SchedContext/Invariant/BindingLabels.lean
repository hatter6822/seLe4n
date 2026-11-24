-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.Policy

/-!
# Equal binding labels

WS-SX SX10 (D36, D37).  Every binding pair carries equal labels: a thread
holding a context (its binding word, bound or lent), a context's thread word,
and a notification bound to a context each name an object labelled as the
holder is (`bindingLabelsEqual`).

The predicate reads three words of the object store and nothing else: a TCB's
`scBindingScCode`, a context's `boundThreadCode` and a notification's
`schedContextCode`.  A state that holds no binding word satisfies it outright
(`bindingLabelsEqual_of_unbound`): that is every booted state, because the
checked boot refuses a configured object carrying any of the three words
(`bootSafeObjectCheck`) and builds none (the boot base case,
`bootFromPlatformCheckedStartedFor_bindingLabelsEqual`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **Every binding pair carries equal labels** (WS-SX SX9.1 and SX10, D37): a
thread holding a context (its binding word, bound or lent), a context's thread
word, and a notification bound to a context each name an object labelled as the
holder is.  The finer projection (D34) shows a binding word exactly where the
object it names is seen, so with equal labels a binding word is shown exactly
where its holder is: no observer sees a holder and misses what it holds, or the
reverse. -/
def bindingLabelsEqual (ctx : LabelingContext) (st : SystemState) : Prop :=
  (∀ (t : SeLe4n.ThreadId) (tcb : TCB) (s : SeLe4n.SchedContextId),
    st.objects[t.toObjId]? = some (.tcb tcb) → tcb.scBindingScCode = s.val + 1 →
    ctx.threadLabelOf t = ctx.objectLabelOf s.toObjId) ∧
  (∀ (s : SeLe4n.SchedContextId) (sc : SchedContext) (t : SeLe4n.ThreadId),
    st.objects[s.toObjId]? = some (.schedContext sc) → sc.boundThreadCode = t.val + 1 →
    ctx.threadLabelOf t = ctx.objectLabelOf s.toObjId) ∧
  (∀ (n : SeLe4n.ObjId) (ntfn : Notification) (s : SeLe4n.SchedContextId),
    st.objects[n]? = some (.notification ntfn) → ntfn.schedContextCode = s.val + 1 →
    ctx.objectLabelOf n = ctx.objectLabelOf s.toObjId) ∧
  (∀ (t : SeLe4n.ThreadId) (tcb : TCB) (s : SeLe4n.SchedContextId) (o : SeLe4n.ThreadId),
    st.objects[t.toObjId]? = some (.tcb tcb) → tcb.scBindingScCode = s.val + 1 →
    tcb.scBindingOwnerCode = o.val + 1 → ctx.threadLabelOf o = ctx.objectLabelOf s.toObjId)

/-- **An object holding no binding word**: a thread bound or lent no context, a
context bound to no thread, a notification bound to no context, or any other
kind of object. -/
def bindingFreeObject : KernelObject → Prop
  | .tcb t => t.scBindingScCode = 0
  | .schedContext sc => sc.boundThreadCode = 0
  | .notification n => n.schedContextCode = 0
  | _ => True

/-- **A state holding no binding word has equal binding labels**, under every
labelling: there is no pair to compare. -/
theorem bindingLabelsEqual_of_unbound {st : SystemState}
    (h : ∀ (k : SeLe4n.ObjId) (o : KernelObject), st.objects[k]? = some o → bindingFreeObject o)
    (ctx : LabelingContext) : bindingLabelsEqual ctx st := by
  refine ⟨fun t tcb s hT hC => ?_, fun s sc t hS hC => ?_, fun n ntfn s hN hC => ?_,
    fun t tcb s o hT hC _ => ?_⟩
  · have := h _ _ hT; simp only [bindingFreeObject] at this; omega
  · have := h _ _ hS; simp only [bindingFreeObject] at this; omega
  · have := h _ _ hN; simp only [bindingFreeObject] at this; omega
  · have := h _ _ hT; simp only [bindingFreeObject] at this; omega

/-- **A lent binding's holder and owner carry the context's label.** -/
theorem bindingLabelsEqual.donated {ctx : LabelingContext} {st : SystemState}
    (hB : bindingLabelsEqual ctx st) {t : SeLe4n.ThreadId} {tcb : TCB}
    {s : SeLe4n.SchedContextId} {o : SeLe4n.ThreadId}
    (hT : st.objects[t.toObjId]? = some (.tcb tcb)) (hD : tcb.schedContextBinding = .donated s o) :
    ctx.threadLabelOf t = ctx.objectLabelOf s.toObjId ∧
      ctx.threadLabelOf o = ctx.objectLabelOf s.toObjId := by
  have hc : tcb.scBindingScCode = s.val + 1 := by
    have := congrArg SchedContextBinding.scCode hD
    rw [TCB.schedContextBinding, SchedContextBinding.scCode_ofCodes] at this
    exact this
  have ho : tcb.scBindingOwnerCode = o.val + 1 := by
    have := congrArg SchedContextBinding.ownerCode hD
    simp only [TCB.schedContextBinding, hc, SchedContextBinding.ownerCode_ofCodes_succ] at this
    simpa [SchedContextBinding.ownerCode] using this
  exact ⟨hB.1 t tcb s hT hc, hB.2.2.2 t tcb s o hT hc ho⟩

/-- **A bound binding's holder carries the context's label.** -/
theorem bindingLabelsEqual.bound {ctx : LabelingContext} {st : SystemState}
    (hB : bindingLabelsEqual ctx st) {t : SeLe4n.ThreadId} {tcb : TCB}
    {s : SeLe4n.SchedContextId}
    (hT : st.objects[t.toObjId]? = some (.tcb tcb)) (hD : tcb.schedContextBinding.scId? = some s) :
    ctx.threadLabelOf t = ctx.objectLabelOf s.toObjId := by
  refine hB.1 t tcb s hT ?_
  simp only [TCB.schedContextBinding, SchedContextBinding.ofCodes] at hD
  split at hD
  · simp [SchedContextBinding.scId?] at hD
  · rename_i k hk
    rw [hk]
    split at hD <;> simp only [SchedContextBinding.scId?, Option.some.injEq] at hD <;> subst hD <;> rfl

/-! ### The binding views

`bindingLabelsEqual` restated over four views of the object store, each a
binding word read at a slot (`0` where the slot holds no object of that kind).
The frame family of the lenders' flow (`contextStackViewsAgree`) is to carry
them (WS-SX SX14, the `bindingLabelsEqual` row of `docs/REGISTERED_DEBT.md`),
so a step that writes none of the four words carries the predicate, and a step
after which every binding word was already there before it (a removal, a
clear) carries it too (`bindingLabelsEqual_of_shrink`). -/

/-- A thread's binding word: the context it holds, bound or lent. -/
def threadContextView (st : SystemState) (t : SeLe4n.ThreadId) : Nat :=
  match st.getTcb? t with
  | some tcb => tcb.scBindingScCode
  | none => 0

/-- A thread's owner word: the thread its lent context goes back to. -/
def threadOwnerView (st : SystemState) (t : SeLe4n.ThreadId) : Nat :=
  match st.getTcb? t with
  | some tcb => tcb.scBindingOwnerCode
  | none => 0

/-- A context's thread word. -/
def contextThreadView (st : SystemState) (s : SeLe4n.SchedContextId) : Nat :=
  match st.getSchedContext? s with
  | some sc => sc.boundThreadCode
  | none => 0

/-- A notification's context word. -/
def notificationContextView (st : SystemState) (n : SeLe4n.ObjId) : Nat :=
  match st.getNotification? n with
  | some ntfn => ntfn.schedContextCode
  | none => 0

/-- **`bindingLabelsEqual` in the views.** -/
theorem bindingLabelsEqual_iff_views {ctx : LabelingContext} {st : SystemState} :
    bindingLabelsEqual ctx st ↔
      (∀ t (s : SeLe4n.SchedContextId), threadContextView st t = s.val + 1 →
        ctx.threadLabelOf t = ctx.objectLabelOf s.toObjId) ∧
      (∀ s (t : SeLe4n.ThreadId), contextThreadView st s = t.val + 1 →
        ctx.threadLabelOf t = ctx.objectLabelOf s.toObjId) ∧
      (∀ n (s : SeLe4n.SchedContextId), notificationContextView st n = s.val + 1 →
        ctx.objectLabelOf n = ctx.objectLabelOf s.toObjId) ∧
      (∀ t (s : SeLe4n.SchedContextId) (o : SeLe4n.ThreadId), threadContextView st t = s.val + 1 →
        threadOwnerView st t = o.val + 1 → ctx.threadLabelOf o = ctx.objectLabelOf s.toObjId) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun t s hV => ?_, fun s t hV => ?_, fun n s hV => ?_, fun t s o hV hW => ?_⟩
    · unfold threadContextView at hV
      split at hV
      · next tcb hO => exact h1 t tcb s ((SystemState.getTcb?_eq_some_iff _ _ _).mp hO) hV
      · omega
    · unfold contextThreadView at hV
      split at hV
      · next sc hO => exact h2 s sc t ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hO) hV
      · omega
    · unfold notificationContextView at hV
      split at hV
      · next ntfn hO => exact h3 n ntfn s ((SystemState.getNotification?_eq_some_iff _ _ _).mp hO) hV
      · omega
    · unfold threadContextView at hV; unfold threadOwnerView at hW
      split at hV
      · next tcb hO =>
        rw [hO] at hW
        exact h4 t tcb s o ((SystemState.getTcb?_eq_some_iff _ _ _).mp hO) hV hW
      · omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun t tcb s hO hC => h1 t s ?_, fun s sc t hO hC => h2 s t ?_,
      fun n ntfn s hO hC => h3 n s ?_, fun t tcb s o hO hC hW => h4 t s o ?_ ?_⟩
    · simp only [threadContextView, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO, hC]
    · simp only [contextThreadView, (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hO, hC]
    · simp only [notificationContextView, (SystemState.getNotification?_eq_some_iff _ _ _).mpr hO, hC]
    · simp only [threadContextView, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO, hC]
    · simp only [threadOwnerView, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO, hW]

/-- **The binding shrink**: every binding word after the step was the same word
before it.  A clear, a removal and a frame are shrinks; a word written to a new
value is not, which is the case the creating sites prove from their gates. -/
structure bindingViewsShrink (st st' : SystemState) : Prop where
  thread : ∀ t k, threadContextView st' t = k + 1 → threadContextView st t = k + 1
  context : ∀ s k, contextThreadView st' s = k + 1 → contextThreadView st s = k + 1
  notification : ∀ n k, notificationContextView st' n = k + 1 →
    notificationContextView st n = k + 1
  owner : ∀ t k o, threadContextView st' t = k + 1 → threadOwnerView st' t = o + 1 →
    threadContextView st t = k + 1 ∧ threadOwnerView st t = o + 1

namespace bindingViewsShrink

theorem refl (st : SystemState) : bindingViewsShrink st st :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ _ h h' => ⟨h, h'⟩⟩

theorem trans {st st' st'' : SystemState} (h1 : bindingViewsShrink st st')
    (h2 : bindingViewsShrink st' st'') : bindingViewsShrink st st'' :=
  ⟨fun t k h => h1.thread t k (h2.thread t k h), fun s k h => h1.context s k (h2.context s k h),
   fun n k h => h1.notification n k (h2.notification n k h),
   fun t k o h h' => let p := h2.owner t k o h h'; h1.owner t k o p.1 p.2⟩

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    bindingViewsShrink st st' :=
  ⟨fun t k hV => by simpa only [threadContextView, SystemState.getTcb?, h] using hV,
   fun s k hV => by simpa only [contextThreadView, SystemState.getSchedContext?, h] using hV,
   fun n k hV => by simpa only [notificationContextView, SystemState.getNotification?, h] using hV,
   fun t k o hV hW => by
     simp only [threadContextView, threadOwnerView, SystemState.getTcb?, h] at hV hW ⊢
     exact ⟨hV, hW⟩⟩

end bindingViewsShrink

/-- **A shrink carries equal binding labels.** -/
theorem bindingLabelsEqual_of_shrink {ctx : LabelingContext} {st st' : SystemState}
    (hInv : bindingLabelsEqual ctx st) (h : bindingViewsShrink st st') :
    bindingLabelsEqual ctx st' := by
  rw [bindingLabelsEqual_iff_views] at hInv ⊢
  exact ⟨fun t s hV => hInv.1 t s (h.thread t _ hV), fun s t hV => hInv.2.1 s t (h.context s _ hV),
    fun n s hV => hInv.2.2.1 n s (h.notification n _ hV),
    fun t s o hV hW => let p := h.owner t _ _ hV hW; hInv.2.2.2 t s o p.1 p.2⟩

/-! ### The binding words read slot by slot

The four views read one slot each: a thread's two words at its slot, a
context's at its slot and a notification's at its slot.  `objBindingWords` is
the four read off one slot, so a step that writes one slot carries the views
everywhere else and is judged at that slot alone (`bindingViewsShrink_of_slot`).
-/

/-- **A slot's binding words**: a thread's context and owner words, a context's
thread word and a notification's context word, `0` where the slot holds no
object of that kind. -/
def objBindingWords : Option KernelObject → Nat × Nat × Nat × Nat
  | some (.tcb t) => (t.scBindingScCode, t.scBindingOwnerCode, 0, 0)
  | some (.schedContext sc) => (0, 0, sc.boundThreadCode, 0)
  | some (.notification n) => (0, 0, 0, n.schedContextCode)
  | _ => (0, 0, 0, 0)

theorem threadContextView_eq_obj (st : SystemState) (t : SeLe4n.ThreadId) :
    threadContextView st t = (objBindingWords st.objects[t.toObjId]?).1 := by
  unfold threadContextView SystemState.getTcb?
  cases st.objects[t.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem threadOwnerView_eq_obj (st : SystemState) (t : SeLe4n.ThreadId) :
    threadOwnerView st t = (objBindingWords st.objects[t.toObjId]?).2.1 := by
  unfold threadOwnerView SystemState.getTcb?
  cases st.objects[t.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem contextThreadView_eq_obj (st : SystemState) (s : SeLe4n.SchedContextId) :
    contextThreadView st s = (objBindingWords st.objects[s.toObjId]?).2.2.1 := by
  unfold contextThreadView SystemState.getSchedContext?
  cases st.objects[s.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem notificationContextView_eq_obj (st : SystemState) (n : SeLe4n.ObjId) :
    notificationContextView st n = (objBindingWords st.objects[n]?).2.2.2 := by
  unfold notificationContextView SystemState.getNotification?
  cases st.objects[n]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- **One slot's binding words shrink**: every word the slot holds after the
step it held before it (the owner word read together with the context word). -/
structure objBindingShrink (old new : Option KernelObject) : Prop where
  thread : ∀ k, (objBindingWords new).1 = k + 1 → (objBindingWords old).1 = k + 1
  context : ∀ k, (objBindingWords new).2.2.1 = k + 1 → (objBindingWords old).2.2.1 = k + 1
  notification : ∀ k, (objBindingWords new).2.2.2 = k + 1 → (objBindingWords old).2.2.2 = k + 1
  owner : ∀ k o, (objBindingWords new).1 = k + 1 → (objBindingWords new).2.1 = o + 1 →
    (objBindingWords old).1 = k + 1 ∧ (objBindingWords old).2.1 = o + 1

namespace objBindingShrink

/-- Equal words shrink. -/
theorem of_eq {old new : Option KernelObject} (h : objBindingWords new = objBindingWords old) :
    objBindingShrink old new :=
  ⟨fun _ hk => h ▸ hk, fun _ hk => h ▸ hk, fun _ hk => h ▸ hk, fun _ _ hk ho => h ▸ ⟨hk, ho⟩⟩

/-- A slot left holding no binding word shrinks. -/
theorem of_free {old new : Option KernelObject} (h : objBindingWords new = (0, 0, 0, 0)) :
    objBindingShrink old new :=
  ⟨fun _ hk => (by rw [h] at hk; cases hk), fun _ hk => (by rw [h] at hk; cases hk),
   fun _ hk => (by rw [h] at hk; cases hk), fun _ _ hk _ => (by rw [h] at hk; cases hk)⟩

/-- **A thread record written keeping both its words, or clearing its context
word.** -/
theorem ofTcb {old : Option KernelObject} {t t' : TCB} (hOld : old = some (.tcb t))
    (h : t'.scBindingScCode = 0 ∨
      (t'.scBindingScCode = t.scBindingScCode ∧ t'.scBindingOwnerCode = t.scBindingOwnerCode)) :
    objBindingShrink old (some (.tcb t')) := by
  subst hOld
  rcases h with h | ⟨h1, h2⟩
  · exact ⟨fun _ hk => (by simp only [objBindingWords, h] at hk; omega),
      fun _ hk => (by simp only [objBindingWords] at hk; omega),
      fun _ hk => (by simp only [objBindingWords] at hk; omega),
      fun _ _ hk _ => (by simp only [objBindingWords, h] at hk; omega)⟩
  · exact of_eq (by simp only [objBindingWords, h1, h2])

/-- **A thread record written keeping its binding** (`TCB.schedContextBinding`):
the context word is the binding's, and the owner word is read back from it
wherever the context word names a context. -/
theorem ofTcbBinding {old : Option KernelObject} {t t' : TCB} (hOld : old = some (.tcb t))
    (h : t'.schedContextBinding = t.schedContextBinding) :
    objBindingShrink old (some (.tcb t')) := by
  subst hOld
  have hc : t'.scBindingScCode = t.scBindingScCode := by
    have := congrArg SchedContextBinding.scCode h
    simpa only [TCB.schedContextBinding, SchedContextBinding.scCode_ofCodes] using this
  refine ⟨fun _ hk => (by simp only [objBindingWords, hc] at hk ⊢; exact hk),
    fun _ hk => (by simp only [objBindingWords] at hk; omega),
    fun _ hk => (by simp only [objBindingWords] at hk; omega), fun k o hk ho => ?_⟩
  simp only [objBindingWords] at hk ho ⊢
  have hk' : t.scBindingScCode = k + 1 := hc ▸ hk
  have := congrArg SchedContextBinding.ownerCode h
  simp only [TCB.schedContextBinding, hk, hk', SchedContextBinding.ownerCode_ofCodes_succ] at this
  exact ⟨hk', this ▸ ho⟩

/-- **A thread record written keeping its context word and clearing its owner
word** (a holder whose lender has gone). -/
theorem ofTcbOwnerCleared {old : Option KernelObject} {t t' : TCB} (hOld : old = some (.tcb t))
    (h1 : t'.scBindingScCode = t.scBindingScCode) (h2 : t'.scBindingOwnerCode = 0) :
    objBindingShrink old (some (.tcb t')) := by
  subst hOld
  exact ⟨fun _ hk => (by simp only [objBindingWords, h1] at hk ⊢; exact hk),
    fun _ hk => (by simp only [objBindingWords] at hk; omega),
    fun _ hk => (by simp only [objBindingWords] at hk; omega),
    fun _ _ _ ho => (by simp only [objBindingWords, h2] at ho; omega)⟩

/-- **A notification written keeping or clearing its context word.** -/
theorem ofNotification {old : Option KernelObject} {n n' : Notification}
    (hOld : old = some (.notification n))
    (h : n'.schedContextCode = 0 ∨ n'.schedContextCode = n.schedContextCode) :
    objBindingShrink old (some (.notification n')) := by
  subst hOld
  rcases h with h | h
  · exact of_free (by simp only [objBindingWords, h])
  · exact of_eq (by simp only [objBindingWords, h])

/-- **A context written keeping or clearing its thread word.** -/
theorem ofSchedContext {old : Option KernelObject} {sc sc' : SchedContext}
    (hOld : old = some (.schedContext sc))
    (h : sc'.boundThreadCode = 0 ∨ sc'.boundThreadCode = sc.boundThreadCode) :
    objBindingShrink old (some (.schedContext sc')) := by
  subst hOld
  rcases h with h | h
  · exact of_free (by simp only [objBindingWords, h])
  · exact of_eq (by simp only [objBindingWords, h])

end objBindingShrink

/-- **The binding shrink read slot by slot.** -/
theorem bindingViewsShrink_of_objects {st st' : SystemState}
    (h : ∀ x : SeLe4n.ObjId, objBindingShrink st.objects[x]? st'.objects[x]?) : bindingViewsShrink st st' :=
  ⟨fun t k hV => by rw [threadContextView_eq_obj] at hV ⊢; exact (h _).thread k hV,
   fun s k hV => by rw [contextThreadView_eq_obj] at hV ⊢; exact (h _).context k hV,
   fun n k hV => by rw [notificationContextView_eq_obj] at hV ⊢; exact (h _).notification k hV,
   fun t k o hV hW => by
     rw [threadContextView_eq_obj] at hV ⊢; rw [threadOwnerView_eq_obj] at hW ⊢
     exact (h _).owner k o hV hW⟩

/-- **One slot written**: the binding shrink is judged at that slot alone. -/
theorem bindingViewsShrink_of_slot {st st' : SystemState} (k : SeLe4n.ObjId)
    (hNe : ∀ x, x ≠ k → st'.objects[x]? = st.objects[x]?)
    (hK : objBindingShrink st.objects[k]? st'.objects[k]?) : bindingViewsShrink st st' :=
  bindingViewsShrink_of_objects fun x => by
    by_cases hx : x = k
    · subst hx; exact hK
    · rw [hNe x hx]; exact .of_eq rfl

/-- **Each thread keeps its binding, and each context and notification after
the step was there before it**: the form a step's thread-binding frame and its
non-thread frame give, read as a shrink. -/
theorem bindingViewsShrink_of_tcbBinding {st st' : SystemState}
    (hT : ∀ x : SeLe4n.ThreadId,
      (st'.getTcb? x).map (·.schedContextBinding) = (st.getTcb? x).map (·.schedContextBinding))
    (hS : ∀ s sc, st'.getSchedContext? s = some sc → st.getSchedContext? s = some sc)
    (hN : ∀ n ntfn, st'.getNotification? n = some ntfn → st.getNotification? n = some ntfn) :
    bindingViewsShrink st st' := by
  have key : ∀ t k, threadContextView st' t = k + 1 →
      ∃ a b, st'.getTcb? t = some a ∧ st.getTcb? t = some b ∧ a.scBindingScCode = k + 1 ∧
        b.scBindingScCode = k + 1 ∧ a.scBindingOwnerCode = b.scBindingOwnerCode := by
    intro t k hV
    unfold threadContextView at hV
    have h := hT t
    cases h1 : st'.getTcb? t with
    | none => rw [h1] at hV; cases hV
    | some a =>
      rw [h1] at hV h
      cases h2 : st.getTcb? t with
      | none => rw [h2] at h; cases h
      | some b =>
        rw [h2] at h
        have hE := Option.some.inj h
        have hb := congrArg SchedContextBinding.scCode hE
        simp only [TCB.schedContextBinding, SchedContextBinding.scCode_ofCodes] at hb
        have hk : b.scBindingScCode = k + 1 := hb ▸ hV
        have ho := congrArg SchedContextBinding.ownerCode hE
        simp only [TCB.schedContextBinding, hV, hk, SchedContextBinding.ownerCode_ofCodes_succ] at ho
        exact ⟨a, b, rfl, rfl, hV, hk, ho⟩
  refine ⟨fun t k hV => ?_, fun s k hV => ?_, fun n k hV => ?_, fun t k o hV hW => ?_⟩
  · obtain ⟨a, b, -, h2, -, hk, -⟩ := key t k hV
    unfold threadContextView; rw [h2]; exact hk
  · unfold contextThreadView at hV ⊢
    cases h1 : st'.getSchedContext? s with
    | none => rw [h1] at hV; cases hV
    | some sc => rw [h1] at hV; rw [hS s sc h1]; exact hV
  · unfold notificationContextView at hV ⊢
    cases h1 : st'.getNotification? n with
    | none => rw [h1] at hV; cases hV
    | some ntfn => rw [h1] at hV; rw [hN n ntfn h1]; exact hV
  · obtain ⟨a, b, h1, h2, -, hk, ho⟩ := key t k hV
    unfold threadOwnerView at hW
    unfold threadContextView threadOwnerView
    rw [h1] at hW; rw [h2]
    exact ⟨hk, ho.symm.trans hW⟩

/-! ### The binding grow: the step a creating site is

A step that writes a binding word to a new value (a bind, a lend, the return to
an owner) is not a shrink.  It carries the predicate when every word after it
is either one the state already had or names an object labelled as the holder
(`bindingLabelsEqual_of_grow`): the label equation a creating site proves from
its gate or from the invariant it is carried under. -/

/-- **The binding grow**: every binding word after the step was there before
it or pairs equal labels. -/
structure bindingViewsGrow (ctx : LabelingContext) (st st' : SystemState) : Prop where
  thread : ∀ t (s : SeLe4n.SchedContextId), threadContextView st' t = s.val + 1 →
    threadContextView st t = s.val + 1 ∨ ctx.threadLabelOf t = ctx.objectLabelOf s.toObjId
  context : ∀ s (t : SeLe4n.ThreadId), contextThreadView st' s = t.val + 1 →
    contextThreadView st s = t.val + 1 ∨ ctx.threadLabelOf t = ctx.objectLabelOf s.toObjId
  notification : ∀ n (s : SeLe4n.SchedContextId), notificationContextView st' n = s.val + 1 →
    notificationContextView st n = s.val + 1 ∨ ctx.objectLabelOf n = ctx.objectLabelOf s.toObjId
  owner : ∀ t (s : SeLe4n.SchedContextId) (o : SeLe4n.ThreadId),
    threadContextView st' t = s.val + 1 → threadOwnerView st' t = o.val + 1 →
    (threadContextView st t = s.val + 1 ∧ threadOwnerView st t = o.val + 1) ∨
      ctx.threadLabelOf o = ctx.objectLabelOf s.toObjId

namespace bindingViewsGrow

theorem of_shrink {ctx : LabelingContext} {st st' : SystemState} (h : bindingViewsShrink st st') :
    bindingViewsGrow ctx st st' :=
  ⟨fun t _ hV => .inl (h.thread t _ hV), fun s _ hV => .inl (h.context s _ hV),
   fun n _ hV => .inl (h.notification n _ hV), fun t _ _ hV hW => .inl (h.owner t _ _ hV hW)⟩

theorem trans {ctx : LabelingContext} {st st' st'' : SystemState} (h1 : bindingViewsGrow ctx st st')
    (h2 : bindingViewsGrow ctx st' st'') : bindingViewsGrow ctx st st'' :=
  ⟨fun t s hV => (h2.thread t s hV).elim (h1.thread t s) .inr,
   fun s t hV => (h2.context s t hV).elim (h1.context s t) .inr,
   fun n s hV => (h2.notification n s hV).elim (h1.notification n s) .inr,
   fun t s o hV hW => (h2.owner t s o hV hW).elim (fun p => h1.owner t s o p.1 p.2) .inr⟩

end bindingViewsGrow

/-- **A grow carries equal binding labels.** -/
theorem bindingLabelsEqual_of_grow {ctx : LabelingContext} {st st' : SystemState}
    (hInv : bindingLabelsEqual ctx st) (h : bindingViewsGrow ctx st st') :
    bindingLabelsEqual ctx st' := by
  rw [bindingLabelsEqual_iff_views] at hInv ⊢
  exact ⟨fun t s hV => (h.thread t s hV).elim (hInv.1 t s) id,
    fun s t hV => (h.context s t hV).elim (hInv.2.1 s t) id,
    fun n s hV => (h.notification n s hV).elim (hInv.2.2.1 n s) id,
    fun t s o hV hW => (h.owner t s o hV hW).elim (fun p => hInv.2.2.2 t s o p.1 p.2) id⟩

/-- **A thread record written at one slot**, every other slot's binding words unchanged: the
grow holds where the record's context word names a context labelled as the
thread and its owner word an owner labelled as that context. -/
theorem bindingViewsGrow_of_tcbSlot {ctx : LabelingContext} {st st' : SystemState}
    {t0 : SeLe4n.ThreadId} {tcb' : TCB}
    (hNe : ∀ x, x ≠ t0.toObjId → objBindingWords st'.objects[x]? = objBindingWords st.objects[x]?)
    (hK : st'.objects[t0.toObjId]? = some (.tcb tcb'))
    (hT : ∀ s : SeLe4n.SchedContextId, tcb'.scBindingScCode = s.val + 1 →
      ctx.threadLabelOf t0 = ctx.objectLabelOf s.toObjId)
    (hO : ∀ (s : SeLe4n.SchedContextId) (o : SeLe4n.ThreadId), tcb'.scBindingScCode = s.val + 1 →
      tcb'.scBindingOwnerCode = o.val + 1 → ctx.threadLabelOf o = ctx.objectLabelOf s.toObjId) :
    bindingViewsGrow ctx st st' := by
  refine ⟨fun t s hV => ?_, fun s t hV => ?_, fun n s hV => ?_, fun t s o hV hW => ?_⟩
  · rw [threadContextView_eq_obj] at hV ⊢
    by_cases hx : t.toObjId = t0.toObjId
    · rw [hx, hK] at hV; rw [SeLe4n.ThreadId.toObjId_injective _ _ hx]; exact .inr (hT s hV)
    · rw [hNe _ hx] at hV; exact .inl hV
  · rw [contextThreadView_eq_obj] at hV ⊢
    by_cases hx : s.toObjId = t0.toObjId
    · rw [hx, hK] at hV; cases hV
    · rw [hNe _ hx] at hV; exact .inl hV
  · rw [notificationContextView_eq_obj] at hV ⊢
    by_cases hx : n = t0.toObjId
    · rw [hx, hK] at hV; cases hV
    · rw [hNe _ hx] at hV; exact .inl hV
  · rw [threadContextView_eq_obj] at hV ⊢; rw [threadOwnerView_eq_obj] at hW ⊢
    by_cases hx : t.toObjId = t0.toObjId
    · rw [hx, hK] at hV hW; exact .inr (hO s o hV hW)
    · rw [hNe _ hx] at hV hW; exact .inl ⟨hV, hW⟩

/-- **A context record written at one slot**, every other slot's binding words unchanged: the
grow holds where its thread word names a thread labelled as the context. -/
theorem bindingViewsGrow_of_schedContextSlot {ctx : LabelingContext} {st st' : SystemState}
    {s0 : SeLe4n.SchedContextId} {sc' : SchedContext}
    (hNe : ∀ x, x ≠ s0.toObjId → objBindingWords st'.objects[x]? = objBindingWords st.objects[x]?)
    (hK : st'.objects[s0.toObjId]? = some (.schedContext sc'))
    (hC : ∀ t : SeLe4n.ThreadId, sc'.boundThreadCode = t.val + 1 →
      ctx.threadLabelOf t = ctx.objectLabelOf s0.toObjId) :
    bindingViewsGrow ctx st st' := by
  refine ⟨fun t s hV => ?_, fun s t hV => ?_, fun n s hV => ?_, fun t s o hV hW => ?_⟩
  · rw [threadContextView_eq_obj] at hV ⊢
    by_cases hx : t.toObjId = s0.toObjId
    · rw [hx, hK] at hV; cases hV
    · rw [hNe _ hx] at hV; exact .inl hV
  · rw [contextThreadView_eq_obj] at hV ⊢
    by_cases hx : s.toObjId = s0.toObjId
    · rw [hx, hK] at hV; rw [SeLe4n.SchedContextId.toObjId_injective _ _ hx]; exact .inr (hC t hV)
    · rw [hNe _ hx] at hV; exact .inl hV
  · rw [notificationContextView_eq_obj] at hV ⊢
    by_cases hx : n = s0.toObjId
    · rw [hx, hK] at hV; cases hV
    · rw [hNe _ hx] at hV; exact .inl hV
  · rw [threadContextView_eq_obj] at hV ⊢; rw [threadOwnerView_eq_obj] at hW ⊢
    by_cases hx : t.toObjId = s0.toObjId
    · rw [hx, hK] at hV; cases hV
    · rw [hNe _ hx] at hV hW; exact .inl ⟨hV, hW⟩

/-- **A notification written at one slot**, every other slot's binding words unchanged: the
grow holds where its context word names a context labelled as the
notification. -/
theorem bindingViewsGrow_of_notificationSlot {ctx : LabelingContext} {st st' : SystemState}
    {n0 : SeLe4n.ObjId} {ntfn' : Notification}
    (hNe : ∀ x, x ≠ n0 → objBindingWords st'.objects[x]? = objBindingWords st.objects[x]?)
    (hK : st'.objects[n0]? = some (.notification ntfn'))
    (hN : ∀ s : SeLe4n.SchedContextId, ntfn'.schedContextCode = s.val + 1 →
      ctx.objectLabelOf n0 = ctx.objectLabelOf s.toObjId) :
    bindingViewsGrow ctx st st' := by
  refine ⟨fun t s hV => ?_, fun s t hV => ?_, fun n s hV => ?_, fun t s o hV hW => ?_⟩
  · rw [threadContextView_eq_obj] at hV ⊢
    by_cases hx : t.toObjId = n0
    · rw [hx, hK] at hV; cases hV
    · rw [hNe _ hx] at hV; exact .inl hV
  · rw [contextThreadView_eq_obj] at hV ⊢
    by_cases hx : s.toObjId = n0
    · rw [hx, hK] at hV; cases hV
    · rw [hNe _ hx] at hV; exact .inl hV
  · rw [notificationContextView_eq_obj] at hV ⊢
    by_cases hx : n = n0
    · subst hx; rw [hK] at hV; exact .inr (hN s hV)
    · rw [hNe _ hx] at hV; exact .inl hV
  · rw [threadContextView_eq_obj] at hV ⊢; rw [threadOwnerView_eq_obj] at hW ⊢
    by_cases hx : t.toObjId = n0
    · rw [hx, hK] at hV; cases hV
    · rw [hNe _ hx] at hV hW; exact .inl ⟨hV, hW⟩

end SeLe4n.Kernel
