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
    ctx.objectLabelOf n = ctx.objectLabelOf s.toObjId)

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
  refine ⟨fun t tcb s hT hC => ?_, fun s sc t hS hC => ?_, fun n ntfn s hN hC => ?_⟩
  · have := h _ _ hT; simp only [bindingFreeObject] at this; omega
  · have := h _ _ hS; simp only [bindingFreeObject] at this; omega
  · have := h _ _ hN; simp only [bindingFreeObject] at this; omega

/-! ### The binding views

`bindingLabelsEqual` restated over three views of the object store, each a
binding word read at a slot (`0` where the slot holds no object of that kind):
the frame family of the lenders' flow (`contextStackViewsAgree`) carries them,
so a step that writes none of the three words carries the predicate, and a step
after which every binding word was already there before it (a removal, a
clear) carries it too (`bindingLabelsEqual_of_shrink`). -/

/-- A thread's binding word: the context it holds, bound or lent. -/
def threadContextView (st : SystemState) (t : SeLe4n.ThreadId) : Nat :=
  match st.getTcb? t with
  | some tcb => tcb.scBindingScCode
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
        ctx.objectLabelOf n = ctx.objectLabelOf s.toObjId) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun t s hV => ?_, fun s t hV => ?_, fun n s hV => ?_⟩
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
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun t tcb s hO hC => h1 t s ?_, fun s sc t hO hC => h2 s t ?_,
      fun n ntfn s hO hC => h3 n s ?_⟩
    · simp only [threadContextView, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO, hC]
    · simp only [contextThreadView, (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hO, hC]
    · simp only [notificationContextView, (SystemState.getNotification?_eq_some_iff _ _ _).mpr hO, hC]

/-- **The binding shrink**: every binding word after the step was the same word
before it.  A clear, a removal and a frame are shrinks; a word written to a new
value is not, which is the case the creating sites prove from their gates. -/
structure bindingViewsShrink (st st' : SystemState) : Prop where
  thread : ∀ t k, threadContextView st' t = k + 1 → threadContextView st t = k + 1
  context : ∀ s k, contextThreadView st' s = k + 1 → contextThreadView st s = k + 1
  notification : ∀ n k, notificationContextView st' n = k + 1 →
    notificationContextView st n = k + 1

namespace bindingViewsShrink

theorem refl (st : SystemState) : bindingViewsShrink st st :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem trans {st st' st'' : SystemState} (h1 : bindingViewsShrink st st')
    (h2 : bindingViewsShrink st' st'') : bindingViewsShrink st st'' :=
  ⟨fun t k h => h1.thread t k (h2.thread t k h), fun s k h => h1.context s k (h2.context s k h),
   fun n k h => h1.notification n k (h2.notification n k h)⟩

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    bindingViewsShrink st st' :=
  ⟨fun t k hV => by simpa only [threadContextView, SystemState.getTcb?, h] using hV,
   fun s k hV => by simpa only [contextThreadView, SystemState.getSchedContext?, h] using hV,
   fun n k hV => by simpa only [notificationContextView, SystemState.getNotification?, h] using hV⟩

end bindingViewsShrink

/-- **A shrink carries equal binding labels.** -/
theorem bindingLabelsEqual_of_shrink {ctx : LabelingContext} {st st' : SystemState}
    (hInv : bindingLabelsEqual ctx st) (h : bindingViewsShrink st st') :
    bindingLabelsEqual ctx st' := by
  rw [bindingLabelsEqual_iff_views] at hInv ⊢
  exact ⟨fun t s hV => hInv.1 t s (h.thread t _ hV), fun s t hV => hInv.2.1 s t (h.context s _ hV),
    fun n s hV => hInv.2.2 n s (h.notification n _ hV)⟩

end SeLe4n.Kernel
