-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Operations

/-!
# A scheduling context donated through a notification

seL4-MCS's `maybeDonateSchedContext` (`notification.c`): when a thread takes a
notification's word — `completeSignal`, and `sendSignal`'s wake of a waiter or
of a bound receiver — and the thread holds no scheduling context while the
notification's context is bound to no thread, the context is donated to the
thread (`schedContext_donate`) and resumed (`schedContext_resume`).

The owner's decision D19 records the donation as the receiving thread's
`.bound` binding, with the notification link kept on the context.  So the
donation is `schedContextBind`'s ok-state, and a bind the checks refuse leaves
the state as it was (`maybeDonateSchedContext_cases`): a thread that already
holds a context, a context bound to a thread or heading a reply stack, and a
thread owed a context by a live reply stack each keep what they hold.

The compiled form (`maybeDonateSchedContextFast`) asks the bind's checks
(`schedContextBindAdmitted`) before any write and makes the bind's writes in
place (`schedContextBindPerform`), so a donation allocates nothing.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **seL4-MCS `maybeDonateSchedContext`**: the context bound to notification
`n`, donated to `tid` as its `.bound` binding when the bind admits it, else the
state unchanged. -/
def maybeDonateSchedContext (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    SystemState :=
  match st.getNotification? n with
  | none => st
  | some ntfn =>
    match ntfn.schedContext with
    | none => st
    | some s =>
      match s.toObjId.toValid?, tid.toValid? with
      | some vS, some vT =>
        match SchedContextOps.schedContextBind vS vT st with
        | .ok ((), st') => st'
        | .error _ => st
      | _, _ => st

/-- **The donation is the identity or a bind of `tid`**: every family lemma of
the donation is the identity's and the bind's. -/
theorem maybeDonateSchedContext_cases (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) :
    maybeDonateSchedContext st n tid = st ∨
      ∃ (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId), vT.val = tid ∧
        SchedContextOps.schedContextBind vS vT st = .ok ((), maybeDonateSchedContext st n tid) := by
  unfold maybeDonateSchedContext
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  split
  · rename_i vS vT _ hT
    split
    · rename_i st' hB
      refine Or.inr ⟨vS, vT, ?_, hB⟩
      unfold SeLe4n.ThreadId.toValid? at hT
      split at hT
      · cases hT
      · cases hT; rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **A property every bind of `tid` carries, and the identity, the donation
carries.** -/
theorem maybeDonateSchedContext_induct (P : SystemState → SystemState → Prop)
    (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (hId : P st st)
    (hBind : ∀ (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId) st', vT.val = tid →
      SchedContextOps.schedContextBind vS vT st = .ok ((), st') → P st st') :
    P st (maybeDonateSchedContext st n tid) := by
  rcases maybeDonateSchedContext_cases st n tid with h | ⟨vS, vT, hT, hB⟩
  · rw [h]; exact hId
  · exact hBind vS vT _ hT hB

/-- **The compiled donation**, the ids passed as their codes: the bind's checks
asked before any write (`schedContextBindAdmitted`), then its writes in place
(`schedContextBindPerform`).  A context code at or past `2 ^ 62` — which no
object store holds — takes the specification, so no code is a heap number. -/
@[noinline] def maybeDonateSchedContextFast (st : SystemState) (nCode tCode : Nat) :
    SystemState :=
  match st.getNotification? ⟨nCode⟩ with
  | none => st
  | some ntfn =>
    let sCode := ntfn.schedContextCode
    if sCode = 0 then st
    else if sCode < 2 ^ 62 then
      if hS : (⟨sCode - 1⟩ : SeLe4n.ObjId) = SeLe4n.ObjId.sentinel then st
      else if hT : (⟨tCode⟩ : SeLe4n.ThreadId) = SeLe4n.ThreadId.sentinel then st
      else if SchedContextOps.schedContextBindAdmitted st ⟨⟨sCode - 1⟩, hS⟩ ⟨⟨tCode⟩, hT⟩ then
        SchedContextOps.schedContextBindPerform st ⟨⟨sCode - 1⟩, hS⟩ ⟨⟨tCode⟩, hT⟩
      else st
    else maybeDonateSchedContext st ⟨nCode⟩ ⟨tCode⟩

/-- A bind its checks refuse is refused. -/
theorem schedContextBind_error_of_not_admitted (st : SystemState) (vS : SeLe4n.ValidObjId)
    (vT : SeLe4n.ValidThreadId)
    (h : SchedContextOps.schedContextBindAdmitted st vS vT = false) :
    ∃ e, SchedContextOps.schedContextBind vS vT st = .error e := by
  unfold SchedContextOps.schedContextBindAdmitted at h
  unfold SchedContextOps.schedContextBind
  cases hW : st.getSchedContextWitnessed? (SeLe4n.SchedContextId.ofObjId vS.val) with
  | none => exact ⟨_, rfl⟩
  | some w =>
    obtain ⟨sc, hSc⟩ := w
    simp only [hW] at h ⊢
    by_cases hB : sc.boundThread.isSome = true
    · simp only [hB, ↓reduceIte]; exact ⟨_, rfl⟩
    by_cases hR : sc.scReply.isSome = true
    · simp only [hB, hR, Bool.false_eq_true, ↓reduceIte]; exact ⟨_, rfl⟩
    simp only [hB, hR, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hT : st.getTcb? vT.val with
    | none => exact ⟨_, rfl⟩
    | some tcb =>
      simp only [hT] at h ⊢
      by_cases hL : replyFrameOnLiveStack st tcb = true
      · simp only [hL, ↓reduceIte]; exact ⟨_, rfl⟩
      simp only [hL, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hBind : tcb.schedContextBinding with
      | unbound => simp [hBind] at h
      | bound _ => exact ⟨_, rfl⟩
      | donated _ _ => exact ⟨_, rfl⟩

/-- **The compiled donation is the donation.** -/
theorem maybeDonateSchedContextFast_eq (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) :
    maybeDonateSchedContextFast st n.val tid.val = maybeDonateSchedContext st n tid := by
  unfold maybeDonateSchedContextFast
  cases hN : st.getNotification? ⟨n.val⟩ with
  | none =>
    unfold maybeDonateSchedContext
    rw [show (⟨n.val⟩ : SeLe4n.ObjId) = n from rfl] at hN
    rw [hN]
  | some ntfn =>
    have hN' : st.getNotification? n = some ntfn := hN
    simp only
    by_cases h0 : ntfn.schedContextCode = 0
    · unfold maybeDonateSchedContext
      simp only [h0, ↓reduceIte, hN', Notification.schedContext, SeLe4n.SchedContextId.ofOptCode]
    by_cases hW : ntfn.schedContextCode < 2 ^ 62
    · simp only [h0, hW, ↓reduceIte]
      unfold maybeDonateSchedContext
      obtain ⟨k, hk⟩ : ∃ k, ntfn.schedContextCode = k + 1 :=
        ⟨ntfn.schedContextCode - 1, by omega⟩
      simp only [hN', Notification.schedContext, hk, SeLe4n.SchedContextId.ofOptCode, Nat.add_sub_cancel,
        SeLe4n.SchedContextId.toObjId, SeLe4n.SchedContextId.toNat, SeLe4n.ObjId.ofNat,
        SeLe4n.ObjId.toValid?, SeLe4n.ThreadId.toValid?]
      by_cases hS : (⟨k⟩ : SeLe4n.ObjId) = SeLe4n.ObjId.sentinel
      · simp only [hS, ↓reduceDIte]
      by_cases hT : (⟨tid.val⟩ : SeLe4n.ThreadId) = SeLe4n.ThreadId.sentinel
      · have hT' : tid = SeLe4n.ThreadId.sentinel := hT
        simp only [hS, hT, hT', ↓reduceDIte]
      have hT' : ¬ tid = SeLe4n.ThreadId.sentinel := hT
      simp only [hS, hT, hT', ↓reduceDIte]
      cases hA : SchedContextOps.schedContextBindAdmitted st ⟨⟨k⟩, hS⟩ ⟨⟨tid.val⟩, hT⟩ with
      | true =>
        have := SchedContextOps.schedContextBind_of_admitted st ⟨⟨k⟩, hS⟩ ⟨⟨tid.val⟩, hT⟩ hA
        simp only [↓reduceIte]
        rw [show (⟨⟨tid.val⟩, hT⟩ : SeLe4n.ValidThreadId) = ⟨tid, hT'⟩ from rfl] at this ⊢
        rw [this]
      | false =>
        obtain ⟨e, he⟩ := schedContextBind_error_of_not_admitted st ⟨⟨k⟩, hS⟩ ⟨⟨tid.val⟩, hT⟩ hA
        rw [show (⟨⟨tid.val⟩, hT⟩ : SeLe4n.ValidThreadId) = ⟨tid, hT'⟩ from rfl] at he
        simp only [Bool.false_eq_true, ↓reduceIte, he]
    · simp only [h0, hW, ↓reduceIte]

/-! ### The donation writes no register -/

/-- **Every thread's register file agrees** between two states. -/
def registersAgree (st' st : SystemState) : Prop :=
  ∀ t : SeLe4n.ThreadId, (st'.getTcb? t).map TCB.registerContext = (st.getTcb? t).map TCB.registerContext

namespace registersAgree

theorem refl (st : SystemState) : registersAgree st st := fun _ => rfl

theorem trans {a b c : SystemState} (h₁ : registersAgree a b) (h₂ : registersAgree b c) :
    registersAgree a c := fun t => (h₁ t).trans (h₂ t)

private theorem getTcb?_map_of_objects {st' st : SystemState} (t : SeLe4n.ThreadId)
    (w : KernelObject → KernelObject) (hw : ∀ x, (∃ y, w x = .tcb y) ↔ ∃ y, x = .tcb y)
    (hr : ∀ x y, w x = .tcb y → ∃ y', x = .tcb y' ∧ y.registerContext = y'.registerContext)
    (h : (st'.objects[t.toObjId]?).map w = (st.objects[t.toObjId]?).map w) :
    (st'.getTcb? t).map TCB.registerContext = (st.getTcb? t).map TCB.registerContext := by
  unfold SystemState.getTcb?
  cases h1 : st'.objects[t.toObjId]? with
  | none =>
    rw [h1] at h
    cases h2 : st.objects[t.toObjId]? with
    | none => rfl
    | some o => rw [h2] at h; cases h
  | some o1 =>
    rw [h1] at h
    cases h2 : st.objects[t.toObjId]? with
    | none => rw [h2] at h; cases h
    | some o2 =>
      rw [h2] at h
      simp only [Option.map_some, Option.some.injEq] at h
      cases o1 with
      | tcb a =>
        obtain ⟨y, hy⟩ := (hw (.tcb a)).mpr ⟨a, rfl⟩
        rw [h] at hy
        obtain ⟨b, rfl, hb⟩ := hr _ _ hy
        obtain ⟨b', hb', ha⟩ := hr _ _ (h ▸ hy)
        cases hb'
        simp only [Option.map_some]
        rw [← h] at hy
        obtain ⟨a', ha', hab⟩ := hr _ _ hy
        cases ha'
        rw [← hab, hb]
      | _ =>
        cases o2 with
        | tcb b =>
          exfalso
          obtain ⟨y, hy⟩ := (hw (.tcb b)).mpr ⟨b, rfl⟩
          rw [← h] at hy
          obtain ⟨_, hx, _⟩ := hr _ _ hy
          cases hx
        | _ => rfl

theorem of_runLinks {st' st : SystemState} (h : st'.objectsAgreeOffRunLinks st) :
    registersAgree st' st := fun t =>
  getTcb?_map_of_objects t KernelObject.withoutRunLinks
    (fun x => by cases x <;> simp [KernelObject.withoutRunLinks])
    (fun x y hx => by
      cases x <;> simp [KernelObject.withoutRunLinks] at hx
      exact ⟨_, rfl, by rw [← hx]; rfl⟩)
    (h t.toObjId)

theorem of_releaseLinks {st' st : SystemState} (h : st'.objectsAgreeOffReleaseLinks st) :
    registersAgree st' st := fun t =>
  getTcb?_map_of_objects t KernelObject.withoutRelease
    (fun x => by cases x <;> simp [KernelObject.withoutRelease])
    (fun x y hx => by
      cases x <;> simp [KernelObject.withoutRelease] at hx
      exact ⟨_, rfl, by rw [← hx]⟩)
    (h t.toObjId)

end registersAgree

/-- A context rewritten, then a thread updated keeping its registers, keeps
every register file. -/
theorem registersAgree.updateTcb_rewriteSchedContext (st : SystemState) (id : SeLe4n.ObjId)
    (sc' : SeLe4n.Kernel.SchedContext) (hA : st.rewriteAdmissible id (.schedContext sc'))
    (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hf : ∀ t, (f t).registerContext = t.registerContext) :
    registersAgree ((st.rewriteObject id (.schedContext sc') hA).updateTcb tid f) st := by
  have hI1 := SystemState.rewriteObject_preserves_objects_invExt _ _ _ hA hInv
  intro t
  by_cases hE : tid.toObjId = t.toObjId
  · have : tid = t := SeLe4n.ThreadId.toObjId_injective _ _ hE
    subst this
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hI1, Option.map_map,
      SystemState.rewriteObject_schedContext_getTcb? _ _ _ _ hInv]
    cases st.getTcb? tid with
    | none => rfl
    | some x => simp [hf]
  · rw [SystemState.updateTcb_getTcb?_ne _ _ _ hI1 _ hE,
      SystemState.rewriteObject_schedContext_getTcb? _ _ _ _ hInv]

/-- **A bind writes no thread's registers**: its writes are the context, the
thread's binding, the run-queue links and the release links. -/
theorem schedContextBind_registersAgree {vS : SeLe4n.ValidObjId} {vT : SeLe4n.ValidThreadId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextBind vS vT st = .ok ((), st')) : registersAgree st' st := by
  unfold SchedContextOps.schedContextBind at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  cases h
  refine registersAgree.trans
    (registersAgree.of_releaseLinks (SystemState.releasePlace_agree _ _ _)) ?_
  split
  · refine registersAgree.trans (fun t => by
      rw [SystemState.markReschedulePendingOnCore_getTcb?]) ?_
    refine registersAgree.trans
      (registersAgree.of_runLinks (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _)) ?_
    exact registersAgree.updateTcb_rewriteSchedContext _ _ _ _ hInv _ _ (fun _ => rfl)
  · exact registersAgree.updateTcb_rewriteSchedContext _ _ _ _ hInv _ _ (fun _ => rfl)

/-- **The donation writes no thread's registers.** -/
theorem maybeDonateSchedContext_registersAgree (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    registersAgree (maybeDonateSchedContext st n tid) st := by
  rcases maybeDonateSchedContext_cases st n tid with h | ⟨_, _, _, hB⟩
  · rw [h]; exact registersAgree.refl _
  · exact schedContextBind_registersAgree hInv hB

end SeLe4n.Kernel
