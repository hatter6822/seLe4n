-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.RunQueueLinkFrame
import SeLe4n.Kernel.SchedContext.ReleaseLinks

/-!
# Agreement off every scheduler link

The scheduler keeps two intrusive queues in the object store: the run queues
link threads through six TCB fields (`TCB.withoutRunLinks`, WS-ZA ZA4.5) and the
release queues link scheduling contexts through three context fields
(`SchedContext.withoutRelease`, WS-ZA ZA6.3).  A step the scheduler takes on one
spine and not on the other — a cross-core wake beside its single-core twin, a
replenishment migration beside none — differs from its twin in both, so the
relation that says "the same objects but for the scheduler's links" erases both
(`objectsAgreeOffSchedulerLinks`).  Each of the two relations implies it
(`of_runLinks`, `of_releaseLinks`), and it reads a thread as the run-link
relation does and a context as the release-link one does.
-/

namespace SeLe4n.Model

open SeLe4n.Kernel (SchedContext)

/-- An object with every scheduler link cleared: a thread's run-queue fields
and a context's release-queue fields. -/
def KernelObject.withoutSchedulerLinks (o : KernelObject) : KernelObject :=
  o.withoutRunLinks.withoutRelease

@[simp] theorem KernelObject.withoutSchedulerLinks_tcb (t : TCB) :
    (KernelObject.tcb t).withoutSchedulerLinks = .tcb t.withoutRunLinks := rfl

@[simp] theorem KernelObject.withoutSchedulerLinks_schedContext (sc : SchedContext) :
    (KernelObject.schedContext sc).withoutSchedulerLinks = .schedContext sc.withoutRelease := rfl

/-- The two clearings commute: they name disjoint kinds. -/
theorem KernelObject.withoutSchedulerLinks_eq_release_run (o : KernelObject) :
    o.withoutSchedulerLinks = o.withoutRelease.withoutRunLinks := by
  cases o <;> rfl

/-- Two objects agreeing off the scheduler links are the same object, two
threads agreeing off their run-queue fields, or two contexts agreeing off their
release-queue fields. -/
theorem KernelObject.withoutSchedulerLinks_eq_cases {o o' : KernelObject}
    (h : o'.withoutSchedulerLinks = o.withoutSchedulerLinks) :
    o' = o ∨
      (∃ t t' : TCB, o = .tcb t ∧ o' = .tcb t' ∧ t'.withoutRunLinks = t.withoutRunLinks) ∨
      (∃ sc sc' : SchedContext, o = .schedContext sc ∧ o' = .schedContext sc' ∧
        sc'.withoutRelease = sc.withoutRelease) := by
  cases o <;> cases o' <;>
    simp only [KernelObject.withoutSchedulerLinks, KernelObject.withoutRunLinks,
      KernelObject.withoutRelease, KernelObject.tcb.injEq, KernelObject.schedContext.injEq,
      reduceCtorEq] at h ⊢ <;>
    first
    | exact Or.inl h
    | exact Or.inr (Or.inl ⟨_, _, rfl, rfl, h⟩)
    | exact Or.inr (Or.inr ⟨_, _, rfl, rfl, h⟩)
    | (subst h; exact Or.inl rfl)

namespace SystemState

/-- **`st'` holds `st`'s objects up to the scheduler's links**: at every key
the two stores hold objects that agree once the run-queue fields of a thread
and the release-queue fields of a context are cleared. -/
def objectsAgreeOffSchedulerLinks (st' st : SystemState) : Prop :=
  ∀ x : SeLe4n.ObjId,
    (st'.objects[x]?).map KernelObject.withoutSchedulerLinks =
      (st.objects[x]?).map KernelObject.withoutSchedulerLinks

/-- A write of the threads' run-queue links moves no context's release link. -/
theorem releaseCoreOf_of_runLinks {a b : SystemState} (h : a.objectsAgreeOffRunLinks b)
    (s : SeLe4n.SchedContextId) : a.releaseCoreOf s = b.releaseCoreOf s := by
  unfold releaseCoreOf; rw [h.getSchedContext?]

namespace objectsAgreeOffSchedulerLinks

theorem refl (st : SystemState) : objectsAgreeOffSchedulerLinks st st := fun _ => rfl

theorem symm {st st' : SystemState} (h : objectsAgreeOffSchedulerLinks st' st) :
    objectsAgreeOffSchedulerLinks st st' := fun x => (h x).symm

theorem trans {st st' st'' : SystemState} (h₂ : objectsAgreeOffSchedulerLinks st'' st')
    (h₁ : objectsAgreeOffSchedulerLinks st' st) : objectsAgreeOffSchedulerLinks st'' st :=
  fun x => (h₂ x).trans (h₁ x)

/-- The relation reads the object stores alone. -/
theorem congr {a a' b b' : SystemState} (ha : a'.objects = a.objects)
    (hb : b'.objects = b.objects) (h : objectsAgreeOffSchedulerLinks a b) :
    objectsAgreeOffSchedulerLinks a' b' := fun x => by rw [ha, hb]; exact h x

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    objectsAgreeOffSchedulerLinks st' st := fun x => by rw [h]

/-- A run-link step agrees off every scheduler link. -/
theorem of_runLinks {st st' : SystemState} (h : objectsAgreeOffRunLinks st' st) :
    objectsAgreeOffSchedulerLinks st' st := fun x => by
  have e := congrArg (Option.map KernelObject.withoutRelease) (h x)
  simpa only [Option.map_map] using e

/-- A release-link step agrees off every scheduler link. -/
theorem of_releaseLinks {st st' : SystemState} (h : objectsAgreeOffReleaseLinks st' st) :
    objectsAgreeOffSchedulerLinks st' st := fun x => by
  have e := congrArg (Option.map KernelObject.withoutRunLinks) (h x)
  simp only [Option.map_map] at e
  have hc : (KernelObject.withoutRunLinks ∘ KernelObject.withoutRelease) =
      KernelObject.withoutSchedulerLinks :=
    funext fun o => (KernelObject.withoutSchedulerLinks_eq_release_run o).symm
  rw [hc] at e
  exact e

variable {st st' : SystemState} (h : objectsAgreeOffSchedulerLinks st' st)
include h

/-- At every key the two stores hold the same object, two threads agreeing off
their run-queue fields, or two contexts agreeing off their release fields. -/
theorem pointwise (x : SeLe4n.ObjId) :
    st'.objects[x]? = st.objects[x]? ∨
      (∃ t t' : TCB, st.objects[x]? = some (.tcb t) ∧ st'.objects[x]? = some (.tcb t') ∧
        t'.withoutRunLinks = t.withoutRunLinks) ∨
      (∃ sc sc' : SchedContext, st.objects[x]? = some (.schedContext sc) ∧
        st'.objects[x]? = some (.schedContext sc') ∧ sc'.withoutRelease = sc.withoutRelease) := by
  have hx := h x
  cases e : st.objects[x]? with
  | none =>
    rw [e] at hx
    cases e' : st'.objects[x]? with
    | none => exact Or.inl rfl
    | some _ => rw [e'] at hx; cases hx
  | some o =>
    rw [e] at hx
    cases e' : st'.objects[x]? with
    | none => rw [e'] at hx; cases hx
    | some o' =>
      rw [e'] at hx
      rcases KernelObject.withoutSchedulerLinks_eq_cases (Option.some.inj hx) with
        h1 | ⟨t, t', rfl, rfl, ht⟩ | ⟨sc, sc', rfl, rfl, hs⟩
      · exact Or.inl (congrArg some h1)
      · exact Or.inr (Or.inl ⟨t, t', rfl, rfl, ht⟩)
      · exact Or.inr (Or.inr ⟨sc, sc', rfl, rfl, hs⟩)

/-- An object neither a thread nor a context is the same object in both stores. -/
theorem get_of_plain {x : SeLe4n.ObjId} {o : KernelObject}
    (hT : ∀ t, o ≠ .tcb t) (hS : ∀ sc, o ≠ .schedContext sc)
    (hx : st.objects[x]? = some o) : st'.objects[x]? = some o := by
  rcases h.pointwise x with e | ⟨t, _, ht, _, _⟩ | ⟨sc, _, hs, _, _⟩
  · rw [e, hx]
  · rw [hx] at ht; exact absurd (Option.some.inj ht) (hT t)
  · rw [hx] at hs; exact absurd (Option.some.inj hs) (hS sc)

theorem get_of_plain' {x : SeLe4n.ObjId} {o : KernelObject}
    (hT : ∀ t, o ≠ .tcb t) (hS : ∀ sc, o ≠ .schedContext sc)
    (hx : st'.objects[x]? = some o) : st.objects[x]? = some o :=
  h.symm.get_of_plain hT hS hx

/-- A TCB in `st` is a TCB in `st'` agreeing off its run-queue fields. -/
theorem get_tcb {x : SeLe4n.ObjId} {t : TCB} (hx : st.objects[x]? = some (.tcb t)) :
    ∃ t', st'.objects[x]? = some (.tcb t') ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  rcases h.pointwise x with e | ⟨t₀, t', ht, ht', e⟩ | ⟨_, _, hs, _, _⟩
  · exact ⟨t, e.trans hx, rfl⟩
  · rw [hx] at ht; cases ht; exact ⟨t', ht', e⟩
  · rw [hx] at hs; cases hs

theorem get_tcb' {x : SeLe4n.ObjId} {t' : TCB} (hx : st'.objects[x]? = some (.tcb t')) :
    ∃ t, st.objects[x]? = some (.tcb t) ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  obtain ⟨t, ht, e⟩ := h.symm.get_tcb hx
  exact ⟨t, ht, e.symm⟩

/-- A context in `st` is a context in `st'` agreeing off its release fields. -/
theorem get_sc {x : SeLe4n.ObjId} {sc : SchedContext} (hx : st.objects[x]? = some (.schedContext sc)) :
    ∃ sc', st'.objects[x]? = some (.schedContext sc') ∧ sc'.withoutRelease = sc.withoutRelease := by
  rcases h.pointwise x with e | ⟨_, _, ht, _, _⟩ | ⟨s₀, sc', hs, hs', e⟩
  · exact ⟨sc, e.trans hx, rfl⟩
  · rw [hx] at ht; cases ht
  · rw [hx] at hs; cases hs; exact ⟨sc', hs', e⟩

theorem get_sc' {x : SeLe4n.ObjId} {sc' : SchedContext}
    (hx : st'.objects[x]? = some (.schedContext sc')) :
    ∃ sc, st.objects[x]? = some (.schedContext sc) ∧ sc'.withoutRelease = sc.withoutRelease := by
  obtain ⟨sc, hs, e⟩ := h.symm.get_sc hx
  exact ⟨sc, hs, e.symm⟩

/-- A key is empty in one store exactly when it is in the other. -/
theorem get_none_iff {x : SeLe4n.ObjId} : st'.objects[x]? = none ↔ st.objects[x]? = none := by
  have hx := h x
  constructor
  · intro e; rw [e] at hx; cases f : st.objects[x]? with
    | none => rfl
    | some _ => rw [f] at hx; cases hx
  · intro e; rw [e] at hx; cases f : st'.objects[x]? with
    | none => rfl
    | some _ => rw [f] at hx; cases hx

theorem get_endpoint_iff {x : SeLe4n.ObjId} {e : Endpoint} :
    st'.objects[x]? = some (.endpoint e) ↔ st.objects[x]? = some (.endpoint e) :=
  ⟨h.get_of_plain' (fun _ e => KernelObject.noConfusion e) (fun _ e => KernelObject.noConfusion e),
   h.get_of_plain (fun _ e => KernelObject.noConfusion e) (fun _ e => KernelObject.noConfusion e)⟩

theorem get_notification_iff {x : SeLe4n.ObjId} {n : Notification} :
    st'.objects[x]? = some (.notification n) ↔ st.objects[x]? = some (.notification n) :=
  ⟨h.get_of_plain' (fun _ e => KernelObject.noConfusion e) (fun _ e => KernelObject.noConfusion e),
   h.get_of_plain (fun _ e => KernelObject.noConfusion e) (fun _ e => KernelObject.noConfusion e)⟩

theorem get_reply_iff {x : SeLe4n.ObjId} {r : SeLe4n.Kernel.Reply} :
    st'.objects[x]? = some (.reply r) ↔ st.objects[x]? = some (.reply r) :=
  ⟨h.get_of_plain' (fun _ e => KernelObject.noConfusion e) (fun _ e => KernelObject.noConfusion e),
   h.get_of_plain (fun _ e => KernelObject.noConfusion e) (fun _ e => KernelObject.noConfusion e)⟩

theorem get_cnode_iff {x : SeLe4n.ObjId} {cn : CNode} :
    st'.objects[x]? = some (.cnode cn) ↔ st.objects[x]? = some (.cnode cn) :=
  ⟨h.get_of_plain' (fun _ e => KernelObject.noConfusion e) (fun _ e => KernelObject.noConfusion e),
   h.get_of_plain (fun _ e => KernelObject.noConfusion e) (fun _ e => KernelObject.noConfusion e)⟩

theorem getTcb? (tid : SeLe4n.ThreadId) :
    (st'.getTcb? tid).map TCB.withoutRunLinks = (st.getTcb? tid).map TCB.withoutRunLinks := by
  cases e : st.getTcb? tid with
  | some t =>
      obtain ⟨t', h', ht⟩ := h.get_tcb ((getTcb?_eq_some_iff st tid t).mp e)
      rw [(getTcb?_eq_some_iff st' tid t').mpr h']; exact congrArg some ht
  | none =>
      cases e' : st'.getTcb? tid with
      | none => rfl
      | some t' =>
          obtain ⟨t, h₀, _⟩ := h.get_tcb' ((getTcb?_eq_some_iff st' tid t').mp e')
          rw [(getTcb?_eq_some_iff st tid t).mpr h₀] at e; cases e

theorem getTcb?_isSome (tid : SeLe4n.ThreadId) :
    (st'.getTcb? tid).isSome = (st.getTcb? tid).isSome := by
  have := congrArg Option.isSome (h.getTcb? tid)
  simpa using this

theorem getTcb?_some {tid : SeLe4n.ThreadId} {t : TCB} (ht : st.getTcb? tid = some t) :
    ∃ t', st'.getTcb? tid = some t' ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  obtain ⟨t', h', e⟩ := h.get_tcb ((getTcb?_eq_some_iff st tid t).mp ht)
  exact ⟨t', (getTcb?_eq_some_iff st' tid t').mpr h', e⟩

theorem getTcb?_some' {tid : SeLe4n.ThreadId} {t' : TCB} (ht : st'.getTcb? tid = some t') :
    ∃ t, st.getTcb? tid = some t ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  obtain ⟨t, h₀, e⟩ := h.get_tcb' ((getTcb?_eq_some_iff st' tid t').mp ht)
  exact ⟨t, (getTcb?_eq_some_iff st tid t).mpr h₀, e⟩

/-- Contexts read the same in both stores off their release fields. -/
theorem getSchedContext? (scId : SeLe4n.SchedContextId) :
    (st'.getSchedContext? scId).map SchedContext.withoutRelease =
      (st.getSchedContext? scId).map SchedContext.withoutRelease := by
  unfold SystemState.getSchedContext?
  rcases h.pointwise scId.toObjId with e | ⟨_, _, ht, ht', _⟩ | ⟨_, _, hs, hs', e⟩
  · rw [e]
  · rw [ht, ht']
  · rw [hs, hs']; exact congrArg some e

theorem getSchedContext?_some {s : SeLe4n.SchedContextId} {sc : SchedContext}
    (hs : st.getSchedContext? s = some sc) :
    ∃ sc', st'.getSchedContext? s = some sc' ∧ sc'.withoutRelease = sc.withoutRelease :=
  SchedContext.map_withoutRelease_some (h.getSchedContext? s) hs

theorem getSchedContext?_some' {s : SeLe4n.SchedContextId} {sc' : SchedContext}
    (hs : st'.getSchedContext? s = some sc') :
    ∃ sc, st.getSchedContext? s = some sc ∧ sc'.withoutRelease = sc.withoutRelease := by
  obtain ⟨sc, e, hw⟩ := SchedContext.map_withoutRelease_some (h.getSchedContext? s).symm hs
  exact ⟨sc, e, hw.symm⟩

/-- Reply objects read the same in both stores. -/
theorem getReply? (rid : SeLe4n.ReplyId) : st'.getReply? rid = st.getReply? rid := by
  unfold SystemState.getReply?
  rcases h.pointwise rid.toObjId with e | ⟨_, _, ht, ht', _⟩ | ⟨_, _, hs, hs', _⟩
  · rw [e]
  · rw [ht, ht']
  · rw [hs, hs']

/-- No scheduler link is a taint word. -/
theorem declassificationTaint : st'.declassificationTaint = st.declassificationTaint :=
  funext fun x => by
    have hx := h x
    have key : ∀ o : KernelObject, o.withoutSchedulerLinks.taintWords = o.taintWords := by
      intro o; cases o <;> rfl
    show (st'.taintWordsAt x).decode = (st.taintWordsAt x).decode
    rw [SystemState.taintWordsAt_eq, SystemState.taintWordsAt_eq]
    revert hx
    cases st'.objects[x]? <;> cases st.objects[x]? <;> intro hx
    · rfl
    · cases hx
    · cases hx
    · simp only [Option.map_some, Option.some.injEq] at hx
      dsimp only
      rw [← key, hx, key]

omit h in
/-- A reading of an object that a context's release fields do not reach reads
two contexts agreeing off those fields alike. -/
private theorem sc_proj {α : Sort _} (f : KernelObject → α) (hf : ∀ o, f o.withoutRelease = f o)
    {sc sc' : SchedContext} (e : sc'.withoutRelease = sc.withoutRelease) :
    f (.schedContext sc') = f (.schedContext sc) := by
  rw [← hf (.schedContext sc'), ← hf (.schedContext sc)]
  show f (.schedContext sc'.withoutRelease) = f (.schedContext sc.withoutRelease)
  rw [e]

/-- A step that writes only scheduler links rewrites each object to one of its
own kind. -/
theorem kindPreserving : SeLe4n.Model.kindPreservingWrite st st' := by
  intro oid
  rcases h.pointwise oid with e | ⟨t, t', ht, ht', e⟩ | ⟨sc, sc', hs, hs', e⟩
  · exact Or.inl e
  · exact Or.inr ⟨_, _, ht, ht', by simp [KernelObject.objectType], by
      simp [KernelObject.objectType], by
        simp only [KernelObject.tcbSlots,
          TCB.proj_eq_of_withoutRunLinks_eq (·.spaceCells) e,
          TCB.proj_eq_of_withoutRunLinks_eq (·.spaceLinks) e], rfl, by
        simp only [KernelObject.bindingCodes,
          TCB.proj_eq_of_withoutRunLinks_eq (·.boundNotificationCode) e], by
        simp only [KernelObject.tableBackLinks,
          TCB.proj_eq_of_withoutRunLinks_eq (·.taintWords) e], rfl⟩
  · exact Or.inr ⟨_, _, hs, hs', rfl, by simp [KernelObject.objectType], rfl, rfl,
      sc_proj KernelObject.bindingCodes (fun o => by cases o <;> rfl) e,
      sc_proj KernelObject.tableBackLinks (fun o => by cases o <;> rfl) e,
      sc_proj KernelObject.mappingView (fun o => by cases o <;> rfl) e⟩

omit h in
/-- Two objects agreeing off the scheduler links hold the same capability slots
and the same derivation-link words. -/
theorem _root_.SeLe4n.Model.KernelObject.slots_eq_of_withoutSchedulerLinks_eq {o o' : KernelObject}
    (e : o'.withoutSchedulerLinks = o.withoutSchedulerLinks) :
    o'.slotCap = o.slotCap ∧ o'.linkWords = o.linkWords ∧ (∀ s, o'.hasSlot s ↔ o.hasSlot s) := by
  rcases KernelObject.withoutSchedulerLinks_eq_cases e with e | ⟨t, t', rfl, rfl, ht⟩ |
    ⟨sc, sc', rfl, rfl, hs⟩
  · subst e; exact ⟨rfl, rfl, fun _ => .rfl⟩
  · exact KernelObject.slots_eq_of_withoutRunLinks_eq (congrArg KernelObject.tcb ht)
  · exact ⟨sc_proj KernelObject.slotCap (fun o => by cases o <;> rfl) hs,
      sc_proj KernelObject.linkWords (fun o => by cases o <;> rfl) hs,
      fun s => Iff.of_eq (sc_proj (fun o => o.hasSlot s) (fun o => by cases o <;> rfl) hs)⟩

/-- An object of `st'` was in `st`, holding the same capability slots. -/
theorem slots_back {x : SeLe4n.ObjId} {o' : KernelObject} (hx : st'.objects[x]? = some o') :
    ∃ o, st.objects[x]? = some o ∧ o'.slotCap = o.slotCap ∧ o'.linkWords = o.linkWords ∧
      (∀ s, o'.hasSlot s ↔ o.hasSlot s) := by
  have hx' := h x
  rw [hx] at hx'
  cases e : st.objects[x]? with
  | none => rw [e] at hx'; cases hx'
  | some o =>
    rw [e] at hx'
    exact ⟨o, rfl, KernelObject.slots_eq_of_withoutSchedulerLinks_eq (Option.some.inj hx')⟩

/-- An object of `st` is in `st'`, holding the same capability slots. -/
theorem slots_fwd {x : SeLe4n.ObjId} {o : KernelObject} (hx : st.objects[x]? = some o) :
    ∃ o', st'.objects[x]? = some o' ∧ o'.slotCap = o.slotCap ∧ o'.linkWords = o.linkWords ∧
      (∀ s, o'.hasSlot s ↔ o.hasSlot s) := by
  obtain ⟨o', ho', hc, hl, hs⟩ := h.symm.slots_back hx
  exact ⟨o', ho', hc.symm, hl.symm, fun s => (hs s).symm⟩

/-- A TCB of `st'` is a TCB of `st` with its run-queue fields rewritten. -/
theorem get_tcb_back {x : SeLe4n.ObjId} {t' : TCB} (hx : st'.objects[x]? = some (.tcb t')) :
    ∃ t : TCB, ∃ (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx rwp rwn rwh rwc : Nat) (ib : UInt64) (ibd icg ifs : Bool),
      st.objects[x]? = some (.tcb t) ∧
      t' = { t with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                    runBucketPrevCode := rbpv, runBucketNextCode := rbnx,
                    replyWaiterPrevCode := rwp, replyWaiterNextCode := rwn,
                    replyWaitersHeadCode := rwh, replyWaitersCount := rwc,
                    ipcBadge := ib, ipcBadged := ibd, ipcCanGrant := icg, ipcFaultSend := ifs } := by
  obtain ⟨t, ht, e⟩ := h.get_tcb' hx
  exact ⟨t, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, TCB.eq_withRunLinks_of_withoutRunLinks_eq e⟩

/-- The same, from `st` to `st'`. -/
theorem get_tcb_fwd {x : SeLe4n.ObjId} {t : TCB} (hx : st.objects[x]? = some (.tcb t)) :
    ∃ t' : TCB, ∃ (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx rwp rwn rwh rwc : Nat) (ib : UInt64) (ibd icg ifs : Bool),
      st'.objects[x]? = some (.tcb t') ∧
      t = { t' with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                    runBucketPrevCode := rbpv, runBucketNextCode := rbnx,
                    replyWaiterPrevCode := rwp, replyWaiterNextCode := rwn,
                    replyWaitersHeadCode := rwh, replyWaitersCount := rwc,
                    ipcBadge := ib, ipcBadged := ibd, ipcCanGrant := icg, ipcFaultSend := ifs } :=
  h.symm.get_tcb_back hx

end objectsAgreeOffSchedulerLinks

end SystemState

end SeLe4n.Model
