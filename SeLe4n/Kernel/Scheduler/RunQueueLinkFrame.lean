/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.Scheduler.RunQueueThreadLinks

/-!
# Run-queue writes leave every other object field alone

WS-ZA ZA4.5: the run queue's links live in the threads' TCBs, so enqueue
and removal write the object store.  They write only the six
run-queue fields, though, and nothing outside the scheduler reads those.  This
module states that frame once — two object stores *agree off the run-queue
links* when they hold the same objects at every key once those six fields are
cleared — and proves it for every run-queue write, so a proof that read "the
object store is unchanged" across a scheduler call reads "unchanged off the
run-queue links" instead.  This is the relation seL4's refinement uses for
`tcbSchedNext` / `tcbSchedPrev`.
-/

namespace SeLe4n.Model

/-- The TCB with its six run-queue fields cleared: everything any reader
outside the run queue can see. -/
def TCB.withoutRunLinks (t : TCB) : TCB :=
  { t with runCoreCode := 0, runPrio := ⟨0⟩, runPrevCode := 0, runNextCode := 0,
           runBucketPrevCode := 0, runBucketNextCode := 0 }

/-- An object with a TCB's run-queue fields cleared; every other kind as is. -/
def KernelObject.withoutRunLinks : KernelObject → KernelObject
  | .tcb t => .tcb t.withoutRunLinks
  | o => o

@[simp] theorem KernelObject.withoutRunLinks_tcb (t : TCB) :
    (KernelObject.tcb t).withoutRunLinks = .tcb t.withoutRunLinks := rfl

/-- A clearing that names a non-TCB object is that object. -/
theorem KernelObject.withoutRunLinks_eq_self_of_not_tcb {o : KernelObject}
    (h : ∀ t, o ≠ .tcb t) : o.withoutRunLinks = o := by
  cases o with
  | tcb t => exact absurd rfl (h t)
  | _ => rfl

/-- Two objects that agree off the run-queue links: one is a TCB exactly when
the other is, and a non-TCB is the same object. -/
theorem KernelObject.withoutRunLinks_eq_tcb {o : KernelObject} {t : TCB}
    (h : o.withoutRunLinks = (KernelObject.tcb t).withoutRunLinks) :
    ∃ t', o = .tcb t' ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  cases o with
  | tcb t' => exact ⟨t', rfl, KernelObject.tcb.inj h⟩
  | _ => cases h

/-- Two TCBs that agree off the run-queue links: the first is the second with
its six run-queue fields rewritten — the form a proof can `subst`. -/
theorem TCB.eq_withRunLinks_of_withoutRunLinks_eq {t t' : TCB}
    (e : t'.withoutRunLinks = t.withoutRunLinks) :
    t' = { t with runCoreCode := t'.runCoreCode, runPrio := t'.runPrio,
                  runPrevCode := t'.runPrevCode, runNextCode := t'.runNextCode,
                  runBucketPrevCode := t'.runBucketPrevCode,
                  runBucketNextCode := t'.runBucketNextCode } := by
  cases t; cases t'
  simp only [TCB.withoutRunLinks, TCB.mk.injEq] at e ⊢
  simp only [e, and_self]

/-- Two TCBs that agree off the run-queue links agree on anything that reads
past those links.  Elaborated from `h`, not the expected type, so a field
equality whose right side is defeq to the projection still checks. -/
@[elab_without_expected_type]
theorem TCB.proj_eq_of_withoutRunLinks_eq {α : Sort _} {t t' : TCB} (f : TCB → α)
    (h : t'.withoutRunLinks = t.withoutRunLinks)
    (hf : ∀ u : TCB, f u.withoutRunLinks = f u := by intro; rfl) : f t' = f t := by
  rw [← hf t', ← hf t, h]

/-- Two lookups that agree off the run-queue links agree on anything that
reads past those links. -/
theorem TCB.map_proj_eq_of_map_withoutRunLinks_eq {α : Type _} {a b : Option TCB}
    (f : TCB → α) (h : a.map TCB.withoutRunLinks = b.map TCB.withoutRunLinks)
    (hf : ∀ u : TCB, f u.withoutRunLinks = f u := by intro; rfl) : a.map f = b.map f := by
  cases a with
  | none => cases b with
    | none => rfl
    | some _ => cases h
  | some t' => cases b with
    | none => cases h
    | some t => exact congrArg some (TCB.proj_eq_of_withoutRunLinks_eq f (Option.some.inj h) hf)

/-- A TCB rewrite that reads no run-queue field: rewriting those fields first
changes nothing off them. -/
def TCB.RunLinksBlind (f : TCB → TCB) : Prop :=
  ∀ (t : TCB) (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx : Nat),
    (f { t with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                runBucketPrevCode := rbpv, runBucketNextCode := rbnx }).withoutRunLinks =
      (f t).withoutRunLinks

theorem KernelObject.withoutRunLinks_eq_of_not_tcb {o o' : KernelObject}
    (h : o'.withoutRunLinks = o.withoutRunLinks) (hNot : ∀ t, o ≠ .tcb t) : o' = o := by
  rw [KernelObject.withoutRunLinks_eq_self_of_not_tcb hNot] at h
  cases o' with
  | tcb t' => exact absurd h.symm (hNot _)
  | _ => exact h

/-- Two objects that agree off the run-queue links are the same object, or
both TCBs. -/
theorem KernelObject.withoutRunLinks_eq_cases {o o' : KernelObject}
    (h : o'.withoutRunLinks = o.withoutRunLinks) :
    o' = o ∨ ∃ t t', o = .tcb t ∧ o' = .tcb t' := by
  cases o with
  | tcb t =>
    obtain ⟨t', rfl, _⟩ := KernelObject.withoutRunLinks_eq_tcb h
    exact Or.inr ⟨t, t', rfl, rfl⟩
  | _ => exact Or.inl (KernelObject.withoutRunLinks_eq_of_not_tcb h (fun _ e => KernelObject.noConfusion e))

/-- Two lookups that agree off the run-queue links: an object one finds, the
other finds too, agreeing off those links. -/
theorem KernelObject.map_withoutRunLinks_eq_some {a b : Option KernelObject} {o : KernelObject}
    (h : a.map KernelObject.withoutRunLinks = b.map KernelObject.withoutRunLinks)
    (ha : a = some o) :
    ∃ o₀, b = some o₀ ∧ o.withoutRunLinks = o₀.withoutRunLinks := by
  subst ha
  cases b with
  | none => cases h
  | some o₀ => exact ⟨o₀, rfl, Option.some.inj h⟩

/-- The pointwise form of a store agreement at one key: a TCB on one side is a
TCB on the other, agreeing off its run-queue fields. -/
theorem KernelObject.map_withoutRunLinks_tcb {a b : Option KernelObject} {t : TCB}
    (h : a.map KernelObject.withoutRunLinks = b.map KernelObject.withoutRunLinks)
    (hb : b = some (.tcb t)) :
    ∃ t', a = some (.tcb t') ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  obtain ⟨o, ha, ho⟩ := KernelObject.map_withoutRunLinks_eq_some h.symm hb
  obtain ⟨t', rfl, ht⟩ := KernelObject.withoutRunLinks_eq_tcb ho.symm
  exact ⟨t', ha, ht⟩

/-- ...and any other object is the same object on both sides. -/
theorem KernelObject.map_withoutRunLinks_of_not_tcb {a b : Option KernelObject} {o : KernelObject}
    (h : a.map KernelObject.withoutRunLinks = b.map KernelObject.withoutRunLinks)
    (hb : b = some o) (hNot : ∀ t, o ≠ .tcb t) : a = some o := by
  obtain ⟨o', ha, ho⟩ := KernelObject.map_withoutRunLinks_eq_some h.symm hb
  rw [ha, KernelObject.withoutRunLinks_eq_of_not_tcb ho.symm hNot]

end SeLe4n.Model

namespace SeLe4n.Model.SystemState
open SeLe4n.Kernel
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.LinkedQueue
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-ZA ZA4.5: `st'` holds `st`'s objects up to TCB run-queue fields — at
every key the same object once those fields are cleared. -/
def objectsAgreeOffRunLinks (st' st : SystemState) : Prop :=
  ∀ x : SeLe4n.ObjId,
    (st'.objects[x]?).map KernelObject.withoutRunLinks =
      (st.objects[x]?).map KernelObject.withoutRunLinks

namespace objectsAgreeOffRunLinks

theorem refl (st : SystemState) : objectsAgreeOffRunLinks st st := fun _ => rfl

theorem symm {st st' : SystemState} (h : objectsAgreeOffRunLinks st' st) :
    objectsAgreeOffRunLinks st st' := fun x => (h x).symm

theorem trans {st st' st'' : SystemState} (h₂ : objectsAgreeOffRunLinks st'' st')
    (h₁ : objectsAgreeOffRunLinks st' st) : objectsAgreeOffRunLinks st'' st :=
  fun x => (h₂ x).trans (h₁ x)

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    objectsAgreeOffRunLinks st' st := fun x => by rw [h]

theorem of_getElem_eq {st st' : SystemState}
    (h : ∀ x : SeLe4n.ObjId, st'.objects[x]? = st.objects[x]?) :
    objectsAgreeOffRunLinks st' st := fun x => by rw [h x]

/-- The relation reads the object store alone. -/
theorem congr {a a' b b' : SystemState} (ha : a'.objects = a.objects)
    (hb : b'.objects = b.objects) (h : objectsAgreeOffRunLinks a b) :
    objectsAgreeOffRunLinks a' b' := fun x => by rw [ha, hb]; exact h x

variable {st st' : SystemState} (h : objectsAgreeOffRunLinks st' st)
include h

/-- A non-TCB object is the same object in both stores. -/
theorem get_of_not_tcb {x : SeLe4n.ObjId} {o : KernelObject}
    (hNot : ∀ t, o ≠ .tcb t) (hx : st.objects[x]? = some o) : st'.objects[x]? = some o := by
  have hx' := h x
  rw [hx] at hx'
  cases e : st'.objects[x]? with
  | none => rw [e] at hx'; cases hx'
  | some o' =>
      rw [e] at hx'
      exact congrArg some (KernelObject.withoutRunLinks_eq_of_not_tcb (Option.some.inj hx') hNot)

/-- …and the converse direction. -/
theorem get_of_not_tcb' {x : SeLe4n.ObjId} {o : KernelObject}
    (hNot : ∀ t, o ≠ .tcb t) (hx : st'.objects[x]? = some o) : st.objects[x]? = some o :=
  h.symm.get_of_not_tcb hNot hx

/-- A TCB in `st` is a TCB in `st'` agreeing off its run-queue fields. -/
theorem get_tcb {x : SeLe4n.ObjId} {t : TCB} (hx : st.objects[x]? = some (.tcb t)) :
    ∃ t', st'.objects[x]? = some (.tcb t') ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  have hx' := h x
  rw [hx] at hx'
  cases e : st'.objects[x]? with
  | none => rw [e] at hx'; cases hx'
  | some o' =>
      rw [e] at hx'
      obtain ⟨t', rfl, ht⟩ := KernelObject.withoutRunLinks_eq_tcb (Option.some.inj hx')
      exact ⟨t', rfl, ht⟩

/-- A TCB in `st'` is a TCB in `st` agreeing off its run-queue fields. -/
theorem get_tcb' {x : SeLe4n.ObjId} {t' : TCB} (hx : st'.objects[x]? = some (.tcb t')) :
    ∃ t, st.objects[x]? = some (.tcb t) ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  obtain ⟨t, ht, e⟩ := h.symm.get_tcb hx
  exact ⟨t, ht, e.symm⟩

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

/-- Each non-TCB kind reads the same in both stores. -/
theorem get_endpoint_iff {x : SeLe4n.ObjId} {e : Endpoint} :
    st'.objects[x]? = some (.endpoint e) ↔ st.objects[x]? = some (.endpoint e) :=
  ⟨h.get_of_not_tcb' (fun _ e => KernelObject.noConfusion e),
   h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e)⟩

theorem get_notification_iff {x : SeLe4n.ObjId} {n : Notification} :
    st'.objects[x]? = some (.notification n) ↔ st.objects[x]? = some (.notification n) :=
  ⟨h.get_of_not_tcb' (fun _ e => KernelObject.noConfusion e),
   h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e)⟩

theorem get_cnode_iff {x : SeLe4n.ObjId} {cn : CNode} :
    st'.objects[x]? = some (.cnode cn) ↔ st.objects[x]? = some (.cnode cn) :=
  ⟨h.get_of_not_tcb' (fun _ e => KernelObject.noConfusion e),
   h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e)⟩

theorem get_vspaceRoot_iff {x : SeLe4n.ObjId} {v : VSpaceRoot} :
    st'.objects[x]? = some (.vspaceRoot v) ↔ st.objects[x]? = some (.vspaceRoot v) :=
  ⟨h.get_of_not_tcb' (fun _ e => KernelObject.noConfusion e),
   h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e)⟩

theorem get_untyped_iff {x : SeLe4n.ObjId} {u : UntypedObject} :
    st'.objects[x]? = some (.untyped u) ↔ st.objects[x]? = some (.untyped u) :=
  ⟨h.get_of_not_tcb' (fun _ e => KernelObject.noConfusion e),
   h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e)⟩

theorem get_schedContext_iff {x : SeLe4n.ObjId} {sc : SeLe4n.Kernel.SchedContext} :
    st'.objects[x]? = some (.schedContext sc) ↔ st.objects[x]? = some (.schedContext sc) :=
  ⟨h.get_of_not_tcb' (fun _ e => KernelObject.noConfusion e),
   h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e)⟩

theorem get_reply_iff {x : SeLe4n.ObjId} {r : SeLe4n.Kernel.Reply} :
    st'.objects[x]? = some (.reply r) ↔ st.objects[x]? = some (.reply r) :=
  ⟨h.get_of_not_tcb' (fun _ e => KernelObject.noConfusion e),
   h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e)⟩

theorem get_frame_iff {x : SeLe4n.ObjId} {f : FrameObject} :
    st'.objects[x]? = some (.frame f) ↔ st.objects[x]? = some (.frame f) :=
  ⟨h.get_of_not_tcb' (fun _ e => KernelObject.noConfusion e),
   h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e)⟩

theorem get_pageTable_iff {x : SeLe4n.ObjId} {pt : PageTableObject} :
    st'.objects[x]? = some (.pageTable pt) ↔ st.objects[x]? = some (.pageTable pt) :=
  ⟨h.get_of_not_tcb' (fun _ e => KernelObject.noConfusion e),
   h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e)⟩

/-- A TCB of `st'` is a TCB of `st` with its run-queue fields rewritten — the
form a proof can `subst`, so every non-run field it reads off the post-state TCB
is, by definition, the pre-state TCB's. -/
theorem get_tcb_back {x : SeLe4n.ObjId} {t' : TCB} (hx : st'.objects[x]? = some (.tcb t')) :
    ∃ t : TCB, ∃ (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx : Nat),
      st.objects[x]? = some (.tcb t) ∧
      t' = { t with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                    runBucketPrevCode := rbpv, runBucketNextCode := rbnx } := by
  obtain ⟨t, ht, e⟩ := h.get_tcb' hx
  exact ⟨t, _, _, _, _, _, _, ht, TCB.eq_withRunLinks_of_withoutRunLinks_eq e⟩

/-- The same, from `st` to `st'`. -/
theorem get_tcb_fwd {x : SeLe4n.ObjId} {t : TCB} (hx : st.objects[x]? = some (.tcb t)) :
    ∃ t' : TCB, ∃ (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx : Nat),
      st'.objects[x]? = some (.tcb t') ∧
      t = { t' with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                    runBucketPrevCode := rbpv, runBucketNextCode := rbnx } :=
  h.symm.get_tcb_back hx

/-- A key holds a TCB in one store exactly when it does in the other. -/
theorem exists_tcb_iff {x : SeLe4n.ObjId} :
    (∃ t, st'.objects[x]? = some (.tcb t)) ↔ (∃ t, st.objects[x]? = some (.tcb t)) :=
  ⟨fun ⟨_, ht⟩ => let ⟨t, ht', _⟩ := h.get_tcb' ht; ⟨t, ht'⟩,
   fun ⟨_, ht⟩ => let ⟨t, ht', _⟩ := h.get_tcb ht; ⟨t, ht'⟩⟩

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

/-- Scheduling contexts read the same in both stores. -/
theorem getSchedContext? (scId : SeLe4n.SchedContextId) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?
  cases e : st.objects[scId.toObjId]? with
  | none => rw [h.get_none_iff.mpr e]
  | some o => cases o with
    | schedContext sc => rw [h.get_schedContext_iff.mpr e]
    | tcb t => obtain ⟨t', h', _⟩ := h.get_tcb e; rw [h']
    | _ => rw [h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e) e]

/-- Reply objects read the same in both stores. -/
theorem getReply? (rid : SeLe4n.ReplyId) : st'.getReply? rid = st.getReply? rid := by
  unfold SystemState.getReply?
  cases e : st.objects[rid.toObjId]? with
  | none => rw [h.get_none_iff.mpr e]
  | some o => cases o with
    | reply r => rw [h.get_reply_iff.mpr e]
    | tcb t => obtain ⟨t', h', _⟩ := h.get_tcb e; rw [h']
    | _ => rw [h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e) e]

/-- A step that writes only run-queue links rewrites each object to one of its
own kind. -/
theorem kindPreserving : SeLe4n.Model.kindPreservingWrite st st' := by
  intro oid
  cases e : st.objects[oid]? with
  | none => exact Or.inl (h.get_none_iff.mpr e)
  | some o => cases o with
    | tcb t =>
      obtain ⟨t', h', _⟩ := h.get_tcb e
      exact Or.inr ⟨_, _, rfl, h', rfl, by simp [KernelObject.objectType]⟩
    | _ => exact Or.inl (h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e) e)

end objectsAgreeOffRunLinks

/-- A TCB rewrite that changes only run-queue fields. -/
def RunLinksOnly (g : TCB → TCB) : Prop := ∀ tcb, (g tcb).withoutRunLinks = tcb.withoutRunLinks

theorem mapTcbInPlace_objectsAgreeOffRunLinks (st : SystemState) (tid : SeLe4n.ThreadId)
    {g : TCB → TCB} (hg : RunLinksOnly g) :
    objectsAgreeOffRunLinks (st.mapTcbInPlace tid g) st := by
  intro x
  rw [objects_mapTcbInPlace]
  split
  · cases st.objects[x]? with
    | none => rfl
    | some o => cases o <;> simp [KernelObject.mapTcb, hg _]
  · rfl

theorem updateTcbAtCode_objectsAgreeOffRunLinks (st : SystemState) (k : Nat)
    {g : TCB → TCB} (hg : RunLinksOnly g) :
    objectsAgreeOffRunLinks (st.updateTcbAtCode k g) st := by
  unfold updateTcbAtCode; split
  · exact .refl _
  · exact mapTcbInPlace_objectsAgreeOffRunLinks _ _ hg

theorem runAppendLinks_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    objectsAgreeOffRunLinks (st.runAppendLinks c t p) st := by
  unfold runAppendLinks
  exact .trans (updateTcbAtCode_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
    (.trans (updateTcbAtCode_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
      (mapTcbInPlace_objectsAgreeOffRunLinks _ _ (fun _ => rfl)))

theorem runEnqueueOnCore_objects (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueOnCore c t p).objects =
      if (st.runLinkOn c t).queued then st.objects else (st.runAppendLinks c t p).objects := by
  unfold runEnqueueOnCore; dsimp only; split <;> rfl

theorem runEnqueueOnCore_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    objectsAgreeOffRunLinks (st.runEnqueueOnCore c t p) st := by
  have h := runEnqueueOnCore_objects st c t p
  split at h
  · exact .of_objects_eq h
  · exact .congr h rfl (runAppendLinks_objectsAgreeOffRunLinks st c t p)

theorem runEnqueueOnCore_objects_invExt (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    (st.runEnqueueOnCore c t p).objects.invExt := by
  rw [runEnqueueOnCore_objects]; split
  · exact hInv
  · exact runAppendLinks_objects_invExt _ _ _ _ hInv

theorem runEnqueueOnCore_objects_invExtK (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hK : st.objects.invExtK) :
    (st.runEnqueueOnCore c t p).objects.invExtK := by
  rw [runEnqueueOnCore_objects]; split
  · exact hK
  · exact runAppendLinks_objects_invExtK _ _ _ _ hK

theorem runUnlinkLinks_objectsAgreeOffRunLinks (st : SystemState) (t : SeLe4n.ThreadId)
    (pv nx bpv bnx : Nat) :
    objectsAgreeOffRunLinks (st.runUnlinkLinks t pv nx bpv bnx) st := by
  unfold runUnlinkLinks
  exact .trans (mapTcbInPlace_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
    (.trans (updateTcbAtCode_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
    (.trans (updateTcbAtCode_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
    (.trans (updateTcbAtCode_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
      (updateTcbAtCode_objectsAgreeOffRunLinks _ _ (fun _ => rfl)))))

theorem runRemoveOnCore_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) :
    objectsAgreeOffRunLinks (st.runRemoveOnCore c t) st := by
  have h := runRemoveOnCore_objects st c t
  split at h
  · exact .congr h rfl (runUnlinkLinks_objectsAgreeOffRunLinks _ _ _ _ _ _)
  · exact .of_objects_eq h

-- ============================================================================
-- Only the object store and the scheduler change
-- ============================================================================

/-- `st'` is `st` with at most its object store and scheduler rewritten: every
other component is `st`'s. -/
def onlyObjectsSchedulerDiffer (st' st : SystemState) : Prop :=
  st' = { st with objects := st'.objects, scheduler := st'.scheduler }

namespace onlyObjectsSchedulerDiffer

theorem refl (st : SystemState) : onlyObjectsSchedulerDiffer st st := rfl

theorem trans {a b c : SystemState} (h₂ : onlyObjectsSchedulerDiffer c b)
    (h₁ : onlyObjectsSchedulerDiffer b a) : onlyObjectsSchedulerDiffer c a := by
  unfold onlyObjectsSchedulerDiffer at *
  calc c = { b with objects := c.objects, scheduler := c.scheduler } := h₂
    _ = _ := by rw [h₁]

theorem withScheduler {a b : SystemState} (h : onlyObjectsSchedulerDiffer b a)
    (s : SchedulerState) : onlyObjectsSchedulerDiffer { b with scheduler := s } a := by
  unfold onlyObjectsSchedulerDiffer at *
  conv => lhs; rw [h]

theorem mapTcbInPlace (st : SystemState) (tid : SeLe4n.ThreadId) (g : TCB → TCB) :
    onlyObjectsSchedulerDiffer (st.mapTcbInPlace tid g) st := rfl

theorem updateTcbAtCode (st : SystemState) (k : Nat) (g : TCB → TCB) :
    onlyObjectsSchedulerDiffer (st.updateTcbAtCode k g) st := by
  unfold SystemState.updateTcbAtCode; split
  · exact .refl _
  · exact mapTcbInPlace _ _ _

/-- Every table but the object store is `st`'s, so the kernel-level table
invariant needs only the object store's. -/
theorem allTablesInvExtK {a b : SystemState} (h : onlyObjectsSchedulerDiffer b a)
    (hK : b.objects.invExtK) (hA : a.allTablesInvExtK) : b.allTablesInvExtK := by
  unfold onlyObjectsSchedulerDiffer at h
  rw [h]
  exact ⟨hK, hA.2⟩

end onlyObjectsSchedulerDiffer

theorem runAppendLinks_onlyObjectsSchedulerDiffer (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    onlyObjectsSchedulerDiffer (st.runAppendLinks c t p) st := by
  unfold runAppendLinks
  exact .trans (.updateTcbAtCode _ _ _) (.trans (.updateTcbAtCode _ _ _) (.mapTcbInPlace _ _ _))

theorem runEnqueueOnCore_onlyObjectsSchedulerDiffer (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    onlyObjectsSchedulerDiffer (st.runEnqueueOnCore c t p) st := by
  unfold runEnqueueOnCore runAppendOnCore; dsimp only; split
  · exact .withScheduler (.refl _) _
  · exact .withScheduler (.withScheduler (runAppendLinks_onlyObjectsSchedulerDiffer _ _ _ _) _) _

theorem runUnlinkLinks_onlyObjectsSchedulerDiffer (st : SystemState) (t : SeLe4n.ThreadId)
    (pv nx bpv bnx : Nat) : onlyObjectsSchedulerDiffer (st.runUnlinkLinks t pv nx bpv bnx) st := by
  unfold runUnlinkLinks
  exact .trans (.mapTcbInPlace _ _ _) (.trans (.updateTcbAtCode _ _ _) (.trans (.updateTcbAtCode _ _ _)
    (.trans (.updateTcbAtCode _ _ _) (.updateTcbAtCode _ _ _))))

theorem runRemoveOnCore_onlyObjectsSchedulerDiffer (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) : onlyObjectsSchedulerDiffer (st.runRemoveOnCore c t) st := by
  unfold runRemoveOnCore; dsimp only; split
  · exact .withScheduler (.withScheduler (runUnlinkLinks_onlyObjectsSchedulerDiffer _ _ _ _ _ _) _) _
  · exact .withScheduler (.refl _) _

-- ============================================================================
-- What each run-queue write does to the scheduler
-- ============================================================================

/-- Core `c`'s ends once `t` is enqueued there at `p`. -/
def runEnqueueEnds (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : RunQueueEnds :=
  if (st.runLinkOn c t).queued then st.scheduler.runQueueEndsOnCore c
  else (st.scheduler.runQueueEndsOnCore c).append t p

/-- Core `c`'s ends once `t` is dequeued there. -/
def runRemoveEnds (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) : RunQueueEnds :=
  let L := st.runLinkOn c t
  if L.queued then
    (st.scheduler.runQueueEndsOnCore c).unlink L.prev L.next L.bucketPrev L.bucketNext L.prio
      (fun n h => RunQueue.maxPrioCodeWalkBy
        ((st.runUnlinkLinks t L.prev L.next L.bucketPrev L.bucketNext).runLinkOn c) n h 0)
  else st.scheduler.runQueueEndsOnCore c

@[simp] theorem runEnqueueOnCore_scheduler (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueOnCore c t p).scheduler =
      (st.scheduler.setRunQueueEndsOnCore c (st.runEnqueueEnds c t p)).setRunQueueOnCore c
        ((st.scheduler.runQueueOnCore c).insert t p) := by
  unfold runEnqueueOnCore runEnqueueEnds runAppendOnCore
  by_cases hq : (st.runLinkOn c t).queued = true
  · simp only [hq, if_true, SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_get]
  · simp only [hq, if_false, Bool.false_eq_true, runAppendLinks_scheduler,
      SchedulerState.setRunQueueEndsOnCore_runQueueOnCore]

@[simp] theorem runRemoveOnCore_scheduler (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.runRemoveOnCore c t).scheduler =
      (st.scheduler.setRunQueueEndsOnCore c (st.runRemoveEnds c t)).setRunQueueOnCore c
        ((st.scheduler.runQueueOnCore c).remove t) := by
  unfold runRemoveOnCore runRemoveEnds
  by_cases hq : (st.runLinkOn c t).queued = true
  · simp only [hq, if_true, runUnlinkLinks_scheduler,
      SchedulerState.setRunQueueEndsOnCore_runQueueOnCore]
  · simp only [hq, if_false, Bool.false_eq_true,
      SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_get]

-- ============================================================================
-- Deschedule: dequeue plus the `current` slot
-- ============================================================================

/-- Take `t` off core `c`'s scheduler: unlink its run-queue links
(`runRemoveOnCore`) and clear the core's `current` slot if `t` holds it.  The
`current` slot is read before the dequeue, which does not write it.  The one
body behind `removeRunnableOnCore`, `removeRunnable` (its boot-core instance)
and each step of the destroy sweep.

The reschedule-SGI accumulator (KSC-1) is flagged exactly when the `current`
slot changes; a pure queue removal stales nothing, so it flags nothing. -/
def runDescheduleOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) : SystemState :=
  let st' := st.runRemoveOnCore c t
  { st' with
      scheduler := SchedulerState.markReschedulePendingOnCoreIf
        (st'.scheduler.setCurrentOnCore c
          (if st.scheduler.currentOnCore c = some t then none
            else st.scheduler.currentOnCore c))
        c (st.scheduler.currentOnCore c == some t) }

theorem runDescheduleOnCore_onlyObjectsSchedulerDiffer (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) : onlyObjectsSchedulerDiffer (st.runDescheduleOnCore c t) st :=
  (runRemoveOnCore_onlyObjectsSchedulerDiffer st c t).withScheduler _

theorem runDescheduleOnCore_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) : (st.runDescheduleOnCore c t).objectsAgreeOffRunLinks st :=
  runRemoveOnCore_objectsAgreeOffRunLinks st c t

theorem runDescheduleOnCore_objects_invExt (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : (st.runDescheduleOnCore c t).objects.invExt :=
  runRemoveOnCore_objects_invExt st c t hInv

@[simp] theorem runDescheduleOnCore_scheduler (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) :
    (st.runDescheduleOnCore c t).scheduler =
      SchedulerState.markReschedulePendingOnCoreIf
        (((st.scheduler.setRunQueueEndsOnCore c (st.runRemoveEnds c t)).setRunQueueOnCore c
          ((st.scheduler.runQueueOnCore c).remove t)).setCurrentOnCore c
          (if st.scheduler.currentOnCore c = some t then none
            else st.scheduler.currentOnCore c))
        c (st.scheduler.currentOnCore c == some t) := by
  simp only [runDescheduleOnCore, runRemoveOnCore_scheduler]

end SeLe4n.Model.SystemState

namespace SeLe4n.Model.SystemState

/-- `run_links_back e at t h`: with `e` a relation whose namespace offers
`get_tcb_back` (`objectsAgreeOffRunLinks st' st`, or the IPC read view) and
`h : st'.objects[x]? = some (.tcb t)`, replace `t` by the pre-state TCB (with
its run-queue fields rewritten, so every other field reads the pre-state's)
and `h` by the pre-state read `st.objects[x]? = some (.tcb t)`. -/
syntax (name := runLinksBack) "run_links_back " term " at " Lean.Parser.Tactic.rcasesPatLo ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| run_links_back $e at $t $h) =>
    `(tactic| (obtain ⟨$t, _, _, _, _, _, _, hPreRunLinks, rfl⟩ :=
                  ($e).get_tcb_back $h
               clear $h
               have $h := hPreRunLinks
               clear hPreRunLinks))

/-- `run_links_fwd e at t h`: the same from `st` to `st'`. -/
syntax (name := runLinksFwd) "run_links_fwd " term " at " Lean.Parser.Tactic.rcasesPatLo ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| run_links_fwd $e at $t $h) =>
    `(tactic| (obtain ⟨$t, _, _, _, _, _, _, hPostRunLinks, rfl⟩ :=
                  ($e).get_tcb_fwd $h
               clear $h
               have $h := hPostRunLinks
               clear hPostRunLinks))

end SeLe4n.Model.SystemState
