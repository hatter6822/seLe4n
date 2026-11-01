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
outside the run queue can see.  WS-ZA ZA4.6: and its four reply-waiter fields
(the links among a server's reply waiters, and a server's queue head and
count), which only the reply-waiter queues and priority inheritance's walk of
them read (`SystemState.replyWaitersConsistent`, `replyWaitersOf`); a write of
either kind of link is a frame for every other reader.  WS-ZA ZA4.7: and the
four fields a blocked sender's capability fills in (`TCB.setSendCap`), which
only the receive that takes its message reads (`blockedSenderMessage`). -/
def TCB.withoutRunLinks (t : TCB) : TCB :=
  { t with runCoreCode := 0, runPrio := ⟨0⟩, runPrevCode := 0, runNextCode := 0,
           runBucketPrevCode := 0, runBucketNextCode := 0,
           replyWaiterPrevCode := 0, replyWaiterNextCode := 0,
           replyWaitersHeadCode := 0, replyWaitersCount := 0,
           ipcBadge := 0, ipcBadged := false, ipcCanGrant := false, ipcFaultSend := false }

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
                  runBucketNextCode := t'.runBucketNextCode,
                  replyWaiterPrevCode := t'.replyWaiterPrevCode,
                  replyWaiterNextCode := t'.replyWaiterNextCode,
                  replyWaitersHeadCode := t'.replyWaitersHeadCode,
                  replyWaitersCount := t'.replyWaitersCount,
                  ipcBadge := t'.ipcBadge, ipcBadged := t'.ipcBadged,
                  ipcCanGrant := t'.ipcCanGrant, ipcFaultSend := t'.ipcFaultSend } := by
  cases t; cases t'
  simp only [TCB.withoutRunLinks, TCB.mk.injEq] at e ⊢
  simp only [e, and_self]

/-- Two TCBs that agree off the run-queue links and the space-slot links: the
first is the second with those fields rewritten. -/
theorem TCB.eq_withRunAndSpaceLinks_of_eq {t t' : TCB}
    (e : t'.withoutRunLinks.withoutLinks = t.withoutRunLinks.withoutLinks) :
    t' = { t with runCoreCode := t'.runCoreCode, runPrio := t'.runPrio,
                  runPrevCode := t'.runPrevCode, runNextCode := t'.runNextCode,
                  runBucketPrevCode := t'.runBucketPrevCode,
                  runBucketNextCode := t'.runBucketNextCode,
                  replyWaiterPrevCode := t'.replyWaiterPrevCode,
                  replyWaiterNextCode := t'.replyWaiterNextCode,
                  replyWaitersHeadCode := t'.replyWaitersHeadCode,
                  replyWaitersCount := t'.replyWaitersCount,
                  ipcBadge := t'.ipcBadge, ipcBadged := t'.ipcBadged,
                  ipcCanGrant := t'.ipcCanGrant, ipcFaultSend := t'.ipcFaultSend,
                  spaceLinks := t'.spaceLinks } := by
  cases t; cases t'
  simp only [TCB.withoutRunLinks, TCB.withoutLinks, TCB.mk.injEq] at e ⊢
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

/-- A lookup that agrees off the run-queue links with `some t` is `some` of a
TCB agreeing with `t` there. -/
theorem TCB.exists_of_map_withoutRunLinks_eq {a : Option TCB} {t : TCB}
    (h : a.map TCB.withoutRunLinks = (some t).map TCB.withoutRunLinks) :
    ∃ t', a = some t' ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  cases a with
  | none => cases h
  | some t' => exact ⟨t', rfl, Option.some.inj h⟩

/-- A TCB rewrite that reads no run-queue field: rewriting those fields first
changes nothing off them. -/
def TCB.RunLinksBlind (f : TCB → TCB) : Prop :=
  ∀ (t : TCB) (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx rwp rwn rwh rwc : Nat) (ib : UInt64) (ibd icg ifs : Bool),
    (f { t with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                runBucketPrevCode := rbpv, runBucketNextCode := rbnx,
                    replyWaiterPrevCode := rwp, replyWaiterNextCode := rwn,
                    replyWaitersHeadCode := rwh, replyWaitersCount := rwc,
                    ipcBadge := ib, ipcBadged := ibd, ipcCanGrant := icg, ipcFaultSend := ifs }).withoutRunLinks =
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


/-- **Two objects that agree off the run-queue links hold the same capability
slots**: the run-queue fields are no slot and no link word. -/
theorem KernelObject.slots_eq_of_withoutRunLinks_eq {o o' : KernelObject}
    (h : o'.withoutRunLinks = o.withoutRunLinks) :
    o'.slotCap = o.slotCap ∧ o'.linkWords = o.linkWords ∧ (∀ s, o'.hasSlot s ↔ o.hasSlot s) := by
  rcases KernelObject.withoutRunLinks_eq_cases h with e | ⟨t, t', rfl, rfl⟩
  · subst e; exact ⟨rfl, rfl, fun _ => .rfl⟩
  · have hT := KernelObject.tcb.inj h
    have hc : t'.spaceCells = t.spaceCells := TCB.proj_eq_of_withoutRunLinks_eq (·.spaceCells) hT
    have hl : t'.spaceLinks = t.spaceLinks := TCB.proj_eq_of_withoutRunLinks_eq (·.spaceLinks) hT
    refine ⟨funext fun s => ?_, ?_, fun _ => .rfl⟩
    · show t'.spaceSlotCap s = t.spaceSlotCap s
      unfold TCB.spaceSlotCap; rw [hc]
    · show t'.spaceLinks.toArray = t.spaceLinks.toArray
      rw [hl]

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

/-- WS-ZA ZA5.12: **the run-queue fields hold no taint words**, so two stores
agreeing off them read the same declassification taint. -/
theorem declassificationTaint : st'.declassificationTaint = st.declassificationTaint :=
  funext fun x => by
    have hx := h x
    have key : ∀ o : KernelObject, o.withoutRunLinks.taintWords = o.taintWords := by
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

/-- At every key the two stores hold the same object, or a TCB in both. -/
theorem pointwise (x : SeLe4n.ObjId) :
    st'.objects[x]? = st.objects[x]? ∨
      ∃ t t' : TCB, st.objects[x]? = some (.tcb t) ∧ st'.objects[x]? = some (.tcb t') := by
  cases e : st.objects[x]? with
  | none => exact Or.inl ((h.get_none_iff).mpr e)
  | some o =>
    cases o with
    | tcb t =>
      obtain ⟨t', ht', _⟩ := h.get_tcb e
      exact Or.inr ⟨t, t', rfl, ht'⟩
    | _ => exact Or.inl (h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e) e)

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

/-- An object of `st'` was in `st`, holding the same capability slots. -/
theorem slots_back {x : SeLe4n.ObjId} {o' : KernelObject} (hx : st'.objects[x]? = some o') :
    ∃ o, st.objects[x]? = some o ∧ o'.slotCap = o.slotCap ∧ o'.linkWords = o.linkWords ∧
      (∀ s, o'.hasSlot s ↔ o.hasSlot s) := by
  obtain ⟨o, ho, he⟩ := KernelObject.map_withoutRunLinks_eq_some (h x) hx
  exact ⟨o, ho, KernelObject.slots_eq_of_withoutRunLinks_eq he⟩

/-- An object of `st` is in `st'`, holding the same capability slots. -/
theorem slots_fwd {x : SeLe4n.ObjId} {o : KernelObject} (hx : st.objects[x]? = some o) :
    ∃ o', st'.objects[x]? = some o' ∧ o'.slotCap = o.slotCap ∧ o'.linkWords = o.linkWords ∧
      (∀ s, o'.hasSlot s ↔ o.hasSlot s) := by
  obtain ⟨o', ho', he⟩ := KernelObject.map_withoutRunLinks_eq_some (h x).symm hx
  exact ⟨o', ho', KernelObject.slots_eq_of_withoutRunLinks_eq he.symm⟩

/-- At every key the two stores hold the same link words. -/
theorem linkWords (x : SeLe4n.ObjId) :
    (st'.objects[x]?).map KernelObject.linkWords = (st.objects[x]?).map KernelObject.linkWords := by
  cases hx : st.objects[x]? with
  | none => rw [h.get_none_iff.mpr hx]
  | some o =>
    obtain ⟨o', ho', -, hw, -⟩ := h.slots_fwd hx
    rw [ho']; simp only [Option.map_some, hw]

/-- A TCB of `st'` is a TCB of `st` with its run-queue fields rewritten — the
form a proof can `subst`, so every non-run field it reads off the post-state TCB
is, by definition, the pre-state TCB's. -/
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

/-- A thread resolving in `st` resolves in `st'` to a TCB agreeing off its
run-queue fields. -/
theorem getTcb?_some {tid : SeLe4n.ThreadId} {t : TCB} (ht : st.getTcb? tid = some t) :
    ∃ t', st'.getTcb? tid = some t' ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  obtain ⟨t', h', e⟩ := h.get_tcb ((getTcb?_eq_some_iff st tid t).mp ht)
  exact ⟨t', (getTcb?_eq_some_iff st' tid t').mpr h', e⟩

/-- The same, from `st'` back to `st`. -/
theorem getTcb?_some' {tid : SeLe4n.ThreadId} {t' : TCB} (ht : st'.getTcb? tid = some t') :
    ∃ t, st.getTcb? tid = some t ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  obtain ⟨t, h₀, e⟩ := h.get_tcb' ((getTcb?_eq_some_iff st' tid t').mp ht)
  exact ⟨t, (getTcb?_eq_some_iff st tid t).mpr h₀, e⟩

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
      obtain ⟨t', h', ht⟩ := h.get_tcb e
      exact Or.inr ⟨_, _, rfl, h', rfl, by simp [KernelObject.objectType], by
        simp only [KernelObject.tcbSlots,
          TCB.proj_eq_of_withoutRunLinks_eq (·.spaceCells) ht,
          TCB.proj_eq_of_withoutRunLinks_eq (·.spaceLinks) ht], rfl, by
        simp only [KernelObject.bindingCodes,
          TCB.proj_eq_of_withoutRunLinks_eq (·.boundNotificationCode) ht], by
        simp only [KernelObject.tableBackLinks,
          TCB.proj_eq_of_withoutRunLinks_eq (·.taintWords) ht], rfl⟩
    | _ => exact Or.inl (h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e) e)

end objectsAgreeOffRunLinks

/-- A run-links-only rewrite that writes no release-queue slot holds the
release queues. -/
theorem releaseStateAgree.of_agreeOffRunLinks {st st' : SystemState}
    (h : objectsAgreeOffRunLinks st' st)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots) : releaseStateAgree st' st :=
  ⟨.of_map KernelObject.withoutRunLinks (fun o _ => by cases o <;> rfl) h, hS⟩

/-- A run-links-only rewrite keeps every context's refill view. -/
theorem _root_.SeLe4n.Kernel.RefillViewsKept.of_agreeOffRunLinks {st st' : SystemState}
    (h : objectsAgreeOffRunLinks st' st) : RefillViewsKept st' st :=
  .of_map KernelObject.withoutRunLinks (fun o => by cases o <;> rfl) h

/-- A run-links-only rewrite keeps every slot's yield codes (WS-ZA ZA6.6). -/
theorem _root_.SeLe4n.Kernel.YieldLinksKept.of_agreeOffRunLinks {st st' : SystemState}
    (h : objectsAgreeOffRunLinks st' st) : YieldLinksKept st' st :=
  .of_map KernelObject.withoutRunLinks (fun o => by cases o <;> rfl) h

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

theorem runEnqueueAdmitted_objects (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueAdmitted c t p).objects =
      if (st.runLinkOn c t).queued then st.objects else (st.runAppendLinks c t p).objects := by
  unfold runEnqueueAdmitted; dsimp only; split <;> rfl

theorem runEnqueueAdmitted_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    objectsAgreeOffRunLinks (st.runEnqueueAdmitted c t p) st := by
  have h := runEnqueueAdmitted_objects st c t p
  split at h
  · exact .of_objects_eq h
  · exact .congr h rfl (runAppendLinks_objectsAgreeOffRunLinks st c t p)

theorem runEnqueueOnCore_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    objectsAgreeOffRunLinks (st.runEnqueueOnCore c t p) st := by
  unfold runEnqueueOnCore; split
  · exact runEnqueueAdmitted_objectsAgreeOffRunLinks st c t p
  · exact .of_objects_eq rfl

theorem runEnqueueAdmitted_objects_invExt (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    (st.runEnqueueAdmitted c t p).objects.invExt := by
  rw [runEnqueueAdmitted_objects]; split
  · exact hInv
  · exact runAppendLinks_objects_invExt _ _ _ _ hInv

theorem runEnqueueOnCore_objects_invExt (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    (st.runEnqueueOnCore c t p).objects.invExt := by
  unfold runEnqueueOnCore; split
  · exact runEnqueueAdmitted_objects_invExt st c t p hInv
  · exact hInv

theorem runEnqueueAdmitted_objects_invExtK (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hK : st.objects.invExtK) :
    (st.runEnqueueAdmitted c t p).objects.invExtK := by
  rw [runEnqueueAdmitted_objects]; split
  · exact hK
  · exact runAppendLinks_objects_invExtK _ _ _ _ hK

theorem runEnqueueOnCore_objects_invExtK (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hK : st.objects.invExtK) :
    (st.runEnqueueOnCore c t p).objects.invExtK := by
  unfold runEnqueueOnCore; split
  · exact runEnqueueAdmitted_objects_invExtK st c t p hK
  · exact hK

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

/-- A step that writes only run-queue links keeps the state fields. -/
theorem StateMono.of_agreeOffRunLinks {st st' : SystemState} (h : objectsAgreeOffRunLinks st' st) :
    StateMono st st' :=
  StateMono.of_stateFields fun t =>
    TCB.map_proj_eq_of_map_withoutRunLinks_eq (fun x => (x.ipcState, x.threadState, x.cpuAffinity))
      (h.getTcb? t)

/-- A step that writes only run-queue links keeps every table back-link: a
thread holds none. -/
theorem TableReferenceFrame.of_agreeOffRunLinks {st st' : SystemState}
    (h : objectsAgreeOffRunLinks st' st)
    (hT : st'.referenceTables = st.referenceTables := by table_frame) :
    TableReferenceFrame st st' :=
  .of_map (g := KernelObject.withoutRunLinks) (fun o => by cases o <;> rfl) hT h


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

/-- The tables that name objects by id are `st`'s. -/
theorem referenceTables {a b : SystemState} (h : onlyObjectsSchedulerDiffer b a) :
    b.referenceTables = a.referenceTables := by
  unfold onlyObjectsSchedulerDiffer at h
  rw [h]; rfl

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

theorem runEnqueueAdmitted_onlyObjectsSchedulerDiffer (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    onlyObjectsSchedulerDiffer (st.runEnqueueAdmitted c t p) st := by
  unfold runEnqueueAdmitted runAppendOnCore; dsimp only; split
  · exact .withScheduler (.refl _) _
  · exact .withScheduler (.withScheduler (runAppendLinks_onlyObjectsSchedulerDiffer _ _ _ _) _) _

theorem runEnqueueOnCore_onlyObjectsSchedulerDiffer (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    onlyObjectsSchedulerDiffer (st.runEnqueueOnCore c t p) st := by
  unfold runEnqueueOnCore; split
  · exact runEnqueueAdmitted_onlyObjectsSchedulerDiffer st c t p
  · exact .refl _

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

@[simp] theorem runRemoveOnCore_referenceTables (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) : (st.runRemoveOnCore c t).referenceTables = st.referenceTables :=
  (runRemoveOnCore_onlyObjectsSchedulerDiffer st c t).referenceTables

@[simp] theorem runEnqueueAdmitted_referenceTables (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (st.runEnqueueAdmitted c t p).referenceTables = st.referenceTables :=
  (runEnqueueAdmitted_onlyObjectsSchedulerDiffer st c t p).referenceTables

@[simp] theorem runEnqueueOnCore_referenceTables (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (st.runEnqueueOnCore c t p).referenceTables = st.referenceTables :=
  (runEnqueueOnCore_onlyObjectsSchedulerDiffer st c t p).referenceTables

/-- A run-queue write leaves the machine where it was. -/
@[simp] theorem runEnqueueAdmitted_machine (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runEnqueueAdmitted c t p).machine = st.machine := by
  have h := runEnqueueAdmitted_onlyObjectsSchedulerDiffer st c t p
  unfold onlyObjectsSchedulerDiffer at h; rw [h]

@[simp] theorem runEnqueueOnCore_machine (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runEnqueueOnCore c t p).machine = st.machine := by
  have h := runEnqueueOnCore_onlyObjectsSchedulerDiffer st c t p
  unfold onlyObjectsSchedulerDiffer at h; rw [h]

@[simp] theorem runRemoveOnCore_machine (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.runRemoveOnCore c t).machine = st.machine := by
  have h := runRemoveOnCore_onlyObjectsSchedulerDiffer st c t
  unfold onlyObjectsSchedulerDiffer at h; rw [h]

/-- The run-queue writes set no core's resident thread (`resident_frame`). -/
macro_rules | `(tactic| resident_frame) => `(tactic|
  (simp only [runEnqueueAdmitted_machine, runEnqueueOnCore_machine, runRemoveOnCore_machine]; done))

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

theorem runEnqueueAdmitted_scheduler (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueAdmitted c t p).scheduler =
      (st.scheduler.setRunQueueEndsOnCore c (st.runEnqueueEnds c t p)).setRunQueueOnCore c
        ((st.scheduler.runQueueOnCore c).insert t p) := by
  unfold runEnqueueAdmitted runEnqueueEnds runAppendOnCore
  by_cases hq : (st.runLinkOn c t).queued = true
  · simp only [hq, if_true, SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_get]
  · simp only [hq, if_false, Bool.false_eq_true, runAppendLinks_scheduler,
      SchedulerState.setRunQueueEndsOnCore_runQueueOnCore]

/-- The scheduler after an enqueue: the admitted enqueue's, or unchanged. -/
theorem runEnqueueOnCore_scheduler (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueOnCore c t p).scheduler =
      if st.runEnqueueAdmits c t then
        (st.scheduler.setRunQueueEndsOnCore c (st.runEnqueueEnds c t p)).setRunQueueOnCore c
          ((st.scheduler.runQueueOnCore c).insert t p)
      else st.scheduler := by
  unfold runEnqueueOnCore; split
  · exact runEnqueueAdmitted_scheduler st c t p
  · rfl

theorem runEnqueueOnCore_scheduler_of_admits {st : SystemState} {c : CoreId}
    {t : SeLe4n.ThreadId} (p : SeLe4n.Priority) (h : st.runEnqueueAdmits c t = true) :
    (st.runEnqueueOnCore c t p).scheduler =
      (st.scheduler.setRunQueueEndsOnCore c (st.runEnqueueEnds c t p)).setRunQueueOnCore c
        ((st.scheduler.runQueueOnCore c).insert t p) := by
  rw [runEnqueueOnCore_of_admits p h, runEnqueueAdmitted_scheduler]

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

theorem RunQueueStage.runRemoveOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    RunQueueStage st (st.runRemoveOnCore c t) :=
  RunQueueStage.of_link (.of_tableFrame
      (fun h r => ⟨runRemoveOnCore_objects_invExt st c t h, runRemoveOnCore_refined r⟩)
      (fun _ => .of_agreeOffRunLinks (runRemoveOnCore_objectsAgreeOffRunLinks st c t)
        (runRemoveOnCore_onlyObjectsSchedulerDiffer st c t).referenceTables)
      (fun _ => .of_agreeOffRunLinks (runRemoveOnCore_objectsAgreeOffRunLinks st c t)
        (by rw [runRemoveOnCore_scheduler]; rfl))
      (fun _ => .of_agreeOffRunLinks (runRemoveOnCore_objectsAgreeOffRunLinks st c t))
      fun _ => .of_agreeOffRunLinks (runRemoveOnCore_objectsAgreeOffRunLinks st c t))
    (fun c' y h' => by
      rw [SchedulerState.currentOnCore, runRemoveOnCore_current] at h'
      exact h')
    (fun c' y h' => by
      rw [runRemoveOnCore_queuedOn] at h'; split at h'
      · cases h'
      · exact h')
    (StateMono.of_agreeOffRunLinks (runRemoveOnCore_objectsAgreeOffRunLinks st c t))

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

/-- The dequeue writes no release-queue slot. -/
@[simp] theorem runDescheduleOnCore_releaseSlots (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.runDescheduleOnCore c t).scheduler.releaseSlots = st.scheduler.releaseSlots := by
  show (st.runRemoveOnCore c t).scheduler.releaseSlots = _
  rw [runRemoveOnCore_scheduler]; rfl

/-- WS-ZA ZA4.7: the compiled `runDescheduleOnCore`.  The core's `current`
slot is compared as its code before the dequeue, so no `some` cell is built
and nothing holds the state the dequeue rewrites.  When `t` is not the core's
current thread the `current` slot and the accumulator are left as the dequeue
left them (ZA5.2): writing the slot's own value back rebuilt it from a
decoded `Option`, and the scheduler record with it. -/
def runDescheduleOnCoreImpl (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    SystemState :=
  if st.scheduler.currentCode.get c == t.val + 1 then
    let st' := st.runRemoveOnCore c t
    { st' with
        scheduler := SchedulerState.markReschedulePendingOnCoreIf
          (st'.scheduler.setCurrentOnCore c none) c true }
  else st.runRemoveOnCore c t

@[csimp] theorem runDescheduleOnCore_eq_impl :
    @runDescheduleOnCore = @runDescheduleOnCoreImpl := by
  funext st c t
  unfold runDescheduleOnCore runDescheduleOnCoreImpl
  by_cases h : st.scheduler.currentCode.get c = t.val + 1
  · have hs : st.scheduler.currentOnCore c = some t := by
      simp [SchedulerState.currentOnCore, h]
    simp [h, hs]
  · have hs : (st.scheduler.currentOnCore c = some t) = False := by
      simp [SchedulerState.currentOnCore, h]
    have hb : (st.scheduler.currentOnCore c == some t) = false := by
      simp [SchedulerState.currentOnCore, h]
    have hd : (st.scheduler.currentCode.get c == t.val + 1) = false := by simp [h]
    simp only [hs, hb, hd, if_false, Bool.false_eq_true]
    have hc : (st.runRemoveOnCore c t).scheduler.currentCode = st.scheduler.currentCode := by
      rw [runRemoveOnCore_scheduler]; rfl
    generalize st.runRemoveOnCore c t = st' at hc ⊢
    have hsch : SchedulerState.markReschedulePendingOnCoreIf
        (st'.scheduler.setCurrentOnCore c (st.scheduler.currentOnCore c)) c false =
          st'.scheduler := by
      simp only [SchedulerState.markReschedulePendingOnCoreIf,
        SchedulerState.setReschedulePendingOnCore, SchedulerState.reschedulePendingOnCore,
        SchedulerState.setCurrentOnCore, SchedulerState.currentOnCore, Bool.or_false,
        SeLe4n.ThreadId.optCode_ofOptCode, ← hc]
      have h1 : st'.scheduler.currentCode.set c.val (st'.scheduler.currentCode.get c) c.isLt =
          st'.scheduler.currentCode := by
        apply Vector.ext; intro i hi
        by_cases hic : c.val = i
        · subst hic; simp [Vector.get]
        · simp [hic]
      have h2 : st'.scheduler.reschedulePending.set c (st'.scheduler.reschedulePending.get c) =
          st'.scheduler.reschedulePending := by
        apply PerCoreFlags.ext; intro c'
        by_cases hcc : c = c'
        · subst hcc; simp
        · rw [PerCoreFlags.get_set_ne _ _ _ _ hcc]
      rw [h1, h2]
    rw [hsch]

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

theorem runDescheduleOnCore_queuedOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (c' : CoreId) (y : SeLe4n.ThreadId) :
    (st.runDescheduleOnCore c t).queuedOn c' y =
      if y = t ∧ c' = c then false else st.queuedOn c' y := by
  have h : RunCoresAgree (st.runDescheduleOnCore c t) (st.runRemoveOnCore c t) :=
    RunCoresAgree.of_objects rfl
  rw [h.queuedOn c' y, runRemoveOnCore_queuedOn]

/-- WS-ZA ZA4.5: re-key thread `t` on core `c` at priority `p`: dequeue it, then
append it to the tail of its new priority bucket, both through the TCB
run-queue links (seL4's `tcbSchedDequeue` then `tcbSchedEnqueue`).  The
ghost queue is re-keyed (`RunQueue.rekey`: only when it holds `t`), so a
requeue never adds a thread to the ghost: under `runQueueRefined` the condition
is the link bit the callers test, and the ghost's membership is preserved with
no hypothesis.  The ghost write is erased, so the compiled requeue is the two
link moves alone. -/
def runRequeueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let st' := (st.runRemoveOnCore c t).runEnqueueAdmitted c t p
  { st' with scheduler := st'.scheduler.setRunQueueOnCore c ((st.scheduler.runQueueOnCore c).rekey t p) }

/-- The requeue's object store is the dequeue-then-enqueue's: the ghost
condition touches only the scheduler. -/
theorem runRequeueOnCore_objects (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runRequeueOnCore c t p).objects = ((st.runRemoveOnCore c t).runEnqueueAdmitted c t p).objects := by
  rfl

/-- A requeue of `t` moves no other thread's core code. -/
theorem runRequeueOnCore_runCoreCode_ne (st : SystemState) (c : CoreId) (t y : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hy : y ≠ t) :
    ((st.runRequeueOnCore c t p).getTcb? y).map TCB.runCoreCode =
      (st.getTcb? y).map TCB.runCoreCode :=
  (RunCoresAgree.of_objects (runRequeueOnCore_objects st c t p) y).trans
    ((runEnqueueAdmitted_runCoreCode_ne _ c t y p hy).trans (runRemoveOnCore_runCoreCode_ne st c t y hy))

/-- A requeue moves no thread's run-queue membership except `t`'s, which it
leaves on `c` (when `t` is a thread at all). -/
theorem runRequeueOnCore_queuedOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) (y : SeLe4n.ThreadId) :
    (st.runRequeueOnCore c t p).queuedOn c' y =
      if y = t then ((st.getTcb? t).isSome && decide (c' = c)) else st.queuedOn c' y := by
  rw [(RunCoresAgree.of_objects (runRequeueOnCore_objects st c t p)).queuedOn c' y,
    runEnqueueAdmitted_queuedOn, runRemoveOnCore_getTcb?_isSome]
  by_cases hy : y = t
  · rw [if_pos hy, if_pos hy]
  · rw [if_neg hy, if_neg hy, runRemoveOnCore_queuedOn, if_neg (fun h => hy h.1)]

/-- Requeueing a thread already queued on `c` moves no thread's membership. -/
theorem runRequeueOnCore_queuedOn_of_queued {st : SystemState} {c : CoreId}
    {t : SeLe4n.ThreadId} (p : SeLe4n.Priority) (h : st.queuedOn c t = true)
    (c' : CoreId) (y : SeLe4n.ThreadId) :
    (st.runRequeueOnCore c t p).queuedOn c' y = st.queuedOn c' y := by
  rw [runRequeueOnCore_queuedOn]
  by_cases hy : y = t
  · subst hy
    rw [if_pos rfl]
    unfold queuedOn at h ⊢
    cases hT : st.getTcb? y with
    | none => rw [hT] at h; cases h
    | some tcb =>
      rw [hT] at h
      simp only [Option.isSome_some, Bool.true_and, beq_iff_eq] at h ⊢
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, h]
      constructor
      · rintro rfl; rfl
      · intro he; exact Fin.ext (by omega)
  · rw [if_neg hy]

theorem runRequeueOnCore_onlyObjectsSchedulerDiffer (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    onlyObjectsSchedulerDiffer (st.runRequeueOnCore c t p) st := by
  have h := (runEnqueueAdmitted_onlyObjectsSchedulerDiffer (st.runRemoveOnCore c t) c t p).trans
    (runRemoveOnCore_onlyObjectsSchedulerDiffer st c t)
  exact h.withScheduler _

theorem runRequeueOnCore_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (st.runRequeueOnCore c t p).objectsAgreeOffRunLinks st := by
  intro x; rw [runRequeueOnCore_objects]
  exact ((runEnqueueAdmitted_objectsAgreeOffRunLinks _ c t p).trans
    (runRemoveOnCore_objectsAgreeOffRunLinks st c t)) x

theorem runRequeueOnCore_objects_invExt (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) : (st.runRequeueOnCore c t p).objects.invExt := by
  rw [runRequeueOnCore_objects]
  exact runEnqueueAdmitted_objects_invExt _ c t p (runRemoveOnCore_objects_invExt st c t hInv)

@[simp] theorem runRequeueOnCore_machine (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runRequeueOnCore c t p).machine = st.machine := by
  have h := runRequeueOnCore_onlyObjectsSchedulerDiffer st c t p
  unfold onlyObjectsSchedulerDiffer at h; rw [h]

/-- The re-key sets no core's resident thread (`resident_frame`). -/
macro_rules | `(tactic| resident_frame) => `(tactic|
  (simp only [runRequeueOnCore_machine]; done))

/-- The scheduler after a re-key: the ghost queue is re-keyed, and the core's
ends are the enqueue's over the dequeued state. -/
@[simp] theorem runRequeueOnCore_scheduler (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runRequeueOnCore c t p).scheduler =
      (st.scheduler.setRunQueueEndsOnCore c ((st.runRemoveOnCore c t).runEnqueueEnds c t p)).setRunQueueOnCore c
        ((st.scheduler.runQueueOnCore c).rekey t p) := by
  unfold runRequeueOnCore; dsimp only
  simp only [runEnqueueAdmitted_scheduler, runRemoveOnCore_scheduler]
  rw [SchedulerState.setRunQueueOnCore_setRunQueueOnCore, SchedulerState.setRunQueueOnCore_setRunQueueEndsOnCore,
    SchedulerState.setRunQueueOnCore_setRunQueueOnCore, SchedulerState.setRunQueueEndsOnCore_setRunQueueEndsOnCore]

/-! A run-queue link write writes only its own core's queue and ends: every
other observable per-core slot reads through. -/

@[simp] theorem runEnqueueOnCore_currentOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueOnCore c t p).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  rw [runEnqueueOnCore_scheduler]; split <;> simp

@[simp] theorem runEnqueueOnCore_activeDomainOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueOnCore c t p).scheduler.activeDomainOnCore c' = st.scheduler.activeDomainOnCore c' := by
  rw [runEnqueueOnCore_scheduler]; split <;> simp

@[simp] theorem runEnqueueOnCore_domainTimeRemainingOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueOnCore c t p).scheduler.domainTimeRemainingOnCore c' = st.scheduler.domainTimeRemainingOnCore c' := by
  rw [runEnqueueOnCore_scheduler]; split <;> simp

@[simp] theorem runEnqueueOnCore_domainScheduleIndexOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueOnCore c t p).scheduler.domainScheduleIndexOnCore c' = st.scheduler.domainScheduleIndexOnCore c' := by
  rw [runEnqueueOnCore_scheduler]; split <;> simp

@[simp] theorem runEnqueueOnCore_reschedulePendingOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueOnCore c t p).scheduler.reschedulePendingOnCore c' = st.scheduler.reschedulePendingOnCore c' := by
  rw [runEnqueueOnCore_scheduler]; split <;> simp

@[simp] theorem runEnqueueOnCore_replenishQueueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueOnCore c t p).scheduler.replenishQueueOnCore c' = st.scheduler.replenishQueueOnCore c' := by
  rw [runEnqueueOnCore_scheduler]; split <;> simp

@[simp] theorem runEnqueueAdmitted_currentOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueAdmitted c t p).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  simp [runEnqueueAdmitted_scheduler]

@[simp] theorem runEnqueueAdmitted_activeDomainOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueAdmitted c t p).scheduler.activeDomainOnCore c' = st.scheduler.activeDomainOnCore c' := by
  simp [runEnqueueAdmitted_scheduler]

@[simp] theorem runEnqueueAdmitted_domainTimeRemainingOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueAdmitted c t p).scheduler.domainTimeRemainingOnCore c' = st.scheduler.domainTimeRemainingOnCore c' := by
  simp [runEnqueueAdmitted_scheduler]

@[simp] theorem runEnqueueAdmitted_domainScheduleIndexOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueAdmitted c t p).scheduler.domainScheduleIndexOnCore c' = st.scheduler.domainScheduleIndexOnCore c' := by
  simp [runEnqueueAdmitted_scheduler]

@[simp] theorem runEnqueueAdmitted_reschedulePendingOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueAdmitted c t p).scheduler.reschedulePendingOnCore c' = st.scheduler.reschedulePendingOnCore c' := by
  simp [runEnqueueAdmitted_scheduler]

@[simp] theorem runEnqueueAdmitted_replenishQueueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runEnqueueAdmitted c t p).scheduler.replenishQueueOnCore c' = st.scheduler.replenishQueueOnCore c' := by
  simp [runEnqueueAdmitted_scheduler]

@[simp] theorem runRequeueOnCore_currentOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runRequeueOnCore c t p).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  simp [runRequeueOnCore_scheduler]

@[simp] theorem runRequeueOnCore_activeDomainOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runRequeueOnCore c t p).scheduler.activeDomainOnCore c' = st.scheduler.activeDomainOnCore c' := by
  simp [runRequeueOnCore_scheduler]

@[simp] theorem runRequeueOnCore_domainTimeRemainingOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runRequeueOnCore c t p).scheduler.domainTimeRemainingOnCore c' = st.scheduler.domainTimeRemainingOnCore c' := by
  simp [runRequeueOnCore_scheduler]

@[simp] theorem runRequeueOnCore_domainScheduleIndexOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runRequeueOnCore c t p).scheduler.domainScheduleIndexOnCore c' = st.scheduler.domainScheduleIndexOnCore c' := by
  simp [runRequeueOnCore_scheduler]

@[simp] theorem runRequeueOnCore_reschedulePendingOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) :
    (st.runRequeueOnCore c t p).scheduler.reschedulePendingOnCore c' = st.scheduler.reschedulePendingOnCore c' := by
  simp [runRequeueOnCore_scheduler]

theorem runRequeueOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (h : c ≠ c') :
    (st.runRequeueOnCore c t p).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  simp [runRequeueOnCore_scheduler, SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ h]

theorem runEnqueueAdmitted_getTcb?_isSome (st : SystemState) (c : CoreId) (t y : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    ((st.runEnqueueAdmitted c t p).getTcb? y).isSome = (st.getTcb? y).isSome := by
  unfold runEnqueueAdmitted; dsimp only
  split
  · rfl
  · show ((st.runAppendLinks c t p).getTcb? y).isSome = _
    unfold runAppendLinks; dsimp only
    rw [updateTcbAtCode_getTcb?_isSome, updateTcbAtCode_getTcb?_isSome,
      mapTcbInPlace_getTcb?_isSome]

theorem runUnlinkLinks_objects_invExtK (st : SystemState) (t : SeLe4n.ThreadId)
    (pv nx bpv bnx : Nat) (hK : st.objects.invExtK) :
    (st.runUnlinkLinks t pv nx bpv bnx).objects.invExtK :=
  mapTcbInPlace_objects_invExtK _ _ _ (updateTcbAtCode_objects_invExtK _ _ _
    (updateTcbAtCode_objects_invExtK _ _ _ (updateTcbAtCode_objects_invExtK _ _ _
      (updateTcbAtCode_objects_invExtK _ _ _ hK))))

theorem runRemoveOnCore_objects_invExtK (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hK : st.objects.invExtK) : (st.runRemoveOnCore c t).objects.invExtK := by
  rw [runRemoveOnCore_objects]
  split
  · exact runUnlinkLinks_objects_invExtK _ _ _ _ _ _ hK
  · exact hK

/-- Storing one object at one key over two stores that agree off the run-queue
links keeps them agreeing. -/
theorem objectsAgreeOffRunLinks.withObjectStored {a b : SystemState}
    (h : objectsAgreeOffRunLinks a b) (ha : a.objects.invExt) (hb : b.objects.invExt)
    (k : SeLe4n.ObjId) (o : KernelObject) :
    objectsAgreeOffRunLinks (a.withObjectStored k o) (b.withObjectStored k o) := fun x => by
  rw [withObjectStored_objects, withObjectStored_objects]
  simp only [RHTable_getElem?_eq_get?]
  by_cases hx : k = x
  · subst hx
    rw [RHTable.getElem?_insert_self _ _ _ ha, RHTable.getElem?_insert_self _ _ _ hb]
  · have hNe : ¬((k == x) = true) := fun e => hx (eq_of_beq e)
    rw [RHTable.getElem?_insert_ne _ _ _ _ hNe ha, RHTable.getElem?_insert_ne _ _ _ _ hNe hb]
    have := h x
    simp only [RHTable_getElem?_eq_get?] at this
    exact this

/-- Clearing the run-queue links keeps an object's kind. -/
@[simp] theorem _root_.SeLe4n.Model.KernelObject.objectType_withoutRunLinks (o : KernelObject) :
    o.withoutRunLinks.objectType = o.objectType := by
  cases o <;> rfl

/-- The lifecycle's kind table is untouched and every object keeps its kind, so
the metadata stays consistent with the store. -/
theorem onlyObjectsSchedulerDiffer.objectTypeMetadataConsistent {a b : SystemState}
    (h : onlyObjectsSchedulerDiffer b a) (hA : objectsAgreeOffRunLinks b a)
    (hC : SystemState.objectTypeMetadataConsistent a) :
    SystemState.objectTypeMetadataConsistent b := by
  intro oid
  have hL : b.lifecycle = a.lifecycle := by rw [h]
  have e := congrArg (Option.map KernelObject.objectType) (hA oid)
  simp only [Option.map_map, Function.comp_def, KernelObject.objectType_withoutRunLinks] at e
  unfold lookupObjectTypeMeta at *
  rw [hL, e]
  exact hC oid

end SeLe4n.Model.SystemState

namespace SeLe4n.Model.SystemState

/-- `run_links_back e at t h`: with `e` a relation whose namespace offers
`get_tcb_back` (`objectsAgreeOffRunLinks st' st`, or the IPC read view) and
`h : st'.objects[x]? = some (.tcb t)`, replace `t` by the pre-state TCB (with
its run-queue fields — and, for the IPC read view, its space-slot links,
bound-notification code and taint words — rewritten, so every other field reads the pre-state's)
and `h` by the pre-state read `st.objects[x]? = some (.tcb t)`. -/
syntax (name := runLinksBack) "run_links_back " term " at " Lean.Parser.Tactic.rcasesPatLo ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| run_links_back $e at $t $h) =>
    `(tactic| (first
                | obtain ⟨$t, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPreRunLinks, rfl⟩ :=
                    ($e).get_tcb_back $h
                | obtain ⟨$t, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPreRunLinks, rfl⟩ :=
                    ($e).get_tcb_back $h
                | obtain ⟨$t, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPreRunLinks, rfl⟩ :=
                    ($e).get_tcb_back $h
               clear $h
               have $h := hPreRunLinks
               clear hPreRunLinks))

/-- `run_links_fwd e at t h`: the same from `st` to `st'`. -/
syntax (name := runLinksFwd) "run_links_fwd " term " at " Lean.Parser.Tactic.rcasesPatLo ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| run_links_fwd $e at $t $h) =>
    `(tactic| (first
                | obtain ⟨$t, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPostRunLinks, rfl⟩ :=
                    ($e).get_tcb_fwd $h
                | obtain ⟨$t, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPostRunLinks, rfl⟩ :=
                    ($e).get_tcb_fwd $h
                | obtain ⟨$t, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPostRunLinks, rfl⟩ :=
                    ($e).get_tcb_fwd $h
               clear $h
               have $h := hPostRunLinks
               clear hPostRunLinks))

end SeLe4n.Model.SystemState

namespace SeLe4n.Model.SystemState
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency (CoreId)

/-! ## The run-queue writes as agreement stages (WS-ZA ZA4.5) -/

/-- A thread queued on core `c` is on no other core's queue: its links name one
core (`TCB.runCoreCode`), so under the agreement the other queues lack it. -/
theorem runQueueRefined.not_contains_of_queued {st : SystemState} (hR : st.runQueueRefined)
    {c c' : CoreId} {t : SeLe4n.ThreadId} (hq : (st.runLinkOn c t).queued = true)
    (hne : c' ≠ c) : (st.scheduler.runQueueOnCore c').contains t = false := by
  obtain ⟨tcb, hT, hC⟩ := (runLinkOn_queued_iff st c t).mp hq
  rw [← (hR c').contains]
  cases hq' : (st.runLinkOn c' t).queued with
  | false => rfl
  | true =>
    obtain ⟨tcb', hT', hC'⟩ := (runLinkOn_queued_iff st c' t).mp hq'
    rw [hT] at hT'; cases hT'
    exact absurd (Fin.ext (by omega)) hne

/-- Re-keying a thread its core's links queue keeps the agreement. -/
theorem RunQueueStage.runRequeueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hq : (st.runLinkOn c t).queued = true) :
    RunQueueStage st (st.runRequeueOnCore c t p) := by
  refine RunQueueStage.of_link ?_
    (fun c' y h' => by
      simpa only [runRequeueOnCore_scheduler, SchedulerState.setRunQueueOnCore_currentOnCore,
        SchedulerState.setRunQueueEndsOnCore_currentOnCore] using h')
    (fun c' y h' => by
      rwa [runRequeueOnCore_queuedOn_of_queued p
        ((queuedOn_eq_runLinkOn st c t).trans hq)] at h')
    (StateMono.of_agreeOffRunLinks (runRequeueOnCore_objectsAgreeOffRunLinks st c t p))
  refine .of_tableFrame ?_ (fun _ => .of_agreeOffRunLinks
    (runRequeueOnCore_objectsAgreeOffRunLinks st c t p)
    (runRequeueOnCore_onlyObjectsSchedulerDiffer st c t p).referenceTables)
    (fun _ => .of_agreeOffRunLinks (runRequeueOnCore_objectsAgreeOffRunLinks st c t p)
      (by rw [runRequeueOnCore_scheduler]; rfl))
    (fun _ => .of_agreeOffRunLinks (runRequeueOnCore_objectsAgreeOffRunLinks st c t p))
    fun _ => .of_agreeOffRunLinks (runRequeueOnCore_objectsAgreeOffRunLinks st c t p)
  intro hInv hR
  refine ⟨runRequeueOnCore_objects_invExt st c t p hInv, ?_⟩
  obtain ⟨tcb, hT, -⟩ := (runLinkOn_queued_iff st c t).mp hq
  have hc : (st.scheduler.runQueueOnCore c).contains t = true := by
    rw [← (hR c).contains]; exact hq
  have hEq : st.runRequeueOnCore c t p = (st.runRemoveOnCore c t).runEnqueueAdmitted c t p := by
    unfold SystemState.runRequeueOnCore; dsimp only
    rw [RunQueue.rekey, if_pos hc, ← runRemoveOnCore_runQueueOnCore_self,
      ← runEnqueueAdmitted_runQueueOnCore_self, SchedulerState.setRunQueueOnCore_runQueueOnCore]
  rw [hEq]
  refine runEnqueueAdmitted_refined (runRemoveOnCore_refined hR) ?_ ?_
  · rw [runRemoveOnCore_getTcb?_isSome, hT]; rfl
  · intro c' hne
    rw [runRemoveOnCore_runQueueOnCore_ne st c c' t (Ne.symm hne)]
    exact hR.not_contains_of_queued hq hne

/-- Taking a thread off a core keeps the agreement: the dequeue is one, and the
`current` slot and the reschedule flag are not read by it. -/
theorem RunQueueStage.runDescheduleOnCore (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) : RunQueueStage st (st.runDescheduleOnCore c t) :=
  (RunQueueStage.runRemoveOnCore st c t).trans (RunQueueStage.of_frame_vacate rfl rfl rfl
    (fun c' y h' => by
      unfold SystemState.runDescheduleOnCore at h'; dsimp only at h'
      simp only [SchedulerState.markReschedulePendingOnCoreIf_currentOnCore] at h'
      by_cases hc : c' = c
      · subst hc
        rw [SchedulerState.setCurrentOnCore_currentOnCore_self] at h'
        split at h'
        · cases h'
        · simpa only [SchedulerState.currentOnCore, runRemoveOnCore_current] using h'
      · rwa [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc)] at h'))

theorem runEnqueueOnCore_current (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runEnqueueOnCore c t p).scheduler.currentCode = st.scheduler.currentCode := by
  unfold runEnqueueOnCore runEnqueueAdmitted runAppendOnCore
  split
  · dsimp only; split <;>
      simp [runAppendLinks_scheduler, SchedulerState.setRunQueueOnCore,
        SchedulerState.setRunQueueEndsOnCore]
  · rfl

/-- The guarded enqueue keeps the link agreement whichever thread it places. -/
theorem RunQueueLinkStage.runEnqueueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : RunQueueLinkStage st (st.runEnqueueOnCore c t p) :=
  .of_tableFrame (fun h r => ⟨runEnqueueOnCore_objects_invExt st c t p h, runEnqueueOnCore_refined r⟩)
    (fun _ => .of_agreeOffRunLinks (runEnqueueOnCore_objectsAgreeOffRunLinks st c t p)
      (runEnqueueOnCore_onlyObjectsSchedulerDiffer st c t p).referenceTables)
    (fun _ => .of_agreeOffRunLinks (runEnqueueOnCore_objectsAgreeOffRunLinks st c t p)
      (by rw [runEnqueueOnCore_scheduler]; split <;> rfl))
    (fun _ => .of_agreeOffRunLinks (runEnqueueOnCore_objectsAgreeOffRunLinks st c t p))
    fun _ => .of_agreeOffRunLinks (runEnqueueOnCore_objectsAgreeOffRunLinks st c t p)

/-- The guarded enqueue of a runnable thread current on no core, on its home
core, is a stage: every current thread stays off the queues, and every queued
one is runnable and on its home. -/
theorem RunQueueStage.runEnqueueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hNC : ∀ c', st.scheduler.currentOnCore c' ≠ some t)
    (hRun : st.runnable t) (hHome : st.homedOn t c) :
    RunQueueStage st (st.runEnqueueOnCore c t p) :=
  RunQueueStage.of_link' (RunQueueLinkStage.runEnqueueOnCore st c t p)
    (fun c' y h' => by rwa [SchedulerState.currentOnCore, runEnqueueOnCore_current] at h')
    (fun c' y hy c'' h' => by
      rw [runEnqueueOnCore_queuedOn, if_neg (fun h => hNC _ (h.1 ▸ hy))] at h'
      exact h')
    (fun y hy c'' h' => by
      rw [runEnqueueOnCore_queuedOn] at h'
      split at h'
      · rename_i h; obtain ⟨rfl, hA⟩ := h
        rw [runEnqueueAdmits_not_idle hA] at hy; cases hy
      · exact h')
    (fun c' y h' => by
      rw [runEnqueueOnCore_queuedOn] at h'
      split at h'
      · rename_i h; obtain ⟨rfl, -⟩ := h
        exact .inr ⟨(StateMono.of_agreeOffRunLinks
          (runEnqueueOnCore_objectsAgreeOffRunLinks st c y p) y).1 hRun,
          (of_decide_eq_true h') ▸
            (StateMono.of_agreeOffRunLinks (runEnqueueOnCore_objectsAgreeOffRunLinks st c y p)).homedOn
              hRun.activeAt hHome⟩
      · exact .inl h')
    (StateMono.of_agreeOffRunLinks (runEnqueueOnCore_objectsAgreeOffRunLinks st c t p))

/-- A stage, then the enqueue of a thread runnable before it and current nowhere
after it, on its home core: the stage keeps the thread runnable. -/
theorem RunQueueStage.then_enqueue {st s : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    {p : SeLe4n.Priority} (h1 : RunQueueStage st s)
    (hNC : ∀ c', s.scheduler.currentOnCore c' ≠ some t) (hRun : st.runnable t)
    (hHome : s.homedOn t c) :
    RunQueueStage st (s.runEnqueueOnCore c t p) :=
  ⟨h1.1.trans (RunQueueLinkStage.runEnqueueOnCore s c t p), fun e h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    (RunQueueStage.runEnqueueOnCore s c t p hNC ((h1.2.2 h r).runnable hRun)
      hHome).2.1 e h' r' r''
      (h1.2.1 e h r r' d),
    fun h r =>
      let ⟨h', r'⟩ := h1.1 h r
      (h1.2.2 h r).trans
        ((RunQueueStage.runEnqueueOnCore s c t p hNC ((h1.2.2 h r).runnable hRun)
          hHome).2.2 h' r')⟩

/-- **A preemption**: the guarded enqueue of core `c`'s current thread back on
`c`'s queue keeps `c`'s scheduling point open. -/
theorem RunQueueWindowStage.requeueCurrent (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) (hCur : st.scheduler.currentOnCore c = some t) :
    RunQueueWindowStage (.preempt c) st (st.runEnqueueOnCore c t p) :=
  ⟨RunQueueLinkStage.runEnqueueOnCore st c t p, fun _ _ _ d =>
    currentDequeuedUniqueExcept_of_requeue d
      (fun c' => by unfold SchedulerState.currentOnCore; rw [runEnqueueOnCore_current])
      (fun c' x hq => by
        rw [runEnqueueOnCore_queuedOn] at hq
        split at hq
        · rename_i h; obtain ⟨rfl, hA⟩ := h
          exact .inr ⟨hCur, of_decide_eq_true hq, runEnqueueAdmits_not_idle hA⟩
        · exact .inl hq)
      (StateMono.of_agreeOffRunLinks (runEnqueueOnCore_objectsAgreeOffRunLinks st c t p)),
    fun _ _ _ _ => StateMono.of_agreeOffRunLinks (runEnqueueOnCore_objectsAgreeOffRunLinks st c t p)⟩

/-- The deschedule empties core `c`'s slot if it held `t`, and keeps every other
slot. -/
theorem runDescheduleOnCore_currentOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (c' : CoreId) :
    (st.runDescheduleOnCore c t).scheduler.currentOnCore c' =
      if c' = c ∧ st.scheduler.currentOnCore c = some t then none
      else st.scheduler.currentOnCore c' := by
  unfold runDescheduleOnCore; dsimp only
  simp only [SchedulerState.markReschedulePendingOnCoreIf_currentOnCore]
  by_cases hc : c' = c
  · subst hc
    rw [SchedulerState.setCurrentOnCore_currentOnCore_self]
    by_cases h : st.scheduler.currentOnCore c' = some t
    · rw [if_pos h, if_pos ⟨rfl, h⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.2)]
  · rw [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc),
      if_neg (fun h => hc h.1)]
    simp only [SchedulerState.currentOnCore, runRemoveOnCore_current]

/-- The deschedule's TCBs differ from the old ones in run-queue links alone. -/
theorem runDescheduleOnCore_getTcb?_ipcState (st : SystemState) (c : CoreId)
    (t u : SeLe4n.ThreadId) :
    ((st.runDescheduleOnCore c t).getTcb? u).map TCB.ipcState = (st.getTcb? u).map TCB.ipcState :=
  TCB.map_proj_eq_of_map_withoutRunLinks_eq _
    ((runDescheduleOnCore_objectsAgreeOffRunLinks st c t).getTcb? u)

/-- Taking core `c`'s current thread off `c` empties `c`'s slot alone. -/
theorem runDescheduleOnCore_currentOnCore_of_current (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (hCur : st.scheduler.currentOnCore c = some t) (c' : CoreId) :
    (st.runDescheduleOnCore c t).scheduler.currentOnCore c' =
      if c' = c then none else st.scheduler.currentOnCore c' := by
  unfold runDescheduleOnCore; dsimp only
  simp only [SchedulerState.markReschedulePendingOnCoreIf_currentOnCore]
  by_cases hc : c' = c
  · subst hc
    rw [SchedulerState.setCurrentOnCore_currentOnCore_self, if_pos hCur, if_pos rfl]
  · rw [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc), if_neg hc]
    simp only [SchedulerState.currentOnCore, runRemoveOnCore_current]

/-- ...so afterwards no core runs `t`, which ran on `c` alone. -/
theorem runDescheduleOnCore_currentNowhere {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    {e : Option SchedPoint} (hD : st.currentDequeuedUniqueExcept e)
    (hCur : st.scheduler.currentOnCore c = some t) :
    (st.runDescheduleOnCore c t).currentNowhere t := fun c' h => by
  rw [runDescheduleOnCore_currentOnCore_of_current st c t hCur] at h
  split at h
  · cases h
  · rename_i hc; exact hc ((hD.current c t hCur).2.1 c' h)

/-- **The dispatch that closes a block**: taking core `c`'s current thread off
`c` empties `c`'s slot, leaves every other slot alone and queues no one. -/
theorem RunQueueDispatchStage.descheduleCurrent (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (hCur : st.scheduler.currentOnCore c = some t) :
    RunQueueDispatchStage c st (st.runDescheduleOnCore c t) :=
  have hM := StateMono.of_agreeOffRunLinks (runDescheduleOnCore_objectsAgreeOffRunLinks st c t)
  ⟨(RunQueueStage.runDescheduleOnCore st c t).1, fun _ _ he _ _ _ d =>
    currentDequeuedUniqueExcept_of_dispatch (new := none) d he
      (runDescheduleOnCore_currentOnCore_of_current st c t hCur)
      (fun _ h => by cases h) (fun _ h => by cases h)
      (fun c' x hq => by
        rw [runDescheduleOnCore_queuedOn] at hq
        split at hq
        · cases hq
        · exact .inl hq)
      hM, fun _ _ => hM⟩

/-- WS-ZA ZA6.4: the guarded enqueue after a frame stage off `P`. -/
theorem RunQueueFrameStage.then_enqueue {P : SeLe4n.SchedContextId → Prop} {st s : SystemState}
    {c : CoreId} {t : SeLe4n.ThreadId} {p : SeLe4n.Priority} (h1 : RunQueueFrameStage P st s)
    (hNC : ∀ c', s.scheduler.currentOnCore c' ≠ some t) (hRun : st.runnable t)
    (hHome : s.homedOn t c) :
    RunQueueFrameStage P st (s.runEnqueueOnCore c t p) :=
  ⟨h1.1.trans ((RunQueueLinkStage.runEnqueueOnCore s c t p).toFrame P), fun e h r r'' d =>
    let ⟨h', r'⟩ := h1.1.links h r
    (RunQueueStage.runEnqueueOnCore s c t p hNC ((h1.2.2 h r).runnable hRun)
      hHome).2.1 e h' r' r''
      (h1.2.1 e h r r' d),
    fun h r =>
      let ⟨h', r'⟩ := h1.1.links h r
      (h1.2.2 h r).trans
        ((RunQueueStage.runEnqueueOnCore s c t p hNC ((h1.2.2 h r).runnable hRun)
          hHome).2.2 h' r')⟩

/-- WS-ZA ZA6.4: the run-queue writes keep every context and every release
queue (`RefillsKeptOff`, off any set). -/
theorem RefillsKeptOff.runRequeueOnCore (P : SeLe4n.SchedContextId → Prop) (st : SystemState)
    (c : CoreId) (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    RefillsKeptOff P (st.runRequeueOnCore c t p) st :=
  .of_releaseSlots (RefillViewsKept.of_agreeOffRunLinks (runRequeueOnCore_objectsAgreeOffRunLinks st c t p))
    (by rw [runRequeueOnCore_scheduler]; rfl)

theorem RefillsKeptOff.runEnqueueOnCore (P : SeLe4n.SchedContextId → Prop) (st : SystemState)
    (c : CoreId) (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    RefillsKeptOff P (st.runEnqueueOnCore c t p) st :=
  .of_releaseSlots (RefillViewsKept.of_agreeOffRunLinks (runEnqueueOnCore_objectsAgreeOffRunLinks st c t p))
    (by rw [runEnqueueOnCore_scheduler]; split <;> rfl)

theorem RefillsKeptOff.markReschedulePendingOnCore (P : SeLe4n.SchedContextId → Prop)
    (st : SystemState) (c : CoreId) : RefillsKeptOff P (st.markReschedulePendingOnCore c) st :=
  .of_releaseSlots (.refl st) rfl

theorem RefillsKeptOff.updateTcb (P : SeLe4n.SchedContextId → Prop) (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : TCB → TCB) (hInv : st.objects.invExt) :
    RefillsKeptOff P (st.updateTcb tid f) st :=
  .of_releaseSlots (.of_getSchedContext?_eq (updateTcb_getSchedContext? st tid f hInv))
    (by rw [updateTcb_scheduler])

/-- A reschedule flag is not read by the agreement. -/
theorem RunQueueStage.markReschedulePendingOnCore (st : SystemState) (c : CoreId) :
    RunQueueStage st (st.markReschedulePendingOnCore c) :=
  RunQueueStage.of_frame rfl rfl rfl

end SeLe4n.Model.SystemState
