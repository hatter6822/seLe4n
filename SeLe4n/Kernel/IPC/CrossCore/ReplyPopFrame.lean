/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDonatedInPlace

/-!
# The donation pop's frame

seL4-MCS's `reply_pop` and the settle of the context handed back
(`popDonationSettledInPlace`) write only a thread's binding, a reply's stack
links and a context (`popFrame`): every other reading a later leg makes is the
one the pre-state gives (`objectsAgreeOffPop`, `popAgreeAt_*`).  The reply,
the reply-receive and the take arms read these facts.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section ReplyRecvDonationFrame

/-- An object as a receive's checks read it across a donation pop: a thread
off its run-queue links and its binding, a reply off its stack links, a
scheduling context not at all, every other kind as it is.  The pop and the
settle write nothing else. -/
def popFieldsView : KernelObject → KernelObject
  | .tcb t => .tcb { t.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 }
  | .reply r => .reply { r with prev := none, next := none }
  | .schedContext _ => .schedContext default
  | o => o

theorem popFieldsView_withoutRunLinks (o : KernelObject) :
    popFieldsView o.withoutRunLinks = popFieldsView o := by
  cases o <;> rfl

theorem popFieldsView_withoutRelease (o : KernelObject) :
    popFieldsView o.withoutRelease = popFieldsView o := by
  cases o <;> rfl

/-- Two states whose objects agree off what a donation pop writes. -/
def objectsAgreeOffPop (s' s : SystemState) : Prop :=
  ∀ x : SeLe4n.ObjId, (s'.objects[x]?).map popFieldsView = (s.objects[x]?).map popFieldsView

theorem objectsAgreeOffPop.refl (s : SystemState) : objectsAgreeOffPop s s := fun _ => rfl

theorem objectsAgreeOffPop.trans {a b d : SystemState} (h₂ : objectsAgreeOffPop d b)
    (h₁ : objectsAgreeOffPop b a) : objectsAgreeOffPop d a := fun x => (h₂ x).trans (h₁ x)

theorem objectsAgreeOffPop.of_objects_eq {s s' : SystemState} (h : s'.objects = s.objects) :
    objectsAgreeOffPop s' s := fun x => by rw [h]

theorem objectsAgreeOffPop.of_release {s s' : SystemState} (h : s'.objectsAgreeOffReleaseLinks s) :
    objectsAgreeOffPop s' s := fun x => by
  have e := congrArg (Option.map popFieldsView) (h x)
  simpa only [Option.map_map, Function.comp_def, popFieldsView_withoutRelease] using e

theorem popAgreeAt_of_runLinks {s s' : SystemState} {x : SeLe4n.ObjId}
    (h : (s'.objects[x]?).map KernelObject.withoutRunLinks =
      (s.objects[x]?).map KernelObject.withoutRunLinks) :
    (s'.objects[x]?).map popFieldsView = (s.objects[x]?).map popFieldsView := by
  have e := congrArg (Option.map popFieldsView) h
  simpa only [Option.map_map, Function.comp_def, popFieldsView_withoutRunLinks] using e

/-- Off the pop's fields, an endpoint is the endpoint it was. -/
theorem popAgreeAt_endpoint {s s' : SystemState} {x : SeLe4n.ObjId} {e : Endpoint}
    (h : (s'.objects[x]?).map popFieldsView = (s.objects[x]?).map popFieldsView)
    (hx : s.objects[x]? = some (.endpoint e)) : s'.objects[x]? = some (.endpoint e) := by
  rw [hx] at h
  cases e' : s'.objects[x]? with
  | none => rw [e'] at h; cases h
  | some o =>
    rw [e'] at h
    have h' := Option.some.inj h
    cases o <;> simp only [popFieldsView, KernelObject.endpoint.injEq, reduceCtorEq] at h' ⊢
    rw [h']

/-- Off the pop's fields, a thread is a thread that agrees off them. -/
theorem popAgreeAt_tcb {s s' : SystemState} {x : SeLe4n.ObjId} {t : TCB}
    (h : (s'.objects[x]?).map popFieldsView = (s.objects[x]?).map popFieldsView)
    (hx : s.objects[x]? = some (.tcb t)) :
    ∃ t', s'.objects[x]? = some (.tcb t') ∧
      ({ t'.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 } : TCB) =
        { t.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 } := by
  rw [hx] at h
  cases e' : s'.objects[x]? with
  | none => rw [e'] at h; cases h
  | some o =>
    rw [e'] at h
    have h' := Option.some.inj h
    cases o <;> simp only [popFieldsView, KernelObject.tcb.injEq, reduceCtorEq] at h'
    exact ⟨_, rfl, h'⟩

/-- Off the pop's fields, a reply is a reply that agrees off its links. -/
theorem popAgreeAt_reply {s s' : SystemState} {x : SeLe4n.ObjId} {r : Reply}
    (h : (s'.objects[x]?).map popFieldsView = (s.objects[x]?).map popFieldsView)
    (hx : s.objects[x]? = some (.reply r)) :
    ∃ r', s'.objects[x]? = some (.reply r') ∧
      ({ r' with prev := none, next := none } : Reply) = { r with prev := none, next := none } := by
  rw [hx] at h
  cases e' : s'.objects[x]? with
  | none => rw [e'] at h; cases h
  | some o =>
    rw [e'] at h
    have h' := Option.some.inj h
    cases o <;> simp only [popFieldsView, KernelObject.reply.injEq, reduceCtorEq] at h'
    exact ⟨_, rfl, h'⟩

/-- Off the pop's fields, an object keeps its kind. -/
theorem popAgreeAt_type {s s' : SystemState} {x : SeLe4n.ObjId}
    (h : (s'.objects[x]?).map popFieldsView = (s.objects[x]?).map popFieldsView) :
    (s'.objects[x]?).map KernelObject.objectType = (s.objects[x]?).map KernelObject.objectType := by
  have hT : ∀ o, (popFieldsView o).objectType = o.objectType := fun o => by cases o <;> rfl
  have e := congrArg (Option.map KernelObject.objectType) h
  simpa only [Option.map_map, Function.comp_def, hT] using e

theorem getObjectType?_of_popAgree {s s' : SystemState} {x : SeLe4n.ObjId}
    (h : (s'.objects[x]?).map popFieldsView = (s.objects[x]?).map popFieldsView) :
    s'.getObjectType? x = s.getObjectType? x :=
  popAgreeAt_type h

theorem getTcb?_isSome_of_popAgree {s s' : SystemState} {p : SeLe4n.ThreadId}
    (h : (s'.objects[p.toObjId]?).map popFieldsView = (s.objects[p.toObjId]?).map popFieldsView)
    (hp : (s.getTcb? p).isSome = true) : (s'.getTcb? p).isSome = true := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨t', h', _⟩ := popAgreeAt_tcb h ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht)
  exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'⟩

theorem getTcb?_none_of_popAgree {s s' : SystemState} {p : SeLe4n.ThreadId}
    (h : (s'.objects[p.toObjId]?).map popFieldsView = (s.objects[p.toObjId]?).map popFieldsView)
    (hn : s.getTcb? p = none) : s'.getTcb? p = none := by
  cases hs : s'.getTcb? p with
  | none => rfl
  | some t' =>
    obtain ⟨t, h', _⟩ := popAgreeAt_tcb h.symm ((SystemState.getTcb?_eq_some_iff _ _ _).mp hs)
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h'] at hn
    cases hn

theorem stasherTestAt_of_popAgree {s s' : SystemState} {x : SeLe4n.ThreadId}
    (h : (s'.objects[x.toObjId]?).map popFieldsView = (s.objects[x.toObjId]?).map popFieldsView)
    (n : Nat) : stasherTestAt s' x n = stasherTestAt s x n := by
  unfold stasherTestAt
  cases hg : s.getTcb? x with
  | none => rw [getTcb?_none_of_popAgree h hg]
  | some t =>
    obtain ⟨t', h', e1⟩ := popAgreeAt_tcb h ((SystemState.getTcb?_eq_some_iff _ _ _).mp hg)
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h']
    have a := congrArg TCB.ipcStateCode e1
    have b := congrArg TCB.pendingReceiveReplyCode e1
    simp only [TCB.withoutRunLinks] at a b
    simp only [a, b]

end ReplyRecvDonationFrame

section ReplyRecvDonationWrites

/-- A step that keeps the index, the lifecycle and every key's slot, and writes
only what a donation pop writes. -/
def popFrame (s' s : SystemState) : Prop :=
  s'.objectIndexSet = s.objectIndexSet ∧ s'.lifecycle = s.lifecycle ∧ s'.objectsKeepFinds s ∧
    objectsAgreeOffPop s' s

theorem popFrame.refl (s : SystemState) : popFrame s s :=
  ⟨rfl, rfl, SystemState.objectsKeepFinds.refl s, objectsAgreeOffPop.refl s⟩

theorem popFrame.trans {a b d : SystemState} (h₂ : popFrame d b) (h₁ : popFrame b a) :
    popFrame d a :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem popFrame_mapValueAt (s : SystemState) (k : SeLe4n.ObjId) (F : KernelObject → KernelObject)
    (hF : ∀ o, popFieldsView (F o) = popFieldsView o) :
    popFrame { s with objects := s.objects.mapValueAt k F } s := by
  refine ⟨rfl, rfl, fun _ => RHTable.findsInPlace_mapValueAt _ _ _ _, fun x => ?_⟩
  show ((s.objects.mapValueAt k F)[x]?).map popFieldsView = (s.objects[x]?).map popFieldsView
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable.get?_mapValueAt]
  split
  · cases s.objects.get? x with
    | none => rfl
    | some o => simp only [Option.map_some, hF]
  · rfl

theorem popFrame_modifyObject (s : SystemState) (k : SeLe4n.ObjId) (F : KernelObject → KernelObject)
    (hNo : s.objects.noResizeDue) (hF : ∀ o, popFieldsView (F o) = popFieldsView o) :
    popFrame (s.modifyObject k F) s := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
  exact popFrame_mapValueAt s k F hF

theorem popFrame_mapTcbInPlace (s : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (hg : ∀ x : TCB, ({ (g x).withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 } : TCB) =
      { x.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 }) :
    popFrame (s.mapTcbInPlace t g) s := by
  unfold SystemState.mapTcbInPlace
  refine popFrame_mapValueAt s _ _ (fun o => ?_)
  cases o <;> simp only [KernelObject.mapTcb, popFieldsView, hg]

theorem popFrame_updateTcb (s : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (hNo : s.objects.noResizeDue)
    (hg : ∀ x : TCB, ({ (g x).withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 } : TCB) =
      { x.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 }) :
    popFrame (s.updateTcb t g) s := by
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
  exact popFrame_mapTcbInPlace s t g hg

theorem popFrame_updateSchedContext (s : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hNo : s.objects.noResizeDue) :
    popFrame (s.updateSchedContext scId f) s := by
  rw [SystemState.updateSchedContext_eq_impl]
  unfold SystemState.updateSchedContextImpl
  split
  · exact popFrame_modifyObject s _ _ hNo (fun o => by cases o <;> rfl)
  · exact popFrame.refl s

theorem markKeyChangeParts_popFrame (st : SystemState) (tid : SeLe4n.ThreadId) (p0 : SeLe4n.Priority)
    (d0 : SeLe4n.Deadline) (dom0 : SeLe4n.DomainId) :
    popFrame (markKeyChangeParts st tid p0 d0 dom0) st := by
  have hO := markKeyChangeParts_objects st tid p0 d0 dom0
  have hX : ∀ {F : Type} (extract : SystemState → F),
      (∀ (s : SystemState) c, extract (s.markReschedulePendingOnCore c) = extract s) →
      extract (markKeyChangeParts st tid p0 d0 dom0) = extract st := by
    intro F extract h
    unfold markKeyChangeParts
    split
    · dsimp only
      split
      · rfl
      · exact markKeyFlagsOver_extract_frame extract h _ _ _ _ _
    · rfl
  exact ⟨hX SystemState.objectIndexSet (fun _ _ => rfl), hX SystemState.lifecycle (fun _ _ => rfl),
    SystemState.objectsKeepFinds.of_objects_eq hO, objectsAgreeOffPop.of_objects_eq hO⟩

theorem markCandidacyGainFor_popFrame (st : SystemState) (tid : SeLe4n.ThreadId) (e : Bool) :
    popFrame (markCandidacyGainFor st tid e) st := by
  have hO := markCandidacyGainFor_objects st tid e
  exact ⟨markCandidacyGainFor_extract_frame SystemState.objectIndexSet st tid e (fun _ _ => rfl),
    markCandidacyGainFor_extract_frame SystemState.lifecycle st tid e (fun _ _ => rfl),
    SystemState.objectsKeepFinds.of_objects_eq hO, objectsAgreeOffPop.of_objects_eq hO⟩

/-- **The pop writes only what a pop writes**, each in its slot. -/
theorem returnDonatedSchedContextInPlace_popFrame (st : SystemState)
    (holder owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) :
    popFrame (returnDonatedSchedContextInPlace st holder owner scId) st := by
  unfold returnDonatedSchedContextInPlace
  split
  · exact popFrame.refl st
  · split
    · exact popFrame.refl st
    · split
      · exact popFrame.refl st
      · split
        · exact popFrame.refl st
        · split
          · exact popFrame.refl st
          · dsimp only
            refine (markKeyChangeParts_popFrame _ _ _ _ _).trans
              ((markCandidacyGainFor_popFrame _ _ _).trans
              ((markKeyChangeParts_popFrame _ _ _ _ _).trans
              ((markCandidacyGainFor_popFrame _ _ _).trans ?_)))
            split
            · refine (popFrame_updateTcb _ _ _ ?_ ?_).trans
                ((popFrame_updateTcb _ _ _ ?_ ?_).trans
                ((popFrame_modifyObject _ _ _ ?_ ?_).trans
                (popFrame_updateSchedContext _ _ _ hNo)))
              all_goals (repeat (first | exact hNo | apply updateTcb_noResizeDue |
                apply modifyObject_noResizeDue | apply updateSchedContext_noResizeDue |
                (intro o; cases o <;> rfl) | (intro _; rfl)))
            · refine (popFrame_updateTcb _ _ _ ?_ ?_).trans
                ((popFrame_updateTcb _ _ _ ?_ ?_).trans
                ((popFrame_modifyObject _ _ _ ?_ ?_).trans
                ((popFrame_modifyObject _ _ _ ?_ ?_).trans
                (popFrame_updateSchedContext _ _ _ hNo))))
              all_goals (repeat (first | exact hNo | apply updateTcb_noResizeDue |
                apply modifyObject_noResizeDue | apply updateSchedContext_noResizeDue |
                (intro o; cases o <;> rfl) | (intro _; rfl)))

end ReplyRecvDonationWrites

section SettleFrame

theorem releaseLinkIn_keepsFinds (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) : (st.releaseLinkIn c s t).objectsKeepFinds st := by
  unfold SystemState.releaseLinkIn
  dsimp only
  split
  · exact fun _ => RHTable.findsInPlace_mapValueAt _ _ _ _
  · exact fun _ => (RHTable.findsInPlace_mapValueAt _ _ _ _).trans
      (RHTable.findsInPlace_mapValueAt _ _ _ _)

theorem releaseInsertOn_keepsFinds (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) : (st.releaseInsertOn c s t).objectsKeepFinds st := by
  unfold SystemState.releaseInsertOn
  split
  · exact .refl _
  · exact releaseLinkIn_keepsFinds st c s t

/-- The settle keeps every key's slot. -/
theorem settleReturnedContext_keepsFinds (st : SystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) :
    (SchedContextOps.settleReturnedContext st c s).objectsKeepFinds st := by
  have hP : (SchedContextOps.purgeReplenishment st s).objectsKeepFinds st := by
    unfold SchedContextOps.purgeReplenishment SystemState.releaseRemoveAnywhere
    split
    · exact releaseRemoveOn_keepsFinds _ _ _
    · exact .refl _
  unfold SchedContextOps.settleReturnedContext
  dsimp only
  split
  · unfold SystemState.releasePlace
    split
    · split
      · exact ((releaseInsertOn_keepsFinds _ _ _ _).trans (releaseRemoveOn_keepsFinds _ _ _)).trans hP
      · exact (releaseRemoveOn_keepsFinds _ _ _).trans hP
    · exact hP
  · exact hP

/-- **The settle writes only release fields**, each in its slot. -/
theorem settleReturnedContext_popFrame (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    popFrame (SchedContextOps.settleReturnedContext st c s) st := by
  have hW := (SchedContextOps.settleReturnedContext_releaseOnlyWrite st c s).1
  exact ⟨by rw [hW], by rw [hW],
    settleReturnedContext_keepsFinds st c s,
    objectsAgreeOffPop.of_release (SchedContextOps.settleReturnedContext_agree st c s)⟩

end SettleFrame

section DonationPopExact

/-- An object other than a scheduling context is the same object across a
write that agrees off the release links. -/
theorem releaseAgreeAt_of_not_sc {s s' : SystemState} (h : s'.objectsAgreeOffReleaseLinks s)
    {x : SeLe4n.ObjId} {o : KernelObject} (hx : s.objects[x]? = some o)
    (hNot : ∀ sc, o ≠ .schedContext sc) : s'.objects[x]? = some o := by
  have e := h x
  rw [hx] at e
  cases e' : s'.objects[x]? with
  | none => rw [e'] at e; cases e
  | some o' =>
    rw [e'] at e
    have e2 := Option.some.inj e
    cases o with
    | schedContext sc => exact absurd rfl (hNot sc)
    | _ => cases o' <;> simp_all [KernelObject.withoutRelease]

/-- The pop's writes in order, on any state: the context, the popped head's
links, the frame below re-headed, the owner's binding and the holder's cleared.
The holder ends unbound and the popped head off its links. -/
theorem popWrites_exact (S : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hr : SeLe4n.ReplyId) (rprev : Option SeLe4n.ReplyId)
    (rnext : Option ReplyStackLink) (owner holder : SeLe4n.ThreadId) (gO : TCB → TCB)
    (r : Reply) (ht : TCB) (hNo : S.objects.noResizeDue)
    (hSR : hr.toObjId ≠ scId.toObjId) (hb : ∀ b, rprev = some b → b ≠ hr)
    (hOR : owner.toObjId ≠ hr.toObjId) (hHR : holder.toObjId ≠ hr.toObjId)
    (hgO : ∀ x : TCB, ({ (gO x).withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 } : TCB) =
      { x.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 })
    (hRo : S.objects[hr.toObjId]? = some (.reply r))
    (hHo : S.objects[holder.toObjId]? = some (.tcb ht)) :
    (∃ t, (((match rprev with
        | none => (S.updateSchedContext scId f).modifyObject hr.toObjId
            (SystemState.mapReplyObject fun x => { x with prev := none, next := none })
        | some b => ((S.updateSchedContext scId f).modifyObject hr.toObjId
            (SystemState.mapReplyObject fun x => { x with prev := none, next := none })).modifyObject
              b.toObjId (SystemState.mapReplyObject fun x => { x with next := rnext })).updateTcb
          owner gO).updateTcb holder
          (fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 })).objects[holder.toObjId]? =
        some (.tcb t) ∧ t.scBindingScCode = 0) ∧
      (((match rprev with
        | none => (S.updateSchedContext scId f).modifyObject hr.toObjId
            (SystemState.mapReplyObject fun x => { x with prev := none, next := none })
        | some b => ((S.updateSchedContext scId f).modifyObject hr.toObjId
            (SystemState.mapReplyObject fun x => { x with prev := none, next := none })).modifyObject
              b.toObjId (SystemState.mapReplyObject fun x => { x with next := rnext })).updateTcb
          owner gO).updateTcb holder
          (fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 })).objects[hr.toObjId]? =
        some (.reply { r with prev := none, next := none }) := by
  have h1 := updateSchedContext_noResizeDue S scId f hNo
  have hF1 := popFrame_updateSchedContext S scId f hNo
  have hS1R : (S.updateSchedContext scId f).objects[hr.toObjId]? = S.objects[hr.toObjId]? := by
    rw [SystemState.updateSchedContext_eq_impl]
    unfold SystemState.updateSchedContextImpl
    split
    · exact objects_modifyObject_ne _ _ _ hNo _ hSR
    · rfl
  generalize S.updateSchedContext scId f = s1 at h1 hF1 hS1R
  have hRp : ∀ (g : Reply → Reply), (∀ r, ({ g r with prev := none, next := none } : Reply) =
      { r with prev := none, next := none }) →
      ∀ o, popFieldsView (SystemState.mapReplyObject g o) = popFieldsView o := by
    intro g hg o; cases o <;> simp only [SystemState.mapReplyObject, popFieldsView, hg]
  have h2 := modifyObject_noResizeDue s1 hr.toObjId
    (SystemState.mapReplyObject fun x => { x with prev := none, next := none }) h1
  have hF2 := (popFrame_modifyObject s1 hr.toObjId _ h1
    (hRp (fun x => { x with prev := none, next := none }) (fun _ => rfl))).trans hF1
  have hS2R : (s1.modifyObject hr.toObjId
      (SystemState.mapReplyObject fun x => { x with prev := none, next := none })).objects[hr.toObjId]? =
      some (.reply { r with prev := none, next := none }) := by
    rw [objects_modifyObject_self _ _ _ h1, hS1R, hRo]; rfl
  generalize s1.modifyObject hr.toObjId
    (SystemState.mapReplyObject fun x => { x with prev := none, next := none }) = s2 at h2 hF2 hS2R
  obtain ⟨s3, h3, hF3, hS3R, hE3⟩ : ∃ s3 : SystemState, s3.objects.noResizeDue ∧ popFrame s3 S ∧
      s3.objects[hr.toObjId]? = some (.reply { r with prev := none, next := none }) ∧
      (match (generalizing := false) rprev with
        | none => s2
        | some b => s2.modifyObject b.toObjId
            (SystemState.mapReplyObject fun x => { x with next := rnext })) = s3 := by
    cases hp : rprev with
    | none => exact ⟨s2, h2, hF2, hS2R, rfl⟩
    | some b =>
      refine ⟨_, modifyObject_noResizeDue _ _ _ h2,
        (popFrame_modifyObject _ _ _ h2
          (hRp (fun x => { x with next := rnext }) (fun _ => rfl))).trans hF2, ?_, rfl⟩
      rw [objects_modifyObject_ne _ _ _ h2 _
        (fun e => hb b hp (SeLe4n.ReplyId.toObjId_injective _ _ e).symm), hS2R]
  rw [hE3]
  have h4 := updateTcb_noResizeDue s3 owner gO h3
  have hF4 := (popFrame_updateTcb s3 owner gO h3 hgO).trans hF3
  have hS4R := (objects_updateTcb_ne s3 owner gO h3 _ (fun e => hOR e.symm)).trans hS3R
  generalize s3.updateTcb owner gO = s4 at h4 hF4 hS4R
  obtain ⟨x, hx, _⟩ := popAgreeAt_tcb (hF4.2.2.2 holder.toObjId) hHo
  refine ⟨⟨{ x with scBindingScCode := 0, scBindingOwnerCode := 0 }, ?_, rfl⟩, ?_⟩
  · rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ h4, SystemState.objects_mapTcbInPlace,
      if_pos (beq_self_eq_true _), hx]
    rfl
  · rw [objects_updateTcb_ne _ _ _ h4 _ (fun e => hHR e.symm)]
    exact hS4R

/-- **The pop's two exact writes the receive reads**: the holder unbound and the
popped head off its links. -/
theorem returnDonatedSchedContextInPlace_exact (S : SystemState) (holder owner : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (hr : SeLe4n.ReplyId) (r : Reply)
    (ot ht : TCB) (hNo : S.objects.noResizeDue)
    (hSc : S.getSchedContext? scId = some sc) (hH : sc.scReply = some hr)
    (hR : S.getReply? hr = some r) (hO : S.getTcb? owner = some ot)
    (hHt : S.getTcb? holder = some ht) (hb : ∀ b, r.prev = some b → b ≠ hr) :
    (∃ t, (returnDonatedSchedContextInPlace S holder owner scId).objects[holder.toObjId]? =
        some (.tcb t) ∧ t.scBindingScCode = 0) ∧
      (returnDonatedSchedContextInPlace S holder owner scId).objects[hr.toObjId]? =
        some (.reply { r with prev := none, next := none }) := by
  have hRo := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hOo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hO
  have hHo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hHt
  have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hOR : owner.toObjId ≠ hr.toObjId := fun e => by rw [e, hRo] at hOo; cases hOo
  have hHR : holder.toObjId ≠ hr.toObjId := fun e => by rw [e, hRo] at hHo; cases hHo
  have hSR : hr.toObjId ≠ scId.toObjId := fun e => by rw [e, hScO] at hRo; cases hRo
  unfold returnDonatedSchedContextInPlace
  simp only [hSc, hH, hR, hO, hHt]
  rw [markKeyChangeParts_objects, markCandidacyGainFor_objects, markKeyChangeParts_objects,
    markCandidacyGainFor_objects]
  refine popWrites_exact S scId _ hr r.prev r.next owner holder _ r ht hNo hSR hb hOR hHR
    ?_ hRo hHo
  intro _; rfl

end DonationPopExact

section DonatedReplyRecvGuard

/-- The thread view the pop leaves a receiver's enqueue checks reading. -/
theorem enqueueAdmits_popView (t : TCB) :
    enqueueAdmits ({ t.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 } : TCB) =
      enqueueAdmits t := rfl

end DonatedReplyRecvGuard


section DonatedReplyRecvDelivered

theorem descheduleAtPlacement_noResizeDue (s : SystemState) (t : SeLe4n.ThreadId)
    (hNo : s.objects.noResizeDue) : (descheduleAtPlacement s t).objects.noResizeDue := by
  unfold descheduleAtPlacement descheduleAt
  split
  · exact removeRunnableOnCore_noResizeDue _ _ _ hNo
  · exact hNo

theorem descheduleAtPlacement_ipcStateCarried (s : SystemState) (t : SeLe4n.ThreadId) :
    ipcStateCarried s (descheduleAtPlacement s t) := by
  unfold descheduleAtPlacement descheduleAt
  split
  · exact ipcStateCarried_of_agree (removeRunnableOnCore_objectsAgreeOffRunLinks _ _ _)
  · exact fun _ x hx => ⟨x, hx, rfl⟩

end DonatedReplyRecvDelivered

end SeLe4n.Kernel
