/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDonatedInPlace

/-!
# A donated reply-receive, each object written in its slot

seL4-MCS's `seL4_ReplyRecv` on a reply whose frame heads the stack of the
context the server holds on loan: the reply leg, `reply_pop` and the settle of
the context handed back (`popDonationSettledInPlace`), then the receive leg
blocking the now-passive server on its endpoint and taking it off its core.
The receive's checks are read on the pre-state and carried across the reply leg
and the pop: the pop and the settle write only a thread's binding, a reply's
stack links and a context (`popFrame`), so every other reading the receive makes
is the one the pre-state gives (`popDonationSettled_receiveGuard`).  The result
is proven equal to the specification's (`replyRecvOnCore_donated_delivered`).
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

theorem notVSpaceRootAt_of_popAgree {s s' : SystemState} {x : SeLe4n.ObjId}
    (h : (s'.objects[x]?).map popFieldsView = (s.objects[x]?).map popFieldsView) :
    notVSpaceRootAt s' x = notVSpaceRootAt s x := by
  rw [notVSpaceRootAt_eq_type, notVSpaceRootAt_eq_type]
  unfold SystemState.getObjectType?
  rw [popAgreeAt_type h]

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

theorem releaseUnlinkOn_keepsFinds (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    (st.releaseUnlinkOn c s).objectsKeepFinds st := by
  unfold SystemState.releaseUnlinkOn
  split
  · dsimp only
    split
    · exact fun _ => RHTable.findsInPlace_mapValueAt _ _ _ _
    · exact fun _ => (RHTable.findsInPlace_mapValueAt _ _ _ _).trans
        (RHTable.findsInPlace_mapValueAt _ _ _ _)
  · exact .refl _

theorem releaseLinkIn_keepsFinds (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) : (st.releaseLinkIn c s t).objectsKeepFinds st := by
  unfold SystemState.releaseLinkIn
  dsimp only
  split
  · exact fun _ => RHTable.findsInPlace_mapValueAt _ _ _ _
  · exact fun _ => (RHTable.findsInPlace_mapValueAt _ _ _ _).trans
      (RHTable.findsInPlace_mapValueAt _ _ _ _)

theorem releaseRemoveOn_keepsFinds (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    (st.releaseRemoveOn c s).objectsKeepFinds st :=
  releaseUnlinkOn_keepsFinds st c s

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

/-- **A donated reply-receive that may block in place**, read on the
pre-state: the caller blocked on a reply from the receiver through reply object
`rid`, the pop's checks (`replyPopsInPlace`), no sender waiting on the
endpoint, the receiver an unreserved thread that may block there in place once
the pop unbinds it, and its reply object not stashed and in its slot for the
stasher record.  Every read is a code. -/
@[inline] def replyRecvDonatedBlocks (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ (some server) => server.val == tid.val
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1 &&
       replyPopsInPlace st c ct.scBindingScCode tid rid
   | none => false) &&
  !tid.isReserved &&
  (match st.getEndpoint? epId with
   | some ep =>
       ep.sendQ.head.isNone &&
       (match st.getTcb? tid with
        | some rt => enqueueAdmits rt && enqueuesInPlaceCode st epId tid ep.recvTailCode
        | none => false)
   | none => false) &&
  (match st.getReply? rid with
   | some rp => !st.replyStashedAt rid rp && replyRecordsInPlace st (rid.val + 1)
   | none => false)

theorem replyRecvDonatedBlocks_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvDonatedBlocks st epId tid c rid = true) :
    ∃ (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply),
      st.objects[c.toObjId]? = some (.tcb ct) ∧
      ct.ipcState = .blockedOnReply ep0 (some tid) ∧ ct.replyObject = some rid ∧
      replyPopsInPlace st c ct.scBindingScCode tid rid = true ∧ tid.isReserved = false ∧
      st.objects[epId]? = some (.endpoint ep) ∧ ep.sendQ.head = none ∧
      st.objects[tid.toObjId]? = some (.tcb rt) ∧ enqueueAdmits rt = true ∧
      enqueuesInPlace st epId tid ep.receiveQ.tail = true ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧
      st.replyStashedAt rid rp = false ∧ replyRecordsInPlace st (rid.val + 1) = true := by
  unfold replyRecvDonatedBlocks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hC, hSRes⟩, hE⟩, hRp⟩ := h
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at hC; cases hC
  | some ct =>
  rw [hTc] at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hIpc, hRO⟩, hW⟩ := hC
  obtain ⟨ep0, hIpc'⟩ : ∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid) := by
    revert hIpc
    split
    · next ep0 server hS =>
      intro e
      have : server = tid := by
        cases server; cases tid; simp only [beq_iff_eq] at e; subst e; rfl
      subst this
      exact ⟨ep0, hS⟩
    · intro e; cases e
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at hE; cases hE
  | some ep =>
  rw [hEp] at hE
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hE
  obtain ⟨hS, hT⟩ := hE
  cases hTt : st.getTcb? tid with
  | none => rw [hTt] at hT; cases hT
  | some rt =>
  rw [hTt] at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨hA, hEnq⟩ := hT
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRp; cases hRp
  | some rp =>
  rw [hR] at hRp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hRp
  obtain ⟨hStash, hRecR⟩ := hRp
  refine ⟨ct, ep0, rt, ep, rp, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hW,
    hSRes, (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp, hS,
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hTt, hA, ?_,
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR, hStash, hRecR⟩
  · simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
  · rw [enqueuesInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode] at hEnq; exact hEnq

section DonatedReplyRecvGuard

/-- The thread view the pop leaves a receiver's enqueue checks reading. -/
theorem enqueueAdmits_popView (t : TCB) :
    enqueueAdmits ({ t.withoutRunLinks with scBindingScCode := 0, scBindingOwnerCode := 0 } : TCB) =
      enqueueAdmits t := rfl

/-- **The donation pop carries the receive's guard**: on the state a donated
reply leg and its pop leave, the endpoint is as it was, the server (unbound by
the pop) may block on it and its block writes in place, each read on the
pre-state. -/
theorem popDonationSettled_receiveGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (rt : TCB) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (home : CoreId)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) (hNext : rp.next = some (.head scId))
    (hScO : st.objects[scId.toObjId]? = some (.schedContext sc)) (hHead : sc.scReply = some rid)
    (hBelow : ∀ b, rp.prev = some b → b ≠ rid)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId home).objects[epId]? =
        some (.endpoint ep) ∧
      (∃ rt1, (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId
          home).objects[tid.toObjId]? = some (.tcb rt1) ∧ receiveBlockAdmits rt1 = true) ∧
      receiveBlocksInPlace (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid
        scId home) epId tid ep.receiveQ.tail (some rid) = true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hR; cases hR
  have hSc' : scId.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hScO; cases hScO
  have hSr : scId.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hScO; cases hScO
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]
  generalize hS1 : storeReplyRendezvousReady st c tid rid = S1
  have hAg := fun x hx hy => hS1 ▸ storeReplyRendezvousReady_agree st c tid rid ct hNo hTc hFC x hx hy
  have hNo1 : S1.objects.noResizeDue := hS1 ▸ storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  obtain ⟨hI, hL⟩ := storeReplyRendezvousReady_fields st c tid rid hNo
  rw [hS1] at hI hL
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyRendezvousReady_keepsFinds st c tid rid hNo hFC
  obtain ⟨tc1, htc1, hc1⟩ := hS1 ▸ storeReplyRendezvousReady_caller st c tid rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyRendezvousReady_reply st c tid rid ct rp hNo hTc hFC hRp hRc
  generalize hTdef : S1.mapTcbInPlace c (holdMessage msg) = T
  have hNoT : T.objects.noResizeDue := by rw [← hTdef]; exact hNo1
  have hHold : ∀ x, x ≠ c.toObjId → T.objects[x]? = S1.objects[x]? := fun x hx => by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  have hTC : T.objects[c.toObjId]? = some (.tcb (holdMessage msg tc1)) := by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
  have hView : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (T.objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks := fun x hx hy => by
    rw [hHold _ hx]; exact hAg x hx hy
  have hTR : T.objects[rid.toObjId]? = some (.reply rp.consumed) := by rw [hHold _ hRc]; exact hR1
  have hKT : T.objectsKeepFinds st := by
    rw [← hTdef]; exact (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
  have hIT : T.objectIndexSet = st.objectIndexSet := by rw [← hTdef]; exact hI
  have hLT : T.lifecycle = st.lifecycle := by rw [← hTdef]; exact hL
  -- the pop's reads on `T`
  have hScT : T.getSchedContext? scId = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hSc' hSr) (fun _ e => by cases e) hScO)
  obtain ⟨rtT, hRtT, _⟩ := agreeAt_tcb (hView _ hTc' hTr) hR
  have hHeadC : rp.consumed = { rp with callerCode := 0 } := Reply.consumed_of_head rp scId hNext
  obtain ⟨⟨t, hPt, hB0⟩, hPr⟩ := returnDonatedSchedContextInPlace_exact T tid c scId sc rid rp.consumed
    (holdMessage msg tc1) rtT hNoT hScT hHead ((SystemState.getReply?_eq_some_iff _ _ _).mpr hTR)
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC) ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRtT)
    (fun b hb => hBelow b (by rw [hHeadC] at hb; exact hb))
  have hFr := returnDonatedSchedContextInPlace_popFrame T tid c scId hNoT
  unfold popDonationSettledInPlace
  generalize returnDonatedSchedContextInPlace T tid c scId = Rr at hPt hPr hFr
  have hAgS := SchedContextOps.settleReturnedContext_agree Rr home scId
  have hF := (settleReturnedContext_popFrame Rr home scId).trans hFr
  generalize SchedContextOps.settleReturnedContext Rr home scId = P at hAgS hF
  have hPt' : P.objects[tid.toObjId]? = some (.tcb t) :=
    releaseAgreeAt_of_not_sc hAgS hPt (fun _ e => by cases e)
  have hPr' : P.objects[rid.toObjId]? =
      some (.reply { rp.consumed with prev := none, next := none }) :=
    releaseAgreeAt_of_not_sc hAgS hPr (fun _ e => by cases e)
  have hComb : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (P.objects[x]?).map popFieldsView = (st.objects[x]?).map popFieldsView :=
    fun x hx hy => (hF.2.2.2 x).trans (popAgreeAt_of_runLinks (hView x hx hy))
  obtain ⟨tcP, hPC, ecP⟩ := popAgreeAt_tcb (hF.2.2.2 c.toObjId) hTC
  refine ⟨popAgreeAt_endpoint (hComb _ hEc hEr) hE, ⟨t, hPt', ?_⟩, ?_⟩
  · obtain ⟨t', h', e'⟩ := popAgreeAt_tcb (hComb _ hTc' hTr) hR
    rw [hPt'] at h'
    cases h'
    unfold receiveBlockAdmits
    rw [← enqueueAdmits_popView t, e', enqueueAdmits_popView, hA]
    have hU : t.schedContextBinding = .unbound := by
      unfold TCB.schedContextBinding SchedContextBinding.ofCodes; rw [hB0]
    rw [hU]
    rfl
  · unfold receiveBlocksInPlace
    have hIP : P.objectIndexSet = st.objectIndexSet := hF.1.trans hIT
    have hLP : P.lifecycle = st.lifecycle := hF.2.1.trans hLT
    have hKP : P.objectsKeepFinds st := hF.2.2.1.trans hKT
    have hV : ∀ x, notVSpaceRootAt st x = true → notVSpaceRootAt P x = true := by
      intro x hx
      by_cases hxc : x = c.toObjId
      · subst hxc; unfold notVSpaceRootAt; rw [SystemState.getObject?_eq_getElem, hPC]
      · by_cases hxr : x = rid.toObjId
        · subst hxr; unfold notVSpaceRootAt; rw [SystemState.getObject?_eq_getElem, hPr']
        · rw [notVSpaceRootAt_of_popAgree (hComb x hxc hxr)]; exact hx
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨enqueuesInPlace_of_frame _ _ _ hIP hLP hKP hV ?_ hEnq, ?_⟩, ?_⟩
    · intro p hp
      by_cases hpc : p.toObjId = c.toObjId
      · exact Option.isSome_iff_exists.mpr
          ⟨tcP, (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hpc ▸ hPC)⟩
      · by_cases hpr : p.toObjId = rid.toObjId
        · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
          have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hx
          rw [hpr, hRp] at this; cases this
        · exact getTcb?_isSome_of_popAgree (hComb _ hpc hpr) hp
    · have hFree : ({ rp.consumed with prev := none, next := none } : Reply).isFree = true := by
        have h := Reply.consumed_caller rp
        simp only [Reply.caller] at h
        simp only [Reply.isFree, Reply.caller, h, Option.isNone_none, Bool.and_self]
      have hSt : P.replyStashedAt rid { rp.consumed with prev := none, next := none } = false := by
        rw [replyStashedAt_eq_stasherTestAt]
        rw [replyStashedAt_eq_stasherTestAt] at hStash
        show (match rp.consumed.stasherCode with
          | 0 => false
          | k + 1 => stasherTestAt P (⟨k⟩ : SeLe4n.ThreadId) (rid.val + 1)) = false
        rw [Reply.consumed_stasherCode]
        revert hStash
        cases rp.stasherCode with
        | zero => intro _; rfl
        | succ k =>
          intro hStash
          dsimp only at hStash ⊢
          by_cases hkc : (⟨k⟩ : SeLe4n.ThreadId).toObjId = c.toObjId
          · unfold stasherTestAt SystemState.getTcb?
            rw [hkc, hPC]
            have e := congrArg TCB.ipcStateCode ecP
            simp only [TCB.withoutRunLinks] at e
            simp only [e]
            show ((holdMessage msg tc1).ipcStateCode == 1 && _) = false
            have e2 : (holdMessage msg tc1).ipcStateCode = tc1.ipcStateCode := rfl
            simp only [e2, hc1, receiverReady, TCB.setIpcState_ipcStateCode]
            rfl
          · by_cases hkr : (⟨k⟩ : SeLe4n.ThreadId).toObjId = rid.toObjId
            · unfold stasherTestAt SystemState.getTcb?; rw [hkr, hPr']
            · rw [stasherTestAt_of_popAgree (hComb _ hkc hkr)]; exact hStash
      simp only [SystemState.replyStashValid]
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hPr']
      simp only [hSt, hFree]
      rfl
    · show replyRecordsInPlace _ (rid.val + 1) = true
      simp only [replyRecordsInPlace, Bool.and_eq_true] at hRec ⊢
      exact ⟨(hKP _).trans hRec.1, storeLeavesIndexAndTypes_of_frame hIP hLP hV hRec.2⟩

end DonatedReplyRecvGuard

section DonatedReplyRecv

/-- **The donated reply-receive that blocks, in place**: under the pop's guard
(`replyPopsInPlace`) with the receiver the server the caller recorded, no sender
waiting and the receive's block admissible once the pop unbinds the server, each
read on the pre-state and carried across the reply leg and the pop
(`popDonationSettled_receiveGuard`), the specification's reply-receive is the
reply's writes, the pop and its settle, the receive's block, the server taken
off its core, its priority walk and the caller's staged message. -/
theorem replyRecvOnCore_donated_inPlace (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (root : SeLe4n.ObjId) (slot : SeLe4n.Slot) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    endpointReplyRecvOnCore epId tid rid c msg root slot core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (descheduleAtPlacement (removeRunnableOnCore (storeReceiveBlock
            (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid
              ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c)) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid) tid core).1 c 0) ∧
      ∃ x, (removeRunnableOnCore (storeReceiveBlock
            (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid
              ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c)) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core).getTcb? tid = some x ∧
        x.ipcState = .blockedOnReceive epId := by
  obtain ⟨rp', scId, sc, hRp', hN, hScO, hHead, hBelow, hCode, hCRes, hNe, hNo, hLC, hFC, hLR, hFR,
    _, hPop⟩ := replyPopsInPlace_donation st c tid rid msg ct hT hSRes hG
  rw [hRp] at hRp'
  cases hRp'
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st tid c tid ct ep0 rid rp msg core hSz hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := popDonationSettled_receiveGuard st c tid rid msg ct rp
    epId ep rt scId sc (determineTargetCore st c) hNo hT hFC hRp hN hScO hHead hBelow
    (fun e => hNe e.symm) hE hR hA hEnq hStash hRec
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRecS : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  rw [← storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hPop
  generalize hS1 : storeReplyRendezvous st c tid rid msg = S1 at hEq hPop hE1 hR1 hG1
  generalize hP : popDonationSettledInPlace S1 c tid scId (determineTargetCore st c) = P
    at hPop hE1 hR1 hG1
  have hEp1 : P.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE1
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) root slot core P =
      (removeRunnableOnCore (storeReceiveBlock P epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq P epId ep tid rt1 (some rid) core hE1 hS hR1 hA1 hG1]
    have hSnd : (receiveRendezvousSender? P epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [hSnd, ↓reduceIte]
  obtain ⟨tb, hTb, hBk⟩ := receiveBlock_receiver_blocked P epId ep tid rt1 (some rid) core hE1 hR1
    hA1 hG1
  have hDq : rendezvousDequeuedCall (removeRunnableOnCore (storeReceiveBlock P epId tid
      ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid = false := by
    unfold rendezvousDequeuedCall lookupTcb
    simp only [hSRes, Bool.false_eq_true, ↓reduceIte, hTb, hBk]
  refine ⟨?_, tb, hTb, hBk⟩
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_some, hEq, hPop, hRecv, hEp1, Option.bind_some, hS]
  simp [replyRecvPostReceiveDonation, hDq, applyReceiveLegPipHandoff,
    Architecture.stageWokenSendCompletion_none]

end DonatedReplyRecv

section DonatedReplyRecvDelivered

/-- The donated reply-receive that blocks, its caller woken holding no message:
the reply's writes, the pop and its settle, the server's block on the endpoint,
the server taken off its core, then its priority walk. -/
@[noinline] def storeReplyRecvDonatedReady (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (core : CoreId) : SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore
    (descheduleAtPlacement (removeRunnableOnCore (storeReceiveBlock
      (popDonationSettledInPlace (storeReplyRendezvousReady st c tid rid) c tid scId home) epId tid
      tailCode (rid.val + 1)) tid core) tid) tid core).1

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

/-- **The donated reply-receive, delivered**: under the guard of
`replyRecvOnCore_donated_inPlace` and a reply of at most four words, the checked
arm's result is the caller's frame written into its saved registers on top of
`storeReplyRecvDonatedReady`; the server, blocked on the endpoint, stages
nothing. -/
theorem replyRecvOnCore_donated_delivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (root : SeLe4n.ObjId) (slot : SeLe4n.Slot) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters) (hSz4 : msg.registers.size ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    (match endpointReplyRecvOnCore epId tid rid c msg root slot core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.installedCount) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), writeDeliveredFrameIfReady
        (storeReplyRecvDonatedReady st c tid rid ⟨replyHeadContextCode st rid - 1⟩
          (determineTargetCore st c) epId ep.recvTailCode core) c
        (Architecture.returnFrameOfMessage msg 0 0)
        (fun _ => (storeReplyRecvDonatedReady st c tid rid ⟨replyHeadContextCode st rid - 1⟩
          (determineTargetCore st c) epId ep.recvTailCode core).mapTcbInPlace c
          (holdMessage msg))) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hNe', hNo, _⟩ := replyPopsInPlace_donation st c tid rid msg ct hT
    hSRes hG
  have hNe : tid ≠ c := fun e => hNe' e.symm
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvOnCore_donated_inPlace st epId tid c rid msg root slot core
    ct ep0 rt ep rp hSz hT hIpc hRO hSRes hG hE hS hR hA hEnq hRp hStash hRec
  rw [hEq]
  simp only [CapTransferSummary.installedCount_empty]
  revert hX
  generalize (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId
  intro hX
  have h1 := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have h2 := popDonationSettledInPlace_noResizeDue _ c tid scId (determineTargetCore st c) h1
  have h3 := storeReceiveBlock_noResizeDue _ epId tid ep.recvTailCode
    (SeLe4n.ReplyId.optCode (some rid)) h2
  have h4 := removeRunnableOnCore_noResizeDue _ tid core h3
  have h5 := descheduleAtPlacement_noResizeDue _ tid h4
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    popDonationSettledInPlace_msg c id _ id _ c tid scId _ h1 (fun e => hNe e.symm),
    storeReceiveBlock_msg _ _ _ _ _ _ _ h2 hNe, removeRunnableOnCore_msg] at hX ⊢
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hX
  rw [descheduleAtPlacement_msg, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ h5,
    stageDeliveredMessage_holdMessage _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ h5) hSz4]
  obtain ⟨x1, hX1, e1⟩ := descheduleAtPlacement_ipcStateCarried _ tid tid x hX
  obtain ⟨x2, hX2, e2⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h5 tid x1 hX1
  rw [stageDeliveredMessage_writeDeliveredFrameIfReady_blocked _ c tid _ _ 0 hCT x2 hX2
    (by rw [e2, e1, hB]; exact fun h => by cases h)]
  rfl

end DonatedReplyRecvDelivered

/-- **The donated reply-receive that blocks, delivered from the registers**:
`storeReplyRecvDonatedReady`'s writes, then the reply's frame written into the
caller's saved registers.  The message is built only where the caller is,
unexpectedly, not ready. -/
@[noinline] def performReplyRecvDonatedDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId) : SystemState :=
  let X := storeReplyRecvDonatedReady st c tid rid scId home epId tailCode core
  writeDeliveredFrameIfReady X c (Architecture.regReplyRecvFrame layout rf len badge)
    (fun _ => holdReplyRecvBody X c layout rf len badge)

end SeLe4n.Kernel
