/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDonatingInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecv

/-!
# seL4-MCS `receiveIPC`'s context return, each object written in its slot

`seL4_ReplyRecv`'s receive leg returns the bound notification's context
(`maybeReturnSchedContext`, `receiveReturnSchedContext`) before it looks at the
endpoint.  The in-place reply-receive forms run that return between the reply
leg and the receive's block, so they need four facts of it on a state that has
room (`noResizeDue`):

* it leaves room (`receiveReturnSchedContext_noResizeDue`);
* it keeps every key's slot (`receiveReturnSchedContext_keepsFinds`);
* it commutes with a message written into another thread's slots
  (`receiveReturnSchedContext_msg`), so the reply's held message can be pulled
  out past it;
* it keeps everything the receive's block guard reads
  (`receiveReturnSchedContext_receiveGuard`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section ReleaseRemoveMoves
variable (r : SeLe4n.ThreadId)

theorem releaseCoreOf_mapTcbInPlace (st : SystemState) (g : TCB → TCB) (s : SeLe4n.SchedContextId) :
    (st.mapTcbInPlace r g).releaseCoreOf s = st.releaseCoreOf s := by
  unfold SystemState.releaseCoreOf; rw [SystemState.getSchedContext?_mapTcbInPlace]

theorem releaseRemoveAnywhere_mapTcbInPlace (st : SystemState) (g : TCB → TCB)
    (s : SeLe4n.SchedContextId) :
    (st.mapTcbInPlace r g).releaseRemoveAnywhere s =
      (st.releaseRemoveAnywhere s).mapTcbInPlace r g := by
  unfold SystemState.releaseRemoveAnywhere
  rw [releaseCoreOf_mapTcbInPlace]
  split
  · exact releaseRemoveOn_mapTcbInPlace r g st _ s
  · rfl

end ReleaseRemoveMoves

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

theorem releaseRemoveOn_keepsFinds (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    (st.releaseRemoveOn c s).objectsKeepFinds st :=
  releaseUnlinkOn_keepsFinds st c s

section ReturnInPlace

/-- The purge leaves room. -/
theorem purgeReplenishment_noResizeDue (st : SystemState) (s : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) :
    (SchedContextOps.purgeReplenishment st s).objects.noResizeDue := by
  unfold SchedContextOps.purgeReplenishment SystemState.releaseRemoveAnywhere
  split
  · exact releaseUnlinkOn_noResizeDue _ _ _ hNo
  · exact hNo

/-- The purge keeps every key's slot. -/
theorem purgeReplenishment_keepsFinds (st : SystemState) (s : SeLe4n.SchedContextId) :
    (SchedContextOps.purgeReplenishment st s).objectsKeepFinds st := by
  unfold SchedContextOps.purgeReplenishment SystemState.releaseRemoveAnywhere
  split
  · exact releaseRemoveOn_keepsFinds _ _ _
  · exact .refl _

/-- A context rewritten in its slot keeps every key's slot. -/
theorem updateSchedContext_keepsFinds (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hNo : st.objects.noResizeDue) :
    (st.updateSchedContext scId f).objectsKeepFinds st := by
  rw [SystemState.updateSchedContext_eq_impl]
  unfold SystemState.updateSchedContextImpl
  split
  · rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
    exact fun _ => RHTable.findsInPlace_mapValueAt _ _ _ _
  · exact .refl _

/-- seL4's three writes leave room and keep every key's slot. -/
theorem schedContextReturnLinks_inPlace (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) :
    (schedContextReturnLinks st vS tid).objects.noResizeDue ∧
      (schedContextReturnLinks st vS tid).objectsKeepFinds st := by
  rw [schedContextReturnLinks_eq_impl]
  unfold schedContextReturnLinksImpl
  split
  · exact ⟨hNo, .refl _⟩
  split
  · exact ⟨hNo, .refl _⟩
  dsimp only
  have hNo1 := updateSchedContext_noResizeDue st (SeLe4n.SchedContextId.ofObjId vS.val)
    (fun sc => { sc with boundThreadCode := 0 }) hNo
  have hK := updateSchedContext_keepsFinds st (SeLe4n.SchedContextId.ofObjId vS.val)
    (fun sc => { sc with boundThreadCode := 0 }) hNo
  generalize (st.updateSchedContext (SeLe4n.SchedContextId.ofObjId vS.val)
    fun sc => { sc with boundThreadCode := 0 }) = U at hNo1 hK
  unfold SystemState.objectsKeepFinds at hK ⊢
  rw [markKeyChangeParts_objects, markCandidacyGainFor_objects]
  cases runningCoreOf? st tid <;> dsimp only <;>
    exact ⟨updateTcb_noResizeDue _ _ _ hNo1, fun k => by
      rw [← hK k, SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1]
      exact SystemState.mapTcbInPlace_keepsFinds _ _ _ k⟩

/-- **The return leaves room and keeps every key's slot**: seL4's three
writes and the purge each rewrite a slot in place. -/
theorem schedContextReturnPerform_inPlace (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) :
    (schedContextReturnPerform st vS tid).objects.noResizeDue ∧
      (schedContextReturnPerform st vS tid).objectsKeepFinds st := by
  obtain ⟨h1, h2⟩ := schedContextReturnLinks_inPlace st vS tid hNo
  exact ⟨purgeReplenishment_noResizeDue _ _ h1, (purgeReplenishment_keepsFinds _ _).trans h2⟩

/-- **The receive's return leaves room.** -/
theorem receiveReturnSchedContext_noResizeDue (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) :
    (receiveReturnSchedContext blocks st tid).objects.noResizeDue :=
  receiveReturnSchedContext_induct (fun _ b => b.objects.noResizeDue) blocks st tid hNo
    (fun vS _ _ _ => (schedContextReturnPerform_inPlace st vS tid hNo).1)

/-- **The receive's return keeps every key's slot.** -/
theorem receiveReturnSchedContext_keepsFinds (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) :
    (receiveReturnSchedContext blocks st tid).objectsKeepFinds st :=
  receiveReturnSchedContext_induct (fun a b => b.objectsKeepFinds a) blocks st tid (.refl _)
    (fun vS _ _ _ => (schedContextReturnPerform_inPlace st vS tid hNo).2)

/-- **A receiver holding no context returns nothing**: seL4's return guard asks
that the context be the receiver's own binding (`schedContextReturnAdmitted`),
which a receiver whose binding code is zero does not hold, so the receive's
return is the identity on it. -/
theorem receiveReturnSchedContext_of_scUnbound {blocks : Bool} {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hT : st.objects[tid.toObjId]? = some (.tcb t))
    (h0 : t.scBindingScCode = 0) :
    receiveReturnSchedContext blocks st tid = st := by
  have hT' : st.getTcb? tid = some t := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  exact receiveReturnSchedContext_induct (fun a b => b = a) blocks st tid rfl
    (fun vS vT hV hA => by
      exfalso
      unfold schedContextReturnAdmitted at hA
      rw [hV, hT'] at hA
      split at hA
      · cases hA
      · simp [TCB.schedContextBinding, h0, SchedContextBinding.ofCodes] at hA)

end ReturnInPlace

section ReturnAgree

/-- **One object as the return leaves it**: unchanged, a thread with its two
binding codes cleared, or a context in both. -/
def returnStep (o' o : KernelObject) : Prop :=
  o' = o ∨ (∃ t, o = .tcb t ∧ o' = .tcb { t with scBindingScCode := 0, scBindingOwnerCode := 0 }) ∨
    (∃ sc sc', o = .schedContext sc ∧ o' = .schedContext sc')

theorem returnStep.trans {a b d : KernelObject} (h₂ : returnStep d b) (h₁ : returnStep b a) :
    returnStep d a := by
  rcases h₂ with rfl | ⟨t, rfl, rfl⟩ | ⟨sc, sc', rfl, rfl⟩
  · exact h₁
  · rcases h₁ with h | ⟨t', rfl, h⟩ | ⟨_, _, _, h⟩
    · subst h; exact Or.inr (Or.inl ⟨t, rfl, rfl⟩)
    · cases h; exact Or.inr (Or.inl ⟨t', rfl, rfl⟩)
    · cases h
  · rcases h₁ with h | ⟨_, _, h⟩ | ⟨s0, _, rfl, h⟩
    · subst h; exact Or.inr (Or.inr ⟨sc, sc', rfl, rfl⟩)
    · cases h
    · exact Or.inr (Or.inr ⟨s0, sc', rfl, rfl⟩)

/-- **Two states as the return relates them**, slot by slot. -/
def returnAgree (s' s : SystemState) : Prop :=
  ∀ x : SeLe4n.ObjId, s'.objects[x]? = s.objects[x]? ∨
    ∃ o o', s.objects[x]? = some o ∧ s'.objects[x]? = some o' ∧ returnStep o' o

theorem returnAgree.refl (s : SystemState) : returnAgree s s := fun _ => Or.inl rfl

theorem returnAgree.of_objects_eq {s s' : SystemState} (h : s'.objects = s.objects) :
    returnAgree s' s := fun _ => Or.inl (by rw [h])

theorem returnAgree.trans {a b d : SystemState} (h₂ : returnAgree d b) (h₁ : returnAgree b a) :
    returnAgree d a := by
  intro x
  rcases h₂ x with e2 | ⟨o, o', hb, hd, r2⟩
  · rw [e2]; exact h₁ x
  · rcases h₁ x with e1 | ⟨p, p', ha, hb', r1⟩
    · rw [← e1]; exact Or.inr ⟨o, o', hb, hd, r2⟩
    · rw [hb'] at hb; cases hb
      exact Or.inr ⟨p, o', ha, hd, r2.trans r1⟩

theorem returnAgree_mapValueAt (s : SystemState) (k : SeLe4n.ObjId) (F : KernelObject → KernelObject)
    (hF : ∀ o, returnStep (F o) o) :
    returnAgree { s with objects := s.objects.mapValueAt k F } s := by
  intro x
  show (s.objects.mapValueAt k F)[x]? = s.objects[x]? ∨ _
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable.get?_mapValueAt]
  split
  · cases s.objects.get? x with
    | none => exact Or.inl rfl
    | some o => exact Or.inr ⟨o, F o, rfl, rfl, hF o⟩
  · exact Or.inl rfl

/-- The purge rewrites contexts only. -/
theorem purgeReplenishment_returnAgree (st : SystemState) (s : SeLe4n.SchedContextId) :
    returnAgree (SchedContextOps.purgeReplenishment st s) st := by
  intro x
  rcases (SchedContextOps.purgeReplenishment_agree st s).pointwise x with e | ⟨sc, sc', h0, h1, _⟩
  · exact Or.inl e
  · exact Or.inr ⟨_, _, h0, h1, Or.inr (Or.inr ⟨sc, sc', rfl, rfl⟩)⟩

/-- seL4's three writes relate their state to the pre-state slot by slot. -/
theorem schedContextReturnLinks_returnAgree (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) :
    returnAgree (schedContextReturnLinks st vS tid) st := by
  rw [schedContextReturnLinks_eq_impl]
  unfold schedContextReturnLinksImpl
  split
  · exact .refl _
  split
  · exact .refl _
  dsimp only
  have hNo1 := updateSchedContext_noResizeDue st (SeLe4n.SchedContextId.ofObjId vS.val)
    (fun sc => { sc with boundThreadCode := 0 }) hNo
  have h1 : returnAgree (st.updateSchedContext (SeLe4n.SchedContextId.ofObjId vS.val)
      fun sc => { sc with boundThreadCode := 0 }) st := by
    rw [SystemState.updateSchedContext_eq_impl]
    unfold SystemState.updateSchedContextImpl
    split
    · rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
      exact returnAgree_mapValueAt _ _ _ (fun o => by
        cases o <;> first | exact Or.inl rfl | exact Or.inr (Or.inr ⟨_, _, rfl, rfl⟩))
    · exact .refl _
  generalize (st.updateSchedContext (SeLe4n.SchedContextId.ofObjId vS.val)
    fun sc => { sc with boundThreadCode := 0 }) = U at hNo1 h1
  have h2 : returnAgree (U.updateTcb tid
      fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 }) U := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1]
    exact returnAgree_mapValueAt _ _ _ (fun o => by
      cases o <;> first | exact Or.inl rfl | exact Or.inr (Or.inl ⟨_, rfl, rfl⟩))
  refine (returnAgree.of_objects_eq ?_).trans (h2.trans h1)
  rw [markKeyChangeParts_objects, markCandidacyGainFor_objects]
  cases runningCoreOf? st tid <;> rfl

/-- **The receive's return relates its state to the pre-state slot by slot.** -/
theorem receiveReturnSchedContext_returnAgree (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) :
    returnAgree (receiveReturnSchedContext blocks st tid) st :=
  receiveReturnSchedContext_induct (fun a b => returnAgree b a) blocks st tid (.refl _)
    (fun vS _ _ _ => (purgeReplenishment_returnAgree _ _).trans
      (schedContextReturnLinks_returnAgree st vS tid hNo))

/-- **The receive's return leaves the machine alone.** -/
theorem receiveReturnSchedContext_machine (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (receiveReturnSchedContext blocks st tid).machine = st.machine := by
  refine receiveReturnSchedContext_induct (fun a b => b.machine = a.machine) blocks st tid rfl
    (fun vS _ _ _ => ?_)
  show (schedContextReturnPerform st vS tid).machine = st.machine
  unfold schedContextReturnPerform
  rw [SchedContextOps.purgeReplenishment_machine]
  unfold schedContextReturnLinks
  split
  · rfl
  split
  · rfl
  dsimp only
  rw [markKeyChangeFor_extract_frame SystemState.machine _ _ _ (fun _ _ => rfl),
    markCandidacyGainFor_extract_frame SystemState.machine _ _ _ (fun _ _ => rfl)]
  have hU : ∀ (s : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB),
      (s.updateTcb t f).machine = s.machine := by
    intro s t f; unfold SystemState.updateTcb; split <;> rfl
  cases runningCoreOf? st tid <;> exact hU _ _ _

end ReturnAgree

section ReturnMessageSlots
variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat)

/-- seL4's three writes commute with a message written into another thread. -/
theorem schedContextReturnLinks_msg (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) (hR : r ≠ tid) :
    schedContextReturnLinks (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) vS tid =
      (schedContextReturnLinks st vS tid).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [schedContextReturnLinks_eq_impl]
  unfold schedContextReturnLinksImpl
  rw [SystemState.getSchedContext?_mapTcbInPlace, SystemState.getTcb?_mapTcbInPlace, if_neg hR]
  cases st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) with
  | none => rfl
  | some _ =>
    cases st.getTcb? tid with
    | none => rfl
    | some tcb =>
      dsimp only
      have hRun : runningCoreOf? (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid =
          runningCoreOf? st tid := rfl
      rw [hasSufficientBudget_msg, hRun, updateSchedContext_msg r ρ μ π _ _ _ hNo,
        updateTcb_msg r ρ μ π _ tid _ (updateSchedContext_noResizeDue _ _ _ hNo)
          (fun h => absurd h.symm hR)]
      cases runningCoreOf? st tid with
      | none => dsimp only; rw [markCandidacyGainFor_msg, markKeyChangeParts_msg]
      | some c =>
        dsimp only
        rw [show ∀ (S : SystemState), (S.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).markReschedulePendingOnCore c =
            (S.markReschedulePendingOnCore c).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) from fun _ => rfl,
          markCandidacyGainFor_msg, markKeyChangeParts_msg]

/-- The return commutes with a message written into another thread. -/
theorem schedContextReturnPerform_msg (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) (hR : r ≠ tid) :
    schedContextReturnPerform (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) vS tid =
      (schedContextReturnPerform st vS tid).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold schedContextReturnPerform SchedContextOps.purgeReplenishment
  rw [schedContextReturnLinks_msg r ρ μ π st vS tid hNo hR, releaseRemoveAnywhere_mapTcbInPlace]

/-- seL4's guard reads no other thread's message. -/
theorem schedContextReturnAdmitted_msg (st : SystemState) (vS : SeLe4n.ValidObjId)
    (vT : SeLe4n.ValidThreadId) (hR : r ≠ vT.val) :
    schedContextReturnAdmitted (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) vS vT =
      schedContextReturnAdmitted st vS vT := by
  unfold schedContextReturnAdmitted
  rw [SystemState.getSchedContext?_mapTcbInPlace, SystemState.getTcb?_mapTcbInPlace, if_neg hR]

/-- **The receive's return commutes with a message written into another
thread**: it reads that thread nowhere and writes none of its slots. -/
theorem receiveReturnSchedContext_msg (blocks : Bool) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) (hR : r ≠ tid) :
    receiveReturnSchedContext blocks (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid =
      (receiveReturnSchedContext blocks st tid).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold receiveReturnSchedContext
  cases blocks with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    rw [SystemState.getTcb?_mapTcbInPlace, if_neg hR]
    cases st.getTcb? tid with
    | none => rfl
    | some t =>
      dsimp only
      split
      · rfl
      unfold maybeReturnSchedContextRunning
      rw [SystemState.getNotification?_mapTcbInPlace]
      cases st.getNotification? _ with
      | none => rfl
      | some ntfn =>
        dsimp only
        cases ntfn.schedContext with
        | none => rfl
        | some s =>
          dsimp only
          split
          · rename_i vS vT _ hT
            have hV : vT.val = tid := by
              unfold SeLe4n.ThreadId.toValid? at hT
              split at hT
              · cases hT
              · cases hT; rfl
            rw [schedContextReturnAdmitted_msg r ρ μ π st vS vT (hV ▸ hR)]
            split
            · exact schedContextReturnPerform_msg r ρ μ π st vS tid hNo hR
            · rfl
          · rfl

end ReturnMessageSlots

section ReturnFrame

/-- seL4's three writes, slot by slot, on a state that has room: the receiver's
slot holds the receiver with its binding codes cleared, and every slot but the
returned context's and the receiver's is as it was. -/
theorem schedContextReturnLinks_objects_off (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) (oid : SeLe4n.ObjId)
    (hS0 : vS.val ≠ oid) :
    (schedContextReturnLinks st vS tid).objects[oid]? =
      if tid.toObjId == oid ∧ (st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val)).isSome
        then (st.objects[oid]?).map
          (KernelObject.mapTcb fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 })
        else st.objects[oid]? := by
  have hC : ∀ (S : SystemState), S.objects.noResizeDue →
      (S.updateSchedContext (SeLe4n.SchedContextId.ofObjId vS.val)
        fun sc => { sc with boundThreadCode := 0 }).objects[oid]? = S.objects[oid]? := by
    intro S hS
    rw [SystemState.updateSchedContext_eq_impl]
    unfold SystemState.updateSchedContextImpl
    split
    · rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hS]
      show (S.objects.mapValueAt _ _)[oid]? = _
      simp only [RHTable_getElem?_eq_get?]
      rw [RHTable.get?_mapValueAt, if_neg (by simpa using hS0)]
    · rfl
  rw [schedContextReturnLinks_eq_impl]
  unfold schedContextReturnLinksImpl
  cases hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) with
  | none => simp
  | some sc =>
  dsimp only
  cases hT : st.getTcb? tid with
  | none =>
    dsimp only
    by_cases h : tid.toObjId = oid
    · subst h
      have : ∀ t, st.objects[tid.toObjId]? ≠ some (.tcb t) := fun t e => by
        rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr e] at hT; cases hT
      cases e : st.objects[tid.toObjId]? with
      | none => simp
      | some o =>
        cases o <;> simp [KernelObject.mapTcb]
        exact absurd e (this _)
    · simp [h]
  | some t =>
  dsimp only
  have hNo1 := updateSchedContext_noResizeDue st (SeLe4n.SchedContextId.ofObjId vS.val)
    (fun sc => { sc with boundThreadCode := 0 }) hNo
  rw [markKeyChangeParts_objects, markCandidacyGainFor_objects]
  have hU : (SystemState.updateTcb (st.updateSchedContext (SeLe4n.SchedContextId.ofObjId vS.val)
      fun sc => { sc with boundThreadCode := 0 }) tid
      fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 }).objects[oid]? =
      if tid.toObjId == oid ∧ (some sc).isSome = true
        then (st.objects[oid]?).map
          (KernelObject.mapTcb fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 })
        else st.objects[oid]? := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1, SystemState.objects_mapTcbInPlace,
      hC _ hNo]
    simp
  cases runningCoreOf? st tid <;> exact hU

/-- **Off the receiver and the returned context, the receive's return moves
release links only**: a slot other than the receiver's, holding no context
bound to the receiver, reads as it did up to the contexts' release fields.  The
context seL4's return takes back is bound to the receiver
(`schedContextReturnAdmitted`), so a context bound to another thread is not it. -/
theorem receiveReturnSchedContext_agreeOff (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) (x : SeLe4n.ObjId)
    (hx : x ≠ tid.toObjId)
    (hxS : ∀ sc, st.objects[x]? = some (.schedContext sc) → sc.boundThread ≠ some tid) :
    ((receiveReturnSchedContext blocks st tid).objects[x]?).map KernelObject.withoutRelease =
      (st.objects[x]?).map KernelObject.withoutRelease :=
  receiveReturnSchedContext_induct
    (fun a b => (b.objects[x]?).map KernelObject.withoutRelease =
      (a.objects[x]?).map KernelObject.withoutRelease) blocks st tid rfl
    (fun vS vT hV hA => by
      have hS0 : vS.val ≠ x := by
        intro e
        unfold schedContextReturnAdmitted at hA
        cases hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) with
        | none => rw [hSc] at hA; cases hA
        | some sc =>
          rw [hSc] at hA
          cases hT : st.getTcb? vT.val with
          | none => rw [hT] at hA; cases hA
          | some t =>
            rw [hT] at hA
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hA
            have hO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
            rw [SeLe4n.SchedContextId.toObjId_ofObjId, e] at hO
            exact hxS sc hO (hV ▸ hA.1)
      show ((SchedContextOps.purgeReplenishment (schedContextReturnLinks st vS tid)
        (SeLe4n.SchedContextId.ofObjId vS.val)).objects[x]?).map KernelObject.withoutRelease = _
      rw [SchedContextOps.purgeReplenishment_agree _ _ x,
        schedContextReturnLinks_objects_off st vS tid hNo x hS0]
      have : ¬ (tid.toObjId == x) = true := by simpa using fun e => hx e.symm
      simp [this])

/-- **seL4's return clears the receiver's two binding codes.** -/
theorem schedContextReturnPerform_getTcb?_self (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (t : TCB) (hNo : st.objects.noResizeDue)
    (hS : (st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val)).isSome = true)
    (hT : st.getTcb? tid = some t) :
    (schedContextReturnPerform st vS tid).getTcb? tid =
      some { t with scBindingScCode := 0, scBindingOwnerCode := 0 } := by
  unfold schedContextReturnPerform
  rw [(SchedContextOps.purgeReplenishment_agree _ _).getTcb? tid]
  have hTO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  have hS0 : vS.val ≠ tid.toObjId := by
    intro e
    obtain ⟨sc, hSc⟩ := Option.isSome_iff_exists.mp hS
    have hO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
    rw [SeLe4n.SchedContextId.toObjId_ofObjId, e, hTO] at hO
    cases hO
  apply (SystemState.getTcb?_eq_some_iff _ _ _).mpr
  rw [schedContextReturnLinks_objects_off st vS tid hNo _ hS0, hTO]
  simp [hS, KernelObject.mapTcb]

/-- **Where it fires, the receive's return leaves the receiver holding no
context**: both binding codes cleared, every other word as it was. -/
theorem receiveReturnSchedContext_getTcb?_self_of_fires {st : SystemState}
    {tid : SeLe4n.ThreadId} (hNo : st.objects.noResizeDue)
    (h : receiveReturnFires true st tid = true) :
    ∃ rt, st.getTcb? tid = some rt ∧
      (receiveReturnSchedContext true st tid).getTcb? tid =
        some { rt with scBindingScCode := 0, scBindingOwnerCode := 0 } := by
  unfold receiveReturnFires at h
  cases hT : st.getTcb? tid with
  | none => rw [hT] at h; simp at h
  | some t =>
    rw [hT] at h
    simp only [Bool.true_and, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨h0, hG⟩ := h
    refine ⟨t, rfl, ?_⟩
    unfold receiveReturnSchedContext
    simp only [↓reduceIte, hT, h0]
    unfold signalReturnGuard at hG
    unfold maybeReturnSchedContextRunning
    revert hG
    cases st.getNotification? ⟨t.boundNotificationCode - 1⟩ with
    | none => intro hG; cases hG
    | some ntfn =>
      dsimp only
      cases ntfn.schedContext with
      | none => intro hG; cases hG
      | some s =>
        dsimp only
        cases s.toObjId.toValid? with
        | none => intro hG; cases hG
        | some vS =>
          cases hV : tid.toValid? with
          | none => intro hG; cases hG
          | some vT =>
            intro hA
            dsimp only
            rw [if_pos hA]
            have hSome : (st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val)).isSome =
                true := by
              cases hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) with
              | none => simp [schedContextReturnAdmitted, hSc] at hA
              | some _ => rfl
            exact schedContextReturnPerform_getTcb?_self st vS tid t hNo hSome hT

/-- An object read up to the contexts' release fields: a non-context reads as
it was. -/
theorem withoutRelease_map_eq_of_not_sc {a b : Option KernelObject} {o : KernelObject}
    (h : a.map KernelObject.withoutRelease = b.map KernelObject.withoutRelease)
    (hb : b = some o) (hNot : ∀ sc, o ≠ .schedContext sc) : a = some o := by
  subst hb
  cases a with
  | none => cases h
  | some o' =>
    simp only [Option.map_some, Option.some.injEq] at h
    cases o with
    | schedContext sc => exact absurd rfl (hNot sc)
    | _ => cases o' <;> first | (simp only [KernelObject.withoutRelease] at h; rw [h]) | cases h

/-- ...and a context reads as a context agreeing off its release fields. -/
theorem withoutRelease_map_eq_sc {a b : Option KernelObject} {sc : SchedContext}
    (h : a.map KernelObject.withoutRelease = b.map KernelObject.withoutRelease)
    (hb : b = some (.schedContext sc)) :
    ∃ sc', a = some (.schedContext sc') ∧ sc'.withoutRelease = sc.withoutRelease := by
  subst hb
  cases a with
  | none => cases h
  | some o' =>
    simp only [Option.map_some, Option.some.injEq] at h
    cases o' with
    | schedContext sc' =>
      simp only [KernelObject.withoutRelease] at h
      exact ⟨sc', rfl, KernelObject.schedContext.inj h⟩
    | _ => simp [KernelObject.withoutRelease] at h

end ReturnFrame

end SeLe4n.Kernel
