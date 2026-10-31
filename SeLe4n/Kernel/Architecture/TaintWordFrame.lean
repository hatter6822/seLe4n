-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.Invariant

/-!
# The whole invariant bundle across a taint-word write

WS-ZA ZA5.11.  The taint step writes a thread's or a notification's taint words
and nothing else in the store (`SystemState.objectsAgreeOffTaint`).  This file
carries `Architecture.proofLayerInvariantBundle` across such a write through
**one frame**: the second store is the first with a word write at every key
(`SystemState.objectsAgreeOffTaint.getElem?_eq`), and every accessor a conjunct
reads is blind to the words (one lemma per accessor below).  Each leaf closes
the same way: an object a post-state conjunct reads is taken back to the
pre-state's object with words written (`tcb_back_eq`, `notification_back_eq`,
`some_back_eq`, or `inert_iff` for a kind holding none), whose every field but
the words is the pre-state's by definition, and an object the pre-state
conjunct promises is taken forward the same way (`tcb_fwd_eq`, …).  No leaf is
restated.  A new bundle conjunct owes its transport here.
-/

namespace SeLe4n.Model.KernelObject

/-- An object written back with its own words is itself. -/
@[simp] theorem withTaintWords_taintWords (o : KernelObject) : o.withTaintWords o.taintWords = o := by
  cases o <;> rfl

/-- **Agreement off the words is a word write**: an object agreeing with `o`
off its words is `o` with that object's words written. -/
theorem withTaintWords_of_eraseTaint_eq {o o' : KernelObject}
    (h : o'.eraseTaint = o.eraseTaint) : o.withTaintWords o'.taintWords = o' := by
  have e := congrArg (·.withTaintWords o'.taintWords) h
  simp only [eraseTaint, withTaintWords_withTaintWords, withTaintWords_taintWords] at e
  exact e.symm

end SeLe4n.Model.KernelObject

namespace SeLe4n.Model.SystemState.objectsAgreeOffTaint

variable {st st' : SystemState}

/-- **The frame of a word write**: every object of the second store is the
first's object at that key with the second's words written. -/
theorem getElem?_eq (h : objectsAgreeOffTaint st st') (k : SeLe4n.ObjId) :
    st'.objects[k]? = (st.objects[k]?).map
      (KernelObject.withTaintWords · ((st'.objects[k]?).elim {} KernelObject.taintWords)) := by
  cases h2 : st'.objects[k]? with
  | none =>
    have hk := h k
    rw [h2] at hk
    cases h1 : st.objects[k]? with
    | none => rfl
    | some _ => rw [h1] at hk; cases hk
  | some o' =>
    obtain ⟨o, h1, e⟩ := some_iff h k o' h2
    rw [h1]
    exact congrArg some (KernelObject.withTaintWords_of_eraseTaint_eq e).symm

/-- A reader blind to the words reads alike on both sides. -/
theorem map_blind (h : objectsAgreeOffTaint st st') {β : Type _} (f : KernelObject → β)
    (hf : ∀ o w, f (o.withTaintWords w) = f o) (k : SeLe4n.ObjId) :
    (st'.objects[k]?).map f = (st.objects[k]?).map f := by
  rw [getElem?_eq h k]
  cases st.objects[k]? with
  | none => rfl
  | some o => exact congrArg some (hf o _)

/-- …and so does a partial reader blind to the words. -/
theorem bind_blind (h : objectsAgreeOffTaint st st') {β : Type _} (f : KernelObject → Option β)
    (hf : ∀ o w, f (o.withTaintWords w) = f o) (k : SeLe4n.ObjId) :
    (st'.objects[k]?).bind f = (st.objects[k]?).bind f := by
  rw [getElem?_eq h k]
  cases st.objects[k]? with
  | none => rfl
  | some o => exact hf o _

/-- A key is empty on one side exactly when on the other. -/
theorem none_iff (h : objectsAgreeOffTaint st st') (k : SeLe4n.ObjId) :
    st'.objects[k]? = none ↔ st.objects[k]? = none := by
  rw [getElem?_eq h k]; cases st.objects[k]? <;> simp

/-- A thread of the second state is a thread of the first with its words written. -/
theorem tcb_back_eq (h : objectsAgreeOffTaint st st') {k : SeLe4n.ObjId} {t' : TCB}
    (h2 : st'.objects[k]? = some (.tcb t')) :
    ∃ t w, st.objects[k]? = some (.tcb t) ∧ t' = t.withTaintWords w := by
  obtain ⟨t, h1, e⟩ := tcb_back h h2
  refine ⟨t, t'.taintWords, h1, ?_⟩
  have := KernelObject.withTaintWords_of_eraseTaint_eq (o := .tcb t) (o' := .tcb t')
    (congrArg KernelObject.tcb e)
  exact (KernelObject.tcb.inj this).symm

/-- A thread of the first state is a thread of the second with words written. -/
theorem tcb_fwd_eq (h : objectsAgreeOffTaint st st') {k : SeLe4n.ObjId} {t : TCB}
    (h1 : st.objects[k]? = some (.tcb t)) :
    ∃ w, st'.objects[k]? = some (.tcb (t.withTaintWords w)) := by
  obtain ⟨t', w, h2, rfl⟩ := tcb_back_eq h.symm h1
  exact ⟨t'.taintWords, by rw [h2]; rfl⟩

/-- A notification of the second state is one of the first with its words written. -/
theorem notification_back_eq (h : objectsAgreeOffTaint st st') {k : SeLe4n.ObjId}
    {n' : Notification} (h2 : st'.objects[k]? = some (.notification n')) :
    ∃ n w, st.objects[k]? = some (.notification n) ∧ n' = n.withTaintWords w := by
  obtain ⟨n, h1, e⟩ := notification_back h h2
  refine ⟨n, n'.taintWords, h1, ?_⟩
  have := KernelObject.withTaintWords_of_eraseTaint_eq (o := .notification n)
    (o' := .notification n') (congrArg KernelObject.notification e)
  exact (KernelObject.notification.inj this).symm

/-- A notification of the first state is one of the second with words written. -/
theorem notification_fwd_eq (h : objectsAgreeOffTaint st st') {k : SeLe4n.ObjId}
    {n : Notification} (h1 : st.objects[k]? = some (.notification n)) :
    ∃ w, st'.objects[k]? = some (.notification (n.withTaintWords w)) := by
  obtain ⟨n', w, h2, rfl⟩ := notification_back_eq h.symm h1
  exact ⟨n'.taintWords, by rw [h2]; rfl⟩


/-! ### The accessors -/

/-- A thread read of the second state is one of the first with words written. -/
theorem getTcb?_back (h : objectsAgreeOffTaint st st') {tid : SeLe4n.ThreadId} {t' : TCB}
    (h2 : st'.getTcb? tid = some t') :
    ∃ t w, st.getTcb? tid = some t ∧ t' = t.withTaintWords w := by
  obtain ⟨t, w, h1, rfl⟩ := tcb_back_eq h ((getTcb?_eq_some_iff _ _ _).mp h2)
  exact ⟨t, w, (getTcb?_eq_some_iff _ _ _).mpr h1, rfl⟩

/-- A thread read of the first state is one of the second with words written. -/
theorem getTcb?_fwd (h : objectsAgreeOffTaint st st') {tid : SeLe4n.ThreadId} {t : TCB}
    (h1 : st.getTcb? tid = some t) : ∃ w, st'.getTcb? tid = some (t.withTaintWords w) := by
  obtain ⟨w, h2⟩ := tcb_fwd_eq h ((getTcb?_eq_some_iff _ _ _).mp h1)
  exact ⟨w, (getTcb?_eq_some_iff _ _ _).mpr h2⟩

/-- A thread read misses on one side exactly when on the other. -/
theorem getTcb?_none_iff (h : objectsAgreeOffTaint st st') (tid : SeLe4n.ThreadId) :
    st'.getTcb? tid = none ↔ st.getTcb? tid = none := by
  unfold getTcb?; rw [getElem?_eq h]
  cases st.objects[tid.toObjId]? with
  | none => rfl
  | some o => cases o <;> simp [KernelObject.withTaintWords]

@[simp] theorem getSchedContext?_eq (h : objectsAgreeOffTaint st st')
    (x : SeLe4n.SchedContextId) : st'.getSchedContext? x = st.getSchedContext? x := by
  unfold getSchedContext?; rw [getElem?_eq h]
  cases st.objects[x.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

@[simp] theorem getReply?_eq (h : objectsAgreeOffTaint st st') (x : SeLe4n.ReplyId) :
    st'.getReply? x = st.getReply? x := by
  unfold getReply?; rw [getElem?_eq h]
  cases st.objects[x.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

@[simp] theorem getEndpoint?_eq (h : objectsAgreeOffTaint st st') (x : SeLe4n.ObjId) :
    st'.getEndpoint? x = st.getEndpoint? x := by
  unfold getEndpoint?; rw [getElem?_eq h]
  cases st.objects[x]? with
  | none => rfl
  | some o => cases o <;> rfl

@[simp] theorem getUntyped?_eq (h : objectsAgreeOffTaint st st') (x : SeLe4n.ObjId) :
    st'.getUntyped? x = st.getUntyped? x := by
  unfold getUntyped?; rw [getElem?_eq h]
  cases st.objects[x]? with
  | none => rfl
  | some o => cases o <;> rfl

@[simp] theorem getCNode?_eq (h : objectsAgreeOffTaint st st') (x : SeLe4n.ObjId) :
    st'.getCNode? x = st.getCNode? x := by
  unfold getCNode?; rw [getElem?_eq h]
  cases st.objects[x]? with
  | none => rfl
  | some o => cases o <;> rfl

@[simp] theorem getVSpaceRoot?_eq (h : objectsAgreeOffTaint st st') (x : SeLe4n.ObjId) :
    st'.getVSpaceRoot? x = st.getVSpaceRoot? x := by
  unfold getVSpaceRoot?; rw [getElem?_eq h]
  cases st.objects[x]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- An object of the second state is one of the first with its words written. -/
theorem some_back_eq (h : objectsAgreeOffTaint st st') {k : SeLe4n.ObjId} {o' : KernelObject}
    (h2 : st'.objects[k]? = some o') :
    ∃ o w, st.objects[k]? = some o ∧ o' = o.withTaintWords w := by
  rw [getElem?_eq h k] at h2
  cases h1 : st.objects[k]? with
  | none => rw [h1] at h2; cases h2
  | some o => rw [h1] at h2; exact ⟨o, _, rfl, (Option.some.inj h2).symm⟩

/-- An object of the first state is one of the second with words written. -/
theorem some_fwd_eq (h : objectsAgreeOffTaint st st') {k : SeLe4n.ObjId} {o : KernelObject}
    (h1 : st.objects[k]? = some o) : ∃ w, st'.objects[k]? = some (o.withTaintWords w) := by
  rw [getElem?_eq h k, h1]; exact ⟨_, rfl⟩

@[simp] theorem lookupCNode_eq (h : objectsAgreeOffTaint st st') (x : SeLe4n.ObjId) :
    st'.lookupCNode x = st.lookupCNode x := by
  unfold lookupCNode; rw [getElem?_eq h]
  cases st.objects[x]? with
  | none => rfl
  | some o => cases o <;> rfl

@[simp] theorem lookupSlotCap_eq (h : objectsAgreeOffTaint st st') (r : SlotRef) :
    st'.lookupSlotCap r = st.lookupSlotCap r := by
  unfold lookupSlotCap; rw [lookupCNode_eq h]

/-- The derivation link a slot holds. -/
@[simp] theorem slotLinkAt_eq (h : objectsAgreeOffTaint st st') :
    st'.slotLinkAt = st.slotLinkAt := by
  funext r f
  unfold slotLinkAt getObject?; rw [getElem?_eq h]
  cases st.objects[r.cnode]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- The service registry, read off the endpoints. -/
theorem serviceRegistry_eq (h : objectsAgreeOffTaint st st') :
    st'.serviceRegistry = st.serviceRegistry := by
  unfold SystemState.serviceRegistry
  simp only [getEndpoint?_eq h]

/-- The capability a slot holds. -/
@[simp] theorem slotCapAt_eq (h : objectsAgreeOffTaint st st') (r : SlotRef) :
    st'.slotCapAt r = st.slotCapAt r := by
  unfold slotCapAt getObject?; rw [getElem?_eq h]
  cases st.objects[r.cnode]? with
  | none => rfl
  | some o => exact congrFun (KernelObject.slotCap_withTaintWords o _) r.slot

/-- An object is present on one side exactly when on the other. -/
theorem present_iff (h : objectsAgreeOffTaint st st') (k : SeLe4n.ObjId) :
    st'.objects[k]? ≠ none ↔ st.objects[k]? ≠ none :=
  not_congr (none_iff h k)

/-- A kind holding no words is read alike, stated for the closing `simp`. -/
theorem inert_eq (h : objectsAgreeOffTaint st st') (k : SeLe4n.ObjId) {o : KernelObject}
    (hN : o.holdsTaint = false := by rfl) :
    (st'.objects[k]? = some o) = (st.objects[k]? = some o) :=
  propext (inert_iff h k hN)

end SeLe4n.Model.SystemState.objectsAgreeOffTaint

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model
open SeLe4n.Model.SystemState (objectsAgreeOffTaint)
open SeLe4n.Kernel.Concurrency (bootCoreId)

variable {st : SystemState} {O : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject}

/-! ### The scheduler conjuncts -/

theorem schedulerInvariantBundle_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : schedulerInvariantBundle st) :
    schedulerInvariantBundle { st with objects := O } := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  unfold currentThreadValid at *
  split at h3
  · rename_i hc; simp [hc]
  · rename_i tid hc
    simp only [hc]
    obtain ⟨t, ht⟩ := h3
    obtain ⟨w, ht'⟩ := objectsAgreeOffTaint.tcb_fwd_eq hA ht
    exact ⟨_, ht'⟩

theorem timeSlicePositive_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : timeSlicePositive st) :
    timeSlicePositive { st with objects := O } := by
  intro tid hr
  have h1 := h tid hr
  split
  · rename_i t hT
    obtain ⟨t0, w, h0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
    rw [h0] at h1; exact h1
  · trivial

theorem currentTimeSlicePositive_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : currentTimeSlicePositive st) :
    currentTimeSlicePositive { st with objects := O } := by
  unfold currentTimeSlicePositive at *
  split at h
  · rename_i hc; simp only [hc]
  · rename_i tid hc
    simp only [hc]
    split
    · rename_i t hT
      obtain ⟨t0, w, h0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
      rw [h0] at h; exact h
    · trivial

theorem edfCurrentHasEarliestDeadline_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (h : edfCurrentHasEarliestDeadline st) :
    edfCurrentHasEarliestDeadline { st with objects := O } := by
  unfold edfCurrentHasEarliestDeadline at *
  split at h
  · rename_i hc; simp only [hc]
  · rename_i cur hc
    simp only [hc]
    split
    · rename_i c hC
      obtain ⟨c0, w, h0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hC
      rw [h0] at h
      intro tid hr
      have h1 := h tid hr
      split
      · rename_i t hT
        obtain ⟨t0, w', h0', rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
        rw [h0'] at h1; exact h1
      · trivial
    · trivial

theorem contextMatchesCurrent_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : contextMatchesCurrent st) :
    contextMatchesCurrent { st with objects := O } := by
  unfold contextMatchesCurrent at *
  split at h
  · rename_i tid hc
    simp only [hc]
    split
    · rename_i t hT
      obtain ⟨t0, w, h0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
      rw [h0] at h; exact h
    · trivial
  · rename_i hc; simp [hc]

theorem runnableThreadsAreTCBs_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : runnableThreadsAreTCBs st) :
    runnableThreadsAreTCBs { st with objects := O } := by
  intro tid hr
  obtain ⟨t, ht⟩ := h tid hr
  obtain ⟨w, ht'⟩ := objectsAgreeOffTaint.tcb_fwd_eq hA ht
  exact ⟨_, ht'⟩

theorem schedulerPriorityMatch_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : schedulerPriorityMatch st) :
    schedulerPriorityMatch { st with objects := O } := by
  intro tid hr
  have h1 := h tid hr
  split
  · rename_i t hT
    obtain ⟨t0, w, h0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
    rw [h0] at h1; exact h1
  · trivial

theorem schedulerInvariantBundleFull_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : schedulerInvariantBundleFull st) :
    schedulerInvariantBundleFull { st with objects := O } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨schedulerInvariantBundle_of_objectsAgreeOffTaint hA h1,
    timeSlicePositive_of_objectsAgreeOffTaint hA h2,
    currentTimeSlicePositive_of_objectsAgreeOffTaint hA h3,
    edfCurrentHasEarliestDeadline_of_objectsAgreeOffTaint hA h4,
    contextMatchesCurrent_of_objectsAgreeOffTaint hA h5,
    runnableThreadsAreTCBs_of_objectsAgreeOffTaint hA h6,
    schedulerPriorityMatch_of_objectsAgreeOffTaint hA h7, h8, h9⟩

/-! ### The scheduling-context conjuncts -/

theorem budgetPositive_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : budgetPositive st) :
    budgetPositive { st with objects := O } := by
  intro tid hr
  have h1 := h tid hr
  split
  · rename_i t hT
    obtain ⟨t0, w, h0, rfl⟩ := objectsAgreeOffTaint.getTcb?_back hA hT
    rw [h0] at h1
    simp only [objectsAgreeOffTaint.getSchedContext?_eq hA]
    exact h1
  · trivial

theorem currentBudgetPositive_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : currentBudgetPositive st) :
    currentBudgetPositive { st with objects := O } := by
  unfold currentBudgetPositive at *
  split at h
  · rename_i hc; simp [hc]
  · rename_i tid hc
    simp only [hc]
    split
    · rename_i t hT
      obtain ⟨t0, w, h0, rfl⟩ := objectsAgreeOffTaint.getTcb?_back hA hT
      rw [h0] at h
      simp only [objectsAgreeOffTaint.getSchedContext?_eq hA]
      exact h
    · trivial

theorem schedContextsWellFormed_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : schedContextsWellFormed st) :
    schedContextsWellFormed { st with objects := O } := fun oid sc h2 =>
  h oid sc ((objectsAgreeOffTaint.inert_iff hA oid rfl).mp h2)

theorem schedContextBindingConsistent_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (h : schedContextBindingConsistent st) :
    schedContextBindingConsistent { st with objects := O } := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun tid t hT scId hb => ?_, fun scId sc hS tid hb => ?_⟩
  · obtain ⟨t0, w, h0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
    obtain ⟨sc, hS, hB⟩ := h1 tid t0 h0 scId hb
    exact ⟨sc, (objectsAgreeOffTaint.inert_iff hA _ rfl).mpr hS, hB⟩
  · obtain ⟨t, hT, hB⟩ := h2 scId sc ((objectsAgreeOffTaint.inert_iff hA _ rfl).mp hS) tid hb
    obtain ⟨w, hT'⟩ := objectsAgreeOffTaint.tcb_fwd_eq hA hT
    exact ⟨_, hT', hB⟩

theorem effectiveParamsMatchRunQueue_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (h : effectiveParamsMatchRunQueue st) :
    effectiveParamsMatchRunQueue { st with objects := O } := by
  intro tid hr
  have h1 := h tid hr
  split
  · rename_i t hT
    obtain ⟨t0, w, h0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
    rw [h0] at h1; exact h1
  · trivial

theorem boundThreadDomainConsistent_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (h : boundThreadDomainConsistent st) :
    boundThreadDomainConsistent { st with objects := O } := by
  intro tid scId
  have h1 := h tid scId
  split
  · rename_i t hT
    obtain ⟨t0, w, h0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
    rw [h0] at h1
    intro hb
    have h2 := h1 hb
    split
    · rename_i sc hS
      rw [(objectsAgreeOffTaint.inert_iff hA _ rfl).mp hS] at h2; exact h2
    · trivial
  · trivial

theorem schedulerInvariantBundleExtended_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (h : schedulerInvariantBundleExtended st) :
    schedulerInvariantBundleExtended { st with objects := O } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨schedulerInvariantBundleFull_of_objectsAgreeOffTaint hA h1,
    budgetPositive_of_objectsAgreeOffTaint hA h2,
    currentBudgetPositive_of_objectsAgreeOffTaint hA h3,
    schedContextsWellFormed_of_objectsAgreeOffTaint hA h4, h5,
    schedContextBindingConsistent_of_objectsAgreeOffTaint hA h6,
    effectiveParamsMatchRunQueue_of_objectsAgreeOffTaint hA h7,
    boundThreadDomainConsistent_of_objectsAgreeOffTaint hA h8⟩

/-! ### The capability conjuncts -/

theorem cspaceLookupSound_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : cspaceLookupSound st) :
    cspaceLookupSound { st with objects := O } := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun cid cn slot cap hC hL => ?_, fun oid o slot cap hO hS => ?_⟩
  · rw [objectsAgreeOffTaint.lookupSlotCap_eq hA]
    exact h1 cid cn slot cap ((objectsAgreeOffTaint.inert_iff hA _ rfl).mp hC) hL
  · obtain ⟨o0, w, h0, rfl⟩ := objectsAgreeOffTaint.some_back_eq hA hO
    rw [objectsAgreeOffTaint.slotCapAt_eq hA]
    exact h2 oid o0 slot cap h0 (by rw [← KernelObject.slotCap_withTaintWords o0 w]; exact hS)

theorem cdtCompleteness_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : cdtCompleteness st) :
    cdtCompleteness { st with objects := O } := by
  intro ref hm
  obtain ⟨o, hO, hS⟩ := h ref hm
  obtain ⟨w, hO'⟩ := objectsAgreeOffTaint.some_fwd_eq hA hO
  exact ⟨_, hO', by rw [KernelObject.slotCap_withTaintWords]; exact hS⟩

theorem cspaceDepthConsistent_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : cspaceDepthConsistent st) :
    cspaceDepthConsistent { st with objects := O } := fun cid cn hC =>
  h cid cn ((objectsAgreeOffTaint.inert_iff hA _ rfl).mp hC)

theorem replyCapPointsToValidReply_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (h : replyCapPointsToValidReply st) :
    replyCapPointsToValidReply { st with objects := O } := by
  intro oid o slot cap rid hO hS hT
  obtain ⟨o0, w, h0, rfl⟩ := objectsAgreeOffTaint.some_back_eq hA hO
  rw [objectsAgreeOffTaint.getReply?_eq hA]
  exact h oid o0 slot cap rid h0 (by rw [← KernelObject.slotCap_withTaintWords o0 w]; exact hS) hT

theorem cdtLinksAgree_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : cdtLinksAgree st) :
    cdtLinksAgree { st with objects := O } := by
  unfold cdtLinksAgree; rw [objectsAgreeOffTaint.slotLinkAt_eq hA]; exact h

theorem capTreeShape_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : SystemState.CapTreeShape st) :
    SystemState.CapTreeShape { st with objects := O } := by
  have e1 : SystemState.slotCapAt { st with objects := O } = st.slotCapAt :=
    funext (objectsAgreeOffTaint.slotCapAt_eq hA)
  have e2 : SystemState.objectPresent { st with objects := O } = st.objectPresent :=
    funext fun k => propext (objectsAgreeOffTaint.present_iff hA k)
  have e3 : SystemState.getUntyped? { st with objects := O } = st.getUntyped? :=
    funext (objectsAgreeOffTaint.getUntyped?_eq hA)
  unfold SystemState.CapTreeShape
  rw [e1, e2, e3]; exact h

theorem capabilityInvariantBundle_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (hI : O.invExt)
    (h : capabilityInvariantBundle st) : capabilityInvariantBundle { st with objects := O } := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8⟩ := h
  exact ⟨cspaceLookupSound_of_objectsAgreeOffTaint hA h1,
    cdtCompleteness_of_objectsAgreeOffTaint hA h2, h3,
    cspaceDepthConsistent_of_objectsAgreeOffTaint hA h4, hI,
    replyCapPointsToValidReply_of_objectsAgreeOffTaint hA h6,
    cdtLinksAgree_of_objectsAgreeOffTaint hA h7,
    capTreeShape_of_objectsAgreeOffTaint hA h8⟩

/-! ### The IPC and coupling conjuncts -/

theorem coreIpcInvariantBundle_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (hI : O.invExt)
    (h : coreIpcInvariantBundle st) : coreIpcInvariantBundle { st with objects := O } :=
  ⟨schedulerInvariantBundle_of_objectsAgreeOffTaint hA h.1,
    capabilityInvariantBundle_of_objectsAgreeOffTaint hA hI h.2.1,
    ipcInvariantFull_of_objectsAgreeOffTaint hA h.2.2⟩

/-- The shape every "a thread in this state is not runnable" conjunct shares:
a statement about each stored thread blind to its words. -/
private theorem forall_tcb_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    {P : SeLe4n.ThreadId → TCB → Prop} (hP : ∀ tid t w, P tid t → P tid (t.withTaintWords w))
    (h : ∀ tid t, st.objects[tid.toObjId]? = some (.tcb t) → P tid t) :
    ∀ tid t, O[tid.toObjId]? = some (.tcb t) → P tid t := fun tid t hT => by
  obtain ⟨t0, w, h0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
  exact hP tid t0 w (h tid t0 h0)

theorem ipcSchedulerCoherenceComponent_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (h : ipcSchedulerCoherenceComponent st) :
    ipcSchedulerCoherenceComponent { st with objects := O } := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨forall_tcb_of_objectsAgreeOffTaint hA (fun _ _ _ x => x) h1,
    fun tid t e hT => forall_tcb_of_objectsAgreeOffTaint hA
      (P := fun tid t => ∀ e, t.ipcState = .blockedOnSend e → tid ∉ st.scheduler.runnable)
      (fun _ _ _ x => x) (fun tid t hT e => h2 tid t e hT) tid t hT e,
    fun tid t e hT => forall_tcb_of_objectsAgreeOffTaint hA
      (P := fun tid t => ∀ e, t.ipcState = .blockedOnReceive e → tid ∉ st.scheduler.runnable)
      (fun _ _ _ x => x) (fun tid t hT e => h3 tid t e hT) tid t hT e,
    fun tid t e hT => forall_tcb_of_objectsAgreeOffTaint hA
      (P := fun tid t => ∀ e, t.ipcState = .blockedOnCall e → tid ∉ st.scheduler.runnable)
      (fun _ _ _ x => x) (fun tid t hT e => h4 tid t e hT) tid t hT e,
    fun tid t e r hT => forall_tcb_of_objectsAgreeOffTaint hA
      (P := fun tid t => ∀ e r, t.ipcState = .blockedOnReply e r → tid ∉ st.scheduler.runnable)
      (fun _ _ _ x => x) (fun tid t hT e r => h5 tid t e r hT) tid t hT e r,
    fun tid t e hT => forall_tcb_of_objectsAgreeOffTaint hA
      (P := fun tid t => ∀ e, t.ipcState = .blockedOnNotification e →
        tid ∉ st.scheduler.runnable)
      (fun _ _ _ x => x) (fun tid t hT e => h6 tid t e hT) tid t hT e⟩

theorem currentThreadDequeueCoherent_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (h : currentThreadDequeueCoherent st) :
    currentThreadDequeueCoherent { st with objects := O } := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · unfold currentThreadIpcReady at *
    split at h1
    · rename_i hc; simp [hc]
    · rename_i tid hc
      simp only [hc]
      intro t hT
      obtain ⟨t0, w, h0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
      exact h1 t0 h0
  · unfold currentNotEndpointQueueHead at *
    split at h2
    · rename_i hc; simp [hc]
    · rename_i tid hc
      simp only [hc]
      intro oid ep hE
      exact h2 oid ep ((objectsAgreeOffTaint.inert_iff hA _ rfl).mp hE)
  · unfold currentNotOnNotificationWaitList at *
    split at h3
    · rename_i hc; simp [hc]
    · rename_i tid hc
      simp only [hc]
      intro oid n hN
      obtain ⟨n0, w, h0, rfl⟩ := objectsAgreeOffTaint.notification_back_eq hA hN
      exact h3 oid n0 h0

theorem ipcSchedulerCouplingInvariantBundle_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (hI : O.invExt)
    (h : ipcSchedulerCouplingInvariantBundle st) :
    ipcSchedulerCouplingInvariantBundle { st with objects := O } :=
  ⟨coreIpcInvariantBundle_of_objectsAgreeOffTaint hA hI h.1,
    ipcSchedulerCoherenceComponent_of_objectsAgreeOffTaint hA h.2.1,
    contextMatchesCurrent_of_objectsAgreeOffTaint hA h.2.2.1,
    currentThreadDequeueCoherent_of_objectsAgreeOffTaint hA h.2.2.2⟩

/-! ### The lifecycle, registry and VSpace conjuncts -/

theorem lifecycleInvariantBundle_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : lifecycleInvariantBundle st) :
    lifecycleInvariantBundle { st with objects := O } := fun oid => by
  have e := objectsAgreeOffTaint.map_blind hA KernelObject.objectType
    KernelObject.objectType_withTaintWords oid
  exact (h oid).trans e.symm

theorem registryInvariant_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : registryInvariant st) :
    registryInvariant { st with objects := O } := by
  have e := objectsAgreeOffTaint.serviceRegistry_eq hA
  refine ⟨fun sid reg hR => ?_, fun sid reg hR => h.2 sid reg (by rw [← e]; exact hR)⟩
  obtain ⟨ep, hT, hP⟩ := h.1 sid reg (by rw [← e]; exact hR)
  exact ⟨ep, hT, (objectsAgreeOffTaint.present_iff hA ep).mpr hP⟩

theorem vspaceInvariantBundle_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : vspaceInvariantBundle st) :
    vspaceInvariantBundle { st with objects := O } := by
  have hV : ∀ oid r, O[oid]? = some (KernelObject.vspaceRoot r) ↔
      st.objects[oid]? = some (KernelObject.vspaceRoot r) :=
    fun oid _ => objectsAgreeOffTaint.inert_iff hA oid rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨fun o1 o2 r1 r2 a b => h1 o1 o2 r1 r2 ((hV _ _).mp a) ((hV _ _).mp b),
    fun o r a => h2 o r ((hV _ _).mp a), ⟨fun asid oid hT => ?_, fun oid r a => h3.2 oid r ((hV _ _).mp a)⟩,
    fun o r v p q a => h4 o r v p q ((hV _ _).mp a),
    fun o r v p q a => h5 o r v p q ((hV _ _).mp a),
    fun o1 o2 r1 r2 a b => h6 o1 o2 r1 r2 ((hV _ _).mp a) ((hV _ _).mp b),
    fun o r v p q a => h7 o r v p q ((hV _ _).mp a),
    fun o r a => h8 o r ((hV _ _).mp a)⟩
  obtain ⟨r, hr, ha⟩ := h3.1 asid oid hT
  exact ⟨r, (hV _ _).mpr hr, ha⟩

/-! ### The notification wait queues -/

theorem notificationWaiterConsistent_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (hInv : notificationWaiterConsistent st) :
    notificationWaiterConsistent { st with objects := O } := by
  have reach : ∀ {n t}, notificationQueueReaches st n t →
      notificationQueueReaches { st with objects := O } n t := by
    intro n t hR
    induction hR with
    | head hN hH =>
      obtain ⟨w, hN'⟩ := objectsAgreeOffTaint.notification_fwd_eq hA hN
      exact .head hN' hH
    | @next a b ta _ hTa hNx ih =>
      obtain ⟨w, hTa'⟩ := objectsAgreeOffTaint.tcb_fwd_eq hA hTa
      exact .next ih hTa' hNx
  refine ⟨fun oid ntfn hN => ?_, fun tid tcb oid hT hB => ?_, fun tid tcb oid hT hB => ?_,
    fun oid ntfn hd tcb hN hH hT => ?_, fun tid tcb hT hNB => ?_⟩
  · obtain ⟨n0, w, hN0, rfl⟩ := objectsAgreeOffTaint.notification_back_eq hA hN
    obtain ⟨hIff, hHead, hTail⟩ := hInv.1 oid n0 hN0
    refine ⟨hIff, fun hd hh => ?_, fun t ht => ?_⟩
    · obtain ⟨tcb, hT, hB⟩ := hHead hd hh
      obtain ⟨w', hT'⟩ := objectsAgreeOffTaint.tcb_fwd_eq hA hT
      exact ⟨_, hT', hB⟩
    · obtain ⟨tcb, hT, hB, hN'⟩ := hTail t ht
      obtain ⟨w', hT'⟩ := objectsAgreeOffTaint.tcb_fwd_eq hA hT
      exact ⟨_, hT', hB, hN'⟩
  · obtain ⟨t0, w, hT0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
    obtain ⟨ntfn, hN, hPrev, hTail, hNext⟩ := hInv.2.1 tid t0 oid hT0 hB
    obtain ⟨wn, hN'⟩ := objectsAgreeOffTaint.notification_fwd_eq hA hN
    refine ⟨_, hN', ?_, hTail, ?_⟩
    · rcases hPrev with hp | ⟨a, ta, ha, hTa, hBa, hNa⟩
      · exact Or.inl hp
      · obtain ⟨wa, hTa'⟩ := objectsAgreeOffTaint.tcb_fwd_eq hA hTa
        exact Or.inr ⟨a, _, ha, hTa', hBa, hNa⟩
    · intro b hb
      obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNext b hb
      obtain ⟨wb, hTb'⟩ := objectsAgreeOffTaint.tcb_fwd_eq hA hTb
      exact ⟨hne, _, hTb', hBb, hPb⟩
  · obtain ⟨t0, w, hT0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
    exact reach (hInv.reaches hT0 hB)
  · obtain ⟨n0, w, hN0, rfl⟩ := objectsAgreeOffTaint.notification_back_eq hA hN
    obtain ⟨t0, w', hT0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
    have hP := hInv.headNoPrev hN0 hH hT0
    exact hP
  · obtain ⟨t0, w, hT0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
    have hL := hInv.unqueuedNoLinks hT0 hNB
    exact hL

/-! ### The translation caches -/

theorem resolveAsidRoot_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (asid : SeLe4n.ASID) :
    resolveAsidRoot { st with objects := O } asid = resolveAsidRoot st asid := by
  unfold resolveAsidRoot
  simp only [objectsAgreeOffTaint.getVSpaceRoot?_eq hA]

theorem tlbConsistent_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : tlbConsistent st st.tlb) :
    tlbConsistent { st with objects := O } st.tlb := fun e he r root hr =>
  h e he r root (by rw [← resolveAsidRoot_of_objectsAgreeOffTaint hA]; exact hr)

theorem tlbEntryConsistent_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (e : TlbEntry) :
    tlbEntryConsistent { st with objects := O } e ↔ tlbEntryConsistent st e := by
  unfold tlbEntryConsistent; rw [resolveAsidRoot_of_objectsAgreeOffTaint hA]

theorem tlbInvalidationConsistent_perCore_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (h : tlbInvalidationConsistent_perCore st) :
    tlbInvalidationConsistent_perCore { st with objects := O } := fun c e he => by
  rcases h c e he with h1 | h2
  · exact .inl ((tlbEntryConsistent_of_objectsAgreeOffTaint hA e).mpr h1)
  · exact .inr h2

theorem icacheCoherent_perCore_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : icacheCoherent_perCore st) :
    icacheCoherent_perCore { st with objects := O } := fun c l hl =>
  ⟨(tlbEntryConsistent_of_objectsAgreeOffTaint hA _).mpr (h c l hl).1, (h c l hl).2⟩

/-! ### The cross-subsystem conjuncts -/

theorem blockingServer_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (tid : SeLe4n.ThreadId) :
    PriorityInheritance.blockingServer { st with objects := O } tid =
      PriorityInheritance.blockingServer st tid := by
  unfold PriorityInheritance.blockingServer
  cases h1 : st.getTcb? tid with
  | none => rw [(objectsAgreeOffTaint.getTcb?_none_iff hA tid).mpr h1]
  | some t =>
    obtain ⟨w, h2⟩ := objectsAgreeOffTaint.getTcb?_fwd hA h1
    rw [h2]; rfl

theorem crossSubsystemInvariant_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (hS : O.size = st.objects.size)
    (h : crossSubsystemInvariant st) : crossSubsystemInvariant { st with objects := O } := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h
  have hR := registryInvariant_of_objectsAgreeOffTaint hA ⟨d1, d2⟩
  have hP := objectsAgreeOffTaint.present_iff hA
  have hQ := collectQueueMembers_congr_queueNext st.objects O
    (fun k => objectsAgreeOffTaint.map_blind hA _ (fun o _ => by cases o <;> rfl) k)
  refine ⟨hR.1, hR.2, fun oid ep hE => ?_, fun oid n hN tid ht => ?_,
    fun tid t hT scId hb => ?_, fun t1 t2 a b scId h1 h2 hb1 hb2 => ?_,
    fun tid hr t hT scId hb => ?_,
    PriorityInheritance.blockingAcyclic_frame st _ d8
      (blockingServer_of_objectsAgreeOffTaint hA) rfl,
    fun oid o hO => ?_, fun o1 o2 u1 u2 a b => d10 o1 o2 u1 u2
      ((objectsAgreeOffTaint.inert_iff hA _ rfl).mp a)
      ((objectsAgreeOffTaint.inert_iff hA _ rfl).mp b)⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := d3 oid ep ((objectsAgreeOffTaint.inert_iff hA _ rfl).mp hE)
    refine ⟨fun t ht => (hP _).mpr (e1 t ht), fun t ht => (hP _).mpr (e2 t ht),
      fun t ht => (hP _).mpr (e3 t ht), fun t ht => (hP _).mpr (e4 t ht),
      fun ms hm t ht => (hP _).mpr (e5 ms ?_ t ht), fun ms hm t ht => (hP _).mpr (e6 ms ?_ t ht)⟩
    · simp only at hm; rw [hQ, hS] at hm; exact hm
    · simp only at hm; rw [hQ, hS] at hm; exact hm
  · obtain ⟨n0, w, hN0, rfl⟩ := objectsAgreeOffTaint.notification_back_eq hA hN
    exact (hP _).mpr (d4 oid n0 hN0 tid ht)
  · obtain ⟨t0, w, hT0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
    obtain ⟨sc, hSc⟩ := d5 tid t0 hT0 scId hb
    exact ⟨sc, (objectsAgreeOffTaint.inert_iff hA _ rfl).mpr hSc⟩
  · obtain ⟨u1, w1, hU1, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA h1
    obtain ⟨u2, w2, hU2, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA h2
    exact d6 t1 t2 u1 u2 scId hU1 hU2 hb1 hb2
  · obtain ⟨t0, w, hT0, rfl⟩ := objectsAgreeOffTaint.tcb_back_eq hA hT
    obtain ⟨sc, hSc, hpos⟩ := d7 tid hr t0 hT0 scId hb
    exact ⟨sc, (objectsAgreeOffTaint.inert_iff hA _ rfl).mpr hSc, hpos⟩
  · obtain ⟨o0, w, hO0, rfl⟩ := objectsAgreeOffTaint.some_back_eq hA hO
    rw [KernelObject.objectType_withTaintWords]
    exact d9 oid o0 hO0

/-! ### The run queues and the mapping records -/

theorem runQueueRefined_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : st.runQueueRefined) :
    SystemState.runQueueRefined { st with objects := O } := by
  have hL : ∀ c t, SystemState.runLinkOn { st with objects := O } c t = st.runLinkOn c t :=
    fun c t => by
      have e := SystemState.getTcb?_map_of_objectsAgreeOffTaint hA (fun x => x.runLinkOn c) (fun _ => rfl) t
      unfold SystemState.runLinkOn
      cases h2 : SystemState.getTcb? { st with objects := O } t <;>
        cases h1 : st.getTcb? t <;> rw [h1, h2] at e <;>
          first | rfl | cases e | exact Option.some.inj e
  exact SystemState.runQueueRefined_of_frame hL rfl rfl h

theorem liveMappingsRecorded_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : st.liveMappingsRecorded) :
    SystemState.liveMappingsRecorded { st with objects := O } :=
  SystemState.liveMappingsRecorded.of_mappingFactsKept
    (SystemState.mappingFactsKept.of_objectsAgreeOffTaint hA) h

/-- WS-ZA ZA6.6: a word write keeps every yield-link code — neither a thread's
`yieldToCode` nor a context's `yieldFromCode` is a taint word — so the two link
ends still agree. -/
theorem yieldLinksAgree_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : st.yieldLinksAgree) :
    SystemState.yieldLinksAgree { st with objects := O } :=
  SystemState.yieldLinksAgree_of_kept
    (YieldLinksKept.of_map KernelObject.eraseTaint (fun o => by cases o <;> rfl) hA) h

/-- WS-ZA ZA6.4: a word write keeps every context's refills — a context holds
no taint word — and writes no release queue, so the refill state stays sound. -/
theorem refillsSound_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (hR' : SystemState.releaseQueueRefined { st with objects := O }) (h : st.refillsSound) :
    SystemState.refillsSound { st with objects := O } := by
  refine SystemState.refillsSound_of_kept (st := st) (st' := { st with objects := O })
    (fun k v hv => ?_) (fun _ => rfl) hR' h
  change objRefillView O[k]? = some v at hv
  cases h2 : O[k]? with
  | none => rw [h2] at hv; cases hv
  | some o' =>
    rw [h2] at hv
    obtain ⟨o, h1, e⟩ := hA.some_iff _ o' h2
    rw [h1]
    cases hH : o'.holdsTaint with
    | false =>
      have hx := KernelObject.eq_of_eraseTaint_eq hH e
      first | (rw [← hx]; exact hv) | (rw [hx]; exact hv) | (subst hx; exact hv)
    | true =>
      cases o' with
      | tcb x => cases hv
      | notification n => cases hv
      | _ => simp [KernelObject.holdsTaint] at hH

/-- WS-ZA ZA6.3: a word write keeps every release link — a context holds no
taint word, and a thread or a notification holds no release link — and writes
no scheduler slot. -/
theorem releaseQueueRefined_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O }) (h : st.releaseQueueRefined) :
    SystemState.releaseQueueRefined { st with objects := O } := by
  refine SystemState.releaseStateAgree.refined (st := st)
    ⟨.of_objReleaseLinkOn fun k c => ?_, rfl⟩ h
  show SystemState.objReleaseLinkOn O[k]? c = _
  have hk := hA k
  cases h2 : O[k]? with
  | none =>
    cases h1 : st.objects[k]? with
    | none => rfl
    | some _ => exact absurd hk (by rw [h1]; exact fun e => by simp_all)
  | some o' =>
    obtain ⟨o, h1, e⟩ := hA.some_iff _ o' h2
    rw [h1]
    cases hH : o'.holdsTaint with
    | false => rw [KernelObject.eq_of_eraseTaint_eq hH e]
    | true =>
      cases o' with
      | tcb x => obtain ⟨y, rfl, -⟩ := KernelObject.eraseTaint_eq_tcb e; rfl
      | notification n => obtain ⟨m, rfl, -⟩ := KernelObject.eraseTaint_eq_notification e; rfl
      | _ => simp [KernelObject.holdsTaint] at hH

/-! ### The whole bundle -/

/-- **WS-ZA ZA5.11: the whole invariant bundle carries across a taint-word
write.**  A store that agrees with `st`'s off the taint words, keeps its table
invariant and its size, satisfies every conjunct `st` does: no conjunct reads a
taint word. -/
theorem proofLayerInvariantBundle_of_objectsAgreeOffTaint
    (hA : st.objectsAgreeOffTaint { st with objects := O })
    (hI : st.objects.invExt → O.invExt) (hS : O.size = st.objects.size)
    (h : proofLayerInvariantBundle st) : proofLayerInvariantBundle { st with objects := O } := by
  obtain ⟨bSched, bCap, bCoreIpc, bCoupling, bLifecycle, bService, bVSpace,
          bCross, bTlb, bSchedExt, bNtfn, bPending, bPerCoreTlb,
          bIcache, bAck, bAudit, bRun, bMap, bRel, bRefill, bYield⟩ := h
  have hI' := hI bCap.2.2.2.2.1
  exact ⟨schedulerInvariantBundleFull_of_objectsAgreeOffTaint hA bSched,
    capabilityInvariantBundle_of_objectsAgreeOffTaint hA hI' bCap,
    coreIpcInvariantBundle_of_objectsAgreeOffTaint hA hI' bCoreIpc,
    ipcSchedulerCouplingInvariantBundle_of_objectsAgreeOffTaint hA hI' bCoupling,
    lifecycleInvariantBundle_of_objectsAgreeOffTaint hA bLifecycle,
    registryInvariant_of_objectsAgreeOffTaint hA bService,
    vspaceInvariantBundle_of_objectsAgreeOffTaint hA bVSpace,
    crossSubsystemInvariant_of_objectsAgreeOffTaint hA hS bCross,
    tlbConsistent_of_objectsAgreeOffTaint hA bTlb,
    schedulerInvariantBundleExtended_of_objectsAgreeOffTaint hA bSchedExt,
    notificationWaiterConsistent_of_objectsAgreeOffTaint hA bNtfn, bPending,
    tlbInvalidationConsistent_perCore_of_objectsAgreeOffTaint hA bPerCoreTlb,
    icacheCoherent_perCore_of_objectsAgreeOffTaint hA bIcache, bAck, bAudit,
    runQueueRefined_of_objectsAgreeOffTaint hA bRun,
    liveMappingsRecorded_of_objectsAgreeOffTaint hA bMap,
    releaseQueueRefined_of_objectsAgreeOffTaint hA bRel,
    refillsSound_of_objectsAgreeOffTaint hA (releaseQueueRefined_of_objectsAgreeOffTaint hA bRel)
      bRefill,
    yieldLinksAgree_of_objectsAgreeOffTaint hA bYield⟩

end SeLe4n.Kernel.Architecture
