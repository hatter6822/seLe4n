/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Scheduler.ReplyWaitersOps

/-! # The yield link's writes as frames

WS-ZA ZA6.6.  `cancelYieldTo` writes the two link ends and nothing else, and
`setConsumed` writes a thread's two return registers and a context's consumed
count.  This module states both as frames — the objects agreeing off the yield
codes (`objectsAgreeOffYield`), and the thread and context updates — and derives
the run-queue stage of each operation (`cancelYieldTo_runQueueStage`,
`setConsumed_runQueueStage`, `completeYieldTo_runQueueStage`,
`completeYieldFrom_runQueueStage`). -/

namespace SeLe4n.Model

open SeLe4n.Kernel

/-- A thread with what the yield operations write cleared: its yield-to code and
the two return registers `setConsumed` writes. -/
@[reducible] def TCB.withoutYieldWrites (t : TCB) : TCB :=
  { t with yieldToCode := 0, registerContext := { t.registerContext with x1 := 0, x2 := 0 } }

/-- An object with what the yield operations write cleared: a thread's yield-to
code and the two return registers `setConsumed` writes (`x1`, `x2`), a
context's yield-from code and its consumed count; every other object as it
is. -/
def KernelObject.withoutYield : KernelObject → KernelObject
  | .tcb t => .tcb t.withoutYieldWrites
  | .schedContext sc => .schedContext { sc with yieldFromCode := 0, consumed := 0 }
  | o => o

namespace SystemState

/-- **Two stores agreeing off the yield writes**: every slot holds the same
object once what the yield operations write is cleared
(`KernelObject.withoutYield`). -/
def objectsAgreeOffYield (st' st : SystemState) : Prop :=
  ∀ x : SeLe4n.ObjId,
    (st'.objects[x]?).map KernelObject.withoutYield = (st.objects[x]?).map KernelObject.withoutYield

namespace objectsAgreeOffYield

theorem refl (st : SystemState) : objectsAgreeOffYield st st := fun _ => rfl

theorem trans {a b c : SystemState} (h₂ : objectsAgreeOffYield c b)
    (h₁ : objectsAgreeOffYield b a) : objectsAgreeOffYield c a :=
  fun x => (h₂ x).trans (h₁ x)

/-- Any reading of a thread's TCB that ignores its yield-to code and its two
return registers agrees. -/
theorem getTcb?_map {st st' : SystemState} (h : objectsAgreeOffYield st' st) {α : Type _}
    (f : TCB → α) (hf : ∀ u : TCB, f u.withoutYieldWrites = f u := by intro; rfl)
    (t : SeLe4n.ThreadId) : (st'.getTcb? t).map f = (st.getTcb? t).map f := by
  have e := h t.toObjId
  unfold getTcb?
  revert e
  cases st'.objects[t.toObjId]? <;> cases st.objects[t.toObjId]? <;> intro e
  · rfl
  · rename_i o; cases o <;> cases e
  · rename_i o; cases o <;> cases e
  · rename_i a b
    simp only [Option.map_some, Option.some.injEq] at e
    cases a <;> cases b <;>
      simp only [KernelObject.withoutYield, reduceCtorEq, KernelObject.tcb.injEq] at e <;>
      simp only [Option.map_some, Option.map_none]
    rename_i u v
    rw [← hf u, ← hf v, e]

/-- Any reading of a context that ignores its yield-from code and its consumed
count agrees. -/
theorem getSchedContext?_map {st st' : SystemState} (h : objectsAgreeOffYield st' st)
    {α : Type _} (f : SchedContext → α)
    (hf : ∀ u : SchedContext, f { u with yieldFromCode := 0, consumed := 0 } = f u := by
      intro; rfl)
    (s : SeLe4n.SchedContextId) :
    (st'.getSchedContext? s).map f = (st.getSchedContext? s).map f := by
  have e := h s.toObjId
  unfold getSchedContext?
  revert e
  cases st'.objects[s.toObjId]? <;> cases st.objects[s.toObjId]? <;> intro e
  · rfl
  · rename_i o; cases o <;> cases e
  · rename_i o; cases o <;> cases e
  · rename_i a b
    simp only [Option.map_some, Option.some.injEq] at e
    cases a <;> cases b <;>
      simp only [KernelObject.withoutYield, reduceCtorEq, KernelObject.schedContext.injEq] at e <;>
      simp only [Option.map_some, Option.map_none]
    rename_i u v
    rw [← hf u, ← hf v, e]

/-- A thread before is a thread after, the same off its yield writes. -/
theorem getTcb?_some {st st' : SystemState} (h : objectsAgreeOffYield st' st)
    {t : SeLe4n.ThreadId} {u : TCB} (hT : st.getTcb? t = some u) :
    ∃ u', st'.getTcb? t = some u' ∧ u'.withoutYieldWrites = u.withoutYieldWrites := by
  have e := h.getTcb?_map TCB.withoutYieldWrites (fun _ => rfl) t
  rw [hT] at e
  cases h' : st'.getTcb? t with
  | none => rw [h'] at e; cases e
  | some u' =>
    rw [h'] at e
    exact ⟨u', rfl, Option.some.inj e⟩

/-- Every thread's run-queue core agrees. -/
theorem runCoresAgree {st st' : SystemState} (h : objectsAgreeOffYield st' st) :
    RunCoresAgree st' st := fun y => h.getTcb?_map TCB.runCoreCode (fun _ => rfl) y

end objectsAgreeOffYield

/-- A thread update that writes nothing but its yield-to code agrees off the
yield codes. -/
theorem updateTcb_objectsAgreeOffYield (st : SystemState) (tid : SeLe4n.ThreadId)
    (g : TCB → TCB) (hInv : st.objects.invExt)
    (hg : ∀ t, KernelObject.withoutYield (.tcb (g t)) = KernelObject.withoutYield (.tcb t)) :
    objectsAgreeOffYield (st.updateTcb tid g) st := fun k => by
  by_cases hk : tid.toObjId = k
  · subst hk
    cases hT : st.getTcb? tid with
    | none => rw [updateTcb_eq_self_of_none hT]
    | some t =>
      rw [updateTcb_eq_of_some hT]
      show ((st.objects.insert tid.toObjId _)[tid.toObjId]?).map _ = _
      have e : (st.objects.insert tid.toObjId (.tcb (g t)))[tid.toObjId]? = some (.tcb (g t)) :=
        RobinHood.RHTable.getElem?_insert_self st.objects _ _ hInv
      rw [e, (getTcb?_eq_some_iff _ _ _).mp hT]
      exact congrArg some (hg t)
  · rw [updateTcb_objects_ne _ _ _ _ hk hInv]

/-- A context update that writes nothing but its yield-from code agrees off
the yield codes. -/
theorem updateSchedContext_objectsAgreeOffYield (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (hInv : st.objects.invExt)
    (hg : ∀ sc, KernelObject.withoutYield (.schedContext (g sc)) =
      KernelObject.withoutYield (.schedContext sc)) :
    objectsAgreeOffYield (st.updateSchedContext s g) st := fun k => by
  by_cases hk : s.toObjId = k
  · subst hk
    cases hS : st.getSchedContext? s with
    | none => rw [updateSchedContext_eq_self_of_none hS]
    | some sc =>
      rw [updateSchedContext_eq_of_some hS]
      show ((st.objects.insert s.toObjId _)[s.toObjId]?).map _ = _
      have e : (st.objects.insert s.toObjId (.schedContext (g sc)))[s.toObjId]? =
          some (.schedContext (g sc)) :=
        RobinHood.RHTable.getElem?_insert_self st.objects _ _ hInv
      rw [e, (getSchedContext?_eq_some_iff _ _ _).mp hS]
      exact congrArg some (hg sc)
  · rw [updateSchedContext_objects_ne _ _ _ _ hk hInv]

/-- **The cancel writes the two link ends alone.** -/
theorem cancelYieldTo_objectsAgreeOffYield (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : objectsAgreeOffYield (cancelYieldTo st tid) st := by
  unfold cancelYieldTo
  split
  · split
    · exact .refl st
    · exact (updateTcb_objectsAgreeOffYield _ tid TCB.yieldCleared
        (updateSchedContext_preserves_objects_invExt _ _ _ hInv) (fun _ => rfl)).trans
        (updateSchedContext_objectsAgreeOffYield _ _ SchedContext.yieldCleared hInv (fun _ => rfl))
  · exact .refl st

/-- **The context's end of the cancel writes the two link ends alone.** -/
theorem cancelYieldFrom_objectsAgreeOffYield (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : objectsAgreeOffYield (cancelYieldFrom st s) st := by
  unfold cancelYieldFrom
  split
  · split
    · exact .refl st
    · exact (updateTcb_objectsAgreeOffYield _ _ TCB.yieldCleared
        (updateSchedContext_preserves_objects_invExt _ _ _ hInv) (fun _ => rfl)).trans
        (updateSchedContext_objectsAgreeOffYield _ _ SchedContext.yieldCleared hInv (fun _ => rfl))
  · exact .refl st

/-- **`setConsumed` writes the consumed count and two return registers alone.** -/
theorem setConsumed_objectsAgreeOffYield (st : SystemState) (s : SeLe4n.SchedContextId)
    (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    objectsAgreeOffYield (setConsumed st s t) st := by
  unfold setConsumed
  split
  · exact (updateTcb_objectsAgreeOffYield _ t (TCB.withConsumed · _)
      (updateSchedContext_preserves_objects_invExt _ s _ hInv) (fun _ => rfl)).trans
      (updateSchedContext_objectsAgreeOffYield _ s SchedContext.updateConsumed hInv (fun _ => rfl))
  · exact .refl st

/-- **The completion of a context's recorded yield writes the yield writes alone.** -/
theorem completeYieldFrom_objectsAgreeOffYield (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : objectsAgreeOffYield (completeYieldFrom st s) st := by
  unfold completeYieldFrom
  split
  · split
    · exact .refl st
    · exact (cancelYieldFrom_objectsAgreeOffYield _ s
        (setConsumed_preserves_objects_invExt _ _ _ hInv)).trans
        (setConsumed_objectsAgreeOffYield _ _ _ hInv)
  · exact .refl st

/-- **A held context's completion writes the yield writes alone.** -/
theorem completeHeldYield_objectsAgreeOffYield (st : SystemState) (held : Nat)
    (hInv : st.objects.invExt) : objectsAgreeOffYield (completeHeldYield st held) st := by
  unfold completeHeldYield
  split
  · exact .refl st
  · exact completeYieldFrom_objectsAgreeOffYield _ _ hInv

/-- **A step that writes only the yield link ends and no scheduler field is a
run-queue stage**: every run link, release link, refill view, table back-link
and thread state reads as before; the link agreement is the step's own
(`hY`). -/
theorem RunQueueStage.of_objectsAgreeOffYield {st st' : SystemState}
    (hA : objectsAgreeOffYield st' st) (hS : st'.scheduler = st.scheduler)
    (hI : st.objects.invExt → st'.objects.invExt)
    (hT : st'.referenceTables = st.referenceTables)
    (hY : st.objects.invExt → st.yieldLinksAgree → st'.yieldLinksAgree)
    (hU : st.objects.invExt → Kernel.YieldToCodesUnset st' st)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueStage st st' := by
  have hL : ∀ c t, st'.runLinkOn c t = st.runLinkOn c t := by
    intro c t
    have e := hA.getTcb?_map (fun x => x.runLinkOn c) (t := t)
    unfold runLinkOn
    cases h1 : st'.getTcb? t <;> cases h2 : st.getTcb? t <;> rw [h1, h2] at e <;>
      first | rfl | cases e | exact Option.some.inj e
  have hM : StateMono st st' :=
    StateMono.of_stateFields (fun t => hA.getTcb?_map _ (t := t))
  have hF : TableReferenceFrame st st' :=
    .of_map (g := KernelObject.withoutYield) (fun o => by cases o <;> rfl) hT hA
  have hRel : releaseStateAgree st' st :=
    ⟨.of_map KernelObject.withoutYield (fun o _ => by cases o <;> rfl) hA, by rw [hS]⟩
  have hV : Kernel.RefillViewsKept st' st :=
    Kernel.RefillViewsKept.of_map KernelObject.withoutYield (fun o => by cases o <;> rfl) hA
  exact ⟨⟨fun h r => ⟨hI h, runQueueRefined_of_frame hL (by rw [hS]) (by rw [hS]) r⟩,
      fun _ _ t => hF.preserves t, fun _ _ r => hRel.refined r,
      fun _ _ _ q s => refillsSoundExcept_of_kept hV
        (fun c => by rw [hRel.replenishQueueOnCore c]) (hRel.refined q) s,
      fun h _ y => hY h y, fun h _ => .of_unset (hU h) hRes⟩,
    fun _ _ _ _ d => currentDequeuedUniqueExcept_of_eq (by rw [hS]) hL hM d, fun _ _ => hM⟩

/-- **The cancel is a run-queue stage**, keeping the link agreement
(`cancelYieldTo_preserves_yieldLinksAgree`). -/
theorem cancelYieldTo_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    RunQueueStage st (cancelYieldTo st tid) :=
  RunQueueStage.of_invExt fun hInv =>
    RunQueueStage.of_objectsAgreeOffYield (cancelYieldTo_objectsAgreeOffYield st tid hInv)
      (cancelYieldTo_scheduler st tid)
      (fun h => cancelYieldTo_preserves_objects_invExt st tid h)
      (by rw [cancelYieldTo_eq_objects]; rfl)
      (fun h y => cancelYieldTo_preserves_yieldLinksAgree st tid h y)
      (fun h => cancelYieldTo_yieldToCodesUnset st tid h)
      (by rw [cancelYieldTo_eq_objects])

/-- The consumed-count read of a context is a run-queue stage: it writes the
count alone, outside the refill view (`updateConsumed_refillView`). -/
theorem updateConsumed_runQueueStage (st : SystemState) (s : SeLe4n.SchedContextId) :
    RunQueueStage st (st.updateSchedContext s SchedContext.updateConsumed) := by
  have hU := updateSchedContext_scheduler st s SchedContext.updateConsumed
  apply RunQueueStage.of_placement
  · exact fun hInv => updateSchedContext_preserves_objects_invExt _ _ _ hInv
  · rw [hU]
  · rw [hU]
  · intro hInv x
    exact congrArg (Option.map TCB.placement) (updateSchedContext_getTcb? st s _ hInv x)
  · exact fun hInv => StateMono.of_getTcb (updateSchedContext_getTcb? st s _ hInv)
  · exact TableReferenceFrame.updateSchedContext st s _
  · exact fun hInv => .updateSchedContext st s _ hInv (fun _ => ⟨rfl, rfl, rfl⟩)
  · exact fun hInv => .updateSchedContext st s _ hInv (fun sc => by simp)
  · exact fun hInv => Kernel.YieldLinksKept.updateSchedContext st s _ hInv (fun _ => rfl)
  · rw [hU]
  · exact congrArg MachineState.residentCode (updateSchedContext_machine st s _)

/-- **`setConsumed` is a run-queue stage**: the count read off the context, then
the thread's two return registers. -/
theorem setConsumed_runQueueStage (st : SystemState) (s : SeLe4n.SchedContextId)
    (t : SeLe4n.ThreadId) : RunQueueStage st (setConsumed st s t) := by
  unfold setConsumed
  split
  · exact (updateConsumed_runQueueStage st s).trans (RunQueueStage.updateTcb _ t (fun _ _ => rfl))
  · exact .refl st

/-- WS-ZA ZA6.9: the Consumed invocation is a run-queue stage that closes as an
entry — it opens no scheduling point. -/
theorem schedContextConsumedOnCore_runQueueEntryStage {s : SeLe4n.SchedContextId}
    {c : Concurrency.CoreId} {st st' : SystemState}
    (h : schedContextConsumedOnCore s c st = .ok st') : RunQueueEntryStage st st' := by
  obtain ⟨caller, -, rfl⟩ := schedContextConsumedOnCore_ok h
  exact (setConsumed_runQueueStage st s caller).entry

/-- **The completion is a run-queue stage**: `setConsumed`, then the cancel. -/
theorem completeYieldTo_runQueueStage (st : SystemState) (y : SeLe4n.ThreadId) :
    RunQueueStage st (completeYieldTo st y) := by
  unfold completeYieldTo
  split
  · split
    · exact .refl st
    · exact (setConsumed_runQueueStage _ _ _).trans (cancelYieldTo_runQueueStage _ _)
  · exact .refl st

/-- The context's end of the cancel is a run-queue stage. -/
theorem cancelYieldFrom_runQueueStage (st : SystemState) (s : SeLe4n.SchedContextId) :
    RunQueueStage st (cancelYieldFrom st s) :=
  RunQueueStage.of_invExt fun hInv =>
    RunQueueStage.of_objectsAgreeOffYield (cancelYieldFrom_objectsAgreeOffYield st s hInv)
      (cancelYieldFrom_scheduler st s)
      (fun h => cancelYieldFrom_preserves_objects_invExt st s h)
      (by rw [cancelYieldFrom_eq_objects]; rfl)
      (fun h y => cancelYieldFrom_preserves_yieldLinksAgree st s h y)
      (fun h => cancelYieldFrom_yieldToCodesUnset st s h)
      (by rw [cancelYieldFrom_eq_objects])

theorem completeYieldFrom_runQueueStage (st : SystemState) (s : SeLe4n.SchedContextId) :
    RunQueueStage st (completeYieldFrom st s) := by
  unfold completeYieldFrom
  split
  · split
    · exact .refl st
    · exact (setConsumed_runQueueStage _ _ _).trans (cancelYieldFrom_runQueueStage _ _)
  · exact .refl st

-- ============================================================================
-- The yield operations write threads and contexts alone
-- ============================================================================

/-- **A step that writes threads and contexts alone**: every slot is unchanged,
or holds a thread before and after, or a context before and after.  Every other
object kind reads back as it was, both ways. -/
def writesTcbScOnly (st' st : SystemState) : Prop :=
  ∀ x : SeLe4n.ObjId, st'.objects[x]? = st.objects[x]? ∨
    (∃ a b, st.objects[x]? = some (.tcb a) ∧ st'.objects[x]? = some (.tcb b)) ∨
    (∃ a b, st.objects[x]? = some (.schedContext a) ∧ st'.objects[x]? = some (.schedContext b))

namespace writesTcbScOnly

theorem refl (st : SystemState) : writesTcbScOnly st st := fun _ => Or.inl rfl

theorem trans {a b c : SystemState} (h₂ : writesTcbScOnly c b) (h₁ : writesTcbScOnly b a) :
    writesTcbScOnly c a := fun x => by
  rcases h₁ x with e1 | ⟨p, q, e1, f1⟩ | ⟨p, q, e1, f1⟩ <;>
  rcases h₂ x with e2 | ⟨r, u, e2, f2⟩ | ⟨r, u, e2, f2⟩
  · exact Or.inl (e2.trans e1)
  · exact Or.inr (Or.inl ⟨r, u, e1.symm.trans e2, f2⟩)
  · exact Or.inr (Or.inr ⟨r, u, e1.symm.trans e2, f2⟩)
  · exact Or.inr (Or.inl ⟨p, q, e1, e2.trans f1⟩)
  · exact Or.inr (Or.inl ⟨p, u, e1, f2⟩)
  · have h := f1.symm.trans e2; simp at h
  · exact Or.inr (Or.inr ⟨p, q, e1, e2.trans f1⟩)
  · have h := f1.symm.trans e2; simp at h
  · exact Or.inr (Or.inr ⟨p, u, e1, f2⟩)

/-- A notification the post-state holds was one in the pre-state. -/
theorem notification_backward {st' st : SystemState} (h : writesTcbScOnly st' st)
    {x : SeLe4n.ObjId} {n : Notification} (hx : st'.objects[x]? = some (.notification n)) :
    st.objects[x]? = some (.notification n) := by
  rcases h x with e | ⟨_, _, _, f⟩ | ⟨_, _, _, f⟩
  · exact e ▸ hx
  · rw [f] at hx; cases hx
  · rw [f] at hx; cases hx

end writesTcbScOnly

theorem updateTcb_writesTcbScOnly (st : SystemState) (tid : SeLe4n.ThreadId) (g : TCB → TCB)
    (hInv : st.objects.invExt) : writesTcbScOnly (st.updateTcb tid g) st := fun k => by
  by_cases hk : tid.toObjId = k
  · subst hk
    cases hT : st.getTcb? tid with
    | none => exact Or.inl (by rw [updateTcb_eq_self_of_none hT])
    | some t =>
      rw [updateTcb_eq_of_some hT]
      have e : (st.objects.insert tid.toObjId (.tcb (g t)))[tid.toObjId]? = some (.tcb (g t)) :=
        RobinHood.RHTable.getElem?_insert_self st.objects _ _ hInv
      exact Or.inr (Or.inl ⟨t, g t, (getTcb?_eq_some_iff _ _ _).mp hT, e⟩)
  · exact Or.inl (updateTcb_objects_ne _ _ _ _ hk hInv)

theorem updateSchedContext_writesTcbScOnly (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (hInv : st.objects.invExt) :
    writesTcbScOnly (st.updateSchedContext s g) st := fun k => by
  by_cases hk : s.toObjId = k
  · subst hk
    cases hS : st.getSchedContext? s with
    | none => exact Or.inl (by rw [updateSchedContext_eq_self_of_none hS])
    | some sc =>
      rw [updateSchedContext_eq_of_some hS]
      have e : (st.objects.insert s.toObjId (.schedContext (g sc)))[s.toObjId]? =
          some (.schedContext (g sc)) :=
        RobinHood.RHTable.getElem?_insert_self st.objects _ _ hInv
      exact Or.inr (Or.inr ⟨sc, g sc, (getSchedContext?_eq_some_iff _ _ _).mp hS, e⟩)
  · exact Or.inl (updateSchedContext_objects_ne _ _ _ _ hk hInv)

theorem cancelYieldTo_writesTcbScOnly (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : writesTcbScOnly (cancelYieldTo st tid) st := by
  unfold cancelYieldTo
  split
  · split
    · exact .refl st
    · exact (updateTcb_writesTcbScOnly _ _ _
        (updateSchedContext_preserves_objects_invExt _ _ _ hInv)).trans
        (updateSchedContext_writesTcbScOnly _ _ _ hInv)
  · exact .refl st

theorem setConsumed_writesTcbScOnly (st : SystemState) (s : SeLe4n.SchedContextId)
    (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) : writesTcbScOnly (setConsumed st s t) st := by
  unfold setConsumed
  split
  · exact (updateTcb_writesTcbScOnly _ _ _
      (updateSchedContext_preserves_objects_invExt _ _ _ hInv)).trans
      (updateSchedContext_writesTcbScOnly _ _ _ hInv)
  · exact .refl st

theorem completeYieldTo_writesTcbScOnly (st : SystemState) (y : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : writesTcbScOnly (completeYieldTo st y) st := by
  unfold completeYieldTo
  split
  · split
    · exact .refl st
    · exact (cancelYieldTo_writesTcbScOnly _ _
        (setConsumed_preserves_objects_invExt _ _ _ hInv)).trans
        (setConsumed_writesTcbScOnly _ _ _ hInv)
  · exact .refl st

theorem cancelYieldFrom_writesTcbScOnly (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : writesTcbScOnly (cancelYieldFrom st s) st := by
  unfold cancelYieldFrom
  split
  · split
    · exact .refl st
    · exact (updateTcb_writesTcbScOnly _ _ _
        (updateSchedContext_preserves_objects_invExt _ _ _ hInv)).trans
        (updateSchedContext_writesTcbScOnly _ _ _ hInv)
  · exact .refl st

theorem completeYieldFrom_writesTcbScOnly (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : writesTcbScOnly (completeYieldFrom st s) st := by
  unfold completeYieldFrom
  split
  · split
    · exact .refl st
    · exact (cancelYieldFrom_writesTcbScOnly _ _
        (setConsumed_preserves_objects_invExt _ _ _ hInv)).trans
        (setConsumed_writesTcbScOnly _ _ _ hInv)
  · exact .refl st

end SystemState

end SeLe4n.Model
