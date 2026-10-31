/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.SchedContext.ReleaseLinks
import SeLe4n.Kernel.SchedContext.Invariant.Defs
import SeLe4n.Kernel.SchedContext.YieldLinkInvariant

/-! # The refill state every transition keeps

WS-ZA ZA6.4: the two kernel-wide facts about scheduling contexts' refills,
carried by every kernel transition the way the release queues' agreement is
(`RunQueueLinkStage.refills`):

- `schedContextsWellFormed`: every context is well formed
  (`schedContextWellFormed`), its refills among them conserved
  (`refillsConserved`: the head and the pending refills hold the budget once);
- `releaseNoRefillStranded`: every bound context whose head is used up and
  holds a pending refill is on a release queue at that refill's time.

Both read a context only through its **refill view** (`SchedContext.refillView`):
its budget, period, remaining budget, period start, refills and whether a thread
is bound.  A step that keeps every slot's refill view and every release queue's
entries keeps both (`refillsSound_of_agree`); a step that writes the refills
proves it of its write.  A third fact keeps the binds placeable:
`releaseQueuedBound`, every queued context bound, so the context a bind takes
is on no queue and its placement lands. -/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-ZA ZA6.4: the fields of a context its refill invariants read — the
budget, the period, the remaining budget and period start, the refills, and
whether a thread is bound — with every other field erased. -/
def SchedContext.refillView (sc : SchedContext) : SchedContext :=
  { scId := ⟨0⟩
    budget := sc.budget
    period := sc.period
    priority := ⟨0⟩
    deadline := ⟨0⟩
    domain := ⟨0⟩
    budgetRemaining := sc.budgetRemaining
    periodStart := sc.periodStart
    refillHeadPresent := sc.refillHeadPresent
    refillHeadAmount := sc.refillHeadAmount
    refillHeadEligibleAt := sc.refillHeadEligibleAt
    refillTailCount := sc.refillTailCount
    refillSlot1Amount := sc.refillSlot1Amount
    refillSlot1EligibleAt := sc.refillSlot1EligibleAt
    refillSlot2Amount := sc.refillSlot2Amount
    refillSlot2EligibleAt := sc.refillSlot2EligibleAt
    refillSlot3Amount := sc.refillSlot3Amount
    refillSlot3EligibleAt := sc.refillSlot3EligibleAt
    refillSlot4Amount := sc.refillSlot4Amount
    refillSlot4EligibleAt := sc.refillSlot4EligibleAt
    refillSlot5Amount := sc.refillSlot5Amount
    refillSlot5EligibleAt := sc.refillSlot5EligibleAt
    refillSlot6Amount := sc.refillSlot6Amount
    refillSlot6EligibleAt := sc.refillSlot6EligibleAt
    refillSlot7Amount := sc.refillSlot7Amount
    refillSlot7EligibleAt := sc.refillSlot7EligibleAt
    boundThreadCode := min sc.boundThreadCode 1 }

/-- WS-ZA ZA6.4: a context the retype creates is well formed: no budget, no
refills, the default period. -/
theorem schedContextWellFormed_empty (scId : SeLe4n.SchedContextId) :
    schedContextWellFormed (SchedContext.empty scId) := by
  unfold schedContextWellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide | (simp [SchedContext.empty, SchedContext.wellFormed, budgetWithinBounds,
    replenishmentListWellFormed, replenishmentAmountsBounded, refillsConserved,
    SchedContext.refillTotal, SchedContext.refillsFit, Budget.zero, sumReplenishments,
    SchedContext.refillSize, maxReplenishments]; try decide)

/-- Well-formedness reads the refill view. -/
theorem schedContextWellFormed_refillView (sc : SchedContext) :
    schedContextWellFormed sc.refillView ↔ schedContextWellFormed sc := Iff.rfl

/-- A context's place reads the refill view. -/
theorem SchedContext.releaseKey?_refillView (sc : SchedContext) :
    sc.refillView.releaseKey? = sc.releaseKey? := rfl

/-- Whether a thread is bound reads the refill view. -/
theorem SchedContext.boundThread_isSome_refillView (sc : SchedContext) :
    sc.refillView.boundThread.isSome = sc.boundThread.isSome := by
  unfold SchedContext.refillView SchedContext.boundThread
  rcases sc.boundThreadCode with _ | k
  · rfl
  · simp [SeLe4n.ThreadId.ofOptCode]

/-- A context's place while bound reads the refill view. -/
theorem SchedContext.boundReleaseKey?_refillView (sc : SchedContext) :
    sc.refillView.boundReleaseKey? = sc.boundReleaseKey? := by
  unfold SchedContext.boundReleaseKey?
  rw [SchedContext.boundThread_isSome_refillView, SchedContext.releaseKey?_refillView]


/-- WS-ZA ZA6.5: the consumed time is outside the refill view: adding to it
leaves the view as it was, so no refill invariant reads it. -/
@[simp] theorem SchedContext.addConsumed_refillView (sc : SchedContext) (t : Nat) :
    (sc.addConsumed t).refillView = sc.refillView := rfl

/-- WS-ZA ZA6.5: and so is its read (`SchedContext.updateConsumed`). -/
@[simp] theorem SchedContext.updateConsumed_refillView (sc : SchedContext) :
    sc.updateConsumed.refillView = sc.refillView := rfl

/-- WS-ZA ZA6.5: the read writes nothing the refill operations keep either. -/
@[simp] theorem SchedContext.updateConsumed_refillsErased (sc : SchedContext) :
    sc.updateConsumed.refillsErased = sc.refillsErased := rfl

/-- WS-ZA ZA6.5: the charge's refill view is the refill charge's alone: the time
it adds to the consumed count is outside it. -/
theorem SchedContext.chargeBudget_refillView (sc : SchedContext) (start usage now : Nat) :
    (sc.chargeBudget start usage now).refillView =
      (((sc.refillUnblockCheck start).refillBudgetCheck usage).releaseReadyHead now).refillView :=
  rfl

/-- A slot's refill view: a context's, none for any other object or an empty
slot. -/
def objRefillView : Option KernelObject → Option SchedContext
  | some (.schedContext sc) => some sc.refillView
  | _ => none

/-- WS-ZA ZA6.4 (moved below the scheduler's bundle, which reads it): every
context in the store is well formed (`schedContextWellFormed`). -/
def schedContextsWellFormed (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (sc : SchedContext),
    st.objects[oid]? = some (.schedContext sc) →
    schedContextWellFormed sc

/-- WS-ZA ZA6.4: every context in the post-state was in the pre-state with the
same refill view: each slot's view is kept, or the slot holds no context any more.
A step that writes no context's refills and creates none keeps the views. -/
def RefillViewsKept (st' st : SystemState) : Prop :=
  ∀ (k : SeLe4n.ObjId) (v : SchedContext),
    objRefillView st'.objects[k]? = some v → objRefillView st.objects[k]? = some v

/-- A slot's view is its context's, read by the context's identifier. -/
theorem objRefillView_eq_getSchedContext? (st : SystemState) (k : SeLe4n.ObjId) :
    objRefillView st.objects[k]? =
      (st.getSchedContext? (SeLe4n.SchedContextId.ofObjId k)).map SchedContext.refillView := by
  unfold SystemState.getSchedContext?
  rw [SeLe4n.SchedContextId.toObjId_ofObjId]
  rcases st.objects[k]? with _ | o
  · rfl
  · cases o <;> rfl

/-- WS-ZA ZA6.5: a slot's refill view is kept when its context's consumed time
is added to or read. -/
theorem objRefillView_addConsumed (sc : SchedContext) (t : Nat) :
    objRefillView (some (.schedContext (sc.addConsumed t))) =
      objRefillView (some (.schedContext sc)) := rfl

theorem objRefillView_updateConsumed (sc : SchedContext) :
    objRefillView (some (.schedContext sc.updateConsumed)) =
      objRefillView (some (.schedContext sc)) := rfl

namespace RefillViewsKept

theorem refl (st : SystemState) : RefillViewsKept st st := fun _ _ h => h

theorem trans {a b d : SystemState} (h₁ : RefillViewsKept a b) (h₂ : RefillViewsKept b d) :
    RefillViewsKept a d := fun k v h => h₂ k v (h₁ k v h)

/-- Equal views are kept. -/
theorem of_eq {st st' : SystemState}
    (h : ∀ k : SeLe4n.ObjId, objRefillView st'.objects[k]? = objRefillView st.objects[k]?) :
    RefillViewsKept st' st := fun k _ e => (h k) ▸ e

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    RefillViewsKept st' st := .of_eq fun k => by rw [h]

/-- Two states whose every context reads alike in view keep the views. -/
theorem of_getSchedContext? {st st' : SystemState}
    (h : ∀ s, (st'.getSchedContext? s).map SchedContext.refillView =
      (st.getSchedContext? s).map SchedContext.refillView) : RefillViewsKept st' st :=
  .of_eq fun k => by rw [objRefillView_eq_getSchedContext?, objRefillView_eq_getSchedContext?]; exact h _

/-- Two states whose every context reads alike keep the views. -/
theorem of_getSchedContext?_eq {st st' : SystemState}
    (h : ∀ s, st'.getSchedContext? s = st.getSchedContext? s) : RefillViewsKept st' st :=
  .of_getSchedContext? fun s => by rw [h s]

/-- Two stores agreeing up to a rewrite that keeps every object's refill view
keep the views. -/
theorem of_map {st st' : SystemState} (g : KernelObject → KernelObject)
    (hg : ∀ o, objRefillView (some (g o)) = objRefillView (some o))
    (h : ∀ k : SeLe4n.ObjId, (st'.objects[k]?).map g = (st.objects[k]?).map g) :
    RefillViewsKept st' st :=
  .of_eq fun k => by
    have e := h k
    revert e
    cases st'.objects[k]? <;> cases st.objects[k]? <;> intro e
    · rfl
    · cases e
    · cases e
    · rename_i a b
      simp only [Option.map_some, Option.some.injEq] at e
      rw [← hg a, e, hg b]

/-- An insert whose object gives its slot's refill view keeps the views. -/
theorem insert {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k o)
    (h : objRefillView (some o) = objRefillView st.objects[k]?) : RefillViewsKept st' st :=
  .of_eq fun x => by
    rw [hO]
    by_cases hx : x = k
    · subst hx
      have e : (st.objects.insert x o)[x]? = some o :=
        RobinHood.RHTable.getElem?_insert_self st.objects x o hInv
      rw [e]; exact h
    · have e : (st.objects.insert k o)[x]? = st.objects[x]? :=
        RobinHood.RHTable.getElem?_insert_ne st.objects k x o
          (by intro h'; exact hx (eq_of_beq h').symm) hInv
      rw [e]

/-- A step whose every post-state context was in the pre-state, unchanged,
keeps the views. -/
theorem of_schedContexts_backward {st st' : SystemState}
    (hB : ∀ (oid : SeLe4n.ObjId) (sc : SchedContext),
      st'.objects[oid]? = some (.schedContext sc) → st.objects[oid]? = some (.schedContext sc)) :
    RefillViewsKept st' st := fun k v h => by
  revert h
  cases e : st'.objects[k]? with
  | none => intro h; cases h
  | some o =>
    cases o <;> intro h <;> simp only [objRefillView, reduceCtorEq] at h
    rw [hB k _ e]; exact h

/-- A store whose object gives its slot's refill view keeps the views. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hS : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (h : objRefillView (some o) = objRefillView st.objects[k]?) : RefillViewsKept st' st := by
  unfold SeLe4n.Model.storeObject at hS; cases hS
  exact .insert hInv rfl h

/-- A context write that keeps the context's view keeps the views. -/
theorem mapSchedContextInPlace (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (hg : ∀ sc, (g sc).refillView = sc.refillView) :
    RefillViewsKept (st.mapSchedContextInPlace s g) st := by
  refine .of_getSchedContext? fun y => ?_
  by_cases hy : y = s
  · subst hy
    rw [SystemState.mapSchedContextInPlace_getSchedContext?_self, Option.map_map]
    cases st.getSchedContext? y with
    | none => rfl
    | some sc => simp only [Option.map_some, Function.comp, hg]
  · rw [SystemState.mapSchedContextInPlace_getSchedContext?_ne _ _ _ hy]


/-- Each context of the post-state is one of the pre-state's in view. -/
theorem getSchedContext? {st st' : SystemState} (h : RefillViewsKept st' st)
    {s : SeLe4n.SchedContextId} {a : SchedContext} (ha : st'.getSchedContext? s = some a) :
    ∃ b, st.getSchedContext? s = some b ∧ b.refillView = a.refillView := by
  have e := h s.toObjId a.refillView (by
    rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp ha]; rfl)
  unfold SystemState.getSchedContext?
  revert e
  rcases st.objects[s.toObjId]? with _ | o
  · intro e; cases e
  · cases o <;> intro e <;> simp only [objRefillView, reduceCtorEq, Option.some.injEq] at e
    exact ⟨_, rfl, e⟩

/-- A context update keeping the context's refill view keeps the views. -/
theorem updateSchedContext (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (hInv : st.objects.invExt)
    (hg : ∀ sc, (g sc).refillView = sc.refillView) :
    RefillViewsKept (st.updateSchedContext s g) st := by
  refine .of_getSchedContext? fun y => ?_
  by_cases hy : s.toObjId = y.toObjId
  · have := SeLe4n.SchedContextId.toObjId_injective _ _ hy
    subst this
    rw [SystemState.updateSchedContext_getSchedContext?_self _ _ _ hInv, Option.map_map]
    cases st.getSchedContext? s with
    | none => rfl
    | some sc => simp only [Option.map_some, Function.comp, hg]
  · rw [SystemState.updateSchedContext_getSchedContext?_ne _ _ _ hInv _ hy]

/-- A write to the release fields alone keeps every context's refill view. -/
theorem of_agreeOffReleaseLinks {st st' : SystemState}
    (h : SystemState.objectsAgreeOffReleaseLinks st' st) : RefillViewsKept st' st :=
  .of_map KernelObject.withoutRelease (fun o => by cases o <;> rfl) h

end RefillViewsKept

/-- WS-ZA ZA6.6: a write to the release fields alone keeps every slot's yield
codes. -/
theorem YieldLinksKept.of_agreeOffReleaseLinks {st st' : SystemState}
    (h : SystemState.objectsAgreeOffReleaseLinks st' st) : YieldLinksKept st' st :=
  .of_map KernelObject.withoutRelease (fun o => by cases o <;> rfl) h

/-- **Every context well formed, read through the views.** -/
theorem schedContextsWellFormed_of_kept {st st' : SystemState} (hK : RefillViewsKept st' st)
    (h : schedContextsWellFormed st) : schedContextsWellFormed st' := by
  intro oid sc hsc
  have e := hK oid sc.refillView (by rw [hsc]; rfl)
  revert e
  rcases hk : st.objects[oid]? with _ | o
  · intro e; cases e
  · cases o <;> intro e <;> simp only [objRefillView, reduceCtorEq, Option.some.injEq] at e
    rename_i sc₀
    rw [← schedContextWellFormed_refillView, ← e, schedContextWellFormed_refillView]
    exact h oid sc₀ hk

/-- **No refill stranded, read through the views and the queues' entries.** -/
theorem releaseNoRefillStranded_of_kept {st st' : SystemState} (hK : RefillViewsKept st' st)
    (hQ : ∀ c, (st'.scheduler.replenishQueueOnCore c).entries =
      (st.scheduler.replenishQueueOnCore c).entries)
    (h : st.releaseNoRefillStranded) : st'.releaseNoRefillStranded := by
  intro s t hk
  cases e' : st'.getSchedContext? s with
  | none => rw [e'] at hk; cases hk
  | some a =>
    rw [e'] at hk
    obtain ⟨b, hb, hv⟩ := hK.getSchedContext? e'
    have hk' : (st.getSchedContext? s).bind SchedContext.boundReleaseKey? = some t := by
      rw [hb]
      simp only [Option.bind_some] at hk ⊢
      rw [← SchedContext.boundReleaseKey?_refillView, hv, SchedContext.boundReleaseKey?_refillView]
      exact hk
    obtain ⟨c, hc⟩ := h s t hk'
    exact ⟨c, by rw [hQ c]; exact hc⟩


end SeLe4n.Kernel

namespace SeLe4n.Model.SystemState

open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-ZA ZA6.4: **every queued context is bound** (seL4-MCS's release queue
holds threads, so a context is on it only through the thread it is bound to):
each entry of every core's release queue names a context a thread holds.  The
unbind takes the context off its queue (`purgeReplenishment`), so a bind finds
the context it binds on no queue. -/
def releaseQueuedBound (st : SystemState) : Prop :=
  ∀ c e, e ∈ (st.scheduler.replenishQueueOnCore c).entries →
    ∃ sc, st.getSchedContext? e.1 = some sc ∧ sc.boundThread.isSome = true

/-- A context on a refined release queue is in the store. -/
theorem releaseQueueRefined_getSchedContext?_of_mem {st : SystemState}
    (hR : st.releaseQueueRefined) {c : CoreId} {e : SeLe4n.SchedContextId × Nat}
    (he : e ∈ (st.scheduler.replenishQueueOnCore c).entries) :
    ∃ sc, st.getSchedContext? e.1 = some sc := by
  have hq := ((hR c).queued e.1).mpr (List.mem_map_of_mem he)
  unfold releaseQueuedOn at hq
  cases h : st.getSchedContext? e.1 with
  | none => rw [h] at hq; cases hq
  | some sc => exact ⟨sc, rfl⟩

/-- **Every queued context bound, read through the views and the entries.** -/
theorem releaseQueuedBound_of_kept {st st' : SystemState} (hK : RefillViewsKept st' st)
    (hQ : ∀ c, (st'.scheduler.replenishQueueOnCore c).entries =
      (st.scheduler.replenishQueueOnCore c).entries)
    (hR' : st'.releaseQueueRefined) (h : st.releaseQueuedBound) : st'.releaseQueuedBound := by
  intro c e he
  obtain ⟨a, ha⟩ := releaseQueueRefined_getSchedContext?_of_mem hR' he
  obtain ⟨b, hb, hv⟩ := hK.getSchedContext? ha
  obtain ⟨sc, hsc, hB⟩ := h c e (by rw [← hQ c]; exact he)
  rw [hb] at hsc; cases hsc
  refine ⟨a, ha, ?_⟩
  rw [← SchedContext.boundThread_isSome_refillView, ← hv, SchedContext.boundThread_isSome_refillView]
  exact hB

/-- **An unbound context is on no release queue**, so every core is free to
queue it. -/
theorem releaseCoreOf_eq_none_of_unbound {st : SystemState} (hR : st.releaseQueueRefined)
    {s : SeLe4n.SchedContextId}
    (hB : ∀ c e, e ∈ (st.scheduler.replenishQueueOnCore c).entries → e.1 = s →
      ∃ sc, st.getSchedContext? e.1 = some sc ∧ sc.boundThread.isSome = true)
    {sc : SchedContext}
    (hSc : st.getSchedContext? s = some sc) (hU : sc.boundThread.isSome = false) :
    st.releaseCoreOf s = none := by
  cases e : st.releaseCoreOf s with
  | none => rfl
  | some d =>
    have hm := ((hR d).queued s).mp (releaseQueuedOn_of_releaseCoreOf e)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    obtain ⟨sc', hsc', hb'⟩ := hB d x hx rfl
    rw [hSc] at hsc'; cases hsc'
    rw [hU] at hb'; cases hb'

/-- An unbound context is free on every core. -/
theorem releaseFreeFor_of_unbound {st : SystemState} (hR : st.releaseQueueRefined)
    {s : SeLe4n.SchedContextId}
    (hB : ∀ c e, e ∈ (st.scheduler.replenishQueueOnCore c).entries → e.1 = s →
      ∃ sc, st.getSchedContext? e.1 = some sc ∧ sc.boundThread.isSome = true)
    {sc : SchedContext}
    (hSc : st.getSchedContext? s = some sc) (hU : sc.boundThread.isSome = false) (c : CoreId) :
    st.releaseFreeFor c s = true := by
  unfold releaseFreeFor; rw [releaseCoreOf_eq_none_of_unbound hR hB hSc hU]


/-- A context of a state whose contexts are all well formed is well formed. -/
theorem schedContextWellFormed_of_get {st : SystemState} (h : schedContextsWellFormed st)
    {s : SeLe4n.SchedContextId} {sc : SchedContext} (hs : st.getSchedContext? s = some sc) :
    schedContextWellFormed sc :=
  h s.toObjId sc ((getSchedContext?_eq_some_iff _ _ _).mp hs)

/-- WS-ZA ZA6.4: **the refill state is sound** — every context well formed
(`schedContextsWellFormed`, its refills conserved among the rest), no bound
context's pending refill stranded off the release queues
(`releaseNoRefillStranded`), and every queued context bound
(`releaseQueuedBound`). -/
def refillsSound (st : SystemState) : Prop :=
  schedContextsWellFormed st ∧ st.releaseNoRefillStranded ∧ st.releaseQueuedBound

/-- WS-ZA ZA6.4: **the refill state is sound off the contexts `S`** — the three
facts of `refillsSound` for every context not in `S` and every entry naming one.
A step that writes context `s`'s refills before it re-places `s` keeps it off
any `S` holding `s`; every other step keeps it off every `S`, which is what a
run-queue stage carries (`RunQueueLinkStage.refills`), so a write to `s` composes
with the stages around it and is closed once at its end
(`refillsSoundExcept_close`). -/
def refillsSoundExcept (S : SeLe4n.SchedContextId → Prop) (st : SystemState) : Prop :=
  (∀ s sc, ¬ S s → st.getSchedContext? s = some sc → schedContextWellFormed sc) ∧
  (∀ s t, ¬ S s → (st.getSchedContext? s).bind SchedContext.boundReleaseKey? = some t →
    ∃ c, (s, t) ∈ (st.scheduler.replenishQueueOnCore c).entries) ∧
  (∀ c e, ¬ S e.1 → e ∈ (st.scheduler.replenishQueueOnCore c).entries →
    ∃ sc, st.getSchedContext? e.1 = some sc ∧ sc.boundThread.isSome = true)

/-- Sound is sound off no context. -/
theorem refillsSound_iff_except (st : SystemState) :
    st.refillsSound ↔ st.refillsSoundExcept (fun _ => False) := by
  constructor
  · rintro ⟨hW, hN, hB⟩
    exact ⟨fun s sc _ h => schedContextWellFormed_of_get hW h, fun s t _ h => hN s t h,
      fun c e _ h => hB c e h⟩
  · rintro ⟨hW, hN, hB⟩
    refine ⟨fun oid sc h => ?_, fun s t h => hN s t (fun h => h) h, fun c e h => hB c e id h⟩
    exact hW (SeLe4n.SchedContextId.ofObjId oid) sc id
      ((getSchedContext?_eq_some_iff _ _ _).mpr (by rw [SeLe4n.SchedContextId.toObjId_ofObjId]; exact h))

theorem refillsSoundExcept.mono {S S' : SeLe4n.SchedContextId → Prop} {st : SystemState}
    (hS : ∀ x, S x → S' x) (h : st.refillsSoundExcept S) : st.refillsSoundExcept S' :=
  ⟨fun s sc hs => h.1 s sc (fun h' => hs (hS s h')),
   fun s t hs => h.2.1 s t (fun h' => hs (hS s h')),
   fun c e hs => h.2.2 c e (fun h' => hs (hS e.1 h'))⟩

/-- WS-ZA ZA6.4: **every context off `P` kept**: each context of the
post-state not in `P` was in the pre-state with the same refill view, and each
entry naming a context not in `P` is on a queue exactly when it was.  A frame
keeps every context (`P` empty); a write to context `s` keeps every other
(`P = (· = s)`). -/
def RefillsKeptOff (P : SeLe4n.SchedContextId → Prop) (st' st : SystemState) : Prop :=
  (∀ s' a, ¬ P s' → st'.getSchedContext? s' = some a →
    ∃ b, st.getSchedContext? s' = some b ∧ b.refillView = a.refillView) ∧
  (∀ c e, ¬ P e.1 → (e ∈ (st'.scheduler.replenishQueueOnCore c).entries ↔
    e ∈ (st.scheduler.replenishQueueOnCore c).entries))

/-- **Keeping the contexts off `P` keeps the state sound off any `S ⊇ P`.** -/
theorem refillsSoundExcept_of_keptOff {P S : SeLe4n.SchedContextId → Prop} {st st' : SystemState}
    (hK : RefillsKeptOff P st' st) (hPS : ∀ x, P x → S x) (hR' : st'.releaseQueueRefined)
    (h : st.refillsSoundExcept S) : st'.refillsSoundExcept S := by
  obtain ⟨hW, hN, hQB⟩ := h
  refine ⟨fun s a hs ha => ?_, fun s t hs hk => ?_, fun c e hs he => ?_⟩
  · obtain ⟨b, hb, hv⟩ := hK.1 s a (fun h => hs (hPS s h)) ha
    rw [← schedContextWellFormed_refillView, ← hv, schedContextWellFormed_refillView]
    exact hW s b hs hb
  · cases e' : st'.getSchedContext? s with
    | none => rw [e'] at hk; cases hk
    | some a =>
      rw [e'] at hk
      obtain ⟨b, hb, hv⟩ := hK.1 s a (fun h => hs (hPS s h)) e'
      have hk' : (st.getSchedContext? s).bind SchedContext.boundReleaseKey? = some t := by
        rw [hb]
        simp only [Option.bind_some] at hk ⊢
        rw [← SchedContext.boundReleaseKey?_refillView, hv,
          SchedContext.boundReleaseKey?_refillView]
        exact hk
      obtain ⟨c, hc⟩ := hN s t hs hk'
      exact ⟨c, (hK.2 c (s, t) (fun h => hs (hPS s h))).mpr hc⟩
  · have hp : ¬ P e.1 := fun h => hs (hPS _ h)
    obtain ⟨a, ha⟩ := releaseQueueRefined_getSchedContext?_of_mem hR' he
    obtain ⟨b, hb, hv⟩ := hK.1 e.1 a hp ha
    obtain ⟨sc, hsc, hbd⟩ := hQB c e hs ((hK.2 c e hp).mp he)
    rw [hb] at hsc; cases hsc
    refine ⟨a, ha, ?_⟩
    rw [← SchedContext.boundThread_isSome_refillView, ← hv,
      SchedContext.boundThread_isSome_refillView]
    exact hbd

/-- **Closing a write to `s`**: sound off `S` and `s`, with `s` well formed,
queued at its place while bound and pending, and queued only while bound, is
sound off `S`. -/
theorem refillsSoundExcept_close {S : SeLe4n.SchedContextId → Prop} {s : SeLe4n.SchedContextId}
    {st : SystemState} (h : st.refillsSoundExcept (fun x => S x ∨ x = s))
    (hWF : ∀ a, st.getSchedContext? s = some a → schedContextWellFormed a)
    (hS : ∀ t, (st.getSchedContext? s).bind SchedContext.boundReleaseKey? = some t →
      ∃ c, (s, t) ∈ (st.scheduler.replenishQueueOnCore c).entries)
    (hB : ∀ c e, e ∈ (st.scheduler.replenishQueueOnCore c).entries → e.1 = s →
      ∃ a, st.getSchedContext? e.1 = some a ∧ a.boundThread.isSome = true) :
    st.refillsSoundExcept S := by
  refine ⟨fun x sc hx hsc => ?_, fun x t hx hk => ?_, fun c e hx he => ?_⟩
  · by_cases e : x = s
    · subst e; exact hWF sc hsc
    · exact h.1 x sc (fun h' => h'.elim hx e) hsc
  · by_cases e : x = s
    · subst e; exact hS t hk
    · exact h.2.1 x t (fun h' => h'.elim hx e) hk
  · by_cases e' : e.1 = s
    · exact hB c e he e'
    · exact h.2.2 c e (fun h' => h'.elim hx e') he

namespace RefillsKeptOff

theorem refl (P : SeLe4n.SchedContextId → Prop) (st : SystemState) : RefillsKeptOff P st st :=
  ⟨fun _ a _ h => ⟨a, h, rfl⟩, fun _ _ _ => Iff.rfl⟩

theorem trans {P : SeLe4n.SchedContextId → Prop} {a b d : SystemState}
    (h₁ : RefillsKeptOff P a b) (h₂ : RefillsKeptOff P b d) : RefillsKeptOff P a d :=
  ⟨fun s' x hs hx => by
    obtain ⟨y, hy, hv⟩ := h₁.1 s' x hs hx
    obtain ⟨z, hz, hv'⟩ := h₂.1 s' y hs hy
    exact ⟨z, hz, hv'.trans hv⟩,
   fun c e he => (h₁.2 c e he).trans (h₂.2 c e he)⟩

theorem mono {P P' : SeLe4n.SchedContextId → Prop} {st st' : SystemState}
    (hP : ∀ x, P x → P' x) (h : RefillsKeptOff P st' st) : RefillsKeptOff P' st' st :=
  ⟨fun s' a hs => h.1 s' a (fun h' => hs (hP s' h')), fun c e he => h.2 c e (fun h' => he (hP _ h'))⟩

/-- A step keeping every refill view and every queue's entries. -/
theorem of_kept {P : SeLe4n.SchedContextId → Prop} {st st' : SystemState}
    (hK : RefillViewsKept st' st)
    (hQ : ∀ c, (st'.scheduler.replenishQueueOnCore c).entries =
      (st.scheduler.replenishQueueOnCore c).entries) : RefillsKeptOff P st' st :=
  ⟨fun _ _ _ ha => hK.getSchedContext? ha, fun c e _ => by rw [hQ c]⟩

/-- A step keeping every refill view and the release-queue slots. -/
theorem of_releaseSlots {P : SeLe4n.SchedContextId → Prop} {st st' : SystemState}
    (hK : RefillViewsKept st' st)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots) : RefillsKeptOff P st' st :=
  .of_kept hK fun c => by
    simp only [SchedulerState.releaseSlots, Prod.mk.injEq] at hS
    unfold SchedulerState.replenishQueueOnCore; rw [hS.1]

/-- A step writing only `s`'s slot and no queue. -/
theorem of_insert {s : SeLe4n.SchedContextId} {st st' : SystemState} {o : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert s.toObjId o)
    (hQ : ∀ c, (st'.scheduler.replenishQueueOnCore c).entries =
      (st.scheduler.replenishQueueOnCore c).entries) :
    RefillsKeptOff (· = s) st' st := by
  refine ⟨fun s' a hs ha => ⟨a, ?_, rfl⟩, fun c e _ => by rw [hQ c]⟩
  have hne : s'.toObjId ≠ s.toObjId := fun h => hs (SeLe4n.SchedContextId.toObjId_injective _ _ h)
  rw [getSchedContext?_eq_some_iff] at ha ⊢
  rw [hO] at ha
  have e : (st.objects.insert s.toObjId o)[s'.toObjId]? = st.objects[s'.toObjId]? :=
    RobinHood.RHTable.getElem?_insert_ne st.objects s.toObjId s'.toObjId o
      (by intro h'; exact hne (eq_of_beq h').symm) hInv
  rw [e] at ha; exact ha

/-- A context update of `s` alone, writing no queue. -/
theorem updateSchedContext (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (hInv : st.objects.invExt) :
    RefillsKeptOff (· = s) (st.updateSchedContext s g) st := by
  refine ⟨fun s' a hs ha => ⟨a, ?_, rfl⟩, fun c e _ => by
    rw [SystemState.updateSchedContext_scheduler]⟩
  have hne : s.toObjId ≠ s'.toObjId := fun h =>
    hs (SeLe4n.SchedContextId.toObjId_injective _ _ h).symm
  rwa [SystemState.updateSchedContext_getSchedContext?_ne _ _ _ hInv _ hne] at ha

/-- A write to the release fields alone, keeping the entries off `P`. -/
theorem of_releaseWrite {P : SeLe4n.SchedContextId → Prop} {st st' : SystemState}
    (hA : objectsAgreeOffReleaseLinks st' st)
    (hQ : ∀ c e, ¬ P e.1 → (e ∈ (st'.scheduler.replenishQueueOnCore c).entries ↔
      e ∈ (st.scheduler.replenishQueueOnCore c).entries)) : RefillsKeptOff P st' st :=
  ⟨fun _ _ _ ha => (RefillViewsKept.of_agreeOffReleaseLinks hA).getSchedContext? ha, hQ⟩

end RefillsKeptOff

/-- **A step keeping every refill view and every queue's entries keeps the
state sound off every `S`.** -/
theorem refillsSoundExcept_of_kept {S : SeLe4n.SchedContextId → Prop} {st st' : SystemState}
    (hK : RefillViewsKept st' st)
    (hQ : ∀ c, (st'.scheduler.replenishQueueOnCore c).entries =
      (st.scheduler.replenishQueueOnCore c).entries)
    (hR' : st'.releaseQueueRefined) (h : st.refillsSoundExcept S) : st'.refillsSoundExcept S :=
  refillsSoundExcept_of_keptOff (P := fun _ => False) (.of_kept hK hQ) (fun _ h => h.elim) hR' h

/-- ...and sound. -/
theorem refillsSound_of_kept {st st' : SystemState} (hK : RefillViewsKept st' st)
    (hQ : ∀ c, (st'.scheduler.replenishQueueOnCore c).entries =
      (st.scheduler.replenishQueueOnCore c).entries)
    (hR' : st'.releaseQueueRefined) (h : st.refillsSound) : st'.refillsSound :=
  (refillsSound_iff_except _).mpr
    (refillsSoundExcept_of_kept hK hQ hR' ((refillsSound_iff_except _).mp h))

/-- A context kept in view from a state sound off `S`, not in `S`, is well
formed. -/
theorem refillsSoundExcept.wellFormed_of_view {S : SeLe4n.SchedContextId → Prop}
    {st : SystemState} (h : st.refillsSoundExcept S) {s : SeLe4n.SchedContextId}
    (hs : ¬ S s) {a b : SchedContext} (hb : st.getSchedContext? s = some b)
    (hv : b.refillView = a.refillView) : schedContextWellFormed a := by
  rw [← schedContextWellFormed_refillView, ← hv, schedContextWellFormed_refillView]
  exact h.1 s b hs hb

/-- **Closing a write that leaves `s` unbound and off every queue**: `s` reads
as a well-formed unbound context `u` in view, and no entry names it. -/
theorem refillsSoundExcept_close_unbound {S : SeLe4n.SchedContextId → Prop}
    {s : SeLe4n.SchedContextId} {st : SystemState} {u : SchedContext}
    (h : st.refillsSoundExcept (fun x => S x ∨ x = s))
    (hView : ∀ a, st.getSchedContext? s = some a → a.refillView = u.refillView)
    (hU : u.boundThread.isSome = false) (hWF : schedContextWellFormed u)
    (hN : ∀ c e, e ∈ (st.scheduler.replenishQueueOnCore c).entries → e.1 ≠ s) :
    st.refillsSoundExcept S := by
  refine refillsSoundExcept_close h (fun a ha => ?_) (fun t ht => ?_)
    (fun c e he hs => absurd hs (hN c e he))
  · rw [← schedContextWellFormed_refillView, hView a ha, schedContextWellFormed_refillView]
    exact hWF
  · cases e : st.getSchedContext? s with
    | none => rw [e] at ht; cases ht
    | some a =>
      rw [e] at ht
      simp only [Option.bind_some] at ht
      rw [← SchedContext.boundReleaseKey?_refillView, hView a e,
        SchedContext.boundReleaseKey?_refillView] at ht
      unfold SchedContext.boundReleaseKey? at ht
      rw [hU] at ht; cases ht

/-- On refined queues, a context linked on no queue is named by no entry. -/
theorem not_mem_entries_of_not_queued {st : SystemState} (hR : st.releaseQueueRefined)
    {s : SeLe4n.SchedContextId} (hq : st.releaseQueuedAnywhere s = false) (c : CoreId)
    (e : SeLe4n.SchedContextId × Nat) (he : e ∈ (st.scheduler.replenishQueueOnCore c).entries) :
    e.1 ≠ s := by
  intro hs
  have hm := ((hR c).queued s).mpr (by rw [← hs]; exact List.mem_map_of_mem he)
  have hn := (releaseQueuedAnywhere_eq_false_iff _ s).mp hq c
  rw [releaseQueuedOn_eq, hn] at hm; cases hm

/-- **Placing `s` keeps every other context's entries.** -/
theorem releasePlace_mem_iff_of_ne (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (c' : CoreId) (e : SeLe4n.SchedContextId × Nat) (he : e.1 ≠ s) :
    e ∈ ((st.releasePlace c s).scheduler.replenishQueueOnCore c').entries ↔
      e ∈ (st.scheduler.replenishQueueOnCore c').entries := by
  constructor
  · intro m
    rcases releasePlace_entries_cases st c s c' e m with h | ⟨h, -⟩
    · exact h
    · exact absurd h he
  · intro m
    by_cases hc : c' = c
    · subst hc
      cases hf : st.releaseFreeFor c' s with
      | false => rw [releasePlace_of_not_free hf]; exact m
      | true =>
        have hm : e ∈ ((st.scheduler.replenishQueueOnCore c').remove s).entries := by
          obtain ⟨a, b⟩ := e
          exact List.mem_filter.mpr ⟨m, by simpa using he⟩
        rw [releasePlace_replenishQueueOnCore_self hf]
        cases st.releaseKeyOf s with
        | none => exact hm
        | some t => exact SeLe4n.Kernel.subset_insertSorted _ s t e hm
    · rw [releasePlace_replenishQueueOnCore_ne st c s c' hc]; exact m

/-- The placement of `s` keeps every context but `s`. -/
theorem RefillsKeptOff.releasePlace (st : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId) :
    RefillsKeptOff (· = s) (st.releasePlace c s) st :=
  .of_releaseWrite (releasePlace_agree st c s) fun c' e he => releasePlace_mem_iff_of_ne st c s c' e he

/-- WS-ZA ZA6.4: **placing a context keeps the state sound off `S`** when the
context is in `S`, or is bound or has nothing pending: its entry, if any, is at
its place (`releasePlace_mem`), and it is bound. -/
theorem releasePlace_refillsSoundExcept {S : SeLe4n.SchedContextId → Prop} {st : SystemState}
    (hR : st.releaseQueueRefined) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hB : ¬ S s → ∀ sc, st.getSchedContext? s = some sc → sc.releaseKey? ≠ none →
      sc.boundThread.isSome = true)
    (h : st.refillsSoundExcept S) : (st.releasePlace c s).refillsSoundExcept S := by
  have hR' := releasePlace_refined hR c s
  have hKo := RefillsKeptOff.releasePlace st c s
  by_cases hs : S s
  · exact refillsSoundExcept_of_keptOff hKo (fun x hx => hx ▸ hs) hR' h
  have hK := RefillViewsKept.of_agreeOffReleaseLinks (releasePlace_agree st c s)
  refine refillsSoundExcept_close
    (refillsSoundExcept_of_keptOff hKo (fun x hx => Or.inr hx) hR' (h.mono fun x hx => Or.inl hx))
    ?_ ?_ ?_
  · intro a ha
    obtain ⟨b, hb, hv⟩ := hK.getSchedContext? ha
    exact h.wellFormed_of_view hs hb hv
  · intro t ht
    cases hf : st.releaseFreeFor c s with
    | false =>
      rw [releasePlace_of_not_free hf] at ht ⊢
      exact h.2.1 s t hs ht
    | true =>
      refine ⟨c, releasePlace_mem hf ?_⟩
      cases e' : (st.releasePlace c s).getSchedContext? s with
      | none => rw [e'] at ht; cases ht
      | some a =>
        rw [e'] at ht
        obtain ⟨b, hb, hv⟩ := hK.getSchedContext? e'
        simp only [Option.bind_some, SchedContext.boundReleaseKey?] at ht
        split at ht
        · refine releaseKeyOf_eq_some.mpr ⟨b, hb, ?_⟩
          rw [← SchedContext.releaseKey?_refillView, hv, SchedContext.releaseKey?_refillView]
          exact ht
        · cases ht
  · intro c' e he hes
    obtain ⟨a, ha⟩ := releaseQueueRefined_getSchedContext?_of_mem hR' he
    obtain ⟨b, hb, hv⟩ := hK.getSchedContext? ha
    refine ⟨a, ha, ?_⟩
    rw [← SchedContext.boundThread_isSome_refillView, ← hv,
      SchedContext.boundThread_isSome_refillView]
    rcases releasePlace_entries_cases st c s c' e he with m | ⟨-, hk⟩
    · obtain ⟨sc, hsc, hbd⟩ := h.2.2 c' e (hes ▸ hs) m
      rw [hb] at hsc; cases hsc; exact hbd
    · rw [hes] at hb
      obtain ⟨sc, hsc, hk'⟩ := releaseKeyOf_eq_some.mp hk
      rw [hb] at hsc; cases hsc
      exact hB hs _ hb (by rw [hk']; exact fun h => by cases h)

/-- On refined queues, a context no entry names has no release core: it is
free for every core. -/
theorem releaseFreeFor_of_not_named {st : SystemState} (hR : st.releaseQueueRefined)
    {s : SeLe4n.SchedContextId}
    (hN : ∀ c e, e ∈ (st.scheduler.replenishQueueOnCore c).entries → e.1 ≠ s) (c : CoreId) :
    st.releaseFreeFor c s = true := by
  unfold releaseFreeFor
  cases e : st.releaseCoreOf s with
  | none => rfl
  | some d =>
    have hm := ((hR d).queued s).mp (releaseQueuedOn_of_releaseCoreOf e)
    obtain ⟨x, hx, hxs⟩ := List.mem_map.mp hm
    exact absurd hxs (hN d x hx)

/-- WS-ZA ZA6.4: **placing a written context closes the write**: a state sound
off `S` and `s`, in which `s` is free for core `c`, well formed, bound while it
has a place, and bound wherever it is queued, is sound off `S` once `s` is
placed on `c`. -/
theorem releasePlace_close {S : SeLe4n.SchedContextId → Prop} {st : SystemState}
    (hR : st.releaseQueueRefined) (c : CoreId) (s : SeLe4n.SchedContextId)
    (hFree : st.releaseFreeFor c s = true)
    (hWF : ∀ a, st.getSchedContext? s = some a → schedContextWellFormed a)
    (hB : ∀ sc, st.getSchedContext? s = some sc → sc.releaseKey? ≠ none →
      sc.boundThread.isSome = true)
    (hQ : ∀ c e, e ∈ (st.scheduler.replenishQueueOnCore c).entries → e.1 = s →
      ∃ a, st.getSchedContext? e.1 = some a ∧ a.boundThread.isSome = true)
    (h : st.refillsSoundExcept (fun x => S x ∨ x = s)) : (st.releasePlace c s).refillsSoundExcept S := by
  have hR' := releasePlace_refined hR c s
  have hKo := RefillsKeptOff.releasePlace st c s
  have hK := RefillViewsKept.of_agreeOffReleaseLinks (releasePlace_agree st c s)
  refine refillsSoundExcept_close (refillsSoundExcept_of_keptOff hKo (fun x hx => Or.inr hx) hR' h)
    ?_ ?_ ?_
  · intro a ha
    obtain ⟨b, hb, hv⟩ := hK.getSchedContext? ha
    rw [← schedContextWellFormed_refillView, ← hv, schedContextWellFormed_refillView]
    exact hWF b hb
  · intro t ht
    refine ⟨c, releasePlace_mem hFree ?_⟩
    cases e' : (st.releasePlace c s).getSchedContext? s with
    | none => rw [e'] at ht; cases ht
    | some a =>
      rw [e'] at ht
      obtain ⟨b, hb, hv⟩ := hK.getSchedContext? e'
      simp only [Option.bind_some, SchedContext.boundReleaseKey?] at ht
      split at ht
      · refine releaseKeyOf_eq_some.mpr ⟨b, hb, ?_⟩
        rw [← SchedContext.releaseKey?_refillView, hv, SchedContext.releaseKey?_refillView]
        exact ht
      · cases ht
  · intro c' e he hes
    obtain ⟨a, ha⟩ := releaseQueueRefined_getSchedContext?_of_mem hR' he
    obtain ⟨b, hb, hv⟩ := hK.getSchedContext? ha
    refine ⟨a, ha, ?_⟩
    rw [← SchedContext.boundThread_isSome_refillView, ← hv,
      SchedContext.boundThread_isSome_refillView]
    rcases releasePlace_entries_cases st c s c' e he with m | ⟨-, hk⟩
    · obtain ⟨sc, hsc, hbd⟩ := hQ c' e m hes
      rw [hb] at hsc; cases hsc; exact hbd
    · rw [hes] at hb
      obtain ⟨sc, hsc, hk'⟩ := releaseKeyOf_eq_some.mp hk
      rw [hb] at hsc; cases hsc
      exact hB _ hb (by rw [hk']; exact fun h => by cases h)

/-- WS-ZA ZA6.4: **what a placement needs, read through a frame**: a state `Y`
naming `s` on no queue and holding `s` as a well-formed bound `u`, and a state
`X` keeping every context and queue of `Y`, give `releasePlace_close`'s four
facts at `X`. -/
theorem closePlace_facts {X Y : SystemState} {s : SeLe4n.SchedContextId} {u : SchedContext}
    (hYs : Y.getSchedContext? s = some u)
    (hN : ∀ c e, e ∈ (Y.scheduler.replenishQueueOnCore c).entries → e.1 ≠ s)
    (hWF : schedContextWellFormed u)
    (hB : u.boundThread.isSome = true) (hK : RefillsKeptOff (fun _ => False) X Y)
    (hXR : X.releaseQueueRefined) (c : CoreId) :
    X.releaseFreeFor c s = true ∧
      (∀ a, X.getSchedContext? s = some a → schedContextWellFormed a) ∧
      (∀ sc, X.getSchedContext? s = some sc → sc.releaseKey? ≠ none →
        sc.boundThread.isSome = true) ∧
      (∀ c e, e ∈ (X.scheduler.replenishQueueOnCore c).entries → e.1 = s →
        ∃ a, X.getSchedContext? e.1 = some a ∧ a.boundThread.isSome = true) := by
  have hNX : ∀ c e, e ∈ (X.scheduler.replenishQueueOnCore c).entries → e.1 ≠ s :=
    fun c e he => hN c e ((hK.2 c e id).mp he)
  have hView : ∀ a, X.getSchedContext? s = some a → a.refillView = u.refillView := by
    intro a ha
    obtain ⟨b, hb, hv⟩ := hK.1 s a id ha
    rw [hYs] at hb; cases hb; exact hv.symm
  refine ⟨releaseFreeFor_of_not_named hXR hNX c, fun a ha => ?_, fun a ha _ => ?_,
    fun c e he hes => absurd hes (hNX c e he)⟩
  · rw [← schedContextWellFormed_refillView, hView a ha, schedContextWellFormed_refillView]
    exact hWF
  · rw [← SchedContext.boundThread_isSome_refillView, hView a ha,
      SchedContext.boundThread_isSome_refillView]
    exact hB

/-- **A release-only write that loses no entry and makes none up keeps the
state sound off every `S`**: every context keeps its refill view, every entry
is still on some core's queue unless its context is no longer bound and pending
at its time, and every entry was on some core's queue before — a move between
queues (the migration), or a removal of a context with nothing pending. -/
theorem refillsSoundExcept_of_releaseMove {S : SeLe4n.SchedContextId → Prop}
    {st st' : SystemState} (hK : RefillViewsKept st' st)
    (hIn : ∀ c e, ¬ S e.1 → e ∈ (st.scheduler.replenishQueueOnCore c).entries →
      (∃ c', e ∈ (st'.scheduler.replenishQueueOnCore c').entries) ∨
        (st.getSchedContext? e.1).bind SchedContext.boundReleaseKey? ≠ some e.2)
    (hOut : ∀ c' e, e ∈ (st'.scheduler.replenishQueueOnCore c').entries →
      ∃ c, e ∈ (st.scheduler.replenishQueueOnCore c).entries)
    (hR' : st'.releaseQueueRefined) (h : st.refillsSoundExcept S) :
    st'.refillsSoundExcept S := by
  obtain ⟨hW, hN, hQB⟩ := h
  refine ⟨fun s a hs ha => ?_, fun s t hs hk => ?_, fun c' e hs he => ?_⟩
  · obtain ⟨b, hb, hv⟩ := hK.getSchedContext? ha
    rw [← schedContextWellFormed_refillView, ← hv, schedContextWellFormed_refillView]
    exact hW s b hs hb
  · cases e' : st'.getSchedContext? s with
    | none => rw [e'] at hk; cases hk
    | some a =>
      rw [e'] at hk
      obtain ⟨b, hb, hv⟩ := hK.getSchedContext? e'
      have hk' : (st.getSchedContext? s).bind SchedContext.boundReleaseKey? = some t := by
        rw [hb]
        simp only [Option.bind_some] at hk ⊢
        rw [← SchedContext.boundReleaseKey?_refillView, hv,
          SchedContext.boundReleaseKey?_refillView]
        exact hk
      obtain ⟨c, hc⟩ := hN s t hs hk'
      rcases hIn c (s, t) hs hc with h1 | h2
      · exact h1
      · exact absurd hk' h2
  · obtain ⟨a, ha⟩ := releaseQueueRefined_getSchedContext?_of_mem hR' he
    obtain ⟨b, hb, hv⟩ := hK.getSchedContext? ha
    obtain ⟨c, hc⟩ := hOut c' e he
    obtain ⟨sc, hsc, hbd⟩ := hQB c e hs hc
    rw [hb] at hsc; cases hsc
    refine ⟨a, ha, ?_⟩
    rw [← SchedContext.boundThread_isSome_refillView, ← hv,
      SchedContext.boundThread_isSome_refillView]
    exact hbd

/-- WS-ZA ZA6.4: **closing a write that leaves context `s` with no place**: a
write to `s` that keeps every queue, leaves `s` well formed, holding budget in
its head (no release key) and bound to the thread it was, is sound off `S` —
the tick's charge that does not use the head up. -/
theorem refillsSoundExcept_close_keyless {S : SeLe4n.SchedContextId → Prop}
    {s : SeLe4n.SchedContextId} {st0 st : SystemState} {a b : SchedContext}
    (hQ : ∀ c, (st.scheduler.replenishQueueOnCore c).entries =
      (st0.scheduler.replenishQueueOnCore c).entries)
    (hs : ¬ S s) (h0 : st0.refillsSoundExcept S)
    (h : st.refillsSoundExcept (fun x => S x ∨ x = s))
    (ha : st.getSchedContext? s = some a) (hb : st0.getSchedContext? s = some b)
    (hWF : schedContextWellFormed a) (hK : a.releaseKey? = none)
    (hBT : a.boundThread = b.boundThread) : st.refillsSoundExcept S := by
  refine refillsSoundExcept_close h (fun a' ha' => ?_) (fun t ht => ?_) (fun c e he hes => ?_)
  · rw [ha] at ha'; cases ha'; exact hWF
  · rw [ha] at ht
    simp only [Option.bind_some, SchedContext.boundReleaseKey?, hK] at ht
    split at ht <;> cases ht
  · obtain ⟨sc0, h1, h2⟩ := h0.2.2 c e (by rw [hes]; exact hs) (by rw [← hQ c]; exact he)
    rw [hes] at h1 ⊢
    rw [hb] at h1; cases h1
    exact ⟨a, ha, by rw [hBT]; exact h2⟩

/-- WS-ZA ZA6.4: **what a placement needs, at a context bound and free**: a
state `X` holding `s` as a well-formed bound `u`, with `s` free for core `c`,
gives `releasePlace_close`'s four facts — the charge's postpone, whose context
is the charged thread's, linked on its home core or on none. -/
theorem closePlace_facts_bound {X : SystemState} {s : SeLe4n.SchedContextId} {u : SchedContext}
    {c : CoreId} (hXs : X.getSchedContext? s = some u) (hWF : schedContextWellFormed u)
    (hB : u.boundThread.isSome = true) (hFree : X.releaseFreeFor c s = true) :
    X.releaseFreeFor c s = true ∧
      (∀ a, X.getSchedContext? s = some a → schedContextWellFormed a) ∧
      (∀ sc, X.getSchedContext? s = some sc → sc.releaseKey? ≠ none →
        sc.boundThread.isSome = true) ∧
      (∀ c e, e ∈ (X.scheduler.replenishQueueOnCore c).entries → e.1 = s →
        ∃ a, X.getSchedContext? e.1 = some a ∧ a.boundThread.isSome = true) :=
  ⟨hFree, fun a ha => by rw [hXs] at ha; cases ha; exact hWF,
    fun a ha _ => by rw [hXs] at ha; cases ha; exact hB,
    fun _ e _ hes => ⟨u, by rw [hes]; exact hXs, hB⟩⟩

/-- WS-ZA ZA6.4: **a state whose release queues are all empty is sound** when
each of its contexts is well formed and bound to no thread: no bound context has
a refill pending, and nothing is queued — the empty state and the boot states. -/
theorem refillsSound_of_empty {st : SystemState}
    (hQ : ∀ c, (st.scheduler.replenishQueueOnCore c).entries = [])
    (hW : ∀ (oid : SeLe4n.ObjId) (sc : SchedContext), st.objects[oid]? = some (.schedContext sc) →
      schedContextWellFormed sc ∧ sc.boundThread = none) : st.refillsSound := by
  refine ⟨fun oid sc h => (hW oid sc h).1, fun s t hk => ?_,
    fun c e he => by rw [hQ c] at he; cases he⟩
  cases e : st.getSchedContext? s with
  | none => rw [e] at hk; cases hk
  | some sc =>
    rw [e] at hk
    have hb := (hW _ sc ((getSchedContext?_eq_some_iff _ _ _).mp e)).2
    simp [SchedContext.boundReleaseKey?, hb] at hk

/-- The empty state is sound: it holds no context and queues nothing. -/
theorem default_refillsSound : (default : SystemState).refillsSound :=
  refillsSound_of_empty
    (fun c => by
      show ((default : SchedulerState).replenishQueueOnCore c).entries = []
      rw [(default_state_perCoreInitialized c).2.2.1]; rfl)
    (fun oid sc h => by
      have h0 : (default : SystemState).objects[oid]? = none := by
        simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
      rw [h0] at h; cases h)

/-- A step that writes neither the objects nor the scheduler keeps the state
sound: the soundness reads the contexts and the release queues alone. -/
theorem refillsSound_of_objects_scheduler_eq {st st' : SystemState}
    (hO : st'.objects = st.objects) (hS : st'.scheduler = st.scheduler)
    (h : st.refillsSound) : st'.refillsSound := by
  obtain ⟨hW, hN, hB⟩ := h
  have hG : ∀ s, st'.getSchedContext? s = st.getSchedContext? s := fun s => by
    unfold getSchedContext?; rw [hO]
  refine ⟨fun oid sc e => hW oid sc (hO ▸ e), fun s t hk => ?_, fun c e he => ?_⟩
  · rw [hG] at hk
    obtain ⟨c, hc⟩ := hN s t hk
    exact ⟨c, by rw [hS]; exact hc⟩
  · rw [hS] at he
    obtain ⟨sc, h1, h2⟩ := hB c e he
    exact ⟨sc, by rw [hG]; exact h1, h2⟩

end SeLe4n.Model.SystemState
