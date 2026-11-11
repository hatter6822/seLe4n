-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Operations
import SeLe4n.Kernel.SchedContext.ReplenishAffinity
import SeLe4n.Kernel.Scheduler.SchedulerLinkFrame
import SeLe4n.Kernel.IPC.Operations.Endpoint
import SeLe4n.Kernel.RobinHood.Invariant.InPlaceCommute

/-!
# Configure through a core's scheduling control

WS-ZA ZA6.4.  seL4-MCS's `invokeSchedControl_ConfigureFlags` configures a
scheduling context on the core whose `SchedControl` capability was invoked.  A
context bound to a thread homed on another core moves to the control's core with
its thread: seL4 takes the thread off its old core's release and ready queues,
stalls the core running it (`remoteTCBStall`), sets the context's core and
migrates the thread there (`migrateTCB`), then refills and resumes it on the new
core.

This kernel homes a context with its bound thread (`determineTargetCore`), so the
move is the thread's affinity change to the control's core
(`setThreadCpuAffinityWithMigration`: the remote stall and vacate of a thread
running on its old home, `vacateForAffinityChange`; its release entry and run
queue entry moved with it; a vacated thread queued on its new home,
`requeueVacatedOnNewHome`), and then the configure runs on the new home
(`schedContextConfigure`), whose release placement and resume tail
(`configureResumeBound`) land there.

**Check before writing.**  Every check is read before the move writes anything:
the parameters, the context, admission (which reads only the contexts' budgets
and periods, which the move does not write) and the move's own checks.
`schedControlConfigureAdmitted` and `schedControlConfigurePerform` are the
checks and the writes, and an admitted configure is the perform
(`schedControlConfigure_of_admitted`).
-/

namespace SeLe4n.Kernel.SchedContextOps

open SeLe4n
open SeLe4n.Kernel.Concurrency (bootCoreId)
open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.RobinHood

/-- **The thread a configure through core `core`'s control moves**: the context's
bound thread, when it is homed on another core; `none` when the context is bound
to no thread or its thread is already homed on `core`. -/
@[inline] def schedControlMovedThread? (st : SystemState) (core : Concurrency.CoreId)
    (sc : SchedContext) : Option SeLe4n.ThreadId :=
  match sc.boundThread with
  | some t => if determineTargetCore st t = core then none else some t
  | none => none

/-- **WS-ZA ZA6.4: configure through core `core`'s scheduling control**
(`invokeSchedControl_ConfigureFlags`).  A context whose bound thread is homed on
another core moves to `core` with its thread first, after every check of the
configure and the move is read (see the module docstring); the configure then
runs on the moved state.  A context with no thread to move is configured where
it is. -/
def schedControlConfigure (core : Concurrency.CoreId) (vScId : ValidObjId)
    (budget period priority deadline domain : Nat) : Kernel Unit :=
  fun st =>
    match st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
    | none => schedContextConfigure vScId budget period priority deadline domain st
    | some sc =>
      match schedControlMovedThread? st core sc with
      | none => schedContextConfigure vScId budget period priority deadline domain st
      | some t =>
        match validateSchedContextParams budget period priority deadline domain with
        | .error e => .error e
        | .ok () =>
          if checkAdmission st (configuredSchedContext budget period priority deadline domain
              st.machine.timer (configureKeepsHead st sc budget period) sc) (some vScId.val) then
            match setThreadCpuAffinityWithMigration st t (some core) core with
            | .error e => .error e
            | .ok (stMoved, _) =>
              schedContextConfigure vScId budget period priority deadline domain stMoved
          else .error .resourceExhausted

/-- **A successful configure through a control is a configure where the context
is, or the move of its thread to the control's core and then a configure
there.**  Every proof about the arm composes the configure's and the affinity
change's along this. -/
theorem schedControlConfigure_ok_cases {core : Concurrency.CoreId} {vScId : ValidObjId}
    {budget period priority deadline domain : Nat} {st st' : SystemState}
    (h : schedControlConfigure core vScId budget period priority deadline domain st =
      .ok ((), st')) :
    schedContextConfigure vScId budget period priority deadline domain st = .ok ((), st') ∨
      ∃ (sc : SchedContext) (t : SeLe4n.ThreadId) (stMoved : SystemState)
        (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)),
        st.getSchedContext? (SchedContextId.ofObjId vScId.val) = some sc ∧
        sc.boundThread = some t ∧ determineTargetCore st t ≠ core ∧
        setThreadCpuAffinityWithMigration st t (some core) core = .ok (stMoved, sgi) ∧
        schedContextConfigure vScId budget period priority deadline domain stMoved =
          .ok ((), st') := by
  unfold schedControlConfigure at h
  cases hS : st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | none => rw [hS] at h; exact .inl h
  | some sc =>
    rw [hS] at h
    dsimp only at h
    cases hT : schedControlMovedThread? st core sc with
    | none => rw [hT] at h; exact .inl h
    | some t =>
      rw [hT] at h
      dsimp only at h
      have hB : sc.boundThread = some t ∧ determineTargetCore st t ≠ core := by
        unfold schedControlMovedThread? at hT
        cases hb : sc.boundThread with
        | none => rw [hb] at hT; cases hT
        | some t' =>
          rw [hb] at hT
          dsimp only at hT
          split at hT
          · cases hT
          · rename_i hne; cases hT; exact ⟨rfl, hne⟩
      split at h
      · cases h
      · split at h
        · split at h
          · cases h
          · rename_i stMoved sgi hMove
            exact .inr ⟨sc, t, stMoved, sgi, rfl, hB.1, hB.2, hMove, h⟩
        · cases h

-- ============================================================================
-- What the configure's checks read
-- ============================================================================

/-- What `schedContextConfigureAdmitted` reads of an object: its kind, and a
scheduling context's budget and period. -/
@[inline] def configureAdmissionView (o : KernelObject) :
    KernelObjectType × Option (Budget × Period) :=
  (o.objectType, match o with
    | .schedContext sc => some (sc.budget, sc.period)
    | _ => none)

/-- WS-UC UC2: what the configure's checks read of an object table, slot by
slot: each slot's key and what `configureAdmissionView` reads of its object.
The admission sum walks the table's slots, so two tables with one slot view sum
alike — with no invariant on either (`admissionUtilizationFrom_eq_of_slotView`). -/
def admissionSlotView (t : RHTable SeLe4n.ObjId KernelObject) :
    List (Option (SeLe4n.ObjId × (KernelObjectType × Option (Budget × Period)))) :=
  t.slots.toList.map (Option.map fun e => (e.key, configureAdmissionView e.value))

/-- WS-UC UC2: a slot write that keeps what the checks read of the object there
keeps the slot view. -/
theorem admissionSlotView_mapValueAt (t : RHTable SeLe4n.ObjId KernelObject)
    (k : SeLe4n.ObjId) (f : KernelObject → KernelObject)
    (h : ∀ v, t.get? k = some v → configureAdmissionView (f v) = configureAdmissionView v) :
    admissionSlotView (t.mapValueAt k f) = admissionSlotView t := by
  cases hk : t.get? k with
  | none => rw [RHTable.mapValueAt_of_get?_none hk]
  | some v =>
    obtain ⟨e, he, hev⟩ := RHTable.slot_of_get? hk
    unfold admissionSlotView
    rw [RHTable.mapValueAt_slots]
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp only [List.getElem_map, Array.getElem_toList, Array.getElem_modify]
      split
      · next hn =>
        subst hn
        have hlt : t.probe k < t.slots.size := by simpa using h2
        have : t.slots[t.probe k]'hlt = some e := by
          rw [Array.getElem?_eq_getElem hlt] at he
          exact Option.some.inj he
        rw [this]
        simp only [RHEntry.mapValue, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
        rw [hev]; exact h v hk
      · rfl

/-- WS-UC UC2: the admission sum reads the slot view alone. -/
theorem admissionUtilizationFrom_eq_slotView (st : SystemState) (hasEx : Bool)
    (ex : SeLe4n.ObjId) :
    admissionUtilizationFrom st hasEx ex =
      (admissionSlotView st.objects).foldl (fun acc slot =>
        match slot with
        | some (k, (_, some (b, p))) =>
          if hasEx && ex == k then acc else acc + (Bandwidth.mk b.val p.val).utilization
        | _ => acc) 0 := by
  unfold admissionUtilizationFrom admissionSlotView RHTable.fold
  rw [← Array.foldl_toList, List.foldl_map]
  congr 1
  funext acc slot
  cases slot with
  | none => rfl
  | some e =>
    obtain ⟨k, o⟩ := e
    simp only [Option.map_some, admissionStep]
    by_cases hx : (hasEx && ex == k) = true <;>
      cases o <;> simp [hx, configureAdmissionView, SchedContext.utilizationPerMille,
        SchedContext.bandwidth]

/-- WS-UC UC2: two tables with one slot view sum alike. -/
theorem admissionUtilizationFrom_eq_of_slotView {st' st : SystemState}
    (h : admissionSlotView st'.objects = admissionSlotView st.objects) (hasEx : Bool)
    (ex : SeLe4n.ObjId) :
    admissionUtilizationFrom st' hasEx ex = admissionUtilizationFrom st hasEx ex := by
  rw [admissionUtilizationFrom_eq_slotView, admissionUtilizationFrom_eq_slotView, h]

/-- WS-UC UC2: a thread written in its slot keeps the slot view. -/
theorem admissionSlotView_mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) :
    admissionSlotView (st.mapTcbInPlace t g).objects = admissionSlotView st.objects :=
  admissionSlotView_mapValueAt _ _ _ fun v _ => by cases v <;> rfl

/-- WS-UC UC2: a context's release links written in its slot keep the slot view. -/
theorem admissionSlotView_mapSchedContextInPlace (st : SystemState)
    (s : SeLe4n.SchedContextId) (g : SchedContext → SchedContext)
    (hg : ∀ sc, (g sc).budget = sc.budget ∧ (g sc).period = sc.period) :
    admissionSlotView (st.mapSchedContextInPlace s g).objects = admissionSlotView st.objects :=
  admissionSlotView_mapValueAt _ _ _ fun v _ => by
    cases v with
    | schedContext sc =>
      simp only [SystemState.mapSchedContextObject, configureAdmissionView,
        KernelObject.objectType, (hg sc).1, (hg sc).2]
    | _ => rfl

/-! WS-UC UC2: the run-queue and release-queue writes keep the slot view: each
is a chain of slot writes of threads' run links or contexts' release links. -/

section AdmissionSlotView
variable (st : SystemState)

theorem admissionSlotView_updateTcbAtCode (k : Nat) (g : TCB → TCB) :
    admissionSlotView (st.updateTcbAtCode k g).objects = admissionSlotView st.objects := by
  unfold SystemState.updateTcbAtCode; split
  · rfl
  · exact admissionSlotView_mapTcbInPlace _ _ _

theorem admissionSlotView_runAppendLinks (c : Concurrency.CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    admissionSlotView (st.runAppendLinks c t p).objects = admissionSlotView st.objects := by
  unfold SystemState.runAppendLinks
  dsimp only
  rw [admissionSlotView_updateTcbAtCode, admissionSlotView_updateTcbAtCode,
    admissionSlotView_mapTcbInPlace]

theorem admissionSlotView_runUnlinkLinks (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat) :
    admissionSlotView (st.runUnlinkLinks t pv nx bpv bnx).objects =
      admissionSlotView st.objects := by
  unfold SystemState.runUnlinkLinks
  dsimp only
  rw [admissionSlotView_mapTcbInPlace, admissionSlotView_updateTcbAtCode,
    admissionSlotView_updateTcbAtCode, admissionSlotView_updateTcbAtCode,
    admissionSlotView_updateTcbAtCode]

theorem admissionSlotView_runEnqueueAdmitted (c : Concurrency.CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    admissionSlotView (st.runEnqueueAdmitted c t p).objects = admissionSlotView st.objects := by
  unfold SystemState.runEnqueueAdmitted
  dsimp only
  split
  · rfl
  · exact admissionSlotView_runAppendLinks _ _ _ _

theorem admissionSlotView_runEnqueueOnCore (c : Concurrency.CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    admissionSlotView (st.runEnqueueOnCore c t p).objects = admissionSlotView st.objects := by
  unfold SystemState.runEnqueueOnCore; split
  · exact admissionSlotView_runEnqueueAdmitted _ _ _ _
  · rfl

theorem admissionSlotView_runRemoveOnCore (c : Concurrency.CoreId) (t : SeLe4n.ThreadId) :
    admissionSlotView (st.runRemoveOnCore c t).objects = admissionSlotView st.objects := by
  unfold SystemState.runRemoveOnCore
  dsimp only
  split
  · exact admissionSlotView_runUnlinkLinks _ _ _ _ _ _
  · rfl

theorem admissionSlotView_releaseUnlinkOn (c : Concurrency.CoreId) (s : SeLe4n.SchedContextId) :
    admissionSlotView (st.releaseUnlinkOn c s).objects = admissionSlotView st.objects := by
  unfold SystemState.releaseUnlinkOn
  have h1 := admissionSlotView_mapSchedContextInPlace st s SchedContext.leaveRelease
    fun _ => ⟨rfl, rfl⟩
  split
  · dsimp only
    split
    · exact h1
    · exact (admissionSlotView_mapSchedContextInPlace (st.mapSchedContextInPlace s
        SchedContext.leaveRelease) _ (SchedContext.withReleaseNext _) fun _ => ⟨rfl, rfl⟩).trans h1
  · rfl

theorem admissionSlotView_releaseLinkIn (c : Concurrency.CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) :
    admissionSlotView (st.releaseLinkIn c s t).objects = admissionSlotView st.objects := by
  unfold SystemState.releaseLinkIn
  have h1 : ∀ n, admissionSlotView (st.mapSchedContextInPlace s
      (SchedContext.joinRelease c n t)).objects = admissionSlotView st.objects := fun n =>
    admissionSlotView_mapSchedContextInPlace st s (SchedContext.joinRelease c n t)
      fun _ => ⟨rfl, rfl⟩
  dsimp only
  split
  · exact h1 _
  · exact (admissionSlotView_mapSchedContextInPlace (st.mapSchedContextInPlace s
      (SchedContext.joinRelease c _ t)) _ (SchedContext.withReleaseNext _)
      fun _ => ⟨rfl, rfl⟩).trans (h1 _)

theorem admissionSlotView_releaseRemoveOn (c : Concurrency.CoreId) (s : SeLe4n.SchedContextId) :
    admissionSlotView (st.releaseRemoveOn c s).objects = admissionSlotView st.objects :=
  admissionSlotView_releaseUnlinkOn st c s

theorem admissionSlotView_releaseInsertOn (c : Concurrency.CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) :
    admissionSlotView (st.releaseInsertOn c s t).objects = admissionSlotView st.objects := by
  unfold SystemState.releaseInsertOn; split
  · rfl
  · exact admissionSlotView_releaseLinkIn st c s t

theorem admissionSlotView_migrateSchedContextReplenishment (scId : SeLe4n.SchedContextId)
    (fromCore toCore : Concurrency.CoreId) :
    admissionSlotView (migrateSchedContextReplenishment st scId fromCore toCore).objects =
      admissionSlotView st.objects := by
  unfold migrateSchedContextReplenishment
  split
  · rfl
  · dsimp only
    split
    · rw [admissionSlotView_releaseInsertOn, admissionSlotView_releaseRemoveOn]
    · rfl

theorem admissionSlotView_migrateRunQueueOnAffinityChange (tid : SeLe4n.ThreadId)
    (fromCore toCore : Concurrency.CoreId) :
    admissionSlotView (migrateRunQueueOnAffinityChange st tid fromCore toCore).objects =
      admissionSlotView st.objects := by
  unfold migrateRunQueueOnAffinityChange
  split
  · rfl
  · split
    · rfl
    · split
      · dsimp only
        rw [admissionSlotView_runEnqueueAdmitted, admissionSlotView_runRemoveOnCore]
      · rfl

theorem admissionSlotView_requeueVacatedOnNewHome (tid : SeLe4n.ThreadId)
    (newCore : Concurrency.CoreId) (vacated : Bool) :
    admissionSlotView (requeueVacatedOnNewHome st tid newCore vacated).objects =
      admissionSlotView st.objects := by
  unfold requeueVacatedOnNewHome
  split
  · split
    · exact admissionSlotView_runEnqueueOnCore _ _ _ _
    · rfl
  · rfl

end AdmissionSlotView

/-- **A step the configure's checks cannot see**: it writes only the object store
and the scheduler, and keeps every object's kind and every context's budget and
period — read by key, and (WS-UC UC2) slot by slot, as the admission sum walks
the table. -/
structure ConfigureAdmissionFrame (st' st : SystemState) : Prop where
  shape : SystemState.onlyObjectsSchedulerDiffer st' st
  view : ∀ x : SeLe4n.ObjId,
    (st'.objects[x]?).map configureAdmissionView = (st.objects[x]?).map configureAdmissionView
  slots : admissionSlotView st'.objects = admissionSlotView st.objects

namespace ConfigureAdmissionFrame

theorem refl (st : SystemState) : ConfigureAdmissionFrame st st := ⟨.refl st, fun _ => rfl, rfl⟩

theorem trans {a b c : SystemState} (h₂ : ConfigureAdmissionFrame c b)
    (h₁ : ConfigureAdmissionFrame b a) : ConfigureAdmissionFrame c a :=
  ⟨h₂.shape.trans h₁.shape, fun x => (h₂.view x).trans (h₁.view x), h₂.slots.trans h₁.slots⟩

/-- A step holding every object off the scheduler's links is one. -/
theorem of_schedulerLinks {st' st : SystemState} (hS : SystemState.onlyObjectsSchedulerDiffer st' st)
    (hA : SystemState.objectsAgreeOffSchedulerLinks st' st)
    (hSl : admissionSlotView st'.objects = admissionSlotView st.objects) :
    ConfigureAdmissionFrame st' st := by
  refine ⟨hS, fun x => ?_, hSl⟩
  have hx := hA x
  cases e : st.objects[x]? with
  | none =>
    cases e' : st'.objects[x]? with
    | none => rfl
    | some _ => rw [e, e'] at hx; cases hx
  | some o =>
    cases e' : st'.objects[x]? with
    | none => rw [e, e'] at hx; cases hx
    | some o' =>
      rw [e, e'] at hx
      simp only [Option.map_some, Option.some.injEq] at hx ⊢
      cases o <;> cases o' <;>
        simp_all [KernelObject.withoutSchedulerLinks, KernelObject.withoutRunLinks,
          KernelObject.withoutRelease, configureAdmissionView, KernelObject.objectType,
          SchedContext.withoutRelease]

variable {st' st : SystemState} (h : ConfigureAdmissionFrame st' st)
include h


/-- A context's budget and period are read off its slot. -/
theorem getSchedContext?_params (s : SeLe4n.SchedContextId) :
    (st'.getSchedContext? s).map (fun sc => (sc.budget, sc.period)) =
      (st.getSchedContext? s).map (fun sc => (sc.budget, sc.period)) := by
  have hx := h.view s.toObjId
  unfold SystemState.getSchedContext?
  cases e : st.objects[s.toObjId]? with
  | none =>
    cases e' : st'.objects[s.toObjId]? with
    | none => rfl
    | some _ => rw [e, e'] at hx; cases hx
  | some o =>
    cases e' : st'.objects[s.toObjId]? with
    | none => rw [e, e'] at hx; cases hx
    | some o' =>
      rw [e, e'] at hx
      simp only [Option.map_some, Option.some.injEq, configureAdmissionView] at hx
      cases o <;> cases o' <;> simp_all [KernelObject.objectType]

/-- The admission sum reads the contexts' budgets and periods alone, slot by
slot. -/
theorem admissionUtilizationFrom_eq (hasEx : Bool) (ex : SeLe4n.ObjId) :
    admissionUtilizationFrom st' hasEx ex = admissionUtilizationFrom st hasEx ex :=
  admissionUtilizationFrom_eq_of_slotView h.slots hasEx ex

/-- The store check reads the slot's kind. -/
theorem storeLeavesIndexAndTypes_eq (id : SeLe4n.ObjId) (ty : KernelObjectType) :
    storeLeavesIndexAndTypes st' id ty = storeLeavesIndexAndTypes st id ty := by
  have hx := h.view id
  unfold storeLeavesIndexAndTypes storeKeepsKind
  cases e : st.objects[id]? with
  | none =>
    cases e' : st'.objects[id]? with
    | none => rfl
    | some _ => rw [e, e'] at hx; cases hx
  | some o =>
    cases e' : st'.objects[id]? with
    | none => rw [e, e'] at hx; cases hx
    | some o' =>
      rw [e, e'] at hx
      simp only [Option.map_some, Option.some.injEq, configureAdmissionView] at hx
      cases o <;> cases o' <;> simp_all [KernelObject.objectType]

/-- **The configure's checks answer alike across the frame.** -/
theorem schedContextConfigureAdmitted_eq (vScId : ValidObjId)
    (budget period priority deadline domain : Nat) :
    schedContextConfigureAdmitted st' vScId budget period priority deadline domain =
      schedContextConfigureAdmitted st vScId budget period priority deadline domain := by
  unfold schedContextConfigureAdmitted
  cases validateSchedContextParams budget period priority deadline domain with
  | error _ => rfl
  | ok _ =>
    have hp := h.getSchedContext?_params (SchedContextId.ofObjId vScId.val)
    dsimp only
    cases e : st.getSchedContext? (SchedContextId.ofObjId vScId.val) <;>
      cases e' : st'.getSchedContext? (SchedContextId.ofObjId vScId.val) <;>
      rw [e, e'] at hp <;> simp only [Option.map_some, Option.map_none, reduceCtorEq] at hp <;>
      first
      | rfl
      | (dsimp only
         rw [h.admissionUtilizationFrom_eq, h.storeLeavesIndexAndTypes_eq])

end ConfigureAdmissionFrame

namespace ConfigureAdmissionFrame

theorem withScheduler {a b : SystemState} (h : ConfigureAdmissionFrame b a) (s : SchedulerState) :
    ConfigureAdmissionFrame { b with scheduler := s } a :=
  ⟨h.shape.withScheduler s, h.view, h.slots⟩

theorem of_runLinks {st' st : SystemState} (hS : SystemState.onlyObjectsSchedulerDiffer st' st)
    (hA : SystemState.objectsAgreeOffRunLinks st' st)
    (hSl : admissionSlotView st'.objects = admissionSlotView st.objects) :
    ConfigureAdmissionFrame st' st :=
  of_schedulerLinks hS (.of_runLinks hA) hSl

theorem of_releaseOnlyWrite {st' st : SystemState} (hW : SystemState.releaseOnlyWrite st' st)
    (hA : SystemState.objectsAgreeOffReleaseLinks st' st)
    (hSl : admissionSlotView st'.objects = admissionSlotView st.objects) :
    ConfigureAdmissionFrame st' st :=
  of_schedulerLinks hW.1 (.of_releaseLinks hA) hSl

/-- A thread rewritten in its slot, found where it stands, stays a thread, and
every other slot is left. -/
theorem updateTcb_of_findsInPlace {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (f : TCB → TCB) (hT : st.getTcb? tid = some t)
    (hF : st.objects.findsInPlace tid.toObjId = true) :
    ConfigureAdmissionFrame (st.updateTcb tid f) st := by
  refine ⟨by rw [SystemState.updateTcb_eq_of_some hT f]; rfl, fun x => ?view, ?slots⟩
  case slots =>
    rw [SystemState.updateTcb_eq_of_some hT f]
    show admissionSlotView (st.objects.insert tid.toObjId (.tcb (f t))) = _
    rw [RHTable.insert_eq_mapValueAt _ hF]
    refine admissionSlotView_mapValueAt _ _ _ fun v hv => ?_
    have hT' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    rw [show st.objects.get? tid.toObjId = st.objects[tid.toObjId]? from rfl, hT'] at hv
    cases hv; rfl
  case view =>
  by_cases hx : tid.toObjId = x
  · subst hx
    have h1 := updateTcb_getTcb?_self_of_findsInPlace f hT hF
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h1, (SystemState.getTcb?_eq_some_iff _ _ _).mp hT]
    rfl
  · rw [updateTcb_get?_ne_of_findsInPlace f hT hF hx]

end ConfigureAdmissionFrame

/-- The migration of a thread's run-queue entry holds the configure's checks. -/
theorem migrateRunQueueOnAffinityChange_configureAdmissionFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : Concurrency.CoreId) :
    ConfigureAdmissionFrame (migrateRunQueueOnAffinityChange st tid fromCore toCore) st := by
  unfold migrateRunQueueOnAffinityChange
  split
  · exact .refl _
  · split
    · exact .refl _
    · split
      · refine ConfigureAdmissionFrame.withScheduler ?_ _
        refine ConfigureAdmissionFrame.of_runLinks
          ((SystemState.runEnqueueAdmitted_onlyObjectsSchedulerDiffer _ _ _ _).trans
            (SystemState.runRemoveOnCore_onlyObjectsSchedulerDiffer _ _ _))
          ((SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ _ _ _).trans
            (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ _ _))
          (by rw [admissionSlotView_runEnqueueAdmitted, admissionSlotView_runRemoveOnCore])
      · exact .refl _

/-- The vacated thread's requeue holds the configure's checks. -/
theorem requeueVacatedOnNewHome_configureAdmissionFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (newCore : Concurrency.CoreId) (vacated : Bool) :
    ConfigureAdmissionFrame (requeueVacatedOnNewHome st tid newCore vacated) st := by
  refine ConfigureAdmissionFrame.of_runLinks ?_
    (requeueVacatedOnNewHome_objectsAgreeOffRunLinks st tid newCore vacated)
    (admissionSlotView_requeueVacatedOnNewHome st tid newCore vacated)
  unfold requeueVacatedOnNewHome
  split
  · split
    · exact (SystemState.runEnqueueOnCore_onlyObjectsSchedulerDiffer _ _ _ _).withScheduler _
    · exact .refl _
  · exact .refl _

/-- **The affinity change holds the configure's checks**: it writes the
scheduler, the thread's own record (found in its slot) and the scheduler links. -/
theorem setAffinityPerform_configureAdmissionFrame {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} (affinity : Option Concurrency.CoreId) (hT : st.getTcb? tid = some tcb)
    (hF : st.objects.findsInPlace tid.toObjId = true) :
    ConfigureAdmissionFrame (setAffinityPerform st tid affinity) st := by
  unfold setAffinityPerform
  simp only [hT]
  have hV : ConfigureAdmissionFrame (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)) st := by
    unfold vacateForAffinityChange
    split
    · exact (ConfigureAdmissionFrame.refl st).withScheduler _
    · exact .refl _
  have hT0 : (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).getTcb? tid = some tcb := by
    rw [vacateForAffinityChange_getTcb?]; exact hT
  have hF0 : (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).objects.findsInPlace tid.toObjId = true := by
    rw [vacateForAffinityChange_objects]; exact hF
  have h1 := (ConfigureAdmissionFrame.updateTcb_of_findsInPlace
    (fun t => { t with cpuAffinity := affinity }) hT0 hF0).trans hV
  refine (requeueVacatedOnNewHome_configureAdmissionFrame _ _ _ _).trans
    ((migrateRunQueueOnAffinityChange_configureAdmissionFrame _ _ _ _).trans ?_)
  split
  · exact (ConfigureAdmissionFrame.of_releaseOnlyWrite
      (migrateSchedContextReplenishment_releaseOnlyWrite _ _ _ _)
      (migrateSchedContextReplenishment_agree _ _ _ _)
      (admissionSlotView_migrateSchedContextReplenishment _ _ _ _)).trans h1
  · exact h1

/-- An admitted affinity change succeeds, and its state is the perform's (the
form `setThreadCpuAffinityOnCore_of_admitted` states for a valid thread id). -/
theorem setThreadCpuAffinityWithMigration_of_admitted (st : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option Concurrency.CoreId) (executingCore : Concurrency.CoreId)
    (h : setAffinityAdmitted st tid affinity = true) :
    ∃ sgi, setThreadCpuAffinityWithMigration st tid affinity executingCore =
      .ok (setAffinityPerform st tid affinity, sgi) := by
  unfold setAffinityAdmitted at h
  cases hT : st.getTcb? tid with
  | none => simp [hT] at h
  | some tcb =>
    simp only [hT, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hF, hD⟩, hI⟩, hR⟩ := h
    have hD' : (affinity.any (fun c => c.val ≥ st.machine.declaredCoreCount)) = false := by
      cases affinity <;> simp_all
    have hT0 : (vacateForAffinityChange st tid (determineTargetCore st tid)
        (affinity.getD bootCoreId)).getTcb? tid = some tcb := by
      rw [vacateForAffinityChange_getTcb?]; exact hT
    unfold setThreadCpuAffinityWithMigration setThreadCpuAffinity
    simp only [hT, hD', hI, hR, Bool.false_eq_true, ↓reduceIte,
      SystemState.getTcbWitnessed?_eq_some hT0]
    rw [SystemState.rewriteObject_tcb_eq_updateTcb hT0 (fun t => { t with cpuAffinity := affinity })]
    unfold setAffinityPerform
    simp only [hT]
    exact ⟨_, rfl⟩

-- ============================================================================
-- The checks and the writes
-- ============================================================================

/-- **WS-ZA ZA6.4: the configure through core `core`'s control, its checks**:
the configure's (`schedContextConfigureAdmitted`) and, when the context's thread
moves, the move's (`setAffinityAdmitted`), all read off the state handed in. -/
@[inline] def schedControlConfigureAdmitted (st : SystemState) (core : Concurrency.CoreId)
    (vScId : ValidObjId) (budget period priority deadline domain : Nat) : Bool :=
  schedContextConfigureAdmitted st vScId budget period priority deadline domain &&
    match st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
    | some sc =>
      match schedControlMovedThread? st core sc with
      | some t => setAffinityAdmitted st t (some core)
      | none => true
    | none => true

/-- **...and its writes**: the move, when the thread moves, and then the
configure's writes on the moved state. -/
@[inline] def schedControlConfigurePerform (st : SystemState) (core : Concurrency.CoreId)
    (vScId : ValidObjId) (budget period priority deadline domain : Nat) : SystemState :=
  match st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | some sc =>
    match schedControlMovedThread? st core sc with
    | some t => schedContextConfigurePerform (setAffinityPerform st t (some core)) vScId budget
        period priority deadline domain
    | none => schedContextConfigurePerform st vScId budget period priority deadline domain
  | none => st

/-- **An admitted configure through a control succeeds, and its state is the
perform's.** -/
theorem schedControlConfigure_of_admitted (st : SystemState) (core : Concurrency.CoreId)
    (vScId : ValidObjId) (budget period priority deadline domain : Nat)
    (h : schedControlConfigureAdmitted st core vScId budget period priority deadline domain = true) :
    schedControlConfigure core vScId budget period priority deadline domain st =
      .ok ((), schedControlConfigurePerform st core vScId budget period priority deadline
        domain) := by
  unfold schedControlConfigureAdmitted at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hC, hM⟩ := h
  unfold schedControlConfigure schedControlConfigurePerform
  cases hS : st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | none =>
    exfalso
    revert hC
    unfold schedContextConfigureAdmitted
    split
    · simp
    · rw [hS]; simp
  | some sc =>
    rw [hS] at hM
    dsimp only at hM ⊢
    cases hT : schedControlMovedThread? st core sc with
    | none => exact schedContextConfigure_of_admitted st vScId _ _ _ _ _ hC
    | some t =>
      rw [hT] at hM
      dsimp only at hM ⊢
      have hC' := hC
      unfold schedContextConfigureAdmitted at hC'
      cases hV : validateSchedContextParams budget period priority deadline domain with
      | error e => simp [hV] at hC'
      | ok u =>
        cases u
        simp only [hV, hS, Bool.and_eq_true, decide_eq_true_eq] at hC'
        have hCheck : checkAdmission st
            (configuredSchedContext budget period priority deadline domain st.machine.timer
              (configureKeepsHead st sc budget period) sc)
            (some vScId.val) = true := by
          rw [checkAdmission_eq_impl]
          have hb := configuredSchedContext_budget_period budget period priority deadline domain
            st.machine.timer (configureKeepsHead st sc budget period) sc
          simp only [checkAdmissionImpl, admissionUtilizationOf, SchedContext.utilizationPerMille,
            SchedContext.bandwidth, hb.1, hb.2, decide_eq_true_eq]
          simpa using hC'.1
        dsimp only
        rw [if_pos hCheck]
        obtain ⟨sgi, hMove⟩ := setThreadCpuAffinityWithMigration_of_admitted st t (some core) core hM
        rw [hMove]
        dsimp only
        apply schedContextConfigure_of_admitted
        have hA := hM
        unfold setAffinityAdmitted at hA
        cases hTcb : st.getTcb? t with
        | none => rw [hTcb] at hA; cases hA
        | some tcb =>
          rw [hTcb] at hA
          simp only [Bool.and_eq_true] at hA
          rw [(setAffinityPerform_configureAdmissionFrame (some core) hTcb
            hA.1.1.1).schedContextConfigureAdmitted_eq]
          exact hC

/-- WS-ZA ZA6.4: **the affinity change moves one home core and no blocking
edge**: it rewrites the thread's affinity and the scheduler links, so every other
thread keeps its home, the moved thread's home is its new affinity, and every
thread keeps its IPC state. -/
theorem setThreadCpuAffinityWithMigration_chainShape {st stM : SystemState}
    {tid : SeLe4n.ThreadId} {affinity : Option Concurrency.CoreId} {ec : Concurrency.CoreId}
    {sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : setThreadCpuAffinityWithMigration st tid affinity ec = .ok (stM, sgi)) :
    (∀ t, t ≠ tid → determineTargetCore stM t = determineTargetCore st t) ∧
    determineTargetCore stM tid = affinity.getD bootCoreId ∧
    (∀ t, PriorityInheritance.blockingServer stM t = PriorityInheritance.blockingServer st t) := by
  obtain ⟨tcb, stSet, hT, -, -, -, hSet, rfl, -⟩ := setThreadCpuAffinityWithMigration_ok_shape h
  have hInvV : (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).objects.invExt := by
    rw [vacateForAffinityChange_objects]; exact hInv
  have hTV : (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).getTcb? tid = some tcb := by
    rw [vacateForAffinityChange_getTcb?]; exact hT
  have hGetV : ∀ t, (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).getTcb? t = st.getTcb? t := fun t => by
    unfold SystemState.getTcb?; rw [vacateForAffinityChange_objects]
  generalize vacateForAffinityChange st tid (determineTargetCore st tid)
    (affinity.getD bootCoreId) = sv at hSet hInvV hTV hGetV
  have hSetEq : stSet = sv.updateTcb tid (fun t => { t with cpuAffinity := affinity }) := by
    unfold setThreadCpuAffinity at hSet
    rw [SystemState.getTcbWitnessed?_eq_some hTV] at hSet
    rw [← (Except.ok.inj hSet)]
    exact SystemState.rewriteObject_tcb_eq_updateTcb hTV (fun t => { t with cpuAffinity := affinity }) _
  subst hSetEq
  -- The tail writes scheduler links alone.
  have key : ∀ sM : SystemState, SystemState.objectsAgreeOffSchedulerLinks sM
      (sv.updateTcb tid (fun t => { t with cpuAffinity := affinity })) →
      (∀ t, t ≠ tid → determineTargetCore sM t = determineTargetCore st t) ∧
      determineTargetCore sM tid = affinity.getD bootCoreId ∧
      (∀ t, PriorityInheritance.blockingServer sM t =
        PriorityInheritance.blockingServer st t) := by
    intro sM hAg
    have hField : ∀ {α : Type} (f : TCB → α), (∀ u : TCB, f u.withoutRunLinks = f u) → ∀ t,
        (sM.getTcb? t).map f =
          ((sv.updateTcb tid (fun t => { t with cpuAffinity := affinity })).getTcb? t).map f :=
      fun f hf t => TCB.map_proj_eq_of_map_withoutRunLinks_eq f (hAg.getTcb? t) hf
    refine ⟨fun t hne => ?_, ?_, fun t => ?_⟩
    · refine determineTargetCore_congr _ _ t ((hField (·.cpuAffinity) (fun _ => rfl) t).trans ?_)
      rw [SystemState.updateTcb_getTcb?_ne _ _ _ hInvV t
        (fun h => hne (SeLe4n.ThreadId.toObjId_injective _ _ h).symm), hGetV]
    · have h1 := hField (·.cpuAffinity) (fun _ => rfl) tid
      rw [SystemState.updateTcb_getTcb?_self _ _ _ hInvV, hTV] at h1
      unfold determineTargetCore
      cases hM : sM.getTcb? tid with
      | none => rw [hM] at h1; cases h1
      | some x =>
        rw [hM] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        simp only [h1]; cases affinity <;> rfl
    · unfold PriorityInheritance.blockingServer
      have h1 := hField TCB.blockingServer? (fun _ => rfl) t
      have h2 : ((sv.updateTcb tid (fun t => { t with cpuAffinity := affinity })).getTcb? t).map
          TCB.blockingServer? = (st.getTcb? t).map TCB.blockingServer? := by
        by_cases hEq : tid.toObjId = t.toObjId
        · cases SeLe4n.ThreadId.toObjId_injective _ _ hEq
          rw [SystemState.updateTcb_getTcb?_self _ _ _ hInvV, hGetV]
          cases st.getTcb? tid <;> rfl
        · rw [SystemState.updateTcb_getTcb?_ne _ _ _ hInvV t hEq, hGetV]
      have h3 := h1.trans h2
      cases hA : sM.getTcb? t <;> cases hB : st.getTcb? t <;> simp_all
  apply key
  refine (SystemState.objectsAgreeOffSchedulerLinks.of_runLinks
    (requeueVacatedOnNewHome_objectsAgreeOffRunLinks _ _ _ _)).trans
    ((SystemState.objectsAgreeOffSchedulerLinks.of_runLinks
      (migrateRunQueueOnAffinityChange_objectsAgreeOffRunLinks _ _ _ _)).trans ?_)
  split
  · exact .of_releaseLinks (migrateSchedContextReplenishment_agree _ _ _ _)
  · exact .refl _

/-- WS-ZA ZA6.4: **every release link of `st'` is `st`'s or names core `d`**:
the reading a footprint needs of a step that moves contexts' release entries to
`d` alone. -/
def releaseCoresMoveOnlyTo (st' st : SystemState) (d : Concurrency.CoreId) : Prop :=
  ∀ (y : SeLe4n.SchedContextId) (c : Concurrency.CoreId),
    st'.releaseCoreOf y = some c → st.releaseCoreOf y = some c ∨ c = d

namespace releaseCoresMoveOnlyTo

theorem refl (st : SystemState) (d : Concurrency.CoreId) : releaseCoresMoveOnlyTo st st d :=
  fun _ _ h => .inl h

theorem trans {a b c : SystemState} {d : Concurrency.CoreId} (h₂ : releaseCoresMoveOnlyTo c b d)
    (h₁ : releaseCoresMoveOnlyTo b a d) : releaseCoresMoveOnlyTo c a d := fun y e h => by
  rcases h₂ y e h with h | h
  · exact h₁ y e h
  · exact .inr h

/-- The relation reads the object stores alone. -/
theorem of_objects {a a' b : SystemState} {d : Concurrency.CoreId}
    (h : releaseCoresMoveOnlyTo a b d) (ha : a'.objects = a.objects) :
    releaseCoresMoveOnlyTo a' b d := fun y e hy => by
  apply h y e
  unfold SystemState.releaseCoreOf SystemState.getSchedContext? at hy ⊢
  rw [← ha]; exact hy

/-- A context rewrite in its slot that keeps its link's core, takes it off every
queue, or puts it on `d`'s. -/
theorem mapSchedContextInPlace (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (d : Concurrency.CoreId)
    (hg : ∀ sc, (g sc).releaseCore? = sc.releaseCore? ∨ (g sc).releaseCore? = none ∨
      (g sc).releaseCore? = some d) :
    releaseCoresMoveOnlyTo (st.mapSchedContextInPlace s g) st d := fun y e hy => by
  unfold SystemState.releaseCoreOf at hy ⊢
  by_cases hys : y = s
  · subst hys
    rw [SystemState.mapSchedContextInPlace_getSchedContext?_self] at hy
    cases hS : st.getSchedContext? y with
    | none => rw [hS] at hy; cases hy
    | some sc =>
      rw [hS] at hy
      simp only [Option.map_some, Option.bind_some] at hy ⊢
      rcases hg sc with h | h | h
      · rw [h] at hy; exact .inl hy
      · rw [h] at hy; cases hy
      · rw [h] at hy; cases hy; exact .inr rfl
  · rw [SystemState.mapSchedContextInPlace_getSchedContext?_ne _ _ _ hys] at hy
    exact .inl hy

theorem leaveRelease_core (sc : SchedContext) : sc.leaveRelease.releaseCore? = none := by
  simp [SchedContext.leaveRelease, SchedContext.releaseCore?]

theorem withReleaseNext_core (sc : SchedContext) (n : Nat) :
    (sc.withReleaseNext n).releaseCore? = sc.releaseCore? := rfl

theorem joinRelease_core (sc : SchedContext) (c : Concurrency.CoreId) (n t : Nat) :
    (sc.joinRelease c n t).releaseCore? = some c :=
  (SchedContext.releaseCore?_eq_some_iff _ c).mpr rfl

theorem releaseUnlinkOn (st : SystemState) (c : Concurrency.CoreId) (s : SeLe4n.SchedContextId)
    (d : Concurrency.CoreId) : releaseCoresMoveOnlyTo (st.releaseUnlinkOn c s) st d := by
  have h1 := mapSchedContextInPlace st s SchedContext.leaveRelease d
    (fun sc => .inr (.inl (leaveRelease_core sc)))
  unfold SystemState.releaseUnlinkOn
  split
  · dsimp only
    split
    · exact of_objects h1 rfl
    · exact of_objects ((mapSchedContextInPlace _ _ _ d
        (fun sc => .inl (withReleaseNext_core sc _))).trans h1) rfl
  · exact refl st d

theorem releaseLinkIn (st : SystemState) (d : Concurrency.CoreId) (s : SeLe4n.SchedContextId)
    (t : Nat) : releaseCoresMoveOnlyTo (st.releaseLinkIn d s t) st d := by
  have h1 : ∀ n, releaseCoresMoveOnlyTo (st.mapSchedContextInPlace s
      (SchedContext.joinRelease d n t)) st d := fun n =>
    mapSchedContextInPlace st s (SchedContext.joinRelease d n t) d
      (fun sc => .inr (.inr (joinRelease_core sc d n t)))
  unfold SystemState.releaseLinkIn
  dsimp only
  split
  · exact of_objects (h1 _) rfl
  · exact of_objects ((mapSchedContextInPlace _ _ _ d
      (fun sc => .inl (withReleaseNext_core sc _))).trans (h1 _)) rfl

end releaseCoresMoveOnlyTo

/-- WS-ZA ZA6.4: **a replenishment migration to `toCore` moves release links to
`toCore` alone.** -/
theorem migrateSchedContextReplenishment_releaseCoresMoveOnlyTo (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : Concurrency.CoreId) :
    releaseCoresMoveOnlyTo (migrateSchedContextReplenishment st scId fromCore toCore) st toCore := by
  unfold migrateSchedContextReplenishment
  split
  · exact .refl st _
  · dsimp only
    have hR : releaseCoresMoveOnlyTo (st.releaseRemoveOn fromCore scId) st toCore :=
      releaseCoresMoveOnlyTo.of_objects (releaseCoresMoveOnlyTo.releaseUnlinkOn st _ _ _) rfl
    have hI : ∀ (a : SystemState) t, releaseCoresMoveOnlyTo (a.releaseInsertOn toCore scId t) a
        toCore := fun a t => by
      unfold SystemState.releaseInsertOn
      split
      · exact .refl _ _
      · unfold SystemState.releaseInsertFresh
        exact releaseCoresMoveOnlyTo.of_objects (releaseCoresMoveOnlyTo.releaseLinkIn _ _ _ _) rfl
    split
    · exact releaseCoresMoveOnlyTo.of_objects ((hI _ _).trans hR) rfl
    · exact releaseCoresMoveOnlyTo.of_objects (.refl st _) rfl

/-- WS-ZA ZA6.4: **the affinity change moves release links to the new home
alone**: its replenishment migration is the one release write. -/
theorem setThreadCpuAffinityWithMigration_releaseCoresMoveOnlyTo {st stM : SystemState}
    {tid : SeLe4n.ThreadId} {affinity : Option Concurrency.CoreId} {ec : Concurrency.CoreId}
    {sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : setThreadCpuAffinityWithMigration st tid affinity ec = .ok (stM, sgi)) :
    releaseCoresMoveOnlyTo stM st (affinity.getD bootCoreId) := by
  obtain ⟨tcb, stSet, hT, -, -, -, hSet, rfl, -⟩ := setThreadCpuAffinityWithMigration_ok_shape h
  have hInvV : (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).objects.invExt := by
    rw [vacateForAffinityChange_objects]; exact hInv
  have hTV : (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).getTcb? tid = some tcb := by
    rw [vacateForAffinityChange_getTcb?]; exact hT
  have hV : releaseCoresMoveOnlyTo (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)) st (affinity.getD bootCoreId) :=
    releaseCoresMoveOnlyTo.of_objects (.refl st _) (vacateForAffinityChange_objects _ _ _ _)
  generalize vacateForAffinityChange st tid (determineTargetCore st tid)
    (affinity.getD bootCoreId) = sv at hSet hInvV hTV hV
  have hSetEq : stSet = sv.updateTcb tid (fun t => { t with cpuAffinity := affinity }) := by
    unfold setThreadCpuAffinity at hSet
    rw [SystemState.getTcbWitnessed?_eq_some hTV] at hSet
    rw [← (Except.ok.inj hSet)]
    exact SystemState.rewriteObject_tcb_eq_updateTcb hTV (fun t => { t with cpuAffinity := affinity }) _
  subst hSetEq
  have hS : releaseCoresMoveOnlyTo (sv.updateTcb tid (fun t => { t with cpuAffinity := affinity }))
      st (affinity.getD bootCoreId) := fun y e hy => by
    rw [SystemState.releaseCoreOf_updateTcb _ _ _ hInvV] at hy
    exact hV y e hy
  have hRun : ∀ {a b : SystemState}, a.objectsAgreeOffRunLinks b →
      releaseCoresMoveOnlyTo b st (affinity.getD bootCoreId) →
      releaseCoresMoveOnlyTo a st (affinity.getD bootCoreId) :=
    fun hA hB y e hy => hB y e (by rw [← SystemState.releaseCoreOf_of_runLinks hA y]; exact hy)
  refine hRun (requeueVacatedOnNewHome_objectsAgreeOffRunLinks _ _ _ _)
    (hRun (migrateRunQueueOnAffinityChange_objectsAgreeOffRunLinks _ _ _ _) ?_)
  split
  · exact (migrateSchedContextReplenishment_releaseCoresMoveOnlyTo _ _ _ _).trans hS
  · exact hS

/-- WS-ZA ZA6.4: **the affinity change keeps every context off its release
fields and the object count**: it writes one thread's affinity, the scheduler
and the scheduler links (WS-UC UC2: the count `objects.size` is the PIP-chain
fuel the write set reads). -/
theorem setThreadCpuAffinityWithMigration_scView {st stM : SystemState}
    {tid : SeLe4n.ThreadId} {affinity : Option Concurrency.CoreId} {ec : Concurrency.CoreId}
    {sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (hInvM : stM.objects.invExt)
    (h : setThreadCpuAffinityWithMigration st tid affinity ec = .ok (stM, sgi)) :
    (∀ s, (stM.getSchedContext? s).map SchedContext.withoutRelease =
      (st.getSchedContext? s).map SchedContext.withoutRelease) ∧
    stM.objects.size = st.objects.size := by
  obtain ⟨tcb, stSet, hT, -, -, -, hSet, rfl, -⟩ := setThreadCpuAffinityWithMigration_ok_shape h
  have hInvV : (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).objects.invExt := by
    rw [vacateForAffinityChange_objects]; exact hInv
  have hTV : (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).getTcb? tid = some tcb := by
    rw [vacateForAffinityChange_getTcb?]; exact hT
  have hGetV : ∀ s, (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).getSchedContext? s = st.getSchedContext? s := fun s => by
    unfold SystemState.getSchedContext?; rw [vacateForAffinityChange_objects]
  have hIdxV : (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).objects.size = st.objects.size := by
    rw [vacateForAffinityChange_objects]
  generalize vacateForAffinityChange st tid (determineTargetCore st tid)
    (affinity.getD bootCoreId) = sv at hSet hInvV hTV hGetV hIdxV hInvM
  have hSetEq : stSet = sv.updateTcb tid (fun t => { t with cpuAffinity := affinity }) := by
    unfold setThreadCpuAffinity at hSet
    rw [SystemState.getTcbWitnessed?_eq_some hTV] at hSet
    rw [← (Except.ok.inj hSet)]
    exact SystemState.rewriteObject_tcb_eq_updateTcb hTV (fun t => { t with cpuAffinity := affinity }) _
  subst hSetEq
  have key : ∀ sM : SystemState, sM.objects.invExt →
      SystemState.objectsAgreeOffSchedulerLinks sM
      (sv.updateTcb tid (fun t => { t with cpuAffinity := affinity })) →
      ConfigureAdmissionFrame sM (sv.updateTcb tid (fun t => { t with cpuAffinity := affinity })) →
      (∀ s, (sM.getSchedContext? s).map SchedContext.withoutRelease =
        (st.getSchedContext? s).map SchedContext.withoutRelease) ∧
      sM.objects.size = st.objects.size := fun sM hInvS hAg _ =>
    ⟨fun s => by rw [hAg.getSchedContext? s, SystemState.updateTcb_getSchedContext? _ _ _ hInvV, hGetV],
     (hAg.objects_size_eq hInvS (SystemState.updateTcb_preserves_objects_invExt _ _ _ hInvV)).trans
       ((SystemState.updateTcb_objects_size _ _ _ hInvV).trans hIdxV)⟩
  apply key _ hInvM
  · refine (SystemState.objectsAgreeOffSchedulerLinks.of_runLinks
      (requeueVacatedOnNewHome_objectsAgreeOffRunLinks _ _ _ _)).trans
      ((SystemState.objectsAgreeOffSchedulerLinks.of_runLinks
        (migrateRunQueueOnAffinityChange_objectsAgreeOffRunLinks _ _ _ _)).trans ?_)
    split
    · exact .of_releaseLinks (migrateSchedContextReplenishment_agree _ _ _ _)
    · exact .refl _
  · refine (requeueVacatedOnNewHome_configureAdmissionFrame _ _ _ _).trans
      ((migrateRunQueueOnAffinityChange_configureAdmissionFrame _ _ _ _).trans ?_)
    split
    · exact ConfigureAdmissionFrame.of_releaseOnlyWrite
        (migrateSchedContextReplenishment_releaseOnlyWrite _ _ _ _)
        (migrateSchedContextReplenishment_agree _ _ _ _)
        (admissionSlotView_migrateSchedContextReplenishment _ _ _ _)
    · exact .refl _

end SeLe4n.Kernel.SchedContextOps
