-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.SchedContextFootprint
import SeLe4n.Kernel.SchedContext.SchedControl
import SeLe4n.Kernel.Scheduler.Operations.AffinityFootprint
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs

/-!
# The scheduler-domain footprint of a configure through a core's control

WS-ZA ZA6.4.  `SchedContextOps.schedControlConfigure` configures in place, or
moves the context's bound thread to the control's core first and configures on
the moved state.  Its footprint is the configure's, read off the pre-state, and
on a move the affinity change's beside the control's core: the moved
configure's cores are the pre-state's configure cores or the control's core
(`schedContextConfigureWriteSet_of_move`,
`schedContextConfigureReplenishCores_of_move`), because the move changes one
thread's home (to the control's core), no blocking edge, no context off its
release fields, and moves release links to the control's core alone.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

/-- The cores a configure through core `core`'s control may write: the
configure's, and on a move the affinity change's and the control's core. -/
def schedControlConfigureWriteSet (st : SystemState) (core : CoreId) (scObjId : SeLe4n.ObjId) :
    List CoreId :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) with
  | some sc =>
      match SchedContextOps.schedControlMovedThread? st core sc with
      | some t => setThreadCpuAffinityWriteSet st t (some core) ++
          core :: schedContextConfigureWriteSet st scObjId
      | none => schedContextConfigureWriteSet st scObjId
  | none => schedContextConfigureWriteSet st scObjId

/-- The replenish queues a configure through core `core`'s control may write. -/
def schedControlConfigureReplenishCores (st : SystemState) (core : CoreId)
    (scObjId : SeLe4n.ObjId) : List CoreId :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) with
  | some sc =>
      match SchedContextOps.schedControlMovedThread? st core sc with
      | some t => setThreadCpuAffinityReplenishCores st t (some core) ++
          core :: schedContextConfigureReplenishCores st scObjId
      | none => schedContextConfigureReplenishCores st scObjId
  | none => schedContextConfigureReplenishCores st scObjId

/-- **The live `.schedContextConfigure` arm's scheduler-domain footprint.** -/
def schedLockSet_schedControlConfigure (st : SystemState) (core : CoreId)
    (scObjId : SeLe4n.ObjId) : List (Concurrency.LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (schedControlConfigureWriteSet st core scObjId)
    (schedControlConfigureReplenishCores st core scObjId)

theorem schedContextConfigureWriteSet_subset_schedControl (st : SystemState) (core : CoreId)
    (scObjId : SeLe4n.ObjId) (d : CoreId) (h : d ∈ schedContextConfigureWriteSet st scObjId) :
    d ∈ schedControlConfigureWriteSet st core scObjId := by
  unfold schedControlConfigureWriteSet
  split
  · split
    · exact List.mem_append.mpr (.inr (List.mem_cons_of_mem _ h))
    · exact h
  · exact h

theorem schedContextConfigureReplenishCores_subset_schedControl (st : SystemState)
    (core : CoreId) (scObjId : SeLe4n.ObjId) (d : CoreId)
    (h : d ∈ schedContextConfigureReplenishCores st scObjId) :
    d ∈ schedControlConfigureReplenishCores st core scObjId := by
  unfold schedControlConfigureReplenishCores
  split
  · split
    · exact List.mem_append.mpr (.inr (List.mem_cons_of_mem _ h))
    · exact h
  · exact h

/-- On a move the footprint is the affinity change's, the control's core and the
pre-state configure's. -/
theorem schedControlConfigureWriteSet_of_move {st : SystemState} {core : CoreId}
    {scObjId : SeLe4n.ObjId} {sc : SchedContext} {t : SeLe4n.ThreadId}
    (hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) = some sc)
    (hB : sc.boundThread = some t) (hNe : determineTargetCore st t ≠ core) :
    schedControlConfigureWriteSet st core scObjId = setThreadCpuAffinityWriteSet st t (some core) ++
      core :: schedContextConfigureWriteSet st scObjId ∧
    schedControlConfigureReplenishCores st core scObjId =
      setThreadCpuAffinityReplenishCores st t (some core) ++
        core :: schedContextConfigureReplenishCores st scObjId := by
  have hMv : SchedContextOps.schedControlMovedThread? st core sc = some t := by
    unfold SchedContextOps.schedControlMovedThread?; simp [hB, hNe]
  unfold schedControlConfigureWriteSet schedControlConfigureReplenishCores
  refine ⟨?_, ?_⟩ <;> simp only [hSc, hMv]

/-- The footprint holds the bound thread's home core's run-queue write lock — the
bucket propagation's own. -/
theorem schedLockSet_schedControlConfigure_contains_home_runQueue_write
    (st : SystemState) (core : CoreId) (scObjId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (h : SchedContextOps.schedContextBoundThread? st scObjId = some tid) :
    (Concurrency.LockKey.runQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
      ∈ schedLockSet_schedControlConfigure st core scObjId :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (schedContextConfigureWriteSet_subset_schedControl _ _ _ _
      (by unfold schedContextConfigureWriteSet schedContextWriteSet; rw [h]; simp))

/-- ...the replenish-queue write lock of the core the context's release link
names, which is the purge's. -/
theorem schedLockSet_schedControlConfigure_contains_replenishQueue_write
    (st : SystemState) (core : CoreId) (scObjId : SeLe4n.ObjId) (d : CoreId)
    (h : st.releaseCoreOf (SeLe4n.SchedContextId.ofObjId scObjId) = some d) :
    (Concurrency.LockKey.replenishQueue d, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedControlConfigure st core scObjId :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (schedContextConfigureReplenishCores_subset_schedControl _ _ _ _ (by
      unfold schedContextConfigureReplenishCores SchedContextOps.purgeReplenishCores
      cases hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) with
      | none => unfold SystemState.releaseCoreOf at h; rw [hSc] at h; cases h
      | some _ => simp only [h]; exact List.mem_append_left _ (List.mem_singleton_self d)))

/-- ...and, on a move, the control's core's run-queue write lock, where the
moved thread lands. -/
theorem schedLockSet_schedControlConfigure_contains_control_runQueue_write
    {st : SystemState} {core : CoreId} {scObjId : SeLe4n.ObjId} {sc : SchedContext}
    {t : SeLe4n.ThreadId}
    (hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) = some sc)
    (hB : sc.boundThread = some t) (hNe : determineTargetCore st t ≠ core) :
    (Concurrency.LockKey.runQueue core, Concurrency.AccessMode.write)
      ∈ schedLockSet_schedControlConfigure st core scObjId := by
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  rw [(schedControlConfigureWriteSet_of_move hSc hB hNe).1]
  exact List.mem_append.mpr (.inr (List.mem_cons_self ..))

/-- No replenish lock at all where the capability's target resolves to no
context: the arm refuses `.objectNotFound` there and writes nothing. -/
theorem schedLockSet_schedControlConfigure_no_replenishQueue_of_absent
    (st : SystemState) (core : CoreId) (scObjId : SeLe4n.ObjId) (c : CoreId)
    (h : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) = none) :
    (Concurrency.LockKey.replenishQueue c, Concurrency.AccessMode.write)
      ∉ schedLockSet_schedControlConfigure st core scObjId := by
  intro hMem
  have := (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mp hMem
  unfold schedControlConfigureReplenishCores schedContextConfigureReplenishCores at this
  rw [h] at this
  exact absurd this (by simp)

/-- The moved context's bound thread, read off the moved state: the move keeps
every context off its release fields. -/
theorem schedContextBoundThread?_of_move {st stM : SystemState} {core : CoreId}
    {scObjId : SeLe4n.ObjId} {sc : SchedContext} {t : SeLe4n.ThreadId}
    {sgi : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) = some sc)
    (hM : setThreadCpuAffinityWithMigration st t (some core) core = .ok (stM, sgi)) :
    ∃ scM, stM.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) = some scM ∧
      scM.boundThread = sc.boundThread := by
  have hV := (SchedContextOps.setThreadCpuAffinityWithMigration_scView hInv hM).1
    (SeLe4n.SchedContextId.ofObjId scObjId)
  rw [hSc] at hV
  cases hS : stM.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) with
  | none => rw [hS] at hV; cases hV
  | some scM =>
    rw [hS] at hV
    simp only [Option.map_some, Option.some.injEq] at hV
    have h := congrArg SchedContext.boundThread hV
    exact ⟨scM, rfl, h⟩

/-- **The moved configure writes the pre-state configure's cores or the
control's core.** -/
theorem schedContextConfigureWriteSet_of_move {st stM : SystemState} {core : CoreId}
    {scObjId : SeLe4n.ObjId} {sc : SchedContext} {t : SeLe4n.ThreadId}
    {sgi : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) = some sc)
    (hB : sc.boundThread = some t)
    (hM : setThreadCpuAffinityWithMigration st t (some core) core = .ok (stM, sgi))
    (d : CoreId) (hd : d ∈ schedContextConfigureWriteSet stM scObjId) :
    d = core ∨ d ∈ schedContextConfigureWriteSet st scObjId := by
  obtain ⟨hHomeNe, hHomeT, hEdge⟩ :=
    SchedContextOps.setThreadCpuAffinityWithMigration_chainShape hInv hM
  have hIdx := (SchedContextOps.setThreadCpuAffinityWithMigration_scView hInv hM).2
  have hInvM := setThreadCpuAffinityWithMigration_preserves_objects_invExt _ _ _ _ hInv _ hM
  obtain ⟨scM, hScM, hBM⟩ := schedContextBoundThread?_of_move hInv hSc hM
  have hBT : SchedContextOps.schedContextBoundThread? stM scObjId = some t := by
    unfold SchedContextOps.schedContextBoundThread?; rw [hScM]; exact hBM.trans hB
  have hBT0 : SchedContextOps.schedContextBoundThread? st scObjId = some t := by
    unfold SchedContextOps.schedContextBoundThread?; rw [hSc]; exact hB
  unfold schedContextConfigureWriteSet schedContextWriteSet at hd ⊢
  rw [hBT] at hd
  rw [hBT0]
  rcases List.mem_append.mp hd with hd | hd
  · rw [List.mem_singleton] at hd
    exact .inl (hd.trans hHomeT)
  · rw [hIdx] at hd
    rcases PriorityInheritance.waiterChainWriteSet_mem_of_homeOverride stM st t core _
        (determineTargetCore st t) _ hInvM hInv
        (fun x => by
          by_cases hx : x = t
          · subst hx; exact .inr hHomeT
          · exact .inl (hHomeNe x hx)) hEdge d hd with h | h
    · exact .inl h
    · exact .inr (List.mem_append.mpr (.inr h))

/-- **The moved configure writes the pre-state configure's replenish queues or
the control's core's.** -/
theorem schedContextConfigureReplenishCores_of_move {st stM : SystemState} {core : CoreId}
    {scObjId : SeLe4n.ObjId} {sc : SchedContext} {t : SeLe4n.ThreadId}
    {sgi : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (hSc : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) = some sc)
    (hB : sc.boundThread = some t)
    (hM : setThreadCpuAffinityWithMigration st t (some core) core = .ok (stM, sgi))
    (d : CoreId) (hd : d ∈ schedContextConfigureReplenishCores stM scObjId) :
    d = core ∨ d ∈ schedContextConfigureReplenishCores st scObjId := by
  obtain ⟨-, hHomeT, -⟩ := SchedContextOps.setThreadCpuAffinityWithMigration_chainShape hInv hM
  have hRel := SchedContextOps.setThreadCpuAffinityWithMigration_releaseCoresMoveOnlyTo hInv hM
  obtain ⟨scM, hScM, hBM⟩ := schedContextBoundThread?_of_move hInv hSc hM
  unfold schedContextConfigureReplenishCores at hd ⊢
  rw [hScM] at hd
  rw [hSc]
  dsimp only at hd ⊢
  rw [hBM, hB] at hd
  rw [hB]
  rcases List.mem_append.mp hd with hd | hd
  · unfold SchedContextOps.purgeReplenishCores at hd ⊢
    cases hR : stM.releaseCoreOf (SeLe4n.SchedContextId.ofObjId scObjId) with
    | none => rw [hR] at hd; cases hd
    | some e =>
      rw [hR, List.mem_singleton] at hd
      subst hd
      rcases hRel _ _ hR with h | h
      · exact .inr (List.mem_append.mpr (.inl (by rw [h]; simp)))
      · exact .inl h
  · rw [List.mem_singleton] at hd
    exact .inl (hd.trans hHomeT)

/-- **The exactness frame**: a configure through a control writes no replenish
queue outside its footprint's replenish segment. -/
theorem schedControlConfigure_replenishQueueOnCore_ne (st st' : SystemState) (core : CoreId)
    (vScId : SeLe4n.ValidObjId) (budget period priority deadline domain : Nat) (c : CoreId)
    (hInv : st.objects.invExt)
    (hne : c ∉ schedControlConfigureReplenishCores st core vScId.val)
    (h : SchedContextOps.schedControlConfigure core vScId budget period priority deadline domain
      st = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  rcases SchedContextOps.schedControlConfigure_ok_cases h with h | ⟨sc, t, stM, sgi, hSc, hB, hNe, hM, h⟩
  · exact schedContextConfigure_replenishQueueOnCore_ne st st' vScId _ _ _ _ _ c
      (fun hm => hne (schedContextConfigureReplenishCores_subset_schedControl _ _ _ _ hm)) h
  · rw [(schedControlConfigureWriteSet_of_move hSc hB hNe).2] at hne
    have hNeA : c ∉ setThreadCpuAffinityReplenishCores st t (some core) :=
      fun hm => hne (List.mem_append.mpr (.inl hm))
    have hNeC : c ∉ schedContextConfigureReplenishCores stM vScId.val := fun hm => by
      rcases schedContextConfigureReplenishCores_of_move hInv hSc hB hM c hm with e | e
      · exact hne (List.mem_append.mpr (.inr (e ▸ List.mem_cons_self ..)))
      · exact hne (List.mem_append.mpr (.inr (List.mem_cons_of_mem _ e)))
    rw [schedContextConfigure_replenishQueueOnCore_ne stM st' vScId _ _ _ _ _ c hNeC h]
    exact setThreadCpuAffinityWithMigration_replenishQueueOnCore_ne st stM t _ core sgi c hInv
      hNeA hM

end SeLe4n.Kernel
