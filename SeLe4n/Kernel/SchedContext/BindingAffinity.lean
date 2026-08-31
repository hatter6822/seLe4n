-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.OperationsPerCore
import SeLe4n.Kernel.SchedContext.ReplenishAffinity
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake

/-!
# The binding lifecycle preserves the replenish-queue invariants

`schedContextBind` and `schedContextUnbind{,OnCore}` are the two live syscall
arms that create and destroy a SchedContext's `boundThread` binding, and until
this module neither carried a `replenishQueueAffinityConsistent` preservation
theorem — the SM5.H family covered the tick, the scheduler, the replenishment
primitives and (since WS-RR RR2) all three donation paths, while the two arms
that make the invariant's obligations appear and disappear rested on an
**unproven operational discipline**: that an unbound SchedContext holds no
replenish-queue entries, so binding one cannot activate a mis-homed entry.

This module states that discipline as an invariant and closes the gap:

* §1 — **`replenishQueueEntriesBoundOnCore`** (the orphan-freedom invariant):
  every entry in a core's replenish queue names a SchedContext that *exists*
  and is *bound*.  The affinity invariant is deliberately vacuous for unbound
  SchedContexts, which is exactly why `schedContextBind` — flipping unbound to
  bound — is the one transition that can make it false without touching a
  queue.  Orphan-freedom is what rules the scenario out: `schedContextBind`'s
  own guard (`sc.boundThread.isSome → .illegalState`) contradicts any
  pre-existing entry for the SchedContext being bound.

  The invariant's existence clause is sound against the object lifecycle by
  construction: no deletion primitive exists in the model, and allocation
  freshness (`retypeFromUntyped`'s occupied-slot guard, AJ2-D/M-09) means a
  SchedContext is never created at an ObjId a stale entry could already name.

* §2 — the queue primitives preserve orphan-freedom: both purges
  (unconditionally — the all-cores purge's theorem sits in §3, after the
  queue characterisation its proof reads), the migration (unconditionally —
  moved entries existed before), and `replenishOnCore` (given the scheduled
  SchedContext is bound, the same shape as its affinity obligation
  `hTarget`).

* §3/§4 — the characterisations of `schedContextUnbind` / `schedContextBind`,
  and the four preservation theorems: unbind preserves affinity with **no**
  orphan-freedom hypothesis, and re-establishes orphan-freedom for its
  SchedContext because the purge provably removes *every* entry the invariant
  admits (under affinity, all of them sit on the bound thread's home core —
  the core the purge targets); bind preserves both, with orphan-freedom
  supplying the no-entries fact its affinity proof turns on.

* §5 — `schedContextUnbindOnCore`, the live dispatch arm: the wrapper's
  scheduling point (`priorityRescheduleOnCore`) either changes nothing or runs
  the `.reschedule` receiver, whose replenish-queue frame and home-core /
  `boundThread` congruences are production
  (`PerCoreWake.lean` / `PerCoreSwitchToThread.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId SgiKind bootCoreId allCores)
open SeLe4n.Kernel.SchedContextOps

-- ============================================================================
-- §1  Orphan-freedom: every replenish-queue entry names a live, bound SchedContext
-- ============================================================================

/-- **The orphan-freedom invariant, per core**: every entry in core `c`'s
replenish queue names a SchedContext that exists in the object store and has a
bound thread.

This is the auxiliary invariant `schedContextBind`'s affinity preservation
turns on.  `replenishQueueAffinityConsistentOnCore` is vacuous for an unbound
SchedContext — deliberately, since the boot core homes affinity-unbound
threads, not unbound SchedContexts' entries — so a stale entry surviving into
an unbound SchedContext's lifetime would sit outside every obligation until
the moment a bind makes it a mis-homed one.  Orphan-freedom says the stale
entry never exists. -/
def replenishQueueEntriesBoundOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (scId : SchedContextId) (t : Nat),
    (scId, t) ∈ (st.scheduler.replenishQueueOnCore c).entries →
    ∃ sc, st.getSchedContext? scId = some sc ∧ ∃ tid, sc.boundThread = some tid

/-- The SMP-wide orphan-freedom invariant — every core's queue is orphan-free. -/
def replenishQueueEntriesBound_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, replenishQueueEntriesBoundOnCore st c

/-- The freshly-booted system is orphan-free on every core (vacuous — the
default replenish queue is empty; same discharge as the affinity invariant's). -/
theorem default_replenishQueueEntriesBound_smp :
    replenishQueueEntriesBound_smp (default : SystemState) := by
  intro c scId t hMem
  have hRepl : (default : SystemState).scheduler.replenishQueueOnCore c
      = SeLe4n.Kernel.ReplenishQueue.empty := (default_state_perCoreInitialized c).2.2.1
  rw [hRepl] at hMem
  simp [SeLe4n.Kernel.ReplenishQueue.empty] at hMem

/-- Transfer: orphan-freedom on core `c` reads the queue's entries and each
SchedContext's existence-plus-`boundThread` projection, nothing else — so it
transfers backwards along an entry-subset and a `boundThread`-projection
agreement.  The orphan-freedom sibling of `affinityConsistent_transfer`. -/
theorem replenishQueueEntriesBoundOnCore_transfer (st base : SystemState) (c : CoreId)
    (hSub : ∀ e, e ∈ (base.scheduler.replenishQueueOnCore c).entries →
                 e ∈ (st.scheduler.replenishQueueOnCore c).entries)
    (hBound : ∀ scId, (base.getSchedContext? scId).map (·.boundThread)
                    = (st.getSchedContext? scId).map (·.boundThread))
    (hCons : replenishQueueEntriesBoundOnCore st c) :
    replenishQueueEntriesBoundOnCore base c := by
  intro scId t hMem
  obtain ⟨sc, hSc, tid, hTid⟩ := hCons scId t (hSub _ hMem)
  have hMapEq := hBound scId
  rw [hSc] at hMapEq
  cases hB : base.getSchedContext? scId with
  | none => rw [hB] at hMapEq; simp at hMapEq
  | some scB =>
    rw [hB] at hMapEq
    simp only [Option.map_some] at hMapEq
    exact ⟨scB, rfl, tid, by rw [Option.some.inj hMapEq, hTid]⟩

-- ============================================================================
-- §2  The queue primitives preserve orphan-freedom
-- ============================================================================

/-- A purge preserves orphan-freedom on every core: it removes entries and
touches no object. -/
theorem purgeReplenishmentOnCore_preserves_replenishQueueEntriesBoundOnCore
    (st : SystemState) (c c' : CoreId) (scId : SchedContextId)
    (hCons : replenishQueueEntriesBoundOnCore st c') :
    replenishQueueEntriesBoundOnCore (purgeReplenishmentOnCore st c scId) c' := by
  intro scId₀ t hMem
  have hObjs : (purgeReplenishmentOnCore st c scId).objects = st.objects := rfl
  have hSc : ∀ s, (purgeReplenishmentOnCore st c scId).getSchedContext? s
      = st.getSchedContext? s := by
    intro s; unfold SystemState.getSchedContext?; rw [hObjs]
  simp only [hSc]
  by_cases hc : c = c'
  · subst hc
    have hQ : (purgeReplenishmentOnCore st c scId).scheduler.replenishQueueOnCore c
        = ReplenishQueue.remove (st.scheduler.replenishQueueOnCore c) scId := by
      simp [purgeReplenishmentOnCore]
    rw [hQ] at hMem
    exact hCons scId₀ t (mem_remove_entries hMem).1
  · have hQ : (purgeReplenishmentOnCore st c scId).scheduler.replenishQueueOnCore c'
        = st.scheduler.replenishQueueOnCore c' := by
      simp only [purgeReplenishmentOnCore]
      exact SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ c c' _ hc
    rw [hQ] at hMem
    exact hCons scId₀ t hMem

/-- The scheduling insert preserves orphan-freedom, given the SchedContext being
scheduled exists and is bound — the orphan-freedom face of the same obligation
its affinity preservation carries as `hTarget`, and one the live CBS enqueue
sites satisfy by construction (they read `scId` off a binding). -/
theorem replenishOnCore_preserves_replenishQueueEntriesBoundOnCore
    (st : SystemState) (c c' : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hCons : replenishQueueEntriesBoundOnCore st c')
    (hBound : ∃ sc, st.getSchedContext? scId = some sc ∧ ∃ tid, sc.boundThread = some tid) :
    replenishQueueEntriesBoundOnCore (replenishOnCore st c scId eligibleAt) c' := by
  intro scId₀ t hMem
  have hObjs : (replenishOnCore st c scId eligibleAt).objects = st.objects := rfl
  have hSc : ∀ s, (replenishOnCore st c scId eligibleAt).getSchedContext? s
      = st.getSchedContext? s := by
    intro s; unfold SystemState.getSchedContext?; rw [hObjs]
  simp only [hSc]
  by_cases hc : c = c'
  · subst hc
    have hQ : (replenishOnCore st c scId eligibleAt).scheduler.replenishQueueOnCore c
        = (st.scheduler.replenishQueueOnCore c).insert scId eligibleAt := by
      simp [replenishOnCore]
    rw [hQ] at hMem
    rcases (mem_insertSorted_iff _ scId eligibleAt (scId₀, t)).mp hMem with hEq | hOld
    · have hScEq : scId₀ = scId := (Prod.mk.injEq .. ▸ hEq).1
      subst hScEq
      exact hBound
    · exact hCons scId₀ t hOld
  · have hQ : (replenishOnCore st c scId eligibleAt).scheduler.replenishQueueOnCore c'
        = st.scheduler.replenishQueueOnCore c' := by
      simp only [replenishOnCore]
      exact SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ c c' _ hc
    rw [hQ] at hMem
    exact hCons scId₀ t hMem

/-- The SM5.H.4 migration preserves orphan-freedom on every core,
unconditionally: it moves entries that already existed (the provenance
decomposition) and touches no object. -/
theorem migrateSchedContextReplenishment_preserves_replenishQueueEntriesBound_smp
    (st : SystemState) (scId : SchedContextId) (fromCore toCore : CoreId)
    (hCons : replenishQueueEntriesBound_smp st) :
    replenishQueueEntriesBound_smp
      (migrateSchedContextReplenishment st scId fromCore toCore) := by
  intro c scId₀ t hMem
  have hObjs := migrateSchedContextReplenishment_objects st scId fromCore toCore
  have hSc : ∀ s, (migrateSchedContextReplenishment st scId fromCore toCore).getSchedContext? s
      = st.getSchedContext? s := by
    intro s; unfold SystemState.getSchedContext?; rw [hObjs]
  simp only [hSc]
  by_cases hSelf : fromCore = toCore
  · rw [hSelf, migrateSchedContextReplenishment_noop] at hMem
    exact hCons c scId₀ t hMem
  · by_cases hTo : c = toCore
    · subst hTo
      rw [migrateSchedContextReplenishment_replenishQueueOnCore_to st scId fromCore c hSelf]
        at hMem
      rcases mem_foldl_insert_provenance _ scId _ _ hMem with hOld | ⟨x, hx, hEq⟩
      · exact hCons c scId₀ t hOld
      · -- a moved entry: it was in `fromCore`'s pre-state queue.
        have hScEq : scId₀ = scId := by
          have := congrArg Prod.fst hEq; simpa using this
        subst hScEq
        obtain ⟨hxMem, _⟩ := List.mem_filter.mp hx
        exact hCons fromCore scId₀ x.2 (by
          have hFst : x.1 = scId₀ := by
            have := (List.mem_filter.mp hx).2; simpa [beq_iff_eq] using this
          rw [← hFst]
          exact hxMem)
    · by_cases hFrom : c = fromCore
      · subst hFrom
        rw [migrateSchedContextReplenishment_replenishQueueOnCore_from st scId c toCore
          (by intro hEq; exact hSelf hEq)] at hMem
        exact hCons c scId₀ t (mem_remove_entries hMem).1
      · rw [show (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore c
              = st.scheduler.replenishQueueOnCore c from by
            unfold migrateSchedContextReplenishment
            rw [if_neg hSelf]
            simp only []
            rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ toCore c _
                (fun hEq => hTo hEq.symm),
              SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ fromCore c _
                (fun hEq => hFrom hEq.symm)]] at hMem
        exact hCons c scId₀ t hMem

-- ============================================================================
-- §3  `schedContextUnbind` — the revocation side of the binding lifecycle
-- ============================================================================

/-- A fold of per-core purges reads, at any core in the (duplicate-free) list,
as one purge of that core's queue — and as the identity elsewhere.  The
`purgeReplenishmentFromAllCores` characterisation, stated over a generic list
so the induction goes through. -/
private theorem foldl_purge_replenishQueueOnCore (scId : SchedContextId) (c : CoreId) :
    ∀ (l : List CoreId), l.Nodup → ∀ (st : SystemState),
    (l.foldl (fun s cc => purgeReplenishmentOnCore s cc scId) st).scheduler.replenishQueueOnCore c
      = if c ∈ l then ReplenishQueue.remove (st.scheduler.replenishQueueOnCore c) scId
        else st.scheduler.replenishQueueOnCore c := by
  intro l
  induction l with
  | nil => intro _ st; simp
  | cons x xs ih =>
    intro hND st
    have hxNotIn : x ∉ xs := (List.nodup_cons.mp hND).1
    have hNDxs : xs.Nodup := (List.nodup_cons.mp hND).2
    rw [List.foldl_cons, ih hNDxs]
    by_cases hcx : c = x
    · subst hcx
      have hNotXs : c ∉ xs := hxNotIn
      rw [if_neg hNotXs, if_pos (List.mem_cons_self ..)]
      simp [purgeReplenishmentOnCore]
    · have hPurgeNe : (purgeReplenishmentOnCore st x scId).scheduler.replenishQueueOnCore c
          = st.scheduler.replenishQueueOnCore c := by
        simp only [purgeReplenishmentOnCore]
        exact SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ x c _
          (fun hEq => hcx hEq.symm)
      by_cases hcxs : c ∈ xs
      · rw [if_pos hcxs, if_pos (List.mem_cons_of_mem x hcxs), hPurgeNe]
      · rw [if_neg hcxs, hPurgeNe,
          if_neg (by intro hMem; rcases List.mem_cons.mp hMem with hEq | hIn
                     · exact hcx hEq
                     · exact hcxs hIn)]

/-- The all-cores purge removes `scId`'s entries from **every** core's queue —
`allCores` is complete and duplicate-free. -/
theorem purgeReplenishmentFromAllCores_replenishQueueOnCore
    (st : SystemState) (scId : SchedContextId) (c : CoreId) :
    (purgeReplenishmentFromAllCores st scId).scheduler.replenishQueueOnCore c
      = ReplenishQueue.remove (st.scheduler.replenishQueueOnCore c) scId := by
  unfold purgeReplenishmentFromAllCores
  rw [foldl_purge_replenishQueueOnCore scId c allCores
    SeLe4n.Kernel.Concurrency.allCores_nodup st]
  rw [if_pos (SeLe4n.Kernel.Concurrency.mem_allCores c)]

/-- The all-cores purge writes no object (each per-core purge is
scheduler-only). -/
theorem purgeReplenishmentFromAllCores_objects (st : SystemState) (scId : SchedContextId) :
    (purgeReplenishmentFromAllCores st scId).objects = st.objects := by
  unfold purgeReplenishmentFromAllCores
  generalize SeLe4n.Kernel.Concurrency.allCores = cores
  induction cores generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih]; rfl

/-- The all-cores purge preserves orphan-freedom on every core,
unconditionally — completing §2's primitive family (it sits here because its
proof reads the two characterisations above). -/
theorem purgeReplenishmentFromAllCores_preserves_replenishQueueEntriesBound_smp
    (st : SystemState) (scId : SchedContextId)
    (hCons : replenishQueueEntriesBound_smp st) :
    replenishQueueEntriesBound_smp (purgeReplenishmentFromAllCores st scId) := by
  intro c scId₀ t hMem
  have hObjs := purgeReplenishmentFromAllCores_objects st scId
  have hSc : ∀ s, (purgeReplenishmentFromAllCores st scId).getSchedContext? s
      = st.getSchedContext? s := by
    intro s; unfold SystemState.getSchedContext?; rw [hObjs]
  simp only [hSc]
  rw [purgeReplenishmentFromAllCores_replenishQueueOnCore st scId c] at hMem
  exact hCons c scId₀ t (mem_remove_entries hMem).1

/-- **The `schedContextUnbind` characterisation**: a successful unbind read a
SchedContext bound to `tid` and produced exactly one of two shapes — the main
arm (the bound TCB exists: both binding sides cleared, the home-core purge) or
the sweep arm (the TCB is gone: the SC side cleared, every core purged).

The scheduler writes the two invariant proofs below do *not* need to see — the
current-clear, the home-queue rebucket — are already erased here: only the
replenish-queue reading survives, and it is stated per core. -/
private theorem schedContextUnbind_ok_char
    (vScId : ValidObjId) (st st' : SystemState)
    (h : schedContextUnbind vScId st = .ok ((), st')) :
    ∃ sc, st.getSchedContext? (SchedContextId.ofObjId vScId.val) = some sc ∧
    ∃ tid, sc.boundThread = some tid ∧
    ((∃ tcb, st.getTcb? tid = some tcb ∧
        st'.objects = (st.objects.insert vScId.val
            (.schedContext { sc with boundThread := none, isActive := false })).insert
            tid.toObjId (.tcb { tcb with schedContextBinding := SchedContextBinding.unbound }) ∧
        (∀ c, st'.scheduler.replenishQueueOnCore c
          = if determineTargetCore st tid = c
            then ReplenishQueue.remove (st.scheduler.replenishQueueOnCore c)
                   ⟨vScId.val.toNat⟩
            else st.scheduler.replenishQueueOnCore c))
     ∨ (st.getTcb? tid = none ∧
        st'.objects = st.objects.insert vScId.val
            (.schedContext { sc with boundThread := none, isActive := false }) ∧
        (∀ c, st'.scheduler.replenishQueueOnCore c
          = ReplenishQueue.remove (st.scheduler.replenishQueueOnCore c)
              ⟨vScId.val.toNat⟩))) := by
  simp only [schedContextUnbind] at h
  cases hSc : st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | none => rw [hSc] at h; cases h
  | some sc =>
    rw [hSc] at h; simp only [] at h
    cases hBT : sc.boundThread with
    | none => rw [hBT] at h; cases h
    | some tid =>
      rw [hBT] at h; simp only [] at h
      refine ⟨sc, rfl, tid, hBT, ?_⟩
      cases hTcb : st.getTcb? tid with
      | some tcb =>
        rw [hTcb] at h; simp only [] at h
        cases h
        refine Or.inl ⟨tcb, rfl, ?_, ?_⟩
        · -- objects: the two inserts survive the scheduler-only wrappers and the
          -- purge (whose object component is definitionally the identity).
          cases hRun : Lifecycle.Suspend.runningCoreOf? st tid <;>
            (simp only []; repeat' split) <;> rfl
        · -- the replenish queue: only the final home-core purge touches it.
          intro c
          by_cases hHome : determineTargetCore st tid = c
          · rw [if_pos hHome]
            cases hRun : Lifecycle.Suspend.runningCoreOf? st tid <;>
              (simp only []; repeat' split) <;>
              simp [purgeReplenishmentOnCore, hHome]
          · rw [if_neg hHome]
            cases hRun : Lifecycle.Suspend.runningCoreOf? st tid <;>
              (simp only []; repeat' split) <;>
              simp [purgeReplenishmentOnCore,
                SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hHome]
      | none =>
        rw [hTcb] at h; simp only [] at h
        have hSt' : _ = st' := congrArg Prod.snd (Except.ok.inj h)
        dsimp only at hSt'
        subst hSt'
        refine Or.inr ⟨by first | exact hTcb | exact rfl, ?_, ?_⟩
        · exact purgeReplenishmentFromAllCores_objects
            ({ st with objects := st.objects.insert vScId.val (KernelObject.schedContext { sc with boundThread := none, isActive := false }) })
            ⟨vScId.val.toNat⟩
        · intro c
          exact purgeReplenishmentFromAllCores_replenishQueueOnCore
            ({ st with objects := st.objects.insert vScId.val (KernelObject.schedContext { sc with boundThread := none, isActive := false }) })
            ⟨vScId.val.toNat⟩ c

-- ============================================================================
-- §4  The four preservation theorems (and the object-store invariant carriers)
-- ============================================================================

/-- Off-key frame: inserting a SchedContext at `scId0`'s slot leaves every
*other* SchedContext's resolution unchanged.  The companion the SM5.I insert
atoms lack: they frame reads across a `boundThread`-preserving rewrite, while
bind/unbind rewrite `boundThread` itself and rely on the key being distinct. -/
private theorem getSchedContext?_insert_schedContext_ne (st result : SystemState)
    (scId0 : SchedContextId) (sc' : SchedContext) (hInv : st.objects.invExt)
    (hObj : result.objects = st.objects.insert scId0.toObjId (KernelObject.schedContext sc'))
    (scId : SchedContextId) (hNe : scId ≠ scId0) :
    result.getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?
  rw [hObj]
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable_getElem?_insert st.objects scId0.toObjId (KernelObject.schedContext sc') hInv
    scId.toObjId]
  have hk : ¬(scId0.toObjId == scId.toObjId) = true := fun hEqB =>
    hNe (SchedContextId.toObjId_injective scId scId0 (eq_of_beq hEqB).symm)
  simp only [hk, if_neg, Bool.not_eq_true]

/-- On-key frame: inserting a SchedContext at `scId0`'s slot makes `scId0`
resolve to exactly the inserted SchedContext. -/
private theorem getSchedContext?_insert_schedContext_self (st result : SystemState)
    (scId0 : SchedContextId) (sc' : SchedContext) (hInv : st.objects.invExt)
    (hObj : result.objects = st.objects.insert scId0.toObjId (KernelObject.schedContext sc')) :
    result.getSchedContext? scId0 = some sc' := by
  rw [getSchedContext?_eq_some_iff]
  rw [hObj]
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable_getElem?_insert st.objects scId0.toObjId (KernelObject.schedContext sc') hInv
    scId0.toObjId]
  simp

/-- The read-frame through a bind/unbind-shaped **double insert**: a
SchedContext slot rewritten (off-key resolutions framed, the on-key slot
resolving to the new value), then a TCB slot rewritten `cpuAffinity`-preserving
(every thread's home core framed).  Shared by the bind proofs and the unbind
main arm — the two transitions write the same shape with opposite binding
directions. -/
private theorem double_insert_read_frame
    (st stMid st' : SystemState) (scId0 : SchedContextId) (sc0 sc' : SchedContext)
    (tid0 : ThreadId) (t0 t' : TCB)
    (hInv : st.objects.invExt)
    (hScOld : st.objects.get? scId0.toObjId = some (KernelObject.schedContext sc0))
    (hTcbOld : st.objects.get? tid0.toObjId = some (KernelObject.tcb t0))
    (hAff : t'.cpuAffinity = t0.cpuAffinity)
    (hMidObj : stMid.objects = st.objects.insert scId0.toObjId (KernelObject.schedContext sc'))
    (hObj : st'.objects = stMid.objects.insert tid0.toObjId (KernelObject.tcb t')) :
    (∀ scId, scId ≠ scId0 → st'.getSchedContext? scId = st.getSchedContext? scId) ∧
    (st'.getSchedContext? scId0 = some sc') ∧
    (∀ t, determineTargetCore st' t = determineTargetCore st t) := by
  have hMidInv : stMid.objects.invExt := by
    rw [hMidObj]
    exact st.objects.insert_preserves_invExt scId0.toObjId (KernelObject.schedContext sc') hInv
  have hMidTcb : stMid.objects.get? tid0.toObjId = some (KernelObject.tcb t0) := by
    rw [hMidObj]
    rw [RHTable_getElem?_insert st.objects scId0.toObjId (KernelObject.schedContext sc') hInv
      tid0.toObjId]
    have hk : ¬(scId0.toObjId == tid0.toObjId) = true := by
      intro hEqB
      rw [show scId0.toObjId = tid0.toObjId from eq_of_beq hEqB] at hScOld
      rw [hScOld] at hTcbOld
      cases hTcbOld
    rw [if_neg hk]
    exact hTcbOld
  refine ⟨fun scId hNe => ?_, ?_, fun t => ?_⟩
  · rw [getSchedContext?_insert_tcb_eq stMid st' tid0 t0 t' hMidInv hMidTcb hObj scId]
    exact getSchedContext?_insert_schedContext_ne st stMid scId0 sc' hInv hMidObj scId hNe
  · rw [getSchedContext?_insert_tcb_eq stMid st' tid0 t0 t' hMidInv hMidTcb hObj scId0]
    exact getSchedContext?_insert_schedContext_self st stMid scId0 sc' hInv hMidObj
  · rw [determineTargetCore_insert_tcb stMid st' tid0 t0 t' hMidInv hMidTcb hAff hObj t]
    have hgt : stMid.getTcb? t = st.getTcb? t :=
      getTcb?_insert_schedContext_eq st stMid scId0 sc0 sc' hInv hScOld hMidObj t
    exact determineTargetCore_congr st stMid t (by rw [hgt])

/-- The read-frame through the unbind sweep arm's **single insert**: the
SchedContext slot rewritten, no TCB write at all. -/
private theorem sc_insert_read_frame
    (st st' : SystemState) (scId0 : SchedContextId) (sc0 sc' : SchedContext)
    (hInv : st.objects.invExt)
    (hScOld : st.objects.get? scId0.toObjId = some (KernelObject.schedContext sc0))
    (hObj : st'.objects = st.objects.insert scId0.toObjId (KernelObject.schedContext sc')) :
    (∀ scId, scId ≠ scId0 → st'.getSchedContext? scId = st.getSchedContext? scId) ∧
    (st'.getSchedContext? scId0 = some sc') ∧
    (∀ t, determineTargetCore st' t = determineTargetCore st t) := by
  refine ⟨fun scId hNe => getSchedContext?_insert_schedContext_ne st st' scId0 sc' hInv hObj scId hNe,
          getSchedContext?_insert_schedContext_self st st' scId0 sc' hInv hObj,
          fun t => ?_⟩
  have hgt : st'.getTcb? t = st.getTcb? t :=
    getTcb?_insert_schedContext_eq st st' scId0 sc0 sc' hInv hScOld hObj t
  exact determineTargetCore_congr st st' t (by rw [hgt])

/-- **The `schedContextBind` characterisation**: a successful bind read an
*unbound* SchedContext and an existing TCB, and produced exactly the two-insert
object write — the SchedContext bound to the thread, the TCB bound to the
SchedContext at the SchedContext's priority — with **every replenish queue
untouched**.  The possible home-core run-queue rebucket and the thread-index
update are erased here: only what the invariant proofs read survives. -/
private theorem schedContextBind_ok_char
    (vScId : ValidObjId) (vThreadId : ValidThreadId) (st st' : SystemState)
    (h : schedContextBind vScId vThreadId st = .ok ((), st')) :
    ∃ sc, st.getSchedContext? (SchedContextId.ofObjId vScId.val) = some sc ∧
      sc.boundThread = none ∧
    ∃ tcb, st.getTcb? vThreadId.val = some tcb ∧
      st'.objects = (st.objects.insert vScId.val
          (.schedContext { sc with boundThread := some vThreadId.val })).insert
          vThreadId.val.toObjId
          (.tcb { tcb with
            schedContextBinding := SchedContextBinding.bound ⟨vScId.val.toNat⟩,
            priority := sc.priority }) ∧
      (∀ c, st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c) := by
  simp only [schedContextBind] at h
  cases hSc : st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | none => rw [hSc] at h; cases h
  | some sc =>
    rw [hSc] at h; simp only [] at h
    cases hBT : sc.boundThread with
    | some tid0 => rw [hBT] at h; simp at h
    | none =>
      rw [hBT] at h
      simp only [Option.isSome_none, Bool.false_eq_true, if_false] at h
      refine ⟨sc, rfl, hBT, ?_⟩
      cases hTcb : st.getTcb? vThreadId.val with
      | none => rw [hTcb] at h; cases h
      | some tcb =>
        rw [hTcb] at h; simp only [] at h
        refine ⟨tcb, rfl, ?_⟩
        cases hDom : tcb.domain != sc.domain with
        | true => rw [hDom] at h; simp at h
        | false =>
          rw [hDom] at h
          simp only [Bool.false_eq_true, if_false] at h
          cases hBind : tcb.schedContextBinding with
          | bound scb => rw [hBind] at h; cases h
          | donated scb owner => rw [hBind] at h; cases h
          | unbound =>
            rw [hBind] at h; simp only [] at h
            cases h
            refine ⟨?_, ?_⟩
            · -- objects: both rebucket arms share the double-insert store.
              simp only []
              repeat' split
              all_goals rfl
            · -- the replenish queues: the rebucket writes a run queue only.
              intro c
              simp only []
              repeat' split
              all_goals simp

/-- The read-frame a successful bind leaves behind: queues untouched, every
*other* SchedContext's resolution untouched, every thread's home core untouched
— and the bound SchedContext was, at the pre-state, live and unbound.  The
last piece is what each preservation proof feeds orphan-freedom to rule the
on-key entry out. -/
private theorem schedContextBind_read_frame
    (vScId : ValidObjId) (vThreadId : ValidThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (h : schedContextBind vScId vThreadId st = .ok ((), st')) :
    (∀ c, st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c) ∧
    (∀ scId, scId ≠ SchedContextId.ofObjId vScId.val →
        st'.getSchedContext? scId = st.getSchedContext? scId) ∧
    (∀ t, determineTargetCore st' t = determineTargetCore st t) ∧
    (∃ sc, st.getSchedContext? (SchedContextId.ofObjId vScId.val) = some sc ∧
        sc.boundThread = none) := by
  obtain ⟨sc, hSc, hBT, tcb, hTcb, hObjEq, hQEq⟩ :=
    schedContextBind_ok_char vScId vThreadId st st' h
  have hScRaw : st.objects.get? vScId.val = some (KernelObject.schedContext sc) :=
    (getSchedContext?_eq_some_iff st _ sc).mp hSc
  have hTcbRaw : st.objects.get? vThreadId.val.toObjId = some (KernelObject.tcb tcb) :=
    (getTcb?_eq_some_iff st _ tcb).mp hTcb
  obtain ⟨hOff, _, hTgt⟩ := double_insert_read_frame st
    ({ st with objects := st.objects.insert vScId.val (KernelObject.schedContext { sc with boundThread := some vThreadId.val }) })
    st' (SchedContextId.ofObjId vScId.val) sc { sc with boundThread := some vThreadId.val }
    vThreadId.val tcb
    { tcb with schedContextBinding := SchedContextBinding.bound ⟨vScId.val.toNat⟩,
               priority := sc.priority }
    hObjInv hScRaw hTcbRaw rfl rfl hObjEq
  exact ⟨hQEq, hOff, hTgt, sc, hSc, hBT⟩

/-- **The live `.schedContextBind` arm preserves affinity-consistency** — the
first of the two theorems whose absence the pre-SM10 audit registered.

Orphan-freedom supplies the pivotal fact: the SchedContext being bound was
unbound, so its guard plus `hOrphan` rule out any queue entry naming it — the
one entry class whose obligation the bind *creates* — and every other entry's
three readings are framed by the double insert. -/
theorem schedContextBind_preserves_replenishQueueAffinityConsistent_smp
    (vScId : ValidObjId) (vThreadId : ValidThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hOrphan : replenishQueueEntriesBound_smp st)
    (h : schedContextBind vScId vThreadId st = .ok ((), st')) :
    replenishQueueAffinityConsistent_smp st' := by
  obtain ⟨hQEq, hOff, hTgt, sc, hSc, hBT⟩ :=
    schedContextBind_read_frame vScId vThreadId st st' hObjInv h
  intro c scId₀ t hMem sc₀ hSc₀ tid₀ hTid₀
  rw [hQEq c] at hMem
  by_cases hEqK : scId₀ = SchedContextId.ofObjId vScId.val
  · -- the freshly-bound SchedContext: orphan-freedom + the unbound guard
    -- forbid any pre-state entry, and the bind writes no queue.
    subst hEqK
    obtain ⟨scP, hScP, tidP, hTidP⟩ := hOrphan c _ t hMem
    rw [hSc] at hScP
    cases hScP
    rw [hBT] at hTidP
    cases hTidP
  · rw [hTgt tid₀]
    exact hCons c scId₀ t hMem sc₀ (by rw [← hOff scId₀ hEqK]; exact hSc₀) tid₀ hTid₀

/-- **`schedContextBind` preserves orphan-freedom**: the queues are untouched,
the on-key entry class is empty (same argument as the affinity proof), and
every off-key entry's SchedContext resolution is framed. -/
theorem schedContextBind_preserves_replenishQueueEntriesBound_smp
    (vScId : ValidObjId) (vThreadId : ValidThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hOrphan : replenishQueueEntriesBound_smp st)
    (h : schedContextBind vScId vThreadId st = .ok ((), st')) :
    replenishQueueEntriesBound_smp st' := by
  obtain ⟨hQEq, hOff, _, sc, hSc, hBT⟩ :=
    schedContextBind_read_frame vScId vThreadId st st' hObjInv h
  intro c scId₀ t hMem
  rw [hQEq c] at hMem
  obtain ⟨sc₀, hSc₀, tid₀, hTid₀⟩ := hOrphan c scId₀ t hMem
  by_cases hEqK : scId₀ = SchedContextId.ofObjId vScId.val
  · subst hEqK
    rw [hSc] at hSc₀
    cases hSc₀
    rw [hBT] at hTid₀
    cases hTid₀
  · exact ⟨sc₀, by rw [hOff scId₀ hEqK]; exact hSc₀, tid₀, hTid₀⟩

/-- `schedContextBind` preserves the object store's extended invariant — its
whole object footprint is two plain inserts. -/
theorem schedContextBind_preserves_objects_invExt
    (vScId : ValidObjId) (vThreadId : ValidThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (h : schedContextBind vScId vThreadId st = .ok ((), st')) :
    st'.objects.invExt := by
  obtain ⟨sc, _, _, tcb, _, hObjEq, _⟩ := schedContextBind_ok_char vScId vThreadId st st' h
  rw [hObjEq]
  exact (st.objects.insert _ _).insert_preserves_invExt _ _
    (st.objects.insert_preserves_invExt _ _ hObjInv)

/-- `schedContextUnbind` preserves the object store's extended invariant — two
plain inserts on the main arm, one on the sweep arm (the purges are
scheduler-only writes, already erased by the characterisation). -/
theorem schedContextUnbind_preserves_objects_invExt
    (vScId : ValidObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (h : schedContextUnbind vScId st = .ok ((), st')) :
    st'.objects.invExt := by
  obtain ⟨sc, _, tid, _, hArm⟩ := schedContextUnbind_ok_char vScId st st' h
  rcases hArm with ⟨tcb, _, hObjEq, _⟩ | ⟨_, hObjEq, _⟩ <;> rw [hObjEq]
  · exact (st.objects.insert _ _).insert_preserves_invExt _ _
      (st.objects.insert_preserves_invExt _ _ hObjInv)
  · exact st.objects.insert_preserves_invExt _ _ hObjInv

/-- **`schedContextUnbind` preserves affinity-consistency** — with *no*
orphan-freedom hypothesis: the entry class whose obligation the unbind changes
is its own SchedContext's, and post-state that SchedContext is unbound, so
those entries' obligations are vacuous wherever they survive; every other
entry's readings are framed, and its membership descends through the purge. -/
theorem schedContextUnbind_preserves_replenishQueueAffinityConsistent_smp
    (vScId : ValidObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : schedContextUnbind vScId st = .ok ((), st')) :
    replenishQueueAffinityConsistent_smp st' := by
  obtain ⟨sc, hSc, tid, hBT, hArm⟩ := schedContextUnbind_ok_char vScId st st' h
  have hScRaw : st.objects.get? vScId.val = some (KernelObject.schedContext sc) :=
    (getSchedContext?_eq_some_iff st _ sc).mp hSc
  rcases hArm with ⟨tcb, hTcb, hObjEq, hQEq⟩ | ⟨hTcb, hObjEq, hQEq⟩
  · -- main arm: double insert + home-core purge.
    have hTcbRaw : st.objects.get? tid.toObjId = some (KernelObject.tcb tcb) :=
      (getTcb?_eq_some_iff st _ tcb).mp hTcb
    obtain ⟨hOff, hSelf, hTgt⟩ := double_insert_read_frame st
      ({ st with objects := st.objects.insert vScId.val (KernelObject.schedContext { sc with boundThread := none, isActive := false }) })
      st' (SchedContextId.ofObjId vScId.val) sc { sc with boundThread := none, isActive := false }
      tid tcb { tcb with schedContextBinding := SchedContextBinding.unbound }
      hObjInv hScRaw hTcbRaw rfl rfl hObjEq
    intro c scId₀ t hMem sc₀ hSc₀ tid₀ hTid₀
    rw [hQEq c] at hMem
    by_cases hEqK : scId₀ = SchedContextId.ofObjId vScId.val
    · -- the unbound SchedContext: its post-state `boundThread` is `none`.
      subst hEqK
      rw [hSelf] at hSc₀
      cases hSc₀
      cases hTid₀
    · have hMemPre : (scId₀, t) ∈ (st.scheduler.replenishQueueOnCore c).entries := by
        by_cases hHome : determineTargetCore st tid = c
        · rw [if_pos hHome] at hMem; exact (mem_remove_entries hMem).1
        · rw [if_neg hHome] at hMem; exact hMem
      rw [hTgt tid₀]
      exact hCons c scId₀ t hMemPre sc₀ (by rw [← hOff scId₀ hEqK]; exact hSc₀) tid₀ hTid₀
  · -- sweep arm: single insert + all-cores purge.
    obtain ⟨hOff, hSelf, hTgt⟩ := sc_insert_read_frame st st'
      (SchedContextId.ofObjId vScId.val) sc { sc with boundThread := none, isActive := false }
      hObjInv hScRaw hObjEq
    intro c scId₀ t hMem sc₀ hSc₀ tid₀ hTid₀
    rw [hQEq c] at hMem
    obtain ⟨hMemPre, hNeK⟩ := mem_remove_entries hMem
    rw [hTgt tid₀]
    exact hCons c scId₀ t hMemPre sc₀ (by rw [← hOff scId₀ hNeK]; exact hSc₀) tid₀ hTid₀

/-- **`schedContextUnbind` re-establishes orphan-freedom** for its SchedContext
and preserves it for every other: on the home core the purge removes the
SchedContext's entries outright; on every other core, pre-state
affinity-consistency proves it never had one there (all its entries sat on the
bound thread's home core — the core the purge targets).  This is the
mutual-dependence direction: unbind's orphan-freedom *needs* affinity, exactly
as bind's affinity needs orphan-freedom. -/
theorem schedContextUnbind_preserves_replenishQueueEntriesBound_smp
    (vScId : ValidObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hOrphan : replenishQueueEntriesBound_smp st)
    (h : schedContextUnbind vScId st = .ok ((), st')) :
    replenishQueueEntriesBound_smp st' := by
  obtain ⟨sc, hSc, tid, hBT, hArm⟩ := schedContextUnbind_ok_char vScId st st' h
  have hScRaw : st.objects.get? vScId.val = some (KernelObject.schedContext sc) :=
    (getSchedContext?_eq_some_iff st _ sc).mp hSc
  rcases hArm with ⟨tcb, hTcb, hObjEq, hQEq⟩ | ⟨hTcb, hObjEq, hQEq⟩
  · -- main arm.
    have hTcbRaw : st.objects.get? tid.toObjId = some (KernelObject.tcb tcb) :=
      (getTcb?_eq_some_iff st _ tcb).mp hTcb
    obtain ⟨hOff, _, _⟩ := double_insert_read_frame st
      ({ st with objects := st.objects.insert vScId.val (KernelObject.schedContext { sc with boundThread := none, isActive := false }) })
      st' (SchedContextId.ofObjId vScId.val) sc { sc with boundThread := none, isActive := false }
      tid tcb { tcb with schedContextBinding := SchedContextBinding.unbound }
      hObjInv hScRaw hTcbRaw rfl rfl hObjEq
    intro c scId₀ t hMem
    rw [hQEq c] at hMem
    by_cases hHome : determineTargetCore st tid = c
    · -- home core: the purge removed the SchedContext's entries.
      rw [if_pos hHome] at hMem
      obtain ⟨hMemPre, hNeK⟩ := mem_remove_entries hMem
      obtain ⟨sc₀, hSc₀, tid₀, hTid₀⟩ := hOrphan c scId₀ t hMemPre
      exact ⟨sc₀, by rw [hOff scId₀ hNeK]; exact hSc₀, tid₀, hTid₀⟩
    · -- non-home core: pre-affinity proves the SchedContext never had an
      -- entry here, and every other entry is framed.
      rw [if_neg hHome] at hMem
      by_cases hEqK : scId₀ = SchedContextId.ofObjId vScId.val
      · subst hEqK
        exact absurd (hCons c _ t hMem sc hSc tid hBT) hHome
      · obtain ⟨sc₀, hSc₀, tid₀, hTid₀⟩ := hOrphan c scId₀ t hMem
        exact ⟨sc₀, by rw [hOff scId₀ hEqK]; exact hSc₀, tid₀, hTid₀⟩
  · -- sweep arm: every core purged, so every survivor is off-key.
    obtain ⟨hOff, _, _⟩ := sc_insert_read_frame st st'
      (SchedContextId.ofObjId vScId.val) sc { sc with boundThread := none, isActive := false }
      hObjInv hScRaw hObjEq
    intro c scId₀ t hMem
    rw [hQEq c] at hMem
    obtain ⟨hMemPre, hNeK⟩ := mem_remove_entries hMem
    obtain ⟨sc₀, hSc₀, tid₀, hTid₀⟩ := hOrphan c scId₀ t hMemPre
    exact ⟨sc₀, by rw [hOff scId₀ hNeK]; exact hSc₀, tid₀, hTid₀⟩

-- ============================================================================
-- §5  `schedContextUnbindOnCore` — the live `.schedContextUnbind` dispatch arm
-- ============================================================================

/-- **The live `.schedContextUnbind` dispatch arm preserves
affinity-consistency** — the second registered theorem.  The wrapper adds a
scheduling point to the unbind; `priorityRescheduleOnCore_state_cases` reduces
it to two outcomes, and the reschedule receiver's queue / `boundThread` /
home-core frames carry the invariant through the one that changes state. -/
theorem schedContextUnbindOnCore_preserves_replenishQueueAffinityConsistent_smp
    (vScId : ValidObjId) (executingCore : CoreId) (st st' : SystemState)
    (sgi? : Option (CoreId × SgiKind))
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : schedContextUnbindOnCore vScId executingCore st = .ok (st', sgi?)) :
    replenishQueueAffinityConsistent_smp st' := by
  unfold schedContextUnbindOnCore at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · next u stU hUnbind =>
    have hCU : replenishQueueAffinityConsistent_smp stU :=
      schedContextUnbind_preserves_replenishQueueAffinityConsistent_smp vScId st stU
        hObjInv hCons hUnbind
    have hInvU : stU.objects.invExt :=
      schedContextUnbind_preserves_objects_invExt vScId st stU hObjInv hUnbind
    rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases stU st'
        (schedContextRunningCore? st vScId.val) executingCore true sgi? h with hEq | hSgi
    · rw [hEq]; exact hCU
    · intro c
      exact replenishQueueAffinityConsistentOnCore_transfer stU st' c
        (fun e hMem => by
          rw [handleRescheduleSgiOnCore_replenishQueueOnCore stU executingCore st' c hSgi]
            at hMem
          exact hMem)
        (fun scId => handleRescheduleSgiOnCore_boundThread stU executingCore st' hInvU hSgi scId)
        (fun t => handleRescheduleSgiOnCore_determineTargetCore stU executingCore st' hInvU hSgi t)
        (hCU c)

/-- **The live `.schedContextUnbind` dispatch arm preserves orphan-freedom** —
same decomposition, through the orphan-freedom transfer. -/
theorem schedContextUnbindOnCore_preserves_replenishQueueEntriesBound_smp
    (vScId : ValidObjId) (executingCore : CoreId) (st st' : SystemState)
    (sgi? : Option (CoreId × SgiKind))
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hOrphan : replenishQueueEntriesBound_smp st)
    (h : schedContextUnbindOnCore vScId executingCore st = .ok (st', sgi?)) :
    replenishQueueEntriesBound_smp st' := by
  unfold schedContextUnbindOnCore at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · next u stU hUnbind =>
    have hOU : replenishQueueEntriesBound_smp stU :=
      schedContextUnbind_preserves_replenishQueueEntriesBound_smp vScId st stU
        hObjInv hCons hOrphan hUnbind
    have hInvU : stU.objects.invExt :=
      schedContextUnbind_preserves_objects_invExt vScId st stU hObjInv hUnbind
    rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases stU st'
        (schedContextRunningCore? st vScId.val) executingCore true sgi? h with hEq | hSgi
    · rw [hEq]; exact hOU
    · intro c
      exact replenishQueueEntriesBoundOnCore_transfer stU st' c
        (fun e hMem => by
          rw [handleRescheduleSgiOnCore_replenishQueueOnCore stU executingCore st' c hSgi]
            at hMem
          exact hMem)
        (fun scId => handleRescheduleSgiOnCore_boundThread stU executingCore st' hInvU hSgi scId)
        (hOU c)

end SeLe4n.Kernel
