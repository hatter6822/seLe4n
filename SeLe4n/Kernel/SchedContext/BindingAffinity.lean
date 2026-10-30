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

* §2 — the queue primitives preserve orphan-freedom: the purge
  (unconditionally — it only removes entries), the migration (unconditionally
  — moved entries existed before), and `replenishOnCore` (given the placed
  SchedContext is bound, the same shape as its affinity obligation
  `hTarget`).

* §3/§4 — the characterisations of `schedContextUnbind` / `schedContextBind`,
  and the four preservation theorems: unbind preserves affinity with **no**
  orphan-freedom hypothesis, and re-establishes orphan-freedom for its
  SchedContext with **no** affinity hypothesis, because the purge removes the
  context's entry from whichever core holds it, read from the context's own
  link (WS-ZA ZA6.3); bind preserves both, with orphan-freedom supplying the
  no-entries fact its affinity proof turns on.

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

/-- Orphan-freedom's per-entry reading transfers along a `boundThread`
projection agreement. -/
private theorem bound_transfer {a b : Option SchedContext}
    (hM : a.map (·.boundThread) = b.map (·.boundThread))
    (hb : ∃ sc, b = some sc ∧ ∃ tid, sc.boundThread = some tid) :
    ∃ sc, a = some sc ∧ ∃ tid, sc.boundThread = some tid := by
  obtain ⟨sc, rfl, tid, ht⟩ := hb
  cases a with
  | none => simp at hM
  | some sc' =>
    simp only [Option.map_some, Option.some.injEq] at hM
    exact ⟨sc', rfl, tid, hM.trans ht⟩

/-- The purge preserves orphan-freedom on every core, unconditionally: it only
removes entries, and it writes no context's bound thread. -/
theorem purgeReplenishment_preserves_replenishQueueEntriesBoundOnCore
    (st : SystemState) (scId : SchedContextId) (c : CoreId)
    (hCons : replenishQueueEntriesBoundOnCore st c) :
    replenishQueueEntriesBoundOnCore (purgeReplenishment st scId) c :=
  replenishQueueEntriesBoundOnCore_transfer st _ c
    (purgeReplenishment_entries_subset st scId c)
    ((purgeReplenishment_agree st scId).getSchedContext?_map (·.boundThread) (fun _ => rfl))
    hCons

/-- The scheduling insert preserves orphan-freedom on every core, given the
SchedContext being placed exists and is bound — the orphan-freedom face of the
same obligation its affinity preservation carries as `hTarget`, and one the
live CBS enqueue sites satisfy by construction (they read `scId` off a
binding).  Placing adds no entry but the placed context's own
(`releasePlace_entries_provenance`). -/
theorem replenishOnCore_preserves_replenishQueueEntriesBoundOnCore
    (st : SystemState) (c c' : CoreId) (scId : SchedContextId)
    (hCons : replenishQueueEntriesBoundOnCore st c')
    (hBound : ∃ sc, st.getSchedContext? scId = some sc ∧ ∃ tid, sc.boundThread = some tid) :
    replenishQueueEntriesBoundOnCore (replenishOnCore st c scId) c' := by
  intro scId₀ t hMem
  have hBt := (SystemState.releasePlace_agree st c scId).getSchedContext?_map
    (·.boundThread) (fun _ => rfl)
  rcases SystemState.releasePlace_entries_provenance st c scId c' _ hMem with hOld | hEq
  · exact bound_transfer (hBt scId₀) (hCons scId₀ t hOld)
  · have hS : scId₀ = scId := hEq
    subst hS
    exact bound_transfer (hBt scId₀) hBound

/-- The SM5.H.4 migration preserves orphan-freedom on every core,
unconditionally: it moves entries that already existed (the provenance
decomposition) and writes no context's bound thread. -/
theorem migrateSchedContextReplenishment_preserves_replenishQueueEntriesBound_smp
    (st : SystemState) (scId : SchedContextId) (fromCore toCore : CoreId)
    (hCons : replenishQueueEntriesBound_smp st) :
    replenishQueueEntriesBound_smp
      (migrateSchedContextReplenishment st scId fromCore toCore) := by
  intro c scId₀ t hMem
  have hBt := migrateSchedContextReplenishment_boundThread st scId fromCore toCore
  by_cases hSelf : fromCore = toCore
  · subst hSelf
    rw [migrateSchedContextReplenishment_noop] at hMem ⊢
    exact hCons c scId₀ t hMem
  · refine bound_transfer (hBt scId₀) ?_
    by_cases hTo : c = toCore
    · subst hTo
      rcases migrateSchedContextReplenishment_mem_toCore st scId fromCore c hSelf _ hMem with
        hOld | ⟨_, hFrom⟩
      · exact hCons c scId₀ t hOld
      · exact hCons fromCore scId₀ t hFrom
    · by_cases hFrom : c = fromCore
      · subst hFrom
        rw [migrateSchedContextReplenishment_replenishQueueOnCore_from st scId c toCore hSelf]
          at hMem
        exact hCons c scId₀ t (mem_remove_entries hMem).1
      · rw [migrateSchedContextReplenishment_replenishQueueOnCore_other st scId fromCore toCore c
          (Ne.symm hFrom) (Ne.symm hTo)] at hMem
        exact hCons c scId₀ t hMem

-- ============================================================================
-- §3  `schedContextUnbind` — the revocation side of the binding lifecycle
-- ============================================================================
-- **WS-RR RR7.39**: `SystemState` gained the `schedulerLocks` field (the state
-- representation of `LockKey.runQueue` / `.replenishQueue`), so every
-- structural `isDefEq` over a `SystemState` record update compares one more
-- field.  This characterisation rewrites through a `match` on `getTcb?` whose
-- motive abstracts two such updates, and it was already the tree's most
-- expensive scheduler-context proof; the extra field pushes it past the default
-- budget.  Raised here rather than restructured because the cost is structural
-- (field count), not a proof-search pathology.
/-- A SchedContext rewrite then a TCB update keeps the object store's invariant
(the two writes are plain inserts). -/
private theorem rewrite_updateTcb_objects_invExt (st0 : SystemState) (id : SeLe4n.ObjId)
    (sc' : SchedContext) (h : st0.rewriteAdmissible id (.schedContext sc'))
    (tid : ThreadId) (t : TCB) (f : TCB → TCB)
    (hInv : st0.objects.invExt) (hT : st0.getTcb? tid = some t) :
    ((st0.rewriteObject id (.schedContext sc') h).updateTcb tid f).objects.invExt := by
  rw [SystemState.updateTcb_after_rewriteObject_schedContext_objects st0 id sc' h tid t f hInv hT]
  exact (st0.objects.insert _ _).insert_preserves_invExt _ _
    (st0.objects.insert_preserves_invExt _ _ hInv)

private theorem purge_insert_entries (st : SystemState) (x : SeLe4n.ObjId) (k : SchedContextId)
    (hk : k.toObjId = x) (sc sc' : SchedContext) (hSc : st.getSchedContext? k = some sc)
    (hInv : st.objects.invExt) (hf : sc'.releaseCoreCode = sc.releaseCoreCode)
    (c : CoreId) (e : SchedContextId × Nat)
    (he : e ∈ ((purgeReplenishment { st with objects := st.objects.insert x (.schedContext sc') } k
      ).scheduler.replenishQueueOnCore c).entries) :
    e ∈ (st.scheduler.replenishQueueOnCore c).entries ∧
      (e.1 = k → st.releaseCoreOf k ≠ some c) := by
  subst hk
  have h1 := purgeReplenishment_entries_subset _ _ c e he
  have h2 := fun hs => purgeReplenishment_entries_self _ _ c e he hs
  refine ⟨h1, fun hs hc => h2 hs ?_⟩
  rw [← hc]
  exact SystemState.releaseCoreOf_insert_schedContext st k sc sc' hSc hInv hf k

set_option maxHeartbeats 800000 in
/-- **The `schedContextUnbind` characterisation**: a successful unbind read a
SchedContext bound to `tid` and produced exactly one of two shapes — the main
arm (the bound TCB exists: both binding sides cleared) or the sweep arm (the
TCB is gone: the SC side cleared).  On both, every core's queue loses exactly
the context's entries: the purge is read from the context's own link, so no
home core is computed and no other core is swept.

The scheduler writes the invariant proofs below do *not* need to see — the
current-clear, the home-queue rebucket, the release-link rewrites — are already
erased here: only the replenish-queue reading survives, stated per core. -/
private theorem schedContextUnbind_ok_char
    (vScId : ValidObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (h : schedContextUnbind vScId st = .ok ((), st')) :
    ∃ sc, st.getSchedContext? (SchedContextId.ofObjId vScId.val) = some sc ∧
    ∃ tid, sc.boundThread = some tid ∧
    (∀ c e, e ∈ (st'.scheduler.replenishQueueOnCore c).entries →
      e ∈ (st.scheduler.replenishQueueOnCore c).entries ∧
      (e.1 = (⟨vScId.val.toNat⟩ : SchedContextId) →
        st.releaseCoreOf ⟨vScId.val.toNat⟩ ≠ some c)) ∧
    st'.objects.invExt ∧
    ((∃ tcb, st.getTcb? tid = some tcb ∧
        st'.objectsAgreeOffSchedulerLinks { st with objects := ((st.objects.insert vScId.val
            (.schedContext { sc with boundThreadCode := 0, isActive := false,
                                     donationOrigin := none })).insert
            tid.toObjId (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 })) })
     ∨ (st.getTcb? tid = none ∧
        st'.objectsAgreeOffReleaseLinks { st with objects := (st.objects.insert vScId.val
            (.schedContext { sc with boundThreadCode := 0, isActive := false,
                                     donationOrigin := none })) })) := by
  simp only [schedContextUnbind] at h
  cases hSc : st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | none => rw [SystemState.getSchedContextWitnessed?_eq_none hSc] at h; cases h
  | some sc =>
    rw [SystemState.getSchedContextWitnessed?_eq_some hSc] at h; simp only [] at h
    cases hBT : sc.boundThread with
    | none => rw [hBT] at h; cases h
    | some tid =>
      rw [hBT] at h; simp only [] at h
      refine ⟨sc, rfl, tid, hBT, ?_⟩
      cases hTcb : st.getTcb? tid with
      | some tcb =>
        rw [hTcb] at h; simp only [] at h
        -- `v0.35.4`: a donated holder is refused, so a successful unbind saw a
        -- binding that is not a donation.
        have hNotDon : tcb.schedContextBinding.isDonated = false := by
          cases hD : tcb.schedContextBinding.isDonated with
          | false => rfl
          | true => rw [hD] at h; simp at h
        simp only [hNotDon, Bool.false_eq_true, if_false] at h
        cases h
        refine ⟨?_, ?_, Or.inl ⟨tcb, rfl, ?_⟩⟩
        · -- the replenish queues: only the purge touches them, on the core
          -- the context's own link names.
          intro c e he
          simp only [markKeyChangeFor_replenishQueueOnCore,
            markCandidacyGainFor_replenishQueueOnCore] at he
          have hm := purgeReplenishment_entries_subset _ _ c e he
          rw [schedContextUnbindQueueStage_replenishQueueOnCore] at hm
          refine ⟨by
            revert hm
            cases hRun : Lifecycle.Suspend.runningCoreOf? st tid <;> intro hm <;>
              simpa [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler] using hm,
            fun hs hc => purgeReplenishment_entries_self _ _ c e he hs ?_⟩
          rw [← hc]
          refine (SystemState.releaseCoreOf_of_runLinks
            (schedContextUnbindQueueStage_objectsAgreeOffRunLinks _ _ _ _ _) _).trans ?_
          refine (SystemState.releaseCoreOf_updateTcb _ _ _ ?_ _).trans ?_
          · exact SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hObjInv
          · apply SystemState.releaseCoreOf_rewrite_of_objects (st := st) (sc := sc) (k := ⟨vScId.val.toNat⟩)
            · rfl
            · rfl
            · exact hSc
            · exact hObjInv
            · rfl
        · rw [markKeyChangeFor_objects, markCandidacyGainFor_objects]
          refine purgeReplenishment_objects_invExt _ _
            (schedContextUnbindQueueStage_objects_invExt _ _ _ _ _ ?_)
          exact rewrite_updateTcb_objects_invExt _ _ _ _ tid tcb _ hObjInv hTcb
        · -- objects: the purge writes release links, the run-queue stage
          -- run-queue links (WS-ZA ZA4.5), and the current-slot stage is a
          -- scheduler-only update of the pre-state, so the two typed writes over
          -- it reduce to the double insert whatever the stage's scheduler is.
          refine SystemState.objectsAgreeOffSchedulerLinks.trans (st' := purgeReplenishment _ _)
            (.of_objects_eq (by rw [markKeyChangeFor_objects, markCandidacyGainFor_objects])) ?_
          refine (SystemState.objectsAgreeOffSchedulerLinks.of_releaseLinks
            (purgeReplenishment_agree _ _)).trans ?_
          refine (SystemState.objectsAgreeOffSchedulerLinks.of_runLinks
            (schedContextUnbindQueueStage_objectsAgreeOffRunLinks _ _ _ _ _)).trans ?_
          exact SystemState.objectsAgreeOffSchedulerLinks.of_objects_eq
            (SystemState.updateTcb_after_rewriteObject_schedContext_objects
              _ vScId.val _ _ tid tcb _ hObjInv hTcb)
      | none =>
        rw [hTcb] at h; simp only [] at h
        have hSt' : _ = st' := congrArg Prod.snd (Except.ok.inj h)
        dsimp only [SystemState.rewriteObject] at hSt'
        subst hSt'
        refine ⟨?_, ?_, Or.inr ⟨by first | exact hTcb | exact rfl, ?_⟩⟩
        · intro c e he
          apply purge_insert_entries (st := st) (sc := sc) (k := ⟨vScId.val.toNat⟩)
            (x := vScId.val) (hk := by rfl) (hSc := hSc) (hInv := hObjInv) (hf := by rfl) (he := he)
        · exact purgeReplenishment_objects_invExt _ _ (st.objects.insert_preserves_invExt _ _ hObjInv)
        · exact purgeReplenishment_agree _ _

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

/-- A scheduler-link step moves no context's bound thread. -/
private theorem boundThread_of_schedulerLinks {st' D : SystemState}
    (hA : st'.objectsAgreeOffSchedulerLinks D) (s : SchedContextId) :
    (st'.getSchedContext? s).map (·.boundThread) = (D.getSchedContext? s).map (·.boundThread) := by
  have e := congrArg (Option.map (·.boundThread)) (hA.getSchedContext? s)
  simp only [Option.map_map] at e
  exact e

/-- ...and no thread's home core: `determineTargetCore` reads `cpuAffinity`. -/
private theorem determineTargetCore_of_schedulerLinks {st' D : SystemState}
    (hA : st'.objectsAgreeOffSchedulerLinks D) (t : ThreadId) :
    determineTargetCore st' t = determineTargetCore D t :=
  determineTargetCore_congr D st' t
    (TCB.map_proj_eq_of_map_withoutRunLinks_eq (·.cpuAffinity) (hA.getTcb? t))

/-- A post-state context read back to the pre-state along a `boundThread`
projection agreement. -/
private theorem boundThread_pull {a b : Option SchedContext} {sc₀ : SchedContext}
    (hM : a.map (·.boundThread) = b.map (·.boundThread)) (ha : a = some sc₀) :
    ∃ sc, b = some sc ∧ sc.boundThread = sc₀.boundThread := by
  subst ha
  cases b with
  | none => simp at hM
  | some sc =>
    simp only [Option.map_some, Option.some.injEq] at hM
    exact ⟨sc, rfl, hM.symm⟩

/-- **The unbind's read frame**, one shape for both arms: every queue loses
exactly the context's entries; every other context keeps its bound thread; the
unbound context binds none; every thread keeps its home core.  The run-queue
and release-link writes are invisible to every reading here (WS-ZA ZA4.5,
ZA6.3). -/
private theorem unbind_read_frame (vScId : ValidObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (h : schedContextUnbind vScId st = .ok ((), st')) :
    (∀ c e, e ∈ (st'.scheduler.replenishQueueOnCore c).entries →
      e ∈ (st.scheduler.replenishQueueOnCore c).entries ∧
      (e.1 = (⟨vScId.val.toNat⟩ : SchedContextId) →
        st.releaseCoreOf ⟨vScId.val.toNat⟩ ≠ some c)) ∧
    (∀ scId, scId ≠ SchedContextId.ofObjId vScId.val →
      (st'.getSchedContext? scId).map (·.boundThread)
        = (st.getSchedContext? scId).map (·.boundThread)) ∧
    ((st'.getSchedContext? (SchedContextId.ofObjId vScId.val)).map (·.boundThread) = some none) ∧
    (∀ t, determineTargetCore st' t = determineTargetCore st t) ∧
    st'.objects.invExt := by
  obtain ⟨sc, hSc, tid, _, hQ, hInv', hArm⟩ := schedContextUnbind_ok_char vScId st st' hObjInv h
  have hScRaw : st.objects.get? vScId.val = some (KernelObject.schedContext sc) :=
    (getSchedContext?_eq_some_iff st _ sc).mp hSc
  have key : ∃ D : SystemState, st'.objectsAgreeOffSchedulerLinks D ∧
      (∀ scId, scId ≠ SchedContextId.ofObjId vScId.val →
        D.getSchedContext? scId = st.getSchedContext? scId) ∧
      D.getSchedContext? (SchedContextId.ofObjId vScId.val) =
        some { sc with boundThreadCode := 0, isActive := false, donationOrigin := none } ∧
      (∀ t, determineTargetCore D t = determineTargetCore st t) := by
    rcases hArm with ⟨tcb, hTcb, hA⟩ | ⟨_, hA⟩
    · have hTcbRaw : st.objects.get? tid.toObjId = some (KernelObject.tcb tcb) :=
        (getTcb?_eq_some_iff st _ tcb).mp hTcb
      obtain ⟨hOff, hSelf, hTgt⟩ := double_insert_read_frame st
        ({ st with objects := st.objects.insert vScId.val (KernelObject.schedContext
            { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) })
        (SchedContextId.ofObjId vScId.val) sc
        { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }
        tid tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }
        hObjInv hScRaw hTcbRaw rfl rfl (st' := { st with objects := ((st.objects.insert vScId.val (.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })).insert tid.toObjId (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 })) }) rfl
      exact ⟨_, hA, hOff, hSelf, hTgt⟩
    · obtain ⟨hOff, hSelf, hTgt⟩ := sc_insert_read_frame st
        { st with objects := (st.objects.insert vScId.val (.schedContext
            { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })) }
        (SchedContextId.ofObjId vScId.val) sc
        { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }
        hObjInv hScRaw rfl
      exact ⟨_, .of_releaseLinks hA, hOff, hSelf, hTgt⟩
  obtain ⟨D, hA, hOff, hSelf, hTgt⟩ := key
  refine ⟨hQ, fun scId hNe => ?_, ?_, fun t => ?_, hInv'⟩
  · rw [boundThread_of_schedulerLinks hA, hOff scId hNe]
  · rw [boundThread_of_schedulerLinks hA, hSelf]; rfl
  · rw [determineTargetCore_of_schedulerLinks hA, hTgt]
/-- **The `schedContextBind` characterisation**: a successful bind read an
*unbound* SchedContext and an existing TCB, and produced exactly the two-insert
object write — the SchedContext bound to the thread, the TCB bound to the
SchedContext at the SchedContext's priority — with **every replenish queue
untouched**.  The possible home-core run-queue rebucket and the thread-index
update are erased here: only what the invariant proofs read survives. -/
private theorem schedContextBind_ok_char
    (vScId : ValidObjId) (vThreadId : ValidThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (h : schedContextBind vScId vThreadId st = .ok ((), st')) :
    ∃ sc, st.getSchedContext? (SchedContextId.ofObjId vScId.val) = some sc ∧
      sc.boundThread = none ∧
    ∃ tcb, st.getTcb? vThreadId.val = some tcb ∧
      st'.objectsAgreeOffRunLinks { st with objects := ((st.objects.insert vScId.val
          (.schedContext { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val),
                                   donationOrigin := none })).insert
          vThreadId.val.toObjId
          (.tcb { tcb with
            scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (SchedContextBinding.bound ⟨vScId.val.toNat⟩), scBindingOwnerCode := 0,
            priority := sc.priority })) } ∧
      st'.objects.invExt ∧
      (∀ c, st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c) := by
  simp only [schedContextBind] at h
  cases hSc : st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | none => rw [SystemState.getSchedContextWitnessed?_eq_none hSc] at h; cases h
  | some sc =>
    rw [SystemState.getSchedContextWitnessed?_eq_some hSc] at h; simp only [] at h
    cases hBT : sc.boundThread with
    | some tid0 => rw [hBT] at h; simp at h
    | none =>
      rw [hBT] at h
      simp only [Option.isSome_none, Bool.false_eq_true, if_false] at h
      -- `v0.35.4`: a context heading a reply stack is refused, so a successful
      -- bind saw none.
      have hNoHead : sc.scReply.isSome = false := by
        cases hH : sc.scReply.isSome with
        | false => rfl
        | true => rw [hH] at h; simp at h
      simp only [hNoHead, Bool.false_eq_true, if_false] at h
      refine ⟨sc, rfl, hBT, ?_⟩
      cases hTcb : st.getTcb? vThreadId.val with
      | none => rw [hTcb] at h; cases h
      | some tcb =>
        rw [hTcb] at h; simp only [] at h
        -- `v0.35.4`: and a thread whose reply frame is on a live stack is refused.
        have hNoLive : replyFrameOnLiveStack st tcb = false := by
          cases hL : replyFrameOnLiveStack st tcb with
          | false => rfl
          | true => rw [hL] at h; split at h <;> simp at h
        simp only [hNoLive, Bool.false_eq_true, if_false] at h
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
            -- `v0.35.71`: the two typed writes over `st`, reduced to the double
            -- insert under the pre-state's TCB witness.
            rw [SystemState.updateTcb_after_rewriteObject_schedContext st vScId.val _ _
              vThreadId.val tcb _ hObjInv hTcb] at h
            cases h
            refine ⟨?_, ?_, ?_⟩
            · -- objects: both rebucket arms move the thread through its TCB
              -- run-queue links over the double-insert store (WS-ZA ZA4.5), and
              -- the reschedule-pending hook writes no object.
              intro x
              simp only [markKeyChangeFor_objects]
              split
              · exact SystemState.runRequeueOnCore_objectsAgreeOffRunLinks _ _ _ _ x
              · split
                · exact SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _ x
                · rfl
            · simp only [markKeyChangeFor_objects]
              split
              · exact SystemState.runRequeueOnCore_objects_invExt _ _ _ _
                  ((st.objects.insert _ _).insert_preserves_invExt _ _
                    (st.objects.insert_preserves_invExt _ _ hObjInv))
              · split
                · exact SystemState.runEnqueueOnCore_objects_invExt _ _ _ _
                    ((st.objects.insert _ _).insert_preserves_invExt _ _
                      (st.objects.insert_preserves_invExt _ _ hObjInv))
                · exact (st.objects.insert _ _).insert_preserves_invExt _ _
                    (st.objects.insert_preserves_invExt _ _ hObjInv)
            · -- the replenish queues: the rebucket writes a run queue (and the
              -- placement arm a reschedule-pending flag) only.
              intro c
              simp only [markKeyChangeFor_replenishQueueOnCore]
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
  obtain ⟨sc, hSc, hBT, tcb, hTcb, hA, _, hQEq⟩ :=
    schedContextBind_ok_char vScId vThreadId st st' hObjInv h
  have hScRaw : st.objects.get? vScId.val = some (KernelObject.schedContext sc) :=
    (getSchedContext?_eq_some_iff st _ sc).mp hSc
  have hTcbRaw : st.objects.get? vThreadId.val.toObjId = some (KernelObject.tcb tcb) :=
    (getTcb?_eq_some_iff st _ tcb).mp hTcb
  -- The frame is the double insert's; the bind's run-queue link writes are
  -- invisible to every reading below (WS-ZA ZA4.5).
  obtain ⟨hOff, _, hTgt⟩ := double_insert_read_frame st
    ({ st with objects := st.objects.insert vScId.val (KernelObject.schedContext
        { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val), donationOrigin := none }) })
    { st with objects := (st.objects.insert vScId.val (KernelObject.schedContext { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val), donationOrigin := none })).insert vThreadId.val.toObjId (KernelObject.tcb { tcb with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (SchedContextBinding.bound ⟨vScId.val.toNat⟩), scBindingOwnerCode := 0, priority := sc.priority }) }
    (SchedContextId.ofObjId vScId.val) sc
    { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val), donationOrigin := none }
    vThreadId.val tcb
    { tcb with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (SchedContextBinding.bound ⟨vScId.val.toNat⟩), scBindingOwnerCode := 0,
               priority := sc.priority }
    hObjInv hScRaw hTcbRaw rfl rfl rfl
  exact ⟨hQEq, fun scId hNe => (hA.getSchedContext? scId).trans (hOff scId hNe),
    fun t => (determineTargetCore_of_objectsAgreeOffRunLinks hA t).trans (hTgt t), sc, hSc, hBT⟩

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
object footprint is two plain inserts and the run-queue link writes. -/
theorem schedContextBind_preserves_objects_invExt
    (vScId : ValidObjId) (vThreadId : ValidThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (h : schedContextBind vScId vThreadId st = .ok ((), st')) :
    st'.objects.invExt := by
  obtain ⟨_, _, _, _, _, _, hInv', _⟩ := schedContextBind_ok_char vScId vThreadId st st' hObjInv h
  exact hInv'

/-- `schedContextUnbind` preserves the object store's extended invariant — two
plain inserts, the run-queue link writes and the release-link purge on the main
arm, one insert and the purge on the sweep arm. -/
theorem schedContextUnbind_preserves_objects_invExt
    (vScId : ValidObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (h : schedContextUnbind vScId st = .ok ((), st')) :
    st'.objects.invExt :=
  (unbind_read_frame vScId st st' hObjInv h).2.2.2.2

/-- **`schedContextUnbind` preserves affinity-consistency** — with *no*
orphan-freedom hypothesis: the purge removes every one of its own context's
entries, whichever core holds them, so every survivor is another context's,
whose readings are framed. -/
theorem schedContextUnbind_preserves_replenishQueueAffinityConsistent_smp
    (vScId : ValidObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : schedContextUnbind vScId st = .ok ((), st')) :
    replenishQueueAffinityConsistent_smp st' := by
  obtain ⟨hQ, hOff, hSelf, hTgt, -⟩ := unbind_read_frame vScId st st' hObjInv h
  intro c scId₀ t hMem sc₀ hSc₀ tid₀ hTid₀
  obtain ⟨hMemPre, -⟩ := hQ c _ hMem
  by_cases hK : scId₀ = SchedContextId.ofObjId vScId.val
  · subst hK
    rw [hSc₀] at hSelf
    simp only [Option.map_some, Option.some.injEq] at hSelf
    rw [hSelf] at hTid₀; cases hTid₀
  have hNeK := hK
  obtain ⟨sc₁, hSc₁, hBt₁⟩ := boundThread_pull (hOff scId₀ hNeK) hSc₀
  rw [hTgt tid₀]
  exact hCons c scId₀ t hMemPre sc₁ hSc₁ tid₀ (hBt₁.trans hTid₀)

/-- **`schedContextUnbind` re-establishes orphan-freedom** for its SchedContext
and preserves it for every other: the purge removes the SchedContext's entries
from whichever core holds them, read from its own link — so, unlike the
home-core purge it replaced, it needs no affinity hypothesis to rule out an
entry on another core. -/
theorem schedContextUnbind_preserves_replenishQueueEntriesBound_smp
    (vScId : ValidObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hOrphan : replenishQueueEntriesBound_smp st)
    (h : schedContextUnbind vScId st = .ok ((), st')) :
    replenishQueueEntriesBound_smp st' := by
  obtain ⟨hQ, hOff, -, -, -⟩ := unbind_read_frame vScId st st' hObjInv h
  intro c scId₀ t hMem
  obtain ⟨hMemPre, hSelfC⟩ := hQ c _ hMem
  have hNeK : scId₀ ≠ SchedContextId.ofObjId vScId.val := fun hEq =>
    hSelfC hEq (SystemState.releaseCoreOf_of_queuedOn
      (((hRef c).queued _).mpr (List.mem_map.mpr ⟨_, hMemPre, hEq⟩)))
  exact bound_transfer (hOff scId₀ hNeK) (hOrphan c scId₀ t hMemPre)

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
    (hObjInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
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
        hObjInv hRef hOrphan hUnbind
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
