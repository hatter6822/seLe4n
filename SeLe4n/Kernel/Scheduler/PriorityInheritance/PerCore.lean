-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.PriorityInheritance.BoundedInversion
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.Concurrency.ContextRestoreSeam

/-!
# WS-SM SM5.F — Per-core priority inheritance protocol (theorem surface)

Per-core PIP theorems (plan §3.6 of `docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md`).
Under SMP a thread `t` on core `c` blocked on a resource held by a thread `t'` on
core `c'` boosts `t'` to `t`'s priority; if `c' ≠ c`, the boost emits a
`.reschedule` SGI to `c'`.

**The boost VALUE stays global.**  `computeMaxWaiterPriority` (the max over *every*
waiter, cross-core) is the value `updatePipBoostOnCore` applies — taking only a
per-core slice would *under-boost* and re-introduce priority inversion.  The
per-core aspect is purely (1) which core's run queue the boosted holder's bucket
migrates on, and (2) whether a remote core must be poked.  `computeMaxWaiterPriorityOnCore`
(Compute) is the per-core analytic *slice* of that global max, used only to bound
a single core's contribution (`pipBoost_perCore_consistent`, SM5.F.3) — never to
set a boost.

This module covers:

* **SM5.F.1** `computeMaxWaiterPriorityOnCore` (def in Compute): the per-core ≤
  global decomposition (`computeMaxWaiterPriorityOnCore_le_global`) and frame.
* **SM5.F.2** `updatePipBoostOnCore` bridge / frame / invariant preservation +
  `pipBoostWithWake` cross-core wake semantics (emits `.reschedule` iff remote +
  material).
* **SM5.F.3** `pipBoost_perCore_consistent` — a core's waiter slice is bounded by
  the holder's (globally-boosted) effective priority.
* **SM5.F.4** `propagatePipChainCrossCore` — donation chain across cores
  (invariant preservation + the cross-core SGI collection).
* **SM5.F.5 / SM5.F.6** `restoreToReadyOnCore` / `restoreToReadyWithWake` — per-core
  resume re-ready + PIP recomputation + cross-core resume wake.
* **SM5.F.7** `blockingServerOnCore` + `blockingGraphOnCore_consistent` — the
  per-core blocking graph is a consistent subgraph of the global one.
* **SM5.F.8** `blockingAcyclic_perCore` — the per-core blocking slice is acyclic
  (a sub-walk of the acyclic global chain).
* **SM5.F.9** `priorityInheritance_perCore_witness` — the aggregate soundness
  witness.

This module is staged (`Platform.Staged`); SM5.I's per-core scheduler/IPC dispatch
is the first runtime exerciser (wiring `pipBoostWithWake` / `restoreToReadyWithWake`
into the live donation / timeout / resume paths so a remote boost fires its SGI).
Every declaration is machine-checked, adding no trusted dependency beyond Lean's
foundational `propext` / `Quot.sound` / `Classical.choice`.
-/

namespace SeLe4n.Kernel.PriorityInheritance

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId CoreId SgiKind)
open SeLe4n.Kernel.Lifecycle.Suspend (restoreToReady restoreToReadyOnCore restoreToReadyWithWake
  resumeReadyMidState resumeThreadOnCore)

-- ============================================================================
-- §1  SM5.F.2 — updatePipBoostOnCore: bridge, frame, invariant preservation
-- ============================================================================

/-- WS-SM SM5.F.2 (bridge): the single-core `updatePipBoost` is `updatePipBoostOnCore`
at the boot core — the only difference is the literal home core, so the per-core
form generalises the single-core one and the existing single-core PIP proof base
is preserved verbatim. -/
theorem updatePipBoost_eq_updatePipBoostOnCore_bootCore (st : SystemState) (tid : ThreadId) :
    updatePipBoost st tid = updatePipBoostOnCore st bootCoreId tid := rfl

/-- WS-SM SM5.F.2: `updatePipBoostOnCore` preserves the object-store invariant —
the only object write is the holder's `pipBoost` `insert` (the per-core bucket
migration touches only the scheduler). -/
theorem updatePipBoostOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (tid : ThreadId) (hInv : st.objects.invExt) :
    (updatePipBoostOnCore st c tid).objects.invExt := by
  simp only [updatePipBoostOnCore]
  split
  · rename_i tcb _
    split
    · exact hInv
    · split
      · split
        · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hInv
        · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hInv
      · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hInv
  · exact hInv

/-- WS-SM SM5.F.2: `updatePipBoostOnCore` does not change `objects[oid]?` for any
`oid ≠ tid.toObjId`. -/
theorem updatePipBoostOnCore_objects_ne (st : SystemState) (c : CoreId) (tid : ThreadId)
    (oid : ObjId) (hNe : ¬(tid.toObjId == oid) = true) (hInv : st.objects.invExt) :
    (updatePipBoostOnCore st c tid).objects[oid]? = st.objects[oid]? := by
  simp only [updatePipBoostOnCore]
  split
  · split
    · rfl
    · split
      · split
        · show (st.objects.insert tid.toObjId _)[oid]? = _
          exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _ hNe hInv
        · exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _ hNe hInv
      · exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _ hNe hInv
  · rfl

/-- WS-SM SM5.F.2: `updatePipBoostOnCore` preserves `objectIndex` — neither the
`objects.insert` nor the scheduler bucket migration touches it. -/
theorem updatePipBoostOnCore_preserves_objectIndex (st : SystemState) (c : CoreId)
    (tid : ThreadId) :
    (updatePipBoostOnCore st c tid).objectIndex = st.objectIndex := by
  simp only [updatePipBoostOnCore]
  split
  · rename_i tcb _
    split
    · rfl
    · split
      · split <;> rfl
      · rfl
  · rfl

/-- WS-SM SM5.F.2 (PIP graph invariant): `updatePipBoostOnCore` preserves
`blockingServer` for every thread.  The blocking graph (which reads only
`ipcState`) is invariant under PIP boost updates — the record-with update sets
only `pipBoost`, and other threads' objects are untouched.  Mirrors the
single-core `updatePipBoost_preserves_blockingServer`. -/
theorem updatePipBoostOnCore_preserves_blockingServer (st : SystemState) (c : CoreId)
    (tid : ThreadId) (hObjInv : st.objects.invExt) (t : ThreadId) :
    blockingServer (updatePipBoostOnCore st c tid) t = blockingServer st t := by
  by_cases hEq : t = tid
  · rw [hEq]
    unfold updatePipBoostOnCore
    cases hTid : st.objects[tid.toObjId]? with
    | none => rfl
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only []
        split
        · rfl
        · refine blockingServer_ipcState_congr _ _ _
            { tcb with pipBoost := computeMaxWaiterPriority st tid } tcb ?_ hTid rfl
          -- `.get?`-method form (AK7-clean: no raw `[·]?` bracket in the proof source).
          have hSelf := RHTable_get?_insert_self st.objects tid.toObjId
            (.tcb { tcb with pipBoost := computeMaxWaiterPriority st tid }) hObjInv
          by_cases hRQ : tid ∈ (st.scheduler.runQueueOnCore c)
          · simp only [hRQ, ite_true]; split <;> exact hSelf
          · simp only [hRQ, ite_false]; exact hSelf
      | _ => rfl
  · exact blockingServer_congr_objects _ _ _
      (updatePipBoostOnCore_objects_ne st c tid t.toObjId
        (fun h => hEq (ThreadId.toObjId_injective tid t (eq_of_beq h)).symm) hObjInv)

/-- WS-SM SM5.F.2: `updatePipBoostOnCore` preserves blocking-graph acyclicity —
it preserves `blockingServer` (graph topology) and `objectIndex` (fuel). -/
theorem updatePipBoostOnCore_preserves_blockingAcyclic (st : SystemState) (c : CoreId)
    (tid : ThreadId) (hObjInv : st.objects.invExt) (hAcyclic : blockingAcyclic st) :
    blockingAcyclic (updatePipBoostOnCore st c tid) :=
  blockingAcyclic_frame st (updatePipBoostOnCore st c tid) hAcyclic
    (fun t => updatePipBoostOnCore_preserves_blockingServer st c tid hObjInv t)
    (updatePipBoostOnCore_preserves_objectIndex st c tid)

/-- WS-SM SM5.F.2 (cross-core frame): a PIP boost on core `c` leaves every *other*
core `c' ≠ c`'s run-queue slot untouched — the bucket migration writes only core
`c`'s slot. -/
theorem updatePipBoostOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId)
    (tid : ThreadId) (h : c ≠ c') :
    (updatePipBoostOnCore st c tid).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
  simp only [updatePipBoostOnCore]
  split
  · rename_i tcb _
    split
    · rfl
    · split
      · split
        · exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne st.scheduler c c' _ h
        · rfl
      · rfl
  · rfl

/-- WS-SM SM5.F.2: `updatePipBoostOnCore` never writes any core's `current` slot. -/
theorem updatePipBoostOnCore_currentOnCore (st : SystemState) (c c' : CoreId)
    (tid : ThreadId) :
    (updatePipBoostOnCore st c tid).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  simp only [updatePipBoostOnCore]
  split
  · rename_i tcb _
    split
    · rfl
    · split
      · split <;> rfl
      · rfl
  · rfl

/-- WS-SM SM5.F.2: the holder's post-boost `pipBoost` is the GLOBAL
`computeMaxWaiterPriority st tid` — whether the update fired (`pipBoost := newBoost`)
or was a no-op (the pre-state `pipBoost` already equalled `newBoost`).  This is the
PIP-consistency the per-core form establishes; `c` (the bucket-migration core) does
not change it. -/
theorem updatePipBoostOnCore_getTcb?_pipBoost (st : SystemState) (c : CoreId) (tid : ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) (hInv : st.objects.invExt) :
    ∃ tcb', (updatePipBoostOnCore st c tid).getTcb? tid = some tcb' ∧
      tcb'.pipBoost = computeMaxWaiterPriority st tid := by
  -- Typed-accessor hypothesis; the raw form is the inferred type of `hRaw` (no raw
  -- `[·]?` bracket in the proof source — AK7-clean).
  have hRaw := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  unfold updatePipBoostOnCore
  simp only [hRaw]
  split
  · -- no-op: pipBoost already equals newBoost
    rename_i hEq
    exact ⟨tcb, hTcb, eq_of_beq hEq⟩
  · -- update: pipBoost := newBoost
    refine ⟨{ tcb with pipBoost := computeMaxWaiterPriority st tid }, ?_, rfl⟩
    rw [SystemState.getTcb?_eq_some_iff]
    have hSelf := RHTable_get?_insert_self st.objects tid.toObjId
      (.tcb { tcb with pipBoost := computeMaxWaiterPriority st tid }) hInv
    by_cases hRQ : tid ∈ (st.scheduler.runQueueOnCore c)
    · simp only [hRQ, ite_true]; split <;> exact hSelf
    · simp only [hRQ, ite_false]; exact hSelf

-- ============================================================================
-- §2  SM5.F.1 / SM5.F.3 — pipBoost_perCore_consistent
-- ============================================================================

/-- WS-SM SM5.F.3 (helper): a thread's `pipBoost` value is bounded by its effective
priority — `effectiveSchedParams` applies the boost via `Nat.max` against the base
(SC- or TCB-derived) priority, so the boost never exceeds the effective priority it
produces. -/
theorem optPriorityVal_pipBoost_le_effectiveSchedParams (st : SystemState) (tcb : TCB) :
    optPriorityVal tcb.pipBoost ≤ (effectiveSchedParams st tcb).1.val := by
  cases hPB : tcb.pipBoost with
  | none => simp [optPriorityVal]
  | some b =>
    rw [optPriorityVal_some]
    simp only [effectiveSchedParams, hPB]
    split <;> (try split) <;> apply Nat.le_max_right

/-- WS-SM SM5.F.3 (plan §3.6, Theorem 3.6.1 `pipBoost_perCore_consistent`): in a
state whose holder `tid` carries a PIP-consistent boost (`pipBoost =
computeMaxWaiterPriority` — the global max over every waiter, which
`updatePipBoostOnCore` establishes), a single core `c`'s waiter slice never exceeds
the holder's effective priority.

This is the soundness statement: per-core ≤ global boost (`computeMaxWaiterPriorityOnCore_le_global`)
≤ holder's effective priority (the boost is applied via `max`).  It justifies that
the cross-core boost mechanism is consistent — no core over-claims. -/
theorem pipBoost_perCore_consistent (st : SystemState) (c : CoreId) (tid : ThreadId)
    (tcb : TCB) (_hTcb : st.getTcb? tid = some tcb)
    (hConsistent : tcb.pipBoost = computeMaxWaiterPriority st tid) :
    optPriorityVal (computeMaxWaiterPriorityOnCore st c tid)
      ≤ (effectiveSchedParams st tcb).1.val :=
  calc optPriorityVal (computeMaxWaiterPriorityOnCore st c tid)
      ≤ optPriorityVal (computeMaxWaiterPriority st tid) :=
        computeMaxWaiterPriorityOnCore_le_global st c tid
    _ = optPriorityVal tcb.pipBoost := by rw [hConsistent]
    _ ≤ (effectiveSchedParams st tcb).1.val :=
        optPriorityVal_pipBoost_le_effectiveSchedParams st tcb

-- ============================================================================
-- §3  SM5.F.2 — pipBoostWithWake (cross-core PIP wake)
-- ============================================================================

/-- WS-SM SM5.F.2: `pipBoostWithWake`'s state component is the per-core boost on the
holder's home core. -/
@[simp] theorem pipBoostWithWake_state (st : SystemState) (tid : ThreadId) (ec : CoreId) :
    (pipBoostWithWake st tid ec).1 = updatePipBoostOnCore st (determineTargetCore st tid) tid := rfl

/-- WS-SM SM5.F.2: a LOCAL PIP boost (home = executing core) emits no SGI — the
executing core picks up the re-bucketed holder on its next scheduling decision. -/
theorem pipBoostWithWake_no_sgi_if_local (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (hLocal : determineTargetCore st tid = ec) :
    (pipBoostWithWake st tid ec).2 = none := by
  simp [pipBoostWithWake, hLocal]

/-- WS-SM SM5.F.2 (Theorem 3.6.1 emission): a REMOTE, RUNNABLE-ON-HOME, MATERIAL PIP
boost emits a `.reschedule` SGI to the holder's home core.  "Material" = the boost
actually raised the holder's *effective* priority (`resolveEffectivePrioDeadline`,
the run-queue bucket key) — NOT merely the raw `pipBoost` — so the boost genuinely
migrates the holder's bucket; "runnable on home" = the holder is in its home core's
run queue, so the boost can actually change which thread that core runs next —
together these are the exact condition under which the remote core's scheduler must
re-evaluate (the boosted holder may now outrank its current thread), and exactly the
condition under which `updatePipBoostOnCore` performs its run-queue bucket migration. -/
theorem pipBoostWithWake_emits_sgi_if_remote (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (t t' : TCB)
    (hRemote : determineTargetCore st tid ≠ ec)
    (hRunnable : tid ∈ st.scheduler.runQueueOnCore (determineTargetCore st tid))
    (hPre : st.getTcb? tid = some t)
    (hPost : (updatePipBoostOnCore st (determineTargetCore st tid) tid).getTcb? tid = some t')
    (hMaterial : (resolveEffectivePrioDeadline st t).1
      ≠ (resolveEffectivePrioDeadline (updatePipBoostOnCore st (determineTargetCore st tid) tid) t').1) :
    (pipBoostWithWake st tid ec).2 = some (determineTargetCore st tid, SgiKind.reschedule) := by
  have hRem : (determineTargetCore st tid == ec) = false := by
    cases h : (determineTargetCore st tid == ec) with
    | false => rfl
    | true => exact absurd (eq_of_beq h) hRemote
  have hMat : ((resolveEffectivePrioDeadline st t).1
      == (resolveEffectivePrioDeadline (updatePipBoostOnCore st (determineTargetCore st tid) tid) t').1)
      = false := by
    cases h : ((resolveEffectivePrioDeadline st t).1
        == (resolveEffectivePrioDeadline (updatePipBoostOnCore st (determineTargetCore st tid) tid) t').1) with
    | false => rfl
    | true => exact absurd (eq_of_beq h) hMaterial
  simp [pipBoostWithWake, hRem, hPre, hPost, hMat, hRunnable]

/-- WS-SM SM5.F.4 (C9 precision): a boost of a holder that is NOT runnable on its
home core emits no SGI — raising the `pipBoost` of a thread not competing for that
core's CPU has no immediate scheduling effect (the boost is consumed when the thread
is next re-enqueued there).  Closes the spurious-cross-core-IPI gap for blocked-holder
boosts (the common PIP case: the boosted holder is itself blocked deeper in the
chain). -/
theorem pipBoostWithWake_no_sgi_if_not_runnable (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (hNotRun : tid ∉ st.scheduler.runQueueOnCore (determineTargetCore st tid)) :
    (pipBoostWithWake st tid ec).2 = none := by
  simp [pipBoostWithWake, hNotRun]

/-- WS-SM SM5.F.2: a PIP boost that does not raise the holder's *effective* priority
(the run-queue bucket key is unchanged) emits no SGI — there is no bucket migration
and hence no scheduling consequence, so poking a remote core would be a spurious
cross-core IPI (the SM5.C.11 latency concern).  Covers both the strict no-op (boost
unchanged) and the immaterial case (boost rose but stayed dominated by the base
priority, so the effective bucket is unchanged). -/
theorem pipBoostWithWake_no_sgi_if_noop (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (t t' : TCB)
    (hPre : st.getTcb? tid = some t)
    (hPost : (updatePipBoostOnCore st (determineTargetCore st tid) tid).getTcb? tid = some t')
    (hNoop : (resolveEffectivePrioDeadline st t).1
      = (resolveEffectivePrioDeadline (updatePipBoostOnCore st (determineTargetCore st tid) tid) t').1) :
    (pipBoostWithWake st tid ec).2 = none := by
  have hEq : ((resolveEffectivePrioDeadline st t).1
      == (resolveEffectivePrioDeadline (updatePipBoostOnCore st (determineTargetCore st tid) tid) t').1)
      = true := by rw [hNoop]; exact beq_self_eq_true _
  simp [pipBoostWithWake, hPre, hPost, hEq]

/-- WS-SM SM5.F.2: any SGI `pipBoostWithWake` emits is a `.reschedule` to the
holder's home core — never another SGI kind, never another core. -/
theorem pipBoostWithWake_sgi_is_reschedule (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (tgt : CoreId) (k : SgiKind)
    (hSgi : (pipBoostWithWake st tid ec).2 = some (tgt, k)) :
    tgt = determineTargetCore st tid ∧ k = SgiKind.reschedule := by
  simp only [pipBoostWithWake] at hSgi
  split at hSgi
  · simp at hSgi
  · split at hSgi
    · split at hSgi
      · split at hSgi
        · simp at hSgi
        · simp only [Option.some.injEq, Prod.mk.injEq] at hSgi
          exact ⟨hSgi.1.symm, hSgi.2.symm⟩
      · simp at hSgi
    · simp at hSgi

/-- WS-SM SM5.F.2 (SM5.C.11 latency parity): the cross-core PIP wake emits AT MOST
ONE SGI — its SGI component is an `Option`, never a list, so a single boost cannot
trigger an SGI storm. -/
theorem pipBoostWithWake_emits_at_most_one_sgi (st : SystemState) (tid : ThreadId)
    (ec : CoreId) :
    (pipBoostWithWake st tid ec).2 = none ∨
    ∃ p, (pipBoostWithWake st tid ec).2 = some p := by
  cases (pipBoostWithWake st tid ec).2 with
  | none => exact Or.inl rfl
  | some p => exact Or.inr ⟨p, rfl⟩

/-- WS-SM SM5.F.2: `pipBoostWithWake` preserves the object-store invariant. -/
theorem pipBoostWithWake_preserves_objects_invExt (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (hInv : st.objects.invExt) :
    (pipBoostWithWake st tid ec).1.objects.invExt := by
  rw [pipBoostWithWake_state]
  exact updatePipBoostOnCore_preserves_objects_invExt st _ tid hInv

/-- WS-SM SM5.F.2: `pipBoostWithWake` preserves blocking-graph acyclicity. -/
theorem pipBoostWithWake_preserves_blockingAcyclic (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (hInv : st.objects.invExt) (hAcyclic : blockingAcyclic st) :
    blockingAcyclic (pipBoostWithWake st tid ec).1 := by
  rw [pipBoostWithWake_state]
  exact updatePipBoostOnCore_preserves_blockingAcyclic st _ tid hInv hAcyclic

/-- WS-SM SM5.F.2 (single-core bridge): on the boot core, a PIP boost of an unbound
thread (home = `bootCoreId`) reduces to the single-core `updatePipBoost` and emits
no SGI — the trace is byte-identical for the single-core path. -/
theorem pipBoostWithWake_bootCore_unbound (st : SystemState) (tid : ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hUnbound : tcb.cpuAffinity = none) :
    pipBoostWithWake st tid bootCoreId = (updatePipBoost st tid, none) := by
  have hTarget : determineTargetCore st tid = bootCoreId := by
    simp only [determineTargetCore, hTcb, hUnbound]
  simp only [pipBoostWithWake, hTarget, beq_self_eq_true, if_true,
    updatePipBoost_eq_updatePipBoostOnCore_bootCore]

-- ============================================================================
-- §4  SM5.F.4 — propagatePipChainCrossCore (donation chain across cores)
-- ============================================================================

/-- WS-SM SM5.F.4: the *state* component of the cross-core chain walk, projected
out so the invariant-preservation inductions never wrestle with the SGI-list
let-pattern.  Its one-step recursion (`_step` below) makes the chain walk's state
effect a clean fold of per-thread `pipBoostWithWake` boosts. -/
def propagatePipChainCrossCoreState (st : SystemState) (startTid : ThreadId)
    (executingCore : CoreId) (fuel : Nat := st.objectIndex.length) : SystemState :=
  (propagatePipChainCrossCore st startTid executingCore fuel).1

@[simp] theorem propagatePipChainCrossCoreState_zero (st : SystemState) (tid : ThreadId)
    (ec : CoreId) :
    propagatePipChainCrossCoreState st tid ec 0 = st := rfl

theorem propagatePipChainCrossCoreState_step (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (n : Nat) :
    propagatePipChainCrossCoreState st tid ec (n + 1) =
      match blockingServer st tid with
      | some nextServer =>
        propagatePipChainCrossCoreState (pipBoostWithWake st tid ec).1 nextServer ec n
      | none => (pipBoostWithWake st tid ec).1 := by
  unfold propagatePipChainCrossCoreState
  rw [propagatePipChainCrossCore_step]
  cases blockingServer st tid <;> rfl

/-- WS-SM SM5.F.4: the cross-core donation chain walk preserves the object-store
invariant — each link is a `pipBoostWithWake` boost (an `invExt`-preserving TCB
`insert`), folded along the chain. -/
theorem propagatePipChainCrossCore_preserves_objects_invExt (st : SystemState)
    (tid : ThreadId) (ec : CoreId) (fuel : Nat) (hInv : st.objects.invExt) :
    (propagatePipChainCrossCore st tid ec fuel).1.objects.invExt := by
  show (propagatePipChainCrossCoreState st tid ec fuel).objects.invExt
  induction fuel generalizing st tid with
  | zero => simpa using hInv
  | succ n ih =>
    rw [propagatePipChainCrossCoreState_step]
    have hst' := pipBoostWithWake_preserves_objects_invExt st tid ec hInv
    cases blockingServer st tid with
    | none => exact hst'
    | some nextServer => exact ih _ nextServer hst'

/-- WS-SM SM5.F.4: the cross-core donation chain walk preserves blocking-graph
acyclicity — each `pipBoostWithWake` boost preserves the blocking graph + fuel. -/
theorem propagatePipChainCrossCore_preserves_blockingAcyclic (st : SystemState)
    (tid : ThreadId) (ec : CoreId) (fuel : Nat) (hInv : st.objects.invExt)
    (hAcyclic : blockingAcyclic st) :
    blockingAcyclic (propagatePipChainCrossCore st tid ec fuel).1 := by
  show blockingAcyclic (propagatePipChainCrossCoreState st tid ec fuel)
  induction fuel generalizing st tid with
  | zero => simpa using hAcyclic
  | succ n ih =>
    rw [propagatePipChainCrossCoreState_step]
    have hst' := pipBoostWithWake_preserves_objects_invExt st tid ec hInv
    have hac' := pipBoostWithWake_preserves_blockingAcyclic st tid ec hInv hAcyclic
    cases blockingServer st tid with
    | none => exact hac'
    | some nextServer => exact ih _ nextServer hst' hac'

/-- WS-SM SM5.F.4 (single-core bridge): with zero fuel the chain walk is identity
and collects no SGIs. -/
theorem propagatePipChainCrossCore_zero_sgis (st : SystemState) (tid : ThreadId) (ec : CoreId) :
    (propagatePipChainCrossCore st tid ec 0).2 = [] := rfl

/-- WS-SM SM5.F.4: the chain walk's SGI list is `[]` exactly when the boosted head
emits no SGI and the rest of the chain emits none (recursive characterisation of
the "no remote work" case).  At the chain head a `none` server (chain ends) leaves
only the head's own SGI. -/
theorem propagatePipChainCrossCore_no_sgis_head_terminal (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (n : Nat) (hEnd : blockingServer st tid = none) :
    (propagatePipChainCrossCore st tid ec (n + 1)).2
      = (match (pipBoostWithWake st tid ec).2 with | some s => [s] | none => []) := by
  rw [propagatePipChainCrossCore_step]
  cases hsgi : (pipBoostWithWake st tid ec).2 <;> simp [hEnd, hsgi]

/-- WS-SM SM5.F.4 (donation chain across cores): when the chain head's boost is
*remote and material*, the walk's collected SGI list begins with the head's
`.reschedule` SGI to its home core — so a chain link on a remote core is genuinely
poked.  The substantive cross-core content. -/
theorem propagatePipChainCrossCore_head_sgi_remote (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (n : Nat) (t t' : TCB)
    (hRemote : determineTargetCore st tid ≠ ec)
    (hRunnable : tid ∈ st.scheduler.runQueueOnCore (determineTargetCore st tid))
    (hPre : st.getTcb? tid = some t)
    (hPost : (updatePipBoostOnCore st (determineTargetCore st tid) tid).getTcb? tid = some t')
    (hMaterial : (resolveEffectivePrioDeadline st t).1
      ≠ (resolveEffectivePrioDeadline (updatePipBoostOnCore st (determineTargetCore st tid) tid) t').1) :
    ∃ rest, (propagatePipChainCrossCore st tid ec (n + 1)).2
      = (determineTargetCore st tid, SgiKind.reschedule) :: rest := by
  rw [propagatePipChainCrossCore_step]
  have hHead : (pipBoostWithWake st tid ec).2
      = some (determineTargetCore st tid, SgiKind.reschedule) :=
    pipBoostWithWake_emits_sgi_if_remote st tid ec t t' hRemote hRunnable hPre hPost hMaterial
  cases hBS : blockingServer st tid with
  | none =>
    refine ⟨[], ?_⟩
    simp [hHead]
  | some nextServer =>
    refine ⟨(propagatePipChainCrossCore (pipBoostWithWake st tid ec).1 nextServer ec n).2, ?_⟩
    simp [hHead]

-- ============================================================================
-- §5  SM5.F.5 / SM5.F.6 — restoreToReadyOnCore / restoreToReadyWithWake
-- ============================================================================

/-- WS-SM SM5.F.5 (helper): `restoreToReady` preserves the object-store invariant
(it `insert`s a single TCB with cleared IPC fields). -/
theorem restoreToReady_objects_invExt (st : SystemState) (tid : ThreadId)
    (hInv : st.objects.invExt) :
    (restoreToReady st tid).objects.invExt := by
  unfold restoreToReady
  split
  · exact RHTable_insert_preserves_invExt _ _ _ hInv
  · exact hInv

/-- WS-SM SM5.F.5: `restoreToReadyOnCore` preserves the object-store invariant —
each of the three steps (restore IPC clear, pipBoost recompute insert, per-core
enqueue) is an `invExt`-preserving `RHTable.insert` (or identity). -/
theorem restoreToReadyOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (tid : ThreadId) (hInv : st.objects.invExt) :
    (restoreToReadyOnCore st c tid).objects.invExt := by
  simp only [restoreToReadyOnCore]
  apply enqueueRunnableOnCore_preserves_objects_invExt
  have h1 : (restoreToReady st tid).objects.invExt := restoreToReady_objects_invExt st tid hInv
  split
  · exact RHTable_insert_preserves_invExt _ _ _ h1
  · exact h1

/-- WS-SM SM5.F.5 (frame): `restoreToReadyOnCore` on core `c` never writes any
core's `current` slot — the restore + pipBoost recompute touch only objects, the
per-core enqueue touches only core `c`'s run queue. -/
theorem restoreToReadyOnCore_currentOnCore (st : SystemState) (c c' : CoreId) (tid : ThreadId) :
    (restoreToReadyOnCore st c tid).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  simp only [restoreToReadyOnCore, enqueueRunnableOnCore_currentOnCore]
  split <;> simp only [Lifecycle.Suspend.restoreToReady_scheduler_eq]

/-- WS-SM SM5.F.5 (cross-core frame): `restoreToReadyOnCore` on core `c` leaves every
*other* core `c' ≠ c`'s run-queue slot untouched. -/
theorem restoreToReadyOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId)
    (tid : ThreadId) (h : c ≠ c') :
    (restoreToReadyOnCore st c tid).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
  simp only [restoreToReadyOnCore]
  rw [enqueueRunnableOnCore_runQueueOnCore_ne _ c c' tid h]
  split <;> simp only [Lifecycle.Suspend.restoreToReady_scheduler_eq]

/-- WS-SM SM5.F.6 (intermediate): the resume re-ready state *before* the per-core
enqueue — restore IPC clear, then write the GLOBAL recomputed `pipBoost` onto the
resumed thread. -/
private def restoreToReadyMidState (st : SystemState) (tid : ThreadId) : SystemState :=
  match (restoreToReady st tid).getTcb? tid with
  | some t => { (restoreToReady st tid) with objects := (restoreToReady st tid).objects.insert tid.toObjId (.tcb { t with pipBoost := computeMaxWaiterPriority (restoreToReady st tid) tid }) }
  | none => restoreToReady st tid

private theorem restoreToReadyOnCore_eq_enqueue_mid (st : SystemState) (c : CoreId) (tid : ThreadId) :
    restoreToReadyOnCore st c tid = enqueueRunnableOnCore (restoreToReadyMidState st tid) c tid := rfl

/-- WS-SM SM5.F.6 (PIP recomputation, plan §3.6 resume H3b): `restoreToReadyOnCore`
recomputes the resumed thread's `pipBoost` from the GLOBAL blocking graph
(`computeMaxWaiterPriority` of the restored state), and the per-core enqueue
preserves that recomputed value.  This is the SMP analogue of `resumeThread`'s
H3b PIP-readiness re-establishment — the boost is recomputed (cross-core correct)
*before* the thread re-enters its home core's run queue. -/
theorem restoreToReadyOnCore_pipBoost_recomputed (st : SystemState) (c : CoreId) (tid : ThreadId)
    (t1 : TCB) (hTcb1 : (restoreToReady st tid).getTcb? tid = some t1)
    (hInv : (restoreToReady st tid).objects.invExt) :
    ∃ t', (restoreToReadyOnCore st c tid).getTcb? tid = some t' ∧
      t'.pipBoost = computeMaxWaiterPriority (restoreToReady st tid) tid := by
  have hInv2 : (restoreToReadyMidState st tid).objects.invExt := by
    simp only [restoreToReadyMidState, hTcb1]
    exact RHTable_insert_preserves_invExt _ _ _ hInv
  have hSt2Tcb : (restoreToReadyMidState st tid).getTcb? tid
      = some { t1 with pipBoost := computeMaxWaiterPriority (restoreToReady st tid) tid } := by
    simp only [restoreToReadyMidState, hTcb1, SystemState.getTcb?_eq_some_iff, RHTable_getElem?_eq_get?]
    exact RHTable_get?_insert_self _ _ _ hInv
  rw [restoreToReadyOnCore_eq_enqueue_mid]
  -- The enqueue preserves `tid`'s pipBoost: no-op keeps the mid-state; the fresh
  -- branch sets only `ipcState` (`enqueueRunnableOnCore_makes_ready`).
  by_cases hRun : runnableOnSomeCore (restoreToReadyMidState st tid) tid = true
  · have hEq : enqueueRunnableOnCore (restoreToReadyMidState st tid) c tid
        = restoreToReadyMidState st tid := by
      unfold enqueueRunnableOnCore; rw [hSt2Tcb]; simp [hRun]
    rw [hEq]
    exact ⟨_, hSt2Tcb, rfl⟩
  · have hFresh : runnableOnSomeCore (restoreToReadyMidState st tid) tid = false := by
      simpa using hRun
    refine ⟨{ t1 with pipBoost := computeMaxWaiterPriority (restoreToReady st tid) tid, ipcState := .ready }, ?_, rfl⟩
    exact enqueueRunnableOnCore_makes_ready (restoreToReadyMidState st tid) c tid
      { t1 with pipBoost := computeMaxWaiterPriority (restoreToReady st tid) tid } hSt2Tcb hInv2 hFresh

-- §5b  SM5.F.6 — restoreToReadyWithWake (cross-core resume wake)

/-- WS-SM SM5.F.6: `restoreToReadyWithWake`'s state component sets the resumed thread
`.Ready` (via `resumeReadyMidState`, PR #811 P2-3) and enqueues it on its home core. -/
@[simp] theorem restoreToReadyWithWake_state (st : SystemState) (tid : ThreadId) (ec : CoreId) :
    (restoreToReadyWithWake st tid ec).1
      = enqueueRunnableOnCore (resumeReadyMidState st tid) (determineTargetCore st tid) tid := rfl

/-- WS-SM SM5.F.6: a LOCAL resume (home = executing core) emits no SGI. -/
theorem restoreToReadyWithWake_no_sgi_if_local (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (hLocal : determineTargetCore st tid = ec) :
    (restoreToReadyWithWake st tid ec).2 = none := by
  simp [restoreToReadyWithWake, hLocal]

/-- WS-SM SM5.F.6: a REMOTE resume of a real thread emits a `.reschedule` SGI to its
home core — the resumed thread newly enters that core's run queue, so the core
must re-evaluate.  Unlike `pipBoostWithWake` there is no materiality guard: resume
genuinely makes the thread runnable. -/
theorem restoreToReadyWithWake_emits_sgi_if_remote (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (tcb : TCB)
    (hRemote : determineTargetCore st tid ≠ ec) (hTcb : st.getTcb? tid = some tcb) :
    (restoreToReadyWithWake st tid ec).2 = some (determineTargetCore st tid, SgiKind.reschedule) := by
  have hRem : (determineTargetCore st tid == ec) = false := by
    cases h : (determineTargetCore st tid == ec) with
    | false => rfl
    | true => exact absurd (eq_of_beq h) hRemote
  simp [restoreToReadyWithWake, hRem, hTcb]

/-- WS-SM SM5.F.6: any SGI `restoreToReadyWithWake` emits is a `.reschedule` to the
resumed thread's home core. -/
theorem restoreToReadyWithWake_sgi_is_reschedule (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (tgt : CoreId) (k : SgiKind)
    (hSgi : (restoreToReadyWithWake st tid ec).2 = some (tgt, k)) :
    tgt = determineTargetCore st tid ∧ k = SgiKind.reschedule := by
  simp only [restoreToReadyWithWake] at hSgi
  split at hSgi
  · simp at hSgi
  · split at hSgi
    · simp at hSgi
    · simp only [Option.some.injEq, Prod.mk.injEq] at hSgi
      exact ⟨hSgi.1.symm, hSgi.2.symm⟩

/-- WS-SM SM5.F.6: `restoreToReadyWithWake` preserves the object-store invariant —
both `resumeReadyMidState` (a single TCB `insert`) and the per-core enqueue preserve it. -/
theorem restoreToReadyWithWake_preserves_objects_invExt (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (hInv : st.objects.invExt) :
    (restoreToReadyWithWake st tid ec).1.objects.invExt := by
  rw [restoreToReadyWithWake_state]
  apply enqueueRunnableOnCore_preserves_objects_invExt
  -- (resumeReadyMidState st tid).objects.invExt
  have hst1Inv : (restoreToReady st tid).objects.invExt := restoreToReady_objects_invExt st tid hInv
  simp only [resumeReadyMidState]
  split
  · exact RHTable_insert_preserves_invExt _ _ _ hst1Inv
  · exact hst1Inv

-- ============================================================================
-- §6  SM5.F.7 / SM5.F.8 — per-core blocking graph (slice + acyclicity)
-- ============================================================================

/-- WS-SM SM5.F.7 (plan §3.6): the per-core slice of the blocking graph — the edge
out of `tid` is present on core `c` iff `tid`'s home core is `c`.  The global
blocking graph is the union of these per-core slices over all cores. -/
def blockingServerOnCore (st : SystemState) (c : CoreId) (tid : ThreadId) : Option ThreadId :=
  if SeLe4n.Kernel.determineTargetCore st tid == c then blockingServer st tid else none

/-- WS-SM SM5.F.7: on its home core, the per-core blocking edge IS the global one. -/
theorem blockingServerOnCore_eq_global_of_onCore (st : SystemState) (c : CoreId) (tid : ThreadId)
    (h : SeLe4n.Kernel.determineTargetCore st tid = c) :
    blockingServerOnCore st c tid = blockingServer st tid := by
  simp [blockingServerOnCore, h]

/-- WS-SM SM5.F.7: off its home core, a thread contributes no per-core edge. -/
theorem blockingServerOnCore_none_of_offCore (st : SystemState) (c : CoreId) (tid : ThreadId)
    (h : SeLe4n.Kernel.determineTargetCore st tid ≠ c) :
    blockingServerOnCore st c tid = none := by
  unfold blockingServerOnCore
  cases hb : (SeLe4n.Kernel.determineTargetCore st tid == c) with
  | false => rfl
  | true => exact absurd (eq_of_beq hb) h

/-- WS-SM SM5.F.7 (consistency, →): every per-core edge is a genuine global edge. -/
theorem blockingServerOnCore_implies_global (st : SystemState) (c : CoreId) (tid s : ThreadId)
    (h : blockingServerOnCore st c tid = some s) :
    blockingServer st tid = some s := by
  unfold blockingServerOnCore at h
  split at h
  · exact h
  · simp at h

/-- WS-SM SM5.F.7 (subgraph): each thread's per-core edge is either absent or equal
to its global edge — the per-core blocking graph is a *subgraph* of the global one.
The hypothesis `blockingAcyclic_of_subgraph` consumes. -/
theorem blockingServerOnCore_subgraph (st : SystemState) (c : CoreId) (tid : ThreadId) :
    blockingServerOnCore st c tid = none ∨ blockingServerOnCore st c tid = blockingServer st tid := by
  unfold blockingServerOnCore
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- WS-SM SM5.F.7 (plan §3.6, `blockingGraphOnCore_consistent`): the global blocking
graph is exactly the union of the per-core slices — an edge `tid → s` is global iff
some core's slice carries it.  Consistency between the per-core and global views. -/
theorem blockingGraphOnCore_consistent (st : SystemState) (tid s : ThreadId) :
    (∃ c, blockingServerOnCore st c tid = some s) ↔ blockingServer st tid = some s := by
  constructor
  · rintro ⟨c, hc⟩; exact blockingServerOnCore_implies_global st c tid s hc
  · intro h
    exact ⟨SeLe4n.Kernel.determineTargetCore st tid,
      (blockingServerOnCore_eq_global_of_onCore st _ tid rfl).trans h⟩

/-- WS-SM SM5.F.8: the per-core blocking *chain* — walk the per-core slice upward.
A sub-walk of the global `blockingChain` (it dead-ends as soon as a node is off
core `c`). -/
def blockingChainOnCore (st : SystemState) (c : CoreId) (tid : ThreadId)
    (fuel : Nat := st.objectIndex.length) : List ThreadId :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    match blockingServerOnCore st c tid with
    | some server => server :: blockingChainOnCore st c server fuel'
    | none => []

/-- WS-SM SM5.F.8: the per-core blocking chain is a subset of the global blocking
chain — every node reached by walking the per-core slice is reached by walking the
global graph (the per-core slice has no edges the global graph lacks). -/
theorem blockingChainOnCore_subset (st : SystemState) (c : CoreId) (tid : ThreadId) (fuel : Nat) :
    ∀ x, x ∈ blockingChainOnCore st c tid fuel → x ∈ blockingChain st tid fuel := by
  induction fuel generalizing tid with
  | zero => intro x h; simp [blockingChainOnCore] at h
  | succ n ih =>
    intro x h
    rw [blockingChain_step]
    simp only [blockingChainOnCore] at h
    rcases blockingServerOnCore_subgraph st c tid with hNone | hEq
    · rw [hNone] at h; simp at h
    · rw [hEq] at h
      cases hSrv : blockingServer st tid with
      | none => simp [hSrv] at h
      | some server =>
        simp only [hSrv, List.mem_cons] at h ⊢
        rcases h with hHead | hTail
        · exact Or.inl hHead
        · exact Or.inr (ih server x hTail)

/-- WS-SM SM5.F.8: the per-core blocking-graph acyclicity predicate. -/
def blockingAcyclicOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid, tid ∉ blockingChainOnCore st c tid

/-- WS-SM SM5.F.8 (plan §3.6, `blockingAcyclic_perCore`): the per-core blocking
slice is acyclic.  Substantive: the per-core chain is a sub-walk of the global
chain (`blockingChainOnCore_subset`), and the global chain is acyclic
(`blockingAcyclic`), so no thread appears in its own per-core chain.  No new PIP
cycle can arise from the per-core decomposition. -/
theorem blockingAcyclic_perCore (st : SystemState) (c : CoreId) (hAcyclic : blockingAcyclic st) :
    blockingAcyclicOnCore st c := fun tid hMem =>
  hAcyclic tid (blockingChainOnCore_subset st c tid st.objectIndex.length tid hMem)

-- ============================================================================
-- §7  SM5.F.9 — priorityInheritance_perCore_witness (aggregate soundness)
-- ============================================================================

/-- WS-SM SM5.F.9 (plan §3.6, `priorityInheritance_perCore_witness`): the aggregate
soundness witness for per-core PIP.  Under the global blocking-acyclicity invariant
(and the object-store invariant), the cross-core PIP wake mechanism is sound:

1. **`pipBoostWithWake` preserves the (global) acyclic invariant** — a cross-core
   boost cannot create a blocking cycle.
2. **every core's blocking slice is acyclic** (`blockingAcyclic_perCore`) — the
   per-core decomposition introduces no cycle.
3. **every core's slice is a consistent subgraph** of the global graph — the
   per-core view never invents an edge.

Together these are the three architectural keystones (plan §4.4 "Deadlock cannot
occur"): the per-core PIP is a sound, acyclic, consistent decomposition of the
global priority-inheritance discipline. -/
theorem priorityInheritance_perCore_witness (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (hInv : st.objects.invExt) (hAcyclic : blockingAcyclic st) :
    blockingAcyclic (pipBoostWithWake st tid ec).1 ∧
    (∀ c, blockingAcyclicOnCore st c) ∧
    (∀ c t, blockingServerOnCore st c t = none ∨ blockingServerOnCore st c t = blockingServer st t) :=
  ⟨pipBoostWithWake_preserves_blockingAcyclic st tid ec hInv hAcyclic,
   fun c => blockingAcyclic_perCore st c hAcyclic,
   fun c t => blockingServerOnCore_subgraph st c t⟩

-- ============================================================================
-- §8  SM5.F.3 — post-boost per-core dominance (consistency, premise-free)
-- ============================================================================
--
-- `pipBoost_perCore_consistent` (§2) bounds a core's slice by the holder's effective
-- priority *given* the holder already carries a PIP-consistent boost.  The theorems
-- below close the loop: a cross-core boost *establishes* that domination
-- unconditionally — after `updatePipBoostOnCore` the holder's effective priority
-- bounds every core's pre-state waiter slice (the boost "covers" the waiters that
-- motivated it).  This is the soundness completeness for SM5.F.3.

/-- WS-SM SM5.F.2: a PIP boost leaves the holder's `cpuAffinity` untouched — the
record update writes only `pipBoost`.  Companion to `updatePipBoostOnCore_getTcb?_pipBoost`;
the home-core stability lemma `updatePipBoostOnCore_preserves_determineTargetCore`
consumes it. -/
theorem updatePipBoostOnCore_getTcb?_cpuAffinity (st : SystemState) (c : CoreId) (tid : ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) (hInv : st.objects.invExt) :
    ∃ t', (updatePipBoostOnCore st c tid).getTcb? tid = some t' ∧ t'.cpuAffinity = tcb.cpuAffinity := by
  have hRaw := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  unfold updatePipBoostOnCore
  simp only [hRaw]
  split
  · exact ⟨tcb, hTcb, rfl⟩
  · refine ⟨{ tcb with pipBoost := computeMaxWaiterPriority st tid }, ?_, rfl⟩
    rw [SystemState.getTcb?_eq_some_iff]
    have hSelf := RHTable_get?_insert_self st.objects tid.toObjId
      (.tcb { tcb with pipBoost := computeMaxWaiterPriority st tid }) hInv
    by_cases hRQ : tid ∈ (st.scheduler.runQueueOnCore c)
    · simp only [hRQ, ite_true]; split <;> exact hSelf
    · simp only [hRQ, ite_false]; exact hSelf

/-- WS-SM SM5.F.2: a PIP boost of a thread with no TCB is the identity — the def's
fallthrough arm returns `st`. -/
theorem updatePipBoostOnCore_eq_self_of_getTcb?_none (st : SystemState) (c : CoreId)
    (tid : ThreadId) (hNone : st.getTcb? tid = none) :
    updatePipBoostOnCore st c tid = st := by
  unfold updatePipBoostOnCore
  unfold SystemState.getTcb? at hNone
  split
  · rename_i tcb hMatch; rw [hMatch] at hNone; simp at hNone
  · rfl

/-- WS-SM SM5.F.4 (cpuAffinity-stability / home-core stability): a PIP boost
preserves *every* thread's home core (`determineTargetCore`).  `determineTargetCore`
reads only `cpuAffinity`, which the boost never changes — so the cross-core chain
walk's home-core decisions are stable as the boosts accumulate.  This is the
invariant the single-core bridge and the deadlock-freedom argument rest on. -/
theorem updatePipBoostOnCore_preserves_determineTargetCore (st : SystemState) (c : CoreId)
    (tid t : ThreadId) (hInv : st.objects.invExt) :
    determineTargetCore (updatePipBoostOnCore st c tid) t = determineTargetCore st t := by
  by_cases hEq : t = tid
  · subst hEq
    cases hTcb : st.getTcb? t with
    | none => rw [updatePipBoostOnCore_eq_self_of_getTcb?_none st c t hTcb]
    | some tcb =>
      obtain ⟨t', hPost, hAff⟩ := updatePipBoostOnCore_getTcb?_cpuAffinity st c t tcb hTcb hInv
      simp only [determineTargetCore, hPost, hTcb, hAff]
  · unfold determineTargetCore
    -- AK7-clean: frame `getTcb? t` via the `.get?`-method form (no raw `[·]?` bracket
    -- in the proof source); the bracket-form `objects_ne` is applied under the
    -- `RHTable_getElem?_eq_get?` bridge.
    have hGet : (updatePipBoostOnCore st c tid).getTcb? t = st.getTcb? t := by
      have hObjNe : (updatePipBoostOnCore st c tid).objects.get? t.toObjId
          = st.objects.get? t.toObjId := by
        rw [← RHTable_getElem?_eq_get?, ← RHTable_getElem?_eq_get?]
        exact updatePipBoostOnCore_objects_ne st c tid t.toObjId
          (fun h => hEq (ThreadId.toObjId_injective tid t (eq_of_beq h)).symm) hInv
      unfold SystemState.getTcb?; simp only [RHTable_getElem?_eq_get?, hObjNe]
    rw [hGet]

/-- WS-SM SM5.F.3 (plan §3.6, post-boost dominance): after a cross-core PIP boost,
the boosted holder's effective priority bounds *every* core's pre-state waiter slice
— premise-free (it does not assume PIP-consistency; the boost *establishes* it).

Chain: per-core slice ≤ global max-waiter (`_le_global`) = the holder's new
`pipBoost` (`_getTcb?_pipBoost`) ≤ the holder's new effective priority
(`optPriorityVal_pipBoost_le_effectiveSchedParams`).  This is the formal content of
"the boost covers the waiters that motivated it": no core's waiter outranks the
boosted holder. -/
theorem updatePipBoostOnCore_establishes_perCore_dominance (st : SystemState) (c c' : CoreId)
    (tid : ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) (hInv : st.objects.invExt) :
    ∃ t', (updatePipBoostOnCore st c tid).getTcb? tid = some t' ∧
      optPriorityVal (computeMaxWaiterPriorityOnCore st c' tid)
        ≤ (effectiveSchedParams (updatePipBoostOnCore st c tid) t').1.val := by
  obtain ⟨t', hPost, hPB⟩ := updatePipBoostOnCore_getTcb?_pipBoost st c tid tcb hTcb hInv
  refine ⟨t', hPost, ?_⟩
  calc optPriorityVal (computeMaxWaiterPriorityOnCore st c' tid)
      ≤ optPriorityVal (computeMaxWaiterPriority st tid) :=
        computeMaxWaiterPriorityOnCore_le_global st c' tid
    _ = optPriorityVal t'.pipBoost := by rw [hPB]
    _ ≤ (effectiveSchedParams (updatePipBoostOnCore st c tid) t').1.val :=
        optPriorityVal_pipBoost_le_effectiveSchedParams _ t'

-- ============================================================================
-- §9  SM5.F.4 — cross-core chain SGI completeness + single-core bridge
-- ============================================================================
--
-- `propagatePipChainCrossCore_head_sgi_remote` (§4) shows the chain *head* contributes
-- an SGI when remote+material.  The lemmas below close the completeness gap: every
-- link the walk visits, at any depth, contributes its `.reschedule` SGI to the root
-- list — `head_emission_mem` (a link's emission enters its local frame's list) +
-- `tail_sgis_mem` (every tail emission lifts to the root) compose to "every remote
-- link is poked".  Plus the SGI list is well-formed (`all_reschedule`) and bounded
-- (`length_le_fuel`, no SGI storm), and the single-core deployment fires no
-- cross-core IPI and reduces to the legacy `propagatePriorityInheritance` walk.

/-- WS-SM SM5.F.4: whatever SGI the chain *head* emits is in the collected list
(generalises `_head_sgi_remote` from the specific `.reschedule` form to any emission;
the per-link base case of the completeness argument). -/
theorem propagatePipChainCrossCore_head_emission_mem (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (n : Nat) (s : CoreId × SgiKind)
    (hHead : (pipBoostWithWake st tid ec).2 = some s) :
    s ∈ (propagatePipChainCrossCore st tid ec (n + 1)).2 := by
  rw [propagatePipChainCrossCore_step]
  cases hbs : blockingServer st tid <;> simp [hHead]

/-- WS-SM SM5.F.4: every SGI the *tail* walk collects lifts to the full list — the
inductive step of "every visited link contributes". -/
theorem propagatePipChainCrossCore_tail_sgis_mem (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (n : Nat) (nextServer : ThreadId)
    (hBS : blockingServer st tid = some nextServer) :
    ∀ x ∈ (propagatePipChainCrossCore (pipBoostWithWake st tid ec).1 nextServer ec n).2,
      x ∈ (propagatePipChainCrossCore st tid ec (n + 1)).2 := by
  intro x hx
  rw [propagatePipChainCrossCore_step]
  cases hsgi : (pipBoostWithWake st tid ec).2 with
  | none => simp only [hBS, hsgi]; simpa using hx
  | some s => simp only [hBS, hsgi]; exact List.mem_append.mpr (Or.inr hx)

/-- WS-SM SM5.F.4: every SGI in the cross-core chain list is a `.reschedule` — the
list is well-formed (no foreign SGI kinds slip in).  Lifts `pipBoostWithWake_sgi_is_reschedule`
to the whole chain. -/
theorem propagatePipChainCrossCore_sgis_all_reschedule (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (fuel : Nat) :
    ∀ p ∈ (propagatePipChainCrossCore st tid ec fuel).2, p.2 = SgiKind.reschedule := by
  induction fuel generalizing st tid with
  | zero => intro p hp; simp [propagatePipChainCrossCore] at hp
  | succ n ih =>
    intro p hp
    rw [propagatePipChainCrossCore_step] at hp
    cases hsgi : (pipBoostWithWake st tid ec).2 with
    | none =>
      cases hbs : blockingServer st tid with
      | none => simp only [hsgi, hbs] at hp; simp at hp
      | some nextServer =>
        simp only [hsgi, hbs] at hp
        exact ih (pipBoostWithWake st tid ec).1 nextServer p (by simpa using hp)
    | some s =>
      have hsk : s.2 = SgiKind.reschedule :=
        (pipBoostWithWake_sgi_is_reschedule st tid ec s.1 s.2 (by rw [hsgi])).2
      cases hbs : blockingServer st tid with
      | none =>
        simp only [hsgi, hbs] at hp
        rw [List.mem_singleton] at hp; rw [hp]; exact hsk
      | some nextServer =>
        simp only [hsgi, hbs] at hp
        rw [List.singleton_append, List.mem_cons] at hp
        rcases hp with hHead | hTail
        · rw [hHead]; exact hsk
        · exact ih (pipBoostWithWake st tid ec).1 nextServer p hTail

/-- WS-SM SM5.F.4 (bounded emission, SM5.C.11 latency parity): the chain SGI list has
length ≤ fuel — one SGI per visited link at most, never an SGI storm. -/
theorem propagatePipChainCrossCore_sgi_length_le_fuel (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (fuel : Nat) :
    (propagatePipChainCrossCore st tid ec fuel).2.length ≤ fuel := by
  induction fuel generalizing st tid with
  | zero => simp [propagatePipChainCrossCore]
  | succ n ih =>
    rw [propagatePipChainCrossCore_step]
    cases hsgi : (pipBoostWithWake st tid ec).2 with
    | none =>
      cases hbs : blockingServer st tid with
      | none => simp [hsgi]
      | some nextServer =>
        simp only [hsgi]
        exact Nat.le_trans (by simpa using ih (pipBoostWithWake st tid ec).1 nextServer)
          (Nat.le_succ n)
    | some s =>
      cases hbs : blockingServer st tid with
      | none => simp only [hsgi]; exact Nat.succ_le_succ (Nat.zero_le n)
      | some nextServer =>
        simp only [hsgi, List.singleton_append, List.length_cons]
        exact Nat.succ_le_succ (ih (pipBoostWithWake st tid ec).1 nextServer)

/-- WS-SM SM5.F.4 (depth-2 completeness witness): when the chain continues past the
head (`blockingServer st tid = some nextServer`) and the *second* link's boost is
remote and material, the second link's `.reschedule` SGI is in the root list —
concretely demonstrating that `head_emission_mem` + `tail_sgis_mem` propagate
emissions from beyond the head.  Generalises by induction to every link. -/
theorem propagatePipChainCrossCore_second_link_sgi_remote (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (n : Nat) (nextServer : ThreadId) (t t' : TCB)
    (hBS : blockingServer st tid = some nextServer)
    (hRemote : determineTargetCore (pipBoostWithWake st tid ec).1 nextServer ≠ ec)
    (hRunnable : nextServer ∈ (pipBoostWithWake st tid ec).1.scheduler.runQueueOnCore
                  (determineTargetCore (pipBoostWithWake st tid ec).1 nextServer))
    (hPre : (pipBoostWithWake st tid ec).1.getTcb? nextServer = some t)
    (hPost : (updatePipBoostOnCore (pipBoostWithWake st tid ec).1
              (determineTargetCore (pipBoostWithWake st tid ec).1 nextServer) nextServer).getTcb?
              nextServer = some t')
    (hMaterial : (resolveEffectivePrioDeadline (pipBoostWithWake st tid ec).1 t).1
      ≠ (resolveEffectivePrioDeadline (updatePipBoostOnCore (pipBoostWithWake st tid ec).1
          (determineTargetCore (pipBoostWithWake st tid ec).1 nextServer) nextServer) t').1) :
    (determineTargetCore (pipBoostWithWake st tid ec).1 nextServer, SgiKind.reschedule)
      ∈ (propagatePipChainCrossCore st tid ec (n + 1 + 1)).2 := by
  have hHeadTail : (pipBoostWithWake (pipBoostWithWake st tid ec).1 nextServer ec).2
      = some (determineTargetCore (pipBoostWithWake st tid ec).1 nextServer, SgiKind.reschedule) :=
    pipBoostWithWake_emits_sgi_if_remote (pipBoostWithWake st tid ec).1 nextServer ec t t'
      hRemote hRunnable hPre hPost hMaterial
  have hInTail : (determineTargetCore (pipBoostWithWake st tid ec).1 nextServer, SgiKind.reschedule)
      ∈ (propagatePipChainCrossCore (pipBoostWithWake st tid ec).1 nextServer ec (n + 1)).2 :=
    propagatePipChainCrossCore_head_emission_mem (pipBoostWithWake st tid ec).1 nextServer ec n _
      hHeadTail
  exact propagatePipChainCrossCore_tail_sgis_mem st tid ec (n + 1) nextServer hBS _ hInTail

/-- WS-SM SM5.F.4 (single-core bridge, no spurious IPI): on a single-core deployment
(every thread unbound ⇒ home = `bootCoreId`) the cross-core chain walk fires NO SGI
— there is no remote core to poke, so the trace carries no cross-core IPI.  The
all-unbound hypothesis is preserved along the walk by
`updatePipBoostOnCore_preserves_determineTargetCore`. -/
theorem propagatePipChainCrossCore_singleCore_no_sgis (st : SystemState) (tid : ThreadId)
    (fuel : Nat) (hInv : st.objects.invExt)
    (hAllBoot : ∀ t, determineTargetCore st t = bootCoreId) :
    (propagatePipChainCrossCore st tid bootCoreId fuel).2 = [] := by
  induction fuel generalizing st tid with
  | zero => rfl
  | succ n ih =>
    rw [propagatePipChainCrossCore_step]
    have hLocal : determineTargetCore st tid = bootCoreId := hAllBoot tid
    have hHeadNone : (pipBoostWithWake st tid bootCoreId).2 = none :=
      pipBoostWithWake_no_sgi_if_local st tid bootCoreId hLocal
    have hStInv : (pipBoostWithWake st tid bootCoreId).1.objects.invExt :=
      pipBoostWithWake_preserves_objects_invExt st tid bootCoreId hInv
    have hStBoot : ∀ t, determineTargetCore (pipBoostWithWake st tid bootCoreId).1 t = bootCoreId := by
      intro t
      rw [pipBoostWithWake_state, updatePipBoostOnCore_preserves_determineTargetCore st _ tid t hInv]
      exact hAllBoot t
    cases hbs : blockingServer st tid with
    | none => simp [hHeadNone]
    | some nextServer =>
      simp only [hHeadNone]
      exact ih (pipBoostWithWake st tid bootCoreId).1 nextServer hStInv hStBoot

/-- WS-SM SM5.F.4 (single-core bridge, behaviour-identical): on a single-core
deployment the cross-core chain walk's *state* effect is exactly the legacy
single-core `propagatePriorityInheritance` walk — `pipBoostWithWake` reduces to
`updatePipBoost` (home = `bootCoreId`) at every link.  This is the formal guarantee
that routing PIP through the per-core walk changes nothing on single-core hardware. -/
theorem propagatePipChainCrossCoreState_singleCore_eq_propagate (st : SystemState)
    (tid : ThreadId) (fuel : Nat) (hInv : st.objects.invExt)
    (hAllBoot : ∀ t, determineTargetCore st t = bootCoreId) :
    propagatePipChainCrossCoreState st tid bootCoreId fuel
      = propagatePriorityInheritance st tid fuel := by
  induction fuel generalizing st tid with
  | zero => rfl
  | succ n ih =>
    rw [propagatePipChainCrossCoreState_step, propagate_step]
    have hLocal : determineTargetCore st tid = bootCoreId := hAllBoot tid
    have hSt' : (pipBoostWithWake st tid bootCoreId).1 = updatePipBoost st tid := by
      rw [pipBoostWithWake_state, hLocal, ← updatePipBoost_eq_updatePipBoostOnCore_bootCore]
    have hStInv : (updatePipBoost st tid).objects.invExt := by
      rw [updatePipBoost_eq_updatePipBoostOnCore_bootCore]
      exact updatePipBoostOnCore_preserves_objects_invExt st bootCoreId tid hInv
    have hStBoot : ∀ t, determineTargetCore (updatePipBoost st tid) t = bootCoreId := by
      intro t
      rw [updatePipBoost_eq_updatePipBoostOnCore_bootCore,
          updatePipBoostOnCore_preserves_determineTargetCore st bootCoreId tid t hInv]
      exact hAllBoot t
    rw [hSt']
    cases hbs : blockingServer st tid with
    | none => rfl
    | some nextServer => exact ih (updatePipBoost st tid) nextServer hStInv hStBoot

-- ============================================================================
-- §9b  SM5.F.4 — memory-model happens-before for the cross-core PIP boost
-- ============================================================================
--
-- The cross-core PIP boost's `.reschedule` SGI obeys the same BKL release-acquire
-- discipline as the wake (SM5.C.4 `wakeOrdering_happensBefore`): the boosting core
-- emits `dsb ish` *before* writing `GICD_SGIR` (SM1.F.8), so its release-store of the
-- boosted holder's new run-queue bucket is visible to the home core before that core
-- takes the SGI (the acquire) and re-runs its scheduler.  The boost's ordering trace
-- is structurally identical to the wake's (a release-store on the boosting core
-- followed by an acquire-load on the home core, same location + value), so we lift
-- the verified `wakeOrdering_*` memory-model results rather than re-deriving them —
-- the events differ only in *meaning* (`loc`/`v` carry the pipBoost bucket rather than
-- the run-queue insertion), which the parameters and docstrings record.

/-- WS-SM SM5.F.4 (memory-model synchronizes-with): the boosting core's release-store
of the holder's new run-queue bucket **synchronizes-with** the home core's acquire-load
when it services the `.reschedule` SGI — the ARM ARM B2.3.7 release/acquire edge the
`dsb ish`-before-`GICD_SGIR` discipline (SM1.F.8) establishes for the cross-core PIP
boost.  Lifts `wakeOrdering_synchronizesWith` (same trace shape). -/
theorem pipBoostOrdering_synchronizesWith (boostCore homeCore : SeLe4n.Kernel.Concurrency.CoreId)
    (loc : SeLe4n.Kernel.Concurrency.AtomicLocation) (v : Nat) :
    SeLe4n.Kernel.Concurrency.synchronizesWith
      (SeLe4n.Kernel.Concurrency.wakeOrderingTrace boostCore homeCore loc v)
      (SeLe4n.Kernel.Concurrency.wakeReleaseEvent boostCore loc v)
      (SeLe4n.Kernel.Concurrency.wakeAcquireEvent homeCore loc v) :=
  SeLe4n.Kernel.Concurrency.wakeOrdering_synchronizesWith boostCore homeCore loc v

/-- WS-SM SM5.F.4 (memory-model headline HB): the cross-core PIP boost's run-queue
publication **happens-before** the home core observes it on the `.reschedule` SGI.

In the verified operational memory model, the boosting core's release of the holder's
new effective-priority bucket happens-before the home core's acquire of it — so when
the home core services the SGI and re-runs `handleRescheduleSgiOnCore`, the boosted
holder's raised priority is *guaranteed visible* in its run queue.  This is the
machine-checked statement of the boost's BKL ordering ("emit the SGI after the boost
is visible"), the PIP-boost analogue of `wakeOrdering_happensBefore`. -/
theorem pipBoostOrdering_happensBefore (boostCore homeCore : SeLe4n.Kernel.Concurrency.CoreId)
    (loc : SeLe4n.Kernel.Concurrency.AtomicLocation) (v : Nat) :
    SeLe4n.Kernel.Concurrency.happensBefore
      (SeLe4n.Kernel.Concurrency.wakeOrderingTrace boostCore homeCore loc v)
      (SeLe4n.Kernel.Concurrency.wakeReleaseEvent boostCore loc v)
      (SeLe4n.Kernel.Concurrency.wakeAcquireEvent homeCore loc v) :=
  SeLe4n.Kernel.Concurrency.wakeOrdering_happensBefore boostCore homeCore loc v

-- ============================================================================
-- §10  SM5.F.9 — priorityInheritance_perCore_witness_full (with decomposition)
-- ============================================================================

/-- WS-SM SM5.F.9 (plan §3.6, full aggregate witness): the complete per-core PIP
soundness witness — the three keystones of `priorityInheritance_perCore_witness`
(acyclicity preservation, per-core acyclicity, subgraph consistency) PLUS the
**exact per-core decomposition** (`computeMaxWaiterPriority_eq_sup_perCore`): the
global boost is the supremum over every core's waiter slice.

This is the closed-loop soundness + completeness statement: the per-core PIP is an
acyclic, consistent decomposition of the global priority-inheritance discipline that
loses no waiter's contribution (the boost the runtime reassembles from the per-core
slices is exactly the global boost). -/
theorem priorityInheritance_perCore_witness_full (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (hInv : st.objects.invExt) (hAcyclic : blockingAcyclic st) :
    blockingAcyclic (pipBoostWithWake st tid ec).1 ∧
    (∀ c, blockingAcyclicOnCore st c) ∧
    (∀ c t, blockingServerOnCore st c t = none ∨ blockingServerOnCore st c t = blockingServer st t) ∧
    optPriorityVal (computeMaxWaiterPriority st tid)
      = SeLe4n.Kernel.Concurrency.allCores.foldl
          (fun n c => Nat.max n (optPriorityVal (computeMaxWaiterPriorityOnCore st c tid))) 0 :=
  ⟨pipBoostWithWake_preserves_blockingAcyclic st tid ec hInv hAcyclic,
   fun c => blockingAcyclic_perCore st c hAcyclic,
   fun c t => blockingServerOnCore_subgraph st c t,
   computeMaxWaiterPriority_eq_sup_perCore st tid⟩

-- ============================================================================
-- §11  SM5.F.6 — resumeThreadOnCore (the complete per-core resume)
-- ============================================================================
--
-- `restoreToReadyOnCore` (§5) is the IPC-clear+enqueue *helper* (parallel to the
-- shared `restoreToReady`); it deliberately does NOT set `threadState`.  The
-- complete per-core resume `resumeThreadOnCore` (the per-core analogue of
-- `resumeThread`) closes that gap: it validates the target is `.Inactive`, sets
-- `threadState := .Ready`, recomputes the GLOBAL `pipBoost`, enqueues on the home
-- core, and returns the cross-core `.reschedule` SGI for a remote resume.

/-- WS-SM SM5.F.6 (helper): the resume "ready mid-state" carries a TCB at `tid` whose
`threadState` is `.Ready` — the H3c step `restoreToReadyOnCore` omits, isolated from
the run-queue enqueue. -/
theorem resumeReadyMidState_getTcb?_ready (st : SystemState) (tid : ThreadId) (tcb : TCB)
    (hGet : st.getTcb? tid = some tcb) (hInv : st.objects.invExt) :
    ∃ tm, (resumeReadyMidState st tid).getTcb? tid = some tm ∧ tm.threadState = .Ready := by
  have hst1Inv : (restoreToReady st tid).objects.invExt := restoreToReady_objects_invExt st tid hInv
  have hst1 : (restoreToReady st tid).getTcb? tid
      = some { tcb with ipcState := .ready, queuePrev := none, queueNext := none, queuePPrev := none, pendingReceiveReply := none } := by
    unfold restoreToReady
    simp only [hGet, SystemState.getTcb?_eq_some_iff, RHTable_getElem?_eq_get?]
    exact RHTable_get?_insert_self st.objects tid.toObjId _ hInv
  simp only [resumeReadyMidState, hst1]
  refine ⟨{ ({ tcb with ipcState := .ready, queuePrev := none, queueNext := none, queuePPrev := none, pendingReceiveReply := none }) with threadState := .Ready, pipBoost := computeMaxWaiterPriority (restoreToReady st tid) tid }, ?_, rfl⟩
  simp only [SystemState.getTcb?_eq_some_iff, RHTable_getElem?_eq_get?]
  exact RHTable_get?_insert_self (restoreToReady st tid).objects tid.toObjId _ hst1Inv

/-- WS-SM SM5.F.6 (helper): the resume "ready mid-state" preserves the object-store
invariant (`restoreToReady` then a single TCB `insert`). -/
theorem resumeReadyMidState_objects_invExt (st : SystemState) (tid : ThreadId)
    (hInv : st.objects.invExt) :
    (resumeReadyMidState st tid).objects.invExt := by
  have hst1Inv : (restoreToReady st tid).objects.invExt := restoreToReady_objects_invExt st tid hInv
  simp only [resumeReadyMidState]
  split
  · exact RHTable_insert_preserves_invExt _ _ _ hst1Inv
  · exact hst1Inv

/-- WS-SM SM5.F.6 (helper, PR #811 P2-5): the resume "ready mid-state" leaves the
scheduler untouched — `restoreToReady` and the single TCB `insert` write only the
object store.  So every core's `current` slot is preserved through the resume's
object-writing prefix (used to discharge the `currentOnCore ec ≠ some tid` side
condition of the inline local reschedule's `handleRescheduleSgiOnCore_getTcb?_ne_current`). -/
theorem resumeReadyMidState_scheduler_eq (st : SystemState) (tid : ThreadId) :
    (resumeReadyMidState st tid).scheduler = st.scheduler := by
  simp only [resumeReadyMidState]
  split <;> simp [Lifecycle.Suspend.restoreToReady_scheduler_eq]

/-- WS-SM SM8.B: and the machine state, register banks included.  Added beside
the scheduler frame for the per-core confinement consumer: SM5.I banks every
core's `RegisterFile` inside one `MachineState`, so a scheduler frame alone
never bounded this step's observable writes. -/
theorem resumeReadyMidState_machine_eq (st : SystemState) (tid : ThreadId) :
    (resumeReadyMidState st tid).machine = st.machine := by
  simp only [resumeReadyMidState]
  split <;> simp [Lifecycle.Suspend.restoreToReady_machine_eq]

/-- WS-SM SM5.F.6 (plan §3.6, resume H3c): the **complete** per-core resume sets the
resumed thread's `threadState := .Ready` — the run-queue enqueue (no-op when already
runnable, else `_makes_ready` which touches only `ipcState`) preserves it, so the
post-resume thread is genuinely `.Ready`.  This is the gap `restoreToReadyOnCore`
leaves and `resumeThreadOnCore` closes. -/
theorem resumeThreadOnCore_sets_threadState (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (ec : CoreId) (tcb : TCB) (st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hGet : st.getTcb? vtid.val = some tcb)
    (hInactive : tcb.threadState = .Inactive) (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore ec ≠ some vtid.val)
    (h : resumeThreadOnCore st vtid ec = .ok (st', sgi)) :
    ∃ t', st'.getTcb? vtid.val = some t' ∧ t'.threadState = .Ready := by
  obtain ⟨tm, hmid, hmidReady⟩ := resumeReadyMidState_getTcb?_ready st vtid.val tcb hGet hInv
  have hmidInv : (resumeReadyMidState st vtid.val).objects.invExt :=
    resumeReadyMidState_objects_invExt st vtid.val hInv
  -- The resume's object-writing prefix (H3+H4) establishes `tid` `.Ready` in the
  -- enqueued state `st3` (enqueue is no-op-or-`_makes_ready`; both keep `.Ready`).
  have hst3 : ∃ t3, (enqueueRunnableOnCore (resumeReadyMidState st vtid.val)
        (determineTargetCore st vtid.val) vtid.val).getTcb? vtid.val = some t3
        ∧ t3.threadState = .Ready := by
    by_cases hRun : runnableOnSomeCore (resumeReadyMidState st vtid.val) vtid.val = true
    · rw [SeLe4n.Kernel.enqueueRunnableOnCore_eq_self_of_runnable _ _ _ hRun]
      exact ⟨tm, hmid, hmidReady⟩
    · have hFresh : runnableOnSomeCore (resumeReadyMidState st vtid.val) vtid.val = false := by
        simpa using hRun
      exact ⟨{ tm with ipcState := .ready },
        SeLe4n.Kernel.enqueueRunnableOnCore_makes_ready _ _ _ tm hmid hmidInv hFresh, hmidReady⟩
  obtain ⟨t3, hst3get, hst3ready⟩ := hst3
  -- `tid` is not `ec`'s current in `st3` (the resume prefix preserves `currentOnCore`).
  have hst3cur : (enqueueRunnableOnCore (resumeReadyMidState st vtid.val)
      (determineTargetCore st vtid.val) vtid.val).scheduler.currentOnCore ec ≠ some vtid.val := by
    rw [SeLe4n.Kernel.enqueueRunnableOnCore_currentOnCore, resumeReadyMidState_scheduler_eq]
    exact hNotCur
  have hst3inv : (enqueueRunnableOnCore (resumeReadyMidState st vtid.val)
      (determineTargetCore st vtid.val) vtid.val).objects.invExt :=
    SeLe4n.Kernel.enqueueRunnableOnCore_preserves_objects_invExt _ _ _ hmidInv
  simp only [resumeThreadOnCore, hGet] at h
  rw [if_neg (by simp [hInactive])] at h
  by_cases hLoc : (determineTargetCore st vtid.val == ec) = true
  · -- LOCAL: the inline `handleRescheduleSgiOnCore` frames out `tid` (not `ec`'s
    -- current), so `tid` keeps the `.Ready` it had in `st3`.
    -- PR #861 review round 32: the local arm is gated on the context-restore
    -- seam, and the flag is a literal `false`, so this branch now returns the
    -- enqueued state `st3` unchanged — the same shape as REMOTE below.  When
    -- SM9.E flips the constant this reduction stops firing and the
    -- `handleRescheduleSgiOnCore_getTcb?_ne_current` step returns.
    simp only [hLoc, if_true, contextRestoreSeamLive, Bool.false_eq_true, if_false] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hst', _⟩ := h
    subst hst'
    exact ⟨t3, hst3get, hst3ready⟩
  · -- REMOTE: the result is the enqueued state `st3` directly.
    simp only [Bool.not_eq_true] at hLoc
    simp only [hLoc, Bool.false_eq_true, if_false] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hst', _⟩ := h
    subst hst'
    exact ⟨t3, hst3get, hst3ready⟩

/-- WS-SM SM5.F.6: the complete per-core resume preserves the object-store invariant —
the object-writing prefix (`resumeReadyMidState` + `enqueueRunnableOnCore`) preserves
`invExt`, and the inline local reschedule (`handleRescheduleSgiOnCore`) does too. -/
theorem resumeThreadOnCore_preserves_objects_invExt (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (ec : CoreId) (tcb : TCB) (st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hGet : st.getTcb? vtid.val = some tcb)
    (hInactive : tcb.threadState = .Inactive) (hInv : st.objects.invExt)
    (h : resumeThreadOnCore st vtid ec = .ok (st', sgi)) :
    st'.objects.invExt := by
  have hmidInv : (resumeReadyMidState st vtid.val).objects.invExt :=
    resumeReadyMidState_objects_invExt st vtid.val hInv
  have hst3inv : (enqueueRunnableOnCore (resumeReadyMidState st vtid.val)
      (determineTargetCore st vtid.val) vtid.val).objects.invExt :=
    SeLe4n.Kernel.enqueueRunnableOnCore_preserves_objects_invExt _ _ _ hmidInv
  simp only [resumeThreadOnCore, hGet] at h
  rw [if_neg (by simp [hInactive])] at h
  by_cases hLoc : (determineTargetCore st vtid.val == ec) = true
  · -- Round 32: gated local arm — the state is `st3` (see the note above).
    simp only [hLoc, if_true, contextRestoreSeamLive, Bool.false_eq_true, if_false] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hst', _⟩ := h
    subst hst'
    exact hst3inv
  · simp only [Bool.not_eq_true] at hLoc
    simp only [hLoc, Bool.false_eq_true, if_false] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hst', _⟩ := h
    subst hst'
    exact hst3inv

/-- WS-SM SM5.F.6: resume of a non-`.Inactive` TCB is rejected with `illegalState`
(parity with `resumeThread`). -/
theorem resumeThreadOnCore_rejects_non_inactive (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (ec : CoreId) (tcb : TCB)
    (hGet : st.getTcb? vtid.val = some tcb)
    (hState : tcb.threadState ≠ .Inactive) :
    resumeThreadOnCore st vtid ec = .error .illegalState := by
  simp only [resumeThreadOnCore, hGet]
  rw [if_pos (by simpa using hState)]

/-- WS-SM SM5.F.6: resume of a non-TCB object (or absent slot) is rejected with
`invalidArgument` — the typed `getTcb?` returns `none` for both. -/
theorem resumeThreadOnCore_rejects_non_tcb (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (ec : CoreId) (hGet : st.getTcb? vtid.val = none) :
    resumeThreadOnCore st vtid ec = .error .invalidArgument := by
  simp only [resumeThreadOnCore, hGet]

/-- WS-SM SM5.F.6 (PR #811 P2-5): a LOCAL complete resume (home = executing core)
emits **no** cross-core SGI — the reschedule is processed inline on the executing core
(`handleRescheduleSgiOnCore`), never deferred to a remote core.  Stated as an
implication over a successful result (the inline reschedule may itself error on a
malformed run queue; on any `.ok` result the SGI component is `none`). -/
theorem resumeThreadOnCore_local_no_sgi (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (ec : CoreId) (tcb : TCB) (st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hGet : st.getTcb? vtid.val = some tcb)
    (hInactive : tcb.threadState = .Inactive)
    (hLocal : determineTargetCore st vtid.val = ec)
    (h : resumeThreadOnCore st vtid ec = .ok (st', sgi)) :
    sgi = none := by
  simp only [resumeThreadOnCore, hGet] at h
  rw [if_neg (by simp [hInactive])] at h
  -- Round 32: the local arm is gated on the context-restore seam, so it returns
  -- `(st3, none)` directly.  The conclusion is unchanged — a local resume still
  -- posts no SGI — and it is now true for a simpler reason.
  simp only [hLocal, beq_self_eq_true, if_true, contextRestoreSeamLive,
    Bool.false_eq_true, if_false] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

/-- WS-SM SM5.F.6: a REMOTE complete resume succeeds and returns the `.reschedule`
SGI to the resumed thread's home core. -/
theorem resumeThreadOnCore_remote_sgi (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (ec : CoreId) (tcb : TCB)
    (hGet : st.getTcb? vtid.val = some tcb)
    (hInactive : tcb.threadState = .Inactive)
    (hRemote : determineTargetCore st vtid.val ≠ ec) :
    ∃ st', resumeThreadOnCore st vtid ec
      = .ok (st', some (determineTargetCore st vtid.val, SgiKind.reschedule)) := by
  simp only [resumeThreadOnCore, hGet]
  rw [if_neg (by simp [hInactive])]
  have hb : (determineTargetCore st vtid.val == ec) = false := by
    cases h : (determineTargetCore st vtid.val == ec) with
    | false => rfl
    | true => exact absurd (eq_of_beq h) hRemote
  simp only [hb]
  exact ⟨_, rfl⟩

/-- WS-SM SM5.F.6 (PR #811 P2-3): the cross-core resume wake leaves the resumed thread
genuinely `.Ready` — it never enqueues / pokes a core for a still-`.Inactive` TCB.  The
pure (state + SGI) analogue of `resumeThreadOnCore_sets_threadState`; the state path goes
through `resumeReadyMidState` (which sets `.Ready`). -/
theorem restoreToReadyWithWake_sets_threadState (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (tcb : TCB) (hGet : st.getTcb? tid = some tcb) (hInv : st.objects.invExt) :
    ∃ t', (restoreToReadyWithWake st tid ec).1.getTcb? tid = some t' ∧ t'.threadState = .Ready := by
  rw [restoreToReadyWithWake_state]
  obtain ⟨tm, hmid, hmidReady⟩ := resumeReadyMidState_getTcb?_ready st tid tcb hGet hInv
  have hmidInv : (resumeReadyMidState st tid).objects.invExt :=
    resumeReadyMidState_objects_invExt st tid hInv
  by_cases hRun : runnableOnSomeCore (resumeReadyMidState st tid) tid = true
  · rw [SeLe4n.Kernel.enqueueRunnableOnCore_eq_self_of_runnable _ _ _ hRun]
    exact ⟨tm, hmid, hmidReady⟩
  · have hFresh : runnableOnSomeCore (resumeReadyMidState st tid) tid = false := by simpa using hRun
    exact ⟨{ tm with ipcState := .ready },
      SeLe4n.Kernel.enqueueRunnableOnCore_makes_ready _ _ _ tm hmid hmidInv hFresh, hmidReady⟩

-- ============================================================================
-- §12  SM5.F.4 — cross-core wake dispatch (the SM6 runtime firing layer)
-- ============================================================================
--
-- The per-core PIP transitions (§3/§4/§5) return the set of cross-core
-- `.reschedule` SGIs a boost warrants; SM5.I's runtime fires them.  This section is
-- the **dispatch** that pulls that firing forward: `computeCrossCoreSgis` derives the
-- SGIs from a transition's *state diff* (for the generic syscall path, which returns
-- only a post-state), and the BaseIO combinators (`crossCoreWakeDispatch`,
-- `pipChainWakeDispatch`, …) commit nothing new but *fire* the SGIs over the FFI
-- (`Concurrency.fireCrossCoreSgis`).  Each combinator is proven **inert on single-core**
-- (`pure ()` when every thread is on the boot core) — so wiring it into the live
-- IPC donation / timeout / resume paths is trace-preserving on single-core hardware
-- and activates automatically once per-core affinities are set.

/-- WS-SM SM5.F.4 / SM6.B: the per-object body of the diff-based dispatch — emits a
`.reschedule` SGI to a thread's *remote* home core iff its presence/bucket in that
core's run queue *changed* across `pre → post`.  Two material cases:

* a **wake / migration** — the thread became newly runnable on its home core (in
  `post`'s home run queue, not in `pre`'s).  This is the SM6.A endpoint-call
  receiver / SM6.B notification-waiter / bound-TCB wake: it leaves the effective
  priority unchanged, yet a freshly-runnable remote thread must be scheduled on its
  home core.  (The earlier priority-only gate dropped this SGI — the live wake
  arrived only at the home core's next timer tick.)
* a **re-bucketing / re-ranking** — the thread was already runnable on its home
  core but its *effective* priority OR deadline (`resolveEffectivePrioDeadline`,
  both components — audit closure: within-bucket selection is EDF, so a
  deadline-only change re-ranks the candidate without moving its bucket)
  changed: a PIP boost (PR #811 P2-2) or a `schedContextConfigure` deadline
  rewrite.  An *immaterial* rewrite (both components unchanged on an
  already-runnable thread) fires nothing.
* a **deschedule** (WS-SM SM6.E) — the thread was *actively current* on its remote
  home core in `pre` and in `post` is neither current nor queued there: a
  cross-core suspend/cancellation removed it, so the home core must be poked to
  stop executing it and dispatch a successor.  (Without this rule a live
  `.tcbSuspend` of a remote-running victim would leave that core executing the
  suspended thread until its next timer tick.)
* a **weakened current** (WS-SM SM6.E, PR #831 review 2 + audit closure) — the
  thread is still current on the same core in both `pre` and `post` but its
  claim to the CPU weakened: its effective priority *dropped* (a PIP-revert
  disinheritance) or its effective deadline moved *later* (EDF re-ranking —
  `schedContextConfigure`): a ready thread on that core may now outrank the
  running choice, so it must re-run its preemption gate.  A strengthening
  (priority raise / deadline pulled earlier) fires nothing (the running choice
  can only outrank strictly more), and a still-current thread is not in the
  run queue (dequeue-on-dispatch), so the queue rules never cover this case.

**Queue-branch precedence (audit note).**  A tid queued on its post-home
never reaches the CURRENT rules.  This is sound under today's transitions —
no single transition both removes a thread from being current on core A and
re-enqueues it on a different core's queue (suspend never re-enqueues; wakes
target non-current threads; migrating a *running* thread to a different
specific core is rejected) — but it is a precedence assumption, not a
theorem.  If such a transition is ever added, restructure this body to run
the current scan unconditionally and union the emissions.

**Scan completeness.**  The pre-current scan takes the FIRST core whose slot
holds the tid; completeness rests on `currentThreadUniqueAcrossCores`
(`Scheduler/Invariant/PerCore.lean`, audit closure) — a thread is current on
at most one core, so there is no second core to miss.

Factored out so the dispatch theorems reference it by name (the single object-store
read site, mirroring `waitersOf`'s raw iteration). -/
def crossCoreSgiBody (pre post : SystemState) (execCore : CoreId) (oid : ObjId)
    : Option (CoreId × SgiKind) :=
  match post.objects[oid]? with
  | some (KernelObject.tcb tpost) =>
    match pre.getTcb? tpost.tid with
    | some tpre =>
      let home := SeLe4n.Kernel.determineTargetCore post tpost.tid
      if tpost.tid ∈ post.scheduler.runQueueOnCore home then
        -- QUEUE rules (wake / re-bucketing), home-keyed: a queued thread lives
        -- on its home core's run queue (the SM5.H.4 migration maintains this).
        -- A home on the executing core needs no poke (single-core inert); fire
        -- UNLESS the thread was already runnable on `home` (not a wake) AND its
        -- effective bucket is unchanged (not a re-bucketing).
        if home == execCore then none
        else if (tpost.tid ∈ pre.scheduler.runQueueOnCore home)
            && ((SeLe4n.Kernel.resolveEffectivePrioDeadline pre tpre).1
                  == (SeLe4n.Kernel.resolveEffectivePrioDeadline post tpost).1)
            && ((SeLe4n.Kernel.resolveEffectivePrioDeadline pre tpre).2.val
                  == (SeLe4n.Kernel.resolveEffectivePrioDeadline post tpost).2.val) then none
        else some (home, SgiKind.reschedule)
      else
        -- CURRENT rules (descheduled / weakened), keyed on the core the
        -- thread was ACTUALLY current on in `pre` (PR #831 review 4): an
        -- unbound thread can be current on a NON-home core (unbinding a
        -- running secondary-core thread is admitted, and its home reverts to
        -- boot — see `runningCoreOf?`), so keying these rules on `home` made
        -- a deschedule/deboost of such a thread invisible to the diff.
        match SeLe4n.Kernel.Concurrency.allCores.find? (fun c =>
            pre.scheduler.currentOnCore c == some tpost.tid) with
        | some preCur =>
          if preCur == execCore then none
          else if !(post.scheduler.currentOnCore preCur == some tpost.tid) then
            -- descheduled-current (WS-SM SM6.E): a cross-core cancellation
            -- removed the running victim — poke the core that was executing it.
            some (preCur, SgiKind.reschedule)
          else if ((SeLe4n.Kernel.resolveEffectivePrioDeadline post tpost).1.val
                < (SeLe4n.Kernel.resolveEffectivePrioDeadline pre tpre).1.val)
              || ((SeLe4n.Kernel.resolveEffectivePrioDeadline pre tpre).2.val
                < (SeLe4n.Kernel.resolveEffectivePrioDeadline post tpost).2.val) then
            -- deboosted-current (PR #831 review 2): still current, effective
            -- priority dropped — the running core must re-run its preemption
            -- gate.  A raise fires nothing.
            some (preCur, SgiKind.reschedule)
          else none
        | none => none
    | none => none
  | _ => none

/-- WS-SM SM8.B (PR #861 review round 16): the cross-core `.reschedule` SGIs
warranted by a **changed `current` slot**, independent of any object.

`crossCoreSgiBody` is indexed by `post.objectIndex` and opens by matching
`post.objects[oid]?` against `some (.tcb tpost)`, falling through to `none`
otherwise — so a change whose subject no longer *exists* in the post-state is
structurally invisible to it.  (Written across two lines deliberately: the AK7
cascade gate greps line-wise for a raw object-store match, and does not exempt
prose that quotes one.)  Destroying a TCB that is current on a remote core is exactly that case: the
retype scrubs and repurposes the object, the sweep clears that core's `current`,
and the object rule then finds no TCB to reason about — so the remote core was
left executing a thread whose storage had already been reused, with no poke.

Deriving the poke from the **slot** rather than from the object closes the whole
class: a remote core whose current thread changed must re-run its scheduler, and
that is true whether the outgoing thread was descheduled, deboosted, or
destroyed.  The executing core is excluded by construction, so a single-core
build (where it is the only core) emits nothing — the same inertness the object
rules maintain. -/
def currentSlotChangeSgis (pre post : SystemState) (execCore : CoreId) :
    List (CoreId × SgiKind) :=
  (SeLe4n.Kernel.Concurrency.allCores.filter (fun c =>
      (c != execCore) && (post.scheduler.currentOnCore c != pre.scheduler.currentOnCore c))).map
    (fun c => (c, SgiKind.reschedule))

/-- WS-SM SM5.F.4 (SM6 dispatch decision): the cross-core `.reschedule` SGIs a
transition `pre → post` warrants, derived from the state diff — one per *remote*
(home ≠ `execCore`) thread whose *effective* run-queue bucket
(`resolveEffectivePrioDeadline`) changed,
coalesced by target core.  This is the dispatch for the generic syscall path, which
returns only a post-state (the per-core boost transitions return their SGIs directly). -/
def computeCrossCoreSgis (pre post : SystemState) (execCore : CoreId) : List (CoreId × SgiKind) :=
  SeLe4n.Kernel.Concurrency.dedupCrossCoreSgis
    (post.objectIndex.filterMap (crossCoreSgiBody pre post execCore)
      ++ currentSlotChangeSgis pre post execCore)

/-- WS-SM SM8.B: the slot rule is **inert on one core** — the executing core is
excluded by construction, and on a single-core build it is the only core. -/
theorem currentSlotChangeSgis_not_execCore (pre post : SystemState) (execCore c : CoreId)
    (k : SgiKind) (h : (c, k) ∈ currentSlotChangeSgis pre post execCore) :
    c ≠ execCore ∧ post.scheduler.currentOnCore c ≠ pre.scheduler.currentOnCore c := by
  unfold currentSlotChangeSgis at h
  simp only [List.mem_map, List.mem_filter] at h
  obtain ⟨c', ⟨-, hFilter⟩, hEq⟩ := h
  simp only [Prod.mk.injEq] at hEq
  obtain ⟨hc, -⟩ := hEq
  subst hc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hFilter
  exact ⟨hFilter.1, hFilter.2⟩

/-- WS-SM SM8.B: and it emits only `.reschedule`. -/
theorem currentSlotChangeSgis_reschedule (pre post : SystemState) (execCore : CoreId)
    (p : CoreId × SgiKind) (h : p ∈ currentSlotChangeSgis pre post execCore) :
    p.2 = SgiKind.reschedule := by
  unfold currentSlotChangeSgis at h
  simp only [List.mem_map, List.mem_filter] at h
  obtain ⟨c, -, hEq⟩ := h
  rw [← hEq]

/-- WS-SM SM8.B (**the destroy case, which the object rule cannot see**): a core
whose `current` slot changed is poked even when the thread that was running
there no longer exists in the post-state. -/
theorem currentSlotChangeSgis_fires_on_change (pre post : SystemState)
    (execCore c : CoreId) (hne : c ≠ execCore)
    (hChanged : post.scheduler.currentOnCore c ≠ pre.scheduler.currentOnCore c) :
    (c, SgiKind.reschedule) ∈ currentSlotChangeSgis pre post execCore := by
  unfold currentSlotChangeSgis
  simp only [List.mem_map, List.mem_filter]
  exact ⟨c, ⟨SeLe4n.Kernel.Concurrency.mem_allCores c, by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨hne, hChanged⟩⟩, rfl⟩

/-! `contextRestoreSeamLive` — the seam flag every consumer reads — now lives
in `SeLe4n.Kernel.Concurrency.ContextRestoreSeam`, imported above and
re-exported by this namespace.  It moved down (PR #861 review round 29)
because `SchedContext/OperationsPerCore.lean` needs the *same* flag for its
own local-reschedule guard and cannot import this module: that edge closes a
cycle through `Kernel.API` / `Model.FreezeProofs` / `Platform.Boot`.  A second
literal would have been the round-20 drift defect all over again. -/

/-- WS-SM SM8.B (PR #861 review round 17): did this transition **vacate the
executing core** — leave it with no current thread when it had one?

The local half of `currentSlotChangeSgis`.  That rule pokes every *remote* core
whose `current` slot changed and excludes the executing core by construction,
for the correct reason — a core does not send itself an interrupt, it runs the
handler inline.  The inline half was never built, so the exclusion was total: a
core that vacated its own slot ran no scheduler at all.

Gated on the **change**, not on the post-state alone.  `post.current = none` by
itself would fire on a core that was already idle before the syscall, which is
not a vacated core and needs no reschedule; and firing unconditionally would add
preemption points that do not exist today, since
`handleRescheduleSgiOnCore` switches whenever a candidate outranks the current
thread. -/
def localSuccessorNeeded (pre post : SystemState) (execCore : CoreId) : Bool :=
  (pre.scheduler.currentOnCore execCore != none) &&
    (post.scheduler.currentOnCore execCore == none)

/-- WS-SM SM8.B (PR #861 review round 17): **run the executing core's scheduler
when the transition vacated it.**

Every blocking leg of the IPC surface — `endpointSendDualOnCore` on the block
path, `endpointReceiveDualOnCore`, `endpointCallOnCore`,
`notificationWaitOnCore` — clears the caller's `current` slot and stops.
Nothing then selects a successor: the timer tick cannot
(`timerTickOnCore_eq_prepared`'s `none` arm returns the prepared state
untouched, and `processReplenishmentsDueOnCore_currentOnCore_eq` says the
prepared state leaves the slot alone), and the SGI list deliberately excludes
the executing core.  The core therefore idles with a populated run queue until
some *other* core happens to poke it — a liveness defect, and a denial of
service when no other core does.

Stated as a **pure state function** so every property below is a theorem about a
pure function, in the project's style; the `BaseIO` entry seam calls it once.

The `.error` arm keeps the committed post-state (fail-closed: a reschedule that
cannot pick a successor must not discard the transition that just committed).
It is reachable only through `switchToThreadOnCore`'s own rejections — the
*selection* side is total, since `chooseBestRunnableEffective_always_ok` (this
PR, review round 15) made the scan skip a non-TCB entry rather than fail.  That
is what lets this be stated without a scheduler-invariant hypothesis. -/
def scheduleLocalSuccessor (pre post : SystemState) (execCore : CoreId) : SystemState :=
  if localSuccessorNeeded pre post execCore then
    match handleRescheduleSgiOnCore post execCore with
    | .ok st => st
    | .error _ => post
  else post

/-- WS-SM SM8.B: the rule is **inert unless the executing core was vacated** —
so a transition that left the slot alone, or that rescheduled the core itself,
passes through unchanged. -/
@[simp] theorem scheduleLocalSuccessor_of_not_needed (pre post : SystemState) (execCore : CoreId)
    (h : localSuccessorNeeded pre post execCore = false) :
    scheduleLocalSuccessor pre post execCore = post := by
  unfold scheduleLocalSuccessor
  simp [h]

/-- WS-SM SM8.B: in particular, inert when the core was **already idle** before
the transition.  A core with nothing to run is not a vacated core. -/
theorem scheduleLocalSuccessor_of_pre_idle (pre post : SystemState) (execCore : CoreId)
    (h : pre.scheduler.currentOnCore execCore = none) :
    scheduleLocalSuccessor pre post execCore = post := by
  apply scheduleLocalSuccessor_of_not_needed
  unfold localSuccessorNeeded
  simp [h]

/-- WS-SM SM8.B: and inert when the transition **left a thread running** on the
executing core.

This is what makes it safe to apply the rule at *every* entry, including
`suspendThreadCrossCoreEntry`, whose transition already runs its own scheduling
point (`suspendRescheduleOnCore`): where a transition rescheduled the core
itself, the post-state slot is populated and this rule does not fire.  The two
mechanisms cannot both dispatch. -/
theorem scheduleLocalSuccessor_of_post_running (pre post : SystemState) (execCore : CoreId)
    (tid : SeLe4n.ThreadId) (h : post.scheduler.currentOnCore execCore = some tid) :
    scheduleLocalSuccessor pre post execCore = post := by
  apply scheduleLocalSuccessor_of_not_needed
  unfold localSuccessorNeeded
  simp [h]

/-- WS-SM SM8.B (PR #861 review round 20): **the successor dispatch as the live
entries run it** — gated on the restore seam it depends on.

`scheduleLocalSuccessor` is correct at the model level and its theorems say so.
But dispatching a successor the runtime cannot install is not an improvement on
not dispatching one.

**Neither state is safe, and this gate does not make one safe** (PR #861 review
round 21 — an earlier version of this note claimed otherwise and was wrong).
Without a context-restore seam the SVC path returns through the blocked caller's
own frame either way, so the caller **keeps executing user code it should not be
running**, on both sides of this guard.  What differs is only what happens at
its *next* syscall: with `currentOnCore = none` the dispatch rejects it
(`syscallDispatchFromAbi` returns `.illegalState`), while with a named successor
it is **attributed to that successor**.  Rejection is better than
misattribution, so the gate picks the less-bad of two broken states — it is a
relative choice, not a safety property, and "fails closed" describes the syscall
boundary alone.

The switch is therefore coupled to its prerequisite rather than described
alongside it.  Today this is `post`; when SM9.E flips `contextRestoreSeamLive`
it becomes the dispatch, with no other edit.  The vacated-core liveness defect
stays open and stays recorded (`contextSwitchSites_restore_pending`), as does
the larger fact it belongs to: with no context restore and no registered
INTID-0 handler, *no* modelled thread switch reaches hardware on any path —
timer preemption, cross-core wake, or syscall.

Deliberately a *wrapper*: folding the guard into `scheduleLocalSuccessor` would
make every theorem about it conditional, and those theorems are what SM9.E
enables rather than has to re-prove. -/
def scheduleLocalSuccessorLive (pre post : SystemState) (execCore : CoreId) : SystemState :=
  if contextRestoreSeamLive then scheduleLocalSuccessor pre post execCore else post

/-- WS-SM SM8.B: what the kernel does **today** — nothing.  `rfl`, so this is
the definition rather than a claim about it. -/
@[simp] theorem scheduleLocalSuccessorLive_inert (pre post : SystemState) (execCore : CoreId) :
    scheduleLocalSuccessorLive pre post execCore = post := rfl

/-- WS-SM SM8.B: and what it does once the seam is live — the full dispatch, so
the flip loses nothing. -/
theorem scheduleLocalSuccessorLive_eq_of_seam_live (pre post : SystemState) (execCore : CoreId)
    (h : contextRestoreSeamLive = true) :
    scheduleLocalSuccessorLive pre post execCore = scheduleLocalSuccessor pre post execCore := by
  unfold scheduleLocalSuccessorLive
  rw [h]
  rfl

/-- WS-SM SM8.B: the two halves of the guard, forward. -/
theorem localSuccessorNeeded_post_none (pre post : SystemState) (execCore : CoreId)
    (h : localSuccessorNeeded pre post execCore = true) :
    post.scheduler.currentOnCore execCore = none := by
  unfold localSuccessorNeeded at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  exact h.2

theorem localSuccessorNeeded_pre_some (pre post : SystemState) (execCore : CoreId)
    (h : localSuccessorNeeded pre post execCore = true) :
    pre.scheduler.currentOnCore execCore ≠ none := by
  unfold localSuccessorNeeded at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  exact h.1

/-- WS-SM SM8.B: a vacated core admits **any** candidate — the preemption gate's
`none` arm.  There is no incumbent to outrank, so the comparison the gate would
otherwise make does not arise. -/
theorem candidateOutranksCurrentOnCore_of_vacated (post : SystemState) (execCore : CoreId)
    (tid : SeLe4n.ThreadId) (h : post.scheduler.currentOnCore execCore = none) :
    candidateOutranksCurrentOnCore post execCore tid = true := by
  unfold candidateOutranksCurrentOnCore
  rw [h]

/-- WS-SM SM8.B (**the headline**): a vacated core **dispatches its successor**.

When the transition left the executing core with no current thread and that
core's run queue holds a budget-eligible candidate, the post-entry state has
that candidate running.  This is the property whose absence was the defect: the
same premises previously left `current = none` with the queue untouched, and
nothing in the system would have changed that before the next unrelated
cross-core poke.

`hOutrank` — the premise its cross-core sibling
`wakeThread_then_handle_dispatches_current` has to assume — is *discharged*
here rather than assumed, because a vacated core has no incumbent. -/
theorem scheduleLocalSuccessor_dispatches (pre post : SystemState) (execCore : CoreId)
    (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hNeeded : localSuccessorNeeded pre post execCore = true)
    (hChosen : chooseThreadEffectiveOnCore post execCore = .ok (some tid))
    (hSwitch : switchToThreadOnCore post execCore tid = .ok st') :
    (scheduleLocalSuccessor pre post execCore).scheduler.currentOnCore execCore = some tid := by
  have hOutrank : candidateOutranksCurrentOnCore post execCore tid = true :=
    candidateOutranksCurrentOnCore_of_vacated post execCore tid
      (localSuccessorNeeded_post_none pre post execCore hNeeded)
  have hHandle : handleRescheduleSgiOnCore post execCore = .ok st' := by
    rw [handleRescheduleSgiOnCore_eq_switch_of_choose_some post execCore tid hChosen hOutrank]
    exact hSwitch
  unfold scheduleLocalSuccessor
  rw [if_pos hNeeded, hHandle]
  exact handleRescheduleSgiOnCore_switches_current post execCore tid st' hChosen hOutrank hHandle

/-- WS-SM SM8.B: and the selection side cannot be what blocks it.  A vacated
core whose run queue holds no budget-eligible thread keeps the committed
post-state — the honest idle outcome, distinct from the defect it replaces
(which idled a core whose queue *did* hold an eligible thread). -/
theorem scheduleLocalSuccessor_idle_of_no_candidate (pre post : SystemState) (execCore : CoreId)
    (hChosen : chooseThreadEffectiveOnCore post execCore = .ok none) :
    scheduleLocalSuccessor pre post execCore = post := by
  unfold scheduleLocalSuccessor handleRescheduleSgiOnCore
  rw [hChosen]
  split <;> rfl

/-- WS-SM SM5.F.4: the dispatch body emits only `.reschedule` SGIs. -/
theorem crossCoreSgiBody_reschedule (pre post : SystemState) (ec : CoreId) (oid : ObjId)
    (p : CoreId × SgiKind) (h : crossCoreSgiBody pre post ec oid = some p) :
    p.2 = SgiKind.reschedule := by
  unfold crossCoreSgiBody at h
  split at h
  · split at h
    · simp only [] at h
      split at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Option.some.injEq] at h; rw [← h]
      · split at h
        · split at h
          · simp at h
          · split at h
            · simp only [Option.some.injEq] at h; rw [← h]
            · split at h
              · simp only [Option.some.injEq] at h; rw [← h]
              · simp at h
        · simp at h
    · simp at h
  · simp at h

/-- PR #831 review 4: on a single-core deployment the pre-state current scan
can only resolve to the boot core — every secondary current slot is empty. -/
theorem currentScan_boot_of_single_core (pre : SystemState) (tid : SeLe4n.ThreadId)
    (hNoRemoteCur : ∀ c : CoreId, c ≠ bootCoreId →
      pre.scheduler.currentOnCore c = none)
    {c : CoreId}
    (hFind : SeLe4n.Kernel.Concurrency.allCores.find? (fun c =>
        pre.scheduler.currentOnCore c == some tid) = some c) :
    c = bootCoreId := by
  have hp := List.find?_some hFind
  by_cases hB : c = bootCoreId
  · exact hB
  · rw [hNoRemoteCur c hB] at hp
    simp at hp

/-- WS-SM SM5.F.4: under all-boot homes AND empty secondary current slots
(single-core deployment — PR #831 review 4 added the current-slot premise when
the descheduled/deboosted rules were re-keyed from the home to the pre-state
running core) the dispatch body is `none`. -/
theorem crossCoreSgiBody_none_single_core (pre post : SystemState) (oid : ObjId)
    (hAllBoot : ∀ t, SeLe4n.Kernel.determineTargetCore post t = bootCoreId)
    (hNoRemoteCur : ∀ c : CoreId, c ≠ bootCoreId →
      pre.scheduler.currentOnCore c = none) :
    crossCoreSgiBody pre post bootCoreId oid = none := by
  unfold crossCoreSgiBody
  split
  · split
    · simp only []
      split
      · rw [if_pos (by simp [hAllBoot])]
      · split
        · rename_i preCur heq
          rw [if_pos (by
            simp [currentScan_boot_of_single_core pre _ hNoRemoteCur heq])]
        · rfl
    · rfl
  · rfl

/-- WS-SM SM6.B (the wake-SGI fix, positive direction): a thread that becomes newly
runnable on a *remote* home core — present in `pre`, in `post`'s home-core run queue
but *not* in `pre`'s home-core run queue — makes the dispatch body emit a
`.reschedule` SGI to that home core.  This is the cross-core poke a notification /
endpoint-call wake warrants; the earlier priority-only gate dropped it (a wake leaves
the effective priority unchanged).  The positive companion of
`crossCoreSgiBody_reschedule` (kind) and `crossCoreSgiBody_none_single_core`
(single-core inertness). -/
theorem crossCoreSgiBody_remote_wake (pre post : SystemState) (execCore : CoreId)
    (oid : ObjId) (tpost tpre : TCB)
    (hPost : post.objects[oid]? = some (.tcb tpost))
    (hPre : pre.getTcb? tpost.tid = some tpre)
    (hRemote : SeLe4n.Kernel.determineTargetCore post tpost.tid ≠ execCore)
    (hPostRq : tpost.tid ∈
        post.scheduler.runQueueOnCore (SeLe4n.Kernel.determineTargetCore post tpost.tid))
    (hPreNotRq : tpost.tid ∉
        pre.scheduler.runQueueOnCore (SeLe4n.Kernel.determineTargetCore post tpost.tid)) :
    crossCoreSgiBody pre post execCore oid
      = some (SeLe4n.Kernel.determineTargetCore post tpost.tid, SgiKind.reschedule) := by
  unfold crossCoreSgiBody
  rw [hPost]
  simp only [hPre]
  rw [if_pos hPostRq, if_neg (by simpa using hRemote),
      if_neg (by simp [hPreNotRq])]

/-- WS-SM SM6.E (the deschedule-SGI rule, positive direction): a thread that was
**actively current** on some *remote* core in `pre` (the pre-state running-core
scan — PR #831 review 4: keyed on the core actually running it, which for an
unbound thread may differ from its home) and in `post` is neither current there
nor queued on its home makes the dispatch body emit a `.reschedule` SGI to that
running core — the cross-core poke a suspend/cancellation of a running victim
warrants, so that core stops executing it.  The suspend-side companion of
`crossCoreSgiBody_remote_wake`. -/
theorem crossCoreSgiBody_remote_deschedule (pre post : SystemState) (execCore : CoreId)
    (oid : ObjId) (tpost tpre : TCB) (preCur : CoreId)
    (hPost : post.objects[oid]? = some (.tcb tpost))
    (hPre : pre.getTcb? tpost.tid = some tpre)
    (hPostNotRq : tpost.tid ∉
        post.scheduler.runQueueOnCore (SeLe4n.Kernel.determineTargetCore post tpost.tid))
    (hFind : SeLe4n.Kernel.Concurrency.allCores.find? (fun c =>
        pre.scheduler.currentOnCore c == some tpost.tid) = some preCur)
    (hRemote : preCur ≠ execCore)
    (hPostNotCur : post.scheduler.currentOnCore preCur ≠ some tpost.tid) :
    crossCoreSgiBody pre post execCore oid
      = some (preCur, SgiKind.reschedule) := by
  unfold crossCoreSgiBody
  rw [hPost]
  simp only [hPre, hFind]
  rw [if_neg hPostNotRq, if_neg (by simpa using hRemote),
      if_pos (by simp [hPostNotCur])]

/-- WS-SM SM6.E (the deboosted-current rule, positive direction — PR #831
review 2, re-keyed by review 4 on the pre-state running core): a thread that is
**still current** on the same *remote* core across `pre → post` but whose
effective priority *dropped* (a PIP-revert disinheritance) makes the dispatch
body emit a `.reschedule` SGI to that core, so a ready thread that now outranks
the deboosted current is dispatched instead of waiting for the next timer tick.
The still-current companion of `crossCoreSgiBody_remote_deschedule`. -/
theorem crossCoreSgiBody_remote_deboost_current (pre post : SystemState)
    (execCore : CoreId) (oid : ObjId) (tpost tpre : TCB) (preCur : CoreId)
    (hPost : post.objects[oid]? = some (.tcb tpost))
    (hPre : pre.getTcb? tpost.tid = some tpre)
    (hPostNotRq : tpost.tid ∉
        post.scheduler.runQueueOnCore (SeLe4n.Kernel.determineTargetCore post tpost.tid))
    (hFind : SeLe4n.Kernel.Concurrency.allCores.find? (fun c =>
        pre.scheduler.currentOnCore c == some tpost.tid) = some preCur)
    (hRemote : preCur ≠ execCore)
    (hPostCur : post.scheduler.currentOnCore preCur = some tpost.tid)
    (hDrop : (SeLe4n.Kernel.resolveEffectivePrioDeadline post tpost).1.val
        < (SeLe4n.Kernel.resolveEffectivePrioDeadline pre tpre).1.val) :
    crossCoreSgiBody pre post execCore oid
      = some (preCur, SgiKind.reschedule) := by
  unfold crossCoreSgiBody
  rw [hPost]
  simp only [hPre, hFind]
  rw [if_neg hPostNotRq, if_neg (by simpa using hRemote),
      if_neg (by simp [hPostCur]), if_pos (by simp [hDrop])]

/-- WS-SM SM5.F.4: every SGI the diff-based dispatch emits is a `.reschedule` — it
pokes cores only to reschedule, never with a foreign SGI kind. -/
theorem computeCrossCoreSgis_all_reschedule (pre post : SystemState) (ec : CoreId) :
    ∀ p ∈ computeCrossCoreSgis pre post ec, p.2 = SgiKind.reschedule := by
  intro p hp
  have hsub := SeLe4n.Kernel.Concurrency.dedupCrossCoreSgis_subset _ p hp
  -- Round 16: two sources now — the object-indexed rules and the slot rule.
  rcases List.mem_append.mp hsub with hObj | hSlot
  · rw [List.mem_filterMap] at hObj
    obtain ⟨oid, _, hbody⟩ := hObj
    exact crossCoreSgiBody_reschedule pre post ec oid p hbody
  · exact currentSlotChangeSgis_reschedule pre post ec p hSlot

/-- WS-SM SM5.F.4 (single-core inertness): on a single-core deployment (every thread
on the boot core ⇒ home = `bootCoreId` = `execCore`) the diff-based dispatch emits NO
SGI.  No production thread on the current single-core path has a remote home, so
`computeCrossCoreSgis` is `[]` there — the dispatch is safe to wire (trace-preserving)
and activates only once per-core affinities exist. -/
theorem computeCrossCoreSgis_nil_single_core (pre post : SystemState)
    (hAllBoot : ∀ t, SeLe4n.Kernel.determineTargetCore post t = bootCoreId)
    (hNoRemoteCur : ∀ c : CoreId, c ≠ bootCoreId →
      pre.scheduler.currentOnCore c = none)
    (hNoRemoteCurPost : ∀ c : CoreId, c ≠ bootCoreId →
      post.scheduler.currentOnCore c = none) :
    computeCrossCoreSgis pre post bootCoreId = [] := by
  unfold computeCrossCoreSgis currentSlotChangeSgis
  rw [List.filterMap_eq_nil_iff.mpr (fun oid _ =>
    crossCoreSgiBody_none_single_core pre post oid hAllBoot hNoRemoteCur)]
  -- Round 16: the slot rule is nil for the same reason the object rules are —
  -- on a single-core deployment no remote core is running anything in EITHER
  -- state, so no remote slot can have changed.  The post-state hypothesis is
  -- new and is not a weakening: it is the same single-core fact as the
  -- pre-state one, which the object rules already required.
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · intro c _
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not]
    intro hne
    rw [hNoRemoteCur c (by simpa using hne), hNoRemoteCurPost c (by simpa using hne)]

/-- WS-SM SM5.F.4 (SM6 dispatch, generic syscall path): fire the cross-core
`.reschedule` SGIs a transition `pre → post` warrants.  Wire this into the BaseIO
syscall-return path (after the pure transition commits, before returning to user mode)
so a cross-core PIP boost from a syscall fires its SGI; on the current single-core path
it is `pure ()` (`crossCoreWakeDispatch_singleCore`). -/
def crossCoreWakeDispatch (pre post : SystemState) (execCore : CoreId) : BaseIO Unit :=
  SeLe4n.Kernel.Concurrency.fireCrossCoreSgis (computeCrossCoreSgis pre post execCore)

/-- WS-SM SM5.F.4: the diff-based syscall dispatch is inert (`pure ()`) on single-core. -/
theorem crossCoreWakeDispatch_singleCore (pre post : SystemState)
    (hAllBoot : ∀ t, SeLe4n.Kernel.determineTargetCore post t = bootCoreId)
    (hNoRemoteCur : ∀ c : CoreId, c ≠ bootCoreId →
      pre.scheduler.currentOnCore c = none)
    (hNoRemoteCurPost : ∀ c : CoreId, c ≠ bootCoreId →
      post.scheduler.currentOnCore c = none) :
    crossCoreWakeDispatch pre post bootCoreId = pure () := by
  unfold crossCoreWakeDispatch
  rw [computeCrossCoreSgis_nil_single_core pre post hAllBoot hNoRemoteCur hNoRemoteCurPost]
  rfl

/-- WS-SM SM5.F.4 (SM6 dispatch, chain path): run the pure cross-core PIP boost chain
(the caller has committed its boost state under the lock) and fire the chain's
cross-core `.reschedule` SGIs.  The dispatch SM5.I invokes from the live IPC donation
path so a cross-core donation boost fires every remote link's SGI. -/
def pipChainWakeDispatch (st : SystemState) (tid : ThreadId) (execCore : CoreId)
    (fuel : Nat := st.objectIndex.length) : BaseIO Unit :=
  SeLe4n.Kernel.Concurrency.fireCrossCoreSgis (propagatePipChainCrossCore st tid execCore fuel).2

/-- WS-SM SM5.F.4: the chain-wake dispatch is inert (`pure ()`) on single-core
(`propagatePipChainCrossCore_singleCore_no_sgis`). -/
theorem pipChainWakeDispatch_singleCore (st : SystemState) (tid : ThreadId) (fuel : Nat)
    (hInv : st.objects.invExt)
    (hAllBoot : ∀ t, SeLe4n.Kernel.determineTargetCore st t = bootCoreId) :
    pipChainWakeDispatch st tid bootCoreId fuel = pure () := by
  unfold pipChainWakeDispatch
  rw [propagatePipChainCrossCore_singleCore_no_sgis st tid fuel hInv hAllBoot]
  rfl

/-- WS-SM SM5.F.4 (SM6 dispatch, single-boost / resume paths): fire the optional SGI a
`pipBoostWithWake` / `restoreToReadyWithWake` / `resumeThreadOnCore` returned — the
single-SGI dispatch (lifts SM5.C `emitWakeSgi`).  Used by the live timeout / resume
paths so a remote boost or resume fires its `.reschedule` SGI. -/
def emitBoostWakeSgi (sgi : Option (CoreId × SgiKind)) : BaseIO Unit :=
  SeLe4n.Kernel.Concurrency.emitWakeSgi sgi

/-- WS-SM SM5.F.4: a local boost/resume (`none`) fires nothing. -/
@[simp] theorem emitBoostWakeSgi_none : (emitBoostWakeSgi none : BaseIO Unit) = pure () := rfl

-- ============================================================================
-- WS-SM SM8.B — the context-restore obligation, as a tripwire
-- ============================================================================

/-- WS-SM SM8.B (PR #861 review round 18): **the sites that change which thread
a core's model says is current.**

Each of these writes `scheduler.currentOnCore` and — through
`switchToThreadOnCore` — `machine.regsOnCore`.  On hardware a change of current
thread is only real once the *outgoing* context is saved into the outgoing
TCB and the *incoming* `registerContext`, `ELR_EL1`, `SPSR_EL1` and address
space are restored before `eret`.  This enumeration exists so that obligation
is a checked partition rather than prose. -/
inductive ContextSwitchSite where
  /-- The periodic tick's preemption point (`timerTickOnCore` →
      `scheduleEffectiveOnCore` → `switchToThreadOnCore`). -/
  | timerPreemption
  /-- The cross-core `.reschedule` SGI handler (`handleRescheduleSgiOnCore`). -/
  | rescheduleSgi
  /-- The suspend pipeline's own scheduling point (`suspendRescheduleOnCore`). -/
  | suspendReschedule
  /-- The vacated-core successor dispatch added in review round 17
      (`scheduleLocalSuccessor`, in `syscallDispatchCrossCoreEntry`). -/
  | vacatedCoreSuccessor
  deriving DecidableEq, Repr, Inhabited

/-- WS-SM SM8.B: the enumeration. -/
def contextSwitchSites : List ContextSwitchSite :=
  [.timerPreemption, .rescheduleSgi, .suspendReschedule, .vacatedCoreSuccessor]

/-- WS-SM SM8.B (the tripwire): every constructor is listed.  A new site that
changes a core's current thread breaks this `decide`, which is the reminder
that it owes the hardware restore below. -/
theorem contextSwitchSites_complete (s : ContextSwitchSite) : s ∈ contextSwitchSites := by
  cases s <;> decide

/-- WS-SM SM8.B: **does this site restore the incoming thread's context to
hardware before exception return?**

For v0.33.5 the answer is uniformly `false`, and that is a statement about the
runtime rather than about any of these transitions:

* the SVC path writes its result into the *original caller's* `ExceptionFrame`
  and returns from that frame (`rust/sele4n-hal/src/trap.rs`, the
  `ec::SVC_AARCH64` arm);
* `lean_per_core_timer_tick` returns `void`, so the timer ISR discards whatever
  the model decided (`rust/sele4n-hal/src/timer.rs`);
* SGI INTID 0 (`.reschedule`) has **no registered handler at all** — only the
  TLB-shootdown request and halt-all INTIDs are registered
  (`rust/sele4n-hal/src/gic.rs`);
* and `machine.regsOnCore` is named nowhere in `SeLe4n/Platform/FFI.lean`, so
  no seam exists to carry a register bank across the boundary in either
  direction.

The consequence is model/hardware divergence about which thread is running,
and it is not merely cosmetic: `syscallDispatchFromAbi` identifies its caller
*solely* by `st.scheduler.currentOnCore executingCore`, so a syscall arriving
from the thread hardware actually resumed would be attributed to the thread the
model believes is current.

Registered rather than fixed because the fix is the SM9.E bring-up seam —
outgoing-context save, incoming-context restore, `ELR`/`SPSR`/`TTBR0`/ASID —
which is a coherent slice of its own and not part of a non-interference proof
cut.  `contextRestoreWired` is the partition: wiring one means flipping its
entry, which breaks the theorem below and forces the change to be reviewed
rather than absorbed silently. -/
def contextRestoreWired : ContextSwitchSite → Bool
  -- The timer ISR calls `lean_per_core_timer_tick`, which returns `void`, and
  -- SGI INTID 0 has no registered handler — neither has a trap frame to install
  -- into, independently of the syscall seam.
  | .timerPreemption      => false
  | .rescheduleSgi        => false
  -- The two syscall-entry sites are wired exactly when the seam is.  Read from
  -- `contextRestoreSeamLive` rather than repeated as literals (round 20), so
  -- this register and the guard on `scheduleLocalSuccessorLive` cannot drift:
  -- the successor is dispatched precisely when its context can be installed.
  | .suspendReschedule    => contextRestoreSeamLive
  | .vacatedCoreSuccessor => contextRestoreSeamLive

/-- WS-SM SM8.B (the honesty marker): **no** context-switch site restores
hardware context yet.

Stated as the full list rather than as "some are pending", because today the
gap is total — this is the one form that makes the *scope* of the divergence
checkable.  When SM9.E wires the first restore, this theorem fails and the
register must be updated in the same commit.

Note the direction of the round-17 change against this backdrop.  Before it, a
blocking syscall left `currentOnCore = none`, and `syscallDispatchFromAbi`
fails *closed* on that (`.illegalState`).  After it the slot names a real
successor, so the same divergence would misidentify a caller rather than
reject it — worse, on a system that had a restore seam to diverge from.  It is
still the right change (a kernel that never dispatches a successor is not a
kernel), but the two must land in that order, which is what this marker
records.

**Which switches are gated, and why not all of them** (PR #861 review rounds 23
and 28).  The rule is *this PR does not add new instances of a pre-existing
defect class* — not *this PR fixes the class*.  So the two scheduling points it
introduced are gated on `contextRestoreSeamLive`:

* `.vacatedCoreSuccessor` — created in round 17, guarded by
  `scheduleLocalSuccessorLive`;
* the `.schedContextUnbind` local reschedule — created in round 15, guarded by
  `SchedContextOps.unbindRescheduleTarget?`;
* `priorityRescheduleOnCore`'s local arm — shared by `.tcbSetPriority`,
  `.tcbSetMCPriority` and (redundantly, above the call-site guard)
  `.schedContextUnbind`;
* `resumeThreadOnCore`'s local arm, behind `.tcbResume`.

In each case the *remote* arm is deliberately ungated: a cross-core
`.reschedule` SGI is a real poke at another processor and has nothing to do
with the missing restore.

**A correction (round 32).** The last two were declined in rounds 23 and 28 on
the grounds that their scheduling points predate this PR.  That was the wrong
granularity.  The *point* is old; the **local switch on a secondary core** is
new, because both arms were boot-pinned before this cut rerouted them — running
`.tcbSetPriority` on core 2 used to poke the boot core, not switch core 2.  So
they sit on the "created here" side of the rule after all, and they are gated
now.

The supporting argument offered at the time — that `.timerPreemption` is
ungated and fires every tick, so gating a syscall path only delays a
misattributed context rather than preventing one — is true, and is a statement
about how *incomplete* the mitigation is, not a licence to skip it.  It applied
equally to the two sites that were gated, which is what made the position
inconsistent.

`.timerPreemption` remains the one ungated site, and cannot be gated: it is how
threads get scheduled at all.  SM9.E closes it with the rest.

All the guards read the one flag, which since round 29 lives in
`SeLe4n.Kernel.Concurrency.ContextRestoreSeam` — low enough that the
`SchedContext` operations can import it, which this module is not (that edge
closes a cycle through `Kernel.API` / `Model.FreezeProofs` / `Platform.Boot`).
One definition, so the flip stays a one-constant change. -/
theorem contextSwitchSites_restore_pending :
    contextSwitchSites.filter (fun s => !contextRestoreWired s) = contextSwitchSites := by
  decide

/-- WS-SM SM8.B: the same fact in the form a consumer would read. -/
theorem contextRestoreWired_none (s : ContextSwitchSite) : contextRestoreWired s = false := by
  cases s <;> rfl

/-- WS-SM SM8.B (PR #861 review round 20, **the coupling**): the live successor
dispatch is inert exactly while its own site is unwired.

This is what makes the ordering a mechanism rather than a note.  A transition
that changes `currentOnCore` on a core whose restore is not wired leaves the
model and the hardware disagreeing about who is running — and
`syscallDispatchFromAbi` identifies its caller *solely* by
`currentOnCore executingCore`, so that disagreement misattributes the next
syscall.  Since `currentOnCore = none` instead fails closed (`.illegalState`),
dispatching an uninstallable successor is strictly worse than dispatching none.

Both sides read `contextRestoreSeamLive`, so SM9.E flips one constant and the
dispatch and its register move together. -/
theorem scheduleLocalSuccessorLive_guard_eq_register :
    contextRestoreSeamLive = contextRestoreWired .vacatedCoreSuccessor := rfl

/-- WS-SM SM8.B: and the same for the suspend entry, which installs through the
identical seam. -/
theorem suspendReschedule_guard_eq_register :
    contextRestoreSeamLive = contextRestoreWired .suspendReschedule := rfl

end SeLe4n.Kernel.PriorityInheritance
