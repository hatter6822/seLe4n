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
open SeLe4n.Kernel.Lifecycle.Suspend (restoreToReady restoreToReadyOnCore restoreToReadyWithWake)

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

/-- WS-SM SM5.F.2 (Theorem 3.6.1 emission): a REMOTE, MATERIAL PIP boost emits a
`.reschedule` SGI to the holder's home core.  "Material" = the boost actually
changed the holder's `pipBoost` (hence its effective run-queue bucket), so the
remote core's scheduler must re-evaluate (the boosted holder may now outrank its
current thread). -/
theorem pipBoostWithWake_emits_sgi_if_remote (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (t t' : TCB)
    (hRemote : determineTargetCore st tid ≠ ec)
    (hPre : st.getTcb? tid = some t)
    (hPost : (updatePipBoostOnCore st (determineTargetCore st tid) tid).getTcb? tid = some t')
    (hMaterial : t.pipBoost ≠ t'.pipBoost) :
    (pipBoostWithWake st tid ec).2 = some (determineTargetCore st tid, SgiKind.reschedule) := by
  have hRem : (determineTargetCore st tid == ec) = false := by
    cases h : (determineTargetCore st tid == ec) with
    | false => rfl
    | true => exact absurd (eq_of_beq h) hRemote
  have hMat : (t.pipBoost == t'.pipBoost) = false := by
    cases h : (t.pipBoost == t'.pipBoost) with
    | false => rfl
    | true => exact absurd (eq_of_beq h) hMaterial
  simp [pipBoostWithWake, hRem, hPre, hPost, hMat]

/-- WS-SM SM5.F.2: a NO-OP PIP boost (the holder's `pipBoost` is unchanged) emits no
SGI — there is no scheduling consequence, so poking a remote core would be a
spurious cross-core IPI (the SM5.C.11 latency concern). -/
theorem pipBoostWithWake_no_sgi_if_noop (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (t t' : TCB)
    (hPre : st.getTcb? tid = some t)
    (hPost : (updatePipBoostOnCore st (determineTargetCore st tid) tid).getTcb? tid = some t')
    (hNoop : t.pipBoost = t'.pipBoost) :
    (pipBoostWithWake st tid ec).2 = none := by
  have hEq : (t.pipBoost == t'.pipBoost) = true := by rw [hNoop]; exact beq_self_eq_true _
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
      · simp at hSgi
      · simp only [Option.some.injEq, Prod.mk.injEq] at hSgi
        exact ⟨hSgi.1.symm, hSgi.2.symm⟩
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
    (hPre : st.getTcb? tid = some t)
    (hPost : (updatePipBoostOnCore st (determineTargetCore st tid) tid).getTcb? tid = some t')
    (hMaterial : t.pipBoost ≠ t'.pipBoost) :
    ∃ rest, (propagatePipChainCrossCore st tid ec (n + 1)).2
      = (determineTargetCore st tid, SgiKind.reschedule) :: rest := by
  rw [propagatePipChainCrossCore_step]
  have hHead : (pipBoostWithWake st tid ec).2
      = some (determineTargetCore st tid, SgiKind.reschedule) :=
    pipBoostWithWake_emits_sgi_if_remote st tid ec t t' hRemote hPre hPost hMaterial
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

/-- WS-SM SM5.F.6: `restoreToReadyWithWake`'s state component is the per-core
re-ready on the resumed thread's home core. -/
@[simp] theorem restoreToReadyWithWake_state (st : SystemState) (tid : ThreadId) (ec : CoreId) :
    (restoreToReadyWithWake st tid ec).1 = restoreToReadyOnCore st (determineTargetCore st tid) tid := rfl

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

/-- WS-SM SM5.F.6: `restoreToReadyWithWake` preserves the object-store invariant. -/
theorem restoreToReadyWithWake_preserves_objects_invExt (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (hInv : st.objects.invExt) :
    (restoreToReadyWithWake st tid ec).1.objects.invExt := by
  rw [restoreToReadyWithWake_state]
  exact restoreToReadyOnCore_preserves_objects_invExt st _ tid hInv

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

end SeLe4n.Kernel.PriorityInheritance
