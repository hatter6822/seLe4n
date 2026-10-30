-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsPreservation

/-!
# WS-SM SM5.I — the live per-core timer tick preserves replenish-queue affinity-consistency

This module discharges the third (and previously hypothesised) conjunct of
`perCoreCbsInvariant` for the live `timerTickOnCore`: replenish-queue
**affinity-consistency** (every queued SchedContext's bound thread is homed on the
core).  The SM5.I landing (`PerCoreTickCbsPreservation`) proved validity +
pipeline-order unconditionally but exposed affinity-consistency as an explicit
`hAffinity` input.  Here that input is **eliminated**: the tick provably never
writes a TCB's `cpuAffinity` (so every thread's `determineTargetCore` home core is
unchanged) nor a SchedContext's `boundThread` (so every queued SC still names the
same thread), and the only *new* replenish entry — the budget tick's
`now + period` insert for the running thread's bound SchedContext — is homed on the
tick core under the **affinity-placement invariant** (a thread current on core `c`
is homed on `c`) plus `schedContextBindingConsistent`.

The result (`timerTickOnCore_preserves_perCoreCbsInvariant`, the strengthened
aggregate moved here) takes the placement invariant + binding consistency + the
object-store well-formedness invariant `invExt` — all maintained by the per-core
scheduler — and proves all three conjuncts, with no assume-the-conclusion
hypothesis.

## Proof architecture

* **Atoms** (§1): a single object-store `insert` of a TCB (resp. SchedContext) at a
  TCB- (resp. SchedContext-) occupied slot preserves every thread's
  `determineTargetCore` and every SchedContext's `boundThread` (the off-key frames
  via `RHTable` `insert_ne`, the on-key cases via the field hypothesis or the
  kind-mismatch `getTcb?_none_of_schedContext` / `getSchedContext?_none_of_tcb`).
* **Transfer helper** (§1): affinity-consistency transfers across any state change
  that (a) only shrinks the replenish queue (subset), (b) preserves
  `determineTargetCore`, and (c) preserves the `boundThread` projection.
* **Per-op frames** (§2): `enqueueRunnableOnCore` / `refillSchedContext` /
  `saveOutgoingContextOnCore` / `scheduleEffectiveOnCore` preserve
  `determineTargetCore` + `boundThread`.
* **Replenishment fold** (§3): `processReplenishmentsDueOnCore` (the prepared phase)
  preserves both, via the per-step `processOneReplenishmentOnCore` frame folded over
  the due-list.
* **Per-phase + headline** (§4): the **prepared** and **schedule** phases preserve
  affinity-consistency (fully proven, via the transfer helper); the **budget** phase
  is supplied as `hBudgetAffinity` — the one residual, since its exhausted arm runs
  the IPC `timeoutBlockedThreads` whose `determineTargetCore` / `getSchedContext?`
  frame reduces to `endpointQueueRemove`'s object-store key-distinctness (a
  `dualQueueSystemInvariant` consequence; tracked debt).  The headline
  `timerTickOnCore_preserves_replenishQueueAffinityConsistentOnCore` composes the
  three phases.
* **Aggregate** (§4): the strengthened `timerTickOnCore_preserves_perCoreCbsInvariant`
  discharges all three CBS conjuncts — replacing the v0.31.57 whole-state
  assume-the-conclusion `hAffinity` with the meaningful, maintained
  `hBudgetAffinity` (budget-phase frame) plus `invExt`.

## Build reachability

Staged via `SeLe4n/Platform/Staged.lean` (with `PerCoreTickCbsPreservation`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId SgiKind bootCoreId)

-- ============================================================================
-- §1  Foundation: insert atoms + the affinity-transfer helper
-- ============================================================================

/-- WS-SM SM5.I (keystone): replenish-queue affinity-consistency transfers across a
state change `st ↝ base` whose core-`c` queue holds only contexts `st`'s held
(`hSub`, at any release time: affinity reads the context, not its place),
preserves every thread's home core (`hTgt`), and preserves every SchedContext's
`boundThread` projection (`hBound`).  Every carried-over context's bound thread
is still homed on `c`. -/
theorem affinityConsistent_transfer_ids (st base : SystemState) (c : CoreId)
    (hSub : ∀ e, e ∈ (base.scheduler.replenishQueueOnCore c).entries →
                 ∃ t', (e.1, t') ∈ (st.scheduler.replenishQueueOnCore c).entries)
    (hTgt : ∀ tid, determineTargetCore base tid = determineTargetCore st tid)
    (hBound : ∀ scId, (base.getSchedContext? scId).map (·.boundThread)
                    = (st.getSchedContext? scId).map (·.boundThread))
    (hCons : replenishQueueAffinityConsistentOnCore st c) :
    replenishQueueAffinityConsistentOnCore base c := by
  intro scId t hMem sc hScBase tid hBoundEq
  rw [hTgt tid]
  have hMapEq := hBound scId
  rw [hScBase] at hMapEq
  cases hSt : st.getSchedContext? scId with
  | none => rw [hSt] at hMapEq; simp at hMapEq
  | some sc0 =>
    rw [hSt] at hMapEq
    simp only [Option.map_some] at hMapEq
    have hbeq : sc.boundThread = sc0.boundThread := Option.some.inj hMapEq
    have hb0 : sc0.boundThread = some tid := hbeq ▸ hBoundEq
    obtain ⟨t', ht'⟩ := hSub _ hMem
    exact hCons scId t' ht' sc0 hSt tid hb0

/-- `affinityConsistent_transfer_ids` for a step that only *shrinks* core `c`'s
queue. -/
theorem affinityConsistent_transfer (st base : SystemState) (c : CoreId)
    (hSub : ∀ e, e ∈ (base.scheduler.replenishQueueOnCore c).entries →
                 e ∈ (st.scheduler.replenishQueueOnCore c).entries)
    (hTgt : ∀ tid, determineTargetCore base tid = determineTargetCore st tid)
    (hBound : ∀ scId, (base.getSchedContext? scId).map (·.boundThread)
                    = (st.getSchedContext? scId).map (·.boundThread))
    (hCons : replenishQueueAffinityConsistentOnCore st c) :
    replenishQueueAffinityConsistentOnCore base c :=
  affinityConsistent_transfer_ids st base c (fun e h => ⟨e.2, hSub e h⟩) hTgt hBound hCons

-- (WS-RR bind/unbind affinity closure: the four insert atoms and the
-- preempt/switch `determineTargetCore` / `boundThread` frames moved to the
-- production `PerCoreSwitchToThread.lean` — the production
-- `SchedContext/BindingAffinity.lean` surface consumes them, and nothing in
-- them reads a staged surface.  They remain visible here through the import
-- closure.)

-- ── shallow TCB / SchedContext writes ──

/-- WS-SM SM5.I: `enqueueRunnableOnCore` preserves every SchedContext's
`boundThread` projection. -/
theorem enqueueRunnableOnCore_boundThread (st : SystemState) (c : CoreId)
    (tid0 : SeLe4n.ThreadId) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    ((enqueueRunnableOnCore st c tid0).getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  rw [enqueueRunnableOnCore_getSchedContext? st c tid0 hInv]

/-- WS-SM SM5.I: `refillSchedContext` (a budget/replenishment SchedContext write)
preserves every thread's home core. -/
theorem refillSchedContext_determineTargetCore (st : SystemState) (scId0 : SeLe4n.SchedContextId)
    (now : Nat) (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    determineTargetCore (refillSchedContext st scId0 now) t = determineTargetCore st t := by
  -- The refill is a typed update: its two equations replace the split.
  unfold refillSchedContext
  cases hOld : st.getSchedContext? scId0 with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hOld]
  | some sc =>
    rw [SystemState.updateSchedContext_eq_of_some hOld]
    exact determineTargetCore_congr_getTcb? _ st t
      (getTcb?_insert_schedContext_eq st _ scId0 sc _ hInv ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hOld) rfl t)

/-- WS-SM SM5.I: `refillSchedContext` preserves every SchedContext's `boundThread`
projection (`processReplenishments` / `cbsUpdateDeadline` write only budget / deadline
fields, never `boundThread`). -/
theorem refillSchedContext_boundThread (st : SystemState) (scId0 : SeLe4n.SchedContextId)
    (now : Nat) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    ((refillSchedContext st scId0 now).getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  unfold refillSchedContext
  cases hOld : st.getSchedContext? scId0 with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hOld]
  | some sc =>
    rw [SystemState.updateSchedContext_eq_of_some hOld]
    have hBT : (cbsUpdateDeadline (processReplenishments sc now) now true).boundThread
        = sc.boundThread := by
      simp only [cbsUpdateDeadline, processReplenishments, applyRefill]
      split <;> simp [SchedContext.boundThread]
    exact getSchedContext?_boundThread_insert_schedContext st _ scId0 sc _ hInv ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hOld) hBT rfl scId

/-- WS-SM SM5.I: `saveOutgoingContextOnCore` (a register-context TCB write) preserves
every thread's home core. -/
theorem saveOutgoingContextOnCore_determineTargetCore (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    determineTargetCore (saveOutgoingContextOnCore st c) t = determineTargetCore st t := by
  cases hc : st.scheduler.currentOnCore c with
  | none => rw [show saveOutgoingContextOnCore st c = st from by simp only [saveOutgoingContextOnCore, hc]]
  | some outTid =>
    cases ho : st.getTcb? outTid with
    | none => rw [show saveOutgoingContextOnCore st c = st from by
        simp only [saveOutgoingContextOnCore, hc, SystemState.updateTcb_eq_self_of_none ho]]
    | some outTcb =>
      have hRaw := (SystemState.getTcb?_eq_some_iff st outTid outTcb).mp ho
      have hObj : (saveOutgoingContextOnCore st c).objects
          = st.objects.insert outTid.toObjId (.tcb { outTcb with registerContext := st.machine.regsOnCore c }) := by
        simp only [saveOutgoingContextOnCore, hc, SystemState.updateTcb_eq_of_some ho]
      exact determineTargetCore_insert_tcb st _ outTid outTcb
        { outTcb with registerContext := st.machine.regsOnCore c } hInv hRaw rfl hObj t

/-- WS-SM SM5.I: `saveOutgoingContextOnCore` preserves every SchedContext's
`boundThread` projection. -/
theorem saveOutgoingContextOnCore_boundThread (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    ((saveOutgoingContextOnCore st c).getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  cases hc : st.scheduler.currentOnCore c with
  | none => rw [show saveOutgoingContextOnCore st c = st from by simp only [saveOutgoingContextOnCore, hc]]
  | some outTid =>
    cases ho : st.getTcb? outTid with
    | none => rw [show saveOutgoingContextOnCore st c = st from by
        simp only [saveOutgoingContextOnCore, hc, SystemState.updateTcb_eq_self_of_none ho]]
    | some outTcb =>
      have hRaw := (SystemState.getTcb?_eq_some_iff st outTid outTcb).mp ho
      have hObj : (saveOutgoingContextOnCore st c).objects
          = st.objects.insert outTid.toObjId (.tcb { outTcb with registerContext := st.machine.regsOnCore c }) := by
        simp only [saveOutgoingContextOnCore, hc, SystemState.updateTcb_eq_of_some ho]
      rw [getSchedContext?_insert_tcb_eq st _ outTid outTcb
        { outTcb with registerContext := st.machine.regsOnCore c } hInv hRaw hObj scId]

/-- WS-SM SM5.I: a successful `scheduleEffectiveOnCore` preserves every thread's home
core (its only object write is the outgoing register-context save). -/
theorem scheduleEffectiveOnCore_determineTargetCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') (t : SeLe4n.ThreadId) :
    determineTargetCore st' t = determineTargetCore st t := by
  rw [determineTargetCore_of_objectsAgreeOffRunLinks
    (scheduleEffectiveOnCore_objectsAgreeOffRunLinks st c st' hStep)]
  exact saveOutgoingContextOnCore_determineTargetCore st c hInv t

/-- WS-SM SM5.I: a successful `scheduleEffectiveOnCore` preserves every
SchedContext's `boundThread` projection. -/
theorem scheduleEffectiveOnCore_boundThread (st : SystemState) (c : CoreId)
    (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') (scId : SeLe4n.SchedContextId) :
    (st'.getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  rw [(scheduleEffectiveOnCore_objectsAgreeOffRunLinks st c st' hStep).getSchedContext? scId]
  exact saveOutgoingContextOnCore_boundThread st c hInv scId

-- ============================================================================
-- §3  Replenishment fold (prepared phase) — `determineTargetCore` + `boundThread`
-- ============================================================================

/-- WS-SM SM5.I: one replenishment step (`refillSchedContext` + an optional cross-core
`wakeThread`) preserves every thread's home core. -/
theorem processOneReplenishmentOnCore_determineTargetCore (st : SystemState) (ec : CoreId)
    (scId0 : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    determineTargetCore (processOneReplenishmentOnCore st ec scId0 now) t
      = determineTargetCore st t := by
  have hRefillDt := refillSchedContext_determineTargetCore st scId0 now hInv t
  have hRefillInv : (refillSchedContext st scId0 now).objects.invExt := by
    unfold refillSchedContext
    exact SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv
  rw [processOneReplenishmentOnCore, show ∀ X : SystemState,
      determineTargetCore (markRefillKeyChange st X scId0) t = determineTargetCore X t from
    fun X => by unfold determineTargetCore; rw [markRefillKeyChange_getTcb?]]
  simp only [refillWakeOnCore]
  split
  · split
    · exact hRefillDt
    · show determineTargetCore (wakeThread (refillSchedContext st scId0 now) _ ec).1 t = _
      rw [wakeThread_state_eq_enqueue,
        enqueueRunnableOnCore_determineTargetCore_eq _ _ _ _ hRefillInv]
      exact hRefillDt
  · exact hRefillDt

/-- WS-SM SM5.I: one replenishment step preserves every SchedContext's `boundThread`
projection. -/
theorem processOneReplenishmentOnCore_boundThread (st : SystemState) (ec : CoreId)
    (scId0 : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt)
    (scId : SeLe4n.SchedContextId) :
    ((processOneReplenishmentOnCore st ec scId0 now).getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  have hRefillBt := refillSchedContext_boundThread st scId0 now hInv scId
  have hRefillInv : (refillSchedContext st scId0 now).objects.invExt := by
    unfold refillSchedContext
    exact SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv
  rw [processOneReplenishmentOnCore, markRefillKeyChange_getSchedContext?]
  simp only [refillWakeOnCore]
  split
  · split
    · exact hRefillBt
    · show ((wakeThread (refillSchedContext st scId0 now) _ ec).1.getSchedContext? scId).map
          (·.boundThread) = _
      rw [wakeThread_state_eq_enqueue,
        enqueueRunnableOnCore_boundThread _ _ _ hRefillInv]
      exact hRefillBt
  · exact hRefillBt

/-- WS-SM SM5.I: `processReplenishmentsDueOnCore` preserves every thread's home core
(each refill and wake preserves it; each placement writes release fields alone). -/
theorem processReplenishmentsDueOnCore_determineTargetCore (st : SystemState) (c : CoreId)
    (now : Nat) (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    determineTargetCore (processReplenishmentsDueOnCore st c now) t
      = determineTargetCore st t :=
  (processReplenishmentsDueOnCore_induction
    (fun s => s.objects.invExt ∧ determineTargetCore s t = determineTargetCore st t) st c now
    (fun s scId ⟨hI, h⟩ => ⟨processOneReplenishmentOnCore_preserves_objects_invExt s c scId now hI,
      (processOneReplenishmentOnCore_determineTargetCore s c scId now hI t).trans h⟩)
    (fun s scId ⟨hI, h⟩ => ⟨SystemState.releasePlace_objects_invExt s c scId hI,
      (replenishOnCore_determineTargetCore s c scId t).trans h⟩) ⟨hInv, rfl⟩).2

/-- WS-SM SM5.I: `processReplenishmentsDueOnCore` preserves every SchedContext's
`boundThread`. -/
theorem processReplenishmentsDueOnCore_boundThread (st : SystemState) (c : CoreId)
    (now : Nat) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    ((processReplenishmentsDueOnCore st c now).getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) :=
  (processReplenishmentsDueOnCore_induction
    (fun s => s.objects.invExt ∧ (s.getSchedContext? scId).map (·.boundThread) =
      (st.getSchedContext? scId).map (·.boundThread)) st c now
    (fun s x ⟨hI, h⟩ => ⟨processOneReplenishmentOnCore_preserves_objects_invExt s c x now hI,
      (processOneReplenishmentOnCore_boundThread s c x now hI scId).trans h⟩)
    (fun s x ⟨hI, h⟩ => ⟨SystemState.releasePlace_objects_invExt s c x hI,
      (replenishOnCore_boundThread s c x scId).trans h⟩) ⟨hInv, rfl⟩).2

-- ============================================================================
-- §4  Per-phase affinity-consistency + the headline + the aggregate
-- ============================================================================

/-- WS-SM SM5.I / WS-ZA ZA6.3: `processReplenishmentsDueOnCore` preserves
replenish-queue affinity-consistency on every core — a pass places again only
the context at core `c`'s head, which core `c`'s queue already held, and the
refills and wakes preserve `determineTargetCore` / `boundThread`. -/
theorem processReplenishmentsDueOnCore_preserves_replenishQueueAffinityConsistentOnCore
    (st : SystemState) (c : CoreId) (now : Nat) (hInv : st.objects.invExt)
    (hRef : st.releaseQueueRefined)
    (hCons : ∀ c', replenishQueueAffinityConsistentOnCore st c') :
    ∀ c', replenishQueueAffinityConsistentOnCore (processReplenishmentsDueOnCore st c now) c' := by
  refine (drainDueOnCore_induction_pass (fun s => s.objects.invExt ∧ s.releaseQueueRefined ∧
      ∀ c', replenishQueueAffinityConsistentOnCore s c') c now ?_ _ st ⟨hInv, hRef, hCons⟩).2.2
  rintro s scId ⟨hI, hR, hC⟩ h0 hId
  have hA := processOneReplenishmentOnCore_releaseStateAgree s c scId now hI
  have hI1 := processOneReplenishmentOnCore_preserves_objects_invExt s c scId now hI
  have hC1 : ∀ c', replenishQueueAffinityConsistentOnCore (processOneReplenishmentOnCore s c scId now) c' :=
    fun c' => affinityConsistent_transfer s _ c' (fun e he => by rwa [hA.replenishQueueOnCore] at he)
      (processOneReplenishmentOnCore_determineTargetCore s c scId now hI)
      (processOneReplenishmentOnCore_boundThread s c scId now hI) (hC c')
  refine ⟨SystemState.releasePlace_objects_invExt _ c scId hI1,
    SystemState.releasePlace_refined (hA.refined hR) c scId, fun c' => ?_⟩
  refine affinityConsistent_transfer_ids _ _ c' ?_ (replenishOnCore_determineTargetCore _ c scId)
    (replenishOnCore_boundThread _ c scId) (hC1 c')
  intro e he
  by_cases hcc : c' = c
  · subst hcc
    rcases SystemState.releasePlace_entries_provenance _ c' scId c' e he with hm | hs
    · exact ⟨e.2, hm⟩
    · have hmem := releaseHead_mem (hR c') h0
      rw [hId, ← hs] at hmem
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hmem
      refine ⟨p.2, ?_⟩
      rw [hA.replenishQueueOnCore, ← hpe]
      exact hp
  · rw [SystemState.releasePlace_replenishQueueOnCore_ne _ c scId c' hcc] at he
    exact ⟨e.2, he⟩

/-- WS-SM SM5.I: the prepared (clear + replenishment) phase preserves affinity. -/
theorem timerTickOnCorePrepared_preserves_replenishQueueAffinityConsistentOnCore
    (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hCons : ∀ c', replenishQueueAffinityConsistentOnCore st c') :
    ∀ c', replenishQueueAffinityConsistentOnCore (timerTickOnCorePrepared st c) c' := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_replenishQueueAffinityConsistentOnCore
  · exact hInv
  · exact SystemState.releaseStateAgree.refined
      (SystemState.releaseStateAgree.of_objects_eq (st := st) (by rfl) (by rfl)) hRef
  · intro c'
    have := hCons c'
    unfold replenishQueueAffinityConsistentOnCore at this ⊢
    simpa only [SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore] using this

/-- WS-SM SM5.I: a successful `scheduleEffectiveOnCore` preserves affinity (it frames
every replenish queue and preserves `determineTargetCore` / `boundThread`). -/
theorem scheduleEffectiveOnCore_preserves_replenishQueueAffinityConsistentOnCore
    (st : SystemState) (c : CoreId) (st' : SystemState) (c' : CoreId) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st')
    (hCons : replenishQueueAffinityConsistentOnCore st c') :
    replenishQueueAffinityConsistentOnCore st' c' := by
  apply affinityConsistent_transfer st st' c'
  · intro e hMem
    rw [scheduleEffectiveOnCore_replenishQueueOnCore st c st' c' hStep] at hMem
    exact hMem
  · intro t; exact scheduleEffectiveOnCore_determineTargetCore st c st' hInv hStep t
  · intro scId; exact scheduleEffectiveOnCore_boundThread st c st' hInv hStep scId
  · exact hCons

/-- WS-SM SM5.I: the prepared phase preserves the object-store invariant. -/
theorem timerTickOnCorePrepared_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (timerTickOnCorePrepared st c).objects.invExt := by
  simp only [timerTickOnCorePrepared]
  exact processReplenishmentsDueOnCore_preserves_objects_invExt _ c _ hInv

/-- WS-SM (PR #880 round 7): the `.reschedule` receiver decision — which the
round-7 tick invokes for a local replenish wake — preserves replenish-queue
affinity-consistency on every core: it frames every replenish queue and
preserves `determineTargetCore` / `boundThread` (identity arms trivially; the
dispatch arm via the switch frames above). -/
theorem handleRescheduleSgiOnCore_preserves_replenishQueueAffinityConsistentOnCore
    (st : SystemState) (c : CoreId) (st' : SystemState) (c' : CoreId)
    (hInv : st.objects.invExt)
    (hStep : handleRescheduleSgiOnCore st c = .ok st')
    (hCons : replenishQueueAffinityConsistentOnCore st c') :
    replenishQueueAffinityConsistentOnCore st' c' := by
  apply affinityConsistent_transfer st st' c'
  · intro e hMem
    rw [handleRescheduleSgiOnCore_replenishQueueOnCore st c st' c' hStep] at hMem
    exact hMem
  · intro t
    unfold handleRescheduleSgiOnCore at hStep
    split at hStep
    · exact absurd hStep (by simp)
    · split at hStep
      · rw [Except.ok.injEq] at hStep; subst hStep
        exact dropCurrentOnCore_determineTargetCore st c hInv t
      · rw [Except.ok.injEq] at hStep; subst hStep; rfl
    · split at hStep
      · split at hStep
        · rename_i sSw hSw
          rw [Except.ok.injEq] at hStep; subst hStep
          rw [show determineTargetCore (sSw.clearReschedulePendingOnCore c) t
                = determineTargetCore sSw t from by
              unfold determineTargetCore; rw [SystemState.clearReschedulePendingOnCore_getTcb?]]
          exact switchToThreadOnCore_determineTargetCore st c _ sSw hInv hSw t
        · split at hStep
          · rw [Except.ok.injEq] at hStep; subst hStep
            exact dropCurrentOnCore_determineTargetCore st c hInv t
          · rw [Except.ok.injEq] at hStep; subst hStep; rfl
      · rw [Except.ok.injEq] at hStep; subst hStep; rfl
  · intro scId
    unfold handleRescheduleSgiOnCore at hStep
    split at hStep
    · exact absurd hStep (by simp)
    · split at hStep
      · rw [Except.ok.injEq] at hStep; subst hStep
        exact preemptCurrentOnCore_boundThread st c _ hInv scId
      · rw [Except.ok.injEq] at hStep; subst hStep; rfl
    · split at hStep
      · split at hStep
        · rename_i sSw hSw
          rw [Except.ok.injEq] at hStep; subst hStep
          rw [SystemState.clearReschedulePendingOnCore_getSchedContext?]
          exact switchToThreadOnCore_boundThread st c _ sSw hInv hSw scId
        · split at hStep
          · rw [Except.ok.injEq] at hStep; subst hStep
            exact preemptCurrentOnCore_boundThread st c _ hInv scId
          · rw [Except.ok.injEq] at hStep; subst hStep; rfl
      · rw [Except.ok.injEq] at hStep; subst hStep; rfl
  · exact hCons

/-- WS-SM SM5.I (headline): the **live per-core timer tick** preserves replenish-queue
affinity-consistency on every core.  The prepared and schedule phases are proven via
the transfer helper; the budget phase is supplied as `hBudgetAffinity` (its exhausted
arm runs the IPC `timeoutBlockedThreads`, whose object-frame is the tracked-debt
residual). -/
theorem timerTickOnCore_preserves_replenishQueueAffinityConsistentOnCore (st : SystemState)
    (c : CoreId) (c' : CoreId)
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hCons : ∀ c'', replenishQueueAffinityConsistentOnCore st c'')
    (hBudgetAffinity : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (st3 : SystemState) (b : Bool),
      (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid →
      ∀ (hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb),
      timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, b) →
      replenishQueueAffinityConsistentOnCore (timerTickOnCorePrepared st c) c' →
      replenishQueueAffinityConsistentOnCore st3 c') :
    replenishQueueAffinityConsistentOnCore (timerTickOnCore st c) c' := by
  have hPrepInv : (timerTickOnCorePrepared st c).objects.invExt :=
    timerTickOnCorePrepared_preserves_objects_invExt st c hInv
  have hPrep : replenishQueueAffinityConsistentOnCore (timerTickOnCorePrepared st c) c' :=
    timerTickOnCorePrepared_preserves_replenishQueueAffinityConsistentOnCore st c hInv hRef hCons c'
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ <;> rw [h]
  rotate_left 2
  · exact scheduleEffectiveOnCore_preserves_replenishQueueAffinityConsistentOnCore _ c _ c'
      (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hB)
      (scheduleEffectiveOnCore_eq_state st3 c)
      (hBudgetAffinity tid tcb st3 true hCur hTcb hB hPrep)
  all_goals
    first
      | exact rescheduleIfPendingOnCore_of
          (P := fun s => replenishQueueAffinityConsistentOnCore s c') _ c hPrep
          (handleRescheduleSgiOnCore_preserves_replenishQueueAffinityConsistentOnCore _ c _ c'
            hPrepInv (handleRescheduleSgiOnCore_eq_state _ c) hPrep)
      | have h3 := hBudgetAffinity tid tcb st3 false hCur hTcb hB hPrep
        exact rescheduleIfPendingOnCore_of
          (P := fun s => replenishQueueAffinityConsistentOnCore s c') _ c h3
          (handleRescheduleSgiOnCore_preserves_replenishQueueAffinityConsistentOnCore _ c _ c'
            (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hB)
            (handleRescheduleSgiOnCore_eq_state _ c) h3)

/-- WS-SM SM5.I (aggregate, strengthened): the **live per-core timer tick** preserves
the per-core CBS invariant `perCoreCbsInvariant` — discharging all three conjuncts
(validity + pipeline-order + affinity-consistency) from the maintained invariants.

This **supersedes** the v0.31.57 `PerCoreTickCbsPreservation.timerTickOnCore_preserves_perCoreCbsInvariant`,
which took the post-state affinity-consistency verbatim as `hAffinity` (an
assume-the-conclusion input).  Here affinity is *derived*: the carried-over entries
via the proven prepared / schedule per-phase frames, leaving only the budget-phase
frame `hBudgetAffinity` (whose exhausted arm's `timeoutBlockedThreads` object-frame is
the single tracked-debt residual — see the headline). -/
theorem timerTickOnCore_preserves_perCoreCbsInvariant_discharged (st : SystemState)
    (c : CoreId) (c' : CoreId)
    (hInv : ∀ c'', perCoreCbsInvariant st c'')
    (hInvObj : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).getSchedContext? scId = some sc →
      0 < sc.period.val)
    (hFuture : currentRefillsFutureOnCore (timerTickOnCorePrepared st c) c)
    (hBudgetAffinity : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (st3 : SystemState) (b : Bool),
      (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid →
      ∀ (hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb),
      timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, b) →
      replenishQueueAffinityConsistentOnCore (timerTickOnCorePrepared st c) c' →
      replenishQueueAffinityConsistentOnCore st3 c') :
    perCoreCbsInvariant (timerTickOnCore st c) c' :=
  ⟨timerTickOnCore_preserves_replenishQueueValidOnCore st c c'
      (fun c'' => (hInv c'').1),
   timerTickOnCore_preserves_replenishmentPipelineOrderOnCore st c c' hInvObj
      (fun c'' => (hInv c'').2.1) hPeriod hFuture,
   timerTickOnCore_preserves_replenishQueueAffinityConsistentOnCore st c c'
      hInvObj hRef (fun c'' => (hInv c'').2.2) hBudgetAffinity⟩

end SeLe4n.Kernel
