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
is homed on `c`) plus the binding pair (`schedContextBindingBidirectional`).

The result (`timerTickOnCore_preserves_perCoreCbsInvariant_discharged`) takes
`currentBoundHomedOnCore` on the prepared state — which the placement invariant and
the binding pair give (`timerTickOnCorePrepared_currentBoundHomedOnCore`, in
`ReschedulePendingArms.Tick`, where the binding pair's drain frame lives) — plus the
object-store well-formedness invariant `invExt`, all maintained by the per-core
scheduler, and proves all three conjuncts, with no assume-the-conclusion
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
* **Budget-phase frames** (§3b): every write of the budget tick keeps every
  thread's home and every context's bound thread (`homeBindFrame`) — the timeout
  pass's abort through `abortPendingIpcOnEndpoint_tcb_lookup` /
  `_binding_backward` and the SchedContext backward / forward frames under
  `invExt` alone — and the exhausting arm's one new entry, its context re-placed on
  the tick core, is homed there when the charged thread is
  (`currentBoundHomedOnCore`: homed on the tick core, the bound thread of its
  context).
* **Per-phase + headline** (§4): the **prepared**, **budget** and **schedule**
  phases preserve affinity-consistency; the headline
  `timerTickOnCore_preserves_replenishQueueAffinityConsistentOnCore` composes the
  three phases.
* **Aggregate** (§4): the strengthened `timerTickOnCore_preserves_perCoreCbsInvariant_discharged`
  discharges all three CBS conjuncts — replacing the v0.31.57 whole-state
  assume-the-conclusion `hAffinity` with `currentBoundHomedOnCore` on the prepared
  state, which the placement invariant (`currentDequeuedUnique`'s `currentHome`) and
  the binding pair give (`timerTickOnCorePrepared_currentBoundHomedOnCore`), plus
  `invExt`.

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
-- §3b  The budget phase's frames: homes and bound threads
-- ============================================================================

/-- A step that keeps every thread's home core and every context's bound thread:
the two readings replenish-queue affinity-consistency takes of the store. -/
def homeBindFrame (st st' : SystemState) : Prop :=
  (∀ t, determineTargetCore st' t = determineTargetCore st t) ∧
    ∀ s, (st'.getSchedContext? s).map (·.boundThread) = (st.getSchedContext? s).map (·.boundThread)

theorem homeBindFrame.refl (st : SystemState) : homeBindFrame st st :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem homeBindFrame.trans {a b d : SystemState} (h₁ : homeBindFrame a b)
    (h₂ : homeBindFrame b d) : homeBindFrame a d :=
  ⟨fun t => (h₂.1 t).trans (h₁.1 t), fun s => (h₂.2 s).trans (h₁.2 s)⟩

/-- The run-queue links are neither a home nor a bound thread. -/
theorem homeBindFrame.of_agreeOffRunLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffRunLinks st) : homeBindFrame st st' :=
  ⟨fun t => determineTargetCore_of_objectsAgreeOffRunLinks h t,
   fun s => by rw [h.getSchedContext? s]⟩

theorem homeBindFrame.of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    homeBindFrame st st' :=
  .of_agreeOffRunLinks (SystemState.objectsAgreeOffRunLinks.of_objects_eq h)

/-- Affinity-consistency carries across a step keeping the core's queue, every
home and every bound thread. -/
theorem homeBindFrame.affinityConsistent {st st' : SystemState} {c : CoreId}
    (h : homeBindFrame st st')
    (hQ : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (hCons : replenishQueueAffinityConsistentOnCore st c) :
    replenishQueueAffinityConsistentOnCore st' c :=
  affinityConsistent_transfer st st' c (fun e he => by rw [← hQ]; exact he) h.1 h.2 hCons

/-- A TCB rewritten in place, its affinity kept. -/
theorem homeBindFrame.rewriteObject_tcb {st : SystemState} {t : SeLe4n.ThreadId} {x x' : TCB}
    (hx : st.getTcb? t = some x) (hA : st.rewriteAdmissible t.toObjId (.tcb x'))
    (hInv : st.objects.invExt) (hAff : x'.cpuAffinity = x.cpuAffinity) :
    homeBindFrame st (st.rewriteObject t.toObjId (.tcb x') hA) := by
  refine ⟨fun y => determineTargetCore_congr _ _ y ?_,
    fun s => by rw [SystemState.rewriteObject_tcb_getSchedContext? _ _ _ _ hInv]⟩
  by_cases hy : t = y
  · subst hy
    rw [SystemState.rewriteObject_tcb_getTcb?_self _ _ _ _ hInv, hx]
    simp only [Option.map_some, hAff]
  · rw [SystemState.rewriteObject_getTcb?_ne _ _ _ _ hInv y
      (fun h => hy (SeLe4n.ThreadId.toObjId_injective _ _ h))]

/-- A SchedContext rewritten in place, its bound thread kept. -/
theorem homeBindFrame.rewriteObject_schedContext {st : SystemState} {s : SchedContextId}
    {sc sc' : SchedContext} (hs : st.getSchedContext? s = some sc)
    (hA : st.rewriteAdmissible s.toObjId (.schedContext sc')) (hInv : st.objects.invExt)
    (hB : sc'.boundThread = sc.boundThread) :
    homeBindFrame st (st.rewriteObject s.toObjId (.schedContext sc') hA) := by
  refine ⟨fun y => by
    unfold determineTargetCore; rw [SystemState.rewriteObject_schedContext_getTcb? _ _ _ _ hInv],
    fun s' => ?_⟩
  by_cases h : s.toObjId = s'.toObjId
  · cases SeLe4n.SchedContextId.toObjId_injective _ _ h
    rw [SystemState.rewriteObject_schedContext_getSchedContext?_self _ _ _ _ hInv, hs]
    simp only [Option.map_some, hB]
  · rw [SystemState.rewriteObject_getSchedContext?_ne _ _ _ _ hInv _ h]

/-- A run-queue placement. -/
theorem enqueueRunnableOnCore_homeBindFrame (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    homeBindFrame st (enqueueRunnableOnCore st c t) :=
  ⟨fun x => enqueueRunnableOnCore_determineTargetCore_eq st c t x hInv,
   fun s => enqueueRunnableOnCore_boundThread st c t hInv s⟩

/-- A priority-inheritance boost write. -/
theorem updatePipBoostOnCore_homeBindFrame (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    homeBindFrame st (PriorityInheritance.updatePipBoostOnCore st c t) :=
  ⟨fun x => PriorityInheritance.updatePipBoostOnCore_determineTargetCore st c t x hInv,
   fun s => by rw [PriorityInheritance.updatePipBoostOnCore_getSchedContext? st c t hInv]⟩

/-- The priority-inheritance revert: one boost write per chain link. -/
theorem revertPriorityInheritance_homeBindFrame (st : SystemState) (t : SeLe4n.ThreadId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    homeBindFrame st (PriorityInheritance.revertPriorityInheritance st t fuel) := by
  induction fuel generalizing st t with
  | zero => exact .refl _
  | succ n ih =>
    unfold PriorityInheritance.revertPriorityInheritance
    have hB := updatePipBoostOnCore_homeBindFrame st bootCoreId t hInv
    split
    · exact hB.trans (ih _ _
        (PriorityInheritance.updatePipBoostOnCore_preserves_objects_invExt st bootCoreId t hInv))
    · exact hB

/-- The timeout's abort: its endpoint splice and the timed-out TCB keep every
thread's placement, and it writes no SchedContext. -/
theorem abortPendingIpcOnEndpoint_homeBindFrame {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') : homeBindFrame st st' := by
  refine ⟨fun t => determineTargetCore_congr st st' t ?_, fun s => ?_⟩
  · cases hPost : st'.getTcb? t with
    | some t' =>
      obtain ⟨t0, h0, -⟩ := abortPendingIpcOnEndpoint_binding_backward epId isReceiveQ tid st st'
        hInv h _ t' ((SystemState.getTcb?_eq_some_iff _ _ _).mp hPost)
      obtain ⟨t'', h'', hP⟩ := abortPendingIpcOnEndpoint_tcb_lookup epId isReceiveQ tid st st'
        hInv h _ t0 h0
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hPost] at h''
      cases KernelObject.tcb.inj (Option.some.inj h'')
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h0]
      simp only [Option.map_some, Option.some.injEq]
      exact congrArg TcbPlacement.cpuAffinity hP
    | none =>
      cases hPre : st.getTcb? t with
      | none => rfl
      | some t0 =>
        obtain ⟨t'', h'', -⟩ := abortPendingIpcOnEndpoint_tcb_lookup epId isReceiveQ tid st st'
          hInv h _ t0 ((SystemState.getTcb?_eq_some_iff _ _ _).mp hPre)
        rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h''] at hPost
        cases hPost
  · cases hPost : st'.getSchedContext? s with
    | some sc =>
      rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
        (abortPendingIpcOnEndpoint_schedContext_backward epId isReceiveQ tid st st' hInv h _ sc
          ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hPost))]
    | none =>
      cases hPre : st.getSchedContext? s with
      | none => rfl
      | some sc =>
        rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
          (abortPendingIpcOnEndpoint_schedContext_forward epId isReceiveQ tid st st' hInv h _ sc
            ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hPre))] at hPost
        cases hPost

/-- The timeout of one IPC-blocked thread: the abort, the wake on its home core,
the reply-waiter unlink and the revert. -/
theorem timeoutThread_homeBindFrame {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {ec : CoreId} {st : SystemState}
    {r : SystemState × Option (CoreId × SgiKind)} (hInv : st.objects.invExt)
    (h : timeoutThread epId isReceiveQ tid ec st = .ok r) : homeBindFrame st r.1 := by
  unfold timeoutThread at h
  split at h
  · cases h
  · rename_i st2 hA
    have hInv2 := abortPendingIpcOnEndpoint_preserves_objects_invExt _ _ _ _ _ hInv hA
    have hW : homeBindFrame st (wakeThread st2 tid ec).1 :=
      (abortPendingIpcOnEndpoint_homeBindFrame hInv hA).trans
        (enqueueRunnableOnCore_homeBindFrame st2 _ tid hInv2)
    have hInvW : (wakeThread st2 tid ec).1.objects.invExt :=
      enqueueRunnableOnCore_preserves_objects_invExt st2 _ tid hInv2
    dsimp only at h
    split at h
    · rw [Except.ok.injEq] at h; subst h
      exact hW.trans ((homeBindFrame.of_agreeOffRunLinks
        (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks _ _ _)).trans
        (revertPriorityInheritance_homeBindFrame _ _ _
          (SystemState.unlinkReplyWaiter_objects_invExt _ _ _ hInvW)))
    · rw [Except.ok.injEq] at h; subst h; exact hW

/-- The exhausted context's timeout pass: its bound thread is timed out when it
is blocked in IPC, and nothing is written otherwise. -/
theorem timeoutBlockedThreads_homeBindFrame (st : SystemState) (scId : SchedContextId)
    (ec : CoreId) (hInv : st.objects.invExt) :
    homeBindFrame st (timeoutBlockedThreads st scId ec).1 := by
  unfold timeoutBlockedThreads timeoutBlockedThreadStep
  split
  · split
    · dsimp only
      split
      · split
        · split
          · rename_i hT
            exact timeoutThread_homeBindFrame hInv hT
          · exact .refl _
        · exact .refl _
      · exact .refl _
    · exact .refl _
  · exact .refl _

/-- The context an exhausting charge writes back names the thread it named. -/
theorem spentSchedContext_boundThread (sc : SchedContext) (now : Nat) :
    (spentSchedContext sc now).boundThread = sc.boundThread := by
  have h : (scheduleReplenishment (consumeBudget sc 1) now ⟨sc.budgetRemaining.val⟩).boundThreadCode =
      sc.boundThreadCode := by
    unfold scheduleReplenishment
    rw [SchedContext.withReplenishments_boundThreadCode]; rfl
  show SeLe4n.ThreadId.ofOptCode (cbsUpdateDeadline _ now true).boundThreadCode = _
  unfold cbsUpdateDeadline; split <;> exact congrArg SeLe4n.ThreadId.ofOptCode h

/-- **An exhausting charge keeps every core's queue affinity-consistent** when
the context it re-places on core `c` names only threads homed on `c`: the
re-placement's entry is the one new entry, and the enqueue, the key hook, the
timeout pass and the diagnostic write keep every home, every bound thread and
every release queue. -/
theorem budgetExhaustOnCore_preserves_replenishQueueAffinityConsistentOnCore
    (st : SystemState) (c c' : CoreId) (tid : SeLe4n.ThreadId)
    (preKey : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId)
    (scId : SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (hInv : st.objects.invExt)
    (hHome : ∀ t, sc.boundThread = some t → determineTargetCore st t = c)
    (hCons : replenishQueueAffinityConsistentOnCore st c') :
    replenishQueueAffinityConsistentOnCore
      (budgetExhaustOnCore st c tid preKey scId sc hSc 1) c' := by
  have hF1 := homeBindFrame.rewriteObject_schedContext hSc
    (SystemState.rewriteAdmissible_schedContext hSc (spentSchedContext sc st.machine.timer)) hInv
    (spentSchedContext_boundThread sc st.machine.timer)
  have hInvRw := SystemState.rewriteObject_preserves_objects_invExt _ _ _
    (SystemState.rewriteAdmissible_schedContext hSc (spentSchedContext sc st.machine.timer)) hInv
  have hConsR := (show replenishQueueAffinityConsistentOnCore (replenishOnCore (st.rewriteObject
      scId.toObjId (.schedContext (spentSchedContext sc st.machine.timer))
      (SystemState.rewriteAdmissible_schedContext hSc _)) c scId) c' from by
    by_cases hcc : c = c'
    · subst hcc
      refine replenishOnCore_preserves_replenishQueueAffinityConsistentOnCore _ c scId
        (hF1.affinityConsistent rfl hCons) ?_
      intro sc1 hSc1 t ht
      rw [SystemState.rewriteObject_schedContext_getSchedContext?_self _ _ _ _ hInv] at hSc1
      cases hSc1
      rw [hF1.1 t]
      exact hHome t ((spentSchedContext_boundThread sc _) ▸ ht)
    · exact replenishOnCore_preserves_replenishQueueAffinityConsistentOnCore_ne _ c c' scId hcc
        (hF1.affinityConsistent rfl hCons))
  have hInvR := SystemState.releasePlace_objects_invExt _ c scId hInvRw
  have hTail : ∀ (s : SystemState) (p : SeLe4n.Priority), s.objects.invExt →
      let T := timeoutBlockedThreads (markKeyChangeFor (s.runEnqueueOnCore c tid p) tid preKey) scId c
      homeBindFrame s { T.1 with
        scheduler := (markRescheduleTargets (T.1.scheduler.setLastTimeoutErrorsOnCore c T.2.1) T.2.2) } := by
    intro s p hs T
    refine (homeBindFrame.of_agreeOffRunLinks
      (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks s c tid p)).trans ?_
    refine (homeBindFrame.of_objects_eq (markKeyChangeFor_objects _ tid preKey)).trans ?_
    refine (timeoutBlockedThreads_homeBindFrame _ scId c ?_).trans (homeBindFrame.of_objects_eq rfl)
    rw [markKeyChangeFor_objects]
    exact SystemState.runEnqueueOnCore_objects_invExt _ _ _ _ hs
  unfold budgetExhaustOnCore spendBudgetOnCore
  exact (hTail _ _ hInvR).affinityConsistent (by
    simp only [markRescheduleTargets_replenishQueueOnCore,
      SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore,
      timeoutBlockedThreads_replenishQueueOnCore, markKeyChangeFor_replenishQueueOnCore,
      SystemState.runEnqueueOnCore_replenishQueueOnCore]) hConsR

/-- **The budget tick keeps every core's queue affinity-consistent** when the
charged thread is homed on the tick core and is the bound thread of the context
its binding names: the unbound arms and the bound arm that does not exhaust
write no release queue, and the exhausting arm re-places that context on the
tick core (`budgetExhaustOnCore_preserves_replenishQueueAffinityConsistentOnCore`). -/
theorem timerTickBudgetOnCore_preserves_replenishQueueAffinityConsistentOnCore
    (st : SystemState) (c c' : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (st3 : SystemState) (b : Bool)
    (hInv : st.objects.invExt) (hHome : determineTargetCore st tid = c)
    (hBound : ∀ scId sc, tcb.schedContextBinding.scId? = some scId →
      st.getSchedContext? scId = some sc → sc.boundThread = some tid)
    (hStep : timerTickBudgetOnCore st c tid tcb hTcb = (st3, b))
    (hCons : replenishQueueAffinityConsistentOnCore st c') :
    replenishQueueAffinityConsistentOnCore st3 c' := by
  have hEx : ∀ scId sc (hSc : st.getSchedContext? scId = some sc)
      (preKey : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId),
      tcb.schedContextBinding.scId? = some scId →
      replenishQueueAffinityConsistentOnCore (budgetExhaustOnCore st c tid preKey scId sc hSc 1) c' :=
    fun scId sc hSc preKey hb =>
      budgetExhaustOnCore_preserves_replenishQueueAffinityConsistentOnCore st c c' tid preKey
        scId sc hSc hInv (fun t ht => by
          rw [hBound scId sc hb hSc] at ht; cases ht; exact hHome) hCons
  have hSpend : ∀ scId sc (hSc : st.getSchedContext? scId = some sc),
      replenishQueueAffinityConsistentOnCore (st.rewriteObject scId.toObjId
        (.schedContext (consumeBudget sc 1)) (SystemState.rewriteAdmissible_schedContext hSc _)) c' :=
    fun scId sc hSc => (homeBindFrame.rewriteObject_schedContext (sc' := consumeBudget sc 1) hSc _
      hInv rfl).affinityConsistent rfl hCons
  match hB : tcb.schedContextBinding with
  | .unbound =>
      by_cases hS : tcb.timeSlice ≤ 1
      · simp only [timerTickBudgetOnCore, hB, if_pos hS, Prod.mk.injEq] at hStep
        obtain ⟨rfl, -⟩ := hStep
        exact ((homeBindFrame.rewriteObject_tcb hTcb
          (SystemState.rewriteAdmissible_tcb hTcb
            { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }) hInv rfl).trans
          (.of_agreeOffRunLinks (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ c tid
            tcb.boostedPriority))).affinityConsistent
          (SystemState.runEnqueueOnCore_replenishQueueOnCore _ _ _ _ _) hCons
      · simp only [timerTickBudgetOnCore, hB, if_neg hS, Prod.mk.injEq] at hStep
        obtain ⟨rfl, -⟩ := hStep
        exact (homeBindFrame.rewriteObject_tcb hTcb
          (SystemState.rewriteAdmissible_tcb hTcb { tcb with timeSlice := tcb.timeSlice - 1 })
          hInv rfl).affinityConsistent rfl hCons
  | .bound scId | .donated scId _ =>
      match hSc : st.getSchedContext? scId with
      | some sc =>
          by_cases hBud : sc.budgetRemaining.val ≤ 1
          · simp only [timerTickBudgetOnCore, hB, SystemState.getSchedContextWitnessed?_eq_some hSc,
              if_pos hBud, Prod.mk.injEq] at hStep
            obtain ⟨rfl, -⟩ := hStep
            exact hEx scId sc _ _ (by rw [hB]; rfl)
          · simp only [timerTickBudgetOnCore, hB, SystemState.getSchedContextWitnessed?_eq_some hSc,
              if_neg hBud, Prod.mk.injEq] at hStep
            obtain ⟨rfl, -⟩ := hStep
            exact hSpend scId sc hSc
      | none =>
          simp only [timerTickBudgetOnCore, hB, SystemState.getSchedContextWitnessed?_eq_none hSc,
            Prod.mk.injEq] at hStep
          obtain ⟨rfl, -⟩ := hStep
          exact hCons

/-- **The thread current on `c` is homed on `c` and named by its context**: the
placement invariant's `currentHome` and the binding pair
(`schedContextBindingBidirectional`) read at core `c`'s current thread — what the
exhausting tick's release entry on `c` needs (derived from the two invariants on
the tick's prepared state by `timerTickOnCorePrepared_currentBoundHomedOnCore`). -/
def currentBoundHomedOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid tcb, st.scheduler.currentOnCore c = some tid → st.getTcb? tid = some tcb →
    determineTargetCore st tid = c ∧
      ∀ scId sc, tcb.schedContextBinding.scId? = some scId → st.getSchedContext? scId = some sc →
        sc.boundThread = some tid



/-- The context an exhausting charge writes back keeps its release link core. -/
theorem spentSchedContext_releaseCoreCode (sc : SchedContext) (now : Nat) :
    (spentSchedContext sc now).releaseCoreCode = sc.releaseCoreCode := by
  have h : (scheduleReplenishment (consumeBudget sc 1) now ⟨sc.budgetRemaining.val⟩).releaseCoreCode =
      sc.releaseCoreCode := by
    unfold scheduleReplenishment
    rw [SchedContext.withReplenishments_releaseCoreCode]; rfl
  show (cbsUpdateDeadline _ now true).releaseCoreCode = _
  unfold cbsUpdateDeadline; split <;> exact h

/-- **A context is linked on its bound thread's home core or on none** (WS-ZA
ZA6.3): a context linked on a core's release queue holds an entry there
(`releaseQueueRefined`), so under affinity-consistency its bound thread is homed
on that core.  The requeue's `releaseFreeFor` guard holds for a context whose
bound thread is homed on the requeuing core. -/
theorem releaseFreeFor_of_boundHome {st : SystemState} {c : CoreId} {s : SchedContextId}
    {sc : SchedContext} {t : SeLe4n.ThreadId} (hRef : st.releaseQueueRefined)
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore st d)
    (hSc : st.getSchedContext? s = some sc) (hB : sc.boundThread = some t)
    (hH : determineTargetCore st t = c) : st.releaseFreeFor c s = true := by
  rw [SystemState.releaseFreeFor_iff]
  intro d hd
  have hm := (hRef d).mem_of_queued (SystemState.releaseQueuedOn_of_releaseCoreOf hd)
  rw [← hAff d s _ hm sc hSc t hB, hH]

/-- **The exhausting tick's requeue is on the context's own core** (WS-ZA ZA6.3):
the charged thread's context, written back charged, is free on the tick core — it
names the charged thread, homed there (`currentBoundHomedOnCore`), and the write
keeps its link core — so the requeue's branch that leaves both queues as they are
is unreachable. -/
theorem budgetExhaust_requeue_releaseFreeFor {st : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {scId : SchedContextId} {sc : SchedContext}
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore st d)
    (hCur : currentBoundHomedOnCore st c) (hc : st.scheduler.currentOnCore c = some tid)
    (hT : st.getTcb? tid = some tcb) (hb : tcb.schedContextBinding.scId? = some scId)
    (hSc : st.getSchedContext? scId = some sc) :
    (st.rewriteObject scId.toObjId (.schedContext (spentSchedContext sc st.machine.timer))
      (SystemState.rewriteAdmissible_schedContext hSc _)).releaseFreeFor c scId = true := by
  have h := releaseFreeFor_of_boundHome hRef hAff hSc ((hCur tid tcb hc hT).2 scId sc hb hSc)
    (hCur tid tcb hc hT).1
  unfold SystemState.releaseFreeFor at h ⊢
  rw [SystemState.releaseCoreOf_rewriteObject_schedContext _ _ _ _ hSc hInv
    (spentSchedContext_releaseCoreCode sc _)]
  exact h

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
the transfer helper; the budget phase by
`timerTickBudgetOnCore_preserves_replenishQueueAffinityConsistentOnCore`, whose one
precondition is the prepared state's `currentBoundHomedOnCore` at the tick core: the
charged thread is homed there and named by its context, so the exhausting arm's
release entry on the tick core is homed on it (WS-ZA ZA6.3). -/
theorem timerTickOnCore_preserves_replenishQueueAffinityConsistentOnCore (st : SystemState)
    (c : CoreId) (c' : CoreId)
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hCons : ∀ c'', replenishQueueAffinityConsistentOnCore st c'')
    (hCurrent : currentBoundHomedOnCore (timerTickOnCorePrepared st c) c) :
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
      (timerTickBudgetOnCore_preserves_replenishQueueAffinityConsistentOnCore _ c c' tid tcb
        hTcb st3 true hPrepInv (hCurrent tid tcb hCur hTcb).1 (hCurrent tid tcb hCur hTcb).2 hB hPrep)
  all_goals
    first
      | exact rescheduleIfPendingOnCore_of
          (P := fun s => replenishQueueAffinityConsistentOnCore s c') _ c hPrep
          (handleRescheduleSgiOnCore_preserves_replenishQueueAffinityConsistentOnCore _ c _ c'
            hPrepInv (handleRescheduleSgiOnCore_eq_state _ c) hPrep)
      | have h3 := timerTickBudgetOnCore_preserves_replenishQueueAffinityConsistentOnCore _ c c'
            tid tcb hTcb st3 false hPrepInv (hCurrent tid tcb hCur hTcb).1
            (hCurrent tid tcb hCur hTcb).2 hB hPrep
        exact rescheduleIfPendingOnCore_of
          (P := fun s => replenishQueueAffinityConsistentOnCore s c') _ c h3
          (handleRescheduleSgiOnCore_preserves_replenishQueueAffinityConsistentOnCore _ c _ c'
            (timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hB)
            (handleRescheduleSgiOnCore_eq_state _ c) h3)

/-- WS-SM SM5.I (aggregate, strengthened): the **live per-core timer tick** preserves
the per-core CBS invariant `perCoreCbsInvariant` — discharging all three conjuncts
(validity + pipeline-order + affinity-consistency) from the maintained invariants.

This replaces the v0.31.57 aggregate, which took the post-state
affinity-consistency verbatim as `hAffinity` (an assume-the-conclusion input) and
was retired in WS-ZA ZA6.3.  Here affinity is *derived*: the carried-over entries
via the proven prepared / schedule per-phase frames, and the budget phase's new
entry from `currentBoundHomedOnCore`, which the placement invariant and the binding
pair give on the prepared state (`timerTickOnCorePrepared_currentBoundHomedOnCore`). -/
theorem timerTickOnCore_preserves_perCoreCbsInvariant_discharged (st : SystemState)
    (c : CoreId) (c' : CoreId)
    (hInv : ∀ c'', perCoreCbsInvariant st c'')
    (hInvObj : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).getSchedContext? scId = some sc →
      0 < sc.period.val)
    (hFuture : currentRefillsFutureOnCore (timerTickOnCorePrepared st c) c)
    (hCurrent : currentBoundHomedOnCore (timerTickOnCorePrepared st c) c) :
    perCoreCbsInvariant (timerTickOnCore st c) c' :=
  ⟨timerTickOnCore_preserves_replenishQueueValidOnCore st c c'
      (fun c'' => (hInv c'').1),
   timerTickOnCore_preserves_replenishmentPipelineOrderOnCore st c c' hInvObj
      (fun c'' => (hInv c'').2.1) hPeriod hFuture,
   timerTickOnCore_preserves_replenishQueueAffinityConsistentOnCore st c c'
      hInvObj hRef (fun c'' => (hInv c'').2.2) hCurrent⟩

end SeLe4n.Kernel
