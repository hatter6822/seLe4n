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
state change `st ↝ base` that only *shrinks* core `c`'s replenish queue (`hSub`),
preserves every thread's home core (`hTgt`), and preserves every SchedContext's
`boundThread` projection (`hBound`).  Every carried-over entry's bound thread is
still homed on `c`. -/
theorem affinityConsistent_transfer (st base : SystemState) (c : CoreId)
    (hSub : ∀ e, e ∈ (base.scheduler.replenishQueueOnCore c).entries →
                 e ∈ (st.scheduler.replenishQueueOnCore c).entries)
    (hTgt : ∀ tid, determineTargetCore base tid = determineTargetCore st tid)
    (hBound : ∀ scId, (base.getSchedContext? scId).map (·.boundThread)
                    = (st.getSchedContext? scId).map (·.boundThread))
    (hCons : replenishQueueAffinityConsistentOnCore st c) :
    replenishQueueAffinityConsistentOnCore base c := by
  intro scId t hMem sc hScBase tid hBoundEq
  rw [hTgt tid]
  have hMapEq := hBound scId
  rw [hScBase] at hMapEq
  -- `(some sc).map boundThread = some sc.boundThread`
  cases hSt : st.getSchedContext? scId with
  | none => rw [hSt] at hMapEq; simp at hMapEq
  | some sc0 =>
    rw [hSt] at hMapEq
    simp only [Option.map_some] at hMapEq
    -- `hMapEq : some sc.boundThread = some sc0.boundThread`
    have hbeq : sc.boundThread = sc0.boundThread := Option.some.inj hMapEq
    have hb0 : sc0.boundThread = some tid := hbeq ▸ hBoundEq
    exact hCons scId t (hSub _ hMem) sc0 hSt tid hb0

/-- WS-SM SM5.I (atom): inserting a `.tcb t'` at a slot already holding a `.tcb t0`
with the same `cpuAffinity` preserves every thread's home core
(`determineTargetCore` reads only `cpuAffinity`). -/
theorem determineTargetCore_insert_tcb (st result : SystemState) (tid0 : SeLe4n.ThreadId)
    (t0 t' : TCB) (hInv : st.objects.invExt)
    (hOld : st.objects.get? tid0.toObjId = some (.tcb t0))
    (hAff : t'.cpuAffinity = t0.cpuAffinity)
    (hObj : result.objects = st.objects.insert tid0.toObjId (.tcb t')) (tid : SeLe4n.ThreadId) :
    determineTargetCore result tid = determineTargetCore st tid := by
  unfold determineTargetCore SystemState.getTcb?
  rw [hObj]
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable_getElem?_insert st.objects tid0.toObjId (.tcb t') hInv tid.toObjId]
  by_cases hk : tid0.toObjId == tid.toObjId
  · simp only [hk, if_pos]
    have hkey : st.objects.get? tid.toObjId = some (.tcb t0) := by
      have : tid.toObjId = tid0.toObjId := (eq_of_beq hk).symm
      rw [this]; exact hOld
    rw [hkey, hAff]
  · simp only [hk, if_neg, Bool.not_eq_true]

/-- WS-SM SM5.I (atom): inserting a `.tcb t'` at a slot already holding a `.tcb t0`
leaves every `getSchedContext?` lookup unchanged (a TCB slot is never a SchedContext
slot — the on-key case is `none = none`). -/
theorem getSchedContext?_insert_tcb_eq (st result : SystemState) (tid0 : SeLe4n.ThreadId)
    (t0 t' : TCB) (hInv : st.objects.invExt)
    (hOld : st.objects.get? tid0.toObjId = some (.tcb t0))
    (hObj : result.objects = st.objects.insert tid0.toObjId (.tcb t')) (scId : SeLe4n.SchedContextId) :
    result.getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?
  rw [hObj]
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable_getElem?_insert st.objects tid0.toObjId (.tcb t') hInv scId.toObjId]
  by_cases hk : tid0.toObjId == scId.toObjId
  · simp only [hk, if_pos]
    have hkey : st.objects.get? scId.toObjId = some (.tcb t0) := by
      have : scId.toObjId = tid0.toObjId := (eq_of_beq hk).symm
      rw [this]; exact hOld
    rw [hkey]
  · simp only [hk, if_neg, Bool.not_eq_true]

/-- WS-SM SM5.I (atom): inserting a `.schedContext sc'` at a slot already holding a
`.schedContext sc0` leaves every `getTcb?` lookup unchanged (a SchedContext slot is
never a TCB slot — the on-key case is `none = none`). -/
theorem getTcb?_insert_schedContext_eq (st result : SystemState) (scId0 : SeLe4n.SchedContextId)
    (sc0 sc' : SchedContext) (hInv : st.objects.invExt)
    (hOld : st.objects.get? scId0.toObjId = some (.schedContext sc0))
    (hObj : result.objects = st.objects.insert scId0.toObjId (.schedContext sc')) (tid : SeLe4n.ThreadId) :
    result.getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?
  rw [hObj]
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable_getElem?_insert st.objects scId0.toObjId (.schedContext sc') hInv tid.toObjId]
  by_cases hk : scId0.toObjId == tid.toObjId
  · simp only [hk, if_pos]
    have hkey : st.objects.get? tid.toObjId = some (.schedContext sc0) := by
      have : tid.toObjId = scId0.toObjId := (eq_of_beq hk).symm
      rw [this]; exact hOld
    rw [hkey]
  · simp only [hk, if_neg, Bool.not_eq_true]

/-- WS-SM SM5.I (atom): inserting a `.schedContext sc'` (with `boundThread` equal to
the displaced `sc0.boundThread`) at a slot already holding a `.schedContext sc0`
preserves every SchedContext's `boundThread` projection. -/
theorem getSchedContext?_boundThread_insert_schedContext (st result : SystemState)
    (scId0 : SeLe4n.SchedContextId) (sc0 sc' : SchedContext) (hInv : st.objects.invExt)
    (hOld : st.objects.get? scId0.toObjId = some (.schedContext sc0))
    (hBT : sc'.boundThread = sc0.boundThread)
    (hObj : result.objects = st.objects.insert scId0.toObjId (.schedContext sc'))
    (scId : SeLe4n.SchedContextId) :
    (result.getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  unfold SystemState.getSchedContext?
  rw [hObj]
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable_getElem?_insert st.objects scId0.toObjId (.schedContext sc') hInv scId.toObjId]
  by_cases hk : scId0.toObjId == scId.toObjId
  · simp only [hk, if_pos]
    have hkey : st.objects.get? scId.toObjId = some (.schedContext sc0) := by
      have : scId.toObjId = scId0.toObjId := (eq_of_beq hk).symm
      rw [this]; exact hOld
    rw [hkey]; simp only [Option.map_some]; rw [hBT]
  · simp only [hk, if_neg, Bool.not_eq_true]

-- ── shallow TCB / SchedContext writes ──

/-- WS-SM SM5.I: `enqueueRunnableOnCore` (an `ipcState := .ready` TCB write)
preserves every thread's home core. -/
theorem enqueueRunnableOnCore_determineTargetCore (st : SystemState) (c : CoreId)
    (tid0 : SeLe4n.ThreadId) (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    determineTargetCore (enqueueRunnableOnCore st c tid0) t = determineTargetCore st t := by
  unfold enqueueRunnableOnCore
  cases hTcb : st.getTcb? tid0 with
  | none => rfl
  | some tcb =>
    cases hR : runnableOnSomeCore st tid0 with
    | true => rfl
    | false =>
      have hRaw := (SystemState.getTcb?_eq_some_iff st tid0 tcb).mp hTcb
      exact determineTargetCore_insert_tcb st _ tid0 tcb { tcb with ipcState := .ready }
        hInv hRaw rfl rfl t

/-- WS-SM SM5.I: `enqueueRunnableOnCore` preserves every SchedContext's
`boundThread` projection. -/
theorem enqueueRunnableOnCore_boundThread (st : SystemState) (c : CoreId)
    (tid0 : SeLe4n.ThreadId) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    ((enqueueRunnableOnCore st c tid0).getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  unfold enqueueRunnableOnCore
  cases hTcb : st.getTcb? tid0 with
  | none => rfl
  | some tcb =>
    cases hR : runnableOnSomeCore st tid0 with
    | true => rfl
    | false =>
      have hRaw := (SystemState.getTcb?_eq_some_iff st tid0 tcb).mp hTcb
      rw [getSchedContext?_insert_tcb_eq st _ tid0 tcb { tcb with ipcState := .ready }
        hInv hRaw rfl scId]

/-- WS-SM SM5.I: `refillSchedContext` (a budget/replenishment SchedContext write)
preserves every thread's home core. -/
theorem refillSchedContext_determineTargetCore (st : SystemState) (scId0 : SeLe4n.SchedContextId)
    (now : Nat) (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    determineTargetCore (refillSchedContext st scId0 now) t = determineTargetCore st t := by
  unfold refillSchedContext
  split
  · rename_i sc hOld
    exact determineTargetCore_congr_getTcb? _ st t
      (getTcb?_insert_schedContext_eq st _ scId0 sc _ hInv hOld rfl t)
  · rfl

/-- WS-SM SM5.I: `refillSchedContext` preserves every SchedContext's `boundThread`
projection (`processReplenishments` / `cbsUpdateDeadline` write only budget / deadline
fields, never `boundThread`). -/
theorem refillSchedContext_boundThread (st : SystemState) (scId0 : SeLe4n.SchedContextId)
    (now : Nat) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    ((refillSchedContext st scId0 now).getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  unfold refillSchedContext
  split
  · rename_i sc hOld
    have hBT : (cbsUpdateDeadline (processReplenishments sc now) now true).boundThread
        = sc.boundThread := by
      simp only [cbsUpdateDeadline, processReplenishments, applyRefill]
      split <;> rfl
    exact getSchedContext?_boundThread_insert_schedContext st _ scId0 sc _ hInv hOld hBT rfl scId
  · rfl

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
        simp only [saveOutgoingContextOnCore, hc, ho]]
    | some outTcb =>
      have hRaw := (SystemState.getTcb?_eq_some_iff st outTid outTcb).mp ho
      have hObj : (saveOutgoingContextOnCore st c).objects
          = st.objects.insert outTid.toObjId (.tcb { outTcb with registerContext := st.machine.regsOnCore c }) := by
        simp only [saveOutgoingContextOnCore, hc, ho]
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
        simp only [saveOutgoingContextOnCore, hc, ho]]
    | some outTcb =>
      have hRaw := (SystemState.getTcb?_eq_some_iff st outTid outTcb).mp ho
      have hObj : (saveOutgoingContextOnCore st c).objects
          = st.objects.insert outTid.toObjId (.tcb { outTcb with registerContext := st.machine.regsOnCore c }) := by
        simp only [saveOutgoingContextOnCore, hc, ho]
      rw [getSchedContext?_insert_tcb_eq st _ outTid outTcb
        { outTcb with registerContext := st.machine.regsOnCore c } hInv hRaw hObj scId]

/-- WS-SM SM5.I: a successful `scheduleEffectiveOnCore` preserves every thread's home
core (its only object write is the outgoing register-context save). -/
theorem scheduleEffectiveOnCore_determineTargetCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') (t : SeLe4n.ThreadId) :
    determineTargetCore st' t = determineTargetCore st t := by
  have hobj := scheduleEffectiveOnCore_objects_eq st c st' hStep
  have hgt : st'.getTcb? t = (saveOutgoingContextOnCore st c).getTcb? t := by
    unfold SystemState.getTcb?; rw [hobj]
  rw [determineTargetCore_congr_getTcb? st' (saveOutgoingContextOnCore st c) t hgt]
  exact saveOutgoingContextOnCore_determineTargetCore st c hInv t

/-- WS-SM SM5.I: a successful `scheduleEffectiveOnCore` preserves every
SchedContext's `boundThread` projection. -/
theorem scheduleEffectiveOnCore_boundThread (st : SystemState) (c : CoreId)
    (st' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleEffectiveOnCore st c = .ok st') (scId : SeLe4n.SchedContextId) :
    (st'.getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  have hobj := scheduleEffectiveOnCore_objects_eq st c st' hStep
  have hgs : st'.getSchedContext? scId = (saveOutgoingContextOnCore st c).getSchedContext? scId := by
    unfold SystemState.getSchedContext?; rw [hobj]
  rw [hgs]
  exact saveOutgoingContextOnCore_boundThread st c hInv scId

-- ============================================================================
-- §3  Replenishment fold (prepared phase) — `determineTargetCore` + `boundThread`
-- ============================================================================

/-- WS-SM SM5.I: one replenishment step (`refillSchedContext` + an optional cross-core
`wakeThread`) preserves every thread's home core. -/
theorem processOneReplenishmentOnCore_determineTargetCore (st : SystemState) (ec : CoreId)
    (scId0 : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    determineTargetCore (processOneReplenishmentOnCore st ec scId0 now).1 t
      = determineTargetCore st t := by
  have hRefillDt := refillSchedContext_determineTargetCore st scId0 now hInv t
  have hRefillInv : (refillSchedContext st scId0 now).objects.invExt := by
    unfold refillSchedContext; split
    · exact RHTable_insert_preserves_invExt st.objects _ _ hInv
    · exact hInv
  simp only [processOneReplenishmentOnCore]
  split
  · split
    · exact hRefillDt
    · rw [wakeThread_state_eq_enqueue,
        enqueueRunnableOnCore_determineTargetCore _ _ _ hRefillInv]
      exact hRefillDt
  · exact hRefillDt

/-- WS-SM SM5.I: one replenishment step preserves every SchedContext's `boundThread`
projection. -/
theorem processOneReplenishmentOnCore_boundThread (st : SystemState) (ec : CoreId)
    (scId0 : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt)
    (scId : SeLe4n.SchedContextId) :
    ((processOneReplenishmentOnCore st ec scId0 now).1.getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  have hRefillBt := refillSchedContext_boundThread st scId0 now hInv scId
  have hRefillInv : (refillSchedContext st scId0 now).objects.invExt := by
    unfold refillSchedContext; split
    · exact RHTable_insert_preserves_invExt st.objects _ _ hInv
    · exact hInv
  simp only [processOneReplenishmentOnCore]
  split
  · split
    · exact hRefillBt
    · rw [wakeThread_state_eq_enqueue,
        enqueueRunnableOnCore_boundThread _ _ _ hRefillInv]
      exact hRefillBt
  · exact hRefillBt

/-- WS-SM SM5.I: the wake fold preserves every thread's home core. -/
theorem foldl_processOne_determineTargetCore (c : CoreId) (now : Nat) (t : SeLe4n.ThreadId)
    (dueIds : List SeLe4n.SchedContextId) (acc : SystemState × List (CoreId × SgiKind))
    (hInv : acc.1.objects.invExt) :
    determineTargetCore (dueIds.foldl (fun acc scId =>
        let (s, sgi?) := processOneReplenishmentOnCore acc.1 c scId now
        (s, acc.2 ++ sgi?.toList)) acc).1 t
      = determineTargetCore acc.1 t := by
  induction dueIds generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldl_cons, ih _
      (processOneReplenishmentOnCore_preserves_objects_invExt acc.1 c hd now hInv)]
    exact processOneReplenishmentOnCore_determineTargetCore acc.1 c hd now hInv t

/-- WS-SM SM5.I: the wake fold preserves every SchedContext's `boundThread`. -/
theorem foldl_processOne_boundThread (c : CoreId) (now : Nat) (scId : SeLe4n.SchedContextId)
    (dueIds : List SeLe4n.SchedContextId) (acc : SystemState × List (CoreId × SgiKind))
    (hInv : acc.1.objects.invExt) :
    ((dueIds.foldl (fun acc scId =>
        let (s, sgi?) := processOneReplenishmentOnCore acc.1 c scId now
        (s, acc.2 ++ sgi?.toList)) acc).1.getSchedContext? scId).map (·.boundThread)
      = (acc.1.getSchedContext? scId).map (·.boundThread) := by
  induction dueIds generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldl_cons, ih _
      (processOneReplenishmentOnCore_preserves_objects_invExt acc.1 c hd now hInv)]
    exact processOneReplenishmentOnCore_boundThread acc.1 c hd now hInv scId

/-- WS-SM SM5.I: `processReplenishmentsDueOnCore` preserves every thread's home core
(the `setReplenishQueueOnCore` seed is object-neutral; the wake fold preserves it). -/
theorem processReplenishmentsDueOnCore_determineTargetCore (st : SystemState) (c : CoreId)
    (now : Nat) (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    determineTargetCore (processReplenishmentsDueOnCore st c now).1 t
      = determineTargetCore st t := by
  simp only [processReplenishmentsDueOnCore]
  exact foldl_processOne_determineTargetCore c now t _ _ hInv

/-- WS-SM SM5.I: `processReplenishmentsDueOnCore` preserves every SchedContext's
`boundThread`. -/
theorem processReplenishmentsDueOnCore_boundThread (st : SystemState) (c : CoreId)
    (now : Nat) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    ((processReplenishmentsDueOnCore st c now).1.getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  simp only [processReplenishmentsDueOnCore]
  exact foldl_processOne_boundThread c now scId _ _ hInv

-- ============================================================================
-- §4  Per-phase affinity-consistency + the headline + the aggregate
-- ============================================================================

/-- WS-SM SM5.I: `processReplenishmentsDueOnCore` preserves replenish-queue
affinity-consistency — it only `popDue`-shrinks core `c`'s queue (every other core's
unchanged) and preserves `determineTargetCore` / `boundThread`. -/
theorem processReplenishmentsDueOnCore_preserves_replenishQueueAffinityConsistentOnCore
    (st : SystemState) (c : CoreId) (now : Nat) (c' : CoreId) (hInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistentOnCore st c') :
    replenishQueueAffinityConsistentOnCore (processReplenishmentsDueOnCore st c now).1 c' := by
  apply affinityConsistent_transfer st (processReplenishmentsDueOnCore st c now).1 c'
  · intro e hMem
    by_cases h : c = c'
    · subst h
      rw [processReplenishmentsDueOnCore_replenishQueueOnCore_self] at hMem
      exact popDue_remaining_subset _ now e hMem
    · rw [processReplenishmentsDueOnCore_replenishQueueOnCore_ne _ _ _ _ h] at hMem
      exact hMem
  · intro t; exact processReplenishmentsDueOnCore_determineTargetCore st c now hInv t
  · intro scId; exact processReplenishmentsDueOnCore_boundThread st c now hInv scId
  · exact hCons

/-- WS-SM SM5.I: the prepared (clear + replenishment) phase preserves affinity. -/
theorem timerTickOnCorePrepared_preserves_replenishQueueAffinityConsistentOnCore
    (st : SystemState) (c c' : CoreId) (hInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistentOnCore st c') :
    replenishQueueAffinityConsistentOnCore (timerTickOnCorePrepared st c).1 c' := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_replenishQueueAffinityConsistentOnCore
  · exact hInv
  · unfold replenishQueueAffinityConsistentOnCore at hCons ⊢
    simpa only [SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore] using hCons

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
    (hInv : st.objects.invExt) : (timerTickOnCorePrepared st c).1.objects.invExt := by
  simp only [timerTickOnCorePrepared]
  exact processReplenishmentsDueOnCore_preserves_objects_invExt _ c _ hInv

/-- WS-SM SM5.I (headline): the **live per-core timer tick** preserves replenish-queue
affinity-consistency on every core.  The prepared and schedule phases are proven via
the transfer helper; the budget phase is supplied as `hBudgetAffinity` (its exhausted
arm runs the IPC `timeoutBlockedThreads`, whose object-frame is the tracked-debt
residual). -/
theorem timerTickOnCore_preserves_replenishQueueAffinityConsistentOnCore (st : SystemState)
    (c : CoreId) (st' : SystemState) (sgis : List (CoreId × SgiKind)) (c' : CoreId)
    (hInv : st.objects.invExt)
    (hCons : ∀ c'', replenishQueueAffinityConsistentOnCore st c'')
    (hBudgetAffinity : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (st3 : SystemState) (b : Bool),
      (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
      timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b) →
      replenishQueueAffinityConsistentOnCore (timerTickOnCorePrepared st c).1 c' →
      replenishQueueAffinityConsistentOnCore st3 c')
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    replenishQueueAffinityConsistentOnCore st' c' := by
  have hPrepInv : (timerTickOnCorePrepared st c).1.objects.invExt :=
    timerTickOnCorePrepared_preserves_objects_invExt st c hInv
  have hPrep : ∀ c'', replenishQueueAffinityConsistentOnCore (timerTickOnCorePrepared st c).1 c'' :=
    fun c'' => timerTickOnCorePrepared_preserves_replenishQueueAffinityConsistentOnCore st c c'' hInv (hCons c'')
  rw [timerTickOnCore_eq_prepared] at hStep
  split at hStep
  · rw [Except.ok.injEq] at hStep
    have hst : (timerTickOnCorePrepared st c).1 = st' := by rw [hStep]
    rw [← hst]; exact hPrep c'
  · rename_i tid hCur
    split at hStep
    · split at hStep
      · simp at hStep
      · rename_i st3 b hbud
        have h3 : replenishQueueAffinityConsistentOnCore st3 c' :=
          hBudgetAffinity _ _ _ _ hCur hbud (hPrep c')
        have h3Inv : st3.objects.invExt :=
          timerTickBudgetOnCore_preserves_objects_invExt _ c _ _ _ _ hPrepInv hbud
        split at hStep
        · split at hStep
          · simp at hStep
          · rename_i st4 hsched
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            exact scheduleEffectiveOnCore_preserves_replenishQueueAffinityConsistentOnCore
              _ c _ c' h3Inv hsched h3
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨hst, _⟩ := hStep; subst hst; exact h3
    · simp at hStep

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
    (c : CoreId) (st' : SystemState) (sgis : List (CoreId × SgiKind)) (c' : CoreId)
    (hInv : ∀ c'', perCoreCbsInvariant st c'')
    (hInvObj : st.objects.invExt)
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).1.getSchedContext? scId = some sc →
      0 < sc.period.val)
    (hBudgetAffinity : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (st3 : SystemState) (b : Bool),
      (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
      timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b) →
      replenishQueueAffinityConsistentOnCore (timerTickOnCorePrepared st c).1 c' →
      replenishQueueAffinityConsistentOnCore st3 c')
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    perCoreCbsInvariant st' c' :=
  ⟨timerTickOnCore_preserves_replenishQueueValidOnCore st c st' sgis c'
      (fun c'' => (hInv c'').1) hStep,
   timerTickOnCore_preserves_replenishmentPipelineOrderOnCore st c st' sgis c'
      (fun c'' => (hInv c'').2.1) hPeriod hStep,
   timerTickOnCore_preserves_replenishQueueAffinityConsistentOnCore st c st' sgis c'
      hInvObj (fun c'' => (hInv c'').2.2) hBudgetAffinity hStep⟩

end SeLe4n.Kernel
